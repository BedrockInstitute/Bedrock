#!/usr/bin/env python3
"""Agda code linter for Bedrock masters (the ```agda fences of src/**/*.lagda.md).

Report-only checks (prose is lint-prose.py's business; STYLE-agda.md is the law):

  A [options]       the file's first pragma is exactly
                    {-# OPTIONS --cubical --safe --guardedness #-}        (STYLE-agda §1)
  B [bare-open]     every `open import` carries a using and/or renaming
                    clause (`hiding` alone does not qualify)              (STYLE-agda §2)
  C [unused-import] imports are *necessary*: every name bound by a
                    using/renaming clause of an import or a plain `open`,
                    and the handle of every qualified `import M [as A]`,
                    is actually used outside the binding clauses.
                    (*Sufficiency* is exactly what `agda` typechecking
                    enforces, so it is not re-checked here.)
  D [forbidden]     no `postulate`, no TERMINATING/NON_TERMINATING/
                    NO_TERMINATION_CHECK/NO_POSITIVITY_CHECK pragma, no
                    interaction holes (`{!...!}` or a bare `?`)           (STYLE-agda §1)

Exemptions:
  - `Everything.lagda.md` skips B and C: its bare import block is the site's
    module list, and its imports are intentionally "unused".
  - The designated hub modules (BARE_OPEN_HUBS: curated re-export preludes,
    designed to be opened wholesale) may be opened bare, skipping B.
  - An import whose lines (or the line just above it) contain `lint-agda: keep`
    in a comment skips B/C, for genuine cases the heuristics cannot see
    (e.g. instance-only imports).
  - `open import ... public` re-exports skip C (they are interface, not use).
  - names ending in `-syntax` skip C (used through their notation, so the
    name itself never re-appears).

Known limits (v1, deliberate): the same name imported from two modules and
used once leaves both imports unflagged (false negatives over false
positives); usage detection is lexical (token-level), not scope-aware.

Usage:
  lint-agda.py [--check] [FILE ...]
  with no FILE, scans git-tracked src/**/*.lagda.md. Exit 1 on any violation.
"""

import glob
import re
import sys

OPTIONS_EXPECTED = ["--cubical", "--safe", "--guardedness"]
EXEMPT_BASENAME = "Everything.lagda.md"
BARE_OPEN_HUBS = {"Base.Prelude", "Base.Truth"}   # STYLE-agda §2
KEEP_MARK = "lint-agda: keep"
FORBIDDEN_PRAGMAS = ("TERMINATING", "NON_TERMINATING",
                     "NO_TERMINATION_CHECK", "NO_POSITIVITY_CHECK")
# Agda token delimiters (note: [ ] , are identifier characters in Agda).
DELIMS = " \t\r\n(){};@"
TOKEN_SPLIT = re.compile("[" + re.escape(DELIMS) + "]+")


# ---- literate extraction -------------------------------------------------

def agda_lines(text):
    """[(lineno, line)] for lines inside ```agda fences (fences excluded)."""
    out, in_agda = [], False
    for i, line in enumerate(text.splitlines(), 1):
        s = line.strip()
        if in_agda:
            if s == "```":
                in_agda = False
            else:
                out.append((i, line))
        elif s == "```agda":
            in_agda = True
    return out


# ---- masking (strings, pragmas, comments -> spaces; newlines kept) --------

def mask_code(code):
    """Return (masked, pragmas, holes) for a code string.

    pragmas: [(line_index, text)] of {-# ... #-} contents; holes: [line_index]
    of {! occurrences. Masked text has strings/pragmas/comments blanked so the
    import parser and tokenizer never see them.
    """
    out = list(code)
    pragmas, holes = [], []
    i, n, line = 0, len(code), 0

    def blank(a, b):
        for k in range(a, b):
            if out[k] != "\n":
                out[k] = " "

    while i < n:
        c = code[i]
        if c == "\n":
            line += 1
            i += 1
        elif c == '"':
            j = i + 1
            while j < n and code[j] not in '"\n':
                j += 2 if code[j] == "\\" else 1
            j = min(j + 1, n)
            blank(i, j)
            i = j
        elif code.startswith("{!", i):
            holes.append(line)
            i += 2
        elif code.startswith("{-#", i):
            j = code.find("#-}", i)
            j = n if j < 0 else j + 3
            pragmas.append((line, code[i + 3:j - 3].strip()))
            blank(i, j)
            line += code.count("\n", i, j)
            i = j
        elif code.startswith("{-", i):
            depth, j = 1, i + 2
            while j < n and depth:
                if code.startswith("{-", j):
                    depth, j = depth + 1, j + 2
                elif code.startswith("-}", j):
                    depth, j = depth - 1, j + 2
                else:
                    j += 1
            blank(i, j)
            line += code.count("\n", i, j)
            i = j
        elif (code.startswith("--", i)
              and (i == 0 or code[i - 1] in DELIMS or code[i - 1] == "\n")):
            j = code.find("\n", i)
            j = n if j < 0 else j
            blank(i, j)
            i = j
        else:
            i += 1
    return "".join(out), pragmas, holes


# ---- import / open statement parsing --------------------------------------

STMT_RE = re.compile(r"^\s*(?:where\s+)?(?:(open)\s+)?import\s+([^\s(){};@]+)(.*)$")
OPEN_RE = re.compile(r"^\s*(?:where\s+)?open\s+(?!import\b)([^\s(){};@]+)(.*)$")
CONT_RE = re.compile(r"^\s*(?:using\b|renaming\b|hiding\b|public\b|\()")
CLAUSE_KEYWORDS = ("using", "renaming", "hiding", "as", "public")


class Stmt:
    def __init__(self, kind, module, first_index):
        self.kind = kind              # "import" | "open-import" | "open"
        self.module = module
        self.lines = [first_index]    # indices into the code-line list
        self.text = ""                # joined statement text after the module name
        self.args = ""
        self.as_name = None
        self.public = False
        self.hiding = False
        self.using = []               # [(name, is_module)]
        self.renamed = []             # [name]


def balanced(text, start):
    """Index just past the ')' matching the '(' at text[start]."""
    depth = 0
    for k in range(start, len(text)):
        if text[k] == "(":
            depth += 1
        elif text[k] == ")":
            depth -= 1
            if depth == 0:
                return k + 1
    return len(text)


def parse_clauses(st):
    """Fill st.args / using / renamed / hiding / public / as_name from st.text."""
    t, i, n = st.text, 0, len(st.text)
    args_end = None
    while i < n:
        m = re.match(r"\s*(using|renaming|hiding|as|public)\b", t[i:])
        if not m:
            i += 1
            continue
        if args_end is None:
            args_end = i
        kw = m.group(1)
        i += m.end()
        if kw == "public":
            st.public = True
        elif kw == "as":
            m2 = re.match(r"\s*([^\s(){};@]+)", t[i:])
            if m2:
                st.as_name = m2.group(1)
                i += m2.end()
        else:
            j = t.find("(", i)
            if j < 0:
                continue
            end = balanced(t, j)
            body = t[j + 1:end - 1]
            i = end
            if kw == "hiding":
                st.hiding = True
                continue
            for item in body.split(";"):
                item = " ".join(item.split())
                if not item:
                    continue
                if kw == "using":
                    if item.startswith("module "):
                        st.using.append((item[len("module "):].strip(), True))
                    else:
                        st.using.append((item, False))
                else:  # renaming: "a to b" / "module A to B"
                    parts = item.split()
                    if "to" in parts:
                        st.renamed.append(parts[parts.index("to") + 1])
    st.args = st.text[:args_end] if args_end is not None else st.text


def parse_statements(lines):
    """lines: [(lineno, text)] of masked code. Returns [Stmt]."""
    stmts, i = [], 0
    while i < len(lines):
        text = lines[i][1]
        m = STMT_RE.match(text)
        kind = None
        if m:
            kind = "open-import" if m.group(1) else "import"
            module, rest = m.group(2), m.group(3)
        else:
            m = OPEN_RE.match(text)
            if m and re.search(r"\b(using|renaming)\b", text + " "):
                kind, module, rest = "open", m.group(1), m.group(2)
        if not kind:
            i += 1
            continue
        st = Stmt(kind, module, i)
        chunks = [rest]
        depth = rest.count("(") - rest.count(")")
        while i + 1 < len(lines):
            nxt = lines[i + 1][1]
            if depth <= 0 and not CONT_RE.match(nxt):
                break
            i += 1
            st.lines.append(i)
            chunks.append(nxt)
            depth += nxt.count("(") - nxt.count(")")
        st.text = " ".join(chunks)
        parse_clauses(st)
        stmts.append(st)
        i += 1
    return stmts


# ---- the checks ------------------------------------------------------------

def lint_file(path):
    text = open(path, encoding="utf-8").read()
    raw = text.splitlines()
    lines = agda_lines(text)
    code = "\n".join(l for _, l in lines)
    masked, pragmas, holes = mask_code(code)
    mlines = list(zip((ln for ln, _ in lines), masked.splitlines()))
    exempt = path.split("/")[-1] == EXEMPT_BASENAME
    findings = []

    def report(idx_or_lineno, rule, msg, by_index=True):
        lineno = mlines[idx_or_lineno][0] if by_index else idx_or_lineno
        findings.append((lineno, rule, msg))

    # A. OPTIONS header
    opts = [(ln, p) for ln, p in pragmas if p.split()[:1] == ["OPTIONS"]]
    if not opts:
        findings.append((1, "options", "no OPTIONS pragma; expected {-# OPTIONS "
                         + " ".join(OPTIONS_EXPECTED) + " #-}"))
    elif opts[0][1].split()[1:] != OPTIONS_EXPECTED:
        report(opts[0][0], "options",
               "OPTIONS must be exactly: " + " ".join(OPTIONS_EXPECTED))

    # D. forbidden constructs
    for ln, p in pragmas:
        name = p.split()[0] if p.split() else ""
        if name in FORBIDDEN_PRAGMAS:
            report(ln, "forbidden", f"pragma {name} is banned (STYLE-agda §1)")
    for ln in holes:
        report(ln, "forbidden", "interaction hole {! ... !} (Frontier is the only debt form)")
    for idx, (_, mtext) in enumerate(mlines):
        toks = [t for t in TOKEN_SPLIT.split(mtext) if t]
        if "postulate" in toks:
            report(idx, "forbidden", "postulate is banned (PLAN D2; use a module parameter)")
        if "?" in toks:
            report(idx, "forbidden", "interaction hole `?` (Frontier is the only debt form)")

    # Parse statements; collect keep-marks from the raw (unmasked) lines.
    stmts = parse_statements(mlines)
    for st in stmts:
        first = mlines[st.lines[0]][0]
        span = [raw[mlines[i][0] - 1] for i in st.lines]
        if first >= 2:
            span.append(raw[first - 2])      # marker on the preceding line also counts
        st.keep = any(KEEP_MARK in l for l in span)

    # B. using-list discipline
    for st in stmts:
        if exempt or st.keep or st.kind != "open-import":
            continue
        if st.module in BARE_OPEN_HUBS:
            continue
        if not st.using and not st.renamed:
            extra = " (`hiding` alone does not qualify)" if st.hiding else ""
            report(st.lines[0], "bare-open",
                   f"open import {st.module} without using/renaming{extra}")

    # C. import necessity
    corpus_lines = list(masked.splitlines())
    tail = []
    for st in stmts:
        for i in st.lines:
            corpus_lines[i] = ""
        tail.append(st.args)                 # module-application arguments are uses
        if st.kind == "open":
            tail.append(st.module)           # `open PT ...` is a use of PT
    for _, p in pragmas:
        if p.split()[:1] != ["OPTIONS"]:
            tail.append(p)                   # BUILTIN/DISPLAY etc. reference names
    tokens = [t for t in TOKEN_SPLIT.split("\n".join(corpus_lines + tail)) if t]
    tokset = set(tokens)
    stripped = {t.strip("_") for t in tokset}

    def used(name):
        if name in tokset or name.endswith("-syntax"):
            return True
        parts = [p for p in name.split("_") if p]
        return bool(parts) and all(p in stripped for p in parts)

    def used_module(handle):
        dotted = handle + "."
        return any(t == handle or t.startswith(dotted) for t in tokset)

    for st in stmts:
        if exempt or st.keep or st.public:
            continue
        if st.kind == "import":
            handle = st.as_name or st.module
            if not used_module(handle) and not (st.using or st.renamed):
                report(st.lines[0], "unused-import",
                       f"qualified import {st.module} is never used")
            continue
        for name, is_mod in st.using:
            ok = used_module(name) if is_mod else used(name)
            if not ok:
                report(st.lines[0], "unused-import",
                       f"`{name}` imported from {st.module} but never used")
        for name in st.renamed:
            if not used(name):
                report(st.lines[0], "unused-import",
                       f"`{name}` (renamed) imported from {st.module} but never used")

    return sorted(findings)


# ---- CLI -------------------------------------------------------------------

def tracked_masters():
    """All masters on disk, tracked or not: a new file must not escape the gate
    merely by not being committed yet."""
    return sorted(glob.glob("src/**/*.lagda.md", recursive=True))


def main(argv):
    files = [a for a in argv if not a.startswith("--")]
    files = [f for f in files if f.endswith(".lagda.md")] or tracked_masters()
    total = 0
    for path in files:
        for lineno, rule, msg in lint_file(path):
            print(f"{path}:{lineno}: [{rule}] {msg}")
            total += 1
    if total:
        print(f"lint-agda: {total} violation(s)")
    return 1 if total else 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
