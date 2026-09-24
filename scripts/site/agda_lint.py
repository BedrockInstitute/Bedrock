"""Pure Agda source lint. Project vocabulary ownership is explicit policy data."""
import re
from dataclasses import dataclass, field

@dataclass(frozen=True)
class AgdaPolicy:
    options: tuple = ('--cubical', '--safe', '--guardedness')
    bare_open_hubs: tuple = ()
    prelude_module: str = ''
    prelude_public_names: dict = field(default_factory=dict)
    empty_family: str = ''
    forbid_monomorphic_empty: bool = False
    hprop_projection: bool = False

KEEP_MARK = "lint-agda: keep"
FORBIDDEN_PRAGMAS = ("TERMINATING", "NON_TERMINATING",
                     "NO_TERMINATION_CHECK", "NO_POSITIVITY_CHECK")
HPROP_SND_RE = re.compile(r"\b[PQ]\b\s*\.snd\b")
EMPTY_BOTTOM_RE = re.compile(r"\bEmpty\.⊥(?!\*)")
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


def agda_trailing_blanks(text):
    """[(lineno, count)] for trailing blank runs inside ```agda fences.

    Report the first line of each run so one malformed fence produces one
    actionable finding even when it contains several trailing blank lines.
    """
    out, in_agda, blank_start = [], False, None
    for i, line in enumerate(text.splitlines(), 1):
        stripped = line.strip()
        if in_agda:
            if stripped == "```":
                if blank_start is not None:
                    out.append((blank_start, i - blank_start))
                in_agda, blank_start = False, None
            elif stripped:
                blank_start = None
            elif blank_start is None:
                blank_start = i
        elif stripped == "```agda":
            in_agda, blank_start = True, None
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
        self.renamed_sources = []     # [source name]


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
                        source = parts[0] if parts[0] != "module" else parts[1]
                        st.renamed_sources.append(source)
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

def lint_text(text, policy=None):
    policy = policy or AgdaPolicy()
    raw = text.splitlines()
    lines = agda_lines(text)
    code = "\n".join(l for _, l in lines)
    masked, pragmas, holes = mask_code(code)
    mlines = list(zip((ln for ln, _ in lines), masked.splitlines()))
    findings = []

    def report(idx_or_lineno, rule, msg, by_index=True):
        lineno = mlines[idx_or_lineno][0] if by_index else idx_or_lineno
        findings.append((lineno, rule, msg))

    # H. A code fence closes directly after its final code line. Blank lines
    # outside the fence still provide the Markdown separation from prose.
    for lineno, count in agda_trailing_blanks(text):
        suffix = "s" if count != 1 else ""
        findings.append((lineno, "trailing-blank",
                         f"remove {count} trailing blank line{suffix} from the Agda fence"))

    # Check the masked concatenated Agda stream, not only one Markdown fence.
    for index, (_, line) in enumerate(mlines):
        if line.strip() != 'private':
            continue
        following = next((item for item in mlines[index + 1:] if item[1].strip()), None)
        if following and re.match(r'\s*module\b', following[1]):
            report(index, 'private-module', 'write `private module` on one line; preserve the privacy of sibling declarations')

    # A. OPTIONS header
    opts = [(ln, p) for ln, p in pragmas if p.split()[:1] == ["OPTIONS"]]
    if not opts:
        findings.append((1, "options", "no OPTIONS pragma; expected {-# OPTIONS "
                         + " ".join(list(policy.options)) + " #-}"))
    elif opts[0][1].split()[1:] != list(policy.options):
        report(opts[0][0], "options",
               "OPTIONS must be exactly: " + " ".join(list(policy.options)))

    # D. forbidden constructs
    for ln, p in pragmas:
        name = p.split()[0] if p.split() else ""
        if name in FORBIDDEN_PRAGMAS:
            report(ln, "forbidden", f"pragma {name} is banned (STYLE-agda §1)")
    for ln in holes:
        report(ln, "forbidden", "interaction hole {! ... !} is banned (STYLE-agda §1)")
    for idx, (_, mtext) in enumerate(mlines):
        toks = [t for t in TOKEN_SPLIT.split(mtext) if t]
        if "postulate" in toks:
            report(idx, "forbidden",
                   "postulate is banned (archived D2, live ruling DD9; "
                   "use a module parameter)")
        if "?" in toks:
            report(idx, "forbidden", "interaction hole `?` is banned (STYLE-agda §1)")
        if policy.forbid_monomorphic_empty and EMPTY_BOTTOM_RE.search(mtext):
            report(idx, "forbidden",
                   "`Empty.⊥` is banned; use the level-polymorphic `⊥* {ℓ}` "
                   f"from {policy.prelude_module}")
        if policy.hprop_projection and HPROP_SND_RE.search(mtext) and "⟨ P ⟩isProp = P .snd" not in mtext:
            report(idx, "hprop-snd",
                   "use `⟨ P ⟩isProp` instead of the representation-level `.snd`")

    # Parse statements; collect keep-marks from the raw (unmasked) lines.
    stmts = parse_statements(mlines)
    for st in stmts:
        first = mlines[st.lines[0]][0]
        span = [raw[mlines[i][0] - 1] for i in st.lines]
        if first >= 2:
            span.append(raw[first - 2])      # marker on the preceding line also counts
        st.keep = any(KEEP_MARK in l for l in span)

    # F. Base.Prelude owns the public empty-type vocabulary. Other modules
    # may use a qualified import while legacy code is being migrated, but
    # must not open the Cubical.Data.Empty module family into local scope.
    is_base_prelude = bool(re.search(
        r"(?m)^\s*module\s+" + re.escape(policy.prelude_module) + r"\s+where\b", masked))
    if policy.prelude_module and not is_base_prelude:
        for st in stmts:
            if (st.kind == "open-import"
                    and (st.module == policy.empty_family
                         or st.module.startswith(policy.empty_family + "."))):
                report(st.lines[0], "empty-open",
                       f"only {policy.prelude_module} may `open import` the "
                       f"{policy.empty_family} module family")
            if st.module in policy.prelude_public_names:
                public_names = set(policy.prelude_public_names[st.module])
                imported = {name for name, is_module in st.using if not is_module}
                imported.update(st.renamed_sources)
                repeated = sorted(imported & public_names)
                unrestricted = (st.kind in {"import", "open-import"}
                                and not re.search(r"\b(?:using|renaming)\b", st.text))
                if st.as_name or (st.kind == "import" and not imported) or unrestricted:
                    report(st.lines[0], "prelude-import",
                           f"do not import or alias all of {st.module}; import only "
                           "non-Prelude names with an explicit using/renaming list")
                elif repeated:
                    report(st.lines[0], "prelude-import",
                           f"{', '.join(repeated)} already come from {policy.prelude_module}; "
                           "do not import or rename them again")

    # B. using-list discipline
    for st in stmts:
        if st.keep or st.kind != "open-import":
            continue
        if st.module in policy.bare_open_hubs:
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
        # A QUALIFIED USE IS A USE, and missing this once broke the tree.
        # A record or module brought in by name, `using ( SWO )`, is then
        # spelled `SWO.tri`, which is ONE token; the bare name never appears.
        # Reporting it as unused made a sweep delete it, on 2026-09-06.
        dotted = name + "."
        if any(t.startswith(dotted) for t in tokset):
            return True
        parts = [p for p in name.split("_") if p]
        return bool(parts) and all(p in stripped for p in parts)

    def used_module(handle):
        dotted = handle + "."
        return any(t == handle or t.startswith(dotted) for t in tokset)

    for st in stmts:
        if st.keep or st.public:
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



__all__ = [name for name in globals() if not name.startswith("__")]
