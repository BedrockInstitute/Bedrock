#!/usr/bin/env python3
"""Prose linter for Bedrock: enforces CJK punctuation conventions and bans em dashes.

Rules (apply to Markdown prose, `*.md` / `*.lagda.md`; the verbatim LICENSE is excluded):

  1. Sentence punctuation , ; : ! ?  -> full-width ，；：！？ in Chinese context   [auto-fix]
  2. Chinese double quotes "..." / “...”  -> 「...」                               [auto-fix]
  3. Parentheses in Chinese context must be half-width ( ), with English-style outer
     spacing: a space before '(' and after ')'   (e.g. 经典原理 (LEM、AC) 是…)        [auto-fix]
     No space after a full-width symbol; no space between two Chinese characters
     (markdown-adjacent spaces are exempt).                                            [auto-fix]
  4. No em dash — (U+2014), ― (U+2015), or 中文 破折号 ——                          [report only]
  5. No single quotes as quotation marks in Chinese context, no quote nesting       [report only]

"Chinese context" = the punctuation is adjacent to (or, for quotes/parens, wraps) a
CJK ideograph or CJK punctuation, looking past whitespace, markdown emphasis markers,
inline code, links and URLs. English apostrophes (V's, field's) and English quotes
("formal purity") are not in Chinese context and are left untouched.

Code spans, fenced code blocks, markdown link/image destinations and URLs are protected.

Usage:
  lint-prose.py [--check | --fix] [--staged] [FILE ...]
  default mode is --check; with no FILE and no --staged, scans git-tracked *.md/*.lagda.md.
Exit status is non-zero if any violation remains (in --fix, only the report-only ones).
"""

import re
import subprocess
import sys

# ---- character classes -------------------------------------------------------

CJK_IDEOGRAPH = [(0x3400, 0x4DBF), (0x4E00, 0x9FFF), (0xF900, 0xFAFF), (0x20000, 0x2FA1F)]
# CJK punctuation / full-width forms used as "Chinese context":
CJK_PUNCT = [(0x3000, 0x303F), (0xFF00, 0xFFEF), (0x2018, 0x2019), (0x201C, 0x201D)]

FULLWIDTH = {",": "，", ";": "；", ":": "：", "!": "！", "?": "？"}
EM_DASHES = {"—", "―"}            # U+2014, U+2015  (en dash U+2013 and hyphen are allowed)
SKIP = set(" \t\r*_~()[]")        # whitespace, markdown emphasis, transparent brackets


def _in(cp, ranges):
    return any(a <= cp <= b for a, b in ranges)


def is_cjk_ideograph(ch):
    return _in(ord(ch), CJK_IDEOGRAPH)


def is_cjk_punct(ch):
    return _in(ord(ch), CJK_PUNCT)


def is_cjk(ch):
    return is_cjk_ideograph(ch) or is_cjk_punct(ch)


# ---- protected-region mask ---------------------------------------------------

def build_protected(text):
    """Boolean mask: True where chars are inside code / link dest / URL (untouchable)."""
    n = len(text)
    prot = [False] * n

    # fenced code blocks (``` or ~~~), inclusive of the fence lines
    pos = 0
    fenced = False
    for line in text.split("\n"):
        stripped = line.lstrip()
        is_fence = stripped.startswith("```") or stripped.startswith("~~~")
        if fenced or is_fence:
            for j in range(pos, pos + len(line)):
                prot[j] = True
        if is_fence:
            fenced = not fenced
        pos += len(line) + 1  # + newline

    def mask(pattern, start_off=0):
        for m in re.finditer(pattern, text):
            for j in range(m.start() + start_off, m.end()):
                prot[j] = True

    mask(r"`[^`\n]*`")                       # inline code
    mask(r"\]\([^)\n]*\)", start_off=1)      # markdown link/image destination: the (...) part
    mask(r"[A-Za-z][A-Za-z0-9+.\-]*://[^\s)]+")  # bare URLs
    return prot


# ---- adjacency ---------------------------------------------------------------

def _scan(text, prot, i, step):
    """Nearest meaningful char in direction `step`, skipping spaces/emphasis/protected.
    Stops at a line boundary."""
    j = i + step
    while 0 <= j < len(text):
        c = text[j]
        if c == "\n":
            return None
        if c in SKIP or prot[j]:
            j += step
            continue
        return c
    return None


def cjk_adjacent(text, prot, i):
    left = _scan(text, prot, i, -1)
    right = _scan(text, prot, i, +1)
    return (left is not None and is_cjk(left)) or (right is not None and is_cjk(right))


# ---- analysis ----------------------------------------------------------------

class Violation:
    __slots__ = ("index", "message", "fixable")

    def __init__(self, index, message, fixable):
        self.index = index
        self.message = message
        self.fixable = fixable


def analyze(text):
    """Return (fixed_text, fixable_violations, manual_violations).

    fixed_text applies rules 1-3. Each list holds Violation objects (against `text`)."""
    prot = build_protected(text)
    n = len(text)
    edits = {}            # index -> replacement char (rules 1-3)
    fixable = []
    manual = []

    # Rule 1: sentence punctuation -> full-width
    for i, ch in enumerate(text):
        if prot[i] or ch not in FULLWIDTH:
            continue
        if ch == ":":
            if text[i + 1:i + 3] == "//":
                continue
            if i > 0 and text[i - 1].isdigit() and i + 1 < n and text[i + 1].isdigit():
                continue
        if cjk_adjacent(text, prot, i):
            edits[i] = FULLWIDTH[ch]
            fixable.append(Violation(i, f"half-width '{ch}' in Chinese context -> '{FULLWIDTH[ch]}'", True))

    # Rule 2: Chinese double quotes -> 「」
    for pat, opench, closech in ((r'"[^"\n]*"', '"', '"'), (r"“[^”\n]*”", "“", "”")):
        for m in re.finditer(pat, text):
            s, e = m.start(), m.end() - 1
            if prot[s] or prot[e]:
                continue
            inner = text[s + 1:e]
            ctx = any(is_cjk(c) for c in inner) or cjk_adjacent(text, prot, s) or cjk_adjacent(text, prot, e)
            if ctx:
                edits[s] = "「"
                edits[e] = "」"
                fixable.append(Violation(s, f"Chinese double quote {opench}…{closech} -> 「…」", True))

    # Rule 3: full-width parens in Chinese context -> half-width
    for i, ch in enumerate(text):
        if prot[i]:
            continue
        if ch in "（）" and cjk_adjacent(text, prot, i):
            edits[i] = "(" if ch == "（" else ")"
            fixable.append(Violation(i, f"full-width '{ch}' in Chinese context -> '{edits[i]}'", True))

    # Rule 3b: half-width parens in Chinese context get English-style outer spacing
    LEAD_GLUE = set("*_~`")  # markdown emphasis / code fence chars that still want a space before '('
    for m in re.finditer(r"\([^()]*\)", text):  # content may wrap across a soft line break
        s, e = m.start(), m.end() - 1
        if prot[s] or prot[e]:
            continue
        content = text[s + 1:e]
        if not (cjk_adjacent(text, prot, s) or cjk_adjacent(text, prot, e) or any(is_cjk(c) for c in content)):
            continue
        if s > 0 and s not in edits:
            p = text[s - 1]
            if is_cjk_ideograph(p) or p.isalnum() or p in LEAD_GLUE:
                edits[s] = " ("
                fixable.append(Violation(s, "half-width '(' in Chinese context needs a leading space", True))
        if e + 1 < n and e not in edits:
            nxt = text[e + 1]
            if is_cjk_ideograph(nxt) or nxt.isalnum():
                edits[e] = ") "
                fixable.append(Violation(e, "half-width ')' in Chinese context needs a trailing space", True))

    # Rule 3c: no space immediately after a full-width punctuation symbol
    for i, ch in enumerate(text):
        if prot[i] or not is_cjk_punct(ch):
            continue
        j = i + 1
        while j < n and text[j] in " \t":
            if j not in edits:
                edits[j] = ""
                fixable.append(Violation(i, f"no space after full-width '{ch}'", True))
            j += 1

    # Rule 3d: no space between two CJK ideographs (markdown-adjacent spaces are exempt)
    ideo = r"[㐀-䶿一-鿿]"
    for m in re.finditer(rf"(?<={ideo})[ \t]+(?={ideo})", text):
        if any(prot[k] for k in range(m.start(), m.end())):
            continue
        for k in range(m.start(), m.end()):
            edits.setdefault(k, "")
        fixable.append(Violation(m.start(), "no space between Chinese characters", True))

    # Rule 4: em dash (report only)
    for i, ch in enumerate(text):
        if prot[i]:
            continue
        if ch in EM_DASHES:
            manual.append(Violation(i, f"em dash '{ch}' is banned; rewrite with ，：。() or split the sentence", False))

    # Rule 5: single quotes in Chinese context + nesting (report only)
    for i, ch in enumerate(text):
        if prot[i]:
            continue
        if ch in ("‘", "’") and cjk_adjacent(text, prot, i):
            manual.append(Violation(i, f"single quote '{ch}' in Chinese context is banned (use 「」, no nesting)", False))
        elif ch == "'" and cjk_adjacent(text, prot, i):
            manual.append(Violation(i, "ASCII single quote as a Chinese quotation mark is banned (use 「」)", False))
        elif ch in ("『", "』"):
            manual.append(Violation(i, f"nested-quote bracket '{ch}' is banned (no quote nesting)", False))

    # Rule 5 (cont.): detect 「 opened while already inside 「…」
    depth = 0
    for i, ch in enumerate(text):
        if prot[i]:
            continue
        if ch == "「":
            if depth > 0:
                manual.append(Violation(i, "nested 「 is banned (no quote nesting)", False))
            depth += 1
        elif ch == "」" and depth > 0:
            depth -= 1

    if edits:
        fixed = "".join(edits.get(i, c) for i, c in enumerate(text))
    else:
        fixed = text
    return fixed, fixable, manual


# ---- driver ------------------------------------------------------------------

def line_of(text, index):
    return text.count("\n", 0, index) + 1


def report(path, text, violations):
    for v in sorted(violations, key=lambda x: x.index):
        ln = line_of(text, v.index)
        print(f"{path}:{ln}: {v.message}")


def git_lines(args):
    try:
        out = subprocess.run(["git", *args], capture_output=True, text=True, check=True).stdout
    except (subprocess.CalledProcessError, FileNotFoundError):
        return []
    return [l for l in out.splitlines() if l]


def target_files(explicit, staged):
    if explicit:
        files = explicit
    elif staged:
        files = git_lines(["diff", "--cached", "--name-only", "--diff-filter=ACM"])
    else:
        files = git_lines(["ls-files", "*.md", "*.lagda.md"])
    return [f for f in files if (f.endswith(".md") or f.endswith(".lagda.md"))]


def main(argv):
    mode = "check"
    staged = False
    paths = []
    for a in argv:
        if a == "--check":
            mode = "check"
        elif a == "--fix":
            mode = "fix"
        elif a == "--staged":
            staged = True
        elif a.startswith("-"):
            sys.stderr.write(f"unknown option: {a}\n")
            return 2
        else:
            paths.append(a)

    files = target_files(paths, staged)
    total_fixable = 0
    total_manual = 0
    fixed_files = []

    for path in files:
        try:
            with open(path, encoding="utf-8") as fh:
                text = fh.read()
        except (OSError, UnicodeDecodeError):
            continue
        fixed, fixable, manual = analyze(text)

        if mode == "fix":
            if fixed != text:
                with open(path, "w", encoding="utf-8") as fh:
                    fh.write(fixed)
                fixed_files.append(path)
            # report manual violations against the fixed text
            _, _, manual = analyze(fixed)
            if manual:
                report(path, fixed, manual)
                total_manual += len(manual)
        else:  # check
            if fixable:
                report(path, text, fixable)
                total_fixable += len(fixable)
            if manual:
                report(path, text, manual)
                total_manual += len(manual)

    if mode == "fix":
        for p in fixed_files:
            print(f"fixed: {p}", file=sys.stderr)
        if total_manual:
            print(f"\n{total_manual} issue(s) need manual rewriting (em dash / single quote / nesting).", file=sys.stderr)
            return 1
        return 0
    else:
        if total_fixable or total_manual:
            hint = "run: python3 scripts/lint-prose.py --fix <files>  (auto-fixes punctuation/quotes; em dash & nesting are manual)"
            print(f"\n{total_fixable + total_manual} violation(s). {hint}", file=sys.stderr)
            return 1
        return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
