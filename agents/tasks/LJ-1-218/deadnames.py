#!/usr/bin/env python3
"""Scan the twelve wing masters for names defined but never used.

Reads in-fence code only. For each top-level-ish declaration name in a wing
master, counts how many times the name appears in the in-fence code of all of
src/ (the master itself included), EXCLUDING the declaration line itself and
comment lines. A name that appears nowhere else is a candidate dead name.

Qualified uses (M.out, C.πX, H.T.Hull) contain the bare name as a substring,
so a plain word count catches them. A name used only in a comment is not a
use. Report the count beside each name; the caller reads the list.
"""
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent.parent.parent

WING = [
    "src/V/Collapse.lagda.md",
    "src/L/Hull.lagda.md",
    "src/V/Presentation.lagda.md",
    "src/FOL/Count.lagda.md",
    "src/L/StageCardinal.lagda.md",
    "src/L/Condensation.lagda.md",
    "src/L/Ordinal/SquareLaw.lagda.md",
    "src/L/Ordinal/StageArith.lagda.md",
    "src/L/BoundedSubset.lagda.md",
    "src/L/Condensation/TwelveAgree.lagda.md",
    "src/L/Condensation/UpperAgree.lagda.md",
    "src/L/Condensation/LowerAgree.lagda.md",
]


def fence_lines(path):
    """Yield (lineno, text) for non-blank, non-comment in-fence lines."""
    out = []
    inside = False
    for i, line in enumerate(path.read_text(encoding="utf-8").splitlines(), 1):
        s = line.strip()
        if s.startswith("```"):
            if not inside and re.match(r"^```+\s*agda\b", s):
                inside = True
            elif inside:
                inside = False
            continue
        if inside and s and not s.startswith("--"):
            out.append((i, s))
    return out


def all_code():
    """(path, [(lineno, text)]) for every tracked master under src/."""
    res = {}
    for p in sorted((ROOT / "src").rglob("*.lagda.md")):
        res[str(p.relative_to(ROOT))] = fence_lines(p)
    return res


def declared_names(code):
    """Top-level declaration names: line starts with a token followed by : or =.

    The first token of the line, then the rest must start with `:` or `=`.
    Record fields are NOT top-level (inside record ... where) but are still
    caught when the record body is flush-left. Good enough for a sweep."""
    names = {}
    for i, s in code:
        toks = s.split()
        if not toks:
            continue
        n = toks[0]
        if n.startswith("(") or n.startswith("{"):
            continue  # module telescope parameters are not definitions
        rest = s[len(n):].lstrip()
        if rest.startswith(":") or rest.startswith("="):
            names.setdefault(n, []).append(i)
    return names


def main():
    code = all_code()
    # Build a combined text per file for counting, but skip comment lines.
    # Count every occurrence of the name as a word (unicode-aware).
    for wf in WING:
        wlines = code.get(wf, [])
        names = declared_names(wlines)
        if not names:
            print(f"== {wf}: no names parsed")
            continue
        # gather all text
        all_text = []
        for f, lines in code.items():
            for _i, s in lines:
                all_text.append(s)
        blob = "\n".join(all_text)
        # For each name, count word occurrences; subtract the declaration
        # occurrences (the definition line itself).
        print(f"== {wf} ({len(names)} names)")
        results = []
        for n, lns in names.items():
            total = blob.count(n)
            results.append((total, n, lns))
        results.sort()
        for total, n, lns in results:
            flag = "  <-- CANDIDATE" if total <= len(lns) else ""
            print(f"  uses={total:4d} decl@{[str(x) for x in lns][:4]} {n}{flag}")


if __name__ == "__main__":
    main()
