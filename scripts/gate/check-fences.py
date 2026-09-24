#!/usr/bin/env python3
"""Three rules about the boundary between code and prose in a `.lagda.md` master.

RULE 1, [unfenced-agda]: no Agda outside a fence. Agda reads only fenced code.
RULE 2, [fenced-comment]: no comment inside a fence. A comment is prose, and
prose belongs between the fences, where the site renders it and the size ledger
does not count it as code.
RULE 3, [fence-language-boundary]: leave a blank line between a closing fence
and a language marker. Agda's Markdown renderer otherwise escapes the marker
as visible source text and breaks the site's language grouping.

WHY THIS EXISTS, and it is one measured failure rather than a tidiness wish.
On 2026-08-11 `[LJ-1.41]` reported two condensation row agreements CLOSED and
machine-checked. `[LJ-1.42]` then found that both sat outside the ` ```agda `
fence, as prose. Agda had never read them. They carried four real defects: a
missing parenthesis, off-by-one body indices, wrong membership indices and a
wrong disjunction elimination.

EVERY EXISTING GATE PASSED. Agda typechecks only fenced code, so the master was
green. `scripts/measure/ledger.py` counts only fenced lines, so the size figure was
right. The orchestrator verified green, verified the count, and committed. The
defect was invisible to all of it, because unfenced text is invisible BY
CONSTRUCTION to every tool this repository has.

WHAT IT LOOKS FOR. A RUN of consecutive declaration-shaped lines outside a
fence. One `Note:` in a paragraph is prose. Three or more consecutive lines
shaped like Agda declarations or clauses is a lost fence. The run threshold is
what keeps this quiet on real prose; raise it rather than weaken the shape test
if a false positive appears.

WHAT IT CANNOT DO. It cannot tell a lost fence from a deliberate code SAMPLE in
prose. `dev/STYLE-i18n.md` requires English inside ` ```agda ` fences, and a
sample belongs in a fence of another language or in backticks. So a hit is a
defect or a style violation, and either way it wants a human.

USE: `.venv/bin/python scripts/gate/check-fences.py`
     `.venv/bin/python scripts/gate/check-fences.py --check`
     `.venv/bin/python scripts/gate/check-fences.py --run 5`
"""
from __future__ import annotations

import argparse
import pathlib
import sys

# LJ-1.291: the root is found by walking up to the repository marker, never by
# counting directories; `scripts/repo_root.py` holds the one walk. LJ-1.295:
# this script lives in a group directory under scripts/, so the SCRIPTS root,
# where `repo_root.py` and `agents_tree.py` sit flat, is found the same way,
# by walking up to `repo_root.py` itself; the group directory joins sys.path
# for siblings imported by bare name.
_HERE = pathlib.Path(__file__).resolve()
sys.path.insert(0, str(_HERE.parent))
_SCRIPTS = next((p for p in _HERE.parents if (p / "repo_root.py").is_file()), None)
if _SCRIPTS is None:
    raise FileNotFoundError(
        f"no repo_root.py above {_HERE}: refusing to guess the scripts root (C-43)")
sys.path.insert(0, str(_SCRIPTS))
from repo_root import find_root


ROOT = find_root(__file__)
SRC = ROOT / "src"

from outcrop.core.fence_lint import DEFAULT_RUN, REMEDY
from outcrop.core.fence_lint import (
    fenced_comments as text_comments, tight_language_boundaries as text_boundaries,
    suspects as text_suspects,
)

def fenced_comments(path):
    return text_comments(path.read_text())

def tight_language_boundaries(path):
    return text_boundaries(path.read_text())

def suspects(path, run):
    return text_suspects(path.read_text(), run)

def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--check", action="store_true",
                    help="exit non-zero on a hit, for the gate")
    ap.add_argument("--run", type=int, default=DEFAULT_RUN,
                    help=f"consecutive declaration-shaped lines to flag "
                         f"(default {DEFAULT_RUN})")
    args = ap.parse_args()

    masters = sorted(SRC.rglob("*.lagda.md"))
    if not masters:
        print("check-fences: no masters found", file=sys.stderr)
        return 2

    defects = 0
    for m in masters:
        hits = suspects(m, args.run)
        if not hits:
            continue
        defects += 1
        rel = m.relative_to(ROOT)
        print(f"  DEFECT [unfenced-agda]: {rel} has {len(hits)} line(s) outside "
              f"a fence that look like Agda. Agda never reads them and "
              f"ledger.py never counts them, so a green tree proves nothing "
              f"about them.")
        for i, line in hits[:6]:
            print(f"    {rel}:{i}: {line.strip()[:72]}")
        if len(hits) > 6:
            print(f"    ... and {len(hits) - 6} more")

    commented = 0
    comment_lines = 0
    for m in masters:
        hits = fenced_comments(m)
        if not hits:
            continue
        commented += 1
        comment_lines += len(hits)
        rel = m.relative_to(ROOT)
        print(f"  DEFECT [fenced-comment]: {rel} has {len(hits)} comment "
              f"line(s) inside a fence. A comment is prose, and prose belongs "
              f"between the fences.")
        for i, line in hits[:6]:
            print(f"    {rel}:{i}: {line.strip()[:72]}")
        if len(hits) > 6:
            print(f"    ... and {len(hits) - 6} more")

    tight = 0
    for m in masters:
        hits = tight_language_boundaries(m)
        if not hits:
            continue
        tight += 1
        rel = m.relative_to(ROOT)
        print(f"  DEFECT [fence-language-boundary]: {rel} has {len(hits)} "
              "language marker(s) immediately after a closing fence. Add a "
              "blank line so the marker remains hidden metadata.")
        for i in hits[:6]:
            print(f"    {rel}:{i}")

    if defects:
        print(f"\ncheck-fences: {defects} master(s) with unfenced Agda. "
              f"[LJ-1.41] reported two theorems CLOSED that sat outside a "
              f"fence and had four defects; every other gate passed.")
    if tight:
        print(f"\ncheck-fences: {tight} master(s) with an unsafe fence/language "
              "marker boundary.")
    if commented:
        print(f"\ncheck-fences: {comment_lines} comment line(s) inside a fence "
              f"in {commented} master(s).")
        print(REMEDY)
    if defects or commented or tight:
        return 1 if args.check else 0

    print(f"check-fences: clean ({len(masters)} masters, run threshold "
          f"{args.run})")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
