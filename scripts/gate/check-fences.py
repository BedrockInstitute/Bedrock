#!/usr/bin/env python3
"""Catch Agda that sits OUTSIDE a code fence in a `.lagda.md` master.

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
import re
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
from repo_root import find_root  # noqa: E402

ROOT = find_root(__file__)
SRC = ROOT / "src"

# An Agda identifier head. Agda admits primes, hyphens, dots and subscripts.
IDENT = r"[^\s():=|`*#>\-][^\s():=]*"

# THREE SHAPES, and the second one is why the first draft of this file was
# blind to the defect it was written for. A signature `f : T` matched, but a
# clause head with arguments, `AndAgree γ = mk ...`, did not, so every run
# broke at its second line and the checker stayed silent on a synthetic
# reproduction of the real defect. Test a checker against the thing it exists
# to catch, or it proves nothing.
SIG = re.compile(rf"^\s*{IDENT}\s*:\s")                    # f : T
CLAUSE = re.compile(rf"^\s*{IDENT}(\s+[^\s=]+)*\s*=\s")    # f x y = e
KEYWORD = re.compile(r"^\s*(where|module|open|private|data|record|"
                     r"postulate|mutual|abstract|opaque|instance|variable)\b")


def looks_like_agda(line: str) -> bool:
    return bool(SIG.match(line) or CLAUSE.match(line) or KEYWORD.match(line))

# Lines that are prose by construction, whatever else they look like.
PROSE_HEAD = ("-", "*", "|", ">", "#", "<!--", "`")

# MARKDOWN MARKERS THAT NEVER OCCUR IN AGDA CODE, and they are the whole
# reason this checker can be quiet. This repository's prose names Agda
# identifiers as `foo`{.Agda}, so a backtick is a certain sign of prose. The
# first draft checked only the FIRST character of a line and fired on wrapped
# paragraphs in `src/Base/Truth.lagda.md` and `src/Everything.lagda.md`.
PROSE_ANYWHERE = ("`", "**", "{.Agda}", "<!--")

DEFAULT_RUN = 3


def suspects(path: pathlib.Path, run: int) -> list[tuple[int, str]]:
    fenced = False
    streak: list[tuple[int, str]] = []
    hits: list[tuple[int, str]] = []
    for i, line in enumerate(path.read_text().split("\n"), 1):
        if line.startswith("```agda"):
            fenced = True
            streak = []
            continue
        if line.startswith("```"):
            fenced = False
            streak = []
            continue
        if fenced:
            continue
        stripped = line.lstrip()
        if not stripped:
            # A blank line ends a run: real Agda blocks are contiguous.
            if len(streak) >= run:
                hits.extend(streak)
            streak = []
            continue
        # An INDENTED line continues a run that has already started: a `where`
        # block's body is Agda but rarely matches a declaration shape on its
        # own. It never STARTS a run, so an indented prose line is inert.
        continues = bool(streak) and line[:1] in (" ", "\t")
        prose = (stripped.startswith(PROSE_HEAD)
                 or any(mark in line for mark in PROSE_ANYWHERE))
        if prose or not (looks_like_agda(line) or continues):
            if len(streak) >= run:
                hits.extend(streak)
            streak = []
            continue
        streak.append((i, line))
    if len(streak) >= run:
        hits.extend(streak)
    return hits


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

    if defects:
        print(f"\ncheck-fences: {defects} master(s) with unfenced Agda. "
              f"[LJ-1.41] reported two theorems CLOSED that sat outside a "
              f"fence and had four defects; every other gate passed.")
        return 1 if args.check else 0

    print(f"check-fences: clean ({len(masters)} masters, run threshold "
          f"{args.run})")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
