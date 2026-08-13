#!/usr/bin/env python3
"""Pins the archive layout: `archive/` mirrors the repository root.

**THE RULE.** The owner ruled on 2026-08-13 that an archived thing sits at the same path
under `archive/` that it had under the repository root. Something archived from
`dev/measurements/` goes to `archive/dev/measurements/`. Something archived from `scripts/`
goes to `archive/scripts/`. **The reason is drift**: a flat bucket with no structural rule
fills up, and then nobody can tell where anything came from. `archive/README.md` is the
canonical home of the rule; `[LJ-1.143]` executed it.

**THE ONE EXTRA LEVEL.** `archive/src/` inserts an ARCHIVAL EVENT directory, because `src/`
has been archived six times and two of those archivals took files out of the same
directories. A flat merge would lose which archival each file came from.

**WHY THIS FILE EXISTS.** Nothing else notices a new bare directory under `archive/`. The
archive sits outside `src/`, so every gate is blind to it by structure: the Agda gate cannot
reach it, the include path excludes it, and the linters do not scan it. That is what makes
the archive free to keep, and it is also why a layout defect there is invisible. **Three
directories drifted in eight days before anyone measured it.**
"""

import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent.parent
ARCHIVE = ROOT / "archive"

FAIL: list[str] = []
PASSED = 0


def check(ok: bool, msg: str) -> None:
    global PASSED
    if ok:
        PASSED += 1
    else:
        FAIL.append(msg)


#: A directory that may sit directly under `archive/` because a directory of that name sits
#: directly under the repository root. This set is DERIVED, never written by hand.
ROOT_DIRS = {p.name for p in ROOT.iterdir() if p.is_dir() and not p.name.startswith(".")}

#: The ONE exception, and it carries its reason. A refused kit never landed in `src/`, so it
#: has no original path for the mirror rule to map (`archive/kits/README.md:35-40`).
#: `[LJ-1.143]` left it rather than invent a home. Adding a name here needs the owner's word.
EXCEPTIONS = {"kits"}

#: An archival-event directory under `archive/src/`: an ISO date, then a slug taken from the
#: archival commit's own subject. The date is what makes the name identify the event.
EVENT = re.compile(r"^\d{4}-\d{2}-\d{2}-[a-z0-9]+(?:-[a-z0-9]+)*$")


# ------------------------------------------------------------------ the mirror
check(ARCHIVE.is_dir(), "there is no archive/")

for d in sorted(p for p in ARCHIVE.iterdir() if p.is_dir()):
    check(d.name in ROOT_DIRS or d.name in EXCEPTIONS,
          f"archive/{d.name}/ mirrors no root directory and is not a declared exception: "
          f"the owner's ruling of 2026-08-13 puts an archived thing at its original path")

# The three directories `[LJ-1.143]` retired must not come back under their old names.
for gone in ("tooling", "measurements", "probes", "rud-route"):
    check(not (ARCHIVE / gone).exists(),
          f"archive/{gone}/ is back: it mirrors no root directory")

# ------------------------------------------------------- the archival events
src = ARCHIVE / "src"
check(src.is_dir(), "there is no archive/src/")
events = sorted(p for p in src.iterdir() if p.is_dir())
check(bool(events), "archive/src/ holds no archival-event directory")
for e in events:
    check(EVENT.match(e.name) is not None,
          f"archive/src/{e.name}/ is not `<date>-<slug>`, so its name does not say "
          f"which archival it was")

# Nothing may sit at `archive/src/` outside an event directory: that is the bare state the
# ruling removes, and it is exactly how the two source buckets diverged.
loose = [p.name for p in src.iterdir() if p.is_file()]
check(not loose, f"file(s) directly under archive/src/, outside any archival event: {loose}")

# ------------------------------------------------- the mirror holds one level down
# `archive/scripts/tests/` mirrors `scripts/tests/`. A test file that landed beside the
# scripts instead would break the mirror silently, because nothing imports it.
sd = ARCHIVE / "scripts"
if sd.is_dir():
    stray = [p.name for p in sd.iterdir() if p.is_file() and p.name.startswith("test_")]
    check(not stray,
          f"archive/scripts/ holds test file(s) that belong in archive/scripts/tests/: {stray}")

# `reuse lint` covers the archive through one path prefix. A move inside it must not need a
# new entry, and this check fails loudly if the carve-out ever stops being a bare prefix.
reuse = (ROOT / "REUSE.toml").read_text(encoding="utf-8")
check('path = "archive/**"' in reuse,
      "REUSE.toml no longer covers archive/ with a single prefix, so a move inside the "
      "archive can now relicense a file")

if FAIL:
    for f in FAIL:
        print(f"FAIL: {f}")
    print(f"test_archive_layout: {len(FAIL)} failing check(s), {PASSED} passed")
    sys.exit(1)
print(f"test_archive_layout: all checks passed ({PASSED})")
