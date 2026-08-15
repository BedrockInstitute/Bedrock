#!/usr/bin/env python3
"""One home for the shape of `agents/tasks/`: where a task's files are, and which one is the brief.

**WHY THIS FILE EXISTS.** Until 2026-08-13 a brief was a file in `agents/briefs/` and a report
was a file in `agents/reports/`. The DIRECTORY carried the distinction, so five checkers each
wrote `ROOT / "agents" / "briefs"` and each was right. `[LJ-1.142]` merged the two trees under
the owner's ruling: one task, one directory, holding the brief, the report and every probe.
**The merge deleted the signal those five checkers read.** This module is where the replacement
signal lives, written once, so a later correction reaches every reader at the same time.

THE LAYOUT
----------

    agents/tasks/<CODE>/            a live task
    agents/tasks/archive/<CODE>/    a task of the retired route
    agents/tasks/archive/Unpaired/  probes no report claims by name

`agents/tasks/DD25/` is GONE. It held the 55 probes of a RULING, which is not a task.
`[LJ-1.143]` placed all 55 in the task directory of the DD25 review that BUILT each one,
on the review's own "THE PROBES" table, so no probe now sits outside a task.

`<CODE>` is the task code with `.` written `-` and the whole name upper case, because
`bedrock.agda-lib` reads `include: src agents/tasks` and **a directory under an include root is
an Agda module name component**. MEASURED 2026-08-13 in this tree: `L3-32-T126` and
`nametest-lowercase` typecheck; a `.` in the name gives `[ModuleNameDoesntMatchFileName]` and a
`_` gives `[ParseError]`, because `.` splits the qualifier and `_` splits a mixfix name. The
evidence is `agents/tasks/LJ-1-142/ProbeNameIndex.agda` and its two negative controls.

THE BRIEF PREDICATE COMES IN TWO FORMS, AND A CALLER MUST PICK THE RIGHT ONE
---------------------------------------------------------------------------

**`briefs()` reads the CONTENT and is exact.** A file is a brief when it is not named a report,
carries neither an `ARCHIVE USED` heading nor a `STATUS:` line in its first twelve lines, and
carries a `tier:` line, a `SCOPE (read)`/`SCOPE (write)` heading, or a `-brief` stem.
**MEASURED against the 920 files at the moment of the merge, while the source directory was
still ground truth: 415 of 415 briefs found, 0 missed, 0 of 505 reports misread.**

**`candidate_briefs()` reads the NAME and is wider.** A file is a candidate when it is not named
a report and its stem, normalised, equals its directory name, or its stem ends `-brief`.
**MEASURED the same way: 415 of 415 found, and 27 archived reports misread**, every one of them
a bare-stem recon, audit or dossier of the retired route under `archive/`.

**A CHECKER THAT LOOKS FOR A MISSING `tier:` LINE MUST USE `candidate_briefs()`**, because
`briefs()` finds a brief partly BY its `tier:` line: a new brief that forgot one would be
invisible to the very check that exists to catch it. That checker pays for the wider set by
never failing an archived record, which is where all 27 misreadings live. **Every other caller
wants `briefs()`.**
"""

from __future__ import annotations

import re
import sys
from pathlib import Path

# LJ-1.291: the root is found by walking up to the repository marker, never by
# counting directories; `scripts/repo_root.py` holds the one walk.
sys.path.insert(0, str(Path(__file__).resolve().parent))
from repo_root import find_root  # noqa: E402

ROOT = find_root(__file__)
TASKS = ROOT / "agents" / "tasks"
ARCHIVE = TASKS / "archive"

#: Directories under `agents/tasks/` that are not tasks. `Unpaired` holds probes whose task no
#: report names; `[LJ-1.141]` named it and `[LJ-1.142]` kept it rather than invent a task for it.
#: `DD25` was the second such bucket and is gone: `[LJ-1.143]` placed all 55 of its probes on the
#: evidence inside the DD25 reviews. The name stays in this set because the tree is read by path
#: and a stale directory must never be read as a task code.
NON_TASK_DIRS = {"DD25", "Unpaired", "archive"}

REPORT_SUFFIXES = ("-report", "-review")
BRIEF_SUFFIX = "-brief"

#: The content signals. MEASURED over the 920 documents at the merge: `ARCHIVE USED` appears in
#: 168 reports and in NO brief; a `STATUS:` line in the first twelve lines appears in 214 reports
#: and in NO brief; `SCOPE (read)` appears in 332 briefs and in NO report. `tier:` appears in 412
#: briefs and in 31 reports, which quote their own brief's header, so it is a positive signal only
#: after the two negative ones have run.
_ARCHIVE_USED = re.compile(r"(?im)^#+\s*(?:\d+\.\s*)?ARCHIVE USED")
_STATUS = re.compile(r"(?im)^\**\s*status\s*:")
_SCOPE = re.compile(r"(?im)^#+\s*SCOPE \((?:read|write)\)")
_TIER = re.compile(r"(?im)^tier:")


def normalise(code: str) -> str:
    """The directory name for a task code. `LJ-1.142` -> `LJ-1-142`."""
    return code.upper().replace(".", "-")


def task_dirs(include_archive: bool = True) -> list[Path]:
    """Every task directory, live first, then the retired route.

    **BOTH levels are filtered by `NON_TASK_DIRS`, and the archive half was not.** The
    `Unpaired` bucket moved from `agents/tasks/` to `agents/tasks/archive/` on 2026-08-13,
    where the filter did not reach it, so twelve probes with no task were reported to five
    checkers as a task named `Unpaired`. Caught by `test_agents_tree.py`.
    """
    out = sorted(p for p in TASKS.iterdir()
                 if p.is_dir() and p.name not in NON_TASK_DIRS)
    if include_archive and ARCHIVE.is_dir():
        out += sorted(p for p in ARCHIVE.iterdir()
                      if p.is_dir() and p.name not in NON_TASK_DIRS)
    return out


def documents(include_archive: bool = True) -> list[Path]:
    """Every brief and report in the tree, in path order.

    A `.lagda.md` is NOT a document here. `agents/tasks/archive/tmp-cond-dd3aa13.lagda.md` is a
    copy of a chapter, not a record of a dispatch, and it sits outside every task directory.
    """
    out: list[Path] = []
    for d in task_dirs(include_archive):
        out += sorted(p for p in d.glob("*.md") if not p.name.endswith(".lagda.md"))
    return out


def is_report(path: Path) -> bool:
    """A file that names itself a report or a review."""
    return path.stem.lower().endswith(REPORT_SUFFIXES)


def is_candidate_brief(path: Path) -> bool:
    """A file that carries its task's own name. Wider than `is_brief`; see the module docstring."""
    if is_report(path):
        return False
    stem = path.stem
    if stem.lower().endswith(BRIEF_SUFFIX):
        return True
    return normalise(stem) == path.parent.name


def is_brief(path: Path, text: str | None = None) -> bool:
    """A file that reads as a brief. Exact against the corpus; see the module docstring."""
    if is_report(path):
        return False
    if text is None:
        text = path.read_text(encoding="utf-8", errors="replace")
    if _ARCHIVE_USED.search(text):
        return False
    if _STATUS.search("\n".join(text.splitlines()[:12])):
        return False
    return (path.stem.lower().endswith(BRIEF_SUFFIX)
            or _TIER.search(text) is not None
            or _SCOPE.search(text) is not None)


def is_archived(path: Path) -> bool:
    """True when the path is under the retired route's half of the tree."""
    return ARCHIVE in path.parents


def briefs(include_archive: bool = True) -> list[Path]:
    """Every brief, read by content. Exact against the corpus; see the module docstring."""
    return [p for p in documents(include_archive) if is_brief(p)]


def candidate_briefs(include_archive: bool = True) -> list[Path]:
    """Every brief, read by name. Use this, NEVER `briefs()`, to audit a brief's own header."""
    return [p for p in documents(include_archive) if is_candidate_brief(p)]


def reports(include_archive: bool = True) -> list[Path]:
    """Every file that names itself a report or a review."""
    return [p for p in documents(include_archive) if is_report(p)]


def task_dir(code: str) -> Path | None:
    """The directory of one task code, live or archived, or None."""
    name = normalise(code)
    for parent in (TASKS, ARCHIVE):
        cand = parent / name
        if cand.is_dir():
            return cand
    return None


def brief_for(code: str) -> Path | None:
    """The one brief of a task code, or None. Used by the source-reading audit."""
    d = task_dir(code)
    if d is None:
        return None
    found = [p for p in sorted(d.glob("*.md")) if is_brief(p)]
    return found[0] if found else None


def task_codes() -> list[str]:
    """Every task code the tree knows, as the directory spells it."""
    return [d.name for d in task_dirs()]
