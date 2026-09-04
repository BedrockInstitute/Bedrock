#!/usr/bin/env python3
"""Pins the `agents/tasks/` layout: the Agda-safe directory name, and the brief predicate.

**THE RULE THIS FILE ENFORCES HAS NO OTHER MACHINE.** `[LJ-1.142]` merged the briefs, the reports
and the probes into one directory per task. Two things can break silently afterwards:

1. **A directory name that Agda cannot parse.** `bedrock.agda-lib` reads
   `include: src agents/tasks`, so a directory there is a module name component. A `.` or a `_`
   in one makes every probe under it unresolvable. Agda only notices when something IMPORTS the
   module, and nothing imports a closed task's probe, so a bad name lands green and stays green.
   **The name test below is the only thing that would catch it.**
2. **A census that drops to zero.** Five checkers read this tree. A path change that empties one
   of their lists makes it pass by reading nothing (C-40).
"""

import re
import subprocess
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
import agents_tree as T  # noqa: E402

FAIL: list[str] = []
PASSED = 0


def check(ok: bool, msg: str) -> None:
    global PASSED
    if ok:
        PASSED += 1
    else:
        FAIL.append(msg)


# ---------------------------------------------------------------- the layout
check(T.TASKS.is_dir(), f"no task tree at {T.TASKS}")
check(T.ARCHIVE.is_dir(), f"no archive half at {T.ARCHIVE}")
check(not (T.ROOT / "agents" / "briefs").exists(),
      "agents/briefs/ is back: the merge of [LJ-1.142] has been undone")
check(not (T.ROOT / "agents" / "reports").exists(),
      "agents/reports/ is back: the root rename of [LJ-1.142] has been undone")

# The include root must be the one the layout assumes, or every probe module name is wrong.
lib = (T.ROOT / "bedrock.agda-lib").read_text(encoding="utf-8")
check(re.search(r"^include:.*\bagents/tasks\b", lib, re.M) is not None,
      "bedrock.agda-lib does not carry `agents/tasks` as an include root")

# No loose brief or report at either level: every record belongs to a task.
loose = [p.name for p in T.TASKS.glob("*.md") if p.name != "README.md"]
check(not loose, f"loose .md at the tasks root, outside any task: {loose}")
loose_a = [p.name for p in T.ARCHIVE.glob("*.md") if not p.name.endswith(".lagda.md")]
check(not loose_a, f"loose .md at the archive root, outside any task: {loose_a}")

# ------------------------------------------------- THE AGDA-SAFE NAME (the point)
# MEASURED 2026-08-13 by [LJ-1.142] in this tree, with agents/tasks/LJ-1-142/ as the evidence:
#   L3-32-T126, nametest-lowercase, NAMETEST-Geology-Legacy   typecheck
#   a `.` in the name   -> [ModuleNameDoesntMatchFileName], the `.` splits the qualifier
#   a `_` in the name   -> [ParseError], the `_` splits a mixfix name and the digits are a literal
AGDA_NAME = re.compile(r"^[A-Za-z][A-Za-z0-9-]*$")

#: [LJ-1.142]'s two NEGATIVE CONTROLS. These directories are deliberately illegal: agda refuses
#: each one, and they are kept so a later reader can re-run the measurement instead of trusting
#: it. They are the ONLY exception, and the test below proves the rule catches them.
NEG = {"NAMETEST-L3.32-DOT", "NAMETEST-L3_32_UNDERSCORE"}

# ONLY TRACKED DIRECTORIES ARE JUDGED, and that is the whole fix of
# 2026-08-16. `rglob` walks the working tree, so a local `__pycache__` under
# any task directory failed this check, and `.state/` under a probe did too.
# Neither is in git, neither reaches another clone, and neither can break an
# Agda module name for anybody. MEASURED: the suite was RED at HEAD on eight
# such directories, five of them `__pycache__`, and nothing reported it
# because `make test` is not part of `make check`.
#
# A directory is TRACKED when git holds a file under it. That is the same
# ground truth `check-probes.py` reads, and it is the only one that survives
# a machine with a different scratch layout.
#
# AND ONLY MODULE SPACE IS JUDGED. The rule exists because `bedrock.agda-lib`
# lists `agents/tasks` as an include root, so a directory on the path to an
# Agda file becomes a module qualifier. A directory that holds no Agda file
# anywhere below it is never a qualifier and the rule does not reach it.
# MEASURED 2026-08-16: `agents/tasks/LJ-1-290/copy/` is a 58-file, 828 kB
# dry-run copy of `scripts/` that the layout migration ran against, it holds
# ZERO Agda files, and its `.github/workflows` failed this check for no
# reason an Agda run could ever have.
module_dirs = set()
for rel in subprocess.run(["git", "ls-files", "agents/tasks"], cwd=T.ROOT,
                          capture_output=True, text=True).stdout.split():
    if not (rel.endswith(".agda") or rel.endswith(".lagda.md")):
        continue
    p = Path(rel).parent
    while p != Path("agents/tasks") and p != Path("."):
        module_dirs.add(T.ROOT / p)
        p = p.parent

bad = []
for d in T.TASKS.rglob("*"):
    if not d.is_dir() or d.name in NEG or d not in module_dirs:
        continue
    if not AGDA_NAME.match(d.name):
        bad.append(str(d.relative_to(T.ROOT)))
check(not bad, f"directory name(s) Agda cannot parse as a module component: {bad[:8]}")

# The evidence must survive, or the measurement above is a claim with no probe. And each negative
# control must still FAIL the rule: a name test that has never rejected anything proves nothing.
ev = T.TASKS / "LJ-1-142" / "ProbeNameIndex.agda"
check(ev.is_file(), f"the naming evidence is gone: {ev}")
for neg in sorted(NEG):
    check((T.TASKS / "LJ-1-142" / neg).is_dir(),
          f"the negative control {neg} is gone; the positive test then proves nothing")
    check(not AGDA_NAME.match(neg),
          f"the name rule ACCEPTS {neg}, which agda refuses: the rule is too weak")

# ------------------------------------------------------------ the census (C-40)
docs = T.documents()
briefs = T.briefs()
cands = T.candidate_briefs()
reports = T.reports()
check(len(docs) > 800, f"document census collapsed to {len(docs)}")
check(len(briefs) > 380, f"brief census collapsed to {len(briefs)}")
check(len(reports) > 400, f"report census collapsed to {len(reports)}")
check(len(T.task_dirs()) > 500, f"task-directory census collapsed to {len(T.task_dirs())}")
check(len(T.task_dirs(False)) > 40,
      f"LIVE task-directory census collapsed to {len(T.task_dirs(False))}")

# The name-based set must be a superset of nothing it should miss: every brief the content
# predicate finds by a `-brief` stem or a matching name must also be a candidate.
missed = [str(p.relative_to(T.ROOT)) for p in briefs
          if T.is_candidate_brief(p) is False and T.normalise(p.stem) == p.parent.name]
check(not missed, f"a brief the name rule should catch is not a candidate: {missed[:5]}")

# ------------------------------------------------------------- the predicates
check(all(not T.is_brief(p) for p in reports),
      "a file named `-report`/`-review` was read as a brief")
check(all(not T.is_report(p) for p in briefs),
      "a brief was read as a report")

# A brief and its report sit in ONE directory: that is the whole ruling.
paired = [d for d in T.task_dirs()
          if any(T.is_brief(p) for p in d.glob("*.md"))
          and any(T.is_report(p) for p in d.glob("*.md"))]
check(len(paired) > 250, f"only {len(paired)} task directories hold BOTH a brief and a report")

# A known task resolves both ways.
check(T.task_dir("LJ-1.142") is not None, "task_dir('LJ-1.142') does not resolve")
check(T.brief_for("LJ-1.142") is not None, "brief_for('LJ-1.142') does not resolve")
check(T.task_dir("L3.32-T126") is not None, "task_dir('L3.32-T126') does not resolve the archive")
check(T.brief_for("nonexistent-task-code") is None, "brief_for invented a brief")
check(T.normalise("LJ-1.142") == "LJ-1-142", "normalise does not turn `.` into `-`")

# A probe lives with its task. ONE non-task bucket is left and it keeps its name.
check((T.ARCHIVE / "Unpaired").is_dir(), "the Unpaired probe bucket is gone")
check("Unpaired" in T.NON_TASK_DIRS, "Unpaired is not declared a non-task directory")

# `[LJ-1.143]` emptied the DD25 bucket on the evidence inside the DD25 reviews, so a DD25
# directory coming BACK is the drift the owner's ruling removes, not a neutral event.
# The name stays in NON_TASK_DIRS so no reader ever takes it for a task code.
check(not (T.TASKS / "DD25").exists(),
      "agents/tasks/DD25/ is back: a probe bucket that is not a task has returned")
check("DD25" in T.NON_TASK_DIRS, "DD25 is not declared a non-task directory")
check(all(d.name not in T.NON_TASK_DIRS for d in T.task_dirs()),
      "a non-task bucket is being reported as a task")

if FAIL:
    for f in FAIL:
        print(f"FAIL: {f}")
    print(f"test_agents_tree: {len(FAIL)} failing check(s), {PASSED} passed")
    sys.exit(1)
print(f"test_agents_tree: all checks passed ({PASSED})")
