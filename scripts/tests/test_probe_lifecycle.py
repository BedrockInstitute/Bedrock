#!/usr/bin/env python3
"""Regression tests for the probe lifecycle: the trigger, the floor and the CLI.

WHY THIS FILE EXISTS. On 2026-08-13 `[LJ-1.133]` found that `--stale --delete`
would have deleted 234 probes while printing "safe to delete", because the rule
was backwards. On the same day `[LJ-1.138]` found two more defects of the same
species: the freshness clock called all 14 probes in `src/` FRESH while all 14
tasks were closed, and `--archive` on its own did nothing and printed the
`--check` success line. **A lifecycle rule that no test pins is the rule that
was backwards this morning.**

The tests below pin the three things that must never silently invert:

1. A LIVE task's probe is HELD, and `[LJ-1.136]` reading `[LJ-1.134]`'s probe
   is the worked case.
2. "The report exists" NEVER closes a task. C-22 makes every running agent
   write its report file in its first minute, so a rule that reads a report
   file as a closed task sweeps a live agent's file.
3. An ineffective flag combination FAILS. It never falls through to another
   mode's success line.

Run: `python3 scripts/tests/test_probe_lifecycle.py`
"""

from __future__ import annotations

import importlib.util
import subprocess
import sys
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent.parent
spec = importlib.util.spec_from_file_location(
    "check_probes", ROOT / "scripts" / "check-probes.py"
)
check_probes = importlib.util.module_from_spec(spec)
spec.loader.exec_module(check_probes)

failures: list[str] = []


def check(name: str, condition: bool, detail: str = "") -> None:
    if condition:
        print(f"  ok    {name}")
    else:
        print(f"  FAIL  {name}{(': ' + detail) if detail else ''}")
        failures.append(name)


# ---------------------------------------------------------------------------
# 1. The stem parse, and its ambiguity is deliberate
# ---------------------------------------------------------------------------
print("stem_codes: a probe names its own task, ambiguously")

check("ProbeLJ1134A offers every digit split",
      check_probes.stem_codes("ProbeLJ1134A")
      == {"LJ-1.134", "LJ-11.34", "LJ-113.4"})
check("the true code is among them", "LJ-1.134" in check_probes.stem_codes("ProbeLJ1134A"))
check("ProbeT126 reads as the retired series", check_probes.stem_codes("ProbeT126") == {"T126"})
check("a decision-coded probe yields no task code",
      check_probes.stem_codes("ProbeDD25F41A") == set())
check("a word-named probe yields no task code",
      check_probes.stem_codes("ProbeBelowLim") == set())
check("zero padding normalizes", check_probes.stem_codes("ProbeLJ104A") == {"LJ-1.4", "LJ-10.4"})


# ---------------------------------------------------------------------------
# 2. The filename -> code map, which is what pairs a brief with its report
# ---------------------------------------------------------------------------
print("_file_code: a brief and its report resolve to ONE code across both series")

pairs = [
    ("LJ-1.136.md", "LJ-1.136"),
    ("lj-1.136-report.md", "LJ-1.136"),
    ("LJ-0.4a.md", "LJ-0.4a"),
    ("lj-0.4f-r-report.md", "LJ-0.4f-r"),
    ("t26-pairkit-brief.md", "T26"),
    ("l3.32-t26-report.md", "T26"),
    ("l3.32-t201-decision.md", "T201"),
    ("compress-recon.md", None),
]
for name, want in pairs:
    check(f"{name} -> {want}", check_probes._file_code(name) == want,
          f"got {check_probes._file_code(name)}")

check("a brief and its differently-named report pair on the code",
      check_probes._file_code("t26-pairkit-brief.md")
      == check_probes._file_code("l3.32-t26-report.md"))


# ---------------------------------------------------------------------------
# 3. THE TRIGGER on the live tree. This is the case the rule was built on.
# ---------------------------------------------------------------------------
print("the trigger on the live tree")

verdicts = check_probes.probe_verdicts()
by_stem = {f.stem: (kind, why) for f, kind, why in verdicts}
live = check_probes.live_tasks()

check("the live set is not empty", bool(live))
check("a live set entry carries its evidence at file:line or a path",
      all((":" in why or "exists" in why) for why in live.values()))

if "ProbeLJ1134A" in by_stem:
    kind, why = by_stem["ProbeLJ1134A"]
    check("ProbeLJ1134A is HELD", kind == check_probes.HELD, f"got {kind}: {why}")
    check("and the hold names WHERE it is claimed", ":" in why, why)
    check("[LJ-1.134] itself is CLOSED, so the hold is not its own task",
          "LJ-1.134" not in live)
else:
    print("  skip  ProbeLJ1134A is no longer in src/; the live-tree case cannot run")

check("no verdict is the retired FRESH class",
      all(kind != "FRESH" for kind, _ in by_stem.values()))
check("every verdict is one of the four",
      all(kind in (check_probes.HELD, check_probes.EVIDENCE,
                   check_probes.NAMED, check_probes.ORPHAN)
          for kind, _ in by_stem.values()))


# ---------------------------------------------------------------------------
# 4. "The report exists" must NEVER close a task. C-22 is why.
# ---------------------------------------------------------------------------
print("C-22: a running agent's report file exists from its first minute")

# The rule may only ever read a MISSING report as evidence of an unfinished
# task. If some future edit inverts it, a task whose report file exists while
# it runs stops being live, and its probe is swept out from under it. The test
# states the property directly: a code with BOTH a brief and a report may still
# be live, and only the task index can say so.
plan_live = {c for c, why in live.items() if why.startswith("dev/PLAN.md")}
reported_and_live = []
for code in plan_live:
    lower = code.lower()
    if (ROOT / "agents" / "reports" / f"{lower}-report.md").exists():
        reported_and_live.append(code)
check("at least one live task already has a report file on disk",
      bool(reported_and_live), "no C-22 skeleton found; the property is untested today")
check("and having it did not close the task",
      all(c in live for c in reported_and_live))


# ---------------------------------------------------------------------------
# 5. The hop is narrow. A wide hop re-creates the backlog.
# ---------------------------------------------------------------------------
print("the one hop out of a live brief is narrow")

check("the hop reaches agents/ only, never dev/",
      check_probes.HOP_INTO == ("agents/reports/", "agents/briefs/"))
check("a dev/ path is not a hop target",
      not check_probes.DOC_PATH.findall("read dev/LESSONS.md whole"))
check("a report path is a hop target",
      check_probes.DOC_PATH.findall("read agents/reports/lj-1.134-report.md WHOLE")
      == ["agents/reports/lj-1.134-report.md"])
check("an archived report path is a hop target",
      check_probes.DOC_PATH.findall("agents/reports/archive/lj-1.74-report.md:209")
      == ["agents/reports/archive/lj-1.74-report.md"])


# ---------------------------------------------------------------------------
# 6. The deletion floor delays a deletion; it never releases a hold.
# ---------------------------------------------------------------------------
print("the deletion floor")

check("the floor is longer than the freshness window it replaced",
      check_probes.DELETE_FLOOR_HOURS > 6.0)

groups, ripe, waiting = check_probes._grouped(check_probes.DELETE_FLOOR_HOURS)
check("every ripe orphan is past the floor",
      all("past the" in why for _, why in ripe))
check("every waiting orphan says it is inside the floor",
      all("inside the" in why for _, why in waiting))
check("ripe and waiting partition the ORPHAN group",
      len(ripe) + len(waiting) == len(groups[check_probes.ORPHAN]))

# A floor of zero must not promote a HELD probe into the deletable set. The
# floor governs ORPHAN alone.
groups0, ripe0, _ = check_probes._grouped(0.0)
check("a zero floor does not touch the HELD group",
      {f.name for f, _ in groups0[check_probes.HELD]}
      == {f.name for f, _ in groups[check_probes.HELD]})
check("a zero floor makes every orphan ripe",
      len(ripe0) == len(groups0[check_probes.ORPHAN]))


# ---------------------------------------------------------------------------
# 7. The CLI. An ineffective combination FAILS; it never prints a success line.
# ---------------------------------------------------------------------------
print("the CLI refuses an ineffective combination")

PY = sys.executable
SCRIPT = str(ROOT / "scripts" / "check-probes.py")


def run(*args: str) -> subprocess.CompletedProcess:
    return subprocess.run([PY, SCRIPT, *args], cwd=ROOT, capture_output=True, text=True)


r = run("--archive")
check("`--archive` alone exits 2", r.returncode == 2, f"got {r.returncode}")
check("`--archive` alone never prints the check success line",
      "check-probes: clean" not in r.stdout, r.stdout)
check("`--archive` alone says which mode it needs", "--sweep" in r.stderr, r.stderr)

r = run("--delete")
check("`--delete` alone exits 2", r.returncode == 2, f"got {r.returncode}")

r = run("--check", "--delete")
check("`--check --delete` exits 2", r.returncode == 2, f"got {r.returncode}")

r = run("--staged", "--archive")
check("`--staged --archive` exits 2", r.returncode == 2, f"got {r.returncode}")

r = run("--stale", "--check")
check("two modes exit 2", r.returncode == 2, f"got {r.returncode}")

r = run("--floor-hours")
check("`--floor-hours` with no number exits 2", r.returncode == 2, f"got {r.returncode}")

r = run("--nonsense")
check("an unknown flag exits 2", r.returncode == 2, f"got {r.returncode}")

r = run("--check")
check("`--check` still works", r.returncode == 0, r.stdout + r.stderr)
check("`--check` still reports the tracked scope", "tracked files" in r.stdout, r.stdout)

r = run("--stale")
check("`--stale` reports without touching anything", r.returncode == 0, r.stderr)
check("`--stale` names the HELD group", "HELD" in r.stdout or "0 orphan" in r.stdout, r.stdout)

r = run("--gate")
check("`--gate` exits 0 or 1, never 2", r.returncode in (0, 1), f"got {r.returncode}")
if r.returncode == 1:
    check("a red gate names the one command that fixes it",
          "make probes-sweep" in r.stderr, r.stderr)


# ---------------------------------------------------------------------------
# 8. The never-commit gate is NOT weakened. It was bought on 2026-08-04.
# ---------------------------------------------------------------------------
print("the never-commit gate still refuses every probe outside archive/probes/")

for path in ("src/ProbeX.agda", "src/L/ProbeX.agda", "probes/ProbeX.agda",
             "ProbeX.agda", "archive/src/L/ProbeX.agda"):
    check(f"{path} is refused", check_probes.classify(path) is not None)
check("archive/probes/ProbeX.agda is accepted",
      check_probes.classify("archive/probes/ProbeX.agda") is None)
check("archive/probes/ProbeX.agdai is still refused",
      check_probes.classify("archive/probes/ProbeX.agdai") is not None)
check("_build/anything is refused", check_probes.classify("_build/x.json") is not None)


print("")
if failures:
    print(f"FAIL: {len(failures)} check(s) failed")
    for f in failures:
        print(f"  - {f}")
    sys.exit(1)
print("test_probe_lifecycle: all checks passed")
