#!/usr/bin/env python3
"""Regression tests for `scripts/check-premises-stated.py`.

WHY THIS FILE EXISTS. `[LJ-1.211]` measured that the briefs caused 8 of 10
DD25 overturns, and `[LJ-1.212]` built the gate its change 1 proposes: a
brief that carries a trigger token and no `## PREMISES` section with a basis
at `file:line` fails. These tests pin the four things that must never
silently invert:

1. A brief with a trigger and no declared premises FAILS, and the message
   names the token and shows the section's shape.
2. A brief with a trigger and a `## PREMISES` section with a basis PASSES.
3. The escapes stay NARROW: a heading with no basis fails, a prose mention
   does not satisfy, a basis outside the section does not satisfy, and the
   four REFUSED tokens do not fire the gate.
4. The real tree exits 0 after grandfathering, and the 28-brief backlog is
   counted and reported, never failed.

Run: `python3 scripts/tests/test_premises_stated.py`
"""

from __future__ import annotations

import importlib.util
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent.parent
spec = importlib.util.spec_from_file_location(
    "check_premises_stated", ROOT / "scripts" / "check-premises-stated.py"
)
cps = importlib.util.module_from_spec(spec)
spec.loader.exec_module(cps)

failures: list[str] = []


def check(name: str, condition: bool, detail: str = "") -> None:
    if condition:
        print(f"  ok    {name}")
    else:
        print(f"  FAIL  {name}{(': ' + detail) if detail else ''}")
        failures.append(name)


PY = sys.executable
SCRIPT = str(ROOT / "scripts" / "check-premises-stated.py")

# A snippet that carries each ACTIVE token, and one that carries each
# REFUSED token without any ACTIVE token.
ACTIVE_SNIPPETS = {
    "the gate is": "the gate is 40 lines",
    "GO needs": "GO needs both",
    "NO-GO is": "NO-GO is either",
    "the only lever": "the only lever is cost",
    "shapes": "price these shapes",
    "measure it, do not argue it": "measure it, do not argue it",
    "a figure with a unit": "40 lines or fewer",
}
REFUSED_SNIPPETS = {
    "section": "read section 4 of the review",
    "a LESSONS law ID": "P-u binds the move",
    "a figure with a unit": "the wing is 2677 lines today",
    "do not weaken": "do not weaken the statement",
}


def write_briefs(root: Path, files: dict[str, str]) -> Path:
    """Write `files` as <code>/<code>.md under root/tasks; return root/tasks."""
    tasks = root / "tasks"
    for code, text in files.items():
        d = tasks / code
        d.mkdir(parents=True, exist_ok=True)
        (d / f"{code}.md").write_text(text, encoding="utf-8")
    return tasks


def run(*args: str) -> subprocess.CompletedProcess:
    return subprocess.run([PY, SCRIPT, *args], cwd=ROOT,
                          capture_output=True, text=True)


PREMISED = (
    "## GOAL\n"
    "Build the thing. GO needs both halves.\n"
    "## PREMISES\n"
    "- the applications collapse at three depths, at "
    "agents/tasks/archive/LJ-1-66/lj-1.66-review.md:230-258\n"
    "## ARCHIVE\n"
    "none\n")

EMPTY_PREMISES = (
    "## GOAL\n"
    "Build the thing. GO needs both halves.\n"
    "## PREMISES\n"
    "- the applications collapse\n"
    "## ARCHIVE\n"
    "none\n")

PROSE_PREMISES = (
    "## GOAL\n"
    "Build the thing. GO needs both halves. These premises are load-bearing.\n"
    "## ARCHIVE\n"
    "none\n")

NO_TRIGGER = (
    "## GOAL\n"
    "Write the report and leave the tree alone.\n"
    "## ARCHIVE\n"
    "none\n")


# ---------------------------------------------------------------------------
# 1. THE DEFECT FAILS.
# ---------------------------------------------------------------------------
print("the defect fails")

with tempfile.TemporaryDirectory() as td:
    tasks = write_briefs(Path(td), {
        "LJ-9-99": "## GOAL\nBuild the thing. NO-GO is a full deliverable.\n",
    })
    rs = run("--tasks", str(tasks))
    check("a trigger with no PREMISES makes the run red", rs.returncode == 1,
          f"got {rs.returncode}: {rs.stdout} {rs.stderr}")
    check("the red names the brief", "LJ-9-99" in rs.stderr)
    check("the red names the token", "NO-GO is" in rs.stderr)
    check("the red shows the section shape", "## PREMISES" in rs.stderr)
    check("the red says what to write", "file:line" in rs.stderr)

check("every ACTIVE token fires on its own snippet",
      all(token in cps.trigger_hits(snippet)
          for token, snippet in ACTIVE_SNIPPETS.items()))
check("every REFUSED token does not fire the gate",
      all(cps.trigger_hits(snippet) == []
          for snippet in REFUSED_SNIPPETS.values()))
check("the table holds 7 ACTIVE and 4 REFUSED rows",
      len([r for r in cps.TRIGGER if r[2]]) == 7
      and len([r for r in cps.TRIGGER if not r[2]]) == 4)


# ---------------------------------------------------------------------------
# 2. THE FIX PASSES.
# ---------------------------------------------------------------------------
print("declared premises clear")

with tempfile.TemporaryDirectory() as td:
    tasks = write_briefs(Path(td), {"LJ-9-99": PREMISED})
    rs = run("--tasks", str(tasks))
    check("a trigger with a PREMISES section and a basis passes",
          rs.returncode == 0, f"{rs.stdout} {rs.stderr}")

with tempfile.TemporaryDirectory() as td:
    tasks = write_briefs(Path(td), {"LJ-9-99": NO_TRIGGER})
    rs = run("--tasks", str(tasks))
    check("a brief with no trigger passes without a PREMISES section",
          rs.returncode == 0, f"{rs.stdout} {rs.stderr}")


# ---------------------------------------------------------------------------
# 3. THE ESCAPES STAY NARROW.
# ---------------------------------------------------------------------------
print("the escapes stay narrow")

with tempfile.TemporaryDirectory() as td:
    tasks = write_briefs(Path(td), {"LJ-9-99": EMPTY_PREMISES})
    rs = run("--tasks", str(tasks))
    check("a PREMISES heading with no basis fails", rs.returncode == 1,
          f"got {rs.returncode}: {rs.stdout} {rs.stderr}")
    check("the message names the missing basis", "no basis" in rs.stderr)

with tempfile.TemporaryDirectory() as td:
    tasks = write_briefs(Path(td), {"LJ-9-99": PROSE_PREMISES})
    rs = run("--tasks", str(tasks))
    check("a prose mention of premises does not satisfy",
          rs.returncode == 1, f"got {rs.returncode}: {rs.stdout} {rs.stderr}")

with tempfile.TemporaryDirectory() as td:
    outside = (
        "## GOAL\n"
        "Build the thing. GO needs both halves.\n"
        "## PREMISES\n"
        "- the applications collapse\n"
        "## ARCHIVE\n"
        "the basis sits here: agents/tasks/LJ-1-93/LJ-1.93.md:12\n")
    tasks = write_briefs(Path(td), {"LJ-9-99": outside})
    rs = run("--tasks", str(tasks))
    check("a basis outside the PREMISES section does not satisfy",
          rs.returncode == 1, f"got {rs.returncode}: {rs.stdout} {rs.stderr}")

check("a basis matches the project's file:line shapes",
      cps.BASIS.search("dev/PLAN.md:624") is not None
      and cps.BASIS.search("scripts/dd25-record.py:40") is not None
      and cps.BASIS.search("src/L/Coding/Model.lagda.md:667-678") is not None)


# ---------------------------------------------------------------------------
# 4. THE REAL TREE, VIA THE CLI.
# ---------------------------------------------------------------------------
print("the real tree")

rs = run()
check("the real tree exits 0 after grandfathering", rs.returncode == 0,
      rs.stderr[-400:])
check("the run prints the backlog count",
      f"{len(cps.PRE_EPOCH)} frozen pre-epoch" in rs.stdout, rs.stdout)
check("the run reports 0 new defects", "0 new defects" in rs.stdout)
check("the frozen briefs are reported, not failed",
      "LJ-1-212" in rs.stdout and "no ## PREMISES section" not in rs.stdout)

with tempfile.TemporaryDirectory() as td:
    tasks = write_briefs(Path(td), {
        "LJ-1-93": "## GOAL\nBuild. the gate is open.\n",
    })
    rs = run("--tasks", str(tasks))
    check("a firing brief in a pre-epoch directory is backlog, not defect",
          rs.returncode == 0, f"got {rs.returncode}: {rs.stdout} {rs.stderr}")
    check("the backlog is counted", "1 frozen pre-epoch" in rs.stdout)


print("")
if failures:
    print(f"FAIL: {len(failures)} check(s) failed")
    for f in failures:
        print(f"  - {f}")
    sys.exit(1)
print("test_premises_stated: all checks passed")
