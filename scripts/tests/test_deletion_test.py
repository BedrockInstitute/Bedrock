#!/usr/bin/env python3
"""Regression tests for the deletion test tool.

WHY THIS FILE EXISTS. The deletion test is D36's judgment. Its shadow count
must equal the ledger's own ac-total, or the two calibers drift apart
silently and the daily proxy stops describing the landing test. [T147] ran
the real test once by hand; the hand-run cannot be re-checked. This file
pins the shadow count to `ledger.py --trophy-split`, and pins the --run
guards so a future edit cannot silently arm the expensive path.

Run: `python3 scripts/tests/test_deletion_test.py`
"""

from __future__ import annotations

import contextlib
import importlib.util
import io
import re
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent.parent
spec = importlib.util.spec_from_file_location(
    "deletion_test", ROOT / "scripts" / "deletion-test.py"
)
deletion_test = importlib.util.module_from_spec(spec)
assert spec.loader is not None
spec.loader.exec_module(deletion_test)

AC_TOTAL_RE = re.compile(r"ac-total ([0-9,]+)")
CAP_HEADROOM_RE = re.compile(r"cap ([0-9,]+) \| headroom ([+-][0-9,]+)")
PROG = "deletion-test.py"


def check(name: str, got, want) -> int:
    ok = got == want
    print(f"  {'ok  ' if ok else 'FAIL'} {name}")
    if not ok:
        print(f"       want: {want!r}\n       got:  {got!r}")
    return 0 if ok else 1


def shadow_line() -> tuple[str, int]:
    out = io.StringIO()
    with contextlib.redirect_stdout(out):
        rc = deletion_test.main([PROG, "--shadow"])
    lines = [line for line in out.getvalue().splitlines()
             if line.startswith("deletion test | shadow")]
    return (lines[0] if lines else "", rc)


def test_shadow_matches_ledger() -> int:
    """The shadow count equals `ledger.py --trophy-split`'s own ac-total.
    This is the drift guard: the two calibers cannot diverge silently."""
    line, rc = shadow_line()
    fails = check("shadow mode exits clean", rc, 0)
    probe = subprocess.run(
        [sys.executable, str(ROOT / "scripts" / "ledger.py"),
         "--trophy-split"],
        cwd=ROOT, capture_output=True, text=True)
    fails += check("ledger --trophy-split exits clean", probe.returncode, 0)
    mine = AC_TOTAL_RE.search(line)
    theirs = AC_TOTAL_RE.search(probe.stdout)
    fails += check("both figures parse", mine is not None and theirs is not None,
                   True)
    if mine and theirs:
        fails += check(
            "shadow ac-total equals ledger ac-total",
            int(mine.group(1).replace(",", "")),
            int(theirs.group(1).replace(",", "")))
    return fails


def test_shadow_reports_cap_and_headroom() -> int:
    """The cap comes from the ledger declaration and the headroom is its
    arithmetic. A cap that vanished would fail the tool, not just the test."""
    line, rc = shadow_line()
    fails = check("shadow exits clean", rc, 0)
    mine = AC_TOTAL_RE.search(line)
    band = CAP_HEADROOM_RE.search(line)
    fails += check("cap and headroom parse",
                   mine is not None and band is not None, True)
    if mine and band:
        count = int(mine.group(1).replace(",", ""))
        cap = int(band.group(1).replace(",", ""))
        headroom = int(band.group(2).replace(",", ""))
        fails += check("cap is the D36 cap", cap, 16000)
        fails += check("headroom is cap minus the count",
                       headroom, cap - count)
    return fails


def test_ac_set_shape() -> int:
    """The AC-side set is the surviving tree's base + ac-only + shared,
    honoring gch_assign: no gch-side master, no retired master, and the
    tree index stays counted but leaves the --run import root."""
    st = deletion_test.shadow_state()
    ac = set(st["ac_files"])
    gch = set(st["gch_files"])
    fails = check("ac and gch sets are disjoint", ac & gch, set())
    data = st["data"]
    files = deletion_test.ledger.tracked_masters()
    buckets, _ = deletion_test.ledger.retiring(files, data)
    retired = {f for hit in buckets.values() for f in hit}
    fails += check("no retired master is in the AC-side set", ac & retired,
                   set())
    fails += check("declared gch-assign masters are gch-side",
                   "src/FOL/Count.lagda.md" in gch
                   and "src/V/Collapse.lagda.md" in gch, True)
    fails += check("Everything is counted in the AC side",
                   deletion_test.EVERYTHING in ac, True)
    fails += check("Everything leaves the --run import root",
                   deletion_test.run_root_files(st),
                   [f for f in st["ac_files"] if f != deletion_test.EVERYTHING])
    return fails


def test_shadow_files_lists_ac_side() -> int:
    """`--files` prints one row per AC-side master, split by its part."""
    out = io.StringIO()
    with contextlib.redirect_stdout(out):
        rc = deletion_test.main([PROG, "--shadow", "--files"])
    rows = [line for line in out.getvalue().splitlines() if "\t" in line]
    st = deletion_test.shadow_state()
    fails = check("--files exits clean", rc, 0)
    fails += check("--files lists one row per AC-side master",
                   len(rows), len(st["ac_files"]))
    fails += check("--files lists base, ac-only and shared",
                   {row.split("\t")[0] for row in rows},
                   {"base", "ac_only", "shared"})
    return fails


def test_run_refuses_without_yes() -> int:
    """The first guard: --run without --yes refuses before any worktree or
    typecheck, and prints the expected cost."""
    out = io.StringIO()
    err = io.StringIO()
    with contextlib.redirect_stdout(out), contextlib.redirect_stderr(err):
        rc = deletion_test.main([PROG, "--run"])
    fails = check("--run without --yes refuses", rc, 1)
    fails += check("refusal names --yes", "--yes" in err.getvalue(), True)
    fails += check("refusal prints the expected cost",
                   "expected cost" in out.getvalue().lower(), True)
    return fails


def test_run_refuses_when_agda_live() -> int:
    """The second guard: a live Agda process blocks the run. The process
    probe is stubbed because the guard must be testable without Agda."""
    saved = deletion_test.agda_blocker
    deletion_test.agda_blocker = lambda: "another Agda process is live."
    try:
        out = io.StringIO()
        err = io.StringIO()
        with contextlib.redirect_stdout(out), contextlib.redirect_stderr(err):
            rc = deletion_test.main([PROG, "--run", "--yes"])
    finally:
        deletion_test.agda_blocker = saved
    fails = check("--run --yes refuses when Agda is live", rc, 1)
    fails += check("refusal names the live process",
                   "another Agda process" in err.getvalue(), True)
    return fails


def test_run_refuses_when_pgrep_cannot_verify() -> int:
    """The fail-closed half of the guard: a pgrep that cannot see the
    process list must refuse, never guess that the tree is clear."""
    saved = deletion_test.agda_blocker
    deletion_test.agda_blocker = (
        lambda: "pgrep cannot verify the process list "
                "(pgrep: Cannot get process list). The guard fails closed.")
    try:
        out = io.StringIO()
        err = io.StringIO()
        with contextlib.redirect_stdout(out), contextlib.redirect_stderr(err):
            rc = deletion_test.main([PROG, "--run", "--yes"])
    finally:
        deletion_test.agda_blocker = saved
    fails = check("--run --yes refuses when pgrep cannot verify", rc, 1)
    fails += check("refusal fails closed",
                   "fails closed" in err.getvalue(), True)
    return fails


def main() -> int:
    fails = 0
    for test in (test_shadow_matches_ledger, test_shadow_reports_cap_and_headroom,
                 test_ac_set_shape, test_shadow_files_lists_ac_side,
                 test_run_refuses_without_yes, test_run_refuses_when_agda_live,
                 test_run_refuses_when_pgrep_cannot_verify):
        fails += test()
    print(f"\n{'PASS' if fails == 0 else 'FAIL'}: {fails} failing check(s)")
    return 1 if fails else 0


if __name__ == "__main__":
    sys.exit(main())
