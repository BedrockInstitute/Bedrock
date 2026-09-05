#!/usr/bin/env python3
"""Regression tests for the task-index checker.

WHY THIS FILE EXISTS. A first draft of the rule-id checker flagged
`T-function`, `I-ideal` and `D-bucket`: ordinary English with a capital, and
its author drew the conclusion that a checker firing on prose gets disabled.
`T<n>` is even more collision-prone, so the extraction here is pinned by
tests: only bracket-enclosed tokens are codes, bare `T88` and every
capital-letter-hyphen prose shape stay silent, and a real tree regression
either duplicates a row, drops a cited code, or pushes a row past the cap.

Run: `python3 scripts/tests/test_task_index.py`
"""

from __future__ import annotations

import importlib.util
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent.parent
spec = importlib.util.spec_from_file_location(
    "check_task_index", ROOT / "scripts" / "gate/check-task-index.py"
)
check_task_index = importlib.util.module_from_spec(spec)
spec.loader.exec_module(check_task_index)

PLAN = """## 11. MASTER status table (live)

| L3.32-T2 | This row lives OUTSIDE the task index and must be ignored | x |

### Task index (one row per dispatch, section 6.0 rules 7 and 8)

| Code | Task | Verdict | Detail |
|---|---|---|---|
| L3.32-T1 | The R4 corrective stop | DELIVERED | dev/JOURNAL.md |
| L3.32-T88 | Measure SquareLaw's 856 s | COMPLETE | agents/tasks/archive/L3-32-T88/l3.32-t88-report.md |

### Bookkeeping
"""


def fails():
    failures = 0

    def check(name, got, want):
        nonlocal failures
        ok = got == want
        failures += not ok
        print(f"  {'ok  ' if ok else 'FAIL'} {name}: want {want!r} got {got!r}")

    # --- extraction: the trap, pinned ---
    check("bare T88 is not a code",
          check_task_index.extract_codes("T88 without brackets is prose"),
          set())
    check("capital-hyphen prose is not a code",
          check_task_index.extract_codes("T-function, I-ideal, D-bucket"),
          set())
    # SINCE THE LJ RENUMBERING the key is a string code, not an int: two live
    # series share numbers, so `LJ-1.1` and `L3.32-T1` must not collide.
    check("short form extracts",
          check_task_index.extract_codes("see [T88] for the measurement"),
          {"T88"})
    check("full form extracts",
          check_task_index.extract_codes("dispatched as [L3.32-T101]"),
          {"T101"})
    check("mixed forms union",
          check_task_index.extract_codes("[L3.32-T101] then [T1], and [T88]"),
          {"T101", "T1", "T88"})
    check("zero-padded full form resolves to the same code",
          check_task_index.extract_codes("[L3.32-T01]"),
          {"T1"})
    check("the two series do not collide",
          check_task_index.extract_codes("[LJ-1.1] and [L3.32-T1]"),
          {"LJ-1.1", "T1"})

    # --- index parsing ---
    # archived=False isolates the parser from the retired-series file, which
    # the checker folds in for every real caller.
    rows = check_task_index.index_rows(PLAN, archived=False)
    check("index rows parsed", [key for _, key, _ in rows], ["T1", "T88"])
    check("rows outside the section ignored", len(rows), 2)
    check("missing section yields no rows",
          check_task_index.index_rows("## 11. MASTER status table\nno index\n",
                                      archived=False),
          [])

    # --- the three failure modes ---
    missing_src = "a citation [T5] with no row"
    errs, cited, unique = check_task_index.check_index(PLAN, missing_src, archived=False)
    # The key is series-neutral since the renumbering: `[T5]` is searched in
    # BOTH indexes, so the message names the key and both places.
    check("cited code without a row fails",
          any("T5" in e and "no index row" in e for e in errs), True)
    check("the failure names both indexes",
          any("TASKS-archived" in e and "PLAN.md" in e for e in errs), True)

    duplicate_plan = PLAN.replace(
        "| L3.32-T88 | Measure SquareLaw's 856 s | COMPLETE | agents/tasks/archive/L3-32-T88/l3.32-t88-report.md |",
        "| L3.32-T88 | first copy | A | x |\n| L3.32-T88 | second copy | B | y |")
    errs, _, _ = check_task_index.check_index(duplicate_plan, "[T88]", archived=False)
    check("duplicate rows fail",
          any("duplicate index row" in e and "L3.32-T88" in e for e in errs), True)

    def make_row(detail: str) -> str:
        return f"| L3.32-T88 | Measure SquareLaw's 856 s | COMPLETE | `{detail}` |"

    over = "x" * (check_task_index.CAP - len(make_row("")) + 1)
    long_plan = PLAN.replace(
        "| L3.32-T88 | Measure SquareLaw's 856 s | COMPLETE | agents/tasks/archive/L3-32-T88/l3.32-t88-report.md |",
        make_row(over))
    errs, _, _ = check_task_index.check_index(long_plan, "[T88]", archived=False)
    check("row over cap fails",
          any("row over cap" in e and "L3.32-T88" in e for e in errs), True)

    at_cap = "x" * (check_task_index.CAP - len(make_row("")))
    cap_plan = PLAN.replace(
        "| L3.32-T88 | Measure SquareLaw's 856 s | COMPLETE | agents/tasks/archive/L3-32-T88/l3.32-t88-report.md |",
        make_row(at_cap))
    errs, _, _ = check_task_index.check_index(cap_plan, "[T88]", archived=False)
    check("row at exactly the cap passes", errs == [], True)

    # --- integration smoke: the real tree must be green ---
    plan_text = (ROOT / "dev" / "PLAN.md").read_text(encoding="utf-8")
    errs, cited, unique = check_task_index.check_index(
        plan_text, check_task_index.scanned_texts())
    print(f"  real tree: {cited} cited codes, {unique} unique rows, "
          f"{len(errs)} defect(s)")
    check("real tree is green", errs, [])

    print(f"\n{14 - failures}/{14} checks passed")
    return 1 if failures else 0


if __name__ == "__main__":
    sys.exit(fails())
