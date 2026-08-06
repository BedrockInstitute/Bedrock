#!/usr/bin/env python3
"""Regression tests for the dev/ maintenance checker.

WHY THIS FILE EXISTS. Every case below is either a defect that was once live
(the 12,634-word PLAN cell, the 3,450-word AGENTS.md, the imported playbook
that sat unrouted for five days, the stale section 0 date) or a wolf the
checker itself flagged on its first run and had to be tuned away (C-21,
ordinary code prose that read as an import marker). `scripts/obligations.py`'s
docstring names the precedent: a claim of test coverage made in prose but
never written down is a false claim, so these are real cases, runnable.

Run: `python3 scripts/tests/test_dev_docs.py`
"""

from __future__ import annotations

import importlib.util
import re
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent.parent
spec = importlib.util.spec_from_file_location(
    "check_dev_docs", ROOT / "scripts" / "check-dev-docs.py"
)
check = importlib.util.module_from_spec(spec)
spec.loader.exec_module(check)


def words(n: int) -> str:
    return " ".join(["w"] * n)


def plan_row(rid: str, body: str) -> str:
    return f"| {rid} | {body} |\n"


def flagged(fn, *args) -> bool:
    return bool(fn(*args))


def memo_dir(content: str) -> Path:
    d = Path(tempfile.mkdtemp())
    (d / "memo.md").write_text(content, encoding="utf-8")
    return d


EMPTY_RULES = {"bundle": {}, "triggers": {}}
ROUTED_RULES = {"bundle": {"probe": {"ids": ["P-i"]}}, "triggers": {}}

CASES = [
    # --- the historical failure states must fire ---
    (lambda: flagged(check.check_agents_size, words(3450)),
     "AGENTS.md at the pre-slim 3,450 words must be over the cap"),
    (lambda: flagged(check.check_plan_cells, plan_row("L3.32", words(12634))),
     "the 12,634-word L3.32 cell must be over the cell cap"),
    (lambda: flagged(check.check_section0_date,
                     "## 0. Where the work stands (2026-08-04)\n\n"
                     "in flight (2026-08-06)\n"),
     "a section 0 heading older than its own body must fire"),
    (lambda: flagged(check.check_imported_routing,
                     "### P-i. The conversion-explosion playbook (imported "
                     "from the source project)\n", EMPTY_RULES),
     "an imported entry with no routing must fire"),

    # --- the boundary: at the cap is clean, one over fires ---
    (lambda: not flagged(check.check_agents_size, words(2200)),
     "AGENTS.md at exactly 2,200 words is clean"),
    (lambda: flagged(check.check_agents_size, words(2201)),
     "AGENTS.md one word over 2,200 fires"),
    (lambda: not flagged(check.check_plan_cells, plan_row("D28", words(1600))),
     "a cell at exactly 1,600 words is clean"),
    (lambda: flagged(check.check_plan_cells, plan_row("D28", words(1601))),
     "a cell one word over 1,600 fires"),

    # --- the current tree's shapes must stay clean (no wolves) ---
    (lambda: not flagged(check.check_agents_size, words(1784)),
     "the current 1,784-word AGENTS.md is clean"),
    (lambda: not flagged(check.check_plan_cells,
                         plan_row("L3.32-F5", words(1125))),
     "the current largest cell (1,125 words) is clean"),
    (lambda: not flagged(check.check_section0_date,
                         "## 0. Where the work stands (2026-08-06)\n\n"
                         "ruled 2026-08-04\n"),
     "a heading as new as its body is clean"),
    (lambda: not flagged(check.check_imported_routing,
                         "### C-21. Telescope types may only use level-generic "
                         "imported names\n", EMPTY_RULES),
     "C-21's 'imported names' is code prose, not an import marker "
     "(the first-version wolf)"),
    (lambda: not flagged(check.check_imported_routing,
                         "### P-i. The conversion-explosion playbook (imported "
                         "from the source project)\n", ROUTED_RULES),
     "an imported entry that IS routed is clean"),
    (lambda: flagged(check.check_section0_date, "## 1. No section zero\n"),
     "PLAN with no section 0 is a finding, not a crash"),

    # --- memo status form ---
    (lambda: not flagged(check.check_memo_status, memo_dir(
        "> **STATUS: the diagnosis below is WRONG and the mechanism is NOT "
        "BUILT.**\n")),
     "a STATUS header stating a verdict is clean"),
    (lambda: flagged(check.check_memo_status,
                     memo_dir("> **STATUS: see the follow-up report.**\n")),
     "a STATUS header with no verdict word fires"),
    (lambda: not flagged(check.check_memo_status, memo_dir("plain memo\n")),
     "a memo with no STATUS header is untouched (form-when-present)"),

    # --- AGENTS enforcement table names real scripts ---
    (lambda: not flagged(check.check_agents_enforcers,
                         "| x | `scripts/ledger.py` |\n"),
     "a named enforcer that exists is clean"),
    (lambda: flagged(check.check_agents_enforcers,
                     "| x | `scripts/nope.py` |\n"),
     "a named enforcer that does not exist fires"),

    # --- the sweep's pure pieces ---
    (lambda: bool(re.search(r"(?<![\w-])" + check._cite_pattern("D-2") +
                            r"(?![\w-])", "PLAN cites D2 here")),
     "the D-2 citation pattern also matches the PLAN-style D2"),
    (lambda: not re.search(r"(?<![\w-])" + check._cite_pattern("D-2") +
                           r"(?![\w-])", "decision D-20 is a different thing"),
     "the D-2 pattern does not match inside D-20"),
    (lambda: bool(check.sweep_cells("## 11.\n" +
                                    plan_row("L3.32-F5", words(700)))),
     "a section 11 cell over 600 words is listed by the sweep"),
    (lambda: not check.sweep_cells("## 11.\n" +
                                   plan_row("L3.32-F5", words(500))),
     "a section 11 cell under 600 words is not listed"),
]


def main() -> int:
    failures = 0
    for run, why in CASES:
        try:
            ok = run()
        except Exception as exc:  # a crash is a failure, reported plainly
            ok, why = False, f"{why} (crashed: {exc})"
        failures += not ok
        print(f"  {'ok  ' if ok else 'FAIL'}  {why}")
    print(f"\n{len(CASES) - failures}/{len(CASES)} passed")
    return 1 if failures else 0


if __name__ == "__main__":
    sys.exit(main())
