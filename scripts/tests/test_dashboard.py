#!/usr/bin/env python3
"""Regression tests for the owner's dashboard generator.

WHY THIS FILE EXISTS. The dashboard is generated from canonical data on
purpose, so a parser bug does not fail a gate the way a handwritten page
would; it silently renders a wrong number on the owner's board. These tests
pin the parsing and staleness behavior that must keep working. The same
standalone shape as scripts/tests/test_obligations.py.

Run: `python3 scripts/tests/test_dashboard.py`
"""

from __future__ import annotations

import importlib.util
import os
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent.parent
spec = importlib.util.spec_from_file_location(
    "dashboard", ROOT / "scripts" / "dashboard.py"
)
dashboard = importlib.util.module_from_spec(spec)
assert spec.loader is not None
spec.loader.exec_module(dashboard)


def check(name: str, got, want) -> int:
    ok = got == want
    print(f"  {'ok  ' if ok else 'FAIL'} {name}")
    if not ok:
        print(f"       want: {want!r}\n       got:  {got!r}")
    return 0 if ok else 1


def test_brief_parse() -> int:
    line = ("standing 18,464 | endpoint 24.95-31.18k naive, "
            "31.60-47.18k calibrated | naive corner +6.18k against the 25k reference")
    d = dashboard.parse_brief(line)
    fails = check("parse_brief standing", d["standing"], 18464)
    fails += check("parse_brief naive band",
                   (d["naive_low_k"], d["naive_high_k"]), (24.95, 31.18))
    fails += check("parse_brief calibrated band",
                   (d["calibrated_low_k"], d["calibrated_high_k"]), (31.60, 47.18))
    return fails


def test_mermaid() -> int:
    body = ("flowchart TD\n    A[\"a slot is free\"] --> B{\"freeze?\"}\n")
    text = "prose\n\n```mermaid\n" + body + "```\n\nmore\n"
    fails = check("extract_mermaid lifts the flowchart block",
                  dashboard.extract_mermaid(text), body)
    fails += check("extract_mermaid None when absent",
                   dashboard.extract_mermaid("no fence here"), None)
    fails += check("extract_mermaid ignores a non-flowchart mermaid block",
                   dashboard.extract_mermaid("```mermaid\ngraph LR\nA --> B\n```"), None)
    return fails


def test_plan_parsing() -> int:
    plan = """## 11. MASTER status table (live)

| Code | Goal | Status |
|---|---|---|
| L0 | Legislation (standing track) | ACTIVE (initial gate cleared) |
| L3 | Technical layer | ACTIVE |
| L3.0 | Internalization theorem | DONE |
| L3.0.1 | Two-instance proof | DONE |
| L3.32-F5 | The worst part first | ANSWERED |
| L4 | Convergence | PLANNED |

### Task index (one row per dispatch, §6.0 rules 7 and 8)

| Code | Task | Verdict | Detail |
|---|---|---|---|
| L3.32-T110 | Maintenance mechanism | IN PROGRESS | `_build/l3.32-t110-report.md` |
| L3.32-T111 | Task index | IN PROGRESS | `_build/l3.32-t111-report.md` |
| L3.32-T112 | Goal table discipline | DELIVERED | `_build/l3.32-t112-report.md` |

### Bookkeeping
"""
    masters = dashboard.master_rows(plan)
    tasks = dashboard.task_rows(plan)
    fails = check("master_rows parses all six goal rows", len(masters), 6)
    fails += check("master row code and status", (masters[0]["code"], masters[0]["status"]),
                   ("L0", "ACTIVE (initial gate cleared)"))
    fails += check("task_rows parses all three rows", len(tasks), 3)
    fails += check("task row verdict", tasks[2]["verdict"], "DELIVERED")
    fails += check("hierarchy roots are the top-level codes",
                   dashboard.hierarchy(masters)["roots"], ["L0", "L3", "L4"])
    tree = dashboard.hierarchy(masters)
    fails += check("hierarchy nests dotted and dash codes under L3",
                   sorted(tree["children"]["L3"]), ["L3.0", "L3.32.F5"])
    fails += check("status_class flags ACTIVE as now",
                   dashboard.status_class("ACTIVE (initial gate cleared)"), "now")
    fails += check("status_class flags DONE as done",
                   dashboard.status_class("DONE"), "done")
    fails += check("status_class flags PLANNED as planned",
                   dashboard.status_class("PLANNED"), "planned")
    fails += check("status_class folds REGISTERED-then-DONE to done",
                   dashboard.status_class("**REGISTERED 2026-07-27** ... DONE the same day"), "done")
    fails += check("status_class keeps a bare REGISTERED row as planned",
                   dashboard.status_class("**REGISTERED 2026-08-04 by owner direction**"), "planned")
    fails += check("status_class flags RULED AND ACTIVE as now",
                   dashboard.status_class("**RULED AND ACTIVE 2026-08-04**"), "now")
    return fails


def test_remaining_rows() -> int:
    data = {"remaining": [
        {"id": "W3", "title": "Face route", "naive_low": 1000, "naive_high": 2700,
         "calibrated_low": 3000, "calibrated_high": 7900, "klass": "x3", "gate": "none"},
        {"id": "W1p", "title": "Transfers", "naive_low": 700, "naive_high": 1720,
         "calibrated_low": 1900, "calibrated_high": 5000, "klass": "x1.3", "gate": "T54"},
    ]}
    rows = dashboard.remaining_rows(data)
    return (
        check("remaining_rows count", len(rows), 2)
        + check("remaining_rows band text", rows[0]["naive"], "1,000-2,700")
        + check("remaining_rows calibrated text", rows[1]["calibrated"], "1,900-5,000")
    )


def test_brief_naming() -> int:
    fails = check("report_for_brief resolves the exact code",
                  dashboard.report_for_brief("l3.32-t112-brief.md"),
                  ROOT / "_build" / "l3.32-t112-report.md")
    fails += check("report_for_brief skips non-task briefs",
                   dashboard.report_for_brief("geology-legacy-brief.md"), None)
    return fails


def test_clean() -> int:
    return check("clean removes the banned em dash",
                 dashboard.clean("cold start\u2014measured"), "cold start-measured")


def test_staleness() -> int:
    """Staleness against the real repository sources: a page stamped after
    every source is fresh, a page stamped before them all is stale on every
    source, and a missing page reports as stale-by-definition."""
    with tempfile.TemporaryDirectory() as td:
        out = Path(td) / "dashboard.html"
        out.write_text("", encoding="utf-8")
        all_labels = [label for label, _ in dashboard.source_stamps()]
        os.utime(out, (2_000_000_000, 2_000_000_000))  # 2033: after every 2026 source
        fails = check("stale_sources empty when the page is newer than every source",
                      dashboard.stale_sources(out), [])
        os.utime(out, (1, 1))  # 1970: before every source
        fails += check("stale_sources names every source when all are newer",
                       dashboard.stale_sources(out), all_labels)
        out.unlink()
        fails += check("stale_sources reports a missing page as stale",
                       len(dashboard.stale_sources(out)), len(all_labels))
    return fails


def main() -> int:
    fails = 0
    for test in (test_brief_parse, test_mermaid, test_plan_parsing,
                 test_remaining_rows, test_brief_naming, test_clean, test_staleness):
        fails += test()
    print(f"\n{'PASS' if fails == 0 else 'FAIL'}: {fails} failing check(s)")
    return 1 if fails else 0


if __name__ == "__main__":
    sys.exit(main())
