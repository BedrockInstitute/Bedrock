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


def walk_route(node: dict, found=None) -> list[dict]:
    """Every node of a route tree, depth first."""
    if found is None:
        found = []
    found.append(node)
    for e in node.get("edges", []):
        walk_route(e["to"], found)
    return found


def test_route_builder() -> int:
    """The route tree is built from the ledger: the campaign branch plus the
    lever branch, each leaf populated from the lever rows, and acyclic."""
    data = {
        "owed": [{"id": "bridge-landing", "status": "frozen"}],
        "lever": [
            {"id": "B-condensation-story", "status": "REFUTED 2026-08-06"},
            {"id": "D-order-core", "status": "PARTLY SUPERSEDED 2026-08-06"},
            {"id": "X-gated", "status": "priced at 3x", "gated": True},
            {"id": "rewrite-worst", "status": "GATE GREEN 2026-08-06 RULED"},
            {"id": "A-level-kit", "status": ""},
        ],
    }
    tree = dashboard.build_route(data)
    fails = check("route tree has both branches",
                  sorted(tree), ["campaign", "lever"])
    nodes = walk_route(tree["campaign"]) + walk_route(tree["lever"])

    def leaf_of(head: str):
        for n in nodes:
            if (n["kind"] == "outcome" and n["label"]
                    and n["label"][0].startswith(head)):
                return n.get("leaves")
        return None

    fails += check("NOT A ROUTE leaf is the refuted lever",
                   leaf_of("NOT A ROUTE"), ["B-condensation-story"])
    fails += check("RE-PRICE FIRST leaf is the superseded lever",
                   leaf_of("RE-PRICE FIRST"), ["D-order-core"])
    fails += check("PROBE FIRST leaf is the gated lever",
                   leaf_of("D22: PROBE FIRST"), ["X-gated"])
    fails += check("KEEP AND WAIT leaf is the waiting lever",
                   leaf_of("KEEP AND WAIT"), ["A-level-kit"])
    fails += check("already-in-route leaf is the ruled lever",
                   leaf_of("already in the route"), ["rewrite-worst"])
    freeze = tree["campaign"]["edges"][0]["to"]
    fails += check("freeze is a decision node", freeze["kind"], "decision")
    fails += check("freeze splits no/yes",
                   [e["label"] for e in freeze["edges"]], ["no", "yes"])
    fails += check("route tree is acyclic",
                   len(nodes), len({id(n) for n in nodes}))
    return fails


def test_route_block_real() -> int:
    """route_block() against the real ledger: same shape as the unit tree,
    with the ledger named as the panel's source."""
    tree, path, note = dashboard.route_block()
    fails = check("route_block names dev/ledger.toml as the source",
                  path, dashboard.LEDGER_TOML)
    fails += check("route_block tree has both branches",
                   sorted(tree or {}), ["campaign", "lever"])
    return fails


def test_route_block_no_data() -> int:
    """A missing ledger must say so on the panel, not crash the generator."""
    saved = dashboard.LEDGER_TOML
    dashboard.LEDGER_TOML = Path("/nonexistent/ledger.toml")
    try:
        tree, path, note = dashboard.route_block()
    finally:
        dashboard.LEDGER_TOML = saved
    fails = check("route_block reports no data instead of crashing",
                  tree is None and "unreadable" in note, True)
    return fails


def test_render_route() -> int:
    tree = dashboard.build_route({"owed": [], "lever": [
        {"id": "L1", "status": "REFUTED"},
        {"id": "L2", "status": ""},
    ]})
    html = dashboard.render_route(tree)
    fails = check("render_route styles decisions and outcomes differently",
                  'class="node decision"' in html
                  and 'class="node outcome"' in html, True)
    fails += check("render_route shows real lever leaves as chips",
                   'class="leaf">L1' in html and 'class="leaf">L2' in html, True)
    fails += check("render_route shows an empty bucket as none",
                   'class="leaf none">none' in html, True)
    fails += check("render_route emits no mermaid and no flowchart",
                   "mermaid" not in html and "flowchart" not in html, True)
    fails += check("render_route emits no script tag", "<script" not in html, True)
    return fails


SAMPLE_WORKBENCH = """Last written: 2026-08-06.

DISPATCHED NOW
  nothing. All slots free.

QUEUED, AND WHAT RELEASES EACH
  Bridge's 50 s tail, profiled   <- READY. The infrastructure round is closed
                                    (owner: infrastructure first, then
                                    development).
  the frozen mathematics         <- D30 lifts, which needs the line above plus
                                    exit condition (2) complete.

CONDITIONS THAT WOULD CHANGE WHAT I DISPATCH
  the tail profiles flat            -> it is the floor. Bridge closes at 199 s.
  the tail shows a concentrated
  cause                             -> one more seal dispatch, priced from the
                                       profile, before the freeze lifts.

NOT DISPATCHING, AND WHY
  the four waiting levers   the freeze stands and none is check-cost work. They
                            wait with their measurements intact.
  B-condensation-story      refuted by [T84]: the clause layer is not
                            Delta-0 certifiable.
"""


def test_parse_workbench() -> int:
    secs = dashboard.parse_workbench(SAMPLE_WORKBENCH)
    fails = check("workbench parse keeps the preamble",
                  secs[0]["preamble"].startswith("Last written: 2026-08-06"), True)
    headings = [s.get("heading") for s in secs if "heading" in s]
    fails += check("workbench parse finds all four headings",
                   headings, list(dashboard.WORKBENCH_HEADINGS))
    queued = secs[2]["items"]
    fails += check("queued item splits on the left arrow",
                   (queued[0]["left"], queued[0]["right"].startswith("READY.")),
                   ("Bridge's 50 s tail, profiled", True))
    fails += check("queued second item is its own split",
                   queued[1]["left"], "the frozen mathematics")
    conds = secs[3]["items"]
    fails += check("wrapped left side stays in one item",
                   conds[1]["left"], "the tail shows a concentrated cause")
    fails += check("condition consequence is the right side",
                   conds[1]["right"].startswith("one more seal dispatch"), True)
    not_disp = secs[4]["items"]
    fails += check("arrow-less items stay separate",
                   len(not_disp), 2)
    not_disp_text = "\n".join(i["text"] for i in not_disp)
    fails += check("no-arrow items stay verbatim",
                   "B-condensation-story" in not_disp_text, True)
    return fails


MALFORMED_WORKBENCH = """Preface line kept verbatim.

DISPATCHED NOW
  only one line here

QUEUED, AND WHAT RELEASES EACH
  no arrow in this item, it stays whole

CONDITIONS THAT WOULD CHANGE WHAT I DISPATCH
  an arrow that points at nothing <-

"""


def test_workbench_drift_fallback() -> int:
    """The fallback for a drifted file: a missing heading gets no block, an
    item without a split stays whole, a dangling arrow is kept verbatim, and
    no line the orchestrator wrote is dropped."""
    secs = dashboard.parse_workbench(MALFORMED_WORKBENCH)
    fails = check("missing heading yields no section for it",
                  any(s.get("heading") == "NOT DISPATCHING, AND WHY"
                      for s in secs), False)
    queued = [s for s in secs
              if s.get("heading") == "QUEUED, AND WHAT RELEASES EACH"][0]["items"]
    fails += check("unsplit queued item stays whole", "left" in queued[0], False)
    conds = [s for s in secs
             if s.get("heading") == "CONDITIONS THAT WOULD CHANGE WHAT I DISPATCH"][0]["items"]
    fails += check("dangling arrow falls back to verbatim",
                   conds[0]["text"].strip().endswith("<-"), True)
    rendered = dashboard.render_workbench_sections(secs)
    for line in MALFORMED_WORKBENCH.splitlines():
        if line.strip():
            fails += check(f"no line lost: {line.strip()[:24]}",
                           dashboard.clean(line.strip()) in rendered, True)
    return fails


def test_render_workbench() -> int:
    rendered = dashboard.render_workbench_sections(
        dashboard.parse_workbench(SAMPLE_WORKBENCH))
    fails = check("render lays split items out side by side",
                  'class="wb-row"' in rendered and 'class="wb-left"' in rendered
                  and 'class="wb-right"' in rendered, True)
    fails += check("render keeps each heading as its own block",
                   all(f"<h3>{h}</h3>" in rendered
                       for h in dashboard.WORKBENCH_HEADINGS), True)
    fails += check("render emits no script tag", "<script" not in rendered, True)
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
    for test in (test_brief_parse, test_route_builder, test_route_block_real,
                 test_route_block_no_data, test_render_route,
                 test_plan_parsing, test_remaining_rows, test_brief_naming,
                 test_clean, test_parse_workbench,
                 test_workbench_drift_fallback, test_render_workbench,
                 test_staleness):
        fails += test()
    print(f"\n{'PASS' if fails == 0 else 'FAIL'}: {fails} failing check(s)")
    return 1 if fails else 0


if __name__ == "__main__":
    sys.exit(main())
