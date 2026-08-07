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
import re
import sys
import tempfile
from datetime import datetime, timezone
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
    # One branch since 2026-08-07: the lever subtree, and the five leaf
    # assertions that went with it, were removed when the lever table left the
    # board and nothing rendered the builder any more.
    fails = check("route tree has the campaign branch only",
                  sorted(tree), ["campaign"])
    nodes = walk_route(tree["campaign"])
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
    fails += check("route_block tree has the campaign branch only",
                   sorted(tree or {}), ["campaign"])
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
    # The two lever-chip assertions went with the lever subtree, 2026-08-07:
    # leaves are a lever-branch feature and the campaign tree carries none.
    fails += check("render_route emits no mermaid and no flowchart",
                   "mermaid" not in html and "flowchart" not in html, True)
    fails += check("render_route emits no script tag", "<script" not in html, True)
    return fails


def test_remaining_pie_slices() -> int:
    """A remaining-row distribution: standing first, large rows individual,
    small rows grouped into a tail that names its members, total equals
    standing plus the midpoints."""
    data = {"remaining": [
        {"id": "A", "title": "alpha", "naive_low": 1000, "naive_high": 2700,
         "calibrated_low": 3000, "calibrated_high": 7900},
        {"id": "B", "title": "beta", "naive_low": 100, "naive_high": 200,
         "calibrated_low": 300, "calibrated_high": 400},
        {"id": "C", "title": "gamma", "naive_low": 300, "naive_high": 500,
         "calibrated_low": 900, "calibrated_high": 1100},
        {"id": "D", "title": "delta", "naive_low": 500, "naive_high": 700,
         "calibrated_low": 900, "calibrated_high": 1300},
        {"id": "E", "title": "eps", "naive_low": 800, "naive_high": 1000,
         "calibrated_low": 1200, "calibrated_high": 1600},
    ]}
    slices = dashboard.remaining_pie_slices(data, "naive", 5000)
    fails = check("pie leads with standing",
                  slices[0]["label"].startswith("standing"), True)
    fails += check("standing slice value", slices[0]["value"], 5000)
    labels = [s["label"] for s in slices]
    fails += check("large row stays individual",
                   any(l.startswith("A:") for l in labels)
                   and any(l.startswith("E:") for l in labels), True)
    tails = [s for s in slices if s["label"].startswith("tail")]
    fails += check("small row is grouped into one tail",
                   len(tails) == 1 and tails[0]["value"] == 150, True)
    fails += check("tail names its members",
                   "B 150" in tails[0]["tail_detail"], True)
    total = sum(s["value"] for s in slices)
    fails += check("pie total is standing plus remaining midpoints",
                   total, 5000 + 1850 + 900 + 600 + 400 + 150)
    return fails


def test_pie_svg() -> int:
    svg = dashboard.pie_svg([
        {"value": 60, "color": "--pie-1"},
        {"value": 40, "color": "--pie-2"},
    ])
    fails = check("pie_svg emits a path per slice", svg.count("<path"), 2)
    fails += check("pie colors come from the palette variables",
                   'fill="var(--pie-1)"' in svg
                   and 'fill="var(--pie-2)"' in svg, True)
    fails += check("pie_svg emits no script tag", "<script" not in svg, True)
    zero = dashboard.pie_svg([
        {"value": 0, "color": "--pie-1"},
        {"value": 100, "color": "--pie-2"},
    ])
    fails += check("a zero slice draws nothing",
                   zero.count("<path") + zero.count("<circle"), 1)
    full = dashboard.pie_svg([{"value": 100, "color": "--pie-1"}])
    fails += check("a single full slice is a circle", "<circle" in full, True)
    fails += check("empty slices draw no svg at all",
                   dashboard.pie_svg([{"value": 0, "color": "--pie-1"}]), "")
    return fails


def test_css_theme_lock() -> int:
    """The visual pass keeps every colour a :root variable: no hex literal
    survives outside the theme block, the font stacks are system-only, and
    the stylesheet carries no script, network or em dash."""
    css = dashboard.CSS
    root_start = css.index(":root {")
    depth = 0
    root_end = None
    for i, ch in enumerate(css[root_start:], root_start):
        if ch == "{":
            depth += 1
        elif ch == "}":
            depth -= 1
            if depth == 0:
                root_end = i
                break
    assert root_end is not None
    outside = css[:root_start] + css[root_end + 1:]
    fails = check("no hex literal outside :root",
                  re.search(r"#[0-9a-fA-F]{3,8}\b", outside), None)
    fails += check("system font stacks only",
                   "font-family: var(--mono)" in css
                   and "font-family: var(--sans)" in css, True)
    fails += check("no @import, URL or fetch in the stylesheet",
                   re.search(r"@import|https?://|fetch\(", css), None)
    fails += check("no script tag in the stylesheet", "<script" in css, False)
    fails += check("no em dash in the stylesheet", "\u2014" in css, False)
    return fails


def test_generated_page_stays_self_contained() -> int:
    """A full generated page keeps zero external references, zero scripts
    and zero em dashes, with a deterministic clock."""
    now = datetime(2026, 8, 6, 9, 0, tzinfo=timezone.utc)
    page = dashboard.render_page(now, Path("/tmp/l3.32-t118-dashboard.html"))
    fails = check("no external reference in the page",
                  len(re.findall(r"https?://|src=|@import|fetch\(", page)), 0)
    fails += check("no script tag in the page", "<script" in page, False)
    fails += check("no em dash in the page", "\u2014" in page, False)
    return fails


def test_measured_stats_marked() -> int:
    """The measured numbers (standing, full check) carry the amber marker and
    numeric table cells carry the tabular-figure class."""
    lines = dashboard.panel_lines()
    seconds = dashboard.panel_seconds()
    fails = check("standing stat carries the measured marker",
                  'class="stat measured"' in lines, True)
    fails += check("full-check stat carries the measured marker",
                   'class="stat measured"' in seconds, True)
    fails += check("numeric cells are marked for tabular figures",
                   'class="num"' in lines, True)
    fails += check("numeric cells are marked in the seconds panel",
                   'class="num"' in seconds, True)
    return fails


def test_pies_share_one_visual_language() -> int:
    """Every pie slice is separated by the same background stroke, so all
    charts read as one instrument."""
    css = dashboard.CSS
    fails = check("pie slices share one stroke",
                  "stroke: var(--bg)" in css, True)
    fails += check("pie stroke width is pinned",
                  "stroke-width: 2px" in css, True)
    return fails


def test_render_pie_chart() -> int:
    slices = [{"label": "a", "value": 75, "color": "--pie-1"},
              {"label": "b", "value": 25, "color": "--pie-2"}]
    html = dashboard.render_pie_chart("test chart", slices)
    fails = check("pie chart labels the total", "total 100" in html, True)
    fails += check("pie chart labels each slice's absolute value",
                   "75 (75%)" in html and "25 (25%)" in html, True)
    fails += check("pie chart emits svg and no script",
                   "<svg" in html and "<script" not in html, True)
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


def test_seconds_panel_pies() -> int:
    """The seconds pies against controlled data: the current check is the hot
    modules plus the remainder, and the tree-cost split is labelled as the
    pre-fix profile."""
    saved = dashboard.LEDGER_TOML
    with tempfile.TemporaryDirectory() as td:
        ledger = Path(td) / "ledger.toml"
        ledger.write_text("""
[timing]
full_cold_seconds = 1000

[[hot]]
module = "A"
seconds = 100

[[tree_cost]]
tree = "T1"
seconds = 300
""", encoding="utf-8")
        dashboard.LEDGER_TOML = ledger
        try:
            html = dashboard.panel_seconds()
        finally:
            dashboard.LEDGER_TOML = saved
    # The wording changed on 2026-08-07 when the board moved to ASD-STE100.
    fails = check("seconds panel draws the current check pie",
                  "Where the cold check spends its time" in html, True)
    fails += check("remainder slice is the full check minus the hot modules",
                   "everything else" in html and "900 (90%)" in html, True)
    fails += check("tree cost pie is labelled as pre-fix",
                   "BEFORE" in html and "300 (100%)" in html, True)
    fails += check("seconds panel names its source",
                   "ledger.toml (mtime" in html, True)
    return fails


def test_lines_panel_pies() -> int:
    """The lines panel on the real ledger draws both caliber pies and labels
    the standing slice, without hardcoding a total that would rot."""
    html = dashboard.panel_lines()
    fails = check("lines panel draws both caliber pies",
                  html.count('class="pie-card"'), 2)
    fails += check("lines panel labels the measured standing",
                   "standing, measured from HEAD" in html, True)
    fails += check("lines panel labels a pie total",
                   'class="pie-total">total ' in html, True)
    fails += check("lines panel names its sources",
                   "dev/ledger.toml (mtime" in html
                   and "scripts/ledger.py" in html, True)
    return fails


def main() -> int:
    fails = 0
    # Seven workbench tests were removed on 2026-08-07 with the workbench
    # itself: parsing, placement onto graph anchors, the drift fallback and
    # the merged-panel renderings all covered code that no longer exists.
    for test in (test_brief_parse, test_route_builder, 
                 test_route_block_real, test_route_block_no_data, 
                 test_render_route, test_remaining_pie_slices, 
                 test_pie_svg, test_render_pie_chart, test_css_theme_lock, 
                 test_generated_page_stays_self_contained, 
                 test_measured_stats_marked, 
                 test_pies_share_one_visual_language, test_plan_parsing, 
                 test_remaining_rows, test_brief_naming, test_clean, 
                 test_staleness, test_seconds_panel_pies, 
                 test_lines_panel_pies):
        fails += test()
    print(f"\n{'PASS' if fails == 0 else 'FAIL'}: {fails} failing check(s)")
    return 1 if fails else 0


if __name__ == "__main__":
    sys.exit(main())
