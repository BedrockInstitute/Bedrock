#!/usr/bin/env python3
"""Owner's dashboard, GENERATED from the canonical data. Never hand-written.

The owner asked for a visual board (the current route, the ledger's remaining
lines in both calibers, the current cold-start seconds, the code hierarchy and
where the project is in it, and the orchestrator's workbench). The design
decision that makes "update it on every sub-agent return" cheap is that this
page is a generated artifact: `make dashboard` rebuilds it from the canonical
sources and `scripts/check-dashboard.py` reports staleness (informational,
never a gate).

Sources, all machine-readable:
  dev/ledger.toml      [[remaining]] rows, [timing], [[hot]], [[tree_cost]],
                       [[lever]] rows, [[owed]] rows (the route graph's
                       decision leaves come from the lever and owed rows)
  dev/PLAN.md          section 11: MASTER status table (96 rows) and the Task
                       index (112 rows)
  _build/briefs/*.md   mtimes and title lines for the workbench panel
  scripts/ledger.py    standing, measured from HEAD (the one number this page
                       must not compute itself; ledger.toml's header says why)

The page is self-contained: one HTML file, inline CSS, no JavaScript, no
external fonts or network. The route flowchart is rendered as semantic HTML
with CSS: the structure is fixed in the generator, so a hand-laid-out diagram
beats a general layout engine, and the page needs neither mermaid nor a
network fetch. Since [T117] the workbench and the route are ONE panel: the
route graph carries the current position and the hand-written workbench
sections attached to the nodes they belong to (DISPATCHED NOW on the start
node, QUEUED on the freeze decision, CONDITIONS on the exit-condition and
TAKE IT NOW nodes, NOT DISPATCHING on the lever outcomes). A workbench line
that cannot be placed is shown verbatim, never dropped. The line and seconds
distributions are drawn as inline SVG pie charts generated in Python: an arc
is arithmetic, no chart library and no network.

Every panel carries the source path and that source's mtime, so a stale panel
is visible rather than misleading. A panel whose source is missing or
unreadable renders a clear "no data" state instead of crashing or inventing a
number (D-10).

Usage:
  dashboard.py --out _build/dashboard.html   generate the page
Exit status: 0 on success (including panels that honestly report no data),
2 on usage error.
"""

from __future__ import annotations

import argparse
import html
import math
import re
import subprocess
import sys
import tomllib
from collections import defaultdict
from datetime import datetime, timezone
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
LEDGER_TOML = ROOT / "dev" / "ledger.toml"
PLAN_MD = ROOT / "dev" / "PLAN.md"
LEDGER_PY = ROOT / "scripts" / "ledger.py"
BRIEFS_DIR = ROOT / "_build" / "briefs"
DEFAULT_OUT = ROOT / "_build" / "dashboard.html"

# Sources the generated page derives from, in staleness-check order. The briefs
# directory is represented by its newest file's mtime, which is what actually
# matters: an edited brief is newer than the page and must trigger a rebuild.
SOURCE_FILES = (LEDGER_TOML, PLAN_MD, LEDGER_PY, Path(__file__))

EM_DASH = "\u2014"  # banned in every language, including the HTML
HORIZONTAL_BAR = "\u2015"  # banned too; the prose linter treats it as one


def read(path: Path) -> str:
    """Read a text file; raise FileNotFoundError if missing."""
    return path.read_text(encoding="utf-8")


def mtime(path: Path) -> datetime:
    """UTC mtime of a file (the honest 'as of' stamp for a panel)."""
    return datetime.fromtimestamp(path.stat().st_mtime, tz=timezone.utc)


def fmt_mtime(when: datetime | None) -> str:
    if when is None:
        return "unknown"
    return when.strftime("%Y-%m-%d %H:%M UTC")


def clean(text: str) -> str:
    """Normalize text for the page: escape HTML and remove banned dashes."""
    text = text.replace(EM_DASH, "-").replace(HORIZONTAL_BAR, "-")
    return html.escape(text)


def truncate(text: str, limit: int) -> str:
    """Shorten a cell for the at-a-glance board; the full text stays in the
    source the panel names."""
    if len(text) <= limit:
        return text
    return text[: limit - 1].rstrip() + "..."


def load_ledger() -> dict:
    """Parse dev/ledger.toml. Raises on a broken file; the caller decides how
    to say so on the panel."""
    return tomllib.loads(read(LEDGER_TOML))


# ---------------------------------------------------------------------------
# Ledger numbers
# ---------------------------------------------------------------------------

def ledger_brief_line() -> str | None:
    """The canonical standing and endpoint line, from scripts/ledger.py --brief.
    Returns None if the tool cannot run (the panel then says standing is
    unavailable rather than guessing)."""
    try:
        out = subprocess.run(
            [sys.executable, str(LEDGER_PY), "--brief"],
            cwd=ROOT, capture_output=True, text=True, timeout=120,
        )
    except (OSError, subprocess.SubprocessError):
        return None
    if out.returncode != 0:
        return None
    return out.stdout.strip()


BRIEF_RE = re.compile(
    r"standing ([\d,]+) \| endpoint ([\d.]+)-([\d.]+)k naive, "
    r"([\d.]+)-([\d.]+)k calibrated \| (.*)$"
)


def parse_brief(line: str) -> dict:
    """Parse the ledger brief line into plain numbers.

    >>> line = "standing 18,464 | endpoint 24.95-31.18k naive, 31.60-47.18k calibrated | naive corner +6.18k against the 25k reference"
    >>> d = parse_brief(line)
    >>> d["standing"], d["naive_low_k"], d["naive_high_k"]
    (18464, 24.95, 31.18)
    """
    m = BRIEF_RE.match(line)
    if not m:
        raise ValueError(f"unrecognized ledger brief line: {line}")
    return {
        "standing": int(m.group(1).replace(",", "")),
        "naive_low_k": float(m.group(2)),
        "naive_high_k": float(m.group(3)),
        "calibrated_low_k": float(m.group(4)),
        "calibrated_high_k": float(m.group(5)),
        "corner": m.group(6),
    }


def remaining_rows(data: dict) -> list[dict]:
    """The [[remaining]] rows, both calibers, as they are declared."""
    out = []
    for row in data.get("remaining", []):
        out.append({
            "id": row.get("id", ""),
            "title": row.get("title", ""),
            "naive": f"{row.get('naive_low', 0):,}-{row.get('naive_high', 0):,}",
            "calibrated": f"{row.get('calibrated_low', 0):,}-{row.get('calibrated_high', 0):,}",
            "klass": row.get("klass", ""),
            "gate": row.get("gate", "none"),
        })
    return out


def lever_what(row: dict) -> str:
    """The human label for a lever row. Compression levers carry `title`;
    the freeze-campaign levers carry `target` or `scope` instead."""
    return row.get("title") or row.get("target") or row.get("scope") or row.get("id", "")


# ---------------------------------------------------------------------------
# The route flowchart: semantic HTML, built from the ledger
# ---------------------------------------------------------------------------


def build_route(data: dict) -> dict:
    """The route decision tree, built from the ledger.

    The DECISION STRUCTURE is fixed here, because it is the ruled procedure
    (D22, D26, D30) and does not drift, while every LEAF is read from
    dev/ledger.toml. A lever that is refuted, superseded or funded shows as
    such the moment its row changes, with no second place to update.

    The tree is rendered as semantic HTML with CSS (see render_route), so no
    layout engine is needed: the two branches, every decision and every branch
    label are known to this code. A node is a dict with a kind (start,
    decision or outcome), a label (list of lines), optional leaves (lever ids
    an outcome names) and optional edges (label plus child node).
    """
    levers = data.get("lever", [])

    def bucket(l: dict) -> str:
        s = (l.get("status") or "").upper()
        if "REFUT" in s:
            return "refuted"
        # in-route is tested BEFORE superseded on purpose. A status can say
        # both, and `rud-rewrite` does: "RULED ... the BATCH ORDER is
        # superseded". The lever is in the route; its ordering was revised.
        # Testing superseded first put it under RE-PRICE FIRST, which was wrong.
        if any(w in s for w in ("RULED", "GREEN", "EXECUTED", "IN FLIGHT")):
            return "in-route"
        if "SUPERSED" in s:
            return "superseded"
        if l.get("gated"):
            return "gated"
        return "waiting"

    groups: dict[str, list[str]] = {}
    for l in levers:
        groups.setdefault(bucket(l), []).append(l.get("id", "?"))

    frozen = [o for o in data.get("owed", []) if o.get("status") == "frozen"]
    freeze_note = (f"{len(frozen)} owed row(s) frozen" if frozen
                   else "nothing frozen")

    def decision(label: list[str], edges=None, anchor: str | None = None) -> dict:
        node = {"kind": "decision", "label": label, "edges": edges or []}
        if anchor is not None:
            node["anchor"] = anchor
        return node

    def outcome(label: list[str], leaves=None, edges=None,
                anchor: str | None = None) -> dict:
        node = {"kind": "outcome", "label": label, "edges": edges or []}
        if leaves is not None:
            node["leaves"] = leaves
        if anchor is not None:
            node["anchor"] = anchor
        return node

    def edge(label: str, to: dict) -> dict:
        return {"label": label, "to": to}

    freeze = decision(["is D30's freeze lifted?"], anchor="freeze")
    # The exit condition loops back to the freeze question. It is rendered as
    # a terminal reference to that question, not as a real cycle, so the tree
    # stays acyclic and the page generator cannot recurse forever.
    back_to_freeze = {"kind": "decision",
                      "label": ["is D30's freeze lifted?"], "edges": []}
    freeze["edges"] = [
        edge("no", outcome(
            ["THE CHECK-COST CAMPAIGN", "the only funded work",
             f"({freeze_note})"],
            edges=[edge("until it holds", outcome([
                "exit condition: every module at or above 2 percent of",
                "tree cost profiled, every removable second removed or",
                "refused with a written price, and the craft recorded",
            ], edges=[edge("repeat", back_to_freeze)],
                anchor="exit-condition"))],
        )),
        edge("yes", outcome(["THE FROZEN MATHEMATICS RESUMES"], edges=[
            edge("", outcome(["the bridge landing: below-lim"], edges=[
                edge("", outcome(["the choice re-home"], edges=[
                    edge("", outcome(["AC on surviving machinery"])),
                ])),
            ])),
            edge("", outcome(["the StepInL rewrite"], edges=[
                edge("", outcome(["W3, the internal well-ordering"], edges=[
                    edge("", outcome(["W7's residue, then the GCH sentence"])),
                ])),
            ])),
        ])),
    ]
    campaign = {"kind": "start", "label": ["a slot is free"],
                "edges": [edge("", freeze)], "anchor": "start"}

    lever_chain = decision(["has it been refuted?"], [
        edge("yes", outcome(["NOT A ROUTE"],
                            leaves=groups.get("refuted", []),
                            anchor="refuted")),
        edge("no", decision(["has ruled work already done part of it?"], [
            edge("yes", outcome(["RE-PRICE FIRST"],
                                leaves=groups.get("superseded", []),
                                anchor="superseded")),
            edge("no", decision(["priced at 3x with an unmeasured widest term?"], [
                edge("yes", outcome(["D22: PROBE FIRST"],
                                    leaves=groups.get("gated", []))),
                edge("no", decision(
                    ["is its region being touched by ruled work anyway?"], [
                        edge("yes", outcome([
                            "TAKE IT NOW", "marginal cost is near zero",
                            "when the file is already open",
                        ], anchor="take-now")),
                        edge("no", decision(
                            ["does the endpoint projection need the lines?"], [
                                edge("no", outcome([
                                    "KEEP AND WAIT",
                                    "D26: a line overage never changes the",
                                    "ROUTE; a lever is compression WITHIN it",
                                ], leaves=groups.get("waiting", []),
                                    anchor="waiting")),
                                edge("yes", outcome([
                                    "rank by net lines per unit of risk,",
                                    "cheapest first",
                                ])),
                            ])),
                    ])),
            ])),
        ])),
    ])
    lever = decision(["is a compression lever being considered?"], [
        edge("already in the route", outcome(["already in the route"],
                                             leaves=groups.get("in-route", []))),
        edge("a new lever", lever_chain),
    ])
    return {"campaign": campaign, "lever": lever}


def route_block() -> tuple[dict | None, Path | None, str]:
    """Build the route decision tree from the ledger (see build_route)."""
    try:
        data = load_ledger()
    except (OSError, tomllib.TOMLDecodeError) as exc:
        return None, None, f"dev/ledger.toml unreadable: {exc}"
    if not data:
        return None, None, "dev/ledger.toml is unreadable"
    return (build_route(data), LEDGER_TOML,
            "built from dev/ledger.toml's lever rows and owed statuses, not "
            "lifted from prose: a leaf changes the moment its row does")


def render_anchor(anchor: str, items: list[dict]) -> str:
    """The hand-written workbench content attached to one route anchor.

    Anchors are where the workbench's four sections live on the graph:
    "start" carries the DISPATCHED NOW position marker, "freeze" carries the
    QUEUED list, "exit-condition" and "take-now" carry CONDITIONS, and the
    lever outcomes carry NOT DISPATCHING rows. Split items keep their arrow
    reading (queued or condition on the left, release or consequence on the
    right); unsplit items stay verbatim in a pre block.
    """
    if not items:
        return ""
    if anchor == "start":
        body = "".join(
            f'<div class="position-text">{clean(i.get("text", ""))}</div>'
            for i in items if i.get("text"))
        return ('<div class="position"><span class="position-tag">'
                "where we are now</span>" + body + "</div>")

    def rows() -> str:
        out = []
        for i in items:
            if i.get("left") and i.get("right"):
                out.append(
                    '<div class="wb-row">'
                    f'<div class="wb-left">{clean(i["left"])}</div>'
                    '<div class="wb-arrow" aria-hidden="true">&rarr;</div>'
                    f'<div class="wb-right">{clean(i["right"])}</div>'
                    "</div>"
                )
            elif i.get("text"):
                out.append(f'<pre class="pre wb-item">{clean(i["text"])}</pre>')
        return "".join(out)

    if anchor == "freeze":
        return ('<div class="wb-anchor"><h4>Queued now, and what releases '
                "each (hand-written)</h4>" + rows() + "</div>")
    if anchor in ("exit-condition", "take-now"):
        return ('<div class="wb-anchor"><h4>Condition that would change this '
                "node (hand-written)</h4>" + rows() + "</div>")
    return ('<div class="wb-anchor"><h4>Not dispatching, and why '
            "(hand-written)</h4>" + rows() + "</div>")


def render_route_node(node: dict, depth: int = 0,
                      placed: dict[str, list[dict]] | None = None) -> str:
    """One node of the route tree as semantic HTML. Decision nodes carry the
    dashed style, outcome nodes the solid one, and an outcome that names real
    levers shows them as chips; an empty bucket shows a muted 'none'. The depth
    guard is a last resort against a cyclic tree, not a rendering feature. A
    node whose anchor has workbench content renders it inside the node, which
    is the [T117] merge: the hand-written sections live on the graph nodes
    they belong to instead of in a separate list."""
    if depth > 32:
        return ('<div class="node outcome"><span class="leaf none">'
                "loop back to an earlier node</span></div>")
    cls = {"start": "node start", "decision": "node decision",
           "outcome": "node outcome"}.get(node["kind"], "node outcome")
    if node.get("anchor") == "start" and placed and placed.get("start"):
        cls += " here"
    label = "<br>".join(clean(ln) for ln in node["label"])
    leaves = ""
    if node["kind"] == "outcome" and "leaves" in node:
        if node["leaves"]:
            chips = "".join(f'<span class="leaf">{clean(l)}</span>'
                            for l in node["leaves"])
        else:
            chips = '<span class="leaf none">none</span>'
        leaves = f'<div class="leaves">{chips}</div>'
    anchor_html = ""
    if placed and node.get("anchor"):
        anchor_html = render_anchor(node["anchor"], placed.get(node["anchor"], []))
    out = [f'<div class="{cls}">{label}{leaves}{anchor_html}</div>']
    for e in node.get("edges", []):
        out.append(
            '<div class="edge"><span class="edge-label">'
            f'{clean(e["label"])}</span><span class="edge-line"></span></div>'
            f'<div class="child">{render_route_node(e["to"], depth + 1, placed)}</div>'
        )
    return "".join(out)


def render_route(tree: dict,
                 placed: dict[str, list[dict]] | None = None) -> str:
    """The route panel body: two independent branches, one column each, with
    the hand-written workbench content attached to the anchored nodes."""
    return (
        '<div class="route">'
        '<div class="branch">'
        '<h3>Campaign: freeze on or off, and what each answer releases</h3>'
        '<div class="flow">' + render_route_node(tree["campaign"], placed=placed)
        + "</div></div>"
        '<div class="branch">'
        '<h3>Lever branch: five questions in order</h3>'
        '<div class="flow">' + render_route_node(tree["lever"], placed=placed)
        + "</div></div>"
        "</div>"
    )


# ---------------------------------------------------------------------------
# PLAN section 11: the code hierarchy and the task index
# ---------------------------------------------------------------------------

def section(text: str, start: str, end: str) -> str:
    """The lines between two headings, exclusive of both."""
    lines = text.splitlines()
    out: list[str] = []
    active = False
    for line in lines:
        if line.startswith(start):
            active = True
            continue
        if active and line.startswith(end):
            break
        if active:
            out.append(line)
    return "\n".join(out)


def table_rows(text: str, header: str) -> list[list[str]]:
    """Pipe rows from a markdown table, skipping the header and separator."""
    rows = []
    header_code = header.split("|")[1].strip().lower()
    for line in text.splitlines():
        line = line.strip()
        if not line.startswith("|"):
            continue
        cells = [c.strip() for c in line.strip("|").split("|")]
        if len(cells) < 3 or cells[0].lower() == header_code:
            continue
        if all(re.fullmatch(r":?-{2,}:?", c) for c in cells):
            continue
        rows.append(cells)
    return rows


def master_rows(plan_text: str) -> list[dict]:
    """MASTER status rows: code, goal, status (status joins any stray pipes)."""
    body = section(plan_text, "## 11. MASTER status table (live)", "### Task index")
    rows = []
    for cells in table_rows(body, "| Code | Goal | Status |"):
        rows.append({
            "code": cells[0],
            "goal": cells[1],
            "status": " | ".join(cells[2:]),
        })
    return rows


def task_rows(plan_text: str) -> list[dict]:
    """Task index rows: code, task, verdict, detail."""
    body = section(plan_text, "### Task index", "### Bookkeeping")
    rows = []
    for cells in table_rows(body, "| Code | Task | Verdict | Detail |"):
        rows.append({
            "code": cells[0],
            "task": cells[1],
            "verdict": cells[2],
            "detail": " | ".join(cells[3:]),
        })
    return rows


def normalize_code(code: str) -> str:
    """A dotted-decimal key for the hierarchy. Dash-codes (L3.32-F5) are
    sub-rows of their dotted parent (L3.32), so a dash becomes a dot only for
    tree geometry; the displayed code keeps its original spelling."""
    return code.replace("-", ".")


def parent_code(code: str) -> str:
    parts = normalize_code(code).split(".")
    return ".".join(parts[:-1]) if len(parts) > 1 else ""


def hierarchy(rows: list[dict]) -> dict[str, dict]:
    """Children map keyed by parent code; roots are codes whose parent is not a
    row code. Keys use the normalized dotted form. A code whose immediate
    parent is absent hangs from its nearest existing ancestor, so a dash-row
    like L3.32-F5 still nests under the campaign even if the intermediate row
    is missing from the table."""
    by_key = {normalize_code(r["code"]): r for r in rows}
    children: dict[str, list[str]] = defaultdict(list)
    for key in by_key:
        parent = parent_code(key)
        while parent and parent not in by_key:
            parent = parent_code(parent)
        children[parent].append(key)
    for key in children:
        children[key].sort()
    return {"by_key": by_key, "children": dict(children),
            "roots": sorted(children.get("", []))}


DONE_WORDS = {
    "DONE", "CLOSED", "DELIVERED", "COMPLETE", "ANSWERED", "FIXED",
    "RESOLVED", "GREEN", "SUPERSEDED", "REJECTED", "REFUTED", "ABANDONED",
    "DISSOLVED", "RE-POINTED", "RE-SCOPED", "EXECUTED", "ABSORBED", "ADOPTED",
    "REFUTATION", "NO-GO", "RED", "STOPPED", "STOP", "DEFECT",
}
COMPLETION_MARKERS = (
    "DONE", "CLOSED", "DELIVERED", "COMPLETE", "ANSWERED", "FIXED", "GREEN",
    "SUPERSEDED", "REJECTED", "REFUTED", "ABANDONED", "DISSOLVED", "EXECUTED",
    "ABSORBED", "ADOPTED", "RESOLVED", "NO-GO", "RED", "STOPPED", "STOP",
)
COMPLETION_RE = re.compile(
    r"\b(" + "|".join(COMPLETION_MARKERS) + r")\b"
)


def status_class(status: str) -> str:
    """A badge class from the status cell's leading keyword, for the
    at-a-glance board. The full status text is always shown too. REGISTERED
    rows that were completed inside the same cell (L3.22-L3.26) fold to done;
    a REGISTERED row with no completion marker is queued, not in flight."""
    first = re.sub(r"[^A-Za-z0-9-]", "", status.strip().split()[0].upper() or "")
    upper = status.upper()
    if first in ("IN", "ACTIVE", "OPEN", "STANDING", "EXECUTING", "GATED",
                 "PROBED", "FROZEN", "IN-FLIGHT", "AT-RISK", "BLOCKED"):
        return "now"
    if first == "RULED" and "ACTIVE" in upper:
        return "now"
    if first == "PLANNED":
        return "planned"
    if first == "REGISTERED":
        return "done" if COMPLETION_RE.search(upper) else "planned"
    if first in DONE_WORDS:
        return "done"
    return "neutral"


# ---------------------------------------------------------------------------
# The workbench: briefs and their reports
# ---------------------------------------------------------------------------

BRIEF_REPORT_RE = re.compile(r"^l3\.32-t(\d+)-brief\.md$")


def first_heading(text: str) -> str | None:
    for line in text.splitlines():
        if line.startswith("# "):
            return line[2:].strip()
    return None


def report_for_brief(name: str) -> Path | None:
    """The exact-code report path for a task brief, if that naming applies."""
    m = BRIEF_REPORT_RE.match(name)
    if not m:
        return None
    return ROOT / "_build" / f"l3.32-t{m.group(1)}-report.md"


def recent_briefs(limit: int = 10) -> list[dict]:
    """Newest briefs by mtime, with their title lines and whether an
    exact-code report exists (the committed evidence of a return)."""
    if not BRIEFS_DIR.is_dir():
        return []
    recs = []
    for path in sorted(BRIEFS_DIR.glob("*.md"),
                       key=lambda p: p.stat().st_mtime, reverse=True):
        report = report_for_brief(path.name)
        recs.append({
            "name": path.name,
            "title": first_heading(read(path)) or path.name,
            "mtime": mtime(path),
            "report": report,
            "returned": report is not None and report.exists(),
        })
    return recs[:limit]


def newest_brief_mtime() -> datetime | None:
    """The newest brief mtime; the directory's effective as-of for staleness."""
    if not BRIEFS_DIR.is_dir():
        return None
    times = [p.stat().st_mtime for p in BRIEFS_DIR.glob("*.md")]
    if not times:
        return None
    return datetime.fromtimestamp(max(times), tz=timezone.utc)


# ---------------------------------------------------------------------------
# Staleness
# ---------------------------------------------------------------------------

def source_stamps() -> list[tuple[str, datetime | None]]:
    """(label, mtime) for every source the page derives from."""
    stamps = [(str(p), mtime(p) if p.exists() else None) for p in SOURCE_FILES]
    stamps.append(("_build/briefs/*.md (newest)", newest_brief_mtime()))
    return stamps


def stale_sources(out_path: Path) -> list[str]:
    """Sources newer than the generated page. Empty means the page is fresh.
    A missing page is stale-by-definition but callers report it separately."""
    if not out_path.exists():
        return [f"{label} (page missing)" for label, _ in source_stamps()]
    out_time = mtime(out_path)
    return [label for label, when in source_stamps()
            if when is not None and when > out_time]


# ---------------------------------------------------------------------------
# HTML
# ---------------------------------------------------------------------------

CSS = """
:root {
  /* Dark, by the owner's standing request. One substrate (deactivated CRT),
     one accent (amber), one slice ramp (steel blue) shared by every chart.
     Every colour in the stylesheet is a variable: a literal left in a rule
     below is a light patch nobody notices until the page is opened at night,
     which is the whole failure mode of a half-applied theme. */
  --bg: #0b0e12; --card: #11151b; --sunk: #0d1117;
  --ink: #e9e7e1; --ink2: #b6b1a5; --muted: #7f7a70;
  --line: #2b333d; --line2: #1e252d;
  --accent: #e0a83c; --now: #2a2313; --now-ink: #f2c96b;
  --done: #12231a; --ok: #7fbf9b; --neutral: #1c222b;
  --warn: #d98b7f; --warn-bg: #251614;
  --plan-bg: #16202c; --plan-ink: #8fb3d8;
  --start-bg: #131a24; --start-line: #4a6b8f; --decision-line: #c99a3d;
  --pie-standing: #e0a83c;
  --pie-1: #a8c4e0; --pie-2: #8ba8c7; --pie-3: #708ca8;
  --pie-4: #577188; --pie-5: #425768; --pie-6: #31404e;
  --pie-tail: #2a3642;
  --sans: -apple-system, BlinkMacSystemFont, "Segoe UI", Roboto,
          "Helvetica Neue", Arial, sans-serif;
  --mono: ui-monospace, "SF Mono", Menlo, Consolas, "Liberation Mono",
          monospace;
}
* { box-sizing: border-box; }
html { color-scheme: dark; }
body { margin: 0; background: var(--bg); color: var(--ink);
  font-family: var(--sans); font-size: 15px; line-height: 1.5; }
header { padding: 24px 28px 16px; border-bottom: 2px solid var(--accent); }
h1 { margin: 0 0 6px; font-size: 1.75rem; line-height: 1.15;
  letter-spacing: -0.01em; font-weight: 700; }
.meta { margin: 0; color: var(--muted); font-size: 0.78rem;
  font-family: var(--mono); line-height: 1.55; max-width: 75ch; }
main { display: grid; grid-template-columns: 1fr 1fr; gap: 18px;
  padding: 24px 28px 10px; align-items: start; }
.panel { background: var(--card); border: 1px solid var(--line);
  padding: 18px 20px 14px; }
.panel.wide { grid-column: 1 / -1; }
h2 { margin: 0 0 12px; padding: 2px 0 10px 12px; font-size: 0.98rem;
  line-height: 1.3; font-weight: 600; letter-spacing: 0.01em;
  border-bottom: 1px solid var(--line); border-left: 3px solid var(--accent); }
h3 { margin: 18px 0 8px; font-family: var(--mono); font-size: 0.7rem;
  font-weight: 600; letter-spacing: 0.14em; text-transform: uppercase;
  color: var(--ink2); }
.src { margin-top: 14px; padding-top: 10px; border-top: 1px dashed var(--line);
  color: var(--muted); font-size: 0.72rem; font-family: var(--mono);
  line-height: 1.6; }
.stats { display: flex; flex-wrap: wrap; gap: 14px; margin: 6px 0 18px; }
.stat { flex: 1 1 170px; border: 1px solid var(--line);
  border-left: 2px solid var(--line2); padding: 12px 14px 10px;
  background: var(--sunk); }
.stat.measured { border-left-color: var(--accent); }
.stat .num { font-family: var(--mono); font-variant-numeric: tabular-nums;
  font-size: 1.9rem; font-weight: 600; line-height: 1.1;
  letter-spacing: -0.02em; }
.stat .lab { font-family: var(--mono); font-size: 0.66rem;
  letter-spacing: 0.09em; text-transform: uppercase; color: var(--muted);
  margin-top: 6px; }
.stat .sub { font-size: 0.75rem; color: var(--muted); margin-top: 5px;
  line-height: 1.45; }
table { border-collapse: collapse; width: 100%; font-size: 0.8rem;
  font-variant-numeric: tabular-nums; }
th { text-align: left; font-family: var(--mono); font-size: 0.66rem;
  font-weight: 600; letter-spacing: 0.1em; text-transform: uppercase;
  color: var(--muted); border-bottom: 1px solid var(--line);
  padding: 6px 10px 6px 0; }
td { padding: 6px 10px 6px 0; border-bottom: 1px solid var(--line2);
  vertical-align: top; line-height: 1.45; }
tr:last-child td { border-bottom: none; }
td.num { font-family: var(--mono); white-space: nowrap; }
.badge { display: inline-block; padding: 2px 7px; font-family: var(--mono);
  font-size: 0.64rem; font-weight: 600; letter-spacing: 0.04em;
  white-space: nowrap; }
.badge.now { background: var(--now); color: var(--now-ink);
  border: 1px solid var(--decision-line); }
.badge.done { background: var(--done); color: var(--ok); }
.badge.planned { background: var(--plan-bg); color: var(--plan-ink); }
.badge.neutral { background: var(--neutral); color: var(--ink2); }
.tree { max-height: 560px; overflow: auto; border: 1px solid var(--line);
  padding: 8px 10px; font-size: 0.78rem; scrollbar-width: thin;
  scrollbar-color: var(--line) var(--bg); }
.tree::-webkit-scrollbar { width: 10px; }
.tree::-webkit-scrollbar-thumb { background: var(--line); }
.tree::-webkit-scrollbar-track { background: var(--bg); }
.tree-row { padding: 3px 6px 3px 2px; display: flex; gap: 10px;
  align-items: baseline; }
.tree-row:hover { background: var(--neutral); }
.tree-row.here { background: var(--now); }
.tree-row .code { font-family: var(--mono); font-weight: 600;
  white-space: nowrap; font-size: 0.74rem; }
.tree-row.here .code { color: var(--now-ink); }
.tree-row .goal { color: var(--ink2); overflow: hidden; text-overflow: ellipsis;
  white-space: nowrap; }
.pre { background: var(--sunk); border: 1px solid var(--line);
  padding: 12px 14px; overflow: auto; font-family: var(--mono);
  font-size: 0.75rem; line-height: 1.55; scrollbar-width: thin;
  scrollbar-color: var(--line) var(--bg); }
.note { font-size: 0.78rem; color: var(--muted); margin: 8px 0; line-height: 1.5; }
.missing { border: 1px solid var(--warn); color: var(--warn);
  background: var(--warn-bg); padding: 12px 14px; font-family: var(--mono);
  font-size: 0.78rem; line-height: 1.5; }
footer { padding: 16px 28px 28px; color: var(--muted); font-size: 0.75rem; }
footer .note { font-family: var(--mono); }
ul { margin: 6px 0; padding-left: 22px; }
li { margin: 4px 0; line-height: 1.45; }
.route { display: grid; grid-template-columns: 1.3fr 1fr; gap: 24px; }
.branch { min-width: 0; }
.branch h3 { margin: 0 0 12px; }
.flow { display: flex; flex-direction: column; }
.node { border: 1px solid var(--line); padding: 10px 12px;
  background: var(--sunk); font-size: 0.8rem; line-height: 1.5; }
.node:hover { background: var(--card); }
.node.start { background: var(--start-bg); border-color: var(--start-line); }
.node.start.here { border-color: var(--now-ink); border-width: 2px; }
.node.decision { border-style: dashed; border-color: var(--decision-line);
  background: var(--sunk); }
.node.outcome { border-style: solid; }
.leaves { margin-top: 8px; display: flex; flex-wrap: wrap; gap: 5px; }
.leaf { background: var(--plan-bg); color: var(--plan-ink);
  border: 1px solid var(--line); padding: 1px 7px; font-family: var(--mono);
  font-size: 0.66rem; font-weight: 600; letter-spacing: 0.03em; }
.leaf.none { background: transparent; color: var(--muted); font-weight: 400; }
.edge { margin: 8px 0 2px 22px; display: flex; align-items: center; gap: 8px;
  font-family: var(--mono); font-size: 0.64rem; color: var(--muted);
  text-transform: uppercase; letter-spacing: 0.1em; }
.edge-line { flex: 1; height: 1px; background: var(--line); position: relative; }
.edge-line::before { content: ""; position: absolute; left: -4px; top: -3px;
  width: 5px; height: 5px; background: var(--bg); border: 1px solid var(--line); }
.child { margin-left: 30px; padding-left: 10px; border-left: 1px solid var(--line); }
.wb-row { display: grid; grid-template-columns: 1fr auto 1.6fr; gap: 10px;
  align-items: start; border: 1px solid var(--line);
  padding: 8px 10px; margin: 6px 0; background: var(--sunk); }
.wb-left { font-weight: 600; }
.wb-right { color: var(--ink2); }
.wb-arrow { color: var(--accent); font-weight: 700; font-family: var(--mono); }
.wb-item { margin: 6px 0; }
.position { margin-top: 10px; border: 1px solid var(--decision-line);
  background: var(--now); padding: 10px 12px; }
.position-tag { display: block; font-family: var(--mono); font-size: 0.62rem;
  font-weight: 700; letter-spacing: 0.12em; color: var(--now-ink);
  text-transform: uppercase; margin-bottom: 5px; }
.position-text { color: var(--now-ink); }
.wb-anchor { margin-top: 10px; border-top: 1px dashed var(--line);
  padding-top: 8px; font-size: 0.75rem; }
.wb-anchor h4 { margin: 0 0 6px; font-family: var(--mono); font-size: 0.62rem;
  letter-spacing: 0.1em; text-transform: uppercase; color: var(--muted); }
.wb-anchor .wb-row { margin: 4px 0; padding: 5px 7px; }
.wb-anchor pre { margin: 4px 0; }
.unplaced { border: 1px dashed var(--warn); padding: 12px 14px; margin-top: 14px; }
.unplaced h3 { color: var(--warn); }
.pie-wrap { display: flex; flex-wrap: wrap; gap: 18px; margin: 12px 0 18px;
  align-items: flex-start; }
.pie-card { flex: 1 1 290px; border: 1px solid var(--line);
  background: var(--sunk); padding: 12px 14px; }
.pie-head { display: flex; align-items: baseline; justify-content: space-between;
  gap: 8px; border-bottom: 1px solid var(--line2); padding-bottom: 6px; }
.pie-title { font-family: var(--mono); font-size: 0.68rem; font-weight: 600;
  letter-spacing: 0.08em; text-transform: uppercase; }
.pie-total { font-family: var(--mono); font-size: 0.8rem; font-weight: 600;
  color: var(--accent); white-space: nowrap; }
.pie-body { display: flex; gap: 14px; align-items: center; margin-top: 12px;
  flex-wrap: wrap; }
.pie { flex: none; display: block; }
.pie path, .pie circle { stroke: var(--bg); stroke-width: 2px; }
.legend { list-style: none; margin: 0; padding: 0; font-size: 0.74rem;
  flex: 1 1 160px; min-width: 160px; }
.legend li { display: flex; gap: 7px; align-items: baseline; margin: 4px 0; }
.swatch { width: 10px; height: 10px; flex: none; align-self: center;
  border: 1px solid var(--line); }
.legend .val { margin-left: auto; color: var(--ink2); white-space: nowrap;
  font-family: var(--mono); font-size: 0.68rem; }
.legend .band { color: var(--muted); font-size: 0.64rem; }
.legend .tail-detail { display: block; margin-left: 17px; color: var(--muted);
  font-size: 0.64rem; }
"""


def panel(title: str, body: str, src: str, wide: bool = False) -> str:
    cls = "panel wide" if wide else "panel"
    return (f'<section class="{cls}">\n<h2>{title}</h2>\n{body}\n'
            f'<div class="src">{src}</div>\n</section>')


def source_note(*paths: Path) -> str:
    parts = []
    for path in paths:
        when = mtime(path) if path.exists() else None
        stamp = fmt_mtime(when) if when else "MISSING"
        parts.append(f"{path} (mtime {stamp})")
    return "source: " + "; ".join(parts)


def no_data(reason: str) -> str:
    return f'<div class="missing">No data behind this panel: {clean(reason)}</div>'


# ---------------------------------------------------------------------------
# Pie charts: inline SVG, generated in Python
# ---------------------------------------------------------------------------

PIE_COLORS = ["--pie-1", "--pie-2", "--pie-3", "--pie-4", "--pie-5", "--pie-6"]


def remaining_pie_slices(data: dict, caliber: str, standing: int) -> list[dict]:
    """One caliber's line distribution: standing first, then each remaining
    row's band MIDPOINT, tail-grouped.

    A band is a range, not a point: the angles use the midpoint so the pie has
    a shape at all, the legend carries the band, and the panel says so. The
    tail rule is explicit: a row stays individual when its midpoint is at
    least 8 percent of the remaining total, capped at six rows and floored at
    four, so a pie never degenerates into a list.
    """
    low_k = "naive_low" if caliber == "naive" else "calibrated_low"
    high_k = "naive_high" if caliber == "naive" else "calibrated_high"
    rows = []
    for r in data.get("remaining", []):
        low = r.get(low_k, 0) or 0
        high = r.get(high_k, 0) or 0
        rows.append({
            "id": r.get("id", "?"),
            "title": r.get("title", ""),
            "mid": round((low + high) / 2),
            "band": f"{low:,}-{high:,}",
        })
    rem_total = sum(r["mid"] for r in rows)
    rows.sort(key=lambda r: r["mid"], reverse=True)
    keep = [r for r in rows if rem_total and r["mid"] >= 0.08 * rem_total][:6]
    if len(keep) < 4:
        keep = rows[:4]
    keep_ids = {r["id"] for r in keep}
    tail = [r for r in rows if r["id"] not in keep_ids]
    slices = [{"label": "standing, measured from HEAD",
               "value": standing, "band": None, "color": "--pie-standing"}]
    for i, r in enumerate(keep):
        slices.append({"label": f"{r['id']}: {truncate(r['title'], 42)}",
                       "value": r["mid"], "band": r["band"],
                       "color": PIE_COLORS[i % len(PIE_COLORS)]})
    if tail:
        tail_val = sum(r["mid"] for r in tail)
        detail = ", ".join(f"{r['id']} {r['mid']:,}" for r in tail)
        slices.append({"label": f"tail: {len(tail)} smaller rows",
                       "value": tail_val, "band": None,
                       "tail_detail": detail, "color": "--pie-tail"})
    return slices


def pie_svg(slices: list[dict], radius: int = 78, cx: int = 88,
            cy: int = 88) -> str:
    """One pie as an inline SVG. An arc is polar-to-cartesian arithmetic: no
    library, no script, no network. A zero slice draws nothing; a single
    100 percent slice draws a circle."""
    total = sum(s["value"] for s in slices)
    if total <= 0:
        return ""
    start = -90.0
    paths = []
    for s in slices:
        value = s["value"]
        if value <= 0:
            continue
        frac = value / total
        sweep = frac * 360.0
        if frac >= 0.9999:
            paths.append(
                f'<circle cx="{cx}" cy="{cy}" r="{radius}" '
                f'fill="var({s["color"]})"/>'
            )
            break
        x1 = cx + radius * math.cos(math.radians(start))
        y1 = cy + radius * math.sin(math.radians(start))
        x2 = cx + radius * math.cos(math.radians(start + sweep))
        y2 = cy + radius * math.sin(math.radians(start + sweep))
        large = 1 if sweep > 180 else 0
        paths.append(
            f'<path d="M {cx} {cy} L {x1:.2f} {y1:.2f} '
            f'A {radius} {radius} 0 {large} 1 {x2:.2f} {y2:.2f} Z" '
            f'fill="var({s["color"]})"/>'
        )
        start += sweep
    return ('<svg class="pie" width="176" height="176" viewBox="0 0 176 176" '
            'role="img" aria-label="pie chart">' + "".join(paths) + "</svg>")


def pie_legend(slices: list[dict], total: int) -> str:
    """The legend beside a pie: label, band when the slice is a range, the
    tail's named members, and value plus percent. The absolute value is on
    every slice, not only in the total line."""
    lis = []
    for s in slices:
        if s["value"] <= 0:
            continue
        band = (f' <span class="band">band {s["band"]}</span>'
                if s.get("band") else "")
        detail = (f'<span class="tail-detail">{clean(s["tail_detail"])}</span>'
                  if s.get("tail_detail") else "")
        pct = s["value"] / total * 100 if total else 0
        lis.append(
            "<li>"
            f'<span class="swatch" style="background:var({s["color"]})"></span>'
            f'<span>{clean(s["label"])}{band}{detail}</span>'
            f'<span class="val">{s["value"]:,} ({pct:.0f}%)</span>'
            "</li>"
        )
    return '<ul class="legend">' + "".join(lis) + "</ul>"


def render_pie_chart(title: str, slices: list[dict]) -> str:
    """A titled pie card: the SVG, its legend, and the absolute total. A
    distribution without its total is decoration, so the total is always
    labelled."""
    total = sum(s["value"] for s in slices)
    return (
        '<div class="pie-card">'
        '<div class="pie-head">'
        f'<span class="pie-title">{clean(title)}</span>'
        f'<span class="pie-total">total {total:,}</span>'
        "</div>"
        f'<div class="pie-body">{pie_svg(slices)}{pie_legend(slices, total)}</div>'
        "</div>"
    )


# ---------------------------------------------------------------------------
# Panels
# ---------------------------------------------------------------------------

def panel_lines() -> str:
    brief_line = ledger_brief_line()
    brief = parse_brief(brief_line) if brief_line else None
    try:
        data = load_ledger()
    except (OSError, tomllib.TOMLDecodeError) as exc:
        return panel("Remaining lines, current plus estimate",
                     no_data(f"dev/ledger.toml unreadable: {exc}"),
                     source_note(LEDGER_TOML))
    rows = remaining_rows(data)
    if brief is None:
        stats = ('<div class="missing">Standing unavailable: '
                 'scripts/ledger.py --brief failed. The remaining rows below '
                 'are still shown from dev/ledger.toml.</div>')
    else:
        stats = (
            '<div class="stats">'
            f'<div class="stat measured"><div class="num">{brief["standing"]:,}</div>'
            '<div class="lab">standing, measured from HEAD</div>'
            '<div class="sub">non-blank lines in Agda fences, tracked masters minus D18 retirements</div></div>'
            f'<div class="stat"><div class="num">{brief["naive_low_k"]:.2f}k to {brief["naive_high_k"]:.2f}k</div>'
            '<div class="lab">endpoint, naive caliber</div>'
            '<div class="sub">standing plus the remaining rows, summed as priced</div></div>'
            f'<div class="stat"><div class="num">{brief["calibrated_low_k"]:.2f}k to {brief["calibrated_high_k"]:.2f}k</div>'
            '<div class="lab">endpoint, calibrated caliber</div>'
            '<div class="sub">x1.3 rows anchored by a probe or comparable, x3 rows only a survey reaches</div></div>'
            '</div>'
        )
    if brief is not None:
        naive_slices = remaining_pie_slices(data, "naive", brief["standing"])
        cal_slices = remaining_pie_slices(data, "calibrated", brief["standing"])
        naive_total = sum(s["value"] for s in naive_slices)
        cal_total = sum(s["value"] for s in cal_slices)
        pies = (
            "<h3>Line distribution</h3>"
            '<p class="note">Angles use each remaining row\'s band MIDPOINT: '
            "the rows are ranges, not points (the bands are in the legend), "
            "and standing is measured while remaining rows are estimates, so "
            "these proportions are a reading aid, not an exact statement. "
            f"Totals are standing ({brief['standing']:,}) plus the remaining "
            f"midpoints: {naive_total:,} naive, {cal_total:,} calibrated.</p>"
            '<div class="pie-wrap">'
            + render_pie_chart("Remaining rows, naive caliber", naive_slices)
            + render_pie_chart("Remaining rows, calibrated caliber", cal_slices)
            + "</div>"
        )
    else:
        pies = ('<div class="missing">Line pie not drawn: standing is '
                "unavailable because scripts/ledger.py --brief failed. The "
                "bands are still shown below.</div>")
    table = (
        '<table><thead><tr><th>row</th><th>work</th><th>naive</th>'
        '<th>calibrated</th><th>class</th></tr></thead><tbody>'
    )
    for row in rows:
        table += (
            f'<tr><td>{clean(row["id"])}</td>'
            f'<td title="{clean(row["title"])}">{clean(truncate(row["title"], 90))}</td>'
            f'<td class="num">{clean(row["naive"])}</td>'
            f'<td class="num">{clean(row["calibrated"])}</td>'
            f'<td>{clean(truncate(row["klass"], 48))}</td></tr>'
        )
    table += "</tbody></table>"
    src = source_note(LEDGER_TOML, LEDGER_PY) + "; standing is not written down, it is computed"
    return panel("Remaining lines: standing, bands and distribution",
                 stats + pies + table, src)


def panel_seconds() -> str:
    try:
        data = load_ledger()
    except (OSError, tomllib.TOMLDecodeError) as exc:
        return panel("Cold-start seconds (current only)",
                     no_data(f"dev/ledger.toml unreadable: {exc}"),
                     source_note(LEDGER_TOML))
    timing = data.get("timing", {})
    full = timing.get("full_cold_seconds")
    if full is None:
        return panel("Cold-start seconds (current only)",
                     no_data("[timing].full_cold_seconds is absent from dev/ledger.toml"),
                     source_note(LEDGER_TOML))
    note = truncate(str(timing.get("note", "")), 240)
    stats = (
        '<div class="stats">'
        f'<div class="stat measured"><div class="num">{full:,} s</div>'
        '<div class="lab">current full cold check, measured</div>'
        '<div class="sub">current only, no estimate; the measurement note: '
        f'{clean(note)}</div></div>'
        '</div>'
    )
    hot = data.get("hot", [])
    hot_rows = "".join(
        f'<tr><td>{clean(h.get("module", ""))}</td>'
        f'<td class="num">{clean(str(h.get("seconds", "")))}</td>'
        f'<td class="num">{clean(str(h.get("lines", "")))}</td>'
        f'<td title="{clean(h.get("why", ""))}">{clean(truncate(h.get("why", ""), 70))}</td></tr>'
        for h in hot
    )
    pie_html = ""
    if full is not None:
        hot_named = [h for h in hot if h.get("seconds")]
        named_sum = sum(int(h["seconds"]) for h in hot_named)
        slices = [
            {"label": h.get("module", "?"), "value": int(h["seconds"]),
             "band": None, "color": PIE_COLORS[i % len(PIE_COLORS)]}
            for i, h in enumerate(hot_named)
        ]
        other = full - named_sum
        caveat = ""
        if other > 0:
            slices.append({"label": "everything else in the profile",
                           "value": other, "band": None,
                           "color": "--pie-tail"})
        elif other < 0:
            caveat = ('<div class="missing">The named hot modules already sum '
                      f"to {named_sum:,} s, above the recorded {full:,} s full "
                      "check, so the measurements are not on one basis and no "
                      "'everything else' slice is invented.</div>")
        pie_html = (
            "<h3>Where the current cold check goes</h3>"
            '<p class="note">Profile-instrumented seconds from dev/ledger.toml; '
            "the profile-to-wall ratio is not pinned (0.6-0.7 per the timing "
            "note). Slices are the named hot modules plus everything else "
            f"({full:,} s total).</p>"
            '<div class="pie-wrap">'
            + render_pie_chart("Current full cold check, by module", slices)
            + "</div>" + caveat
        )
    hot_table = (
        "<h3>Hot modules</h3>"
        '<table><thead><tr><th>module</th><th>seconds</th><th>lines</th>'
        '<th>why it costs</th></tr></thead><tbody>' + hot_rows + "</tbody></table>"
    )
    costs = data.get("tree_cost", [])
    cost_rows = "".join(
        f'<tr><td>{clean(c.get("tree", ""))}</td>'
        f'<td class="num">{clean(str(c.get("modules", "")))}</td>'
        f'<td class="num">{clean(str(c.get("lines", "")))}</td>'
        f'<td class="num">{clean(str(c.get("seconds", "")))}</td>'
        f'<td class="num">{clean(str(c.get("per_line", "")))}</td></tr>'
        for c in costs
    )
    cost_pie = ""
    if costs:
        cost_slices = [
            {"label": c.get("tree", "?"), "value": int(c.get("seconds", 0) or 0),
             "band": None, "color": PIE_COLORS[i % len(PIE_COLORS)]}
            for i, c in enumerate(costs)
        ]
        cost_total = sum(s["value"] for s in cost_slices)
        cost_pie = (
            "<h3>Tree cost: the subtree split</h3>"
            '<p class="note">The tree_cost rows are the PRE-FIX profile: they '
            f"sum to {cost_total:,} s, the 2,723 s profile the timing note "
            "records (within rounding), NOT the current check total. The two "
            "are different measurements and are not added.</p>"
            '<div class="pie-wrap">'
            + render_pie_chart("Pre-fix profile seconds, by subtree", cost_slices)
            + "</div>"
        )
    cost_table = (
        "<h3>Tree cost</h3>"
        '<table><thead><tr><th>tree</th><th>modules</th><th>lines</th>'
        '<th>seconds</th><th>seconds/line</th></tr></thead><tbody>'
        + cost_rows + "</tbody></table>"
    )
    src = source_note(LEDGER_TOML)
    return panel("Cold-start seconds: current check and its distribution",
                 stats + pie_html + cost_pie + hot_table + cost_table, src)


def panel_hierarchy() -> str:
    if not PLAN_MD.exists():
        return panel("Code hierarchy and where we are",
                     no_data("dev/PLAN.md is missing"),
                     source_note(PLAN_MD))
    rows = master_rows(read(PLAN_MD))
    if not rows:
        return panel("Code hierarchy and where we are",
                     no_data("no MASTER status rows parsed from dev/PLAN.md section 11"),
                     source_note(PLAN_MD))
    tree = hierarchy(rows)
    here = [r for r in rows if status_class(r["status"]) == "now"]
    counts: dict[str, int] = defaultdict(int)
    for r in rows:
        counts[status_class(r["status"])] += 1
    here_text = ", ".join(clean(r["code"]) for r in here) or "none"
    stats = (
        '<div class="stats">'
        f'<div class="stat"><div class="num">{len(rows)}</div>'
        '<div class="lab">goal rows in the MASTER status table</div></div>'
        f'<div class="stat"><div class="num">{len(here)}</div>'
        '<div class="lab">rows marked active, open, standing or in flight</div>'
        f'<div class="sub">where we are now: {here_text}</div></div>'
        f'<div class="stat"><div class="num">{counts["done"]}</div>'
        '<div class="lab">closed or delivered</div></div>'
        f'<div class="stat"><div class="num">{counts.get("planned", 0)}</div>'
        '<div class="lab">planned or registered as next</div></div>'
        '</div>'
    )
    tree_html = ['<div class="tree">']
    by_key = tree["by_key"]
    children = tree["children"]

    def walk(key: str, depth: int) -> None:
        row = by_key[key]
        cls = "tree-row here" if status_class(row["status"]) == "now" else "tree-row"
        badge = status_class(row["status"])
        tree_html.append(
            f'<div class="{cls}" style="padding-left:{depth * 18}px">'
            f'<span class="code">{clean(row["code"])}</span>'
            f'<span class="goal" title="{clean(row["goal"])}">{clean(truncate(row["goal"], 70))}</span>'
            f'<span class="badge {badge}">{clean(truncate(row["status"], 34))}</span></div>'
        )
        for child in children.get(key, []):
            walk(child, depth + 1)

    for root in tree["roots"]:
        walk(root, 0)
    tree_html.append("</div>")
    src = source_note(PLAN_MD) + ("; badges are a glance aid by the status cell's "
                                  "leading word; the full status text is in the source")
    return panel("Code hierarchy and where we are", stats + "".join(tree_html), src, wide=True)


WORKBENCH_MD = ROOT / "_build" / "workbench.md"


WORKBENCH_HEADINGS = (
    "DISPATCHED NOW",
    "QUEUED, AND WHAT RELEASES EACH",
    "CONDITIONS THAT WOULD CHANGE WHAT I DISPATCH",
    "NOT DISPATCHING, AND WHY",
)
WORKBENCH_SPLIT_HEADINGS = (
    "QUEUED, AND WHAT RELEASES EACH",
    "CONDITIONS THAT WOULD CHANGE WHAT I DISPATCH",
)


def match_workbench_heading(line: str) -> tuple[str, str] | None:
    """The heading a line starts with, forgivingly (markdown markers, case,
    extra whitespace), plus whatever follows it on the same line so trailing
    prose is never lost. Returns None when the line is not a heading."""
    norm = re.sub(r"\s+", " ", line.strip().strip("#* ").strip()).upper()
    best = None
    for h in WORKBENCH_HEADINGS:
        if norm.startswith(h) and (best is None or len(h) > len(best)):
            best = h
    if best is None:
        return None
    return best, norm[len(best):].strip()


def split_on_arrow(text: str) -> tuple[str, str] | None:
    """Split an item on the first '<-' or '->'. Both sides must be non-empty;
    a dangling marker falls back to None so the caller keeps the item whole."""
    pos, marker = None, None
    for m in ("<-", "->"):
        i = text.find(m)
        if i != -1 and (pos is None or i < pos):
            pos, marker = i, m
    if pos is None:
        return None
    left = text[:pos].strip()
    right = text[pos + len(marker):].strip()
    if not left or not right:
        return None
    return left, right


def split_workbench_items(body: str, heading: str) -> list[dict]:
    """Items under one heading, from a scan of the raw lines.

    An item starts at a line indented as little as the section's first line.
    A line at that indent starts a NEW item only when the previous item has
    already shown its arrow, or when it follows a deeper-indented continuation
    (the end of the previous item's text). That keeps a left side that wraps
    over two lines, like the CONDITIONS sample, in one item, while still
    separating arrow-less items like the NOT DISPATCHING rows. QUEUED and
    CONDITIONS items that split on '<-' or '->' become {"left", "right"};
    every other item stays whole as {"text"} with its original line breaks.
    A line that cannot be placed is kept verbatim, never dropped."""
    lines = [ln.rstrip() for ln in body.splitlines() if ln.strip()]
    if not lines:
        return []
    base = len(lines[0]) - len(lines[0].lstrip())
    items: list[dict] = []
    current: list[str] = []
    arrow_seen = False
    prev_indent = base

    def flush() -> None:
        nonlocal current
        if not current:
            return
        text = " ".join(ln.strip() for ln in current)
        if heading in WORKBENCH_SPLIT_HEADINGS:
            parts = split_on_arrow(text)
            if parts is not None:
                items.append({"left": parts[0], "right": parts[1]})
                current = []
                return
        items.append({"text": "\n".join(current)})
        current = []

    for ln in lines:
        indent = len(ln) - len(ln.lstrip())
        if (indent <= base and current
                and (arrow_seen or prev_indent > base)):
            flush()
            arrow_seen = False
        current.append(ln)
        if "<-" in ln or "->" in ln:
            arrow_seen = True
        prev_indent = indent
    flush()
    return items


def parse_workbench(text: str) -> list[dict]:
    """The hand-written workbench file as sections, in file order. Each entry
    is {"heading", "items"} for a recognized heading or {"preamble"} for text
    before the first heading. A heading that is missing simply has no section:
    its content cannot exist, and nothing else is dropped."""
    sections: list[tuple[str, list[str]]] = []
    preamble: list[str] = []
    current: list[str] | None = None
    for line in text.splitlines():
        matched = match_workbench_heading(line)
        if matched is not None:
            heading, rest = matched
            if current is not None:
                sections.append((current[0], current[1]))
            current = [heading, []]
            if rest:
                current[1].append(rest)
        elif current is not None:
            current[1].append(line)
        else:
            preamble.append(line)
    if current is not None:
        sections.append((current[0], current[1]))

    out: list[dict] = []
    if any(ln.strip() for ln in preamble):
        out.append({"preamble": "\n".join(preamble)})
    for heading, body in sections:
        out.append({"heading": heading,
                    "items": split_workbench_items("\n".join(body), heading)})
    return out


LAST_WRITTEN_RE = re.compile(r"^\s*last written\b", re.IGNORECASE)


def workbench_last_written(sections: list[dict]) -> str | None:
    """The orchestrator's own as-of stamp from the preamble, if present. It is
    metadata, not workbench state, so it is shown as a note rather than placed
    on a graph node."""
    for sec in sections:
        if "preamble" in sec:
            for ln in sec["preamble"].splitlines():
                if LAST_WRITTEN_RE.match(ln):
                    return ln.strip()
    return None


CONDITION_TAIL_WORDS = ("tail",)
CONDITION_LEVER_WORDS = ("lever", "ruled work", "region", "open")


def place_workbench(sections: list[dict]) -> tuple[dict[str, list[dict]], list[dict]]:
    """Map the hand-written workbench sections onto route anchors, and keep
    everything that does not map in the unplaced list.

    The [T117] merge reading, tested against the real workbench before this
    was built: DISPATCHED NOW is the position marker on the campaign start
    node; QUEUED items are what waits on the freeze decision (each carries its
    own release condition, the same edge-with-a-condition the graph already
    draws); CONDITIONS are branch conditions on the exit-condition node (the
    tail profile) and the TAKE IT NOW node (a lever's region opened by ruled
    work); NOT DISPATCHING rows name the lever outcomes they already sit in
    (refuted, superseded, waiting).

    The keyword tests are deliberately forgiving and the fallback is absolute:
    an item that matches nothing is returned unplaced and rendered verbatim,
    so a drifted workbench loses no line. The "Last written" preamble stamp is
    metadata, not state, and is not returned here.
    """
    placed: dict[str, list[dict]] = defaultdict(list)
    unplaced: list[dict] = []
    for sec in sections:
        if "preamble" in sec:
            leftover = [ln for ln in sec["preamble"].splitlines()
                        if ln.strip() and not LAST_WRITTEN_RE.match(ln)]
            if leftover:
                unplaced.append({"heading": "Written before the first heading",
                                 "items": [{"text": "\n".join(leftover)}]})
            continue
        heading = sec["heading"]
        if heading == "DISPATCHED NOW":
            for item in sec["items"]:
                placed["start"].append(item)
        elif heading == "QUEUED, AND WHAT RELEASES EACH":
            for item in sec["items"]:
                placed["freeze"].append(item)
        elif heading == "CONDITIONS THAT WOULD CHANGE WHAT I DISPATCH":
            for item in sec["items"]:
                low = (item.get("left") or item.get("text") or "").lower()
                if any(w in low for w in CONDITION_TAIL_WORDS):
                    placed["exit-condition"].append(item)
                elif any(w in low for w in CONDITION_LEVER_WORDS):
                    placed["take-now"].append(item)
                else:
                    unplaced.append({"heading": heading, "items": [item]})
        elif heading == "NOT DISPATCHING, AND WHY":
            for item in sec["items"]:
                low = (item.get("text") or "").lower()
                if "refut" in low:
                    placed["refuted"].append(item)
                elif "supersed" in low:
                    placed["superseded"].append(item)
                elif "wait" in low:
                    placed["waiting"].append(item)
                else:
                    unplaced.append({"heading": heading, "items": [item]})
        else:
            unplaced.append({"heading": heading, "items": sec["items"]})
    return dict(placed), unplaced


def render_workbench_sections(sections: list[dict]) -> str:
    """The parsed workbench as HTML blocks. QUEUED and CONDITIONS items lay
    the two sides of a split out side by side; everything else is verbatim."""
    parts: list[str] = []
    for sec in sections:
        if "preamble" in sec:
            parts.append(
                "<h3>Written before the first heading</h3>"
                f'<pre class="pre wb-item">{clean(sec["preamble"])}</pre>'
            )
            continue
        heading = sec["heading"]
        parts.append(f"<h3>{clean(heading)}</h3>")
        if not sec["items"]:
            parts.append('<p class="note">Nothing written under this '
                         "heading.</p>")
            continue
        if heading in WORKBENCH_SPLIT_HEADINGS:
            arrow = "&rarr;"
            for item in sec["items"]:
                if "left" in item:
                    parts.append(
                        '<div class="wb-row">'
                        f'<div class="wb-left">{clean(item["left"])}</div>'
                        f'<div class="wb-arrow" aria-hidden="true">{arrow}</div>'
                        f'<div class="wb-right">{clean(item["right"])}</div>'
                        "</div>"
                    )
                else:
                    parts.append(f'<pre class="pre wb-item">'
                                 f'{clean(item["text"])}</pre>')
        else:
            for item in sec["items"]:
                parts.append(f'<pre class="pre wb-item">'
                             f'{clean(item["text"])}</pre>')
    return "".join(parts)


def panel_workbench_route() -> str:
    """THE merged panel: the route graph with the hand-written workbench
    attached to the nodes it belongs to (the [T117] merge).

    The two old panels were one thing seen twice: the route is the decision
    procedure, and the workbench is where the orchestrator stands inside it.
    The strong move is a single picture that answers where are we (position
    marker on the start node), what happens next (the queue on the freeze
    decision), and what would change it (conditions on the exit-condition and
    TAKE IT NOW nodes, and the not-dispatching rows on the lever outcomes).
    The hand-written half still rules: a section that cannot be placed is
    rendered verbatim below the graph, and the generated corroboration (task
    index, briefs, owed table, lever rows) stays under the graph, so the merge
    loses no information the two panels carried.
    """
    tree, _path, note = route_block()
    sections: list[dict] = []
    if WORKBENCH_MD.exists():
        sections = parse_workbench(read(WORKBENCH_MD).strip())
    placed, unplaced = place_workbench(sections)
    parts: list[str] = []
    if sections:
        hand_note = "Hand-written half: " + source_note(WORKBENCH_MD)
        stamp = workbench_last_written(sections)
        if stamp:
            hand_note += "; " + clean(stamp)
        parts.append(f'<p class="note">{hand_note}</p>')
    if tree is None:
        parts.append(no_data(f"route graph: {note}"))
        if sections:
            parts.append(
                "<h3>Hand-written workbench, shown verbatim</h3>"
                '<p class="note">The route graph cannot be built from the '
                "ledger, so no node can carry these sections; every line is "
                "shown as written instead.</p>"
                + render_workbench_sections(sections)
            )
    else:
        parts.append(
            '<p class="note">' + clean(note)
            + ". The hand-written workbench sections are attached to the graph "
            "nodes they belong to: DISPATCHED NOW marks the current position, "
            "QUEUED sits on the freeze decision, CONDITIONS sit on the nodes "
            "they change, NOT DISPATCHING sits on the lever outcomes it names. "
            "A line that could not be placed is shown verbatim below.</p>"
        )
        parts.append(render_route(tree, placed))
        if unplaced:
            parts.append(
                '<div class="unplaced">'
                "<h3>Hand-written workbench text that could not be placed (verbatim)</h3>"
                '<p class="note">No line is dropped: if a section does not '
                "match a graph node, it lands here whole.</p>"
                + render_workbench_sections(unplaced)
                + "</div>"
            )
    if not WORKBENCH_MD.exists():
        parts.append(
            '<h3>Written by the orchestrator at the last return</h3>'
            '<p class="note">_build/workbench.md is absent, so the hand-written '
            "half is empty. It is written by hand at every return and "
            "git-ignored on purpose: it describes a moment, not a state of the "
            "tree.</p>"
        )

    # Generated corroboration: honest about what committed data can and cannot
    # say, so the hand-written half is corroborated, never replaced.
    plan_ok = PLAN_MD.exists()
    tasks = task_rows(read(PLAN_MD)) if plan_ok else []
    briefs = recent_briefs()
    parts.append(
        "<h3>Dispatched now, from committed evidence</h3>"
        '<p class="note">Live dispatch state lives in .claude/, which is never '
        "committed and which agents must not touch. What follows is generated "
        "from committed data only, so it corroborates the hand-written half "
        "rather than replacing it.</p>"
    )
    in_progress = [t for t in tasks if "IN PROGRESS" in t["verdict"].upper()]
    if in_progress:
        parts.append("<ul>")
        for t in in_progress:
            parts.append(
                f'<li>Task index marks <b>{clean(t["code"])}</b> IN PROGRESS: '
                f'{clean(t["task"])}</li>')
        parts.append("</ul>")
    else:
        parts.append('<p class="note">No task-index row is marked IN PROGRESS.</p>')
    if briefs:
        parts.append(
            "<h3>Newest briefs (by file mtime; no exact-code report means the "
            "return is not yet recorded under that code)</h3><ul>"
        )
        for b in briefs:
            status = "report exists" if b["returned"] else "no exact-code report"
            parts.append(
                f'<li>{clean(b["name"])} ({clean(fmt_mtime(b["mtime"]))}): '
                f'{clean(truncate(b["title"], 90))} <span class="badge neutral">'
                f'{clean(status)}</span></li>')
        parts.append("</ul>")

    try:
        data = load_ledger()
    except (OSError, tomllib.TOMLDecodeError):
        data = {}
    owed = data.get("owed", [])
    if owed:
        order = {"ready": 0, "in-flight": 1, "blocked": 2, "frozen": 3,
                 "at-risk": 4, "delivered": 5}
        owed_sorted = sorted(owed, key=lambda r: order.get(r.get("status", ""), 9))
        rows = "".join(
            f'<tr><td>{clean(r.get("id", ""))}</td>'
            f'<td>{clean(r.get("trophy", ""))}</td>'
            f'<td title="{clean(r.get("detail", ""))}">{clean(truncate(r.get("title", ""), 72))}</td>'
            f'<td><span class="badge {status_class(r.get("status", ""))}">'
            f'{clean(r.get("status", ""))}</span></td>'
            f'<td>{clean(r.get("blocked_by", "") or "-")}</td></tr>'
            for r in owed_sorted
        )
        parts.append(
            "<h3>Queued next: the ledger's owed table (the committed work queue)</h3>"
            '<table><thead><tr><th>id</th><th>trophy</th><th>work</th>'
            '<th>status</th><th>blocked by</th></tr></thead><tbody>'
            + rows + "</tbody></table>"
        )

    levers = data.get("lever", [])
    if levers:
        lever_rows = "".join(
            f'<tr><td>{clean(r.get("id", ""))}</td>'
            f'<td title="{clean(lever_what(r))}">{clean(truncate(lever_what(r), 55))}</td>'
            f'<td title="{clean(r.get("status", ""))}">{clean(truncate(r.get("status", ""), 60))}</td>'
            f'<td class="num">{clean(str(r.get("cost_low", "")))}-{clean(str(r.get("cost_high", "")))}</td>'
            f'<td class="num">{clean(str(r.get("net_low", "")))}-{clean(str(r.get("net_high", "")))}</td>'
            f'<td class="num">{clean(str(r.get("risk", "")))}</td>'
            f'<td>{clean(str(r.get("klass", "")))}</td></tr>'
            for r in levers
        )
        parts.append(
            "<h3>The lever rows: status, cost, net and risk</h3>"
            '<p class="note">The graph above shows where each lever sits; these '
            "rows carry the current status, cost, net and risk of each option "
            "from dev/ledger.toml.</p>"
            '<table><thead><tr><th>lever</th><th>what</th><th>status</th>'
            '<th>cost</th><th>net</th><th>risk</th><th>class</th></tr></thead>'
            "<tbody>" + lever_rows + "</tbody></table>"
        )

    srcs = [PLAN_MD] if plan_ok else []
    src = source_note(*srcs) if srcs else "source: dev/PLAN.md (missing)"
    brief_note = newest_brief_mtime()
    if brief_note is not None:
        src += f"; _build/briefs/ (newest mtime {fmt_mtime(brief_note)})"
    if WORKBENCH_MD.exists():
        src += "; _build/workbench.md (mtime " + fmt_mtime(mtime(WORKBENCH_MD)) + ")"
    if owed or levers or tree is not None:
        src += "; dev/ledger.toml (mtime " + fmt_mtime(mtime(LEDGER_TOML)) + ")"
    return panel(
        "The workbench route: where we are, what happens next, what would change it",
        "".join(parts), src, wide=True)


def render_page(now: datetime, out_path: Path) -> str:
    panels = [
        panel_workbench_route(),
        panel_lines(),
        panel_seconds(),
        panel_hierarchy(),
    ]
    body = "\n".join(panels)
    # Freshness is judged against the generation instant, not against the
    # pre-write file: the page this render produces is as fresh as `now`, and
    # a source touched after that instant is the only way it can be stale.
    stale = [label for label, when in source_stamps()
             if when is not None and when > now]
    if stale:
        foot = (
            '<p class="note"><b>Stale:</b> ' + clean(", ".join(stale))
            + ". Run make dashboard.</p>"
        )
    else:
        foot = ("<p class=\"note\">Fresh: regenerated at "
                + clean(now.strftime("%Y-%m-%d %H:%M UTC"))
                + " from the sources each panel names. Run "
                + "scripts/check-dashboard.py any time to verify.</p>")
    return (
        "<!DOCTYPE html>\n<html lang=\"en\">\n<head>\n<meta charset=\"utf-8\">\n"
        "<meta name=\"viewport\" content=\"width=device-width, initial-scale=1\">\n"
        "<title>Bedrock owner's dashboard</title>\n<style>\n" + CSS
        + "\n</style>\n</head>\n<body>\n<header>\n"
        "<h1>Bedrock owner's dashboard</h1>\n"
        f'<p class="meta">Generated {clean(now.strftime("%Y-%m-%d %H:%M UTC"))} by '
        "scripts/dashboard.py from the canonical data (dev/ledger.toml, "
        "dev/PLAN.md, _build/briefs). Every panel names its "
        "source and that source's mtime; a stale panel is visible, never "
        "silent.</p>\n</header>\n<main>\n"
        + body
        + "\n</main>\n<footer>"
        + foot
        + "</footer>\n</body>\n</html>\n"
    )


def main(argv: list[str]) -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--out", default=str(DEFAULT_OUT),
                    help="output HTML path (default _build/dashboard.html)")
    args = ap.parse_args(argv[1:])
    out_path = Path(args.out)
    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text(render_page(datetime.now(timezone.utc), out_path),
                        encoding="utf-8")
    print(f"dashboard written: {out_path}")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
