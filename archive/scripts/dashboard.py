#!/usr/bin/env python3
"""Owner's dashboard, GENERATED from the canonical data. Never hand-written.

The owner asked for a visual board (the current route, the ledger's remaining
lines in both calibers, the current cold-start seconds, the code hierarchy and
where the project is in it). The design
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
  _build/briefs/*.md   mtimes and title lines, to tell a dispatched brief
                       from a returned one
  scripts/ledger.py    standing, measured from HEAD (the one number this page
                       must not compute itself; ledger.toml's header says why)

The page is self-contained: one HTML file, inline CSS, no JavaScript, no
external fonts or network. The route flowchart is rendered as semantic HTML
with CSS: the structure is fixed in the generator, so a hand-laid-out diagram
beats a general layout engine, and the page needs neither mermaid nor a
network fetch. The workbench was DELETED on 2026-08-07 by the owner's
ruling, and with it the hand-written half this file used to parse, place onto
graph anchors and render. The route graph now stands alone on ledger rows, and
the agent table's `next` column reads the ledger's owed queue. The four-part
trophy split and the seconds distributions are drawn as inline SVG pie charts
generated in Python: an arc is arithmetic, no chart library and no network.

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


def ledger_trophy_split_line() -> str | None:
    """The four-part per-trophy caliber, from scripts/ledger.py --trophy-split.
    Returns None if the tool cannot run (the panel then says the split is
    unavailable rather than guessing)."""
    try:
        out = subprocess.run(
            [sys.executable, str(LEDGER_PY), "--trophy-split"],
            cwd=ROOT, capture_output=True, text=True, timeout=120,
        )
    except (OSError, subprocess.SubprocessError):
        return None
    if out.returncode != 0:
        return None
    return out.stdout.strip()


TROPHY_SPLIT_RE = re.compile(
    r"trophy split base ([\d,]+) \| ac-only ([\d,]+) \| shared ([\d,]+) \| "
    r"gch-only ([\d,]+) \| ac-total ([\d,]+) \| standing ([\d,]+)"
)


def parse_trophy_split(line: str) -> dict:
    """Parse the trophy-split line into plain numbers.

    The caliber measures the SURVIVING tree, so the last field is standing.

    Ruling D33: the split follows the RULED AC route, one reading only.

    >>> line = ("trophy split base 2,793 | ac-only 2,423 | shared 8,699 | "
    ...         "gch-only 5,308 | ac-total 13,915 | standing 19,223")
    >>> d = parse_trophy_split(line)
    >>> (d["ac_total"], d["standing"])
    (13915, 19223)
    """
    m = TROPHY_SPLIT_RE.match(line)
    if not m:
        raise ValueError(f"unrecognized trophy-split line: {line}")
    return {
        "base": int(m.group(1).replace(",", "")),
        "ac_only": int(m.group(2).replace(",", "")),
        "shared": int(m.group(3).replace(",", "")),
        "gch_only": int(m.group(4).replace(",", "")),
        "ac_total": int(m.group(5).replace(",", "")),
        "standing": int(m.group(6).replace(",", "")),
    }


def ledger_budget_line() -> str | None:
    """The AC budget strip's numbers, from scripts/ledger.py --budget (D36).
    Returns None when no budget is declared or the tool cannot run."""
    try:
        out = subprocess.run(
            [sys.executable, str(LEDGER_PY), "--budget"],
            cwd=ROOT, capture_output=True, text=True, timeout=120,
        )
    except (OSError, subprocess.SubprocessError):
        return None
    if out.returncode != 0:
        return None
    return out.stdout.strip()


BUDGET_RE = re.compile(
    r"ac budget \| cap ([\d,]+) \| measured ([\d,]+) "
    r"\| endpoint-naive ([\d,]+)-([\d,]+) \| endpoint-cal ([\d,]+)-([\d,]+) "
    r"\| headroom-naive ([+-][\d,]+) \| status (GREEN|AT-RISK|RED)$"
)


def parse_budget(line: str) -> dict:
    """Parse the budget line into plain numbers.

    >>> line = ("ac budget | cap 16,000 | measured 14,420 "
    ...         "| endpoint-naive 18,141-19,541 | endpoint-cal 20,115-23,651 "
    ...         "| headroom-naive -3,541 | status RED")
    >>> d = parse_budget(line)
    >>> (d["cap"], d["measured"], d["headroom"], d["status"])
    (16000, 14420, -3541, 'RED')
    """
    m = BUDGET_RE.match(line)
    if not m:
        raise ValueError(f"unrecognized budget line: {line}")
    num = lambda s: int(s.replace(",", "").replace("+", ""))
    return {
        "cap": num(m.group(1)), "measured": num(m.group(2)),
        "naive": (num(m.group(3)), num(m.group(4))),
        "cal": (num(m.group(5)), num(m.group(6))),
        "headroom": num(m.group(7)), "status": m.group(8),
    }


def ledger_trophy_matrix_line() -> str | None:
    """The nine cells of the trophy matrix, from scripts/ledger.py
    --trophy-matrix. Returns None if the tool cannot run (the panel then
    says the matrix is unavailable rather than guessing)."""
    try:
        out = subprocess.run(
            [sys.executable, str(LEDGER_PY), "--trophy-matrix"],
            cwd=ROOT, capture_output=True, text=True, timeout=120,
        )
    except (OSError, subprocess.SubprocessError):
        return None
    if out.returncode != 0:
        return None
    return out.stdout.strip()


MATRIX_RE = re.compile(
    r"trophy matrix \| ac-standing ([\d,]+) \| gch-standing ([\d,]+) "
    r"\| both-standing ([\d,]+) "
    r"\| ac-naive ([\d,]+)-([\d,]+) \| gch-naive ([\d,]+)-([\d,]+) "
    r"\| both-naive ([\d,]+)-([\d,]+) "
    r"\| ac-calibrated ([\d,]+)-([\d,]+) \| gch-calibrated ([\d,]+)-([\d,]+) "
    r"\| both-calibrated ([\d,]+)-([\d,]+) \| both-equals-brief (yes|no)"
)


def parse_trophy_matrix(line: str) -> dict:
    """Parse the trophy-matrix line into plain numbers.

    The both column must equal the --brief endpoint. ledger.py asserts the
    equality in the same process that prints this line, and the identity
    field records the result, so a broken identity shows as no.

    >>> line = ("trophy matrix | ac-standing 10,026 | gch-standing 18,970 "
    ...         "| both-standing 19,085 | ac-naive 13,746-15,716 "
    ...         "| gch-naive 26,975-33,188 | both-naive 27,390-33,953 "
    ...         "| ac-calibrated 16,126-20,176 | gch-calibrated 33,600-48,515 "
    ...         "| both-calibrated 34,615-50,580 | both-equals-brief yes")
    >>> d = parse_trophy_matrix(line)
    >>> (d["ac"]["standing"], d["gch"]["standing"], d["both"]["standing"])
    (10026, 18970, 19085)
    >>> d["both"]["naive"]
    (27390, 33953)
    >>> d["identity_ok"]
    True
    """
    m = MATRIX_RE.match(line)
    if not m:
        raise ValueError(f"unrecognized trophy-matrix line: {line}")
    g = m.groups()

    def band(lo: str, hi: str) -> tuple[int, int]:
        return (int(lo.replace(",", "")), int(hi.replace(",", "")))

    return {
        "ac": {"standing": int(g[0].replace(",", "")),
               "naive": band(g[3], g[4]),
               "calibrated": band(g[9], g[10])},
        "gch": {"standing": int(g[1].replace(",", "")),
                "naive": band(g[5], g[6]),
                "calibrated": band(g[11], g[12])},
        "both": {"standing": int(g[2].replace(",", "")),
                 "naive": band(g[7], g[8]),
                 "calibrated": band(g[13], g[14])},
        "identity_ok": g[15] == "yes",
    }


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

    # The lever subtree is gone, 2026-08-07: it went with the lever table, and
    # the builder went with it once nothing rendered it. `bucket` and the
    # `groups` classification below existed only to fill its leaves.
    return {"campaign": campaign}


def route_block() -> tuple[dict | None, Path | None, str]:
    """Build the route decision tree from the ledger (see build_route)."""
    try:
        data = load_ledger()
    except (OSError, tomllib.TOMLDecodeError) as exc:
        return None, None, f"dev/ledger.toml unreadable: {exc}"
    if not data:
        return None, None, "dev/ledger.toml is unreadable"
    return (build_route(data), LEDGER_TOML,
            "The graph comes from the lever rows and the owed statuses in "
            "dev/ledger.toml. Nobody copies it from prose. A leaf changes "
            "when its row changes.")


def render_route_node(node: dict, depth: int = 0) -> str:
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
    out = [f'<div class="{cls}">{label}{leaves}{anchor_html}</div>']
    for e in node.get("edges", []):
        out.append(
            '<div class="edge"><span class="edge-label">'
            f'{clean(e["label"])}</span><span class="edge-line"></span></div>'
            f'<div class="child">{render_route_node(e["to"], depth + 1)}</div>'
        )
    return "".join(out)


def render_route(tree: dict) -> str:
    """The route panel body: two independent branches, one column each, with
    the hand-written workbench content attached to the anchored nodes."""
    return (
        '<div class="route">'
        '<div class="branch">'
        '<h3>Campaign: freeze on or off, and what each answer releases</h3>'
        '<div class="flow">' + render_route_node(tree["campaign"])
        + "</div></div>"
        # The lever branch is not drawn, 2026-08-07: it answered "what should
        # we compress", which is a question for a decision, not for a board.
        + ("" if "lever" not in tree else
           '<div class="branch">'
           '<h3>Lever branch: five questions in order</h3>'
           '<div class="flow">' + render_route_node(tree["lever"])
           + "</div></div>")
        + "</div>"
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
td.measured { color: var(--accent); }
.badge { display: inline-block; padding: 2px 7px; font-family: var(--mono);
  font-size: 0.64rem; font-weight: 600; letter-spacing: 0.04em;
  white-space: nowrap; }
.badge.now { background: var(--now); color: var(--now-ink);
  border: 1px solid var(--decision-line); }
.badge.done { background: var(--done); color: var(--ok); }
.badge.planned { background: var(--plan-bg); color: var(--plan-ink); }
.badge.neutral { background: var(--neutral); color: var(--ink2); }
/* The agent table's three states, 2026-08-07: each label its own colour, so
   the row's state reads before the text does. `next` borrows the planned
   blue, `flight` the live amber, `returned` the delivered green. */
.badge.st-next { background: var(--plan-bg); color: var(--plan-ink); }
.badge.st-flight { background: var(--now); color: var(--now-ink);
  box-shadow: inset 0 0 0 1px var(--accent); }
.badge.st-returned { background: var(--done); color: var(--ok); }
.badge.st-over { background: var(--warn-bg); color: var(--warn); }
td.over { color: var(--warn); font-weight: 600; }
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
.route { display: grid; grid-template-columns: 1fr; gap: 24px; }
/* One branch since the lever subtree was dropped on 2026-08-07: the
   two-column grid left the campaign tree in half the width. */
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
  align-items: start; border: 1px solid var(--line);
  padding: 8px 10px; margin: 6px 0; background: var(--sunk); }
.position { margin-top: 10px; border: 1px solid var(--decision-line);
  background: var(--now); padding: 10px 12px; }
.position-tag { display: block; font-family: var(--mono); font-size: 0.62rem;
  font-weight: 700; letter-spacing: 0.12em; color: var(--now-ink);
  text-transform: uppercase; margin-bottom: 5px; }
.position-text { color: var(--now-ink); }
  padding-top: 8px; font-size: 0.75rem; }
  letter-spacing: 0.1em; text-transform: uppercase; color: var(--muted); }
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

def trophy_matrix_table(matrix: dict) -> str:
    """The nine cells as one table.

    Standing is a measured point. Each endpoint is a band. The board says the
    columns do not add up, because AC standing and GCH standing both count the
    base and the shared parts. Without that note, the first reader reports
    the correct arithmetic as a bug."""
    def band(col: str, key: str) -> str:
        lo, hi = matrix[col][key]
        return f"{lo:,} to {hi:,}"

    rows = (
        "<tr><th>standing</th>"
        + f'<td class="num measured">{matrix["ac"]["standing"]:,}</td>'
        + f'<td class="num measured">{matrix["gch"]["standing"]:,}</td>'
        + f'<td class="num measured">{matrix["both"]["standing"]:,}</td></tr>'
        "<tr><th>endpoint, naive</th>"
        + f'<td class="num">{band("ac", "naive")}</td>'
        + f'<td class="num">{band("gch", "naive")}</td>'
        + f'<td class="num">{band("both", "naive")}</td></tr>'
        "<tr><th>endpoint, calibrated</th>"
        + f'<td class="num">{band("ac", "calibrated")}</td>'
        + f'<td class="num">{band("gch", "calibrated")}</td>'
        + f'<td class="num">{band("both", "calibrated")}</td></tr>'
    )
    return (
        "<h3>The trophy matrix</h3>"
        '<p class="note">An endpoint is standing plus the rows the trophy '
        "needs. The three columns do not add up. That is correct. AC standing "
        "and GCH standing both count the base and the shared parts. The "
        "AC-and-GCH column equals the endpoint that scripts/ledger.py --brief "
        "prints. Standing is measured from HEAD.</p>"
        '<table><thead><tr><th></th><th>AC trophy</th><th>GCH trophy</th>'
        '<th>AC and GCH</th></tr></thead><tbody>' + rows + "</tbody></table>"
    )


def panel_lines() -> str:
    matrix_line = ledger_trophy_matrix_line()
    matrix = parse_trophy_matrix(matrix_line) if matrix_line else None
    split_line = ledger_trophy_split_line()
    split = parse_trophy_split(split_line) if split_line else None
    try:
        data = load_ledger()
    except (OSError, tomllib.TOMLDecodeError) as exc:
        return panel("The trophy matrix: three calibers by three trophies",
                     no_data(f"dev/ledger.toml unreadable: {exc}"),
                     source_note(LEDGER_TOML))
    body = ""
    if matrix is None:
        body += ('<div class="missing">Trophy matrix unavailable: '
                 'scripts/ledger.py --trophy-matrix failed. The cells are '
                 'computed there, so this board does not guess them.</div>')
    else:
        body += trophy_matrix_table(matrix)
    budget_line = ledger_budget_line()
    budget = parse_budget(budget_line) if budget_line else None
    if budget is not None:
        # THE AC BUDGET STRIP (D36). The tripwire arms on the MEASURED number;
        # the endpoint projection goes red first and blocks nothing (D26).
        badge = {"GREEN": "st-returned", "AT-RISK": "st-flight",
                 "RED": "st-over"}.get(budget["status"], "st-over")
        klass = "measured" if budget["status"] == "GREEN" else "over"
        body += (
            "<h3>The AC budget, ruling D36</h3>"
            f'<p class="note">The pure AC closure must land under '
            f'<b>{budget["cap"]:,}</b> lines. The bar it beats: the '
            f"internalization route delivered L&nbsp;&#8871;&nbsp;AC at 17,496 "
            f"lines, and its probed compression floor was 16,000, which [T205] "
            f"found unsupported and the owner replaced with 20,000 on "
            f"2026-08-09. The tripwire "
            f"arms on the measured number only.</p>"
            f'<table><thead><tr><th>cap</th><th>measured now</th>'
            f"<th>endpoint, naive</th><th>endpoint, calibrated</th>"
            f"<th>headroom vs naive top</th><th>status</th></tr></thead>"
            f"<tbody><tr>"
            f'<td class="num">{budget["cap"]:,}</td>'
            f'<td class="num measured">{budget["measured"]:,}</td>'
            f'<td class="num">{budget["naive"][0]:,}-{budget["naive"][1]:,}</td>'
            f'<td class="num">{budget["cal"][0]:,}-{budget["cal"][1]:,}</td>'
            f'<td class="num {klass}">{budget["headroom"]:+,}</td>'
            f'<td><span class="badge {badge}">{budget["status"]}</span></td>'
            f"</tr></tbody></table>"
        )
    if split is not None:
        split_slices = [
            {"label": "1. base, outside L", "value": split["base"],
             "band": None, "color": "--pie-1"},
            {"label": "2. AC alone on L", "value": split["ac_only"],
             "band": None, "color": "--pie-2"},
            {"label": "3. shared with GCH", "value": split["shared"],
             "band": None, "color": "--pie-3"},
            {"label": "4. GCH alone on L", "value": split["gch_only"],
             "band": None, "color": "--pie-4"},
        ]
        body += (
            "<h3>How much of the tree both trophies share</h3>"
            '<p class="note">This counts the SURVIVING tree, like every other '
            "figure on this board, and it excludes the retirement set. Part 1 "
            "is everything outside L. Part 2 is the L content only AC needs. "
            "Part 3 is the L content both trophies need. Part 4 is the L "
            "content only GCH needs, and it is shown for the check. The four "
            "parts sum to standing.</p>"
            # One reading only, per ruling D33: the split follows the ruled AC route,
            # and the delivered-endpoint reading is retired by the owner's word.

            
            '<div class="pie-wrap">'
            + render_pie_chart("The standing tree, four parts", split_slices)
            + "</div>"
        )
    else:
        body += ('<div class="missing">Trophy split unavailable: '
                 'scripts/ledger.py --trophy-split failed. The four-part pie '
                 "is not drawn.</div>")
    # Standing is MEASURED by scripts/ledger.py, never read from the toml, so
    # both the matrix and the split are named as script outputs. Dropping the
    # script names when the raw table went was a real loss of provenance and
    # the test suite caught it.
    src = (source_note(LEDGER_TOML)
           + "; scripts/ledger.py --brief, --trophy-split and --trophy-matrix "
           "(measure standing and compute the cells)")
    return panel("The trophy matrix: three calibers by three trophies",
                 body, src, wide=True)


def panel_seconds() -> str:
    try:
        data = load_ledger()
    except (OSError, tomllib.TOMLDecodeError) as exc:
        return panel("Cold-start seconds (current only)",
                     no_data(f"dev/ledger.toml unreadable: {exc}"),
                     source_note(LEDGER_TOML), wide=True)
    timing = data.get("timing", {})
    full = timing.get("full_cold_seconds")
    if full is None:
        return panel("Cold-start seconds (current only)",
                     no_data("[timing].full_cold_seconds is absent from dev/ledger.toml"),
                     source_note(LEDGER_TOML), wide=True)
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
            "<h3>Where the cold check spends its time</h3>"
            '<p class="note">These seconds come from a profile run recorded in '
            "dev/ledger.toml. Nobody pinned the ratio of profile time to wall "
            "time. The timing note gives 0.6 to 0.7. Each part is a named hot "
            f"module. The last part is all other modules. The total is {full:,} "
            "seconds.</p>"
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
            "<h3>Tree cost: the subtree split</h3>"  # the table below shares it
            '<p class="note">The tree_cost rows come from the profile BEFORE '
            f"the fixes. They sum to {cost_total:,} seconds. The timing note "
            "records that profile as 2,723 seconds, which agrees after "
            "rounding. This total is NOT the current check total. The two "
            "numbers are different measurements. Do not add them.</p>"
            '<div class="pie-wrap">'
            + render_pie_chart("Pre-fix profile seconds, by subtree", cost_slices)
            + "</div>"
        )
    # The raw [[tree_cost]] table under the pie is REMOVED, 2026-08-07, at the
    # owner's direction: the pie already draws the same rows, and a chart with
    # its own source data printed underneath is the board restating itself.
    cost_table = ""

    src = source_note(LEDGER_TOML)
    # Full width, 2026-08-07 at the owner's direction. This panel now carries
    # three subsections and two pies. Every other panel on the board is wide,
    # so a half-width one here also broke the column rhythm.
    return panel("Cold-start seconds: current check and its distribution",
                 stats + pie_html + cost_pie + hot_table + cost_table, src,
                 wide=True)


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


# ---------------------------------------------------------------------------
# THE WORKBENCH IS GONE, 2026-08-07, by the owner's ruling: _build/workbench.md
# is deleted and no longer written or maintained.
#
# It existed because a board cannot know what the orchestrator intends to do
# next, and for a day it was the only source for that. What it cost was a
# hand-edited file at every return, a parser with five heading forms, a
# placement pass onto graph anchors, and a fallback renderer for everything
# that did not place. All of that is removed here.
#
# What replaces the one thing it uniquely supplied: the agent table's `next`
# column now reads the ledger's [[owed]] rows in status order. That is weaker
# in one specific way and the weakness is stated rather than hidden. The owed
# rows say what is READY, not what will be dispatched first, so the
# orchestrator's ordering judgement no longer reaches the board. It reaches
# the ledger, dev/PLAN.md and the commit messages instead, all of which are
# committed and reviewable, which the workbench never was.
# ---------------------------------------------------------------------------

def panel_route() -> str:
    """The route graph, built from the ledger and nothing else.

    It was a merged panel until 2026-08-07: the graph plus the orchestrator's
    hand-written workbench attached to the nodes it named. The workbench is
    gone, so the graph stands alone and every leaf in it is a ledger row that
    changes the moment its row does.
    """
    tree, _path, note = route_block()
    parts: list[str] = []
    if tree is None:
        parts.append(no_data(f"route graph: {note}"))
    else:
        parts.append(f'<p class="note">{clean(note)}</p>')
        parts.append(render_route(tree))
    src = source_note(LEDGER_TOML)
    return panel("The route: where we are, and what each answer releases",
                 "".join(parts), src, wide=True)


AGENT_RETURNED_MAX = 10
AGENT_NEXT_MAX = 10


def owed_next(limit: int = AGENT_NEXT_MAX) -> list[dict]:
    """The work queue, in status order, as the agent table's `next` rows.

    This replaced the orchestrator's hand-written NEXT list when the workbench
    was deleted. It answers a slightly different question and the difference is
    stated on the board: these rows are what is READY, not what will be
    dispatched first. Ordering is a judgement and no longer reaches the board.
    """
    try:
        data = load_ledger()
    except (OSError, tomllib.TOMLDecodeError):
        return []
    order = {"ready": 0, "exempt": 1, "in-flight": 2, "blocked": 3,
             "frozen": 4, "at-risk": 5}
    rows = [r for r in data.get("owed", []) if r.get("status") != "delivered"]
    rows.sort(key=lambda r: order.get(r.get("status", ""), 9))
    return rows[:limit]


def panel_agents() -> str:
    plan_ok = PLAN_MD.exists()
    tasks = task_rows(read(PLAN_MD)) if plan_ok else []
    briefs = recent_briefs()

    def is_live(v: str) -> bool:
        u = v.upper()
        return "DISPATCHED" in u or "IN PROGRESS" in u

    live = [t for t in tasks if is_live(t["verdict"])]
    done = [t for t in tasks if not is_live(t["verdict"])][-AGENT_RETURNED_MAX:]
    unreturned = {b["name"] for b in briefs if not b["returned"]}

    # Order is the owner's, 2026-08-07: next first, then in flight, then
    # returned. A board is read top down and the question at the top should be
    # the one being decided, not the one already answered.
    rows = []
    nxt = owed_next()
    for r in nxt:
        release = r.get("blocked_by") or r.get("status", "")
        rows.append(
            '<tr><td><span class="badge st-next">next</span></td>'
            f'<td>{clean(r.get("id", ""))}</td>'
            f'<td title="{clean(r.get("detail", ""))}">{clean(truncate(r.get("title", ""), 62))}</td>'
            f'<td><span class="badge {status_class(r.get("status", ""))}">'
            f'{clean(r.get("status", ""))}</span> {clean(truncate(release, 70))}</td></tr>')
    if not nxt:
        rows.append('<tr><td><span class="badge st-next">next</span></td>'
                    '<td colspan="3" class="note">The ledger has no owed row that is '
                    "not yet delivered.</td></tr>")
    if live:
        for t_ in live:
            hint = "brief has no report yet" if any(
                t_["code"].lower().replace("l3.32-", "") in b for b in unreturned) else ""
            rows.append(
                '<tr class="live"><td><span class="badge st-flight">in flight</span></td>'
                f'<td>{clean(t_["code"])}</td>'
                f'<td title="{clean(t_["task"])}">{clean(truncate(t_["task"], 62))}</td>'
                f'<td>{clean(t_["verdict"])}{" &middot; " + clean(hint) if hint else ""}</td></tr>')
    else:
        rows.append('<tr class="live"><td><span class="badge st-flight">in flight</span></td>'
                    '<td colspan="3" class="note">Nothing dispatched. The task index '
                    "shows no row as DISPATCHED or IN PROGRESS.</td></tr>")
    for t_ in reversed(done):
        rows.append(
            '<tr><td><span class="badge st-returned">returned</span></td>'
            f'<td>{clean(t_["code"])}</td>'
            f'<td title="{clean(t_["task"])}">{clean(truncate(t_["task"], 62))}</td>'
            f'<td title="{clean(t_["verdict"])}">{clean(truncate(t_["verdict"], 88))}</td></tr>')

    body = (
        '<p class="note">This table shows three states. '
        "<b>Returned</b> and <b>in flight</b> come from the task index in "
        "dev/PLAN.md. The live agent data stays in .claude/, and nobody "
        "commits that directory. Thus this table shows only committed data. "
        "<b>Next</b> comes from the owed rows in the ledger, in status order. "
        "Those rows show which work is ready. They do not show which work "
        "goes first. The orchestrator decides the order, and this page does "
        "not show that decision.</p>"
        '<table><thead><tr><th>state</th><th>code</th><th>task</th>'
        "<th>result, or what releases it</th></tr></thead><tbody>"
        + "".join(rows) + "</tbody></table>"
    )
    srcs = [PLAN_MD] if plan_ok else []
    src = source_note(*srcs) if srcs else "source: dev/PLAN.md (missing)"
    src += "; dev/ledger.toml (mtime " + fmt_mtime(mtime(LEDGER_TOML)) + ")"
    return panel("Agents: next, in flight, returned", body, src, wide=True)


def render_page(now: datetime, out_path: Path) -> str:
    # Order is the owner's, 2026-08-07: what is happening first, then why,
    # then the two measured quantities. `panel_hierarchy` is deliberately not
    # here: the module tree answered no question the other panels do not, and
    # a board is judged by what it makes you look at. The function is kept so
    # restoring it is one line.
    panels = [
        panel_agents(),
        panel_route(),
        panel_lines(),
        panel_seconds(),
    ]
    body = "\n".join(panels)
    # Freshness is judged against the generation instant, not against the
    # pre-write file: the page this render produces is as fresh as `now`, and
    # a source touched after that instant is the only way it can be stale.
    stale = [label for label, when in source_stamps()
             if when is not None and when > now]
    if stale:
        foot = (
            '<p class="note"><b>This page is stale.</b> These sources changed '
            "after the generator made the page: " + clean(", ".join(stale))
            + ". Run make dashboard.</p>"
        )
    else:
        foot = ("<p class=\"note\">This page is fresh. The generator made it at "
                + clean(now.strftime("%Y-%m-%d %H:%M UTC"))
                + " from the sources that each panel names. "
                + "Run scripts/check-dashboard.py to check this again.</p>")
    return (
        "<!DOCTYPE html>\n<html lang=\"en\">\n<head>\n<meta charset=\"utf-8\">\n"
        "<meta name=\"viewport\" content=\"width=device-width, initial-scale=1\">\n"
        "<title>Bedrock owner's dashboard</title>\n<style>\n" + CSS
        + "\n</style>\n</head>\n<body>\n<header>\n"
        "<h1>Bedrock owner's dashboard</h1>\n"
        f'<p class="meta">scripts/dashboard.py made this page at '
        f'{clean(now.strftime("%Y-%m-%d %H:%M UTC"))}. '
        "It reads dev/ledger.toml, dev/PLAN.md and _build/briefs. "
        "Each panel names its source and the time of the last change to that "
        "source. You always see a stale panel.</p>\n</header>\n<main>\n"
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
