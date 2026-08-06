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
                       [[lever]] rows, [[owed]] rows
  dev/LEDGER.md        the "Which route, under which condition" mermaid block
  dev/PLAN.md          section 11: MASTER status table (96 rows) and the Task
                       index (112 rows)
  _build/briefs/*.md   mtimes and title lines for the workbench panel
  scripts/ledger.py    standing, measured from HEAD (the one number this page
                       must not compute itself; dev/LEDGER.md explains why)

The page is self-contained: one HTML file, inline CSS, no JavaScript, no
external fonts or network. The flowchart is emitted as its labelled mermaid
source in a <pre> block, not rendered: no mermaid renderer is vendored in the
repository and the page must not fetch one over the network. The source IS the
canonical data, so showing it verbatim is the honest choice.

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
import re
import subprocess
import sys
import tomllib
from collections import defaultdict
from datetime import datetime, timezone
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
LEDGER_TOML = ROOT / "dev" / "ledger.toml"
LEDGER_MD = ROOT / "dev" / "LEDGER.md"
PLAN_MD = ROOT / "dev" / "PLAN.md"
LEDGER_PY = ROOT / "scripts" / "ledger.py"
BRIEFS_DIR = ROOT / "_build" / "briefs"
DEFAULT_OUT = ROOT / "_build" / "dashboard.html"

# Sources the generated page derives from, in staleness-check order. The briefs
# directory is represented by its newest file's mtime, which is what actually
# matters: an edited brief is newer than the page and must trigger a rebuild.
SOURCE_FILES = (LEDGER_TOML, LEDGER_MD, PLAN_MD, LEDGER_PY, Path(__file__))

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
# The route flowchart (mermaid source, lifted verbatim)
# ---------------------------------------------------------------------------

MERMAID_FENCE = re.compile(r"```mermaid\s*\n(.*?)```", re.S)


def extract_mermaid(text: str) -> str | None:
    """The first mermaid block whose first non-empty line starts with
    'flowchart'. Returns the block body verbatim, or None when the route
    flowchart is not in this text."""
    for block in MERMAID_FENCE.findall(text):
        first = next((ln.strip() for ln in block.splitlines() if ln.strip()), "")
        if first.lower().startswith("flowchart"):
            return block
    return None


def route_block() -> tuple[str | None, Path | None, str]:
    """BUILD the route flowchart from the ledger, do not lift a written one.

    A first version lifted a hand-written mermaid block out of dev/LEDGER.md.
    That block was correctly deleted the same day: a diagram is orientation for
    the owner, and the agent documents are being stripped to what changes what
    an agent DOES. Lifting it also had the defect every hand-written diagram
    has, which this project has now paid for twice in one day: it goes stale
    silently, and a flowchart with a stale node is worse than no flowchart.

    So the DECISION STRUCTURE is fixed here, because it is the ruled procedure
    (D22, D26, D30) and does not drift, while every LEAF is read from
    dev/ledger.toml. A lever that is refuted, superseded or funded shows as
    such the moment its row changes, with no second place to update.
    """
    data = load_ledger()
    if not data:
        return None, None, "dev/ledger.toml is unreadable"

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

    def names(key: str) -> str:
        got = groups.get(key, [])
        return "<br/>".join(got) if got else "none"

    frozen = [o for o in data.get("owed", []) if o.get("status") == "frozen"]
    freeze_note = (f"{len(frozen)} owed row(s) frozen" if frozen
                   else "nothing frozen")

    body = f"""flowchart TD
    Start["a slot is free"] --> Freeze{{"is D30's freeze lifted?"}}
    Freeze -- "no" --> Cost["THE CHECK-COST CAMPAIGN<br/>the only funded work<br/>({freeze_note})"]
    Cost --> Exit["exit condition: every module at or<br/>above 2 percent of tree cost profiled,<br/>every removable second removed or<br/>refused with a written price,<br/>and the craft recorded"]
    Exit --> Freeze
    Freeze -- "yes" --> Math["THE FROZEN MATHEMATICS RESUMES"]
    Math --> Bridge["the bridge landing: below-lim"]
    Bridge --> Rehome["the choice re-home"]
    Rehome --> AC["AC on surviving machinery"]
    Math --> StepInL["the StepInL rewrite"]
    StepInL --> W3["W3, the internal well-ordering"]
    W3 --> GCH["W7's residue, then the GCH sentence"]

    Start --> Lever{{"is a compression lever<br/>being considered?"}}
    Lever --> Refuted{{"has it been refuted?"}}
    Refuted -- "yes" --> Closed["NOT A ROUTE<br/>{names('refuted')}"]
    Refuted -- "no" --> Superseded{{"has ruled work<br/>already done part of it?"}}
    Superseded -- "yes" --> Reprice["RE-PRICE FIRST<br/>{names('superseded')}"]
    Superseded -- "no" --> Gated{{"priced at 3x with an<br/>unmeasured widest term?"}}
    Gated -- "yes" --> Probe["D22: PROBE FIRST<br/>{names('gated')}"]
    Gated -- "no" --> Touched{{"is its region being touched<br/>by ruled work anyway?"}}
    Touched -- "yes" --> Take["TAKE IT NOW<br/>marginal cost is near zero<br/>when the file is already open"]
    Touched -- "no" --> Need{{"does the endpoint projection<br/>need the lines?"}}
    Need -- "no" --> Wait["KEEP AND WAIT<br/>{names('waiting')}<br/>D26: a line overage never changes<br/>the ROUTE; a lever is compression<br/>WITHIN it"]
    Need -- "yes" --> Rank["rank by net lines per unit of risk,<br/>cheapest first"]

    Lever --> InRoute["already in the route:<br/>{names('in-route')}"]"""
    return body, LEDGER_TOML, ("built from dev/ledger.toml's lever rows and owed "
                               "statuses, not lifted from prose: a leaf changes "
                               "the moment its row does")


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
  --bg: #f5f4ef; --card: #ffffff; --ink: #1c1b1a; --muted: #6a675f;
  --line: #dcd9d0; --accent: #8a5a00; --now: #fff3c4; --done: #e7f2e2;
  --neutral: #eef0f2; --warn: #b3271d; --ok: #1f6f3d;
}
* { box-sizing: border-box; }
body { margin: 0; background: var(--bg); color: var(--ink);
  font-family: -apple-system, "Segoe UI", Roboto, Helvetica, Arial, sans-serif;
  line-height: 1.45; }
header { padding: 22px 28px 14px; border-bottom: 3px solid var(--accent); }
h1 { margin: 0 0 4px; font-size: 26px; letter-spacing: 0.2px; }
.meta { margin: 0; color: var(--muted); font-size: 13px; }
main { display: grid; grid-template-columns: 1fr 1fr; gap: 18px;
  padding: 22px 28px 8px; align-items: start; }
.panel { background: var(--card); border: 1px solid var(--line);
  border-radius: 8px; padding: 16px 18px 12px; }
.panel.wide { grid-column: 1 / -1; }
h2 { margin: 0 0 10px; font-size: 17px; border-bottom: 1px solid var(--line);
  padding-bottom: 6px; }
h3 { margin: 14px 0 6px; font-size: 13.5px; color: #3f3d38; }
.src { margin-top: 12px; padding-top: 8px; border-top: 1px dashed var(--line);
  color: var(--muted); font-size: 11.5px; font-family: ui-monospace, Menlo, Consolas, monospace; }
.stats { display: flex; flex-wrap: wrap; gap: 14px; margin: 4px 0 14px; }
.stat { flex: 1 1 170px; border: 1px solid var(--line); border-radius: 6px;
  padding: 10px 12px; background: #faf9f5; }
.stat .num { font-size: 34px; font-weight: 700; line-height: 1.1; }
.stat .lab { font-size: 12px; color: var(--muted); margin-top: 2px; }
.stat .sub { font-size: 12px; margin-top: 4px; }
table { border-collapse: collapse; width: 100%; font-size: 12.5px; }
th { text-align: left; color: var(--muted); font-weight: 600;
  border-bottom: 1px solid var(--line); padding: 5px 8px 5px 0; }
td { padding: 5px 8px 5px 0; border-bottom: 1px solid #f0ede5; vertical-align: top; }
tr:last-child td { border-bottom: none; }
.badge { display: inline-block; padding: 1px 7px; border-radius: 10px;
  font-size: 11px; font-weight: 600; white-space: nowrap; }
.badge.now { background: var(--now); color: #6b4e00; }
.badge.done { background: var(--done); color: var(--ok); }
.badge.planned { background: #e3ecf7; color: #1f4e79; }
.badge.neutral { background: var(--neutral); color: #3f3d38; }
.tree { max-height: 560px; overflow: auto; border: 1px solid var(--line);
  border-radius: 6px; padding: 6px 8px; font-size: 12.5px; }
.tree-row { padding: 2px 4px; border-radius: 4px; display: flex; gap: 8px;
  align-items: baseline; }
.tree-row.here { background: var(--now); }
.tree-row .code { font-family: ui-monospace, Menlo, Consolas, monospace;
  font-weight: 600; white-space: nowrap; }
.tree-row .goal { color: #4b4842; overflow: hidden; text-overflow: ellipsis;
  white-space: nowrap; }
.pre { background: #f8f7f2; border: 1px solid var(--line); border-radius: 6px;
  padding: 12px; overflow: auto; font-family: ui-monospace, Menlo, Consolas, monospace;
  font-size: 12px; line-height: 1.5; }
.note { font-size: 12.5px; color: var(--muted); margin: 8px 0; }
.missing { border: 1px solid var(--warn); color: var(--warn);
  background: #fdf1f0; border-radius: 6px; padding: 12px; font-size: 13px; }
footer { padding: 14px 28px 26px; color: var(--muted); font-size: 12px; }
ul { margin: 6px 0; padding-left: 20px; }
li { margin: 3px 0; }
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
# Panels
# ---------------------------------------------------------------------------

def panel_route() -> str:
    body, path, note = route_block()
    if body is None:
        return panel("Route: which route, under which condition",
                     no_data(note), "source: none")
    # The block carries class="mermaid" as well as the page's own class. Opened
    # from disk this changes nothing, since the page vendors no renderer and
    # deliberately fetches none; but a viewer that renders mermaid natively will
    # draw it, and that is free. The source stays readable either way, which is
    # the point: this file IS the canonical block from dev/LEDGER.md.
    label = ("Mermaid flowchart source, lifted verbatim. The page is "
             "self-contained and vendors no renderer, so this shows as source "
             "here and renders in any Mermaid-capable viewer.")
    inner = (
        f'<p class="note">{clean(note)}. {label}</p>\n'
        f'<pre class="mermaid pre">{clean(body)}</pre>'
    )
    src = source_note(path) if path is not None else "source: none"
    return panel("Route: which route, under which condition", inner, src, wide=True)


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
            f'<div class="stat"><div class="num">{brief["standing"]:,}</div>'
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
    table = (
        '<table><thead><tr><th>row</th><th>work</th><th>naive</th>'
        '<th>calibrated</th><th>class</th></tr></thead><tbody>'
    )
    for row in rows:
        table += (
            f'<tr><td>{clean(row["id"])}</td>'
            f'<td title="{clean(row["title"])}">{clean(truncate(row["title"], 90))}</td>'
            f'<td>{clean(row["naive"])}</td><td>{clean(row["calibrated"])}</td>'
            f'<td>{clean(truncate(row["klass"], 48))}</td></tr>'
        )
    table += "</tbody></table>"
    src = source_note(LEDGER_TOML, LEDGER_PY) + "; standing is not written down, it is computed"
    return panel("Remaining lines, current plus estimate", stats + table, src)


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
        f'<div class="stat"><div class="num">{full:,} s</div>'
        '<div class="lab">current full cold check, measured</div>'
        '<div class="sub">current only, no estimate; the measurement note: '
        f'{clean(note)}</div></div>'
        '</div>'
    )
    hot = data.get("hot", [])
    hot_rows = "".join(
        f'<tr><td>{clean(h.get("module", ""))}</td>'
        f'<td>{clean(str(h.get("seconds", "")))}</td>'
        f'<td>{clean(str(h.get("lines", "")))}</td>'
        f'<td title="{clean(h.get("why", ""))}">{clean(truncate(h.get("why", ""), 70))}</td></tr>'
        for h in hot
    )
    hot_table = (
        "<h3>Hot modules</h3>"
        '<table><thead><tr><th>module</th><th>seconds</th><th>lines</th>'
        '<th>why it costs</th></tr></thead><tbody>' + hot_rows + "</tbody></table>"
    )
    costs = data.get("tree_cost", [])
    cost_rows = "".join(
        f'<tr><td>{clean(c.get("tree", ""))}</td>'
        f'<td>{clean(str(c.get("modules", "")))}</td>'
        f'<td>{clean(str(c.get("lines", "")))}</td>'
        f'<td>{clean(str(c.get("seconds", "")))}</td>'
        f'<td>{clean(str(c.get("per_line", "")))}</td></tr>'
        for c in costs
    )
    cost_table = (
        "<h3>Tree cost</h3>"
        '<table><thead><tr><th>tree</th><th>modules</th><th>lines</th>'
        '<th>seconds</th><th>seconds/line</th></tr></thead><tbody>'
        + cost_rows + "</tbody></table>"
    )
    src = source_note(LEDGER_TOML)
    return panel("Cold-start seconds (current only)", stats + hot_table + cost_table, src)


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


def panel_workbench() -> str:
    """The one panel with a HAND-WRITTEN half, by the owner's ruling.

    The rest of this page is generated, which is what makes refreshing it one
    command. But the orchestrator's own state, what is dispatched right now and
    what is queued behind it, exists nowhere in committed data: it lives in
    `.claude/`, which is never committed. A generator cannot produce it and
    should not pretend to.

    So `_build/workbench.md` is written BY HAND at every return, and this panel
    shows it above the generated evidence. It is git-ignored on purpose: it
    describes a moment, not a state of the repository, and a stale committed
    copy of it would be worse than none. If it is absent the panel says so.
    """
    parts: list[str] = []
    plan_ok = PLAN_MD.exists()
    tasks = task_rows(read(PLAN_MD)) if plan_ok else []
    briefs = recent_briefs()

    if WORKBENCH_MD.exists():
        hand = read(WORKBENCH_MD).strip()
        parts.append(
            '<h3>Written by the orchestrator at the last return</h3>'
            f'<p class="note">{source_note(WORKBENCH_MD)}. Hand-written, not '
            'generated: no committed data carries it.</p>'
            f'<pre class="pre">{clean(hand)}</pre>'
        )
    else:
        parts.append(
            '<h3>Written by the orchestrator at the last return</h3>'
            '<p class="note">_build/workbench.md is absent, so this half of the '
            'panel is empty. It is hand-written at every return and git-ignored '
            'on purpose: it describes a moment, not a state of the tree.</p>'
        )

    # Dispatched now: honest about what committed data can and cannot say.
    parts.append(
        '<h3>Dispatched now, from committed evidence</h3>'
        '<p class="note">Live dispatch state lives in .claude/, which is never '
        'committed and which agents must not touch. What follows is generated '
        'from committed data only, so it corroborates the hand-written half '
        'rather than replacing it.</p>'
    )
    in_progress = [t for t in tasks if "IN PROGRESS" in t["verdict"].upper()]
    if in_progress:
        parts.append('<ul>')
        for t in in_progress:
            parts.append(
                f'<li>Task index marks <b>{clean(t["code"])}</b> IN PROGRESS: '
                f'{clean(t["task"])}</li>')
        parts.append('</ul>')
    else:
        parts.append('<p class="note">No task-index row is marked IN PROGRESS.</p>')
    if briefs:
        parts.append(
            "<h3>Newest briefs (by file mtime; no exact-code report means the "
            "return is not yet recorded under that code)</h3>"
            "<ul>"
        )
        for b in briefs:
            status = "report exists" if b["returned"] else "no exact-code report"
            parts.append(
                f'<li>{clean(b["name"])} ({clean(fmt_mtime(b["mtime"]))}): '
                f'{clean(truncate(b["title"], 90))} <span class="badge neutral">'
                f'{clean(status)}</span></li>')
        parts.append("</ul>")

    # Queued next: the ledger's owed table is the honest committed queue.
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

    # Conditions: the lever branch of the flowchart plus the lever rows.
    levers = data.get("lever", [])
    if levers:
        lever_rows = "".join(
            f'<tr><td>{clean(r.get("id", ""))}</td>'
            f'<td title="{clean(lever_what(r))}">{clean(truncate(lever_what(r), 55))}</td>'
            f'<td title="{clean(r.get("status", ""))}">{clean(truncate(r.get("status", ""), 60))}</td>'
            f'<td>{clean(str(r.get("cost_low", "")))}-{clean(str(r.get("cost_high", "")))}</td>'
            f'<td>{clean(str(r.get("net_low", "")))}-{clean(str(r.get("net_high", "")))}</td>'
            f'<td>{clean(str(r.get("risk", "")))}</td>'
            f'<td>{clean(str(r.get("klass", "")))}</td></tr>'
            for r in levers
        )
        parts.append(
            "<h3>What condition triggers what</h3>"
            '<p class="note">The route panel holds the condition graph (the '
            "freeze gate and the lever branch). These rows carry each lever "
            "option's current status, cost, net and risk from dev/ledger.toml.</p>"
            '<table><thead><tr><th>lever</th><th>what</th><th>status</th>'
            '<th>cost</th><th>net</th><th>risk</th><th>class</th></tr></thead>'
            "<tbody>" + lever_rows + "</tbody></table>"
        )

    srcs = [PLAN_MD] if plan_ok else []
    src = source_note(*srcs) if srcs else "source: dev/PLAN.md (missing)"
    brief_note = newest_brief_mtime()
    if brief_note is not None:
        src += f"; _build/briefs/ (newest mtime {fmt_mtime(brief_note)})"
    if owed or levers:
        src += "; dev/ledger.toml (mtime " + fmt_mtime(mtime(LEDGER_TOML)) + ")"
    return panel("Orchestrator's workbench", "".join(parts), src, wide=True)


def render_page(now: datetime, out_path: Path) -> str:
    panels = [
        panel_route(),
        panel_lines(),
        panel_seconds(),
        panel_hierarchy(),
        panel_workbench(),
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
        "dev/LEDGER.md, dev/PLAN.md, _build/briefs). Every panel names its "
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
