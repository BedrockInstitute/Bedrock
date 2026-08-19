#!/usr/bin/env python3
"""Pick and create the pane one agent dispatch will run in. ONE home for the layout rule.

**WHY THIS FILE EXISTS.** The rule used to live in about twenty five lines of shell inside
`launcher.py`'s driver string, steered by two state files, and it produced a layout the
driver's own comments had MEASURED as broken. Six dispatches in a scratch workspace on
2026-08-19 gave columns 145, 73, 36 and 36 wide and panes 62, 31, 16 and 8 rows tall, with
each column's BOTTOM pane spanning every column opened after it.

**THE CAUSE, and it is a property of `herdr pane split` and not a coding slip.** A split
divides ONE PANE'S RECTANGLE. To open a new full-height column you must split a
full-height pane. Once a column has been split DOWN it holds no full-height pane, so a
「new column」opened off that column's top pane is really a nested split inside the top
half: half height, and the bottom pane keeps the full width it had. The old driver kept
its `rightmost-column` file pointing at exactly that top pane. Its own docstring recorded
the failure and nothing connected the two.

**THE RULE, and it has two phases with no alternation inside either.**

1. **COLUMNS FIRST.** While fewer than `max_columns()` agent columns exist, a dispatch
   splits RIGHT off the rightmost column, or off BASE when there is none. Every pane is
   full height during this phase, so every right-split is a ROOT-LEVEL column boundary and
   `equalise-panes.py`'s arithmetic is exactly valid.
2. **ROWS SECOND.** Once the columns are open, a dispatch splits DOWN the LAST pane of
   the SHALLOWEST column, leftmost on a tie. A down-split divides a pane inside its own
   column and changes no column's width, so the equaliser is not run and cannot be
   confused, and the grid fills evenly left to right.

MEASURED 2026-08-19, eight dispatches at four columns: BASE 58 wide and full height, then
four columns 58 wide each holding two panes 31 rows tall, strictly left to right. Compare
the old rule's 36 by 8.

**PHASE 2 NEVER ENDS, so a dispatch is never refused for want of a slot.** The ninth
dispatch deepens a column to three rows, the thirteenth to four. Tidiness is never worth a
lost agent, which is the principle `equalise-panes.py` already states for its own errors.

**AND THE OVERFLOW MUST NOT OPEN A COLUMN, which the first version of this file got wrong
in exactly the way the old driver did.** MEASURED 2026-08-19 on the ninth dispatch: it
split RIGHT off column four's TOP pane, so the new column came out half height and column
four's BOTTOM pane widened to span both. Deepening is the only growth that leaves every
width alone.

**IT PRINTS A PANE ID ON STDOUT AND NOTHING ELSE, and it never raises.** Any failure
prints nothing, and the caller then falls back to its own split, so a broken layout costs
one ugly pane and never a dispatch.

Usage:
  pane-slot.py --base <PANE> [--cwd DIR] [--env K=V]... [--state DIR] [--plan]
"""
from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent.parent

#: The narrowest column this layout will open on purpose. MEASURED 2026-08-19: at four
#: columns beside BASE in a 290 column area every column came out 58 wide, which reads
#: Agda comfortably; the old rule's third column was 36 wide and its fourth pane 8 rows
#: tall. Below this a column is not worth opening and the second row is used instead.
MIN_COL_WIDTH = 56

#: ONE state file, one line per agent column, left to right: `<top>` or `<top> <bottom>`.
#: It replaced `herdr-open-column` and `herdr-rightmost-column`, which could disagree: on
#: 2026-08-19 the second named a DEAD pane while the first was empty, so the next dispatch
#: would have taken the BASE fallback that the driver's own comments measured as the worst
#: case. **It is ADVISORY and self-healing**: a line naming a pane herdr no longer has is
#: dropped on read, so a stale file costs one column and never a wrong split.
STATE_REL = Path(".pod-state") / "herdr-columns"


def _herdr(*args):
    """One herdr call. Returns the `result` object, or None. It never raises."""
    try:
        d = subprocess.run(["herdr", *args], capture_output=True, text=True, timeout=60)
    except (OSError, subprocess.SubprocessError):
        return None
    if d.returncode != 0:
        return None
    try:
        return json.loads(d.stdout)["result"]
    except (ValueError, KeyError, TypeError):
        return None


def layout(base: str) -> dict:
    return (_herdr("pane", "layout", "--pane", base) or {}).get("layout") or {}


def live_panes(base: str) -> set[str]:
    return {p["pane_id"] for p in layout(base).get("panes", [])}


def max_columns(base: str) -> int:
    """How many agent columns fit beside BASE at `MIN_COL_WIDTH`, at least one.

    It reads the area from the live layout rather than assuming a terminal size, because
    the answer changes when the owner resizes the window and a hardcoded count would then
    open columns nobody can read.
    """
    area = layout(base).get("area") or {}
    width = int(area.get("width") or 0)
    if width <= 0:
        return 4                               # a layout we cannot read: the measured 4
    return max(1, width // MIN_COL_WIDTH - 1)  # minus one, because BASE is a column too


def read_columns(state: Path, base: str) -> list[list[str]]:
    """The columns, left to right, with every dead pane dropped. `[[top], [top, bottom]]`."""
    try:
        text = (state / STATE_REL.name).read_text(encoding="utf-8")
    except OSError:
        return []
    alive = live_panes(base)
    out = []
    for line in text.split("\n"):
        ids = [i for i in line.split() if i in alive]
        if ids:
            out.append(ids)                    # a column may hold three panes or more
    return out


def write_columns(state: Path, cols: list[list[str]]) -> None:
    try:
        state.mkdir(parents=True, exist_ok=True)
        (state / STATE_REL.name).write_text(
            "\n".join(" ".join(c) for c in cols) + "\n", encoding="utf-8")
    except OSError:
        pass                                   # an unwritable state file costs one column


def plan(cols: list[list[str]], limit: int, base: str) -> tuple[str, str]:
    """The decision alone, as `(direction, source_pane)`. Pure, so a test can read it.

    TWO PHASES AND NOTHING ELSE. Below the column limit, open a column off the rightmost.
    At or above it, deepen the SHALLOWEST column, leftmost on a tie, by splitting its LAST
    pane. The source is the last pane and never the first, because splitting a column's top
    pane divides only the top half and leaves everything below it spanning wider.
    """
    if len(cols) < limit:
        return "right", (cols[-1][0] if cols else base)
    shallowest = min(range(len(cols)), key=lambda i: (len(cols[i]), i))
    return "down", cols[shallowest][-1]


def split(source: str, direction: str, cwd: str | None, env: list[str]) -> str | None:
    args = ["pane", "split", "--pane", source, "--direction", direction,
            "--ratio", "0.5", "--no-focus"]
    if cwd:
        args += ["--cwd", cwd]
    for e in env:
        args += ["--env", e]
    r = _herdr(*args)
    try:
        return r["pane"]["pane_id"]
    except (TypeError, KeyError):
        return None


def equalise(base: str) -> None:
    """Only after a RIGHT split. A down-split changes no column's width."""
    try:
        subprocess.run([sys.executable, str(Path(__file__).parent / "equalise-panes.py"),
                        base], capture_output=True, timeout=60)
    except (OSError, subprocess.SubprocessError):
        pass


def main(argv: list[str]) -> int:
    if "-h" in argv or "--help" in argv or not argv:
        print(__doc__)
        return 2
    base = cwd = None
    env: list[str] = []
    state = ROOT / ".pod-state"
    show_plan = False
    i = 0
    while i < len(argv):
        a = argv[i]
        if a == "--base" and i + 1 < len(argv):
            base = argv[i + 1]; i += 2
        elif a == "--cwd" and i + 1 < len(argv):
            cwd = argv[i + 1]; i += 2
        elif a == "--env" and i + 1 < len(argv):
            env.append(argv[i + 1]); i += 2
        elif a == "--state" and i + 1 < len(argv):
            state = Path(argv[i + 1]); i += 2
        elif a == "--plan":
            show_plan = True; i += 1
        else:
            print(f"pane-slot: unknown argument {a!r}", file=sys.stderr)
            return 2
    if not base:
        print("pane-slot: --base <PANE> is required", file=sys.stderr)
        return 2

    cols = read_columns(state, base)
    limit = max_columns(base)
    direction, source = plan(cols, limit, base)
    if show_plan:
        print(f"{direction} {source} (columns {len(cols)}/{limit})")
        return 0
    pane = split(source, direction, cwd, env)
    if pane is None:
        return 1                               # print NOTHING; the caller falls back
    if direction == "right":
        cols.append([pane])
        equalise(base)
    else:
        for c in cols:
            if source in c:                    # the source is the column's LAST pane
                c.append(pane)
                break
    write_columns(state, cols)
    print(pane)
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
