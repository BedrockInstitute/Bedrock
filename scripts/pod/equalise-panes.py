#!/usr/bin/env python3
"""Give every agent column the same width, by setting each right-split's ratio.

WHY. A `pane split` halves its target, so columns opened off the rightmost one come out
130, 65, 32, 32: each new column is half the last and the fourth is unreadable. MEASURED
2026-08-18 in a scratch workspace.

THE ARITHMETIC. Right-splits nest, so the k-th split from the root governs the boundary
between column k and everything right of it. For N equal columns the k-th ratio is
1/(N-k+1): 0.25, 0.3333, 0.5 for four. Verified in the same workspace: 65, 65, 65, 64.

`herdr pane resize --amount` moves a boundary and the layout reports the resulting ratio,
so the target ratio is reached by asking for the delta from where it is now.

IT NEVER RAISES. A layout that cannot be read, a pane that has gone, a herdr that is not
running: each leaves the panes as they are, which is untidy and never broken.
"""
import json
import subprocess
import sys


def _herdr(*args):
    r = subprocess.run(["herdr", *args], capture_output=True, text=True)
    if r.returncode != 0:
        raise RuntimeError(r.stderr.strip()[:120] or "herdr failed")
    return json.loads(r.stdout)["result"]


def equalise(pane: str) -> str:
    lay = _herdr("pane", "layout", "--pane", pane)["layout"]
    rights = [s for s in lay["splits"] if s["direction"] == "right"]
    if len(rights) < 2:
        return "one column, nothing to equalise"
    # The splits arrive outermost first, which is the order the arithmetic needs.
    n = len(rights) + 1
    moved = 0
    for k, s in enumerate(rights, start=1):
        want = 1.0 / (n - k + 1)
        have = float(s.get("ratio", 0.5))
        delta = round(have - want, 4)
        if abs(delta) < 0.005:
            continue
        # The pane on the RIGHT of this boundary owns it for a `left` nudge.
        target = _right_of(lay, s)
        if not target:
            continue
        _herdr("pane", "resize", "--pane", target, "--direction", "left",
               "--amount", str(delta))
        moved += 1
    return f"{n} columns equalised, {moved} boundary/boundaries moved"


def _right_of(lay, split):
    """The leftmost pane whose left edge sits at this split's boundary."""
    r = split["rect"]
    edge = r["x"] + int(r["width"] * float(split.get("ratio", 0.5)))
    best, bestd = None, 10**9
    for p in lay["panes"]:
        d = abs(p["rect"]["x"] - edge)
        if d < bestd:
            best, bestd = p["pane_id"], d
    return best if bestd <= 3 else None


if __name__ == "__main__":
    try:
        print(equalise(sys.argv[1]))
    except Exception as exc:                    # noqa: BLE001. Tidiness never breaks a run
        print(f"equalise skipped: {exc}", file=sys.stderr)
