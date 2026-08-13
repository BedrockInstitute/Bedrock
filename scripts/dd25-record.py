#!/usr/bin/env python3
"""Read the DD25 review record BACK from the register, never from recall.

WHY THIS EXISTS, and it is one measured failure rather than a tidiness wish.
On 2026-08-11 the orchestrator told the owner, and wrote into a brief, that
DD25 had fired ten times with "six overturns and four upholds". The true
record was SEVEN overturns, two upholds and one split. The verdict cells in
`dev/PLAN.md` section 11 were correct the whole time. Nothing read them back.

`scripts/ledger.py` exists because a standing SIZE figure was quoted from a
paragraph for nine consecutive dispatches. This is the same failure on the
DISPATCH record, so it gets the same cure: one script, one source, and the
figure is never typed by hand.

`[LJ-1]`'s retrospective (`agents/reports/archive/lj-1-retrospective.md`) found the miscount
and named it a finding in its own right.

USE: `.venv/bin/python scripts/dd25-record.py`
     `.venv/bin/python scripts/dd25-record.py --phase LJ-2`
"""
from __future__ import annotations

import argparse
import pathlib
import re
import sys

PLAN = pathlib.Path(__file__).resolve().parent.parent / "dev" / "PLAN.md"

# A review row is a goal row whose code ends in `-R`. The verdict lives in the
# third cell, which section 11's format fixes as the status column.
ROW = re.compile(r"^\|\s*(?P<code>[A-Za-z0-9.\-]+-R)\s*\|(?P<desc>[^|]*)\|(?P<verdict>[^|]*)\|")

# The classifier is deliberately dumb. A verdict cell that says both words is
# a SPLIT, and a split must be counted as its own thing rather than rounded to
# whichever word came first: `[LJ-1.6-R]` upheld a stop and overturned the
# reason and the price, and calling that either name loses the finding.
def classify(verdict: str) -> str:
    v = verdict.upper()
    up, over = "UPHOLD" in v, "OVERTURN" in v
    if up and over:
        return "SPLIT"
    if over:
        return "OVERTURN"
    if up:
        return "UPHOLD"
    return "OPEN"


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--phase", default=None,
                    help="restrict to one phase prefix, for example LJ-1")
    args = ap.parse_args()

    if not PLAN.exists():
        print(f"dd25-record: {PLAN} not found", file=sys.stderr)
        return 2

    rows = []
    for line in PLAN.read_text().splitlines():
        m = ROW.match(line)
        if not m:
            continue
        code = m.group("code")
        if args.phase and not code.startswith(args.phase + "."):
            continue
        rows.append((code, classify(m.group("verdict")), m.group("verdict").strip()))

    if not rows:
        scope = f" for {args.phase}" if args.phase else ""
        print(f"dd25-record: no review rows found{scope}")
        return 0

    counts = {}
    for _, cls, _ in rows:
        counts[cls] = counts.get(cls, 0) + 1

    width = max(len(c) for c, _, _ in rows)
    for code, cls, raw in sorted(rows):
        print(f"  {code:<{width}}  {cls:<9}  {raw}")

    total = len(rows)
    parts = ", ".join(f"{n} {k.lower()}" for k, n in sorted(counts.items()))
    print(f"\ndd25-record: {total} review(s): {parts}")

    over = counts.get("OVERTURN", 0)
    if total:
        pct = 100.0 * over / total
        print(f"dd25-record: overturn rate {pct:.0f} percent")
        # The retrospective's judgment, kept here so the number arrives with
        # its meaning: DD25 paying is not the same as the upstream process
        # being healthy. A high rate says the returns are deciding on
        # inferences, which is what Change 1 attacks.
        if pct >= 60:
            print("dd25-record: a rate at or above 60 percent indicts the UPSTREAM "
                  "process, not the reviews. Classify each negative's deciding "
                  "claim MEASURED or INFERRED before it sets a verdict.")
    if counts.get("OPEN"):
        print(f"dd25-record: {counts['OPEN']} review(s) have no verdict word yet")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
