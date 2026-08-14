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

`[LJ-1]`'s retrospective (`agents/tasks/archive/LJ-1-RETROSPECTIVE/lj-1-retrospective.md`) found the miscount
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
# THE `-R` SUFFIX UNDERCOUNTS, and [LJ-1.211] MEASURED the gap: six DD25 reviews
# carry an ordinary task code and name their target in the row instead. So the
# population is the WIDE definition `check-dd25-review-named.py` already uses: a
# `-R` row, OR any row whose own text says it is a DD25 review. A register that
# reads a narrower population than the gate would disagree with the gate.
ROW = re.compile(r"^\|\s*(?P<code>[A-Za-z0-9.\-]+-R)\s*\|(?P<desc>[^|]*)\|(?P<verdict>[^|]*)\|")
ROW_WIDE = re.compile(
    r"^\|\s*(?P<code>[A-Za-z0-9.\-]+)\s*\|(?P<desc>[^|]*)\|(?P<verdict>[^|]*)\|")
IS_REVIEW = re.compile(r"DD25 review|adversarial review of", re.I)

# The classifier is deliberately dumb. A verdict cell that says both words is
# a SPLIT, and a split must be counted as its own thing rather than rounded to
# whichever word came first: `[LJ-1.6-R]` upheld a stop and overturned the
# reason and the price, and calling that either name loses the finding.
def classify(verdict: str) -> str:
    # UPHELD IS THE COMMON SPELLING AND THE FIRST VERSION MISSED IT, so a cell
    # reading "SPLIT: measures upheld, conclusions overturned" counted as a
    # plain OVERTURN and the headline rate read 71 percent instead of 64.
    # MEASURED by [LJ-1.211] against dev/PLAN.md:624. The docstring already said
    # a split is its own category; only the matcher did not.
    v = verdict.upper()
    up = "UPHOLD" in v or "UPHELD" in v
    over = "OVERTURN" in v or "OVERTURNED" in v
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
        # THE WIDE POPULATION, [LJ-1.211]'s change 2. A `-R` row is a review by
        # its code; any other row is a review when its own text says so. Reading
        # a narrower population than `check-dd25-review-named.py` would let the
        # register and the gate disagree about what DD25 has done.
        m = ROW.match(line)
        if not m:
            m = ROW_WIDE.match(line)
            if not m or not IS_REVIEW.search(line):
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

    # THE DENOMINATOR IS THE DECIDED REVIEWS, NOT THE POPULATION. Widening the
    # population to [LJ-1.211]'s definition pulled in rows whose verdict cell
    # has no verdict word yet, and dividing by those reads an undecided review
    # as "not an overturn". MEASURED the moment the widening landed: 11 of 36
    # printed 31 percent while 11 of 24 decided is 46. An open review is not
    # evidence in either direction and it is excluded from the rate and named
    # separately.
    over = counts.get("OVERTURN", 0)
    decided = total - counts.get("OPEN", 0)
    if decided:
        pct = 100.0 * over / decided
        print(f"dd25-record: overturn rate {pct:.0f} percent "
              f"({over} of {decided} DECIDED; {counts.get('OPEN', 0)} open are excluded)")
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
