#!/usr/bin/env python3
"""Pins the peak clock of `scripts/dispatch_policy.py` (LJ-1.207).

THE RULE BEING PINNED, from the owner's instruction of 2026-08-14. DeepSeek
prices peak and off-peak, the off-peak price is half the peak price, and peak
is Beijing time 09:00 to 12:00 and 14:00 to 18:00. The dispatch mode follows
that clock: OFF-PEAK, `pi-subagent-mode` leads. PEAK,
`in-harness-subagent-mode` leads. `pi-subagent-mode` was `deepseek-subagent-
mode` until `[LJ-1.285]` renamed it 2026-08-15, off the vendor name; the
retired name still resolves through `ALIASES` (C-41).

THE PRECEDENCE. The owner's pinned `VERSION_IN_FORCE` wins, always. The clock
decides only when `VERSION_IN_FORCE` is `auto`. A tool that silently overrides
a ruling is worse than no tool, so the test pins the order.

THE WINDOWS ARE HALF-OPEN [start, end) at minute resolution. A minute belongs
to the window that STARTED at its hour, and the boundary instant itself
belongs to the window that is starting. So 09:00:00 and 14:00:00 are peak and
12:00:00 and 18:00:00 are off-peak. The six cases below are the owner's named
boundaries; the second-level edges pin the convention so it cannot drift.

BEIJING TIME, NOT LOCAL TIME. The conversion is UTC+8, explicit, with no
daylight saving, so a machine in any zone gets the same answer. The test
feeds the same instant expressed in three zones and demands the same state.
"""

import sys
from datetime import datetime, timedelta, timezone
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
import dispatch_policy as P  # noqa: E402

BJ = timezone(timedelta(hours=8))


def bj(h: int, m: int, s: int = 0, day: int = 14) -> datetime:
    """A Beijing-time instant on 2026-08-`day` (the 14th by default)."""
    return datetime(2026, 8, day, h, m, s, tzinfo=BJ)


FAIL: list[str] = []
PASSED = 0


def check(ok: bool, msg: str) -> None:
    global PASSED
    if ok:
        PASSED += 1
    else:
        FAIL.append(msg)


def state_of(h: int, m: int) -> str:
    return P.clock_state(bj(h, m))


# ------------------------------------------------------------------ the six
# THE SIX BOUNDARY CASES, with the side each falls on. The owner named these
# six instants in the brief; the side is the half-open convention above.
check(state_of(8, 59) == "off-peak", "08:59 must be OFF-PEAK (pi leads)")
check(state_of(9, 0) == "peak", "09:00 must be PEAK (in-harness leads)")
check(state_of(12, 0) == "off-peak", "12:00 must be OFF-PEAK")
check(state_of(13, 59) == "off-peak", "13:59 must be OFF-PEAK")
check(state_of(14, 0) == "peak", "14:00 must be PEAK")
check(state_of(18, 0) == "off-peak", "18:00 must be OFF-PEAK")

# The mode each state selects, so the six cases pin the economics too.
check(P.clock_mode(bj(8, 59)) == "pi-subagent-mode",
      "off-peak must select pi-subagent-mode")
check(P.clock_mode(bj(9, 0)) == "in-harness-subagent-mode",
      "peak must select in-harness-subagent-mode")

# ------------------------------------------------------------------- the edges
# The half-open convention, pinned at second level so it cannot drift.
check(P.clock_state(bj(8, 59, 59)) == "off-peak", "08:59:59 off-peak")
check(P.clock_state(bj(9, 0, 0)) == "peak", "09:00:00 peak")
check(P.clock_state(bj(11, 59, 59)) == "peak", "11:59:59 peak")
check(P.clock_state(bj(12, 0, 0)) == "off-peak", "12:00:00 off-peak")
check(P.clock_state(bj(13, 59, 59)) == "off-peak", "13:59:59 off-peak")
check(P.clock_state(bj(14, 0, 0)) == "peak", "14:00:00 peak")
check(P.clock_state(bj(17, 59, 59)) == "peak", "17:59:59 peak")
check(P.clock_state(bj(18, 0, 0)) == "off-peak", "18:00:00 off-peak")

# ------------------------------------------------------------------ the zones
# The same instant expressed in three zones must give the same Beijing time
# and the same state. The machine's local zone is never read. 04:00 UTC is
# 09:00 at +05:00, 12:00 at +08:00, and the boundary instant of 12:00 Beijing
# is off-peak under the half-open convention.
inst_a = datetime(2026, 8, 14, 9, 0, 0, tzinfo=timezone(timedelta(hours=5)))
inst_b = datetime(2026, 8, 14, 4, 0, 0, tzinfo=timezone.utc)
inst_c = datetime(2026, 8, 14, 12, 0, 0, tzinfo=BJ)
check(P.beijing_now(inst_a) == P.beijing_now(inst_c),
      "09:00+05:00 and 12:00+08:00 are the same Beijing instant")
check(P.beijing_now(inst_b) == P.beijing_now(inst_c),
      "04:00 UTC and 12:00+08:00 are the same Beijing instant")
check(P.clock_state(inst_a) == P.clock_state(inst_c) == "off-peak",
      "the same instant must pick the same state from any zone")

# ------------------------------------------------------------------ next boundary
# The next boundary and the state after it, so a reader never computes them.
nb, after = P.next_boundary(bj(8, 59))
check(nb == bj(9, 0) and after == "peak", "08:59 -> 09:00, peak begins")
nb, after = P.next_boundary(bj(9, 0))
check(nb == bj(12, 0) and after == "off-peak", "09:00 -> 12:00, off-peak begins")
nb, after = P.next_boundary(bj(12, 0))
check(nb == bj(14, 0) and after == "peak", "12:00 -> 14:00, peak begins")
nb, after = P.next_boundary(bj(13, 59))
check(nb == bj(14, 0) and after == "peak", "13:59 -> 14:00, peak begins")
nb, after = P.next_boundary(bj(14, 0))
check(nb == bj(18, 0) and after == "off-peak", "14:00 -> 18:00, off-peak begins")
nb, after = P.next_boundary(bj(18, 0))
check(nb == bj(9, 0, day=15) and after == "peak",
      "18:00 -> next day 09:00, peak begins (the overnight boundary)")

# ------------------------------------------------------------------ precedence
# THE OWNER'S PIN WINS, ALWAYS. The clock decides only when VERSION_IN_FORCE
# is `auto`.
old = P.VERSION_IN_FORCE
try:
    P.VERSION_IN_FORCE = "pi-subagent-mode"
    check(P.in_force() == "pi-subagent-mode",
          "a pinned mode wins over the clock, even in peak")
    P.VERSION_IN_FORCE = "in-harness-subagent-mode"
    check(P.in_force() == "in-harness-subagent-mode",
          "a pinned in-harness mode wins over the clock, even off-peak")
    # THE RETIRED NAME MUST KEEP RESOLVING, even as a raw pin, not only on a
    # brief's tier line (C-41, DD17 step 4). `[LJ-1.285]` renamed
    # `deepseek-subagent-mode` to `pi-subagent-mode`; 189 frozen briefs under
    # `agents/` still carry the old name, MEASURED 2026-08-15.
    P.VERSION_IN_FORCE = "deepseek-subagent-mode"
    check(P.in_force() == "pi-subagent-mode",
          "the retired name deepseek-subagent-mode still resolves, through ALIASES")
finally:
    P.VERSION_IN_FORCE = old
check(P.VERSION_IN_FORCE == old, "the test restored the switch value")

# ------------------------------------------------------------------ the invariant
# DD17's invariant under BOTH modes: the critic is never the same head as the
# author. A clock that flips the default must flip the adversarial row with
# it. The two tables swap exactly those rows, and the test CONFIRMS it rather
# than assuming it, because the clock makes the swap load-bearing twice a day.
for mode in ("pi-subagent-mode", "in-harness-subagent-mode"):
    t = P.POLICY[mode]["cases"]
    check(t["default"]["agent"] != t["adversarial"]["agent"],
          f"{mode}: the critic is not the author (default {t['default']['agent']} "
          f"vs adversarial {t['adversarial']['agent']})")
check(P.POLICY["pi-subagent-mode"]["cases"]["default"]
      == P.POLICY["in-harness-subagent-mode"]["cases"]["adversarial"],
      "pi's default row is in-harness's adversarial row")
check(P.POLICY["pi-subagent-mode"]["cases"]["adversarial"]
      == P.POLICY["in-harness-subagent-mode"]["cases"]["default"],
      "pi's adversarial row is in-harness's default row")

# The emergency tier is untouched: `fable` is legal in every case, and no
# clock state can make it a default.
check(P.EMERGENCY_TOKEN == "fable", "the emergency token is still fable")
check("fable" in P.expected_tier_tokens("default"),
      "fable stays legal, whatever the clock says")

if FAIL:
    for f in FAIL:
        print(f"FAIL: {f}")
    print(f"test_dispatch_clock: {len(FAIL)} failing check(s), {PASSED} passed")
    sys.exit(1)
print(f"test_dispatch_clock: all checks passed ({PASSED})")
