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

THE CLOCK BELONGS TO THE VENDOR since `[LJ-1.288]`, 2026-08-15. The windows
moved to `dev/vendors.toml` because they are data about DEEPSEEK and never a
global fact. The last section of this file pins that half: an absent config
gives today's answers, a vendor with its own hours drives the clock on those
hours, a vendor that prices one flat rate has NO clock and resolves `auto` to
its `default_mode`, and every malformed config refuses loudly instead of
picking something.
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

# ------------------------------------------------------------------ the vendor
# THE CLOCK BELONGS TO THE VENDOR, from the owner's instruction of 2026-08-15
# (`[LJ-1.288]`). The peak clock exists because DEEPSEEK prices by the hour, so
# the clock runs only while the vendor in force declares price bands. A FLAT
# vendor gives it no basis, and `auto` then resolves to that vendor's
# `default_mode`. A pin still beats both, which is the rule above and does not
# change.
#
# THE CONFIG IS `dev/vendors.toml`. These checks never touch it. They build a
# config in a temporary file, load it with `P.load_vendor(path)`, and put it in
# force by setting `P.VENDOR`, exactly as the checks above set
# `P.VERSION_IN_FORCE`. Every one restores what it changed.
#
# WHAT A REFUSAL LOOKS LIKE. The loader raises `SystemExit`, which is this
# module's established loud idiom and is NOT swallowed by a consumer that wraps
# the import in `except Exception`. A check that expects a refusal proves the
# refusal fires AND that its message names the vendor, because a refusal nobody
# can act on is only a crash (C-43).

import tempfile  # noqa: E402

BANDED = """
in_force = "acme"
[vendors.acme]
model = "acme-model"
pi_provider = "acme"
pi_wired = true
base_state = "off-peak"
windows = [ { state = "peak", start = "20:00", end = "23:00" } ]
"""

FLAT = """
in_force = "acme"
[vendors.acme]
model = "acme-model"
pi_provider = "acme"
pi_wired = true
default_mode = "pi-subagent-mode"
"""

UNWIRED = """
in_force = "acme"
[vendors.acme]
model = "acme-model"
pi_provider = "acme"
pi_wired = false
default_mode = "in-harness-subagent-mode"
"""


def vendor_of(text: str):
    """Load a config written as text, through the real loader."""
    with tempfile.NamedTemporaryFile("w", suffix=".toml", delete=False,
                                     encoding="utf-8") as fh:
        fh.write(text)
        name = fh.name
    try:
        return P.load_vendor(Path(name))
    finally:
        Path(name).unlink()


def refusal(text: str) -> str:
    """The refusal a bad config raises, as a string. Empty when it loaded."""
    try:
        v = vendor_of(text)
    except SystemExit as exc:
        return str(exc)
    saved = P.VENDOR
    try:
        P.VENDOR = v
        P._validate_vendor_against_policy()
        return ""
    except SystemExit as exc:
        return str(exc)
    finally:
        P.VENDOR = saved


def with_vendor(text: str, fn):
    """Run `fn` with the config in `text` in force, then restore."""
    saved = P.VENDOR
    try:
        P.VENDOR = vendor_of(text)
        return fn()
    finally:
        P.VENDOR = saved


def raised(fn) -> str:
    """The SystemExit message `fn` raises, or the empty string."""
    try:
        fn()
        return ""
    except SystemExit as exc:
        return str(exc)


# THE ABSENT CONFIG IS THE COMPATIBILITY FLOOR. Deleting `dev/vendors.toml`
# must not change a single answer, and this is where that is pinned.
missing = P.load_vendor(Path("/nonexistent/vendors.toml"))
check(missing is P.BUILTIN_VENDOR,
      "an absent config gives the built-in vendor, not a crash")
check(missing.name == "deepseek" and missing.model == "deepseek-v4-pro",
      "the built-in vendor is deepseek on deepseek-v4-pro, today's data")
check(missing.windows == ((9, 0, 12, 0, "peak"), (14, 0, 18, 0, "peak")),
      "the built-in windows are the owner's 09:00-12:00 and 14:00-18:00")

# THE SHIPPED CONFIG MUST SAY THE SAME THING AS THE FLOOR. If these two ever
# disagree, deleting the config would change behaviour, and the claim that the
# config is a change of shape and not of policy would be false.
shipped = P.load_vendor()
check(shipped.name == P.BUILTIN_VENDOR.name
      and shipped.model == P.BUILTIN_VENDOR.model
      and shipped.windows == P.BUILTIN_VENDOR.windows
      and shipped.base_state == P.BUILTIN_VENDOR.base_state
      and shipped.pi_wired == P.BUILTIN_VENDOR.pi_wired,
      "the shipped config and the built-in floor declare the same vendor")
check(P.MODEL == P.VENDOR.model,
      "MODEL is the vendor's model, and the name consumers read did not change")
check(P.PEAK_WINDOWS == ((9, 0, 12, 0), (14, 0, 18, 0)),
      "PEAK_WINDOWS still reads as it did, from the vendor's peak band")

# A BANDED VENDOR DRIVES THE CLOCK ON ITS OWN HOURS. This is the whole point of
# moving the windows into the config: they are data about a vendor, never a
# global fact. `acme` is dear from 20:00 to 23:00, so 15:00 is off-peak for it
# while 15:00 is PEAK for deepseek.
check(with_vendor(BANDED, lambda: P.clock_state(bj(21, 0))) == "peak",
      "a vendor's own window drives the clock: 21:00 is peak for acme")
check(with_vendor(BANDED, lambda: P.clock_state(bj(15, 0))) == "off-peak",
      "15:00 is off-peak for acme, and PEAK for deepseek, from the same code")
check(with_vendor(BANDED, lambda: P.auto_mode()) in
      ("pi-subagent-mode", "in-harness-subagent-mode"),
      "a banded vendor still resolves auto through the clock")
check(with_vendor(BANDED, lambda: P.next_boundary(bj(21, 0))[0]) == bj(23, 0),
      "the boundary list is built from the vendor's windows")

# A FLAT VENDOR HAS NO CLOCK, AND SAYS SO. The refusal must name the vendor.
flat_clock = with_vendor(FLAT, lambda: raised(P.clock_state))
check("no price window" in flat_clock and "acme" in flat_clock,
      "a flat vendor refuses the clock and names itself")
check(with_vendor(FLAT, lambda: P.auto_mode()) == "pi-subagent-mode",
      "a flat vendor resolves auto to its declared default_mode")

# THE PIN STILL BEATS BOTH, and that is today's rule, unchanged.
old = P.VERSION_IN_FORCE
try:
    P.VERSION_IN_FORCE = "in-harness-subagent-mode"
    check(with_vendor(FLAT, lambda: P.in_force()) == "in-harness-subagent-mode",
          "a pin beats a flat vendor's default_mode")
    check(with_vendor(BANDED, lambda: P.in_force()) == "in-harness-subagent-mode",
          "a pin beats a banded vendor's clock")
finally:
    P.VERSION_IN_FORCE = old
check(P.VERSION_IN_FORCE == old, "the vendor checks restored the switch value")

# AN UNWIRED VENDOR REFUSES AT THE DISPATCH POINT, and nowhere else. `pi` is
# wired to deepseek and to nothing else today, so a vendor may be DECLARED
# before it can run. What must never happen is a head that starts on a model
# nothing can run.
unwired = with_vendor(UNWIRED, lambda: raised(P.default_harness))
check("pi_wired = false" in unwired and "acme" in unwired,
      "an unwired vendor refuses default_harness, naming the vendor and the field")
check("refusal, not a reminder" in unwired,
      "the unwired refusal says it is a refusal")
check(with_vendor(UNWIRED, lambda: P.tier_token("default")) in P.LEGAL_TOKENS,
      "an unwired vendor still lets a FROZEN record be judged (C-41)")
check(with_vendor(UNWIRED, lambda: P.render()) != "",
      "the inspection command still prints under an unwired vendor")

# EVERY MALFORMED CONFIG REFUSES, AND NAMES THE FAULT. There is no field with a
# silent default, because an escape hatch is the shape a wrong choice hides in.
check("has no `[vendors.grok]` table" in refusal(
    'in_force = "grok"\n[vendors.acme]\nmodel = "m"\npi_provider = "a"\n'
    'pi_wired = true\ndefault_mode = "pi-subagent-mode"\n'),
    "an unknown vendor name refuses and lists the declared vendors")
check("Declare `default_mode`" in refusal(
    'in_force = "acme"\n[vendors.acme]\nmodel = "m"\npi_provider = "a"\n'
    'pi_wired = true\n'),
    "a flat vendor with no default_mode refuses")
check("must declare `base_state`" in refusal(
    'in_force = "acme"\n[vendors.acme]\nmodel = "m"\npi_provider = "a"\n'
    'pi_wired = true\nwindows = [ { state = "peak", start = "09:00", '
    'end = "12:00" } ]\n'),
    "a banded vendor with no base_state refuses")
check("declares both `windows` and `default_mode`" in refusal(
    'in_force = "acme"\n[vendors.acme]\nmodel = "m"\npi_provider = "a"\n'
    'pi_wired = true\nbase_state = "off-peak"\ndefault_mode = "pi-subagent-mode"'
    '\nwindows = [ { state = "peak", start = "09:00", end = "12:00" } ]\n'),
    "a vendor that is both banded and flat refuses")
check("must not overlap" in refusal(
    'in_force = "acme"\n[vendors.acme]\nmodel = "m"\npi_provider = "a"\n'
    'pi_wired = true\nbase_state = "off-peak"\nwindows = [ '
    '{ state = "peak", start = "09:00", end = "12:00" }, '
    '{ state = "peak", start = "11:00", end = "13:00" } ]\n'),
    "overlapping windows refuse")
check("never crosses midnight" in refusal(
    'in_force = "acme"\n[vendors.acme]\nmodel = "m"\npi_provider = "a"\n'
    'pi_wired = true\nbase_state = "off-peak"\nwindows = [ '
    '{ state = "peak", start = "22:00", end = "02:00" } ]\n'),
    "a window that crosses midnight refuses")
check("must declare `pi_wired`" in refusal(
    'in_force = "acme"\n[vendors.acme]\nmodel = "m"\npi_provider = "a"\n'
    'default_mode = "pi-subagent-mode"\n'),
    "a vendor with no pi_wired refuses; the field has no default")
check("unknown field" in refusal(
    'in_force = "acme"\n[vendors.acme]\nmodel = "m"\npi_provider = "a"\n'
    'pi_wired = true\ndefault_mode = "pi-subagent-mode"\nvendor_note = "x"\n'),
    "an unknown field refuses instead of being ignored in silence")
check("cannot be read as TOML" in refusal("in_force = [[[\n"),
      "a config that is not TOML refuses and says so")

# THE DD19 LINE, ENFORCED. The config may NAME a band or a mode. This module
# decides whether the name is real, because what a band selects and what a mode
# IS are both policy. A third price band costs one new `CLOCK_STATES` row.
check("`CLOCK_STATES` has no row for it" in refusal(
    'in_force = "acme"\n[vendors.acme]\nmodel = "m"\npi_provider = "a"\n'
    'pi_wired = true\nbase_state = "off-peak"\nwindows = [ '
    '{ state = "super-peak", start = "14:00", end = "18:00" } ]\n'),
    "a band with no CLOCK_STATES row refuses, and the row belongs to policy")
check("which is not a mode" in refusal(
    'in_force = "acme"\n[vendors.acme]\nmodel = "m"\npi_provider = "a"\n'
    'pi_wired = true\ndefault_mode = "no-such-mode"\n'),
    "a default_mode that is not a mode refuses")
check(refusal(
    'in_force = "acme"\n[vendors.acme]\nmodel = "m"\npi_provider = "a"\n'
    'pi_wired = true\ndefault_mode = "deepseek-subagent-mode"\n') == "",
    "a RETIRED mode name is legal as default_mode, through ALIASES (C-41)")

if FAIL:
    for f in FAIL:
        print(f"FAIL: {f}")
    print(f"test_dispatch_clock: {len(FAIL)} failing check(s), {PASSED} passed")
    sys.exit(1)
print(f"test_dispatch_clock: all checks passed ({PASSED})")
