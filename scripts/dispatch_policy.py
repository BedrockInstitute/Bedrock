#!/usr/bin/env python3
"""THE DISPATCH POLICY. One switch, two tables, one clock, one place to edit.

WHAT THIS IS. DD17 says which head runs a dispatch. From 2026-08-13 it has TWO
versions, and exactly one of them is in force. `VERSION_IN_FORCE` below is the
switch. Edit that one line and every consumer follows: the checker that reads a
brief's `tier:` line, the default harness `dispatch.py` picks, and the table the
inspection command prints.

THE PRECEDENCE, and it is the first thing to read in this file:

  * The owner's pinned `VERSION_IN_FORCE` ALWAYS WINS. A pinned value is a
    ruling, and a tool that silently overrides a ruling is worse than no tool.
  * `VERSION_IN_FORCE = "auto"` delegates to the clock, which picks the mode
    from DeepSeek's peak and off-peak windows in Beijing time. The clock
    decides ONLY when the owner has not pinned a mode.

The clock rule came from the owner's instruction of 2026-08-14: DeepSeek
prices peak and off-peak, the off-peak price is half the peak price, peak is
Beijing time 09:00 to 12:00 and 14:00 to 18:00, and the dispatch mode follows
that clock. OFF-PEAK, deepseek is half price and `deepseek-subagent-mode`
leads. PEAK, deepseek is dear and the in-harness Opus is not billed on that
clock, so `in-harness-subagent-mode` leads.

INSPECT IT WITH ONE COMMAND, and never by reading code:

    python3 scripts/dispatch_policy.py

It prints the version in force, its full table, why it is in force, the
condition that reverts it, and, when the clock selected the version, the
window it is in and the next boundary.

THE HONEST LIMIT, AND IT IS THE MOST IMPORTANT LINE IN THIS FILE.

**This switch CANNOT force the orchestrator to use the right head.** An
in-harness Opus subagent never passes through `.claude/skills/codex-dispatch/
dispatch.py`, so no value here can start it, stop it, or redirect it. The same
gap already cost this project two mandatory rules on `[LJ-1.11]`, and PLAN DD18
and DD25 both record it.

What the switch DOES do, and this is all it does:

  1. It DRIVES the default harness `dispatch.py` uses when no `--harness` is
     given. That is authoritative, because that code path reads this file.
  2. It DRIVES what `scripts/check-dispatch-policy.py` accepts in a `tier:`
     line. That makes a wrong choice DETECTABLE by an audit.
  3. It DRIVES what the inspection command prints.

Everything else is convention, enforced by the audit and by nothing else. A
switch that looked authoritative over the orchestrator would be false safety,
which `AGENTS.md` names as worse than no rule at all.

THE OVERRIDE IS TEMPORARY. The field records the date it was set and the
condition that reverts it, because a switch that records only its position
loses why it is there. The owner sets a mode by word, and each mode is named
for the head it LEADS with, so the name says what it does.
"""

from __future__ import annotations

import sys
from datetime import datetime, time, timedelta, timezone

# ---------------------------------------------------------------------------
# THE SWITCH. One of two values, and the order of power is visible here.
#   a mode name ("deepseek-subagent-mode", "in-harness-subagent-mode"): a
#     PIN. The owner set it by word. It wins over the clock, always.
#   "auto": the clock picks the mode from the Beijing-time peak windows
#     below. The owner's instruction of 2026-08-14 made the clock the rule;
#     a mode named here overrides it.
# ---------------------------------------------------------------------------

AUTO = "auto"
VERSION_IN_FORCE = AUTO

# The auto state's own provenance. A position without a reason is a position
# nobody can retire. The pin that ran 2026-08-14 was `deepseek-subagent-mode`,
# set by word when the owner cancelled the quota mode of 2026-08-13.
SET_ON = "2026-08-14"
SET_BY = "the repository owner"
REASON = ("The owner's instruction of 2026-08-14: DeepSeek prices peak and "
          "off-peak, the off-peak price is half the peak price, peak is "
          "Beijing time 09:00 to 12:00 and 14:00 to 18:00, and the dispatch "
          "mode follows that clock. OFF-PEAK, deepseek is half price and "
          "`deepseek-subagent-mode` leads. PEAK, deepseek is dear and the "
          "in-harness Opus is not billed on that clock, so "
          "`in-harness-subagent-mode` leads.")
REVERT_CONDITION = ("The owner pins a mode by word. Set VERSION_IN_FORCE to "
                    "`deepseek-subagent-mode` or `in-harness-subagent-mode` "
                    "and change nothing else; a pinned mode wins over the "
                    "clock. The pin that ran on 2026-08-14 was deepseek, set "
                    "by word when the owner cancelled the quota mode, and it "
                    "is what a pin looks like.")

# ---------------------------------------------------------------------------
# THE CLOCK. One table of windows, one table of states, and the whole rule.
# DD4: the clock is generic in the WINDOWS, not in the two modes. A second
# provider with different windows, or a change to DeepSeek's hours, is one
# edit to PEAK_WINDOWS and nothing else.
# ---------------------------------------------------------------------------
#
# PEAK_WINDOWS is in BEIJING time, which the rule states. The conversion from
# UTC is explicit in `beijing_now()`: Beijing is UTC+8 with no daylight
# saving, so the offset is a constant and a machine in any zone gets the same
# answer.
#
# THE WINDOWS ARE HALF-OPEN [start, end) at minute resolution. A minute
# belongs to the window that STARTED at its hour: 11:59 is peak, 12:00 is
# off-peak; 17:59 is peak, 18:00 is off-peak. The boundary instant itself
# belongs to the window that is starting, so 09:00:00 and 14:00:00 are peak
# and 12:00:00 and 18:00:00 are off-peak.
#
# PEAK_WINDOWS must be ordered by start time and must not be empty; the first
# window's start is the next day's first boundary.
PEAK_WINDOWS: tuple[tuple[int, int, int, int], ...] = (
    (9, 0, 12, 0),   # 09:00 to 12:00 Beijing
    (14, 0, 18, 0),  # 14:00 to 18:00 Beijing
)

# The mode each clock state selects. The two states and the two modes are the
# whole economics: off-peak deepseek is half price, peak it is dear.
CLOCK_STATES: dict[str, str] = {
    "peak": "in-harness-subagent-mode",
    "off-peak": "deepseek-subagent-mode",
}

BEIJING_TZ = timezone(timedelta(hours=8))


def beijing_now(now: datetime | None = None) -> datetime:
    """Beijing wall-clock time for an instant.

    THE CONVERSION IS EXPLICIT, because the rule is stated in Beijing time
    and a machine in another zone must get the same answer. The input is
    converted from its own zone (UTC when none is given) to UTC+8; the
    machine's local zone is never read.
    """
    t = now or datetime.now(timezone.utc)
    return t.astimezone(BEIJING_TZ)


def clock_state(now: datetime | None = None) -> str:
    """`peak` or `off-peak`, from the Beijing wall clock at `now`."""
    bj = beijing_now(now)
    hm = (bj.hour, bj.minute)
    for sh, sm, eh, em in PEAK_WINDOWS:
        if (sh, sm) <= hm < (eh, em):
            return "peak"
    return "off-peak"


def clock_mode(now: datetime | None = None) -> str:
    """The mode the clock selects at `now`."""
    return CLOCK_STATES[clock_state(now)]


def _boundaries(day) -> list[tuple[datetime, str]]:
    """Today's window starts and ends, plus tomorrow's first start, so the
    boundary list is never empty. The state named is the state AFTER the
    boundary."""
    out: list[tuple[datetime, str]] = []
    for sh, sm, eh, em in PEAK_WINDOWS:
        out.append((datetime.combine(day, time(sh, sm), tzinfo=BEIJING_TZ), "peak"))
        out.append((datetime.combine(day, time(eh, em), tzinfo=BEIJING_TZ), "off-peak"))
    sh, sm = PEAK_WINDOWS[0][0], PEAK_WINDOWS[0][1]
    out.append((datetime.combine(day + timedelta(days=1), time(sh, sm),
                                 tzinfo=BEIJING_TZ), "peak"))
    return out


def next_boundary(now: datetime | None = None) -> tuple[datetime, str]:
    """(the next instant the clock state changes, the state after it)."""
    bj = beijing_now(now)
    future = [(t, s) for t, s in _boundaries(bj.date()) if t > bj]
    return min(future, key=lambda x: x[0])


def current_window(now: datetime | None = None) -> tuple[datetime | None, datetime, str]:
    """(start, end, state) of the window `now` falls in, Beijing time.
    The start is the last boundary at or before now, the end the next one,
    and the state is constant between them."""
    bj = beijing_now(now)
    bs = _boundaries(bj.date())
    past = [(t, s) for t, s in bs if t <= bj]
    future = [(t, s) for t, s in bs if t > bj]
    start = past[-1][0] if past else None
    end = future[0][0]
    return start, end, clock_state(bj)


# ---------------------------------------------------------------------------
# THE TWO TABLES. This is their ONE home. Nothing restates them.
# ---------------------------------------------------------------------------
#
# A HEAD has two parts under this policy:
#   harness   what runs the agent. `herdr` is the pane server; `in-harness` is
#             an Opus subagent inside the orchestrator's own session, which
#             dispatch.py cannot start.
#   agent     which coding agent runs inside it: `pi`, `codex`, or `opus 5`.
#
# THE CASES:
#   default             an ordinary dispatch of any kind.
#   adversarial         a negative return's review (DD25), or any adversarial
#                       review. THE CRITIC IS NEVER THE SAME HEAD AS THE
#                       AUTHOR, which is why the two tables swap this row and
#                       the default row. `.claude/skills/codex-dispatch/
#                       SKILL.md` states the same rule.
#   fallback            the head to use when the case's own head is unavailable.

MODEL = "deepseek-v4-pro"

#: THE MODEL RULE, ruled 2026-08-14 by the owner and separate from the head.
#: **A task that is pure natural-language work, and touches no Agda code, takes
#: `deepseek-v4-flash`. Everything else takes the model above.**
#:
#: THE HEAD AND THE MODEL ARE TWO DIFFERENT CHOICES and this file holds both.
#: The switch's `cases` table picks the HEAD, which is who runs the task. This
#: rule picks the MODEL that head runs on. A brief's `tier:` line names the head
#: and, when the model is not the default, the model too, so an audit can see
#: both.
#:
#: IT IS NEARLY MECHANICAL, and that is why it is written as a function rather
#: than as prose. `dispatch.py` already takes `--agda` for a task that will run
#: Agda, because C-12 caps how many may hold a process at once. That same flag
#: answers this question, so the rule costs no new declaration.
#:
#: WHAT IT CANNOT SEE: a task that runs no Agda but still READS and reasons
#: about Agda source. `--agda` is about holding a process, not about subject
#: matter. So the orchestrator overrides with `--model` where the brief is about
#: code, and the brief records why.
FLASH = "deepseek-v4-flash"


def model_for(runs_agda: bool) -> str:
    """The model a dispatch takes, from whether it will run Agda."""
    return MODEL if runs_agda else FLASH

#: THE RETIRED NAMES, and they must keep resolving. `normal` and `override` said
#: WHICH ONE WAS THE EXCEPTION and never WHICH HEAD LEADS, so a reader had to
#: open this file to learn what either meant. The owner renamed them
#: 2026-08-14, by the head each one leads with.
#:
#: **52 frozen briefs carry `override` on their tier line.** A brief is a
#: record and a record is never rewritten, so the old names resolve here
#: forever. `dev/LESSONS.md` C-41 is the law: a retired name that stops
#: resolving turns every citation of it into a dangling pointer, and one that
#: resolves to the WRONG thing is worse still.
ALIASES: dict[str, str] = {
    "normal": "deepseek-subagent-mode",
    "override": "in-harness-subagent-mode",
}


def canonical(version: str) -> str:
    """The live name for a version, whether it is written new or retired."""
    v = version.strip().lower()
    return ALIASES.get(v, v)


POLICY: dict[str, dict] = {
    "deepseek-subagent-mode": {
        "summary": "The steady state. pi leads, codex backs it up, Opus reviews.",
        "cases": {
            "default": {
                "harness": "herdr",
                "agent": "pi",
                "model": MODEL,
                "tier_token": "pi",
            },
            "adversarial": {
                "harness": "in-harness",
                "agent": "opus 5",
                "model": "",
                "tier_token": "opus",
            },
            "fallback": {
                "harness": "herdr",
                "agent": "codex",
                "model": MODEL,
                "tier_token": "codex",
            },
        },
        "note": ("THE DEFAULT IS pi, NOT codex, and that is a real change to "
                 "DD17 rather than a restatement of it. DD17 as first written "
                 "made codex the default for EVERY dispatch. [LJ-1.126] made "
                 "pi viable on 2026-08-13 by landing streaming and resume."),
    },
    "in-harness-subagent-mode": {
        "summary": "Opus leads while the owner's weekly allowance permits it.",
        "cases": {
            "default": {
                "harness": "in-harness",
                "agent": "opus 5",
                "model": "",
                "tier_token": "opus",
            },
            "adversarial": {
                "harness": "herdr",
                "agent": "pi",
                "model": MODEL,
                "tier_token": "pi",
            },
            "fallback": {
                "harness": "herdr",
                "agent": "codex",
                "model": MODEL,
                "tier_token": "codex",
            },
        },
        "note": ("TEMPORARY. The reason is quota, never quality. The two "
                 "tables swap the default row and the adversarial row, "
                 "because the invariant under both versions is that THE "
                 "CRITIC IS NEVER THE SAME HEAD AS THE AUTHOR."),
    },
}

# The invariant that survives both versions, stated once so a third version
# cannot be written without it.
INVARIANT = "The critic must not be the author."

# The `tier:` tokens a brief may legally carry. `fable` is DD17's emergency
# breakthrough tier: it sits outside both tables, needs its trigger named in
# the brief, and is never a default.
EMERGENCY_TOKEN = "fable"
LEGAL_TOKENS = ("opus", "pi", "codex", EMERGENCY_TOKEN)

# How a head maps onto `dispatch.py --harness`. `in-harness` has NO mapping,
# and that absence is the honest limit above: dispatch.py cannot start an Opus
# subagent, so a case whose head is in-harness has no harness at all.
HARNESS_FOR_AGENT = {"pi": "herdr-pi", "codex": "herdr"}


# --------------------------------------------------------------------------- api


def in_force() -> str:
    """The mode in force. A pinned mode wins; `auto` delegates to the clock.
    Raises when the switch holds an unknown value, because a policy nobody
    can read must stop rather than pick one."""
    if VERSION_IN_FORCE == AUTO:
        return clock_mode()
    if VERSION_IN_FORCE not in POLICY:
        raise SystemExit(
            f"dispatch_policy: VERSION_IN_FORCE is {VERSION_IN_FORCE!r}, which "
            f"is not one of {', '.join(sorted(POLICY))} and not {AUTO!r}. Fix "
            f"the switch in {__file__}.")
    return VERSION_IN_FORCE


def table(version: str | None = None) -> dict:
    return POLICY[version or in_force()]


def head(case: str, version: str | None = None) -> dict:
    """The head for one case under one version."""
    return table(version)["cases"][case]


def tier_token(case: str, version: str | None = None) -> str:
    return head(case, version)["tier_token"]


def default_harness(version: str | None = None) -> str | None:
    """What `dispatch.py` uses when no `--harness` is given.

    THIS IS AUTHORITATIVE, because dispatch.py reads it.

    The rule: dispatch.py can only run a head whose harness is `herdr`. Under
    `normal` the default case is herdr plus pi, so that is the answer. Under
    `override` the default case is an in-harness Opus subagent, which this tool
    cannot start at all; the nearest head it CAN run is the fallback, herdr
    plus codex. So an override-era dispatch that reaches dispatch.py with no
    `--harness` is by definition NOT the default case, and the fallback is the
    honest default for it.
    """
    d = head("default", version)
    if d["harness"] == "in-harness":
        d = head("fallback", version)
    return HARNESS_FOR_AGENT.get(d["agent"])


def expected_tier_tokens(case: str, version: str | None = None) -> set[str]:
    """The tokens a brief of this case may legally carry.

    The fallback is always legal: a head can be unavailable on any day, and a
    brief that says so is not a policy breach. The emergency tier is legal
    everywhere for the same reason, and DD17 makes its trigger the brief's job
    to name.
    """
    return {tier_token(case, version), tier_token("fallback", version),
            EMERGENCY_TOKEN}


def render(version: str | None = None) -> str:
    """Render the policy. `None` or `'auto'` renders what is in force; a mode
    name renders that mode's table with the (NOT the switch's value) marker
    when it is not the pin."""
    explicit = version is not None and version != AUTO
    v = version or in_force()
    if v == AUTO:
        v = in_force()
    t = POLICY[v]
    lines = [
        f"DISPATCH POLICY: `{v}` is IN FORCE"
        + ("" if not explicit else "   (NOT the switch's value)"),
    ]
    if VERSION_IN_FORCE == AUTO:
        state = clock_state()
        start, end, _ = current_window()
        boundary, after_state = next_boundary()
        win = (f"{start:%H:%M} to {end:%H:%M}" if start
               else "(before today's first boundary)")
        lines += [
            f"  selected by the clock, not by a ruling "
            f"(VERSION_IN_FORCE = {AUTO!r})",
            f"  clock: {state.upper()} now. Beijing "
            f"{beijing_now():%Y-%m-%d %H:%M}, window {win}",
            f"  peak windows (Beijing): "
            + ", ".join(f"{sh:02d}:{sm:02d} to {eh:02d}:{em:02d}"
                         for sh, sm, eh, em in PEAK_WINDOWS),
            f"  next boundary: {boundary:%Y-%m-%d %H:%M} Beijing, "
            f"{after_state} begins, mode becomes "
            f"`{CLOCK_STATES[after_state]}`",
            f"  set {SET_ON} by {SET_BY}",
            f"  reason: {REASON}",
            f"  revert: {REVERT_CONDITION}",
        ]
    else:
        lines += [
            f"  set {SET_ON} by {SET_BY}",
            f"  reason: {REASON}",
            f"  revert: {REVERT_CONDITION}",
        ]
        if VERSION_IN_FORCE != AUTO:
            lines.append(
                f"  a PIN: `{VERSION_IN_FORCE}` is pinned and wins over the "
                f"clock, which would select `{clock_mode()}` "
                f"({clock_state()} now)")
    lines += [
        "",
        f"  {t['summary']}",
        "",
        f"  {'case':<14} {'harness':<12} {'agent':<8} {'model':<18} tier:",
        f"  {'-' * 14} {'-' * 12} {'-' * 8} {'-' * 18} -----",
    ]
    for case, h in t["cases"].items():
        lines.append(f"  {case:<14} {h['harness']:<12} {h['agent']:<8} "
                     f"{h['model'] or '-':<18} {h['tier_token']}")
    lines += [
        "",
        f"  INVARIANT, both versions: {INVARIANT}",
        f"  {t['note']}",
        "",
        f"  dispatch.py default harness under this version: "
        f"{default_harness(v) or '(none: the default head is in-harness)'}",
        "",
        "  THE LIMIT. This switch cannot force the orchestrator's choice. An",
        "  in-harness Opus dispatch never passes through dispatch.py. The",
        "  switch drives the default harness, the checker, and this printout,",
        "  and makes a wrong choice DETECTABLE. It does not make one",
        "  impossible.",
    ]
    return "\n".join(lines)


def main() -> int:
    which = sys.argv[1] if len(sys.argv) > 1 else None
    if which in ("-h", "--help"):
        print("usage: dispatch_policy.py [auto|deepseek-subagent-mode|"
              "in-harness-subagent-mode]")
        print("  no argument: print the mode the clock selects now")
        return 0
    if which and which != AUTO and which not in POLICY:
        print(f"unknown version {which!r}; known: auto, "
              f"{', '.join(sorted(POLICY))}", file=sys.stderr)
        return 2
    print(render(which))
    return 0


if __name__ == "__main__":
    sys.exit(main())
