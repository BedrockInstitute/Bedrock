#!/usr/bin/env python3
"""THE DISPATCH POLICY. One hardcoded switch, two tables, and one place to edit.

WHAT THIS IS. DD17 says which head runs a dispatch. From 2026-08-13 it has TWO
versions, and exactly one of them is in force. `VERSION_IN_FORCE` below is the
switch. Edit that one line and every consumer follows: the checker that reads a
brief's `tier:` line, the default harness `dispatch.py` picks, and the table the
inspection command prints.

INSPECT IT WITH ONE COMMAND, and never by reading code:

    python3 scripts/dispatch_policy.py

It prints the version in force, its full table, why it is in force, and the
condition that reverts it.

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
loses why it is there. The owner cancels the override by word, and the state to
return to is `normal`.
"""

from __future__ import annotations

import sys

# ---------------------------------------------------------------------------
# THE SWITCH. Edit this one value to change the policy. Nothing else.
# ---------------------------------------------------------------------------

VERSION_IN_FORCE = "override"

# The switch's own provenance. A position without a reason is a position
# nobody can retire.
SET_ON = "2026-08-13"
SET_BY = "the repository owner"
REASON = ("QUOTA, not quality. The owner has most of the week's allowance left, "
          "and [LJ-1.121] measured pi's return quality as fully acceptable.")
REVERT_CONDITION = ("The owner cancels the override by word. Set "
                    "VERSION_IN_FORCE = \"normal\" and change nothing else.")

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

POLICY: dict[str, dict] = {
    "normal": {
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
    "override": {
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
    """The version in force. Raises when the switch holds an unknown value,
    because a policy nobody can read must stop rather than pick one."""
    if VERSION_IN_FORCE not in POLICY:
        raise SystemExit(
            f"dispatch_policy: VERSION_IN_FORCE is {VERSION_IN_FORCE!r}, which "
            f"is not one of {', '.join(sorted(POLICY))}. Fix the switch in "
            f"{__file__}.")
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
    v = version or in_force()
    t = POLICY[v]
    lines = [
        f"DISPATCH POLICY: `{v}` is IN FORCE"
        + ("" if v == VERSION_IN_FORCE else "   (NOT the switch's value)"),
        f"  set {SET_ON} by {SET_BY}",
        f"  reason: {REASON}",
        f"  revert: {REVERT_CONDITION}",
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
        print("usage: dispatch_policy.py [normal|override]")
        print("  no argument: print the version in force")
        return 0
    if which and which not in POLICY:
        print(f"unknown version {which!r}; known: {', '.join(sorted(POLICY))}",
              file=sys.stderr)
        return 2
    print(render(which))
    return 0


if __name__ == "__main__":
    sys.exit(main())
