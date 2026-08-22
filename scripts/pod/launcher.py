#!/usr/bin/env python3
"""The dispatch wrapper. Every codex agent for this project is launched through here.

WHY THIS EXISTS. The skill file already documented the right way to dispatch, and the
orchestrator read it and then made the same class of mistake three times in one day:
dispatched on a model the backend rejects (two dead agents), dispatched a report-writing
brief under a read-only sandbox that blocked the report (one dead agent), and killed two
live agents by stopping the watcher shell that had launched them into its own process
group. Every one of those failures was SILENT: no error line, no final message, a log
that stops mid-sentence and reads exactly like a crash.

Documentation could not prevent them because documentation is advice at the moment of
writing a command. This script is the command. It refuses the mistakes instead of
warning about them, and it keeps a registry so a violation is visible.

HARDENED 2026-08-05 against [L3.32-T58]'s adversarial review, which found 18 defects with
reproductions. The ones that mattered most, all now fixed and each marked at its site:
the registry's unlocked read-modify-write oversubscribed the slot ceiling and silently
lost records under the tool's own documented fan-out (FM1); `alive()` read EPERM as "dead",
so a live agent could read as exited (FM2); the dead-model refusal lived only in `run`, so
`queue` and `resume` could still launch it, recreating failure mode 1 through the very
route the skill recommends (FM3); and the read-only detection missed the exact phrasing
this file's own docs use (FM4).

  launcher.py run <task> <brief> [--agda] [--tier wide|heavy] [--effort max]
  launcher.py queue <task> <brief> [--agda]    wait for a free slot, then run, detached
  launcher.py resume <task> [--note TEXT]      continue a killed or exhausted agent
  launcher.py status [--all]                   the census, including unmanaged strays
  launcher.py check <brief>                    validate a brief without launching
  launcher.py wait [--all] [--timeout S]       block until an agent returns, then report
  launcher.py gate-ready                       exit 1 if a full-tree gate would read a
                                               half-written file

`--effort` is REQUIRED on the `herdr-claude` harness, which is the default. `--tier`
selects amendment A14's Agda concurrency tier, and with it the one GHCRTS caliber that
tier measures under. Both values live in `dev/pod/heads.toml` and nowhere else.

NOTIFICATION. Agents are setsid'd so that killing whatever launched them cannot take them
down, and the price of that detachment is that nothing is watching them: the orchestrator's
harness only announces background work IT tracks, so returns went unnoticed until the owner
asked. `wait` is the fix and it is deliberately NOT the agents' parent: it only polls the
registry, so it inherits none of the ownership that made the original watcher lethal. Run it
as a tracked background job right after dispatching, and the harness announces the return:

    .venv/bin/python scripts/pod/launcher.py wait        # exits when the FIRST agent returns
    .venv/bin/python scripts/pod/launcher.py wait --all  # exits when the last one does

Exit status: 0 fine, 1 refused or defect found, 2 usage error.
"""

from __future__ import annotations

import argparse
import contextlib
import datetime as _dt
import errno
import fcntl
import json
import os
import pathlib
import re
import shlex
import shutil
import signal
import subprocess
import sys
import time
from pathlib import Path

ROOT = Path("/Users/alsg/Agentic/Bedrock")

# THE NAME THIS FILE IS INVOKED BY, and it changed at the cutover of 2026-08-18.
# The module was `.claude/skills/codex-dispatch/dispatch.py`; the cutover deleted that
# copy and this file is `scripts/pod/launcher.py`. Every remedy string below prints THIS
# constant, so a rename moves one line and never leaves an operator a command that fails.
# The interpreter is `.venv/bin/python` because the shared Boundary in `AGENTS.md`
# requires it and a bare `python3` may not carry the pinned dependencies.
CLI = ".venv/bin/python scripts/pod/launcher.py"
# THE RUNTIME STATE IS `.pod-state/`, AND IT USED TO SIT BESIDE THIS FILE.
#
# `STATE` was `Path(__file__).parent / ".state"`, which is `scripts/pod/.state`
# in this copy. That path is not in `.gitignore`, and THREE things in the POD
# already say where it belongs:
#
#   1. `dev/memos/LJ-4-pod-program-design.md` section 4.0 lists `.pod-state/logs/`
#      as the home of the WORKER TRANSCRIPTS, which is what `LOGS` holds.
#   2. `scripts/pod/pod.py:prune_logs()` reads `<root>/.pod-state/logs` and
#      matches `<CODE>-*`, which is exactly the name `launch()` writes. Under the
#      old path it pruned an empty directory and the transcripts grew for ever.
#   3. `.gitignore` already carries `.pod-state/`, and the design says that line
#      matters TWICE: it keeps the state out of the index, and it keeps the state
#      out of `git status --untracked-files=all`, which is what FACT 4 reads
#      (`scripts/pod/facts.py:316`). Under the old path every dispatch added a
#      registry file and a log to the worker's own changed-file count.
#
# `_build/` is not an option: `make clean` empties it and would erase a live
# registry, which is the design's own reason for `.pod-state/`.
STATE = ROOT / ".pod-state"
REGISTRY = STATE / "registry.json"
LOCKFILE = STATE / "registry.lock"
LOGS = STATE / "logs"

# FM17: the block WAS date-gated, and the gate did its job. The backend's own message
# named early August 2026; the one-line re-check the skill prescribes succeeded on
# 2026-08-13 (`codex exec -m deepseek-v4-pro "say ok"` -> ok, 15,885 tokens), so the
# entry is gone rather than left to expire. The owner ruled the same day that codex uses
# the pro model from now on.
#
# THE MODEL NAME HAS NO DATE SUFFIX. The release is called DeepSeek-V4-Pro-0813, but the
# API rejects `deepseek-v4-pro-0813`: "The supported API model names are deepseek-v4-pro
# or deepseek-v4-flash". Measured 2026-08-13. Pass the bare name.
BLOCKED_MODELS: dict[str, _dt.date] = {}
# THE MODEL COMES FROM THE VENDOR ROW, not from a literal here. [LJ-1.288] put
# the vendor in `dev/vendors.toml`, so this line was the last place that welded
# the dispatcher to one vendor. The fallback literal survives ONLY for the case
# where the policy module cannot be read at all, which the block below reports.
DEFAULT_MODEL = "deepseek-v4-pro"

# THE HARNESS, AND ITS DEFAULT COMES FROM THE POLICY SWITCH.
#
# `herdr` starts the agent inside a herdr pane, which the herdr server owns, so
# the agent survives the death of whatever launched it exactly as the old setsid
# path did, and it ALSO becomes visible to `herdr agent list`, `attach` and
# `wait` from any other terminal. That is the reason for the switch to it.
#
#   herdr      a herdr pane running a CODEX agent
#   herdr-pi   a herdr pane running a PI agent. `herdr agent start --kind`
#              accepts `pi`, measured 2026-08-13 on herdr 0.8.0. This value
#              exists because the policy's own head is "herdr, then pi", and
#              before [LJ-1.127] that head could not be expressed at all: the
#              old HERDR_KIND map had a `pi` entry that no code path could
#              reach, because `--harness pi` took the separate direct-exec
#              branch instead.
#   codex      the old direct-exec path, kept as the fallback when the herdr
#              server is down
#   pi         the pi CLI direct, through pi_stream.py
#
# THE DEFAULT IS NOT A CONSTANT HERE ANY MORE. `scripts/dispatch_policy.py`
# holds the one switch that selects the dispatch policy version, and the
# default harness follows it. If that module cannot be imported the fallback is
# `herdr`, and the tool says so rather than guessing in silence.
# [LJ-1.295] moved the policy into `scripts/dispatch/` on 2026-08-15. This file is
# UNTRACKED and outside every agent's scope, so no gate and no checker would have
# caught the break; the only signal was this tool's own warning line, which is why
# that warning exists rather than a silent fallback. Both directories are on the
# path: `scripts/` still holds `agents_tree.py`, which is genuinely cross-group.
_POLICY_DIRS = [str(ROOT / "scripts" / "dispatch"), str(ROOT / "scripts")]
for _d in _POLICY_DIRS:
    if _d not in sys.path:
        sys.path.insert(0, _d)
#
# AN UNWIRED VENDOR MUST NOT KILL INSPECTION, and this block is where that is
# decided. `default_harness()` validates the vendor and raises SystemExit when
# `pi` is not wired to it, so an uncaught call HERE would take down `status`,
# `wait` and every other read-only subcommand. [LJ-1.288] found that at this
# call site. You cannot read your way out of a broken config if reading is what
# breaks, so the refusal is caught here and RE-RAISED on the launch path only,
# by `require_vendor_wired()` in `launch()`.
# POD EDIT 5 of 6 (design section 6.2), and this is the edit that prevents a
# SILENT wrong dispatch.
#
# `default_harness()` at scripts/dispatch/dispatch_policy.py:840-861 ends in
# `HARNESS_FOR_AGENT.get(d["agent"])`, and that map at :784 holds no claude
# token, so `default_harness()` can NEVER return `herdr-claude`. Section 7.1
# row 21 then RETIRES dispatch_policy.py, at which point the handler below sets
# the hard literal, the old literal was `herdr`, and HERDR_KIND maps `herdr` to
# kind `codex`. So after the retirement every dispatch that omits `--harness`
# would silently start a CODEX agent on a deepseek model, because DEFAULT_MODEL
# is `deepseek-v4-pro`.
#
# All three literals now read `herdr-claude`. THE MODULE DEFAULT IS STILL NOT
# LOAD-BEARING: the POD passes `--harness`, `--model` and `--effort` on every
# dispatch, from dev/pod/heads.toml.
VENDOR_ERROR = ""
try:
    import dispatch_policy as POLICY
    POLICY_ERROR = ""
    POLICY_RETIRED = False
    try:
        HARNESS = POLICY.default_harness() or "herdr-claude"
    except SystemExit as _vexc:                 # an unwired vendor, by design
        HARNESS = "herdr-claude"
        VENDOR_ERROR = str(_vexc)
except Exception as _exc:                       # pragma: no cover
    POLICY = None
    HARNESS = "herdr-claude"
    # TWO CAUSES, ONE VARIABLE, AND THE OPERATOR MUST BE ABLE TO TELL THEM APART.
    # The module is ABSENT by design since 2026-08-18: section 7.1 row 21 RETIRED it and
    # the cutover moved it to `archive/scripts/dispatch/dispatch_policy.py`. That is not
    # a defect, and nothing here is load-bearing any more, because the POD passes
    # `--harness`, `--model` and `--effort` on every dispatch from `dev/pod/heads.toml`.
    # A module that IS present and still fails to import IS a defect.
    # The report stays in BOTH cases, because the design rules that the retirement is
    # reported and never silent, and `test_pod_launcher.py` pins that. Only the WORDING
    # and the severity change, so the first line the owner reads on `run` and on `status`
    # no longer reads as an error. `POLICY_RETIRED` picks the prefix in `main()`.
    _present = [str(Path(_d) / "dispatch_policy.py") for _d in _POLICY_DIRS
                if (Path(_d) / "dispatch_policy.py").is_file()]
    POLICY_RETIRED = not _present
    POLICY_ERROR = (
        # THE TEXT NAMES NO COMMAND-LINE FLAG. `test_pod_launcher.py:743-744` asserts
        # that a brief refusal prints without the effort flag's spelling anywhere in
        # stderr, and this line shares that stream.
        (f"archive/scripts/dispatch/dispatch_policy.py is RETIRED by section 7.1 row 21 and now "
         f"sits under archive/. The default harness is {HARNESS!r}. Every POD dispatch "
         f"names its harness, its model and its effort from dev/pod/heads.toml.")
        if POLICY_RETIRED else
        (f"{_present[0]} is present and could not be read ({_exc}); "
         f"the default harness fell back to {HARNESS!r}"))

# The vendor's own values, with the pre-config literals as the fallback for a
# policy module that will not import at all.
if POLICY is not None:
    DEFAULT_MODEL = getattr(POLICY, "MODEL", DEFAULT_MODEL)
    PI_PROVIDER = getattr(POLICY, "PI_PROVIDER", "deepseek")
else:
    PI_PROVIDER = "deepseek"

# THE PI STREAM WRAPPER. `pi -p` prints nothing until it exits, so [LJ-1.121]
# left a 2071-byte log that never changed size and nobody could watch the run.
# `pi --mode json` streams, but it streams one JSON object per token: a
# 27-second run wrote 27 KB over 269 lines, 237 of them token deltas. So the
# raw stream goes through pi_stream.py, which renders readable lines, keeps the
# untouched JSONL in a sidecar, writes the final message, and re-emits pi's
# session id in the codex `session id:` shape that SESSION_RE already matches.
# Measured 2026-08-13 by [LJ-1.126]. See that file's docstring for what it drops.
PI_STREAM = Path(__file__).resolve().parent / "pi_stream.py"

# THE THREE THINGS THE TRIAL FOUND, all measured 2026-08-13 before the switch:
#
# 1. HERDR NAMES ARE LOWERCASE. `LJ-1.123` is refused with invalid_agent_name:
#    "must start with a lowercase letter and contain only lowercase letters,
#    digits, '-' or '_'". So a task code is mapped, and herdr_name() below is the
#    ONE place that mapping lives.
# 2. A BARE `agent wait` AFTER `agent prompt` RACES AND FIRES AT ONCE. Measured:
#    prompt submitted at 09:18:22, wait returned at 09:18:22 with status `idle`,
#    because the agent had not started yet. `agent prompt --wait --until ...`
#    waits for the first state observed AFTER submission and is the correct
#    primitive. A bare wait armed later, while the agent is already `working`,
#    is also correct, and did not fire spuriously in seven minutes.
# 3. `agent start --kind codex` USES CODEX'S OWN DEFAULT MODEL. The trial pane
#    read `model: deepseek-v4-flash high` when pro was intended. The model must
#    be passed through the `-- <AGENT_ARG>...` slot.
# [LJ-1.127], 2026-08-13: this map used to read {"herdr": "codex", "pi": "pi"}
# and its `pi` entry was DEAD. `kind` is computed inside the `HARNESS ==
# "herdr"` branch, so the lookup could only ever return "codex", and
# `--harness pi` never reached that branch at all. The policy's own head is
# "herdr, then pi", so the combination the map promised was the one
# combination the tool could not run. `herdr-pi` is that combination and it is
# now reachable. MEASURED on herdr 0.8.0: `herdr agent start --kind` lists
# `pi` among its possible values.
# POD EDIT 1 of 6 (design section 6.2). `herdr-claude` runs a CLAUDE agent in a
# server-owned pane. MEASURED 2026-08-17: `herdr agent start --help` lists
# `claude` among its `--kind` values, and `herdr integration status` prints
# `claude: current (v7)`, so a claude pane reports the `working`, `idle`, `done`
# and `blocked` lifecycle the driver below waits on.
# `HERDR_HARNESSES` is derived from this map, so it needs no edit.
# POD EDIT, 2026-08-19: `herdr-grok` runs a GROK agent in a server-owned pane. MEASURED
# that day, end to end, before any head was pointed at it: `herdr agent start --kind`
# lists `grok`; `herdr integration status` prints `grok: current (v1)`, so a grok pane
# reports the `working`, `idle`, `done` and `blocked` lifecycle this driver waits on; and
# `herdr agent prompt` reached it, it went to `done` and it WROTE THE FILE it was asked
# for. That last half is the one that matters, because the failure class this project has
# measured twice is an agent that echoes its prompt and exits `done` having written
# nothing.
HERDR_KIND = {"herdr": "codex", "herdr-pi": "pi", "herdr-claude": "claude",
              "herdr-grok": "grok"}
HERDR_HARNESSES = tuple(HERDR_KIND)

# THE AGENT PANES LIVE IN THEIR OWN TAB, and that is not tidiness.
# 2026-08-13: an agent was killed mid-run by a stray keystroke, because its pane
# sat in the owner's active tab. The old setsid path made agents untouchable; the
# herdr path puts them in a real terminal a human is using. A separate tab
# restores the isolation without giving up `agent list`, `attach` or `wait`.
#
# Tab `w1:t3` is labelled `agents`. If it is gone, `herdr tab create --label
# agents` makes another and its root pane id goes here.
# THE AGENT WORKSPACE IS FOUND BY LABEL AND CREATED IF MISSING, and pinning an
# id instead was measured wrong the same day it was written.
#
# 2026-08-13, in order: an agent died to a stray keystroke because its pane sat in
# the owner's active workspace; a `tab create` returned a pane that was gone by the
# next dispatch; a workspace created at the project root worked, so the base pane
# was pinned to its root id; and then the owner closed that workspace and every
# agent in it died with it. A pinned id cannot survive a closed workspace. A LABEL
# can, because the driver recreates the workspace when the lookup finds nothing.
#
# The owner's instruction stands: the workspace is rooted at the PROJECT, not at ~.
# The label used only when the workspace has to be RE-created. herdr rewrites it
# from the content anyway, so it is a hint, never a key. Owner's instruction,
# 2026-08-13: agents share the project workspace with the main agent, and the
# owner will not close it. So the name is the project's.
HERDR_WORKSPACE_LABEL = "Bedrock"

# AND THE LABEL IS NOT A KEY EITHER. Measured 2026-08-13: a workspace created
# with --label bedrock-agents was reported as `bedrock-agents` at creation and as
# `Bedrock` one dispatch later. herdr relabels a workspace from its content, so a
# label lookup misses and the driver creates a second workspace every time. The
# id IS stable, so the id is remembered here and only re-created when a lookup
# proves it gone.
HERDR_WS_FILE = STATE / "herdr-workspace"
#: **THE PANE LAYOUT IS NOT DECIDED HERE.** `scripts/pod/pane-slot.py` owns the rule, the
#: state and the splits, and its docstring carries the two phases and the measurements.
#: The paragraphs that stood here described the OLD rule, which was measured broken on
#: 2026-08-19, and the file is the classic place a repaired rule leaves its own obituary.
#: **THE TWO LAYOUT STATE FILES ARE GONE.** `herdr-open-column` and
#: `herdr-rightmost-column` steered the old shell rule and could disagree: on 2026-08-19
#: one was empty while the other named a DEAD pane, which sent the next dispatch down the
#: BASE fallback this file had MEASURED as the worst case. `scripts/pod/pane-slot.py`
#: keeps ONE file, `.pod-state/herdr-columns`, and drops a dead pane on read.
#: The column equaliser, run after a new COLUMN is opened. See its docstring for the
#: arithmetic and for the measurements that justify it. **`pane-slot.py` calls it now**,
#: because the rule that knows a RIGHT split just happened lives there.
EQUALISE = Path(__file__).resolve().parent / "equalise-panes.py"
#: **THE ONE HOME OF THE PANE LAYOUT RULE.** It picks the direction, picks the source
#: pane, performs the split and keeps the state. Its docstring carries the two phases and
#: every measurement behind them.
PANE_SLOT = Path(__file__).resolve().parent / "pane-slot.py"
#: The one-liner that reads a pane id out of a `pane split` response. It appears four
#: times below and a second spelling of it would be a second thing to get wrong.
SPLIT_ID = ("python3 -c 'import json,sys; "
            "print(json.load(sys.stdin)[\"result\"][\"pane\"][\"pane_id\"])'")


def herdr_name(task: str) -> str:
    """Map a task code to a legal herdr agent name, reversibly enough to join.

    `LJ-1.123` -> `lj-1-123`. Uppercase and dots are the only characters our task
    codes carry that herdr refuses."""
    return task.lower().replace(".", "-")

# THE AGDA CEILING, AND AMENDMENT A14 RESTORED C-12's TWO TIERS ON 2026-08-17.
#
# WHAT THIS BLOCK USED TO SAY, and why it was wrong. [L3.32-T119] found three
# documents giving three different numbers: this file said two, `dev/LESSONS.md`
# C-12 says up to FOUR at -M8g in WIDE mode with a memory floor and a watchdog,
# and AGENTS.md said one process at a time. The tool implemented none of C-12's
# tier, floor or watchdog, so it pinned TWO and dropped the WIDE tier.
#
# THE POD IMPLEMENTS ALL THREE PRECONDITIONS, so the permission returns.
# `scripts/pod/pod.py` starts and confirms `scripts/ops/agda-watchdog.sh` every
# tick (A13), reads system free memory before it opens slots three and four
# (A14), and refuses every Agda task while the watchdog is down. A14 says the
# pinned two "halved throughput without saying so", and it names the two tiers:
# WIDE is four concurrent at -M8g, HEAVY is two at -M12g.
#
# THE CALIBER WAS ALSO WRONG, and R13 is the rule. `-M8g` sets a heap cap and NO
# allocation area, so every number measured under it is incomparable with a
# number measured under R13's caliber. A15 splits the program's own two runs:
# a per-task acceptance run uses `-A64m -I0 -M8g`, the worker's caliber, and a
# whole-tree `make check` uses `-A64m -I0 -M16g`, C-12's orchestrator caliber,
# because that run holds the machine alone. Neither of those is this constant:
# THIS is the caliber handed to a dispatched WORKER's pane, and it is the WIDE
# tier's, one caliber PER TIER.
#
# THE MEASUREMENT REASON FOR TWO IS NOT LOST, it moved to the right surface. Two
# `agda --profile=definitions` runs corrupt each other's numbers ([T88] had to
# disclose a contended baseline, and [T101] and [T103] each measured a module
# the campaign then re-priced from). A brief that measures now declares
# `machine: exclusive`, and `pod.py:admits()` gives it the machine alone. A tier
# is not a permission to contend; it is a heap budget.
#
# A RECORD CARRIES ITS TIER, so two measurements are compared only within a
# tier. `launch()` writes `tier` into the registry record beside `model`.
#
# ONE OWNER FOR THE NUMBERS. `dev/pod/heads.toml` holds them and
# `scripts/pod/heads.py` is their loader, whose own docstring rules that two
# READERS of one file are admissible and two OWNERS are not. This file is a
# reader. The literals below are C-12's own floor and they are used ONLY when
# that loader cannot be reached, which `HEADS_ERROR` reports on every launch
# path rather than passing in silence.
_C12_FLOOR_TIERS = {
    "wide": {"slots": 2, "heap": "-A64m -I0 -M8g"},
    "heavy": {"slots": 2, "heap": "-A64m -I0 -M12g"},
    "shared": {"max_heap_sum_gb": 32},
}
#: The claude CLI's own five `--effort` values, MEASURED 2026-08-17 by [LJ-4-0].
#: They are `legal.efforts` in `dev/pod/heads.toml`, and the literal here is the
#: fallback for a file that will not load at all.
_CLI_EFFORTS = ("low", "medium", "high", "xhigh", "max")
HEADS_ERROR = ""
try:
    _pod_dir = str(Path(__file__).resolve().parent)
    if _pod_dir not in sys.path:
        sys.path.insert(0, _pod_dir)
    import heads as HEADS_MOD
    _HEADS_CFG = HEADS_MOD.load_heads()
    AGDA_TIERS = _HEADS_CFG["tiers"]
    LEGAL_EFFORTS = tuple(_HEADS_CFG["legal"]["efforts"])
    LEGAL_MODELS = tuple(_HEADS_CFG["legal"]["models"])
except Exception as _hexc:                      # pragma: no cover - config damage
    HEADS_MOD = None
    _HEADS_CFG = None
    AGDA_TIERS = _C12_FLOOR_TIERS
    LEGAL_EFFORTS = _CLI_EFFORTS
    LEGAL_MODELS = ()
    HEADS_ERROR = (f"dev/pod/heads.toml could not be read through "
                   f"scripts/pod/heads.py ({_hexc}); the Agda tiers fell back to "
                   f"C-12's two-slot floor and the WIDE caliber, and the legal "
                   f"effort list fell back to the claude CLI's own five")

# The tier a dispatch gets when nobody names one. A14 makes WIDE the ordinary
# tier and HEAVY the exception, so a caller that says nothing gets WIDE.
AGDA_TIER_DEFAULT = "wide"
#: The mixed worst case A14 caps. `admits()` in pod.py counts slots in ONE tier;
#: only this file sees every live holder's tier, so the SUM is checked here.
AGDA_MAX_HEAP_SUM_GB = int(AGDA_TIERS.get("shared", _C12_FLOOR_TIERS["shared"])
                           .get("max_heap_sum_gb",
                                _C12_FLOOR_TIERS["shared"]["max_heap_sum_gb"]))
_HEAP_GB_RE = re.compile(r"-M(\d+)g\b")


def agda_tiers() -> tuple[str, ...]:
    """The tier names a dispatch may ask for, in a stable order."""
    return tuple(t for t in AGDA_TIERS if t != "shared")


def _tier_row(tier: str) -> dict:
    """One tier's row, or the default tier's. `shared` is not a tier: it holds the
    two cross-tier numbers, so asking for it gets the default row."""
    row = AGDA_TIERS.get(tier) if tier in agda_tiers() else None
    return dict(row or AGDA_TIERS[AGDA_TIER_DEFAULT])


def agda_heap(tier: str = AGDA_TIER_DEFAULT) -> str:
    """The GHCRTS caliber for one tier. R13: one caliber PER TIER, A14."""
    return str(_tier_row(tier)["heap"])


def agda_slots(tier: str = AGDA_TIER_DEFAULT) -> int:
    """The slot ceiling for one tier."""
    return int(_tier_row(tier)["slots"])


def agda_heap_gb(tier: str = AGDA_TIER_DEFAULT) -> int:
    """The `-M<n>g` figure of a tier's caliber, for the mixed-tier heap sum.

    A caliber with no readable cap counts as the largest tier's, because an
    unreadable sensor must refuse rather than clear (FM12)."""
    m = _HEAP_GB_RE.search(agda_heap(tier))
    if m:
        return int(m.group(1))
    return max((int(x.group(1)) for x in
                (_HEAP_GB_RE.search(str(v.get("heap", ""))) for v in AGDA_TIERS.values())
                if x), default=12)


#: Kept as the WIDE tier's values so an old reader of either name still works.
#: Both are DERIVED now; neither is a literal any more.
AGDA_HEAP = agda_heap(AGDA_TIER_DEFAULT)
AGDA_SLOTS = agda_slots(AGDA_TIER_DEFAULT)
# The codex header is ANSI-bold, so the literal bytes are
# "\x1b[1msession id:\x1b[0m 019ff5c4-...". A pattern anchored on "session id: "
# never matched, and every killed dispatch was therefore unresumable: the tool
# said "no session id in its record or its log" while the id sat in the log.
# MEASURED 2026-08-12 on [LJ-1.80], whose id was 019ff5c4-4557-75d0-bb7b-a00b491f8a64.
# Tolerate the escapes rather than stripping the whole file, which would cost a
# second pass over a multi-megabyte log.
#
# PI REUSES THIS PATTERN AND ADDS NONE OF ITS OWN. pi prints its session id only
# as the `id` field of the first --mode json event, so pi_stream.py re-emits it
# as a plain `session id: <uuid>` line. One pattern, three harnesses, and the two
# existing scrapes needed no change. [LJ-1.126], 2026-08-13.
SESSION_RE = re.compile(r"session id:(?:\x1b\[[0-9;]*m)?\s*([0-9a-f-]{8,})")


# --------------------------------------------------------------------------- state


@contextlib.contextmanager
def registry_lock():
    """FM1: serialize the whole load-check-save. Without this, two dispatches racing for the
    last slot both launched (three Agda agents against a ceiling of two) and a 10-way
    fan-out kept only 3 of 10 records, silently. The lock is a separate file so a corrupt
    registry cannot also break locking."""
    STATE.mkdir(parents=True, exist_ok=True)
    LOGS.mkdir(parents=True, exist_ok=True)
    with open(LOCKFILE, "a+") as fh:
        fcntl.flock(fh, fcntl.LOCK_EX)
        try:
            yield
        finally:
            fcntl.flock(fh, fcntl.LOCK_UN)


def load() -> dict:
    """FM6: a truncated or corrupt registry used to crash every command with a raw traceback.
    Now it is moved aside, reported, and replaced, so the tool degrades instead of bricking."""
    if not REGISTRY.exists():
        return {"dispatches": {}}
    try:
        data = json.loads(REGISTRY.read_text())
    except json.JSONDecodeError as exc:
        # [L3.32-T119]: this used to move the file aside and return an EMPTY
        # registry, which silently disarmed everything built on it. With no
        # records, `gate-ready` authorises a full gate over half-written
        # masters, the Agda slot count drops to zero so more agents can launch,
        # and `wait` says nothing is running. The old message told the reader to
        # "re-adopt" the live agents and NO SUCH COMMAND EXISTS.
        #
        # FM12's lesson, which was applied to `ps` and not here: an unreadable
        # sensor must REFUSE, never clear. A tool that cannot read its own state
        # must stop, not proceed as though the state were empty.
        broken = REGISTRY.with_suffix(f".corrupt-{int(time.time())}")
        shutil.copy2(str(REGISTRY), str(broken))
        raise SystemExit(
            f"dispatch: REFUSING. registry.json is corrupt ({exc}). A copy is at "
            f"{broken.name} and the original is untouched.\n"
            f"  Agents may still be running. Proceeding on an empty registry would "
            f"make gate-ready green over a half-written tree and would let the slot "
            f"ceiling be exceeded.\n"
            f"  Repair the JSON by hand, or move it aside DELIBERATELY once you have "
            f"confirmed with `pgrep -f 'bin/codex exec'` that nothing is live.")
    if not isinstance(data, dict) or not isinstance(data.get("dispatches"), dict):
        return {"dispatches": {}}
    return data


def save(reg: dict) -> None:
    """FM1/FM6: atomic replace, so a crash mid-write can never leave a half-file behind."""
    STATE.mkdir(parents=True, exist_ok=True)
    tmp = REGISTRY.with_suffix(".tmp")
    tmp.write_text(json.dumps(reg, indent=2))
    tmp.replace(REGISTRY)


def proc_start(pid: int) -> str | None:
    """The process's start time, or None when `ps` could not be consulted at all.

    THE DISTINCTION IS LOAD-BEARING and its absence was a real defect
    ([L3.32-T119], 2026-08-06). This returned "" both when `ps` ran and found
    nothing (the process is gone) and when `ps` itself failed (we simply cannot
    look). `alive()` read the second as the first, so in any sandbox where `ps`
    is blocked EVERY agent read as dead: `status` reported `agents live: 0`
    while an agent was mid-write, and `gate-ready` then answered "no agent is
    live, a full-tree gate will read a settled tree". That is precisely the
    spurious GREEN that the gate-ready check exists to prevent, manufactured by
    the check itself.

    None means unusable. "" means ran and found nothing.
    """
    try:
        out = subprocess.run(["ps", "-o", "lstart=", "-p", str(pid)],
                             capture_output=True, text=True)
    except OSError:
        return None
    if out.returncode not in (0, 1):   # 1 is ps's ordinary "no such process"
        return None
    return out.stdout.strip()


def alive(pid: int, started: str = "") -> bool:
    """FM2: EPERM means the process EXISTS and we merely cannot signal it. The old code
    caught it as OSError and answered 'dead', so in any restricted context a live agent
    read as exited, the slot count dropped, and `resume` would have duplicated it.
    FM5: a matching start time is what distinguishes our agent from a recycled PID."""
    if pid <= 0:
        return False
    try:
        os.kill(pid, 0)
    except ProcessLookupError:
        return False
    except PermissionError:
        pass  # exists, owned by someone else or otherwise unsignalable
    except OSError as exc:
        if exc.errno == errno.ESRCH:
            return False
    if started:
        now = proc_start(pid)
        if now is None:
            # `ps` is unusable here, so the recycling check cannot run. TRUST
            # os.kill(pid, 0) above, which already established the process
            # exists. The previous code answered "dead" in this branch, on
            # FM1/T73's reasoning that a dead agent must not hold a slot
            # forever. That reasoning was right about its own case and wrong
            # here, because it conflated "ps found nothing" with "ps could not
            # be asked". Between the two errors the asymmetry decides it: a
            # dead agent holding a slot wastes time and is visible in `status`,
            # while a live agent read as dead makes `gate-ready` green and a
            # twelve-minute gate then reads a half-written tree and is
            # BELIEVED. Prefer the error that is loud over the one that is
            # trusted.
            return True
        if now == "":
            return False  # ps ran and found nothing: the process is gone
        if now != started:
            return False  # the PID was recycled; this is not our agent
    return True


def rec_alive(d: dict) -> bool:
    return alive(int(d.get("pid", 0) or 0), d.get("proc_start", ""))


def final_is_clean(path: str | Path) -> bool:
    """True when the final-message file holds a real return.

    [LJ-1.127], MEASURED 2026-08-13. The old test was `exists() and size > 0`,
    and on the herdr path the driver writes `herdr agent read`'s output into
    that file WHATEVER it is. Both `herdrtest1-resume` attempts failed with
    `{"error":{"code":"agent_not_found"...}}`, wrote 105 and 112 bytes, and
    were announced in returns.log as `clean`. A failed run recorded as a clean
    return is the silent-death shape this whole file exists to refuse.
    """
    p = Path(path or "")
    if not p.exists() or p.stat().st_size == 0:
        return False
    try:
        head = p.read_text(errors="ignore").strip()
    except OSError:
        return False
    if not head:
        return False
    # A herdr error object and nothing else. Anything longer holds real output.
    if head.startswith('{"error"') and len(head) < 600:
        return False
    return True


def running(reg: dict) -> dict:
    # FM7: every record access goes through .get, so a key drift degrades instead of crashing.
    return {t: d for t, d in reg.get("dispatches", {}).items() if rec_alive(d)}


def agda_holders(reg: dict) -> dict:
    return {t: d for t, d in running(reg).items() if d.get("agda")}


def agda_heap_sum_over(reg: dict, tier: str) -> str:
    """A14's mixed worst case: the message when one more holder breaks the cap.

    It returns "" when the dispatch fits. WHY IT IS NOT A SLOT COUNT: two HEAVY
    holders at -M12g and two WIDE at -M8g sit inside BOTH per-tier ceilings and
    still reach 40 GB of worst-case heap. A14 caps the sum at
    `tiers.shared.max_heap_sum_gb`, 32 GB, and only the registry knows what tier
    each live holder took, because `launch()` writes it there.

    A record written before A14 carries no tier. It counts as the DEFAULT tier
    rather than as zero: an unread field must never make the sum look smaller.
    """
    held = agda_holders(reg)
    total = sum(agda_heap_gb(d.get("tier") or AGDA_TIER_DEFAULT) for d in held.values())
    want = agda_heap_gb(tier)
    if total + want <= AGDA_MAX_HEAP_SUM_GB:
        return ""
    parts = ", ".join(f"{t} {agda_heap_gb(d.get('tier') or AGDA_TIER_DEFAULT)} GB "
                      f"({d.get('tier') or AGDA_TIER_DEFAULT})"
                      for t, d in sorted(held.items()))
    return (f"the live Agda holders already budget {total} GB of worst-case heap "
            f"({parts or 'none'}), and one more {tier} holder adds {want} GB. A14 "
            f"caps the mixed worst case at {AGDA_MAX_HEAP_SUM_GB} GB. Wait, or "
            f"dispatch it in a smaller tier.")


#: PID 1 is `launchd` on this machine and `init` elsewhere. IT IS NOT AN AGENT: it is
#: where the kernel reparents a process whose real parent exited. `agda_pileup()` below
#: keeps it out of the per-parent count for that reason, and `agda_orphans()` reads it as
#: the ONE reliable mark of an Agda run that nobody owns any more.
INIT_PID = 1


def _etime_seconds(text: str):
    """`ps -o etime=` as whole seconds, or None. The format is `[[dd-]hh:]mm:ss`.

    THE THREE SHAPES ARE ALL LIVE ON THIS MACHINE, measured 2026-08-22 from one
    `ps -A -o pid=,ppid=,etime=,comm=` read: `41:27` (mm:ss), `07:39:52` (hh:mm:ss)
    and `03-05:55:58` (dd-hh:mm:ss). A shape this cannot parse returns None and the
    caller then treats the process as UNAGED rather than as old, because a kill
    decided on an unreadable clock is the wrong direction.
    """
    s = (text or "").strip()
    days = 0
    if "-" in s:
        head, _, s = s.partition("-")
        try:
            days = int(head)
        except ValueError:
            return None
    parts = s.split(":")
    if not 2 <= len(parts) <= 3:
        return None
    try:
        nums = [int(p) for p in parts]
    except ValueError:
        return None
    if any(n < 0 for n in nums) or days < 0:
        return None
    if len(nums) == 2:
        nums = [0] + nums
    return days * 86400 + nums[0] * 3600 + nums[1] * 60 + nums[2]


def agda_processes() -> tuple[list[tuple[int, int, int | None]], str | None]:
    """Every live `agda` process as `(pid, ppid, elapsed_s)`, and a warning or None.

    ONE `ps` READ AND ONE PARSER. `agda_pileup()` and `agda_orphans()` both answer
    questions about the same population, and two readers of one process table drift.
    `elapsed_s` is None when `ps` printed an `etime` this cannot parse.

    FM12 applies here as it does to `strays()`: `ps` can fail outright, and an
    unreadable `ps` must say BLIND rather than return an empty list that reads as an
    all-clear.
    """
    try:
        out = subprocess.run(["ps", "-A", "-o", "pid=,ppid=,etime=,comm="],
                             capture_output=True, text=True)
    except OSError as exc:
        return [], f"could not run ps ({exc}); the agda census is BLIND"
    if out.returncode != 0 or not out.stdout.strip():
        return [], "ps returned nothing; the agda census is BLIND"
    rows: list[tuple[int, int, int | None]] = []
    for line in out.stdout.splitlines():
        parts = line.split(None, 3)
        if len(parts) != 4 or os.path.basename(parts[3].strip()) != "agda":
            continue
        try:
            pid, ppid = int(parts[0]), int(parts[1])
        except ValueError:
            continue
        rows.append((pid, ppid, _etime_seconds(parts[2])))
    return rows, None


def agda_pileup() -> tuple[int, dict[int, int], str | None]:
    """Total live agda processes, and how many each parent owns.

    WHY THIS EXISTS. On 2026-08-12 one agent had SIX agda processes alive at
    once, all children of the same codex wrapper, all checking the same probe,
    started a minute or two apart with none of the earlier ones killed. Each
    carried C-12's -M8g cap, so the worst case was 48 GB on a 64 GB machine,
    and the load average reached 19. The OWNER saw it; no tool did. `status`
    counted codex agents and never looked at what they had spawned, so a
    per-process cap silently became a machine-level risk. C-12 says ONE agda
    process per agent, and now something checks it.

    **`INIT_PID` IS NOT A PARENT IN THIS COUNT, AND READING IT AS ONE FROZE THE WHOLE
    LOOP FOR 2 h 07 min.** MEASURED 2026-08-22: two Agda processes left over from
    LJ-1.524 sat at PPID 1 with 153 and 145 minutes elapsed. They bucketed together as
    `{1: 2}`, `admits()` at `scripts/pod/pod.py:2077` read that as C-12's pile-up and
    returned False for EVERY task, Agda or not, because the pile-up limb runs before
    the `if not t.agda` early-out at `:2079`. Rule (c) at `scripts/pod/pod.py:4267-4269`
    then `continue`d in silence. The transition log carries NOTHING between seq 2448 at
    `2026-08-22T07:04:19Z` and seq 2449 at `2026-08-22T09:11:26Z`, and four tasks that
    had been sitting in RETURNED across that gap all closed inside 86 seconds once the
    two orphans were killed by hand.

    C-12's rule is ONE agda process per AGENT, and the orphanage is not an agent: N
    processes at PPID 1 are N different dead parents, not one live agent retrying. The
    pile-up test therefore skips the bucket. The orphans STAY IN `total`, because they
    are real processes burning real CPU against A14's tier ceiling, and `agda_orphans()`
    below is what actually removes them.
    """
    rows, warn = agda_processes()
    if warn:
        return 0, {}, warn
    per_parent: dict[int, int] = {}
    for _pid, ppid, _elapsed in rows:
        if ppid == INIT_PID:
            continue                          # the orphanage, not an agent
        per_parent[ppid] = per_parent.get(ppid, 0) + 1
    return len(rows), per_parent, None


def agda_orphans(min_elapsed_s: int) -> tuple[list[tuple[int, int]], str | None]:
    """Every OWNERLESS `agda` process older than `min_elapsed_s`, as `(pid, elapsed_s)`.

    **THIS IS THE OTHER HALF OF GAP M2, and the gap's first half never covered it.**
    `run_agda()` at `scripts/pod/facts.py:223-224` passes `timeout=deadline_s` to
    `subprocess.run`, so the POD's OWN Agda runs are bounded. A worker's are not: a
    coder or a mathematician typechecks its own work inside a herdr pane, that Agda is a
    child of the pane and not of anything the POD holds a pid for, and no limb of
    `_rule_b()` at `scripts/pod/pod.py:4108-4125` can reach it. The `pid dead` limb kills
    nothing at all, and `kill_process_group(t.pid)` on the deadline limb targets the
    `bash -c driver` group, which the pane agent left at `start_new_session=True`
    (`:1797-1799`). So a worker's Agda had NO deadline in this program.

    TWO CONDITIONS, AND BOTH ARE THE INCIDENT'S OWN MEASUREMENTS.

      1. `ppid == INIT_PID`. The parent has exited, so nobody is waiting on this run and
         nobody can read its answer. A live worker's Agda has a live parent; the POD's
         own `run_agda()` child has the POD as its parent. Neither can match.
      2. `elapsed_s > min_elapsed_s`. The caller passes `agda_deadline_s`, 1800 s
         (`dev/pod/heads.toml:264`), which is 5.9 times the measured worst case of
         300.81 s (`dev/pod/heads.toml:276-279`). The two orphans of 2026-08-22 ran 153
         and 145 minutes, which is 5.1 and 4.8 times that bar.

    Condition 1 is what makes this safe rather than merely bounded: it cannot select a
    process that any live thing owns. A process whose `etime` did not parse is UNAGED
    and is never returned, for the same reason.
    """
    bar = min_elapsed_s
    if not isinstance(bar, int) or isinstance(bar, bool) or bar <= 0:
        return [], (f"the orphan bar {min_elapsed_s!r} is not a positive whole number "
                    f"of seconds; the agda orphan reap is REFUSED this tick")
    rows, warn = agda_processes()
    if warn:
        return [], warn
    return sorted((pid, elapsed) for pid, ppid, elapsed in rows
                  if ppid == INIT_PID and elapsed is not None and elapsed > bar), None


def strays(reg: dict) -> tuple[list[str], str | None]:
    """FM12: ps can fail outright (it did, inside a sandbox), and an unreadable ps used to
    crash the census or silently report no strays, which is the worst possible answer from
    a safety check. Returns (strays, warning).

    [LJ-1.127], 2026-08-13: THE HERDR SWITCH BROKE THIS CHECK AND IT WOULD HAVE
    FIRED ON EVERY LEGITIMATE AGENT. Under the old setsid path the codex process
    WAS the registry's pid, or its direct child. Under herdr the agent runs in a
    server-owned pane, so its parent is a herdr shell and neither its pid nor its
    ppid is in the registry. Every live herdr agent therefore matched the stray
    test, and `cmd_status` exits 1 on a stray, so the census would have reported
    a violation for correct work and returned failure. A safety check that fires
    on the normal case teaches its reader to ignore it.

    THE CURE IS ANCESTRY, not a wider exemption. A codex process whose ancestor
    chain reaches a herdr process is herdr-managed and is not a raw stray. That
    keeps the check's real target: a codex started by hand, which belongs to no
    registry record and to no herdr agent either.

    The herdr-managed processes are still audited, one level up, by
    `herdr_orphan_agents()`: a herdr AGENT whose name maps to no registry task
    is the herdr-era shape of the same violation.
    """
    known = {int(d.get("pid", 0) or 0) for d in reg.get("dispatches", {}).values()}
    try:
        out = subprocess.run(["ps", "-A", "-o", "pid=,ppid=,comm="],
                             capture_output=True, text=True)
    except OSError as exc:
        return [], f"could not run ps ({exc}); stray detection is BLIND this run"
    if out.returncode != 0 or not out.stdout.strip():
        return [], ("ps returned nothing; stray detection is BLIND this run, so do not "
                    "read an empty stray list as an all-clear")
    parent: dict[int, int] = {}
    comm: dict[int, str] = {}
    rows: list[tuple[int, int, str]] = []
    for line in out.stdout.splitlines():
        parts = line.split(None, 2)
        if len(parts) != 3:
            continue
        try:
            pid, ppid = int(parts[0]), int(parts[1])
        except ValueError:
            continue
        parent[pid], comm[pid] = ppid, parts[2].strip()
        rows.append((pid, ppid, parts[2]))

    def herdr_managed(pid: int) -> bool:
        """True when an ancestor of `pid` is a herdr process. Bounded, because a
        corrupt ps table could otherwise loop forever."""
        seen, cur = set(), pid
        for _ in range(64):
            cur = parent.get(cur, 0)
            if cur <= 1 or cur in seen:
                return False
            seen.add(cur)
            if "herdr" in os.path.basename(comm.get(cur, "")).lower():
                return True
        return False

    found = []
    for pid, ppid, c in rows:
        # FM12: match a PREFIX, since macOS truncates comm and a longer needle silently
        # matched nothing.
        if "codex-darwin-arm" not in c:
            continue
        if pid in known or ppid in known:
            continue
        if herdr_managed(pid):
            continue
        # FM12: an orphan whose wrapper died is ours, not a violation; only flag it when no
        # registry record could plausibly own it.
        found.append(f"pid {pid} (ppid {ppid})")
    return found, None


# --------------------------------------------------------------------------- herdr


def herdr_agents() -> tuple[list[dict], str | None]:
    """Every agent the herdr server knows, or a reason we could not ask.

    Returns ([], None) when herdr is not installed at all, because the codex and
    pi harnesses do not need it and a missing optional tool is not a defect.
    """
    if not shutil.which("herdr"):
        return [], None
    try:
        out = subprocess.run(["herdr", "agent", "list"],
                             capture_output=True, text=True, timeout=15)
    except (OSError, subprocess.SubprocessError) as exc:
        return [], f"could not run `herdr agent list` ({exc})"
    if out.returncode != 0:
        return [], f"`herdr agent list` failed: {out.stderr.strip()[:160]}"
    try:
        return json.loads(out.stdout)["result"]["agents"], None
    except (json.JSONDecodeError, KeyError, TypeError) as exc:
        return [], f"`herdr agent list` returned an unreadable shape ({exc})"


def herdr_agent_named(name: str) -> dict | None:
    """The live herdr agent with this name, or None.

    An unreadable list returns a placeholder dict, which is the SAFE side for a
    resident reuse: treating a live agent as missing would start a SECOND
    session under the same name. `maintainer_alive()` uses the same direction.
    """
    if not herdr_present():
        return None
    agents, err = herdr_agents()
    if err:
        return {"name": name, "agent_status": "unknown"}
    for a in agents:
        if a.get("name") == name:
            return a
    return None


def herdr_present() -> bool:
    """Is the herdr binary here at all? `herdr_agents()` cannot say.

    It returns `([], None)` both when herdr is MISSING and when herdr knows no agents,
    and a liveness check must not read the first as the second: that reads「the resident
    maintainer is gone」on a machine that could never host one, and tries to launch it
    again on every tick.
    """
    return bool(shutil.which("herdr"))


def herdr_prompt(name: str, text: str) -> bool:
    """Submit one prompt to a live agent. It launches nothing and it does NOT wait.

    **NO `--wait`, ON PURPOSE.** A prompt to a busy head queues and is read when that
    head finishes its current tool call (`dev/LESSONS.md` C-61, once worth 4.25 hours).
    Waiting here would block the tick loop behind whatever the maintainer is doing, and
    the queueing is the property rule (e) wants: a batch that arrives mid-repair takes
    its turn instead of racing it.
    """
    if not shutil.which("herdr"):
        return False
    try:
        out = subprocess.run(["herdr", "agent", "prompt", name, text],
                             capture_output=True, text=True, timeout=30)
    except (OSError, subprocess.SubprocessError):
        return False
    return out.returncode == 0


def sweepable_panes(reg: dict) -> tuple[list[dict], list[dict], str | None]:
    """Panes safe to close, panes that are EVIDENCE, and any blindness warning.

    WHY THIS EXISTS. `[LJ-1.124]`'s pane did not close. Its driver was launched
    BEFORE the close-on-clean-finish change, so it ran the old code and the
    orchestrator closed the pane by hand. That is one instance of a general
    hole: a pane whose driver died, or whose driver predates a change, is never
    swept by anything.

    THE RULE, and the second half matters more than the first.

      SWEEPABLE: the herdr agent is idle, its name maps back to a registry task,
      that task's record is NOT alive, and the task finished CLEANLY, meaning it
      left a non-empty final message and its log carries no death marker.

      EVIDENCE, never closed: everything else that maps to a task. A pane whose
      task ended in a death is the only record of how it died, and this project
      read three deaths out of a pane that was still open on 2026-08-13. The
      sweep reports those and leaves them alone.

    A pane holding a LIVE agent is never in either list, and neither is a pane
    whose agent name maps to no task at all: that is somebody else's terminal,
    including the orchestrator's own.
    """
    agents, warn = herdr_agents()
    by_name = {herdr_name(t): (t, d) for t, d in reg.get("dispatches", {}).items()}
    sweep, evidence = [], []
    for a in agents:
        hit = by_name.get(a.get("name", ""))
        if not hit:
            continue                      # not ours: never touched
        task, d = hit
        if a.get("agent_status") not in ("idle", "done"):
            continue                      # still working or blocked
        if rec_alive(d):
            continue                      # its driver is alive; leave it be
        final = Path(d.get("final", ""))
        clean = final_is_clean(final)
        died = False
        log = Path(d.get("log", ""))
        if log.exists():
            try:
                tail = log.read_text(errors="ignore")[-4000:]
                died = ("kept for forensics" in tail or "DIED" in tail
                        or "NOT closed" in tail)
            except OSError:
                died = True               # unreadable log: treat as evidence
        row = {"task": task, "name": a.get("name"), "pane": a.get("pane_id"),
               "clean": clean, "died": died}
        (sweep if (clean and not died) else evidence).append(row)
    return sweep, evidence, warn


def close_pane(pane_id: str) -> bool:
    try:
        out = subprocess.run(["herdr", "pane", "close", pane_id],
                             capture_output=True, text=True, timeout=15)
    except (OSError, subprocess.SubprocessError):
        return False
    return out.returncode == 0


# --------------------------------------------------------------------------- validation


SAFE_TASK = re.compile(r"^[A-Za-z0-9][A-Za-z0-9._-]*$")

# FM4: the old regex required the literal word "write" immediately before a _build/ path and
# so missed every realistic phrasing, INCLUDING the one this file's own documentation uses
# ("write your report to _build/x.md"). Widened to any write-ish verb within a short window
# of a _build/ path.
WRITE_ORDER = re.compile(
    r"(writ|output|save|deliver|produce|emit)\w*\b[^.\n]{0,80}?`?_build/", re.I)


def check_model(model: str, allow: bool) -> str | None:
    """FM3/FM17: called from launch(), so EVERY path refuses, not only `run`; and gated on a
    date so it lifts itself instead of needing a code edit nobody will remember to make."""
    until = BLOCKED_MODELS.get(model)
    if not until or allow:
        return None
    if _dt.date.today() >= until:
        return None
    return (f"{model} is rejected by this backend (measured 2026-08-05: 'available starting "
            f"early August 2026'). The agent dies in seconds having written nothing, which "
            f"looks exactly like a clean empty finish. Use {DEFAULT_MODEL}, or pass "
            f"--allow-model once a one-line `codex exec -m {model} \"say ok\"` succeeds.")


# POD EDIT 6 of 6, row 14 (design section 6.2). `switch_defects()` IS DELETED
# HERE, whole. It refused a dispatch whose HEAD contradicted THE SWITCH, and it
# read `POLICY.in_force()`, `POLICY.head()` and the `tier:` line.
#
# WHY IT GOES. DD17 is SUPERSEDED, section 7.1. It is also INERT once row 21
# retires scripts/dispatch/dispatch_policy.py: the import fails, `POLICY` is
# None, and the function's first statement returns an empty list for ever. A
# refusal that cannot fire is a lie about what is checked (C-43), so it is
# removed rather than left. (The first form of this note read `POLICY_ERROR
# becomes truthy`. That variable now stays EMPTY for the designed absence, so
# the test that matters is `POLICY is None`.)
#
# ITS MEASUREMENT IS KEPT. MEASURED 2026-08-15: LJ-1.272 at 09:29 and LJ-1.273
# at 10:21 Beijing both ran pi/deepseek through herdr, inside the 09:00 to 12:00
# PEAK window, when the other mode was in force and deepseek was at double
# price. Nothing stopped either dispatch. The POD closes that hole differently:
# the head is resolved ONCE from dev/pod/heads.toml, at dispatch, and the
# resolved `model`, `effort`, `role` and `heads_sha256` go into the transition
# log line (AD26, design section 5.3.1). A program reads the file; nobody
# answers "which head" from memory.


def launch_defects(brief: Path, sandbox: str, agda: bool = False,
                   case: str = "default") -> list[str]:
    """Every refusal that must fire before an agent starts.

    ADDED 2026-08-07 after the orchestrator dispatched T135 on a brief that
    `check` had just refused. `cmd_check` called `validate` AND
    `rule_bundle_defects`; `cmd_run` called only `validate`. So the rule
    that says "cite the mandatory bundle" existed only in the command nobody
    is forced to run.

    This is the FM3 defect class again, and the docstring at the top of this
    file already records it: "the dead-model refusal lived only in `run`, so
    `queue` and `resume` could still launch it". A refusal that one entry
    point enforces is not a refusal. Every launch path now calls this one
    function, so a new check cannot land in half of them.

    POD EDIT 6 of 6 (design section 6.2). THREE OF THE FIVE CALLS ARE GONE, and
    each removal is a released refusal with a row number in the design's table:

      row 10  rule_bundle_defects()  AGENTS.md is void under AD4. The function
                                     only escaped when scripts/pod/rules.py
                                     was absent, and row 22 KEEPS that file, so
                                     it would have stayed live for ever.
      row 11  dd4_defects()          DD4 is a WRITTEN RULE, clause W2. The
                                     program carries it into
                                     dev/pod/instructions/mathematician.md at
                                     every dispatch. THE GATE CANNOT TRAVEL WITH
                                     IT: it reads the BRIEF FILE and demands the
                                     token `DD4`, and neither the section 6.3
                                     template nor the worked brief carries one,
                                     so keeping it refuses every POD dispatch
                                     from day 2 onward. Injecting the
                                     instruction file at prompt time does not
                                     satisfy it, because the refusal never reads
                                     the prompt. W2 has no metric by the owner's
                                     own decision, so its enforcement point is
                                     agent discipline and section 3.1 states the
                                     loss.
      row 14  switch_defects()       DD17 is SUPERSEDED. It is also inert once
                                     row 21 retires dispatch_policy.py, which
                                     leaves `POLICY` None.

    `case` is now unread here. The parameter stays because `cmd_run`,
    `cmd_check` and `cmd_queue` all pass it, and the design orders no signature
    change.

    THE TWO CALLS THAT STAY. `validate()` keeps five of its nine refusals, and
    `survey_defects()` keeps both of its own: DD18 is MECHANISED, section 7.4
    injects `## ARCHIVE` and `## LITERATURE`, and pre-flight P15 reads them.

    THE UNREADABLE BRIEF IS REFUSED FIRST, and it used to be a TRACEBACK. The
    sum below evaluates BOTH callees, so `survey_defects()` read the file even
    after `validate()` had already answered "brief does not exist", and
    `dispatch.py check <missing brief>` printed a FileNotFoundError. A path that
    is a DIRECTORY got past `exists()` and raised IsADirectoryError inside
    `validate()` itself. The POD runs UNATTENDED, so a traceback is not a cosmetic
    defect: the loop stops with nobody reading it. Both are one refusal now, with
    the exit code this file's contract already gives a refusal, 1.
    """
    if (why := brief_unreadable(brief)):
        return [why]
    return validate(brief, sandbox, agda) + survey_defects(brief)


def brief_unreadable(brief: Path) -> str:
    """The one reason a brief cannot be read at all, or "" when it can.

    Every caller that is about to read the file calls this first. It answers the
    four ways a path fails before its CONTENT can be judged: it is missing, it is
    a directory, the operating system refuses it, or its bytes are not UTF-8.
    """
    try:
        if not brief.exists():
            return (f"brief does not exist: {brief}. A brief lives at "
                    f"{ROOT}/agents/tasks/<CODE>/<CODE>.md and it is tracked.")
        if brief.is_dir():
            return (f"brief is a DIRECTORY, not a file: {brief}. A task directory "
                    f"HOLDS the brief; name the brief file inside it, which is "
                    f"{brief}/<CODE>.md.")
        brief.read_text(encoding="utf-8")
    except UnicodeDecodeError as exc:
        return f"brief is not UTF-8 text: {brief} ({exc.reason})"
    except OSError as exc:
        return f"brief cannot be read: {brief} ({exc.strerror or exc})"
    return ""


def case_from_args(a) -> str:
    """The dispatch case, ASSERTED on the command line and never inferred.

    Mutually exclusive by construction: argparse gives at most one of the two flags a
    true value, and neither means the default case.
    """
    if getattr(a, "adversarial", False):
        return "adversarial"
    if getattr(a, "fallback", False):
        return "fallback"
    return "default"


def validate(brief: Path, sandbox: str, agda: bool = False) -> list[str]:
    """Refuse the failure modes that have actually happened, not hypothetical ones.

    IT GUARDS ITS OWN READ. `launch_defects()` calls `brief_unreadable()` first,
    but this function has direct callers too, and a check that only one entry
    point performs is not a check. That is FM3, recorded at the top of this file.
    """
    defects = []
    if (why := brief_unreadable(brief)):
        return [why]

    # FM15: compare the real path, not just the parent's name, so a fixtures directory that
    # happens to be called "briefs" no longer satisfies the pinning rule.
    #
    # THE HOME MOVED AND THIS CHECK DID NOT, until 2026-08-14. The owner merged
    # briefs and reports into one directory per task, so a brief now lives at
    # `agents/tasks/<CODE>/`, is TRACKED, and survives a reboot better than
    # `_build/` ever did, `_build/` being a temporary folder by AGENTS.md's own
    # words. This check still demanded `_build/briefs/`, so EVERY dispatch
    # through this tool would have been refused since the move.
    #
    # NOBODY SAW IT, and the reason is worth keeping: the DD17 override sends
    # every default dispatch in-harness, and an in-harness dispatch never passes
    # through this file. A broken path stays green while nothing walks it. It
    # surfaced only when an adversarial review had to go to the harness the
    # switch names.
    #
    # THE LEGACY HOME WAS REMOVED 2026-08-14. The briefs that once lived in
    # `_build/briefs/` moved into `agents/tasks/<CODE>/`; the directory is
    # gone, `_build/` is git-ignored and `make clean` empties it, and the
    # workaround that created it is forbidden by AGENTS.md, which calls
    # `_build/` a temporary folder and not a rubbish bin. The task directory
    # is the only pinned home, and ORCHESTRATION section 3 is the rule it
    # serves: the brief must survive a reboot and be readable by the owner.
    try:
        real = brief.resolve()
        pinned = real.parent.parent == (ROOT / "agents" / "tasks").resolve()
    except OSError:
        pinned = False
    if not pinned:
        defects.append(f"brief is not pinned: it is at {brief.parent}. Put it in its task "
                       f"directory, {ROOT}/agents/tasks/<CODE>/, where it is tracked; "
                       f"ORCHESTRATION section 3 requires the brief to survive a reboot "
                       f"and be readable by the owner")

    text = brief.read_text(encoding="utf-8")

    # POD EDIT 6 of 6, rows 3 and 4 (design section 6.2). TWO REFUSALS DELETED
    # HERE, and both die of the same cause: DD17 is SUPERSEDED, section 7.1.
    #
    #   row 3  no `tier:` line. The head no longer comes from a line of brief
    #          prose. It comes from dev/pod/heads.toml, resolved ONCE at
    #          dispatch and written into the transition log (AD26).
    #   row 4  the tier line's mode against the switch. The switch is
    #          scripts/dispatch/dispatch_policy.py, which section 7.1 row 21
    #          retires, and there is no mode to be in force any more.
    #
    # The measurement behind row 4 is kept, because it says what the POD must
    # not lose: MEASURED 2026-08-15, LJ-1.272 at 09:29 and LJ-1.273 at 10:21
    # both went to pi/deepseek inside the Beijing PEAK window, when the other
    # mode was in force. The orchestrator answered "which head" from memory. The
    # POD cannot repeat it, because a program and not a memory reads heads.toml.

    # FM16: a SCOPE (write) section only orders a write when it actually names a path, so a
    # brief documenting "SCOPE (write): none" is no longer refused for no reason.
    scope_names_path = False
    m = re.search(r"^#*\s*SCOPE \(write\)(.*?)(?=^#|\Z)", text, re.M | re.S)
    if m and re.search(r"`?(_build/|src/)", m.group(1)):
        scope_names_path = True
    if (WRITE_ORDER.search(text) or scope_names_path) and sandbox == "read-only":
        defects.append("brief orders a written deliverable but the sandbox is read-only, "
                       "which blocks the agent from writing its own report. Use "
                       "workspace-write and let the brief's SCOPE restrict what may be "
                       "touched")

    # FM4: Agda writes .agdai interface files, so this combination cannot work at all.
    if agda and sandbox == "read-only":
        defects.append("--agda with --sandbox read-only cannot work: Agda writes .agdai "
                       "interface files and a read-only sandbox blocks them")

    # [L3.32-T119] 1.6: the rule-bundle refusal derives the task kind from this
    # header, and 89 of 127 briefs lack it, so the derivation silently fell back
    # to `recon` and asked for the smallest bundle. Requiring it is the one line
    # that must come before any write-territory check can be built at all.
    if not re.search(r"^#*\s*SCOPE\s*\(write\)", text, re.M | re.I):
        defects.append(
            "brief has no `SCOPE (write)` section. The task kind is DERIVED from "
            "it, so without it the rule bundle silently defaults to the smallest "
            "one. Write it even for a read-only dispatch: a SCOPE (write) naming "
            "only the report is the honest form.")

    # POD EDIT 6 of 6, rows 8 and 9 (design section 6.2). TWO MORE REFUSALS
    # DELETED HERE, and both rested on dev/ORCHESTRATION.md, which AD4 voids.
    #
    #   row 8  no RETURN section. The brief's BRANCH BLOCK is the return
    #          contract now (design section 4.1): the mathematician writes the
    #          branches, and admission appends each one to the rule table, so a
    #          return is judged against a row and never against prose.
    #   row 9  no checkable evidence. The section 6.3 template would pass this
    #          anyway, because `## PREMISES` writes `file:line`. A refusal that
    #          the template satisfies by construction is not a refusal.
    return defects


# --------------------------------------------------------------------------- launching


def _require_vendor_or_die() -> None:
    """Re-raise the vendor refusal, on the LAUNCH path and nowhere else.

    The import block above swallows it so that `status` and `wait` keep working
    when the config names a vendor `pi` cannot run. A LAUNCH must not: starting
    an agent on a vendor with no wiring is the silent failure [LJ-1.288]'s
    refusal exists to prevent, and C-43 is why it is loud.
    """
    if VENDOR_ERROR:
        print(f"dispatch: REFUSED: {VENDOR_ERROR}", file=sys.stderr)
        raise SystemExit(1)
    if POLICY is not None and hasattr(POLICY, "require_vendor_wired"):
        POLICY.require_vendor_wired()


def _prompt_files(preamble, brief, reuse_resident: bool = False) -> list:
    """Files `cat` joins into one prompt.

    A FRESH start (or any dispatched worker) gets the preamble then the brief.
    A REUSE of a resident agent gets the brief alone: the slot file, AGENTS.md,
    the screen and the direction were cat'd at session start. Recatting them on
    every refill and every later task paid the same Boundary again.
    """
    if reuse_resident:
        return [brief]
    return list(preamble or []) + [brief]


def _cat_list(preamble, brief, reuse_resident: bool = False) -> str:
    """The shell-quoted file list `cat` receives.

    ONE SOURCE PER FILE AND NO COPY ON DISK. The shared Boundary lives in `AGENTS.md`
    and a slot's own clauses in its instruction file; `cat` joins them at first
    start, so neither is ever transcribed into the other. That is the owner's
    single-source rule of 2026-08-18 applied to the prompt itself.
    """
    files = _prompt_files(preamble, brief, reuse_resident)
    return " ".join(shlex.quote(str(f)) for f in files)


def launch(task: str, brief: Path, agda: bool, sandbox: str, model: str,
           resume_id: str | None = None, note: str | None = None,
           allow_model: bool = False, case: str = "default",
           effort: str = "", tier: str = AGDA_TIER_DEFAULT,
           preamble: "list[Path] | None" = None,
           provider: str | None = None, resident: bool = False,
           workdir: "Path | None" = None,
           agent_name: str | None = None) -> int:
    # POD EDIT 3 of 6, part 1 of 3 (design section 6.2). `effort` is the claude
    # CLI's `--effort` value and edit 2 puts it on the argv. It defaults to the
    # empty string so every existing caller keeps working; the POD passes
    # `--harness`, `--model` and `--effort` on every dispatch.
    # `tier` is A14's, and it defaults to WIDE, which is the ordinary tier.
    # `case` is only read by switch_defects, below, and a RESUME skips that block entirely:
    # DD17 step 6 rules that an agent already running keeps the head that was correct when
    # it was sent, and the `if resume_id is None:` guard already implements exactly that.
    # FM14: a task name becomes a filename and a registry key, so `../escape` wrote outside
    # the state tree and `a/b` crashed.
    _require_vendor_or_die()
    if not SAFE_TASK.match(task):
        print(f"dispatch: refused: task name {task!r} must match {SAFE_TASK.pattern} "
              f"(no slashes, no ..)", file=sys.stderr)
        return 1

    if tier not in agda_tiers():
        print(f"dispatch: refused: tier {tier!r} is not one of "
              f"{', '.join(agda_tiers())}. A14 names two, and dev/pod/heads.toml "
              f"is where they live.", file=sys.stderr)
        return 1
    if agda and HEADS_ERROR:
        # An unreadable config is not a reason to guess a heap budget. C-12's
        # floor still runs, so a hand dispatch is not blocked, but it is LOUD:
        # a silent fallback is how the wrong caliber got measured in the first
        # place.
        print(f"dispatch: WARNING: {HEADS_ERROR}", file=sys.stderr)

    # THE EMPTY EFFORT IS A REFUSAL AND IT USED TO BE AN ARGV VALUE.
    #
    # Edit 2 puts `--effort <effort>` on a claude pane's argv unconditionally,
    # so an unset effort reached the CLI as `--effort ""`. `--effort` is not
    # optional for the POD either: `dev/pod/heads.toml` gives every one of the
    # five slots an effort, and AD26 records the value that RAN. A run at the
    # CLI's own default is a run at an effort nobody chose and nobody logged.
    #
    # THE REFUSAL LIVES HERE because `launch()` is the one funnel every path
    # crosses. `main()` refuses the same thing earlier as a USAGE error, exit 2;
    # this one is a launch refusal, exit 1. FM3 is the rule: a check that one
    # entry point performs is not a check. A RESUME reaches this line with the
    # effort recovered from the record, so an old record with no effort is
    # refused here rather than resumed at a default.
    if HERDR_KIND.get(HARNESS) == "claude" and not effort:
        print(f"dispatch: REFUSED. the {HARNESS} harness runs the claude CLI, whose "
              f"`--effort` takes one of {', '.join(LEGAL_EFFORTS)}, and none was "
              f"given. An empty value reaches the pane as `--effort \"\"`. Pass "
              f"--effort, or read the slot's value from dev/pod/heads.toml, which "
              f"is its one home.", file=sys.stderr)
        if resume_id:
            print(f"          this is a RESUME: {task} has no `effort` in its "
                  f"registry record, so there is no recorded value to resume at.",
                  file=sys.stderr)
        return 1

    # FM3: the model refusal lives HERE, so run, queue and resume all pass through it.
    if (why := check_model(model, allow_model)):
        print(f"dispatch: REFUSED. {why}", file=sys.stderr)
        return 1

    # NOTES PRINT ON EVERY LAUNCH PATH, and this one goes here for a reason the
    # file's own history supplies. The archive NOTE was first wired into
    # cmd_check alone, so `run`, `queue` and `resume` never printed it. That is
    # the FM3 defect verbatim, recorded at the top of this file: "the dead-model
    # refusal lived only in `run`, so `queue` and `resume` could still launch
    # it". A check that one entry point performs is not a check. launch() is
    # the one funnel every path crosses.
    #
    # It is a NOTE and never a defect: it must not block, because the claim
    # under test is that DD18's archive half needs no gate, and a gate would
    # destroy the evidence by making the lapse impossible.
    # FM8: the queue's waiter re-reads the brief at fire time, which could have been edited
    # or deleted since it was validated, so validate again at the moment of launch.
    if resume_id is None:
        # [LJ-1.127]: `return 1` used to sit INSIDE this loop, so a brief with
        # four defects printed one and stopped. The orchestrator then fixed
        # that one, re-ran, and found the next: four round trips for one
        # brief. `cmd_run` and `cmd_check` always printed the whole list.
        if defects := launch_defects(brief, sandbox, agda, case):
            for d in defects:
                print(f"dispatch: REFUSED: {d}", file=sys.stderr)
            return 1

    with registry_lock():
        reg = load()
        # [L3.32-T119]: refuse on the BRIEF, not only the task name. A resume
        # launches as `T-resume`, so a queued `T` saw no live `T` and launched
        # anyway: two agents, one brief, one write territory, no check. The
        # brief is what the territory belongs to, so it is what must be unique.
        holder = brief_in_flight(brief)
        if holder and holder != task:
            print(f"dispatch: REFUSED. {holder} is already live on this exact brief "
                  f"({brief.name}). Two agents on one brief hold the same write "
                  f"territory and will overwrite each other.", file=sys.stderr)
            return 1
        if (clash := territory_in_flight(brief, task)):
            other, overlap = clash
            print(f"dispatch: REFUSED. {other} is live and its write scope already "
                  f"holds {', '.join(sorted(overlap))}. Two agents writing one file "
                  f"in one checkout see each other's edits, and the second patch "
                  f"either fails on stale context or silently drops the first. "
                  f"Narrow this brief's SCOPE (write), or wait for {other}.",
                  file=sys.stderr)
            return 1
        if task in running(reg):
            print(f"dispatch: {task} is already running "
                  f"(pid {reg['dispatches'][task].get('pid')})", file=sys.stderr)
            return 1
        # FM10: never silently overwrite a dead task's record; its session id is the only
        # way to resume it and it existed nowhere else.
        prior = reg.get("dispatches", {}).get(task)
        if prior and not rec_alive(prior):
            reg.setdefault("history", []).append(prior)
        # A14, AND THE SLOT COUNT IS NOW THE TIER'S. WIDE admits four, HEAVY two.
        if agda and len(agda_holders(reg)) >= agda_slots(tier):
            held = ", ".join(agda_holders(reg))
            print(f"dispatch: the {agda_slots(tier)} Agda slots of the {tier} tier "
                  f"are held by {held}. "
                  f"Use `{CLI} queue {task} {brief}` instead of waiting by hand",
                  file=sys.stderr)
            return 1
        # AND THE SLOT COUNT ALONE IS NOT A14. A14 also caps the MIXED worst case
        # at 32 GB, and a slot count cannot see it: two HEAVY holders at -M12g
        # plus two WIDE at -M8g is four processes inside every per-tier ceiling
        # and 40 GB of worst-case heap on a 64 GB box. `pod.py:agda_slots()`
        # counts slots in ONE tier and never reads another tier's holders, so
        # this file is the only place the sum can be taken: the registry is where
        # every live holder's tier is written.
        if agda and (over := agda_heap_sum_over(reg, tier)):
            print(f"dispatch: REFUSED. {over}", file=sys.stderr)
            return 1

        LOGS.mkdir(parents=True, exist_ok=True)
        stamp = time.strftime("%Y%m%d-%H%M%S")
        # FM10: timestamped logs, so a re-run or a second resume never truncates the
        # forensic record of the previous attempt.
        log = LOGS / f"{task}-{stamp}.log"
        final = LOGS / f"{task}-{stamp}-final.md"
        # The pi harness only. The rendered log drops token deltas and partial tool
        # output, so the untouched event stream is kept beside it for forensics.
        events = LOGS / f"{task}-{stamp}-events.jsonl"

        if HARNESS in HERDR_HARNESSES:
            # THE DRIVER CHILD IS THE AGENT'S LIFETIME. Everything downstream in
            # this file, the slot accounting, `status`, and `wait`, keys on a PID
            # that lives exactly as long as the run. Under herdr the agent lives
            # in a server-owned pane and has no such pid, so we spawn a small
            # driver that does start + prompt --wait and exits when the agent
            # stops. Its pid IS the run's lifetime, so nothing downstream moves.
            # A HERDR RESUME TARGETS THE ORIGINAL AGENT, NOT THE NEW TASK NAME.
            # cmd_resume launches under `<task>-resume`, and mapping THAT gives
            # `lj-1-124-resume`, which no pane holds. Measured 2026-08-13: the
            # first loosened resume failed with agent_not_found on exactly that.
            # The agent still answers to its original name, so strip the suffix.
            base_task = task[:-7] if resume_id and task.endswith("-resume") else task
            hname = agent_name or herdr_name(base_task)
            reuse_resident = bool(resident and not resume_id
                                  and herdr_agent_named(hname))
            kind = HERDR_KIND.get(HARNESS, "codex")
            # A herdr pane does NOT inherit this process's environment, so the
            # Agda caliber has to be handed over explicitly. C-12: never raise
            # the cap. A14: the caliber is the TIER's, and R13's WIDE caliber is
            # `-A64m -I0 -M8g`, which HOLDS A SPACE, so this value can only reach
            # the shell through `shlex.join` below. It used to be `-M8g`, one
            # word with no allocation area, and every number measured under it
            # was incomparable with a number measured under R13's.
            envargs = ["--env", f"GHCRTS={agda_heap(tier)}"] if agda else []
            # `pane-slot.py` takes the same `--env K=V` pairs, so one list serves both it
            # and the BASE fallback below.
            slotenv = list(envargs)
            # POD EDIT 2 of 6 (design section 6.2). The old builder was a
            # two-branch conditional expression, so a `claude` kind fell into
            # the `else` branch and emitted `-- --provider deepseek --model
            # <model>`. The claude CLI has no `--provider` flag.
            #
            # `--permission-mode` matters at the FIRST launch: a trust prompt
            # makes herdr report `blocked`, which the driver below does not treat
            # as a death, so the agent would sit forever.
            # MEASURED 2026-08-17: `claude --help` lists `--model`, `--effort`
            # with exactly the five values of `legal.efforts`, and
            # `--permission-mode`.
            # **THE MODE IS `auto`, owner's ruling 2026-08-19**, and it replaces
            # `acceptEdits`. MEASURED 2026-08-19: `claude --help` lists the six
            # choices `acceptEdits`, `auto`, `bypassPermissions`, `manual`,
            # `dontAsk` and `plan`, so the value is spelled exactly `auto`.
            # **GROK TAKES THE SAME MODEL AND EFFORT FLAGS AS CLAUDE, measured
            # 2026-08-19.** `grok --help` on grok 1.0.5: `-m/--model`, `--effort`, and
            # `--permission-mode`. The probe that day started with `--permission-mode auto`.
            # **CODER GROK STALLS ON TOOL APPROVAL, owner's ruling 2026-08-20.** `auto`
            # still waits. `grok --help` lists `--always-approve` as "Auto-approve all
            # tool executions". The grok kind takes that flag. Claude stays on `auto`.
            if kind == "codex":
                model_args = ["--", "-m", model]
            elif kind == "claude":
                model_args = ["--", "--model", model, "--effort", effort,
                              "--permission-mode", "auto"]
            elif kind == "grok":
                model_args = ["--", "--model", model, "--effort", effort,
                              "--always-approve"]
            else:
                # **PI'S EFFORT DIAL IS `--thinking`, NOT `--effort`, and it was missed
                # the first time this branch was written** (A28). MEASURED 2026-08-21:
                # `pi --help` lists `--thinking <level>` with `off, minimal, low, medium,
                # high, xhigh, max`, a superset of `legal.efforts`. Every string this
                # branch can receive (the empty string, or any of `legal.efforts`) is
                # legal to `pi` unchanged; only the empty string omits the flag, exactly
                # as the claude and grok branches omit nothing they are given but this
                # one head kept carrying "" by choice until the owner asked for one pi
                # head to carry a real value (2026-08-21, `Qwen3.8-27B-oQ4e-mtp`
                # gets `high`).
                model_args = ["--", "--provider", provider or PI_PROVIDER, "--model", model]
                if effort:
                    model_args += ["--thinking", effort]
            # **THE WORKER'S CWD, and it is the TASK'S OWN CHECKOUT when it has one.**
            # `workdir` is the isolated worktree the POD builds for a task; it defaults to
            # the repository root, so every existing caller and every non-POD dispatch is
            # unchanged. Isolation is what stops a whole-tree checker attributing one
            # agent's writes to another, measured three times on 2026-08-19.
            WD = str(workdir) if workdir else str(ROOT)
            prompt_text = (note or "Resume where you left off, then write your report.") \
                          if resume_id else brief.read_text(encoding="utf-8")
            driver = (
                "set -uo pipefail\n"
                f"herdr agent get {hname} >/dev/null 2>&1 || "
                "{ echo \"HERDR resident agent " + hname + " no longer exists; "
                "the next tick will start it again.\"; exit 1; }\n"
                f"herdr agent prompt {hname} \"$(cat {_cat_list(preamble, brief, True)})\"\n"
                f"herdr agent wait {hname} --until working --timeout 120000 || "
                "{ echo \"HERDR resident agent never started working on this prompt\"; "
                "exit 1; }\n"
                "STOPPED=0\n"
                "for i in 1 2 3 4 5 6 7 8 9 10; do\n"
                f"  herdr agent wait {hname} --until idle --until done "
                "&& { STOPPED=1; break; }\n"
                f"  if herdr agent get {hname} 2>/dev/null | grep -q "
                "'\"agent_status\":\"blocked\"'; then\n"
                "    echo \"HERDR agent is BLOCKED: it is waiting for input.\"\n"
                "    break\n"
                "  fi\n"
                f"  herdr agent get {hname} >/dev/null 2>&1 || break\n"
                "  sleep 5\n"
                "done\n"
                f"herdr agent get {hname} >/dev/null 2>&1 || "
                "{ echo \"HERDR resident agent DIED during the run; pane kept\"; "
                "exit 1; }\n"
                f"herdr agent read {hname} --source recent --lines 400 > "
                f"{shlex.quote(str(final))} 2>&1\n"
                "if [ \"$STOPPED\" != 1 ]; then\n"
                "  echo \"HERDR resident agent is STILL ALIVE and the wait never "
                "succeeded; pane kept and NOT closed\"\n"
                "  exit 1\n"
                "fi\n"
                f"echo \"HERDR done; resident agent {hname} kept\"\n"
            ) if reuse_resident else (
                "set -uo pipefail\n"
                # Resolve the agent workspace by LABEL, creating it if the owner
                # closed it. Then split inside it. Never split into the owner's own.
                f"export WS=$(cat {shlex.quote(str(HERDR_WS_FILE))} 2>/dev/null || true)\n"
                # [LJ-1.127] THE PANE LIST IS READ ONCE AND ITS FAILURE IS NOT A
                # REASON TO BUILD A SECOND WORKSPACE. The old form piped
                # `herdr pane list` straight into python: a herdr server that was
                # down, or any JSON shape change, threw inside the one-liner, left
                # BASE empty, and the empty BASE then triggered `workspace create`.
                # That is how a transient error turns into a duplicate workspace,
                # which is the `w8` failure arriving through a second door.
                # Now the two cases are separated: NO PANE IN THIS WORKSPACE means
                # create, and CANNOT READ THE PANE LIST means stop.
                "PANES=$(herdr pane list 2>&1) || "
                "{ echo \"HERDR pane list failed: $PANES\"; exit 1; }\n"
                f"BASE=$(printf '%s' \"$PANES\" | python3 -c \"import json,sys,os;"
                f"ws=os.environ.get('WS','');"
                "d=json.load(sys.stdin);"
                "ps=d['result']['panes'];"
                "m=[p for p in ps if ws and p.get('workspace_id')==ws];"
                # PREFER A PANE THAT IS NOT RUNNING AN AGENT. The old code took
                # m[0], whatever it was. Measured 2026-08-13: the only pane in w7
                # was the ORCHESTRATOR'S OWN claude pane, so every dispatch split
                # it; and once agents exist, m[0] can be a LIVE AGENT'S pane, which
                # a clean finish then closes. Splitting a pane that is closing is a
                # race that kills the new dispatch with `agent_pane_busy`.
                "free=[p['pane_id'] for p in m if not p.get('agent')];"
                "print((free or [p['pane_id'] for p in m] or [''])[0])"
                f"\") || {{ echo \"HERDR pane list unreadable\"; exit 1; }}\n"
                "if [ -z \"$BASE\" ]; then\n"
                f"  BASE=$(herdr workspace create --cwd {shlex.quote(WD)} "
                f"--label {HERDR_WORKSPACE_LABEL} | python3 -c \"import json,sys;"
                "r=json.load(sys.stdin)['result'];"
                f"open({str(HERDR_WS_FILE)!r},'w').write(r['root_pane']['workspace_id']);"
                "print(r['root_pane']['pane_id'])\")\n"
                "fi\n"
                "echo \"HERDR base=$BASE\"\n"
                # LEFT AND RIGHT, not top and bottom: owner's preference,
                # 2026-08-13. An agent's output is long lines of Agda and report
                # prose, so width is worth more than height.
                # SHELL QUOTING, NOT STRING JOINING. `' '.join(envargs)` broke on
                # A14's caliber the day it landed: `GHCRTS=-A64m -I0 -M8g` holds
                # two spaces, so the shell read `-I0` and `-M8g` as two more
                # arguments to `pane split` and the pane got `GHCRTS=-A64m`.
                # `shlex.quote` is the tool, and this file already ruled that in
                # the resume driver below: "Python repr is not shell quoting".
                # **THE LAYOUT RULE HAS ONE HOME AND IT IS NOT THIS STRING.**
                # `scripts/pod/pane-slot.py` picks and creates the pane, and its docstring
                # carries the rule, the two phases and the measurements. It replaced about
                # twenty five lines of shell here plus the two state files
                # `herdr-open-column` and `herdr-rightmost-column`, which could disagree
                # and on 2026-08-19 did: one was empty and the other named a DEAD pane.
                #
                # WHAT WAS WRONG, MEASURED that day in a scratch workspace over six
                # dispatches: columns 145, 73, 36 and 36 wide, panes 62, 31, 16 and 8 rows
                # tall, and each column's BOTTOM pane spanning every column opened after
                # it. The cause is a property of `pane split`, which divides ONE PANE'S
                # rectangle: once a column has been split DOWN it holds no full-height
                # pane, so opening a「new column」off its top pane is a nested split inside
                # the top half. The old rule kept `herdr-rightmost-column` pointing at
                # exactly that pane. **The comment above it had measured this failure and
                # nothing connected the two.**
                #
                # After the repair, twelve dispatches: every column 58 wide, x strictly
                # increasing left to right, and no width changes once the columns are open.
                #
                # IT PRINTS NOTHING WHEN IT CANNOT PLACE A PANE, and the fallback below
                # then splits off BASE, which is ugly and never a lost dispatch.
                f"SLOT={shlex.quote(str(PANE_SLOT))}\n"
                f"PANE=$(python3 \"$SLOT\" --base \"$BASE\" "
                f"--cwd {shlex.quote(WD)} {shlex.join(slotenv)} 2>/dev/null || true)\n"
                "if [ -z \"$PANE\" ]; then\n"
                f"  PANE=$(herdr pane split --pane \"$BASE\" --direction right "
                f"--ratio 0.5 --no-focus --cwd {shlex.quote(WD)} {shlex.join(envargs)} "
                f"| {SPLIT_ID})\n"
                "fi\n"
                "echo \"HERDR pane=$PANE\"\n"
                # A FRESHLY SPLIT PANE IS NOT YET AN INTERACTIVE SHELL. Measured
                # 2026-08-13: `agent start` on a pane created milliseconds earlier
                # fails with agent_pane_busy, "not an available shell". The trial
                # won this race by luck. Retry on a bounded loop; `--timeout` does
                # not cover it, because herdr refuses before it starts waiting.
                # SHELL QUOTING AGAIN, AND THIS ONE WAS AN INJECTION.
                # `' '.join(model_args)` put `model` and `effort` into a shell
                # STRING with no quoting at all. Both come from
                # `dev/pod/heads.toml`, which is a config file the owner edits, so
                # a value holding `;` or a backtick ran as a command in this
                # driver's shell. A config value is not a trusted literal: it is
                # data, and data reaches a shell quoted or not at all.
                "for i in 1 2 3 4 5 6 7 8 9 10; do\n"
                f"  herdr agent start {hname} --kind {kind} --pane \"$PANE\" "
                f"{shlex.join(model_args)} && break\n"
                "  sleep 2\n"
                "done\n"
                # [LJ-1.127] AN AGENT NAME THAT IS ALREADY TAKEN MUST NOT PASS
                # THIS GUARD. `agent start` fails when the name exists, the retry
                # loop then burns twenty seconds, and `agent get` SUCCEEDS,
                # because the OLD agent is what it finds. The driver would then
                # prompt the previous run's agent in the previous run's pane and
                # close the new empty pane at the end. That is a second dispatch
                # silently driving the first. Compare the pane herdr reports
                # against the pane we split.
                # THE EXISTENCE CHECK IS THE RELIABLE ONE AND IT COMES FIRST.
                # The pane comparison below is best effort: `agent get`'s success
                # shape is inferred from `agent start`'s, which the herdrtest1 log
                # shows as result.agent.pane_id, and it has not been measured on a
                # live `get`. So an unreadable shape leaves GOT empty and the
                # comparison is SKIPPED rather than failing every dispatch on a
                # guess.
                f"herdr agent get {hname} >/dev/null 2>&1 || "
                "{ echo \"HERDR agent never started; closing unused pane $PANE\"; "
                "herdr pane close \"$PANE\" >/dev/null 2>&1 || true; exit 1; }\n"
                f"GOT=$(herdr agent get {hname} 2>/dev/null | python3 -c "
                "\"import json,sys;a=(json.load(sys.stdin).get('result') or {})"
                ".get('agent') or {};print(a.get('pane_id',''))\""
                " 2>/dev/null)\n"
                "if [ -n \"$GOT\" ] && [ \"$GOT\" != \"$PANE\" ]; then\n"
                f"  echo \"HERDR agent {hname} already exists in pane $GOT, not in"
                " $PANE. A run under this task code is still alive. Closing the"
                " unused pane $PANE\"\n"
                "  herdr pane close \"$PANE\" >/dev/null 2>&1 || true\n"
                "  exit 1\n"
                "fi\n"
                # TWO PHASE, AND ONE PHASE IS NOT ENOUGH. `--until idle` matches
                # the state the agent is ALREADY in at submission, so a one-phase
                # wait returns at once whether or not the agent ever started.
                # Measured twice on 2026-08-13, once with a bare wait and once
                # with prompt --wait. Wait for `working` FIRST, then for the stop.
                # THE PREAMBLE IS CAT'D AHEAD OF THE BRIEF, and until 2026-08-18 nothing was.
                # MEASURED that day: `INSTRUCTIONS` had ZERO consumers and the three
                # mentions of a slot file in this program were all comments, so every
                # worker was launched with its brief ALONE. It received neither the
                # shared Boundary nor one clause of its own role.
                f"herdr agent prompt {hname} \"$(cat {_cat_list(preamble, brief)})\"\n"
                # NEVER-STARTED-WORKING MUST FREE THE NAME. MEASURED 2026-08-20 on
                # POD-REFILL-20260820-110248: `wait --until working` timed out, the
                # pane was kept for forensics WITH the herdr name still bound, and
                # the next two hourly refills (seq 276, 277) refused
                # `agent_name_taken` for three hours. The log already has the
                # timeout. The pane was a blank splash. Close it. A worker that
                # DIED after writing still keeps its pane, below.
                f"herdr agent wait {hname} --until working --timeout 120000 || "
                "{ echo \"HERDR agent never started working; releasing the name and "
                "closing pane $PANE\"; "
                f"herdr agent rename {hname} --clear >/dev/null 2>&1 || true; "
                "herdr pane close \"$PANE\" >/dev/null 2>&1 || true; exit 1; }\n"
                # THE SECOND WAIT CAN FAIL WITHOUT THE AGENT STOPPING, and an
                # unchecked failure reads as a finished run. Measured 2026-08-13:
                # moving the agent's pane between workspaces made `agent wait`
                # return agent_not_running against the OLD pane while the agent
                # kept working at the new one. The driver then walked past the
                # death guard, because `agent get` correctly found the agent
                # alive, and printed done. So retry the wait while the agent
                # still exists, and only give up when it is really gone.
                # [LJ-1.127] AND THE RETRY MUST RECORD WHETHER IT SUCCEEDED.
                # The loop below used to fall through on exhaustion with no flag
                # set, so ten failed waits against a LIVE agent read exactly like
                # a finished run: the death guard passed (the agent was alive,
                # which is the problem), the driver read a half-written pane, and
                # then CLOSED THE PANE, killing a working agent. That re-created
                # the very defect the retry was added to fix, in a worse form.
                # STOPPED=1 only when the agent really reached a stop state.
                "STOPPED=0\n"
                "for i in 1 2 3 4 5 6 7 8 9 10; do\n"
                # [LJ-1.205] BLOCKED IS NOT A STOP STATE, ruled by the owner
                # 2026-08-14. herdr defines `blocked` as an approval or question
                # UI awaiting input, and the official skill says to inspect and
                # ANSWER it. Counting it here made a pi agent that paused for
                # approval read as FINISHED: the driver read the pane, CLOSED it,
                # and recorded a return, which is irreversible. The consequence
                # was INFERRED from this code and never measured, and the owner
                # ruled the safe side: review it, then close it.
                f"  herdr agent wait {hname} --until idle --until done "
                "&& { STOPPED=1; break; }\n"
                # And say WHICH not-stopped it is, so a pause for approval is
                # never filed as a death. The pane stays open either way.
                #
                # THE `f` PREFIX IS LOAD-BEARING and it was missing until 2026-08-15.
                # Without it `{hname}` reached the shell as four literal characters, so
                # `herdr agent get {hname}` always failed and the blocked branch could
                # never be entered: a paused agent was reported as a death. [LJ-1.303]
                # found it with an `ast` sweep for the only plain literal in the file
                # carrying a placeholder.
                f"  if herdr agent get {hname} 2>/dev/null | grep -q '\"agent_status\":\"blocked\"'; then\n"
                "    echo \"HERDR agent is BLOCKED: it is waiting for input.\"\n"
                "    break\n"
                "  fi\n"
                f"  herdr agent get {hname} >/dev/null 2>&1 || break\n"
                "  sleep 5\n"
                "done\n"
                # A DEAD AGENT LOOKS EXACTLY LIKE A FINISHED ONE HERE. There is no
                # exit code to read: the driver exits 0 either way. Measured
                # 2026-08-13: codex auto-updated at startup, printed "Please
                # restart Codex", exited, and the pane fell back to zsh; the wait
                # then returned and the run read as complete. So prove the agent
                # still exists before declaring the run done.
                f"herdr agent get {hname} >/dev/null 2>&1 || "
                "{ echo \"HERDR agent DIED during the run; pane $PANE kept for forensics\"; exit 1; }\n"
                # [LJ-1.127] A LIVE AGENT THE DRIVER CANNOT WAIT ON IS NOT A
                # FINISHED AGENT. Read the pane for whatever it holds, then leave
                # the pane OPEN and exit non-zero, so `status` shows the return as
                # a death and the agent keeps its terminal.
                f"herdr agent read {hname} --source recent --lines 400 > {shlex.quote(str(final))} 2>&1\n"
                "if [ \"$STOPPED\" != 1 ]; then\n"
                "  echo \"HERDR agent is STILL ALIVE and the wait never succeeded;"
                " pane $PANE kept and NOT closed\"\n"
                "  exit 1\n"
                "fi\n"
                # CLOSE THE PANE ON A CLEAN FINISH ONLY. Every `exit 1` above
                # leaves the pane open on purpose: a dead agent's terminal is the
                # only evidence of how it died, and this session read three deaths
                # out of a pane that was still there. A finished agent's pane holds
                # nothing the final-message file does not, so it goes.
                #
                # A RESIDENT AGENT IS NEVER CLOSED, and closing it is the ONLY thing
                # that ends one. MEASURED 2026-08-18 on a throwaway `claude` head:
                # after its turn the agent reports `agent_status: done`, and a SECOND
                # `herdr agent prompt` was accepted and answered on the SAME
                # `agent_session` id. `done` is a label on a live agent, not a death.
                # The maintainer is resident under the owner's ruling of 2026-08-18,
                # so `pod.py` prompts one long-lived session instead of launching a
                # fresh batch, and the owner can attach to it at any time.
                + ("echo \"HERDR done pane=$PANE kept; the agent is RESIDENT\"\n"
                   if resident else
                   "herdr pane close \"$PANE\" >/dev/null 2>&1\n"
                   "echo \"HERDR done pane=$PANE closed\"\n")
            ) if not resume_id else (
                # [LJ-1.127] THE RESUME DRIVER CARRIED THREE DEFECTS THE FRESH
                # DRIVER HAD ALREADY PAID FOR, because it was written as a
                # two-line afterthought and never run against a live agent.
                #
                # 1. ONE-PHASE WAIT. `agent prompt --wait --until idle` is the
                #    exact form measured on 2026-08-13 to return AT ONCE, because
                #    `idle` is the state the agent is already in at submission.
                #    The driver would then read a pane holding nothing but the
                #    prompt and exit 0, and the run would read as complete.
                # 2. NO EXISTENCE CHECK. If the agent is gone, `agent prompt`
                #    fails, `agent read` writes the error text into the final
                #    message file, and the driver still exits 0. Measured: both
                #    herdrtest1 resume attempts failed with `agent_not_found` and
                #    both were recorded as returns.
                # 3. PYTHON `repr` IS NOT SHELL QUOTING. A note holding an
                #    apostrophe produced a double-quoted shell word, so `$` and a
                #    backtick expanded; a note holding both quote characters
                #    produced a shell SYNTAX ERROR. shlex.quote is the right tool
                #    and it is now used for every interpolated value.
                "set -uo pipefail\n"
                f"herdr agent get {hname} >/dev/null 2>&1 || "
                "{ echo \"HERDR agent " + hname + " no longer exists; a herdr "
                "resume works only while the pane is alive. Re-dispatch.\"; "
                "exit 1; }\n"
                f"herdr agent prompt {hname} {shlex.quote(prompt_text)}\n"
                f"herdr agent wait {hname} --until working --timeout 120000 || "
                "{ echo \"HERDR resumed agent never started working\"; exit 1; }\n"
                "STOPPED=0\n"
                "for i in 1 2 3 4 5 6 7 8 9 10; do\n"
                f"  herdr agent wait {hname} --until idle --until done "
                "--until blocked && { STOPPED=1; break; }\n"
                f"  herdr agent get {hname} >/dev/null 2>&1 || break\n"
                "  sleep 5\n"
                "done\n"
                f"herdr agent read {hname} --source recent --lines 400 > {shlex.quote(str(final))} 2>&1\n"
                "[ \"$STOPPED\" = 1 ] || { echo \"HERDR resumed agent never "
                "reached a stop state\"; exit 1; }\n"
                f"echo \"HERDR resume done for {hname}\"\n"
            )
            cmd = ["bash", "-c", driver]
        elif HARNESS == "pi":
            # THE PI HARNESS IS NOT A RENAME. Verified against pi 0.84.1 and
            # https://pi.dev/docs/latest on 2026-08-13, before anything was dispatched:
            #
            #   codex exec           ->  pi -p          (subcommand becomes a flag)
            #   -m MODEL             ->  --provider deepseek --model MODEL
            #   -C DIR               ->  NONE. pi takes the cwd it is launched in, and
            #                            launch() already sets cwd=ROOT, so this is covered.
            #   -o FILE              ->  NONE. pi_stream.py writes the final file from the
            #                            LAST `message_end` whose role is `assistant`.
            #   -s read-only|workspace-write
            #                        ->  NONE, AND THERE IS NO EQUIVALENT. The docs say it
            #                            outright: "Pi does not include a built-in sandbox.
            #                            Built-in tools can read files, write files, edit
            #                            files, and run shell commands with the permissions
            #                            of the pi process." So a pi agent can write ANYWHERE
            #                            this user can. The brief's SCOPE section is the only
            #                            restriction left, and `sandbox` below is recorded in
            #                            the registry for the audit trail, not enforced.
            #
            # STREAMING AND RESUME, both wired 2026-08-13 by [LJ-1.126].
            #
            # STREAMING. `pi -p` alone prints nothing until it exits, so the log of a
            # pi dispatch stayed empty for the whole run: [LJ-1.121]'s log was 2071
            # bytes and never changed size. `pi --mode json` streams one JSON object
            # per event, and pi_stream.py renders those into readable lines, so the
            # log now grows during the run. The raw events go to a sidecar .jsonl.
            #
            # RESUME. pi's session id is the `id` field of the FIRST --mode json
            # event, not a "session id:" line. pi_stream.py re-emits it in the codex
            # shape, so SESSION_RE finds it and BOTH scrapes, the one in launch()
            # below and the one in cmd_resume, work for pi with no second pattern.
            #
            # `--session <id>` is the resume flag. `--resume` is a boolean that opens
            # an INTERACTIVE picker and is useless here; `--continue` takes no id.
            # Measured from `pi --help` and from
            # .../pi-coding-agent/dist/cli/args.js on 2026-08-13.
            prompt = (note or "Resume where you left off, then write your report.") \
                     if resume_id else brief.read_text(encoding="utf-8")
            pi_cmd = ["pi", "--mode", "json", "-p",
                      "--provider", provider or PI_PROVIDER, "--model", model]
            if resume_id:
                pi_cmd += ["--session", resume_id]
            pi_cmd.append(prompt)
            cmd = [sys.executable, str(PI_STREAM), "--events", str(events),
                   "--final", str(final), "--"] + pi_cmd
        elif resume_id:
            # FM18: the -resume suffix is applied in exactly one place now.
            # FLAG ORDER IS LOAD-BEARING (measured 2026-08-05): `codex exec resume` accepts
            # only -m, -c, -i and the feature flags. Putting -s, -C or -o AFTER `resume`
            # fails the parse with "unexpected argument '-s'" and the agent never starts.
            prompt = note or "Resume where you left off, then write your report."
            cmd = ["codex", "exec", "-s", sandbox, "-C", str(ROOT), "-m", model,
                   "-o", str(final), "resume", resume_id, prompt]
        else:
            cmd = ["codex", "exec", "-s", sandbox, "-C", str(ROOT), "-m", model,
                   "-o", str(final), brief.read_text(encoding="utf-8")]

        env = dict(os.environ)
        if agda:
            # The direct-exec paths inherit this process's environment, so the
            # caliber goes on it. Same tier, same string, one source: A14.
            env["GHCRTS"] = agda_heap(tier)

        # start_new_session=True calls setsid(2) in the child, so the agent leaves this
        # process group. Killing whatever launched it can no longer take it down. This is
        # the fix for the 2026-08-05 double kill; nohup does NOT do this.
        try:
            with open(log, "wb") as fh:
                # stdin=DEVNULL is load-bearing (measured 2026-08-05): codex reads stdin
                # for extra context even when the prompt is on the command line, and a
                # backgrounded launch inherits a pipe that never closes, so it BLOCKS
                # FOREVER. T84 sat 13 minutes with a 0-byte log saying "Reading additional
                # input from stdin..." and would have sat there all night. DEVNULL gives it
                # immediate EOF and it proceeds with the argv prompt.
                proc = subprocess.Popen(cmd, stdout=fh, stderr=subprocess.STDOUT,
                                        stdin=subprocess.DEVNULL,
                                        cwd=WD, env=env, start_new_session=True)
        except OSError as exc:
            # FM13: a missing codex binary used to be a raw traceback.
            print(f"dispatch: could not launch: {exc}", file=sys.stderr)
            return 1

        reg = load()
        reg.setdefault("dispatches", {})[task] = {
            "pid": proc.pid, "proc_start": proc_start(proc.pid), "brief": str(brief),
            "agda": agda, "sandbox": sandbox, "model": model, "log": str(log),
            # POD EDIT 3 of 6, part 2 of 3 (design section 6.2). The effort is
            # RECORDED beside the model for the same reason the harness is
            # recorded below: a resume has no `--effort` flag, so without this
            # record every resume would drop to the empty string and the pane
            # would run at the CLI's own default. AD26 also needs the value that
            # actually ran, not the value `heads.toml` holds today.
            "effort": effort,
            # A14: A RECORD CARRIES ITS TIER. Two measurements are compared only
            # inside one tier, because the caliber differs between them, and the
            # mixed-tier heap sum above can only be taken when every live holder
            # says which budget it took.
            "tier": tier, "agda_heap": agda_heap(tier) if agda else "",
            "final": str(final), "session": "", "resumed_from": resume_id,
            "started": time.strftime("%Y-%m-%d %H:%M:%S"),
            # THE HARNESS IS RECORDED BECAUSE RESUME HAD NO WAY TO KNOW IT.
            # `main()` sets the global from `--harness`, and the `resume`
            # subcommand has no such flag, so every resume ran on the codex path
            # whatever launched the original. A pi session id handed to `codex
            # exec resume` cannot work. Found and fixed 2026-08-13 by [LJ-1.126].
            "harness": HARNESS,
            "events": str(events) if HARNESS == "pi" else "",
        }
        save(reg)

    session = ""
    dead_early = False
    for _ in range(60):
        time.sleep(0.5)
        if log.exists() and (m := SESSION_RE.search(log.read_text(errors="ignore"))):
            session = m.group(1)
            break
        if proc.poll() is not None:
            dead_early = True
            break

    with registry_lock():
        reg = load()
        if task in reg.get("dispatches", {}):
            reg["dispatches"][task]["session"] = session
            save(reg)

    # FM13: never report a launch as successful when the process is already gone. That is
    # the exact shape of failure mode 1 and it used to print "away" and exit 0.
    if dead_early and proc.returncode != 0:
        print(f"dispatch: {task} EXITED IMMEDIATELY (rc {proc.returncode}). This is the "
              f"silent-death shape: read {log} for the reason.", file=sys.stderr)
        return 1
    print(f"dispatch: {task} away, pid {proc.pid}, "
          f"session {session or '(not printed yet; resume rescans the log)'}")
    print(f"          log {log}")
    print(f"          ARM THE NOTIFIER: {CLI} wait, as a harness-tracked background "
          f"job. Without it this return is silent.")
    return 0


# --------------------------------------------------------------------------- commands


def resolve_brief(arg: str) -> Path:
    p = Path(arg)
    return p if p.is_absolute() else ROOT / p


def announce(done: dict) -> None:
    """Append every reported return to the durable log.

    [L3.32-T119] found this was written in exactly ONE of the two report paths.
    `run --wait`, which SKILL.md recommends as the whole notification path,
    marked returns `reported` and never wrote a line, so a lost report was
    unrecoverable through the very route the fix for that failure recommends.
    The registry still carries the forensics: T97 and T98 sit `reported = True`
    with final messages on disk while returns.log has no line for either.

    SECOND MEASURED DEFECT, 2026-08-12: the body of this function was
    `announce(done)`. It called itself, so every `run --wait` return died in a
    RecursionError after the registry had already been marked `reported`. The
    docstring above described a fix that was never written, and it read as
    though it had been. That is why `status` reported ten returns never
    announced across LJ-1.47 to LJ-1.55: all ten were audited, but nothing
    durable recorded them, so a genuinely lost return would have been
    invisible. The body now matches the writer at the foot of `_report`.
    """
    stamp = time.strftime("%Y-%m-%d %H:%M:%S")
    try:
        LOGS.mkdir(parents=True, exist_ok=True)
        with open(STATE / "returns.log", "a") as rf:
            for tname in sorted(done):
                d = done[tname]
                final = Path(d.get("final", ""))
                ok = "clean" if final_is_clean(final) else "NO-FINAL-MESSAGE"
                rf.write(f"{stamp}  {tname}  {ok}  {d.get('log','')}\n")
    except OSError:
        pass


def _wait_for(task: str) -> int:
    """Block until one named agent exits, then report it. This is what makes `--wait` the
    whole notification path: the harness tracks THIS command, so its exit is the signal and
    nobody has to remember to arm anything."""
    start = time.time()
    while True:
        time.sleep(10)
        reg = load()
        d = reg.get("dispatches", {}).get(task)
        if d is None or rec_alive(d):
            continue
        with registry_lock():
            reg = load()
            if task in reg.get("dispatches", {}):
                reg["dispatches"][task]["reported"] = True
                save(reg)
                announce({task: reg['dispatches'][task]})
        final = Path(d.get("final", ""))
        print(f"dispatch: {task} RETURNED after {int(time.time() - start)}s")
        if final_is_clean(final):
            print(f"  finished cleanly, final message {final}")
        else:
            print(f"  NO FINAL MESSAGE: killed or ran out of budget. Its work may still be "
                  f"on disk. Consider `{CLI} resume {task}`.")
        print(f"  log {d.get('log')}")
        others = [t for t in running(reg) if t != task]
        if others:
            print(f"dispatch: still running: {', '.join(sorted(others))}")
        return 0


def cmd_run(a) -> int:
    brief = resolve_brief(a.brief)
    if (why := check_model(a.model, a.allow_model)):
        print(f"dispatch: REFUSED. {why}", file=sys.stderr)
        return 1
    if defects := launch_defects(brief, a.sandbox, a.agda, case_from_args(a)):
        for d in defects:
            print(f"dispatch: REFUSED: {d}", file=sys.stderr)
        return 1
    # POD EDIT 3 of 6, part 3 of 3, caller one (design section 6.2).
    rc = launch(a.task, brief, a.agda, a.sandbox, a.model, allow_model=a.allow_model,
                case=case_from_args(a), effort=getattr(a, "effort", ""),
                tier=getattr(a, "tier", AGDA_TIER_DEFAULT))
    if rc == 0 and getattr(a, "wait", False):
        return _wait_for(a.task)
    return rc


def cmd_queue(a) -> int:
    """Wait for a free Agda slot in a DETACHED process, then run. Safe to kill: the agent
    it eventually launches is setsid'd, so it survives the waiter's death."""
    brief = resolve_brief(a.brief)
    if (why := check_model(a.model, a.allow_model)):
        print(f"dispatch: REFUSED. {why}", file=sys.stderr)
        return 1
    if not SAFE_TASK.match(a.task):
        print(f"dispatch: refused: task name {a.task!r} must match {SAFE_TASK.pattern}",
              file=sys.stderr)
        return 1
    # FM9: refuse a colliding name HERE, not later inside a detached waiter whose log the
    # orchestrator may never read.
    if a.task in running(load()):
        print(f"dispatch: {a.task} is already running; queueing it would double-launch",
              file=sys.stderr)
        return 1
    if defects := launch_defects(brief, a.sandbox, a.agda, case_from_args(a)):
        for d in defects:
            print(f"dispatch: REFUSED: {d}", file=sys.stderr)
        return 1

    resume_id, note = None, None
    if a.resume_of:
        prior = load().get("dispatches", {}).get(a.resume_of)
        prior_session = (prior or {}).get("session", "")
        if prior and not prior_session and (prior.get("harness") or "codex") == "herdr":
            # Same loosening as cmd_resume, one command over. Owner's ruling,
            # 2026-08-13.
            prior_session = "herdr-by-name"
        if not prior or not prior_session:
            print(f"dispatch: no recorded session for {a.resume_of}", file=sys.stderr)
            return 1
        resume_id, note = prior_session, a.note
        # SAME DEFECT AS cmd_resume, one command over. A queued resume built its
        # command from `--harness`, which defaults to herdr, so a pi agent's
        # session id could be handed to a herdr pane. The record wins, because
        # only the launching harness can read its own session id.
        global HARNESS
        prior_h = prior.get("harness") or "codex"
        if prior_h != HARNESS:
            print(f"dispatch: {a.resume_of} ran on the {prior_h} harness, so this "
                  f"resume uses {prior_h} and not {HARNESS}")
            HARNESS = prior_h

    here = str(Path(__file__).resolve().parent)
    # THE WAITER IMPORTS THIS FILE BY ITS OWN NAME, AND IT USED TO IMPORT A NAME
    # THAT NO LONGER EXISTS. This module was `dispatch.py` in the skill directory
    # and it is `launcher.py` under `scripts/pod/`, so the generated line
    # `import dispatch as D` raised ModuleNotFoundError in a DETACHED process
    # whose only trace is a log nobody reads. Every queued dispatch was dead on
    # arrival. Reading the name off `__file__` makes the next rename harmless.
    me = Path(__file__).resolve().stem
    script = (
        f"import sys, time\n"
        f"sys.path.insert(0, {here!r})\n"
        f"import {me} as D\n"
        # THE WAITER IS A FRESH PROCESS, so D.HARNESS is the module default and
        # main()'s `global HARNESS` never ran here. Measured 2026-08-13: LJ-1.121 was
        # queued with --harness pi and launched on codex, and only the agent log's
        # "OpenAI Codex v0.146.0" header showed it. Set it explicitly.
        f"D.HARNESS = {HARNESS!r}\n"
        # [L3.32-T247]: the queue waited on Agda SLOTS only, so a job blocked on
        # write TERRITORY launched at once and died on the launch-time refusal
        # (`QUEUE RESULT rc=1`). Territory is the commoner reason to queue: the
        # slots gate cost, the territory gates correctness (C-25). Wait on both.
        f"while True:\n"
        f"    with D.registry_lock():\n"
        f"        reg = D.load()\n"
        # A14: the ceiling is the TIER's, and the heap sum is checked with it,
        # because a queue that waits on the slot count alone launches into a
        # mixed-tier overshoot and dies on `launch()`'s own refusal.
        f"        free = ((not {a.agda!r}) or "
        f"(len(D.agda_holders(reg)) < D.agda_slots({a.tier!r}) "
        f"and not D.agda_heap_sum_over(reg, {a.tier!r})))\n"
        f"    clash = D.territory_in_flight(D.Path({str(brief)!r}), {a.task!r})\n"
        f"    if free and not clash: break\n"
        f"    time.sleep(30)\n"
        f"rc = D.launch({a.task!r}, D.Path({str(brief)!r}), {a.agda!r}, {a.sandbox!r}, "
        f"{a.model!r}, resume_id={resume_id!r}, note={note!r}, allow_model={a.allow_model!r}, "
        # THE EFFORT AND THE TIER MUST CROSS THE PROCESS BOUNDARY TOO. The
        # generated call carried neither, so a queued claude dispatch reached
        # `launch()` with `effort=""`, which the refusal above now catches; before
        # that refusal it reached the pane as `--effort ""`.
        f"effort={getattr(a, 'effort', '')!r}, tier={a.tier!r}, "
        # The QUEUE fires LATER, so the SWITCH may have moved between this command and the
        # launch. The case is pinned here and switch_defects re-reads the SWITCH at fire time,
        # which is the behaviour we want: a queued default-case dispatch that would land in
        # a peak window is refused AT THE LAUNCH, not waved through because it was queued
        # off-peak. FM8 already re-validates the brief at fire time for the same reason.
        f"case={case_from_args(a)!r})\n"
        f"print('QUEUE RESULT rc=%d' % rc)\n"
    )
    LOGS.mkdir(parents=True, exist_ok=True)
    waiter_log = LOGS / f"{a.task}-queue-{time.strftime('%Y%m%d-%H%M%S')}.log"
    with open(waiter_log, "wb") as fh:
        p = subprocess.Popen([sys.executable, "-c", script], stdout=fh,
                             stderr=subprocess.STDOUT, stdin=subprocess.DEVNULL,
                             cwd=ROOT, start_new_session=True)
    print(f"dispatch: {a.task} queued behind the Agda slots (waiter pid {p.pid}).")
    print(f"          The waiter is detached and the agent it launches will be too, so "
          f"stopping either one cannot take the other down.")
    print(f"          waiter log {waiter_log}")
    print(f"          ARM THE NOTIFIER: {CLI} wait, as a harness-tracked background "
          f"job, or pass --wait next time and skip this step.")
    return 0


def brief_in_flight(brief: Path) -> str | None:
    """The task name of a LIVE agent already holding this brief, if any.

    [L3.32-T119] found the collision check keyed on TASK NAME, which a resume
    walks straight past: `resume T` launches under `T-resume`, so a queued
    `T` waiting for a slot still sees no live `T` and launches. Two agents,
    one brief, the same write territory, and nothing anywhere noticed. The
    registry already carries T53-resume and T81-resume, so the path is in use.

    Keying on the brief closes it, and the brief is what the write territory
    actually belongs to.
    """
    want = str(brief.resolve())
    for name, d in running(load()).items():
        if d.get("brief") and str(Path(d["brief"]).resolve()) == want:
            return name
    return None


def write_paths(brief: Path) -> set[str]:
    """The repository paths a brief ORDERS its agent to write.

    Shared with the rule-bundle derivation, which needs the same reading: the
    lines that GRANT a write, with the lines that FORBID one dropped first. A
    scope saying "Never src/Everything.lagda.md" grants nothing, and counting
    it as territory would deadlock every build against every other build.
    """
    try:
        text = brief.read_text(encoding="utf-8")
    except (OSError, UnicodeDecodeError):
        # UnicodeDecodeError is a ValueError, not an OSError, so the old catch
        # let a non-UTF-8 brief raise out of a territory check.
        return set()
    m = re.search(r"##\s*SCOPE\s*\(write\)(.*?)(?=\n##\s|\Z)", text, re.S | re.I)
    if not m:
        return set()
    # [L3.32-T249]: the filter ran per LINE, and a prohibition that WRAPS puts
    # "Never" on one line and its paths on the next, so the paths survived and
    # the checker refused a probe over a file it was forbidden to touch. Join
    # wrapped lines into logical units first: a new unit starts at a blank
    # line, a bullet, or a heading, and everything else continues the previous.
    units, cur = [], ""
    for ln in m.group(1).split("\n"):
        if not ln.strip() or re.match(r"\s*([-*+]|\d+\.|#)", ln):
            if cur: units.append(cur)
            cur = ln
        else:
            cur = (cur + " " + ln).strip() if cur else ln
    if cur: units.append(cur)
    kept = [u for u in units
            if not re.search(r"\bnever\b|\bread-only\b|\bdo not (write|touch)\b",
                             u, re.I)]
    body = "\n".join(kept)
    # `_build` is included so the grant is reported honestly. The CLASH filter
    # drops reports, not this parser: every brief writes one, so treating a
    # report as contested territory would refuse every parallel dispatch.
    return set(re.findall(r"`?((?:src|dev|scripts|_build)/[\w./-]+"
                          r"\.(?:lagda\.md|agda|md|toml|py))`?", body))


def territory_in_flight(brief: Path, task: str) -> tuple[str, set[str]] | None:
    """A LIVE lane whose write scope intersects this brief's, and the overlap.

    [L3.32-T226] found the 2026-08-08 hole: `brief_in_flight` keys on the brief
    PATH, so two DIFFERENT briefs naming the same master walk straight past it.
    Two lanes were sent with "the shared home you propose" in their write
    scope, both proposed `src/L/LevelKit.lagda.md`, and both wrote it. Nothing
    was lost, because they happened to append to different regions, but that is
    luck and not a mechanism. The territory is the file, so the file is what
    must be unique across live lanes.
    """
    mine = write_paths(brief)
    open_mine = open_grant(brief)
    if not mine and not open_mine:
        return None
    for name, d in running(load()).items():
        if name == task or not d.get("brief"):
            continue
        ob = Path(d["brief"])
        # A report under _build/ is per-task by construction and never contested.
        overlap = {p for p in (mine & write_paths(ob)) if not p.startswith("_build/")}
        # THE CASE THAT ACTUALLY HAPPENED. Neither T225 nor T226 named LevelKit:
        # both said "the shared home you propose", and both proposed the same
        # home. An unbounded grant intersects every other unbounded grant, so
        # two of them live at once is the refusal, with no path to compare.
        if open_mine and open_grant(ob):
            overlap = overlap | {"an unnamed `shared home you propose` (both briefs)"}
        if overlap:
            return name, overlap
    return None


def open_grant(brief: Path) -> bool:
    """True when a brief's write scope grants a file it does not name.

    A phrase like "the shared home you propose" is a write order whose target
    the brief cannot state, so no path check can compare it against a sibling.
    It is legal, and often right: the agent knows where the content belongs
    better than the orchestrator does. It is only unsafe in PARALLEL.
    """
    try:
        text = brief.read_text(encoding="utf-8")
    except OSError:
        return False
    m = re.search(r"##\s*SCOPE\s*\(write\)(.*?)(?=\n##\s|\Z)", text, re.S | re.I)
    if not m:
        return False
    return bool(re.search(r"\b(home|module|file|master|chapter)\b[^.\n]{0,40}"
                          r"\byou\s+(propose|choose|pick|name)\b", m.group(1), re.I))


def cmd_resume(a) -> int:
    reg = load()
    d = reg.get("dispatches", {}).get(a.task)
    if not d:
        print(f"dispatch: no record of {a.task}", file=sys.stderr)
        return 1
    if rec_alive(d):
        print(f"dispatch: {a.task} is still alive (pid {d.get('pid')}); do not resume a "
              f"running agent", file=sys.stderr)
        return 1
    session = d.get("session", "")
    if not session:
        # FM11: the scrape is bounded, so rescan the log before refusing. The id was often
        # sitting right there.
        log = Path(d.get("log", ""))
        if log.exists() and (m := SESSION_RE.search(log.read_text(errors="ignore"))):
            session = m.group(1)
            print(f"dispatch: session id recovered from the log: {session}")
    if not session and (d.get("harness") or "codex") == "herdr":
        # HERDR RESUMES BY NAME, NOT BY SESSION ID. Owner's ruling, 2026-08-13:
        # loosen this, because herdr's own state management is better and a
        # resume is unlikely to be needed at all. The herdr branch in launch()
        # only re-prompts the agent by its herdr name, which the task code maps
        # to, so it never reads a session id. The sentinel below exists only to
        # pick that branch; nothing consumes its value.
        #
        # It works ONLY while the agent is still alive in its pane. A herdr
        # resume of a DEAD agent fails at `agent prompt` with agent_not_found,
        # which is the honest outcome: the pane is gone, so there is nothing to
        # resume and the work must be re-dispatched.
        session = "herdr-by-name"
        print(f"dispatch: {a.task} ran on herdr, which resumes by agent name; "
              f"this only works while its pane is alive")
    if not session:
        print(f"dispatch: {a.task} has no session id in its record or its log; it cannot "
              f"be resumed, only re-dispatched", file=sys.stderr)
        return 1
    # RESUME MUST RUN ON THE HARNESS THAT STARTED THE AGENT. `main()` sets the
    # global from `--harness`, which the `resume` subcommand does not have, so
    # the global was always "codex" here. A pi session id given to `codex exec
    # resume` starts a codex agent on an id codex never issued.
    #
    # The fallback is "codex" and not the module default, because a record
    # written before 2026-08-13 carries no `harness` field and every one of
    # those WAS launched on the codex path. Changing the fallback would
    # re-route the whole history. Measured and fixed 2026-08-13 by [LJ-1.126].
    global HARNESS
    HARNESS = d.get("harness") or "codex"
    print(f"dispatch: resuming on the {HARNESS} harness, as recorded at launch")
    # POD EDIT 3 of 6, part 3 of 3, caller two (design section 6.2). The effort
    # is recovered from the RECORD, exactly as the harness is recovered above.
    # A14: THE TIER COMES FROM THE RECORD TOO, for the same reason the effort
    # does. A resume that silently changed tier would change the caliber, and a
    # measurement taken across a caliber change is not a measurement.
    return launch(f"{a.task}-resume", Path(d.get("brief", "")), d.get("agda", False),
                  d.get("sandbox", "workspace-write"), d.get("model", DEFAULT_MODEL),
                  resume_id=session, note=a.note, allow_model=a.allow_model,
                  effort=d.get("effort", ""),
                  tier=d.get("tier") or AGDA_TIER_DEFAULT)


# ---------------------------------------------------------------------------
# STALL DETECTION, added 2026-08-07 after [L3.32-T131].
#
# WHAT HAPPENED. T131 ran two hours, grew a 17 MB log, and left its report at
# 42 skeleton lines. It was not slow: it had written the same scratch
# diagnostic file 1,622 times, looping on one type puzzle. The orchestrator
# found it only by hand-counting occurrences in the log, which is not a check
# anybody runs on a healthy day, and the loop was invisible to `status`
# because the log WAS growing and the process WAS alive.
#
# WHAT THIS CHECKS. Two independent signals, because either alone lies:
#   1. The deliverable is not growing while the log is. C-22 requires the
#      report be filled as answers land, so a live agent whose report has not
#      changed in a long time is either stuck or violating C-22, and both are
#      worth interrupting for.
#   2. The log repeats one file-create diff many times over. A run that
#      re-creates the same scratch file dozens of times is not exploring.
#
# It reports; it never kills. A stalled agent may still be recoverable with
# `resume --note`, and T131's 802-line probe was: it held both halves of what
# it had been sent for, unreported.
# ---------------------------------------------------------------------------

STALL_QUIET_SECONDS = 1800     # deliverable untouched this long, while live
STALL_REPEAT_DIFFS = 40        # same file created this many times in one log


def stall_note(task: str, d: dict, log: Path, now: float) -> str:
    """A warning line for a live agent that looks stuck. Never fatal."""
    bits = []
    report = d.get("report") or ""
    if not report:
        # Derive it the way the briefs name it, so this works for old records.
        # [LJ-1.127]: the retired `L3.32` shape was the ONLY one tried, so the
        # whole live `LJ` series derived nothing and the quiet-deliverable half
        # of this detector was dead for every task since 2026-08-09. Try the
        # live shape first.
        for cand in (ROOT / "_build" / f"{task.lower()}-report.md",
                     ROOT / "_build" / f"l3.32-{task.lower()}-report.md"):
            if cand.exists():
                report = str(cand)
                break
    if report and Path(report).exists() and log.exists():
        quiet = now - Path(report).stat().st_mtime
        if quiet > STALL_QUIET_SECONDS and log.stat().st_mtime > Path(report).stat().st_mtime:
            bits.append(f"deliverable untouched {int(quiet // 60)}m while the log moves")
    try:
        if log.exists() and log.stat().st_size > 2_000_000:
            blob = log.read_bytes().decode("utf-8", "replace")
            # Count creations of files OTHER than the agent's own deliverable.
            # [L3.32-T225] 2026-08-08: all 76 of a flagged lane's file-create
            # diffs were `_build/l3.32-t225-report.md`, which is C-22 working
            # exactly as the rulebook orders: create the deliverable early and
            # rewrite it as answers land. A stall warning that fires on
            # COMPLIANCE teaches the orchestrator to ignore the warning, and
            # then a real stall goes unread. The report is excluded.
            # [LJ-1.3] 2026-08-10: the SAME defect, one exclusion short. T225
            # excluded the report and stopped there, so a BUILD agent
            # rewriting its chapter incrementally still trips the alarm: 111
            # creations of src/L/Hull.lagda.md, a file at 263 of its target
            # 340-540 lines and visibly growing. C-22 orders exactly that for
            # the chapter as well as the report. So exclude every path the
            # brief's own SCOPE (write) names, which is the definition of "the
            # deliverable" this heuristic was reaching for.
            own_names = {Path(report).name if report
                         else f"l3.32-{task.lower()}-report.md"}
            own_dirs: set[str] = set()
            brief = d.get("brief")
            if brief and Path(brief).exists():
                try:
                    btext = Path(brief).read_text(encoding="utf-8")
                    m = re.search(r"^#*\s*SCOPE\s*\(write\)(.*?)(?=^#|\Z)",
                                  btext, re.S | re.M | re.I)
                    if m:
                        own_names |= {Path(q).name for q in
                                      re.findall(r"`([\w./-]+\.(?:lagda\.md|agda|md))`",
                                                 m.group(1))}
                        # A BRIEF MAY AUTHORIZE A FILE BY DIRECTORY, and the
                        # name regex above cannot see that. [LJ-1.6] said
                        # "New masters under `src/L/`", created exactly the two
                        # masters it was allowed, and every rewrite of a
                        # 708-line file counted as a create diff "outside the
                        # deliverable". The alarm then cried wolf on precisely
                        # the task class most likely to create files, which is
                        # worse than silence: a false stall invites the
                        # orchestrator to kill or resume a healthy agent.
                        own_dirs |= {q.rstrip("/") for q in
                                     re.findall(r"`([\w./-]+/)`", m.group(1))}
                except OSError:
                    pass
            # Only a header IMMEDIATELY followed by `new file mode` is a
            # creation. Matching the header alone counts every ordinary edit
            # and the number stops meaning anything.
            creates = re.findall(r"^diff --git a/(\S+) b/\S+\nnew file mode",
                                 blob, re.M)
            def owned(c: str) -> bool:
                if Path(c).name in own_names:
                    return True
                return any(c == d or c.startswith(d + "/") for d in own_dirs)

            n = sum(1 for c in creates if not owned(c))
            if n >= STALL_REPEAT_DIFFS:
                bits.append(f"{n} file-create diffs outside the deliverable, "
                            f"likely re-writing one scratch file")
    except OSError:
        pass
    return ("  <-- POSSIBLE STALL: " + "; ".join(bits) +
            ". Check the log tail, then `resume --note` with what survived") if bits else ""



# POD EDIT 6 of 6, row 15, first half (design section 6.2).
# `unregistered_returns()` IS DELETED HERE, whole, with its `cmd_status` banner
# below. It read the `dev/PLAN.md` task index and reported every task whose row
# still said DISPATCHED or QUEUED after the waiter announced its return.
#
# WHY IT GOES. `dev/PLAN.md` section 11 is the goal and dispatch index, and the
# POD replaces it with dev/pod/queue.toml and the transition log
# (design section 5.3.1). A status word that nothing writes cannot be read.
#
# ITS MEASUREMENT IS KEPT. [L3.32-T208], 2026-08-08: T208 and T209 returned in
# the SAME announcement, at the same second. T209 was audited and registered;
# T208 was dropped, and its row sat on DISPATCHED for a day with a complete
# report on disk. The owner found it, not the tooling. THE POD CANNOT REPEAT
# IT: a return is a state transition the program itself writes, so there is no
# hand-registration step to forget.


def cmd_status(a) -> int:
    reg = load()
    live = running(reg)
    holders = agda_holders(reg)
    # A14: THE CENSUS PRINTS THE HEAP SUM, not only the count. Two holders can
    # sit inside every slot ceiling and still budget 24 GB, and the count alone
    # hides that. Each holder is named with the tier it took.
    heap_now = sum(agda_heap_gb(d.get("tier") or AGDA_TIER_DEFAULT)
                   for d in holders.values())
    print(f"Agda slots: {len(holders)}/{agda_slots(AGDA_TIER_DEFAULT)} held in the "
          f"{AGDA_TIER_DEFAULT} tier, {heap_now}/{AGDA_MAX_HEAP_SUM_GB} GB of "
          f"worst-case heap budgeted" +
          (" by " + ", ".join(f"{t} ({d.get('tier') or AGDA_TIER_DEFAULT})"
                              for t, d in sorted(holders.items())) if holders else ""))
    print(f"agents live: {len(live)}")
    now = time.time()
    items = sorted(reg.get("dispatches", {}).items())
    for t, d in items:
        is_live = rec_alive(d)
        if not is_live and not a.all and not final_is_clean(d.get("final", "")):
            pass  # still shown: an exited agent with no final message is the signal
        state = "RUNNING" if is_live else "exited "
        log = Path(d.get("log", ""))
        age = ""
        if log.exists():
            age = (f"  log {log.stat().st_size // 1024}k, "
                   f"last write {int(now - log.stat().st_mtime)}s ago")
        note = ""
        if not is_live and not final_is_clean(d.get("final", "")):
            note = "  <-- EXITED WITH NO FINAL MESSAGE: killed or exhausted, consider `resume`"
        elif is_live:
            note = stall_note(t, d, log, now)
        print(f"  {state} {t:<16} pid {str(d.get('pid')):<7} "
              f"agda={str(d.get('agda')):<5}{age}{note}")
    if hist := reg.get("history"):
        print(f"  ({len(hist)} superseded record(s) kept in history; their session ids "
              f"survive for resume)")

    # FM5 (T73): the old filter keyed on the year and would have silently stopped alarming on
    # 2027-01-01, and already skipped any record without a `started` field.
    silent = [t for t, d in reg.get("dispatches", {}).items()
              if not rec_alive(d) and not d.get("reported")]
    if silent:
        print()
        print(f"!! {len(silent)} RETURN(S) NEVER REPORTED: {', '.join(sorted(silent))}")
        print("   These agents exited and no `wait` ever announced them, so their slots sat")
        print("   idle for however long that has been. This is the 2026-08-05 defect: a")
        print("   waiter reports once and must be re-armed, and a return nobody watched is")
        print("   a return nobody acted on. Audit them now, then re-arm.")

    # [LJ-1.205] THE OWNER'S SECOND HALF: stopping on `blocked` is only safe if
    # nothing lets a blocked agent sit forgotten. Reviewing it is a human act and
    # a human act with no alarm is a leak, so the census shouts until the pane is
    # gone. It costs one `herdr agent list` and it is the only thing standing
    # between "review before closing" and "never closed".
    blocked = []
    for task, d in reg.get("dispatches", {}).items():
        if not rec_alive(d):
            continue
        try:
            out = subprocess.run(["herdr", "agent", "get", herdr_name(task)],
                                 capture_output=True, text=True, timeout=10).stdout
        except Exception:
            continue
        if '"agent_status":"blocked"' in out:
            blocked.append(task)
    if blocked:
        print()
        print(f"!! {len(blocked)} AGENT(S) BLOCKED, waiting for input: "
              f"{', '.join(sorted(blocked))}")
        print("   herdr reports an approval or question UI. The driver no longer counts")
        print("   `blocked` as finished (owner, 2026-08-14), so the pane is OPEN and the")
        print("   agent is ALIVE and doing nothing. Read it, answer it, or stop it:")
        for task in sorted(blocked):
            print(f"       herdr agent read {herdr_name(task)} --source recent --lines 60")
            print(f"       herdr agent prompt {herdr_name(task)} \"<your answer>\"")
        print("   This banner is the mechanism: a reviewed agent nobody closed keeps")
        print("   shouting here until its pane is gone.")

    # POD EDIT 6 of 6, row 15, second half (design section 6.2). THE
    # UNREGISTERED-RETURN BANNER IS DELETED HERE, with the function that fed it.
    # It read `dev/PLAN.md` section 11, and dev/pod/queue.toml plus the
    # transition log replace that index.

    rl = STATE / "returns.log"
    if rl.exists():
        tail = [l.rstrip() for l in rl.read_text().splitlines()][-5:]
        if tail:
            print("\n  last returns announced (durable log, survives a lost notification):")
            for l in tail:
                print(f"    {l}")

    total_agda, per_parent, agda_warn = agda_pileup()
    if agda_warn:
        print(f"\nWARNING: {agda_warn}")
    else:
        piled = {ppid: n for ppid, n in per_parent.items() if n > 1}
        if piled:
            print(f"\n!! AGDA PILEUP: {total_agda} agda processes are live, and one parent "
                  f"owns more than one.")
            for ppid, n in sorted(piled.items(), key=lambda kv: -kv[1]):
                print(f"   ppid {ppid} owns {n} agda processes")
            print("   C-12 is ONE agda process per agent. Each carries the -M8g cap, so N of")
            print("   them is N x 8 GB of worst-case allocation on one machine. An agent that")
            print("   retries a walling typecheck without killing the previous one produces")
            print("   exactly this. Kill the extras, then decide whether to stop the agent.")
        elif total_agda:
            print(f"\nagda: {total_agda} live, one per parent, within C-12.")
        # THE ORPHANS GET THEIR OWN LINE, because `per_parent` no longer holds them and
        # a census that counts them into the total without naming them reads as a
        # pile-up that is not there. `pod.py`'s `reap_orphan_agda()` ends them at
        # `agda_deadline_s`; this only reports what is on the machine right now.
        owned, _ = agda_orphans(1)
        if owned:
            print(f"\n{len(owned)} ORPHANED agda process(es) at PPID {INIT_PID}, whose "
                  f"parent has exited:")
            for pid, elapsed in owned:
                print(f"   pid {pid}, {elapsed} s elapsed")
            print("   Nobody is waiting on these and nobody can read their answers. The")
            print("   POD reaps one past agda_deadline_s on its next tick.")

    # THE PANE SWEEP. [LJ-1.124]'s pane stayed open because its driver predated
    # the close-on-clean-finish change, and a human closed it. Nothing swept it,
    # and nothing swept any pane whose driver died either.
    sweep, evidence, herdr_warn = sweepable_panes(reg)
    if herdr_warn:
        print(f"\nWARNING: {herdr_warn}; the pane sweep is BLIND this run, so "
              f"an empty sweep list is not an all-clear")
    if evidence:
        print(f"\n{len(evidence)} PANE(S) KEPT AS EVIDENCE, and the sweep will "
              f"not close them:")
        for r in evidence:
            why = "no final message" if not r["clean"] else "log records a death"
            print(f"  {r['pane']}  {r['task']:<16} {why}")
        print("   A dead agent's terminal is the only record of how it died. "
              "Close one by hand only after you have read it.")
    if sweep:
        print(f"\n{len(sweep)} STALE PANE(S) can be closed: their agents are "
              f"idle, their drivers have exited, and each left a clean final "
              f"message.")
        for r in sweep:
            print(f"  {r['pane']}  {r['task']}")
        if a.sweep_panes:
            for r in sweep:
                ok = close_pane(r["pane"])
                print(f"   {'closed' if ok else 'COULD NOT CLOSE'} {r['pane']} "
                      f"({r['task']})")
        else:
            print(f"   Run `{CLI} status --sweep-panes` to close them. "
                  "This tool reports by default and never closes without the "
                  "flag.")

    found, warning = strays(reg)
    if warning:
        print(f"\nWARNING: {warning}")
        return 1
    if found:
        print("\nUNMANAGED STRAYS (launched outside this script, so unregistered, "
              "uncounted against the slots, and unresumable):")
        for x in found:
            print(f"  {x}")
        return 1
    # THE HERDR-ERA SHAPE OF THE SAME VIOLATION. A herdr agent whose name maps
    # to no registry task was started outside this script, so it is uncounted
    # against the Agda slots and nothing will ever announce its return. It is
    # reported and NOT failed on, because the workspace is shared with the
    # owner's own agents by the owner's instruction, 2026-08-13.
    agents, _ = herdr_agents()
    known_names = {herdr_name(t) for t in reg.get("dispatches", {})}
    outside = [x for x in agents if x.get("name") not in known_names]
    if outside:
        print(f"\n{len(outside)} herdr agent(s) outside this registry "
              f"(shared workspace, so this is a note and not a violation):")
        for x in outside:
            # An agent nobody named through this script carries no `name` key
            # at all, so say what it IS rather than printing `None`.
            label = x.get("name") or f"(unnamed {x.get('agent')})"
            print(f"  {x.get('pane_id')}  {label} "
                  f"[{x.get('agent')}, {x.get('agent_status')}]")
    warn_if_unarmed()
    return 0


# WHY THERE IS NO "AM I HARNESS-TRACKED" CHECK, though one was written and
# removed on 2026-08-06. The failure it aimed at is real: arming the waiter with
# `&` inside a compound Bash command produces a waiter whose report reaches
# nobody, and T117 sat unnoticed for 32 minutes that way. But from inside the
# process that case is indistinguishable from the CORRECT one: fd 1 is a pipe
# in both, because the arming command is routinely piped through `tail`. The
# check therefore refused to arm in exactly the situation it must arm in, which
# is worse than the disease. A check that cannot separate the failure from the
# correct usage is not a check.
#
# What catches it instead, and did: the durable returns.log, and `status`'s
# loud NO WAITER IS ARMED banner. Detection after the fact plus a cheap recovery
# beat a detector that fires on the wrong cases.


def already_announced() -> set[str]:
    """Task names the durable log has already reported.

    MEASURED DEFECT, 2026-08-06: a freshly armed waiter re-announced T117, a
    return that had been audited half an hour earlier, treated that as its one
    report, and exited. The live agent it was armed for was left unwatched.
    A waiter must not spend its single report on old news.
    """
    log = STATE / "returns.log"
    if not log.exists():
        return set()
    out = set()
    for line in log.read_text().splitlines():
        parts = line.split()
        if len(parts) >= 3:
            out.add(parts[2])
    return out


WAITER_PID = STATE / "waiter.pid"


def waiter_alive() -> list[int]:
    """PIDs of live waiters, from a PID FILE rather than a command-line grep.

    [L3.32-T119] found two defects in the grep version. It matched on the
    string "dispatch.py wait", so any process whose command line contained
    those words counted, including a reviewer reading the file. And the
    singleton kill built on it was racy: two waiters arming in the same tick
    each read pgrep before either exited, so each killed the other and zero
    were left, the mirror image of the five-waiter pile-up it was added to fix.

    A PID file written under the registry lock has neither problem.
    """
    me = os.getpid()
    if not WAITER_PID.exists():
        return []
    try:
        pid = int(WAITER_PID.read_text().strip())
    except (ValueError, OSError):
        return []
    if pid == me or not alive(pid):
        return []
    return [pid]


def warn_if_unarmed() -> None:
    """Say loudly when agents are live and nothing is watching them.

    MEASURED 2026-08-06: the re-arm is the orchestrator's job and the
    orchestrator forgets. Every return that went unnoticed this session went
    unnoticed in exactly this state. So both `run` and `status` check it: any
    command that touches the registry now also tells you the notification
    path is dead.
    """
    live = running(load())
    if live and not waiter_alive():
        print(f"\n!! NO WAITER IS ARMED and {len(live)} agent(s) are live "
              f"({', '.join(sorted(live))}).")
        print("   Their returns will produce NO notification. Arm one now, as a")
        print("   harness-tracked background job:")
        # The cutover deleted `.claude/skills/codex-dispatch/dispatch.py`, which this
        # line used to print, and moved the `wait` subcommand into THIS file
        # (`cmd_wait` below). `CLI` is the one home of the invocation string.
        print(f"       {CLI} wait")


def cmd_wait(a) -> int:
    """Block until a registered agent exits, then say what came back and what it left.

    This exists because setsid detachment (correctly) hides agents from the orchestrator's
    harness, so a return produced no signal at all. `wait` owns nothing and signals nothing:
    it polls the registry and exits, which is what turns a return into a notification.
    Killing it is harmless, unlike the watcher whose death took two agents with it."""
    start = time.time()
    watched = running(load())
    if not watched:
        print("dispatch: nothing is running; no return to wait for")
        return 0

    # POD EDIT 6 of 6, row 17 (design section 6.2). THE `wait --all` REFUSAL IS
    # DELETED HERE. It is dead code under the POD: the POD never runs `wait`.
    # The program polls its own state file every `tick_seconds` and rule (f)
    # reads a finished worker, so no human arms a waiter and no waiter can be
    # armed wrongly.
    #
    # ITS MEASUREMENT IS KEPT, because it names a hazard the POD must not
    # rebuild: MEASURED 2026-08-06, the orchestrator armed `wait --all` on every
    # dispatch of the session and lost four returns. `--all` blocks until the
    # SLOWEST agent finishes, so a fast return sits unnoticed behind a slow one.
    # T97 and T98 returned and sat while T96 kept running. The POD's answer is
    # structural: it reads EVERY running task at every tick and never blocks on
    # one.

    # SINGLETON, under the registry lock so two waiters arming in the same tick
    # cannot kill each other. An earlier comment here claimed this ran after a
    # harness check; that check was written and removed the same session and the
    # comment outlived it, which is exactly the kind of lie [L3.32-T119] was
    # dispatched to find. There is no harness check. What there is: one PID
    # file, taken atomically, so the last arming wins and the count is never
    # zero by accident.
    with registry_lock():
        for pid in waiter_alive():
            try:
                os.kill(pid, signal.SIGTERM)
                print(f"dispatch: retired the previous waiter (pid {pid}); one at a time")
            except OSError:
                pass
        try:
            WAITER_PID.parent.mkdir(parents=True, exist_ok=True)
            WAITER_PID.write_text(str(os.getpid()))
        except OSError:
            pass


    print(f"dispatch: watching {len(watched)} agent(s): {', '.join(sorted(watched))}")
    done: dict = {}
    while True:
        time.sleep(15)
        reg = load()
        # MEASURED DEFECT, 2026-08-05: the watch set used to be snapshotted at start, so an
        # agent dispatched afterwards was never watched and its return produced no signal at
        # all. Two returns sat unnoticed for 52 minutes until the owner asked. Re-scan every
        # tick and adopt anything new.
        for t, d in reg.get("dispatches", {}).items():
            # FM3 (T73): adopting only LIVE records missed an agent that was dispatched after
            # this waiter began and died inside one 15 s tick: never watched, never
            # announced, never flagged. Adopt any unreported record we have not seen.
            if t not in watched and t not in done and not d.get("reported"):
                watched[t] = d
                print(f"dispatch: also watching {t}, dispatched after this wait began")
        done = {t: d for t, d in watched.items()
                if t in reg.get("dispatches", {}) and not rec_alive(reg["dispatches"][t])}
        if done and not a.all:
            break
        if a.all and len(done) == len(watched):
            break
        if a.timeout and (time.time() - start) > a.timeout:
            print(f"dispatch: timed out after {a.timeout}s with "
                  f"{len(watched) - len(done)} still running")
            return 0

    with registry_lock():
        reg = load()
        for tname in done:
            if tname in reg.get("dispatches", {}):
                reg["dispatches"][tname]["reported"] = True
        save(reg)
    # MEASURED 2026-08-06: a waiter whose stdout goes nowhere (started with `&` and its
    # output discarded, instead of as a harness-tracked job) SILENTLY CONSUMES the return it
    # reports: it marks `reported` and the message reaches no one. T90's return was lost that
    # way. The waiter cannot know where its stdout goes, so it also writes every return to a
    # durable log; a lost notification is then recoverable instead of gone.
    stamp = time.strftime("%Y-%m-%d %H:%M:%S")
    try:
        LOGS.mkdir(parents=True, exist_ok=True)
        with open(STATE / "returns.log", "a") as rf:
            for tname in sorted(done):
                d = done[tname]
                final = Path(d.get("final", ""))
                ok = "clean" if final_is_clean(final) else "NO-FINAL-MESSAGE"
                rf.write(f"{stamp}  {tname}  {ok}  {d.get('log','')}\n")
    except OSError:
        pass
    print(f"dispatch: {len(done)} agent(s) RETURNED after "
          f"{int(time.time() - start)}s: {', '.join(sorted(done))}")
    for t, d in sorted(done.items()):
        final = Path(d.get("final", ""))
        if final_is_clean(final):
            print(f"  {t}: finished cleanly, final message {final}")
        else:
            print(f"  {t}: NO FINAL MESSAGE, so it was killed or ran out of budget. "
                  f"Its work may still be on disk. Consider `{CLI} resume {t}`.")
        print(f"       log {d.get('log')}")
    still = [t for t in watched if t not in done]
    if still:
        print(f"dispatch: {len(still)} agent(s) STILL RUNNING and now UNWATCHED: "
              f"{', '.join(sorted(still))}")
        print(f"dispatch: RE-ARM NOW, or their returns will sit unnoticed. "
              f"One waiter reports once; that is the whole contract.")
    return 0


# POD EDIT 6 of 6, row 16 (design section 6.2). `_tree_maybe_live()` IS DELETED
# HERE, with `_TREE_N`, `_PLAN_INDEX`, `_TASKS_TREE`, `_TREE_ROW` and `_SCOPE`,
# which had no other reader, and with the second half of `cmd_gate_ready()`
# below.
#
# WHAT IT DID. It was `gate-ready`'s PLAN-ROW HALF, a second opinion beside the
# registry: it read the `dev/PLAN.md` task index for every row still saying
# DISPATCHED, then looked for a write younger than 15 minutes inside that
# task's directory or its brief's declared SCOPE (write).
#
# WHY IT GOES. Its ONE input is `dev/PLAN.md` section 11, which dev/pod/
# queue.toml and the transition log replace. It cannot read a row that nothing
# writes. The registry half of `cmd_gate_ready()` STAYS and still refuses.
#
# ITS MEASUREMENT IS KEPT, AND SO IS THE GAP IT CLOSED. [LJ-1.371] measured
# that the registry is blind to an in-harness dispatch, which passes through no
# tool: 46 percent of all dispatches wrote no registry record, and on
# 2026-08-16 `gate-ready` said "no agent is live" over a live agent's tree. The
# POD closes that gap at the source and not with a second opinion: EVERY POD
# worker starts through `launch()`, so every worker writes a registry record and
# a transition log line. An in-harness dispatch does not exist under AD18.


def cmd_gate_ready(a) -> int:
    """Refuse a full-tree gate while any agent is live.

    Measured 2026-08-05: a full `agda src/Everything.lagda.md` was run while an agent was
    mid-write on a master, and it failed on a name that agent had not finished introducing.
    The result LOOKED like a red gate on the change being audited, and it was nothing of the
    kind. The dangerous half of this is the other one: had the half-written file happened to
    parse, the run would have gone GREEN over content nobody had finished writing.

    ORCHESTRATION section 4 already forbids a tree-wide WRITE while agents hold territory.
    This is the same hazard on the read side, and it needed its own check."""
    # POD EDIT 6 of 6, row 16, second half (design section 6.2). THE PLAN-ROW
    # SECOND OPINION IS GONE. The registry half below is the whole check now.
    live = running(load())
    if not live:
        print("dispatch: no agent is live; a full-tree gate will read a settled tree")
        return 0
    print(f"dispatch: DO NOT run a full-tree gate now. {len(live)} agent(s) are live "
          f"({', '.join(sorted(live))}) and may be mid-write on a master. A gate run now "
          f"reads half-written files: a spurious failure at best, a spurious GREEN at "
          f"worst. Wait for the run to end and re-run this command.", file=sys.stderr)
    return 1


# POD EDIT 6 of 6, row 11 (design section 6.2). `dd4_defects()` IS DELETED
# HERE, whole, and amendment A7 is why that is a RE-HOMING and not a loss.
#
# DD4 is the route's core constraint: maximize the code the two proofs share,
# and write it generic. Under A7 it is a WRITTEN RULE, clause W2 of design
# section 3.1, and the program carries it into
# dev/pod/instructions/mathematician.md at every dispatch.
#
# THE GATE CANNOT TRAVEL WITH THE RULE. This function read the BRIEF FILE and
# demanded the token `DD4`, or both halves of the DD4 sentence. Neither the
# section 6.3 template nor the worked brief of section 6.4 carries one, so
# keeping the function refuses EVERY POD dispatch from day 2 onward. Injecting
# the instruction file at prompt time does not satisfy it either, because the
# refusal never reads the prompt.
#
# WHAT IS LOST, STATED PLAINLY. W2 has no metric, by the owner's own decision: a
# shared-line count is gamed the moment it gates anything. So W2's `enforced by`
# value is `agent discipline`, and section 3.1 states the loss. The risk is
# real: [LJ-0.3] measured an imported playbook sitting uncited in 102 of 112
# briefs over five days, which is this exact mechanism drifting once already.


def survey_defects(brief: Path) -> list[str]:
    """DD18's two surveys, enforced identically. Refusals, on EVERY brief.

    THE RULE. A brief carries an ARCHIVE section naming what in the archives
    may bear on the task, and a LITERATURE section naming what in
    dev/literature/ may. A return carries ARCHIVE USED and LITERATURE USED,
    saying what was read, what was taken, and WHY NOT for anything skipped.

    WHY BOTH ARE GATED, aligned by the owner 2026-08-10. The archive half ran
    on review alone and never once lapsed: twelve of twelve briefs and
    thirteen of thirteen returns complied. That record argued against gating
    it. The owner ruled the two should be enforced the same way regardless,
    and the record makes the gate cheap rather than redundant: a rule already
    obeyed costs nothing to check.

    WHY EVERY BRIEF, AND NOT ONLY A BUILD. The literature half was first
    scoped to master-writing briefs, on the reasoning that a recon or a
    tooling task needs no mathematics. That reasoning was WRONG and the test
    is the case that prompted the whole rule: `[LJ-1.1]` is a recon, it wrote
    only a report, and it PLANNED THE ENTIRE GCH WING without citing a line of
    dev/literature/. Under the build-only scope the gate would have exempted
    exactly the brief it was built for. So both checks fire on every brief.

    THE ESCAPE VALVE IS ONE HONEST LINE, per section, and it is deliberate. A
    brief satisfies either by naming the corpus and saying nothing in it bears
    on the task. That is cheap to write and it forces the author to LOOK,
    which is the whole point. A check nobody can satisfy honestly gets
    satisfied dishonestly.

    THIS BINDS THE CODEX PATH ONLY. An in-harness dispatch does not pass
    through this file, and [LJ-1.11] proved that gap by going out short two
    mandatory rules. The orchestrator applies these by hand there.

    IT GUARDS ITS OWN READ, for the same FM3 reason `validate()` does. This
    function was the site of the missing-brief traceback: the funnel's `+` runs
    it even when `validate()` has already refused.
    """
    if (why := brief_unreadable(brief)):
        return [why]
    text = brief.read_text(encoding="utf-8")
    out = []
    if not (re.search(r"^#*\s*ARCHIVE\b", text, re.M | re.I)
            or re.search(r"\barchive/", text)):
        out.append(
            "brief carries no ARCHIVE section (DD18). Name what may bear on "
            "the task in archive/rud-route/ for the retired code, "
            "archive/dev/TASKS-archived.md for what each dispatch found, "
            "JOURNAL-archived.md for why, DECISIONS-archived.md for the "
            "rulings. Require an ARCHIVE USED section in the return. If "
            "nothing applies, say so in one line naming the archives.")
    if not (re.search(r"^#*\s*LITERATURE\b", text, re.M | re.I)
            or re.search(r"dev/literature/", text)):
        out.append(
            "brief carries no LITERATURE section (DD18). dev/literature/ holds "
            "the digested mathematics: digest.md for the orthodox route, "
            "j-hierarchy.md for condensation, devlin-errata.md for the known "
            "errors in the primary text, BIBLIOGRAPHY.md for what was fetched "
            "and what consumed it. Require a LITERATURE USED section in the "
            "return, with WHY NOT for anything skipped. If nothing applies, "
            "say so in one line naming dev/literature/.")
    return out


def brief_kind(text: str) -> str:
    """The task kind, DERIVED from the brief's write scope, never self-declared.

    NOTE, POD EDIT 6 of 6: this function LOST ITS ONLY CALLER when row 10
    removed `rule_bundle_defects()`. The design orders no removal of it, so it
    stays. A later reader who needs the brief kind has it here.

    [L3.32-T105] pointed out that an author who declares the kind chooses the
    bundle. Extracted from rule_bundle_defects on 2026-08-10 so the literature
    refusal derives the kind the SAME way; two copies would drift, which is the
    defect class C-26 names and which this file has already paid for twice
    today in its forbid-pattern and probe-suffix rules.
    """
    # Derive the kind: a brief that may write a master is a build, a brief that
    # writes only probes or /tmp is a probe, anything else is a recon.
    scope = re.search(r"##\s*SCOPE\s*\(write\)(.*?)(?=\n##\s|\Z)", text,
                      re.S | re.I)
    body = scope.group(1) if scope else ""
    # A SCOPE (write) section names masters twice: the ones the agent may write
    # and the ones it must NOT. Counting the prohibitions classified [T99], a
    # probe whose scope says "Never any master, in particular SquareLaw", as a
    # build, and demanded the wrong bundle. Drop the forbidding lines first.
    # A FORBIDDING clause is dropped before the paths are read, and the unit
    # is a SENTENCE, not a line. Two failures forced that.
    #
    # [T99]: "Never any master, in particular SquareLaw" classified a probe as
    # a build, so forbidding text had to be dropped at all.
    #
    # [LJ-1.1], 2026-08-09, two separate faults in the line-based version.
    # First, the brief wrapped as "You may not\ntouch `src/`", which put the
    # negation and the path on DIFFERENT LINES, so the path survived and a
    # recon was sent the build bundle. Second, widening the pattern then broke
    # the other direction: "`src/L/Foo.lagda.md`, new. Do not touch
    # `src/L/Bar.lagda.md`." is one line holding a permission AND a
    # prohibition, and dropping the line dropped the permission, classifying a
    # real build as a recon. Sentences fix both: joining the wrapped text
    # reunites "may not" with its path, and splitting on sentence ends keeps
    # the permission that merely shares a line with a prohibition.
    # THE NEGATION MUST BE ABOUT WRITING, NOT ABOUT COMMITTING. [LJ-1.2]'s
    # scope read "`src/ProbeLJ12.lagda.md`, which is a PROBE and is never
    # committed", and the bare `never` swallowed the sentence that NAMES the
    # probe, so a probe brief derived as a recon and got the wrong bundle.
    # "Never committed" is D-1's lifecycle rule and appears inside PERMITTING
    # sentences constantly; committing is a different action from writing.
    NOT_A_WRITE_VERB = r"(?!\s+(?:commit|push))"
    FORBID = re.compile(r"\bnever\b" + NOT_A_WRITE_VERB
                        + r"|\bread-only\b|\bno master\b"
                        r"|\b(?:do|may|must|shall|will|can)\s?n[o\u2019']t\b"
                        + NOT_A_WRITE_VERB
                        + r"|\bnot (?:write|touch|edit|modify)\b", re.I)
    flat = re.sub(r"\s+", " ", body)
    sentences = re.split(r"(?<=[.;!?])\s+", flat)
    body = " ".join(s for s in sentences if not FORBID.search(s))
    # A PROBE IS A PROBE WHEREVER IT IS, and in whichever suffix. scripts/
    # check-probes.py says exactly that and recognizes Probe* in .agda and
    # .lagda.md alike; this derivation knew only .agda, so [LJ-1.2]'s
    # `src/ProbeLJ12.lagda.md` matched the MASTER pattern and a probe brief
    # derived as a build. The two tools now agree on what a probe looks like.
    PROBE = r"`?(src/Probe[\w.-]*\.(?:agda|lagda\.md))`?"
    probes = re.findall(PROBE, body)
    masters = [m for m in re.findall(r"`?(src/[\w./-]+\.lagda\.md)`?", body)
               if not pathlib.Path(m).name.startswith("Probe")]
    if masters:
        kind = "build"
    elif probes or "/tmp" in body:
        kind = "probe"
    else:
        kind = "recon"
    if "adversarial" in text[:1200].lower():
        kind = "review"
    return kind


# POD EDIT 6 of 6, row 10 (design section 6.2). `rule_bundle_defects()` IS
# DELETED HERE, whole. It refused a brief that did not cite its kind's mandatory
# rule bundle, derived from the brief's write scope and read out of
# scripts/pod/rules.py.
#
# WHY IT GOES. The bundle it demanded is AGENTS.md's rule set, and AD4 voids
# that document. THE FUNCTION WOULD OTHERWISE STAY LIVE: its only escape is
# `scripts/pod/rules.py` being absent, and section 7.1 row 22 KEEPS that
# file. So an unremoved copy refuses every POD brief for a rule set that no
# longer binds.
#
# ITS MEASUREMENT IS KEPT. [LJ-1.295] moved rules.py on 2026-08-15 at 17:25 and
# this function still named the old path, so the refusal was DEAD for four
# hours and a brief citing ZERO mandatory rules passed `check` clean, exit 0.
# The POD answers the same need differently: design section 7.4 GENERATES the
# `## LAWS`, `## ARCHIVE` and `## LITERATURE` sections into the brief, so the
# author cannot forget them and no gate has to notice.


def cmd_check(a) -> int:
    brief = resolve_brief(a.brief)
    defects = launch_defects(brief, a.sandbox, a.agda, case_from_args(a))
    for d in defects:
        print(f"dispatch: {d}", file=sys.stderr)
    if defects:
        return 1
    print(f"dispatch: {brief.name} is well formed for sandbox {a.sandbox}"
          + (" with --agda" if a.agda else ""))
    return 0


def main() -> int:
    p = argparse.ArgumentParser(description=__doc__,
                                formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = p.add_subparsers(dest="cmd", required=True)

    def common(sp):
        sp.add_argument("task")
        sp.add_argument("brief")
        sp.add_argument("--agda", action="store_true",
                        help="the agent will run Agda, so it holds one of the two slots")
        sp.add_argument("--sandbox", default="workspace-write",
                        choices=["workspace-write", "read-only"])
        sp.add_argument("--model", default=DEFAULT_MODEL)
        # POD EDIT 4 of 6, part 1 of 2 (design section 6.2). The five values are
        # `legal.efforts` in dev/pod/heads.toml, and the claude CLI's `--effort`
        # takes exactly those five. The empty default keeps every non-claude
        # dispatch unchanged.
        sp.add_argument("--effort",
                        choices=tuple(LEGAL_EFFORTS) + ("",),
                        default="",
                        help="the claude CLI's reasoning effort. It reaches the "
                             "pane and the pane reports it twice: the banner says "
                             "`with max effort` and the footer says `max · /effort`. "
                             "THE VALUE COMES FROM dev/pod/heads.toml, never from "
                             "memory. REQUIRED on a claude harness: the empty "
                             "default is what a non-claude dispatch keeps")
        # A14. The tier picks the GHCRTS caliber and the slot ceiling, and the
        # record carries it so two measurements are compared only within a tier.
        sp.add_argument("--tier", choices=agda_tiers(), default=AGDA_TIER_DEFAULT,
                        help="the Agda concurrency tier of dev/pod/heads.toml. "
                             "wide is four concurrent writers at -A64m -I0 -M8g; "
                             "heavy is two at -A64m -I0 -M12g. The mixed worst-case "
                             "heap sum is held at or under 32 GB whichever is used")
        # POD EDIT 4 of 6, part 2 of 2 (design section 6.2). `argparse` validates
        # a SUPPLIED value against `choices`, so `--harness herdr-claude` was
        # refused before any other edit could run. This edit BLOCKS the other
        # three, so it comes with them or none of them work.
        # **THE LIST IS DERIVED AND IT USED TO BE A SECOND HAND-WRITTEN COPY.** MEASURED
        # 2026-08-19 while wiring grok: `HERDR_KIND` gained `herdr-grok`, every runtime
        # path took it, and this tuple did not, so argparse refused `--harness herdr-grok`
        # before one line of the new wiring could run. The map above is the one home; the
        # two direct-exec harnesses are not in it and are named beside it.
        sp.add_argument("--harness",
                        choices=tuple(HERDR_HARNESSES) + ("codex", "pi"),
                        default=HARNESS,
                        help="herdr-claude runs a CLAUDE agent in a server-owned "
                             "pane, which is the POD's one harness; "
                             "herdr runs a CODEX agent in a server-owned pane and "
                             "herdr-pi runs a PI agent in one, so `herdr agent "
                             "list|attach|wait` see either from any terminal; codex "
                             "is the old direct-exec path; pi runs the pi CLI direct "
                             "through pi_stream.py. THE MODULE DEFAULT IS NOT "
                             "LOAD-BEARING: the POD passes --harness, --model and "
                             "--effort on every dispatch, and dev/pod/heads.toml is "
                             "the one home of all three")
        sp.add_argument("--wait", action="store_true",
                        help="after launching, block until THIS agent returns, then report. "
                             "Run the whole command as a harness-tracked background job and "
                             "its exit becomes the notification, which removes the separate "
                             "arming step and the chance of forgetting it")
        g = sp.add_mutually_exclusive_group()
        g.add_argument("--adversarial", action="store_true",
                       help="assert this is the ADVERSARIAL case (DD25). Required when the "
                            "mode in force makes this head correct only for that case.")
        g.add_argument("--fallback", action="store_true",
                       help="assert this is the FALLBACK case: the head the table gives is "
                            "unavailable today. Say why in the brief.")
        sp.add_argument("--allow-model", action="store_true",
                        help="lift a date-gated model block for this run, after verifying "
                             "the model works with a one-line codex exec")

    common(sub.add_parser("run"))
    q = sub.add_parser("queue")
    common(q)
    q.add_argument("--resume-of", default=None, metavar="TASK",
                   help="continue TASK's recorded session instead of running the brief "
                        "fresh; the right choice whenever an agent was killed or ran out "
                        "of budget")
    q.add_argument("--note", default=None,
                   help="tell the resumed agent what survived, so it does not redo it")
    r = sub.add_parser("resume")
    r.add_argument("task")
    r.add_argument("--note", default=None,
                   help="tell the resumed agent what survived, so it does not redo it")
    r.add_argument("--allow-model", action="store_true")
    s = sub.add_parser("status")
    s.add_argument("--all", action="store_true", help="include superseded history")
    s.add_argument("--sweep-panes", action="store_true",
                   help="close the stale herdr panes the census reports. A pane "
                        "whose task ended in a death is NEVER closed: it is the "
                        "only evidence of how the agent died")
    sub.add_parser("gate-ready")
    w = sub.add_parser("wait")
    w.add_argument("--all", action="store_true",
                   help="BLOCKING mode: wait for EVERY running agent. This is NOT the "
                        "notification path and is REFUSED when more than one agent is "
                        "live. Use plain `wait` to be notified; use this only to block "
                        "before a gate.")
    w.add_argument("--timeout", type=int, default=0, help="seconds; 0 means no limit")
    c = sub.add_parser("check")
    c.add_argument("brief")
    c.add_argument("--sandbox", default="workspace-write",
                   choices=["workspace-write", "read-only"])
    c.add_argument("--agda", action="store_true")
    cg = c.add_mutually_exclusive_group()
    cg.add_argument("--adversarial", action="store_true")
    cg.add_argument("--fallback", action="store_true")

    a = p.parse_args()
    global HARNESS
    # THE FALLBACK IS THE POLICY'S DEFAULT, NOT "codex". `resume`, `status`,
    # `wait`, `check` and `gate-ready` carry no `--harness`, so this line used
    # to force the global to "codex" for every one of them. `cmd_resume` then
    # overwrote it from the record, which hid the defect; nothing else did.
    # [LJ-1.127], 2026-08-13.
    HARNESS = getattr(a, "harness", None) or HARNESS
    # A CLAUDE HARNESS WITH NO EFFORT IS A USAGE ERROR, exit 2, and it used to be
    # ACCEPTED. `--effort` defaults to "" so that a codex or a pi dispatch keeps
    # working, and edit 2 then put that empty string on a claude pane's argv as
    # `--effort ""`. The default harness is now `herdr-claude`, so the accepted
    # command `launcher.py run <task> <brief>` was itself the broken one.
    #
    # TWO REFUSALS, TWO CODES, AND THAT IS THE FILE'S CONTRACT. This one is the
    # command line's, so it exits 2 like every other argparse error. `launch()`
    # refuses the same state at the funnel and exits 1, because a caller that
    # reaches `launch()` in-process never passed through argparse.
    if (getattr(a, "effort", None) == "" and HERDR_KIND.get(HARNESS) == "claude"
            and a.cmd in ("run", "queue")):
        p.error(f"--effort is required on the {HARNESS} harness, which runs the "
                f"claude CLI. Give one of {', '.join(LEGAL_EFFORTS)}. The value "
                f"belongs to the head's slot in dev/pod/heads.toml, which is its "
                f"one home; an empty value would reach the pane as --effort \"\".")
    # POD EDIT 5 of 6, second half (design section 6.2). THE CASE-OVERRIDE BLOCK
    # IS DELETED HERE. It read `POLICY.head(<case>)` and then
    # `POLICY.HARNESS_FOR_AGENT`, so it could rewrite the harness of an
    # `--adversarial` or `--fallback` dispatch out from under `heads.toml`.
    # Section 7.1 row 21 retires scripts/dispatch/dispatch_policy.py, and the
    # POD resolves a head from dev/pod/heads.toml ONCE, at dispatch (AD26).
    # Two head sources is one source too many.
    #
    # ITS MEASUREMENT IS KEPT, because it is why the block existed:
    # MEASURED 2026-08-15, LJ-1.311 was dispatched --adversarial, the table
    # printed `pi`, and the launch argv read `["codex","-m","glm-5.3"]`. The
    # agent then sat 2762 s on codex's hook-trust modal and returned nothing.
    # The POD cannot repeat it, because it passes `--harness` explicitly.
    if POLICY_ERROR:
        # A designed retirement is a NOTE. A module that is present and broken is a
        # WARNING. One variable carries both, and `POLICY_RETIRED` separates them.
        print(f"dispatch: {'NOTE' if POLICY_RETIRED else 'WARNING'}: {POLICY_ERROR}",
              file=sys.stderr)
    if HEADS_ERROR:
        print(f"dispatch: WARNING: {HEADS_ERROR}", file=sys.stderr)
    return {"run": cmd_run, "queue": cmd_queue, "resume": cmd_resume,
            "status": cmd_status, "check": cmd_check, "wait": cmd_wait,
            "gate-ready": cmd_gate_ready}[a.cmd](a)


if __name__ == "__main__":
    sys.exit(main())
