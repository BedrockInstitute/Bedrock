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
lost records under the tool's own documented fan-out (D1); `alive()` read EPERM as "dead",
so a live agent could read as exited (D2); the dead-model refusal lived only in `run`, so
`queue` and `resume` could still launch it, recreating failure mode 1 through the very
route the skill recommends (D3); and the read-only detection missed the exact phrasing
this file's own docs use (D4).

  dispatch.py run <task> <brief> [--agda] [--sandbox read-only]
  dispatch.py queue <task> <brief> [--agda]    wait for a free slot, then run, detached
  dispatch.py resume <task> [--note TEXT]      continue a killed or exhausted agent
  dispatch.py status [--all]                   the census, including unmanaged strays
  dispatch.py check <brief>                    validate a brief without launching
  dispatch.py wait [--all] [--timeout S]       block until an agent returns, then report
  dispatch.py gate-ready                       exit 1 if a full-tree gate would read a
                                               half-written file

NOTIFICATION. Agents are setsid'd so that killing whatever launched them cannot take them
down, and the price of that detachment is that nothing is watching them: the orchestrator's
harness only announces background work IT tracks, so returns went unnoticed until the owner
asked. `wait` is the fix and it is deliberately NOT the agents' parent: it only polls the
registry, so it inherits none of the ownership that made the original watcher lethal. Run it
as a tracked background job right after dispatching, and the harness announces the return:

    python3 dispatch.py wait          # exits when the FIRST agent returns
    python3 dispatch.py wait --all    # exits when the last one does

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
STATE = Path(__file__).resolve().parent / ".state"
REGISTRY = STATE / "registry.json"
LOCKFILE = STATE / "registry.lock"
LOGS = STATE / "logs"

# D17: the block WAS date-gated, and the gate did its job. The backend's own message
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
# THE DEFAULT IS NOT A CONSTANT HERE ANY MORE. `scripts/dispatch/dispatch_policy.py`
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
VENDOR_ERROR = ""
try:
    import dispatch_policy as POLICY
    POLICY_ERROR = ""
    try:
        HARNESS = POLICY.default_harness() or "herdr"
    except SystemExit as _vexc:                 # an unwired vendor, by design
        HARNESS = "herdr"
        VENDOR_ERROR = str(_vexc)
except Exception as _exc:                       # pragma: no cover
    POLICY = None
    HARNESS = "herdr"
    POLICY_ERROR = (f"scripts/dispatch/dispatch_policy.py could not be read ({_exc}); "
                    f"the default harness fell back to {HARNESS!r}")

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
HERDR_KIND = {"herdr": "codex", "herdr-pi": "pi"}
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


def herdr_name(task: str) -> str:
    """Map a task code to a legal herdr agent name, reversibly enough to join.

    `LJ-1.123` -> `lj-1-123`. Uppercase and dots are the only characters our task
    codes carry that herdr refuses."""
    return task.lower().replace(".", "-")

# THE AGDA CEILING, AND WHY IT IS TWO AND NOT FOUR.
#
# [L3.32-T119] found three documents giving three different numbers: this file
# said two, LESSONS C-12 says up to FOUR at -M8g in WIDE mode with a memory
# floor and a watchdog, and AGENTS.md says one process at a time. The tool
# implements none of C-12's tier, floor or watchdog, so quoting its four would
# have been quoting a permission whose preconditions do not exist here.
#
# TWO stands, on a reason that outranks throughput. This campaign spends its
# days MEASURING check cost, and two `agda --profile=definitions` runs corrupt
# each other's numbers. [T88] had to disclose a contended baseline for exactly
# that reason, and [T101] and [T103] each measured a module the campaign then
# re-priced from. A wrong measurement here is not slow, it is believed.
#
# The dispatcher cannot see WHAT an agent profiles, so it cannot allow the safe
# concurrent case and forbid the ruinous one. Until it can, the ceiling is the
# only guard and it stays where a corrupted measurement cannot happen: the
# brief carries "one Agda process, nothing else running" for any timed run, and
# the orchestrator holds the second slot open when a measurement is live.
AGDA_HEAP = "-M8g"
AGDA_SLOTS = 2
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
    """D1: serialize the whole load-check-save. Without this, two dispatches racing for the
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
    """D6: a truncated or corrupt registry used to crash every command with a raw traceback.
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
        # D12's lesson, which was applied to `ps` and not here: an unreadable
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
    """D1/D6: atomic replace, so a crash mid-write can never leave a half-file behind."""
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
    """D2: EPERM means the process EXISTS and we merely cannot signal it. The old code
    caught it as OSError and answered 'dead', so in any restricted context a live agent
    read as exited, the slot count dropped, and `resume` would have duplicated it.
    D5: a matching start time is what distinguishes our agent from a recycled PID."""
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
            # D1/T73's reasoning that a dead agent must not hold a slot
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
    # D7: every record access goes through .get, so a key drift degrades instead of crashing.
    return {t: d for t, d in reg.get("dispatches", {}).items() if rec_alive(d)}


def agda_holders(reg: dict) -> dict:
    return {t: d for t, d in running(reg).items() if d.get("agda")}


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
    """
    try:
        out = subprocess.run(["ps", "-A", "-o", "pid=,ppid=,comm="],
                             capture_output=True, text=True)
    except OSError as exc:
        return 0, {}, f"could not run ps ({exc}); agda pileup detection is BLIND"
    if out.returncode != 0 or not out.stdout.strip():
        return 0, {}, "ps returned nothing; agda pileup detection is BLIND"
    per_parent: dict[int, int] = {}
    total = 0
    for line in out.stdout.splitlines():
        parts = line.split(None, 2)
        if len(parts) != 3 or os.path.basename(parts[2].strip()) != "agda":
            continue
        try:
            ppid = int(parts[1])
        except ValueError:
            continue
        per_parent[ppid] = per_parent.get(ppid, 0) + 1
        total += 1
    return total, per_parent, None


def strays(reg: dict) -> tuple[list[str], str | None]:
    """D12: ps can fail outright (it did, inside a sandbox), and an unreadable ps used to
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
        # D12: match a PREFIX, since macOS truncates comm and a longer needle silently
        # matched nothing.
        if "codex-darwin-arm" not in c:
            continue
        if pid in known or ppid in known:
            continue
        if herdr_managed(pid):
            continue
        # D12: an orphan whose wrapper died is ours, not a violation; only flag it when no
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

# D4: the old regex required the literal word "write" immediately before a _build/ path and
# so missed every realistic phrasing, INCLUDING the one this file's own documentation uses
# ("write your report to _build/x.md"). Widened to any write-ish verb within a short window
# of a _build/ path.
WRITE_ORDER = re.compile(
    r"(writ|output|save|deliver|produce|emit)\w*\b[^.\n]{0,80}?`?_build/", re.I)


def check_model(model: str, allow: bool) -> str | None:
    """D3/D17: called from launch(), so EVERY path refuses, not only `run`; and gated on a
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


def clock_defects(brief: Path, case: str = "default") -> list[str]:
    """Refuse a dispatch whose HEAD contradicts the clock, whatever the brief says.

    THE HOLE THIS CLOSES. The tier-line check above compares the brief's TEXT against the
    mode in force. Text is cheap: writing the right mode name in the tier line and then
    launching the wrong head passes it. The head that actually runs is the command line,
    and this function refuses on that.

    THE RULE, and `dispatch_policy.default_harness` already states its first half: this
    dispatcher can only run a head whose harness is `herdr`. So under a mode whose DEFAULT
    head is in-harness, a default-case dispatch through this tool is a contradiction in
    terms. It is not a near miss to be downgraded; it is the wrong tool, and the tool that
    knows the time is the one that must say so.

    WHAT IT COSTS TO GET WRONG. MEASURED 2026-08-15: LJ-1.272 at 09:29 and LJ-1.273 at
    10:21 Beijing both ran pi/deepseek through herdr, inside the 09:00 to 12:00 PEAK
    window, when in-harness-subagent-mode was in force and deepseek was at double price.
    The owner set that clock on 2026-08-14 for exactly this reason. Nothing stopped either
    dispatch: check-dispatch-policy.py judges a brief by the mode it NAMES, which is right
    for a frozen record and blind here, and `default_harness` quietly downgraded to the
    fallback instead of refusing.

    THE CASE IS ASSERTED ON THE COMMAND LINE, never inferred from the brief. Under
    in-harness-subagent-mode the adversarial head IS herdr/pi, so a peak-time pi dispatch
    can be perfectly correct. It must SAY it is adversarial, with `--adversarial`, so the
    assertion lands in the launch log where an audit can find it. An inferred case would
    be one more thing that reads as checked and is not (C-43).
    """
    if POLICY_ERROR:
        return []
    text = brief.read_text(encoding="utf-8")
    m = re.search(r"^tier:\s*([a-z0-9-]+)", text, re.M)
    if not m:
        return []  # the missing-tier-line refusal in validate() already fired
    token = m.group(1)
    try:
        version = POLICY.in_force()
        cases = {c: POLICY.head(c, version) for c in ("default", "adversarial", "fallback")}
    except Exception:
        return []

    if token == getattr(POLICY, "EMERGENCY_TOKEN", "fable"):
        return []  # DD17's breakthrough tier is legal everywhere; the brief names its trigger

    legal_here = [c for c, h in cases.items()
                  if h["tier_token"] == token and h["harness"] != "in-harness"]
    in_harness_only = [c for c, h in cases.items()
                       if h["tier_token"] == token and h["harness"] == "in-harness"]

    if in_harness_only and not legal_here:
        return [f"tier line names head `{token}`, and under `{version}` that head runs "
                f"IN-HARNESS (case: {', '.join(in_harness_only)}). An in-harness dispatch "
                f"never passes through this tool, so there is nothing for it to launch. "
                f"Start the subagent in the harness instead. This is a refusal, not a "
                f"reminder."]

    if not legal_here:
        want = ", ".join(f"{c}={h['tier_token']}({h['harness']})" for c, h in cases.items())
        return [f"tier line names head `{token}`, which is not the head for ANY case under "
                f"`{version}`, the mode in force right now. Under it: {want}. Run "
                f"`python3 scripts/dispatch/dispatch_policy.py` and read the clock line."]

    if case not in legal_here:
        flag = {"adversarial": "--adversarial", "fallback": "--fallback"}
        need = " or ".join(sorted(flag[c] for c in legal_here if c in flag))
        dflt = cases["default"]
        return [f"tier line names head `{token}`, and under `{version}` that head is "
                f"correct ONLY for the {' and '.join(sorted(legal_here))} case, while this "
                f"dispatch declares `{case}`. The default head right now is "
                f"`{dflt['tier_token']}` on `{dflt['harness']}`. "
                + (f"If this really is that case, pass {need} and the assertion goes into "
                   f"the launch log. " if need else "")
                + f"Otherwise take the head the table gives. This is a refusal, not a "
                  f"reminder: the clock decides, and it does not read the brief."]
    return []


def launch_defects(brief: Path, sandbox: str, agda: bool = False,
                   case: str = "default") -> list[str]:
    """Every refusal that must fire before an agent starts.

    ADDED 2026-08-07 after the orchestrator dispatched T135 on a brief that
    `check` had just refused. `cmd_check` called `validate` AND
    `rule_bundle_defects`; `cmd_run` called only `validate`. So the rule
    that says "cite the mandatory bundle" existed only in the command nobody
    is forced to run.

    This is the D3 defect class again, and the docstring at the top of this
    file already records it: "the dead-model refusal lived only in `run`, so
    `queue` and `resume` could still launch it". A refusal that one entry
    point enforces is not a refusal. Every launch path now calls this one
    function, so a new check cannot land in half of them.
    """
    return (validate(brief, sandbox, agda) + rule_bundle_defects(brief)
            + dd4_defects(brief) + survey_defects(brief)
            + clock_defects(brief, case))


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
    """Refuse the failure modes that have actually happened, not hypothetical ones."""
    defects = []
    if not brief.exists():
        return [f"brief does not exist: {brief}"]

    # D15: compare the real path, not just the parent's name, so a fixtures directory that
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

    if not re.search(r"^tier:", text, re.M):
        defects.append("brief has no `tier:` line. The tier line names the head, the mode "
                       "and the version, so an audit can trace the choice. The head for "
                       "each case lives in scripts/dispatch/dispatch_policy.py; a head other "
                       "than "
                       "the table's must name why, and if the sentence will not write, "
                       "take the head the table gives")

    # A BRIEF ABOUT TO BE DISPATCHED NAMES THE MODE IN FORCE NOW.
    #
    # This is deliberately the OPPOSITE rule to scripts/check-dispatch-policy.py, which
    # judges a brief by the mode it NAMES and never by today's switch. That rule is right
    # for a FROZEN record: a brief written under the old mode was correct, and a record is
    # never rewritten (C-41).
    #
    # It is wrong for a brief about to be SENT. Between the two, nothing looked at the
    # clock, so a brief naming a mode that is not in force passed both gates and took the
    # wrong head. MEASURED 2026-08-15: LJ-1.272 at 09:29 and LJ-1.273 at 10:21 both went to
    # pi/deepseek inside the Beijing 09:00-12:00 PEAK window, when in-harness-subagent-mode
    # was in force and deepseek was at double price. The orchestrator answered "which head"
    # from memory, which the skill's first rule forbids in those words. check-dispatch-
    # policy.py passed both, correctly and uselessly: it read a self-consistent pairing.
    #
    # So the clock is read HERE, at the one moment it can still change the outcome.
    m_tier = re.search(r"^tier:.*$", text, re.M)
    if m_tier and not POLICY_ERROR:
        named = re.findall(r"\(([a-z0-9-]+-subagent-mode|normal|override)\)", m_tier.group(0))
        if named:
            try:
                want = POLICY.in_force()
                got = POLICY.canonical(named[0])
            except Exception:
                want = got = None
            if want and got and got != want:
                defects.append(
                    f"brief's tier line names mode `{named[0]}` (canonically `{got}`) but "
                    f"`{want}` is IN FORCE right now. Run "
                    f"`python3 scripts/dispatch/dispatch_policy.py` "
                    f"and read the clock line. Under `{want}` the default head is "
                    f"`{POLICY.tier_token('default', want)}` and the adversarial head is "
                    f"`{POLICY.tier_token('adversarial', want)}`. Fix the tier line and the "
                    f"head together, or if this brief is a FROZEN record being re-checked "
                    f"rather than dispatched, use check-dispatch-policy.py instead, which "
                    f"judges a brief by the mode it names. This is a refusal, not a "
                    f"reminder: the clock moved and the orchestrator's memory did not")

    # D16: a SCOPE (write) section only orders a write when it actually names a path, so a
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

    # D4: Agda writes .agdai interface files, so this combination cannot work at all.
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

    # D15: require the RETURN and evidence rules as SECTIONS, not as stray substrings.
    if not re.search(r"^#*\s*RETURN\b", text, re.M):
        defects.append("brief has no RETURN section: the deliverable's exact shape is "
                       "what makes a return auditable")
    # A brief must demand CHECKABLE evidence, but the right standard depends on the task:
    # `file:line` for anything read out of this tree, a citation URL for a literature search.
    # Requiring the literal `file:line` refused a literature brief on 2026-08-05 whose real
    # evidence standard was stricter (every row carries a URL), and the only way to satisfy
    # the check would have been to insert a magic string. A gate that is passed by inserting
    # a magic string is worse than no gate.
    if "file:line" not in text and not re.search(r"\bURL\b|\bcite\b|citation", text, re.I):
        defects.append("brief demands no checkable evidence: require `file:line` for anything "
                       "read out of this tree, or a citation URL for a literature search")
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


def launch(task: str, brief: Path, agda: bool, sandbox: str, model: str,
           resume_id: str | None = None, note: str | None = None,
           allow_model: bool = False, case: str = "default") -> int:
    # `case` is only read by clock_defects, below, and a RESUME skips that block entirely:
    # DD17 step 6 rules that an agent already running keeps the head that was correct when
    # it was sent, and the `if resume_id is None:` guard already implements exactly that.
    # D14: a task name becomes a filename and a registry key, so `../escape` wrote outside
    # the state tree and `a/b` crashed.
    _require_vendor_or_die()
    if not SAFE_TASK.match(task):
        print(f"dispatch: refused: task name {task!r} must match {SAFE_TASK.pattern} "
              f"(no slashes, no ..)", file=sys.stderr)
        return 1

    # D3: the model refusal lives HERE, so run, queue and resume all pass through it.
    if (why := check_model(model, allow_model)):
        print(f"dispatch: REFUSED. {why}", file=sys.stderr)
        return 1

    # NOTES PRINT ON EVERY LAUNCH PATH, and this one goes here for a reason the
    # file's own history supplies. The archive NOTE was first wired into
    # cmd_check alone, so `run`, `queue` and `resume` never printed it. That is
    # the D3 defect verbatim, recorded at the top of this file: "the dead-model
    # refusal lived only in `run`, so `queue` and `resume` could still launch
    # it". A check that one entry point performs is not a check. launch() is
    # the one funnel every path crosses.
    #
    # It is a NOTE and never a defect: it must not block, because the claim
    # under test is that DD18's archive half needs no gate, and a gate would
    # destroy the evidence by making the lapse impossible.
    # D8: the queue's waiter re-reads the brief at fire time, which could have been edited
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
        # D10: never silently overwrite a dead task's record; its session id is the only
        # way to resume it and it existed nowhere else.
        prior = reg.get("dispatches", {}).get(task)
        if prior and not rec_alive(prior):
            reg.setdefault("history", []).append(prior)
        if agda and len(agda_holders(reg)) >= AGDA_SLOTS:
            held = ", ".join(agda_holders(reg))
            print(f"dispatch: the {AGDA_SLOTS} Agda slots are held by {held}. "
                  f"Use `dispatch.py queue {task} {brief}` instead of waiting by hand",
                  file=sys.stderr)
            return 1

        LOGS.mkdir(parents=True, exist_ok=True)
        stamp = time.strftime("%Y%m%d-%H%M%S")
        # D10: timestamped logs, so a re-run or a second resume never truncates the
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
            hname = herdr_name(base_task)
            kind = HERDR_KIND.get(HARNESS, "codex")
            # A herdr pane does NOT inherit this process's environment, so the
            # Agda cap has to be handed over explicitly. C-12: never raise it.
            envargs = ["--env", f"GHCRTS={AGDA_HEAP}"] if agda else []
            model_args = ["--", "-m", model] if kind == "codex" else \
                         ["--", "--provider", PI_PROVIDER, "--model", model]
            prompt_text = (note or "Resume where you left off, then write your report.") \
                          if resume_id else brief.read_text(encoding="utf-8")
            driver = (
                "set -uo pipefail\n"
                # Resolve the agent workspace by LABEL, creating it if the owner
                # closed it. Then split inside it. Never split into the owner's own.
                f"export WS=$(cat {str(HERDR_WS_FILE)!r} 2>/dev/null || true)\n"
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
                f"  BASE=$(herdr workspace create --cwd {str(ROOT)!r} "
                f"--label {HERDR_WORKSPACE_LABEL} | python3 -c \"import json,sys;"
                "r=json.load(sys.stdin)['result'];"
                f"open({str(HERDR_WS_FILE)!r},'w').write(r['root_pane']['workspace_id']);"
                "print(r['root_pane']['pane_id'])\")\n"
                "fi\n"
                "echo \"HERDR base=$BASE\"\n"
                # LEFT AND RIGHT, not top and bottom: owner's preference,
                # 2026-08-13. An agent's output is long lines of Agda and report
                # prose, so width is worth more than height.
                f"PANE=$(herdr pane split --pane \"$BASE\" --direction right "
                f"--ratio 0.5 --no-focus --cwd {str(ROOT)!r} {' '.join(envargs)} "
                "| python3 -c 'import json,sys; print(json.load(sys.stdin)[\"result\"][\"pane\"][\"pane_id\"])')\n"
                "echo \"HERDR pane=$PANE\"\n"
                # A FRESHLY SPLIT PANE IS NOT YET AN INTERACTIVE SHELL. Measured
                # 2026-08-13: `agent start` on a pane created milliseconds earlier
                # fails with agent_pane_busy, "not an available shell". The trial
                # won this race by luck. Retry on a bounded loop; `--timeout` does
                # not cover it, because herdr refuses before it starts waiting.
                "for i in 1 2 3 4 5 6 7 8 9 10; do\n"
                f"  herdr agent start {hname} --kind {kind} --pane \"$PANE\" "
                f"{' '.join(model_args)} && break\n"
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
                "{ echo \"HERDR agent never started; pane $PANE kept for forensics\"; exit 1; }\n"
                f"GOT=$(herdr agent get {hname} 2>/dev/null | python3 -c "
                "\"import json,sys;a=(json.load(sys.stdin).get('result') or {})"
                ".get('agent') or {};print(a.get('pane_id',''))\""
                " 2>/dev/null)\n"
                "if [ -n \"$GOT\" ] && [ \"$GOT\" != \"$PANE\" ]; then\n"
                f"  echo \"HERDR agent {hname} already exists in pane $GOT, not in"
                " $PANE. A run under this task code is still alive. Refusing to"
                " drive it; pane $PANE kept for forensics\"\n"
                "  exit 1\n"
                "fi\n"
                # TWO PHASE, AND ONE PHASE IS NOT ENOUGH. `--until idle` matches
                # the state the agent is ALREADY in at submission, so a one-phase
                # wait returns at once whether or not the agent ever started.
                # Measured twice on 2026-08-13, once with a bare wait and once
                # with prompt --wait. Wait for `working` FIRST, then for the stop.
                f"herdr agent prompt {hname} \"$(cat {str(brief)!r})\"\n"
                f"herdr agent wait {hname} --until working --timeout 120000 || "
                "{ echo \"HERDR agent never started working; pane $PANE kept for forensics\"; exit 1; }\n"
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
                # THE `f` PREFIX IS LOAD-BEARING AND IT WAS MISSING. Without it
                # the driver ran `herdr agent get {hname}` literally, which
                # cannot resolve, so `grep -q` never matched and this whole
                # blocked-detection branch was unreachable. A pause for approval
                # was then filed as a not-stopped run for the full retry loop.
                # MEASURED 2026-08-15 by `[LJ-1.303]`, with `ast`: it was the
                # ONLY plain string literal in this file carrying a placeholder.
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
                f"herdr agent read {hname} --source recent --lines 400 > {str(final)!r} 2>&1\n"
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
                "herdr pane close \"$PANE\" >/dev/null 2>&1\n"
                "echo \"HERDR done pane=$PANE closed\"\n"
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
                f"herdr agent read {hname} --source recent --lines 400 > {str(final)!r} 2>&1\n"
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
                      "--provider", PI_PROVIDER, "--model", model]
            if resume_id:
                pi_cmd += ["--session", resume_id]
            pi_cmd.append(prompt)
            cmd = [sys.executable, str(PI_STREAM), "--events", str(events),
                   "--final", str(final), "--"] + pi_cmd
        elif resume_id:
            # D18: the -resume suffix is applied in exactly one place now.
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
            env["GHCRTS"] = AGDA_HEAP

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
                                        cwd=ROOT, env=env, start_new_session=True)
        except OSError as exc:
            # D13: a missing codex binary used to be a raw traceback.
            print(f"dispatch: could not launch: {exc}", file=sys.stderr)
            return 1

        reg = load()
        reg.setdefault("dispatches", {})[task] = {
            "pid": proc.pid, "proc_start": proc_start(proc.pid), "brief": str(brief),
            "agda": agda, "sandbox": sandbox, "model": model, "log": str(log),
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

    # D13: never report a launch as successful when the process is already gone. That is
    # the exact shape of failure mode 1 and it used to print "away" and exit 0.
    if dead_early and proc.returncode != 0:
        print(f"dispatch: {task} EXITED IMMEDIATELY (rc {proc.returncode}). This is the "
              f"silent-death shape: read {log} for the reason.", file=sys.stderr)
        return 1
    print(f"dispatch: {task} away, pid {proc.pid}, "
          f"session {session or '(not printed yet; resume rescans the log)'}")
    print(f"          log {log}")
    print(f"          ARM THE NOTIFIER: dispatch.py wait, as a harness-tracked background "
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
                  f"on disk. Consider `dispatch.py resume {task}`.")
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
    rc = launch(a.task, brief, a.agda, a.sandbox, a.model, allow_model=a.allow_model,
                case=case_from_args(a))
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
    # D9: refuse a colliding name HERE, not later inside a detached waiter whose log the
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
    script = (
        f"import sys, time\n"
        f"sys.path.insert(0, {here!r})\n"
        f"import dispatch as D\n"
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
        f"        free = (not {a.agda!r}) or len(D.agda_holders(reg)) < D.AGDA_SLOTS\n"
        f"    clash = D.territory_in_flight(D.Path({str(brief)!r}), {a.task!r})\n"
        f"    if free and not clash: break\n"
        f"    time.sleep(30)\n"
        f"rc = D.launch({a.task!r}, D.Path({str(brief)!r}), {a.agda!r}, {a.sandbox!r}, "
        f"{a.model!r}, resume_id={resume_id!r}, note={note!r}, allow_model={a.allow_model!r}, "
        # The QUEUE fires LATER, so the clock may have turned between this command and the
        # launch. The case is pinned here and clock_defects re-reads the clock at fire time,
        # which is the behaviour we want: a queued default-case dispatch that would land in
        # a peak window is refused AT THE LAUNCH, not waved through because it was queued
        # off-peak. D8 already re-validates the brief at fire time for the same reason.
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
    print(f"          ARM THE NOTIFIER: dispatch.py wait, as a harness-tracked background "
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
    except OSError:
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
        # D11: the scrape is bounded, so rescan the log before refusing. The id was often
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
    return launch(f"{a.task}-resume", Path(d.get("brief", "")), d.get("agda", False),
                  d.get("sandbox", "workspace-write"), d.get("model", DEFAULT_MODEL),
                  resume_id=session, note=a.note, allow_model=a.allow_model)


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
        # [LJ-1.303] 2026-08-15: THE SAME DEFECT, ONE HOME LATER. The reports
        # moved out of `_build/` into `agents/tasks/<CODE>/` on 2026-08-14, and
        # this derivation still looked only in `_build/`. MEASURED: `_build/`
        # holds NO `*report*.md` at all today, so the quiet-deliverable half was
        # dead for every live task, exactly as [LJ-1.127] found it dead for the
        # retired series. The task directory is tried FIRST, and the two old
        # shapes are kept because an old record still names them.
        for cand in (ROOT / "agents" / "tasks" / task.upper().replace(".", "-")
                     / f"{task.lower()}-report.md",
                     ROOT / "_build" / f"{task.lower()}-report.md",
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



def unregistered_returns() -> list[tuple[str, str]]:
    """Tasks the waiter ANNOUNCED whose PLAN row still says DISPATCHED.

    [L3.32-T208] 2026-08-08 is why this exists. T208 and T209 returned in the
    SAME announcement, at the same second. T209 was audited and registered;
    T208 was dropped, and its row sat on DISPATCHED for a day with a complete
    report on disk. The owner found it, not the tooling.

    The existing alarm could not: it fires on `not reported`, meaning a return
    no waiter ever announced. T208 WAS announced, so it was invisible to that
    check by construction. 140 of 145 announcements carried exactly one return,
    which is why an audit loop keyed on the ANNOUNCEMENT rather than on each
    TASK inside it looked correct until the day one carried two.
    """
    plan = ROOT / "dev" / "PLAN.md"
    if not plan.exists():
        return []
    text = plan.read_text(encoding="utf-8")
    out = []
    for name, d in load().get("dispatches", {}).items():
        if not d.get("reported") or rec_alive(d):
            continue
        # [LJ-1.127] TWO SERIES, AND ONLY THE RETIRED ONE WAS MATCHED. The row
        # id for the live series is `| LJ-1.126 |`, never `| L3.32-LJ-1.126 |`,
        # so this alarm has reported all-clear for every dispatch since
        # 2026-08-09 while being unable to see a single one of them. That is the
        # exact failure it was built to catch, in the checker itself.
        m = re.search(r"^\| (?:L3\.32-)?" + re.escape(name.upper())
                      + r" \| [^|]*\| ([^|]*)\|", text, re.M | re.I)
        if m and m.group(1).strip().upper().startswith("DISPATCHED"):
            out.append((name, m.group(1).strip()[:60]))
    return sorted(out)


def cmd_status(a) -> int:
    reg = load()
    live = running(reg)
    holders = agda_holders(reg)
    print(f"Agda slots: {len(holders)}/{AGDA_SLOTS} held" +
          (f" by {', '.join(holders)}" if holders else ""))
    print(f"agents live: {len(live)}")
    now = time.time()
    items = sorted(reg.get("dispatches", {}).items())
    for t, d in items:
        is_live = rec_alive(d)
        # Every record prints, live or not: an exited agent with no final message IS
        # the signal this census exists for.
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

    # D5 (T73): the old filter keyed on the year and would have silently stopped alarming on
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

    if (unreg := unregistered_returns()):
        print()
        print(f"!! {len(unreg)} ANNOUNCED RETURN(S) NEVER REGISTERED in dev/PLAN.md:")
        for name, v in unreg:
            print(f"   {name}: the row still reads {v!r}")
        print("   These were announced and then dropped at audit. [T208] sat like this")
        print("   for a day with a finished report on disk. Register the verdict now.")

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
            print("   Run `dispatch.py status --sweep-panes` to close them. "
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
        print("       python3 .claude/skills/codex-dispatch/dispatch.py wait")


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

    # MEASURED DEFECT, 2026-08-06: the orchestrator armed `wait --all` on EVERY
    # dispatch of the session and lost four returns to it. --all blocks until the
    # SLOWEST agent finishes, so a fast return sits unnoticed behind a slow one:
    # T97 and T98 returned and sat while T96 kept running. The flag's help text
    # already said "PREFER THE DEFAULT" in capitals and that changed nothing,
    # which is this file's founding lesson: documentation is advice at the moment
    # of writing a command, and this script IS the command. So it refuses.
    if a.all and len(watched) > 1:
        print(f"dispatch: REFUSED. `wait --all` blocks until the SLOWEST of "
              f"{len(watched)} agents ({', '.join(sorted(watched))}) finishes, so "
              f"every earlier return sits unnoticed behind it. That is how four "
              f"returns were lost on 2026-08-06.")
        print("dispatch: use plain `wait` (it reports the FIRST return, then you "
              "re-arm), or `wait --all` only when exactly one agent is live.")
        return 2

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
            # D3 (T73): adopting only LIVE records missed an agent that was dispatched after
            # this waiter began and died inside one 15 s tick: never watched, never
            # announced, never flagged. Adopt any unreported record we have not seen.
            #
            # `reported` IS WHAT KEEPS OLD NEWS OUT, and that rule is measured.
            # MEASURED DEFECT, 2026-08-06: a freshly armed waiter re-announced T117,
            # a return audited half an hour earlier, treated that as its one report
            # and exited, leaving the live agent it was armed for unwatched. A
            # waiter must not spend its single report on old news. A second reader
            # of returns.log, `already_announced()`, was written for the same rule
            # and had NO CALLER, so it enforced nothing; [LJ-1.303] removed it
            # 2026-08-15 and the rule lives on this line.
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
    #
    # ONE WRITER, NOT TWO. This was `announce()`'s body written out a second time,
    # line for line. `announce()`'s own docstring records the session where the two
    # report paths disagreed and ten returns went unlogged, which is the defect a
    # second copy re-opens. [LJ-1.303], 2026-08-15.
    announce(done)
    print(f"dispatch: {len(done)} agent(s) RETURNED after "
          f"{int(time.time() - start)}s: {', '.join(sorted(done))}")
    for t, d in sorted(done.items()):
        final = Path(d.get("final", ""))
        if final_is_clean(final):
            print(f"  {t}: finished cleanly, final message {final}")
        else:
            print(f"  {t}: NO FINAL MESSAGE, so it was killed or ran out of budget. "
                  f"Its work may still be on disk. Consider `dispatch.py resume {t}`.")
        print(f"       log {d.get('log')}")
    still = [t for t in watched if t not in done]
    if still:
        print(f"dispatch: {len(still)} agent(s) STILL RUNNING and now UNWATCHED: "
              f"{', '.join(sorted(still))}")
        print(f"dispatch: RE-ARM NOW, or their returns will sit unnoticed. "
              f"One waiter reports once; that is the whole contract.")
    return 0


def cmd_gate_ready(a) -> int:
    """Refuse a full-tree gate while any agent is live.

    Measured 2026-08-05: a full `agda src/Everything.lagda.md` was run while an agent was
    mid-write on a master, and it failed on a name that agent had not finished introducing.
    The result LOOKED like a red gate on the change being audited, and it was nothing of the
    kind. The dangerous half of this is the other one: had the half-written file happened to
    parse, the run would have gone GREEN over content nobody had finished writing.

    ORCHESTRATION section 4 already forbids a tree-wide WRITE while agents hold territory.
    This is the same hazard on the read side, and it needed its own check."""
    live = running(load())
    if not live:
        print("dispatch: no agent is live; a full-tree gate will read a settled tree")
        return 0
    print(f"dispatch: DO NOT run a full-tree gate now. {len(live)} agent(s) are live "
          f"({', '.join(sorted(live))}) and may be mid-write on a master. A gate run now "
          f"reads half-written files: a spurious failure at best, a spurious GREEN at worst. "
          f"Wait with `dispatch.py wait`, and re-arm after each return: `--all` is refused while more than one agent is live, so it cannot be the recovery from this state.", file=sys.stderr)
    return 1


def dd4_defects(brief: Path) -> list[str]:
    """Refuse a brief that does not carry DD4, whatever its kind.

    WHY THIS IS A REFUSAL. DD4 is the route's CORE constraint, maximize the
    code the two proofs share, and the owner ruled it gets no threshold and no
    pass-or-fail: a shared-line count is gamed the moment it gates anything.
    So DD4's ONLY enforcement is that it is stated in every brief and answered
    in every return.

    [LJ-0.3] then named the obvious risk: this project has run that exact
    mechanism before and it drifted. An imported playbook sat uncited in 102
    of 112 briefs for five days, which is the failure the function below this
    one exists to prevent. A rule whose enforcement is "the orchestrator will
    remember" is a wish, and DD4 is too important to leave as one.

    THIS GATES THE BRIEF, NOT THE CODE. Nothing here measures reuse or judges
    an architecture; that stays a human question by ruling. All this refuses
    is a brief that forgot to ask it.
    """
    text = brief.read_text(encoding="utf-8")
    if re.search(r"(?<![\w-])DD4(?![\w-])", text):
        return []
    # A brief may satisfy DD4 by stating it rather than citing the code, so
    # accept the rule's own words too. Both halves must appear: the sharing
    # objective and the generic discipline are one rule seen from two ends.
    shares = re.search(r"code the two proofs share|maximum reuse|maximize .{0,20}shar",
                       text, re.I)
    generic = re.search(r"write it generic|structure-generic|generic carrier", text, re.I)
    if shares and generic:
        return []
    return ["brief does not carry DD4. It is the route's core constraint and it "
            "has NO metric and no checker by the owner's ruling, so being stated "
            "in every brief IS its enforcement. Add both halves: maximize the "
            "code the two proofs share, and write it generic. This is a refusal "
            "because the same mechanism already drifted once, uncited in 102 of "
            "112 briefs over five days."]


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
    """
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


def rule_bundle_defects(brief: Path) -> list[str]:
    """Refuse a brief that does not carry its kind's mandatory rule bundle.

    WHY THIS IS A REFUSAL AND NOT A REMINDER. The alternative, tried on
    2026-08-06, was a sentence in dev/ORCHESTRATION.md telling the orchestrator
    to name the new laws in every brief. AGENTS.md says a rule whose
    enforcement point is a person's intention is a wish, and the orchestrator
    is precisely the component that drifted for five days while an entire
    imported playbook sat uncited in 102 of 112 briefs.

    The KIND IS DERIVED from the brief's write scope, never read from a
    self-declared field: [L3.32-T105] pointed out that an author who declares
    the kind chooses the bundle.
    """
    text = brief.read_text(encoding="utf-8")
    # THE PATH MOVED AND THIS REFUSAL WENT SILENT. `[LJ-1.295]` moved `rules.py`
    # into `scripts/dispatch/` on 2026-08-15. This line still named
    # `scripts/rules.py`, and the `exists()` guard below then returned NO
    # DEFECTS for every brief, so the mandatory-bundle refusal was disarmed the
    # moment the file moved. MEASURED 2026-08-15 by `[LJ-1.303]`: a brief citing
    # ZERO mandatory rules passed `dispatch.py check` clean.
    #
    # THE GUARD IS THE HAZARD, not the path. A missing checker that returns
    # "no defects" is C-40's shape and this file's own founding lesson. So the
    # absence is now REPORTED instead of waved through.
    rules_py = ROOT / "scripts" / "dispatch" / "rules.py"
    if not rules_py.exists():
        return [f"the rule table is missing: {rules_py} does not exist, so the "
                f"mandatory-bundle refusal cannot run. It was disarmed exactly "
                f"this way once, when `[LJ-1.295]` moved the file and this line "
                f"kept the old path. Restore it or fix this path; do not "
                f"dispatch on an unchecked bundle."]
    kind = brief_kind(text)

    out = subprocess.run([sys.executable, str(rules_py), "--for", kind],
                         capture_output=True, text=True)
    if out.returncode != 0:
        return []
    wanted = re.findall(r"^- \*\*((?:Rule \d+)|(?:P-[a-z])|(?:[RTIDC]-\d+))",
                        out.stdout, re.M)
    missing = [r for r in wanted if not re.search(
        r"(?<![\w-])" + re.escape(r) + r"(?![\w-])", text)]
    if not missing:
        return []
    return [f"brief is kind `{kind}` (derived from its write scope) and does "
            f"not cite {len(missing)} mandatory rule(s): {', '.join(missing)}. "
            f"Run `python3 scripts/dispatch/rules.py --for {kind}` and paste the bundle "
            f"into SCOPE (read). This is a refusal, not a reminder: the "
            f"orchestrator's memory is what drifted."]


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
        sp.add_argument("--harness",
                        choices=("herdr", "herdr-pi", "codex", "pi"), default=HARNESS,
                        help="herdr runs a CODEX agent in a server-owned pane and "
                             "herdr-pi runs a PI agent in one, so `herdr agent "
                             "list|attach|wait` see either from any terminal; codex "
                             "is the old direct-exec path; pi runs the pi CLI direct "
                             "through pi_stream.py. THE DEFAULT COMES FROM "
                             "scripts/dispatch/dispatch_policy.py and follows the "
                             "policy "
                             "version in force")
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
    if POLICY_ERROR:
        print(f"dispatch: WARNING: {POLICY_ERROR}", file=sys.stderr)
    return {"run": cmd_run, "queue": cmd_queue, "resume": cmd_resume,
            "status": cmd_status, "check": cmd_check, "wait": cmd_wait,
            "gate-ready": cmd_gate_ready}[a.cmd](a)


if __name__ == "__main__":
    sys.exit(main())
