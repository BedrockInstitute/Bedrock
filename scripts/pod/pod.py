#!/usr/bin/env python3
"""The POD runner: the tick, the state, the transition log and the five subcommands.

WHY THIS FILE EXISTS. The old flow ran on an orchestrator's attention. It read a report,
decided what the report meant, and wrote the next brief. Two measurements on 2026-08-16
priced that: `[LJ-1.375]` found a verdict LINE that disagreed with its own BODY, and
`[LJ-1.376]`'s audit named the orchestrator's own unread live record the costliest defect
in the tree. This file reads no report. It measures six facts, matches one table, and
performs one of eight actions, and every step it takes is one line in a TRACKED log.

THE SIX RULES THAT COST THE MOST IF THEY ARE DROPPED
(`dev/memos/L9-pod-program-design.md` section 5):

- **The log line is written FIRST, then the state file.** The tracked log is the truth and
  `.pod-state/state.json` is a cache of its fold. A lost state file is recoverable from
  the log; a lost log line is recoverable from nothing. `emit()` writes in that order
  under one lock and fsyncs both.
- **The stop stops DISPATCHING and never touches a running worker.** On 2026-08-05 two
  live agents died because somebody stopped the watcher shell that had launched them into
  its own process group (`scripts/pod/launcher.py:7-9`). Rule (f) is the only rule the
  stop refuses; rules (a1) to (e) keep running, so work that already returned is still
  observed and closed. The stated consequence: the PARKED count can pass 3 after the stop.
- **`attempt_max` bounds the four looping actions.** `route()` is pure, so a retry that
  changes nothing reproduces the same record, the same row matches, and the task cycles
  for ever. The cap parks it naming the row that kept matching, because that is a design
  error in the ROW and not in the task.
- **`admits()` REFUSES on the Agda pile-up rather than printing about it.** On 2026-08-12
  one agent held six Agda processes at once, each at the 8 GB cap: 48 GB of worst case on
  a 64 GB machine and a load average of 19. The OWNER saw it; no tool did.
  `agda_pileup()` in `scripts/pod/launcher.py` had ONE consumer and it only printed.
- **THE PROGRAM OWNS THE WATCHDOG (A13), and the tiers are C-12's (A14).**
  `dev/LESSONS.md` C-12 says restart `scripts/ops/agda-watchdog.sh` at every session, and
  THE POD HAS NO SESSION, so before A13 nothing started it. MEASURED 2026-08-17: it was
  not running. `pod run` starts it, `watchdog_tick()` confirms it every tick, and
  `admits()` refuses every Agda task while it is down. A14 restores the two tiers with it:
  WIDE admits four concurrent Agda writers at `-M8g`, HEAVY admits two at `-M12g`, the
  mixed worst-case heap sum stays at or under 32 GB, and slots three and four open only
  above 25 percent free memory.
- **AN IDLE SLOT IS CURED, NOT REPORTED (A11).** Rule (g) dispatches the mathematician
  with the standing brief `dev/pod/instructions/refill-queue.md` when a slot is free and
  the queue holds no dispatchable entry. The program decides only that somebody must be
  asked; the head decides the work, so AD1 holds.

WHAT THIS FILE DOES NOT DO. It never judges. It never writes a brief, never writes a
table row, never reads prose and never asks a model anything. `scripts/pod/table.py`
routes, `scripts/pod/accept.py` measures, `scripts/pod/preflight.py` refuses a malformed
brief, and the mathematician holds every judgement (AD1, AD3).

IT REFUSES; IT NEVER RAISES. The loop runs UNATTENDED, so a traceback stops everything
and nobody reads it. Every reader of a file, a log line, a process table or a numeric
field treats a malformed value as ABSENT and takes the refusing direction, which is the
one FM12 names: a blind sensor never admits.

Usage:
  pod.py run          the sleep loop: tick, sleep `tick_seconds`, repeat until STOP
  pod.py tick         one pass, then exit. This is the testable unit and `run` calls it
  pod.py resume       clear `.pod-state/STOPPED`, re-evaluate every PARKED task, then run
  pod.py status       print the state file as a table. It writes nothing
  pod.py stop         write `.pod-state/STOPPED`, wait for every RUNNING worker, then
                      commit the tracked table and log
Exit status: 0 clean; 1 the loop stopped, a command refused, or the run failed; 2 a
usage error, which is an unknown or absent subcommand and nothing else.
"""

from __future__ import annotations

import contextlib
import datetime
import fcntl
import json
import os
import re
import signal
import subprocess
import sys
import time
import tomllib
from pathlib import Path

# LJ-1.291 and LJ-1.295: the root is found by walking up to the repository marker, never
# by counting directories. The group directory joins sys.path for siblings imported by
# bare name, and the scripts root is found by walking up to `repo_root.py` itself.
_HERE = Path(__file__).resolve()
sys.path.insert(0, str(_HERE.parent))
_SCRIPTS = next((p for p in _HERE.parents if (p / "repo_root.py").is_file()), None)
if _SCRIPTS is None:
    raise FileNotFoundError(
        f"no repo_root.py above {_HERE}: refusing to guess the scripts root (C-43)")
sys.path.insert(0, str(_SCRIPTS))
from repo_root import find_root  # noqa: E402

import agents_tree  # noqa: E402
import accept as accept_mod  # noqa: E402
import facts as facts_mod  # noqa: E402
import heads as heads_mod  # noqa: E402
import preflight as preflight_mod  # noqa: E402
import table as table_mod  # noqa: E402
import witness as witness_mod  # noqa: E402

ROOT = find_root(__file__)

# ---------------------------------------------------------------- where everything lives

#: Section 4.0. NOT `_build/`: the `clean:` target of the `Makefile` empties it, so
#: `make clean` would erase the runtime state of a live loop.
POD_STATE = ROOT / ".pod-state"
STATE_FILE = POD_STATE / "state.json"
STOPPED_FILE = POD_STATE / "STOPPED"
LOG_DIR = POD_STATE / "logs"
LOCKFILE = POD_STATE / "pod.lock"

#: Tracked, append only, ONE FILE PER MONTH. At about 124 KB per median day (5.3.1),
#: monthly rotation holds any git blob under 11 MB.
TRANSITIONS = ROOT / "dev" / "pod" / "transitions"
QUEUE = ROOT / "dev" / "pod" / "queue.toml"
TABLE = ROOT / "dev" / "pod" / "table.toml"
CORPUS = ROOT / "dev" / "pod" / "replay-corpus.jsonl"
PROPOSALS = ROOT / "dev" / "pod" / "proposals"
INSTRUCTIONS = ROOT / "dev" / "pod" / "instructions"
WATCHDOG = ROOT / "scripts" / "ops" / "agda-watchdog.sh"
BARK = ROOT / "scripts" / "ops" / "bark-push.sh"
DIGEST = ROOT / "scripts" / "pod" / "digest.py"

#: R18's one automatic scope path. A task that writes a NEW master must also wire it, or
#: acceptance conjunct 3 refuses the return the task itself caused. `laws_bundle()` builds
#: R17's producer path the same way, from the caller's root, so a test root works too.
EVERYTHING = "src/Everything.lagda.md"

#: Amendment A11's standing brief, rule (g). THE ORCHESTRATOR WRITES IT AND THE PROGRAM
#: NEVER DOES: AD3 gives every brief to the mathematician, so an absent file is a named
#: dependency and one recorded refusal, never a brief this file invents.
REFILL_BRIEF = ROOT / "agents" / "tasks" / "POD-REFILL" / "POD-REFILL.md"

#: Rule (g)'s dispatch name. It is not a task: it holds no state record, exactly like
#: AD15's `POD-BATCH`, because its return is READ OUT OF `dev/pod/queue.toml` by rule
#: (a1) on the next tick and never routed through the table.
REFILL_TASK = "POD-REFILL"

#: The floor between two rule (g) dispatches, in hours. A mathematician that queues
#: NOTHING is a legal return (the standing brief says so), so without a floor an empty
#: queue would dispatch one refill every `tick_seconds`. `dev/pod/heads.toml` names no
#: key for it and this program may not edit that file, so the owner's key WINS when it
#: appears: `_refill_min_hours()` reads `[limits].refill_min_hours` first.
REFILL_MIN_HOURS = 1.0

#: A14's two tiers, C-12's own. WIDE is four concurrent Agda writers at `-M8g`, HEAVY is
#: two at `-M12g`, and `dev/pod/heads.toml` `[tiers]` holds both numbers.
#:
#: THE VOCABULARY HAS ONE HOME AND IT IS `facts.TASK_TIERS`, because `run_agda()` turns
#: the name into a caliber: a second spelling here would be a second memory cap.
TIERS = tuple(facts_mod.TASK_TIERS)
WIDE = facts_mod.DEFAULT_TIER
HEAVY = next((x for x in TIERS if x != WIDE), WIDE)

#: Six states. Twelve transitions. Nothing else is legal (section 5.2).
READY, RUNNING, RETURNED, CHECKING, DONE, PARKED = (
    "READY", "RUNNING", "RETURNED", "CHECKING", "DONE", "PARKED")
STATES = (READY, RUNNING, RETURNED, CHECKING, DONE, PARKED)

#: The twelve legal transitions, as (from, to). `NONE` is the creation edge of rule (a1).
NONE = None
TRANSITIONS_LEGAL = {
    (NONE, READY),          # 1  a queue entry, rule (a1)
    (READY, RUNNING),       # 2  launch() returned a pid
    (RUNNING, RETURNED),    # 3, 3b  rec_alive() is false, or the deadline passed
    (RETURNED, CHECKING),   # 4  the acceptance runner started
    (CHECKING, DONE),       # 5  a done row matched and R4 holds for its outcome
    (CHECKING, READY),      # 6  a row matched and its action retries or escalates
    (CHECKING, PARKED),     # 7, 11 no match, park, R7, attempt_max, R4, or stop_loop
    (READY, PARKED),        # 8  pre-flight, admission or launch refused
    (PARKED, READY),        # 9, 10 the table changed, or the brief was repaired
}

#: The nine park reasons of section 5.5. Each NAMES its cause and rule (a2) branches on
#: it. `no-match` is the ONE reason AD7's first number counts, so its string is exact.
PARK_REASONS = ("no-match", "no-change", "preflight:", "attempt_max:", "r4",
                "admission", "launch", "row:", "stop_loop:")

#: `pod_tick()` returns one of these. Only `stop_loop` and rule (d) return STOP.
CONTINUE, STOP = "CONTINUE", "STOP"

#: The FOUR looping actions, and `attempt_max` covers these and no others (section 5.1).
#: Each one returns the task to READY, so `route()` being pure means the same record
#: reproduces and the same row wins for ever. `park`, `park_and_split` and `stop_loop`
#: never return to READY, so they cannot loop and the cap must not touch them.
LOOPING = ("accept", "escalate", "redispatch", "redispatch_narrower")

#: The log record's `to` value for the loop's own line. It carries `task: ""`, and rule
#: (d) and `apply()` are its two writers.
LOOP_STOPPED = "STOPPED"


class PodError(Exception):
    """The loop cannot proceed and nothing is guessed. Every raise names its reason."""


# ---------------------------------------------------------------- the lock


@contextlib.contextmanager
def pod_lock():
    """ONE RUNNER AT A TIME, and the same `flock` shape `registry_lock()` uses.

    It takes a SEPARATE lock file, exactly as `registry_lock()` at
    `registry_lock()` in `scripts/pod/launcher.py` does, so a corrupt state file cannot also break locking.
    Both writes of section 5.3 sit inside it: without one lock, two ticks racing for the
    last Agda slot both dispatch, which is the measured defect FM1 records.
    """
    POD_STATE.mkdir(parents=True, exist_ok=True)
    LOG_DIR.mkdir(parents=True, exist_ok=True)
    with open(LOCKFILE, "a+") as fh:
        fcntl.flock(fh, fcntl.LOCK_EX)
        try:
            yield
        finally:
            fcntl.flock(fh, fcntl.LOCK_UN)


# ---------------------------------------------------------------- the state record


#: The 12 fields that carry over unchanged from the dispatch registry (section 5.2).
#: `session` and `resumed_from` are DROPPED, because AD16 resumes by a fresh instance.
CARRIED = ("pid", "proc_start", "brief", "agda", "sandbox", "model", "log", "final",
           "started", "harness", "events", "reported")

#: The 14 fields the POD adds, plus `unbound_before` and `tier`. BOTH EXTRAS ARE
#: DISCLOSED rather than smuggled. Section 5.2 lists fourteen; section 5.4 then reads
#: `t.unbound_before` for conjunct 4, so a task carrying only the fourteen cannot run its
#: own acceptance test, and the field is the pre-flight's finding SET, carried and never
#: re-derived at the return. `tier` is amendment A14's: `admits()` counts slots and heap
#: PER TIER, and a record carries its tier so two measurements are compared only inside
#: one tier. Both are copied ONCE, at creation, exactly as `exclusive` is.
ADDED = ("status", "role", "effort", "exclusive", "attempt", "predecessor", "run",
         "record", "obl_before", "row", "park_reason", "parked_at", "head_slot",
         "scope_narrow", "unbound_before", "tier")

FIELDS = CARRIED + ADDED


class Task:
    """One task. `t.code` is the map KEY and never a field, exactly as section 5.2 rules.

    ONE STATE RECORD PER CODE. A review is a second DISPATCH and not a second task: `role`
    names which head is live and `attempt` counts the instances. Two records under one
    code would also hit the launcher's own duplicate refusal.
    """

    def __init__(self, code, **kw):
        self.code = code
        for f in FIELDS:
            setattr(self, f, kw.get(f))
        if self.status is None:
            self.status = READY
        if self.attempt is None:
            self.attempt = 0
        if self.agda is None:
            self.agda = True
        if self.exclusive is None:
            self.exclusive = False
        if self.reported is None:
            self.reported = False
        if self.tier not in TIERS:
            # A14. An ABSENT declaration is WIDE, because `-A64m -I0 -M8g` is the caliber
            # `run_agda()` really sets, so WIDE is the true worst case and not an
            # optimistic one. A declaration that is PRESENT and unreadable is a different
            # case and `task_tier()` takes the conservative tier there.
            self.tier = WIDE

    def to_dict(self):
        return {f: getattr(self, f) for f in FIELDS}

    @classmethod
    def from_dict(cls, code, d):
        return cls(code, **{f: d.get(f) for f in FIELDS})

    def elapsed(self, now=None):
        """Wall seconds since the dispatch, or 0.0 when the task never started.

        It reads `started`, the one field `launch()` writes at the dispatch. A task with
        no `started` has not run, so a deadline can never fire on it.
        """
        if not self.started:
            return 0.0
        try:
            t0 = time.mktime(time.strptime(self.started, "%Y-%m-%d %H:%M:%S"))
        except (ValueError, TypeError):
            return 0.0
        return max(0.0, (time.time() if now is None else now) - t0)

    def registry_record(self):
        """The shape `rec_alive()` in `scripts/pod/launcher.py` reads."""
        return {"pid": self.pid or 0, "proc_start": self.proc_start or ""}


class State:
    """`.pod-state/state.json`, a cache of the log's fold. Version 1."""

    def __init__(self, seq=0, stopped=None, tasks=None):
        self.seq = _int(seq, 0)            # a non-numeric seq is ABSENT, never a crash
        self.stopped = stopped
        self.tasks = tasks or {}

    def to_dict(self):
        return {"version": 1, "seq": self.seq, "stopped": self.stopped,
                "tasks": {c: t.to_dict() for c, t in self.tasks.items()}}

    def count(self, status):
        return sum(1 for t in self.tasks.values() if t.status == status)

    def of(self, status):
        """Every task in one state, in code order, so a tick is reproducible."""
        return [self.tasks[c] for c in sorted(self.tasks) if self.tasks[c].status == status]


def load_state(path=None):
    """The state cache. A missing, unreadable or MALFORMED file gives an EMPTY state, and
    the log then rebuilds it: that is crash window one and it is the designed, safe window.

    IT NEVER RAISES. The file is a cache, so the worst a bad one costs is one fold of the
    tracked log, while a raise here stops an unattended loop at start-up. A JSON document
    that parses but is not an object, a `tasks` value that is not an object, a task record
    that is not an object and a non-numeric `seq` are each treated as absent.
    """
    p = STATE_FILE if path is None else Path(path)
    try:
        data = json.loads(p.read_text(encoding="utf-8"))
    except (OSError, ValueError):          # ValueError covers JSONDecodeError
        return State()
    if not isinstance(data, dict):
        return State()
    raw = data.get("tasks")
    tasks = {}
    if isinstance(raw, dict):
        for c, d in raw.items():
            if isinstance(c, str) and isinstance(d, dict):
                tasks[c] = Task.from_dict(c, d)
    return State(_int(data.get("seq"), 0), data.get("stopped"), tasks)


def _int(value, default=None):
    """One field as an int, or `default`. A NON-NUMERIC FIELD IS ABSENT AND NEVER A ZERO.

    A hand-edited log line, a torn write and an older schema all produce a field of the
    wrong type, and `int("x")` raises where the loop cannot recover. `True` is refused
    with the strings, because a boolean is not a count.
    """
    if isinstance(value, bool) or not isinstance(value, (int, float, str)):
        return default
    try:
        return int(value)
    except (TypeError, ValueError):
        return default


def save_state(st, path=None):
    """tmp -> fsync -> rename -> fsync(dir). BOTH fsyncs, and m6 is why.

    `save()` in `scripts/pod/launcher.py` renames a temporary file with NO `os.fsync`,
    which is atomic against a process crash and not durable against a machine crash. The
    rename orders the two writes; only the fsyncs make the bytes survive a power cut.
    """
    p = STATE_FILE if path is None else Path(path)
    p.parent.mkdir(parents=True, exist_ok=True)
    tmp = p.with_suffix(".tmp")
    try:
        with open(tmp, "w", encoding="utf-8") as fh:
            json.dump(st.to_dict(), fh, indent=1, sort_keys=True, default=str)
            fh.flush()
            os.fsync(fh.fileno())          # FSYNC ONE: the bytes of the new state
        tmp.replace(p)
        dfd = os.open(p.parent, os.O_RDONLY)
        try:
            os.fsync(dfd)                  # FSYNC TWO: the rename itself
        finally:
            os.close(dfd)
    except OSError as e:
        # A FULL OR READ-ONLY DISK IS A REFUSAL WITH A REASON, never a traceback. The log
        # line is already durable at this point, so the fold recovers the transition; what
        # is lost is only the cache, which is crash window one.
        raise PodError(f"cannot write {p}: {e}") from e


# ---------------------------------------------------------------- the transition log


def log_path(when=None, root=None):
    """`dev/pod/transitions/<YYYY-MM>.jsonl`. MONTHLY ROTATION, and 4.0 measured why.

    At about 124 KB per median day and 210 KB at the peak, a month is about 3.7 MB, so a
    monthly file holds any git blob well under 11 MB. A single file would not.
    """
    root = ROOT if root is None else Path(root)
    when = when or datetime.datetime.now(datetime.timezone.utc)
    return root / "dev" / "pod" / "transitions" / f"{when:%Y-%m}.jsonl"


def log_files(root=None):
    """Every monthly file, oldest first. The fold reads them in that order."""
    root = ROOT if root is None else Path(root)
    d = root / "dev" / "pod" / "transitions"
    return sorted(d.glob("*.jsonl")) if d.is_dir() else []


def log_lines(root=None, since=0):
    """Every log line with `seq` above `since`, in seq order. A bad line is SKIPPED.

    A line that does not parse is not a reason to lose every line after it: the log is
    append only and one torn tail write is the shape a crash makes.

    THREE SHAPES ARE SKIPPED AND NOT ONE. A line that is not JSON, a line whose JSON is
    not an object, and a line whose `seq` is not a number. `int("x")` raised here before,
    and the raise ran inside `replay_log()` at the top of every tick, so ONE hand-edited
    character in a TRACKED file stopped the whole unattended loop.
    """
    out = []
    for f in log_files(root):
        try:
            text = f.read_text(encoding="utf-8")
        except OSError:
            continue
        for line in text.split("\n"):
            if not line.strip():
                continue
            try:
                rec = json.loads(line)
            except ValueError:             # ValueError covers JSONDecodeError
                continue
            if not isinstance(rec, dict):
                continue
            seq = _int(rec.get("seq"))
            if seq is not None and seq > since:
                out.append(rec)
    out.sort(key=lambda r: _int(r.get("seq"), 0))
    return out


def replay_log(st, root=None):
    """Apply every log line with `seq` greater than the state's. Crash window one.

    THE LOG IS THE TRUTH AND THE STATE IS ITS FOLD. The line carries the routable half of
    the record, which is what section 4.5.1 reads: `task`, `concurrency` and `caliber` at
    the top level and the six facts nested. The whole record, with its `conjuncts`, lives
    in the state file only, and rule (c) always reads a FRESH one, so no routing decision
    ever depends on the half the fold cannot restore.

    EVERY FIELD IS CHECKED BEFORE IT IS FOLDED, and a field of the wrong type is ABSENT.
    A line whose `to` is not one of the six states moves no task, because `cmd_status()`
    formats `status` and `route()` compares it; a `facts` object that is not a complete
    six-fact record is dropped, because `matches()` INDEXES the six keys and a partial one
    raised `KeyError` inside rule (a2). A tracked file that any agent may edit is exactly
    where a malformed line comes from.
    """
    for line in log_lines(root, st.seq):
        st.seq = max(st.seq, _int(line.get("seq"), 0))
        code = line.get("task") or ""
        if not isinstance(code, str):
            continue                                   # a task key is a string or nothing
        to = line.get("to")
        if not code:                                   # the loop's own line
            st.stopped = line.get("ts") if to == LOOP_STOPPED else None
            continue
        if to is not None and to not in STATES:
            continue                                   # not a transition this loop wrote
        t = st.tasks.get(code) or Task(code)
        st.tasks[code] = t
        t.status = to or t.status
        for f in ("pid", "brief", "role", "model", "effort", "run",
                  "park_reason", "obl_before", "row", "tier"):
            if f in line:
                setattr(t, f, line[f])
        if "attempt" in line:
            t.attempt = _int(line["attempt"], t.attempt or 0)
        if t.tier not in TIERS:
            t.tier = WIDE
        if _is_record(line):
            t.record = {"task": code, "facts": line["facts"],
                        "concurrency": line.get("concurrency"),
                        "caliber": line.get("caliber"), "tier": t.tier}
        if t.status == PARKED and t.parked_at is None:
            t.parked_at = _epoch(line.get("ts"))
    return st


def _is_record(line):
    """True when a log line carries a WHOLE six-fact record that `matches()` can index.

    `matches()` in `scripts/pod/table.py` reads `rec["facts"]["exit_code"]` and four
    more by SUBSCRIPT, so a line carrying half a facts object raises `KeyError` inside
    `route()`. R7 already forbids guessing a fact, and this is the same rule at the fold:
    a partial record is no record.
    """
    f = line.get("facts")
    return isinstance(f, dict) and all(k in f for k in table_mod.FACT_KEYS)


def _epoch(ts):
    """One ISO-8601 UTC stamp as epoch seconds, or None. It never guesses a clock."""
    if not ts:
        return None
    try:
        return datetime.datetime.strptime(ts, "%Y-%m-%dT%H:%M:%SZ").replace(
            tzinfo=datetime.timezone.utc).timestamp()
    except (ValueError, TypeError):
        return None


def _now_iso():
    return datetime.datetime.now(datetime.timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")


def corpus_append(line, path=None):
    """The `live` stream of section 4.5.3: one routed record becomes one corpus record.

    ONE WRITER PUTS A RECORD IN AND IT IS `emit()`. Every transition line that carries
    BOTH a `facts` object and a routing decision is appended, with `id` set to
    `"c-" + seq` and `provenance` set to `live`. That makes the corpus a SUBSET of the log
    by construction, and `seq` makes the id unique and the append idempotent after a crash.
    """
    p = CORPUS if path is None else Path(path)
    rec = {"id": "c-" + str(line["seq"]), "task": line["task"], "provenance": "live",
           "recorded": str(line["ts"])[:10], "facts": line["facts"],
           "caliber": line.get("caliber"), "concurrency": line.get("concurrency"),
           "tier": line.get("tier"),       # A14: a record is compared inside one tier
           "row": line.get("row"), "action": line.get("action")}
    try:
        p.parent.mkdir(parents=True, exist_ok=True)
        if p.is_file() and f'"id": "c-{line["seq"]}"' in p.read_text(encoding="utf-8"):
            return False                   # idempotent after a crash between the writes
        with open(p, "a", encoding="utf-8") as fh:
            fh.write(json.dumps(rec, sort_keys=True, default=str) + "\n")
            fh.flush()
            os.fsync(fh.fileno())
    except OSError:
        # THE CORPUS IS THE REPLAY'S EVIDENCE AND NOT THE LOOP'S TRUTH. The transition
        # line is already durable, and section 4.5.3 builds the corpus FORWARD from the
        # log, so a corpus write that fails costs one replay record and never a task.
        return False
    return True


def _abs(path, root=None):
    """One repository-relative path as an absolute one. The state and the log keep the
    RELATIVE form, because a log line must read the same on any clone."""
    root = ROOT if root is None else Path(root)
    p = Path(path)
    return p if p.is_absolute() else root / p


def emit_event(st, event, root=None, **fields):
    """One log line that is NOT a task transition, and there are exactly FOUR kinds.

    Section 6.7's `batch` line, which `harvest_batch()` writes and hands to the next batch
    as input; section 7.4 Part 1b's `retrieval` line, which carries the miss signal;
    A13's `watchdog` line, which records one restart of the memory backstop; and A11's
    `refill` line, which records one rule (g) dispatch or the one dependency it waits on.
    None of the four moves a task, so none may claim one of the twelve transitions;
    writing them through `emit()` would need a thirteenth edge that means nothing.
    """
    root = ROOT if root is None else Path(root)
    line = {"ts": _now_iso(), "seq": st.seq + 1, "task": "", "event": event}
    line.update({k: v for k, v in fields.items() if v is not None})
    with pod_lock():
        _append_line(line, root)
        st.seq += 1
        save_state(st)
    return line


def _append_line(line, root):
    """The ONE writer of a log line: serialise, append, fsync. It never half-writes.

    `json.dumps` runs BEFORE the file opens, so a value that cannot be serialised leaves
    the file untouched, and `default=str` means no field can produce that case at all.
    Without it, one caller passing a `datetime.date` or a `Path` in `**fields` raises
    `TypeError` after the side effect is already performed, which is crash window two
    with no line to recover from. `split_entry()` builds exactly such a value today, and
    `emit_event()` already carried `default=str` while `emit()` did not.
    """
    body = json.dumps(line, sort_keys=True, default=str) + "\n"
    path = log_path(root=root)
    try:
        path.parent.mkdir(parents=True, exist_ok=True)
        with open(path, "a", encoding="utf-8") as fh:
            fh.write(body)
            fh.flush()
            os.fsync(fh.fileno())
    except OSError as e:
        # THE LOG IS THE TRUTH. A line that cannot be written must stop the loop with a
        # reason, because the state file would otherwise record a transition that no
        # tracked file carries, and section 5.3 says a lost log line is recoverable from
        # NOTHING.
        raise PodError(f"cannot append to {path}: {e}") from e


def emit(st, subject, frm, to, rec=None, root=None, **fields):
    """ONE transition. The log line FIRST, then the state file, both under one lock.

    THE WRITE ORDER IS THE CRASH SAFETY (section 5.3):

        1. the side effect is already performed by the caller
        2. with pod_lock():                  one flock for both writers
        3.     append one line to LOG; os.fsync(log_fd)
        4.     st.seq += 1; save_state(st)   tmp -> fsync -> rename -> fsync(dir)

    A lost state file is recoverable from the log; a lost log line is recoverable from
    NOTHING. Crash window two, the side effect done and the log not written, is safe for a
    different reason: every side effect is re-observable. A spawned worker becomes an
    ORPHAN, which `strays()` finds; an acceptance run leaves its `runs/accept-<n>.out`;
    and `admit_rows()` is idempotent.
    """
    root = ROOT if root is None else Path(root)
    code = subject.code if isinstance(subject, Task) else (subject or "")
    t = subject if isinstance(subject, Task) else st.tasks.get(code)
    if (frm, to) not in TRANSITIONS_LEGAL and to != LOOP_STOPPED:
        raise PodError(f"{code}: {frm} -> {to} is not one of the twelve legal transitions")

    line = {"ts": _now_iso(), "seq": st.seq + 1, "task": code,
            "from": frm, "to": to}
    if rec is not None:
        # A PARK line carries `"row": null` and the record that matched nothing, so the
        # `row` key is written whenever a record is, present or null.
        line["facts"] = rec["facts"]
        line["caliber"] = rec.get("caliber")
        line["concurrency"] = rec.get("concurrency")
        line.setdefault("row", None)
    for k, v in fields.items():
        if v is not None or k in ("row", "why", "reason"):
            line[k] = v
    if t is not None:
        for k, v in (("pid", t.pid), ("role", t.role), ("attempt", t.attempt),
                     ("model", t.model), ("effort", t.effort), ("run", t.run),
                     ("tier", t.tier)):    # A14: a record carries its tier
            line.setdefault(k, v)
        line.setdefault("heads_sha256", _heads_sha())

    with pod_lock():
        _append_line(line, root)           # STEP 3. The log line is durable FIRST.
        if "facts" in line and "row" in line:
            corpus_append(line)            # section 4.5.2, the `live` stream
        st.seq += 1
        if t is not None:
            t.status = to
            st.tasks[code] = t
            if to == PARKED:
                t.parked_at = time.time()
                t.park_reason = fields.get("reason", t.park_reason)
            if rec is not None:
                t.record = rec
            if "row" in line:
                t.row = line["row"]
        if to == LOOP_STOPPED:
            st.stopped = line["ts"]
        save_state(st)                     # STEP 4. tmp -> fsync -> rename -> fsync(dir)
    return line


_HEADS_SHA = []


def _heads_sha():
    """The `heads.toml` digest AD26 stamps into every line, or None when unreadable.

    AD26 is a RECORD and not a policy: the program resolves the head ONCE, at dispatch,
    and writes what ran. Nothing re-reads the file for a running task.
    """
    if _HEADS_SHA:
        return _HEADS_SHA[0]
    try:
        _HEADS_SHA.append(heads_mod.sha256()[:8])
    except heads_mod.HeadsError:
        _HEADS_SHA.append(None)
    return _HEADS_SHA[0]


# ---------------------------------------------------------------- the queue, section 5.2


def queue_entries(path=None):
    """Every `[[task]]` entry of `dev/pod/queue.toml`, tracked. A bad file is EMPTY.

    NOTHING ELSE CREATES A TASK: the mathematician writes an entry, `park_and_split`
    appends one, and the owner may add one by hand. The program never writes a brief,
    because AD3 gives the brief to the mathematician.
    """
    p = QUEUE if path is None else Path(path)
    try:
        data = tomllib.loads(p.read_text(encoding="utf-8"))
    except (OSError, ValueError, UnicodeDecodeError):
        return []                          # ValueError covers TOMLDecodeError
    if not isinstance(data, dict):
        return []
    out = data.get("task")
    if not isinstance(out, list):
        return []
    # AN ENTRY THAT IS NOT A TABLE IS NOT AN ENTRY. `[[task]]` gives a dict, and any
    # other TOML value would reach `e.get()` in rule (a1) as a string or a number.
    return [e for e in out if isinstance(e, dict)]


def queue_append(entry, path=None):
    """Append one entry. `park_and_split` and `harvest_batch()` are the two callers.

    IT RETURNS FALSE AND NEVER RAISES. The queue is TRACKED and a maintainer batch is one
    of the writers, so a proposal file holding a `[[queue]]` value that is not a table
    reaches here; a full disk reaches here too. Neither is a reason to abandon a tick that
    has already parked a task.
    """
    if not isinstance(entry, dict):
        return False
    p = QUEUE if path is None else Path(path)
    body = ["", "[[task]]"]
    for k in ("code", "brief", "split_of", "reason", "added", "added_by", "failed_check"):
        if entry.get(k) is None:
            continue
        v = entry[k]
        body.append(f"{k} = {v}" if isinstance(v, datetime.date)
                    else f"{k} = {json.dumps(v, default=str)}")
    try:
        p.parent.mkdir(parents=True, exist_ok=True)
        with open(p, "a", encoding="utf-8") as fh:
            fh.write("\n".join(body) + "\n")
            fh.flush()
            os.fsync(fh.fileno())
    except OSError:
        return False
    return True


def split_entry(t, rec):
    """A REQUEST entry, and it NAMES NO BRIEF, which is what makes it a request.

    An entry with no `brief` is never a task: rule (a1) skips it and the digest prints it
    until the mathematician adds the brief path. The program never writes a brief (AD3).
    """
    f = (rec or {}).get("facts", {})
    return {"code": t.code + "-split", "split_of": t.code,
            "reason": f"park_and_split: error_class {f.get('error_class')}, "
                      f"{len(f.get('changed_files') or [])} changed files",
            "added": datetime.date.today(), "added_by": "maintainer"}


def stamp_pod_marker(code, root=None):
    """Section 9.3: `agents/tasks/<CODE>/.pod`, ONE line, written at task creation.

    IT SURVIVES A COPY, and AD6 salvages `agents/` by copying, so a git-only marker is
    lost at exactly the moment the reader needs it. The backstop for anything with no
    stamp is `git log --oneline pre-pod-2026-08-17..HEAD -- agents/tasks/<CODE>/`.
    """
    root = ROOT if root is None else Path(root)
    try:
        d = root / "agents" / "tasks" / agents_tree.normalise(code)
        if not d.is_dir():
            return None
        line = (f"pod=1 table={_sha_of(root / 'dev' / 'pod' / 'table.toml')} "
                f"heads={_sha_of(root / 'dev' / 'pod' / 'heads.toml')} at={_now_iso()}\n")
        (d / ".pod").write_text(line, encoding="utf-8")
        return str((d / ".pod").relative_to(root))
    except (OSError, ValueError, TypeError, AttributeError):
        # A MARKER IS PROVENANCE AND NOT A GATE. The backstop section 9.3 names is
        # `git log --oneline pre-pod-2026-08-17..HEAD -- agents/tasks/<CODE>/`, so a
        # marker that cannot be written costs a convenience and never a task.
        return None


def _sha_of(path):
    import hashlib
    try:
        return hashlib.sha256(Path(path).read_bytes()).hexdigest()
    except OSError:
        return "absent"


def section_span(text, name):
    """The (start, end) offsets of one `## NAME` section BODY, or None when it is absent.

    The heading match is a PREFIX match, exactly as `preflight.section()` reads it, because
    the program appends `(program-generated, do not edit)` to three headings. This function
    gives the OFFSETS, so a block can be filled in place; `preflight.section()` gives the
    TEXT, and `laws_missing()` below tests emptiness with that one, so the program and P21
    can never disagree about which characters are the body.
    """
    m = re.search(r"^##[ \t]+" + re.escape(name) + r"[^\n]*\n", text, re.M)
    if m is None:
        return None
    nxt = re.search(r"^##[ \t]", text[m.end():], re.M)
    return m.end(), (m.end() + nxt.start() if nxt else len(text))


def laws_missing(text):
    """True when P21 would refuse this brief: the `## LAWS` block is absent or empty."""
    body = preflight_mod.section(text, "LAWS")
    return body is None or not body.strip()


#: R17's heading, exactly as memo section 6.3's template writes it. `preflight.section()`
#: matches the name by PREFIX, so the parenthesis is prose and never a second name.
LAWS_HEADING = "## LAWS (program-generated, do not edit)"


def laws_bundle(paths, root=None):
    """R17's LAWS text for one write scope, or None when the producer refused.

    THIS IS HOW `dev/LESSONS.md` REACHES A WORKER, and nothing else in the flow delivers
    one line of it. Section 7.1 row 22 keeps `scripts/dispatch/rules.py` out of the
    `make check` gate and INSIDE the brief builder for exactly this. Pre-flight P21 refuses
    a brief whose block is absent or empty, so a producer that returns None parks the task
    with a reason, which is the loud path.

    THE KIND IS DERIVED AND NEVER DECLARED ([T105], memo section 6.3). The derivation has
    ONE home, `kind_for_scope()` in `rules.py`, so this function imports that function
    rather than repeating the rule; the BUNDLE TEXT is the command's own output, verbatim,
    which is what the template names. `sys.path` is restored, because `rules.py` puts its
    own group directory in front at import time.

    THE OUTPUT IS TESTED BY ITS HEADER. `emit()` in `rules.py` opens every real bundle with
    `MANDATORY for kind`, and its two failure prints do not, so an unknown kind writes no
    block instead of writing an error message into the brief as if it were law.
    """
    root = ROOT if root is None else Path(root)
    tool = root / "scripts" / "dispatch" / "rules.py"
    saved = list(sys.path)
    try:
        import importlib.util                          # deferred: only the builder needs it
        spec = importlib.util.spec_from_file_location("pod_rules", tool)
        mod = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(mod)
        kind = mod.kind_for_scope(list(paths))
    except Exception:                                  # noqa: BLE001. See the docstring
        return None
    finally:
        sys.path[:] = saved
    try:
        done = subprocess.run([sys.executable, str(tool), "--for", str(kind)],
                              cwd=str(root), capture_output=True, text=True, timeout=120)
    except (OSError, subprocess.SubprocessError):
        return None
    out = (done.stdout or "").strip()
    return out if out.startswith("MANDATORY for kind") else None


def unwired_masters(paths, root=None):
    """R18's trigger: every `src/` master in a write scope that `Everything` does not import.

    THE MODULE NAME COMES FROM THE PATH AND NEVER FROM THE FILE, because the master the
    task will write does not exist yet. `check_closure()` in `scripts/pod/check-closure.py`
    maps the two directions the same way, so the trigger and the refusal agree.

    AN EMPTY IMPORT LIST ADDS NOTHING. `imported_by_everything()` returns an empty set when
    it cannot read the closure checker, and that is indistinguishable from a catalog that
    imports nothing. Granting the catalog as write territory on a blind sensor is the wrong
    direction (AD17), and a tree whose catalog really imports nothing fails conjunct 3 for
    every task anyway.
    """
    try:
        imported = facts_mod.imported_by_everything(root)
    except Exception:                                  # noqa: BLE001. A blind reader adds nothing
        return []
    if not imported:
        return []
    out = []
    for p in paths:
        if not p.startswith("src/") or not p.endswith(".lagda.md") or p == EVERYTHING:
            continue
        if any(c in p for c in preflight_mod.GLOB_CHARS):
            continue                                   # a pattern names no one module
        name = p[len("src/"):-len(".lagda.md")].replace("/", ".")
        if name not in imported and p not in out:
            out.append(p)
    return out


def add_everything_to_scope(text):
    """R18: put `src/Everything.lagda.md` in `## SCOPE (write)`. The text, or None.

    WITHOUT THIS LIMB A NEW MASTER CANNOT BE WIRED. `check_closure()` fails on a master
    `Everything` does not import, acceptance conjunct 3 runs it, and R8 commits by explicit
    path derived from the task's scope, so an import line outside the declared scope is
    neither permitted nor committed. The task would therefore be refused for the defect its
    own brief forced on it.
    """
    span = section_span(text, "SCOPE")
    if span is None:
        return None
    start, end = span
    body = text[start:end].rstrip("\n")
    line = (f"- `{EVERYTHING}` (R18, program-generated: wire the new master here, because "
            f"acceptance conjunct 3 refuses a catalog that does not import it)")
    return text[:start] + body + "\n" + line + "\n\n" + text[end:]


def inject_survey(brief, root=None):
    """The brief builder's augmentation pass: R10 and section 7.4, plus R17 and R18.

    THE WORKER CANNOT SKIP A SURVEY IT NEVER HAD TO PERFORM. MEASURED 2026-08-17: 282
    live briefs, of which 244 never name `JOURNAL-archived.md`. The blocks are written
    BEFORE pre-flight P15 and P21 read them, so a brief with a dead injected path parks
    rather than dispatching. A block the brief already carries is left alone, because a
    record is never rewritten; the ONE exception is a `## LAWS` heading with an empty body,
    which is filled in place, because a second heading of that name would leave P21 reading
    the first and empty one for ever.

    THREE RULES, ONE WRITE. R18 goes first, because it changes `## SCOPE (write)` and R17
    derives its kind from that section. The kind cannot change under it: R18 adds a `src/`
    path only to a scope that already names one, so a `build` stays a `build`. The file is
    written once, at the end, and only when the text really changed.

    A FAILED INJECTION IS NOT A FAILED TASK. The retrieval reads an index, a corpus and
    the brief itself, so it can fail on a missing file, a malformed `obligations` list or
    a full disk. Pre-flight P15 and P21 then refuse the brief for the block it lacks and the
    task PARKS with a reason, which is the loud path; raising here would stop the whole loop
    for one brief.
    """
    root = ROOT if root is None else Path(root)
    if not isinstance(brief, (str, Path)) or not str(brief):
        return False
    p = Path(brief) if Path(brief).is_absolute() else root / brief
    try:
        if not p.is_file():
            return False
        text = original = p.read_text(encoding="utf-8")
        scope = preflight_mod.scope_paths(text)

        # R18. The new master gets its wiring path before anything reads the scope again.
        if unwired_masters(scope, root) and EVERYTHING not in scope:
            text = add_everything_to_scope(text) or text

        # R17. The measured lesson book, for the kind the write scope derives.
        if laws_missing(text):
            bundle = laws_bundle(scope, root)
            span = section_span(text, "LAWS")
            if bundle is not None and span is None:
                text = text.rstrip("\n") + "\n\n" + LAWS_HEADING + "\n\n" + bundle + "\n"
            elif bundle is not None:
                text = text[:span[0]] + "\n" + bundle + "\n\n" + text[span[1]:]

        # R10, section 7.4. The two retrieval blocks.
        if "## ARCHIVE" not in text or "## LITERATURE" not in text:
            try:
                import retrieve as retrieve_mod         # deferred: it builds an index
            except ImportError:
                retrieve_mod = None
            if retrieve_mod is not None:
                obligations = witness_mod.obligations_of(p)
                query = retrieve_mod.build_query(scope, obligations,
                                                 retrieve_mod.goal_text(str(p)))
                blocks = []
                if "## ARCHIVE" not in text:
                    blocks.append(retrieve_mod.candidate_block(
                        "ARCHIVE", query, retrieve_mod.ARCHIVE_SCOPE))
                if "## LITERATURE" not in text:
                    blocks.append(retrieve_mod.candidate_block(
                        "LITERATURE", query, retrieve_mod.LITERATURE_SCOPE))
                text = text.rstrip("\n") + "\n\n" + "\n".join(blocks)

        if text == original:
            return False
        p.write_text(text, encoding="utf-8")
    except Exception:                                  # noqa: BLE001. See the docstring
        return False
    return True


def emit_retrieval(st, t, root=None):
    """Section 7.4 Part 1b: ONE `retrieval` line per return. It never raises.

    `dispatch_signal()` in `scripts/pod/retrieve.py` is the producer and `scripts/pod/
    digest.py` is the reader: it counts `retrieval_miss`, `retrieval_zero_overlap` and
    `retrieval_undetermined` off this event and off nothing else. Without this call all
    three read zero for ever, and the semantic-index trigger can never fire, so the program
    would claim a measurement it does not take.

    THE `event` KEY IS DROPPED BEFORE THE CALL. `miss_signal()` puts `"event": "retrieval"`
    into its own record and `emit_event()` takes the event as a positional argument, so
    passing the record whole raises `TypeError` for a duplicate keyword.

    A SIGNAL THAT CANNOT BE TAKEN IS NOT A FAILED RETURN. The producer reads the brief and
    the report beside it, so a missing report, an unreadable corpus or a full disk must cost
    one log line and never the acceptance that already ran.
    """
    root = ROOT if root is None else Path(root)
    try:
        import retrieve as retrieve_mod                # deferred: it builds an index
        signal = retrieve_mod.dispatch_signal(t.code, t.brief)
        emit_event(st, "retrieval", root=root,
                   **{k: v for k, v in signal.items() if k != "event"})
    except Exception:                                  # noqa: BLE001. See the docstring
        return False
    return True


def archived_codes(st, root=None):
    """Every live task whose directory now sits under `agents/tasks/archive/`.

    This is expiry's SECOND mechanical trigger (section 4.6). `task_dir()` at
    `scripts/agents_tree.py:169` looks in `agents/tasks/` and then in the archive, so the
    test is which parent it found.
    """
    root = ROOT if root is None else Path(root)
    live = root / "agents" / "tasks"
    out = []
    for code in sorted(st.tasks):
        try:
            d = agents_tree.task_dir(code)
        except (OSError, ValueError, TypeError):
            continue                       # a code that names no directory is not archived
        if d is not None and d.parent != live:
            out.append(code)
    return out


# ---------------------------------------------------------------- concurrency, AD17


def load1():
    """The one-minute load average. Every run record writes a `# load before` line."""
    try:
        return os.getloadavg()[0]
    except OSError:
        return 0.0


def free_memory_pct():
    """System free memory as a percentage, or None when it cannot be read.

    A14 fills Agda slots three and four only above `free_memory_pct_for_extra`. NONE IS
    NOT ZERO AND IT IS NOT A HUNDRED: an unreadable sensor must refuse, never clear (FM12),
    so `agda_slots()` drops to the two-slot floor when this returns None.
    """
    if sys.platform == "darwin":
        try:
            out = subprocess.run(["memory_pressure", "-Q"], capture_output=True,
                                 text=True, timeout=20).stdout
        except (OSError, subprocess.SubprocessError):
            return None
        for line in out.split("\n"):
            if "free percentage" in line:
                digits = "".join(c for c in line.split(":")[-1] if c.isdigit())
                return float(digits) if digits else None
        return None
    try:
        text = Path("/proc/meminfo").read_text(encoding="utf-8")
    except OSError:
        return None
    fields = {}
    for line in text.split("\n"):
        parts = line.split(":")
        if len(parts) != 2 or not parts[1].strip().split():
            continue
        try:
            fields[parts[0]] = float(parts[1].strip().split()[0])
        except ValueError:
            continue                       # a non-numeric field is ABSENT, never a zero
    total, avail = fields.get("MemTotal"), fields.get("MemAvailable")
    return 100.0 * avail / total if total and avail else None


def watchdog_alive():
    """A13: `admits()` refuses every Agda task while `scripts/ops/agda-watchdog.sh` is down.

    The watchdog is the BACKSTOP for the guard that matters: it kills any Agda over the
    14 GB per-process cap and, below an 8 percent system free floor, the largest one. It
    was born 2026-08-02 after four unguarded parallel writers crashed the 64 GB box. With
    it down, the POD's own slot arithmetic is the only guard left, and A13 says that is
    not enough. An unreadable `pgrep` reads as DOWN, which is the safe direction.
    """
    try:
        done = subprocess.run(["pgrep", "-f", "agda-watchdog.sh"],
                              capture_output=True, text=True, timeout=20)
    except (OSError, subprocess.SubprocessError):
        return False
    return done.returncode == 0 and bool(done.stdout.strip())


#: A13's memo, and it holds ONE value: the reason of the newest watchdog restart that
#: FAILED, or None. It bounds the log: see `watchdog_tick()`.
_WATCHDOG = {"reported": None}


def watchdog_start(root=None):
    """Start `scripts/ops/agda-watchdog.sh` detached. It returns (pid, None) or
    (None, reason).

    IT STARTS THE SCRIPT THE WAY THE SCRIPT EXPECTS. `agda-watchdog.sh:5` reads
    `dirname "$0"` and then walks up to `.git`, so the ABSOLUTE script path is the one
    argument that matters; the script reads no stdin and appends to
    `_build/tools/agda-watchdog.log` itself.

    THE CHILD GETS ITS OWN SESSION, and the founding incident of the launcher is why: on
    2026-08-05 two live agents died because somebody stopped the watcher shell that had
    launched them into its own process group (`scripts/pod/launcher.py:7-9`). A watchdog
    that dies with the POD is a watchdog that is down exactly when a killed loop leaves
    Agda processes behind.
    """
    root = ROOT if root is None else Path(root)
    if not WATCHDOG.is_file():
        return None, f"{WATCHDOG} is not a file"
    argv = ([str(WATCHDOG)] if os.access(WATCHDOG, os.X_OK)
            else ["/bin/zsh", str(WATCHDOG)])          # the script's own shebang is zsh
    try:
        proc = subprocess.Popen(argv, cwd=str(root), start_new_session=True,
                                stdin=subprocess.DEVNULL,
                                stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
    except (OSError, ValueError) as e:
        return None, f"{type(e).__name__}: {e}"
    return proc.pid, None


def watchdog_backstop_note(path=None):
    """C-12's two numbers, read from the SCRIPT and compared with `dev/pod/heads.toml`.

    A13 returns the 14 GB per-process backstop and the 8 percent system-free floor WITH
    the watchdog. Both numbers are written twice: in the shell script at
    `scripts/ops/agda-watchdog.sh:12-13`, and in `[tiers.shared]` of `dev/pod/heads.toml`.
    Two homes for one number drift silently, so this READS both and NAMES a disagreement
    on the restart line.

    IT NEVER REFUSES. This program owns neither file, so a refusal here would idle the
    loop with the cure outside its reach. It returns None when the two agree or when
    either is unreadable.
    """
    p = WATCHDOG if path is None else Path(path)
    try:
        text = p.read_text(encoding="utf-8")
        shared = heads_mod.load_heads()["tiers"]["shared"]
    except (OSError, KeyError, TypeError, heads_mod.HeadsError):
        return None
    out = []
    for pattern, key, unit in (
            (r"LIMIT_KB=\$\(\(\s*(\d+)\s*\*\s*1024\s*\*\s*1024\s*\)\)",
             "per_process_backstop_gb", "GB per process"),
            (r"^FREE_MIN=(\d+)", "system_free_floor_pct", "percent system free")):
        m = re.search(pattern, text, re.M)
        want = shared.get(key)
        if m is None or want is None:
            continue
        if _int(m.group(1)) != _int(want):
            out.append(f"the script says {m.group(1)} {unit} and "
                       f"[tiers.shared].{key} says {want}")
    return "; ".join(out) or None


def watchdog_tick(st, root=None):
    """A13: every tick CONFIRMS the watchdog, and one restart writes ONE log line.

    C-12 says restart `scripts/ops/agda-watchdog.sh` at every session. THE POD HAS NO
    SESSION, and the design's script table put the watchdog outside the POD entirely, so
    nothing would ever start it. MEASURED 2026-08-17: it was not running. The owner ruled
    that the program is its owner.

    ONE LINE PER RESTART, AND NOT ONE A TICK. A restart that SUCCEEDS is rare and writes
    its line. A restart that FAILS repeats every tick, and at `tick_seconds = 30` that is
    2,880 lines a day into a TRACKED file that the digest and the maintainer batch read;
    so a failure writes its line once and stays silent until the reason CHANGES or the
    watchdog comes back. The refusal itself is not silent: `admits()` refuses every Agda
    task for as long as this returns False.
    """
    if watchdog_alive():
        _WATCHDOG["reported"] = None
        return True
    pid, why = watchdog_start(root)
    if pid is not None or _WATCHDOG["reported"] != why:
        _WATCHDOG["reported"] = why
        emit_event(st, "watchdog", root=root,
                   result="started" if pid is not None else "REFUSED",
                   pid=pid, why=why, backstop=watchdog_backstop_note())
    return pid is not None


def tier_heap_gb(tier):
    """The `-M` cap of one tier, in whole gigabytes, or None when it cannot be read.

    THE PARSER HAS ONE HOME. `heads.py` reads the caliber string for its own load-time
    check of A14's 32 GB sum, and this calls that parser rather than writing a second one:
    two readers of one field drift, and the field is a memory cap.
    """
    try:
        cfg = heads_mod.load_heads()
        return heads_mod._heap_gb(cfg["tiers"][tier]["heap"])
    except (heads_mod.HeadsError, KeyError, TypeError):
        return None


def agda_slots(tier=WIDE):
    """A14's slot count for one tier, cut to the floor when free memory is low or unread.

    C-12's TWO TIERS: WIDE is four concurrent Agda writers at `-M8g`, HEAVY is two at
    `-M12g`, and the mixed worst-case heap sum stays at or under 32 GB, which `heads.py`
    checks at load and `heap_sum_ok()` checks per admission. Slots three and four fill
    ONLY above `free_memory_pct_for_extra`, which is C-12's own 25 percent.

    THE TIER SURFACE IS THIN AND THAT IS DISCLOSED. No `[row.when]` key names a tier, so
    a task declares one in the `agda_tier:` line of its brief's `## HEAD` block, which
    `task_tier()` reads and no pre-flight check enforces. A brief that names none is WIDE.
    A HEAVY declaration now buys BOTH halves: `launch()` passes `tier=tier_of(t)` to the
    launcher, so the pane gets `-A64m -I0 -M12g` and the registry record carries `heavy`
    for the heap sum. The program's OWN acceptance run stays at the WIDE caliber (A15).

    THE DANGLING HALF, AND IT IS A DOCUMENTATION GAP RATHER THAN A CODE ONE. No brief
    template and no slot instruction file names `agda_tier:` today: `grep -rn agda_tier
    dev/ agents/` returns nothing (MEASURED 2026-08-18). A mathematician therefore has no
    written way to declare HEAVY, and every task runs WIDE by default until memo section
    6.3's `## HEAD` template and `dev/pod/instructions/mathematician.md` name the field.
    Both files are guarded by `check-spec-surface.py`, so the edit needs the owner's dated
    `Spec-surface-approved:` trailer and cannot be made from here.
    """
    try:
        cfg = heads_mod.load_heads()
        slots = _int(cfg["tiers"][tier]["slots"])
        need = cfg["tiers"]["shared"]["free_memory_pct_for_extra"]
    except (heads_mod.HeadsError, KeyError, TypeError):
        return 2                              # C-12's floor, never a guess upward
    if slots is None or slots < 1 or not isinstance(need, (int, float)):
        return 2
    floor = min(slots, 2)
    pct = free_memory_pct()
    if pct is None or pct <= need:
        return floor
    return slots


def heap_sum_ok(st, t, tier):
    """A14's mixed worst case: the sum of the running heap caps stays at or under 32 GB.

    ONE TIER'S OWN ARITHMETIC IS NOT ENOUGH, and that is why this exists beside
    `agda_slots()`. Four WIDE writers are 32 GB and two HEAVY writers are 24 GB, so each
    tier alone holds; one HEAVY beside three WIDE is 36 GB, which no per-tier count
    refuses. C-12 measured the cost of getting this wrong on 2026-08-02: four unguarded
    parallel writers OOM-crashed a 64 GB machine and took four in-flight tasks down.

    IT COUNTS THE POD'S OWN WRITERS, which is what it can attribute a tier to. The census
    of `agda_pileup()` counts every Agda process on the machine and `admits()` refuses on
    that too, so the two guards are AND-ed and neither replaces the other.
    """
    try:
        cap = heads_mod.load_heads()["tiers"]["shared"]["max_heap_sum_gb"]
    except (heads_mod.HeadsError, KeyError, TypeError):
        return True                           # the check has no bar, so it claims nothing
    if not isinstance(cap, (int, float)):
        return True
    total = tier_heap_gb(tier)
    if total is None:
        return True                           # an unreadable caliber is `agda_slots()`'s
    for x in st.tasks.values():
        if x.status in (RUNNING, CHECKING) and x.agda and x.code != t.code:
            total += tier_heap_gb(tier_of(x)) or 0
    return total <= cap


def tier_of(t):
    """One task's tier, normalised. An unreadable value is WIDE, the caliber that runs."""
    tier = getattr(t, "tier", None)
    return tier if tier in TIERS else WIDE


def task_tier(brief, root=None):
    """The `agda_tier:` line of a brief's `## HEAD` block. A14, and it is copied ONCE.

    THREE CASES AND EACH IS RULED. A brief that names NO tier is WIDE, because the
    caliber `run_agda()` sets is the WIDE one, so WIDE is the true worst case and not an
    optimistic guess. A brief that names one of the two tiers gets it. A brief that names
    a THIRD string is a declaration this program cannot read, so it takes HEAVY, which is
    conservative in both terms at once: fewer slots and a bigger heap in the sum.
    """
    root = ROOT if root is None else Path(root)
    if not isinstance(brief, (str, Path)) or not str(brief):
        return WIDE
    p = Path(brief) if Path(brief).is_absolute() else root / brief
    try:
        declared = preflight_mod.head_field(p.read_text(encoding="utf-8"), "agda_tier")
    except (OSError, UnicodeDecodeError):
        return WIDE
    if declared is None:
        return WIDE
    return declared if declared in TIERS else HEAVY


def agda_pileup():
    """The launcher's census, unchanged. THREE values, and the POD refuses on all three.

    `agda_pileup()` in `scripts/pod/launcher.py` returns `(total, per_parent, warning)`
    and its ONE consumer, `cmd_status`, only PRINTS. Under AD17 the POD must REFUSE on it.
    A launcher this file cannot load reads as BLIND, which refuses: admitting on a blind
    sensor is the wrong direction and FM12 names it.
    """
    mod = facts_mod.launcher()
    if mod is None:
        return 0, {}, "no launcher module is readable; agda pileup detection is BLIND"
    try:
        total, per_parent, warning = mod.agda_pileup()
    except Exception as e:                    # noqa: BLE001. A census that RAISES is blind
        return 0, {}, f"agda_pileup raised {type(e).__name__}: {e}; the census is BLIND"
    if not isinstance(per_parent, dict) or _int(total) is None:
        return 0, {}, "agda_pileup returned an unreadable census; it is BLIND"
    return _int(total), per_parent, warning


def admits(st, t, agda=None):
    """Section 5.6, AD17, amended by A13 and A14. It REFUSES; it never prints.

    THREE PROPERTIES, and each repairs a real defect. All three values of `agda_pileup()`
    are unpacked, because reading `[0]` as a boolean would refuse every admission while
    ONE Agda process lives. The threshold is `agents/tasks/LJ-1-331/run.sh:14-18`'s own
    rule. And the warning is never discarded: when `ps` fails the census is BLIND, and
    admitting on that is the wrong direction.

    EXCLUSIVE IS NOT ONLY ABOUT SLOTS. A `machine: exclusive` task gets the machine alone
    and stays READY while the load average sits above `exclusive_max_load1`.

    A13 AND A14 ADD THREE LIMBS TO THE AGDA HALF, and all three are C-12's. The watchdog
    must be UP, because it is the 14 GB per-process backstop and the 8 percent free floor
    and nothing else provides them. The slot ceiling is the TIER's, four for WIDE and two
    for HEAVY, and the third and fourth open only above 25 percent free memory. And the
    mixed worst-case heap sum stays at or under 32 GB, which no per-tier count catches.
    """
    running = [x for x in st.tasks.values() if x.status in (RUNNING, CHECKING)]
    if any(x.exclusive for x in running):
        return False
    limits = _limits()
    if t.exclusive and load1() > limits["exclusive_max_load1"]:
        return False
    if t.exclusive:
        return not running
    total, per_parent, blind = agda_pileup()
    if blind:
        return False                          # never guess
    if any(n > 1 for n in per_parent.values()):
        return False                          # the pile-up: C-12 says ONE per agent
    if not (t.agda if agda is None else agda):
        return True                           # no Agda, so no C-12 limb applies
    if not watchdog_alive():
        return False                          # A13. The backstop is down
    tier = tier_of(t)
    if total >= agda_slots(tier):
        return False                          # A14. The tier's own ceiling
    return heap_sum_ok(st, t, tier)           # A14. The mixed worst case


def _limits():
    """The five limits, or a REFUSAL. There is no fallback literal, and 6.1 is why."""
    try:
        return heads_mod.limits()
    except heads_mod.HeadsError as e:
        raise PodError(str(e)) from e


# ---------------------------------------------------------------- the dispatch


def head_slot_of(brief, root=None):
    """The `head_slot:` line of a brief's `## HEAD` block, or the mathematician.

    Pre-flight P11 refuses a slot that `heads.toml` does not name, so by the time rule (f)
    reads it the value is legal. A brief that names none gets `mathematician`, which AD24
    makes the default author.
    """
    root = ROOT if root is None else Path(root)
    p = Path(brief) if Path(brief).is_absolute() else root / brief
    try:
        text = p.read_text(encoding="utf-8")
    except OSError:
        return "mathematician"
    return preflight_mod.head_field(text, "head_slot") or "mathematician"


def machine_class(brief, root=None):
    """`machine: exclusive` or `machine: shared`, from the brief's one machine-readable
    line. Pre-flight P13 refuses a brief with neither, so this never guesses.

    The value is copied ONCE into the state record at admission, so a later edit of the
    brief cannot change a running task's class, exactly as the launcher does for the
    harness.
    """
    root = ROOT if root is None else Path(root)
    p = Path(brief) if Path(brief).is_absolute() else root / brief
    try:
        text = p.read_text(encoding="utf-8")
    except OSError:
        return False
    return preflight_mod.head_field(text, "machine") == "exclusive"


def reviewed(t, root=None):
    """True when THIS attempt already went out as an adversarial review. It holds no state.

    It reads the log: a `READY -> RUNNING` line for this code carrying this `attempt` and
    `role: "mathematician_adversarial"`, both of which are log fields.
    """
    for line in log_lines(root):
        if (line.get("task") == t.code and line.get("to") == RUNNING
                and line.get("attempt") == t.attempt
                and line.get("role") == "mathematician_adversarial"):
            return True
    return False


def same_row_runs(t, row_id, root=None):
    """The CONSECUTIVE `CHECKING -> READY` lines for this code whose `row` is `row_id`.

    IT READS THE LOG, so the cap survives a crash, and a DIFFERENT matching row starts a
    new run at zero, which is what "the maintainer fixed the row" looks like.
    """
    n = 0
    for line in log_lines(root):
        if line.get("task") != t.code or line.get("from") != CHECKING:
            continue
        if line.get("to") == READY and line.get("row") == row_id:
            n += 1
        elif line.get("to") == READY:
            n = 0                              # a different row: the run restarts
    return n


def review_brief(t, slot, root=None):
    """The program-written review brief, `agents/tasks/<CODE>/review-<PRED>.md`. AD27.

    `launch()` demands a brief file, so the review needs one, and the mathematician never
    writes it. It carries FOUR sections and no fewer, which is what satisfies the seven
    KEPT refusals of section 6.2 by construction: `## SCOPE (write)`, `## ARCHIVE`,
    `## LITERATURE` and `## HEAD`, plus the three questions.

    **IT CARRIES NO BRANCH BLOCK and the pre-flight never reads it**, because it produces
    no routing of its own. The two file names differ on purpose: the review BRIEF is
    `review-<PRED>.md` and the review OUTPUT is `review-of-<PRED>.md`, so a branch
    globbing `review-of-*.md` reads the reviewer's work and never the program's own input.

    IT RETURNS None WHEN IT CANNOT WRITE, and rule (f) then parks with `reason: "launch"`.
    A dispatch whose brief file does not exist is a KEPT refusal of section 6.2 firing
    later and louder, so the program refuses at the point it knows.
    """
    root = ROOT if root is None else Path(root)
    try:
        pred = f"{t.code}#{max(1, (_int(t.attempt, 1) or 1) - 1)}"
        safe = pred.replace("#", "-").replace(".", "-")
        d = root / "agents" / "tasks" / agents_tree.normalise(t.code)
        d.mkdir(parents=True, exist_ok=True)
        out = d / f"review-{safe}.md"
        rel = str(out.relative_to(root))
    except (OSError, ValueError, TypeError):
        return None
    outfile = rel.replace("review-", "review-of-", 1)
    body = [
        f"# {t.code}: adversarial review of {pred}",
        "",
        "## HEAD",
        f"head_slot: {slot}",
        "machine: shared",
        "",
        "## SCOPE (write)",
        f"- {outfile}",
        "- dev/JOURNAL.md",
        "",
        "## THE OBLIGATION",
        f"Attack the return of {pred}. Write {outfile} and nothing else, plus one",
        "`dev/JOURNAL.md` entry for the return you attacked.",
        "",
        "## WHAT YOU READ, and all of it is tracked",
        f"- the newest `agents/tasks/{agents_tree.normalise(t.code)}/*-report.md`",
        f"- the work brief `{t.brief}`",
        f"- the probes `agents/tasks/{agents_tree.normalise(t.code)}/*.agda`",
        f"- the six facts, `model`, `effort` and `heads_sha256` of that instance in",
        "  `dev/pod/transitions/`",
        "",
        "## THE THREE QUESTIONS, and answer only these",
        "1. Does the predecessor's verdict LINE match its own BODY? The project measured",
        "   that failure twice on 2026-08-16: `[LJ-1.375]` caught it on `[LJ-1.373]`, and",
        "   `[LJ-1.376]` named the orchestrator's own unread live record the costliest",
        "   defect in the tree.",
        "2. Is every load-bearing claim backed by a `file:line` that resolves today?",
        "3. Is the predecessor's enumeration complete?",
        "",
    ]
    out.write_text("\n".join(body), encoding="utf-8")
    try:
        import retrieve as retrieve_mod
        query = retrieve_mod.build_query([outfile], [], f"review of {pred}")
        with open(out, "a", encoding="utf-8") as fh:
            fh.write(retrieve_mod.candidate_block(
                "ARCHIVE", query, retrieve_mod.ARCHIVE_SCOPE) + "\n")
            fh.write(retrieve_mod.candidate_block(
                "LITERATURE", query, retrieve_mod.LITERATURE_SCOPE) + "\n")
    except ImportError:
        with open(out, "a", encoding="utf-8") as fh:
            fh.write("## ARCHIVE (program-generated, do not edit)\n\nNO HIT\n\n")
            fh.write("## LITERATURE (program-generated, do not edit)\n\nNO HIT\n")
    return rel


def model_readback_ok(task, model):
    """The read-back refusal of `dev/pod/heads.toml`, in the direction B4 MEASURED.

    A wrong model ID passes the loader when `legal.models` holds it, and then fails INSIDE
    the pane: `herdr agent start` still returns `agent_started`, the agent reaches
    `working` and then `done`, and every guard in the launcher reads that as a healthy run
    (`agents/tasks/L9-0/l9.0-b4-model-ids.md:95-101`).

    THE RULE, and it is the CORRECTED direction. Read the banner line that ends with
    `. Claude Max`. PARK the task when that line contains the requested model string
    VERBATIM, case sensitively, because `Opus 5` contains `opus` under a case-insensitive
    match. A resolving ID prints a DISPLAY NAME and never its own ID. The design's own
    text at `dev/memos/L9-pod-program-design.md:1754-1755` is REFUTED by that measurement:
    it parks every correct dispatch and passes every wrong one.

    A banner that cannot be read is NOT a refusal, because the rule fires only on a
    positive detection.
    """
    try:
        done = subprocess.run(["herdr", "agent", "read", task], capture_output=True,
                              text=True, timeout=60)
    except (OSError, subprocess.SubprocessError):
        return True
    for line in done.stdout.split("\n"):
        if "Claude Max" in line and model in line:
            return False
    return True


def launch(t, brief, role, root=None):
    """Rule (f)'s dispatch. It returns the PID, or None when a KEPT refusal fired.

    The launcher's `launch()` returns an exit CODE and writes the pid into its registry,
    so this reads the pid back from that registry under the launcher's own lock. NEVER
    SILENT: a refusal returns None and rule (f) parks with `reason: "launch"`.

    The head is resolved ONCE, here, from `dev/pod/heads.toml` (AD26), and the four values
    are written onto the task so the transition log records what RAN.

    EVERY FAILURE PATH RETURNS None AND NONE RAISES. The launcher is a large program that
    reads a registry, a vendor pin, a brief and a pane server, and any of them can fail in
    a way it did not plan for. Rule (f) parks with `reason: "launch"` on None, which is a
    park the maintainer batch reads; a raise here would abandon the whole tick with the
    dispatch possibly already performed.
    """
    root = ROOT if root is None else Path(root)
    if not brief:
        return None
    mod = facts_mod.launcher()
    if mod is None:
        return None
    try:
        head = heads_mod.head(role)
    except heads_mod.HeadsError:
        return None
    t.role, t.model, t.effort = role, head["model"], head["effort"]
    t.harness, t.sandbox = head["harness"], head["sandbox"]
    path = Path(brief) if Path(brief).is_absolute() else root / brief
    try:
        mod.HARNESS = head["harness"]
        # A14: THE TIER TRAVELS TO THE PANE. `launch()` defaults it to `AGDA_TIER_DEFAULT`,
        # which is WIDE, so omitting it ran every HEAVY task at the WIDE caliber AND wrote
        # `"tier": "wide"` into the registry record that `agda_heap_sum_over()` reads. The
        # heap-sum guard then budgeted 8 GB for a worker holding 12.
        rc = mod.launch(t.code, path, bool(t.agda), head["sandbox"], head["model"],
                        effort=head["effort"], tier=tier_of(t))
    except SystemExit:
        return None                            # the launcher REFUSED on a corrupt registry
    except Exception:                          # noqa: BLE001. See the docstring
        return None
    if rc != 0:
        return None
    try:
        if not model_readback_ok(mod.herdr_name(t.code), head["model"]):
            return None
        with mod.registry_lock():
            d = (mod.load().get("dispatches") or {}).get(t.code) or {}
    except Exception:                          # noqa: BLE001. The pid is unreadable
        return None
    if not isinstance(d, dict) or not d.get("pid"):
        return None
    for f in ("pid", "proc_start", "log", "final", "started", "events"):
        setattr(t, f, d.get(f))
    return d["pid"]


def rec_alive(t):
    """The launcher's own liveness test, unchanged. It reads `ps` and `os.kill(pid, 0)`.

    THE ASYMMETRY IS DELIBERATE and it copies `alive()` at
    `alive()` in `scripts/pod/launcher.py`: a dead agent holding a slot is visible, while a live
    agent read as dead makes a gate green over a half-written tree.
    """
    mod = facts_mod.launcher()
    if mod is None:
        return False
    try:
        return bool(mod.rec_alive(t.registry_record()))
    except Exception:                          # noqa: BLE001. `ps` and `os.kill` both fail
        # A LIVENESS TEST THAT RAISES IS NOT A LIVE WORKER. The asymmetry is the launcher's
        # own: a dead agent holding a slot is visible, while a live agent read as dead
        # makes a gate green over a half-written tree. Reading False here RETURNS the task,
        # and the acceptance runner then measures the tree that is really there.
        return False


def kill_process_group(pid):
    """The deadline kill. It targets the process GROUP, which `start_new_session=True`
    in `launch()`, `scripts/pod/launcher.py`, allows. Without a deadline a hung worker holds an
    Agda slot for ever, because the only other exit from RUNNING is a dead pid."""
    n = _int(pid)
    if not n or n <= 0:
        return False                           # a missing or non-numeric pid kills nothing
    try:
        os.killpg(os.getpgid(n), signal.SIGTERM)
        time.sleep(2)
        os.killpg(os.getpgid(n), signal.SIGKILL)
    except OSError:                            # ProcessLookupError is an OSError
        return False
    return True


# ---------------------------------------------------------------- the close


def commit_task(t, rec, root=None):
    """The DONE handler: `ledger.py --write`, then R8's explicit-path commit.

    R8 COMMITS BY EXPLICIT PATH AND NEVER PUSHES. `check-live-territory.py:4-6` records
    the cost of the alternative: on 2026-08-13 two `git add -A` calls swept a sibling
    agent's work into the orchestrator's commit. One push is one CI run and one deploy,
    so the program never pushes.

    A `ledger.py --write` REFUSAL DOES NOT BLOCK THE CLOSE, and the reason is that the
    commit here names explicit paths and never `dev/ledger.toml`. The refusal is recorded
    on the record as `ledger`, the digest prints it, and the owed re-measurement is a
    maintainer input. Blocking here would need a tenth park reason, and section 5.5's list
    of nine is closed.
    """
    root = ROOT if root is None else Path(root)
    rc, out = 0, ""
    try:
        done = subprocess.run([sys.executable, "scripts/measure/ledger.py", "--write"],
                              cwd=root, capture_output=True, text=True, timeout=600)
        rc, out = done.returncode, (done.stdout + done.stderr).strip()
    except (OSError, subprocess.SubprocessError) as e:
        rc, out = 1, str(e)
    rec["ledger"] = "clean" if rc == 0 else "refused"
    rec["ledger_note"] = out[-400:]
    paths = [p for p in (rec.get("facts") or {}).get("changed_files") or []
             if isinstance(p, str)]
    if paths:
        try:
            table_mod.git_commit([root / p for p in paths],
                                 f"pod: {t.code} done, row {t.row}")
        except Exception:                      # noqa: BLE001. `git_commit` returns False
            # A FAILED COMMIT IS NOT A FAILED CLOSE, and section 4.1 property 4 rules it:
            # the work stands in the tracked file uncommitted, `pod stop` commits it, and
            # both checklists run `pod stop` before they require a clean tree.
            pass
    return rc == 0


def notify_owner(why, root=None):
    """The stop push, AD20. The loop has exactly TWO stops and both push immediately.

    Rule (d), when the parked count reaches 3, and `apply()`, when a `stop_loop` row
    matched. Neither waits for the digest. `scripts/ops/bark-push.sh` is day 7's and it
    reads both secrets from the environment; until it exists the push is a recorded
    no-op, because a missing channel must never stop the loop from stopping.
    """
    root = ROOT if root is None else Path(root)
    if not BARK.is_file():
        return False
    env = dict(os.environ, BARK_TITLE="POD 已停止", BARK_GROUP="Bedrock POD",
               BARK_BODY=str(why)[:140])
    try:
        subprocess.run(["sh", str(BARK)], cwd=root, env=env, timeout=60,
                       stdin=subprocess.DEVNULL, capture_output=True)
    except (OSError, subprocess.SubprocessError):
        return False
    return True


# ---------------------------------------------------------------- rule (e)'s helpers


def hours_since_last_batch(root=None):
    """Hours since the newest `batch` line in the transition log, or a large number.

    A log with no batch line has never run one, so the trigger must fire: returning a
    large number is what makes the FIRST batch happen, and returning 0 would starve it.
    """
    newest = None
    for line in log_lines(root):
        if line.get("event") == "batch":
            newest = _epoch(line.get("ts")) or newest
    if newest is None:
        return 1e9
    return (time.time() - newest) / 3600.0


def hours_since_last_refill(root=None):
    """Hours since the newest `refill` line, or a large number. A11's floor reads it.

    IT READS THE LOG AND HOLDS NO STATE, exactly as `hours_since_last_batch()` does, so
    the floor survives a crash and a restart cannot turn one refill an hour into one
    refill a tick.
    """
    newest = None
    for line in log_lines(root):
        if line.get("event") == "refill":
            newest = _epoch(line.get("ts")) or newest
    if newest is None:
        return 1e9
    return (time.time() - newest) / 3600.0


def _refill_min_hours():
    """A11's floor between two rule (g) dispatches. The OWNER'S KEY WINS when it exists.

    `dev/pod/heads.toml` is the one home of a limit and this program may not edit it, so
    the constant here is a floor and not a second home: `[limits].refill_min_hours` beats
    it the moment the owner adds the key.
    """
    try:
        value = heads_mod.limits().get("refill_min_hours")
    except heads_mod.HeadsError:
        return REFILL_MIN_HOURS
    return value if isinstance(value, (int, float)) and value > 0 else REFILL_MIN_HOURS


def dispatchable_entries(st):
    """Every `dev/pod/queue.toml` entry rule (a1) would still turn into a task.

    A11 counts THIS and not the raw entries. An entry with no `brief` is a REQUEST and
    never a task (section 5.2), and an entry whose code already carries a state record was
    created on an earlier tick, so neither one is work waiting for a free slot.
    """
    out = []
    for e in queue_entries():
        code, brief = e.get("code"), e.get("brief")
        if not isinstance(code, str) or not isinstance(brief, str) or not brief:
            continue
        if code in st.tasks:
            continue
        out.append(e)
    return out


def maintainer_scope_ok(root=None, proposal=None):
    """R15, checked BEFORE the replay: the batch wrote the proposal file and nothing else.

    IT TAKES FACT 4'S SNAPSHOT, `git status --porcelain --untracked-files=all`, and
    REFUSES when any path other than the proposal file appears, tracked or untracked. The
    `--untracked-files=all` flag is why the untracked half is visible, and a check that
    reads only the tracked half discards the information the flag paid for: a maintainer
    that writes a NEW file writes an untracked path, which is exactly the class the flag
    exists to reveal.

    TWO PATHS ARE NOT THE MODEL'S WRITE AND R15 IS ABOUT THE MODEL'S WRITE. `.pod-state/`
    is the loop's own runtime state, and a `*.toml.admitted` file is the PROGRAM's own
    rename of an already admitted proposal. Counting either one would make every batch
    after the first refuse on `scope` for a path no model touched, and the maintainer
    would never write another row.
    """
    root = ROOT if root is None else Path(root)
    allowed = {proposal} if proposal else set()
    bad = [p for p in facts_mod._status_paths(root)
           if p not in allowed and not p.startswith(".pod-state/")
           and not p.endswith(".toml.admitted")]
    return (not bad), bad


def harvest_batch(st, root=None):
    """Rule (e)'s first act: R15's scope check, then the replay, then the append.

    THE GATE IS THE REPLAY and it runs through the SAME writer admission uses. On ADMIT
    the rows go in through `write_table()` and the commit is by explicit path. On REJECT
    the moved records go back into the proposal file and the batch parks, which is a
    maintainer input at the next batch.

    DISCLOSED NARROWING of the ruled text: the ruling names `dev/pod/table.toml` as the
    maintainer's one write path, and the design gives it the PROPOSAL file instead,
    because the replay gate must sit between the model and the table. That is narrower and
    never wider.
    """
    root = ROOT if root is None else Path(root)
    d = root / "dev" / "pod" / "proposals"
    if not d.is_dir():
        return []
    try:
        import replay as replay_mod            # deferred: replay imports table
    except ImportError as e:
        # THE GATE IS THE REPLAY, so a batch with no replay is not admitted at all. The
        # proposal file stays where it is and the next batch reads it again.
        return [emit_event(st, "batch", result="refused",
                           why=f"the replay module is unreadable: {e}", root=root)]
    out = []
    for path in sorted(d.glob("*.toml")):
        rel = str(path.relative_to(root))
        try:
            data = tomllib.loads(path.read_text(encoding="utf-8"))
        except (OSError, ValueError, UnicodeDecodeError) as e:
            out.append(emit_event(st, "batch", result="parse",
                                  proposal=rel, why=str(e)[:200], root=root))
            continue
        if not isinstance(data, dict):
            out.append(emit_event(st, "batch", result="parse", proposal=rel,
                                  why="the proposal is not a TOML table", root=root))
            continue
        ok, bad = maintainer_scope_ok(root, rel)
        if not ok:
            out.append(emit_event(st, "batch", result="scope",
                                  proposal=rel, paths=bad[:20], root=root))
            continue
        queued = data.get("queue")
        for entry in queued if isinstance(queued, list) else []:
            queue_append(entry)                # R15: a REQUEST is not a write
        rows = data.get("row")
        if not isinstance(rows, list) or not rows:
            out.append(emit_event(st, "batch", result="empty",
                                  proposal=rel, root=root))
            continue
        try:
            slots = table_mod.head_slots(root)
            old = table_mod.load_table(TABLE, slots)
            new = old + [table_mod.check_row(dict(r), slots) for r in rows]
            table_mod.check_table(new, slots)
            verdict, moved = replay_mod.replay(old, new, replay_mod.corpus())
        except Exception as e:                 # noqa: BLE001. A PROPOSAL IS UNTRUSTED TEXT
            # `check_row()` raises `TableError` for every shape it knows, and a `[[row]]`
            # value that is not a table reaches `dict(r)` before it, which raises
            # `TypeError` instead. The model wrote this file, so every raise it can
            # produce is one refusal line and never a stopped loop.
            out.append(emit_event(st, "batch", result="refused",
                                  proposal=rel, why=f"{type(e).__name__}: {e}"[:200],
                                  root=root))
            continue
        if verdict != "ADMIT":
            out.append(emit_event(st, "batch", result="reject", proposal=rel,
                                  moved=[list(m) for m in moved][:20], root=root))
            continue
        try:
            table_mod.write_table(new)
            # THE RENAME COMES FIRST AND THE COMMIT CARRIES BOTH PATHS. The admitted
            # proposal is the evidence of what the maintainer proposed, and R8 commits by
            # explicit path, so leaving it untracked would make the NEXT batch refuse on
            # `scope` for a file the program itself renamed. Committing the old path too
            # records the rename when the proposal was already tracked.
            done = path.with_suffix(".toml.admitted")
            path.rename(done)
            table_mod.git_commit([TABLE, path, done], f"pod: admit batch {path.name}")
        except (OSError, table_mod.TableError) as e:
            out.append(emit_event(st, "batch", result="refused", proposal=rel,
                                  why=f"the admitted table did not land: {e}"[:200],
                                  root=root))
            continue
        out.append(emit_event(st, "batch", result="admit",
                              proposal=rel, rows=len(rows), root=root))
    return out


def park_reason_of(code, root=None):
    """The newest park reason for one code, READ FROM THE LOG and not from the fold.

    `replay_log()` above restores `park_reason` from a key the line does not carry:
    `emit()` writes the field as `reason`. A folded state therefore carries no reason,
    and the batch brief would name `None` for every park after a restart. The log line
    always carries one, so the batch reads it there.
    """
    reason = None
    for line in log_lines(root):
        if line.get("task") == code and line.get("to") == PARKED and line.get("reason"):
            reason = line["reason"]
    return reason


def batch_lists(root=None):
    """The three log-derived lists of section 6.7, as brief lines.

    THE BATCH AND THE DIGEST COUNT ONE THING ONE WAY. `digest.maintainer_inputs()`
    produces every list, so the maintainer never sees a shadowing count the owner's
    digest does not. The import is DEFERRED, because `digest` imports this module.
    """
    try:
        import digest as digest_mod
        got = digest_mod.maintainer_inputs(ROOT if root is None else Path(root))
        out = ["", f"## THE NO-MATCH RECORDS, window {got['hours']:g} hours"]
        rows = []
        for rec in got["no_match"]:
            f = rec.get("facts") or {}
            rows.append(f"- {rec.get('task')}: exit_code {f.get('exit_code')}, "
                        f"error_class {f.get('error_class')}, "
                        f"obligations_delta {f.get('obligations_delta')}, "
                        f"record {rec.get('run')}")
        out += rows or ["- NONE"]
        out += ["", "## THE SHADOWING LIST, section 4.4"]
        out += [f"- row `{rid}` lost {n} time(s) in the window"
                for rid, n in got["shadowed"]] or ["- NONE"]
        out += ["", "## THE EXPIRY FALLOUT, section 4.6"]
        out += [f"- record {r['record']} ({r['task']}) was won by the expired row "
                f"`{r['row']}` and now falls to "
                f"{('`' + r['falls_to'] + '`') if r['falls_to'] else 'NO MATCH'}"
                for r in got["fallout"]] or ["- NONE"]
    except Exception as e:                     # a broken reader must not stop the batch
        # THE WHOLE FORMATTING SITS INSIDE THE GUARD, and not only the call. `digest.py`
        # is another module's contract: a key it renames raises `KeyError` in the f-string
        # below the call, where the guard did not reach, and that raise ran inside rule (e)
        # on every tick.
        return ["", "## THE LOG-DERIVED LISTS", "",
                f"UNAVAILABLE: {type(e).__name__}: {str(e)[:200]}"]
    return out


def spawn_maintainer(st, root=None):
    """AD2 and AD15: one program-written brief at `agents/tasks/POD-BATCH/<ts>.md`.

    IT IS PINNED UNDER `agents/tasks/` so KEPT refusal 2 of section 6.2 holds and
    `SAFE_TASK` in `scripts/pod/launcher.py` admits the name. The program fills it
    from the log: every PARKED code with its reason and its facts, every no-match record
    in the window, and the shadowing and expiry lists.

    AN `attempt_max:<row id>` PARK IS THE LOUDEST INPUT, because it names a row that
    matched again and again and never changed the facts.
    """
    root = ROOT if root is None else Path(root)
    ts = time.strftime("%Y%m%d-%H%M%S")
    d = root / "agents" / "tasks" / "POD-BATCH"
    try:
        d.mkdir(parents=True, exist_ok=True)
    except OSError:
        return None
    proposal = f"dev/pod/proposals/{ts}.toml"
    parked = st.of(PARKED)
    body = [
        f"# POD-BATCH: propose table rows for {len(parked)} parked tasks, {ts}",
        "",
        "## HEAD",
        "head_slot: maintainer",
        "machine: shared",
        "",
        "## SCOPE (write)",
        f"- {proposal}",
        "",
        "## THE OBLIGATION",
        f"Write `{proposal}` in the row schema of `dev/pod/table.toml`. Write nothing",
        "else. You never edit `dev/pod/table.toml`, never edit a brief and never run the",
        "loop. A brief repair is a `[[queue]]` request in the same file, naming the check",
        "that failed; the program appends it and the mathematician repairs the brief.",
        "",
        "## THE PARKED TASKS, from the transition log",
    ]
    for t in parked:
        f = (t.record or {}).get("facts") or {}
        reason = t.park_reason or park_reason_of(t.code, root) or ""
        loud = (" LOUDEST INPUT: this row matched again and again and never changed the"
                " facts." if reason.startswith("attempt_max:") else "")
        body.append(f"- {t.code}: reason `{reason}`, exit_code "
                    f"{f.get('exit_code')}, error_class {f.get('error_class')}, "
                    f"obligations_delta {f.get('obligations_delta')}, "
                    f"{len(f.get('changed_files') or [])} changed files.{loud}")
    body += batch_lists(root)
    body += ["", "## ARCHIVE (program-generated, do not edit)", "", "NO HIT", "",
             "## LITERATURE (program-generated, do not edit)", "", "NO HIT", ""]
    brief = d / f"{ts}.md"
    try:
        brief.write_text("\n".join(body), encoding="utf-8")
    except OSError:
        return None                            # no brief, no dispatch. The next tick tries
    mod = facts_mod.launcher()
    if mod is None:
        return None
    try:
        head = heads_mod.head("maintainer")
        mod.HARNESS = head["harness"]
        rc = mod.launch("POD-BATCH", brief, False, head["sandbox"], head["model"],
                        effort=head["effort"])
    except SystemExit:
        return None
    except Exception:                          # noqa: BLE001. The batch is not the loop
        # THE MAINTAINER IS AD15'S BATCH AND NOT A TASK. A dispatch that fails costs one
        # batch, which the same trigger re-fires; a raise here would stop the loop from
        # OBSERVING and CLOSING work that has already returned.
        return None
    return str(brief.relative_to(root)) if rc == 0 else None


def write_digest(st, root=None):
    """Section 8's digest. It hangs off the same trigger as the maintainer batch.

    THE PROGRAM GENERATES IT AND NO MODEL WRITES IT. `scripts/pod/digest.py` is day 7's;
    until it exists this records the trigger and prints nothing, because a digest with
    invented fields is worse than no digest (every field names its source, and a field
    with no source is not in the digest).
    """
    root = ROOT if root is None else Path(root)
    if not DIGEST.is_file():
        return None
    try:
        subprocess.run([sys.executable, str(DIGEST)], cwd=root, timeout=600,
                       capture_output=True)
    except (OSError, subprocess.SubprocessError):
        return None
    return str(DIGEST.relative_to(root))


def prune_logs(days=30, st=None, root=None):
    """Section 4.0's retention: 30 days after the task reaches DONE or PARKED.

    THE COMPARABLE HOLDS 931 MB OVER 1,017 FILES, which is why a retention exists at all.
    A log whose task is still live is NEVER pruned, whatever its age, because the file is
    the only transcript of a running worker.
    """
    root = ROOT if root is None else Path(root)
    d = root / ".pod-state" / "logs"
    if not d.is_dir():
        return 0
    closed = {c for c, t in (st.tasks if st else {}).items()
              if t.status in (DONE, PARKED)}
    cut, n = time.time() - days * 86400, 0
    for f in sorted(d.iterdir()):
        if not f.is_file():
            continue
        owner = next((c for c in closed if f.name.startswith(c + "-")), None)
        if owner is None:
            continue
        try:
            if f.stat().st_mtime < cut:
                f.unlink()
                n += 1
        except OSError:
            continue
    return n


# ---------------------------------------------------------------- apply(), section 5.1


def apply(action, t, rec, row_id, st, root=None):
    """The six actions rule (c) does not handle inline. It returns STOP only for
    `stop_loop`.

    Every one of the eight actions of section 4.2 reaches an implementation here or in
    rule (c). `done` and `accept` never arrive: rule (c) has them.
    """
    r = "row:" + str(row_id)                   # the park reason, section 5.5
    row = _row_of(row_id, root)
    if action == "park":
        emit(st, t, CHECKING, PARKED, rec=rec, row=row_id, reason=r, root=root)
    elif action == "park_and_split":
        queue_append(split_entry(t, rec))      # a REQUEST entry, section 5.2
        emit(st, t, CHECKING, PARKED, rec=rec, row=row_id, reason=r, root=root)
    elif action == "redispatch":
        t.attempt = _int(t.attempt, 0) + 1
        emit(st, t, CHECKING, READY, rec=rec, row=row_id, root=root)
    elif action == "redispatch_narrower":
        t.scope_narrow = accept_mod.first_failing_target(rec)
        t.attempt = _int(t.attempt, 0) + 1
        emit(st, t, CHECKING, READY, rec=rec, row=row_id,
             scope_narrow=t.scope_narrow, root=root)
    elif action == "escalate":
        t.head_slot = (row or {}).get("head_slot")     # AD27. Rule (f) dispatches it
        t.attempt = _int(t.attempt, 0) + 1
        emit(st, t, CHECKING, READY, rec=rec, row=row_id,
             head_slot=t.head_slot, root=root)
    elif action == "stop_loop":
        # THE TASK IS PARKED FIRST, AND THAT ORDER IS DELIBERATE. The task must not stay
        # CHECKING across the stop; the park line names the row, and `pod resume`
        # re-routes it through rule (a2) like any other park.
        emit(st, t, CHECKING, PARKED, rec=rec, row=row_id,
             reason="stop_loop:" + str(row_id), root=root)
        emit(st, "", NONE, LOOP_STOPPED, why="row " + str(row_id), root=root)
        STOPPED_FILE.parent.mkdir(parents=True, exist_ok=True)
        STOPPED_FILE.touch()
        notify_owner("row " + str(row_id), root)
        return STOP
    else:
        raise KeyError(action)                 # done and accept never arrive
    return CONTINUE


def _row_of(row_id, root=None):
    """One row by id, or None. `escalate` reads its `head_slot`; R4 reads its `outcome`.

    A TABLE THAT DOES NOT LOAD GIVES None, and both readers hold for that: `r4_holds()`
    reads `(row or {}).get("outcome")`, so a `done` close with no readable row needs all
    six conjuncts, which is the strict direction.
    """
    try:
        for row in table_mod.load_table(TABLE, table_mod.head_slots(root)):
            if row.get("id") == row_id:
                return row
    except (table_mod.TableError, heads_mod.HeadsError, OSError):
        return None
    return None


# ---------------------------------------------------------------- the tick, section 5.1


def pod_tick(st=None, root=None):
    """ONE PASS. `pod run` sleeps, not this. It returns CONTINUE or STOP.

    THE ORDER OF THE SEVEN RULES IS FIXED. Rule (f) is the ONLY writer of a task row and
    it runs late, after the pre-flight, the admission and `admits()`, so each step guards
    the next: a branch block that does not parse can never reach `dev/pod/table.toml`, and
    by the time a worker returns, rule (c)'s `route()` can see this task's rows.

    THE WATCHDOG IS CONFIRMED FIRST (A13), before any rule consults `admits()`. Rule (g)
    RUNS LAST (A11), because a slot is free only once rule (f) has filled every slot it
    can, and because rule (g) DISPATCHES: `_rule_f()` returns STOP on `.pod-state/STOPPED`
    and this returns before rule (g) ever runs.
    """
    root = ROOT if root is None else Path(root)
    st = load_state() if st is None else st
    replay_log(st, root)                       # apply every log line with seq > st.seq

    watchdog_tick(st, root)                    # A13. Every tick confirms the backstop
    _rule_a1(st, root)
    _rule_a2(st, root)
    _rule_b(st, root)
    if _rule_c(st, root) is STOP:
        return STOP
    if _rule_d(st, root) is STOP:
        return STOP
    _rule_e(st, root)
    if _rule_f(st, root) is STOP:
        return STOP
    _rule_g(st, root)                          # A11. A free slot with an empty queue
    return CONTINUE


def _rule_a1(st, root):
    """(a1) CREATE. `dev/pod/queue.toml` is the ONLY producer of a task.

    An entry with no `brief` is a REQUEST and never a task, so it is skipped here and the
    digest prints it until the mathematician adds the brief path.
    """
    for e in dispatchable_entries(st):
        code, brief = e["code"], e["brief"]
        # TWO ENTRIES, ONE CODE. The list was built before the first of them created its
        # record, and section 5.2 rules ONE state record per code.
        if code in st.tasks:
            continue
        inject_survey(brief, root)             # R10, 7.4. BEFORE pre-flight P15 reads it
        stamp_pod_marker(code, root)           # section 9.3, one `.pod` line per task
        t = Task(code, brief=brief, status=READY, attempt=0,
                 exclusive=machine_class(brief, root),
                 tier=task_tier(brief, root))  # A14, copied ONCE, exactly as `exclusive`
        st.tasks[code] = t
        emit(st, t, NONE, READY, brief=brief, root=root)
    for code in archived_codes(st, root):
        try:
            table_mod.expire_rows(code)        # section 4.6, the second expiry trigger
        except (table_mod.TableError, heads_mod.HeadsError, OSError):
            continue                           # a table that does not load expires nothing


def _rule_a2(st, root):
    """(a2) UNPARK. AD16, and it is automatic. A park is never terminal.

    Each of the nine park reasons has its own un-park test, and the branch is what makes
    a pre-flight park recoverable: a task refused BEFORE dispatch has no record, so
    `route()` cannot un-park it, and this re-runs `preflight()` instead.
    """
    try:
        mtime = TABLE.stat().st_mtime
    except OSError:
        mtime = 0.0
    for t in list(st.of(PARKED)):
        reason = t.park_reason if isinstance(t.park_reason, str) else ""
        if reason.startswith("preflight:"):
            if _preflight(t, root) == []:
                emit(st, t, PARKED, READY, root=root)
            continue
        if reason in ("admission", "launch"):
            if (t.parked_at or 0) < mtime:
                emit(st, t, PARKED, READY, root=root)      # retry, section 4.1
            continue
        if t.record is None:
            continue                           # a no-change park, section 5.5
        if (t.parked_at or 0) >= mtime:
            continue
        row_id, _act = _route(t.record, root)  # the WHOLE record, B3
        if row_id is None:
            continue
        if reason == "attempt_max:" + str(row_id):
            continue                           # B2: the guilty row did not change
        emit(st, t, PARKED, READY, row=row_id, root=root)


def _route(rec, root):
    """`route()` over the WHOLE record, and a record it cannot read matches NOTHING.

    `matches()` in `scripts/pod/table.py` INDEXES the six fact keys, so a record with
    a missing or mistyped fact raises `KeyError` there, and a `[row.when]` key the loader
    never saw raises `KeyError` by design (R1). Both would stop the loop from inside rule
    (a2) and rule (c). NO MATCH is the honest answer and it is loud: the task PARKS with
    `no-match`, three parks stop the loop, and the owner gets the push.
    """
    try:
        return table_mod.route(_table(root), rec)
    except Exception:                          # noqa: BLE001. See the docstring
        return None, None


def _preflight(t, root):
    """AD21's pre-flight, and a check that RAISES refuses the brief rather than the loop.

    The pre-flight reads the brief, resolves every path it names and runs
    `check-closure.py`, so a missing file or a broken tool raises inside it. The refusal
    it returns is a LIST of strings and rule (f) reads `d[0].split()[0]`, so a raise
    becomes one synthetic entry with the same shape: the task parks with a `preflight:`
    reason and rule (a2) re-runs it on the next tick, which is what repairs it. `P0` is
    THIS program's id and never one of the pre-flight's own `P1` to `P22`, so a reader can
    tell a refused brief from a pre-flight that could not run at all.
    """
    try:
        out = preflight_mod.preflight(_abs(t.brief, root), root, show=False)
    except Exception as e:                     # noqa: BLE001. See the docstring
        return [f"P0 the pre-flight could not run: {type(e).__name__}: {e}"]
    return out if isinstance(out, list) else []


def _rule_b(st, root):
    """(b) OBSERVE. A worker is dead when its pid is dead, or when it ran too long.

    `worker_deadline_s` is NEW AND IT IS NEEDED. The only other exit from RUNNING is a
    dead pid, so a hung worker would hold an Agda slot for ever.
    """
    deadline = _limits()["worker_deadline_s"]
    for t in list(st.of(RUNNING)):
        if t.elapsed() > deadline:
            kill_process_group(t.pid)
            emit(st, t, RUNNING, RETURNED, why="deadline", root=root)
        elif not rec_alive(t):
            emit(st, t, RUNNING, RETURNED, why="pid dead", root=root)


def _rule_c(st, root):
    """(c) ACCEPT. AD13 runs here, ONE TASK AT A TIME.

    `admits(st, t, agda=True)` whatever the brief says, because the acceptance runner
    starts Agda for every case of section 4.3.2 except case 4, and the program cannot know
    which case applies until fact 4 is measured.

    AN ACCEPTANCE THAT RAISES IS A RETURN THE PROGRAM CANNOT MEASURE, so R7 applies and
    the task parks with `no-change`. The runner starts Agda, runs six gate commands and
    calls `witness_delta()`, which RAISES BY DESIGN when the task carries no `obl_before`
    (`witness_delta()`, `scripts/pod/witness.py`), and a task folded from a log whose dispatch line was
    lost carries exactly that. Before this guard one such task ended the whole tick in a
    traceback, with the task frozen in CHECKING and no line saying why.
    """
    limits = _limits()
    for t in list(st.of(RETURNED)):
        if not admits(st, t, agda=True):
            continue                           # section 5.6. The runner runs Agda
        emit(st, t, RETURNED, CHECKING, root=root)
        try:
            rec = accept_mod.run_acceptance(t, root)
        except Exception as e:                 # noqa: BLE001. See the docstring
            emit(st, t, CHECKING, PARKED, reason="no-change", root=root,
                 why=f"the acceptance runner raised {type(e).__name__}: {e}"[:400])
            continue
        if rec is None:                        # R7, section 4.3.2 case 3
            emit(st, t, CHECKING, PARKED, reason="no-change", root=root)
            continue
        t.run = rec.get("run")
        emit_retrieval(st, t, root)            # section 7.4 Part 1b, ONE line per return
        row_id, action = _route(rec, root)     # the WHOLE record
        if row_id is None:
            emit(st, t, CHECKING, PARKED, rec=rec, reason="no-match", root=root)
        elif action == "done":
            row = _row_of(row_id, root)
            if not accept_mod.r4_holds(rec, row):
                emit(st, t, CHECKING, PARKED, rec=rec, row=row_id, reason="r4", root=root)
            else:
                commit_task(t, rec, root)      # ledger.py --write, then R8's path commit
                emit(st, t, CHECKING, DONE, rec=rec, row=row_id,
                     scope=(row or {}).get("scope"), root=root)
                try:
                    table_mod.expire_rows(t.code)   # section 4.6, the first trigger
                except (table_mod.TableError, heads_mod.HeadsError, OSError):
                    pass                       # the close stands; the rows expire later
        elif (action in LOOPING
                and same_row_runs(t, row_id, root) + 1 >= limits["attempt_max"]):
            # THE CAP NAMES THE ROW THAT KEPT MATCHING. That is a design error in the ROW
            # and not in the task, and the park is how the maintainer learns of it.
            #
            # IT COVERS THE FOUR LOOPING ACTIONS AND NO OTHER. `park`, `park_and_split`
            # and `stop_loop` do not loop, so capping them would only mean one thing: a
            # row whose action the maintainer CHANGED to `stop_loop` after four accepts
            # would park under the cap and the loop would not stop, which A3 forbids.
            emit(st, t, CHECKING, PARKED, rec=rec, row=row_id,
                 reason="attempt_max:" + str(row_id), root=root)
        elif action == "accept":
            t.attempt = _int(t.attempt, 0) + 1
            emit(st, t, CHECKING, READY, rec=rec, row=row_id, root=root)
        elif apply(action, t, rec, row_id, st, root) is STOP:
            return STOP                        # stop_loop only
    return CONTINUE


def _rule_d(st, root):
    """(d) STOP. AD14, at three parked tasks.

    THE STOP STOPS DISPATCHING AND NEVER TOUCHES A RUNNING WORKER, so the PARKED count can
    pass 3 after the stop, because the already-running workers keep landing. That is the
    honest count and gap M7 states it as a ruling.
    """
    if st.count(PARKED) < 3:
        return CONTINUE
    if STOPPED_FILE.exists():
        return STOP                            # already stopped: one line, not one a tick
    emit(st, "", NONE, LOOP_STOPPED, why="3 parked", root=root)
    STOPPED_FILE.parent.mkdir(parents=True, exist_ok=True)
    STOPPED_FILE.touch()
    notify_owner("3 parked", root)
    return STOP


def _rule_e(st, root):
    """(e) MAINTAINER. AD15. The digest hangs off the same trigger, section 8.1."""
    harvest_batch(st, root)                    # R15 then the replay, section 6.7
    prune_logs(30, st, root)                   # the retention of section 4.0
    if hours_since_last_batch(root) >= 12 or st.count(PARKED) >= 3:
        spawn_maintainer(st, root)
        write_digest(st, root)


def _rule_f(st, root):
    """(f) ADMIT AND SPAWN. This is the ONLY writer of a task row, section 4.1.

    THE STOP REFUSES THIS RULE AND NOTHING ELSE. Rules (a1) to (e) keep running, so work
    that already returned is still observed and closed.

    THE ORDER IS FIXED AND EACH STEP GUARDS THE NEXT. The pre-flight refuses a malformed
    brief before any table write. Admission then writes the rows, so by the time the
    worker returns rule (c)'s `route()` can see them; without that step every first
    instance no-matches. `admits()` then decides concurrency, and only then does the
    dispatch point of fact 3 run.
    """
    if STOPPED_FILE.exists():
        return STOP
    ready = sorted(st.of(READY), key=lambda t: (_int(t.attempt, 0), str(t.code)))
    for t in ready:
        d = _preflight(t, root)
        if d:
            emit(st, t, READY, PARKED, reason="preflight:" + _check_id(d[0]),
                 detail=d, root=root)
            continue
        try:
            admitted = table_mod.admit_rows(t.code, _abs(t.brief, root))   # R3 guards it
        except Exception as e:                 # noqa: BLE001. A brief is UNTRUSTED text
            # THE BRANCH BLOCK IS THE MODEL'S OWN TOML and admission parses it against a
            # table this program did not write, so `TableError` is the planned refusal and
            # any other raise is the unplanned one. Both mean the same thing here: the
            # rows did not go in, so the task must not dispatch.
            admitted = False
            d = [f"admission raised {type(e).__name__}: {e}"[:400]]
        if not admitted:
            emit(st, t, READY, PARKED, reason="admission", root=root,
                 detail=d or None)
            continue
        if not admits(st, t):
            continue                           # section 5.6
        slot = t.head_slot or ("mathematician_adversarial"   # AD27, section 6.6
                               if _int(t.attempt, 0) > 1 and not reviewed(t, root)
                               else None)
        if slot:
            b, role = review_brief(t, slot, root), slot
        else:
            b, role = t.brief, head_slot_of(t.brief, root)
        t.head_slot = None                     # R11. The head is resolved once, here
        try:
            t.unbound_before = accept_mod.unbound_findings(root)
            t.obl_before = witness_mod.witness_unresolved(t)  # fact 3 at dispatch, 4.7
        except Exception:                      # noqa: BLE001. NO DISPATCH POINT, NO DISPATCH
            # FACT 3 NEEDS BOTH ENDS. `witness_delta()` refuses at the return when the task
            # carries no `obl_before`, so dispatching without it buys a return the program
            # can never measure. The park is a KEPT refusal firing at the dispatch itself,
            # which is what `reason: "launch"` names (section 5.5).
            emit(st, t, READY, PARKED, reason="launch", root=root,
                 why="the fact 3 dispatch point could not be measured")
            continue
        pid = launch(t, b, role, root)
        if pid is None:                        # a KEPT refusal of 6.2 fired. Never silent
            emit(st, t, READY, PARKED, reason="launch", root=root)
            continue
        emit(st, t, READY, RUNNING, pid=pid, brief=t.brief, dispatched_brief=b,
             role=role, obl_before=t.obl_before, root=root)   # K6. brief is the TASK's
    return CONTINUE


def _rule_g(st, root):
    """(g) REFILL, amendment A11. AN IDLE SLOT IS CURED MECHANICALLY, not reported.

    THE PROGRAM DECIDES ONLY THAT SOMEBODY MUST BE ASKED, and the head decides what the
    work is, so AD1 holds. It is the shape of AD15's maintainer trigger and AD16's
    automatic re-dispatch, both of which the design already admits. Gap M12 recorded the
    loss it closes: `admits()` caps concurrency and nothing required the queue to be
    non-empty, so an empty queue idled the whole loop and no digest field counted it.

    FOUR CONDITIONS, IN THE ORDER THAT COSTS LEAST. No READY task waits, because a READY
    task takes the free slot first. No `dev/pod/queue.toml` entry is dispatchable, which
    is A11's own test. A slot is free, measured by asking `admits()` about the task a
    queue entry would become, so the watchdog limb and both A14 limbs bind here too. And
    the floor since the last refill has passed, because a mathematician that queues
    NOTHING is a legal return and without a floor this would dispatch one refill every
    `tick_seconds`.

    IT IS NOT A TASK AND HOLDS NO STATE RECORD, exactly like `POD-BATCH`. Its return is
    read out of `dev/pod/queue.toml` by rule (a1) on the next tick, so routing it through
    the table would park it for no match and count against AD14's three.

    A REFILL THAT OUTLIVES THE FLOOR IS THE LAUNCHER'S REFUSAL, and it is recorded. The
    launcher refuses a second dispatch under a live task name and a second dispatch on a
    live brief, so an hour-old refill still working writes `result: "REFUSED"` here and
    never a second agent on one brief.
    """
    if st.of(READY) or dispatchable_entries(st):
        return None
    if not admits(st, Task(REFILL_TASK, agda=True, exclusive=False)):
        return None                            # no slot is free
    if hours_since_last_refill(root) < _refill_min_hours():
        return None
    rel = str(REFILL_BRIEF)
    with contextlib.suppress(ValueError):
        rel = str(REFILL_BRIEF.relative_to(root))
    if not REFILL_BRIEF.is_file():
        # THE DEPENDENCY IS NAMED AND NEVER GUESSED. A11 says the orchestrator writes the
        # standing brief and AD3 gives every brief to the mathematician, so the program
        # records the miss and waits. The floor above throttles this line too.
        return emit_event(st, "refill", result="absent", brief=rel, root=root)
    mod = facts_mod.launcher()
    if mod is None:
        return emit_event(st, "refill", result="REFUSED", brief=rel, root=root,
                          why="no launcher module is readable")
    try:
        head = heads_mod.head("mathematician")
        mod.HARNESS = head["harness"]
        rc = mod.launch(REFILL_TASK, REFILL_BRIEF, False, head["sandbox"],
                        head["model"], effort=head["effort"])
    except SystemExit:
        rc, why = 1, "the launcher refused"
    except Exception as e:                     # noqa: BLE001. One refill is not the loop
        rc, why = 1, f"{type(e).__name__}: {e}"[:200]
    else:
        why = None if rc == 0 else f"the launcher exited {rc}"
    return emit_event(st, "refill", brief=rel, root=root, why=why,
                      result="dispatched" if rc == 0 else "REFUSED")


def _check_id(refusal):
    """The check id at the head of one pre-flight refusal, or `P?`.

    Rule (f) writes `preflight:<id>` and rule (a2) branches on the prefix, so an EMPTY
    refusal string must not reach `str.split()[0]` and raise `IndexError` on a park that
    is already the unhappy path.
    """
    parts = str(refusal).split()
    return parts[0] if parts else "P?"


_TABLE_CACHE = {}


def _table(root=None):
    """The rule table, re-read whenever the file changes. `route()` never sees a stale one.

    Rule (a2) compares `t.parked_at` with the table's mtime, so the tick must read the
    table the operator edited and not the one it loaded at start.

    A TABLE THAT DOES NOT LOAD KEEPS THE LAST ONE THAT DID, and holds NOTHING when none
    ever did. A half-written file appears for as long as an editor takes to save, and
    parking three tasks over that would stop the loop for a transient. When no good table
    was ever read the answer is the empty one, so every return parks with `no-match`,
    three parks stop the loop, and the owner gets the push, which is the loud direction.
    """
    try:
        stamp = TABLE.stat().st_mtime
    except OSError:
        return []
    if _TABLE_CACHE.get("stamp") != stamp:
        try:
            _TABLE_CACHE["rows"] = table_mod.load_table(TABLE, table_mod.head_slots(root))
            _TABLE_CACHE["stamp"] = stamp
        except (table_mod.TableError, heads_mod.HeadsError, OSError):
            return _TABLE_CACHE.get("rows", [])
    return _TABLE_CACHE["rows"]


# ---------------------------------------------------------------- the five subcommands


def cmd_tick(argv):
    """One pass, then exit. This is the testable unit and `pod run` calls it."""
    st = load_state()
    verdict = pod_tick(st)
    print(f"pod tick: seq {st.seq}, "
          + ", ".join(f"{s} {st.count(s)}" for s in STATES) + f", {verdict}")
    return 1 if verdict is STOP else 0


def cmd_run(argv):
    """The sleep loop. It holds NO state of its own and re-reads the state file every
    tick, so an operator may stop it at any moment.

    ONE RUNNER AT A TIME: it takes the same `flock` shape `registry_lock()` takes, on a
    separate lock file, for the whole run.

    IT STARTS THE WATCHDOG BEFORE THE FIRST TICK (A13). C-12 says restart
    `scripts/ops/agda-watchdog.sh` at every session; the POD has no session, so `pod run`
    IS the session and this is the start. Every tick then confirms it.
    """
    try:
        tick_seconds = _limits()["tick_seconds"]
    except PodError as e:
        print(f"pod run: REFUSED. {e}", file=sys.stderr)
        return 1
    try:
        POD_STATE.mkdir(parents=True, exist_ok=True)
        runlock = open(POD_STATE / "run.lock", "a+")
    except OSError as e:
        print(f"pod run: REFUSED. {POD_STATE} is not writable: {e}", file=sys.stderr)
        return 1
    try:
        fcntl.flock(runlock, fcntl.LOCK_EX | fcntl.LOCK_NB)
    except OSError:
        print("pod run: REFUSED. another runner holds .pod-state/run.lock. Two runners "
              "racing for the last Agda slot both dispatch (FM1).", file=sys.stderr)
        return 1
    started = watchdog_tick(load_state())       # A13. The session is this process
    print("pod run: the agda watchdog is up" if started else
          "pod run: the agda watchdog is DOWN. Every Agda task is REFUSED until it "
          "starts, because it is C-12's 14 GB backstop and 8 percent free floor (A13).")
    stopping = []
    signal.signal(signal.SIGINT, lambda *_: stopping.append(1))
    signal.signal(signal.SIGTERM, lambda *_: stopping.append(1))
    while not stopping:
        st = load_state()
        if pod_tick(st) is STOP:
            print(f"pod run: STOP at seq {st.seq}. Read the digest, then `pod resume`.")
            return 1
        for _ in range(int(tick_seconds)):
            if stopping:
                break
            time.sleep(1)
    print("pod run: a signal arrived. Every running worker is untouched (section 5.5).")
    return 0


def cmd_resume(argv):
    """Clear `.pod-state/STOPPED`, re-evaluate every PARKED task, then return to the loop.

    THE RESTART IS FIVE STEPS and this is the fifth: read the digest, let the maintainer
    batch run, let the replay admit or refuse each new row, repair any brief the pre-flight
    refused, then run this. A task that now passes goes `PARKED -> READY` and is
    re-dispatched as a FRESH instance (AD16). If three still stand, the loop stops again at
    once, which is correct.

    RULE (a2) ALSO RUNS ON EVERY ORDINARY TICK, so this is a convenience and never the
    only path.
    """
    if STOPPED_FILE.exists():
        STOPPED_FILE.unlink()
    st = load_state()
    replay_log(st)
    before = st.count(PARKED)
    _rule_a2(st, ROOT)
    print(f"pod resume: {before} parked, {st.count(PARKED)} still parked, "
          f"{st.count(READY)} ready")
    if "--once" in argv:
        return 0
    return cmd_run(argv)


def cmd_status(argv):
    """Print the state file as a table. IT WRITES NOTHING."""
    st = load_state()
    replay_log(st)
    print(f"pod status: seq {st.seq}, "
          f"stopped {st.stopped or 'no'}, "
          f"table {'present' if TABLE.is_file() else 'ABSENT'}, "
          f"parked {st.count(PARKED)}/3")
    if not st.tasks:
        print("  no task. `dev/pod/queue.toml` is the only producer of one.")
        return 0
    print(f"  {'code':16s} {'state':9s} {'att':3s} {'tier':5s} {'role':26s} "
          f"{'row':30s} reason")
    for code in sorted(st.tasks):
        t = st.tasks[code]
        # EVERY FIELD IS COERCED BEFORE IT IS FORMATTED. A folded log line can carry any
        # JSON value, and `f"{x:9s}"` raises on a number while `f"{x:<3d}"` raises on a
        # string, so `pod status` was one hand-edited character away from a traceback.
        print(f"  {str(code):16s} {str(t.status):9s} {_int(t.attempt, 0):<3d} "
              f"{tier_of(t):5s} {str(t.role or '-'):26s} {str(t.row or '-'):30s} "
              f"{str(t.park_reason or '')}")
    return 0


def cmd_stop(argv):
    """Write `.pod-state/STOPPED`, wait for every RUNNING worker, then commit.

    THE STOP STOPS DISPATCHING. IT NEVER TOUCHES A RUNNING WORKER. The founding incident
    of the launcher is exactly that: on 2026-08-05 two live agents died because somebody
    stopped the watcher shell that had launched them into its own process group
    (`scripts/pod/launcher.py:7-9`).

    Run it before the checklists of sections 9.1 and 9.2: both require a clean tree and
    this is what commits the tracked table and the tracked log.
    """
    try:
        POD_STATE.mkdir(parents=True, exist_ok=True)
        STOPPED_FILE.touch()
    except OSError as e:
        print(f"pod stop: REFUSED. cannot write {STOPPED_FILE}: {e}", file=sys.stderr)
        return 1
    st = load_state()
    replay_log(st)
    deadline = time.time() + 60 * 60
    while st.count(RUNNING) and time.time() < deadline:
        print(f"pod stop: waiting for {st.count(RUNNING)} running worker(s). "
              f"They are NOT killed.")
        time.sleep(30)
        st = load_state()
        replay_log(st)
        _rule_b(st, ROOT)
    paths = [TABLE] + log_files()
    if CORPUS.is_file():
        paths.append(CORPUS)
    if QUEUE.is_file():
        paths.append(QUEUE)
    try:
        ok = table_mod.git_commit([p for p in paths if Path(p).is_file()],
                                  "pod: stop, commit the tracked table and log")
    except Exception:                          # noqa: BLE001. The flag is already written
        ok = False
    print(f"pod stop: STOPPED written, {st.count(RUNNING)} still running, "
          f"commit {'clean' if ok else 'REFUSED (commit by hand before any checklist)'}")
    return 0


COMMANDS = {"run": cmd_run, "tick": cmd_tick, "resume": cmd_resume,
            "status": cmd_status, "stop": cmd_stop}


def main(argv):
    """The three exit codes, and each one names a different reader.

    0 is clean. 2 is a USAGE error and nothing else: an absent or unknown subcommand, so
    a caller that mistyped sees the usage text and no state moves. 1 is every real
    failure: the loop stopped, a command refused, or a raise reached here.

    THE LAST CLAUSE IS THE UNATTENDED LOOP'S BACKSTOP. Every reader below refuses in
    place, so this should never fire; when it does, one line naming the exception beats a
    traceback that nobody is awake to read, and the exit code stays 1 so a supervisor can
    tell the run failed.
    """
    if not argv or argv[0] not in COMMANDS:
        print(__doc__)
        return 2
    try:
        return COMMANDS[argv[0]](argv[1:])
    except PodError as e:
        print(f"pod: REFUSED. {e}", file=sys.stderr)
        return 1
    except KeyboardInterrupt:
        print("pod: interrupted. Every running worker is untouched (section 5.5).",
              file=sys.stderr)
        return 1
    except Exception as e:                     # noqa: BLE001. See the docstring
        print(f"pod: FAILED. {type(e).__name__}: {e}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
