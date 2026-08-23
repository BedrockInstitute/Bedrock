#!/usr/bin/env python3
"""Regression tests for the POD loop: the tick, the six actions, the log and the writer.

WHY THIS FILE EXISTS. Every rule under test was bought with a measured failure, and each
one, read back wrongly, loses work that a real dispatch already paid for:

1. **The write order of `emit()`.** The tracked log is the truth and `.pod-state/state.json`
   is a cache of its fold. A lost state file is recoverable from the log; a lost log line
   is recoverable from NOTHING. The crash test kills a child process BETWEEN the two
   fsyncs and proves the fold recovers.
2. **The stop refuses rule (f) and nothing else.** On 2026-08-05 two live agents died
   because somebody stopped the watcher shell that had launched them into its own process
   group (`scripts/pod/launcher.py:7-9`). The stop must keep observing and keep closing.
3. **`attempt_max` bounds the four looping actions.** `route()` is pure, so a retry that
   changes nothing reproduces the same record, the same row matches, and the task cycles
   for ever. The cap parks the task NAMING the row that kept matching.
4. **`admits()` REFUSES on the Agda pile-up.** On 2026-08-12 one agent held six Agda
   processes at once, each at the 8 GB cap: 48 GB of worst case on a 64 GB machine and a
   load average of 19. The OWNER saw it; no tool did.
5. **`ledger.py --write` writes no standing figure and no half of a measured pair.**
   `dev/ledger.toml:77-82` rules the first; `validate_ratio_baseline()`'s own docstring
   rules the second, and a rewritten LINES term over an unmeasured SECONDS term is the
   C-28 class this repository has already paid for twice.

NO TEST HERE STARTS AGDA, DISPATCHES AN AGENT OR WRITES INTO THE REPOSITORY. Every tick
runs against a temporary repository root, `launch()` is a recorder, `run_acceptance()`
returns a canned record, and `git_commit` never runs.

THE FIXTURE CAN FAIL, which is C-45. The park-counter test drives the SAME loop that
parks nothing when the table matches, so a green result is not the fixture's default.

Run: `python3 scripts/tests/test_pod_loop.py`
"""

from __future__ import annotations

import contextlib
import datetime
import importlib.util
import inspect
import io
import json
import os
import re
import shutil
import signal
import subprocess
import sys
import tempfile
import textwrap
import time
import types
import pathlib
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent.parent
sys.path.insert(0, str(ROOT / "scripts"))
sys.path.insert(0, str(ROOT / "scripts" / "pod"))


def _load(name: str, rel: str):
    spec = importlib.util.spec_from_file_location(name, ROOT / rel)
    mod = importlib.util.module_from_spec(spec)
    sys.modules[name] = mod
    spec.loader.exec_module(mod)
    return mod


agents_tree = _load("agents_tree", "scripts/agents_tree.py")
table_mod = _load("table", "scripts/pod/table.py")
replay_mod = _load("replay", "scripts/pod/replay.py")
preflight_mod = _load("preflight", "scripts/pod/preflight.py")
facts_mod = _load("facts", "scripts/pod/facts.py")
witness_mod = _load("witness", "scripts/pod/witness.py")
heads_mod = _load("heads", "scripts/pod/heads.py")
accept_mod = _load("accept", "scripts/pod/accept.py")
pod = _load("pod", "scripts/pod/pod.py")

#: THE UNPATCHED FUNCTION, captured at import. `LoopCase.setUp` replaces
#: `pod.ensure_maintainer` with a counter, so a test that reaches for
#: `pod.ensure_maintainer` or `pod.__dict__[...]` gets THE COUNTER and passes
#: without ever running the code it names. That mistake was made and caught in
#: the same hour on 2026-08-18.
REAL_ENSURE_MAINTAINER = pod.ensure_maintainer
REAL_PROMPT_MAINTAINER = pod.prompt_maintainer
REAL_ENSURE_MATHEMATICIAN = pod.ensure_mathematician
REAL_INJECT_SURVEY = pod.inject_survey
ledger = _load("ledger", "scripts/measure/ledger.py")

#: The real functions, captured BEFORE any test replaces them. A test that wants the real
#: `admits()` must hold a reference taken at import, not one read out of the module after
#: the fixture has patched it.
REAL_ADMITS = pod.admits
REAL_LAUNCH = pod.launch
REAL_WATCHDOG_TICK = pod.watchdog_tick
REAL_RULE_G = pod._rule_g
REAL_KILL = pod.kill_process_group

DAY = datetime.date(2026, 8, 17)
CODE = "LJ-1.386"
DIR = "LJ-1-386"


# ---------------------------------------------------------------- fixtures


BRANCHES = """\
```toml pod-branches
[[branch]]
id = "go"
priority = 10
action = "done"
outcome = "go"

  [branch.when]
  exit_code = 0
  obligations_delta_max = -2
  heap_wall = false

[[branch]]
id = "no-go-stated"
priority = 20
action = "done"
outcome = "no-go"

  [branch.when]
  exit_code = 42
  error_class = "unsolved_meta"
  changed_files_any = ["agents/tasks/LJ-1-386/review-of-*.md"]

[[branch]]
id = "no-go-attacked"
priority = 15
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  error_class_in = ["unsolved_meta", "universe_level", "other"]
  changed_files_any = ["agents/tasks/LJ-1-386/Probe386.agda"]
  changed_files_none = ["agents/tasks/LJ-1-386/review-of-*.md"]

[[branch]]
id = "retry-on-termination"
priority = 40
action = "accept"

  [branch.when]
  error_class = "termination"
```
"""

BRIEF = """\
# LJ-1.386: internal existence of a pairing code at a band ordinal, GO or NO-GO

## HEAD
head_slot: coder
machine: shared

## THE OBLIGATION
Prove the internal existence of a pairing code at the band ordinal.

## OBLIGATION NAMES
obligations = ["agents/tasks/LJ-1-386/Probe386.agda::code-exists",
               "agents/tasks/LJ-1-386/Probe386.agda::code-inj"]

## SCOPE (write)
- agents/tasks/LJ-1-386/Probe386.agda
- agents/tasks/LJ-1-386/lj-1.386-report.md

## PREMISES
- `chosen` is total on a band ordinal. Basis: src/L/Cardinal.lagda.md:194-195

## WHAT IS DELIVERED ALREADY
- `Good`, the predicate the code must satisfy: src/L/Cardinal.lagda.md:186-189

## WHAT IS MISSING
The inhabitation of the truncated sum.

## LAWS (program-generated, do not edit)
- D-1: write the probe in the task directory and run it while the task is live.

## ARCHIVE (program-generated, do not edit)
Corpus search for: L.Cardinal, Good
- archive/dev/TASKS-archived.md:80    (1 key hit)

## LITERATURE (program-generated, do not edit)
Corpus search for: pairing code
- dev/literature/j-hierarchy.md       NO HIT

## THE REASONING
The prose half. It is never executed and it gates nothing.

## WHAT GO AND NO-GO EACH EARN
A NO-GO is worth as much as a GO here.

## BRANCHES
""" + BRANCHES


def sys_row(rid="sys-park-everything", action="park", priority=900,
            when=None, **kw):
    out = {"id": rid, "scope": "system", "priority": priority, "action": action,
           "added": DAY, "added_by": "owner", "reason": "a test row",
           "expired": False, "when": dict(when or {"heap_wall": True})}
    out.update(kw)
    return out


def record(task=CODE, exit_code=0, error_class=None, delta=-2,
           changed=("agents/tasks/LJ-1-386/Probe386.agda",), seconds=1.0,
           heap_wall=False, concurrency=1, conjuncts=None, **kw):
    """One whole acceptance record, in the shape 4.5.2 stores and 5.3.1 logs."""
    out = {"task": task, "concurrency": concurrency, "caliber": facts_mod.CAP,
           "conjuncts": conjuncts or {1: True, 2: True, 3: True,
                                      4: True, 5: True, 6: True},
           "runs_all": [], "run": None,
           "facts": {"exit_code": exit_code, "error_class": error_class,
                     "obligations_delta": delta, "changed_files": list(changed),
                     "seconds": seconds, "heap_wall": heap_wall}}
    out.update(kw)
    return out


class LoopCase(unittest.TestCase):
    """One temporary repository per test. NOTHING here writes into the real tree.

    Every side effect the tick can have is replaced by a recorder: `launch()` never
    spawns, `run_acceptance()` never starts Agda, `git_commit` never commits, and the
    maintainer, the digest and the owner push are counted rather than performed.
    """

    def setUp(self):
        self.dir = tempfile.TemporaryDirectory()
        self.tmp = Path(self.dir.name)
        self.addCleanup(self.dir.cleanup)
        self.build_tree()
        self.use_tree()
        self.calls = {"launch": [], "commit": [], "notify": [], "digest": 0,
                      "maintainer": 0, "ensure": 0, "acceptance": [], "watchdog": 0,
                      "refill": 0}
        self.patch_side_effects()

    # ---------------------------------------------------------------- the fixture

    def build_tree(self):
        tmp = self.tmp
        (tmp / "dev" / "pod" / "transitions").mkdir(parents=True, exist_ok=True)
        (tmp / "dev" / "pod" / "proposals").mkdir(parents=True, exist_ok=True)
        (tmp / "dev" / "literature").mkdir(parents=True, exist_ok=True)
        (tmp / "dev" / "literature" / "j-hierarchy.md").write_text("literature\n")
        (tmp / "archive" / "dev").mkdir(parents=True, exist_ok=True)
        (tmp / "archive" / "dev" / "TASKS-archived.md").write_text("x\n" * 200)
        (tmp / "src" / "L").mkdir(parents=True, exist_ok=True)
        (tmp / "src" / "L" / "Cardinal.lagda.md").write_text("line\n" * 300)
        shutil.copy(ROOT / "dev" / "pod" / "heads.toml",
                    tmp / "dev" / "pod" / "heads.toml")
        (tmp / "dev" / "pod" / "replay-corpus.jsonl").write_text("")
        (tmp / "dev" / "pod" / "screen.toml").write_text("endpoint = \"ruled\"\n")
        table_path = tmp / "dev" / "pod" / "table.toml"
        table_path.write_text(table_mod.dump_table([]), encoding="utf-8")
        task = tmp / "agents" / "tasks" / DIR
        task.mkdir(parents=True, exist_ok=True)
        (task / f"{CODE}.md").write_text(BRIEF, encoding="utf-8")
        math = tmp / "agents" / "tasks" / "POD-MATH"
        math.mkdir(parents=True, exist_ok=True)
        src_math = ROOT / "agents" / "tasks" / "POD-MATH" / "POD-MATH.md"
        if src_math.is_file():
            shutil.copy(src_math, math / "POD-MATH.md")
        else:
            (math / "POD-MATH.md").write_text(
                "# standing\n\n## HEAD\nhead_slot: mathematician\n\n"
                "## SCOPE (write)\nreport\n\n## ARCHIVE\nnone\n\n"
                "## LITERATURE\nnone\n")
        (tmp / ".pod-state" / "logs").mkdir(parents=True, exist_ok=True)

    def use_tree(self):
        tmp = self.tmp
        self.swap(pod, ROOT=tmp, POD_STATE=tmp / ".pod-state",
                  STATE_FILE=tmp / ".pod-state" / "state.json",
                  STOPPED_FILE=tmp / ".pod-state" / "STOPPED",
                  DRAIN_FILE=tmp / ".pod-state" / "DRAINING",
                  LOG_DIR=tmp / ".pod-state" / "logs",
                  LOCKFILE=tmp / ".pod-state" / "pod.lock",
                  RELOAD_FILE=tmp / ".pod-state" / "reload",
                  REACCEPT_FILE=tmp / ".pod-state" / "reaccept",
                  TRANSITIONS=tmp / "dev" / "pod" / "transitions",
                  QUEUE=tmp / "dev" / "pod" / "queue.toml",
                  TABLE=tmp / "dev" / "pod" / "table.toml",
                  CORPUS=tmp / "dev" / "pod" / "replay-corpus.jsonl",
                  PROPOSALS=tmp / "dev" / "pod" / "proposals",
                  INSTRUCTIONS=tmp / "dev" / "pod" / "instructions",
                  REFILL_BRIEF=tmp / "agents" / "tasks" / "POD-REFILL"
                  / "POD-REFILL.md",
                  MATH_BRIEF=tmp / "agents" / "tasks" / "POD-MATH"
                  / "POD-MATH.md",
                  WATCHDOG=tmp / "scripts" / "ops" / "agda-watchdog.sh",
                  BARK=tmp / "scripts" / "ops" / "bark-push.sh",
                  DIGEST=tmp / "scripts" / "pod" / "digest.py")
        self.swap(table_mod, ROOT=tmp, TABLE=tmp / "dev" / "pod" / "table.toml",
                  HEADS=tmp / "dev" / "pod" / "heads.toml")
        self.swap(replay_mod, ROOT=tmp,
                  CORPUS=tmp / "dev" / "pod" / "replay-corpus.jsonl")
        self.swap(facts_mod, ROOT=tmp)
        self.swap(accept_mod, ROOT=tmp)
        self.swap(witness_mod, ROOT=tmp)
        self.swap(preflight_mod, ROOT=tmp,
                  CLOSURE=ROOT / "scripts" / "pod" / "check-closure.py")
        self.swap(heads_mod, HEADS=tmp / "dev" / "pod" / "heads.toml")
        self.swap(agents_tree, ROOT=tmp, TASKS=tmp / "agents" / "tasks",
                  ARCHIVE=tmp / "agents" / "tasks" / "archive")
        heads_mod._CACHE.clear()
        pod._HEADS_SHA.clear()
        pod._TABLE_CACHE.clear()
        pod._WATCHDOG["reported"] = None       # A13's memo is module state: reset it
        self.addCleanup(heads_mod._CACHE.clear)
        self.addCleanup(pod._HEADS_SHA.clear)
        self.addCleanup(pod._TABLE_CACHE.clear)
        self.addCleanup(pod._WATCHDOG.__setitem__, "reported", None)

    def swap(self, mod, **kw):
        for k, v in kw.items():
            old = getattr(mod, k)
            setattr(mod, k, v)
            self.addCleanup(setattr, mod, k, old)

    def patch(self, mod, name, value):
        old = getattr(mod, name)
        setattr(mod, name, value)
        self.addCleanup(setattr, mod, name, old)

    def patch_side_effects(self):
        """Every side effect a tick can have becomes a recorder. NOTHING is dispatched."""
        # `st` IS THE FIFTH ARGUMENT SINCE A27, and rule (f) passes it positionally. A
        # stub with the old four-argument shape reads that as `TypeError` and the whole
        # dispatch dies as a park, which is exactly how this stub failed on 2026-08-21.
        def fake_launch(t, brief, role, root=None, st=None):
            self.calls["launch"].append((t.code, str(brief), role, t.attempt))
            t.pid, t.proc_start, t.started = 4242, "start", time.strftime(
                "%Y-%m-%d %H:%M:%S")
            t.model, t.effort, t.role = "claude-opus-5", "max", role
            return 4242
        self.patch(pod, "launch", fake_launch)
        self.patch(pod, "rec_alive", lambda t: True)
        self.patch(pod, "admits", lambda st, t, agda=None: True)
        self.patch(pod, "notify_owner",
                   lambda why, root=None: self.calls["notify"].append(why))
        self.patch(pod, "write_digest",
                   lambda st, root=None: self.calls.__setitem__(
                       "digest", self.calls["digest"] + 1))
        # TWO COUNTERS SINCE 2026-08-18, because rule (e) now does two different things
        # at two different cadences. `ensure_maintainer` runs EVERY tick and is
        # idempotent: the maintainer is RESIDENT and outlives this program, so its
        # liveness is not on the batch trigger. `prompt_maintainer` is what the trigger
        # fires, and it FEEDS the live session instead of launching a new one.
        self.patch(pod, "ensure_maintainer",
                   lambda st, root=None: self.calls.__setitem__(
                       "ensure", self.calls["ensure"] + 1))
        self.patch(pod, "ensure_mathematician",
                   lambda st, root=None: None)
        self.patch(pod, "mathematician_busy", lambda st, root=None: False)
        # **THE COUNTER ALSO STAMPS THE CLOCK, because the real one does.** A stub that
        # only counts leaves `hours_since_last_batch()` and `park_since_last_batch()`
        # reading a log with no batch line in it, so every trigger test measured a
        # trigger that can never be satisfied and no test could see a re-fire. That is
        # the same trap `maintainer_scope_ok()` fell into: a test that stubs the thing
        # under test cannot fail for the reason it exists.
        def _prompt(st, root=None):
            self.calls["maintainer"] = self.calls["maintainer"] + 1
            pod.emit_event(st, "batch", result="prompted", root=root or self.tmp)
        self.patch(pod, "prompt_maintainer", _prompt)
        self.patch(pod, "inject_survey", lambda brief, root=None: False)
        self.patch(pod, "kill_process_group", lambda pid: True)
        # A13 AND A11 ARE SIDE EFFECTS LIKE ANY OTHER. The real `watchdog_tick()` reads
        # the machine's process table and would START A PROCESS, and the real `_rule_g()`
        # would DISPATCH AN AGENT. Both are counted here and driven for real by their own
        # classes, so no test's result depends on whether a watchdog happens to run on the
        # machine the suite runs on.
        self.patch(pod, "watchdog_tick",
                   lambda st, root=None: self.calls.__setitem__(
                       "watchdog", self.calls["watchdog"] + 1) or True)
        self.patch(pod, "_rule_g",
                   lambda st, root=None: self.calls.__setitem__(
                       "refill", self.calls["refill"] + 1))
        self.patch(table_mod, "git_commit",
                   lambda paths, message, root=None:
                   self.calls["commit"].append(message) or True)
        self.patch(witness_mod, "witness_unresolved", lambda t, root=None: 2)
        self.patch(accept_mod, "unbound_findings", lambda root=None: [])
        # THE STUB RECORDS `t.row` AS IT WAS AT CALL TIME, because the real
        # `commit_task()` builds its git message from exactly that. See
        # `test_the_commit_message_names_the_row_that_CLOSED_the_task`.
        self.patch(pod, "commit_task",
                   lambda t, rec, root=None: self.calls.__setitem__(
                       "commit_row", getattr(t, "row", None)) or True)

    # ---------------------------------------------------------------- helpers

    def write_table(self, rows):
        table_mod.write_table(rows, self.tmp / "dev" / "pod" / "table.toml")
        pod._TABLE_CACHE.clear()

    def queue(self, *entries):
        body = []
        for e in entries:
            body.append("[[task]]")
            for k, v in e.items():
                body.append(f"{k} = {json.dumps(v)}")
            body.append("")
        (self.tmp / "dev" / "pod" / "queue.toml").write_text("\n".join(body))

    def set_acceptance(self, rec):
        def fake(t, root=None):
            self.calls["acceptance"].append(t.code)
            return rec
        self.patch(accept_mod, "run_acceptance", fake)

    def tick(self, st=None):
        st = pod.load_state() if st is None else st
        return st, pod.pod_tick(st, self.tmp)

    def lines(self):
        return pod.log_lines(self.tmp)

    def state_of(self, st, code=CODE):
        return st.tasks[code]

    def give_scene(self, code=CODE):
        """An isolated checkout. Re-accept refuses without one (LJ-1.388)."""
        p = (self.tmp / ".pod-state" / "worktrees"
             / agents_tree.normalise(code))
        p.mkdir(parents=True, exist_ok=True)
        return p


# ---------------------------------------------------------------- rule (a1) CREATE


class RuleA1(LoopCase):
    """`dev/pod/queue.toml` is the ONLY producer of a task, and AD2 and AD3 need that."""

    def test_an_entry_with_a_brief_becomes_a_ready_task(self):
        """Transition 1, and rule (a1) is its only writer. The whole tick then carries the
        task on to RUNNING through rule (f), so this reads the CREATION edge alone."""
        self.queue({"code": CODE, "brief": f"agents/tasks/{DIR}/{CODE}.md"})
        st = pod.State()
        pod._rule_a1(st, self.tmp)
        self.assertEqual(st.tasks[CODE].status, pod.READY)
        line = self.lines()[0]
        self.assertEqual((line["from"], line["to"]), (None, "READY"))
        self.assertEqual(line["brief"], f"agents/tasks/{DIR}/{CODE}.md")

    def test_the_whole_tick_carries_a_new_entry_to_running(self):
        """End to end: the queue produces the task, rule (f) admits its rows and
        dispatches, and the log holds one line per transition."""
        self.queue({"code": CODE, "brief": f"agents/tasks/{DIR}/{CODE}.md"})
        st, verdict = self.tick()
        self.assertIs(verdict, pod.CONTINUE)
        self.assertEqual(st.tasks[CODE].status, pod.RUNNING)
        self.assertEqual([(x["from"], x["to"]) for x in self.lines()
                          if x["task"] == CODE],
                         [(None, "READY"), ("READY", "RUNNING")])

    def test_two_entries_under_ONE_code_create_ONE_task(self):
        """Section 5.2 rules one state record per code, and the queue is hand-written:
        the owner adds an entry, `park_and_split` appends one, and the maintainer batch
        appends one, so the same code can be written twice."""
        self.queue({"code": CODE, "brief": f"agents/tasks/{DIR}/{CODE}.md"},
                   {"code": CODE, "brief": f"agents/tasks/{DIR}/{CODE}.md"})
        st = pod.State()
        pod._rule_a1(st, self.tmp)
        self.assertEqual(len(st.tasks), 1)
        self.assertEqual(len([x for x in self.lines() if x["to"] == "READY"]), 1)

    def test_an_entry_with_no_brief_is_a_request_and_never_a_task(self):
        """`split_entry()` writes `code`, `split_of` and `reason` and NO brief. The digest
        prints it until the mathematician adds the path; rule (a1) skips it."""
        self.queue({"code": "LJ-1.999-split", "split_of": CODE, "reason": "a split"})
        st, _ = self.tick()
        self.assertEqual(st.tasks, {})

    def test_a_mathematician_brief_is_not_a_task_and_writes_no_table_row(self):
        """Owner 2026-08-21: the mathematician is resident. A queue entry that
        names that slot is not admitted into the table and is not a TASK."""
        math = self.tmp / "agents" / "tasks" / "LJ-1-999"
        math.mkdir(parents=True, exist_ok=True)
        brief = math / "LJ-1.999.md"
        brief.write_text(BRIEF.replace("head_slot: coder",
                                       "head_slot: mathematician"),
                         encoding="utf-8")
        self.queue({"code": "LJ-1.999", "brief": "agents/tasks/LJ-1-999/LJ-1.999.md"})
        st, _ = self.tick()
        self.assertNotIn("LJ-1.999", st.tasks)
        rows = table_mod.load_table(self.tmp / "dev" / "pod" / "table.toml")
        self.assertEqual([r for r in rows if r.get("scope") == "task:LJ-1.999"], [])

    def test_the_pod_marker_is_written_at_creation(self):
        """Section 9.3: the marker SURVIVES A COPY, and AD6 salvages `agents/` by
        copying, so a git-only marker is lost when the reader needs it."""
        self.queue({"code": CODE, "brief": f"agents/tasks/{DIR}/{CODE}.md"})
        self.tick()
        marker = self.tmp / "agents" / "tasks" / DIR / ".pod"
        self.assertTrue(marker.is_file())
        self.assertIn("pod=1", marker.read_text())
        # THE TWO DIGESTS ARE THE POINT, and `table=` alone would hold for an empty
        # value. The marker says which table and which heads file the task was created
        # under, so the digests are re-derived and compared. The re-stamp is what makes
        # them comparable: rule (f) admitted this task's rows during the tick above, so
        # the table on disk is no longer the one creation saw.
        import hashlib
        pod.stamp_pod_marker(CODE, self.tmp)
        text = marker.read_text()
        for key, path in (("table", "table.toml"), ("heads", "heads.toml")):
            want = hashlib.sha256(
                (self.tmp / "dev" / "pod" / path).read_bytes()).hexdigest()
            self.assertIn(f"{key}={want}", text)

    def test_a_task_directory_under_archive_expires_its_rows(self):
        """Expiry's SECOND mechanical trigger, section 4.6. A row is never deleted."""
        self.write_table([sys_row("task-lj-1-386-go", scope=f"task:{CODE}",
                                  priority=10)])
        self.queue({"code": CODE, "brief": f"agents/tasks/{DIR}/{CODE}.md"})
        st, _ = self.tick()
        arch = self.tmp / "agents" / "tasks" / "archive"
        arch.mkdir(parents=True, exist_ok=True)
        shutil.move(str(self.tmp / "agents" / "tasks" / DIR), str(arch / DIR))
        self.tick(st)
        rows = table_mod.load_table(self.tmp / "dev" / "pod" / "table.toml")
        self.assertTrue(rows[0]["expired"])
        self.assertIn("expired_at", rows[0])

    def test_the_machine_line_is_copied_once_at_creation(self):
        """5.6: a later edit of the brief cannot change a running task's class."""
        brief = self.tmp / "agents" / "tasks" / DIR / f"{CODE}.md"
        brief.write_text(BRIEF.replace("machine: shared", "machine: exclusive"))
        self.queue({"code": CODE, "brief": f"agents/tasks/{DIR}/{CODE}.md"})
        st, _ = self.tick()
        self.assertTrue(st.tasks[CODE].exclusive)


# ---------------------------------------------------------------- rule (a2) UNPARK


class RuleA2(LoopCase):
    """AD16, and it is AUTOMATIC. A park is never terminal and each reason has its test."""

    def parked(self, reason, rec=None, parked_at=0.0):
        st = pod.State()
        t = pod.Task(CODE, brief=f"agents/tasks/{DIR}/{CODE}.md", status=pod.PARKED,
                     park_reason=reason, record=rec, parked_at=parked_at, attempt=1)
        st.tasks[CODE] = t
        return st, t

    def test_a_preflight_park_re_runs_the_preflight_and_unparks_on_a_pass(self):
        """A task refused BEFORE dispatch has no record, so `route()` cannot un-park it."""
        st, t = self.parked("preflight:P1")
        pod._rule_a2(st, self.tmp)
        self.assertEqual(t.status, pod.READY)

    def test_a_preflight_park_stays_parked_while_the_brief_is_still_broken(self):
        brief = self.tmp / "agents" / "tasks" / DIR / f"{CODE}.md"
        brief.write_text(BRIEF.replace("```toml pod-branches", "```toml branches"))
        st, t = self.parked("preflight:P1")
        pod._rule_a2(st, self.tmp)
        self.assertEqual(t.status, pod.PARKED)

    def test_an_admission_park_retries_on_the_next_table_edit(self):
        st, t = self.parked("admission", parked_at=0.0)
        self.write_table([sys_row()])
        pod._rule_a2(st, self.tmp)
        self.assertEqual(t.status, pod.READY)

    def test_an_admission_park_waits_while_the_table_is_unchanged(self):
        self.write_table([sys_row()])
        st, t = self.parked("admission", parked_at=time.time() + 60)
        pod._rule_a2(st, self.tmp)
        self.assertEqual(t.status, pod.PARKED)

    def test_a_no_change_park_carries_no_record_so_route_can_never_unpark_it(self):
        """5.5: it waits for the maintainer batch's queue request, and nothing else."""
        self.write_table([sys_row(when={"exit_code": 0})])
        st, t = self.parked("no-change", rec=None, parked_at=0.0)
        pod._rule_a2(st, self.tmp)
        self.assertEqual(t.status, pod.PARKED)

    def test_a_no_match_park_unparks_once_a_new_row_matches_the_record(self):
        """A table edit newer than the park re-measures the scene. It does not
        re-dispatch a worker (PARKED → CHECKING, transition 14)."""
        st, t = self.parked("no-match", rec=record(), parked_at=0.0)
        self.give_scene()
        self.write_table([sys_row(when={"exit_code": 0})])
        pod._rule_a2(st, self.tmp)
        self.assertEqual(t.status, pod.CHECKING)
        self.assertEqual(self.lines()[-1].get("why"),
                         "reaccept: the scene is still there, no worker")

    def test_a_no_match_park_reaccepts_after_a_reload_stamp(self):
        """LJ-1.400: a meter repair plus reload salvages the worktree, no worker."""
        st, t = self.parked("no-match", rec=record(), parked_at=time.time() - 10)
        self.give_scene()
        pod.stamp_reaccept(self.tmp)
        pod._rule_a2(st, self.tmp)
        self.assertEqual(t.status, pod.CHECKING)
        self.assertEqual(self.calls["launch"], [])

    def test_a_no_match_park_does_not_spin_after_a_failed_reaccept(self):
        st, t = self.parked("no-match", rec=record(), parked_at=time.time() + 60)
        pod.stamp_reaccept(self.tmp)
        pod._rule_a2(st, self.tmp)
        self.assertEqual(t.status, pod.PARKED)

    def test_reaccept_moves_one_park_per_tick(self):
        """Idle CHECKING waiters filled the heap sum and deadlocked the first salvage."""
        st = pod.State()
        for code in ("LJ-1.900", "LJ-1.901"):
            st.tasks[code] = pod.Task(code, brief=f"agents/tasks/{DIR}/{CODE}.md",
                                      status=pod.PARKED, park_reason="no-match",
                                      record=record(), parked_at=0.0)
            self.give_scene(code)
        pod.stamp_reaccept(self.tmp)
        self.write_table([sys_row(when={"exit_code": 0})])
        pod._rule_a2(st, self.tmp)
        checking = [c for c, t in st.tasks.items() if t.status == pod.CHECKING]
        parked = [c for c, t in st.tasks.items() if t.status == pod.PARKED]
        self.assertEqual(len(checking), 1, checking)
        self.assertEqual(len(parked), 1, parked)

    def test_a_no_match_park_without_a_worktree_is_not_reaccepted(self):
        """LJ-1.386/388, 2026-08-20: re-accept on main hit spec-surface and R7."""
        st, t = self.parked("no-match", rec=record(), parked_at=0.0)
        pod.stamp_reaccept(self.tmp)
        pod._rule_a2(st, self.tmp)
        self.assertEqual(t.status, pod.PARKED)
        self.assertEqual(self.calls["launch"], [])

    def test_a_checking_task_without_a_worktree_parks_and_keeps_the_record(self):
        """The leftover CHECKING from the 388 stop must not re-measure main."""
        rec = record()
        st = pod.State()
        t = pod.Task(CODE, brief=f"agents/tasks/{DIR}/{CODE}.md",
                     status=pod.CHECKING, record=rec, park_reason="no-match")
        st.tasks[CODE] = t
        self.set_acceptance(record(exit_code=1, error_class="spec_surface"))
        pod._rule_c(st, self.tmp)
        self.assertEqual(t.status, pod.PARKED)
        self.assertEqual(t.park_reason, "no-match")
        self.assertIsNotNone(t.record)
        self.assertEqual(self.calls["acceptance"], [])

    def test_a_salvage_park_reaccepts_after_a_reload_stamp(self):
        """LJ-1.388: the copy is retried, no worker."""
        st, t = self.parked("salvage:LJ-1.386", rec=record(),
                            parked_at=time.time() - 10)
        self.give_scene()
        pod.stamp_reaccept(self.tmp)
        pod._rule_a2(st, self.tmp)
        self.assertEqual(t.status, pod.CHECKING)
        self.assertEqual(self.calls["launch"], [])

    def test_a_quota_park_is_not_reaccepted(self):
        """A vendor window is not a mis-measured scene."""
        self.patch(pod, "quota_open", lambda reason: False)
        st, t = self.parked("quota:2026-08-19T20:19:47", rec=record(),
                            parked_at=0.0)
        pod.stamp_reaccept(self.tmp)
        pod._rule_a2(st, self.tmp)
        self.assertEqual(t.status, pod.PARKED)

    def test_a_failed_reaccept_does_not_prompt_a_POD_REVIEW(self):
        """LJ-1.422, 2026-08-20: each reload re-accepted the critic park and
        `notify_closes` treated CHECKING→PARKED as a worker return."""
        prompts = []

        class _Mod:
            @staticmethod
            def herdr_name(t):
                return "pod-batch"

            @staticmethod
            def herdr_prompt(name, text):
                prompts.append(text)
                return True

        self.patch(facts_mod, "launcher", lambda: _Mod)
        st = pod.State()
        rec = record()
        t = pod.Task(CODE, status=pod.PARKED, park_reason="no-match", record=rec)
        st.tasks[CODE] = t
        seq_before = st.seq
        pod.emit(st, t, pod.PARKED, pod.CHECKING, rec=rec, reason="no-match",
                 root=self.tmp, why="reaccept: the scene is still there, no worker")
        pod.emit(st, t, pod.CHECKING, pod.PARKED, rec=rec, reason="no-match",
                 root=self.tmp)
        self.assertIsNone(pod.notify_closes(seq_before, self.tmp))
        self.assertEqual(prompts, [])

    def test_a_reaccept_that_closes_DONE_still_prompts(self):
        prompts = []

        class _Mod:
            @staticmethod
            def herdr_name(t):
                return "pod-batch"

            @staticmethod
            def herdr_prompt(name, text):
                prompts.append(text)
                return True

        self.patch(facts_mod, "launcher", lambda: _Mod)
        st = pod.State()
        rec = record()
        t = pod.Task(CODE, status=pod.PARKED, park_reason="no-match", record=rec)
        st.tasks[CODE] = t
        seq_before = st.seq
        pod.emit(st, t, pod.PARKED, pod.CHECKING, rec=rec, reason="no-match",
                 root=self.tmp, why="reaccept: the scene is still there, no worker")
        pod.emit(st, t, pod.CHECKING, pod.DONE, rec=rec, row="sys-go",
                 root=self.tmp)
        self.assertIsNotNone(pod.notify_closes(seq_before, self.tmp))
        self.assertTrue(any("DONE" in p for p in prompts), prompts)

    def test_a_worker_park_still_prompts_a_POD_REVIEW(self):
        prompts = []

        class _Mod:
            @staticmethod
            def herdr_name(t):
                return "pod-batch"

            @staticmethod
            def herdr_prompt(name, text):
                prompts.append(text)
                return True

        self.patch(facts_mod, "launcher", lambda: _Mod)
        st = pod.State()
        rec = record()
        t = pod.Task(CODE, status=pod.RETURNED, record=rec)
        st.tasks[CODE] = t
        seq_before = st.seq
        pod.emit(st, t, pod.RETURNED, pod.CHECKING, root=self.tmp)
        pod.emit(st, t, pod.CHECKING, pod.PARKED, rec=rec, reason="no-match",
                 root=self.tmp)
        self.assertIsNotNone(pod.notify_closes(seq_before, self.tmp))
        self.assertTrue(any("PARKED" in p for p in prompts), prompts)

    def test_a_reaccept_close_does_not_launch(self):
        """Full tick: PARKED → CHECKING → DONE, and launch() is never called."""
        rec = record(exit_code=0, delta=-2)
        rec["facts"]["obligations_open"] = 0
        st, t = self.parked("no-match", rec=record(delta=0), parked_at=0.0)
        self.give_scene()
        self.patch(pod, "salvage_worktree", lambda t, root=None: [])
        self.patch(pod, "drop_worktree", lambda code, root=None: True)
        t.obl_before = 2
        self.write_table([sys_row("sys-go", action="done", outcome="go",
                                  priority=10,
                                  when={"exit_code": 0,
                                        "obligations_delta_max": -2,
                                        "heap_wall": False})])
        self.set_acceptance(rec)
        st, _ = self.tick(st)
        self.assertEqual(t.status, pod.DONE)
        self.assertEqual(self.calls["launch"], [])
        self.assertEqual(self.calls["acceptance"], [CODE])

    def test_an_attempt_max_park_stays_while_the_GUILTY_row_still_wins(self):
        """B2: a table edit that does not touch the guilty row costs no dispatch."""
        self.write_table([sys_row("sys-guilty", action="accept",
                                  when={"exit_code": 0})])
        st, t = self.parked("attempt_max:sys-guilty", rec=record(), parked_at=0.0)
        pod._rule_a2(st, self.tmp)
        self.assertEqual(t.status, pod.PARKED)

    def test_an_attempt_max_park_unparks_when_a_DIFFERENT_row_now_wins(self):
        self.write_table([sys_row("sys-guilty", action="accept", priority=900,
                                  when={"exit_code": 0}),
                          sys_row("sys-new", action="park", priority=10,
                                  when={"exit_code": 0})])
        st, t = self.parked("attempt_max:sys-guilty", rec=record(), parked_at=0.0)
        pod._rule_a2(st, self.tmp)
        self.assertEqual(t.status, pod.READY)
        self.assertEqual(t.row, "sys-new")


# ---------------------------------------------------------------- rule (b) OBSERVE


class RuleB(LoopCase):
    """A worker is dead when its pid is dead, or when it ran too long."""

    def running(self, started=None):
        st = pod.State()
        t = pod.Task(CODE, brief=f"agents/tasks/{DIR}/{CODE}.md", status=pod.RUNNING,
                     pid=4242, started=started or time.strftime("%Y-%m-%d %H:%M:%S"))
        st.tasks[CODE] = t
        return st, t

    def test_a_dead_pid_returns_the_task(self):
        self.patch(pod, "rec_alive", lambda t: False)
        st, t = self.running()
        pod._rule_b(st, self.tmp)
        self.assertEqual(t.status, pod.RETURNED)
        self.assertEqual(self.lines()[-1]["why"], "pid dead")

    def test_a_live_pid_inside_the_deadline_keeps_running(self):
        st, t = self.running()
        pod._rule_b(st, self.tmp)
        self.assertEqual(t.status, pod.RUNNING)

    def test_the_worker_deadline_kills_the_group_and_returns_the_task(self):
        """Without it a hung worker holds an Agda slot for ever: the only other exit
        from RUNNING is a dead pid."""
        killed = []
        self.patch(pod, "kill_process_group", lambda pid: killed.append(pid) or True)
        old = time.strftime("%Y-%m-%d %H:%M:%S", time.localtime(time.time() - 100000))
        st, t = self.running(started=old)
        pod._rule_b(st, self.tmp)
        self.assertEqual(killed, [4242])
        self.assertEqual(t.status, pod.RETURNED)
        self.assertEqual(self.lines()[-1]["why"], "deadline")


# ---------------------------------------------------------------- rule (c) ACCEPT


class FeedClockCountsFeeds(LoopCase):
    """**ONE EVENT NAME CARRIED TWO THINGS AND THE HARVEST RESET THE FEED CLOCK.**

    `harvest_batch()` emits `event: "batch"` on nine paths of its own, `parse`, `scope`,
    `empty`, `refused`, `reject` and `admit`, and it runs FIRST inside rule (e). Both
    triggers read the newest `batch` line, so ONE leftover proposal file, even an EMPTY
    one, made `hours_since_last_batch()` read zero and `park_since_last_batch()` read
    false, and the prompt was skipped: the maintainer was not told about the parks and the
    twelve hour clock restarted from a harvest nobody read.

    Found by an adversarial review of the rule (e) reorder, which made it reachable on the
    tick that matters most, the one that stops the loop.
    """

    def emit_batch(self, result, task=""):
        st = pod.State()
        return pod.emit_event(st, "batch", result=result, root=self.tmp)

    def test_a_HARVEST_outcome_does_not_reset_the_twelve_hour_clock(self):
        for result in ("empty", "admit", "parse", "scope", "reject", "refused"):
            self.emit_batch(result)
        self.assertGreater(pod.hours_since_last_batch(self.tmp), 1000,
                           "a harvest reset the clock that decides whether to FEED")

    def test_a_FEED_does_reset_it(self):
        self.emit_batch("prompted")
        self.assertLess(pod.hours_since_last_batch(self.tmp), 1.0)

    def test_a_HARVEST_does_not_swallow_the_NEW_PARK_edge(self):
        st = pod.State()
        st.tasks[CODE] = t = pod.Task(CODE, status=pod.CHECKING)
        pod.emit_event(st, "batch", result="prompted", root=self.tmp)
        pod.emit(st, t, pod.CHECKING, pod.PARKED, reason="no-match", rec=record(),
                 root=self.tmp)
        self.assertTrue(pod.park_since_last_batch(self.tmp))
        self.emit_batch("empty")               # a leftover proposal, harvested
        self.assertTrue(pod.park_since_last_batch(self.tmp),
                        "a harvest swallowed the edge that tells the maintainer")

    def test_a_FEED_closes_the_edge_because_the_maintainer_WAS_told(self):
        st = pod.State()
        st.tasks[CODE] = t = pod.Task(CODE, status=pod.CHECKING)
        pod.emit(st, t, pod.CHECKING, pod.PARKED, reason="no-match", rec=record(),
                 root=self.tmp)
        self.assertTrue(pod.park_since_last_batch(self.tmp))
        self.emit_batch("prompted")
        self.assertFalse(pod.park_since_last_batch(self.tmp))

    def test_a_failed_reaccept_is_not_a_new_park_edge(self):
        """LJ-1.422, 2026-08-20: twelve re-accepts of one critic park, each a
        CHECKING→PARKED after `why: reaccept:`, each firing a batch."""
        st = pod.State()
        st.tasks[CODE] = t = pod.Task(CODE, status=pod.PARKED)
        pod.emit_event(st, "batch", result="prompted", root=self.tmp)
        rec = record()
        pod.emit(st, t, pod.PARKED, pod.CHECKING, rec=rec, reason="no-match",
                 root=self.tmp, why="reaccept: the scene is still there, no worker")
        pod.emit(st, t, pod.CHECKING, pod.PARKED, rec=rec, reason="no-match",
                 root=self.tmp)
        self.assertFalse(pod.park_since_last_batch(self.tmp),
                         "a re-accept that parks again is the same park")

    def test_a_worker_park_after_a_reaccept_still_counts(self):
        """A later RETURNED→CHECKING→PARKED is a new park, even of the same code."""
        st = pod.State()
        st.tasks[CODE] = t = pod.Task(CODE, status=pod.PARKED)
        pod.emit_event(st, "batch", result="prompted", root=self.tmp)
        rec = record()
        pod.emit(st, t, pod.PARKED, pod.CHECKING, rec=rec, reason="no-match",
                 root=self.tmp, why="reaccept: the scene is still there, no worker")
        pod.emit(st, t, pod.CHECKING, pod.READY, rec=rec, root=self.tmp)
        pod.emit(st, t, pod.READY, pod.RUNNING, root=self.tmp)
        pod.emit(st, t, pod.RUNNING, pod.RETURNED, why="pid dead", root=self.tmp)
        pod.emit(st, t, pod.RETURNED, pod.CHECKING, root=self.tmp)
        pod.emit(st, t, pod.CHECKING, pod.PARKED, rec=rec, reason="no-match",
                 root=self.tmp)
        self.assertTrue(pod.park_since_last_batch(self.tmp),
                        "a worker park after a re-accept was swallowed")


class MaintainerIsFedBeforeTheStop(LoopCase):
    """**THE STOP MUST NOT SUPPRESS THE ROLE THAT CLEARS A PARK.**

    Rule (d) returned STOP before rule (e) ran, so on a tick that reached `parked_max` the
    maintainer was neither started nor fed. MEASURED 2026-08-19 on the first tick after
    the grok handover: six parked became NINE in one tick, (d) stopped the loop, and
    `ensure_maintainer()` was never called, so the new head was never started at all. The
    loop halted and the only role that could unhalt it did not exist.

    (d)'s STOP means stop DISPATCHING, and (e) dispatches no worker.
    """

    def parked(self, n):
        st = pod.State()
        for i in range(n):
            code = f"LJ-1.{900 + i}"
            st.tasks[code] = pod.Task(code, status=pod.PARKED, park_reason="no-match",
                                      record=record(), parked_at=0.0)
        return st

    def test_the_maintainer_is_ENSURED_on_the_very_tick_that_stops(self):
        st = self.parked(pod._limits()["parked_max"])
        self.assertIs(pod.pod_tick(st, self.tmp), pod.STOP)
        self.assertGreaterEqual(self.calls["ensure"], 1,
                                "the loop stopped without starting the maintainer")

    def test_the_stop_still_happens(self):
        """The repair must not cost the stop. AD14 is unchanged."""
        st = self.parked(pod._limits()["parked_max"])
        self.assertIs(pod.pod_tick(st, self.tmp), pod.STOP)
        self.assertTrue((self.tmp / ".pod-state" / "STOPPED").exists())

    def test_rule_e_runs_before_rule_d_in_the_tick(self):
        """Read the order out of the source, so a future edit that moves one back is
        caught by name rather than by a symptom nobody connects to it."""
        src = (ROOT / "scripts" / "pod" / "pod.py").read_text(encoding="utf-8")
        body = src.split("def pod_tick(", 1)[1].split("\ndef ", 1)[0]
        self.assertLess(body.index("_rule_e(st, root)"), body.index("if _rule_d("),
                        "rule (d) stops before rule (e) feeds the maintainer")


class RuleBKillOrder(LoopCase):
    """**A KILL AIMED AT A RECYCLED PID TAKES OUT SOMEBODY ELSE'S PROCESS GROUP.**

    The deadline limb used to run `kill_process_group()` on a pid it had not checked.
    MEASURED 2026-08-19 at the maintainer handover: two tasks had been RUNNING since
    08:43Z, both pids were long gone, and `pod stop` reached the kill for both. Nothing
    was harmed only because `killpg` raised. It is the launcher's founding incident in
    miniature.
    """

    def running(self, elapsed_s):
        """`elapsed()` reads `started`, the one field `launch()` writes at the dispatch,
        as `%Y-%m-%d %H:%M:%S` local. A task with no `started` has not run and no deadline
        can fire on it, so the fixture must set that field and not a made-up one."""
        st = pod.State()
        t = pod.Task(CODE, brief=f"agents/tasks/{DIR}/{CODE}.md", status=pod.RUNNING,
                     pid=424242, attempt=1,
                     started=time.strftime("%Y-%m-%d %H:%M:%S",
                                           time.localtime(time.time() - elapsed_s)))
        st.tasks[CODE] = t
        return st, t

    def test_a_dead_pid_past_its_deadline_is_NEVER_killed(self):
        """The whole point. `rec_alive()` compares the recorded `proc_start` with the live
        process, which is the recycling guard, and the old order skipped it."""
        killed = []
        self.swap(pod, rec_alive=lambda t: False,
                  kill_process_group=lambda pid: killed.append(pid))
        st, t = self.running(10 ** 9)
        pod._rule_b(st, self.tmp)
        self.assertEqual(killed, [], "it killed a pid it had not checked")
        self.assertEqual(t.status, pod.RETURNED)
        self.assertEqual(self.lines()[-1]["why"], "pid dead",
                         "a task whose pid is gone must not be reported as a deadline")

    def test_a_LIVE_worker_past_its_deadline_is_still_killed(self):
        """The deadline exists because the only other exit from RUNNING is a dead pid, so
        a hung worker would hold an Agda slot for ever. Reordering must not lose that."""
        killed = []
        self.swap(pod, rec_alive=lambda t: True,
                  kill_process_group=lambda pid: killed.append(pid))
        st, t = self.running(10 ** 9)
        pod._rule_b(st, self.tmp)
        self.assertEqual(killed, [424242])
        self.assertEqual(self.lines()[-1]["why"], "deadline")

    def test_a_LIVE_but_UNRECOGNISED_pid_PARKS_and_is_never_RETURNED(self):
        """**TWO ADVERSARIAL ROUNDS SHAPED THIS ONE BRANCH.** Round 1 refuted the kill:
        `rec_alive()` is false for a pid that is STILL RUNNING whenever `proc_start` does
        not match. Round 2 refuted the repair: RETURNED frees the slot, because `admits()`
        counts RUNNING and CHECKING only, `heap_sum_ok()` ignores a RETURNED task's heap,
        the exclusive limb returns before any process census, and the Agda ceiling is
        four. **The sharp harm is rule (c)**, which would accept a tree the live process
        may still be writing."""
        self.swap(pod, rec_alive=lambda t: False, pid_exists=lambda pid: True,
                  kill_process_group=lambda pid: self.fail("it killed a pid it cannot own"))
        st, t = self.running(10 ** 9)
        pod._rule_b(st, self.tmp)
        self.assertEqual(t.status, pod.PARKED, "RETURNED would let rule (c) accept it")
        self.assertEqual(t.park_reason, "orphan:424242")
        self.assertIn("still be writing", " ".join(self.lines()[-1].get("detail") or []))

    def test_an_orphan_park_HOLDS_because_no_clock_can_settle_it(self):
        """`quota:` re-opens on a clock and `admission` on a table edit. Neither can say
        whose process a pid is, so this one waits for a person."""
        st = pod.State()
        st.tasks[CODE] = t = pod.Task(CODE, brief=f"agents/tasks/{DIR}/{CODE}.md",
                                      status=pod.PARKED, park_reason="orphan:424242",
                                      record=None, parked_at=0.0, attempt=1)
        pod._rule_a2(st, self.tmp)
        self.assertEqual(t.status, pod.PARKED)

    def test_an_orphan_park_is_a_reason_the_program_admits(self):
        self.assertIn("orphan:", pod.PARK_REASONS)

    def test_a_pid_that_is_GENUINELY_gone_still_reads_pid_dead(self):
        self.swap(pod, rec_alive=lambda t: False, pid_exists=lambda pid: False,
                  kill_process_group=lambda pid: self.fail("it killed a dead pid"))
        st, t = self.running(10 ** 9)
        pod._rule_b(st, self.tmp)
        self.assertEqual(self.lines()[-1]["why"], "pid dead")

    def test_pid_exists_asks_only_whether_the_number_is_live(self):
        """It must NOT re-answer the ownership question, which `rec_alive()` owns."""
        self.assertTrue(pod.pid_exists(os.getpid()))
        self.assertFalse(pod.pid_exists(0))
        self.assertFalse(pod.pid_exists("not a pid"))

    def test_a_LIVE_worker_inside_its_deadline_is_left_alone(self):
        self.swap(pod, rec_alive=lambda t: True,
                  kill_process_group=lambda pid: self.fail("it killed a healthy worker"))
        st, t = self.running(1)
        pod._rule_b(st, self.tmp)
        self.assertEqual(t.status, pod.RUNNING)


class RuleC(LoopCase):
    """AD13 runs here, ONE TASK AT A TIME, and every limb writes exactly one line."""

    def returned(self, attempt=1):
        st = pod.State()
        t = pod.Task(CODE, brief=f"agents/tasks/{DIR}/{CODE}.md", status=pod.RETURNED,
                     attempt=attempt, obl_before=2)
        st.tasks[CODE] = t
        return st, t

    def test_no_change_in_scope_drops_the_return_and_parks(self):
        """R7 and section 4.5.4: a half-record with a guessed field would license a row
        no evidence supports, and the replay would then certify that row as safe."""
        self.set_acceptance(None)
        st, t = self.returned()
        pod._rule_c(st, self.tmp)
        self.assertEqual(t.status, pod.PARKED)
        self.assertEqual(t.park_reason, "no-change")
        self.assertNotIn("facts", self.lines()[-1])

    def test_a_no_change_park_writes_nothing_to_the_corpus(self):
        self.set_acceptance(None)
        st, _ = self.returned()
        pod._rule_c(st, self.tmp)
        self.assertEqual(
            (self.tmp / "dev" / "pod" / "replay-corpus.jsonl").read_text(), "")

    def test_no_matching_row_parks_with_the_exact_string_no_match(self):
        """AD7's first number counts THIS string on THIS one site, so it is exact."""
        self.set_acceptance(record())
        st, t = self.returned()
        pod._rule_c(st, self.tmp)
        self.assertEqual(t.park_reason, "no-match")
        self.assertIsNone(self.lines()[-1]["row"])
        self.assertIn("facts", self.lines()[-1])

    def test_a_done_row_with_r4_holding_closes_the_task_and_expires_its_rows(self):
        self.write_table([sys_row("sys-done", action="done", outcome="go",
                                  when={"exit_code": 0}),
                          sys_row("task-lj-1-386-x", scope=f"task:{CODE}",
                                  priority=10, when={"heap_wall": True})])
        self.set_acceptance(record())
        st, t = self.returned()
        pod._rule_c(st, self.tmp)
        self.assertEqual(t.status, pod.DONE)
        rows = {r["id"]: r for r in table_mod.load_table(
            self.tmp / "dev" / "pod" / "table.toml")}
        self.assertTrue(rows["task-lj-1-386-x"]["expired"])

    def test_the_commit_message_names_the_row_that_CLOSED_the_task(self):
        """**GIT IS THE PERMANENT RECORD AND IT NAMED THE WRONG RULE.**

        `commit_task()` builds its message from `t.row`, and it is called BEFORE the
        `emit()` that assigns it, so the message carried the row from the PREVIOUS
        routing. MEASURED 2026-08-19: LJ-1.394 closed on `task-lj-1-394-no-go-stated`
        while git recorded `pod: LJ-1.394 done, row task-lj-1-394-no-go-attacked`, the
        escalate row that had routed its attempt 1. The transition log was right and the
        human-facing record was wrong.
        """
        self.write_table([sys_row("sys-stale", scope=f"task:{CODE}", priority=5,
                                  action="escalate", head_slot="coder_adversarial",
                                  when={"heap_wall": True}),
                          sys_row("sys-closer", action="done", outcome="go",
                                  when={"exit_code": 0})])
        self.set_acceptance(record())
        st, t = self.returned()
        t.row = "sys-stale"                    # what an earlier routing left behind
        pod._rule_c(st, self.tmp)
        self.assertEqual(t.status, pod.DONE)
        self.assertEqual(self.calls["commit_row"], "sys-closer",
                         "the commit named a row that did not close this task")

    def test_r4_refuses_a_go_close_whose_conjuncts_are_not_all_held(self):
        """A `done` row may match `exit_code = 42`, so R4 is what stops a green close
        over a red tree. On a refusal the task PARKS with `reason: "r4"`."""
        self.write_table([sys_row("sys-done", action="done", outcome="go",
                                  when={"exit_code": 0})])
        bad = record(conjuncts={1: True, 2: True, 3: False, 4: True, 5: True, 6: True})
        self.set_acceptance(bad)
        st, t = self.returned()
        pod._rule_c(st, self.tmp)
        self.assertEqual(t.status, pod.PARKED)
        self.assertEqual(t.park_reason, "r4")

    def test_a_no_go_close_needs_only_conjuncts_5_and_6(self):
        """A6 and R4's split. A NO-GO lands no proof, so conjuncts 1 to 4 measure
        nothing; conjuncts 5 and 6 protect the TREE and still bind."""
        self.write_table([sys_row("sys-nogo", action="done", outcome="no-go",
                                  when={"exit_code": 42})])
        rec = record(exit_code=42, delta=0,
                     conjuncts={1: False, 2: False, 3: False, 4: False,
                                5: True, 6: True})
        self.set_acceptance(rec)
        st, t = self.returned()
        pod._rule_c(st, self.tmp)
        self.assertEqual(t.status, pod.DONE)

    def test_a_no_go_close_is_still_refused_when_conjunct_5_is_red(self):
        self.write_table([sys_row("sys-nogo", action="done", outcome="no-go",
                                  when={"exit_code": 42})])
        rec = record(exit_code=42, conjuncts={5: False, 6: True})
        self.set_acceptance(rec)
        st, t = self.returned()
        pod._rule_c(st, self.tmp)
        self.assertEqual(t.park_reason, "r4")

    def test_a_no_go_that_fails_conjunct_6_is_accepted_not_parked_r4(self):
        """MEASURED 2026-08-20 on LJ-1.419: no-go-stated matched, conjunct 6
        FAILED, error_class stayed unsolved_meta, sys-lint-accept missed, r4
        parked a worktree that re-accept cannot repair without a worker."""
        self.write_table([sys_row("sys-nogo", action="done", outcome="no-go",
                                  when={"exit_code": 42})])
        rec = record(exit_code=42, error_class="unsolved_meta", delta=0,
                     conjuncts={1: False, 2: True, 3: True, 4: True,
                                5: True, 6: False})
        self.set_acceptance(rec)
        st, t = self.returned()
        pod._rule_c(st, self.tmp)
        self.assertEqual(t.status, pod.READY)
        self.assertEqual(t.row, "sys-lint-accept")
        self.assertEqual(t.attempt, 2)

    def test_accept_raises_the_attempt_and_returns_the_task_to_ready(self):
        self.write_table([sys_row("sys-accept", action="accept",
                                  when={"exit_code": 0})])
        self.set_acceptance(record())
        st, t = self.returned(attempt=1)
        pod._rule_c(st, self.tmp)
        self.assertEqual(t.status, pod.READY)
        self.assertEqual(t.attempt, 2)

    def test_attempt_max_parks_naming_the_row_that_kept_matching(self):
        """B2. `route()` is pure, so a retry that changes nothing reproduces the same
        record and the same winner. The cap NAMES the row, because that is a design error
        in the ROW and not in the task."""
        self.write_table([sys_row("sys-accept", action="accept",
                                  when={"exit_code": 0})])
        self.set_acceptance(record())
        st, t = self.returned(attempt=1)
        limit = heads_mod.limits()["attempt_max"]
        for _ in range(limit):
            t.status = pod.RETURNED
            pod._rule_c(st, self.tmp)
        self.assertEqual(t.status, pod.PARKED)
        self.assertEqual(t.park_reason, "attempt_max:sys-accept")

    def test_the_cap_covers_the_four_LOOPING_actions_and_never_a_stop_loop(self):
        """A3 makes a `stop_loop` row undefeatable, and the cap must not defeat it.

        The shape is a real one: a row accepts four times, the maintainer reads the park
        and CHANGES that row's action to `stop_loop`. `same_row_runs()` still counts four
        for the id, so an unguarded cap parks the task under `attempt_max` and the loop
        keeps running through the very row that says stop.
        """
        self.write_table([sys_row("sys-x", action="accept", when={"exit_code": 0})])
        self.set_acceptance(record())
        st, t = self.returned(attempt=1)
        for _ in range(heads_mod.limits()["attempt_max"] - 1):
            t.status = pod.RETURNED
            pod._rule_c(st, self.tmp)
        self.write_table([sys_row("sys-x", action="stop_loop", when={"exit_code": 0})])
        t.status = pod.RETURNED
        self.assertIs(pod._rule_c(st, self.tmp), pod.STOP)
        self.assertEqual(t.park_reason, "stop_loop:sys-x")

    def test_a_different_matching_row_restarts_the_run_at_zero(self):
        """That is what "the maintainer fixed the row" looks like."""
        self.write_table([sys_row("sys-a", action="accept", when={"exit_code": 0})])
        self.set_acceptance(record())
        st, t = self.returned()
        t.status = pod.RETURNED
        pod._rule_c(st, self.tmp)
        self.write_table([sys_row("sys-b", action="accept", when={"exit_code": 0})])
        t.status = pod.RETURNED
        pod._rule_c(st, self.tmp)
        self.assertEqual(pod.same_row_runs(t, "sys-a", self.tmp), 0)
        self.assertEqual(pod.same_row_runs(t, "sys-b", self.tmp), 1)

    def test_every_routed_record_is_appended_to_the_corpus_as_live(self):
        """4.5.2: ONE writer puts a record in and it is `emit()`. `seq` makes the id
        unique and the append idempotent after a crash."""
        self.write_table([sys_row("sys-accept", action="accept",
                                  when={"exit_code": 0})])
        self.set_acceptance(record())
        st, _ = self.returned()
        pod._rule_c(st, self.tmp)
        text = (self.tmp / "dev" / "pod" / "replay-corpus.jsonl").read_text()
        rows = [json.loads(x) for x in text.strip().split("\n")]
        self.assertEqual(len(rows), 1)
        self.assertEqual(rows[0]["provenance"], "live")
        self.assertTrue(rows[0]["id"].startswith("c-"))
        replay_mod.check_record(rows[0])       # it must pass the corpus loader

    def test_a3_sorts_stop_loop_ahead_of_a_task_row_that_also_matches(self):
        """Without A3 a task branch reading only `seconds_min` outranks the system row
        and the loop keeps running through a change to the trophy statement."""
        self.write_table([
            sys_row("sys-spec-surface", action="stop_loop", priority=1,
                    when={"error_class": "spec_surface"}),
            sys_row("task-lj-1-386-slow", scope=f"task:{CODE}", priority=10,
                    action="accept", when={"changed_files_count_max": 5})])
        self.set_acceptance(record(exit_code=1, error_class="spec_surface"))
        st, t = self.returned()
        self.assertIs(pod._rule_c(st, self.tmp), pod.STOP)
        self.assertEqual(t.park_reason, "stop_loop:sys-spec-surface")


# ---------------------------------------------------------------- apply()'s six actions


class Actions(LoopCase):
    """Every one of the eight actions reaches an implementation. `done` and `accept` are
    rule (c)'s; the other six are here."""

    def setUp(self):
        super().setUp()
        self.st = pod.State()
        self.t = pod.Task(CODE, brief=f"agents/tasks/{DIR}/{CODE}.md",
                          status=pod.CHECKING, attempt=1)
        self.st.tasks[CODE] = self.t
        self.rec = record()

    def act(self, action, row_id="sys-x", **kw):
        self.write_table([sys_row(row_id, action=action, when={"exit_code": 0}, **kw)])
        return pod.apply(action, self.t, self.rec, row_id, self.st, self.tmp)

    def test_park_parks_with_the_row_reason(self):
        self.assertIs(self.act("park"), pod.CONTINUE)
        self.assertEqual(self.t.status, pod.PARKED)
        self.assertEqual(self.t.park_reason, "row:sys-x")

    def test_park_and_split_appends_a_queue_REQUEST_with_no_brief(self):
        """The program never writes a brief, because AD3 gives the brief to the
        mathematician. An entry with no `brief` is a REQUEST and never a task."""
        self.assertIs(self.act("park_and_split"), pod.CONTINUE)
        entries = pod.queue_entries(self.tmp / "dev" / "pod" / "queue.toml")
        self.assertEqual(len(entries), 1)
        self.assertNotIn("brief", entries[0])
        self.assertEqual(entries[0]["split_of"], CODE)
        self.assertEqual(self.t.status, pod.PARKED)

    def test_redispatch_returns_to_ready_and_raises_the_attempt(self):
        self.assertIs(self.act("redispatch"), pod.CONTINUE)
        self.assertEqual(self.t.status, pod.READY)
        self.assertEqual(self.t.attempt, 2)

    def test_redispatch_narrower_cuts_the_scope_to_the_first_failing_target(self):
        self.rec["runs_all"] = [{"target": "src/A.lagda.md", "rc": 0, "seconds": 1.0},
                                {"target": "src/B.lagda.md", "rc": 1, "seconds": 2.0}]
        self.assertIs(self.act("redispatch_narrower"), pod.CONTINUE)
        self.assertEqual(self.t.scope_narrow, "src/B.lagda.md")
        self.assertEqual(self.t.status, pod.READY)

    def test_redispatch_narrower_narrows_nothing_when_every_run_passed(self):
        """It returns None rather than guessing a file.

        THE FIELD IS DIRTIED FIRST. `scope_narrow` is None on a fresh task, so asserting
        None after the call held even when `apply()` never wrote the field at all.
        """
        self.t.scope_narrow = "src/Stale.lagda.md"
        self.rec["runs_all"] = [{"target": "src/A.lagda.md", "rc": 0, "seconds": 1.0}]
        self.act("redispatch_narrower")
        self.assertIsNone(self.t.scope_narrow)

    def test_escalate_sets_the_head_slot_the_row_names_and_rule_f_dispatches_it(self):
        self.assertIs(self.act("escalate", head_slot="coder_adversarial"), pod.CONTINUE)
        self.assertEqual(self.t.head_slot, "coder_adversarial")
        self.assertEqual(self.t.status, pod.READY)

    def test_stop_loop_parks_its_own_task_FIRST_then_stops(self):
        """The order is deliberate: the task must not stay CHECKING across the stop, and
        the park line names the row so `pod resume` re-routes it like any other park."""
        self.assertIs(self.act("stop_loop"), pod.STOP)
        self.assertEqual(self.t.status, pod.PARKED)
        self.assertEqual(self.t.park_reason, "stop_loop:sys-x")
        lines = self.lines()
        self.assertEqual(lines[-2]["to"], "PARKED")
        self.assertEqual(lines[-1]["to"], "STOPPED")
        self.assertEqual(lines[-1]["task"], "")
        self.assertTrue((self.tmp / ".pod-state" / "STOPPED").exists())
        self.assertEqual(self.calls["notify"], ["row sys-x"])

    def test_an_unknown_action_raises_rather_than_passing_silently(self):
        with self.assertRaises(KeyError):
            pod.apply("teleport", self.t, self.rec, "sys-x", self.st, self.tmp)

    def test_every_action_of_section_4_2_reaches_an_implementation(self):
        """The set is CLOSED, so the program makes no judgement."""
        handled = {"done", "accept"}                      # rule (c) has these two
        src = Path(ROOT / "scripts" / "pod" / "pod.py").read_text(encoding="utf-8")
        for action in table_mod.ACTIONS:
            if action in handled:
                continue
            self.assertIn(f'action == "{action}"', src, action)


# ---------------------------------------------------------------- rule (d) STOP AT 3


class RuleD(LoopCase):
    """AD14. `parked_max` parked tasks stop the loop, and the stop never touches a worker.

    **THE THRESHOLD IS READ AND NEVER SPELLED.** These tests carried the literal 3, so
    raising `[limits].parked_max` to 7 on 2026-08-19 reddened five of them for the one
    reason that must never redden a test, which is that the configuration changed exactly
    as it was asked to. The limit now comes from the same place the rule reads it.
    """

    LIMIT = pod._limits()["parked_max"]

    def park(self, st, n):
        for i in range(n):
            code = f"LJ-1.{400 + i}"
            st.tasks[code] = pod.Task(code, status=pod.PARKED,
                                      park_reason="no-match", parked_at=time.time())
        return st

    def test_one_below_the_limit_does_not_stop_the_loop(self):
        st = self.park(pod.State(), self.LIMIT - 1)
        self.assertIs(pod._rule_d(st, self.tmp), pod.CONTINUE)
        self.assertFalse((self.tmp / ".pod-state" / "STOPPED").exists())

    def test_the_limit_stops_the_loop_and_pushes_to_the_owner(self):
        st = self.park(pod.State(), self.LIMIT)
        self.assertIs(pod._rule_d(st, self.tmp), pod.STOP)
        self.assertTrue((self.tmp / ".pod-state" / "STOPPED").exists())
        # THE SENTENCE COUNTS THE PARKS, it does not recite the limit.
        self.assertEqual(self.calls["notify"], [f"{self.LIMIT} parked"])
        line = self.lines()[-1]
        self.assertEqual((line["task"], line["to"], line["why"]),
                         ("", "STOPPED", f"{self.LIMIT} parked"))

    def test_the_stop_writes_ONE_loop_line_and_not_one_a_tick(self):
        st = self.park(pod.State(), self.LIMIT)
        pod._rule_d(st, self.tmp)
        pod._rule_d(st, self.tmp)
        stops = [x for x in self.lines() if x["to"] == "STOPPED"]
        self.assertEqual(len(stops), 1)

    def test_the_park_counter_reaching_the_limit_stops_the_WHOLE_tick(self):
        """The end-to-end path: `parked_max` returns that match nothing park, and the last
        stops the loop. The fixture CAN fail: with a matching row nothing parks."""
        self.set_acceptance(record())
        st = pod.State()
        for i in range(self.LIMIT):
            code = f"LJ-1.{500 + i}"
            st.tasks[code] = pod.Task(code, status=pod.RETURNED,
                                      brief=f"agents/tasks/{DIR}/{CODE}.md")
        self.assertIs(pod.pod_tick(st, self.tmp), pod.STOP)
        self.assertEqual(st.count(pod.PARKED), self.LIMIT)
        self.assertTrue((self.tmp / ".pod-state" / "STOPPED").exists())

    def test_the_same_three_returns_park_NOTHING_when_a_row_matches(self):
        """C-45: the fixture that produced the stop above can also produce no stop."""
        self.write_table([sys_row("sys-accept", action="accept",
                                  when={"exit_code": 0})])
        self.set_acceptance(record())
        # The three codes are not the fixture's task, so rule (f) would park them on
        # `admission` for a reason that has nothing to do with the routing under test.
        self.patch(preflight_mod, "preflight",
                   lambda brief, root=None, show=True, **kw: [])
        self.patch(table_mod, "admit_rows", lambda code, brief: True)
        st = pod.State()
        for i in range(3):
            code = f"LJ-1.{500 + i}"
            st.tasks[code] = pod.Task(code, status=pod.RETURNED,
                                      brief=f"agents/tasks/{DIR}/{CODE}.md")
        pod.pod_tick(st, self.tmp)
        self.assertEqual(st.count(pod.PARKED), 0)

    def test_the_stop_refuses_rule_f_and_nothing_else(self):
        """M7's stated consequence and the founding incident behind it: the stop stops
        DISPATCHING. Rules (a1) to (e) keep running, so work that already returned is
        still observed and closed."""
        (self.tmp / ".pod-state" / "STOPPED").touch()
        self.write_table([sys_row("sys-accept", action="accept",
                                  when={"exit_code": 0})])
        self.set_acceptance(record())
        st = pod.State()
        st.tasks[CODE] = pod.Task(CODE, status=pod.RETURNED,
                                  brief=f"agents/tasks/{DIR}/{CODE}.md")
        self.assertIs(pod.pod_tick(st, self.tmp), pod.STOP)
        self.assertEqual(st.tasks[CODE].status, pod.READY)   # rule (c) ran
        self.assertEqual(self.calls["launch"], [])           # rule (f) did not

    def test_a_soft_stop_does_not_launch_and_keeps_ticking_while_a_worker_runs(self):
        """`--soft` must not make `_rule_f` return STOP while a pid is still live,
        or the return has nobody accepting it."""
        (self.tmp / ".pod-state" / "DRAINING").touch()
        st = pod.State()
        st.tasks[CODE] = pod.Task(CODE, status=pod.RUNNING, pid=os.getpid(),
                                  brief=f"agents/tasks/{DIR}/{CODE}.md")
        st.tasks["LJ-1.500"] = pod.Task("LJ-1.500", status=pod.READY,
                                        brief=f"agents/tasks/{DIR}/{CODE}.md")
        self.assertIs(pod.pod_tick(st, self.tmp), pod.CONTINUE)
        self.assertEqual(self.calls["launch"], [])
        self.assertEqual(st.tasks["LJ-1.500"].status, pod.READY)
        self.assertTrue((self.tmp / ".pod-state" / "DRAINING").exists())
        self.assertFalse((self.tmp / ".pod-state" / "STOPPED").exists())

    def test_a_soft_stop_STOPs_when_no_agent_is_in_flight(self):
        (self.tmp / ".pod-state" / "DRAINING").touch()
        st = pod.State()
        st.tasks[CODE] = pod.Task(CODE, status=pod.PARKED, park_reason="no-match",
                                  brief=f"agents/tasks/{DIR}/{CODE}.md")
        self.assertIs(pod.pod_tick(st, self.tmp), pod.STOP)
        self.assertTrue((self.tmp / ".pod-state" / "STOPPED").exists())
        self.assertFalse((self.tmp / ".pod-state" / "DRAINING").exists())
        self.assertEqual(self.lines()[-1]["to"], pod.LOOP_STOPPED)
        self.assertEqual(self.lines()[-1]["why"], "drain")

    def test_a_soft_stop_still_closes_a_return_then_STOPs(self):
        """Rules (b) and (c) run before the drain check, so the last return is
        accepted on the same tick the loop exits."""
        (self.tmp / ".pod-state" / "DRAINING").touch()
        self.write_table([sys_row("sys-accept", action="accept",
                                  when={"exit_code": 0})])
        self.set_acceptance(record())
        st = pod.State()
        st.tasks[CODE] = pod.Task(CODE, status=pod.RETURNED,
                                  brief=f"agents/tasks/{DIR}/{CODE}.md")
        self.assertIs(pod.pod_tick(st, self.tmp), pod.STOP)
        self.assertEqual(st.tasks[CODE].status, pod.READY)
        self.assertEqual(self.calls["launch"], [])
        self.assertEqual(self.lines()[-1]["why"], "drain")


# ---------------------------------------------------------------- rule (e) MAINTAINER


class DeclaredStop(LoopCase):
    """A mathematician calling a halt, owner's ruling 2026-08-18.

    **THE RULING IS THAT A DECLARED STOP AND AN EMPTY QUEUE ARE DIFFERENT STATES.** Rule
    (g) asks a mathematician what is missing and it had two outcomes, both of which the
    program read as「nothing to dispatch」: so the loop refilled every hour for ever, and
    nothing in it counted finished work.
    """

    def _write(self, text):
        d = self.tmp / "dev" / "pod"
        d.mkdir(parents=True, exist_ok=True)
        (d / "stop-request.toml").write_text(text, encoding="utf-8")
        return d / "stop-request.toml"

    GOOD = ('[stop]\nclaim = "milestone"\nreason = "Both trophies are in the case."\n'
            'evidence = ["src/Landmarks.lagda.md:76", "src/Landmarks.lagda.md:88"]\n')

    def test_a_declared_stop_STOPS_the_loop_with_its_own_reason(self):
        self._write(self.GOOD)
        st = pod.State()
        self.assertIs(pod._rule_d(st, self.tmp), pod.STOP)
        line = json.loads((self.tmp / "dev" / "pod" / "transitions"
                           ).glob("*.jsonl").__next__().read_text().splitlines()[-1])
        self.assertEqual(line.get("why"), "declared:milestone",
                         "the declared stop must not share a reason with the parked stop")
        self.assertIn("Landmarks", " ".join(line.get("declared_evidence") or []))

    def test_it_is_read_ONCE_so_a_stale_file_cannot_stop_tomorrow(self):
        p = self._write(self.GOOD)
        pod._rule_d(pod.State(), self.tmp)
        self.assertFalse(p.is_file(), "the honoured request was not retired")
        self.assertTrue(p.with_suffix(".toml.stopped").is_file())

    def test_a_stop_with_NO_CHECKABLE_EVIDENCE_is_refused_and_never_silent(self):
        """A model that can halt the programme by writing four words is a model whose
        worst hour costs a day. And a refusal nobody records is worse than no refusal:
        the mathematician believes it stopped the loop and it did not."""
        for bad, what in (
            ('[stop]\nclaim = "milestone"\nreason = "done"\nevidence = ["it works"]\n',
             "no file:line"),
            ('[stop]\nreason = "done"\nevidence = ["a.md:1"]\n', "no claim"),
            ('[stop]\nclaim = "m"\nevidence = ["a.md:1"]\n', "no reason"),
            ('[stop]\nclaim = "m"\nreason = "d"\n', "no evidence"),
            ('not toml at all\n', "unparseable"),
        ):
            with self.subTest(what=what):
                p = self._write(bad)
                st = pod.State()
                self.assertIs(pod._rule_d(st, self.tmp), pod.CONTINUE,
                              f"an unevidenced stop ({what}) halted the loop")
                self.assertFalse(p.is_file())
                self.assertTrue(p.with_suffix(".toml.refused").is_file(),
                                f"the refusal of ({what}) left no trace")
                log = (self.tmp / "dev" / "pod" / "transitions").glob("*.jsonl")
                text = "".join(f.read_text() for f in log)
                self.assertIn("stop_request", text, "the refusal was silent")
                p.with_suffix(".toml.refused").unlink()

    def test_NO_request_leaves_rule_d_exactly_as_it_was(self):
        st = pod.State()
        self.assertIs(pod._rule_d(st, self.tmp), pod.CONTINUE)
        for i in range(pod._limits()["parked_max"]):     # the limit, never a literal
            st.tasks[f"LJ-1.{i}"] = pod.Task(f"LJ-1.{i}", status=pod.PARKED)
        self.assertIs(pod._rule_d(st, self.tmp), pod.STOP, "the parked stop broke")


class StateSalvage(unittest.TestCase):
    """A state file that something outside this program renamed away.

    **MEASURED 2026-08-18.** `.pod-state/` held `state [conflicted].json`,
    `state [conflicted 2].json` and `state [conflicted 3].json` at seq 3, 4 and 5, and no
    `state.json` at all. 27 such files stand in this tree, the oldest from 2026-07-27, in
    `_build/` (12), `.claude/` (11), `.pod-state/` (3) and `agents/` (1). No tracked
    source has ever been hit. `save_state()` writes a temporary file and renames it over
    the target, which is the correct atomic write and the exact shape a naive sync client
    reads as a two-sided change.
    """

    def setUp(self):
        self.dir = tempfile.TemporaryDirectory()
        self.tmp = Path(self.dir.name)
        self.addCleanup(self.dir.cleanup)

    def _copy(self, name, seq):
        (self.tmp / name).write_text(
            json.dumps({"version": 1, "seq": seq, "stopped": False, "tasks": {}}),
            encoding="utf-8")
        return self.tmp / name

    def test_the_NEWEST_readable_copy_is_taken_and_restored_in_place(self):
        import time as _t
        for i, name in enumerate(("state [conflicted].json",
                                  "state [conflicted 2].json",
                                  "state [conflicted 3].json")):
            q = self._copy(name, 3 + i)
            os.utime(q, (1000 + i, 1000 + i))
        st = pod.load_state(self.tmp / "state.json")
        self.assertEqual(st.seq, 5, "the salvage took a stale copy")
        self.assertTrue((self.tmp / "state.json").is_file(),
                        "the salvage must put the file back, or the next tick salvages "
                        "again and the loop never has a state file of its own")

    def test_both_spellings_are_matched_because_both_are_in_this_tree(self):
        q = self._copy("state (conflicted).json", 7)
        os.utime(q, (1000, 1000))
        self.assertEqual(pod.load_state(self.tmp / "state.json").seq, 7)

    def test_an_unreadable_copy_is_skipped_for_the_next_one(self):
        old = self._copy("state [conflicted].json", 2)
        os.utime(old, (1000, 1000))
        bad = self.tmp / "state [conflicted 2].json"
        bad.write_text("{ this is not json", encoding="utf-8")
        os.utime(bad, (2000, 2000))
        self.assertEqual(pod.load_state(self.tmp / "state.json").seq, 2)

    def test_with_no_copy_at_all_it_is_still_a_blank_state_and_never_a_raise(self):
        self.assertEqual(pod.load_state(self.tmp / "state.json").seq, 0)

    def test_an_unrelated_neighbour_is_never_taken(self):
        """`conflict_copies` must not sweep up a file that merely sits beside it."""
        (self.tmp / "registry.json").write_text('{"seq": 99}', encoding="utf-8")
        (self.tmp / "state-backup.json").write_text('{"seq": 98}', encoding="utf-8")
        self.assertEqual(pod.conflict_copies(self.tmp / "state.json"), [])


class Direction(LoopCase):
    """`dev/pod/direction.md`: the owner's standing mathematical direction, ruled
    2026-08-18.

    **THE GAP IT FILLS WAS MEASURED FIRST.** No line of the program read `dev/PLAN.md`,
    so a mid-flight correction had no mechanical path at all: the REFILL brief's prose
    asked a mathematician to read the plan, and rule (g) fires only on an empty queue.
    """

    def _write(self, text):
        d = self.tmp / "dev" / "pod"
        d.mkdir(parents=True, exist_ok=True)
        (d / "direction.md").write_text(text, encoding="utf-8")

    def test_a_change_is_reported_ONCE_so_a_rule_acting_on_it_cannot_loop(self):
        self._write("aim at the bridge first")
        self.assertTrue(pod.direction_changed(None, self.tmp))
        self.assertFalse(pod.direction_changed(None, self.tmp))
        self._write("aim at GCH first")
        self.assertTrue(pod.direction_changed(None, self.tmp))
        self.assertFalse(pod.direction_changed(None, self.tmp))

    def test_the_outgoing_direction_is_ARCHIVED_and_never_deleted(self):
        """Owner's ruling: keep one current direction and archive the old."""
        self._write("first direction")
        pod.direction_changed(None, self.tmp)
        self._write("second direction")
        pod.direction_changed(None, self.tmp)
        arc = self.tmp / "archive" / "dev" / "direction"
        bodies = [f.read_text(encoding="utf-8") for f in arc.glob("*.md")]
        self.assertEqual(bodies, ["first direction"],
                         "the superseded direction must survive under archive/")
        self.assertEqual((self.tmp / "dev" / "pod" / "direction.md").read_text(),
                         "second direction", "the live file keeps ONE direction")

    def test_plan_mode_reports_a_change_without_CONSUMING_it(self):
        """`--plan` that swallowed the change would make the real tick miss it."""
        self._write("a direction")
        self.assertTrue(pod.direction_changed(None, self.tmp, record=False))
        self.assertTrue(pod.direction_changed(None, self.tmp, record=False))
        self.assertTrue(pod.direction_changed(None, self.tmp))   # still there for real

    def test_every_slot_is_handed_the_direction(self):
        """Owner's ruling: all five. A reviewer that does not know the direction
        reviews against the old one."""
        (self.tmp / "AGENTS.md").write_text("boundary", encoding="utf-8")
        self._write("d")
        inst = self.tmp / "dev" / "pod" / "instructions"
        inst.mkdir(parents=True, exist_ok=True)
        (self.tmp / "dev" / "pod" / "screen.toml").write_text("endpoint = \"ruled\"\n")
        for slot in ("mathematician", "mathematician_adversarial", "coder",
                     "coder_adversarial", "maintainer"):
            (inst / f"{slot}.md").write_text("clauses", encoding="utf-8")
            names = [f.name for f in pod.preamble_for(slot, self.tmp)]
            self.assertEqual(names, [f"{slot}.md", "AGENTS.md", "screen.toml",
                                     "direction.md"],
                             f"{slot} was dispatched without the screen or the direction")
            self.assertEqual(pod.PREAMBLE_MISSING, [],
                             "a complete preamble reports no defect")

    def test_a_missing_preamble_file_is_NAMED_and_still_never_refuses(self):
        """**THE SILENT DROP WAS THE DEFECT.** `preamble_for()` filtered absent files out
        and said nothing, so a worker dispatched with NO Boundary at all produced a
        shorter list and nothing in the program read its length. The docstring claimed
        「the caller's own defect list reports the rest」and no caller had one: `grep -n
        "defect list" scripts/pod/pod.py` found the claim and nothing else.

        IT MUST STILL NOT REFUSE. Three of the four rules in front of a worker is better
        than none, and an absent rule home is a repair for the maintainer, not a reason
        to stop the loop."""
        self._write("d")
        inst = self.tmp / "dev" / "pod" / "instructions"
        inst.mkdir(parents=True, exist_ok=True)
        (inst / "coder.md").write_text("clauses", encoding="utf-8")
        # `AGENTS.md` and the screen are both absent in this tree.
        (self.tmp / "AGENTS.md").unlink(missing_ok=True)
        (self.tmp / "dev" / "pod" / "screen.toml").unlink(missing_ok=True)
        buf = io.StringIO()
        with contextlib.redirect_stderr(buf):
            got = pod.preamble_for("coder", self.tmp)
        self.assertEqual([f.name for f in got], ["coder.md", "direction.md"],
                         "what exists is still handed over")
        self.assertEqual([pathlib.Path(p).name for p in pod.PREAMBLE_MISSING],
                         ["AGENTS.md", "screen.toml"])
        self.assertIn("AGENTS.md", buf.getvalue(),
                      "the operator's pane is the channel rule (f) already tees")

    def test_the_missing_list_is_the_LAST_call_and_never_an_accumulation(self):
        """A stale name would send the maintainer to repair a file that is already
        there."""
        self._write("d")
        inst = self.tmp / "dev" / "pod" / "instructions"
        inst.mkdir(parents=True, exist_ok=True)
        (inst / "coder.md").write_text("clauses", encoding="utf-8")
        (self.tmp / "AGENTS.md").unlink(missing_ok=True)
        (self.tmp / "dev" / "pod" / "screen.toml").unlink(missing_ok=True)
        with contextlib.redirect_stderr(io.StringIO()):
            pod.preamble_for("coder", self.tmp)
            self.assertTrue(pod.PREAMBLE_MISSING)
            (self.tmp / "AGENTS.md").write_text("boundary", encoding="utf-8")
            (self.tmp / "dev" / "pod" / "screen.toml").write_text("x = 1\n")
            pod.preamble_for("coder", self.tmp)
        self.assertEqual(pod.PREAMBLE_MISSING, [])


class RuleE(LoopCase):
    """AD15. The trigger is mechanical: 12 hours, or three parked tasks.

    **THE TRIGGER GATES THE BATCH AND NOT THE MAINTAINER, since 2026-08-18.** The owner
    ruled the master order wrong: the maintainer is the role that repairs `pod.py`, so
    it must outlive `pod.py`, and its liveness cannot hang off a twelve-hour batch clock.
    Rule (e) now ensures it EVERY tick, idempotently, and the trigger only feeds it.
    """

    def test_the_maintainer_is_ensured_every_tick_whatever_the_trigger_says(self):
        """The residency ruling in one assertion. A batch line one minute old holds the
        BATCH, and the maintainer's own liveness is checked all the same."""
        st = pod.State()
        # `result="prompted"` is what「the maintainer was FED」means. A harvest
        # outcome carries the same event name and must NOT hold the trigger,
        # which `FeedClockCountsFeeds` pins.
        pod.emit_event(st, "batch", result="prompted", root=self.tmp)
        for _ in range(3):
            pod._rule_e(st, self.tmp)
        self.assertEqual(self.calls["ensure"], 3, "residency is not on the batch clock")
        self.assertEqual(self.calls["maintainer"], 0, "the batch trigger was held")

    def test_the_ensure_is_idempotent_by_construction_not_by_a_refusal(self):
        """**THE DEFECT THIS REPLACES GOT WORSE WITH TIME.** `spawn_maintainer()` leaned
        on the launcher's「task already running」refusal, which returned None and wrote NO
        batch line, so `hours_since_last_batch()` kept reporting a stale age and the
        trigger re-fired every `tick_seconds`, invisibly. `ensure_maintainer()` asks
        whether the agent is there and returns without launching when it is, so there is
        no refusal path for a loop to form on."""
        seen = []
        self.patch(pod, "maintainer_alive", lambda root=None: True)
        self.patch(pod, "write_batch_brief", lambda st, root=None: seen.append(1))
        st = pod.State()
        for _ in range(5):
            REAL_ENSURE_MAINTAINER(st, self.tmp)   # the REAL one, not setUp's counter
        self.assertEqual(seen, [], "a live maintainer must cost nothing at all")

        # AND IT MUST STILL LAUNCH WHEN THE AGENT IS GONE, or「costs nothing」would be
        # satisfied by a function that does nothing at all.
        self.patch(pod, "maintainer_alive", lambda root=None: False)
        REAL_ENSURE_MAINTAINER(st, self.tmp)
        self.assertEqual(seen, [1], "a dead maintainer must be started again")

    def test_a_prompt_STAMPS_the_clock_so_the_next_tick_does_not_prompt_again(self):
        """**THE DEFECT THIS PINS IS THE OLD ONE REBORN ON A NEW PATH.** The spawn era's
        loop was hidden by the launcher's「task already running」refusal, which cost one
        wasted launch per tick. A PROMPT HAS NO REFUSAL: `herdr agent prompt` always
        succeeds and queues, so an unstamped clock would hand the resident maintainer a
        duplicate batch every `tick_seconds`, and C-61 says each one is read in turn.

        `hours_since_last_batch()` counts `batch` lines, and until 2026-08-18 only
        `harvest_batch()` wrote one, which happens when the maintainer RETURNS.
        """
        prompts = []
        self.patch(pod, "maintainer_alive", lambda root=None: True)
        self.patch(pod, "write_batch_brief",
                   lambda st, root=None: self.tmp / "agents" / "tasks" / "b.md")

        class _Mod:
            HARNESS = ""

            @staticmethod
            def herdr_name(t):
                return "pod-batch"

            @staticmethod
            def herdr_prompt(name, text):
                prompts.append(name)
                return True

        self.patch(facts_mod, "launcher", lambda: _Mod)
        st = pod.State()
        self.assertGreaterEqual(pod.hours_since_last_batch(self.tmp), 12)
        REAL_PROMPT_MAINTAINER(st, self.tmp)   # the REAL one, not setUp's counter
        self.assertEqual(len(prompts), 1)
        self.assertLess(pod.hours_since_last_batch(self.tmp), 1,
                        "the prompt did not stamp the clock; rule (e) will re-fire "
                        "on the very next tick and flood the resident maintainer")

    def test_the_first_batch_fires_because_no_batch_line_exists_yet(self):
        st = pod.State()
        pod._rule_e(st, self.tmp)
        self.assertEqual(self.calls["maintainer"], 1)
        self.assertEqual(self.calls["digest"], 1)

    def test_a_recent_batch_line_holds_the_trigger_below_three_parked(self):
        st = pod.State()
        # `result="prompted"` is what「the maintainer was FED」means. A harvest
        # outcome carries the same event name and must NOT hold the trigger,
        # which `FeedClockCountsFeeds` pins.
        pod.emit_event(st, "batch", result="prompted", root=self.tmp)
        pod._rule_e(st, self.tmp)
        self.assertEqual(self.calls["maintainer"], 0)

    def _park_three(self, st):
        """Park three tasks the way production does, through a real transition each.

        A hand-set `status = PARKED` with no log line is not a park: `emit()` is the only
        writer of one, and AD15's trigger reads the log.
        """
        for i in range(3):
            t = pod.Task(f"X{i}", status=pod.CHECKING)
            st.tasks[f"X{i}"] = t
            pod.emit(st, t, pod.CHECKING, pod.PARKED, reason="no-match", root=self.tmp)

    def test_a_new_park_fires_the_batch_whatever_the_clock_says(self):
        st = pod.State()
        # `result="prompted"` is what「the maintainer was FED」means. A harvest
        # outcome carries the same event name and must NOT hold the trigger,
        # which `FeedClockCountsFeeds` pins.
        pod.emit_event(st, "batch", result="prompted", root=self.tmp)
        self._park_three(st)
        pod._rule_e(st, self.tmp)
        self.assertEqual(self.calls["maintainer"], 1)

    def test_the_SAME_parks_never_fire_a_second_batch(self):
        """**THE PROMPT STORM, and this is its regression guard.** The trigger used to
        read `st.count(PARKED) >= 3`, which is a LEVEL: three parked tasks stay parked
        until a row un-parks them, so it held at every tick. MEASURED 2026-08-19: four
        identical batches at 07:05:03, 07:05:34, 07:06:06 and 07:06:37, one per tick,
        all naming the same three tasks. It is an EDGE now, so a park set that nobody
        has cured is asked about ONCE."""
        st = pod.State()
        # `result="prompted"` is what「the maintainer was FED」means. A harvest
        # outcome carries the same event name and must NOT hold the trigger,
        # which `FeedClockCountsFeeds` pins.
        pod.emit_event(st, "batch", result="prompted", root=self.tmp)
        self._park_three(st)
        pod._rule_e(st, self.tmp)
        pod._rule_e(st, self.tmp)
        pod._rule_e(st, self.tmp)
        self.assertEqual(self.calls["maintainer"], 1,
                         "the same three parks asked the maintainer more than once")

    def test_r15_refuses_a_batch_that_wrote_outside_the_proposal_file(self):
        """`--untracked-files=all` is why the untracked half is visible: a maintainer
        that writes a NEW file writes an untracked path, which is the class the flag
        exists to reveal."""
        self.patch(facts_mod, "_status_paths",
                   lambda root: ["dev/pod/proposals/x.toml", "src/L/Cardinal.lagda.md"])
        (self.tmp / "dev" / "pod" / "proposals" / "x.toml").write_text(
            '[[row]]\nid = "r"\n')
        st = pod.State()
        pod.harvest_batch(st, self.tmp)
        line = [x for x in self.lines() if x.get("event") == "batch"][-1]
        self.assertEqual(line["result"], "scope")
        self.assertIn("src/L/Cardinal.lagda.md", line["paths"])

    def test_a_scoped_batch_reaches_the_replay_and_admits_a_clean_row(self):
        self.patch(facts_mod, "_status_paths",
                   lambda root: ["dev/pod/proposals/x.toml"])
        (self.tmp / "dev" / "pod" / "proposals" / "x.toml").write_text(textwrap.dedent("""
            [[row]]
            id = "sys-new-row"
            scope = "system"
            priority = 50
            action = "park"
            added = 2026-08-17
            added_by = "maintainer"
            reason = "a proposed row"
            expired = false

              [row.when]
              heap_wall = true
            """))
        st = pod.State()
        pod.harvest_batch(st, self.tmp)
        line = [x for x in self.lines() if x.get("event") == "batch"][-1]
        self.assertEqual(line["result"], "admit")
        ids = [r["id"] for r in table_mod.load_table(
            self.tmp / "dev" / "pod" / "table.toml")]
        self.assertIn("sys-new-row", ids)

    def test_the_replay_REJECTS_a_row_that_moves_a_frozen_record(self):
        """R3: a new row must not move a record an existing row already matches."""
        self.write_table([sys_row("sys-old", action="accept", priority=100,
                                  when={"exit_code": 0})])
        rec = record()
        rec["id"], rec["provenance"] = "c-1", "live"
        (self.tmp / "dev" / "pod" / "replay-corpus.jsonl").write_text(
            json.dumps(rec) + "\n")
        self.patch(facts_mod, "_status_paths",
                   lambda root: ["dev/pod/proposals/x.toml"])
        (self.tmp / "dev" / "pod" / "proposals" / "x.toml").write_text(textwrap.dedent("""
            [[row]]
            id = "sys-thief"
            scope = "system"
            priority = 1
            action = "park"
            added = 2026-08-17
            added_by = "maintainer"
            reason = "it steals the traffic"
            expired = false

              [row.when]
              exit_code = 0
            """))
        st = pod.State()
        pod.harvest_batch(st, self.tmp)
        line = [x for x in self.lines() if x.get("event") == "batch"][-1]
        self.assertEqual(line["result"], "reject")
        self.assertTrue(line["moved"])

    def test_an_admitted_proposal_is_renamed_and_COMMITTED_by_explicit_path(self):
        """R15 READS THE WHOLE TREE, so the batch must not leave its own file behind.

        `harvest_batch()` renames an admitted proposal to `*.toml.admitted`. Left
        untracked, that file is a path other than the next proposal, so
        `maintainer_scope_ok()` refuses the NEXT batch on `scope` and no row is ever
        admitted again. The commit is R8's: explicit paths, and never a push.
        """
        self.patch(facts_mod, "_status_paths",
                   lambda root: ["dev/pod/proposals/x.toml"])
        (self.tmp / "dev" / "pod" / "proposals" / "x.toml").write_text(textwrap.dedent("""
            [[row]]
            id = "sys-admitted"
            scope = "system"
            priority = 50
            action = "park"
            added = 2026-08-17
            added_by = "maintainer"
            reason = "a proposed row"
            expired = false

              [row.when]
              heap_wall = true
            """))
        committed = []
        self.patch(table_mod, "git_commit",
                   lambda paths, message, root=None:
                   committed.append([str(p) for p in paths]) or True)
        pod.harvest_batch(pod.State(), self.tmp)
        self.assertFalse((self.tmp / "dev" / "pod" / "proposals" / "x.toml").exists())
        self.assertTrue((self.tmp / "dev" / "pod" / "proposals"
                         / "x.toml.admitted").is_file())
        self.assertTrue(any(p.endswith("x.toml.admitted") for p in committed[-1]))
        self.assertTrue(any(p.endswith("table.toml") for p in committed[-1]))

    def test_an_ADMITTED_proposal_left_in_the_tree_never_refuses_the_next_batch(self):
        """The program renamed it, so it is not the model's write and R15 is about the
        model's write."""
        self.patch(facts_mod, "_status_paths",
                   lambda root: ["dev/pod/proposals/old.toml.admitted",
                                 ".pod-state/state.json",
                                 "dev/pod/proposals/new.toml"])
        ok, bad = pod.maintainer_scope_ok(self.tmp, "dev/pod/proposals/new.toml")
        self.assertTrue(ok, bad)

    def test_a_queue_request_in_a_proposal_is_appended_and_is_not_a_write(self):
        self.patch(facts_mod, "_status_paths",
                   lambda root: ["dev/pod/proposals/x.toml"])
        (self.tmp / "dev" / "pod" / "proposals" / "x.toml").write_text(textwrap.dedent("""
            [[queue]]
            code = "LJ-1.386"
            reason = "preflight:P8 names a dead path"

            [[row]]
            id = "sys-q"
            scope = "system"
            priority = 60
            action = "park"
            added = 2026-08-17
            added_by = "maintainer"
            reason = "a row"
            expired = false

              [row.when]
              heap_wall = true
            """))
        st = pod.State()
        pod.harvest_batch(st, self.tmp)
        entries = pod.queue_entries(self.tmp / "dev" / "pod" / "queue.toml")
        self.assertEqual(entries[0]["code"], CODE)
        self.assertNotIn("brief", entries[0])

    def test_a_queue_request_is_appended_even_when_R15_refuses_the_batch(self):
        """MEASURED 2026-08-20 on POD-BATCH 194053.

        The proposal carried three `[[queue]]` requests and no rows. Harvest
        retired it `scope` because `scripts/pod/*.py` were already dirty, and
        `continue` skipped `queue_append`. A REQUEST is not a write. The
        owner-authorised A21 repairs never reached the queue.
        """
        self.patch(facts_mod, "_status_paths",
                   lambda root: ["dev/pod/proposals/x.toml", "scripts/pod/pod.py"])
        (self.tmp / "dev" / "pod" / "proposals" / "x.toml").write_text(textwrap.dedent("""
            [[queue]]
            code = "LJ-1.386"
            failed_check = "A21"
            reason = "brief names mathematician and Agda"
            """))
        st = pod.State()
        pod.harvest_batch(st, self.tmp)
        entries = pod.queue_entries(self.tmp / "dev" / "pod" / "queue.toml")
        self.assertEqual(len(entries), 1, "the REQUEST was swallowed by R15")
        self.assertEqual(entries[0]["code"], CODE)
        self.assertEqual(entries[0].get("failed_check"), "A21")
        self.assertFalse((self.tmp / "dev" / "pod" / "proposals" / "x.toml").exists())
        self.assertTrue((self.tmp / "dev" / "pod" / "proposals" / "x.toml.scope").is_file())

    def test_prune_logs_keeps_a_LIVE_task_log_whatever_its_age(self):
        """The file is the only transcript of a running worker."""
        d = self.tmp / ".pod-state" / "logs"
        live = d / f"{CODE}-old.log"
        live.write_text("x")
        os.utime(live, (0, 0))
        st = pod.State()
        st.tasks[CODE] = pod.Task(CODE, status=pod.RUNNING)
        self.assertEqual(pod.prune_logs(30, st, self.tmp), 0)
        self.assertTrue(live.exists())

    def test_prune_logs_removes_a_closed_task_log_past_the_retention(self):
        d = self.tmp / ".pod-state" / "logs"
        old = d / f"{CODE}-old.log"
        old.write_text("x")
        os.utime(old, (0, 0))
        st = pod.State()
        st.tasks[CODE] = pod.Task(CODE, status=pod.DONE)
        self.assertEqual(pod.prune_logs(30, st, self.tmp), 1)
        self.assertFalse(old.exists())


# ---------------------------------------------------------------- resident mathematician


class ResidentMathematician(LoopCase):
    """Owner 2026-08-20: the mathematician is one herdr agent, every task a prompt."""

    def test_a_reuse_prompt_is_the_brief_alone(self):
        """First start cats preamble then brief. Refill and later tasks cat the
        brief only, so AGENTS.md is not paid a second time."""
        import launcher as L
        pre = [Path("mathematician.md"), Path("AGENTS.md")]
        brief = Path("agents/tasks/POD-REFILL/POD-REFILL.md")
        self.assertEqual(L._prompt_files(pre, brief, False), pre + [brief])
        self.assertEqual(L._prompt_files(pre, brief, True), [brief])

    def test_ensure_is_idempotent_when_the_agent_is_there(self):
        seen = []
        self.patch(pod, "mathematician_alive", lambda root=None: True)
        self.patch(pod, "ensure_mathematician", REAL_ENSURE_MATHEMATICIAN)

        class _Mod:
            HARNESS = ""

            @staticmethod
            def launch(*a, **kw):
                seen.append(kw)
                return 0

        self.patch(facts_mod, "launcher", lambda: _Mod)
        st = pod.State()
        for _ in range(3):
            REAL_ENSURE_MATHEMATICIAN(st, self.tmp)
        self.assertEqual(seen, [])

    def test_ensure_starts_the_standing_session_when_the_agent_is_gone(self):
        seen = []
        self.patch(pod, "mathematician_alive", lambda root=None: False)
        self.patch(pod, "ensure_mathematician", REAL_ENSURE_MATHEMATICIAN)

        class _Mod:
            HARNESS = ""

            @staticmethod
            def herdr_name(t):
                return t.lower().replace(".", "-")

            @staticmethod
            def launch(task, brief, agda, sandbox, model, **kw):
                seen.append((task, kw.get("resident"), kw.get("agent_name")))
                return 0

        self.patch(facts_mod, "launcher", lambda: _Mod)
        st = pod.State()
        REAL_ENSURE_MATHEMATICIAN(st, self.tmp)
        self.assertEqual(seen, [("POD-MATH", True, "pod-math")])

    def test_a_mathematician_dispatch_reuses_the_resident_name_and_skips_a_worktree(self):
        seen = []

        class _Stub:
            HARNESS = ""

            @staticmethod
            def herdr_name(t):
                return t.lower().replace(".", "-")

            @staticmethod
            def launch(*a, **kw):
                seen.append((a, kw))
                return 4242

        self.patch(facts_mod, "launcher", lambda: _Stub)
        self.patch(pod, "launch", REAL_LAUNCH)
        t = pod.Task(CODE, agda=True, tier="wide")
        REAL_LAUNCH(t, f"agents/tasks/{DIR}/{CODE}.md", "mathematician", self.tmp)
        self.assertEqual(len(seen), 1)
        args, kw = seen[0]
        self.assertFalse(args[2], "the resident mathematician pane takes no Agda caliber")
        self.assertTrue(kw.get("resident"))
        self.assertEqual(kw.get("agent_name"), "pod-math")
        self.assertIsNone(kw.get("workdir"))

    def test_a_busy_resident_leaves_a_READY_mathematician_task_unlaunched(self):
        brief = self.tmp / "agents" / "tasks" / DIR / f"{CODE}.md"
        brief.write_text(BRIEF.replace("head_slot: coder",
                                       "head_slot: mathematician"),
                         encoding="utf-8")
        self.patch(pod, "mathematician_busy", lambda st, root=None: True)
        st = pod.State()
        t = pod.Task(CODE, brief=f"agents/tasks/{DIR}/{CODE}.md", status=pod.READY)
        st.tasks[CODE] = t
        self.patch(preflight_mod, "preflight", lambda *a, **k: [])
        self.patch(table_mod, "admit_rows", lambda *a, **k: True)
        pod._rule_f(st, self.tmp)
        self.assertEqual(t.status, pod.READY)
        self.assertEqual(self.calls["launch"], [])

    def test_a_busy_resident_holds_the_refill(self):
        self.patch(pod, "_rule_g", REAL_RULE_G)
        self.patch(pod, "mathematician_busy", lambda st, root=None: True)
        (self.tmp / "agents" / "tasks" / "POD-REFILL").mkdir(parents=True, exist_ok=True)
        (self.tmp / "agents" / "tasks" / "POD-REFILL" / "POD-REFILL.md").write_text(
            "# refill\n\n## HEAD\nhead_slot: mathematician\n")
        launched = []

        class FakeLauncher:
            HARNESS = ""

            @staticmethod
            def launch(*a, **kw):
                launched.append(a)
                return 0

        self.patch(facts_mod, "launcher", lambda: FakeLauncher)
        pod._rule_g(pod.State(), self.tmp)
        self.assertEqual(launched, [])


class RuleF(LoopCase):
    """The ONLY writer of a task row. Its order is fixed and each step guards the next."""

    def ready(self, attempt=0, head_slot=None):
        st = pod.State()
        t = pod.Task(CODE, brief=f"agents/tasks/{DIR}/{CODE}.md", status=pod.READY,
                     attempt=attempt, head_slot=head_slot)
        st.tasks[CODE] = t
        return st, t

    def test_a_clean_brief_admits_its_rows_and_dispatches(self):
        st, t = self.ready()
        pod._rule_f(st, self.tmp)
        self.assertEqual(t.status, pod.RUNNING)
        rows = table_mod.load_table(self.tmp / "dev" / "pod" / "table.toml")
        self.assertEqual({r["id"] for r in rows},
                         {"task-lj-1-386-go", "task-lj-1-386-no-go-stated",
                          "task-lj-1-386-no-go-attacked",
                          "task-lj-1-386-retry-on-termination"})

    def test_admission_runs_BEFORE_the_launch_so_route_can_see_the_rows(self):
        """Without that order every first instance no-matches."""
        order = []
        real = table_mod.admit_rows
        self.patch(table_mod, "admit_rows",
                   lambda c, b: order.append("admit") or real(c, b))
        self.patch(pod, "launch",
                   lambda t, b, r, root=None, st=None: order.append("launch") or 1)
        st, _ = self.ready()
        pod._rule_f(st, self.tmp)
        self.assertEqual(order, ["admit", "launch"])

    def test_a_malformed_brief_parks_before_any_table_write(self):
        """A branch block that does not parse can never reach `dev/pod/table.toml`."""
        brief = self.tmp / "agents" / "tasks" / DIR / f"{CODE}.md"
        brief.write_text(BRIEF.replace('id = "go"', "id = go"))
        st, t = self.ready()
        pod._rule_f(st, self.tmp)
        self.assertEqual(t.status, pod.PARKED)
        self.assertTrue(t.park_reason.startswith("preflight:"))
        self.assertEqual(table_mod.load_table(
            self.tmp / "dev" / "pod" / "table.toml"), [])

    def test_a_preflight_park_carries_the_WHOLE_refusal_list_in_detail(self):
        brief = self.tmp / "agents" / "tasks" / DIR / f"{CODE}.md"
        brief.write_text(BRIEF.replace('id = "go"', "id = go"))
        st, _ = self.ready()
        pod._rule_f(st, self.tmp)
        line = self.lines()[-1]
        # THE IDS ARE WRITTEN OUT. Deriving the expected reason from the line's own
        # `detail` re-ran the program's formula over the program's own output, so it held
        # for any id the pre-flight produced. This brief breaks the branch block's TOML,
        # which is P2, and the WHOLE list is what the maintainer batch reads.
        self.assertEqual(line["reason"], "preflight:P2")
        self.assertEqual(line["detail"][0], "P2 branch block does not parse")
        self.assertGreater(len(line["detail"]), 1)

    def test_an_admission_refusal_parks_and_writes_no_row(self):
        self.patch(table_mod, "admit_rows", lambda code, brief: False)
        st, t = self.ready()
        pod._rule_f(st, self.tmp)
        self.assertEqual(t.park_reason, "admission")
        self.assertEqual(table_mod.load_table(
            self.tmp / "dev" / "pod" / "table.toml"), [])

    def test_a_launch_refusal_parks_and_is_NEVER_silent(self):
        self.patch(pod, "launch", lambda t, b, r, root=None, st=None: None)
        st, t = self.ready()
        pod._rule_f(st, self.tmp)
        self.assertEqual(t.park_reason, "launch")

    def test_a_concurrency_refusal_leaves_the_task_READY_and_parks_nothing(self):
        self.patch(pod, "admits", lambda st, t, agda=None: False)
        st, t = self.ready()
        pod._rule_f(st, self.tmp)
        self.assertEqual(t.status, pod.READY)
        self.assertEqual(self.calls["launch"], [])

    def test_the_dispatch_point_of_fact_3_runs_and_writes_obl_before(self):
        st, t = self.ready()
        pod._rule_f(st, self.tmp)
        self.assertEqual(t.obl_before, 2)
        self.assertEqual(self.lines()[-1]["obl_before"], 2)

    def test_a_second_instance_goes_out_as_an_adversarial_review(self):
        """AD27: the critic is never the same model as the author."""
        st, t = self.ready(attempt=2)
        pod._rule_f(st, self.tmp)
        code, brief, role, _ = self.calls["launch"][0]
        self.assertEqual(role, "mathematician_adversarial")
        self.assertTrue(brief.endswith("review-LJ-1-386-1.md"))

    def test_the_review_brief_carries_no_branch_block_and_names_the_OUTPUT_apart(self):
        """The BRIEF is `review-<PRED>.md` and the OUTPUT is `review-of-<PRED>.md`, so a
        branch globbing `review-of-*.md` reads the reviewer's work and never the
        program's own input."""
        st, t = self.ready(attempt=2)
        rel = pod.review_brief(t, "mathematician_adversarial", self.tmp)
        text = (self.tmp / rel).read_text()
        self.assertNotIn("pod-branches", text)
        self.assertIn("review-of-LJ-1-386-1.md", text)
        self.assertIn("## SCOPE (write)", text)
        self.assertIn("## ARCHIVE", text)
        self.assertIn("## LITERATURE", text)
        # **THE REVIEW SCOPE CLAIMS NOTHING SHARED, and this assertion is inverted from
        # what it used to be.** The template named `dev/JOURNAL.md`, so every generated
        # review brief claimed one file and `territory_in_flight()` made ANY TWO
        # ESCALATIONS mutually exclusive. MEASURED 2026-08-19: LJ-1.394's escalation, the
        # first adversarial dispatch this programme ever made, parked `launch` because
        # LJ-1.391 was live and already held it. A22 runs four or five coder tasks at
        # once, so the collision is routine. A reviewer's deliverable is its own review
        # file; a journal entry is a consolidation step and never a per-review write.
        scope = text.split("## THE OBLIGATION", 1)[0]
        self.assertNotIn("dev/JOURNAL.md", scope,
                         "a shared write path serialises every escalation")

    def test_a_timeout_escalation_names_the_timeout_and_not_only_the_three_questions(self):
        """Owner's instruction 2026-08-22, MEASURED on [LJ-1.541]: a critic sent only
        the generic three questions has nothing to attack when the predecessor made no
        stated verdict at all, because the run_agda() call itself hit agda_deadline_s.
        sys-timeout-escalate (dev/pod/table.toml) routes that record here instead of a
        no-match park, and the brief must say so explicitly."""
        st, t = self.ready(attempt=2)
        t.record = {"facts": {"error_class": "timeout", "exit_code": None}}
        rel = pod.review_brief(t, "coder_adversarial", self.tmp)
        text = (self.tmp / rel).read_text()
        self.assertIn("WHY THIS ESCALATED: THE ACCEPTANCE CHECK ITSELF TIMED OUT", text)
        self.assertIn("agda_deadline_s", text)
        # THE NOTE SITS INSIDE THE OBLIGATION, before the generic questions, so a critic
        # reading top to bottom meets it before the part that assumes a stated verdict.
        self.assertLess(text.index("WHY THIS ESCALATED"),
                        text.index("THE THREE QUESTIONS"))

    def test_a_non_timeout_escalation_carries_no_timeout_note(self):
        """The note is additive and keyed on the fact, not on every escalation."""
        st, t = self.ready(attempt=2)
        t.record = {"facts": {"error_class": "lint", "exit_code": 1}}
        rel = pod.review_brief(t, "coder_adversarial", self.tmp)
        text = (self.tmp / rel).read_text()
        self.assertNotIn("WHY THIS ESCALATED", text)

    def test_a_review_brief_with_no_record_at_all_carries_no_timeout_note(self):
        """`t.record` is None before a task's first CHECKING; the note must not raise on
        that shape either."""
        st, t = self.ready(attempt=2)
        self.assertIsNone(t.record)
        rel = pod.review_brief(t, "coder_adversarial", self.tmp)
        text = (self.tmp / rel).read_text()
        self.assertNotIn("WHY THIS ESCALATED", text)

    def test_the_three_questions_name_the_section_that_carries_them(self):
        """**A CITATION THE CRITIC CAN CHECK.** MEASURED 2026-08-22 over the 124 files
        matching `agents/tasks/LJ-1-*/review-of-*.md`: 14 head a four-question section
        and 6 of those name SECTION 6.6 for it. Section 6.6 carries three questions and
        the four are DD25's, at `archive/dev/DD-archived.md:35`, so those six returns
        cite a live memo section for archived text. The brief now names the home of the
        list it gives, and names the slot file's four as a different set."""
        st, t = self.ready(attempt=2)
        text = (self.tmp / pod.review_brief(t, "coder_adversarial", self.tmp)).read_text()
        self.assertIn("dev/memos/LJ-4-pod-program-design.md:2853-2858", text)
        self.assertIn("FOUR", text, "the brief must name the slot file's other list")
        # The citation sits WITH the list, not in a footer a critic can stop before.
        self.assertLess(text.index("THE THREE QUESTIONS"),
                        text.index("LJ-4-pod-program-design.md:2853-2858"))
        self.assertLess(text.index("LJ-4-pod-program-design.md:2853-2858"),
                        text.index("1. Does the predecessor's verdict LINE"))

    def test_the_generated_headings_are_separated_by_a_blank_line(self):
        """`## ARCHIVE` used to land on the line after question 3 with no blank line
        between them, because the body ended in exactly one newline and the retrieval
        block was appended straight onto it. A heading glued to a list item is a
        markdown hazard for no gain."""
        st, t = self.ready(attempt=2)
        text = (self.tmp / pod.review_brief(t, "coder_adversarial", self.tmp)).read_text()
        for head in ("## ARCHIVE", "## LITERATURE"):
            i = text.index(head)
            self.assertTrue(text[:i].endswith("\n\n"),
                            f"{head} must be preceded by a blank line")

    def test_the_review_brief_names_the_accept_arm_and_warns_about_the_log(self):
        """**THE CRITIC RUNS IN THE TASK'S WORKTREE AND THE LOG IS TRACKED.**
        `_accept_one()` gives `run_acceptance()` the worktree as its root under
        isolation, so `runs/accept-<n>.out` is written into the checkout the critic
        gets. `dev/pod/transitions/<YYYY-MM>.jsonl` is tracked, so that checkout holds
        it at the worktree's BASE COMMIT. MEASURED 2026-08-22: the critics on LJ-1.532,
        LJ-1.533 and LJ-1.535 each reported their copy ending at LJ-1.399 and each
        rebuilt the six facts from the accept arm, which the brief never named."""
        st, t = self.ready(attempt=2)
        text = (self.tmp / pod.review_brief(t, "coder_adversarial", self.tmp)).read_text()
        self.assertIn(f"agents/tasks/{DIR}/runs/accept-*.out", text)
        self.assertIn(f"dev/pod/transitions/{time.strftime('%Y-%m')}.jsonl", text)
        self.assertIn(f'"task": "{CODE}"', text)
        self.assertIn("base commit", text, "the staleness must be stated, not implied")
        # The arm comes FIRST, because it is the one that is always in the checkout.
        self.assertLess(text.index("runs/accept-*.out"),
                        text.index("dev/pod/transitions/"))

    def test_the_logged_brief_is_ALWAYS_the_task_brief_and_never_the_review(self):
        """K6. Writing the review brief into `brief` would park the task with
        `preflight:P1` for ever, since rule (a2) would re-run P1 against a file that can
        never carry a branch block."""
        st, t = self.ready(attempt=2)
        pod._rule_f(st, self.tmp)
        line = self.lines()[-1]
        self.assertEqual(line["brief"], f"agents/tasks/{DIR}/{CODE}.md")
        self.assertTrue(line["dispatched_brief"].endswith("review-LJ-1-386-1.md"))

    def test_a_review_already_sent_for_this_attempt_is_not_sent_twice(self):
        """`reviewed()` reads the log and holds no state."""
        st, t = self.ready(attempt=2)
        pod._rule_f(st, self.tmp)
        t.status = pod.READY
        pod._rule_f(st, self.tmp)
        roles = [c[2] for c in self.calls["launch"]]
        self.assertEqual(roles, ["mathematician_adversarial", "coder"])

    def test_an_escalate_row_head_slot_wins_over_the_review_default(self):
        st, t = self.ready(attempt=2, head_slot="coder_adversarial")
        pod._rule_f(st, self.tmp)
        self.assertEqual(self.calls["launch"][0][2], "coder_adversarial")

    def test_the_head_slot_is_resolved_ONCE_and_then_cleared(self):
        """R11. A head that changed between two reads would make the record
        irreproducible."""
        st, t = self.ready(attempt=2, head_slot="coder_adversarial")
        pod._rule_f(st, self.tmp)
        self.assertIsNone(t.head_slot)

    def test_ready_tasks_go_out_in_attempt_then_code_order(self):
        st = pod.State()
        for code, attempt in (("LJ-1.700", 3), ("LJ-1.386", 1), ("LJ-1.100", 1)):
            st.tasks[code] = pod.Task(code, status=pod.READY, attempt=attempt,
                                      brief=f"agents/tasks/{DIR}/{CODE}.md")
        self.patch(table_mod, "admit_rows", lambda code, brief: True)
        pod._rule_f(st, self.tmp)
        self.assertEqual([c[0] for c in self.calls["launch"]],
                         ["LJ-1.100", "LJ-1.386", "LJ-1.700"])


# ---------------------------------------------------------------- emit() and the log


class Emit(LoopCase):
    """The tracked log is the truth and the state file is a cache of its fold."""

    def test_the_log_line_is_written_before_the_state_file(self):
        """A lost state file is recoverable from the log; a lost log line is recoverable
        from NOTHING."""
        order = []
        real_save = pod.save_state
        self.patch(pod, "save_state",
                   lambda st, path=None: order.append("state") or real_save(st, path))
        st = pod.State()
        st.tasks[CODE] = t = pod.Task(CODE, status=pod.READY)
        real_open = open

        def watch(path, *a, **kw):
            if str(path).endswith(".jsonl"):
                order.append("log")
            return real_open(path, *a, **kw)
        import builtins
        self.patch(builtins, "open", watch)
        pod.emit(st, t, pod.READY, pod.RUNNING, pid=1, root=self.tmp)
        self.assertEqual(order[:2], ["log", "state"])

    def test_the_log_rotates_monthly(self):
        """At about 124 KB per median day, monthly rotation holds any git blob under
        11 MB. A single file would not."""
        jan = datetime.datetime(2026, 1, 5, tzinfo=datetime.timezone.utc)
        feb = datetime.datetime(2026, 2, 5, tzinfo=datetime.timezone.utc)
        self.assertEqual(pod.log_path(jan, self.tmp).name, "2026-01.jsonl")
        self.assertEqual(pod.log_path(feb, self.tmp).name, "2026-02.jsonl")
        self.assertNotEqual(pod.log_path(jan, self.tmp), pod.log_path(feb, self.tmp))

    def test_the_fold_reads_every_monthly_file_in_seq_order(self):
        d = self.tmp / "dev" / "pod" / "transitions"
        (d / "2026-01.jsonl").write_text(json.dumps(
            {"ts": "2026-01-05T00:00:00Z", "seq": 1, "task": CODE,
             "from": None, "to": "READY"}) + "\n")
        (d / "2026-02.jsonl").write_text(json.dumps(
            {"ts": "2026-02-05T00:00:00Z", "seq": 2, "task": CODE,
             "from": "READY", "to": "RUNNING", "pid": 7}) + "\n")
        st = pod.replay_log(pod.State(), self.tmp)
        self.assertEqual(st.seq, 2)
        self.assertEqual(st.tasks[CODE].status, pod.RUNNING)
        self.assertEqual(st.tasks[CODE].pid, 7)

    def test_an_illegal_transition_is_refused_rather_than_written(self):
        """Six states, the legal set, nothing else is legal."""
        st = pod.State()
        st.tasks[CODE] = t = pod.Task(CODE, status=pod.DONE)
        with self.assertRaises(pod.PodError):
            pod.emit(st, t, pod.DONE, pod.RUNNING, root=self.tmp)

    def test_parked_to_checking_is_legal(self):
        """Transition 14. AD16 still forbids PARKED → DONE."""
        st = pod.State()
        st.tasks[CODE] = t = pod.Task(CODE, status=pod.PARKED)
        pod.emit(st, t, pod.PARKED, pod.CHECKING, root=self.tmp)
        self.assertEqual(t.status, pod.CHECKING)
        t.status = pod.PARKED
        with self.assertRaises(pod.PodError):
            pod.emit(st, t, pod.PARKED, pod.DONE, root=self.tmp)

    def test_every_park_line_carries_a_row_key_and_a_reason(self):
        """5.5: on a PARK the program writes exactly ONE line, with `"row": null`."""
        st = pod.State()
        st.tasks[CODE] = t = pod.Task(CODE, status=pod.CHECKING)
        pod.emit(st, t, pod.CHECKING, pod.PARKED, rec=record(),
                 reason="no-match", root=self.tmp)
        line = self.lines()[-1]
        self.assertIn("row", line)
        self.assertIsNone(line["row"])
        self.assertEqual(line["reason"], "no-match")

    def test_the_program_writes_NO_park_reason_outside_the_nine(self):
        """IT READS EVERY `reason=` THE PROGRAM PASSES, and not the source text.

        The old test searched `pod.py` for each member of `PARK_REASONS`, which is DEFINED
        in `pod.py`: the tuple literal answered every search, so no deletion and no new
        reason could fail it. This parses the file and collects the `reason=` argument of
        every call, so a TENTH reason is caught the moment somebody writes one. Section
        5.5's list of nine is closed, and `harvest_batch()` depends on that: a reason rule
        (a2) cannot branch on is a park nothing ever un-parks.
        """
        import ast
        src = Path(ROOT / "scripts" / "pod" / "pod.py").read_text(encoding="utf-8")
        written = []
        for node in ast.walk(ast.parse(src)):
            if not isinstance(node, ast.Call):
                continue
            for kw in node.keywords:
                if kw.arg != "reason":
                    continue
                if isinstance(kw.value, ast.Constant):
                    written.append(kw.value.value)          # reason="no-match"
                elif isinstance(kw.value, ast.BinOp) and \
                        isinstance(kw.value.left, ast.Constant):
                    written.append(kw.value.left.value)     # reason="attempt_max:" + id
        self.assertGreaterEqual(len(written), 8)
        for reason in written:
            self.assertIn(reason, pod.PARK_REASONS, reason)
        # **THE REVERSE HALF: NO DECLARED REASON IS DEAD.** This line asserted a COUNT
        # until 2026-08-19, and a count is a snapshot of a list the program is designed to
        # grow: `salvage:` made it ten and `quota:` made it eleven, and each addition
        # turned this suite red for a change that was correct. What the count was really
        # guarding is that the tuple and the code agree, and containment says that in both
        # directions without pinning a number. Three reasons reach `emit()` through a
        # variable rather than a literal keyword, so the text is what this half reads.
        body = src.split("PARK_REASONS = (", 1)[1].split(")", 1)[1]
        for reason in pod.PARK_REASONS:
            self.assertIn(f'"{reason}"', body,
                          f"{reason} is declared and no site in pod.py writes it")

    def test_the_line_stamps_the_heads_digest_so_ad26_can_read_what_ran(self):
        st = pod.State()
        st.tasks[CODE] = t = pod.Task(CODE, status=pod.READY)
        pod.emit(st, t, pod.READY, pod.RUNNING, pid=1, root=self.tmp)
        self.assertEqual(self.lines()[-1]["heads_sha256"],
                         heads_mod.sha256(self.tmp / "dev" / "pod" / "heads.toml")[:8])

    def test_the_corpus_append_is_idempotent_after_a_crash(self):
        """`seq` makes the id unique, so a re-run of the same line adds nothing."""
        st = pod.State()
        st.tasks[CODE] = t = pod.Task(CODE, status=pod.CHECKING)
        line = pod.emit(st, t, pod.CHECKING, pod.PARKED, rec=record(),
                        reason="no-match", root=self.tmp)
        self.assertFalse(pod.corpus_append(
            line, self.tmp / "dev" / "pod" / "replay-corpus.jsonl"))
        text = (self.tmp / "dev" / "pod" / "replay-corpus.jsonl").read_text()
        self.assertEqual(len(text.strip().split("\n")), 1)

    def test_a_stale_emit_does_not_clobber_a_resume_ready_or_reuse_its_seq(self):
        """MEASURED 2026-08-20 on LJ-1.386 and LJ-1.390.

        `resume --retry` wrote PARKED→READY at seq 714/715. The live tick still held
        seq 713 and the PARKED copies, then `emit()` assigned those same two seqs to
        LJ-1.433/434 READY→RUNNING and `save_state()` wrote the PARKED copies back.
        `replay_log()` only folds `seq > st.seq`, so the READY lines were gone once
        the cache sat at seq 731.
        """
        parked = pod.State(seq=713)
        parked.tasks[CODE] = pod.Task(CODE, status=pod.PARKED,
                                      park_reason="no-change")
        parked.tasks["LJ-1.433"] = pod.Task("LJ-1.433", status=pod.READY)
        pod.save_state(parked)

        resume = pod.load_state()
        pod.replay_log(resume, self.tmp)
        pod.emit(resume, resume.tasks[CODE], pod.PARKED, pod.READY,
                 why="resume --retry", root=self.tmp)

        stale = parked
        self.assertEqual(stale.seq, 713)
        self.assertEqual(stale.tasks[CODE].status, pod.PARKED)
        pod.emit(stale, stale.tasks["LJ-1.433"], pod.READY, pod.RUNNING,
                 pid=1, root=self.tmp)

        self.assertEqual(stale.tasks[CODE].status, pod.READY,
                         "the tick's in-memory copy must absorb the resume READY")
        self.assertEqual(stale.tasks["LJ-1.433"].status, pod.RUNNING)
        durable = pod.replay_log(pod.load_state(), self.tmp)
        self.assertEqual(durable.tasks[CODE].status, pod.READY)
        self.assertEqual(durable.tasks["LJ-1.433"].status, pod.RUNNING)
        seqs = [line["seq"] for line in pod.log_lines(self.tmp)]
        self.assertEqual(seqs, sorted(set(seqs)), "seq numbers are unique")
        self.assertEqual(durable.seq, 715)


# ---------------------------------------------------------------- crash safety


CRASH_CHILD = """\
import importlib.util, os, sys
from pathlib import Path
ROOT = Path(sys.argv[1])
TMP = Path(sys.argv[2])
sys.path.insert(0, str(ROOT / "scripts"))
sys.path.insert(0, str(ROOT / "scripts" / "pod"))


def load(name, rel):
    spec = importlib.util.spec_from_file_location(name, ROOT / rel)
    mod = importlib.util.module_from_spec(spec)
    sys.modules[name] = mod
    spec.loader.exec_module(mod)
    return mod


pod = load("pod", "scripts/pod/pod.py")
pod.ROOT = TMP
pod.POD_STATE = TMP / ".pod-state"
pod.STATE_FILE = TMP / ".pod-state" / "state.json"
pod.LOG_DIR = TMP / ".pod-state" / "logs"
pod.LOCKFILE = TMP / ".pod-state" / "pod.lock"
pod.CORPUS = TMP / "dev" / "pod" / "replay-corpus.jsonl"

# THE KILL SITS BETWEEN THE TWO FSYNCS. The log line is fsynced by `emit()` at step 3;
# `save_state()` performs the second fsync at step 4 and never runs.
pod.save_state = lambda st, path=None: os._exit(9)

st = pod.State()
st.tasks["LJ-1.386"] = pod.Task("LJ-1.386", status="READY", brief="b")
pod.emit(st, st.tasks["LJ-1.386"], "READY", "RUNNING", pid=4242, root=TMP)
os._exit(0)
"""


class CrashSafety(LoopCase):
    """Crash window one: the log written, the state not. It is the designed, safe window."""

    def test_a_kill_between_the_two_fsyncs_loses_the_state_and_not_the_log(self):
        child = self.tmp / "crash_child.py"
        child.write_text(CRASH_CHILD)
        done = subprocess.run([sys.executable, str(child), str(ROOT), str(self.tmp)],
                              capture_output=True, text=True, timeout=120)
        self.assertEqual(done.returncode, 9, done.stderr)
        # The log line is durable.
        lines = pod.log_lines(self.tmp)
        self.assertEqual(len(lines), 1)
        self.assertEqual(lines[0]["to"], "RUNNING")
        self.assertEqual(lines[0]["pid"], 4242)
        # The state file never landed.
        self.assertFalse((self.tmp / ".pod-state" / "state.json").exists())
        # The next start applies every line with `seq` above the state's.
        st = pod.replay_log(pod.load_state(), self.tmp)
        self.assertEqual(st.seq, 1)
        self.assertEqual(st.tasks[CODE].status, pod.RUNNING)
        self.assertEqual(st.tasks[CODE].pid, 4242)

    def test_the_fold_is_idempotent_so_a_second_start_changes_nothing(self):
        child = self.tmp / "crash_child.py"
        child.write_text(CRASH_CHILD)
        subprocess.run([sys.executable, str(child), str(ROOT), str(self.tmp)],
                       capture_output=True, text=True, timeout=120)
        st = pod.replay_log(pod.load_state(), self.tmp)
        pod.save_state(st, self.tmp / ".pod-state" / "state.json")
        again = pod.replay_log(pod.load_state(), self.tmp)
        self.assertEqual(again.seq, st.seq)
        self.assertEqual(again.tasks[CODE].status, pod.RUNNING)

    def test_save_state_calls_fsync_on_the_file_AND_on_the_directory(self):
        """Gap m6. The rename is atomic against a process crash and NOT durable against a
        machine crash; only the two fsyncs make the bytes survive a power cut."""
        seen = []
        real = os.fsync
        self.patch(os, "fsync", lambda fd: seen.append(fd) or real(fd))
        pod.save_state(pod.State(), self.tmp / ".pod-state" / "state.json")
        self.assertEqual(len(seen), 2)

    def test_a_torn_tail_line_is_skipped_and_the_lines_before_it_survive(self):
        d = self.tmp / "dev" / "pod" / "transitions"
        (d / "2026-08.jsonl").write_text(
            json.dumps({"ts": "2026-08-17T00:00:00Z", "seq": 1, "task": CODE,
                        "from": None, "to": "READY"}) + "\n{\"seq\": 2, \"ta")
        st = pod.replay_log(pod.State(), self.tmp)
        self.assertEqual(st.seq, 1)
        self.assertEqual(st.tasks[CODE].status, pod.READY)


# ---------------------------------------------------------------- admits(), AD17


class Admits(LoopCase):
    """Section 5.6. It REFUSES; it never prints."""

    def setUp(self):
        super().setUp()
        self.patch(pod, "admits", REAL_ADMITS)          # the real one, from import
        self.patch(pod, "watchdog_alive", lambda: True)
        self.patch(pod, "agda_pileup", lambda: (0, {}, None))
        self.patch(pod, "free_memory_pct", lambda: 90.0)
        # THE LOAD AVERAGE IS THE MACHINE'S, and `os.getloadavg()` reads whatever else is
        # running. Two of the tests below admit an EXCLUSIVE task, which refuses above
        # `exclusive_max_load1`, so an unpatched `load1()` made them pass on a quiet
        # machine and fail on a busy one. MEASURED: the suite failed under a parallel
        # Agda run and passed alone, with no edit between.
        self.patch(pod, "load1", lambda: 0.5)
        self.st = pod.State()
        self.t = pod.Task(CODE, status=pod.READY, agda=True)

    def test_a_clean_machine_admits(self):
        self.assertTrue(pod.admits(self.st, self.t))

    def test_a_blind_census_REFUSES(self):
        """When `ps` fails the census is BLIND, and admitting on a blind sensor is the
        wrong direction (D12)."""
        self.patch(pod, "agda_pileup", lambda: (0, {}, "ps returned nothing; BLIND"))
        self.assertFalse(pod.admits(self.st, self.t))

    def test_a_pile_up_of_two_under_ONE_parent_REFUSES(self):
        """C-12 says ONE agda process per agent. On 2026-08-12 one agent held six."""
        self.patch(pod, "agda_pileup", lambda: (2, {900: 2}, None))
        self.assertFalse(pod.admits(self.st, self.t))

    def test_the_pile_up_limb_refuses_a_NON_AGDA_task_too_and_that_is_deliberate(self):
        """**THIS IS WHAT MADE ONE CENSUS DEFECT A TOTAL STALL ON 2026-08-22.** The limb
        sits above the `if not t.agda` early-out on purpose, because C-12's hazard is the
        MACHINE and not the task. It is pinned here so the repair is understood as being
        in the census and never in this ordering: dropping the limb below the early-out
        would let a non-Agda task start next to six unguarded writers."""
        self.patch(pod, "agda_pileup", lambda: (2, {900: 2}, None))
        self.t.agda = False
        self.assertFalse(pod.admits(self.st, self.t))

    def test_TWO_ORPHANS_NO_LONGER_LOOK_LIKE_ONE_AGENT(self):
        """**THE 2026-08-22 STALL, pinned end to end at the boundary that broke.**

        The two leftover Agda processes of LJ-1.524 sat at PPID 1. The old
        `agda_pileup()` returned `{1: 2}` from that, this function read it as C-12's
        pile-up, and the loop admitted NOTHING for 2 h 07 min: seq 2448 at
        `2026-08-22T07:04:19Z` to seq 2449 at `2026-08-22T09:11:26Z` with no line
        between. `agda_pileup()` now leaves the orphanage out of `per_parent` and keeps
        both processes in `total`, so the census still charges A14's ceiling for them
        while it stops claiming one agent holds them.

        OWNER'S RULING 2026-08-23 tightened the live ceiling to 1, which the total of 2
        orphans alone would now trip regardless of `per_parent` -- that is
        `test_but_FOUR_orphans_still_fill_the_WIDE_tier_so_the_cap_is_not_lost`'s own
        property, tested separately. This test's property is narrower and still needs
        isolating: an EMPTY `per_parent` must not itself refuse, so the ceiling is
        patched here to a value the total of 2 sits under, decoupled from whatever the
        live policy's own number is on any given day."""
        self.patch(pod, "agda_pileup", lambda: (2, {}, None))
        self.patch(pod, "agda_slots", lambda tier=pod.WIDE: 4)
        self.assertTrue(pod.admits(self.st, self.t))
        self.t.agda = False
        self.assertTrue(pod.admits(self.st, self.t))

    def test_but_FOUR_orphans_still_fill_the_WIDE_tier_so_the_cap_is_not_lost(self):
        """They are real processes burning real heap. The reap removes them; the ceiling
        must not pretend they are absent until it does."""
        self.patch(pod, "agda_pileup", lambda: (4, {}, None))
        self.assertFalse(pod.admits(self.st, self.t))

    def test_the_total_at_the_WIDE_ceiling_REFUSES_and_one_below_it_ADMITS(self):
        """THE NUMBER IS WRITTEN OUT, and it is the owner's 2026-08-23 one (was A14's
        four). Reading the ceiling back out of `agda_slots()` made the pair
        `total >= slots` true for any value the function returned, including a broken
        zero, so the test held whatever the tier said."""
        self.patch(pod, "agda_pileup", lambda: (1, {900: 1}, None))
        self.assertFalse(pod.admits(self.st, self.t))
        self.patch(pod, "agda_pileup", lambda: (0, {}, None))
        self.assertTrue(pod.admits(self.st, self.t))

    def test_a_non_agda_task_is_admitted_at_the_ceiling(self):
        self.patch(pod, "agda_pileup", lambda: (4, {900: 1, 901: 1, 902: 1, 903: 1},
                                                None))
        self.t.agda = False
        self.assertTrue(pod.admits(self.st, self.t))

    def test_a13_refuses_every_agda_task_while_the_watchdog_is_down(self):
        """The watchdog is the backstop born 2026-08-02 after four unguarded parallel
        writers crashed the 64 GB box."""
        self.patch(pod, "watchdog_alive", lambda: False)
        self.assertFalse(pod.admits(self.st, self.t))
        self.t.agda = False
        self.assertTrue(pod.admits(self.st, self.t))

    def test_a_live_exclusive_task_refuses_every_other_task(self):
        self.st.tasks["X"] = pod.Task("X", status=pod.RUNNING, exclusive=True)
        self.assertFalse(pod.admits(self.st, self.t))

    def test_an_exclusive_task_waits_for_an_empty_machine(self):
        self.t.exclusive = True
        self.st.tasks["X"] = pod.Task("X", status=pod.RUNNING)
        self.assertFalse(pod.admits(self.st, self.t))
        self.st.tasks.clear()
        self.assertTrue(pod.admits(self.st, self.t))

    def test_an_exclusive_task_waits_while_the_load_average_is_high(self):
        """Exclusive is not only about slots: every run record writes a `# load before`
        line, and a contended machine gives a wrong measurement, not a slow one."""
        self.t.exclusive = True
        self.patch(pod, "load1", lambda: 99.0)
        self.assertFalse(pod.admits(self.st, self.t))

    def test_a14_fills_slots_three_and_four_only_above_the_free_memory_floor(self):
        """OWNER'S RULING 2026-08-23: slots = 1 now, so `floor = min(1, 2)` already
        equals `slots` itself -- there is no third or fourth slot left to hold back,
        and low free memory can no longer cut the count below 1."""
        self.assertEqual(pod.agda_slots(), 1)
        self.patch(pod, "free_memory_pct", lambda: 5.0)
        self.assertEqual(pod.agda_slots(), 1)

    def test_an_unreadable_memory_sensor_drops_to_the_two_slot_floor(self):
        """NONE IS NOT ZERO AND IT IS NOT A HUNDRED. An unreadable sensor must refuse.

        OWNER'S RULING 2026-08-23: the floor an unreadable sensor drops to is now 1,
        the same as `slots` itself, since `min(1, 2) == 1`."""
        self.patch(pod, "free_memory_pct", lambda: None)
        self.assertEqual(pod.agda_slots(), 1)

    def test_rule_c_passes_agda_True_whatever_the_brief_says(self):
        """The acceptance runner starts Agda for every case except case 4, and the
        program cannot know which case applies until fact 4 is measured.

        IT DRIVES RULE (c) AND READS THE ARGUMENT, rather than grepping the source for
        the call. A source grep passes while the call sits in a branch nothing reaches.
        """
        seen = []
        self.patch(pod, "admits",
                   lambda st, t, agda=None: seen.append(agda) or True)
        self.patch(accept_mod, "run_acceptance", lambda t, root=None: None)
        st = pod.State()
        st.tasks[CODE] = pod.Task(CODE, status=pod.RETURNED, agda=False,
                                  brief=f"agents/tasks/{DIR}/{CODE}.md")
        pod._rule_c(st, self.tmp)
        self.assertEqual(seen, [True])         # the task says False and rule (c) says True


# ------------------------------------------------- gap M2, the orphaned Agda reaper


class ReapOrphanAgda(LoopCase):
    """**THE 2026-08-22 INCIDENT, and it has two independent halves.**

    MEASURED. Two Agda processes belonging to LJ-1.524 were found alive at PPID 1 at
    ~100 percent CPU, 153 and 145 minutes elapsed: `agents/tasks/LJ-1-524/Probe524.agda`
    and `agents/tasks/LJ-1-524/runs/BisI.agda`. `agda_deadline_s` is 1800 s
    (`dev/pod/heads.toml:264`), so both were over the cap by 5.1 and 4.8 times.

    HALF ONE, THE STALL. `agda_pileup()` bucketed both under PID 1, `admits()` read
    `{1: 2}` as C-12's pile-up and returned False for EVERY task, and rule (c)
    (`scripts/pod/pod.py:4267-4269`) `continue`d in silence. The transition log carries
    NOTHING between seq 2448 at `2026-08-22T07:04:19Z` and seq 2449 at
    `2026-08-22T09:11:26Z`, 2 h 07 min, with four tasks stuck in RETURNED across the
    whole gap and all four closed within 86 seconds of it ending.

    HALF TWO, THE MISSING KILL. LJ-1.524 left RUNNING through `_rule_b()`'s `pid dead`
    limb (`:4122`), which kills nothing, 49 minutes into a `worker_deadline_s` of
    43200 s. Nothing in this program had ever been able to bound a worker's OWN Agda:
    `run_agda()`'s `timeout=` covers only the acceptance pipeline's runs.

    NO TEST HERE SIGNALS A REAL PROCESS. `os.kill` is a recorder and the census is a
    fixture, so the suite can pin the kill order without owning a process to kill.
    """

    #: The incident's own two orphans, plus one healthy Agda a live worker owns.
    ORPHANS = [(501, 9180), (502, 8700)]

    def setUp(self):
        super().setUp()
        self.killed = []
        self.censuses = []
        self.patch(pod, "agda_orphans", self.census)
        self.patch(pod.os, "kill", lambda pid, sig: self.killed.append((pid, sig)))
        self.patch(pod.time, "sleep", lambda s: None)
        self.answers = [(list(self.ORPHANS), None), (list(self.ORPHANS), None)]
        pod._REAP["reported"] = None
        self.addCleanup(pod._REAP.__setitem__, "reported", None)

    def census(self, bar):
        self.censuses.append(bar)
        return self.answers.pop(0) if self.answers else ([], None)

    def test_the_bar_is_agda_deadline_s_and_no_literal_of_its_own(self):
        """ONE HOME FOR THE NUMBER. A second literal here would drift from
        `dev/pod/heads.toml` the first time the owner moved it."""
        pod.reap_orphan_agda(pod.State(), self.tmp)
        self.assertEqual(self.censuses[0], heads_mod.limits()["agda_deadline_s"])
        self.assertEqual(self.censuses[0], 1800)

    def test_each_orphan_takes_a_SIGTERM_and_then_a_SIGKILL(self):
        killed = pod.reap_orphan_agda(pod.State(), self.tmp)
        self.assertEqual(killed, [501, 502])
        self.assertEqual(self.killed,
                         [(501, signal.SIGTERM), (502, signal.SIGTERM),
                          (501, signal.SIGKILL), (502, signal.SIGKILL)])

    def test_the_SIGKILL_is_aimed_through_a_SECOND_census_which_is_the_pid_recycling_guard(self):
        """`_rule_b()`'s docstring at `:4063-4068` records what this guards: a pid the
        operating system has RECYCLED belongs to somebody else. 501 dies on the TERM, so
        the second census no longer holds it and no KILL may be aimed at that number."""
        self.answers = [(list(self.ORPHANS), None), ([(502, 8743)], None)]
        pod.reap_orphan_agda(pod.State(), self.tmp)
        self.assertEqual([p for p, s in self.killed if s == signal.SIGKILL], [502])

    def test_a_BLIND_second_census_sends_NO_sigkill_at_all(self):
        """BLIND means kill nothing, which is the opposite direction from `admits()`,
        where BLIND means refuse. One is about starting work and the other about ending
        it."""
        self.answers = [(list(self.ORPHANS), None), ([], "ps returned nothing; BLIND")]
        pod.reap_orphan_agda(pod.State(), self.tmp)
        self.assertEqual([p for p, s in self.killed if s == signal.SIGKILL], [])

    def test_a_quiet_tick_kills_nothing_and_writes_NO_line(self):
        """A13's watchdog learned this in numbers: at `tick_seconds = 30` a per-tick line
        is 2,880 lines a day into a TRACKED file."""
        self.answers = [([], None)]
        st = pod.State()
        self.assertEqual(pod.reap_orphan_agda(st, self.tmp), [])
        self.assertEqual(self.killed, [])
        self.assertEqual(self.lines(), [])

    def test_a_reap_writes_ONE_event_line_naming_every_pid_and_the_bar(self):
        """A program that kills a process on this machine without saying so is worse than
        one that leaves it running."""
        st = pod.State()
        pod.reap_orphan_agda(st, self.tmp)
        lines = self.lines()
        self.assertEqual(len(lines), 1)
        self.assertEqual(lines[0]["event"], "reap")
        self.assertEqual(lines[0]["result"], "killed")
        self.assertEqual(lines[0]["pids"], [501, 502])
        self.assertEqual(lines[0]["bar_s"], 1800)
        self.assertEqual(lines[0]["task"], "")   # it moves no task
        self.assertIn("9180 s elapsed", " ".join(lines[0]["detail"]))

    def test_a_BLIND_census_says_so_ONCE_and_not_once_a_tick(self):
        self.answers = [([], "ps returned nothing; BLIND")] * 4
        st = pod.State()
        for _ in range(3):
            self.assertEqual(pod.reap_orphan_agda(st, self.tmp), [])
        self.assertEqual(len(self.lines()), 1)
        self.assertEqual(self.lines()[0]["result"], "BLIND")
        self.assertEqual(self.killed, [])

    def test_a_BLIND_census_speaks_again_when_the_REASON_changes(self):
        st = pod.State()
        self.answers = [([], "ps returned nothing; BLIND")]
        pod.reap_orphan_agda(st, self.tmp)
        self.answers = [([], "could not run ps (boom); BLIND")]
        pod.reap_orphan_agda(st, self.tmp)
        self.assertEqual(len(self.lines()), 2)

    def test_a_pid_that_is_already_gone_at_the_SIGTERM_is_dropped(self):
        def boom(pid, sig):
            if pid == 501:
                raise ProcessLookupError(3, "No such process")
            self.killed.append((pid, sig))
        self.patch(pod.os, "kill", boom)
        self.assertEqual(pod.reap_orphan_agda(pod.State(), self.tmp), [502])

    def test_the_reap_runs_on_the_tick_BEFORE_any_rule_consults_admits(self):
        """The capacity it frees must be visible on THIS tick and not the next one.
        Rules (c), (f) and (g) are the consumers of `admits()`.

        IT MATCHES THE CALL AND NOT THE NAME, because `pod_tick()`'s docstring names
        `_rule_f()` two paragraphs above the call and a bare-name index read the PROSE."""
        src = inspect.getsource(pod.pod_tick)
        first = src.index("reap_orphan_agda(st, root)")
        for later in ("_rule_c(st, root)", "_rule_f(st, root)", "_rule_g(st, root)"):
            self.assertLess(first, src.index(later), later)

    def test_it_NEVER_calls_kill_process_group(self):
        """An orphan's process group is whatever session its dead parent left behind, and
        this program cannot know what else is in it. The launcher's founding incident
        (`scripts/pod/launcher.py:7-9`) is a process group killed out from under two live
        agents on 2026-08-05."""
        self.patch(pod, "kill_process_group",
                   lambda pid: self.fail("it killed a group it does not own"))
        pod.reap_orphan_agda(pod.State(), self.tmp)

    def test_an_unreadable_limits_block_kills_nothing(self):
        def boom():
            raise pod.PodError("heads.toml does not parse")
        self.patch(pod, "_limits", boom)
        self.assertEqual(pod.reap_orphan_agda(pod.State(), self.tmp), [])
        self.assertEqual(self.killed, [])
        self.assertEqual(self.lines()[0]["result"], "BLIND")


class AgdaOrphansWrapper(LoopCase):
    """`agda_orphans()` in `pod.py` owns the REFUSAL; the launcher owns the census.

    THE `getattr` IS THE HOT RESTART AND NOT DEFENSIVENESS. `cmd_run()` reloads this
    file and the launcher independently, and the loop's own comment at
    `scripts/pod/pod.py:5204-5207` records a measured split image where one side of a
    call had widened and the other had not.
    """

    def with_launcher(self, mod):
        self.patch(facts_mod, "launcher", lambda: mod)

    def test_no_launcher_is_BLIND(self):
        self.with_launcher(None)
        found, warn = pod.agda_orphans(1800)
        self.assertEqual(found, [])
        self.assertIn("BLIND", warn)

    def test_a_launcher_with_no_agda_orphans_is_BLIND_and_never_a_traceback(self):
        self.with_launcher(types.SimpleNamespace())
        found, warn = pod.agda_orphans(1800)
        self.assertEqual(found, [])
        self.assertIn("BLIND", warn)

    def test_a_census_that_RAISES_is_BLIND(self):
        def boom(bar):
            raise RuntimeError("ps exploded")
        self.with_launcher(types.SimpleNamespace(agda_orphans=boom))
        found, warn = pod.agda_orphans(1800)
        self.assertEqual(found, [])
        self.assertIn("RuntimeError", warn)

    def test_an_unreadable_shape_is_BLIND_and_never_half_read(self):
        for bad in (["not a pair"], [("a", "b")], [(1, 60)], [(None, 1)]):
            self.with_launcher(
                types.SimpleNamespace(agda_orphans=lambda bar, v=bad: (v, None)))
            found, warn = pod.agda_orphans(1800)
            self.assertEqual(found, [], bad)
            self.assertIn("BLIND", warn or "", bad)

    def test_a_good_census_passes_through_as_whole_numbers(self):
        self.with_launcher(types.SimpleNamespace(
            agda_orphans=lambda bar: ([("501", "9180")], None)))
        self.assertEqual(pod.agda_orphans(1800), ([(501, 9180)], None))


# ---------------------------------------------------------------- A13, the watchdog


WATCHDOG_SH = """\
#!/bin/zsh
LIMIT_KB=$((6*1024*1024))    # 6 GB per-process backstop, owner's ruling 2026-08-23
FREE_MIN=8                   # system free-percentage floor
while true; do sleep 20; done
"""


class Watchdog(LoopCase):
    """A13. `dev/LESSONS.md` C-12 says restart the watchdog at every session, and THE POD
    HAS NO SESSION, so nothing started it. MEASURED 2026-08-17: it was not running.

    NO TEST HERE STARTS A PROCESS. `subprocess.Popen` is a recorder, so the argv, the
    session flag and the working directory are read without spawning a shell loop that
    would outlive the suite.
    """

    def setUp(self):
        super().setUp()
        self.patch(pod, "watchdog_tick", REAL_WATCHDOG_TICK)   # the real one, from import
        self.spawned = []
        self.patch(subprocess, "Popen", self.fake_popen)
        (self.tmp / "scripts" / "ops").mkdir(parents=True, exist_ok=True)
        (self.tmp / "scripts" / "ops" / "agda-watchdog.sh").write_text(WATCHDOG_SH)

    def fake_popen(self, argv, **kw):
        self.spawned.append((list(argv), kw))

        class P:
            pid = 31337
        return P()

    def down(self):
        self.patch(pod, "watchdog_alive", lambda: False)

    def up(self):
        self.patch(pod, "watchdog_alive", lambda: True)

    def watchdog_lines(self):
        return [x for x in self.lines() if x.get("event") == "watchdog"]

    def test_a_live_watchdog_starts_nothing_and_writes_no_line(self):
        self.up()
        st = pod.State()
        self.assertTrue(pod.watchdog_tick(st, self.tmp))
        self.assertEqual(self.spawned, [])
        self.assertEqual(self.watchdog_lines(), [])

    def test_a_dead_watchdog_is_restarted_with_ONE_line(self):
        """A13's own words: every tick confirms the process is alive and restarts it with
        one log line if it is not."""
        self.down()
        st = pod.State()
        self.assertTrue(pod.watchdog_tick(st, self.tmp))
        self.assertEqual(len(self.spawned), 1)
        lines = self.watchdog_lines()
        self.assertEqual(len(lines), 1)
        self.assertEqual(lines[0]["result"], "started")
        self.assertEqual(lines[0]["pid"], 31337)
        self.assertEqual(lines[0]["task"], "")          # it is not a task transition

    def test_the_restart_passes_the_absolute_script_path_in_its_OWN_session(self):
        """`agda-watchdog.sh:5` reads `dirname "$0"` and walks up to `.git`, so the path
        is the one argument that matters. The new session is the founding incident of the
        launcher: a watcher shell that dies takes its children with it."""
        self.down()
        pod.watchdog_tick(pod.State(), self.tmp)
        argv, kw = self.spawned[0]
        self.assertIn(str(self.tmp / "scripts" / "ops" / "agda-watchdog.sh"), argv)
        self.assertTrue(Path(argv[-1]).is_absolute())
        self.assertTrue(kw["start_new_session"])
        self.assertEqual(kw["cwd"], str(self.tmp))

    def test_a_restart_that_KEEPS_failing_writes_ONE_line_and_not_one_a_tick(self):
        """At `tick_seconds = 30` a line a tick is 2,880 lines a day into a TRACKED file
        that the digest and the maintainer batch both read."""
        self.down()
        (self.tmp / "scripts" / "ops" / "agda-watchdog.sh").unlink()
        st = pod.State()
        for _ in range(5):
            self.assertFalse(pod.watchdog_tick(st, self.tmp))
        lines = self.watchdog_lines()
        self.assertEqual(len(lines), 1)
        self.assertEqual(lines[0]["result"], "REFUSED")
        self.assertIn("is not a file", lines[0]["why"])

    def test_a_failure_whose_REASON_changes_writes_a_second_line(self):
        """The memo silences a repeat and never a new fault."""
        self.down()
        (self.tmp / "scripts" / "ops" / "agda-watchdog.sh").unlink()
        st = pod.State()
        pod.watchdog_tick(st, self.tmp)
        self.patch(subprocess, "Popen",
                   lambda *a, **kw: (_ for _ in ()).throw(OSError("Exec format error")))
        (self.tmp / "scripts" / "ops" / "agda-watchdog.sh").write_text(WATCHDOG_SH)
        pod.watchdog_tick(st, self.tmp)
        whys = [x["why"] for x in self.watchdog_lines()]
        self.assertEqual(len(whys), 2)
        self.assertIn("Exec format error", whys[1])

    def test_a_watchdog_that_comes_BACK_clears_the_memo(self):
        """The next failure after a recovery is a new fault and writes its own line."""
        self.down()
        (self.tmp / "scripts" / "ops" / "agda-watchdog.sh").unlink()
        st = pod.State()
        pod.watchdog_tick(st, self.tmp)
        self.patch(pod, "watchdog_alive", lambda: True)
        pod.watchdog_tick(st, self.tmp)
        self.patch(pod, "watchdog_alive", lambda: False)
        pod.watchdog_tick(st, self.tmp)
        self.assertEqual(len(self.watchdog_lines()), 2)

    def test_the_backstop_note_is_silent_when_the_two_homes_AGREE(self):
        """The owner's 2026-08-23 6 GB per-process cap and C-12's 8 percent free floor
        are written twice: in the script and in `[tiers.shared]`. The fixture's copies
        agree."""
        self.assertIsNone(pod.watchdog_backstop_note())

    def test_the_backstop_note_NAMES_a_disagreement_between_the_two_homes(self):
        """Two homes for one number drift silently, and this number is a memory cap."""
        p = self.tmp / "scripts" / "ops" / "agda-watchdog.sh"
        p.write_text(WATCHDOG_SH.replace("6*1024*1024", "10*1024*1024")
                     .replace("FREE_MIN=8", "FREE_MIN=3"))
        # THE WHOLE PHRASE, and not the digit alone: `assertIn("3", note)` holds on any
        # note that carries a 3 anywhere, including the one that names the RIGHT number.
        note = pod.watchdog_backstop_note()
        self.assertIn("the script says 10 GB per process and "
                      "[tiers.shared].per_process_backstop_gb says 6", note)
        self.assertIn("the script says 3 percent system free and "
                      "[tiers.shared].system_free_floor_pct says 8", note)

    def test_an_unreadable_script_gives_no_note_and_never_raises(self):
        (self.tmp / "scripts" / "ops" / "agda-watchdog.sh").unlink()
        self.assertIsNone(pod.watchdog_backstop_note())

    def test_every_tick_confirms_the_watchdog(self):
        """A13 says every tick, so the call sits above every rule that reads `admits()`."""
        self.patch(pod, "watchdog_tick",
                   lambda st, root=None: self.calls.__setitem__(
                       "watchdog", self.calls["watchdog"] + 1) or True)
        pod.pod_tick(pod.State(), self.tmp)
        pod.pod_tick(pod.State(), self.tmp)
        self.assertEqual(self.calls["watchdog"], 2)


# ---------------------------------------------------------------- A14, the two tiers


class Tiers(LoopCase):
    """A14 restored C-12's tiers: WIDE four at `-M8g`, HEAVY two at `-M12g`, the mixed
    worst case at or under 32 GB, and slots three and four only above 25 percent free."""

    def setUp(self):
        super().setUp()
        self.patch(pod, "admits", REAL_ADMITS)
        self.patch(pod, "watchdog_alive", lambda: True)
        self.patch(pod, "agda_pileup", lambda: (0, {}, None))
        self.patch(pod, "free_memory_pct", lambda: 90.0)
        self.st = pod.State()

    def running(self, code, tier, status=None):
        t = pod.Task(code, status=status or pod.RUNNING, agda=True, tier=tier)
        self.st.tasks[code] = t
        return t

    def brief_with(self, line):
        p = self.tmp / "agents" / "tasks" / DIR / f"{CODE}.md"
        p.write_text(BRIEF.replace("machine: shared", "machine: shared\n" + line))
        return f"agents/tasks/{DIR}/{CODE}.md"

    def test_a_brief_that_names_no_tier_is_WIDE(self):
        """WIDE is the caliber `run_agda()` really sets, so it is the true worst case."""
        self.assertEqual(pod.task_tier(f"agents/tasks/{DIR}/{CODE}.md", self.tmp),
                         pod.WIDE)

    def test_a_brief_that_declares_heavy_gets_HEAVY(self):
        brief = self.brief_with("agda_tier: heavy")
        self.assertEqual(pod.task_tier(brief, self.tmp), pod.HEAVY)

    def test_a_tier_NOBODY_RULED_takes_the_conservative_tier(self):
        """A declaration the program cannot read is not a licence for four slots: HEAVY
        is stricter in both terms at once, fewer slots and a bigger heap in the sum."""
        brief = self.brief_with("agda_tier: enormous")
        self.assertEqual(pod.task_tier(brief, self.tmp), pod.HEAVY)

    def test_an_unreadable_brief_is_WIDE_and_never_raises(self):
        self.assertEqual(pod.task_tier("agents/tasks/nowhere/x.md", self.tmp), pod.WIDE)

    def test_the_tier_is_copied_ONCE_at_creation_like_the_machine_class(self):
        self.brief_with("agda_tier: heavy")
        self.queue({"code": CODE, "brief": f"agents/tasks/{DIR}/{CODE}.md"})
        st = pod.State()
        pod._rule_a1(st, self.tmp)
        self.assertEqual(st.tasks[CODE].tier, pod.HEAVY)
        self.assertEqual(self.lines()[-1]["tier"], pod.HEAVY)

    def test_the_WIDE_tier_admits_four_and_the_HEAVY_tier_admits_two(self):
        """OWNER'S RULING 2026-08-23: both are now one. The two names survive so a
        brief may still declare either, but `admits()`'s GLOBAL total is checked
        against the SAME ceiling either way."""
        self.assertEqual(pod.agda_slots(pod.WIDE), 1)
        self.assertEqual(pod.agda_slots(pod.HEAVY), 1)

    def test_the_third_slot_opens_only_above_the_free_memory_floor(self):
        """C-12's own 25 percent, and `[tiers.shared]` holds the number.

        OWNER'S RULING 2026-08-23: `agda_slots()` no longer varies with free memory
        (`floor = min(1, 2) == slots` already), so there is no THIRD slot left to gate
        on this floor at all -- both branches now refuse identically, at total >= 1."""
        self.patch(pod, "agda_pileup", lambda: (1, {900: 1}, None))
        t = pod.Task("X", agda=True, tier=pod.WIDE)
        self.assertFalse(pod.admits(self.st, t))
        self.patch(pod, "free_memory_pct", lambda: 24.0)
        self.assertFalse(pod.admits(self.st, t))

    def test_a_HEAVY_task_is_refused_at_TWO_where_a_WIDE_task_is_admitted(self):
        """The tier changes the ceiling and nothing else does. OWNER'S RULING
        2026-08-23 made both tiers' LIVE ceiling the same (1), so this property is
        demonstrated here by patching `agda_slots` to give the two tiers distinct
        ceilings again, decoupled from the live policy's own numbers -- the
        MECHANISM (each tier reads its own ceiling) is what is under test, not
        today's particular figure."""
        self.patch(pod, "agda_pileup", lambda: (2, {900: 1, 901: 1}, None))
        self.patch(pod, "agda_slots", lambda tier=pod.WIDE: 3 if tier == pod.WIDE else 2)
        self.assertTrue(pod.admits(self.st, pod.Task("W", agda=True, tier=pod.WIDE)))
        self.assertFalse(pod.admits(self.st, pod.Task("H", agda=True, tier=pod.HEAVY)))

    def test_the_mixed_worst_case_holds_at_or_under_the_4_GB_sum(self):
        """ONE HEAVY BESIDE THREE WIDE is 16 GB under the owner's 2026-08-23 4 GB-per-
        writer caliber, and no per-tier count refuses it on its own: the heavy tier
        sees one of its own and the wide tier sees three of its own. `agda_slots` is
        patched generously so the CEILING check (now 1 for both tiers, and refusing
        on its own regardless) does not mask the SUM check this test is about."""
        self.patch(pod, "agda_pileup", lambda: (3, {900: 1, 901: 1, 902: 1}, None))
        self.patch(pod, "agda_slots", lambda tier=pod.WIDE: 10)
        self.running("A", pod.HEAVY)
        self.running("B", pod.WIDE)
        self.running("C", pod.WIDE)
        self.assertFalse(pod.admits(self.st, pod.Task("D", agda=True, tier=pod.WIDE)))

    def test_the_lone_WIDE_writer_is_exactly_the_4_GB_sum_and_still_fits(self):
        """The bar is `at or under`: owner's ruling 2026-08-23 made the sum cap equal
        to a single writer's own caliber, so the ONE slot that is now reachable stays
        reachable at the exact boundary, the same property the old four-writers-at-
        32-GB test demonstrated for the four-slot cap. `agda_slots` is patched
        generously to isolate the SUM check from the (now separately refusing)
        ceiling check."""
        self.patch(pod, "agda_pileup", lambda: (0, {}, None))
        self.patch(pod, "agda_slots", lambda tier=pod.WIDE: 10)
        self.assertTrue(pod.admits(self.st, pod.Task("D", agda=True, tier=pod.WIDE)))

    def test_a_CHECKING_task_holds_its_heap_too(self):
        """The acceptance runner starts Agda, so a task in CHECKING is a live writer."""
        self.patch(pod, "agda_pileup", lambda: (3, {900: 1, 901: 1, 902: 1}, None))
        self.patch(pod, "agda_slots", lambda tier=pod.WIDE: 10)
        self.running("A", pod.HEAVY, status=pod.CHECKING)
        self.running("B", pod.WIDE)
        self.running("C", pod.WIDE)
        self.assertFalse(pod.admits(self.st, pod.Task("D", agda=True, tier=pod.WIDE)))

    def test_a_task_never_counts_its_OWN_heap_twice(self):
        """Rule (c) asks about a task that is already CHECKING, and counting it on both
        sides would refuse the acceptance run of the fourth wide task for ever.
        `agda_slots` is patched generously so the (now separately refusing) ceiling
        does not mask the property this test is about."""
        self.patch(pod, "agda_pileup", lambda: (3, {900: 1, 901: 1, 902: 1}, None))
        self.patch(pod, "agda_slots", lambda tier=pod.WIDE: 10)
        t = self.running("D", pod.WIDE, status=pod.CHECKING)
        self.assertTrue(pod.admits(self.st, t))

    def test_the_transition_line_carries_the_tier_so_two_records_compare_inside_one(self):
        st = pod.State()
        st.tasks[CODE] = t = pod.Task(CODE, status=pod.READY, tier=pod.HEAVY)
        pod.emit(st, t, pod.READY, pod.RUNNING, pid=1, root=self.tmp)
        self.assertEqual(self.lines()[-1]["tier"], pod.HEAVY)

    def test_the_tier_vocabulary_has_ONE_home(self):
        """`run_agda()` turns the name into a caliber, so a second spelling here would be
        a second memory cap."""
        self.assertEqual(tuple(pod.TIERS), tuple(facts_mod.TASK_TIERS))
        self.assertEqual(pod.WIDE, facts_mod.DEFAULT_TIER)


# ---------------------------------------------------------------- A11, rule (g) REFILL


class RuleG(LoopCase):
    """A11. An idle slot is CURED mechanically and not merely reported (gap M12)."""

    def setUp(self):
        super().setUp()
        self.patch(pod, "_rule_g", REAL_RULE_G)
        (self.tmp / "dev" / "pod" / "instructions").mkdir(parents=True, exist_ok=True)
        (self.tmp / "agents" / "tasks" / "POD-REFILL").mkdir(parents=True, exist_ok=True)
        (self.tmp / "agents" / "tasks" / "POD-REFILL" / "POD-REFILL.md").write_text(
            "# the standing refill brief\n\n## HEAD\nhead_slot: mathematician\n")
        self.launched = launched = []

        class FakeLauncher:
            """The four values rule (g) hands the launcher. IT SPAWNS NOTHING."""

            HARNESS = ""

            @staticmethod
            # `**kw` ON PURPOSE, 2026-08-18. This stub pinned the launcher's exact
            # signature, so adding a `provider=` argument raised a TypeError inside
            # `pod.launch()`, whose broad `except Exception` turns any failure into
            #「nothing launched」. Six RuleG tests then failed with `0 != 1` and named
            # the floor, not the signature. A stub that pins a signature it does not
            # assert on buys nothing and costs a wrong diagnosis.
            def launch(task, brief, agda, sandbox, model, effort="", preamble=None,
                       tier="wide", **kw):
                launched.append((task, str(brief), agda, model, effort))
                return 0
        self.patch(facts_mod, "launcher", lambda: FakeLauncher)

    def refill_lines(self):
        return [x for x in self.lines() if x.get("event") == "refill"]

    def test_a_NEW_DIRECTION_re_plans_a_queue_that_is_not_empty(self):
        """**THE WHOLE POINT OF THE DIRECTION FILE.** Rule (g) otherwise waits for the
        queue to drain, so a correction the owner writes now takes effect whenever the
        queue happens to run out, which on a full queue is hours. A fresh direction
        bypasses BOTH the empty-queue gate and the refill floor.

        WHAT HAPPENS TO THE ENTRIES ALREADY QUEUED IS NOT THE PROGRAM'S CALL. It deletes
        none of them. AD3 gives that judgement to the mathematician this dispatch starts.
        """
        st = pod.State()
        self.patch(pod, "dispatchable_entries", lambda s_: [{"task": "LJ-1.999"}])
        self.patch(pod, "hours_since_last_refill", lambda root=None: 0.0)

        pod._rule_g(st, self.tmp)              # a full queue and a fresh floor: no refill
        self.assertEqual(self.launched, [], "a full queue must not refill on its own")

        d = self.tmp / "dev" / "pod"
        d.mkdir(parents=True, exist_ok=True)
        (d / "direction.md").write_text("prove the bridge before GCH", encoding="utf-8")

        pod._rule_g(st, self.tmp)
        self.assertEqual(len(self.launched), 1,
                         "a new direction did not re-plan a non-empty queue")
        pod._rule_g(st, self.tmp)
        self.assertEqual(len(self.launched), 1,
                         "the direction fired twice; the sha was not recorded")

    def test_a_free_slot_and_an_empty_queue_dispatch_the_standing_brief(self):
        """The program decides only that somebody must be asked; the head decides the
        work, so AD1 holds."""
        pod._rule_g(pod.State(), self.tmp)
        self.assertEqual(len(self.launched), 1)
        task, brief, agda, model, effort = self.launched[0]
        self.assertEqual(task, "POD-REFILL")
        self.assertTrue(brief.endswith("agents/tasks/POD-REFILL/POD-REFILL.md"))
        self.assertFalse(agda)
        self.assertEqual(model, heads_mod.head("mathematician")["model"])
        self.assertEqual(self.refill_lines()[-1]["result"], "dispatched")

    def test_a_dispatchable_queue_entry_holds_the_refill(self):
        """A11's own test: the queue holds work rule (a1) will turn into a task."""
        self.queue({"code": CODE, "brief": f"agents/tasks/{DIR}/{CODE}.md"})
        pod._rule_g(pod.State(), self.tmp)
        self.assertEqual(self.launched, [])
        self.assertEqual(self.refill_lines(), [])

    def test_a_REQUEST_with_no_brief_does_NOT_hold_the_refill(self):
        """An entry with no `brief` is never a task (section 5.2), so it is not work."""
        self.queue({"code": "LJ-1.999-split", "split_of": CODE, "reason": "a split"})
        pod._rule_g(pod.State(), self.tmp)
        self.assertEqual(len(self.launched), 1)

    def test_an_entry_whose_task_already_EXISTS_does_not_hold_the_refill(self):
        self.queue({"code": CODE, "brief": f"agents/tasks/{DIR}/{CODE}.md"})
        st = pod.State()
        st.tasks[CODE] = pod.Task(CODE, status=pod.DONE)
        pod._rule_g(st, self.tmp)
        self.assertEqual(len(self.launched), 1)

    def test_a_READY_task_takes_the_free_slot_first(self):
        st = pod.State()
        st.tasks[CODE] = pod.Task(CODE, status=pod.READY)
        pod._rule_g(st, self.tmp)
        self.assertEqual(self.launched, [])

    def test_no_free_slot_means_no_refill(self):
        self.patch(pod, "admits", lambda st, t, agda=None: False)
        pod._rule_g(pod.State(), self.tmp)
        self.assertEqual(self.launched, [])
        self.assertEqual(self.refill_lines(), [])

    def test_the_floor_stops_a_refill_every_tick(self):
        """A mathematician that queues NOTHING is a legal return, so without a floor an
        empty queue would dispatch one refill every `tick_seconds`."""
        st = pod.State()
        for _ in range(4):
            pod._rule_g(st, self.tmp)
        self.assertEqual(len(self.launched), 1)

    def test_the_floor_is_read_from_the_LOG_so_it_survives_a_restart(self):
        pod._rule_g(pod.State(), self.tmp)
        self.assertLess(pod.hours_since_last_refill(self.tmp), 1.0)
        fresh = pod.State()                    # a new process, an empty state file
        pod._rule_g(fresh, self.tmp)
        self.assertEqual(len(self.launched), 1)

    def test_the_floor_does_not_hold_when_the_last_refill_queued_work(self):
        """MEASURED 2026-08-20 after POD-REFILL-192930.

        The floor exists because a mathematician that queues NOTHING is a legal
        return. A refill that produced a task has already spaced the next ask:
        those tasks occupied the slots. Holding the hour after they park leaves
        free slots idle.
        """
        st = pod.State()
        pod._rule_g(st, self.tmp)
        self.assertEqual(len(self.launched), 1)
        t = pod.Task(CODE, brief=f"agents/tasks/{DIR}/{CODE}.md", status=pod.READY)
        st.tasks[CODE] = t
        pod.emit(st, t, pod.NONE, pod.READY, brief=t.brief, root=self.tmp)
        t.status = pod.DONE
        pod._rule_g(st, self.tmp)
        self.assertEqual(len(self.launched), 2,
                         "a refill that queued work still sat behind the hour floor")

    def test_the_owner_s_own_limit_key_WINS_over_the_constant(self):
        """`dev/pod/heads.toml` is the one home of a limit, and the constant is a floor
        that yields the moment the owner writes the key."""
        st = pod.State()
        pod._rule_g(st, self.tmp)              # the constant admits the first refill
        self.assertEqual(len(self.launched), 1)
        p = self.tmp / "dev" / "pod" / "heads.toml"
        p.write_text(p.read_text().replace(
            "attempt_max = 4", "attempt_max = 4\nrefill_min_hours = 1e12"))
        heads_mod._CACHE.clear()
        self.assertEqual(pod._refill_min_hours(), 1e12)
        pod.log_path(root=self.tmp).unlink()   # no refill line at all in the log
        pod._rule_g(pod.State(), self.tmp)     # and it STILL waits, on the key alone
        self.assertEqual(len(self.launched), 1)

    def test_an_ABSENT_standing_brief_is_NAMED_and_never_invented(self):
        """AD3 gives every brief to the mathematician, so the program records the missing
        dependency and waits. It never writes a brief."""
        (self.tmp / "agents" / "tasks" / "POD-REFILL" / "POD-REFILL.md").unlink()
        pod._rule_g(pod.State(), self.tmp)
        self.assertEqual(self.launched, [])
        line = self.refill_lines()[-1]
        self.assertEqual(line["result"], "absent")
        self.assertEqual(line["brief"], "agents/tasks/POD-REFILL/POD-REFILL.md")

    def test_a_launcher_refusal_is_recorded_and_never_silent(self):
        class Broken:
            HARNESS = ""

            @staticmethod
            def launch(*a, **kw):
                raise RuntimeError("the pane server is gone")
        self.patch(facts_mod, "launcher", lambda: Broken)
        pod._rule_g(pod.State(), self.tmp)
        line = self.refill_lines()[-1]
        self.assertEqual(line["result"], "REFUSED")
        self.assertIn("the pane server is gone", line["why"])

    def test_an_already_running_refill_records_the_launcher_why(self):
        """MEASURED 2026-08-20 seq 279. Direction change, live refill, no new pane."""
        class Busy:
            HARNESS = ""

            @staticmethod
            def launch(*a, **kw):
                print("dispatch: POD-REFILL is already running (pid 89237)",
                      file=sys.stderr)
                return 1
        self.patch(facts_mod, "launcher", lambda: Busy)
        pod._rule_g(pod.State(), self.tmp)
        line = self.refill_lines()[-1]
        self.assertEqual(line["result"], "REFUSED")
        self.assertIn("already running", line["why"])
        self.assertNotEqual(line["why"], "the launcher exited 1")

    def test_the_refill_is_NOT_a_task_and_holds_no_state_record(self):
        """Routing it through the table would park it for no match and count against
        AD14's three, exactly as `POD-BATCH` must not."""
        st = pod.State()
        pod._rule_g(st, self.tmp)
        self.assertEqual(st.tasks, {})

    def test_a_stopped_loop_dispatches_NO_refill(self):
        """Rule (g) DISPATCHES, so the stop refuses it exactly as it refuses rule (f)."""
        self.patch(pod, "_rule_g",
                   lambda st, root=None: self.calls.__setitem__(
                       "refill", self.calls["refill"] + 1))
        (self.tmp / ".pod-state" / "STOPPED").touch()
        self.assertIs(pod.pod_tick(pod.State(), self.tmp), pod.STOP)
        self.assertEqual(self.calls["refill"], 0)

    def test_an_ordinary_tick_reaches_rule_g_LAST(self):
        self.patch(pod, "_rule_g",
                   lambda st, root=None: self.calls.__setitem__(
                       "refill", self.calls["refill"] + 1))
        self.assertIs(pod.pod_tick(pod.State(), self.tmp), pod.CONTINUE)
        self.assertEqual(self.calls["refill"], 1)


# ---------------------------------------------------------------- the heads loader


class Heads(LoopCase):
    """AD26 and section 6.1. NO FIELD HAS A SILENT DEFAULT."""

    def edit(self, old, new):
        """One edit to the fixture's `heads.toml`, and IT MUST LAND.

        A `str.replace` that matches nothing is silent, so a re-worded comment in the real
        file would leave every refusal test below editing NOTHING and passing on a clean
        file. The assertion is the fixture's own C-45 guard.
        """
        p = self.tmp / "dev" / "pod" / "heads.toml"
        before = p.read_text()
        after = before.replace(old, new)
        self.assertNotEqual(before, after, f"the fixture edit matched nothing: {old!r}")
        p.write_text(after)
        heads_mod._CACHE.clear()

    def test_the_five_ruled_slots_load_and_every_head_is_INTERNALLY_consistent(self):
        """AD24 and AD25 name four heads and AD2 needs a fifth. A loader that merely
        PARSES proves nothing here, because `_require()` already refuses a missing field.

        **THIS PINNED A12's MODEL AND WENT RED FOR AN OWNER RULING.** A12 set the
        maintainer to `claude-opus-5` at effort `high`; A26 moved the slot to grok on
        2026-08-19; the owner moved it back to opus at `xhigh` on 2026-08-20. A model
        name is the owner's under AD26 and moves whenever they say so, so what this
        asserts now is what the LOADER guarantees: five slots, every field inside its
        legal set, and every head reachable."""
        cfg = heads_mod.load_heads(self.tmp / "dev" / "pod" / "heads.toml")
        self.assertEqual(sorted(cfg["heads"]),
                         ["coder", "coder_adversarial", "maintainer",
                          "mathematician", "mathematician_adversarial"])
        # A27: A SLOT MAPS TO A LIST, ALWAYS, whichever of the two spellings the file
        # uses. One shape is what stops a reader branching on the type it happened to get.
        for slot, rows in cfg["heads"].items():
            self.assertIsInstance(rows, list, slot)
            self.assertTrue(rows, slot)
            for row in rows:
                self.assertIn(row["model"], cfg["legal"]["models"], slot)
                self.assertIn(row["effort"], cfg["legal"]["efforts"], slot)
                self.assertTrue(row["harness"], slot)
        maint = heads_mod.head("maintainer", self.tmp / "dev" / "pod" / "heads.toml")
        self.assertEqual(maint["effort"], "xhigh")
        self.assertEqual(maint["model"], "claude-sonnet-5")
        for k in heads_mod.LIMIT_KEYS:
            self.assertGreater(cfg["limits"][k], 0, k)

    def test_a_model_outside_legal_models_is_REFUSED(self):
        self.edit('mathematician             = { model = "claude-opus-5"',
                  'mathematician             = { model = "claude-haiku-5"')
        with self.assertRaises(heads_mod.HeadsError):
            heads_mod.load_heads(self.tmp / "dev" / "pod" / "heads.toml", cache=False)

    def test_a_missing_limit_is_REFUSED_and_never_defaulted(self):
        self.edit("attempt_max = 4", "attempts_max = 4")
        with self.assertRaises(heads_mod.HeadsError):
            heads_mod.load_heads(self.tmp / "dev" / "pod" / "heads.toml", cache=False)

    def test_an_unknown_slot_is_REFUSED_rather_than_defaulted(self):
        with self.assertRaises(heads_mod.HeadsError):
            heads_mod.head("archaeologist", self.tmp / "dev" / "pod" / "heads.toml")

    def test_the_mixed_worst_case_heap_sum_is_checked_at_load(self):
        """A14 holds the sum at or under `max_heap_sum_gb`. A future edit that widens a
        tier is caught here and not on the machine that runs out of memory. OWNER'S
        RULING 2026-08-23 made ONE writer at 4 GB the whole budget, so widening to two
        (2 x 4 = 8 GB) already breaks it."""
        self.edit("slots = 1                     # OWNER'S RULING 2026-08-23: one Agda "
                  "writer, no more",
                  "slots = 2                     # widened past the sum cap for this test")
        with self.assertRaises(heads_mod.HeadsError):
            heads_mod.load_heads(self.tmp / "dev" / "pod" / "heads.toml", cache=False)

    def test_the_critic_is_never_the_same_model_as_the_author(self):
        """DD25's invariant survives mechanically, by construction of `[heads]`.

        **A27 MADE THIS A SET COMPARISON AND NOT A STRING ONE.** An author slot may now
        carry two models, and the invariant is that NO model of the author is a model of
        the critic: one shared string is one review a model gives its own work.

        **OWNER'S RULING 2026-08-23 WAIVED ONE PAIR.** Qwen's return gave `coder` the
        fallback `glm-5.3`, which `mathematician_adversarial` already carried and kept.
        A coder stop/no-go branch CAN route to `mathematician_adversarial`, so this is a
        real, disclosed exception and not a silent hole: it is asserted on its own,
        below, rather than folded into the loop that still holds the other two pairs.
        """
        p = self.tmp / "dev" / "pod" / "heads.toml"
        for author, critic in (("mathematician", "mathematician_adversarial"),
                               ("coder", "coder_adversarial")):
            a = {r["model"] for r in heads_mod.configs(author, p)}
            c = {r["model"] for r in heads_mod.configs(critic, p)}
            self.assertEqual(a & c, set(), f"{critic} shares a model with {author}")
        coder = {r["model"] for r in heads_mod.configs("coder", p)}
        math_adv = {r["model"] for r in heads_mod.configs("mathematician_adversarial", p)}
        self.assertEqual(coder & math_adv, {"glm-5.3"},
                         "owner's ruling 2026-08-23's disclosed exception")

    # ---------------------------------------------------- A27, the multi-model slot

    def cfgs(self):
        """Every config of the live `coder` slot, through the loader the program uses."""
        return heads_mod.configs("coder", self.tmp / "dev" / "pod" / "heads.toml")

    def test_the_single_table_spelling_still_loads_and_still_means_one_head(self):
        """**BACKWARD COMPATIBILITY IS THE POINT OF THE SUPERSET.** Four slots were not
        touched by A27 and must load byte-for-byte as they did, so this asserts the SHAPE
        of the return and not only that the file parses.

        **TWO OF THOSE FOUR CARRY A CHOICE SINCE A29**: the owner ruled both critics onto
        a second head on 2026-08-21. The superset claim is unchanged and the slots that
        can still witness it are the two below.
        """
        p = self.tmp / "dev" / "pod" / "heads.toml"
        for slot in ("mathematician", "maintainer"):
            rows = heads_mod.configs(slot, p)
            self.assertEqual(len(rows), 1, slot)
            self.assertIsNone(rows[0]["max_concurrency"], slot)
            # `head()` WITHOUT A MODEL IS THE OLD CALL and it still answers for these four.
            self.assertEqual(heads_mod.head(slot, p)["model"], rows[0]["model"])

    @unittest.skip("owner 2026-08-22: qwen is out of [heads].coder for maintenance, "
                    "so coder is a one-config array and no longer 'carries a choice'. "
                    "Un-skip when qwen's line is restored.")
    def test_head_refuses_a_slot_that_carries_a_choice_and_answers_a_named_model(self):
        """A default head is a model nobody ruled, so `head("coder")` REFUSES rather than
        returning the first entry and calling it the default."""
        p = self.tmp / "dev" / "pod" / "heads.toml"
        with self.assertRaises(heads_mod.HeadsError):
            heads_mod.head("coder", p)
        for row in self.cfgs():
            self.assertEqual(heads_mod.head("coder", p, row["model"])["model"],
                             row["model"])
        # A LEGAL MODEL THIS SLOT DOES NOT CARRY IS STILL A REFUSAL, which is the case
        # that separates "the loader knows the string" from "this slot may run it".
        # It used to name `claude-opus-5`; the owner made that the coder's own second
        # head on 2026-08-21, so the probe moved to a model no coder config names.
        self.assertNotIn("glm-5.3", {r["model"] for r in self.cfgs()})
        with self.assertRaises(heads_mod.HeadsError):
            heads_mod.head("coder", p, "glm-5.3")

    @unittest.skip("owner 2026-08-22: qwen was coder's one capped config; with it out "
                    "for maintenance, coder carries no capped head to pick first. "
                    "Un-skip when qwen's line is restored.")
    def test_a_capped_model_with_headroom_is_chosen_before_the_uncapped_one(self):
        """THE POLICY IS CAPPED FIRST. An idle pod sends the coder to the LOCAL head."""
        cfgs = self.cfgs()
        got = pod.pick_head_config(cfgs, [0] * len(cfgs))
        self.assertEqual(got["max_concurrency"], 1)
        self.assertEqual(got["harness"], "herdr-pi")

    def test_a_capped_model_AT_its_cap_is_skipped_for_the_next_eligible_one(self):
        cfgs = self.cfgs()
        counts = [c["max_concurrency"] or 0 for c in cfgs]
        got = pod.pick_head_config(cfgs, counts)
        self.assertIsNotNone(got)
        self.assertIsNone(got["max_concurrency"], "a full cap was spent anyway")

    def test_every_capped_model_full_falls_through_to_the_uncapped_one(self):
        """A synthetic three-config slot, because the live file has one capped head and
        the fall-through needs two. C-45: a fixture that cannot exercise the branch is
        not a fixture."""
        cfgs = [{"model": "a", "max_concurrency": 1},
                {"model": "b", "max_concurrency": 2},
                {"model": "c", "max_concurrency": None}]
        self.assertEqual(pod.pick_head_config(cfgs, [0, 0, 0])["model"], "a")
        self.assertEqual(pod.pick_head_config(cfgs, [1, 0, 0])["model"], "b")
        self.assertEqual(pod.pick_head_config(cfgs, [1, 2, 0])["model"], "c")
        # THE TIE-BREAK IS THE FILE'S OWN ORDER, so `b` first would answer `b`.
        self.assertEqual(pod.pick_head_config(list(reversed(cfgs)),
                                              [0, 0, 0])["model"], "b")

    def test_a_slot_whose_every_capped_model_is_full_and_none_uncapped_REFUSES(self):
        """It returns None rather than the first config: dispatching anyway would break
        the cap the owner wrote, and dispatching nothing in silence is the blind sensor."""
        cfgs = [{"model": "a", "max_concurrency": 1},
                {"model": "b", "max_concurrency": 1}]
        self.assertIsNone(pod.pick_head_config(cfgs, [1, 1]))
        why = pod.head_full_refusal("coder", cfgs, [1, 1])
        self.assertIn("a 1/1", why)
        self.assertIn("b 1/1", why)

    def test_a_slot_of_ONE_config_picks_it_whatever_the_count_says(self):
        """The four unchanged slots behave exactly as they did before A27: one config,
        no cap, and the live count is never consulted."""
        one = [{"model": "solo", "max_concurrency": None}]
        for n in (0, 1, 7):
            self.assertIs(pod.pick_head_config(one, [n]), one[0])

    def test_the_live_count_is_per_slot_and_per_model_and_counts_only_live_states(self):
        """RUNNING and CHECKING hold a head. DONE and PARKED do not: their agent exited,
        so counting them would shrink a cap that nothing is using."""
        cfgs = [{"model": "m1"}, {"model": "m2"}]
        st = pod.State()
        for code, role, model, status in (
                ("A", "coder", "m1", pod.RUNNING),
                ("B", "coder", "m1", pod.CHECKING),
                ("C", "coder", "m1", pod.DONE),
                ("D", "coder", "m1", pod.PARKED),
                ("E", "coder_adversarial", "m1", pod.RUNNING),   # another SLOT
                ("F", "coder", "m2", pod.RUNNING)):
            st.tasks[code] = pod.Task(code, role=role, model=model, status=status)
        self.assertEqual(pod.head_live_counts(st, "coder", cfgs), [2, 1])
        self.assertEqual(pod.head_live_counts(st, "mathematician", cfgs), [0, 0])
        # NO STATE COUNTS ZERO, which is the only honest answer a caller with no census
        # can give. Rule (f) always has one.
        self.assertEqual(pod.head_live_counts(None, "coder", cfgs), [0, 0])

    def test_rule_f_hands_the_state_to_launch_so_the_cap_can_be_counted(self):
        """A27's wiring, and the defect it guards is a five-argument call meeting a
        four-argument stub: rule (f) would then park every dispatch as `launch`."""
        self.assertIn("st", inspect.signature(pod.launch).parameters)
        src = inspect.getsource(pod._rule_f)
        self.assertIn("launch(t, b, role, root, st)", src)

    # ---------------------------------------------------- A27, the loader's refusals

    def test_an_empty_array_of_configs_is_REFUSED(self):
        self.edit('coder                     = [', 'coder = []\nunused = [')
        with self.assertRaises(heads_mod.HeadsError):
            heads_mod.load_heads(self.tmp / "dev" / "pod" / "heads.toml", cache=False)

    #: THE CODER'S SECOND CONFIG, VERBATIM, and the edits below aim at THIS row rather
    #: than at any other array element. OWNER'S RULING 2026-08-23 made it `glm-5.3`
    #: (qwen's own fallback); `mathematician_adversarial` also carries a `glm-5.3` row,
    #: but with DIFFERENT padding, so a `str.replace` naming this exact literal still
    #: cannot land on the wrong slot.
    CODER_2ND = ('  { model = "glm-5.3",              effort = "",'
                 ' harness = "herdr-pi", sandbox = "acceptEdits" },')

    def test_an_array_element_that_is_not_a_table_is_REFUSED(self):
        """An array of STRINGS parses as TOML and names no harness, so the refusal has to
        be the loader's and cannot be the parser's."""
        self.edit(self.CODER_2ND, '  "glm-5.3",')
        with self.assertRaises(heads_mod.HeadsError):
            heads_mod.load_heads(self.tmp / "dev" / "pod" / "heads.toml", cache=False)

    def test_a_config_missing_a_required_field_is_REFUSED(self):
        self.edit(self.CODER_2ND, '  { model = "glm-5.3", effort = "" },')
        with self.assertRaises(heads_mod.HeadsError):
            heads_mod.load_heads(self.tmp / "dev" / "pod" / "heads.toml", cache=False)

    def test_a_config_carrying_an_unknown_field_is_REFUSED(self):
        self.edit("max_concurrency = 1 }", "max_concurrancy = 1 }")
        with self.assertRaises(heads_mod.HeadsError):
            heads_mod.load_heads(self.tmp / "dev" / "pod" / "heads.toml", cache=False)

    def test_a_cap_that_is_not_a_positive_integer_is_REFUSED(self):
        """A ZERO IS NOT `unlimited`: it is a head no task can ever reach. A BOOLEAN is an
        `int` in Python, so `true` would otherwise load as a cap of one."""
        for bad in ("0", "-1", '"1"', "1.5", "true"):
            with self.subTest(cap=bad):
                self.edit("max_concurrency = 1 }", f"max_concurrency = {bad} }}")
                with self.assertRaises(heads_mod.HeadsError):
                    heads_mod.load_heads(self.tmp / "dev" / "pod" / "heads.toml",
                                         cache=False)
                self.edit(f"max_concurrency = {bad} }}", "max_concurrency = 1 }")

    def test_one_slot_naming_one_model_twice_is_REFUSED(self):
        """The dispatcher counts a live head by its SLOT and its MODEL, so two configs on
        one model are two caps it cannot tell apart."""
        self.edit(self.CODER_2ND,
                  '  { model = "Qwen3.8-27B-oQ4e-mtp", effort = "",'
                  ' harness = "herdr-pi", sandbox = "acceptEdits" },')
        with self.assertRaises(heads_mod.HeadsError):
            heads_mod.load_heads(self.tmp / "dev" / "pod" / "heads.toml", cache=False)

    def test_a_model_outside_legal_models_is_REFUSED_inside_an_array_too(self):
        """The single-table path had this check and the array path is a second entry to
        the same rule, so it is checked at both."""
        self.edit(self.CODER_2ND,
                  '  { model = "claude-haiku-5", effort = "",'
                  ' harness = "herdr-pi", sandbox = "acceptEdits" },')
        with self.assertRaises(heads_mod.HeadsError):
            heads_mod.load_heads(self.tmp / "dev" / "pod" / "heads.toml", cache=False)

    @unittest.skip("owner 2026-08-22: this edit targets qwen's coder entry to prove the "
                    "refusal applies per-config; qwen's line is out of [heads].coder "
                    "for maintenance, so `configs(\"coder\")` no longer reads it. "
                    "Un-skip when qwen's line is restored.")
    def test_a_herdr_pi_config_with_no_provider_entry_is_REFUSED(self):
        """`legal.pi_provider` had zero consumers until 2026-08-18 and both `glm-5.3`
        heads dispatched on `deepseek`. The refusal applies per CONFIG, not per slot."""
        self.edit('"Qwen3.8-27B-oQ4e-mtp" = "omlx"', '"unused-key" = "omlx"')
        with self.assertRaises(heads_mod.HeadsError):
            heads_mod.configs("coder", self.tmp / "dev" / "pod" / "heads.toml",
                              cache=False)


# ---------------------------------------------------------------- the acceptance runner


class Acceptance(LoopCase):
    """Section 5.4. It MEASURES all six first, then TESTS all six."""

    class T:
        code, brief, obl_before, unbound_before = CODE, None, 0, ()

    def stub(self, **kw):
        """Every conjunct is a value. NO TEST HERE STARTS AGDA."""
        self.patch(accept_mod, "spec_surface", lambda root=None: kw.get("c5", True))
        self.patch(accept_mod, "closure", lambda root=None: kw.get("c3", True))
        self.patch(accept_mod, "unbound_new",
                   lambda ch, before, root=None: (kw.get("c4", True), False))
        self.patch(accept_mod, "precommit_set",
                   lambda code=None, root=None: kw.get("c6", True))
        self.patch(accept_mod, "conjunct1", lambda tgts, root=None, deadline_s=None,
                   slots=None, tier=pod.WIDE: dict(
                       accept_mod.VACUOUS, concurrency=1, tier=tier,
                       rc=kw.get("rc", 0), agda_class=kw.get("agda_class")))
        # A23: FOUR values now, the fourth being fact 8, the unresolved count at EXIT.
        # A stub pinned at three unpacks as a ValueError inside `run_acceptance`.
        self.patch(witness_mod, "witness_delta",
                   lambda t, root=None: (kw.get("delta", -2), 1.3, False,
                                         kw.get("open", 0)))
        self.patch(facts_mod, "changed_files_scoped",
                   lambda code, brief, root=None: (list(kw.get("ch", ["a.md"])), []))
        self.patch(facts_mod, "verification_target",
                   lambda ch, code, root=None: [])

    def test_no_change_in_scope_returns_None_under_R7(self):
        self.stub(ch=[])
        self.assertIsNone(accept_mod.run_acceptance(self.T(), self.tmp))

    def test_all_six_held_gives_exit_code_0_and_no_class(self):
        self.stub()
        rec = accept_mod.run_acceptance(self.T(), self.tmp)
        self.assertEqual(rec["facts"]["exit_code"], 0)
        self.assertIsNone(rec["facts"]["error_class"])

    def test_conjunct_5_runs_FIRST_so_a_surface_change_is_never_hidden(self):
        """A3 makes the spec surface undefeatable: an Agda failure must never hide a
        change to the trophy statement."""
        self.stub(c5=False, rc=42, agda_class="unsolved_meta")
        rec = accept_mod.run_acceptance(self.T(), self.tmp)
        self.assertEqual(rec["facts"]["error_class"], "spec_surface")

    def test_each_runner_conjunct_names_its_own_class(self):
        for kw, want in ((dict(delta=3), "obligations_up"),
                         (dict(c3=False), "closure_open"),
                         (dict(c4=False), "unbound_hyp"),
                         (dict(c6=False), "lint")):
            with self.subTest(**kw):
                case = Acceptance("test_all_six_held_gives_exit_code_0_and_no_class")
                case.setUp()
                case.stub(**kw)
                rec = accept_mod.run_acceptance(case.T(), case.tmp)
                self.assertEqual(rec["facts"]["error_class"], want)
                self.assertEqual(rec["facts"]["exit_code"], 1)
                case.doCleanups()

    def test_conjunct_1_carries_AGDA_s_own_exit_code_and_class(self):
        self.stub(rc=42, agda_class="unsolved_meta")
        rec = accept_mod.run_acceptance(self.T(), self.tmp)
        self.assertEqual(rec["facts"]["exit_code"], 42)
        self.assertEqual(rec["facts"]["error_class"], "unsolved_meta")

    def test_a_deadline_needs_no_special_case(self):
        """`r1["rc"]` is None, conjunct 1 fails, `exit_code` is None, and a row keyed on
        `exit_code_absent` matches."""
        self.stub(rc=None, agda_class="timeout")
        rec = accept_mod.run_acceptance(self.T(), self.tmp)
        self.assertIsNone(rec["facts"]["exit_code"])
        self.assertEqual(rec["facts"]["error_class"], "timeout")
        self.assertTrue(table_mod.matches({"exit_code_absent": True}, rec))

    def test_the_measuring_never_stops_early_at_the_first_failure(self):
        """A branch may route on a fact whose conjunct failed, which is how a NO-GO
        reaches a `done` row."""
        self.stub(c5=False, delta=5)
        rec = accept_mod.run_acceptance(self.T(), self.tmp)
        self.assertEqual(rec["facts"]["obligations_delta"], 5)
        self.assertIn(2, rec["conjuncts"])

    def test_the_record_passes_the_corpus_loader(self):
        self.stub()
        rec = accept_mod.run_acceptance(self.T(), self.tmp)
        rec["id"] = "c-1"
        replay_mod.check_record(rec)

    def test_case_4_holds_conjunct_1_VACUOUSLY_and_starts_no_process(self):
        """IT DRIVES THE REAL `conjunct1()`. The stub returns `VACUOUS` whatever it is
        given, so asserting `agda_vacuous` against the stub only read the stub back: it
        could not tell case 4 from a run that started Agda and lied about it.

        `run_agda` becomes a recorder that FAILS the test if it is called. A report-only
        return starts no Agda process, and `concurrency` is 0 rather than 1 so a vacuous
        record can never read as a solo measurement and let `seconds_max` match 0.0 s that
        nothing measured.
        """
        started = []
        self.patch(facts_mod, "run_agda",
                   lambda *a, **kw: started.append(a) or {"rc": 0, "seconds": 9.9})
        r1 = accept_mod.conjunct1([], self.tmp)
        self.assertEqual(started, [])
        self.assertTrue(r1["vacuous"])
        self.assertEqual(r1["seconds"], 0.0)
        self.assertNotEqual(r1["concurrency"], 1)
        vacuous = record(seconds=0.0, concurrency=r1["concurrency"])
        self.assertFalse(table_mod.matches({"seconds_max": 5.0}, vacuous))
        # C-45: the same call with a target DOES start one.
        accept_mod.conjunct1(["src/L/Cardinal.lagda.md"], self.tmp, deadline_s=1)
        self.assertEqual(len(started), 1)

    def test_r4_reads_the_conjuncts_and_costs_no_re_run(self):
        rec = record(conjuncts={1: True, 2: True, 3: True, 4: True, 5: True, 6: True})
        self.assertTrue(accept_mod.r4_holds(rec, {"outcome": "go"}))
        rec["conjuncts"][2] = False
        self.assertFalse(accept_mod.r4_holds(rec, {"outcome": "go"}))
        self.assertTrue(accept_mod.r4_holds(rec, {"outcome": "no-go"}))


# ---------------------------------------------------------------- ledger.py --write


class LedgerWrite(unittest.TestCase):
    """Design section 7.1 row 26: the DONE handler needs a WRITER and not only a reader.

    `--write` was `if mode == "write": mode = "check"` until 2026-08-17, so the handler
    that runs at every close wrote nothing.
    """

    def setUp(self):
        self.dir = tempfile.TemporaryDirectory()
        self.addCleanup(self.dir.cleanup)
        self.tmp = Path(self.dir.name)

    def ledger_file(self, seconds=True, declared=10000):
        text = ["# a comment that must survive the rewrite", "",
                "[ratio]", "# the provenance of the figure below",
                f"ac_baseline_lines = {declared}",
                "ac_baseline_tolerance_lines = 50"]
        if seconds:
            text.append("ac_baseline_seconds_per_line = 0.5")  # synthetic, never the ledger figure
        text += ["", "[basis]", "ac_baseline_lines = 999   # a decoy in another table"]
        p = self.tmp / "ledger.toml"
        p.write_text("\n".join(text) + "\n", encoding="utf-8")
        return p

    def test_it_REFUSES_to_write_half_of_a_measured_pair(self):
        """A rewritten LINES term over an unmeasured SECONDS term is the C-28 class, and
        `validate_ratio_baseline()`'s own docstring names the cure: re-measure both."""
        p = self.ledger_file(seconds=True, declared=10000)
        data = {"ratio": {"ac_baseline_lines": 10000,
                          "ac_baseline_seconds_per_line": 0.5,   # synthetic. NEVER the ledger figure:
                          # a real one here is a DD24 claim outside dev/ledger.toml,
                          # which check-baseline-home.py refuses, and it goes stale.
                          "ac_baseline_tolerance_lines": 50}}
        ledger.derive = lambda t, k, d, f, s: (20000, "a test cone")
        written, refused = ledger.write_declaration(data, [], 0, p)
        self.assertEqual(written, [])
        self.assertEqual(len(refused), 1)
        self.assertIn("ac_baseline_seconds_per_line", refused[0])
        self.assertIn("10000", p.read_text())          # the file is UNTOUCHED

    def test_it_WRITES_a_census_that_is_no_half_of_a_pair(self):
        p = self.ledger_file(seconds=False, declared=10000)
        data = {"ratio": {"ac_baseline_lines": 10000,
                          "ac_baseline_tolerance_lines": 50}}
        ledger.derive = lambda t, k, d, f, s: (20000, "a test cone")
        written, refused = ledger.write_declaration(data, [], 0, p)
        self.assertEqual(refused, [])
        self.assertEqual(len(written), 1)
        text = p.read_text()
        self.assertIn("ac_baseline_lines = 20000", text)
        self.assertIn("# a comment that must survive the rewrite", text)
        self.assertIn("# the provenance of the figure below", text)
        self.assertIn("ac_baseline_lines = 999", text)   # the decoy is untouched

    def test_a_drift_inside_the_guard_s_own_tolerance_writes_NOTHING(self):
        """`--check` refuses only above the tolerance, so `--write` must act only above
        it. Two owners of one word is the defect this repository refuses everywhere."""
        p = self.ledger_file(seconds=False, declared=10000)
        data = {"ratio": {"ac_baseline_lines": 10000,
                          "ac_baseline_tolerance_lines": 50}}
        ledger.derive = lambda t, k, d, f, s: (10040, "a test cone")
        written, refused = ledger.write_declaration(data, [], 0, p)
        self.assertEqual((written, refused), ([], []))
        self.assertIn("ac_baseline_lines = 10000", p.read_text())

    def test_it_NEVER_writes_a_standing_figure(self):
        """`dev/ledger.toml:77-82`: "There is no standing figure in this file and there
        must never be one." A standing figure written into prose was re-quoted unchecked
        for nine dispatches while the tree moved under it.

        THE WRITABLE SET IS WHAT THIS READS. A grep for the sentence that says so passed
        on the COMMENT and would have passed with a standing key in `DERIVED` beneath it,
        so the prose half is gone and the set itself is the test.
        """
        self.assertTrue(ledger.DERIVED)
        for table, key, *_ in ledger.DERIVED:
            self.assertNotIn("standing", key)
            self.assertNotIn("standing", table)

    def test_check_still_exits_0_on_the_real_ledger(self):
        done = subprocess.run(
            [sys.executable, "scripts/measure/ledger.py", "--check"],
            cwd=ROOT, capture_output=True, text=True, timeout=600)
        self.assertEqual(done.returncode, 0, done.stderr)
        self.assertIn("declaration clean", done.stdout)

    def test_write_exits_0_on_the_real_ledger_and_changes_no_byte(self):
        before = (ROOT / "dev" / "ledger.toml").read_bytes()
        done = subprocess.run(
            [sys.executable, "scripts/measure/ledger.py", "--write"],
            cwd=ROOT, capture_output=True, text=True, timeout=600)
        self.assertEqual(done.returncode, 0, done.stderr)
        self.assertEqual((ROOT / "dev" / "ledger.toml").read_bytes(), before)

    def test_the_scalar_rewrite_reads_ONE_table_and_never_a_later_one(self):
        p = self.ledger_file(seconds=False, declared=10000)
        span = ledger._scalar_line(p.read_text(), "basis", "ac_baseline_lines")
        self.assertIsNotNone(span)
        self.assertEqual(span[2], "999")


# ---------------------------------------------------------------- it refuses, never raises


class Refuses(LoopCase):
    """THE LOOP RUNS UNATTENDED, so a traceback stops everything and nobody reads it.

    Every test here feeds one malformed input to one reader and demands a REFUSAL: a
    skipped line, an empty state, a park with a reason, or an exit code. The inputs are
    the three shapes the brief names, and all three are real: `dev/pod/transitions/` and
    `dev/pod/queue.toml` are TRACKED files that any agent may edit, `.pod-state/` survives
    a crash mid-write, and every sibling module runs subprocesses that fail.
    """

    def log(self, *lines):
        p = pod.log_path(root=self.tmp)
        p.parent.mkdir(parents=True, exist_ok=True)
        p.write_text("\n".join(lines) + "\n")

    def test_a_line_whose_seq_is_not_a_number_is_SKIPPED(self):
        """`int("x")` raised inside `replay_log()`, at the TOP of every tick, so one
        hand-edited character in a tracked file stopped the whole loop."""
        self.log(json.dumps({"ts": "2026-08-17T00:00:00Z", "seq": "soon", "task": CODE,
                             "from": None, "to": "READY"}),
                 json.dumps({"ts": "2026-08-17T00:00:01Z", "seq": 2, "task": CODE,
                             "from": None, "to": "READY"}))
        st = pod.replay_log(pod.State(), self.tmp)
        self.assertEqual(st.seq, 2)
        self.assertEqual(st.tasks[CODE].status, pod.READY)

    def test_a_line_that_is_JSON_but_not_an_OBJECT_is_SKIPPED(self):
        self.log("[1, 2, 3]", json.dumps({"ts": "2026-08-17T00:00:01Z", "seq": 4,
                                          "task": CODE, "from": None, "to": "READY"}))
        st = pod.replay_log(pod.State(), self.tmp)
        self.assertEqual(st.seq, 4)

    def test_a_line_whose_state_is_NOT_one_of_the_six_moves_no_task(self):
        """`cmd_status()` formats `status` and `route()` compares it, so a `to` of 5 was
        a `ValueError` waiting in the status table."""
        self.log(json.dumps({"ts": "2026-08-17T00:00:00Z", "seq": 1, "task": CODE,
                             "from": None, "to": "READY"}),
                 json.dumps({"ts": "2026-08-17T00:00:01Z", "seq": 2, "task": CODE,
                             "from": "READY", "to": 5}))
        st = pod.replay_log(pod.State(), self.tmp)
        self.assertEqual(st.tasks[CODE].status, pod.READY)

    def test_a_line_carrying_HALF_a_facts_object_restores_no_record(self):
        """`matches()` INDEXES the six fact keys, so half a record raised `KeyError`
        inside rule (a2)'s `route()`. R7 is the same rule: a partial record is no record.
        """
        self.log(json.dumps({"ts": "2026-08-17T00:00:00Z", "seq": 1, "task": CODE,
                             "from": "CHECKING", "to": "PARKED", "row": None,
                             "facts": {"exit_code": 0}}))
        st = pod.replay_log(pod.State(), self.tmp)
        self.assertIsNone(st.tasks[CODE].record)
        self.write_table([sys_row(when={"exit_code": 0})])
        pod._rule_a2(st, self.tmp)             # it must not raise
        self.assertEqual(st.tasks[CODE].status, pod.PARKED)

    def test_a_WHOLE_facts_object_DOES_restore_the_record(self):
        """C-45: the guard above can also pass, so it is not refusing everything."""
        self.log(json.dumps({"ts": "2026-08-17T00:00:00Z", "seq": 1, "task": CODE,
                             "from": "CHECKING", "to": "PARKED", "row": None,
                             "park_reason": "no-match",
                             "facts": record()["facts"]}))
        st = pod.replay_log(pod.State(), self.tmp)
        self.assertIsNotNone(st.tasks[CODE].record)
        self.give_scene()
        self.write_table([sys_row(when={"exit_code": 0})])
        pod._rule_a2(st, self.tmp)
        self.assertEqual(st.tasks[CODE].status, pod.CHECKING)

    def test_a_record_with_a_missing_fact_ROUTES_TO_NOTHING(self):
        self.write_table([sys_row(when={"exit_code": 0})])
        rec = record()
        del rec["facts"]["changed_files"]
        self.assertEqual(pod._route(rec, self.tmp), (None, None))

    def test_a_state_file_that_is_not_an_object_gives_an_EMPTY_state(self):
        p = self.tmp / ".pod-state" / "state.json"
        p.write_text('["not", "a", "state"]')
        st = pod.load_state(p)
        self.assertEqual((st.seq, st.tasks), (0, {}))

    def test_a_state_file_with_a_non_numeric_seq_reads_seq_ZERO(self):
        p = self.tmp / ".pod-state" / "state.json"
        p.write_text(json.dumps({"version": 1, "seq": "many", "tasks": {}}))
        self.assertEqual(pod.load_state(p).seq, 0)

    def test_a_queue_entry_that_is_not_a_TABLE_is_skipped(self):
        (self.tmp / "dev" / "pod" / "queue.toml").write_text('task = ["a string"]\n')
        st = pod.State()
        pod._rule_a1(st, self.tmp)
        self.assertEqual(st.tasks, {})

    def test_a_queue_file_that_does_not_parse_reads_as_EMPTY(self):
        (self.tmp / "dev" / "pod" / "queue.toml").write_text("[[task]\ncode = \n")
        self.assertEqual(pod.queue_entries(self.tmp / "dev" / "pod" / "queue.toml"), [])

    def test_pod_status_prints_a_task_whose_fields_are_the_wrong_TYPE(self):
        """`f"{x:9s}"` raises on a number and `f"{x:<3d}"` raises on a string, so the
        status table was one hand-edited character away from a traceback."""
        st = pod.State()
        st.tasks[CODE] = pod.Task(CODE, status=pod.READY, attempt="two", row=7,
                                  role=None, park_reason=3, tier="enormous")
        pod.save_state(st, self.tmp / ".pod-state" / "state.json")
        self.assertEqual(pod.cmd_status([]), 0)

    def test_an_acceptance_runner_that_RAISES_parks_the_task_under_R7(self):
        """`witness_delta()` raises BY DESIGN when the task carries no `obl_before`, and a
        task folded from a log whose dispatch line was lost carries exactly that. The tick
        used to end in a traceback with the task frozen in CHECKING."""
        def boom(t, root=None):
            raise ValueError("the task carries no obl_before")
        self.patch(accept_mod, "run_acceptance", boom)
        st = pod.State()
        st.tasks[CODE] = t = pod.Task(CODE, status=pod.RETURNED,
                                      brief=f"agents/tasks/{DIR}/{CODE}.md")
        self.assertIs(pod._rule_c(st, self.tmp), pod.CONTINUE)
        self.assertEqual(t.status, pod.PARKED)
        self.assertEqual(t.park_reason, "no-change")
        self.assertIn("obl_before", self.lines()[-1]["why"])

    def test_a_preflight_that_RAISES_parks_the_brief_and_not_the_loop(self):
        def boom(brief, root=None, show=True, **kw):
            raise OSError("check-closure.py is gone")
        self.patch(preflight_mod, "preflight", boom)
        st = pod.State()
        st.tasks[CODE] = t = pod.Task(CODE, status=pod.READY,
                                      brief=f"agents/tasks/{DIR}/{CODE}.md")
        pod._rule_f(st, self.tmp)
        self.assertEqual(t.park_reason, "preflight:P0")
        self.assertIn("check-closure.py is gone", self.lines()[-1]["detail"][0])

    def test_an_EMPTY_refusal_string_still_names_a_check_id(self):
        """Rule (a2) branches on the `preflight:` prefix, so `"".split()[0]` must never
        run on the unhappy path."""
        self.patch(preflight_mod, "preflight",
                   lambda brief, root=None, show=True, **kw: [""])
        st = pod.State()
        st.tasks[CODE] = t = pod.Task(CODE, status=pod.READY,
                                      brief=f"agents/tasks/{DIR}/{CODE}.md")
        pod._rule_f(st, self.tmp)
        self.assertEqual(t.park_reason, "preflight:P?")

    def test_an_admission_that_RAISES_parks_and_writes_no_row(self):
        def boom(code, brief):
            raise TypeError("a branch value is not a table")
        self.patch(table_mod, "admit_rows", boom)
        st = pod.State()
        st.tasks[CODE] = t = pod.Task(CODE, status=pod.READY,
                                      brief=f"agents/tasks/{DIR}/{CODE}.md")
        pod._rule_f(st, self.tmp)
        self.assertEqual(t.park_reason, "admission")
        self.assertEqual(table_mod.load_table(
            self.tmp / "dev" / "pod" / "table.toml"), [])

    def test_a_fact_3_dispatch_point_that_RAISES_refuses_the_dispatch(self):
        """Fact 3 needs BOTH ends: without `obl_before` the return can never be measured,
        so the program refuses at the point it knows and never sends the worker."""
        def boom(t, root=None):
            raise tomllib.TOMLDecodeError("the obligation list does not parse", "", 0)
        self.patch(witness_mod, "witness_unresolved", boom)
        st = pod.State()
        st.tasks[CODE] = t = pod.Task(CODE, status=pod.READY,
                                      brief=f"agents/tasks/{DIR}/{CODE}.md")
        pod._rule_f(st, self.tmp)
        self.assertEqual(t.park_reason, "launch")
        self.assertEqual(self.calls["launch"], [])

    def test_a_review_brief_that_cannot_be_written_parks_rather_than_dispatching(self):
        self.patch(pod, "launch", REAL_LAUNCH)
        self.patch(pod, "review_brief", lambda t, slot, root=None: None)
        st = pod.State()
        st.tasks[CODE] = t = pod.Task(CODE, status=pod.READY, attempt=2,
                                      brief=f"agents/tasks/{DIR}/{CODE}.md")
        pod._rule_f(st, self.tmp)
        self.assertEqual(t.park_reason, "launch")

    def test_a_census_that_RAISES_reads_as_BLIND_and_refuses(self):
        """D12: admitting on a blind sensor is the wrong direction."""
        class Broken:
            @staticmethod
            def agda_pileup():
                raise OSError("ps is gone")
        self.patch(facts_mod, "launcher", lambda: Broken)
        total, per_parent, blind = pod.agda_pileup()
        self.assertEqual((total, per_parent), (0, {}))
        self.assertIn("BLIND", blind)
        self.assertFalse(REAL_ADMITS(pod.State(), pod.Task("X", agda=True)))

    def test_a_non_numeric_pid_kills_nothing_and_returns_False(self):
        self.assertFalse(REAL_KILL("not-a-pid"))
        self.assertFalse(REAL_KILL(None))
        self.assertFalse(REAL_KILL(0))

    def test_a_proposal_row_that_is_not_a_TABLE_is_one_refusal_line(self):
        """A PROPOSAL IS UNTRUSTED TEXT: the maintainer model wrote it, and `dict(r)` on a
        string raises where `check_row()` never runs."""
        self.patch(facts_mod, "_status_paths",
                   lambda root: ["dev/pod/proposals/x.toml"])
        (self.tmp / "dev" / "pod" / "proposals" / "x.toml").write_text(
            'row = ["not a table"]\n')
        st = pod.State()
        pod.harvest_batch(st, self.tmp)
        line = [x for x in self.lines() if x.get("event") == "batch"][-1]
        self.assertEqual(line["result"], "refused")

    def test_a_digest_that_renames_a_key_leaves_the_batch_brief_readable(self):
        """The whole formatting sits inside the guard, and not only the call: a `KeyError`
        in the f-string below it ran on every tick."""
        class Broken:
            @staticmethod
            def maintainer_inputs(root):
                return {"no_match": [], "shadowed": [], "fallout": []}   # no `hours`
        sys.modules["digest"] = Broken
        self.addCleanup(sys.modules.pop, "digest", None)
        out = pod.batch_lists(self.tmp)
        self.assertTrue(any("UNAVAILABLE" in x for x in out))

    def test_an_unexpected_raise_exits_1_with_a_message_and_no_traceback(self):
        """The unattended backstop. One line naming the exception beats a traceback that
        nobody is awake to read, and a supervisor still reads the exit code."""
        def boom(argv):
            raise RuntimeError("something nobody planned for")
        self.patch(pod, "COMMANDS", dict(pod.COMMANDS, tick=boom))
        self.assertEqual(pod.main(["tick"]), 1)

    def test_a_refusal_with_a_reason_exits_1_and_a_usage_error_exits_2(self):
        """The two codes name different readers, so they are not one code."""
        def refuse(argv):
            raise pod.PodError("dev/pod/heads.toml carries no [limits]")
        self.patch(pod, "COMMANDS", dict(pod.COMMANDS, tick=refuse))
        self.assertEqual(pod.main(["tick"]), 1)
        self.assertEqual(pod.main([]), 2)
        self.assertEqual(pod.main(["fly"]), 2)


# ---------------------------------------------------------------- the subcommands


class Commands(LoopCase):
    """`pod.py` is the program and nothing else runs it."""

    #: The five section 5.0 names. `maintainer` joined them on 2026-08-19.
    RULED = ("resume", "run", "status", "stop", "tick")

    def test_every_ruled_subcommand_is_still_there(self):
        """**THIS PINNED THE WHOLE SET BY EQUALITY AND WENT RED FOR AN ADDITION.** It is
        the seventh snapshot of the day: the set is a thing the program is designed to
        grow, and what must hold is that nothing RULED disappears."""
        for name in self.RULED:
            self.assertIn(name, pod.COMMANDS, name)

    def test_every_subcommand_is_callable_and_named_in_the_usage_text(self):
        """The other direction, and it is the one that catches a command nobody can find:
        `main()` prints the module docstring for an unknown name, so a subcommand the
        docstring does not name is one no reader is told about."""
        doc = pod.__doc__ or ""
        for name, fn in pod.COMMANDS.items():
            self.assertTrue(callable(fn), name)
            self.assertIn(name, doc, f"`{name}` is a subcommand the usage text omits")

    def test_status_writes_nothing(self):
        self.queue({"code": CODE, "brief": f"agents/tasks/{DIR}/{CODE}.md"})
        self.tick()
        before = sorted((p, p.stat().st_mtime) for p in self.tmp.rglob("*")
                        if p.is_file())
        pod.cmd_status([])
        after = sorted((p, p.stat().st_mtime) for p in self.tmp.rglob("*")
                       if p.is_file())
        self.assertEqual(before, after)

    def test_resume_clears_the_stopped_file_and_re_evaluates_every_park(self):
        (self.tmp / ".pod-state" / "STOPPED").touch()
        st = pod.State()
        st.tasks[CODE] = pod.Task(CODE, brief=f"agents/tasks/{DIR}/{CODE}.md",
                                  status=pod.PARKED, park_reason="preflight:P1",
                                  parked_at=0.0)
        pod.save_state(st, self.tmp / ".pod-state" / "state.json")
        self.assertEqual(pod.cmd_resume(["--once"]), 0)
        self.assertFalse((self.tmp / ".pod-state" / "STOPPED").exists())
        self.assertEqual(pod.load_state().tasks[CODE].status, pod.READY)

    def test_retry_takes_the_codes_it_is_given_and_leaves_the_rest_parked(self):
        """**THE SEVEN PARKED TASKS DID NOT ALL WANT THE SAME THING.** MEASURED
        2026-08-19: three met the coder vendor's quota and never ran, so a re-run is the
        only honest answer, while four had already delivered and were stuck only because
        their records predate fact 8, where a re-run buys a bookkeeping close with agent
        time. A bare `--retry` still takes every park, for a cause that really is global.
        """
        (self.tmp / ".pod-state" / "STOPPED").touch()
        st = pod.State()
        for code in ("LJ-1.801", "LJ-1.802", "LJ-1.803"):
            st.tasks[code] = pod.Task(code, status=pod.PARKED,
                                      park_reason="no-change", parked_at=0.0)
        pod.save_state(st, self.tmp / ".pod-state" / "state.json")
        self.assertEqual(pod.cmd_resume(["--retry", "LJ-1.802", "--once"]), 0)
        got = pod.load_state().tasks
        self.assertEqual(got["LJ-1.802"].status, pod.READY, "the named code re-ran")
        self.assertEqual(got["LJ-1.801"].status, pod.PARKED, "an unnamed code stayed")
        self.assertEqual(got["LJ-1.803"].status, pod.PARKED, "an unnamed code stayed")

    def test_a_bare_retry_takes_every_park(self):
        (self.tmp / ".pod-state" / "STOPPED").touch()
        st = pod.State()
        for code in ("LJ-1.801", "LJ-1.802"):
            st.tasks[code] = pod.Task(code, status=pod.PARKED,
                                      park_reason="no-change", parked_at=0.0)
        pod.save_state(st, self.tmp / ".pod-state" / "state.json")
        self.assertEqual(pod.cmd_resume(["--retry", "--once"]), 0)
        got = pod.load_state().tasks
        self.assertEqual({c: got[c].status for c in ("LJ-1.801", "LJ-1.802")},
                         {"LJ-1.801": pod.READY, "LJ-1.802": pod.READY})

    def test_tick_returns_1_when_the_loop_stopped(self):
        st = pod.State()
        for i in range(pod._limits()["parked_max"]):     # the limit, never a literal
            st.tasks[f"X{i}"] = pod.Task(f"X{i}", status=pod.PARKED,
                                         park_reason="no-match")
        pod.save_state(st, self.tmp / ".pod-state" / "state.json")
        self.assertEqual(pod.cmd_tick([]), 1)

    def test_stop_writes_the_flag_and_commits_by_explicit_path(self):
        """R8 commits by EXPLICIT PATH and the program NEVER pushes: one push is one CI
        run and one deploy."""
        self.assertEqual(pod.cmd_stop([]), 0)
        self.assertTrue((self.tmp / ".pod-state" / "STOPPED").exists())
        self.assertEqual(len(self.calls["commit"]), 1)

    def test_stop_soft_writes_DRAINING_and_does_not_STOPPED(self):
        self.assertEqual(pod.cmd_stop(["--soft"]), 0)
        self.assertTrue((self.tmp / ".pod-state" / "DRAINING").exists())
        self.assertFalse((self.tmp / ".pod-state" / "STOPPED").exists())
        self.assertEqual(len(self.calls["commit"]), 0)

    def test_an_unknown_subcommand_is_a_usage_error(self):
        self.assertEqual(pod.main(["fly"]), 2)



class MaintainerScopeAgainstRealGit(unittest.TestCase):
    """R15 against a REAL `git status`, because every other scope test stubs the sensor.

    WHY THIS EXISTS. A blank agent ran one production-faithful tick on 2026-08-18 and
    measured the failure the suite could not see: batch 1 admitted, batch 2 refused on
    `scope`, naming three paths the PROGRAM writes. `maintainer_scope_ok()`'s own
    docstring had named that hazard and excluded two of the five paths. The other tests
    patch `facts_mod._status_paths` with a hand-written list, so none of them could ever
    have caught it. **This one calls git.**
    """

    def test_the_program_s_own_writes_are_not_the_model_s(self):
        import subprocess, tempfile, os
        with tempfile.TemporaryDirectory() as d:
            root = pathlib.Path(d)
            subprocess.run(["git", "init", "-q"], cwd=root, check=True)
            subprocess.run(["git", "config", "user.email", "t@t"], cwd=root, check=True)
            subprocess.run(["git", "config", "user.name", "t"], cwd=root, check=True)
            (root / "seed").write_text("x")
            subprocess.run(["git", "add", "-A"], cwd=root, check=True)
            subprocess.run(["git", "commit", "-qm", "seed"], cwd=root, check=True)
            # Exactly what one tick leaves behind, and the program wrote every one.
            for rel in ("dev/pod/transitions/2026-08.jsonl",
                        "agents/tasks/LJ-1-386/.pod",
                        "agents/tasks/POD-BATCH/20260818-000000.md",
                        ".pod-state/state.json",
                        "dev/pod/table.toml"):
                p = root / rel
                p.parent.mkdir(parents=True, exist_ok=True)
                p.write_text("written by the program\n")
            prop = "dev/pod/proposals/20260818-000000.toml"
            (root / prop).parent.mkdir(parents=True, exist_ok=True)
            (root / prop).write_text("# the model's one write\n")
            ok, bad = pod.maintainer_scope_ok(root=root, proposal=prop)
            self.assertTrue(ok, f"R15 counted the program's own writes as the model's: {bad}")
            # AND IT STILL REFUSES A REAL FOREIGN WRITE, or the fix would be a hole.
            (root / "dev" / "PLAN.md").write_text("the model edited a live document\n")
            ok2, bad2 = pod.maintainer_scope_ok(root=root, proposal=prop)
            self.assertFalse(ok2, "R15 must refuse a write outside the proposal file")
            self.assertIn("dev/PLAN.md", bad2)



class SideScopeReport(LoopCase):
    """Item 10 against a dirty-set delta that is not authorship.

    MEASURED 2026-08-20 on POD-REFILL-20260820-110248: the head never started
    working, `final.md` was never written, and the notice named `dev/pod/table.toml`
    (`expire_rows`) plus three spec-surface files the owner was editing.
    """

    def test_expire_rows_dirty_table_is_not_the_refill(self):
        self.patch(facts_mod, "_status_paths",
                   lambda root: ["dev/pod/table.toml", "dev/pod/queue.toml",
                                 "scripts/pod/check-spec-surface.py"])
        st = pod.State()
        st.tasks["LJ-1.404"] = pod.Task("LJ-1.404", status=pod.DONE)
        got = pod.side_scope_report("POD-REFILL", before=[], st=st, root=self.tmp)
        self.assertNotIn("dev/pod/table.toml", got)
        self.assertNotIn("dev/pod/queue.toml", got)
        self.assertIn("scripts/pod/check-spec-surface.py", got)

    def test_a_never_started_dispatch_wrote_nothing(self):
        log = self.tmp / "never.log"
        log.write_text(
            "HERDR agent never started working; pane w7:p6R kept for forensics\n")
        row = {"log": str(log),
               "final": str(self.tmp / "POD-REFILL-missing-final.md")}
        self.assertTrue(pod._never_started_working(row))
        self.patch(facts_mod, "_status_paths",
                   lambda root: ["scripts/pod/check-spec-surface.py",
                                 "scripts/README.md",
                                 "scripts/tests/test_pod_gates.py",
                                 "dev/pod/table.toml"])
        got = pod.side_stray_paths("POD-REFILL", before=[], st=pod.State(),
                                   row=row, root=self.tmp)
        self.assertEqual(got, [])

    def test_a_missing_log_is_not_treated_as_never_started(self):
        self.assertFalse(pod._never_started_working({"log": str(self.tmp / "nope.log")}))
        self.assertFalse(pod._never_started_working({}))

    def test_a_direction_archive_and_the_plan_are_not_the_refill(self):
        """MEASURED 2026-08-20 on POD-REFILL-20260820-140414."""
        self.patch(facts_mod, "_status_paths",
                   lambda root: ["archive/dev/direction/20260820-142326.md",
                                 "dev/pod/screen.toml",
                                 "dev/pod/rulings.toml",
                                 "dev/pod/direction.md",
                                 "scripts/pod/check-spec-surface.py"])
        got = pod.side_scope_report("POD-REFILL", before=[], st=pod.State(),
                                    root=self.tmp)
        self.assertNotIn("archive/dev/direction/20260820-142326.md", got)
        self.assertNotIn("dev/pod/screen.toml", got)
        self.assertNotIn("dev/pod/rulings.toml", got)
        self.assertNotIn("dev/pod/direction.md", got)
        self.assertIn("scripts/pod/check-spec-surface.py", got)

    def test_a_journal_archive_is_not_the_refill(self):
        """MEASURED 2026-08-20 on POD-REFILL-20260820-152340."""
        self.patch(facts_mod, "_status_paths",
                   lambda root: ["agents/README.md",
                                 "archive/dev/JOURNAL.md",
                                 "archive/dev/README.md",
                                 "dev/README.md",
                                 "dev/build-manifest.toml",
                                 "dev/memos/LJ-4-pod-program-design.md",
                                 "dev/pod/instructions/mathematician.md",
                                 "dev/pod/instructions/mathematician_adversarial.md",
                                 "scripts/pod/check-spec-surface.py"])
        got = pod.side_scope_report("POD-REFILL", before=[], st=pod.State(),
                                    root=self.tmp)
        self.assertEqual(got, ["scripts/pod/check-spec-surface.py"])

    def test_a_spec_surface_commit_is_not_the_refill(self):
        """MEASURED 2026-08-20 on POD-REFILL-20260820-202416: Makefile and
        spec-surface.toml. The transcript names only queue.toml and four briefs."""
        self.patch(facts_mod, "_status_paths",
                   lambda root: ["Makefile",
                                 "dev/pod/spec-surface.toml",
                                 "scripts/pod/check-spec-surface.py"])
        got = pod.side_scope_report("POD-REFILL", before=[], st=pod.State(),
                                    root=self.tmp)
        self.assertNotIn("Makefile", got)
        self.assertNotIn("dev/pod/spec-surface.toml", got)
        self.assertEqual(got, ["scripts/pod/check-spec-surface.py"])


class StandingRefillBrief(unittest.TestCase):
    """The standing refill brief names the live screen, never the archived plan.

    MEASURED 2026-08-20 on POD-REFILL-20260820-162432: the head's first tool
    call was that `dev/PLAN.md` does not exist (transcript
    `.pod-state/logs/POD-REFILL-20260820-162432-final.md:140`). PLAN.md was
    archived the same day as `archive/dev/PLAN-archived.md`. `AGENTS.md`
    already names `dev/pod/screen.toml`. The standing brief is the one
    document the program never rewrites, so it drifted.
    """

    def test_it_names_the_live_screen_and_not_the_archived_plan(self):
        text = (ROOT / "agents" / "tasks" / "POD-REFILL" / "POD-REFILL.md").read_text(
            encoding="utf-8")
        self.assertNotIn("dev/PLAN.md", text)
        self.assertIn("dev/pod/screen.toml", text)
        self.assertNotIn("L9-pod-program-design.md", text)
        self.assertIn("LJ-4-pod-program-design.md", text)


class LawsBundleProducer(LoopCase):
    """R17's producer is `scripts/pod/rules.py`.

    MEASURED 2026-08-20 on POD-REFILL-20260820-140414: `laws_bundle()` still
    opened `scripts/dispatch/rules.py`, which does not exist, so the injector
    returned None and every queued brief carried a handwritten LAWS block.
    """

    def test_the_producer_is_the_pod_rules_module(self):
        live = self.tmp / "scripts" / "pod" / "rules.py"
        live.parent.mkdir(parents=True, exist_ok=True)
        live.write_text(
            "import argparse\n"
            "def kind_for_scope(paths):\n"
            "    return 'probe'\n"
            "if __name__ == '__main__':\n"
            "    p = argparse.ArgumentParser()\n"
            "    p.add_argument('--for', dest='kind')\n"
            "    args = p.parse_args()\n"
            "    print(f'MANDATORY for kind `{args.kind}` (fixture):')\n",
            encoding="utf-8")
        stale = self.tmp / "scripts" / "dispatch" / "rules.py"
        stale.parent.mkdir(parents=True, exist_ok=True)
        stale.write_text(
            "def kind_for_scope(paths):\n"
            "    return 'probe'\n"
            "if __name__ == '__main__':\n"
            "    print('STALE DISPATCH PATH')\n",
            encoding="utf-8")
        got = pod.laws_bundle(["agents/tasks/x/Probe.agda"], root=self.tmp)
        self.assertIsNotNone(got)
        self.assertTrue(got.startswith("MANDATORY for kind"), got)
        self.assertNotIn("STALE", got)

    def test_a_missing_producer_writes_no_block(self):
        got = pod.laws_bundle(["agents/tasks/x/Probe.agda"], root=self.tmp)
        self.assertIsNone(got)


class RetrievalReadsTheWorktree(LoopCase):
    """Isolation: the miss signal reads the report the worker wrote.

    MEASURED 2026-08-20 on LJ-1.406: acceptance ran in the worktree (conjunct 6
    held), then `emit_retrieval` opened the MAIN brief, found no report, and
    recorded `used: 0` / `offered: 9`. Salvage copied
    `agents/tasks/LJ-1-406/lj-1.406-report.md` after that line. 407, 408 and 409
    closed the same hour with the same `used: 0` shape.
    """

    ARCHIVE_BLOCK = (
        "## ARCHIVE (program-generated, do not edit)\n\n"
        "Corpus search over archive/dev:\n"
        "- CANDIDATE archive/dev/TASKS-archived.md  (score 1.000)\n"
    )
    REPORT = (
        "# Report\n\n"
        "## ARCHIVE USED\n\n"
        "- `archive/dev/TASKS-archived.md:80`: read it.\n"
    )

    def _write_brief(self, where):
        where.mkdir(parents=True, exist_ok=True)
        brief = where / f"{CODE}.md"
        brief.write_text("# fixture\n\n" + self.ARCHIVE_BLOCK, encoding="utf-8")
        return brief

    def _retrieval_lines(self):
        out = []
        trans = self.tmp / "dev" / "pod" / "transitions"
        for p in sorted(trans.glob("*.jsonl")):
            for line in p.read_text(encoding="utf-8").splitlines():
                if not line.strip():
                    continue
                rec = json.loads(line)
                if rec.get("event") == "retrieval":
                    out.append(rec)
        return out

    def test_a_worktree_report_is_what_the_signal_counts(self):
        home = self.tmp / "agents" / "tasks" / DIR
        self._write_brief(home)
        report = home / f"{CODE.lower()}-report.md"
        if report.exists():
            report.unlink()
        wt_home = self.tmp / ".pod-state" / "worktrees" / DIR / "agents" / "tasks" / DIR
        self._write_brief(wt_home)
        (wt_home / f"{CODE.lower()}-report.md").write_text(self.REPORT, encoding="utf-8")
        t = pod.Task(CODE, brief=f"agents/tasks/{DIR}/{CODE}.md")
        self.assertTrue(pod.emit_retrieval(pod.State(), t, root=self.tmp))
        lines = self._retrieval_lines()
        self.assertEqual(len(lines), 1, lines)
        self.assertEqual(lines[0]["used"], 1, lines[0])
        self.assertEqual(lines[0]["offered"], 1, lines[0])

    def test_without_a_worktree_the_main_report_still_counts(self):
        home = self.tmp / "agents" / "tasks" / DIR
        self._write_brief(home)
        (home / f"{CODE.lower()}-report.md").write_text(self.REPORT, encoding="utf-8")
        t = pod.Task(CODE, brief=f"agents/tasks/{DIR}/{CODE}.md")
        self.assertTrue(pod.emit_retrieval(pod.State(), t, root=self.tmp))
        lines = self._retrieval_lines()
        self.assertEqual(len(lines), 1, lines)
        self.assertEqual(lines[0]["used"], 1, lines[0])


class InjectSurveyReplacesHandwritten(LoopCase):
    """R10 writes the program-generated ARCHIVE block even when a heading exists.

    MEASURED 2026-08-20 on LJ-1.417: the refill wrote `## ARCHIVE` with `NO HIT`
    and no `(program-generated)` marker. `inject_survey` saw the heading and
    skipped. Conjunct 6 then FAILED (`lint`) because the duty block was never
    in front of the coder. `sys-lint-accept` re-dispatched the same brief.
    """

    def setUp(self):
        super().setUp()
        self.patch(pod, "inject_survey", REAL_INJECT_SURVEY)

    def test_a_handwritten_archive_is_replaced(self):
        brief = self.tmp / "agents" / "tasks" / DIR / f"{CODE}.md"
        brief.parent.mkdir(parents=True, exist_ok=True)
        brief.write_text(
            "# fixture\n\n## THE OBLIGATION\n\ngo\n\n"
            "## ARCHIVE\n\nNO HIT.\n\n"
            "## LITERATURE\n\nread digest\n",
            encoding="utf-8")
        fake = types.SimpleNamespace(
            ARCHIVE_SCOPE=["archive/src"],
            LITERATURE_SCOPE=["dev/literature"],
            build_query=lambda *a, **k: "q",
            goal_text=lambda p: "g",
            candidate_block=lambda heading, query, scope, k=5: (
                f"## {heading} (program-generated, do not edit)\n\n"
                f"Corpus search over {', '.join(scope)}: NO HIT\n\n"
                "**ANSWER THIS BLOCK**\n"),
        )
        prev = sys.modules.get("retrieve")
        sys.modules["retrieve"] = fake
        self.patch(pod.witness_mod, "obligations_of", lambda p: [])
        try:
            self.assertTrue(pod.inject_survey(brief, root=self.tmp))
        finally:
            if prev is None:
                sys.modules.pop("retrieve", None)
            else:
                sys.modules["retrieve"] = prev
        text = brief.read_text(encoding="utf-8")
        self.assertIn("## ARCHIVE (program-generated, do not edit)", text)
        self.assertIn("## LITERATURE (program-generated, do not edit)", text)
        self.assertIn("**ANSWER THIS BLOCK**", text)
        self.assertEqual(text.count("## ARCHIVE"), 1)
        self.assertEqual(text.count("## LITERATURE"), 1)

    def test_a_program_generated_block_is_left_alone(self):
        brief = self.tmp / "agents" / "tasks" / DIR / f"{CODE}.md"
        brief.parent.mkdir(parents=True, exist_ok=True)
        original = (
            "# fixture\n\n"
            "## ARCHIVE (program-generated, do not edit)\n\n"
            "- CANDIDATE archive/dev/TASKS-archived.md  (score 1.000)\n\n"
            "## LITERATURE (program-generated, do not edit)\n\n"
            "Corpus search over dev/literature: NO HIT\n")
        brief.write_text(original, encoding="utf-8")
        pod.inject_survey(brief, root=self.tmp)
        text = brief.read_text(encoding="utf-8")
        self.assertIn("- CANDIDATE archive/dev/TASKS-archived.md  (score 1.000)", text)
        self.assertIn("Corpus search over dev/literature: NO HIT", text)
        self.assertEqual(text.count("## ARCHIVE"), 1)
        self.assertEqual(text.count("## LITERATURE"), 1)


class SettledProposalIsRetired(unittest.TestCase):
    """D2: a settled proposal must never be judged twice.

    MEASURED by a blank agent on 2026-08-18: only the ADMIT path renamed anything, so a
    `parse`, `scope`, `empty`, `refused` or `reject` proposal stayed where it was and
    every tick re-read it and wrote another line into the TRACKED log. Three runs, three
    identical lines. At `tick_seconds = 30` that is 2,880 lines a day, growing the
    repository without bound and burying the lines that mean something.
    """

    def test_one_settled_proposal_writes_one_line_however_many_ticks_run(self):
        import tempfile
        for verdict, body in (("empty", "queue = []\n"),
                              ("parse", "this is not TOML {{{\n")):
            with self.subTest(verdict=verdict), tempfile.TemporaryDirectory() as d:
                root = pathlib.Path(d)
                props = root / "dev" / "pod" / "proposals"
                props.mkdir(parents=True)
                f = props / "20260818-000000.toml"
                f.write_text(body)
                seen = []
                st = pod.State()
                old_emit, old_scope = pod.emit_event, pod.maintainer_scope_ok
                pod.emit_event = lambda st, kind, root=None, **kw: (seen.append(kw), {})[1]
                pod.maintainer_scope_ok = lambda r, rel: (True, [])
                try:
                    for _ in range(3):
                        pod.harvest_batch(st, root=root)
                finally:
                    pod.emit_event, pod.maintainer_scope_ok = old_emit, old_scope
                self.assertEqual(len(seen), 1,
                                 f"{verdict}: judged {len(seen)} times, not once")
                self.assertFalse(f.exists(), "the settled proposal was not retired")
                self.assertTrue((props / f"20260818-000000.toml.{verdict}").is_file(),
                                f"expected the .{verdict} suffix")


class EveryDispatchCarriesItsRules(unittest.TestCase):
    """No worker is ever launched without `AGENTS.md` and its slot file ahead of the brief.

    MEASURED 2026-08-18, and it is why this reads the SOURCE rather than a behaviour. The
    slot files reached nobody for the whole life of the cutover: the launcher cat'd the
    brief alone. The repair wired `_rule_f` and left the OTHER TWO dispatch points
    untouched, so the maintainer and the refill still launched with no rules. The owner
    found that by asking how the maintainer's own head config takes effect.

    **THE COUNT IS NECESSARY AND IT IS NOT SUFFICIENT, and the second half of that
    sentence was learned on 2026-08-18.** This test stayed green while rule (f), the
    dispatch point every real task passes, sent `preamble_for(t.head_slot)` one
    statement after `t.head_slot = None`. The call text carried the word `preamble`,
    so the count was satisfied and the worker still got no slot file. The excuse
    written here was that a behavioural test「would need three fixtures」. It needs
    one, and `PreambleAndProviderReachTheWorker` below is it.
    """

    def test_every_launch_call_passes_a_preamble(self):
        src = pathlib.Path("scripts/pod/pod.py").read_text(encoding="utf-8")
        calls = []
        for i in range(len(src)):
            if not src.startswith("mod.launch(", i):
                continue
            depth, j = 0, i + len("mod.launch")
            while j < len(src):
                if src[j] == "(":
                    depth += 1
                elif src[j] == ")":
                    depth -= 1
                    if depth == 0:
                        break
                j += 1
            calls.append(src[i:j + 1])
        self.assertGreaterEqual(len(calls), 3, "the dispatch points moved; re-read pod.py")
        missing = [c.split("(", 1)[1][:60] for c in calls if "preamble" not in c]
        self.assertEqual(missing, [],
                         f"{len(missing)} dispatch point(s) launch a worker with no rules")


class PreambleAndProviderReachTheWorker(unittest.TestCase):
    """What `launch()` HANDS the launcher, measured through a stub rather than read.

    Two defects hid behind source-reading tests until 2026-08-18. `_rule_f` nulled
    `t.head_slot` before passing it to `preamble_for`, so every real dispatch lost its
    slot file; and the provider was a module constant, so both `glm-5.3` heads
    dispatched on `deepseek`. The second is silent by construction: `pi` warns, echoes
    the prompt, and exits `done` in ten seconds having written nothing.
    """

    def _capture(self, role, st=None, task=None, expect_call=True):
        calls = []

        class _Stub:
            HARNESS = ""

            @staticmethod
            def launch(*a, **kw):
                calls.append(kw)
                return 4242

        # **`make_worktree()` IS A FILESYSTEM SIDE EFFECT ON THIS PATH, and this test
        # drives `pod.launch()` with the REAL ROOT because it is checking the argv the
        # launcher receives.** MEASURED 2026-08-19, the hour isolation was turned on: the
        # suite left a real git worktree at `.pod-state/worktrees/LJ-1-999` in the
        # repository every time it ran. A test that means to inspect one call must not
        # perform the other's side effect.
        real = pod.facts_mod.launcher
        real_wt = pod.make_worktree
        pod.facts_mod.launcher = lambda: _Stub
        pod.make_worktree = lambda code, root=None: None
        try:
            t = task or types.SimpleNamespace(
                code="LJ-1.999", agda=False, tier="wide", head_slot=None, role=None,
                model=None, effort=None, harness=None, sandbox=None)
            pod.launch(t, "agents/tasks/LJ-1-999/LJ-1.999.md", role, ROOT, st)
        finally:
            pod.facts_mod.launcher = real
            pod.make_worktree = real_wt
        if not expect_call:
            self.assertEqual(calls, [], "a refused dispatch reached the launcher")
            return None
        self.assertEqual(len(calls), 1, "the stub was not reached")
        # THE TASK ITSELF IS PART OF THE MEASUREMENT SINCE A27: `launch()` writes the
        # model it CHOSE onto it, which is the field the transition log records (AD26).
        calls[0]["_task"] = t
        return calls[0]

    def test_the_worker_gets_agents_md_and_its_own_slot_file(self):
        for role in sorted(heads_mod.load_heads()["heads"]):
            with self.subTest(role=role):
                names = [pathlib.Path(f).name for f in self._capture(role)["preamble"]]
                # THE SLOT FILE IS THE ROLE'S AND NEVER THE MODEL'S. A27 lets one slot
                # carry two models; the preamble is per SLOT, so the file list below is
                # the same whichever model `pick_head_config()` chose.
                # THE SLOT FILE IS FIRST, then the shared Boundary. Owner 2026-08-20.
                # THE DIRECTION IS LAST, closest to the brief. Owner's ruling of
                # 2026-08-18 gives it to all five slots. The screen sits in front of
                # it. This list is exact rather than a containment check.
                self.assertEqual(names, [f"{role}.md", "AGENTS.md", "screen.toml",
                                         "direction.md"],
                                 f"a {role} worker was launched with {names}")

    @unittest.skip("owner 2026-08-22: grok-4.6 now sits first in both critic arrays "
                    "and claude-opus-5 is coder's only entry, so an idle pod's default "
                    "pick is herdr-claude or herdr-grok on every slot and no pi head is "
                    "ever the default choice. Un-skip when a slot's first-choice head "
                    "is herdr-pi again.")
    def test_a_pi_head_gets_its_own_providers_and_never_a_default(self):
        """**IT ASKS `pick_head_config()` WHICH MODEL RAN, and does not assume one.**

        A27 made a slot a LIST of configs, so `[heads].<role>` no longer names one model.
        `_capture()` drives `pod.launch()` with no state, which counts every live head as
        zero, so the config this test expects is the one the policy picks from an idle
        machine. Reading `[heads].<role>["harness"]` here would raise on a list and, worse,
        would pin a model the dispatcher may not have chosen.
        """
        table = heads_mod.load_heads()["legal"]["pi_provider"]
        seen = {}
        for role in sorted(heads_mod.load_heads()["heads"]):
            with self.subTest(role=role):
                cfgs = heads_mod.configs(role)
                row = pod.pick_head_config(cfgs, pod.head_live_counts(None, role, cfgs))
                self.assertIsNotNone(row, f"{role} has no eligible head on an idle pod")
                got = self._capture(role).get("provider")
                if row["harness"] != "herdr-pi":
                    self.assertIsNone(got, f"{role} is not a pi head")
                    continue
                self.assertEqual(got, table[row["model"]],
                                 f"{role} runs {row['model']} and was sent to {got}")
                seen[row["model"]] = got
        self.assertTrue(seen, "no pi head was dispatched, so the provider lookup was not exercised")

    # ------------------------------------------------------------------ A27 end to end

    def _live(self, slot, model, n=1, status=None):
        """A `State` holding `n` live tasks on one slot and one model."""
        st = pod.State()
        for i in range(n):
            code = f"LIVE-{i}"
            st.tasks[code] = pod.Task(code, role=slot, model=model,
                                      status=status or pod.RUNNING)
        return st

    @unittest.skip("owner 2026-08-22: qwen was coder's one capped config; with it out "
                    "for maintenance, heads_mod.configs(\"coder\") has no entry with "
                    "max_concurrency set. Un-skip when qwen's line is restored.")
    def test_an_idle_coder_slot_dispatches_on_the_CAPPED_head(self):
        """The whole of A27 through the real `launch()`: the policy picks, the launcher
        gets that model with that provider, and the TASK records what ran (AD26)."""
        got = self._capture("coder", pod.State())
        cap = [c for c in heads_mod.configs("coder")
               if c["max_concurrency"] is not None][0]
        self.assertEqual(got["_task"].model, cap["model"])
        self.assertEqual(got["_task"].harness, cap["harness"])
        # THE PROVIDER IS THE KEYWORD THE PANE REALLY GETS, and the model reaches the
        # launcher POSITIONALLY, so `_task.model` above is the readable end of it.
        self.assertEqual(got["provider"], cap["pi_provider"])
        self.assertEqual(got["effort"], cap["effort"])

    @unittest.skip("owner 2026-08-22: qwen was coder's one capped config; with it out "
                    "for maintenance, heads_mod.configs(\"coder\") has no entry with "
                    "max_concurrency set. Un-skip when qwen's line is restored.")
    def test_a_second_task_spills_to_the_UNCAPPED_head_while_the_first_is_live(self):
        """**THIS IS THE CASE THE FEATURE EXISTS FOR** and no unit test of the policy
        alone can reach it: the count comes from `st.tasks`, which rule (f) mutates as it
        dispatches, so the second dispatch of one tick must already see the first."""
        cap = [c for c in heads_mod.configs("coder")
               if c["max_concurrency"] is not None][0]
        free = [c for c in heads_mod.configs("coder")
                if c["max_concurrency"] is None][0]
        st = self._live("coder", cap["model"], cap["max_concurrency"])
        got = self._capture("coder", st)
        self.assertEqual(got["_task"].model, free["model"])
        self.assertEqual(got["_task"].harness, free["harness"])
        self.assertIsNone(got["provider"], "a non-pi head was sent a provider")
        self.assertEqual(got["effort"], free["effort"])

    @unittest.skip("owner 2026-08-22: qwen was coder's one capped config; with it out "
                    "for maintenance, heads_mod.configs(\"coder\") has no entry with "
                    "max_concurrency set. Un-skip when qwen's line is restored.")
    def test_a_task_that_is_DONE_frees_the_capped_head_again(self):
        """A closed task holds no head. Counting one would shrink a cap nothing uses."""
        cap = [c for c in heads_mod.configs("coder")
               if c["max_concurrency"] is not None][0]
        st = self._live("coder", cap["model"], cap["max_concurrency"], pod.DONE)
        self.assertEqual(self._capture("coder", st)["_task"].model, cap["model"])

    @unittest.skip("owner 2026-08-22: qwen was coder's one capped config; with it out "
                    "for maintenance, heads_mod.configs(\"coder\") has no entry with "
                    "max_concurrency set. Un-skip when qwen's line is restored.")
    def test_a_live_task_on_ANOTHER_slot_does_not_spend_the_coder_cap(self):
        """The pair is the slot AND the model, so one model shared by two slots would
        otherwise have one cap between them."""
        cap = [c for c in heads_mod.configs("coder")
               if c["max_concurrency"] is not None][0]
        st = self._live("coder_adversarial", cap["model"], cap["max_concurrency"])
        self.assertEqual(self._capture("coder", st)["_task"].model, cap["model"])

    def test_every_head_full_REFUSES_the_dispatch_and_names_the_caps(self):
        """`launch()` returns None and leaves words in `LAUNCH_REFUSAL`, which rule (f)
        writes into the park as `why`. A silent None is the defect the stderr tee already
        repaired once."""
        cfgs = [{"model": "m1", "effort": "", "harness": "herdr-pi",
                 "sandbox": "acceptEdits", "max_concurrency": 1, "pi_provider": "p"}]
        real = heads_mod.configs
        heads_mod.configs = lambda slot, path=None, cache=True: tuple(cfgs)
        try:
            st = self._live("coder", "m1", 1)
            self.assertIsNone(self._capture("coder", st, expect_call=False))
        finally:
            heads_mod.configs = real
        self.assertIn("max_concurrency", pod.LAUNCH_REFUSAL)
        self.assertIn("m1 1/1", pod.LAUNCH_REFUSAL)


class QuotaPark(LoopCase):
    """A VENDOR REFUSAL IS NOT AN EMPTY RETURN, and until 2026-08-19 both said `no-change`.

    MEASURED that day: seven parked tasks, three loop stops and four maintainer batches,
    all one five-hour usage limit whose reset time sat in a file the program never opened.
    """

    #: THE REAL SHAPE, and it is the whole reason these tests exist. The final message is
    #: a pane capture and the terminal hard-wrapped it, in the worst case to ONE CHARACTER
    #: PER LINE, so `grep "Usage limit"` over the raw bytes finds nothing. Copied from
    #: `.pod-state/logs/LJ-1.396-20260819-164127-final.md`.
    WRAPPED = "\n".join(" " + c for c in
                        'Error: 429: {"code":"1308","message":"Usage limit reached for 5 '
                        'hour. Your limit will reset at 2026-08-19 20:19:47"}')

    def final(self, text, code=CODE, stamp="20260819-164127"):
        (self.tmp / ".pod-state" / "logs" / f"{code}-{stamp}-final.md").write_text(
            text, encoding="utf-8")

    def returned(self):
        st = pod.State()
        t = pod.Task(CODE, brief=f"agents/tasks/{DIR}/{CODE}.md", status=pod.RETURNED,
                     attempt=1, obl_before=2)
        st.tasks[CODE] = t
        return st, t

    def parked(self, reason):
        st = pod.State()
        t = pod.Task(CODE, brief=f"agents/tasks/{DIR}/{CODE}.md", status=pod.PARKED,
                     park_reason=reason, record=None, parked_at=0.0, attempt=1)
        st.tasks[CODE] = t
        return st, t

    # ------------------------------------------------------------------ the reader

    def assertQuotaStamp(self, got, naive="2026-08-19T20:19:47"):
        """The vendor's clock plus the offset this machine had when the file was read."""
        self.assertIsNotNone(got)
        self.assertRegex(got, rf"^{re.escape(naive)}[+-]\d{{2}}:\d{{2}}$", got)

    def test_the_phrase_is_found_THROUGH_the_terminal_wrapping(self):
        """The one invariant. A matcher that reads the raw text finds nothing at all."""
        self.final(self.WRAPPED)
        self.assertNotIn("Usage limit", self.WRAPPED, "the fixture is no longer wrapped")
        self.assertQuotaStamp(pod.vendor_refusal(CODE, self.tmp))

    def test_PROSE_THAT_QUOTES_THE_MESSAGE_is_not_a_refusal(self):
        """**A FALSE POSITIVE, found by an adversarial review on 2026-08-19.** The matcher
        keyed on the SENTENCE, so a report quoting the vendor and a brief describing the
        rule both fired. The real returns carry the status and the vendor code beside the
        phrase, `429: {"code":"1308","message":"Usage limit reached`, and prose does not."""
        for text in (
            "The coder said `Usage limit reached for 5 hour. Your limit will reset at "
            "2026-08-19 20:19:47` and then finished the work.",
            "A25: Usage limit reached for 5 hour. Your limit will reset at "
            "2026-08-19 20:19:47 is the shape this matches.",
        ):
            self.final(text)
            self.assertIsNone(pod.vendor_refusal(CODE, self.tmp),
                              f"prose read as a vendor refusal: {text[:40]}")

    def test_the_ENVELOPE_is_what_makes_it_a_refusal(self):
        """The other direction: the real shape must still match through the wrapping."""
        self.final(self.WRAPPED)
        self.assertQuotaStamp(pod.vendor_refusal(CODE, self.tmp))

    def test_a_return_with_no_refusal_reads_as_no_refusal(self):
        self.final("the coder finished and wrote a report\n")
        self.assertIsNone(pod.vendor_refusal(CODE, self.tmp))

    def test_no_log_at_all_reads_as_no_refusal(self):
        self.assertIsNone(pod.vendor_refusal(CODE, self.tmp))

    def test_the_NEWEST_return_is_the_one_read(self):
        """A task that was quota-refused yesterday and ran today is not quota-refused."""
        self.final(self.WRAPPED, stamp="20260819-100000")
        self.final("this instance ran and returned\n", stamp="20260819-164127")
        self.assertIsNone(pod.vendor_refusal(CODE, self.tmp))

    # ------------------------------------------------------------------ rule (c)

    def test_rule_c_names_the_quota_instead_of_calling_it_no_change(self):
        self.final(self.WRAPPED)
        self.set_acceptance(None)
        st, t = self.returned()
        pod._rule_c(st, self.tmp)
        self.assertEqual(t.status, pod.PARKED)
        self.assertTrue(t.park_reason.startswith("quota:"), t.park_reason)
        self.assertQuotaStamp(t.park_reason[len("quota:"):])

    def test_rule_c_keeps_no_change_when_nothing_proves_a_refusal(self):
        """THE OLDER NAME IS THE FALLBACK. A reason must never claim what it cannot read."""
        self.final("the coder ran and changed nothing\n")
        self.set_acceptance(None)
        st, t = self.returned()
        pod._rule_c(st, self.tmp)
        self.assertEqual(t.park_reason, "no-change")

    def test_quota_is_a_park_reason_the_program_admits(self):
        self.assertIn("quota:", pod.PARK_REASONS)

    # ------------------------------------------------------------------ rule (a2)

    def test_a_quota_park_HOLDS_while_the_vendor_window_is_still_open(self):
        future = (datetime.datetime.now()
                  + datetime.timedelta(hours=2)).isoformat(timespec="seconds")
        st, t = self.parked(f"quota:{future}")
        pod._rule_a2(st, self.tmp)
        self.assertEqual(t.status, pod.PARKED)

    def test_a_quota_park_RE_OPENS_ON_THE_CLOCK_and_needs_no_person(self):
        """It is the only park that does. Every other cause is inside the project and
        ends when somebody acts; a vendor's window ends by itself."""
        past = (datetime.datetime.now()
                - datetime.timedelta(minutes=1)).isoformat(timespec="seconds")
        st, t = self.parked(f"quota:{past}")
        pod._rule_a2(st, self.tmp)
        self.assertEqual(t.status, pod.READY)

    def test_a_quota_park_the_program_did_not_write_opens_at_once(self):
        """`vendor_refusal()` never emits an unreadable time, so a hand wrote this one,
        and holding it for ever is the worse of the two failures."""
        st, t = self.parked("quota:whenever")
        pod._rule_a2(st, self.tmp)
        self.assertEqual(t.status, pod.READY)

    def test_a_RESTORED_relic_with_a_later_NAME_is_not_the_newest_return(self):
        """Name sort treated a restored quota file as newest when its stamp sorted last.
        Recency is mtime: when the file landed, which is when this program wrote it."""
        relic = self.tmp / ".pod-state" / "logs" / f"{CODE}-20260819-200000-final.md"
        later = self.tmp / ".pod-state" / "logs" / f"{CODE}-20260819-100000-final.md"
        relic.write_text(self.WRAPPED, encoding="utf-8")
        later.write_text("this instance ran and returned\n", encoding="utf-8")
        os.utime(relic, (1_000_000, 1_000_000))
        os.utime(later, (2_000_000, 2_000_000))
        self.assertIsNone(pod.vendor_refusal(CODE, self.tmp),
                          "a restored relic with a later NAME won on the name sort")

    def test_an_AWARE_stamp_does_not_move_when_the_zone_would_have_shifted_a_naive_one(self):
        """The defect: naive 20:19 compared to local now, so a TZ change moved the
        instant. An offset stamp is compared in UTC and does not move."""
        future = (datetime.datetime.now(datetime.timezone.utc)
                  + datetime.timedelta(hours=2)).strftime("%Y-%m-%dT%H:%M:%S+00:00")
        past = (datetime.datetime.now(datetime.timezone.utc)
                - datetime.timedelta(hours=2)).strftime("%Y-%m-%dT%H:%M:%S+00:00")
        self.assertFalse(pod.quota_open("quota:" + future),
                         "a future UTC stamp opened early")
        self.assertTrue(pod.quota_open("quota:" + past),
                        "a past UTC stamp held")
        self.final(self.WRAPPED)
        got = pod.vendor_refusal(CODE, self.tmp)
        self.assertQuotaStamp(got)
        self.assertNotEqual(got, "2026-08-19T20:19:47",
                            "the stamp was stored naive, so a later TZ change can move it")


class FallbackPark(LoopCase):
    """A29. A HEAD THAT PRODUCED NOTHING FALLS BACK TO THE SLOT'S NEXT HEAD.

    **THE MECHANISM SHIPPED UNTESTED ON 2026-08-21 AND THIS CLASS IS THE REPAIR.** It
    fired twice on real work that day (`LJ-1.481`, `LJ-1.488`) and no test named it, so
    every claim below was believed and none was checked.

    Its trigger then was `max_concurrency`, because the head that had failed twice
    (`LJ-1.478`, `LJ-1.479`, oMLX's own process memory ceiling) was the one capped head in
    `dev/pod/heads.toml`. The owner ruled the same retry for two UNCAPPED critic slots on
    the same day, so the gate is now the arithmetic that made the retry possible at all:
    the slot has somewhere else to send the task.

    **THE WHOLE CLASS TURNS ON WHAT `rec is None` MEANS.** It is R7: the runner measured
    NOTHING, so the vendor crashed, was refused, or hit a ceiling. A stated NO-GO carries
    a RECORD and routes through the table. No test here may let the two blur, and
    `test_a_MEASURED_return_never_falls_back...` is the one that would catch it.
    """

    def returned(self, role="coder_adversarial", model="glm-5.3", avoid=None):
        st = pod.State()
        t = pod.Task(CODE, brief=f"agents/tasks/{DIR}/{CODE}.md", status=pod.RETURNED,
                     attempt=1, obl_before=2, role=role, model=model,
                     avoid_models=avoid)
        st.tasks[CODE] = t
        return st, t

    def parked(self, reason, avoid=None):
        st = pod.State()
        t = pod.Task(CODE, brief=f"agents/tasks/{DIR}/{CODE}.md", status=pod.PARKED,
                     park_reason=reason, record=None, parked_at=0.0, attempt=1,
                     avoid_models=avoid)
        st.tasks[CODE] = t
        return st, t

    def set_heads(self, **slots):
        """A synthetic `[heads]`, so a truth-table test does not move when the owner
        re-points a slot. The tests that DO read the live file say so in their names."""
        self.patch(heads_mod, "configs",
                   lambda slot, *a, **k: tuple(slots[slot]))

    # ------------------------------------------------- the trigger, on a synthetic file

    def test_the_trigger_is_a_slot_with_a_CHOICE_and_not_a_capped_model(self):
        """**THE ONE CHECK THAT SEPARATES A29 FROM WHAT IT REPLACED.** Every model here is
        UNCAPPED, which is exactly the shape the old `_capped_model()` gate refused."""
        self.set_heads(critic=[{"model": "glm-5.3", "max_concurrency": None},
                               {"model": "grok-4.6", "max_concurrency": None}])
        self.assertTrue(pod._has_fallback_head("critic", "glm-5.3", self.tmp))
        self.assertTrue(pod._has_fallback_head("critic", "grok-4.6", self.tmp))

    def test_a_capped_model_still_triggers_it_so_A27s_own_case_did_not_regress(self):
        self.set_heads(coder=[{"model": "local", "max_concurrency": 1},
                              {"model": "cloud", "max_concurrency": None}])
        self.assertTrue(pod._has_fallback_head("coder", "local", self.tmp))

    def test_a_slot_of_ONE_head_never_triggers_it_however_the_head_is_shaped(self):
        """There is nowhere else to send the task, so the honest answer is the plain
        `no-change` that waits for a person."""
        self.set_heads(solo=[{"model": "only", "max_concurrency": None}])
        self.assertFalse(pod._has_fallback_head("solo", "only", self.tmp))
        self.set_heads(solo=[{"model": "only", "max_concurrency": 1}])
        self.assertFalse(pod._has_fallback_head("solo", "only", self.tmp))

    def test_a_model_the_slot_does_not_carry_never_triggers_it(self):
        """The pair is the slot AND the model. A task whose recorded model has since left
        the file must not be retried as though the file still ruled it."""
        self.set_heads(critic=[{"model": "glm-5.3", "max_concurrency": None},
                               {"model": "grok-4.6", "max_concurrency": None}])
        self.assertFalse(pod._has_fallback_head("critic", "deepseek-v4-pro", self.tmp))

    def test_a_heads_file_it_cannot_read_answers_FALSE_and_never_guesses(self):
        """The same direction `_no_change_reason()` takes: an unreadable file gets the
        plain `no-change` it always got, never a guess dressed as a finding."""
        def boom(slot, *a, **k):
            raise heads_mod.HeadsError("unreadable")
        self.patch(heads_mod, "configs", boom)
        self.assertFalse(pod._has_fallback_head("coder", "anything", self.tmp))

    # ------------------------------------------------- the trigger, on the LIVE file

    def test_the_LIVE_file_gives_every_dispatched_slot_a_fallback_but_the_author(self):
        """**THE OWNER'S RULING OF 2026-08-21, READ BACK FROM THE FILE THAT BINDS.**
        Both critics carry a choice; `mathematician` is one head and parks `no-change`
        exactly as it always did.

        **`coder` REJOINED THE LIST 2026-08-23**, qwen's return from the 2026-08-22
        maintenance drop giving it a second head (`glm-5.3`) again -- the same ruling
        that moved `claude-opus-5` from `coder` to `coder_adversarial`'s own second
        head, replacing `glm-5.3` there."""
        for slot, model in (("mathematician_adversarial", "glm-5.3"),
                            ("mathematician_adversarial", "grok-4.6"),
                            ("coder_adversarial", "claude-opus-5"),
                            ("coder_adversarial", "grok-4.6"),
                            ("coder", "Qwen3.8-27B-oQ4e-mtp"),
                            ("coder", "glm-5.3")):
            with self.subTest(slot=slot, model=model):
                self.assertTrue(pod._has_fallback_head(slot, model, self.tmp))
        self.assertFalse(
            pod._has_fallback_head("mathematician", "claude-opus-5", self.tmp))

    # ------------------------------------------------------------------ rule (c)

    def test_an_R7_return_on_a_slot_with_a_choice_parks_fallback_and_names_the_model(self):
        self.set_acceptance(None)
        st, t = self.returned(role="coder_adversarial", model="grok-4.6")
        pod._rule_c(st, self.tmp)
        self.assertEqual(t.status, pod.PARKED)
        self.assertEqual(t.park_reason, "fallback:grok-4.6")
        self.assertEqual(list(t.avoid_models), ["grok-4.6"])

    def test_an_R7_return_on_a_ONE_head_slot_is_the_plain_no_change_it_always_was(self):
        self.set_acceptance(None)
        st, t = self.returned(role="mathematician", model="claude-opus-5")
        pod._rule_c(st, self.tmp)
        self.assertEqual(t.park_reason, "no-change")
        self.assertFalse(t.avoid_models)

    def test_a_VENDOR_REFUSAL_stays_a_quota_park_and_is_not_turned_into_a_fallback(self):
        """A25 owns this return. The window ends by itself and the model is not at fault,
        so spending a second head on it would burn the fallback for nothing."""
        (self.tmp / ".pod-state" / "logs"
         / f"{CODE}-20260819-164127-final.md").write_text(
            QuotaPark.WRAPPED, encoding="utf-8")
        self.set_acceptance(None)
        st, t = self.returned(role="coder_adversarial", model="grok-4.6")
        pod._rule_c(st, self.tmp)
        self.assertTrue(t.park_reason.startswith("quota:"), t.park_reason)
        self.assertFalse(t.avoid_models)

    def test_a_MEASURED_return_never_falls_back_however_negative_it_is(self):
        """**THE LINE A29 MUST NOT CROSS.** A stated NO-GO is a real answer with real
        content. It carries a record, so R7 never fires, so nothing is excluded and no
        head is spent twice on a question that was already answered."""
        self.set_acceptance(record(exit_code=42, error_class="unsolved_meta", delta=0))
        st, t = self.returned(role="coder_adversarial", model="grok-4.6")
        pod._rule_c(st, self.tmp)
        self.assertNotEqual(t.park_reason, "fallback:grok-4.6")
        self.assertFalse(t.avoid_models)

    def test_the_SAME_model_is_never_excluded_twice(self):
        """A task already carrying its model on the avoid list has nothing new to learn
        from a second identical return, so it takes the plain `no-change` and waits."""
        self.set_acceptance(None)
        st, t = self.returned(role="coder_adversarial", model="grok-4.6",
                              avoid=["grok-4.6"])
        pod._rule_c(st, self.tmp)
        self.assertEqual(t.park_reason, "no-change")
        self.assertEqual(list(t.avoid_models), ["grok-4.6"])

    def test_a_SECOND_failure_adds_the_other_model_which_is_why_it_terminates(self):
        """The exclusion is MONOTONIC. Once both heads are on the list `launch()` has no
        candidate left and rule (f) parks `launch`, never a third fallback."""
        self.set_acceptance(None)
        st, t = self.returned(role="coder_adversarial", model="claude-opus-5",
                              avoid=["grok-4.6"])
        pod._rule_c(st, self.tmp)
        self.assertEqual(t.park_reason, "fallback:claude-opus-5")
        self.assertEqual(sorted(t.avoid_models), ["claude-opus-5", "grok-4.6"])

    def test_fallback_is_a_park_reason_the_program_admits_and_capacity_is_gone(self):
        """ONE NAME, ONE MECHANISM. A second redundant reason string would divide the
        `PARK_CLASSES` digest derives from this tuple."""
        self.assertIn("fallback:", pod.PARK_REASONS)
        self.assertNotIn("capacity:", pod.PARK_REASONS)

    # ------------------------------------------------------------------ rule (a2)

    def test_a_fallback_park_REOPENS_AT_ONCE_with_no_clock_and_no_table_edit(self):
        """**THE ONE PARK THAT DOES.** `parked_at` is 0.0 and the table is untouched, so
        an `admission` or `launch` park would hold here. This one has nothing to gate on:
        the avoid list already guarantees the retry lands on a different head."""
        st, t = self.parked("fallback:glm-5.3", avoid=["glm-5.3"])
        pod._rule_a2(st, self.tmp)
        self.assertEqual(t.status, pod.READY)

    def test_the_reopen_KEEPS_the_avoid_list_because_that_is_the_whole_retry(self):
        """A reopen that dropped it would send the task straight back to the head that
        just produced nothing, and the park would repeat for ever."""
        st, t = self.parked("fallback:glm-5.3", avoid=["glm-5.3"])
        pod._rule_a2(st, self.tmp)
        self.assertEqual(list(t.avoid_models), ["glm-5.3"])

    def test_a_plain_no_change_park_still_waits_for_a_person(self):
        """The contrast that gives the test above its meaning: same rule, same clock,
        opposite answer, and section 5.5 rules it."""
        st, t = self.parked("no-change")
        pod._rule_a2(st, self.tmp)
        self.assertEqual(t.status, pod.PARKED)

    # ------------------------------------------------------------------ the launcher

    #: THE REAL `launch()`, because `LoopCase` replaces it with a recorder that never
    #: reads `avoid_models` at all. A test of the exclusion against that stub would pass
    #: on a `launch()` that had lost the feature entirely.
    def real_launch(self, t, role="coder_adversarial"):
        class FakeLauncher:
            HARNESS = ""
        self.patch(facts_mod, "launcher", lambda: FakeLauncher)
        return REAL_LAUNCH(t, f"agents/tasks/{DIR}/{CODE}.md", role, self.tmp,
                           pod.State())

    def test_launch_drops_every_avoided_model_from_the_candidate_list(self):
        """`launch()` is the ONE reader of `avoid_models`, so the retry cannot repeat the
        head that just failed."""
        seen = {}

        def spy(cfgs, counts):
            seen["cfgs"] = list(cfgs)
            return None                        # refuse, so nothing is really dispatched

        self.patch(pod, "pick_head_config", spy)
        self.real_launch(pod.Task(CODE, avoid_models=["grok-4.6"]))
        self.assertEqual([c["model"] for c in seen["cfgs"]], ["claude-opus-5"])

    def test_launch_with_no_avoid_list_sees_every_config_the_slot_carries(self):
        """The contrast: this is every OTHER task in the program, and the filter above
        must be a no-op for it."""
        seen = {}

        def spy(cfgs, counts):
            seen["cfgs"] = list(cfgs)
            return None

        self.patch(pod, "pick_head_config", spy)
        self.real_launch(pod.Task(CODE))
        self.assertEqual(sorted(c["model"] for c in seen["cfgs"]),
                         ["claude-opus-5", "grok-4.6"])

    def test_excluding_EVERY_model_is_the_ordinary_launch_refusal_and_not_a_loop(self):
        """It is not special-cased: `pick_head_config()` on an empty tuple returns None
        exactly as it does when every config is at its cap, and rule (f) parks `launch`."""
        t = pod.Task(CODE, avoid_models=["claude-opus-5", "grok-4.6"])
        self.assertIsNone(self.real_launch(t))
        # AND IT SAYS SO. A park that names no cap costs the maintainer a pane read.
        self.assertIn("coder_adversarial", pod.LAUNCH_REFUSAL or "")


class TwoThresholds(LoopCase):
    """AD15's parked trigger and AD14's stop were ONE number until 2026-08-19.

    `parked_max` moved to 7 that day and rule (d) followed it while rule (e) did not, so
    the maintainer is fed at the third park and the loop halts at the seventh. The owner
    ruled that correct. These tests pin the RELATION and never either number, because both
    are values the project is expected to move.
    """

    def test_the_maintainer_is_warned_at_or_before_the_stop(self):
        """The one invariant. A trigger at or above `parked_max` would arrive with the
        stop it exists to prevent, and the role that repairs the loop would learn of a
        park only from the page that says the loop already halted."""
        self.assertLessEqual(pod.BATCH_PARKED, pod._limits()["parked_max"])

    def test_rule_e_feeds_the_maintainer_at_the_batch_threshold_not_at_the_stop(self):
        st = pod.State()
        for i in range(pod.BATCH_PARKED):
            code = f"LJ-1.{900 + i}"
            st.tasks[code] = pod.Task(code, status=pod.PARKED, park_reason="no-match",
                                      record=record(), parked_at=0.0)
        pod.emit(st, st.tasks["LJ-1.900"], pod.CHECKING, pod.PARKED,
                 reason="no-match", rec=record(), root=self.tmp)
        pod._rule_e(st, self.tmp)
        self.assertEqual(self.calls["maintainer"], 1,
                         "the maintainer was not fed at the batch threshold")

    def test_rule_d_does_NOT_stop_at_the_batch_threshold(self):
        """The gap between the two numbers is the warning, so it must be a real gap."""
        if pod.BATCH_PARKED >= pod._limits()["parked_max"]:
            self.skipTest("the two thresholds are equal, so there is no warning window")
        st = pod.State()
        for i in range(pod.BATCH_PARKED):
            code = f"LJ-1.{900 + i}"
            st.tasks[code] = pod.Task(code, status=pod.PARKED, park_reason="no-match")
        self.assertIs(pod._rule_d(st, self.tmp), pod.CONTINUE)
        self.assertFalse((self.tmp / ".pod-state" / "STOPPED").exists())

    def test_a_quota_park_COUNTS_toward_the_stop(self):
        """Owner's ruling, 2026-08-19, against the maintainer's recommendation. The loop
        cannot do the project's work while its heads are refused, so a stop that pages the
        owner is a truer report of that than a loop that keeps ticking."""
        st = pod.State()
        for i in range(pod._limits()["parked_max"]):
            code = f"LJ-1.{900 + i}"
            st.tasks[code] = pod.Task(code, status=pod.PARKED,
                                      park_reason="quota:2026-08-19T20:19:47")
        self.assertIs(pod._rule_d(st, self.tmp), pod.STOP)
        self.assertTrue((self.tmp / ".pod-state" / "STOPPED").exists())


class CommitOnClose(unittest.TestCase):
    """`commit_task()` against a REAL git repository, because the defect was git's shape.

    MEASURED 2026-08-19: `git_commit()` over two real edits and one absent path commits
    NOTHING and returns False. `commit_task()` read no return value and caught only
    exceptions, so a close whose commit did nothing wrote a DONE line and said nothing
    else. Amendment A24 made that reachable: fact 4 counts every path under the task home
    and `salvage_worktree()` used to copy back only `## SCOPE (write)`. A task-home
    file now lands; a path outside both the task home and the declared scope still
    does not.
    """

    def setUp(self):
        self.dir = tempfile.TemporaryDirectory()
        self.tmp = Path(self.dir.name)
        self.addCleanup(self.dir.cleanup)
        run = lambda *a: subprocess.run(["git", *a], cwd=self.tmp, capture_output=True)
        run("init", "-q")
        run("config", "user.email", "t@t")
        run("config", "user.name", "t")
        (self.tmp / "kept.md").write_text("a\n")
        run("add", "-A")
        run("commit", "-qm", "base")
        (self.tmp / "kept.md").write_text("a2\n")

    def commits(self):
        out = subprocess.run(["git", "log", "--oneline"], cwd=self.tmp,
                             capture_output=True, text=True).stdout
        return [l for l in out.splitlines() if l.strip()]

    def close(self, changed, refused=None):
        """Run the DONE handler with `ledger.py` stubbed out. It returns the record."""
        rec = {"facts": {"changed_files": changed}}
        if refused is not None:
            rec["changed_files_refused"] = list(refused)
        t = pod.Task("LJ-1.999", status=pod.CHECKING)
        t.row = "sys-x"
        real = subprocess.run
        def fake(argv, *a, **k):
            if "ledger.py" in " ".join(str(x) for x in argv):
                return subprocess.CompletedProcess(argv, 0, "", "")
            return real(argv, *a, **k)
        subprocess.run = fake
        try:
            pod.commit_task(t, rec, self.tmp)
        finally:
            subprocess.run = real
        return rec

    def test_a_path_the_main_tree_does_not_hold_no_longer_loses_the_whole_commit(self):
        """The measured defect. `never-salvaged.md` is what A24 leaves behind."""
        rec = self.close(["kept.md", "never-salvaged.md"])
        self.assertEqual(len(self.commits()), 2, "the close committed nothing at all")
        self.assertEqual(rec["commit"], "clean")
        self.assertEqual(rec["commit_absent"], ["never-salvaged.md"])

    def test_a_DIRECTORY_in_changed_files_is_never_committed(self):
        """**`git commit -- <dir>` SWEEPS EVERYTHING UNDER IT**, which is the `git add -A`
        hazard R8 exists to refuse, arriving through a path fact 4 measured. Raised by an
        adversarial review on 2026-08-19."""
        (self.tmp / "adir").mkdir()
        (self.tmp / "adir" / "sweep-me.md").write_text("not this task's work\n")
        rec = self.close(["kept.md", "adir"])
        self.assertEqual(rec["commit_absent"], ["adir"])
        out = subprocess.run(["git", "show", "--name-only", "--format="], cwd=self.tmp,
                             capture_output=True, text=True).stdout
        self.assertNotIn("sweep-me", out, "a directory swept a file into the close")
        self.assertIn("kept.md", out)

    def test_a_path_that_ESCAPES_the_repository_is_never_committed(self):
        rec = self.close(["kept.md", "../outside.md", "/etc/hosts"])
        self.assertEqual(sorted(rec["commit_absent"]), ["../outside.md", "/etc/hosts"])
        self.assertEqual(rec["commit"], "clean")

    def test_a_clean_close_records_that_it_committed(self):
        rec = self.close(["kept.md"])
        self.assertEqual(rec["commit"], "clean")
        self.assertNotIn("commit_absent", rec)
        self.assertEqual(len(self.commits()), 2)

    def test_a_close_with_NOTHING_left_to_commit_is_recorded_and_not_silent(self):
        """Every named path is gone. The close still stands; the record says why."""
        rec = self.close(["never-salvaged.md"])
        self.assertEqual(rec["commit_absent"], ["never-salvaged.md"])
        self.assertEqual(len(self.commits()), 1, "it committed something from nothing")

    def test_a_refused_close_unstages_and_records_the_git_error(self):
        """MEASURED 2026-08-20 on LJ-1.404: `commit: refused` left the three deliverable
        files staged, and the next human commit swept them (`f898e3b`)."""
        pod._REFUSED_COMMIT_TRIED.clear()
        hook = self.tmp / ".git" / "hooks" / "pre-commit"
        hook.parent.mkdir(parents=True, exist_ok=True)
        hook.write_text("#!/bin/sh\necho HOOK-REFUSED >&2\nexit 1\n")
        hook.chmod(0o755)
        subprocess.run(["git", "config", "core.hooksPath", ".git/hooks"],
                       cwd=self.tmp, capture_output=True)
        rec = self.close(["kept.md"])
        self.assertEqual(rec["commit"], "refused")
        self.assertIn("HOOK-REFUSED", rec.get("commit_note", ""))
        cached = subprocess.run(["git", "diff", "--cached", "--name-only"],
                                cwd=self.tmp, capture_output=True, text=True).stdout
        self.assertEqual(cached.strip(), "", "a refused commit left paths staged")

    def test_a_refused_close_is_retried_once_the_hook_is_gone(self):
        """The 404 recovery: salvage already copied the files; the next tick commits."""
        pod._REFUSED_COMMIT_TRIED.clear()
        hook = self.tmp / ".git" / "hooks" / "pre-commit"
        hook.parent.mkdir(parents=True, exist_ok=True)
        hook.write_text("#!/bin/sh\necho HOOK-REFUSED >&2\nexit 1\n")
        hook.chmod(0o755)
        subprocess.run(["git", "config", "core.hooksPath", ".git/hooks"],
                       cwd=self.tmp, capture_output=True)
        rec = self.close(["kept.md"])
        self.assertEqual(rec["commit"], "refused")
        hook.unlink()
        t = pod.Task("LJ-1.999", status=pod.DONE)
        t.row = "sys-x"
        t.record = rec
        st = pod.State()
        st.tasks[t.code] = t
        pod.retry_refused_commits(st, self.tmp)
        self.assertEqual(rec["commit"], "clean")
        self.assertEqual(len(self.commits()), 2)

    def test_a21_discarded_task_home_probe_is_still_committed(self):
        """MEASURED 2026-08-20 on LJ-1.439: A21 dropped Probe439.agda from fact 4,
        the close committed the report, and the probe stayed untracked."""
        probe = Path("agents") / "tasks" / "LJ-1-999" / "Probe999.agda"
        (self.tmp / probe).parent.mkdir(parents=True)
        (self.tmp / probe).write_text("module Probe999 where\n")
        rec = self.close(["kept.md"], refused=[str(probe)])
        self.assertEqual(rec["commit"], "clean")
        out = subprocess.run(["git", "show", "--name-only", "--format="], cwd=self.tmp,
                             capture_output=True, text=True).stdout
        self.assertIn("kept.md", out)
        self.assertIn("Probe999.agda", out)

    def test_a21_discarded_src_agda_is_not_committed(self):
        src = Path("src") / "L" / "Critic.agda"
        (self.tmp / src).parent.mkdir(parents=True)
        (self.tmp / src).write_text("module Critic where\n")
        rec = self.close(["kept.md"], refused=[str(src)])
        self.assertEqual(rec["commit"], "clean")
        out = subprocess.run(["git", "show", "--name-only", "--format="], cwd=self.tmp,
                             capture_output=True, text=True).stdout
        self.assertIn("kept.md", out)
        self.assertNotIn("Critic.agda", out)
        tracked = subprocess.run(["git", "ls-files", "--", str(src)], cwd=self.tmp,
                                 capture_output=True, text=True).stdout
        self.assertEqual(tracked.strip(), "")

    def test_a_clean_close_retries_the_untracked_a21_probe(self):
        """The 439 recovery: the close already committed fact 4; the next tick
        commits the probe A21 dropped."""
        pod._REFUSED_COMMIT_TRIED.clear()
        probe = Path("agents") / "tasks" / "LJ-1-999" / "Probe999.agda"
        (self.tmp / probe).parent.mkdir(parents=True)
        (self.tmp / probe).write_text("module Probe999 where\n")
        rec = self.close(["kept.md"])
        self.assertEqual(rec["commit"], "clean")
        tracked = subprocess.run(["git", "ls-files", "--", str(probe)], cwd=self.tmp,
                                 capture_output=True, text=True).stdout
        self.assertEqual(tracked.strip(), "")
        rec["changed_files_refused"] = [str(probe)]
        t = pod.Task("LJ-1.999", status=pod.DONE)
        t.row = "sys-critic-upheld-no-go"
        t.record = rec
        st = pod.State()
        st.tasks[t.code] = t
        pod.retry_refused_commits(st, self.tmp)
        self.assertEqual(rec["commit"], "clean")
        out = subprocess.run(["git", "log", "-1", "--name-only", "--format=%s"],
                             cwd=self.tmp, capture_output=True, text=True).stdout
        self.assertIn("A21-refused on close", out.splitlines()[0])
        self.assertIn("Probe999.agda", out)


class MaintainerPreset(LoopCase):
    """`pod.py maintainer` switches the resident head, and the ROW stays the one home.

    The four fields must move TOGETHER. A row carrying `harness = "herdr-grok"` with
    `model = "claude-opus-5"` loads, dispatches, and fails inside the pane, which is the
    failure class the read-back guard exists for and cannot catch for every harness. A
    preset is the unit that keeps them together.
    """

    def heads(self):
        return self.tmp / "dev" / "pod" / "heads.toml"

    def row(self):
        import tomllib
        return tomllib.loads(self.heads().read_text(encoding="utf-8"))["heads"]["maintainer"]

    def test_the_live_file_offers_both_heads_the_owner_named(self):
        got = pod.maintainer_presets(ROOT)
        self.assertIn("claude", got)
        self.assertIn("grok", got)
        for name, r in got.items():
            for k in ("model", "effort", "harness", "sandbox"):
                self.assertIn(k, r, f"preset {name} carries no {k}")

    def test_a_preset_moves_all_four_fields_together(self):
        pod.write_maintainer_row("claude", self.tmp)
        self.assertEqual((self.row()["model"], self.row()["harness"]),
                         ("claude-opus-5", "herdr-claude"))
        pod.write_maintainer_row("grok", self.tmp)
        self.assertEqual((self.row()["model"], self.row()["harness"]),
                         ("grok-4.6", "herdr-grok"))

    def test_an_unknown_preset_is_REFUSED_and_the_file_is_untouched(self):
        before = self.heads().read_text(encoding="utf-8")
        with self.assertRaises(pod.PodError):
            pod.write_maintainer_row("nonesuch", self.tmp)
        self.assertEqual(self.heads().read_text(encoding="utf-8"), before)

    def test_a_preset_the_LOADER_would_refuse_ROLLS_BACK(self):
        """The file must never be left holding a row the next dispatch cannot use. The
        check is the REAL loader and not a second opinion about what it accepts."""
        h = self.heads()
        h.write_text(h.read_text(encoding="utf-8") + '\n[maintainer_presets]\n'
                     'bogus = { model = "claude-haiku-5", effort = "high", '
                     'harness = "herdr-claude", sandbox = "acceptEdits" }\n',
                     encoding="utf-8")
        before = h.read_text(encoding="utf-8")
        with self.assertRaises(pod.PodError):
            pod.write_maintainer_row("bogus", self.tmp)
        self.assertEqual(h.read_text(encoding="utf-8"), before,
                         "a refused preset left the file changed")

    def test_the_comments_of_the_owners_file_SURVIVE_a_switch(self):
        """It rewrites ONE LINE as text. A TOML writer would drop about a hundred lines of
        measurement, which is the whole value of that file."""
        marker = "THE READ-BACK REFUSAL"
        self.assertIn(marker, self.heads().read_text(encoding="utf-8"))
        pod.write_maintainer_row("claude", self.tmp)
        self.assertIn(marker, self.heads().read_text(encoding="utf-8"))

    def test_a_MAINTAINER_KEY_IN_ANOTHER_TABLE_cannot_be_rewritten_instead(self):
        """**A SILENT NO-OP THAT REPORTED SUCCESS**, found by an adversarial pass over this
        command on 2026-08-19. The rewrite ran over the WHOLE FILE with `count=1`, so with
        a table before `[heads]` holding a key named `maintainer` it rewrote THAT key. The
        loader check passed, because the real row was untouched and still valid, and
        `--use claude` reported success while the head stayed on grok."""
        # A SECOND `[maintainer_presets]` would be duplicate TOML and refuse for the
        # wrong reason. The attack is only that a `maintainer = {...}` LINE sits earlier
        # in the file, so any table before `[heads]` reproduces it.
        h = self.heads()
        early = ('[an_earlier_table]\n'
                 'maintainer = { model = "claude-opus-5", effort = "xhigh", '
                 'harness = "herdr-claude", sandbox = "acceptEdits" }\n\n[heads]\n')
        h.write_text(re.sub(r"^\[heads\]\s*$", early.rstrip("\n"),
                            h.read_text(encoding="utf-8"), count=1, flags=re.M),
                     encoding="utf-8")
        pod.write_maintainer_row("claude", self.tmp)
        self.assertEqual(self.row()["model"], "claude-opus-5",
                         "the switch rewrote a key in another table and said it worked")

    def test_a_write_that_DID_NOT_TAKE_is_refused_and_rolled_back(self):
        """The general guard, and it is stronger than any regex. The row is read back
        through the REAL loader and compared with the preset field by field, so every way
        a write can fail to land ends in a refusal rather than in a false success."""
        # THE TABLE HEADER AND NEVER A COMMENT THAT MENTIONS IT. A plain `.replace` hits
        # the first prose occurrence and leaves the real table standing, which is a
        # fixture that tests nothing.
        h = self.heads()
        h.write_text(re.sub(r"^\[heads\]\s*$", "[heads_disabled]",
                            h.read_text(encoding="utf-8"), count=1, flags=re.M),
                     encoding="utf-8")
        before = h.read_text(encoding="utf-8")
        with self.assertRaises(pod.PodError):
            pod.write_maintainer_row("claude", self.tmp)
        self.assertEqual(h.read_text(encoding="utf-8"), before)

    def stub_launcher(self, prompts):
        """The launcher `cmd_maintainer` reaches for. It resolves the name and records
        every prompt, so a test can read what the two sessions were told."""
        class _Stub:
            @staticmethod
            def herdr_name(task):
                return "pod-batch"

            @staticmethod
            def herdr_prompt(name, text):
                prompts.append((name, text))
                return True
        real = pod.facts_mod.launcher
        pod.facts_mod.launcher = lambda: _Stub
        self.addCleanup(lambda: setattr(pod.facts_mod, "launcher", real))

    def test_a_HANDOVER_THAT_CANNOT_START_gives_the_name_BACK(self):
        """**WITHOUT THIS THE SLOT IS LEFT WITH NO MAINTAINER AT ALL.**
        `ensure_maintainer()` returns None on five paths, one of which is「an exclusive
        task is live」, and by then the live agent has been renamed away: it receives no
        mail and nothing has replaced it. If the loop is not running, nothing ever tries
        again. Found by an adversarial pass on 2026-08-19."""
        renames, prompts = [], []
        self.stub_launcher(prompts)
        self.swap(pod,
                  retire_maintainer_agent=lambda root=None: "pod-batch-retired-X",
                  rename_maintainer_agent=lambda a, b: (renames.append((a, b)), True)[1],
                  ensure_maintainer=lambda st, root=None: None)
        rc = pod.cmd_maintainer(["--handover", "claude"])
        self.assertEqual(rc, 1)
        self.assertIn(("pod-batch-retired-X", "pod-batch"), renames,
                      "the outgoing session was left without the name")

    def test_a_HANDOVER_THAT_STARTS_does_not_rename_anything_back(self):
        renames, prompts = [], []
        self.stub_launcher(prompts)
        self.swap(pod,
                  retire_maintainer_agent=lambda root=None: "pod-batch-retired-X",
                  rename_maintainer_agent=lambda a, b: (renames.append((a, b)), True)[1],
                  ensure_maintainer=lambda st, root=None: "agents/tasks/POD-BATCH/x.md")
        rc = pod.cmd_maintainer(["--handover", "claude"])
        self.assertEqual(rc, 0)
        self.assertEqual(renames, [], "it took the name back from the head it just started")
        told = dict(prompts)
        self.assertIn("pod-batch", told, "the new head was never told it is the maintainer")
        self.assertIn("maintainer-handover.md", told["pod-batch"],
                      "the new head was not pointed at the handover")
        self.assertIn("pod-batch-retired-X", told,
                      "the outgoing session was never told it is retired")

    def test_a_switch_leaves_the_OTHER_four_slots_alone(self):
        import tomllib
        before = tomllib.loads(self.heads().read_text(encoding="utf-8"))["heads"]
        pod.write_maintainer_row("claude", self.tmp)
        after = tomllib.loads(self.heads().read_text(encoding="utf-8"))["heads"]
        for slot in ("mathematician", "mathematician_adversarial",
                     "coder", "coder_adversarial"):
            self.assertEqual(before[slot], after[slot], slot)

    def test_a_TRAILING_COMMENT_on_the_row_is_matched_and_kept(self):
        """`--use` said the row was not in [heads] when a `# note` sat after the brace.
        That refuse is safe and the message is a lie. Found 2026-08-19."""
        h = self.heads()
        h.write_text(re.sub(
            r"^(maintainer\s*=\s*\{[^}]*\})\s*$",
            r"\1  # the current head",
            h.read_text(encoding="utf-8"), count=1, flags=re.M), encoding="utf-8")
        pod.write_maintainer_row("claude", self.tmp)
        text = h.read_text(encoding="utf-8")
        self.assertEqual(self.row()["model"], "claude-opus-5")
        self.assertIn("# the current head", text,
                      "the rewrite dropped the comment it had just matched")

    def test_the_live_file_is_untouched_until_the_loader_ACCEPTS(self):
        """A kill between write and read-back left the new bytes on disk. The loader
        must now see a sibling .tmp; the live path stays on `before` until replace."""
        live = self.heads()
        before = live.read_text(encoding="utf-8")
        real = heads_mod.load_heads

        def wrapped(path, cache=True):
            self.assertEqual(live.read_text(encoding="utf-8"), before,
                             "the live file changed before the loader ran")
            return real(path, cache=False)

        self.patch(heads_mod, "load_heads", wrapped)
        pod.write_maintainer_row("claude", self.tmp)
        self.assertEqual(self.row()["model"], "claude-opus-5")
        self.assertFalse(live.with_name(live.name + ".tmp").exists(),
                         "the sibling .tmp was left behind after a clean replace")


class MutationAuditSplicesOneCheck(unittest.TestCase):
    """A pre-flight mutant that reformats the whole file dies for quote style, not the
    gate. `splice_deleted_appends` must change only the deleted check."""

    def test_a_P1_mutant_leaves_every_other_double_quoted_P_id_in_place(self):
        """`ast.unparse` rewrote `"P2 ` to `'P2 ` and test_pod_table went red for every
        mutant. MEASURED 2026-08-19."""
        audit = _load("mutation_audit", "scripts/tests/mutation-audit.py")
        src = (ROOT / "scripts" / "pod" / "preflight.py").read_text(encoding="utf-8")
        new = audit.splice_deleted_appends(src, "P1")
        self.assertIsNotNone(new)
        self.assertNotEqual(new, src)
        self.assertIn('d.append("P1 ', src)
        self.assertNotIn('d.append("P1 ', new, "P1's append is still in the mutant")
        for code in ("P2", "P10", "P22"):
            self.assertIn(f'"{code} ', new,
                          f"the mutant reformatted {code}; unparse would do that")


class PaneSlotLock(unittest.TestCase):
    """Two writers without a lock drop a column. `columns_lock` is the same flock
    shape as `pod_lock()`."""

    def setUp(self):
        self.dir = tempfile.TemporaryDirectory()
        self.state = Path(self.dir.name)
        self.addCleanup(self.dir.cleanup)
        self.ps = _load("pane_slot_for_loop_tests", "scripts/pod/pane-slot.py")

    def test_two_locked_writers_keep_both_columns(self):
        """Without the lock, both read empty, both write, last write wins. With it,
        the second read sees the first pane. MEASURED 2026-08-19 as last-write-wins."""
        worker = (
            "import sys, time\n"
            "from pathlib import Path\n"
            "import importlib.util\n"
            "spec = importlib.util.spec_from_file_location('ps', sys.argv[1])\n"
            "ps = importlib.util.module_from_spec(spec)\n"
            "spec.loader.exec_module(ps)\n"
            "state = Path(sys.argv[2])\n"
            "pane = sys.argv[3]\n"
            "path = state / 'herdr-columns'\n"
            "with ps.columns_lock(state):\n"
            "    text = path.read_text() if path.is_file() else ''\n"
            "    time.sleep(0.4)\n"
            "    path.write_text(text + pane + '\\n')\n"
        )
        script = self.state / "worker.py"
        script.write_text(worker, encoding="utf-8")
        slot = str(ROOT / "scripts" / "pod" / "pane-slot.py")
        procs = [
            subprocess.Popen([sys.executable, str(script), slot, str(self.state), pane])
            for pane in ("pA", "pB")
        ]
        for p in procs:
            self.assertEqual(p.wait(timeout=10), 0)
        got = set((self.state / "herdr-columns").read_text().split())
        self.assertEqual(got, {"pA", "pB"},
                         f"a locked pair of writers dropped a column: {got}")

    def test_write_columns_replaces_and_never_truncates_in_place(self):
        """A torn Path.write_text made the next plan() see no columns and right-split
        BASE. os.replace of a sibling is the one write to the live name."""
        path = self.state / "herdr-columns"
        path.write_text("old\n", encoding="utf-8")
        self.ps.write_columns(self.state, [["p1"], ["p2"]])
        self.assertEqual(path.read_text(encoding="utf-8"), "p1\np2\n")
        self.assertFalse((self.state / "herdr-columns.tmp").exists())


class SeedWorktreeInputs(unittest.TestCase):
    """LJ-1.396, 2026-08-20: an untracked brief never reached the worktree.

    Conjunct 6 then printed `has no brief` and R4 refused a `no-go` that had matched.
    """

    def setUp(self):
        self.dir = tempfile.TemporaryDirectory()
        self.tmp = Path(self.dir.name)
        self.addCleanup(self.dir.cleanup)
        self.main = self.tmp / "agents" / "tasks" / "LJ-1-396"
        self.wt = self.tmp / ".pod-state" / "worktrees" / "LJ-1-396"
        self.dest = self.wt / "agents" / "tasks" / "LJ-1-396"
        self.main.mkdir(parents=True)
        self.dest.mkdir(parents=True)

    def test_an_untracked_brief_is_copied_into_the_worktree(self):
        (self.main / "LJ-1.396.md").write_text("# brief\n")
        (self.main / ".pod").write_text("pod\n")
        n = pod.seed_worktree_inputs("LJ-1.396", self.wt, self.tmp)
        self.assertEqual(n, 2)
        self.assertEqual((self.dest / "LJ-1.396.md").read_text(), "# brief\n")
        self.assertEqual((self.dest / ".pod").read_text(), "pod\n")

    def test_an_existing_worktree_file_is_never_overwritten(self):
        (self.main / "lj-1.396-report.md").write_text("MAIN RELIC\n")
        (self.dest / "lj-1.396-report.md").write_text("WORKER REPORT\n")
        n = pod.seed_worktree_inputs("LJ-1.396", self.wt, self.tmp)
        self.assertEqual(n, 0)
        self.assertEqual((self.dest / "lj-1.396-report.md").read_text(),
                         "WORKER REPORT\n")

    def test_a_subdirectory_is_not_copied(self):
        (self.main / "runs").mkdir()
        (self.main / "runs" / "old.out").write_text("no\n")
        n = pod.seed_worktree_inputs("LJ-1.396", self.wt, self.tmp)
        self.assertEqual(n, 0)
        self.assertFalse((self.dest / "runs").exists())

    def test_a_reuse_of_make_worktree_still_seeds(self):
        """The retry path used to `return wt` before copying, which is how LJ-1.396
        was retried into the same empty task home."""
        (self.main / "LJ-1.396.md").write_text("# brief\n")
        real_of = pod.worktree_of
        pod.worktree_of = lambda code, root=None: self.wt
        try:
            got = pod.make_worktree("LJ-1.396", self.tmp)
        finally:
            pod.worktree_of = real_of
        self.assertEqual(got, self.wt)
        self.assertTrue((self.dest / "LJ-1.396.md").is_file())


class SalvageWorktree(unittest.TestCase):
    """LJ-1.399, 2026-08-20: isolation destroyed the file that matched no-go-stated.

    `task-lj-1-399-no-go-stated` keys on `changed_files_any = review-of-*.md`.
    The brief's SCOPE named only the probe and the report. Salvage copied those
    two, `drop_worktree()` removed the worktree, and the review file was gone.
    """

    def setUp(self):
        self.dir = tempfile.TemporaryDirectory()
        self.tmp = Path(self.dir.name)
        self.addCleanup(self.dir.cleanup)
        run = lambda *a: subprocess.run(["git", *a], cwd=self.tmp, capture_output=True)
        run("init", "-q")
        run("config", "user.email", "t@t")
        run("config", "user.name", "t")
        home = self.tmp / "agents" / "tasks" / "LJ-1-399"
        home.mkdir(parents=True)
        (home / "LJ-1.399.md").write_text(
            "## SCOPE (write)\n"
            "- agents/tasks/LJ-1-399/Probe399.agda\n"
            "- agents/tasks/LJ-1-399/lj-1.399-report.md\n"
        )
        (home / "Probe399.agda").write_text("-- old probe\n")
        (self.tmp / "src").mkdir()
        (self.tmp / "src" / "guarded.agda").write_text("-- main guarded\n")
        run("add", "-A")
        run("commit", "-qm", "base")
        self.wt = self.tmp / ".pod-state" / "worktrees" / "LJ-1-399"
        self.wt.parent.mkdir(parents=True)
        added = subprocess.run(
            ["git", "worktree", "add", "--detach", str(self.wt), "HEAD"],
            cwd=self.tmp, capture_output=True, text=True)
        if added.returncode != 0:
            self.fail(f"git worktree add refused: {added.stderr}")
        self.t = pod.Task("LJ-1.399", brief="agents/tasks/LJ-1-399/LJ-1.399.md")
        self.whome = self.wt / "agents" / "tasks" / "LJ-1-399"

    def test_a_review_file_outside_scope_is_copied(self):
        """The measured defect. The no-go-stated row matches on this file."""
        (self.whome / "review-of-omega-pair-code.md").write_text("NO-GO\n")
        (self.whome / "lj-1.399-report.md").write_text("report\n")
        (self.whome / "Probe399.agda").write_text("-- new probe\n")
        bad = pod.salvage_worktree(self.t, self.tmp)
        self.assertEqual(bad, [])
        dest = self.tmp / "agents" / "tasks" / "LJ-1-399"
        self.assertEqual((dest / "review-of-omega-pair-code.md").read_text(), "NO-GO\n")
        self.assertEqual((dest / "lj-1.399-report.md").read_text(), "report\n")
        self.assertEqual((dest / "Probe399.agda").read_text(), "-- new probe\n")

    def test_a_src_write_outside_scope_is_not_copied(self):
        """The honour system still holds outside the task home."""
        (self.wt / "src" / "guarded.agda").write_text("-- worker guarded\n")
        (self.wt / "src" / "foreign.agda").write_text("-- foreign\n")
        bad = pod.salvage_worktree(self.t, self.tmp)
        self.assertEqual(bad, [])
        self.assertEqual((self.tmp / "src" / "guarded.agda").read_text(),
                         "-- main guarded\n")
        self.assertFalse((self.tmp / "src" / "foreign.agda").exists())

    def test_a_main_tree_edit_of_a_task_home_file_still_refuses(self):
        dest = self.tmp / "agents" / "tasks" / "LJ-1-399" / "Probe399.agda"
        dest.write_text("-- MAIN EDIT\n")
        subprocess.run(["git", "add", "-A"], cwd=self.tmp, capture_output=True)
        subprocess.run(["git", "commit", "-qm", "main moved it"],
                       cwd=self.tmp, capture_output=True)
        (self.whome / "Probe399.agda").write_text("-- WORKER PROBE\n")
        bad = pod.salvage_worktree(self.t, self.tmp)
        self.assertTrue(any("Probe399.agda" in x for x in bad), bad)
        self.assertEqual(dest.read_text(), "-- MAIN EDIT\n")

    def test_uncommitted_task_home_dirt_is_overwritten_by_the_worktree(self):
        """LJ-1.388, 2026-08-20: pre-isolation leftover is not a merge."""
        dest = self.tmp / "agents" / "tasks" / "LJ-1-399" / "Probe399.agda"
        dest.write_text("-- MAIN RELIC uncommitted\n")
        (self.whome / "Probe399.agda").write_text("-- WORKER PROBE\n")
        bad = pod.salvage_worktree(self.t, self.tmp)
        self.assertEqual(bad, [])
        self.assertEqual(dest.read_text(), "-- WORKER PROBE\n")

    def test_no_worktree_is_a_noop(self):
        shutil.rmtree(self.wt)
        self.assertEqual(pod.salvage_worktree(self.t, self.tmp), [])

    def test_an_untouched_brief_does_not_block_salvage_when_main_committed_it(self):
        """LJ-1.386, 2026-08-20: A21 retargeted the brief on main after the
        worktree forked. Salvage walked the whole home, the brief collided,
        and a `sys-obligations-satisfied` close parked `salvage:` in a loop."""
        dest = self.tmp / "agents" / "tasks" / "LJ-1-399" / "LJ-1.399.md"
        dest.write_text(dest.read_text() + "head_slot: coder\n")
        subprocess.run(["git", "add", "-A"], cwd=self.tmp, capture_output=True)
        subprocess.run(["git", "commit", "-qm", "retarget brief"],
                       cwd=self.tmp, capture_output=True)
        (self.whome / "lj-1.399-report.md").write_text("report\n")
        bad = pod.salvage_worktree(self.t, self.tmp)
        self.assertEqual(bad, [])
        self.assertIn("head_slot: coder", dest.read_text())
        self.assertEqual(
            (self.tmp / "agents" / "tasks" / "LJ-1-399" / "lj-1.399-report.md")
            .read_text(),
            "report\n")

    def test_identical_bytes_are_not_a_collision_even_if_both_sides_moved(self):
        """LJ-1.386 seq 813: worktree brief already matched main, both differed
        from the fork, and salvage still parked."""
        dest = self.tmp / "agents" / "tasks" / "LJ-1-399" / "LJ-1.399.md"
        text = dest.read_text() + "head_slot: coder\n"
        dest.write_text(text)
        subprocess.run(["git", "add", "-A"], cwd=self.tmp, capture_output=True)
        subprocess.run(["git", "commit", "-qm", "retarget brief"],
                       cwd=self.tmp, capture_output=True)
        (self.whome / "LJ-1.399.md").write_text(text)
        (self.whome / "lj-1.399-report.md").write_text("report\n")
        bad = pod.salvage_worktree(self.t, self.tmp)
        self.assertEqual(bad, [])
        self.assertEqual(
            (self.tmp / "agents" / "tasks" / "LJ-1-399" / "lj-1.399-report.md")
            .read_text(),
            "report\n")


if __name__ == "__main__":
    unittest.main(verbosity=2)
