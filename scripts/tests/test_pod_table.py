#!/usr/bin/env python3
"""Regression tests for the POD table, the router, the replay, the admission and the
pre-flight.

WHY THIS FILE EXISTS. Every rule under test was bought with a measured failure, and each
one, read back wrongly, sends a real return to the wrong place:

1. **A3, `stop_loop` sorts first.** `sys-spec-surface` is a SYSTEM row and a task branch
   that reads only `seconds_min` and `changed_files_count_max` matches the same record.
   Without A3 that branch outranks the system row and the loop keeps running through a
   change to the trophy statement.
2. **The concurrency guard.** A contended cold gate measured 150.09 s against 133.69 s,
   so a seconds key against a record whose `concurrency` is not 1 compares two different
   quantities. `matches()` fails the key instead, and a record carrying `null` never
   raises.
3. **R3, the replay.** A widened `when` block that captures another row's traffic changes
   what a PAST return means. The replay compares the pair `(row_id, action)` over frozen
   records, so the change is arithmetic and not an opinion.
4. **Admission namespacing.** A branch id is a bare word inside one brief, so two briefs
   both writing `go` collide in a table whose ids are unique table-wide.
5. **P18 and P20 together.** P18 puts an attacking branch in every brief, and P20 exists
   because that branch can kill the `done` branch it protects: if it outranks a `done`
   branch and both match one record, `route()` reproduces the same winner on every retry
   and `attempt_max` parks the task instead of closing it.
6. **P19 with A6.** A NO-GO leaves every declared name unresolved, so its delta is 0 and
   the delta limb can never hold. Without the `outcome = "no-go"` limb, no brief could
   express a refusal.
7. **The record boundary, and it was a measured crash.** A corpus line whose
   `obligations_delta` held a string reached `matches()` and raised `TypeError` on `>=`.
   `admit_rows()` catches `TableError` and `OSError` and never a `TypeError`, so the
   traceback stopped an unattended loop. `check_record()` now tests the TYPE of every
   fact, at the one boundary a record enters through.
8. **A10, DD24's ratio bar.** Gap M13 named the hole: with no ratio row, slow code closes
   green. One seeded system row carries the bar, and `matches()` fails its keys rather
   than raising when a record carries no `lines`.

NO TEST HERE STARTS AGDA, and no test writes into the repository. Every table write goes
to a temporary directory, `git_commit` is replaced by a recorder, and P16's subprocess is
passed in as a value. EXACTLY ONE TEST SPAWNS A PROCESS,
`test_the_script_entry_point_catches_a_refusal_raised_inside_replay`, because the defect
it pins lives only in the `__main__` import path and no in-process call can reach it.

THE FIXTURE CAN FAIL, which is C-45. Each pre-flight test builds the SAME brief that
passes all 22 checks, breaks exactly one thing, and asserts both the refusal and the pass.

Run: `python3 scripts/tests/test_pod_table.py`
"""

from __future__ import annotations

import contextlib
import datetime
import importlib.util
import io
import json
import re
import shutil
import subprocess
import sys
import tempfile
import tomllib
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


table = _load("table", "scripts/pod/table.py")
replay_mod = _load("replay", "scripts/pod/replay.py")
preflight_mod = _load("preflight", "scripts/pod/preflight.py")
facts = _load("pod_facts", "scripts/pod/facts.py")

DAY = datetime.date(2026, 8, 17)
SLOTS = ("mathematician", "mathematician_adversarial", "coder", "coder_adversarial",
         "maintainer")


# ---------------------------------------------------------------- fixtures


_DEFAULT_WHEN = object()


def row(rid, action="park", scope="system", priority=100, when=_DEFAULT_WHEN, **kw):
    """One well-formed row. Only the varying fields are written at a call site."""
    when = {"heap_wall": True} if when is _DEFAULT_WHEN else when
    out = {"id": rid, "scope": scope, "priority": priority, "action": action,
           "added": DAY, "added_by": "maintainer", "reason": "a test row",
           "expired": False, "when": dict(when)}
    out.update(kw)
    return out


def record(rid="c-1", task="LJ-1.386", exit_code=0, error_class=None, delta=0,
           changed=("agents/tasks/LJ-1-386/Probe386.agda",), seconds=1.0,
           heap_wall=False, concurrency=1, lines=None, **kw):
    """One whole record, in the shape section 4.5.2 stores and section 5.3.1 logs.

    `lines` is fact 7 under amendment A10 and it joins the SIX inside `facts`, never at
    the top level. It is omitted by default, because a six-fact record is what the log
    format still writes and what every fact 7 key must fail against.
    """
    out = {"id": rid, "task": task, "concurrency": concurrency,
           "caliber": facts.CAP,
           "facts": {"exit_code": exit_code, "error_class": error_class,
                     "obligations_delta": delta, "changed_files": list(changed),
                     "seconds": seconds, "heap_wall": heap_wall}}
    if lines is not None:
        out["facts"]["lines"] = lines
    out.update(kw)
    return out


#: ONE VALUE PER ADMITTED `[row.when]` KEY, chosen so that every key DECIDES the probe
#: record below rather than short-circuiting. `Matches` drives the whole set, because a
#: count of the keys cannot see a key that `matches()` has no branch for.
WHEN_PROBE = {
    "exit_code": 42,
    "exit_code_in": [42, 251],
    "exit_code_absent": False,
    "error_class": "termination",
    "error_class_in": ["termination", "other"],
    "obligations_delta_min": -1,
    "obligations_delta_max": 1,
    "changed_files_any": ["src/*"],
    "changed_files_none": ["dev/*"],
    "changed_files_all_within": ["src/*"],
    "changed_files_count_min": 1,
    "changed_files_count_max": 9,
    "seconds_min": 1.0,
    "seconds_max": 100.0,
    "heap_wall": False,
    "seconds_per_line_min": 0.001,
    "seconds_per_line_max": 0.1,
}


BRANCHES_386 = """\
```toml pod-branches
[[branch]]          # The obligation is discharged and both names resolve.
id = "go"
priority = 10
action = "done"
outcome = "go"

  [branch.when]
  exit_code = 0
  obligations_delta_max = -2
  heap_wall = false

[[branch]]          # A stated NO-GO, once the adversarial head has read it.
id = "no-go-stated"
priority = 20
action = "done"
outcome = "no-go"

  [branch.when]
  exit_code = 42
  error_class = "unsolved_meta"
  changed_files_any = ["agents/tasks/LJ-1-386/review-of-*.md"]

[[branch]]          # P18 requires this one in EVERY brief.
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
id = "heap-wall-escalate"
priority = 30
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  heap_wall = true

[[branch]]
id = "ran-long-and-changed-little"
priority = 50
action = "park"

  [branch.when]
  seconds_min = 3600.0
  changed_files_count_max = 1
```
"""

BRIEF_386 = """\
# LJ-1.386: internal existence of a pairing code at a band ordinal, GO or NO-GO

## HEAD
head_slot: mathematician
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
- `small-inj` gives the injection. Basis: src/L/Coding/Injection.lagda.md:147-151

## WHAT IS DELIVERED ALREADY
- `Good`, the predicate the code must satisfy: src/L/Cardinal.lagda.md:186-189

## WHAT IS MISSING
The inhabitation of the truncated sum.

## LAWS (program-generated, do not edit)
- D-1: write the probe in the task directory and run it while the task is live.

## ARCHIVE (program-generated, do not edit)
Corpus search for: L.Cardinal, Good, small-inj
- archive/dev/TASKS-archived.md:80    (1 key hit)
- archive/dev/JOURNAL-archived.md     NO HIT

## LITERATURE (program-generated, do not edit)
Corpus search for: pairing code, band ordinal
- dev/literature/j-hierarchy.md       NO HIT

## THE REASONING
The prose half. It is never executed and it gates nothing.

## WHAT GO AND NO-GO EACH EARN
A NO-GO is worth as much as a GO here.

## BRANCHES
""" + BRANCHES_386


def build_tree(tmp: Path, brief_text: str = BRIEF_386) -> Path:
    """A minimal repository the pre-flight can read, with the worked brief of section 6.4.

    THE BRIEF IS SECTION 6.4'S, WITH ONE ADDITION. Section 6.4 writes out every section of
    the worked example and omits `## LAWS`, which pre-flight P21 refuses a brief without.
    The fixture adds that block, so the example passes all 22 checks.
    """
    (tmp / "dev" / "pod").mkdir(parents=True, exist_ok=True)
    shutil.copy(ROOT / "dev" / "pod" / "heads.toml", tmp / "dev" / "pod" / "heads.toml")
    (tmp / "dev" / "literature").mkdir(parents=True, exist_ok=True)
    (tmp / "dev" / "literature" / "j-hierarchy.md").write_text("literature\n")
    (tmp / "archive" / "dev").mkdir(parents=True, exist_ok=True)
    for name in ("TASKS-archived.md", "JOURNAL-archived.md"):
        (tmp / "archive" / "dev" / name).write_text("x\n" * 200)
    (tmp / "src" / "L" / "Coding").mkdir(parents=True, exist_ok=True)
    (tmp / "src" / "L" / "Cardinal.lagda.md").write_text("line\n" * 300)
    (tmp / "src" / "L" / "Coding" / "Injection.lagda.md").write_text("line\n" * 300)
    task = tmp / "agents" / "tasks" / "LJ-1-386"
    task.mkdir(parents=True, exist_ok=True)
    brief = task / "LJ-1.386.md"
    brief.write_text(brief_text, encoding="utf-8")
    return brief


class TreeCase(unittest.TestCase):
    """One temporary repository per test. Nothing here writes into the real tree."""

    def setUp(self):
        self.dir = tempfile.TemporaryDirectory()
        self.tmp = Path(self.dir.name)
        self.addCleanup(self.dir.cleanup)

    def brief(self, text=BRIEF_386):
        return build_tree(self.tmp, text)

    def run_preflight(self, text=BRIEF_386, **kw):
        b = self.brief(text)
        return preflight_mod.preflight(b, root=self.tmp, show=False, closure=True,
                                       slots=SLOTS, **kw)


# ---------------------------------------------------------------- the loader


class Loader(TreeCase):
    """Section 4.2. The loader refuses an unknown key, so a typo never becomes a silent
    no-match row that a maintainer reads as coverage."""

    def load(self, rows, schema=None, vocab=None):
        """The rows, written out and read back, with `schema` or `vocab` replaced.

        THE FIXTURE CAN FAIL, which is C-45: each substitution is asserted, so a rename in
        `dump_table()` cannot turn a refusal test into a test of an unchanged file.
        """
        text = table.dump_table([table.check_row(r, SLOTS) for r in rows])
        if schema is not None:
            self.assertIn("schema = 1", text)
            text = text.replace("schema = 1", f"schema = {schema}")
        if vocab is not None:
            self.assertIn(f'vocab = "{table.VOCAB}"', text)
            text = text.replace(f'vocab = "{table.VOCAB}"', f'vocab = "{vocab}"')
        p = self.tmp / "t.toml"
        p.parent.mkdir(parents=True, exist_ok=True)
        p.write_text(text, encoding="utf-8")
        return table.load_table(p, SLOTS)

    def test_the_seeded_table_loads_and_carries_the_five_system_rows(self):
        """The fifth is amendment A10's, and it carries DD24's restored ratio bar."""
        rows = table.load_table()
        # A SUPERSET, NOT AN EQUALITY, since 2026-08-18. `dev/pod/table.toml` is a LIVE
        # file: rule (a1) writes a `task-<code>-*` row into it on every CREATE, so an
        # equality here is green only until the program runs once, and then red forever.
        # A gate that a working program turns red is a gate nobody reads. The invariant
        # is that the five SYSTEM rows are all present and none has expired; the task
        # rows are runtime and belong to no assertion.
        system = sorted(r["id"] for r in rows if r["id"].startswith("sys-"))
        self.assertEqual(system,
                         ["sys-coder-adversarial-on-heap-wall", "sys-dd24-ratio-bar",
                          "sys-heap-wall", "sys-slow-green-empty", "sys-spec-surface"])
        # THE SECOND ASSERTION MUST BE ABLE TO FAIL ON ITS OWN, and an id list said twice
        # cannot. This one reads BEHAVIOUR: a plain green return that no seeded row models
        # reaches NO MATCH and parks under R5. A seed row widened by one key would route
        # it, and not one id would change.
        self.assertEqual(table.route(rows, record(exit_code=0, seconds=2.0, delta=-1)),
                         (None, None))
        self.assertTrue(all(not r["expired"] for r in rows))

    def test_the_seeded_table_declares_the_seventh_fact_vocabulary(self):
        """Section 4.2 bumps `vocab` when the fact set changes and A10 changed it: fact 7
        `lines` joined the six of AD11."""
        text = (ROOT / "dev" / "pod" / "table.toml").read_text(encoding="utf-8")
        self.assertIn('vocab = "seven-facts/1"', text)
        self.assertNotIn("six-facts/1", text)

    def test_the_seeded_ratio_row_carries_the_bar_and_names_its_basis(self):
        """A10 rules ONE seeded system row for DD24's bar. Its figure comes from
        `agents/tasks/LJ-4-0/l9.0-b3-probe-report.md:185`, 0.01069 s per in-fence line, at
        the `[ratio]` tolerance. The reason names that record, because a bar whose basis
        is not written down is the drift DD24's own amendment was ruled against."""
        bar = next(r for r in table.load_table() if r["id"] == "sys-dd24-ratio-bar")
        self.assertEqual(sorted(bar["when"]),
                         ["exit_code", "heap_wall", "seconds_per_line_min"])
        self.assertEqual(bar["when"]["exit_code"], 0)
        self.assertGreater(bar["when"]["seconds_per_line_min"], 0.01069)
        # THE BASIS IS BOTH HALVES, the record AND the figure it measured. A reason that
        # names the file and drops the rate leaves the bar unreadable, and an unreadable
        # bar is how DD24's own number drifted for three days.
        self.assertIn("l9.0-b3-probe-report.md:185", bar["reason"])
        self.assertIn("0.01069", bar["reason"])
        self.assertEqual(bar["added_by"], "owner")

    def test_the_ratio_pair_is_the_only_fact_seven_key(self):
        """A10 names the FACT and no key, so `table.py` picks ONE pair and says so in its
        docstring. `lines_min` and `lines_max` were invented by the first build and no
        ruled bar needs them: a key nothing needs is a key every maintainer must read."""
        for key in ("lines", "lines_min", "lines_max"):
            self.assertNotIn(key, table.WHEN_TYPES)
            with self.assertRaises(table.TableError):
                table.check_row(row("r", when={key: 1}), SLOTS)
        for key in ("seconds_per_line_min", "seconds_per_line_max"):
            self.assertIn(key, table.WHEN_TYPES)
            self.assertEqual(table.check_row(row("r", when={key: 0.5}), SLOTS)["when"],
                             {key: 0.5})

    def test_a_rewrite_of_the_seeded_table_is_byte_identical(self):
        """`write_table()` rewrites the whole file at every admission. A re-write that
        moved one byte would put noise in every review diff."""
        live = (ROOT / "dev" / "pod" / "table.toml").read_text(encoding="utf-8")
        self.assertEqual(table.dump_table(table.load_table()), live)

    def test_an_unknown_row_key_is_refused(self):
        with self.assertRaises(table.TableError):
            table.check_row(row("r", tier="wide"), SLOTS)

    def test_an_unknown_when_key_is_refused(self):
        """R1: a branch matches only the facts of AD11. The loader catches the key first,
        so `matches()` raising `KeyError` stays an alarm and never a routine path."""
        with self.assertRaises(table.TableError):
            table.check_row(row("r", when={"concurrency": 1}), SLOTS)

    def test_an_empty_when_block_is_refused(self):
        with self.assertRaises(table.TableError):
            table.check_row(row("r", when={}), SLOTS)

    def test_head_slot_is_required_exactly_when_the_action_escalates(self):
        with self.assertRaises(table.TableError):
            table.check_row(row("r", action="escalate"), SLOTS)
        with self.assertRaises(table.TableError):
            table.check_row(row("r", action="park", head_slot="coder"), SLOTS)
        ok = table.check_row(row("r", action="escalate", head_slot="coder"), SLOTS)
        self.assertEqual(ok["head_slot"], "coder")

    def test_a_head_slot_outside_heads_toml_is_refused(self):
        with self.assertRaises(table.TableError):
            table.check_row(row("r", action="escalate", head_slot="reviewer"), SLOTS)

    def test_outcome_is_required_exactly_when_the_action_is_done(self):
        with self.assertRaises(table.TableError):
            table.check_row(row("r", action="done"), SLOTS)
        with self.assertRaises(table.TableError):
            table.check_row(row("r", action="park", outcome="go"), SLOTS)
        self.assertEqual(
            table.check_row(row("r", action="done", outcome="no-go"), SLOTS)["outcome"],
            "no-go")

    def test_every_one_of_the_eight_actions_loads_and_a_ninth_is_refused(self):
        """COUNTING THE EIGHT PROVES NOTHING. An action named in `ACTIONS` that the
        conditional-field rules cannot express would keep the count honest and refuse
        every row that used it, so each one is LOADED here instead."""
        for action in table.ACTIONS:
            extra = {}
            if action == "escalate":
                extra["head_slot"] = "coder"
            if action == "done":
                extra["outcome"] = "go"
            if action == "stop_loop":
                # `stop_loop` IS OWNER-ONLY since 2026-08-19, and `row()` defaults to
                # `added_by = "maintainer"`. The refusal is asserted on its own in
                # `StopLoopIsOwnerOnly`; here the point is only that the action LOADS.
                extra["added_by"] = "owner"
            got = table.check_row(row("r", action=action, **extra), SLOTS)
            self.assertEqual(got["action"], action)
        with self.assertRaises(table.TableError):
            table.check_row(row("r", action="retry"), SLOTS)

    def test_a_duplicate_id_is_refused(self):
        with self.assertRaises(table.TableError):
            table.check_table([table.check_row(row("r"), SLOTS),
                               table.check_row(row("r", priority=2), SLOTS)])

    def test_two_rows_of_one_scope_at_one_priority_are_refused(self):
        """Step 4 of section 4.4 stays an ALARM. If two rows of one scope could share a
        priority, the byte order of a name would silently decide a routing."""
        with self.assertRaises(table.TableError):
            table.check_table([table.check_row(row("a", priority=7), SLOTS),
                               table.check_row(row("b", priority=7), SLOTS)])
        table.check_table([table.check_row(row("a", priority=7), SLOTS),
                           table.check_row(row("b", priority=7, scope="task:LJ-1.1"),
                                           SLOTS)])

    def test_a_reason_over_two_hundred_characters_is_refused(self):
        with self.assertRaises(table.TableError):
            table.check_row(row("r", reason="x" * 201), SLOTS)

    def test_an_unknown_schema_or_vocab_is_refused(self):
        """`six-facts/1` IS THE ONE THIS LOADER USED BEFORE A10, and it is now refused. A
        table written for another fact set would otherwise be routed by a vocabulary its
        author never agreed to."""
        self.assertEqual(table.VOCAB, "seven-facts/1")
        with self.assertRaises(table.TableError):
            self.load([row("r")], schema=2)
        with self.assertRaises(table.TableError):
            self.load([row("r")], vocab="six-facts/1")
        self.assertEqual([r["id"] for r in self.load([row("r")])], ["r"])

    def test_expired_at_is_present_exactly_when_the_row_is_expired(self):
        with self.assertRaises(table.TableError):
            table.check_row(row("r", expired=True), SLOTS)
        with self.assertRaises(table.TableError):
            table.check_row(row("r", expired_at=DAY), SLOTS)

    def test_a_when_value_of_the_wrong_type_is_refused(self):
        for when in ({"exit_code": "0"}, {"heap_wall": "true"}, {"seconds_min": "3"},
                     {"error_class_in": "unsolved_meta"}, {"changed_files_any": []},
                     {"exit_code_in": ["0"]}):
            with self.assertRaises(table.TableError):
                table.check_row(row("r", when=when), SLOTS)


# ---------------------------------------------------------------- matches


class Matches(unittest.TestCase):
    """AD11's six facts, amendment A5's exit codes and amendment A1's delta."""

    def test_every_admitted_key_is_reachable_and_nothing_else_is(self):
        """R1, and a COUNT of the keys cannot prove it. A key added to `WHEN_TYPES` with
        no branch in `matches()` keeps any count honest, loads into a row, and raises
        `KeyError` on the first record that reaches it. So every admitted key is DRIVEN
        here, against a record it must decide, and the closed list is compared by NAME."""
        self.assertEqual(set(WHEN_PROBE), set(table.WHEN_TYPES))
        rec = record(exit_code=42, error_class="termination",
                     changed=["src/L/Foo.lagda.md"], seconds=10.0, lines=1000)
        for key, value in WHEN_PROBE.items():
            self.assertIs(table.matches({key: value}, rec), True, key)
        with self.assertRaises(KeyError):
            table.matches({"concurrency": 1}, rec)

    def test_the_five_exit_codes_of_amendment_a5(self):
        self.assertTrue(table.matches({"exit_code": 0}, record(exit_code=0)))
        self.assertTrue(table.matches({"exit_code": 42}, record(exit_code=42)))
        self.assertTrue(table.matches({"exit_code": 251}, record(exit_code=251)))
        self.assertTrue(table.matches({"exit_code": 1}, record(exit_code=1)))
        self.assertTrue(table.matches({"exit_code_absent": True},
                                      record(exit_code=None)))
        self.assertFalse(table.matches({"exit_code_absent": True}, record(exit_code=0)))
        self.assertTrue(table.matches({"exit_code_in": [42, 251]}, record(exit_code=251)))

    def test_the_eleven_error_classes_route_and_a_green_run_matches_none(self):
        for cls in facts.ERROR_CLASSES:
            self.assertTrue(table.matches({"error_class": cls},
                                          record(exit_code=1, error_class=cls)))
        green = record(exit_code=0, error_class=None)
        for cls in facts.ERROR_CLASSES:
            self.assertFalse(table.matches({"error_class": cls}, green))
        self.assertTrue(table.matches({"exit_code": 0}, green))

    def test_the_obligation_delta_is_a_range(self):
        """Amendment A1. A task that discharges two names gives -2, and a task that writes
        nothing gives 0, which is what keeps a `go` branch off a dead worker."""
        self.assertTrue(table.matches({"obligations_delta_max": -2}, record(delta=-2)))
        self.assertFalse(table.matches({"obligations_delta_max": -2}, record(delta=0)))
        self.assertTrue(table.matches({"obligations_delta_min": 0,
                                       "obligations_delta_max": 0}, record(delta=0)))

    def test_the_four_changed_file_keys(self):
        ch = ["src/L/Foo.lagda.md", "agents/tasks/LJ-1-386/lj-1.386-report.md"]
        r = record(changed=ch)
        self.assertTrue(table.matches({"changed_files_any": ["src/*"]}, r))
        self.assertFalse(table.matches({"changed_files_none": ["src/*"]}, r))
        self.assertTrue(table.matches({"changed_files_none": ["dev/*"]}, r))
        self.assertTrue(table.matches(
            {"changed_files_all_within": ["src/*", "agents/tasks/*"]}, r))
        self.assertFalse(table.matches({"changed_files_all_within": ["src/*"]}, r))
        self.assertTrue(table.matches({"changed_files_count_min": 2,
                                       "changed_files_count_max": 2}, r))

    def test_a_glob_is_case_sensitive(self):
        """`fnmatch.fnmatchcase`, so a case-folding filesystem never decides a routing."""
        r = record(changed=["src/L/Foo.lagda.md"])
        self.assertFalse(table.matches({"changed_files_any": ["SRC/*"]}, r))

    def test_a_seconds_key_fails_against_a_contended_record(self):
        """A contended cold gate measured 150.09 s against 133.69 s, so the record's
        `concurrency` guards every seconds key. It is a GUARD and never a matcher."""
        self.assertTrue(table.matches({"seconds_min": 300.0},
                                      record(seconds=456.0, concurrency=1)))
        self.assertFalse(table.matches({"seconds_min": 300.0},
                                       record(seconds=456.0, concurrency=2)))

    def test_a_record_with_no_process_count_never_raises_and_never_matches_seconds(self):
        """A hand-copied `report` record carries `null`, and section 4.5.2 forbids
        guessing a process count."""
        r = record(seconds=456.0)
        del r["concurrency"]
        self.assertFalse(table.matches({"seconds_min": 1.0}, r))
        self.assertTrue(table.matches({"exit_code": 0}, r))

    def test_the_heap_wall_is_a_boolean_both_ways(self):
        self.assertTrue(table.matches({"heap_wall": True}, record(heap_wall=True)))
        self.assertTrue(table.matches({"heap_wall": False}, record(heap_wall=False)))
        self.assertFalse(table.matches({"heap_wall": True}, record(heap_wall=False)))

    def test_every_key_of_one_block_is_and_ed(self):
        """A row holds no OR. Section 4.2 states it and this is the arithmetic."""
        when = {"exit_code": 0, "heap_wall": False, "obligations_delta_max": 0}
        self.assertTrue(table.matches(when, record(exit_code=0, delta=-1)))
        self.assertFalse(table.matches(when, record(exit_code=42, delta=-1)))

    def test_fact_seven_of_amendment_a10_is_absent_from_a_six_fact_record(self):
        """A10 restores DD24's RATIO form. A record that carries no `lines` fails every
        fact 7 key rather than raising, which is the same direction the seconds guard
        takes. The log format still writes six facts, so this is the common case."""
        self.assertFalse(table.matches({"seconds_per_line_max": 1.0}, record()))
        self.assertFalse(table.matches({"seconds_per_line_min": 0.0}, record()))
        self.assertTrue(table.matches({"exit_code": 0}, record()))

    def test_the_ratio_divides_and_a_zero_divisor_never_raises(self):
        wide = record(seconds=100.0, lines=10000)          # 0.01 s per line
        self.assertTrue(table.matches({"seconds_per_line_max": 0.02}, wide))
        self.assertTrue(table.matches({"seconds_per_line_min": 0.01}, wide))
        self.assertFalse(table.matches({"seconds_per_line_min": 0.02}, wide))
        empty = record(seconds=100.0, lines=0)
        self.assertFalse(table.matches({"seconds_per_line_min": 0.0}, empty))
        self.assertFalse(table.matches({"seconds_per_line_max": 9e9}, empty))

    def test_the_ratio_keys_obey_the_same_concurrency_guard_as_the_seconds_keys(self):
        """A ratio built from contended seconds is the same bad comparison the seconds
        guard exists for, so the guard covers the numerator wherever it appears."""
        contended = record(seconds=100.0, lines=10000, concurrency=4)
        alone = record(seconds=100.0, lines=10000)
        for key, value in (("seconds_per_line_max", 0.02),
                           ("seconds_per_line_min", 0.001)):
            self.assertFalse(table.matches({key: value}, contended), key)
            self.assertTrue(table.matches({key: value}, alone), key)
        unstated = record(seconds=100.0, lines=10000)
        del unstated["concurrency"]
        self.assertFalse(table.matches({"seconds_per_line_max": 0.02}, unstated))


# ---------------------------------------------------------------- route


class Route(unittest.TestCase):
    """Section 4.4's one total order, and it involves no judgement."""

    def test_no_match_returns_a_pair_of_none(self):
        """R5: no match PARKS the task. A fallback row would turn every unmodelled return
        into a routing nobody wrote."""
        self.assertEqual(table.route([row("r", when={"heap_wall": True})],
                                     record(heap_wall=False)), (None, None))

    def test_a_stop_loop_row_outranks_a_task_row_of_any_priority(self):
        """AMENDMENT A3, and this is the case that bought it: a task branch reading only
        `seconds_min` and `changed_files_count_max` never mentions fact 1, so it matches a
        spec surface record and would otherwise let the loop run on."""
        sys_row = row("sys-spec-surface", action="stop_loop", priority=1,
                      when={"error_class": "spec_surface"})
        task_row = row("task-lj-1-386-slow", action="park", scope="task:LJ-1.386",
                       priority=1, when={"seconds_min": 1.0,
                                         "changed_files_count_max": 5})
        rec = record(exit_code=1, error_class="spec_surface", seconds=9.0)
        self.assertEqual(table.route([task_row, sys_row], rec),
                         ("sys-spec-surface", "stop_loop"))

    def test_a_task_row_beats_a_system_row_at_a_worse_priority(self):
        sysr = row("sys-heap-wall", action="park_and_split", priority=1,
                   when={"heap_wall": True})
        task = row("task-lj-1-386-heap", action="accept", scope="task:LJ-1.386",
                   priority=900, when={"heap_wall": True})
        self.assertEqual(table.route([sysr, task], record(heap_wall=True)),
                         ("task-lj-1-386-heap", "accept"))

    def test_priority_then_id_decides_two_rows_of_one_scope(self):
        a = row("aaa", action="park", priority=10)
        b = row("bbb", action="accept", priority=20)
        self.assertEqual(table.route([b, a], record(heap_wall=True))[0], "aaa")
        c = row("ccc", action="accept", priority=10, scope="task:LJ-1.386")
        d = row("ddd", action="park", priority=20, scope="task:LJ-1.386")
        self.assertEqual(table.route([d, c], record(heap_wall=True))[0], "ccc")

    def test_another_tasks_row_never_grades_this_return(self):
        other = row("task-lj-1-375-mustfail", action="accept", scope="task:LJ-1.375",
                    priority=10, when={"exit_code": 42})
        rec = record(task="LJ-1.386", exit_code=42)
        self.assertEqual(table.route([other], rec), (None, None))
        mine = dict(other, id="task-lj-1-386-mustfail", scope="task:LJ-1.386")
        self.assertEqual(table.route([mine], rec)[1], "accept")

    def test_an_expired_row_never_wins_and_stays_in_the_file(self):
        """THE ROUTER DROPS IT, and the caller does not. The old second assertion counted
        a two-element list literal written on the same line, which no change to this
        program could ever make false. These two read the router instead: the expired row
        is absent from the hit list, and the SAME row un-expired wins."""
        live = row("sys-heap-wall", action="park_and_split")
        dead = row("task-lj-1-266-heap", action="accept", scope="task:LJ-1.266",
                   priority=1, expired=True, expired_at=DAY)
        rec = record(task="LJ-1.266", heap_wall=True)
        self.assertEqual(table.route([dead, live], rec)[0], "sys-heap-wall")
        self.assertEqual([r["id"] for r in table.hits([dead, live], rec)],
                         ["sys-heap-wall"])
        revived = {k: v for k, v in dead.items() if k != "expired_at"}
        revived["expired"] = False
        self.assertEqual(table.route([revived, live], rec),
                         ("task-lj-1-266-heap", "accept"))

    def test_the_hit_list_reports_shadowing_and_never_refuses_it(self):
        """Section 4.4: shadowing is REPORTED, not refused. The digest re-runs this list
        over the window and prints how often a row lost, so a row that never wins in
        30 days is a maintainer signal."""
        heap = row("sys-heap-wall", action="park_and_split", priority=100,
                   when={"heap_wall": True})
        coder = row("sys-coder-adversarial-on-heap-wall", action="escalate",
                    head_slot="coder_adversarial", priority=90,
                    when={"heap_wall": True, "changed_files_any": ["src/*"]})
        rec = record(heap_wall=True, changed=["src/L/Sucker.lagda.md"])
        got = table.hits([heap, coder], rec)
        self.assertEqual([r["id"] for r in got],
                         ["sys-coder-adversarial-on-heap-wall", "sys-heap-wall"])
        self.assertEqual(table.route([heap, coder], rec)[1], "escalate")


class SeededRows(unittest.TestCase):
    """The four seeded system rows against the three returns section 4.8 cites."""

    def setUp(self):
        self.rows = table.load_table()

    def test_lj_1_266_heap_wall_routes_to_park_and_split(self):
        """`agents/tasks/LJ-1-266/lj-1.266-report.md:73` states MEASURED "Heap exhausted"
        at 8,192 MB, exit 251, and `:209` states only `agents/tasks/LJ-1-266/` written."""
        rec = record(task="LJ-1.266", exit_code=251, error_class="heap_wall",
                     heap_wall=True,
                     changed=["agents/tasks/LJ-1-266/lj-1.266-report.md"])
        self.assertEqual(table.route(self.rows, rec),
                         ("sys-heap-wall", "park_and_split"))

    def test_a_heap_wall_inside_src_reaches_the_stronger_head_first(self):
        rec = record(task="LJ-1.266", exit_code=251, error_class="heap_wall",
                     heap_wall=True, changed=["src/L/Cardinal.lagda.md"])
        self.assertEqual(table.route(self.rows, rec),
                         ("sys-coder-adversarial-on-heap-wall", "escalate"))

    def test_lj_1_381_slow_green_and_empty_reaches_the_coder_critic(self):
        """`agents/tasks/LJ-1-381/lj-1.381-report.md:80-83` states 456 s against a 2.5 s
        floor, exit 0, and nothing landed in `src/`."""
        rec = record(task="LJ-1.381", exit_code=0, seconds=456.0, delta=0,
                     changed=["agents/tasks/LJ-1-381/lj-1.381-report.md"])
        self.assertEqual(table.route(self.rows, rec),
                         ("sys-slow-green-empty", "escalate"))

    def test_a_green_run_over_dd24s_restored_ratio_bar_reaches_the_coder_critic(self):
        """AMENDMENT A10 closes gap M13: with no ratio row, slow code closes green. The
        bar is seconds over in-fence lines, seeded from
        `agents/tasks/LJ-4-0/l9.0-b3-probe-report.md:185`."""
        over = record(task="LJ-1.386", exit_code=0, seconds=200.0, lines=10000, delta=-1,
                      changed=["src/L/Cardinal.lagda.md"])
        self.assertEqual(table.route(self.rows, over),
                         ("sys-dd24-ratio-bar", "escalate"))
        under = record(task="LJ-1.386", exit_code=0, seconds=100.0, lines=10000, delta=-1,
                       changed=["src/L/Cardinal.lagda.md"])
        self.assertEqual(table.route(self.rows, under), (None, None))

    def test_the_ratio_bar_never_fires_on_a_record_that_carries_no_lines(self):
        """The bar needs fact 7, and fact 7 is absent whenever the write scope was not
        counted. The row then fails rather than guessing a divisor, which is R7."""
        blind = record(task="LJ-1.386", exit_code=0, seconds=200.0, delta=-1,
                       changed=["src/L/Cardinal.lagda.md"])
        self.assertEqual(table.route(self.rows, blind), (None, None))

    def test_a_spec_surface_record_stops_the_loop(self):
        rec = record(task="LJ-1.386", exit_code=1, error_class="spec_surface",
                     changed=["src/Landmarks.lagda.md"])
        self.assertEqual(table.route(self.rows, rec),
                         ("sys-spec-surface", "stop_loop"))

    def test_lj_1_375_must_fail_no_matches_until_its_task_row_exists(self):
        """A task row inverts the default for one task. Without it a must-fail control's
        exit 42 reaches NO MATCH and parks, which is R5 and not a routing."""
        rec = record(task="LJ-1.375", exit_code=42, error_class="universe_level",
                     changed=["agents/tasks/LJ-1-375/MustFail375A.agda"])
        self.assertEqual(table.route(self.rows, rec), (None, None))
        task = row("task-lj-1-375-mustfail", action="accept", scope="task:LJ-1.375",
                   priority=10,
                   when={"exit_code": 42, "error_class": "universe_level",
                         "changed_files_any": ["agents/tasks/LJ-1-375/MustFail*.agda"],
                         "heap_wall": False})
        self.assertEqual(table.route(self.rows + [table.check_row(task, SLOTS)], rec),
                         ("task-lj-1-375-mustfail", "accept"))


# ---------------------------------------------------------------- the replay


class Replay(unittest.TestCase):
    """AD10. The test is REGRESSION ONLY and it needs no ground-truth label."""

    def setUp(self):
        self.old = [table.check_row(row("sys-heap-wall", action="park_and_split",
                                        priority=100, when={"heap_wall": True}), SLOTS)]
        self.rec = record(heap_wall=True, changed=["src/L/Foo.lagda.md"])

    def test_a_record_that_never_matched_may_become_a_match(self):
        """Added coverage is the REASON to add a row, so a new match is admitted."""
        green = record(rid="c-2", exit_code=0)
        new = self.old + [table.check_row(row("sys-green", action="accept", priority=50,
                                              when={"exit_code": 0}), SLOTS)]
        self.assertEqual(replay_mod.replay(self.old, new, [green])[0], "ADMIT")

    def test_a_row_that_captures_another_rows_traffic_is_rejected(self):
        new = self.old + [table.check_row(
            row("sys-heap-wall-src", action="escalate", head_slot="coder_adversarial",
                priority=90, when={"heap_wall": True}), SLOTS)]
        verdict, moved = replay_mod.replay(self.old, new, [self.rec])
        self.assertEqual(verdict, "REJECT")
        self.assertEqual(moved, [("c-1", "sys-heap-wall", "park_and_split",
                                  "sys-heap-wall-src", "escalate")])

    def test_a_changed_action_on_one_row_is_a_rejection(self):
        """An EDIT is a remove plus an add, and the same test guards it."""
        new = [dict(self.old[0], action="park")]
        self.assertEqual(replay_mod.replay(self.old, new, [self.rec])[0], "REJECT")

    def test_an_expiry_moves_traffic_and_the_replay_is_not_what_guards_it(self):
        """Section 4.6: expiry is EXEMPT from R3. The router drops an expired row, so
        expiry DOES move every record that row used to win; R3 forbids a MAINTAINER from
        moving traffic and not a row from dying with its task."""
        expired = [dict(self.old[0], expired=True, expired_at=DAY)]
        verdict, moved = replay_mod.replay(self.old, expired, [self.rec])
        self.assertEqual(verdict, "REJECT")
        self.assertEqual(moved[0][3], None)

    def test_an_empty_corpus_admits_every_table_and_the_count_says_so(self):
        """AN EMPTY CORPUS ADMITS EVERY TABLE and the consequence is stated, not hidden.

        **IT NO LONGER READS THE LIVE CORPUS.** It used to assert that
        `dev/pod/replay-corpus.jsonl` was empty, which was true on day one and is a
        PROPERTY OF A GROWING FILE rather than of this code. MEASURED 2026-08-19: the
        first `live` record landed, `c-17` from LJ-1.386's `sys-spec-surface` close, and
        this test failed for the one reason that should never fail a test, which is that
        the program worked. R3 arming is the goal, so the assertion moves to a fixture.
        """
        self.assertEqual(replay_mod.replay(self.old, [], [])[0], "ADMIT")
        with tempfile.TemporaryDirectory() as d:
            empty = Path(d) / "c.jsonl"
            empty.write_text("")
            self.assertEqual(replay_mod.corpus(empty), [])

    def test_a_retired_record_stays_in_the_file_and_is_skipped(self):
        with tempfile.TemporaryDirectory() as d:
            p = Path(d) / "c.jsonl"
            live = record(rid="c-1")
            dead = dict(record(rid="c-2"), retired=True)
            p.write_text(json.dumps(live) + "\n" + json.dumps(dead) + "\n")
            self.assertEqual([r["id"] for r in replay_mod.corpus(p)], ["c-1"])
            self.assertEqual(len(replay_mod.records(p, retired=True)), 2)

    def test_a_record_of_the_wrong_shape_is_refused(self):
        """R7: the program never guesses a fact. A half-record would license a row no
        evidence supports, and the replay would then certify that row as safe."""
        bad = record()
        del bad["facts"]["seconds"]
        with self.assertRaises(table.TableError):
            replay_mod.check_record(bad)
        extra = record()
        extra["facts"]["concurrency"] = 1
        with self.assertRaises(table.TableError):
            replay_mod.check_record(extra)

    def test_a_report_record_must_name_its_source(self):
        with self.assertRaises(table.TableError):
            replay_mod.check_record(dict(record(), provenance="report"))
        replay_mod.check_record(dict(record(), provenance="report",
                                     source="agents/tasks/LJ-1-375/x.md:144"))


class RecordBoundary(unittest.TestCase):
    """`check_record()` is the ONE boundary a record enters through, and the TYPE test
    lives there and nowhere else.

    THE CRASH IT ANSWERS WAS REAL. A corpus line whose `obligations_delta` held a string
    reached `table.matches()` and raised `TypeError` on `>=`. `admit_rows()` catches
    `TableError` and `OSError` and never a `TypeError`, so one malformed line stopped an
    unattended loop with a traceback and nobody watching. Testing the type at each of the
    seventeen comparisons would give one rule seventeen homes, which clause W5 forbids.
    """

    def test_a_string_valued_fact_is_refused_before_any_comparison(self):
        bad = record()
        bad["facts"]["obligations_delta"] = "0"
        with self.assertRaises(table.TableError):
            replay_mod.check_record(bad)
        # THE FIXTURE CAN FAIL: the same record with the integer passes and then routes.
        good = record(delta=0)
        self.assertIs(replay_mod.check_record(good), good)
        self.assertTrue(table.matches({"obligations_delta_min": 0}, good))

    def test_every_fact_carries_a_type_and_a_wrong_one_is_refused(self):
        """`bool` is a subclass of `int` in Python, so `heap_wall = 1` and
        `obligations_delta = true` are both defects the plain `isinstance` test misses."""
        for key, value in (("exit_code", "0"), ("exit_code", 1.5),
                           ("error_class", 7), ("obligations_delta", "0"),
                           ("obligations_delta", True), ("changed_files", "src/L/F.md"),
                           ("seconds", "1.0"), ("seconds", True),
                           ("heap_wall", "false"), ("heap_wall", 1),
                           ("lines", "1000"), ("lines", True)):
            bad = record()
            bad["facts"][key] = value
            with self.assertRaises(table.TableError, msg=f"{key} = {value!r}"):
                replay_mod.check_record(bad)

    def test_a_null_fact_is_admitted_where_the_design_gives_null_a_meaning(self):
        """Refusing null would refuse a record the runner really writes. `exit_code` is
        null when conjunct 1's Agda deadline passed (section 4.3), `error_class` is null
        on a green run, and `lines` is null when the write scope was not counted."""
        for key in ("exit_code", "error_class", "lines"):
            ok = record()
            ok["facts"][key] = None
            self.assertIs(replay_mod.check_record(ok), ok)
        # AND THE THREE THAT MAY NOT BE NULL are refused, so the list above is a rule.
        for key in ("obligations_delta", "changed_files", "seconds", "heap_wall"):
            bad = record()
            bad["facts"][key] = None
            with self.assertRaises(table.TableError, msg=key):
                replay_mod.check_record(bad)

    def test_a_changed_file_that_is_not_a_path_is_refused(self):
        bad = record()
        bad["facts"]["changed_files"] = ["src/L/Foo.lagda.md", 7]
        with self.assertRaises(table.TableError):
            replay_mod.check_record(bad)

    def test_the_top_level_keys_the_router_reads_are_typed_too(self):
        """`hits()` reads `rec["task"]` and `matches()` reads `rec["concurrency"]`, so a
        wrong type there routes as badly as a wrong fact."""
        for key, value in (("id", 7), ("task", None), ("task", ""),
                           ("concurrency", "1"), ("concurrency", True)):
            bad = record()
            bad[key] = value
            with self.assertRaises(table.TableError, msg=f"{key} = {value!r}"):
                replay_mod.check_record(bad)
        absent = record()
        del absent["concurrency"]
        self.assertIs(replay_mod.check_record(absent), absent)

    def test_a_corpus_file_with_one_bad_line_refuses_and_names_the_line(self):
        with tempfile.TemporaryDirectory() as d:
            p = Path(d) / "c.jsonl"
            bad = record(rid="c-2")
            bad["facts"]["seconds"] = "1.0"
            p.write_text(json.dumps(record(rid="c-1")) + "\n" + json.dumps(bad) + "\n")
            with self.assertRaises(table.TableError) as caught:
                replay_mod.corpus(p)
            self.assertIn(":2", str(caught.exception))
            self.assertIn("facts.seconds", str(caught.exception))


# ---------------------------------------------------------------- the admission


class Admission(TreeCase):
    """Section 4.1. `admit_rows()` is the ONLY writer of a task row."""

    def setUp(self):
        super().setUp()
        self.brief_path = self.brief()
        self.table_path = self.tmp / "dev" / "pod" / "table.toml"
        self.table_path.write_text(table.dump_table([]), encoding="utf-8")
        self.corpus_path = self.tmp / "dev" / "pod" / "replay-corpus.jsonl"
        self.corpus_path.write_text("", encoding="utf-8")
        self.commits = []
        self._old = (table.TABLE, table.git_commit, table.head_slots, replay_mod.CORPUS)
        table.TABLE = self.table_path
        replay_mod.CORPUS = self.corpus_path
        table.git_commit = lambda paths, msg, root=None: self.commits.append(msg) or True
        table.head_slots = lambda root=None: SLOTS
        self.addCleanup(self.restore)

    def restore(self):
        (table.TABLE, table.git_commit, table.head_slots, replay_mod.CORPUS) = self._old

    def rows(self):
        return table.load_table(self.table_path, SLOTS)

    def test_a_branch_id_is_namespaced_at_admission_and_nowhere_else(self):
        self.assertTrue(table.admit_rows("LJ-1.386", self.brief_path))
        ids = [r["id"] for r in self.rows()]
        self.assertIn("task-lj-1-386-go", ids)
        self.assertIn("task-lj-1-386-no-go-attacked", ids)
        self.assertTrue(all(r["scope"] == "task:LJ-1.386" for r in self.rows()))
        self.assertTrue(all(r["added_by"] == "mathematician" for r in self.rows()))

    def test_two_briefs_both_naming_go_do_not_collide(self):
        """Cutover step 15b. A branch id is a bare word inside one brief."""
        self.assertTrue(table.admit_rows("LJ-1.386", self.brief_path))
        other = self.tmp / "agents" / "tasks" / "LJ-1-388"
        other.mkdir(parents=True)
        second = other / "LJ-1.388.md"
        second.write_text(BRIEF_386.replace("LJ-1.386", "LJ-1.388")
                          .replace("LJ-1-386", "LJ-1-388"), encoding="utf-8")
        self.assertTrue(table.admit_rows("LJ-1.388", second))
        ids = [r["id"] for r in self.rows()]
        self.assertIn("task-lj-1-386-go", ids)
        self.assertIn("task-lj-1-388-go", ids)

    def test_a_second_admission_of_one_brief_writes_nothing(self):
        self.assertTrue(table.admit_rows("LJ-1.386", self.brief_path))
        before = self.table_path.read_text(encoding="utf-8")
        self.assertEqual(len(self.commits), 1)
        self.assertTrue(table.admit_rows("LJ-1.386", self.brief_path))
        self.assertEqual(self.table_path.read_text(encoding="utf-8"), before)
        self.assertEqual(len(self.commits), 1)

    def test_a_row_that_moves_a_frozen_record_is_rejected_and_nothing_is_written(self):
        """Cutover step 15b's third case, and section 4.1 property 3: on a REJECT no row
        enters the table and rule (f) parks with `reason: "admission"`."""
        seed = table.check_row(row("sys-heap-wall", action="park_and_split",
                                   when={"heap_wall": True}), SLOTS)
        self.table_path.write_text(table.dump_table([seed]), encoding="utf-8")
        rec = record(task="LJ-1.386", heap_wall=True)
        self.corpus_path.write_text(json.dumps(rec) + "\n", encoding="utf-8")
        before = self.table_path.read_text(encoding="utf-8")
        self.assertFalse(table.admit_rows("LJ-1.386", self.brief_path))
        self.assertEqual(self.table_path.read_text(encoding="utf-8"), before)
        self.assertEqual(self.commits, [])

    def test_a_corpus_line_with_a_string_valued_fact_refuses_and_never_raises(self):
        """THE MEASURED CRASH, END TO END. `admit_rows()` catches `TableError` and
        `OSError` and never a `TypeError`, so the raise inside `matches()` escaped into
        the unattended loop. The boundary refuses the line, the admission returns False,
        and rule (f) parks with `reason: "admission"` instead."""
        bad = record(task="LJ-1.386", heap_wall=True)
        bad["facts"]["obligations_delta"] = "0"
        self.corpus_path.write_text(json.dumps(bad) + "\n", encoding="utf-8")
        before = self.table_path.read_text(encoding="utf-8")
        self.assertFalse(table.admit_rows("LJ-1.386", self.brief_path))
        self.assertEqual(self.table_path.read_text(encoding="utf-8"), before)
        self.assertEqual(self.commits, [])
        # THE FIXTURE CAN FAIL: the same line with the integer admits the same brief.
        good = record(task="LJ-1.386", heap_wall=True)
        self.corpus_path.write_text(json.dumps(good) + "\n", encoding="utf-8")
        self.assertTrue(table.admit_rows("LJ-1.386", self.brief_path))

    def test_a_malformed_branch_block_returns_false_and_never_raises(self):
        bad = self.tmp / "agents" / "tasks" / "LJ-1-386" / "bad.md"
        bad.write_text("# LJ-1.386: x\n\n```toml pod-branches\n[[branch]]\nid = 1\n```\n")
        self.assertFalse(table.admit_rows("LJ-1.386", bad))

    def test_an_unknown_branch_key_is_refused(self):
        block = BRANCHES_386.replace('id = "go"', 'id = "go"\nscope = "system"')
        p = self.tmp / "agents" / "tasks" / "LJ-1-386" / "k.md"
        p.write_text("# LJ-1.386: x\n\n" + block, encoding="utf-8")
        with self.assertRaises(table.TableError):
            table.branches_of(p)

    def test_the_reason_comes_from_the_branch_heading(self):
        table.admit_rows("LJ-1.386", self.brief_path)
        got = {r["id"]: r["reason"] for r in self.rows()}
        self.assertEqual(got["task-lj-1-386-go"],
                         "The obligation is discharged and both names resolve.")
        self.assertTrue(got["task-lj-1-386-heap-wall-escalate"].startswith("branch "))

    def test_expiry_marks_the_rows_and_deletes_none(self):
        """Clause W4 applied to a table row: an expired row is never deleted, because it
        records why one task routed differently."""
        table.admit_rows("LJ-1.386", self.brief_path)
        n = table.expire_rows("LJ-1.386", at=DAY)
        self.assertEqual(n, 5)
        rows = self.rows()
        self.assertEqual(len(rows), 5)
        self.assertTrue(all(r["expired"] and r["expired_at"] == DAY for r in rows))
        self.assertEqual(table.expire_rows("LJ-1.386", at=DAY), 0)
        rec = record(task="LJ-1.386", exit_code=0, delta=-2)
        self.assertEqual(table.route(rows, rec), (None, None))

    def test_a_changed_brief_replaces_that_codes_rows(self):
        table.admit_rows("LJ-1.386", self.brief_path)
        text = self.brief_path.read_text(encoding="utf-8").replace(
            'id = "ran-long-and-changed-little"', 'id = "ran-long"')
        self.brief_path.write_text(text, encoding="utf-8")
        self.assertTrue(table.admit_rows("LJ-1.386", self.brief_path))
        ids = [r["id"] for r in self.rows()]
        self.assertIn("task-lj-1-386-ran-long", ids)
        self.assertNotIn("task-lj-1-386-ran-long-and-changed-little", ids)
        self.assertEqual(len(ids), 5)

    def test_the_admitted_rows_route_the_worked_example(self):
        """Section 6.4, and both `done` branches are reachable."""
        table.admit_rows("LJ-1.386", self.brief_path)
        rows = self.rows()
        go = record(task="LJ-1.386", exit_code=0, delta=-2)
        self.assertEqual(table.route(rows, go), ("task-lj-1-386-go", "done"))
        first = record(task="LJ-1.386", exit_code=42, error_class="unsolved_meta",
                       changed=["agents/tasks/LJ-1-386/Probe386.agda"])
        self.assertEqual(table.route(rows, first),
                         ("task-lj-1-386-no-go-attacked", "escalate"))
        after = record(task="LJ-1.386", exit_code=42, error_class="unsolved_meta",
                       changed=["agents/tasks/LJ-1-386/Probe386.agda",
                                "agents/tasks/LJ-1-386/review-of-a1.md"])
        self.assertEqual(table.route(rows, after),
                         ("task-lj-1-386-no-go-stated", "done"))


# ---------------------------------------------------------------- the command line


class CommandLine(TreeCase):
    """`table.py --route` and its three tracebacks.

    THE LOOP RUNS UNATTENDED, so a crash is not cosmetic: it stops the loop with a stack
    trace and nobody is watching. A missing file ended in `FileNotFoundError`, a file that
    is not JSON ended in `JSONDecodeError`, and a record with a string-valued fact ended
    in `TypeError` inside `matches()`. Each one is now a message on standard error and
    exit 1, which the module contract already defines as a refusal.
    """

    def run_main(self, argv):
        out, err = io.StringIO(), io.StringIO()
        with contextlib.redirect_stdout(out), contextlib.redirect_stderr(err):
            code = table.main(argv)
        return code, out.getvalue(), err.getvalue()

    def write_json(self, name, text):
        p = self.tmp / name
        p.write_text(text, encoding="utf-8")
        return str(p)

    def test_route_refuses_a_missing_file_with_a_message(self):
        code, out, err = self.run_main(["--route", str(self.tmp / "nope.json")])
        self.assertEqual(code, 1)
        self.assertIn("REFUSED", err)
        self.assertIn("is unreadable", err)
        self.assertEqual(out, "")

    def test_route_refuses_a_file_that_is_not_json(self):
        p = self.write_json("x.json", "this is not json\n")
        code, _out, err = self.run_main(["--route", p])
        self.assertEqual(code, 1)
        self.assertIn("does not parse as JSON", err)

    def test_route_refuses_a_record_with_a_string_valued_fact(self):
        bad = record(task="LJ-1.266", heap_wall=True)
        bad["facts"]["seconds"] = "1.0"
        code, _out, err = self.run_main(["--route", self.write_json("b.json",
                                                                   json.dumps(bad))])
        self.assertEqual(code, 1)
        self.assertIn("facts.seconds", err)

    def test_route_prints_the_row_and_the_action_for_a_good_record(self):
        """THE FIXTURE CAN FAIL: the three refusals above are worth nothing unless one
        well-formed record still routes and exits 0."""
        rec = record(task="LJ-1.266", exit_code=251, error_class="heap_wall",
                     heap_wall=True, changed=["agents/tasks/LJ-1-266/r.md"])
        code, out, err = self.run_main(["--route", self.write_json("g.json",
                                                                  json.dumps(rec))])
        self.assertEqual((code, out.strip(), err), (0, "sys-heap-wall park_and_split", ""))

    def test_route_reports_no_match_as_a_refusal_and_not_as_a_crash(self):
        rec = record(task="LJ-1.386", exit_code=0, seconds=2.0, delta=-1)
        code, out, _err = self.run_main(["--route", self.write_json("n.json",
                                                                   json.dumps(rec))])
        self.assertEqual((code, out.strip()), (1, "NO MATCH"))

    def test_check_and_rows_read_the_seeded_table(self):
        self.assertEqual(self.run_main(["--check"])[0], 0)
        code, out, _err = self.run_main(["--rows"])
        self.assertEqual(code, 0)
        self.assertIn("sys-dd24-ratio-bar", out)

    def test_the_script_entry_point_catches_a_refusal_raised_inside_replay(self):
        """ONE MODULE OBJECT, and this is the ONE test here that spawns a process.

        Running `table.py` as a script names it `__main__`. `main()` then imports
        `replay`, which does its own `import table` and builds a SECOND copy of the
        module, whose `TableError` is a different class. `except TableError` in `main()`
        missed every refusal raised inside `replay.py`, so `--route` printed a traceback
        where it had a message. The defect lives only in the `__main__` path, and no
        in-process call can reach it.
        """
        bad = record()
        bad["facts"]["obligations_delta"] = "0"
        p = self.tmp / "bad.json"
        p.write_text(json.dumps(bad), encoding="utf-8")
        done = subprocess.run(
            [sys.executable, str(ROOT / "scripts" / "pod" / "table.py"), "--route",
             str(p)], capture_output=True, text=True)
        self.assertEqual(done.returncode, 1)
        self.assertNotIn("Traceback", done.stderr)
        self.assertIn("REFUSED", done.stderr)
        self.assertIn("facts.obligations_delta", done.stderr)

    def test_a_usage_error_exits_two_and_never_one(self):
        """Exit 2 is the usage error and exit 1 is a refusal. A caller that cannot tell
        them apart retries a broken command line for ever."""
        for argv in ([], ["--help"], ["--nope"], ["--route"]):
            self.assertEqual(self.run_main(argv)[0], 2, argv)


# ---------------------------------------------------------------- the pre-flight


class Preflight(TreeCase):
    """AD21's 22 checks. Each test breaks ONE thing in a brief that otherwise passes."""

    def ids(self, d):
        return [line.split()[0] for line in d]

    def test_the_worked_brief_of_section_6_4_passes_every_check(self):
        self.assertEqual(self.run_preflight(), [])

    def test_p1_refuses_a_missing_brief_and_a_second_branch_block(self):
        self.assertEqual(preflight_mod.preflight(self.tmp / "nope.md", root=self.tmp,
                                                 show=False, closure=True, slots=SLOTS),
                         ["P1 no brief, no branch block, or more than one"])
        d = self.run_preflight(BRIEF_386 + "\n" + BRANCHES_386)
        self.assertIn("P1 no brief, no branch block, or more than one", d)

    def test_p2_refuses_a_block_that_does_not_parse(self):
        d = self.run_preflight(BRIEF_386.replace('id = "go"', 'id = go'))
        self.assertIn("P2 branch block does not parse", d)

    def test_p3_refuses_an_empty_branch_set(self):
        text = re.sub(r"```toml pod-branches\n.*?```",
                      "```toml pod-branches\nbranch = []\n```", BRIEF_386, flags=re.S)
        self.assertIn("P3 branch set is empty", self.run_preflight(text))

    def test_p4_refuses_a_seventh_fact_and_admits_a10s_ratio_keys(self):
        """A SEVENTH FACT IS THE FAILURE P4 EXISTS FOR. Amendment A10 admits fact 7's ONE
        key pair, the quotient, and nothing else joins it: `lines_max` is a name the first
        build invented and no ruled bar needs."""
        d = self.run_preflight(BRIEF_386.replace("  heap_wall = true",
                                                 "  reviewer_said = true"))
        self.assertIn("P4 branch heap-wall-escalate matches on reviewer_said", d)
        e = self.run_preflight(BRIEF_386.replace("  heap_wall = true",
                                                 "  lines_max = 400"))
        self.assertIn("P4 branch heap-wall-escalate matches on lines_max", e)
        ok = self.run_preflight(BRIEF_386.replace("  heap_wall = true",
                                                  "  seconds_per_line_max = 0.02"))
        self.assertNotIn("P4", self.ids(ok))
        also = self.run_preflight(BRIEF_386.replace("  seconds_min = 3600.0",
                                                    "  seconds_per_line_min = 0.5"))
        self.assertNotIn("P4", self.ids(also))

    def test_p5_refuses_a_class_outside_the_eleven(self):
        d = self.run_preflight(BRIEF_386.replace('error_class = "unsolved_meta"',
                                                 'error_class = "meta_unsolved"'))
        self.assertIn("P5 branch no-go-stated names class meta_unsolved", d)

    def test_p6_refuses_an_action_outside_the_eight(self):
        d = self.run_preflight(BRIEF_386.replace('action = "park"', 'action = "retry"'))
        self.assertIn("P6 branch ran-long-and-changed-little names action retry", d)

    def test_p7_refuses_a_duplicate_id_and_a_shared_priority(self):
        d = self.run_preflight(BRIEF_386.replace('id = "heap-wall-escalate"',
                                                 'id = "go"'))
        self.assertIn("P7 branch go is a duplicate", d)
        e = self.run_preflight(BRIEF_386.replace("priority = 30", "priority = 10"))
        self.assertIn("P7 branch heap-wall-escalate is a duplicate", e)

    def test_p8_refuses_a_path_whose_parent_is_absent(self):
        """P8 ACCEPTS A FILE THAT DOES NOT YET EXIST, because the probe is what the task
        writes. It refuses a path whose directory does not exist."""
        d = self.run_preflight(BRIEF_386.replace(
            'changed_files_any = ["agents/tasks/LJ-1-386/Probe386.agda"]',
            'changed_files_any = ["agents/tasks/LJ-1-999/Probe999.agda"]'))
        self.assertIn("P8 branch no-go-attacked names agents/tasks/LJ-1-999/Probe999.agda",
                      d)
        e = self.run_preflight(BRIEF_386.replace(
            "- agents/tasks/LJ-1-386/Probe386.agda",
            "- agents/tasks/LJ-1-777/Probe777.agda"))
        self.assertIn("P8 branch scope names agents/tasks/LJ-1-777/Probe777.agda", e)

    def test_p8_refuses_a_path_that_escapes_the_root(self):
        d = self.run_preflight(BRIEF_386.replace(
            "- agents/tasks/LJ-1-386/Probe386.agda",
            "- agents/../../elsewhere/Probe.agda"))
        self.assertIn("P8", self.ids(d))

    def test_p9_refuses_a_brief_no_branch_can_finish(self):
        text = BRIEF_386.replace('action = "done"', 'action = "accept"')
        text = text.replace('outcome = "go"\n', "").replace('outcome = "no-go"\n', "")
        self.assertIn("P9 no branch can finish this task", self.run_preflight(text))

    def test_p10_refuses_two_identical_when_blocks(self):
        text = BRIEF_386.replace("  seconds_min = 3600.0\n  changed_files_count_max = 1",
                                 "  heap_wall = true")
        d = self.run_preflight(text)
        self.assertIn("P10 branches heap-wall-escalate and ran-long-and-changed-little "
                      "are identical", d)

    def test_p11_refuses_a_slot_that_is_not_in_heads_toml(self):
        d = self.run_preflight(BRIEF_386.replace("head_slot: mathematician",
                                                 "head_slot: reviewer"))
        self.assertIn("P11 head slot reviewer is not in heads.toml", d)
        e = self.run_preflight(BRIEF_386.replace(
            'head_slot = "mathematician_adversarial"\n\n  [branch.when]\n  heap_wall',
            '\n  [branch.when]\n  heap_wall'))
        self.assertIn("P11 head slot <none> is not in heads.toml", e)

    def test_p11_refuses_a_head_slot_on_a_branch_that_does_not_escalate(self):
        """THE SECOND DIRECTION, and section 4.2 rules both: `head_slot` is required
        exactly when the action is `escalate` and ABSENT otherwise. The pre-flight tested
        one, so a brief carrying a LEGAL slot on a `park` branch passed here, reached
        `admit_rows()`, was refused there, and parked with `reason: "admission"` instead
        of `reason: "preflight:P11"`."""
        text = BRIEF_386.replace(
            'id = "ran-long-and-changed-little"\npriority = 50\naction = "park"',
            'id = "ran-long-and-changed-little"\npriority = 50\naction = "park"\n'
            'head_slot = "coder"')
        self.assertEqual(text.count('head_slot = "coder"'), 1)   # the fixture can fail
        d = self.run_preflight(text)
        self.assertIn("P11 head slot coder is not admitted on a park branch", d)
        # THE ROW LOADER ALREADY AGREED, and this check now mirrors it.
        with self.assertRaises(table.TableError):
            table.check_row(row("r", action="park", head_slot="coder"), SLOTS)

    def test_p11_refuses_rather_than_raises_when_heads_toml_cannot_be_read(self):
        """`preflight()` must RETURN a list, because rule (f) reads `d[0].split()[0]`.
        `head_slots()` raised `TableError` straight through it, which is a traceback in
        the unattended loop and not a park."""
        brief = self.brief()
        self.assertEqual(preflight_mod.preflight(brief, root=self.tmp, show=False,
                                                 closure=True), [])
        (self.tmp / "dev" / "pod" / "heads.toml").unlink()
        d = preflight_mod.preflight(brief, root=self.tmp, show=False, closure=True)
        self.assertEqual(d, ["P11 head slot <none> is not in heads.toml"])

    def test_p12_refuses_a_code_the_directory_does_not_carry(self):
        d = self.run_preflight(BRIEF_386.replace("# LJ-1.386:", "# LJ-1.387:"))
        self.assertIn("P12 brief code and directory disagree", d)

    def test_p13_refuses_a_missing_machine_class(self):
        d = self.run_preflight(BRIEF_386.replace("machine: shared", "machine: quiet"))
        self.assertIn("P13 machine class is missing", d)
        e = self.run_preflight(BRIEF_386.replace("machine: shared\n", ""))
        self.assertIn("P13 machine class is missing", e)

    def test_p14_refuses_an_obligation_with_no_double_colon(self):
        d = self.run_preflight(BRIEF_386.replace(
            "Probe386.agda::code-inj", "Probe386.agda:code-inj"))
        self.assertIn("P14 obligation 2 is empty or malformed", d)
        e = self.run_preflight(re.sub(r"obligations = \[[^\]]*\]",
                                      "obligations = []", BRIEF_386))
        self.assertIn("P14 obligation 1 is empty or malformed", e)

    def test_p14_refuses_an_obligation_that_is_not_a_string_and_never_raises(self):
        """The field is author-written TOML, so it holds whatever TOML holds. A non-string
        entry reached `parse_obligation()` and raised `AttributeError` on `.count`, which
        is a traceback in the unattended loop and not a refusal."""
        d = self.run_preflight(re.sub(r"obligations = \[[^\]]*\]", "obligations = [7]",
                                      BRIEF_386))
        self.assertIn("P14 obligation 1 is empty or malformed", d)
        e = self.run_preflight(re.sub(r"obligations = \[[^\]]*\]",
                                      'obligations = "a::b"', BRIEF_386))
        self.assertIn("P14 obligation 1 is empty or malformed", e)

    def test_p14_refuses_a_probe_path_outside_the_root(self):
        d = self.run_preflight(BRIEF_386.replace(
            "agents/tasks/LJ-1-386/Probe386.agda::code-exists",
            "/etc/Probe386.agda::code-exists"))
        self.assertIn("P14 obligation 1 is empty or malformed", d)

    def test_p15_refuses_a_missing_block_and_a_dead_path(self):
        d = self.run_preflight(BRIEF_386.replace(
            "- archive/dev/TASKS-archived.md:80    (1 key hit)",
            "- archive/dev/GONE-archived.md:80    (1 key hit)"))
        self.assertIn("P15 injected block missing or dead path", d)
        e = self.run_preflight(re.sub(
            r"## LITERATURE \(program-generated, do not edit\)\n.*?\n\n", "",
            BRIEF_386, flags=re.S))
        self.assertIn("P15 injected block missing or dead path", e)

    def test_p16_reports_a_tree_that_was_already_open(self):
        b = self.brief()
        d = preflight_mod.preflight(b, root=self.tmp, show=False, closure=False,
                                    slots=SLOTS)
        self.assertEqual(d, ["P16 the tree was already open before this task"])

    def test_p17_refuses_a_premise_with_no_live_basis(self):
        d = self.run_preflight(BRIEF_386.replace(
            "Basis: src/L/Cardinal.lagda.md:194-195",
            "Basis: src/L/Cardinal.lagda.md:9994-9995"))
        self.assertIn("P17 premise 1 has no live basis", d)
        e = self.run_preflight(BRIEF_386.replace(
            "- `small-inj` gives the injection. Basis: "
            "src/L/Coding/Injection.lagda.md:147-151",
            "- `small-inj` gives the injection."))
        self.assertIn("P17 premise 2 has no live basis", e)

    def test_p18_refuses_a_brief_nothing_can_attack(self):
        """DD25's mechanised half. `dev/ORCHESTRATION.md:108-112` records `[LJ-0.4]`
        refusing four blocks on measurement, the orchestrator accepting all four, and
        `[LJ-0.8]` then finding a propagated sign error standing in five places."""
        text = BRIEF_386.replace('head_slot = "mathematician_adversarial"',
                                 'head_slot = "coder_adversarial"')
        d = self.run_preflight(text)
        self.assertIn("P18 nothing can attack this return", d)

    def test_p19_refuses_a_done_branch_that_can_close_on_no_work(self):
        d = self.run_preflight(BRIEF_386.replace("obligations_delta_max = -2",
                                                 "obligations_delta_max = 0"))
        self.assertIn("P19 branch go can close on no work", d)

    def test_p19_admits_a_no_go_close_with_no_delta_key_under_a6(self):
        """A NO-GO leaves every declared name unresolved, so its delta is 0 and the first
        limb can never hold. Without A6 no brief could express a refusal.

        THE PREMISE IS READ AND NOT ASSUMED. `P19 not in []` says nothing on its own: it
        holds for any passing brief. So the branch is opened first, and the test proves
        that only A6's second limb can be what admitted it.
        """
        block = tomllib.loads(table.branch_block(self.brief()))
        nogo = next(b for b in block["branch"] if b["id"] == "no-go-stated")
        self.assertNotIn("obligations_delta_max", nogo["when"])
        self.assertEqual(nogo["outcome"], "no-go")
        self.assertEqual(self.run_preflight(), [])
        e = self.run_preflight(BRIEF_386.replace('outcome = "no-go"\n', ""))
        self.assertIn("P19 branch no-go-stated can close on no work", e)

    def test_p20_refuses_an_escalate_branch_that_shadows_a_done_branch(self):
        """P20 exists because P18 can kill the branch it protects. Section 6.4 keeps the
        two blocks disjoint with `review-of-*.md`; remove that key and P20 fires."""
        d = self.run_preflight(BRIEF_386.replace(
            '  changed_files_none = ["agents/tasks/LJ-1-386/review-of-*.md"]\n', ""))
        self.assertIn("P20 branch no-go-attacked shadows done branch no-go-stated", d)

    def test_p20_reads_the_order_of_section_4_4_and_not_the_priority_alone(self):
        """A branch that LOSES to the `done` branch shadows nothing, whatever it matches."""
        text = BRIEF_386.replace(
            '  changed_files_none = ["agents/tasks/LJ-1-386/review-of-*.md"]\n', "")
        text = text.replace('id = "no-go-attacked"\npriority = 15',
                            'id = "no-go-attacked"\npriority = 25')
        self.assertNotIn("P20", self.ids(self.run_preflight(text)))

    def test_p20_survives_a_branch_whose_priority_is_not_an_integer(self):
        """P7 refuses the priority. P20's sort ran first and raised `TypeError` comparing
        a string with an integer, so P7's refusal never reached rule (f)."""
        # A RAISE MAKES THIS TEST AN ERROR, so no assertion states `never raises`. What is
        # asserted is that the refusal P7 owes actually arrives, which the raise prevented.
        d = self.run_preflight(BRIEF_386.replace("priority = 50", 'priority = "50"'))
        self.assertIn("P7 branch ran-long-and-changed-little is a duplicate", d)

    def test_p21_refuses_an_absent_or_empty_laws_bundle(self):
        """R17: the measured lesson book reaches a worker through this block and nothing
        else in the new flow delivers one line of it."""
        d = self.run_preflight(re.sub(
            r"## LAWS \(program-generated, do not edit\)\n.*?\n\n", "", BRIEF_386,
            flags=re.S))
        self.assertIn("P21 the LAWS bundle is absent or empty", d)
        e = self.run_preflight(BRIEF_386.replace(
            "- D-1: write the probe in the task directory and run it while the task "
            "is live.", ""))
        self.assertIn("P21 the LAWS bundle is absent or empty", e)

    def test_p22_prints_a_readme_and_never_refuses(self):
        """P22 IS PROVED BY ITS PRINTER, because it has no refusal string. The old form
        asserted only that the pre-flight passed, which holds whether or not P22 printed
        one character, so the printed line is what this reads."""
        brief = self.brief()
        readme = self.tmp / "agents" / "tasks" / "LJ-1-386" / "README.md"
        readme.write_text("the task directory\n")
        self.assertEqual(preflight_mod.p22_readmes(BRIEF_386, self.tmp),
                         ["agents/tasks/LJ-1-386/README.md"])
        out = io.StringIO()
        with contextlib.redirect_stdout(out):
            d = preflight_mod.preflight(brief, root=self.tmp, show=True, closure=True,
                                        slots=SLOTS)
        self.assertEqual(d, [])
        self.assertEqual(out.getvalue(), "P22 read agents/tasks/LJ-1-386/README.md\n")
        quiet = io.StringIO()
        with contextlib.redirect_stdout(quiet):
            preflight_mod.preflight(brief, root=self.tmp, show=False, closure=True,
                                    slots=SLOTS)
        self.assertEqual(quiet.getvalue(), "")

    def test_the_first_refusal_names_the_check_rule_f_parks_with(self):
        """Rule (f) reads `d[0].split()[0]` and writes `reason: "preflight:P4"`."""
        d = self.run_preflight(BRIEF_386.replace("  heap_wall = true",
                                                 "  reviewer_said = true"))
        self.assertEqual(d[0].split()[0], "P4")

    def test_every_check_id_the_preflight_can_emit_is_one_of_the_twenty_two(self):
        """A CHECK WITH NO TEST IS A CHECK NOBODY PROVED, and the old form of this test
        could not fail: it asked whether the substring `P1` sits in a file that also
        writes `P11`, and the docstring above it supplied `P22` by itself.

        Both halves below discriminate. The first reads the ids `preflight.py` can
        actually PRINT, so a dropped check fails it and an invented id fails it. The
        second reads the ids THIS file names at a word boundary, so `P11` no longer
        answers for `P1`.
        """
        want = {f"P{n}" for n in range(1, 23)}
        emitted = set(re.findall(
            r'"(P\d+) ', (ROOT / "scripts" / "pod" / "preflight.py").read_text(
                encoding="utf-8")))
        self.assertEqual(emitted, want)          # the ids compare as TEXT, so `P08` fails
        named = set(re.findall(r"\bP\d+\b", Path(__file__).read_text(encoding="utf-8")))
        self.assertEqual(want - named, set())


class Contradiction(unittest.TestCase):
    """P20's fixed contradiction table. It needs no solver and its limit is disclosed."""

    def test_two_exit_codes_that_differ_contradict(self):
        self.assertTrue(preflight_mod.contradicts({"exit_code": 0}, {"exit_code": 42}))
        self.assertFalse(preflight_mod.contradicts({"exit_code": 42}, {"exit_code": 42}))

    def test_two_disjoint_in_lists_contradict(self):
        self.assertTrue(preflight_mod.contradicts(
            {"error_class_in": ["termination"]}, {"error_class_in": ["unsolved_meta"]}))
        self.assertFalse(preflight_mod.contradicts(
            {"error_class_in": ["termination", "other"]},
            {"error_class_in": ["other"]}))

    def test_two_delta_ranges_that_do_not_overlap_contradict(self):
        self.assertTrue(preflight_mod.contradicts({"obligations_delta_min": 0},
                                                  {"obligations_delta_max": -1}))
        self.assertFalse(preflight_mod.contradicts({"obligations_delta_min": -3},
                                                   {"obligations_delta_max": -1}))

    def test_one_glob_in_any_and_in_none_contradicts(self):
        self.assertTrue(preflight_mod.contradicts(
            {"changed_files_none": ["agents/tasks/LJ-1-386/review-of-*.md"]},
            {"changed_files_any": ["agents/tasks/LJ-1-386/review-of-*.md"]}))

    def test_a_separation_written_two_ways_is_not_recognised(self):
        """THE LIMIT IS DISCLOSED, and P20 then REFUSES the brief, which is the safe
        direction."""
        self.assertFalse(preflight_mod.contradicts(
            {"changed_files_none": ["agents/tasks/LJ-1-386/review-of-a.md"]},
            {"changed_files_any": ["agents/tasks/LJ-1-386/review-of-*.md"]}))

    def test_a_value_of_the_wrong_type_reads_as_no_contradiction_and_never_raises(self):
        """`set(5)` and `"0" > -1` both raise `TypeError`, and this function runs BEFORE
        admission, where `table.check_row()` refuses the type. No contradiction is the
        safe direction, because P20 then refuses the brief."""
        for a, b in (({"error_class_in": "termination"},
                      {"error_class_in": ["unsolved_meta"]}),
                     ({"exit_code_in": [{}]}, {"exit_code_in": [0]}),
                     ({"obligations_delta_min": "0"}, {"obligations_delta_max": -1}),
                     ({"obligations_delta_min": True}, {"obligations_delta_max": -1}),
                     ({"changed_files_any": "src/*"}, {"changed_files_none": ["src/*"]})):
            self.assertFalse(preflight_mod.contradicts(a, b), (a, b))
            self.assertFalse(preflight_mod.contradicts(b, a), (b, a))
        # THE FIXTURE CAN FAIL: the same pairs, correctly typed, DO contradict.
        self.assertTrue(preflight_mod.contradicts(
            {"error_class_in": ["termination"]}, {"error_class_in": ["unsolved_meta"]}))
        self.assertTrue(preflight_mod.contradicts(
            {"obligations_delta_min": 0}, {"obligations_delta_max": -1}))
        self.assertTrue(preflight_mod.contradicts(
            {"changed_files_any": ["src/*"]}, {"changed_files_none": ["src/*"]}))


class StopLoopIsOwnerOnly(unittest.TestCase):
    """`stop_loop` halts the whole programme, so no model may add such a row.
    Ruled 2026-08-19.

    **THE GUARD THAT WAS SUPPOSED TO COVER THIS IS INERT.** `dev/pod/replay-corpus.jsonl`
    is 0 bytes and `replay.py --count` prints「EMPTY. replay() returns ADMIT for every
    table and R3 guards nothing until the first record lands.」Seeding the corpus would
    not have closed it either: R3 rejects a table that MOVES a frozen record, and a
    `stop_loop` row keyed on a class no record carries moves nothing.
    """

    def _row(self, added_by, action="stop_loop", **extra):
        row = {"id": "x-1", "scope": "system", "priority": 1, "action": action,
               "added": datetime.date(2026, 8, 19), "added_by": added_by, "reason": "r",
               "when": {"error_class": "spec_surface"}}
        row.update(extra)
        return row

    def test_the_owner_may_add_one(self):
        table.check_row(self._row("owner"))          # must not raise

    def test_no_model_may_add_one(self):
        for who in ("mathematician", "maintainer"):
            with self.subTest(who=who), self.assertRaises(table.TableError) as e:
                table.check_row(self._row(who))
            self.assertIn("stop-request.toml", str(e.exception),
                          "the refusal must name the channel a model SHOULD use")

    def test_a_model_may_still_add_every_other_action(self):
        """The refusal is one action wide. A model that could no longer write a `park`
        row would be a maintainer that cannot do its job."""
        for act, extra in (("done", {"outcome": "go"}), ("accept", {}),
                           ("park", {}), ("redispatch", {})):
            with self.subTest(action=act):
                table.check_row(self._row("maintainer", action=act, **extra))

    def test_every_live_row_that_stops_the_loop_is_the_owners(self):
        """This is the assertion that would have caught a model-added halt already in
        the tree, rather than only the next one."""
        for r in table.load_table():
            if r["action"] == "stop_loop":
                self.assertEqual(r["added_by"], "owner", f"row {r['id']}")


if __name__ == "__main__":
    unittest.main(verbosity=2)
