#!/usr/bin/env python3
"""Regression tests for the POD recorder, the fact 3 witness meter and fact 7.

WHY THIS FILE EXISTS. Every rule below was bought with a measurement, and each one, read
back wrongly, produces a green record that says the opposite of what happened:

1. **The class map.** Over the log corpus of 1,017 files, a location-anchored error form
   matched 3,097 tags of 3,395 and lost 30 of 30 `UnsolvedConstraints`, the class a NO-GO
   routes on. The form under test matches a tag with a location and a tag without one.
2. **The FIRST name in output order.** Agda prints many tags per failure. A map that took
   the last one would classify a run by its final message.
3. **The heap wall needs two signals.** `Heap exhausted` appears on 472 corpus lines and
   only 37 match `^agda: Heap exhausted;`.
4. **The witness meter's four values.** `[NotInScope]` fires INSIDE a red probe too,
   measured at `agents/tasks/LJ-1-286/ProbeLJ1286A.agda:30`. A meter that greps the tag
   anywhere reports a red probe as a discharged obligation, which closes a `go` branch on
   no work. The rule anchors on the FILE in the error's location line.
5. **The exit codes.** Agda returns 0, 42 and 251, and 1 is free, which is why amendment
   A5 gives 1 to the acceptance runner's five other conjuncts.
6. **The process count includes THIS run.** MEASURED 2026-08-17: `slots()` returned the
   launcher's holder count alone, which is 0 for a solo acceptance run, while `matches()`
   admits a seconds key only when `concurrency == 1`. Fact 5 was unmatchable and every
   branch keyed on seconds was dead. `ProcessCount` below fails on that old body.
7. **A crash is not a cosmetic defect.** The POD runs unattended. A probe deleted or
   renamed inside the task's own scope, a probe path that names a directory and a
   `--deadline abc` each raised a traceback out of the tick, where nobody was watching.
   `Refusals` below holds one test per crash.
8. **Fact 7 has ONE caliber**, the ledger's: non-blank lines inside ` ```agda ` fences.
   `Fact7` asserts the count agrees with `scripts/measure/ledger.py` file by file, so the
   two cannot drift into two calibers under one name.

NO TEST HERE STARTS AGDA. The suite must stay inside `make test`, so every Agda result is
a recorded shape and the live proof is the report's own witness runs. The one test that
exercises `run_agda()` replaces `subprocess.run` with a stub and asserts the argv, the
`GHCRTS` value and the refusal.

Run: `python3 scripts/tests/test_pod_facts.py`
"""

from __future__ import annotations

import importlib.util
import os
import subprocess
import sys
import tempfile
import tomllib
import types
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent.parent


def _load(name: str, rel: str):
    spec = importlib.util.spec_from_file_location(name, ROOT / rel)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


facts = _load("pod_facts", "scripts/pod/facts.py")
witness = _load("pod_witness", "scripts/pod/witness.py")
closure = _load("pod_check_closure", "scripts/pod/check-closure.py")
accept = _load("pod_accept", "scripts/pod/accept.py")
table = _load("pod_table", "scripts/pod/table.py")


def agda_out(*tags, located=True, path="src/L/Foo.lagda.md"):
    """One Agda-shaped error block per tag, with or without a location line."""
    out = []
    for n, tag in enumerate(tags, 1):
        head = f"{path}:{n * 10},3-9 " if located else ""
        out.append(f"{head}error: [{tag}]\nsome message text\n")
    return "\n".join(out)


class Patching(unittest.TestCase):
    """One undo path for every attribute a test replaces."""

    def patch(self, obj, name, value):
        old = getattr(obj, name)
        setattr(obj, name, value)
        self.addCleanup(setattr, obj, name, old)

    def tmp(self) -> Path:
        d = Path(tempfile.mkdtemp())
        return d


class ClassMap(unittest.TestCase):
    """Fact 2. The six Agda classes, the five runner classes and the three parser rules."""

    def test_every_mapped_name_reaches_its_class(self):
        want = {"TerminationIssue": "termination",
                "UnequalSorts": "universe_level",
                "UnequalLevel": "universe_level",
                "UnsolvedMetaVariables": "unsolved_meta",
                "UnsolvedInteractionMetas": "unsolved_meta",
                "UnsolvedConstraints": "unsolved_meta",
                "MetaCannotDependOn": "unsolved_meta"}
        self.assertEqual(facts.CLASS, want, "the class map is section 4.3.1's, exactly")
        for name, cls in want.items():
            self.assertEqual(facts.classify(42, [name], False, False), cls, name)

    def test_an_unmapped_name_is_other(self):
        for name in ("UnequalTerms", "NotInScope", "FileNotFound", "CoInfectiveImport"):
            self.assertEqual(facts.classify(42, [name], False, False), "other", name)

    def test_the_class_is_the_first_name_in_output_order(self):
        names = [m.group("cls") for m in
                 facts.ERR.finditer(agda_out("UnequalSorts", "UnsolvedConstraints"))]
        self.assertEqual(names, ["UnequalSorts", "UnsolvedConstraints"])
        self.assertEqual(facts.classify(42, names, False, False), "universe_level")

    def test_a_tag_with_no_location_is_still_matched(self):
        """The 298 corpus misses, including 30 of 30 UnsolvedConstraints."""
        out = agda_out("UnsolvedConstraints", located=False)
        names = [m.group("cls") for m in facts.ERR.finditer(out)]
        self.assertEqual(names, ["UnsolvedConstraints"])
        self.assertEqual(facts.classify(42, names, False, False), "unsolved_meta")

    def test_a_green_run_has_no_class(self):
        self.assertIsNone(facts.classify(0, [], False, False))

    def test_non_zero_with_no_name_is_other(self):
        """The shape a missing input file makes: exit 42 and no bracketed name."""
        self.assertEqual(facts.classify(42, [], False, False), "other")

    def test_heap_beats_the_names_and_timeout_beats_the_heap(self):
        self.assertEqual(facts.classify(251, ["UnequalSorts"], True, False), "heap_wall")
        self.assertEqual(facts.classify(None, [], True, True), "timeout")

    def test_the_heap_string_must_start_the_line(self):
        self.assertTrue(facts.HEAP.search("agda: Heap exhausted;\n"))
        self.assertFalse(facts.HEAP.search("  note: Heap exhausted; and this is prose\n"))

    def test_the_eleven_classes_are_closed(self):
        self.assertEqual(len(facts.ERROR_CLASSES), 11)
        self.assertEqual(set(facts.CLASS.values()) | {"heap_wall", "timeout", "other"},
                         set(facts.AGDA_CLASSES))
        self.assertEqual(facts.RUNNER_CLASSES,
                         ("obligations_up", "closure_open", "unbound_hyp",
                          "spec_surface", "lint"))

    def test_safe_is_read_and_never_assumed(self):
        self.assertTrue(facts.SAFE.search("{-# OPTIONS --cubical --safe #-}\n"))
        self.assertFalse(facts.SAFE.search("{-# OPTIONS --cubical --guardedness #-}\n"))

    def test_partial_output_from_a_killed_child_is_text_either_way(self):
        """MEASURED 2026-08-18 on CPython 3.11.15, darwin: a child killed by
        `subprocess.run(..., text=True, timeout=...)` gives `e.stdout` as BYTES and
        `e.stderr` as None. The helper must carry both, plus the unmeasured `str` case."""
        self.assertEqual(facts._as_text(b"half"), "half")
        self.assertEqual(facts._as_text("half"), "half")
        self.assertEqual(facts._as_text(None), "")

    def test_the_measured_shape_of_a_killed_child_is_the_one_the_helper_takes(self):
        """The claim above is re-measured here, so it can never become a quoted number.

        It runs `python -c`, never Agda: the deadline path is the recorder's, not Agda's.
        """
        with self.assertRaises(subprocess.TimeoutExpired) as caught:
            subprocess.run([sys.executable, "-c",
                            "import sys, time; sys.stdout.write('half'); "
                            "sys.stdout.flush(); time.sleep(5)"],
                           capture_output=True, text=True, timeout=1.0)
        e = caught.exception
        self.assertIsInstance(e.stdout, bytes, "the design's `.decode` reads THIS shape")
        self.assertIsNone(e.stderr, "stderr is None, so `_as_text` must take None")
        self.assertEqual(facts._as_text(e.stdout) + facts._as_text(e.stderr), "half")


class Calibers(unittest.TestCase):
    """A14 and A15. One named constant per tier, and no heap literal at a call site."""

    def heads(self):
        path = ROOT / "dev" / "pod" / "heads.toml"
        self.assertTrue(path.is_file(),
                        "dev/pod/heads.toml is the ONE home of the tier numbers")
        return tomllib.loads(path.read_text(encoding="utf-8"))

    def test_each_tier_caliber_equals_its_heads_toml_row(self):
        """The loader owns the numbers; this module is a reader. Drift fails HERE."""
        tiers = self.heads()["tiers"]
        self.assertEqual(facts.CAP_WIDE, tiers["wide"]["heap"])
        self.assertEqual(facts.CAP_HEAVY, tiers["heavy"]["heap"])
        self.assertNotEqual(facts.CAP_WIDE, facts.CAP_HEAVY,
                            "A14 gives the two tiers two calibers")

    def test_the_acceptance_caliber_is_the_workers_and_the_tree_caliber_is_not(self):
        """A15. A per-task run uses -M8g; a whole-tree make check uses -M16g."""
        self.assertEqual(facts.CAP, facts.CAP_WIDE)
        self.assertEqual(accept.DEFAULT_TIER, "wide")
        self.assertIn("-M8g", facts.CAP)
        self.assertIn("-M16g", facts.CAP_TREE)
        self.assertNotIn(facts.CAP_TREE, facts.CALIBER.values().__class__.__name__)
        self.assertNotIn("tree", facts.TASK_TIERS,
                         "the tree caliber belongs to a run that holds the machine alone")

    def test_an_unknown_tier_is_refused_and_never_falls_back(self):
        for bad in ("WIDE", "huge", None, 8):
            with self.assertRaises(ValueError, msg=repr(bad)):
                facts.caliber_of(bad)

    def test_the_tier_picks_the_heap_and_the_record_carries_both(self):
        """No Agda: `subprocess.run` is stubbed, so this reads the argv and the env."""
        seen = {}

        def fake_run(argv, cwd=None, env=None, **kw):
            seen["argv"], seen["env"] = argv, env
            return types.SimpleNamespace(returncode=0, stdout="", stderr="")

        self.patch(facts.subprocess, "run", fake_run)
        r = facts.run_agda("src/Everything.lagda.md", ROOT, 60, 1, tier="heavy")
        self.assertEqual(seen["env"]["GHCRTS"], facts.CAP_HEAVY)
        self.assertEqual(r["caliber"], facts.CAP_HEAVY)
        self.assertEqual(r["tier"], "heavy")
        r = facts.run_agda("src/Everything.lagda.md", ROOT, 60, 1)
        self.assertEqual(seen["env"]["GHCRTS"], facts.CAP_WIDE)
        self.assertEqual(r["tier"], "wide")

    def patch(self, obj, name, value):
        old = getattr(obj, name)
        setattr(obj, name, value)
        self.addCleanup(setattr, obj, name, old)


class ProcessCount(Patching):
    """Fact 5's guard. `slots()` counts the processes live DURING the run, this one too.

    THE OLD BODY RETURNED `len(agda_holders(load()))`. Every assertion here fails on it,
    because a solo acceptance run then reads 0 and `matches()` refuses every seconds key.
    """

    def launcher(self, holders):
        """Stub the Agda-slot census on EVERY `facts` module object, because there are two.

        **THE STUB USED TO ISOLATE ONLY HALF THE TEST.** `_load()` above builds this
        file's `facts` under the module name `pod_facts`, while `accept.py` runs its own
        `import facts` and gets a SECOND object for the same file, with its own
        `_LAUNCHER` list. Patching only the first left every assertion that goes THROUGH
        `accept` reading the live `.pod-state/registry.json` instead of the stub.

        MEASURED 2026-08-19: `test_a_seconds_key_matches_a_solo_record...` passed with no
        pod running and failed `1 != 0` with LJ-1.388 dispatched, because the real
        registry then held one live Agda dispatch. The test was not measuring the stub it
        set up, and it only ever said so on the day the pod actually ran a task.
        """
        mod = types.SimpleNamespace(load=lambda: {},
                                    agda_holders=lambda reg: dict.fromkeys(holders, {}))
        seen = {}
        for m in (facts, getattr(accept, "facts_mod", None)):
            if m is not None and hasattr(m, "_LAUNCHER"):
                seen.setdefault(id(m), m)
        for m in seen.values():
            old = list(m._LAUNCHER)
            m._LAUNCHER[:] = [mod]
            self.addCleanup(
                lambda m=m, old=old: m._LAUNCHER.__setitem__(slice(None), old))

    def test_a_solo_run_reads_one_and_not_zero(self):
        self.launcher([])
        self.assertEqual(facts.slots(), 1,
                         "the acceptance run's OWN Agda process is the first one")

    def test_every_other_holder_is_added_to_this_run(self):
        self.launcher(["LJ-1.401", "LJ-1.402"])
        self.assertEqual(facts.slots(), 3)

    def test_a_measurement_point_that_starts_nothing_passes_own_zero(self):
        self.launcher([])
        self.assertEqual(facts.slots(own=0), 0,
                         "section 4.3.2 case 4 starts no Agda, so it is not a solo run")

    def test_an_unreadable_launcher_refuses_rather_than_guessing(self):
        self.patch(facts, "launcher", lambda: None)
        self.assertIsNone(facts.slots())

    def test_a_seconds_key_matches_a_solo_record_and_only_a_solo_record(self):
        """THE DEFECT, END TO END. `matches()` is fact 5's only consumer."""
        self.launcher([])
        rec = accept.conjunct1([], root=ROOT)             # case 4, no Agda process
        self.assertEqual(rec["concurrency"], 0)
        self.assertFalse(table.matches({"seconds_max": 5.0}, dict(rec, facts={
            "exit_code": 0, "error_class": None, "obligations_delta": 0,
            "changed_files": ["a"], "seconds": 0.0, "heap_wall": False})),
            "a vacuous record measured no seconds, so no seconds key may match it")

        solo = {"concurrency": facts.slots(),
                "facts": {"exit_code": 0, "error_class": None, "obligations_delta": -1,
                          "changed_files": ["src/L/Foo.lagda.md"], "seconds": 3.2,
                          "heap_wall": False, "lines": 100}}
        self.assertTrue(table.matches({"seconds_max": 5.0}, solo),
                        "a solo acceptance run must be matchable on fact 5")
        self.assertTrue(table.matches({"seconds_per_line_max": 0.05}, solo),
                        "DD24's restored ratio needs fact 5 AND fact 7")
        self.launcher(["LJ-1.401"])
        contended = dict(solo, concurrency=facts.slots())
        self.assertFalse(table.matches({"seconds_max": 5.0}, contended),
                         "a contended cold gate measured 150.09 s against 133.69 s")


class Refusals(Patching):
    """Every crash the adversarial review found, one test each. The POD is unattended."""

    def test_an_unreadable_target_is_not_a_crash_and_not_a_guessed_fact(self):
        """`Path(root, target).read_text()` raised out of the ONE place Agda starts."""
        text, why = facts._head_text(ROOT, "agents/tasks/NO-SUCH/Gone.agda")
        self.assertEqual(text, "")
        self.assertIn("FileNotFoundError", why)
        text, why = facts._head_text(ROOT, "agents/tasks")          # a directory
        self.assertEqual(text, "")
        self.assertIn("IsADirectoryError", why)
        text, why = facts._head_text(ROOT, "src/Everything.lagda.md")
        self.assertIn("module Everything", text)
        self.assertIsNone(why)

    def test_a_missing_target_still_starts_agda_and_records_agdas_own_code(self):
        """MEASURED: agda over an absent path exits 42 with no bracketed name, which
        `classify()` calls `other`. The recorder must not invent that code itself."""
        def fake_run(argv, cwd=None, env=None, **kw):
            self.assertNotIn("--safe", argv, "no head, so no --safe sniff")
            return types.SimpleNamespace(returncode=42, stdout="", stderr="not found")

        self.patch(facts.subprocess, "run", fake_run)
        r = facts.run_agda("agents/tasks/NO-SUCH/Gone.agda", ROOT, 60, 1)
        self.assertEqual(r["rc"], 42)
        self.assertEqual(r["agda_class"], "other")
        self.assertIn("FileNotFoundError", r["target_unreadable"])

    def test_an_agda_that_cannot_start_refuses_and_writes_no_fact(self):
        def fake_run(*a, **kw):
            raise FileNotFoundError(2, "No such file or directory: 'agda'")

        self.patch(facts.subprocess, "run", fake_run)
        with self.assertRaises(facts.AgdaStartError):
            facts.run_agda("src/Everything.lagda.md", ROOT, 60, 1)

    def test_a_deleted_probe_in_scope_is_dropped_from_the_target_list(self):
        """git status reports a delete, and a rename as a delete plus an untracked add.
        Without the filter the runner hands Agda a file that is gone and the task goes
        red for legitimate work."""
        live = "agents/tasks/LJ-1-383/Probe383.agda"
        self.assertTrue((ROOT / live).is_file(), "the sampled probe moved")
        ch = [live, "agents/tasks/LJ-1-383/Gone.agda"]
        self.assertEqual(facts.verification_target(ch, "LJ-1.383"), [live])

    def test_a_deleted_master_still_sends_the_run_at_everything(self):
        """A task that deletes a master MUST go red, so Everything is never dropped."""
        tgt = facts.verification_target(["src/L/Deleted.lagda.md"], "LJ-1.383")
        self.assertEqual(tgt, ["src/Everything.lagda.md"])

    def test_a_probe_path_that_is_a_directory_starts_no_process(self):
        """`exists()` passed a directory into `probe_code()`, which raised
        IsADirectoryError into the tick."""
        m = witness.measure(["agents/tasks::name"], code="LJ-1.999", slots=1)
        self.assertEqual(m["rows"][0]["value"], witness.NO_FILE)
        self.assertIn("directory", m["rows"][0]["detail"])
        self.assertEqual(m["witness_seconds"], 0.0)

    def test_an_unreadable_probe_is_a_probe_red_row_and_never_a_traceback(self):
        d = self.tmp()
        (d / "P.agda").write_text("module P where\n", encoding="utf-8")
        (d / "P.agda").chmod(0o000)
        self.addCleanup((d / "P.agda").chmod, 0o600)
        if os.access(d / "P.agda", os.R_OK):
            self.skipTest("this user reads a 000 file; the OSError path cannot fire")
        with self.assertRaises(witness.DerivationError):
            witness.probe_code(d / "P.agda")

    def test_a_non_string_obligation_is_a_row_and_never_an_attribute_error(self):
        m = witness.measure(["p::x", 5, ["a"]], code="LJ-1.999", slots=1)
        self.assertEqual([r["value"] for r in m["rows"]],
                         [witness.NO_FILE, witness.PROBE_RED, witness.PROBE_RED])
        self.assertEqual(m["unresolved"], 3, "an unmeterable name stays UNRESOLVED")

    def test_a_brief_that_cannot_be_read_refuses_and_never_returns_empty(self):
        """An empty list would state that the brief declares no obligation, which is a
        fact nothing measured. P14 catches ValueError, and DerivationError is one."""
        with self.assertRaises(witness.DerivationError):
            witness.obligations_of(ROOT / "agents" / "tasks" / "NO-SUCH" / "brief.md")
        self.assertIsInstance(witness.DerivationError("x"), ValueError)
        d = self.tmp()
        bad = d / "bad.md"
        bad.write_text("## OBLIGATION NAMES\nobligations = [\"a\", oops]\n",
                       encoding="utf-8")
        with self.assertRaises(witness.DerivationError):
            witness.obligations_of(bad)
        wrong = d / "wrong.md"
        wrong.write_text("## OBLIGATION NAMES\nobligations = [42]\n", encoding="utf-8")
        self.assertEqual(witness.obligations_of(wrong), [42],
                         "a list of the wrong element type is P14's refusal, not this "
                         "reader's; the meter rows it as PROBE RED")

    def test_the_witness_command_line_refuses_a_bad_deadline(self):
        def run(*args):
            return subprocess.run([sys.executable, "scripts/pod/witness.py", *args],
                                  cwd=ROOT, capture_output=True, text=True)
        bad = run("--deadline", "abc", "p::x")
        self.assertEqual(bad.returncode, 2)
        self.assertIn("REFUSED", bad.stderr)
        self.assertNotIn("Traceback", bad.stderr)
        self.assertEqual(run("--deadline", "0", "p::x").returncode, 2)
        self.assertEqual(run("--deadline").returncode, 2)
        gone = run("--brief", "no/such/brief.md")
        self.assertEqual(gone.returncode, 2)
        self.assertNotIn("Traceback", gone.stderr)
        self.assertEqual(run("--nonsense").returncode, 2)

    def test_the_acceptance_command_line_refuses_a_bad_count_and_a_bad_tier(self):
        def run(*args):
            return subprocess.run([sys.executable, "scripts/pod/accept.py", *args],
                                  cwd=ROOT, capture_output=True, text=True)
        bad = run("--task", "LJ-1.999", "--obl-before", "abc")
        self.assertEqual(bad.returncode, 2)
        self.assertIn("REFUSED", bad.stderr)
        self.assertNotIn("Traceback", bad.stderr)
        tier = run("--task", "LJ-1.999", "--tier", "huge")
        self.assertEqual(tier.returncode, 2)
        self.assertIn("REFUSED", tier.stderr)
        self.assertEqual(run("--task").returncode, 2, "an option with no value")
        self.assertEqual(run("--conjuncts").returncode, 0)


class ExitCodes(unittest.TestCase):
    """Fact 1. Agda's codes are 0, 42 and 251; 1 is free and A5 takes it for the runner."""

    def test_agdas_own_codes_fold_to_a_class(self):
        self.assertIsNone(facts.classify(0, [], False, False))
        self.assertEqual(facts.classify(42, ["TerminationIssue"], False, False),
                         "termination")
        self.assertEqual(facts.classify(251, [], True, False), "heap_wall")
        self.assertEqual(facts.classify(None, [], False, True), "timeout")

    def test_the_closure_check_exit_codes(self):
        """0 clean, 2 usage. `--check closure` is the acceptance runner's conjunct 3."""
        def run(*args):
            return subprocess.run([sys.executable, "scripts/pod/check-closure.py", *args],
                                  cwd=ROOT, capture_output=True, text=True)
        clean = run("--check", "closure")
        self.assertEqual(clean.returncode, 0, clean.stderr)
        self.assertIn("check-closure: clean", clean.stdout)
        self.assertEqual(run("--check", "no-such-check").returncode, 2)
        self.assertEqual(run("--gate-debt").returncode, 2,
                         "the batched-gate counter is retired with its protocol")

    def test_the_four_checks_and_their_classes_are_pinned(self):
        """accept.py routes conjunct 3 on the exit code, which only FAIL classes set."""
        self.assertEqual(closure.CHECKS["closure"][1], "FAIL")
        self.assertEqual(closure.CHECKS["archive"][1], "FAIL")
        self.assertEqual(closure.CHECKS["closure-new"][1], "WARN")
        self.assertEqual(closure.CHECKS["module-body"][1], "WARN")
        self.assertEqual(set(closure.CHECKS),
                         {"closure", "archive", "closure-new", "module-body"},
                         "check_retiring, shared-cjk and spdx left in the 7.2 split")

    def test_the_witness_cli_exit_codes(self):
        """0 every obligation resolved, 1 one or more UNRESOLVED, 2 usage. No Agda here."""
        def run(*args):
            return subprocess.run([sys.executable, "scripts/pod/witness.py", *args],
                                  cwd=ROOT, capture_output=True, text=True)
        self.assertEqual(run().returncode, 2)
        gone = run("agents/tasks/NO-SUCH-TASK/Probe.agda::name")
        self.assertEqual(gone.returncode, 1, gone.stderr)
        self.assertIn("no-file", gone.stdout)


class ClosureCheck(Patching):
    """Section 7.2. The gate that notices a master `Everything` never imports."""

    def tree(self, wired, tracked):
        """A whole fake `src/`, and the module globals pointed at it."""
        d = self.tmp()
        src = d / "src"
        (src / "L").mkdir(parents=True)
        imports = "".join(f"import {name}\n" for name in wired)
        (src / "Everything.lagda.md").write_text(
            f"# catalog\n\n```agda\nmodule Everything where\n{imports}```\n",
            encoding="utf-8")
        for name in ("L.Wired", "L.Orphan"):
            rel = name.replace(".", "/") + ".lagda.md"
            (src / rel).write_text(f"```agda\nmodule {name} where\n```\n",
                                   encoding="utf-8")
        self.patch(closure, "ROOT", d)
        self.patch(closure, "SRC", src)
        self.patch(closure, "EVERYTHING", src / "Everything.lagda.md")
        self.patch(closure, "ARCHIVE", d / "archive")
        self.patch(closure, "_tracked_or_staged", lambda: set(tracked))
        return d

    def test_an_unwired_tracked_master_is_a_fail_hit_that_names_the_import_to_add(self):
        """The gate's only documented false-green mode: a master nobody imports is never
        typechecked and `make check` still goes green."""
        self.tree(wired=["L.Wired"],
                  tracked={"src/Everything.lagda.md", "src/L/Wired.lagda.md",
                           "src/L/Orphan.lagda.md"})
        hits = closure.check_closure()
        self.assertEqual(len(hits), 1, hits)
        self.assertIn("src/L/Orphan.lagda.md", hits[0])
        self.assertIn("import L.Orphan", hits[0])
        self.assertEqual(closure.check_closure_new(), [],
                         "a TRACKED master is the FAIL check's, never the WARN check's")

    def test_the_same_master_untracked_is_a_warn_and_blocks_nobody(self):
        """A concurrent agent's half-written chapter blocked an unrelated commit twice on
        2026-08-05, and that is why the two checks split."""
        self.tree(wired=["L.Wired"],
                  tracked={"src/Everything.lagda.md", "src/L/Wired.lagda.md"})
        self.assertEqual(closure.check_closure(), [])
        warn = closure.check_closure_new()
        self.assertEqual(len(warn), 1, warn)
        self.assertIn("src/L/Orphan.lagda.md", warn[0])

    def test_an_import_with_no_master_is_a_fail_hit_too(self):
        self.tree(wired=["L.Wired", "L.Vanished"],
                  tracked={"src/Everything.lagda.md", "src/L/Wired.lagda.md",
                           "src/L/Orphan.lagda.md"})
        hits = [h for h in closure.check_closure() if "L.Vanished" in h]
        self.assertEqual(len(hits), 1, "an import naming no master is the other half")

    def test_one_parser_serves_the_gate_and_the_verification_target(self):
        """`imported_modules()` is the ONE reader of the catalog's import list. A second
        regex could send the acceptance run at the wrong file (section 4.3.2 case 1)."""
        self.tree(wired=["L.Wired"], tracked={"src/Everything.lagda.md"})
        self.assertEqual(closure.imported_modules(), {"L.Wired"})


class PassRule(unittest.TestCase):
    """Fact 3. The four values of section 4.7.4, and the anchor that separates two of them."""

    def result(self, rc, out, heap=False, names=()):
        return {"rc": rc, "out": out, "heap_wall": heap, "caliber": facts.CAP,
                "error_names_all": list(names), "seconds": 1.0}

    def test_exit_zero_is_the_only_resolved_value(self):
        v, _ = witness.verdict(self.result(0, ""), ROOT / ".pod-state/witness/W.agda")
        self.assertEqual(v, witness.PASS)

    def test_not_in_scope_inside_the_witness_is_missing(self):
        w = ROOT / ".pod-state" / "witness" / "W.agda"
        out = agda_out("NotInScope", path=str(w))
        v, detail = witness.verdict(self.result(42, out, names=["NotInScope"]), w)
        self.assertEqual(v, witness.MISSING, detail)

    def test_a_relative_location_line_still_names_the_witness(self):
        w = ROOT / ".pod-state" / "witness" / "W.agda"
        out = agda_out("NotInScope", path=".pod-state/witness/W.agda")
        v, _ = witness.verdict(self.result(42, out, names=["NotInScope"]), w, root=ROOT)
        self.assertEqual(v, witness.MISSING)

    def test_not_in_scope_inside_the_probe_is_probe_red(self):
        """MEASURED at agents/tasks/LJ-1-286/ProbeLJ1286A.agda:30. This is the whole point
        of the anchor: the same tag, a different file, the opposite meaning."""
        w = ROOT / ".pod-state" / "witness" / "W.agda"
        out = agda_out("NotInScope", path="agents/tasks/LJ-1-286/ProbeLJ1286A.agda")
        v, _ = witness.verdict(self.result(42, out, names=["NotInScope"]), w, root=ROOT)
        self.assertEqual(v, witness.PROBE_RED)

    def test_any_other_tag_at_exit_42_is_probe_red(self):
        w = ROOT / ".pod-state" / "witness" / "W.agda"
        out = agda_out("CoInfectiveImport", path=str(w))
        v, _ = witness.verdict(self.result(42, out, names=["CoInfectiveImport"]), w)
        self.assertEqual(v, witness.PROBE_RED)

    def test_a_heap_wall_and_a_deadline_are_probe_red_and_never_resolved(self):
        w = ROOT / ".pod-state" / "witness" / "W.agda"
        v, _ = witness.verdict(self.result(251, "", heap=True), w)
        self.assertEqual(v, witness.PROBE_RED)
        v, _ = witness.verdict(self.result(None, ""), w)
        self.assertEqual(v, witness.PROBE_RED)

    def test_no_file_starts_no_process(self):
        """The probe path does not exist, so the meter never starts Agda and the name
        stays UNRESOLVED at both measurement points, which gives a delta of 0."""
        m = witness.measure(["agents/tasks/NO-SUCH/Probe.agda::name"], code="LJ-1.999",
                            slots=1)
        self.assertEqual(m["unresolved"], 1)
        self.assertEqual(m["witness_seconds"], 0.0)
        self.assertFalse(m["probe_red"])
        self.assertEqual(m["rows"][0]["value"], witness.NO_FILE)


class UnresolvedCount(Patching):
    """Fact 3's arithmetic: which values count as resolved, and what the delta is."""

    PROBE = "agents/tasks/LJ-1-383/Probe383.agda"

    def stub(self, value):
        self.patch(witness, "_run", lambda *a, **k: {
            "witness": ".pod-state/witness/W.agda", "source": "", "rc": 0,
            "seconds": 0.5, "value": value, "detail": "stub", "error_names_all": []})

    def test_only_pass_counts_as_resolved(self):
        """PASS is the ONLY resolved value. MISSING and PROBE RED both leave the name
        unresolved, which can stop a `go` branch closing and can never open one."""
        self.assertTrue((ROOT / self.PROBE).is_file(), "the sampled probe moved")
        for value, unresolved in ((witness.PASS, 0), (witness.MISSING, 1),
                                  (witness.PROBE_RED, 1)):
            self.stub(value)
            m = witness.measure([self.PROBE + "::x"], code="LJ-1.383", slots=1)
            self.assertEqual(m["unresolved"], unresolved, value)
            self.assertEqual(m["probe_red"], value == witness.PROBE_RED, value)

    def test_the_four_values_are_the_four_of_section_4_7_4(self):
        self.assertEqual({witness.PASS, witness.MISSING, witness.PROBE_RED,
                          witness.NO_FILE},
                         {"pass", "missing", "probe-red", "no-file"})

    def test_the_delta_is_exit_minus_dispatch(self):
        self.patch(witness, "measure", lambda *a, **k: {
            "unresolved": 1, "witness_seconds": 2.5, "probe_red": False, "rows": []})
        t = types.SimpleNamespace(code="LJ-1.999", obligations=["p::x"], obl_before=3)
        delta, seconds, red = witness.witness_delta(t)
        self.assertEqual((delta, seconds, red), (-2, 2.5, False))

    def test_no_dispatch_point_refuses_rather_than_guessing_a_fact(self):
        """R7: drop the return, never guess. A delta needs both measurement points."""
        self.patch(witness, "measure", lambda *a, **k: {
            "unresolved": 1, "witness_seconds": 0.0, "probe_red": False, "rows": []})
        t = types.SimpleNamespace(code="LJ-1.999", obligations=["p::x"], obl_before=None)
        with self.assertRaises(ValueError):
            witness.witness_delta(t)

    def test_a_declared_list_of_the_wrong_type_falls_back_to_the_brief(self):
        """The state file is hand-editable, and `list(5)` is a TypeError in the tick."""
        t = types.SimpleNamespace(code="LJ-1.999", obligations=5, brief=None)
        self.assertEqual(witness._obligations_of_task(t), [])


class Derivation(unittest.TestCase):
    """A4's four steps. The meter derives all four parts and authors nothing."""

    PROBE = ("{-# OPTIONS --cubical --guardedness #-}\n"
             "\n"
             "open import Base.Prelude\n"
             "open import Base.Classical using ( LEM )\n"
             "\n"
             "module LJ-1-383.Probe383 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where\n"
             "\n"
             "module Wire (a : V) where\n"
             "  residue2-false-at-record = a\n")

    def probe(self, text=None):
        d = Path(tempfile.mkdtemp())
        p = d / "Probe383.agda"
        p.write_text(text if text is not None else self.PROBE, encoding="utf-8")
        return p

    def test_the_grammar_takes_a_path_and_a_dotted_name(self):
        self.assertEqual(witness.parse_obligation(
            "agents/tasks/LJ-1-383/Probe383.agda::Wire.residue2-false-at-record"),
            ("agents/tasks/LJ-1-383/Probe383.agda", "Wire.residue2-false-at-record"))
        for bad in ("no-separator", "a::", "::b", "a::b::c", "a::b..c", 5, None):
            with self.assertRaises(witness.DerivationError, msg=repr(bad)):
                witness.parse_obligation(bad)

    def test_the_four_steps_produce_the_designs_own_witness(self):
        src = witness.witness_source(self.probe(),
                                     ["Wire.residue2-false-at-record"], "WitnessA2")
        self.assertIn("open import Base.Classical using ( LEM )", src)   # step 1
        self.assertIn("module WitnessA2 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where", src)
        self.assertIn("import LJ-1-383.Probe383", src)
        self.assertIn("module Target = LJ-1-383.Probe383 {ℓ} lem", src)  # step 3
        self.assertIn("witness = Target.Wire.residue2-false-at-record", src)  # step 4

    def test_the_witness_options_line_always_carries_safe(self):
        """A witness with --safe REFUSES a probe without one: [CoInfectiveImport], exit 42,
        so a probe cannot discharge an obligation with a postulate."""
        src = witness.witness_source(self.probe(), ["Wire.x"], "W")
        self.assertIn("--safe", src.split("\n")[0])
        self.assertTrue(facts.SAFE.search(src))
        kept = witness.ensure_safe("{-# OPTIONS --cubical --safe #-}\n")
        self.assertEqual(kept.count("--safe"), 1, "an existing flag is not duplicated")
        self.assertIn("{-# OPTIONS --safe #-}",
                      witness.ensure_safe("open import Base.Prelude\n"))

    def test_a_brace_name_is_wrapped_and_a_paren_name_is_bare(self):
        self.assertEqual(witness.binder_application("{ℓ : Level} (lem : LEM (ℓ-suc ℓ))"),
                         "{ℓ} lem")
        self.assertEqual(witness.binder_application("{ℓ ℓ' : Level} (a b : X)"),
                         "{ℓ} {ℓ'} a b")
        self.assertEqual(witness.binder_application(""), "")

    def test_the_widest_telescope_in_the_tree_derives(self):
        """Eight explicit parameters, agents/tasks/LJ-1-306/GenAgree.agda:50."""
        real = ROOT / "agents" / "tasks" / "LJ-1-306" / "GenAgree.agda"
        if not real.is_file():
            self.skipTest("the sampled probe is archived")
        src = witness.witness_source(real, ["isTmAt"], "W")
        self.assertIn("module Target = LJ-1-306.GenAgree {ℓ} M M-trans numeralL "
                      "numeralL-fst pairʟ pairʟ-fst sucʟ sucʟ-fst", src)

    def test_a_multi_line_header_is_joined_until_where(self):
        text = ("{-# OPTIONS --cubical --safe #-}\n"
                "open import Base.Prelude\n"
                "\n"
                "module M.N {ℓ : Level}\n"
                "  (a : A)   -- a comment that says where, deliberately\n"
                "  where\n"
                "\n"
                "x = a\n")
        preamble, name, telescope = witness.split_header(text)
        self.assertEqual(name, "M.N")
        self.assertEqual(witness.binder_application(telescope), "{ℓ} a")
        self.assertNotIn("module", preamble)

    def test_a_literate_probe_gives_its_fences_and_no_prose(self):
        d = Path(tempfile.mkdtemp())
        p = d / "P.lagda.md"
        p.write_text("Some prose that is not Agda.\n\n"
                     "```agda\n{-# OPTIONS --cubical --safe #-}\n"
                     "module P where\n```\n", encoding="utf-8")
        code = witness.probe_code(p)
        self.assertNotIn("prose", code)
        self.assertIn("module P where", code)

    def test_a_grouped_witness_names_every_obligation(self):
        """The fast path is only ever a fast path: exit 0 proves every name present."""
        src = witness.witness_source(self.probe(), ["Wire.a", "Wire.b"], "W")
        self.assertIn("witness0 = Target.Wire.a", src)
        self.assertIn("witness1 = Target.Wire.b", src)

    def test_a_name_below_the_header_is_a_derivation_error_and_not_a_guess(self):
        """Cost one of the disclosed departure: the preamble is the lines ABOVE the header."""
        with self.assertRaises(witness.DerivationError):
            witness.split_header("x = 1\n")
        with self.assertRaises(witness.DerivationError):
            witness.binder_application("ℓ")

    def test_the_brief_field_is_read_with_tomllib(self):
        """`## OBLIGATION NAMES` carries one TOML assignment, and pre-flight P14 reads the
        same syntax. A hand-written string reader would let the two disagree."""
        d = Path(tempfile.mkdtemp())
        b = d / "LJ-1-386.md"
        b.write_text("# LJ-1.386: a code exists\n\n## OBLIGATION NAMES\n"
                     'obligations = ["agents/tasks/LJ-1-386/Probe386.agda::code-exists",\n'
                     '               "agents/tasks/LJ-1-386/Probe386.agda::code-band"]\n\n'
                     "## BRANCHES\nobligations_delta_max = -2\n", encoding="utf-8")
        self.assertEqual(witness.obligations_of(b),
                         ["agents/tasks/LJ-1-386/Probe386.agda::code-exists",
                          "agents/tasks/LJ-1-386/Probe386.agda::code-band"])
        bare = d / "no-field.md"
        bare.write_text("# LJ-1.999\n\nno obligation field at all\n", encoding="utf-8")
        self.assertEqual(witness.obligations_of(bare), [],
                         "a brief with no field declares nothing; P14 refuses it")

    def test_the_witness_name_is_stable_and_unique_per_obligation(self):
        a = witness.witness_name("LJ-1.383", "p::x")
        self.assertEqual(a, witness.witness_name("LJ-1.383", "p::x"))
        self.assertNotEqual(a, witness.witness_name("LJ-1.383", "p::y"))
        self.assertTrue(a.startswith("Witness-LJ-1-383-"))


class VerificationTarget(Patching):
    """Section 4.3.2. Four cases, and they partition the input space."""

    def test_a_changed_master_sends_the_run_at_everything(self):
        tgt = facts.verification_target(["src/L/BoundedSubset.lagda.md"], "LJ-1.383")
        self.assertEqual(tgt, ["src/Everything.lagda.md"])

    def test_a_new_unwired_master_runs_alone_first_and_a_wired_one_does_not(self):
        """`Everything` never reads an unwired master, so conjunct 1 would be vacuous for
        it. It must also EXIST: an unwired name with no file is a delete, not a chapter."""
        d = self.tmp()
        (d / "src" / "L").mkdir(parents=True)
        new, wired = "src/L/NewChapter.lagda.md", "src/L/Wired.lagda.md"
        for rel in (new, wired):
            (d / rel).write_text("```agda\n```\n", encoding="utf-8")
        self.patch(facts, "imported_by_everything", lambda root=None: {"L.Wired"})
        self.assertEqual(facts.verification_target([new, wired], "LJ-1.383", root=d),
                         [new, "src/Everything.lagda.md"])
        self.assertEqual(facts.verification_target([wired], "LJ-1.383", root=d),
                         ["src/Everything.lagda.md"])
        self.assertEqual(facts.verification_target(["src/L/Gone.lagda.md"], "LJ-1.383",
                                                   root=d),
                         ["src/Everything.lagda.md"], "a deleted master is not a new one")

    def test_probes_are_the_target_when_no_master_changed(self):
        ch = ["agents/tasks/LJ-1-383/Probe383.agda",
              "agents/tasks/LJ-1-383/lj-1.383-report.md"]
        self.assertEqual(facts.verification_target(ch, "LJ-1.383"),
                         ["agents/tasks/LJ-1-383/Probe383.agda"])

    def test_another_tasks_probe_is_not_a_target(self):
        ch = ["agents/tasks/LJ-1-306/GenAgree.agda"]
        self.assertEqual(facts.verification_target(ch, "LJ-1.383"), [])

    def test_a_report_only_return_gives_an_empty_list(self):
        """Case 4: no Agda process starts and conjunct 1 HOLDS VACUOUSLY."""
        self.assertEqual(
            facts.verification_target(["agents/tasks/LJ-1-383/lj-1.383-report.md"],
                                      "LJ-1.383"), [])
        self.assertEqual(facts.verification_target([], "LJ-1.383"), [])

    def test_an_unreadable_closure_module_degrades_in_the_strict_direction(self):
        """Every changed master then reads as NEW, so each runs ALONE and Everything runs
        too: strictly more Agda, never less. The alternative stops the loop."""
        d = self.tmp()
        (d / "src" / "L").mkdir(parents=True)
        (d / "src" / "L" / "Wired.lagda.md").write_text("```agda\n```\n", encoding="utf-8")
        tgt = facts.verification_target(["src/L/Wired.lagda.md"], "LJ-1.383", root=d)
        self.assertEqual(tgt, ["src/L/Wired.lagda.md", "src/Everything.lagda.md"])


class ChangedFiles(Patching):
    """Fact 4. ONE snapshot at exit, scoped to the task, with everything else foreign."""

    def repo(self):
        d = self.tmp()
        subprocess.run(["git", "init", "-q"], cwd=d, check=True,
                       capture_output=True, text=True)
        return d

    def test_the_snapshot_reads_untracked_files_inside_a_new_directory(self):
        """`git diff` cannot see an untracked file, and check-timing.py:195 records that a
        brand-new master evaded that gate entirely. Without `--untracked-files=all` git
        prints the DIRECTORY `sub/` and never the file inside it."""
        d = self.repo()
        (d / "new.txt").write_text("x", encoding="utf-8")
        (d / "sub").mkdir()
        (d / "sub" / "deep.txt").write_text("y", encoding="utf-8")
        self.assertEqual(facts._status_paths(d), ["new.txt", "sub/deep.txt"])

    def test_a_rename_reports_the_new_path_and_not_the_arrow(self):
        d = self.repo()
        (d / "old.txt").write_text("x", encoding="utf-8")
        git = ["git", "-c", "user.email=t@t", "-c", "user.name=t"]
        subprocess.run(git + ["add", "old.txt"], cwd=d, check=True, capture_output=True)
        subprocess.run(git + ["commit", "-qm", "one"], cwd=d, check=True,
                       capture_output=True)
        subprocess.run(git + ["mv", "old.txt", "new.txt"], cwd=d, check=True,
                       capture_output=True)
        self.assertEqual(facts._status_paths(d), ["new.txt"])

    def test_a_foreign_path_never_enters_the_facts(self):
        """THE SCOPE RESTRICTION STOPS TASK A BEING GRADED ON TASK B'S WORK. In scope is
        `write_paths(brief)` or the task's own directory; every other path is foreign."""
        snapshot = ["agents/tasks/LJ-1-999/Probe.agda",
                    "agents/tasks/LJ-1-401/Other.agda",
                    "dev/PLAN.md",
                    "src/L/Granted.lagda.md"]
        self.patch(facts, "_status_paths", lambda root: list(snapshot))
        self.patch(facts, "write_paths", lambda brief: {"src/L/Granted.lagda.md"})
        mine, foreign = facts.changed_files_scoped("LJ-1.999", "brief.md")
        self.assertEqual(mine, ["agents/tasks/LJ-1-999/Probe.agda",
                                "src/L/Granted.lagda.md"])
        self.assertEqual(foreign, ["agents/tasks/LJ-1-401/Other.agda", "dev/PLAN.md"])
        self.assertEqual(sorted(mine + foreign), sorted(snapshot),
                         "the two halves partition the snapshot")

    def test_a_task_with_no_grant_owns_only_its_own_directory(self):
        snapshot = ["agents/tasks/LJ-1-999/report.md", "src/L/Granted.lagda.md"]
        self.patch(facts, "_status_paths", lambda root: list(snapshot))
        mine, foreign = facts.changed_files_scoped("LJ-1.999", None)
        self.assertEqual(mine, ["agents/tasks/LJ-1-999/report.md"])
        self.assertEqual(foreign, ["src/L/Granted.lagda.md"])


class Fact7(Patching):
    """Amendment A10. `lines` is the in-fence line count of the task's own write scope."""

    def test_the_count_agrees_with_the_ledgers_own_counter_file_by_file(self):
        """ONE CALIBER. `scripts/measure/ledger.py:145` is its home and this reuses the
        module. A second rule under one name is how two figures start to disagree."""
        led = accept.ledger()
        self.assertIsNotNone(led, "scripts/measure/ledger.py must load")
        masters = [m for m in led.countable_masters()][:12]
        self.assertTrue(masters, "the tree has countable masters")
        for m in masters:
            self.assertEqual(accept.in_fence_lines([m]), led.count(m, at_head=False), m)

    def test_it_reads_the_working_tree_and_not_head(self):
        """The work is uncommitted at the acceptance point, so `at_head` counts zero."""
        d = self.tmp()
        (d / "src").mkdir()
        (d / "src" / "New.lagda.md").write_text(
            "prose\n\n```agda\nmodule New where\n\nx = 1\n```\n", encoding="utf-8")
        self.assertEqual(accept.in_fence_lines(["src/New.lagda.md"], root=d), 2,
                         "two non-blank lines inside the fence, and the prose is not one")

    def test_a_probe_and_a_report_and_a_deleted_file_contribute_nothing(self):
        d = self.tmp()
        (d / "p.agda").write_text("module P where\nx = 1\n", encoding="utf-8")
        (d / "r.md").write_text("a report\n", encoding="utf-8")
        self.assertEqual(accept.in_fence_lines(["p.agda", "r.md", "gone.lagda.md"],
                                               root=d), 0)

    def test_the_two_catalogs_are_excluded_by_the_owners_ruling(self):
        """2026-08-10: a catalog grows with the project and drifts in the direction that
        flatters the tree. Wiring one master must not buy a task 98 lines of ratio."""
        led = accept.ledger()
        self.assertIn("src/Everything.lagda.md", led.UNCOUNTED)
        real = accept.in_fence_lines(["src/Everything.lagda.md"])
        self.assertEqual(real, 0)
        alone = led.count("src/Everything.lagda.md", at_head=False)
        self.assertGreater(alone, 50, "the catalog does hold lines; they are excluded")

    def test_an_absent_ledger_gives_none_and_never_zero(self):
        """A guessed 0 would make DD24's ratio infinite and flatter nothing; a guessed
        count would flatter the task. `matches()` refuses every fact 7 key on None."""
        old = list(accept._LEDGER)
        accept._LEDGER[:] = [None]
        self.addCleanup(lambda: accept._LEDGER.__setitem__(slice(None), old))
        self.assertIsNone(accept.in_fence_lines(["src/L/BoundedSubset.lagda.md"]))
        rec = {"concurrency": 1,
               "facts": {"exit_code": 0, "error_class": None, "obligations_delta": -1,
                         "changed_files": ["a"], "seconds": 3.0, "heap_wall": False,
                         "lines": None}}
        self.assertFalse(table.matches({"seconds_per_line_max": 1.0}, rec))
        self.assertTrue(table.matches({"seconds_per_line_max": 1.0},
                                      dict(rec, facts=dict(rec["facts"], lines=100))),
                        "with a real count the same row matches, so the None is the guard")

    def test_the_key_the_table_reads_is_the_key_the_runner_writes(self):
        """ONE NAME ACROSS TWO MODULES. The runner writes `facts["lines"]` and the router
        reads `FACT_KEY_A10`; a rename on either side must fail here, not in the loop."""
        self.assertEqual(table.FACT_KEY_A10, "lines")
        self.assertIn("seconds_per_line_max", table.WHEN_TYPES)
        self.assertIn("seconds_per_line_min", table.WHEN_TYPES)


class AcceptanceRecord(Patching):
    """Section 5.4. The record shape the router reads, with no Agda started."""

    def stub(self, targets=(), rc=0, lines=7):
        self.patch(accept.facts_mod, "changed_files_scoped",
                   lambda code, brief, root=None: (["src/L/Foo.lagda.md"], ["dev/PLAN.md"]))
        self.patch(accept.facts_mod, "verification_target",
                   lambda ch, code, root=None: list(targets))
        self.patch(accept, "conjunct1", lambda tgts, root=None, deadline_s=None,
                   slots=None, tier="wide": {
                       "rc": rc, "agda_class": None if rc == 0 else "other",
                       "seconds": 3.5, "heap_wall": False, "caliber": facts.CALIBER[tier],
                       "tier": tier, "concurrency": 1, "error_names_all": [],
                       "runs_all": [], "vacuous": not tgts})
        self.patch(accept.witness_mod, "witness_delta", lambda t: (-2, 1.5, False))
        self.patch(accept, "spec_surface", lambda root=None: True)
        self.patch(accept, "closure", lambda root=None: True)
        self.patch(accept, "unbound_new", lambda ch, before, root=None: (True, True))
        self.patch(accept, "precommit_set", lambda code=None, root=None: True)
        self.patch(accept, "in_fence_lines", lambda ch, root=None: lines)
        self.patch(accept, "_write_run_record", lambda t, rec, root=None: None)

    def test_the_record_carries_all_seven_facts_and_its_tier(self):
        self.stub(targets=["src/Everything.lagda.md"])
        rec = accept.run_acceptance(accept._Task("LJ-1.999", tier="heavy"))
        self.assertEqual(set(rec["facts"]),
                         set(table.FACT_KEYS) | {table.FACT_KEY_A10},
                         "the router's fact vocabulary is the runner's, exactly")
        self.assertEqual(rec["facts"]["lines"], 7)
        self.assertEqual(rec["facts"]["exit_code"], 0)
        self.assertEqual(rec["tier"], "heavy")
        self.assertEqual(rec["caliber"], facts.CAP_HEAVY,
                         "A14: a HEAVY task measures under -M12g, and the record says so")
        self.assertEqual(rec["changed_files_foreign"], ["dev/PLAN.md"])

    def test_a_failed_conjunct_names_its_own_class_and_takes_exit_1(self):
        self.stub(targets=["src/Everything.lagda.md"])
        self.patch(accept, "closure", lambda root=None: False)
        rec = accept.run_acceptance(accept._Task("LJ-1.999"))
        self.assertEqual(rec["facts"]["exit_code"], 1, "1 is the runner's, A5")
        self.assertEqual(rec["facts"]["error_class"], "closure_open")

    def test_the_order_is_5_1_2_3_4_6_and_the_first_failure_names_the_class(self):
        self.stub(targets=["src/Everything.lagda.md"], rc=42)
        self.patch(accept, "spec_surface", lambda root=None: False)
        rec = accept.run_acceptance(accept._Task("LJ-1.999"))
        self.assertEqual(rec["facts"]["error_class"], "spec_surface",
                         "A3 makes the spec surface undefeatable, so it is measured first")

    def test_no_change_in_scope_drops_the_return(self):
        self.stub()
        self.patch(accept.facts_mod, "changed_files_scoped",
                   lambda code, brief, root=None: ([], []))
        self.assertIsNone(accept.run_acceptance(accept._Task("LJ-1.999")),
                          "R7, section 4.3.2 case 3: no fact has a source")

    def test_r4_reads_the_outcome_and_a_no_go_needs_only_5_and_6(self):
        rec = {"conjuncts": {1: False, 2: False, 3: False, 4: False, 5: True, 6: True}}
        self.assertTrue(accept.r4_holds(rec, {"outcome": "no-go"}))
        self.assertFalse(accept.r4_holds(rec, {"outcome": "go"}))
        self.assertFalse(accept.r4_holds({"conjuncts": {5: False, 6: True}},
                                         {"outcome": "no-go"}))

    def test_the_first_failing_target_is_the_verification_run(self):
        rec = {"runs_all": [{"target": "a.agda", "rc": 0},
                            {"target": "b.agda", "rc": 42},
                            {"target": "c.agda", "rc": 42}]}
        self.assertEqual(accept.first_failing_target(rec), "b.agda")
        self.assertIsNone(accept.first_failing_target({"runs_all": []}))


if __name__ == "__main__":
    os.environ.setdefault("GIT_OPTIONAL_LOCKS", "0")
    unittest.main(verbosity=2)
