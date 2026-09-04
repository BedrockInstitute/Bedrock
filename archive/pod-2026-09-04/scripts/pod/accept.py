#!/usr/bin/env python3
"""The acceptance runner of AD13, amendment A5: six conjuncts, one record, seven facts.

WHY THIS FILE EXISTS. A5 gives the acceptance test its enforcement point: IT IS FACT 1.
An earlier draft of the design listed conjuncts that no fact could see, so a task could
route to `done` with three of them red. Here `exit_code` is the RUNNER's code and not
Agda's, and every conjunct that fails names its own error class.

THE MEASURED FAILURE BEHIND THE WHOLE FILE. On 2026-08-16 `[LJ-1.375]` found a verdict
LINE that disagreed with its own BODY, and `[LJ-1.376]` named the orchestrator's own
unread live record the costliest defect in the tree. A runner that measures six facts
and never reads a report cannot read a report wrongly.

THE ORDER IS 5, 1, 2, 3, 4, 6, AND THE FIRST FAILURE NAMES THE CLASS. Conjunct 5 runs
first for two reasons that agree: it is the cheapest, at one sha256 per surface file, and
A3 makes the spec surface undefeatable, so an Agda failure must never hide a change to
the trophy statement.

IT MEASURES ALL SIX FIRST, THEN TESTS ALL SIX. A branch may route on a fact whose
conjunct failed, which is how a NO-GO reaches a `done` row, so the measuring never stops
early. Only conjunct 1 stops at its FIRST failing target, because section 4.3.2 rules
that the first failing run IS the verification run.

WHAT THIS FILE DOES NOT DO. It never reads a report, it never decides an action and it
never closes a task. `scripts/pod/table.py` routes the record it returns and
`scripts/pod/pod.py` performs the action.

FACT 7 IS MEASURED HERE, amendment A10. DD24's bar is a RATIO, seconds over in-fence
lines, so the record carries `lines`: the in-fence line count of the task's own write
scope. NOTHING ELSE PRODUCES IT. `matches()` in `scripts/pod/table.py` reads it as
`FACT_KEY_A10` and refuses every `seconds_per_line` key while it is absent, so a missing
count can only stop a row matching and can never open one.

Usage:
  accept.py --task <CODE> --brief <PATH> [--obl-before <n>] [--tier wide|heavy]
                           run the six conjuncts over one task and print its record
  accept.py --conjuncts    print the six conjuncts, their classes and their commands
Exit status: 0 all six held, 1 one failed, the return carries no change, or `agda` could
not start, 2 usage error.
"""

from __future__ import annotations

import importlib.util
import json
import os
import subprocess
import sys
import time
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
import facts as facts_mod  # noqa: E402
import heads as heads_mod  # noqa: E402
import witness as witness_mod  # noqa: E402

ROOT = find_root(__file__)

#: The class each RUNNER conjunct writes when it fails. Conjunct 1 is absent because its
#: class is AGDA's, from `classify()` at `scripts/pod/facts.py:108`.
RUNNER_CLASS = {2: "obligations_up", 3: "closure_open", 4: "unbound_hyp",
                5: "spec_surface", 6: "lint"}

#: Section 4.3.2 case 4: a report-only return. No Agda process starts and conjunct 1
#: HOLDS VACUOUSLY. The record still carries the caliber, because a reader comparing two
#: records must see that this one measured no seconds at all.
VACUOUS = {"rc": 0, "agda_class": None, "seconds": 0.0, "heap_wall": False,
           "caliber": facts_mod.CAP, "error_names_all": [], "runs_all": [],
           "vacuous": True}

#: Conjunct 6's member list is PINNED. It is rows 1, 2, 3, 4, 6 and 33 of design section
#: 7.1, plus `check-survey-quotes.py`. A lint red PARKS the task: R14 says the tree's
#: hygiene is not a thing a worker may trade away for a proof.
PRECOMMIT_SET = (
    ("lint-agda", ["scripts/gate/lint-agda.py", "--check"]),          # row 1
    ("lint-prose", ["scripts/gate/lint-prose.py", "--check"]),        # row 2
    ("glossary", ["scripts/gate/check-glossary.py", "--check"]),      # row 3
    ("fences", ["scripts/gate/check-fences.py", "--check"]),          # row 4
    ("probes", ["scripts/gate/check-probes.py", "--check"]),          # row 6
    ("markers", ["scripts/site/weave-i18n.py", "--check"]),           # row 33
)

#: The two checkers the runner calls by their own flag, not through the set above.
SPEC_SURFACE = ["scripts/pod/check-spec-surface.py", "--check"]
CLOSURE = ["scripts/pod/check-closure.py", "--check", "closure"]
UNBOUND = ["scripts/measure/check-unbound-hyp.py", "--check"]
SURVEY_QUOTES = ["scripts/pod/check-survey-quotes.py"]

#: The gate set gets its own deadline. A checker that hangs must not hold an Agda slot
#: for the whole `worker_deadline_s`, and none of the seven starts Agda.
GATE_DEADLINE_S = 600

#: A15. A PER-TASK acceptance run defaults to the WIDE tier's caliber, `-A64m -I0 -M2g`
#: (owner's ruling 2026-08-23, second same-day ruling; was `-M8g`, then briefly `-M4g`
#: for a few hours), which is the worker's own default too, so an acceptance measurement
#: compares directly with the run record beside it. A HEAVY task passes `tier="heavy"`
#: and `run_agda()` gives it `-M4g` instead (was `-M12g`, unchanged by the second
#: ruling). The whole-tree caliber, `facts.CAP_TREE`, belongs to a `make check` and
#: never to this file.
DEFAULT_TIER = facts_mod.DEFAULT_TIER


def _run(argv, root=None, deadline_s=GATE_DEADLINE_S):
    """One checker, by explicit path, under the repository root. It never raises.

    A checker that cannot start is a FAILED conjunct and never a passed one. FM12's rule
    holds here: an unreadable sensor must REFUSE, never clear. A green conjunct on a
    missing checker is the exact shape of a gate that guards nothing.
    """
    root = ROOT if root is None else Path(root)
    try:
        done = subprocess.run([sys.executable] + [str(a) for a in argv], cwd=root,
                              capture_output=True, text=True, timeout=deadline_s)
    except (OSError, subprocess.TimeoutExpired) as e:
        return 1, f"{argv[0]}: could not run ({e})"
    return done.returncode, (done.stdout + done.stderr)


# ---------------------------------------------------------------- the six conjuncts


def spec_surface(root=None):
    """Conjunct 5, AD22. `check-spec-surface.py --check` exits 0. Class `spec_surface`."""
    return _run(SPEC_SURFACE, root)[0] == 0


def conjunct1(tgts, root=None, deadline_s=None, slots=None, tier=DEFAULT_TIER):
    """Conjunct 1, AD13. The FIRST failing run, or the LAST when every one passes.

    Section 4.3.2 partitions the targets four ways and `verification_target()` at
    `scripts/pod/facts.py` performs the partition. Case 4 gives an EMPTY list and this
    returns VACUOUS: a report-only return starts no Agda process.

    THE TWO BRANCHES COUNT PROCESSES DIFFERENTLY, and the difference is the point.
    `facts.slots()` counts the Agda processes live DURING the measurement, so a real run
    counts its OWN process and a solo run reads 1, which is what `matches()` needs before
    it admits a seconds key. Case 4 starts no process, so it passes `own=0`: a vacuous
    record must never read as a solo measurement and let `seconds_max` match 0.0 s that
    nothing measured.

    `runs_all` carries every wall the runner measured, which is the provenance a later
    reader needs to see that the record's `seconds` is one run of several.
    """
    root = ROOT if root is None else Path(root)
    if not tgts:                                             # case 4
        live = facts_mod.slots(own=0) if slots is None else slots
        return dict(VACUOUS, concurrency=live, tier=tier,
                    caliber=facts_mod.caliber_of(tier))      # the tier it WOULD have used
    live = facts_mod.slots() if slots is None else slots
    if deadline_s is None:
        deadline_s = heads_mod.limits()["agda_deadline_s"]
    runs, r = [], None
    for target in tgts:                       # run_agda takes ONE target, 4.3.1
        r = facts_mod.run_agda(target, root, deadline_s, live, tier=tier)
        runs.append({"target": target, "rc": r["rc"], "seconds": r["seconds"]})
        if r["rc"] != 0:
            return dict(r, runs_all=runs)
    return dict(r, runs_all=runs)


def closure(root=None):
    """Conjunct 3, section 7.2. `check-closure.py --check closure` exits 0.

    A master that `Everything` does not import has no consumers, so conjunct 1 is vacuous
    for it. This conjunct is what notices the orphan.
    """
    return _run(CLOSURE, root)[0] == 0


def unbound_findings(root=None):
    """The finding SET of `check-unbound-hyp.py`, as `file:name` strings.

    THE TOOL HAS NO BASELINE MODE, and a naive read fails every task for ever: MEASURED
    2026-08-17 it prints five findings today (`src/L/Absorption.lagda.md:398` and `:400`,
    `src/L/InjChain.lagda.md:471`, `src/L/Reflect.lagda.md:365`,
    `src/L/StageCardinal.lagda.md:281`). So the pre-flight snapshots the set, the
    acceptance re-runs it, and the conjunct fails on a SET DIFFERENCE.

    THE KEY IS THE HYPOTHESIS NAME, NOT THE LINE. MEASURED 2026-08-21 on LJ-1.469: an
    import widened earlier in the same file shifted two untouched findings from
    `:398`/`:400` to `:399`/`:401`; a line-keyed set difference read that shift as two
    new findings and parked a task with a delivered obligation. The tool's own output
    carries the bound name at each line (`{file}:{line}: {name}: {why}`,
    `scripts/measure/check-unbound-hyp.py:367`), so keying on it instead survives a shift
    an unrelated edit causes.
    """
    rc, out = _run(UNBOUND, root)
    found = []
    for line in out.split("\n"):
        head = line.split(":")
        if len(head) >= 3 and head[1].strip().isdigit() and head[0].endswith(".lagda.md"):
            found.append(f"{head[0]}:{head[2].strip()}")
    return sorted(set(found))


def unbound_new(ch, before, root=None):
    """Conjunct 4, section 7.1 row 30: no NEW unbound hypothesis. Returns (held, vacuous).

    The tool reads only tracked masters, so a task that changed no master passes
    VACUOUSLY and the record carries `unbound_vacuous: true`. `before` is the pre-flight
    snapshot carried on the task; a task dispatched without one gets an EMPTY set, which
    is the strict direction and never the lenient one.
    """
    masters = [p for p in ch if p.startswith("src/") and p.endswith(".lagda.md")]
    if not masters:
        return True, True                     # vacuous: no master changed
    now = set(unbound_findings(root))
    return not (now - set(before or ())), False


def precommit_set(code=None, root=None):
    """Conjunct 6. The PINNED member list, plus `check-survey-quotes.py`. Class `lint`.

    `check-survey-quotes.py` takes the task CODE, because the gate is ONE task: the
    runner names the task that just returned, and `--all` is a survey tool that MEASURED
    80 failures over 278 pairs, every one a record written before the amendment of
    2026-08-16 and never rewritten.
    """
    for _name, argv in PRECOMMIT_SET:
        if _run(argv, root)[0] != 0:
            return False
    if code:
        return _run(SURVEY_QUOTES + [code], root)[0] == 0
    return True


def precommit_detail(code=None, root=None):
    """Which ONE member of `precommit_set()` failed, and its output, truncated.

    **CONJUNCT 6 IS SEVEN CHECKS WIDE AND THE RECORD NAMED NONE OF THEM.** Conjunct 5
    got `spec_surface_detail` at backlog item 6 (2026-08-19) for exactly this reason:
    `error_class: "lint"` alone cannot distinguish a stray glossary term from a
    misplaced fence from an unanswered survey citation, so a redispatched worker gets
    told to fix an error it cannot identify, and a human reviewing the record later has
    to manually re-run all seven checks against a worktree that may have already moved
    past the failing state. MEASURED on `[LJ-1.643]`, 2026-08-26: two consecutive
    critic dispatches hit `sys-lint-accept` with byte-identical facts, and by the time
    a maintainer went looking, every one of the seven checks passed clean again, the
    worktree having moved on. The SAME re-run-on-failure pattern `spec_surface_detail`
    uses, one call site only, called ONLY when `precommit_set()` already returned
    False, so the cost is one process on the rare (already red) path and nothing on
    the common (green) one.

    **`survey-quotes` GETS ITS OWN, WIDER CAP.** The six `PRECOMMIT_SET` checks each
    report one localised defect, so 600 characters covers the useful part. Survey-quotes
    reports an ENUMERATION, one line per unanswered path, and the enumeration IS the fix:
    a worker that never sees a path was never told to answer it. MEASURED on `[LJ-1.685]`,
    2026-08-26: ten CANDIDATE paths went unanswered and the 600-character cap kept only
    eight of the ten lines, cutting the enumeration and the compliance instruction below
    it. The worker in that case reconstructed the missing two from the check itself
    rather than from this field, so the truncation did not cause that failure, but a
    worker that trusts the injected note alone has no such fallback. 2,000 characters
    holds the worst case this table can produce today (ten unanswered CANDIDATE lines
    plus the instruction paragraph, MEASURED under 1,200) with a wide margin.
    """
    for name, argv in PRECOMMIT_SET:
        rc, out = _run(argv, root)
        if rc != 0:
            return f"{name}: " + " ".join(out.split())[:600]
    if code:
        rc, out = _run(SURVEY_QUOTES + [code], root)
        if rc != 0:
            return "survey-quotes: " + " ".join(out.split())[:2000]
    return ""


# ---------------------------------------------------------------- fact 7, amendment A10


_LEDGER = []


def ledger():
    """`scripts/measure/ledger.py`, the ONE home of the in-fence line caliber, or None.

    It is loaded BY PATH because `scripts/measure/` is not a package and this file's
    `sys.path` holds `scripts/` and `scripts/pod/` only. It costs 0.012 s to load,
    MEASURED 2026-08-18, and the module is cached here for the process.
    """
    if _LEDGER:
        return _LEDGER[0]
    path = ROOT / "scripts" / "measure" / "ledger.py"
    mod = None
    try:
        spec = importlib.util.spec_from_file_location("pod_ledger", path)
        mod = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(mod)
    except Exception:                          # a ledger that will not load must not stop
        mod = None                             # the tick; `lines` is then absent, not 0
    _LEDGER.append(mod)
    return mod


def in_fence_lines(paths, root=None):
    """Fact 7 `lines`, A10: the in-fence line count of the task's own write scope.

    THE CALIBER IS THE LEDGER'S AND IT IS NOT RE-INVENTED. `count()` at
    `scripts/measure/ledger.py:145` counts non-blank lines inside ` ```agda ` fences, and
    this function reads the SAME fence pattern out of that module, `ledger.FENCE`, then
    applies the same non-blank rule. `test_pod_facts.py` asserts the two agree file by
    file over the real masters, so a change to the ledger's rule fails a test here rather
    than drifting silently. It returns None when the ledger will not load, because a
    guessed line count would flatter DD24's ratio.

    THREE RULES, EACH DISCLOSED AS A CHOICE.

    - **It reads the WORKING TREE, not HEAD.** The ledger reads HEAD, because it records
      the repository. Fact 7 measures the work this task just did, which is uncommitted at
      the acceptance point, so `at_head` would count zero for every new file.
    - **A `.agda` probe contributes 0.** It carries no fence, and counting its raw lines
      would be a SECOND caliber under one name. A probe-only task therefore reads
      `lines = 0` and `matches()` refuses both ratio keys against it.
    - **The two catalogs are excluded**, `ledger.UNCOUNTED`. The owner ruled on 2026-08-10
      that `src/Everything.lagda.md` and `src/Landmarks.lagda.md` never count toward a
      threshold, because a catalog grows with the project and drifts in the direction that
      flatters the tree. Wiring one new master into `Everything` must not buy a task 98
      lines of ratio.
    """
    led = ledger()
    if led is None:
        return None
    root = ROOT if root is None else Path(root)
    total = 0
    for rel in paths:
        if not rel.endswith(".lagda.md") or rel in led.UNCOUNTED:
            continue
        try:
            text = (root / rel).read_text(encoding="utf-8")
        except OSError:
            continue                           # deleted in this task's own scope: 0 lines
        total += sum(1 for block in led.FENCE.findall(text)
                     for line in block.split("\n") if line.strip())
    return total


# ---------------------------------------------------------------- the record


def first_failing_target(rec):
    """`redispatch_narrower` reads this: the first target whose run did not exit 0.

    It reads `runs_all`, which conjunct 1 fills in target order, so the answer is the run
    section 4.3.2 already called the verification run. It returns None when every run
    passed, and `apply()` then narrows nothing rather than guessing a file.
    """
    for run in rec.get("runs_all") or ():
        if run.get("rc") != 0:
            return run.get("target")
    return None


def r4_holds(rec, row):
    """R4, amended by A6: a `done` row closes only when its `outcome`'s conjuncts hold.

    | outcome | conjuncts required | why |
    |---|---|---|
    | `go`    | all six | The task claims landed work, so every measure of it must hold |
    | `no-go` | 5 and 6 | A NO-GO lands no proof, so conjuncts 1 to 4 measure nothing.
                          Conjuncts 5 and 6 protect the TREE and still bind |

    Without the split, A6 and AD13 contradict each other: a `done` row may match
    `exit_code = 42`, because a stated NO-GO discharges the obligation to ANSWER, and an
    un-amended R4 forbade exactly that. The handler reads `conjuncts` from the record, so
    the test costs no re-run.
    """
    held = rec.get("conjuncts") or {}
    outcome = (row or {}).get("outcome")
    need = (5, 6) if outcome == "no-go" else (1, 2, 3, 4, 5, 6)
    return all(bool(held.get(n, held.get(str(n)))) for n in need)


def _write_run_record(t, rec, root=None):
    """`agents/tasks/<CODE>/runs/accept-<n>.out`, in the proven format.

    `agents/tasks/LJ-1-331/run.sh` writes this format and `runs/h2-valk.out` beside it is
    a real one: the arm, the file, the flags, `GHCRTS`, the Agda slot count, the load
    average, `# wall seconds` and `# exit`. NOTHING TYPECHECKS A TASK'S PROBES ONCE THE
    TASK CLOSES, so the run file is the only surviving evidence of what was measured.

    THREE DEPARTURES FROM `run.sh`, and each one is a fact that file could not carry.
    `# tier` is A14's, and without it two records under two calibers read as comparable.
    `# in-fence lines` is fact 7, A10, the denominator of DD24's restored ratio. And
    `run.sh:24` writes `# agda slots before`, which counts the OTHER processes; this
    counts the processes live DURING the run, this one included, so the word `before`
    would be false and the key reads `# agda slots during`.
    """
    root = ROOT if root is None else Path(root)
    home = root / "agents" / "tasks" / agents_tree.normalise(t.code) / "runs"
    try:
        home.mkdir(parents=True, exist_ok=True)
        n = 1 + len(list(home.glob("accept-*.out")))
        path = home / f"accept-{n}.out"
        f = rec["facts"]
        lines = [
            f"# arm accept-{n}",
            f"# task {t.code}",
            f"# brief {getattr(t, 'brief', '') or ''}",
            f"# flags (none)",
            f"# GHCRTS {rec['caliber']}",
            f"# tier {rec.get('tier')}",
            f"# agda slots during {rec['concurrency']}",
            f"# load before {os.getloadavg()}",
            # THIS RUN FILE's OWN start, not the dispatch's. `own_line` below compares
            # against `t.started` (the DISPATCH's start, `getattr(t, "started", None)`
            # in `run_acceptance()`), a different moment this acceptance run may follow
            # by minutes or hours. Two timestamps named `started` four lines apart, an
            # owner's-review finding, 2026-08-23: read each against its own paragraph.
            f"# started {time.strftime('%Y-%m-%d %H:%M:%S')}",
        ]
        for n_, ok in sorted((rec.get("conjuncts") or {}).items()):
            lines.append(f"# conjunct {n_} {'held' if ok else 'FAILED'}")
        for run in rec.get("runs_all") or ():
            lines.append(f"# run {run['target']} rc {run['rc']} "
                         f"seconds {run['seconds']}")
        own = rec.get("changed_files_own")
        if own is None:
            own_line = "# changed files own ? (started not recorded)"
        elif not own and f["changed_files"]:
            own_line = (f"# changed files own 0 of {len(f['changed_files'])} "
                        "(INHERITED: this attempt touched none of them)")
        else:
            own_line = f"# changed files own {len(own)} of {len(f['changed_files'])}"
        lines += [
            f"# changed files {len(f['changed_files'])}",
            own_line,
            f"# in-fence lines {f.get('lines')}",
            f"# obligations delta {f['obligations_delta']}",
            f"# wall seconds {f['seconds']}",
            f"# error class {f['error_class']}",
            f"# exit {f['exit_code']}",
            "",
            json.dumps(rec, sort_keys=True),
            "",
        ]
        path.write_text("\n".join(lines), encoding="utf-8")
        return str(path.relative_to(root))
    except OSError:
        # A run file that cannot be written is NOT a failed acceptance. The record is the
        # measurement and the file is its copy; refusing here would park a task over a
        # full disk and lose the six facts the loop already paid for.
        return None


def run_acceptance(t, root=None, tier=None):
    """Section 5.4. One task, six conjuncts, ONE record with SEVEN facts nested.

    It returns None under R7, section 4.3.2 case 3: no changed file in scope, so no fact
    can be measured, the return is DROPPED loudly and the task parks with `no-change`. A
    half-record with a guessed exit code would license a row no evidence supports, and
    the replay would then certify that row as safe (section 4.5.4).

    `tier` is A14's, and the record carries it beside `caliber` so two measurements are
    compared only inside one tier. The task's own `tier` attribute wins when it carries
    one; the default is WIDE, which is A15's per-task acceptance caliber.
    """
    root = ROOT if root is None else Path(root)
    if tier is None:
        tier = getattr(t, "tier", None) or DEFAULT_TIER
    ch, foreign = facts_mod.changed_files_scoped(
        t.code, getattr(t, "brief", None), root)          # fact 4, task-scoped
    # **A MATHEMATICIAN'S AGDA IS DISCARDED, owner's ruling 2026-08-19.** Amendment A21
    # gives the mathematician two verbs, READ and WRITE A BRIEF, and no Agda at all,
    # deliverable or probe. The rule is framed in its slot file and in the brief; this is
    # the detection behind it, and the owner ruled the consequence: the code is thrown
    # away rather than graded.
    #
    # DISCARDING MEANS IT EARNS NOTHING, AND THE FILES ARE NOT DELETED. Dropping them from
    # fact 4 is the whole penalty and it is total: the record cannot show the work, no row
    # can match on it, and no `done` can be earned by it. When the drop empties fact 4, R7
    # below fires and the task parks `no-change`, which is the honest reading of a return
    # whose only output was work it was told not to do. **The files stay on disk on
    # purpose**, exactly as a dead agent's pane is kept: they are the evidence of what
    # happened, and deleting a worker's output is not recoverable.
    role = str(getattr(t, "role", "") or "")
    refused_agda = []
    if role.startswith("mathematician"):
        refused_agda = [p for p in ch if p.endswith(".agda")]
        if refused_agda:
            ch = [p for p in ch if not p.endswith(".agda")]
            print(f"accept: {t.code} ran as `{role}` and wrote Agda, which A21 forbids. "
                  f"DISCARDED from fact 4, kept on disk: {', '.join(refused_agda)}",
                  file=sys.stderr)
    # **A VERDICT ARTIFACT IS MINTED BY A VERDICT SLOT AND BY NOBODY ELSE.**
    # `review-of-*.md` is the reviewer's deliverable by the program's own naming
    # division (`program_task_write()`): the program's INPUT is `review-<PRED>.md`,
    # the reviewer's OUTPUT is `review-of-<PRED>.md`, and the no-go-stated /
    # sys-critic-upheld-no-go rows read the output glob as "a critic has spoken".
    # MEASURED TWICE on 2026-08-27/28: seq 4953 (LJ-1.711) and seq 4973 (LJ-1.712)
    # both closed DONE `sys-critic-upheld-no-go` on a `review-of-*.md` file that the
    # ESCALATED CODER itself wrote during a lint-back-to-author fix pass -- no
    # critic was ever dispatched in either instance. The A21 penalty is the match,
    # and this is its sibling: an author instance's verdict-named writes are
    # dropped from fact 4 and kept on disk as scene evidence. No verdict slot, no
    # verdict artifact; a genuine critic's return still carries its own.
    refused_verdict = []
    if role not in ("mathematician_adversarial", "coder_adversarial"):
        refused_verdict = [p for p in ch
                           if p.rsplit("/", 1)[-1].startswith("review-of-")
                           and p.endswith(".md")]
        if refused_verdict:
            ch = [p for p in ch if p not in refused_verdict]
            print(f"accept: {t.code} ran as `{role}` and wrote verdict-named files, "
                  f"which only an adversarial slot may mint. DISCARDED from fact 4, "
                  f"kept on disk: {', '.join(refused_verdict)}", file=sys.stderr)
    own = facts_mod.own_changed_files(ch, getattr(t, "started", None), root)
    routed_changed = own if own is not None else ch
    scene_changed = ch                 # the whole reused scene, provenance only
    if not routed_changed:
        # **R7 NOW READS THE OWNED SLICE, NOT THE REUSED SCENE.** A dispatch that
        # died before writing a byte over a scene an earlier instance left dirty
        # used to be accepted, routed on the inherited files and, at seq 4904,
        # closed DONE on their verdicts. This attempt's evidence is empty; the
        # record-less `no-change` park is the honest answer, and the scene stays on
        # disk exactly as every other kept refusal does.
        return None                            # R7, section 4.3.2 case 3. No record.
    # PROVENANCE, NOT A CONJUNCT. `own` is None when `t.started` cannot say (the CLI's
    # `_Task` stub carries no `started`), else the subset of `ch` this dispatch itself
    # wrote. Recorded so a reader never has to redo the mtime archaeology `[LJ-1.582]`
    # took (owner's ruling 2026-08-23): it is measured and shown, never routed on,
    # because R1 closes `[row.when]` to the six facts of AD11 plus `lines` and
    # `obligations_open`, and adding a seventh matchable key is an amendment this
    # maintainer does not make. (The seq-4904 repair above does not add one either:
    # it re-scopes what key #4 MEANS, keeping the six-key fence intact.)
    c5 = spec_surface(root)                    # cheapest, and A3 puts it first
    # **THE DETAIL IS CAPTURED ONLY ON FAILURE, and the signature above is unchanged on
    # purpose**: `scripts/tests/test_pod_facts.py:919` patches `spec_surface` with a
    # `lambda root=None: <bool>`, so returning a tuple would break every such patch.
    # The re-run costs one process on the rare path and nothing on the green one.
    #
    # WHY IT IS CAPTURED AT ALL, MEASURED 2026-08-19: LJ-1.386 stopped the loop on
    # `sys-spec-surface` while `src/` carried NO change at all. The mover was
    # `AGENTS.md`, a FOREIGN uncommitted file, because this conjunct reads the WHOLE
    # tree and not the task's scope. The owner was told only「row sys-spec-surface」,
    # which is backlog item 6: the same sentence for a landed trophy, a deleted one and
    # a foreign edit. The row's behaviour is the owner's and stays; this names the mover.
    c5_detail = "" if c5 else " ".join(_run(SPEC_SURFACE, root)[1].split())[:600]
    r1 = conjunct1(facts_mod.verification_target(routed_changed, t.code, root),
                   root, tier=tier)
    d3, wsec, red, open3 = witness_mod.witness_delta(t, root)   # facts 3 and 8, 4.7
    c3 = closure(root)
    c4, uvac = unbound_new(routed_changed, getattr(t, "unbound_before", None), root)
    c6 = precommit_set(t.code, root)
    # SAME PATTERN AS c5_detail, SAME REASON: captured only on the rare red path, so the
    # green path pays nothing. `precommit_detail()` re-runs the seven members in order
    # and returns the first that fails, named, so a reader is not left with `error_class:
    # "lint"` and seven candidates. Backlog item 35, measured on `[LJ-1.643]`.
    c6_detail = "" if c6 else precommit_detail(t.code, root)
    held = [(5, c5), (1, r1["rc"] == 0), (2, d3 <= 0), (3, c3), (4, c4), (6, c6)]
    bad = next((n for n, ok in held if not ok), None)     # order 5, 1, 2, 3, 4, 6
    rec = {"task": t.code, "concurrency": r1["concurrency"],
           "caliber": r1["caliber"], "tier": r1.get("tier", tier),
           "witness_seconds": wsec,
           "obligations_probe_red": red, "error_names_all": r1["error_names_all"],
           "agda_vacuous": r1.get("vacuous", False), "unbound_vacuous": uvac,
           "changed_files_foreign": foreign,   # outside the scope, 4.3.1. Digest counts it
           "changed_files_refused": refused_agda,   # A21: a mathematician's Agda, dropped
           "verdict_files_refused": refused_verdict,   # author-minted review-of, dropped
           "changed_files_own": own,           # provenance for [LJ-1.582]. NOT matchable
           "changed_files_scene": scene_changed,   # the reused scene. NOT matchable
           "spec_surface_detail": c5_detail,   # provenance for the stop. NOT matchable
           "lint_detail": c6_detail,           # which of the 7 conjunct-6 checks. NOT matchable
           "runs_all": r1["runs_all"],         # every other Agda wall, provenance
           "conjuncts": dict(held),            # provenance. R4 reads it. NOT matchable
           "facts": {"exit_code": 0 if bad is None else
                                  (r1["rc"] if bad == 1 else 1),
                     "error_class": None if bad is None else
                                    (r1["agda_class"] if bad == 1 else RUNNER_CLASS[bad]),
                     "obligations_delta": d3, "changed_files": routed_changed,
                     "seconds": r1["seconds"], "heap_wall": r1["heap_wall"],
                     # FACT 7, A10. It is measured over the SAME list fact 4 reports, so
                     # the ratio's numerator and denominator describe one task's work.
                     # (And since the seq-4904 repair, "one task's work" means ONE
                     # attempt's work whenever `started` can say so.)
                     "lines": in_fence_lines(routed_changed, root),
                     # **FACT 8: THE UNRESOLVED COUNT AT EXIT, a LEVEL and not a
                     # difference.** Fact 3 is a delta, and a delta cannot tell a finished
                     # task from an idle one: 0 before and 0 after reads the same as 5 and
                     # 5. So every `done` row had to key on `obligations_delta_max = -2`,
                     # which fires only on the ONE instance that discharges the names, and
                     # a re-run, a review and a mathematician's return were each complete
                     # and unable to close. MEASURED 2026-08-19: five tasks parked
                     # `no-match` in one afternoon, all reading `exit_code 0`,
                     # `error_class None`, `obligations_delta 0`, by three legitimate
                     # routes. The number was already in the meter and was discarded.
                     "obligations_open": open3}}
    # THE DEADLINE NEEDS NO SPECIAL CASE. `r1["rc"]` is None, conjunct 1 fails,
    # `exit_code` is None, and a row keyed on `exit_code_absent` matches.
    rec["run"] = _write_run_record(t, rec, root)
    return rec


# ---------------------------------------------------------------- the command line


class _Task:
    """The four fields `run_acceptance()` reads, for the command line and the tests."""

    def __init__(self, code, brief=None, obl_before=0, unbound_before=(), tier=None):
        self.code, self.brief = code, brief
        self.obl_before, self.unbound_before = obl_before, unbound_before
        self.tier = tier


def _usage(message):
    """One refusal shape for the command line: the reason, then the contract. Exit 2.

    A WRONG FLAG MUST READ AS A WRONG FLAG. `--obl-before abc` used to reach `int()` and
    end in a `ValueError` traceback, which reads as a broken runner. It prints the
    `Usage:` block alone, because the module docstring's measured rules bury it.
    """
    print(f"accept: REFUSED. {message}", file=sys.stderr)
    print(__doc__[__doc__.index("Usage:"):], file=sys.stderr)
    return 2


def main(argv):
    if not argv or argv[0] in ("-h", "--help"):
        print(__doc__)
        return 2
    if argv[0] == "--conjuncts":
        print("order 5, 1, 2, 3, 4, 6. The first failure names the class.")
        print(f"  5 spec_surface   {' '.join(SPEC_SURFACE)}")
        print("  1 <agda class>   agda over verification_target(), section 4.3.2")
        print("  2 obligations_up the witness meter of section 4.7, delta at or below 0")
        print(f"  3 closure_open   {' '.join(CLOSURE)}")
        print(f"  4 unbound_hyp    {' '.join(UNBOUND)}, on a SET difference")
        for name, cmd in PRECOMMIT_SET:
            print(f"  6 lint           {name}: {' '.join(cmd)}")
        print(f"  6 lint           survey-quotes: {' '.join(SURVEY_QUOTES)} <CODE>")
        return 0
    if len(argv) % 2:
        return _usage("every option takes one value")
    args = dict(zip(argv[::2], argv[1::2]))
    unknown = [k for k in args if k not in ("--task", "--brief", "--obl-before", "--tier")]
    if unknown:
        return _usage(f"unknown option {unknown[0]}")
    code = args.get("--task")
    if not code:
        return _usage("--task <CODE> names the task to accept")
    raw = args.get("--obl-before", 0)
    try:
        obl_before = int(raw)
    except (TypeError, ValueError):
        return _usage(f"--obl-before {raw!r} is not an integer")
    tier = args.get("--tier", DEFAULT_TIER)
    if tier not in facts_mod.TASK_TIERS:
        return _usage(f"--tier {tier!r} is not one of "
                      f"{', '.join(facts_mod.TASK_TIERS)}")
    t = _Task(code, args.get("--brief"), obl_before, tier=tier)
    try:
        rec = run_acceptance(t)
    except facts_mod.AgdaStartError as exc:
        # A machine failure and NOT a task fact. Recording an exit code for a process that
        # never started would write a measurement nothing measured.
        print(f"accept: FAILED. {exc}", file=sys.stderr)
        return 1
    except witness_mod.DerivationError as exc:
        return _usage(str(exc))                # a brief that cannot declare an obligation
    if rec is None:
        print(f"{code}: NO CHANGE in scope. R7 drops the return and the task parks.")
        return 1
    print(json.dumps(rec, indent=2, sort_keys=True))
    return 0 if rec["facts"]["exit_code"] == 0 else 1


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
