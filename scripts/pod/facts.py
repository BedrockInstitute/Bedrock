#!/usr/bin/env python3
"""The six-fact recorder of the POD program, and the ONE place the POD starts Agda.

WHY THIS EXISTS, and every rule below is a measured failure and not a preference
(`dev/memos/L9-pod-program-design.md` section 4.3.1):

- **The error regex takes no location.** Agda prints many tags with no
  `file:line.col` prefix. Over the log corpus of 1,017 files, 3,395 error tags and 49
  distinct names, a form anchored on that prefix matched 3,097 and missed 298. The miss
  was not uniform: it lost 30 of 30 `UnsolvedConstraints`, the class a NO-GO routes on.
  The form below matches 3,395 of 3,395.
- **`--safe` is read and never assumed.** 426 tracked live probe files, 417 declare
  `--safe` and 9 do not. A hard-coded `--safe` makes those 9 fail on a safety error and
  records a wrong class.
- **The heap wall needs two signals.** Agda emits no bracketed name on a heap wall. It
  writes three lines to stderr and exits 251. Over the corpus `Heap exhausted` appears on
  472 lines and only 37 match `^agda: Heap exhausted;`.
- **Fact 4 reads untracked files.** `git diff` cannot see an untracked file, and
  `scripts/measure/check-timing.py:195` records that a brand-new master evaded that gate.
- **One caliber PER TIER, and never a literal at the call site (A14, A15).**
  `scripts/measure/check-timing.py:232` runs a bare `agda` under a bare `-M8g` and stashes
  the `.agdai` to force a COLD run. A cross-caliber comparison is worse than no
  comparison, so every second comes from `run_agda()`, every record carries `caliber` and
  `tier`, and two measurements are compared only inside one tier.
- **The process count includes THIS run (A14, and the defect it repairs).** MEASURED
  2026-08-17: `slots()` returned the launcher's holder count alone, which is 0 for a solo
  acceptance run, while `matches()` admits a seconds key only when `concurrency == 1`. So
  every `seconds_min` and `seconds_max` key was unmatchable and fact 5 routed nothing.
  The count is the number of Agda processes live DURING the measurement, and this run's
  own process is one of them.

WHAT THIS MODULE DOES NOT DO. It measures. It never tests a conjunct and it never routes.
`run_agda()` returns Agda's own `rc` and `agda_class`; section 5.4's acceptance runner
folds them into facts 1 and 2, and only there.

Facts 1 and 2 belong to the acceptance runner (amendment A5). Fact 3 is the witness meter
of `scripts/pod/witness.py`. This module holds facts 4, 5 and 6, the Agda process, the
error class map and the verification target rule of section 4.3.2.
"""

from __future__ import annotations

import importlib.util
import os
import re
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

ROOT = find_root(__file__)
EVERYTHING = "src/Everything.lagda.md"

ERR = re.compile(r"(?:^(?P<file>[^\s:]+):(?P<line>\d+)[.,]\d+[^\n]*?)?"
                 r"error: \[(?P<cls>[A-Za-z.]+)\]", re.M)
HEAP = re.compile(r"^agda: Heap exhausted;", re.M)
SAFE = re.compile(r"^\{-#\s+OPTIONS\b[^#]*--safe", re.M)

# R13, AMENDED BY A14 and A15. ONE NAMED CONSTANT PER TIER, and no call site writes a
# heap literal: A14 restores C-12's two tiers, so a HEAVY task must be able to ask for its
# own caliber without an edit here. The numbers are `dev/pod/heads.toml [tiers.*] heap`,
# which is their ONE owner (`scripts/pod/heads.py`); this module is a READER, and
# `test_pod_facts.py` fails when the two drift apart.
CAP_WIDE = "-A64m -I0 -M8g"      # A14 WIDE: four concurrent Agda writers
CAP_HEAVY = "-A64m -I0 -M12g"    # A14 HEAVY: two concurrent Agda writers
CAP_TREE = "-A64m -I0 -M16g"     # A15: a WHOLE-TREE `make check`, C-12's orchestrator
                                 # caliber, because that run holds the machine alone. No
                                 # caller in this module runs one; the constant is the
                                 # named home, so the next caller copies no literal.
CALIBER = {"wide": CAP_WIDE, "heavy": CAP_HEAVY, "tree": CAP_TREE}
TASK_TIERS = ("wide", "heavy")   # the two tiers a TASK may declare, A14. `tree` is not
                                 # one of them: it belongs to a run that holds the machine
CAP = CAP_WIDE                   # A15: a PER-TASK acceptance run uses the worker's own
                                 # caliber, so an acceptance measurement compares directly
                                 # with the run record beside it. Read by `accept.VACUOUS`.
DEFAULT_TIER = "wide"

CLASS = {"TerminationIssue": "termination",
         "UnequalSorts": "universe_level", "UnequalLevel": "universe_level",
         "UnsolvedMetaVariables": "unsolved_meta",
         "UnsolvedInteractionMetas": "unsolved_meta",
         "UnsolvedConstraints": "unsolved_meta",
         "MetaCannotDependOn": "unsolved_meta"}

# The eleven classes of fact 2, in snake case. Six come from Agda through conjunct 1.
# Five come from the acceptance runner's other conjuncts and are exact by construction,
# because the runner reads its own checker's exit code. A green run carries None.
AGDA_CLASSES = ("termination", "universe_level", "unsolved_meta", "heap_wall",
                "timeout", "other")
RUNNER_CLASSES = ("obligations_up", "closure_open", "unbound_hyp", "spec_surface", "lint")
ERROR_CLASSES = AGDA_CLASSES + RUNNER_CLASSES


def classify(rc, names, heap, timed_out):
    """Fact 2 from one Agda run. Three parser rules, each disclosed as a choice.

    A non-zero exit with an empty name list is `other`, the shape a missing input file
    makes. The class is the FIRST name in output order, which is Agda's print order and
    not a judgement. `universe_level` is exactly {UnequalSorts, UnequalLevel}, and gap M1
    carries the cost: `UnequalTerms` also hides universe failures and stays in `other`.
    """
    if timed_out:
        return "timeout"
    if heap:
        return "heap_wall"
    if rc == 0:
        return None                            # a green run has no class
    if not names:
        return "other"                         # the shape a missing file makes
    return CLASS.get(names[0], "other")        # FIRST name in output order


def _as_text(raw) -> str:
    """Partial output from a killed child, whatever `subprocess` hands back.

    THE EARLIER REASON WRITTEN HERE WAS FALSE AND IS WITHDRAWN. It claimed that `text=True`
    makes `TimeoutExpired.stdout` a `str`, so the design's
    `(e.stdout or b"").decode("utf8", "replace")` raised `AttributeError` on every
    deadline. MEASURED 2026-08-18 on this machine, CPython 3.11.15 on darwin: a child
    killed by `subprocess.run(..., text=True, timeout=0.7)` gives `e.stdout` as `bytes`
    (`b'half'`) and `e.stderr` as `None`. So `.decode` does NOT raise there.

    WHAT IS REALLY WRONG WITH THE DESIGN'S LINE, and it is one defect, not two.
    `(e.stdout or b"")` reads STDOUT ALONE and drops `e.stderr`, which is where Agda
    writes the heap wall. Fact 6 then reads a heap wall out of an empty string.
    `run_agda()` below joins both halves through this helper.

    THE `str` BRANCH IS DEFENSIVE AND UNMEASURED, and it is one `isinstance` call:
    `subprocess` documents no type for a killed child's partial output, and the `None`
    branch above is measured.
    """
    if raw is None:
        return ""
    if isinstance(raw, bytes):
        return raw.decode("utf8", "replace")
    return str(raw)


class AgdaStartError(RuntimeError):
    """The `agda` process could not be STARTED, so no fact was measured.

    IT IS NOT A TASK FACT AND IT IS NEVER RECORDED AS ONE. A missing `agda` binary, or a
    kernel refusal to fork, says nothing about the task's proof. Giving it an exit code
    here would write a measurement nothing measured, so this module refuses instead and the
    two command lines that call it (`accept.py`, `witness.py`) print the message and exit 1.
    """


def _head_text(root, target, n=4000):
    """The first `n` characters of the target, and the reason it could not be read.

    THE READ SERVES ONE PURPOSE: the `--safe` sniff. An unreadable target is NOT a crash
    here and it is not a guessed fact either. MEASURED 2026-08-18: `agda` over a path that
    does not exist exits 42 and prints no bracketed name, and `classify()` already calls
    that shape `other`. So the honest measurement is AGDA'S OWN, and the recorder starts
    it. Before this fix `Path(root, target).read_text()` raised `FileNotFoundError` inside
    the one place the POD starts Agda: a probe deleted or renamed inside the task's own
    scope still appears in `git status`, reached `run_agda()`, and stopped the loop with a
    traceback that nobody was watching.
    """
    try:
        return Path(root, target).read_text("utf8", "replace")[:n], None
    except OSError as exc:
        return "", f"{type(exc).__name__}: {exc}"


def caliber_of(tier):
    """The heap caliber of ONE tier, or a refusal. A15, and no literal at a call site.

    An unknown tier is a REFUSAL and never a fallback to the WIDE caliber: a HEAVY task
    silently run at `-M8g` records a number that reads as comparable and is not.
    """
    try:
        return CALIBER[tier]
    except (KeyError, TypeError):
        raise ValueError(f"unknown Agda tier {tier!r}: pick one of "
                         f"{', '.join(sorted(CALIBER))} (A14, A15)") from None


def run_agda(target, root, deadline_s, slots, include=(), tier=DEFAULT_TIER):
    """Start Agda ONCE, over ONE target, and read the process object.

    It never reads a transcript. `rc` and `agda_class` are AGDA's, not the record's.
    `include` carries `--include-path` terms; the witness meter of section 4.7.3 needs
    three of them, and conjunct 1 needs none because `bedrock.agda-lib` reads
    `include: src agents/tasks` and the POD runs with `cwd` at the repository root.

    `tier` picks the caliber, A14 and A15. The default is WIDE, which is the per-task
    acceptance caliber; a HEAVY task passes `tier="heavy"` and gets `-M12g` with no edit
    here. The record carries BOTH `caliber` and `tier`, because A14 rules that two
    measurements are compared only inside one tier.

    `slots` is the Agda process count DURING this run, counting this run's own process.
    It is recorded and never interpreted here: `matches()` refuses a seconds key against a
    record whose `concurrency` is not 1, because a contended cold gate measured 150.09 s
    against 133.69 s.

    IT RAISES ONLY `AgdaStartError`, and only when the process could not start at all. An
    unreadable target is not that case: see `_head_text()`.
    """
    head, unreadable = _head_text(root, target)                     # absolute wins
    argv = (["agda"] + ["--include-path=" + str(p) for p in include]
            + (["--safe"] if SAFE.search(head) else []) + [str(target)])
    env = dict(os.environ, GHCRTS=caliber_of(tier))
    start = time.monotonic()
    try:
        # M2: `which timeout gtimeout` returns nothing on this machine and Agda emits no
        # timeout error and no timeout exit code, so the POD owns the deadline.
        p = subprocess.run(argv, cwd=root, env=env, capture_output=True,
                           text=True, timeout=deadline_s, start_new_session=True)
        rc, out, timed_out = p.returncode, (p.stdout + p.stderr), False
    except subprocess.TimeoutExpired as e:
        rc, out, timed_out = None, _as_text(e.stdout) + _as_text(e.stderr), True
    except OSError as exc:                     # no `agda` on PATH, or no fork
        raise AgdaStartError(f"agda could not start over {target}: {exc}") from exc
    seconds = time.monotonic() - start
    names = [m.group("cls") for m in ERR.finditer(out)]
    heap = rc == 251 or bool(HEAP.search(out))
    return {"rc": rc, "agda_class": classify(rc, names, heap, timed_out),
            "seconds": round(seconds, 2), "heap_wall": heap, "out": out,
            "caliber": caliber_of(tier), "tier": tier,
            "safe": "--safe" in argv, "concurrency": slots,
            "target_unreadable": unreadable,   # provenance: why no `--safe` sniff ran
            "error_names_all": names}          # provenance, NOT matchable


_LAUNCHER = []


def launcher():
    """The dispatch launcher module, or None. It owns the registry and the write scope.

    ONE HOME IS READ, `scripts/pod/launcher.py`. The list held three candidates until
    2026-08-18. The other two are gone and neither can come back by accident: cutover
    step 4 kept the `launcher.py` name and never wrote `scripts/pod/dispatch.py`, and the
    same cutover deleted the pre-cutover skill copy at
    `.claude/skills/codex-dispatch/dispatch.py`. A fallback that can never fire documents
    a file that does not exist, so it is removed rather than kept. The module is loaded by
    PATH and never by name, because this call must not depend on `sys.path`.
    """
    if _LAUNCHER:
        return _LAUNCHER[0]
    mod = None
    for cand in (ROOT / "scripts" / "pod" / "launcher.py",):
        if not cand.is_file():
            continue
        spec = importlib.util.spec_from_file_location("pod_launcher", cand)
        mod = importlib.util.module_from_spec(spec)
        try:
            spec.loader.exec_module(mod)
        except Exception:                      # a half-moved launcher must not crash the
            mod = None                         # recorder; the caller reads None loudly
            continue
        break
    _LAUNCHER.append(mod)
    return mod


def slots(own=1):
    """The Agda process count DURING a run, counting this run's OWN process.

    THE INVERTED READING THIS REPLACES MADE FACT 5 UNMATCHABLE, and it was MEASURED on
    2026-08-17. The old body returned `len(agda_holders(load()))`, the launcher's count of
    OTHER live dispatches holding an Agda slot, which is 0 when the POD runs an acceptance
    alone. `matches()` at `scripts/pod/table.py:507` admits a seconds key only when
    `rec["concurrency"] == 1`, so a solo run recorded 0, no `seconds_min` or `seconds_max`
    key could ever match, and every branch keyed on fact 5 was dead.

    `own` is how many processes THIS caller is about to start: 1 for a real Agda run, and
    0 for a measurement point that starts none. Section 4.3.2 case 4 is the only 0 today:
    a report-only return runs no Agda, so its record must NOT read as a solo measurement
    and must not admit a seconds key against 0.0 s that nothing measured.

    It returns None when no launcher is readable. NO FACT IS EVER GUESSED: a record that
    states no process count carries `null`, and `matches()` then refuses every seconds
    key against it, which is the safe direction.
    """
    mod = launcher()
    if mod is None:
        return None
    return len(mod.agda_holders(mod.load())) + own


def write_paths(brief):
    """The repository paths a brief ORDERS its agent to write, from the launcher.

    One parser, one home. The launcher's `write_paths()` drops the lines that FORBID a
    write before it reads the ones that grant one, and a second implementation here
    would let the two disagree about what a task's territory is.
    """
    mod = launcher()
    if mod is None or brief is None:
        return set()
    return mod.write_paths(Path(brief))


def _status_paths(root):
    """Every changed path, from ONE snapshot at exit.

    `--untracked-files=all` is required: `git diff` cannot see an untracked file. Ignored
    paths do not appear, so `.pod-state/witness/` is invisible here by construction.
    """
    out = subprocess.run(["git", "status", "--porcelain", "--untracked-files=all"],
                         cwd=root, capture_output=True, text=True).stdout
    paths = []
    for line in out.split("\n"):
        if len(line) < 4:
            continue
        entry = line[3:]
        if " -> " in entry:                    # a rename reports old -> new
            entry = entry.split(" -> ", 1)[1]
        entry = entry.strip()
        if entry.startswith('"') and entry.endswith('"'):
            entry = entry[1:-1]                # core.quotepath quotes a non-ASCII name
        if entry:
            paths.append(entry)
    return sorted(set(paths))


def changed_files_scoped(code, brief, root=None):
    """Fact 4: (in scope, foreign). ONE snapshot, taken at exit, scoped to the task.

    THE SCOPE RESTRICTION STOPS TASK A BEING GRADED ON TASK B'S WORK. In scope means a
    path inside `write_paths(brief)` or under `agents/tasks/<CODE>/`. Any other changed
    path is foreign: it stays outside `facts` and the digest counts it.

    The snapshot is CUMULATIVE and that is deliberate. The program commits only at DONE,
    so an earlier instance leaves its files dirty; on a difference of two snapshots a
    second instance that edits the same already-dirty file produces an EMPTY set, R7
    drops the return and the task parks.
    """
    root = ROOT if root is None else Path(root)
    granted = set(write_paths(brief))
    home = "agents/tasks/" + agents_tree.normalise(code) + "/"
    mine, foreign = [], []
    for p in _status_paths(root):
        (mine if (p in granted or p.startswith(home)) else foreign).append(p)
    return mine, foreign


def changed_files(t):
    """Fact 4 for one live task object, as section 5.4 calls it."""
    return changed_files_scoped(t.code, getattr(t, "brief", None))


def imported_by_everything(root=None):
    """The module names `src/Everything.lagda.md` imports, through the closure check.

    ONE parser. `scripts/pod/check-closure.py` owns the import list, because conjunct 3
    and this rule must never disagree about which master is wired.
    """
    root = ROOT if root is None else Path(root)
    path = root / "scripts" / "pod" / "check-closure.py"
    try:
        spec = importlib.util.spec_from_file_location("pod_check_closure", path)
        mod = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(mod)
        return mod.imported_modules()
    except (OSError, ImportError, AttributeError) as exc:
        # A DEGRADATION IN THE STRICT DIRECTION, and it is announced. With no import list
        # every changed master reads as NEW, so `verification_target()` runs each one
        # alone AND `Everything` after it: strictly more Agda, never less. The alternative,
        # raising, stops the whole loop over a checker this run does not need.
        print(f"facts: cannot read {path} ({exc}); every changed master will run alone "
              f"as well as through Everything", file=sys.stderr)
        return set()


def verification_target(ch, code, root=None):
    """Section 4.3.2: which run is the verification run. FOUR cases, and they partition.

    1. One `src/` master or more changed. The target is `src/Everything.lagda.md`, which
       imports 98 masters, so one run covers the changed masters AND every consumer. A
       NEW master that `Everything` does not import yet is the one exception, and it runs
       alone first.
    2. No master and one probe or more under `agents/tasks/<CODE>/`. Those files are the
       targets, in path order.
    3. `ch` is empty. There is no target and R7 drops the return. The caller tests `ch`,
       because this function cannot tell case 3 from case 4 by its result.
    4. Neither, and `ch` is not empty. A report-only return is the common shape. The list
       is empty, no Agda process starts, and conjunct 1 HOLDS VACUOUSLY.

    A TARGET THAT NO LONGER EXISTS IS DROPPED, and only the target list is affected: the
    path stays in fact 4, where a `changed_files_any` key still routes on it. `git status`
    reports a DELETED path and reports a RENAME as a delete plus an untracked add, so
    without this filter a task that renames its own probe hands Agda a file that is gone.
    Agda then exits 42 with no bracketed name, conjunct 1 goes red, and the task is
    punished for legitimate work until `attempt_max` parks it. `src/Everything.lagda.md`
    is NEVER dropped: a task that deletes the catalog must go red, and it does.
    """
    root = ROOT if root is None else Path(root)
    masters = [p for p in ch if p.startswith("src/") and p.endswith(".lagda.md")]
    if masters:
        wired = imported_by_everything(root)
        new = [p for p in sorted(masters)
               if p != EVERYTHING
               and p[len("src/"):-len(".lagda.md")].replace("/", ".") not in wired
               and Path(root, p).is_file()]
        return new + [EVERYTHING]
    home = "agents/tasks/" + agents_tree.normalise(code) + "/"
    probes = [p for p in sorted(ch)
              if p.startswith(home) and (p.endswith(".agda") or p.endswith(".lagda.md"))
              and Path(root, p).is_file()]
    return probes
