#!/usr/bin/env python3
"""Pins the six edits section 6.2 of the POD design makes to the launcher, and the
five crash-or-injection defects an adversarial review found in them on 2026-08-17.

WHY THIS FILE EXISTS. The launcher is not new code. It is
`.claude/skills/codex-dispatch/dispatch.py`, copied to `scripts/pod/launcher.py`
and edited (AD18, amendment A2). Every edit repairs a MEASURED failure, and most
of them are invisible until a dispatch runs:

  edit 1  a `claude` kind that no map holds cannot start at all.
  edit 2  a `claude` kind fell into the pi branch and emitted
          `-- --provider deepseek --model <model>`. The claude CLI has no
          `--provider` flag.
  edit 3  a resume with no recorded effort drops to the CLI's own default, so
          the resumed pane runs at an effort nobody chose.
  edit 4  `argparse` validates a SUPPLIED value against `choices`, so
          `--harness herdr-claude` was refused before any other edit could run.
  edit 5  after section 7.1 row 21 retires `dispatch_policy.py`, the fallback
          literal decides every dispatch that omits `--harness`. The old literal
          was `herdr`, which maps to kind `codex`, so every POD dispatch would
          have started a CODEX agent on a deepseek model.
  edit 6  ten refusals are RELEASED. Without them released, `launch()` refuses
          every POD brief and edits 1 to 5 buy nothing.

THE FIVE DEFECTS THE REVIEW FOUND IN THE EDITS THEMSELVES, all now repaired and
each with a section below. THE POD RUNS UNATTENDED, so a traceback is not a
cosmetic defect: the loop stops and nobody is watching.

  R1  `AGDA_HEAP = "-M8g"` sets a heap cap and NO allocation area, so every
      number measured under it is incomparable with R13's caliber. A14 also
      needs one caliber PER TIER, and there was one literal for both.
  R2  edit 2's `effort` reached a SHELL STRING through `' '.join(model_args)`
      with no quoting. A config value ran as a command.
  R3  the generated queue waiter did `import dispatch as D`. The module is
      `launcher.py`, so every queued dispatch died on ModuleNotFoundError in a
      detached process whose log nobody reads.
  R4  `check <missing brief>` raised FileNotFoundError and `check <directory>`
      raised IsADirectoryError, both uncaught.
  R5  `run <task> <brief> --harness herdr-claude` with no `--effort` was
      ACCEPTED, and the empty string reached the pane as `--effort ""`.

WHAT THIS SUITE REFUSES TO DO. It never starts an agent, it never writes into
`agents/`, and it never touches the live registry. Every brief fixture lives in
a temporary tree, `ROOT` is patched at the module object so `validate()`
resolves the fixture's task directory there, and every launch that reaches the
spawn is caught by a fake `Popen` that returns the command instead of running it.

THE FIXTURE MUST BE ABLE TO FAIL. C-45: a test that cannot fail is not a test.
So section 6 also runs the SAME fixture through the PRISTINE dispatcher, which
must refuse it. When the pristine copy is absent, the suite says so and the
proof of edit 6 rests on the released functions being gone.

Run: .venv/bin/python scripts/tests/test_pod_launcher.py
Exit status: 0 every check passed, 1 at least one failed.
"""

from __future__ import annotations

import ast
import importlib.util
import inspect
import io
import contextlib
import os
import subprocess
import sys
import tempfile
import textwrap
import tomllib
import types
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent.parent
LAUNCHER = ROOT / "scripts" / "pod" / "launcher.py"
HEADS = ROOT / "dev" / "pod" / "heads.toml"
POD = ROOT / "scripts" / "pod" / "pod.py"
PRISTINE = ROOT / ".claude" / "skills" / "codex-dispatch" / "dispatch.py"

FAILED: list[str] = []
_LOADS = 0


def check(label: str, got, want) -> None:
    ok = got == want
    print(f"  {'ok  ' if ok else 'FAIL'} {label}: want {want} got {got}")
    if not ok:
        FAILED.append(label)


def check_true(label: str, got) -> None:
    check(label, bool(got), True)


# --------------------------------------------------------------- loading the module
#
# THE LAUNCHER IS LOADED, NEVER READ AS TEXT, wherever a behaviour can be run.
# A substring test passes on a comment, and this file is 60 percent comment.


class _Block:
    """An import hook that refuses one module name, so edit 5's last literal runs."""

    def __init__(self, name: str) -> None:
        self.name = name

    def find_module(self, fullname, path=None):      # pragma: no cover
        return None

    def find_spec(self, fullname, path=None, target=None):
        if fullname == self.name:
            raise ModuleNotFoundError(f"blocked by the test: {fullname}")
        return None


def load_launcher(policy: str = "real"):
    """Import `scripts/pod/launcher.py` under a private module name.

    `policy` selects which of edit 5's three literals the import walks:
      "real"     the machine's own dispatch_policy, whatever it says
      "empty"    a policy whose default_harness() returns "" (line 133's `or`)
      "systemexit" a policy that raises SystemExit (line 135, an unwired vendor)
      "absent"   no policy module at all (line 139, the retirement case)
    """
    global _LOADS
    _LOADS += 1
    name = f"pod_launcher_{_LOADS}"
    saved = sys.modules.pop("dispatch_policy", None)
    hook = None
    try:
        if policy == "absent":
            hook = _Block("dispatch_policy")
            sys.meta_path.insert(0, hook)
        elif policy in ("empty", "systemexit"):
            fake = types.ModuleType("dispatch_policy")
            fake.MODEL = "deepseek-v4-pro"
            fake.PI_PROVIDER = "deepseek"
            if policy == "empty":
                fake.default_harness = lambda: ""
            else:
                def _boom():
                    raise SystemExit("the vendor is not wired")
                fake.default_harness = _boom
            sys.modules["dispatch_policy"] = fake
        spec = importlib.util.spec_from_file_location(name, LAUNCHER)
        mod = importlib.util.module_from_spec(spec)
        sys.modules[name] = mod
        assert spec.loader is not None
        spec.loader.exec_module(mod)
        return mod
    finally:
        if hook is not None:
            sys.meta_path.remove(hook)
        sys.modules.pop("dispatch_policy", None)
        if saved is not None:
            sys.modules["dispatch_policy"] = saved


def load_pristine():
    """The UNEDITED dispatcher, if this machine still holds it.

    It is git-ignored, so a fresh clone has none. The suite degrades to a
    printed note rather than a failure.
    """
    if not PRISTINE.exists():
        return None
    spec = importlib.util.spec_from_file_location("pod_launcher_pristine", PRISTINE)
    mod = importlib.util.module_from_spec(spec)
    sys.modules["pod_launcher_pristine"] = mod
    assert spec.loader is not None
    spec.loader.exec_module(mod)
    return mod


def fn_ast(fn) -> ast.AST:
    return ast.parse(textwrap.dedent(inspect.getsource(fn)))


# ------------------------------------------------------------------- the fixture
#
# ONE BRIEF THAT TRIPS EVERY RELEASED REFUSAL AND SATISFIES EVERY KEPT ONE.
# It carries no `tier:` line (row 3), no mode name (row 4), no RETURN section
# (row 8), no `file:line` and no citation word (row 9), no `DD4` token and
# neither half of the DD4 sentence (row 11), and no mandatory rule code at all
# (row 10). It carries `## SCOPE (write)` (rows 5, 6, 7), `## ARCHIVE` (row 12)
# and `## LITERATURE` (row 13).

FIXTURE = """# ZZ-1.1: one deliverable obligation, GO or NO-GO

## HEAD
mathematician

## THE OBLIGATION
Show that the band ordinal admits a pairing code.

## SCOPE (write)
- `agents/tasks/ZZ-1-1/zz-1.1-report.md`

## PREMISES
The band ordinal is already delivered.

## ARCHIVE (program-generated, do not edit)
Nothing in the four archives bears on this task.

## LITERATURE (program-generated, do not edit)
Nothing in the digested mathematics bears on this task.

## BRANCHES
- GO: the code exists. Next obligation opens.
- NO-GO: the code does not exist. The route needs a new step.
"""


def write_pinned(tmp: Path, code: str = "ZZ-1-1", text: str = FIXTURE) -> Path:
    """A brief pinned at <tmp>/agents/tasks/<CODE>/<CODE>.md, which row 2 demands."""
    d = tmp / "agents" / "tasks" / code
    d.mkdir(parents=True, exist_ok=True)
    brief = d / f"{code}.md"
    brief.write_text(text, encoding="utf-8")
    return brief


def attempt(fn, *a, **kw) -> list[str]:
    """Call a defect function and always return a LIST of strings.

    A REGRESSION MUST FAIL A CHECK, NOT KILL THE SUITE. Half of what this file
    pins are traceback defects, so an unguarded call here turns one regression
    into a suite that stops before it reports the other twenty. A raise becomes
    one defect string that matches nothing, so every check over it fails and the
    run still finishes and still lists them.
    """
    try:
        out = fn(*a, **kw)
    except Exception as exc:                       # noqa: BLE001 - that is the point
        return [f"RAISED {type(exc).__name__}: {exc}"]
    return list(out)


def defects_for(mod, tmp: Path, brief: Path, sandbox="workspace-write", agda=False):
    """Run the module's own funnel with ROOT pointed at the temporary tree."""
    saved = mod.ROOT
    mod.ROOT = tmp
    try:
        return attempt(mod.launch_defects, brief, sandbox, agda)
    finally:
        mod.ROOT = saved


def sandboxed(mod, tmp: Path):
    """Point every path the module writes at a temporary tree, and undo it after.

    THE LIVE REGISTRY IS NEVER TOUCHED. `launch()` writes a record, a lock file
    and a log, and a test that wrote them into `scripts/pod/.state` would change
    the Agda slot census of a real dispatch.
    """
    keep = {k: getattr(mod, k) for k in
            ("ROOT", "STATE", "REGISTRY", "LOCKFILE", "LOGS")}
    mod.ROOT = tmp
    mod.STATE = tmp / ".state"
    mod.REGISTRY = mod.STATE / "registry.json"
    mod.LOCKFILE = mod.STATE / "registry.lock"
    mod.LOGS = mod.STATE / "logs"

    @contextlib.contextmanager
    def _restore():
        try:
            yield
        finally:
            for k, v in keep.items():
                setattr(mod, k, v)
    return _restore()


class _FakeProc:
    """A process that never existed. `launch()` reads `pid`, `poll` and `returncode`.

    IT REPORTS A CLEAN EXIT, and that is a speed decision with a reason. After the
    spawn `launch()` scrapes the log for a session id for up to 60 half-second
    ticks, breaking early only when the child has exited. A child that never exits
    costs this suite 30 seconds per launch. A clean exit breaks the loop at once
    and still walks every line after it: `dead_early` is true, `returncode` is 0,
    so the silent-death refusal correctly does NOT fire and `launch()` returns 0.
    """
    pid = 424242
    returncode = 0

    def poll(self):
        return self.returncode


def capture_launch(mod, tmp: Path, **kw):
    """Run `launch()` with the spawn faked, and return (rc, argv, stdout, stderr).

    `argv` is the command `launch()` WOULD have run. That is the only place edit
    2's quoting can be read, because the argv is built inside `launch()` and is
    never returned.
    """
    seen: dict = {}
    real_popen = mod.subprocess.Popen
    real_start = mod.proc_start

    def fake_popen(cmd, **_):
        seen["cmd"] = cmd
        return _FakeProc()

    out, err = io.StringIO(), io.StringIO()
    with sandboxed(mod, tmp):
        mod.subprocess.Popen = fake_popen
        mod.proc_start = lambda pid: "0"
        try:
            with contextlib.redirect_stdout(out), contextlib.redirect_stderr(err):
                rc = mod.launch(**kw)
        finally:
            mod.subprocess.Popen = real_popen
            mod.proc_start = real_start
    return rc, seen.get("cmd"), out.getvalue(), err.getvalue()


#: A PATH THAT HOLDS NO AGENT BINARY, and this is a safety belt rather than tidiness.
#: Every `cli()` run below is expected to be REFUSED before it launches, and a test
#: whose safety rests on the refusal it is testing starts a real agent the day that
#: refusal regresses. It happened once while this suite was being written. `bash`,
#: `ps` and `python3` live here; `herdr` and `codex` live in the user's own bin and
#: do not, so a regression fails the check instead of dispatching.
SAFE_PATH = "/usr/bin:/bin:/usr/sbin:/sbin"


def cli(*args, **kw):
    """Run the launcher as the command line does, so argparse's own exit 2 is real."""
    env = dict(os.environ, PATH=SAFE_PATH)
    return subprocess.run([sys.executable, str(LAUNCHER), *args],
                          capture_output=True, text=True, cwd=str(ROOT), env=env, **kw)


# ------------------------------------------------------------------------ the tests


def main() -> int:
    mod = load_launcher("real")
    # READ THE DEFAULT BEFORE ANY TEST MOVES IT. The R2 and R5 sections below set
    # `mod.HARNESS` on purpose, so this is the only point where the module's own
    # resolution is still visible.
    default_harness = mod.HARNESS
    tmp = Path(tempfile.mkdtemp(prefix="pod-launcher-test-"))
    heads = tomllib.loads(HEADS.read_text(encoding="utf-8"))

    print("edit 1: the herdr-claude kind reaches the driver")
    check("HERDR_KIND maps herdr-claude to the claude kind",
          mod.HERDR_KIND.get("herdr-claude"), "claude")
    check("HERDR_HARNESSES is derived, so it now holds three harnesses",
          tuple(mod.HERDR_HARNESSES), ("herdr", "herdr-pi", "herdr-claude"))
    check("the codex kind is untouched", mod.HERDR_KIND.get("herdr"), "codex")
    check("the pi kind is untouched", mod.HERDR_KIND.get("herdr-pi"), "pi")

    print("edit 2: the model_args builder has three branches, not two")
    branch = None
    for node in ast.walk(fn_ast(mod.launch)):
        if (isinstance(node, ast.If) and isinstance(node.test, ast.Compare)
                and isinstance(node.test.left, ast.Name)
                and node.test.left.id == "kind"):
            branch = node
            break
    check_true("the builder is an if statement inside launch()", branch is not None)
    if branch is not None:
        code = compile(ast.Module(body=[branch], type_ignores=[]), "<builder>", "exec")

        def run(kind, provider=None):
            ns = {"kind": kind, "model": "claude-opus-5", "effort": "max",
                  "PI_PROVIDER": "deepseek", "provider": provider}
            exec(code, ns)
            return ns["model_args"]

        # THE PROVIDER IS AN ARGUMENT, NOT A CONSTANT, since 2026-08-18. `PI_PROVIDER`
        # was a module constant reading a policy module that now lives under archive/,
        # so it was always "deepseek" and both glm-5.3 heads dispatched to the wrong
        # vendor. That failure is silent: pi warns, echoes the prompt, and exits done.
        check("a pi kind takes the provider it is GIVEN",
              run("pi", "zai")[:3], ["--", "--provider", "zai"])
        check("a pi kind falls back to the constant only when given nothing",
              run("pi")[:3], ["--", "--provider", "deepseek"])
        check("a claude kind emits --model, --effort and --permission-mode",
              run("claude"),
              ["--", "--model", "claude-opus-5", "--effort", "max",
               "--permission-mode", "auto"])
        check("a claude kind never emits --provider",
              "--provider" in run("claude"), False)
        check("the codex branch is unchanged",
              run("codex"), ["--", "-m", "claude-opus-5"])
        check("the pi branch is unchanged",
              run("pi"), ["--", "--provider", "deepseek", "--model", "claude-opus-5"])

    print("edit 3: the effort reaches the argv, the record and both callers")
    params = inspect.signature(mod.launch).parameters
    check_true("launch() takes an effort parameter", "effort" in params)
    check("its default is the empty string, and R5's refusal is what makes that "
          "safe", params["effort"].default if "effort" in params else None, "")
    rec = None
    for node in ast.walk(fn_ast(mod.launch)):
        if (isinstance(node, ast.Dict)
                and any(isinstance(k, ast.Constant) and k.value == "pid"
                        for k in node.keys if k is not None)):
            rec = node
            break
    check_true("the registry record is a dict literal in launch()", rec is not None)
    if rec is not None:
        keys = [k.value for k in rec.keys if isinstance(k, ast.Constant)]
        check("the record carries an effort key beside the model",
              ("effort" in keys and "model" in keys), True)
        val = dict(zip(keys, rec.values)).get("effort")
        check("the recorded value is the effort argument, not a literal",
              isinstance(val, ast.Name) and val.id == "effort", True)
        # A14: A RECORD CARRIES ITS TIER. Without it the mixed heap sum below
        # cannot be taken, because nothing says which budget a live holder took.
        check("the record carries the tier too, which A14 requires",
              "tier" in keys, True)
        tval = dict(zip(keys, rec.values)).get("tier")
        check("the recorded tier is the tier argument, not a literal",
              isinstance(tval, ast.Name) and tval.id == "tier", True)

    def threads(fn, kw) -> bool:
        for node in ast.walk(fn_ast(fn)):
            if (isinstance(node, ast.Call) and isinstance(node.func, ast.Name)
                    and node.func.id == "launch"
                    and any(k.arg == kw for k in node.keywords)):
                return True
        return False

    check("caller one, cmd_run, threads the effort", threads(mod.cmd_run, "effort"), True)
    check("caller two, cmd_resume, threads the effort",
          threads(mod.cmd_resume, "effort"), True)
    check("caller one threads the tier", threads(mod.cmd_run, "tier"), True)
    check("caller two recovers the tier from the record, as it does the effort",
          threads(mod.cmd_resume, "tier"), True)

    print("edit 4: argparse accepts the new harness and the new effort")
    # The brief is README.md: it EXISTS and it is NOT pinned, so the run reaches
    # the funnel and stops at row 2's refusal. A nonexistent path would stop
    # earlier and for a different reason, which R4 below checks on its own.
    r = cli("run", "zz-parse-test", "README.md", "--harness", "herdr-claude",
            "--effort", "max")
    check("a herdr-claude dispatch parses and reaches the funnel "
          "(exit 1, not argparse's exit 2)", r.returncode, 1)
    check_true("it stops at row 2's pinning refusal, which edit 6 KEEPS",
               "not pinned" in r.stderr)
    bad = cli("run", "zz", "zz.md", "--harness", "herdr-claws", "--effort", "max")
    check("an unknown harness is still an argparse error", bad.returncode, 2)
    bad_e = cli("run", "zz", "zz.md", "--effort", "ultra")
    check("an effort outside the five legal values is an argparse error",
          bad_e.returncode, 2)
    check("the five legal efforts come from heads.toml and not from a literal",
          list(mod.LEGAL_EFFORTS), heads["legal"]["efforts"])

    print("edit 5: every harness fallback literal reads herdr-claude")
    check("an empty default_harness() falls to herdr-claude",
          load_launcher("empty").HARNESS, "herdr-claude")
    check("an unwired vendor falls to herdr-claude",
          load_launcher("systemexit").HARNESS, "herdr-claude")
    absent = load_launcher("absent")
    check("a retired dispatch_policy falls to herdr-claude",
          absent.HARNESS, "herdr-claude")
    check("and the retirement is reported, never silent",
          bool(absent.POLICY_ERROR), True)
    # THE CHECK IS ON THE SYNTAX TREE, NEVER ON THE TEXT. This file is more
    # comment than code, and the comment that RECORDS the removal names the
    # symbol it removed. A substring test would read that comment as live code.
    main_ast = fn_ast(mod.main)
    check("main() no longer reads the policy's harness map",
          [n.attr for n in ast.walk(main_ast) if isinstance(n, ast.Attribute)
           and n.attr == "HARNESS_FOR_AGENT"], [])
    check("main() no longer asks the policy for a head",
          [n for n in ast.walk(main_ast) if isinstance(n, ast.Call)
           and isinstance(n.func, ast.Attribute) and n.func.attr == "head"], [])
    # THIS CHECK USED TO BE A SUBSTRING SEARCH FOR ONE SPELLING of the deleted
    # case-override block, `'"--harness" not in sys.argv'`. It could not fail:
    # any rewrite of the same logic in single quotes, or with a different
    # variable, passed it. The tree carries no spelling.
    check("main() reads no part of sys.argv, so the case-override block that "
          "rewrote a harness cannot come back in another spelling",
          [n for n in ast.walk(main_ast) if isinstance(n, ast.Attribute)
           and n.attr == "argv"], [])
    check("and the whole module never reads sys.argv either",
          [n.lineno for n in ast.walk(ast.parse(LAUNCHER.read_text(encoding="utf-8")))
           if isinstance(n, ast.Attribute) and n.attr == "argv"
           and isinstance(n.value, ast.Name) and n.value.id == "sys"], [])

    print("edit 6: the ten released refusals are gone and the seven kept ones fire")
    for name in ("switch_defects", "dd4_defects", "rule_bundle_defects",
                 "unregistered_returns", "_tree_maybe_live"):
        check(f"{name}() is removed", hasattr(mod, name), False)
    funnel = inspect.getsource(mod.launch_defects)
    check("the funnel refuses an unreadable brief first, then calls validate() "
          "and survey_defects() and nothing else",
          [n.func.id for n in ast.walk(ast.parse(textwrap.dedent(funnel)))
           if isinstance(n, ast.Call) and isinstance(n.func, ast.Name)],
          ["brief_unreadable", "validate", "survey_defects"])

    brief = write_pinned(tmp)
    check("a POD brief with no tier line, no RETURN, no file:line and no DD4 "
          "passes the whole funnel", defects_for(mod, tmp, brief), [])

    print("edit 6: the seven KEPT refusals still refuse")
    missing = tmp / "agents" / "tasks" / "ZZ-9-9" / "ZZ-9-9.md"
    saved_root, mod.ROOT = mod.ROOT, tmp
    try:
        got = attempt(mod.validate, missing, "workspace-write", False)
    finally:
        mod.ROOT = saved_root
    check_true("row 1, a missing brief is still refused by validate(), which "
               "guards its own read and never raises",
               got and "does not exist" in got[0])
    loose = tmp / "loose.md"
    loose.write_text(FIXTURE, encoding="utf-8")
    got = defects_for(mod, tmp, loose)
    check_true("row 2, an unpinned brief is still refused",
               any("not pinned" in d for d in got))
    scoped = write_pinned(tmp, "ZZ-2-2", FIXTURE.replace(
        "- `agents/tasks/ZZ-1-1/zz-1.1-report.md`", "- `src/L/Band.lagda.md`"))
    got = defects_for(mod, tmp, scoped, sandbox="read-only")
    check_true("row 5, a write order under a read-only sandbox is still refused",
               any("read-only" in d and "written deliverable" in d for d in got))
    got = defects_for(mod, tmp, brief, sandbox="read-only", agda=True)
    check_true("row 6, --agda under a read-only sandbox is still refused",
               any("agdai" in d for d in got))
    noscope = write_pinned(tmp, "ZZ-3-3",
                           FIXTURE.replace("## SCOPE (write)", "## WHERE"))
    got = defects_for(mod, tmp, noscope)
    check_true("row 7, a brief with no SCOPE (write) is still refused",
               any("SCOPE (write)" in d for d in got))
    noarch = write_pinned(tmp, "ZZ-4-4", FIXTURE.replace(
        "## ARCHIVE (program-generated, do not edit)\n"
        "Nothing in the four archives bears on this task.\n", ""))
    got = defects_for(mod, tmp, noarch)
    check_true("row 12, a brief with no ARCHIVE section is still refused",
               any("ARCHIVE" in d for d in got))
    nolit = write_pinned(tmp, "ZZ-5-5", FIXTURE.replace(
        "## LITERATURE (program-generated, do not edit)\n"
        "Nothing in the digested mathematics bears on this task.\n", ""))
    got = defects_for(mod, tmp, nolit)
    check_true("row 13, a brief with no LITERATURE section is still refused",
               any("LITERATURE" in d for d in got))

    print("edit 6: rows 15, 16 and 17, the three refusals outside the funnel")
    check("the cmd_status PLAN banner is gone",
          "NEVER REGISTERED" in inspect.getsource(mod.cmd_status), False)
    check("the wait --all refusal is gone",
          "wait --all` blocks until the SLOWEST"
          in inspect.getsource(mod.cmd_wait), False)
    gate = inspect.getsource(mod.cmd_gate_ready)
    check("gate-ready no longer reads a PLAN row",
          "_tree_maybe_live" in gate, False)
    # BOTH DIRECTIONS, because the empty-registry answer alone is 0 for a
    # function that had been deleted. The second call proves the registry is
    # still READ and still decides.
    saved_running = mod.running
    try:
        mod.running = lambda reg: {}
        check("gate-ready is green when the registry holds nobody",
              mod.cmd_gate_ready(None), 0)
        mod.running = lambda reg: {"zz-live": {"pid": 1}}
        err = io.StringIO()
        with contextlib.redirect_stderr(err):
            rc = mod.cmd_gate_ready(None)
        check("and RED when it holds one live agent, on the registry alone", rc, 1)
        check_true("and it names the agent that blocks the gate",
                   "zz-live" in err.getvalue())
    finally:
        mod.running = saved_running

    # ------------------------------------------------------------------ R1
    print("R1: one GHCRTS caliber PER TIER, and neither is the old -M8g")
    check("the WIDE caliber is R13's, with the allocation area the old literal "
          "dropped", mod.agda_heap("wide"), "-A64m -I0 -M8g")
    check("the HEAVY caliber raises only the cap", mod.agda_heap("heavy"),
          "-A64m -I0 -M12g")
    check("no caliber is the bare -M8g the review found",
          [t for t in mod.agda_tiers() if mod.agda_heap(t) == "-M8g"], [])
    check("the caliber is READ from heads.toml and is not a second literal",
          [mod.agda_heap(t) for t in ("wide", "heavy")],
          [heads["tiers"]["wide"]["heap"], heads["tiers"]["heavy"]["heap"]])
    check("A14's WIDE tier admits four concurrent Agda writers",
          mod.agda_slots("wide"), 4)
    check("A14's HEAVY tier admits two", mod.agda_slots("heavy"), 2)
    check("the loader was reachable, so no fallback literal is in play",
          mod.HEADS_ERROR, "")
    # THE MIXED SUM IS THE HALF A SLOT COUNT CANNOT SEE. Each row below sits
    # inside BOTH per-tier ceilings; only the arithmetic separates them.
    def reg_of(*tiers):
        return {"dispatches": {f"t{i}": {"agda": True, "tier": t, "pid": i}
                               for i, t in enumerate(tiers)}}

    saved_running = mod.running
    try:
        mod.running = lambda reg: reg["dispatches"]
        check("three WIDE holders leave room for a fourth: 24 + 8 = 32",
              mod.agda_heap_sum_over(reg_of("wide", "wide", "wide"), "wide"), "")
        check_true("a FIFTH would break the 32 GB cap",
                   mod.agda_heap_sum_over(
                       reg_of("wide", "wide", "wide", "wide"), "wide"))
        check("two HEAVY holders leave room for one WIDE: 24 + 8 = 32",
              mod.agda_heap_sum_over(reg_of("heavy", "heavy"), "wide"), "")
        check_true("but not for a second WIDE, which no slot ceiling notices: "
                   "four processes, 40 GB",
                   mod.agda_heap_sum_over(
                       reg_of("heavy", "heavy", "wide"), "wide"))
        check_true("and not for a third HEAVY either",
                   mod.agda_heap_sum_over(reg_of("heavy", "heavy"), "heavy"))
        check("a record written before A14 carries no tier and counts as the "
              "default tier, never as zero",
              mod.agda_heap_sum_over({"dispatches": {"old": {"agda": True}}}, "wide"),
              mod.agda_heap_sum_over(reg_of("wide"), "wide"))
    finally:
        mod.running = saved_running

    # ------------------------------------------------------------------ R2
    print("R2: the driver quotes every interpolated value, so a config value "
          "cannot run as a command")
    inject = "max; touch /tmp/pod-launcher-pwned"
    mod.HARNESS = "herdr-claude"
    rc, cmd, _, err = capture_launch(
        mod, tmp, task="ZZ-1-1", brief=brief, agda=True, sandbox="workspace-write",
        model="claude-opus-5", effort=inject, tier="wide")
    check("the launch reached the spawn", rc, 0)
    driver = (cmd or ["", "", ""])[2]
    check_true("the driver is the bash script, not the argv", "herdr agent start" in driver)
    check("the injected effort is ONE quoted shell word",
          f"--effort '{inject}'" in driver, True)
    check("and never reaches the shell unquoted, which is the injection",
          f"--effort {inject}" in driver, False)
    check("the caliber holds two spaces and is also ONE quoted word",
          "--env 'GHCRTS=-A64m -I0 -M8g'" in driver, True)
    check("an unquoted caliber would have handed -I0 and -M8g to pane split "
          "as two more arguments", "--env GHCRTS=-A64m -I0" in driver, False)
    rc, cmd, _, _ = capture_launch(
        mod, tmp, task="ZZ-2-2", brief=brief, agda=True, sandbox="workspace-write",
        model="claude-opus-5", effort="max", tier="heavy")
    check("a HEAVY dispatch gets the HEAVY caliber on its pane", rc, 0)
    check_true("and it is the -M12g one",
               "--env 'GHCRTS=-A64m -I0 -M12g'" in (cmd or ["", "", ""])[2])

    # ------------------------------------------------------------------ R3
    print("R3: the generated queue waiter imports THIS module, and it runs")
    seen: dict = {}
    real_popen = mod.subprocess.Popen
    with sandboxed(mod, tmp):
        mod.subprocess.Popen = lambda c, **kw: (seen.__setitem__("s", c[2]), _FakeProc())[1]
        try:
            out = io.StringIO()
            with contextlib.redirect_stdout(out):
                mod.cmd_queue(types.SimpleNamespace(
                    task="ZZ-1-1", brief=str(brief), agda=True,
                    sandbox="workspace-write", model="claude-opus-5", effort="max",
                    tier="heavy", harness="herdr-claude", adversarial=False,
                    fallback=False, allow_model=False, resume_of=None, note=None))
        finally:
            mod.subprocess.Popen = real_popen
    waiter = seen.get("s", "")
    check("the waiter imports launcher, the name this module actually has",
          "import launcher as D" in waiter, True)
    check("and never the name it had in the skill directory",
          "import dispatch as D" in waiter, False)
    check("the waiter carries the effort across the process boundary",
          "effort='max'" in waiter, True)
    check("and the tier with it, so the queued run gets the caliber it queued for",
          "tier='heavy'" in waiter, True)
    check("it waits on the TIER's slot count, not on one global number",
          "D.agda_slots('heavy')" in waiter, True)
    check("and on the mixed heap sum, which a slot count cannot see",
          "D.agda_heap_sum_over(reg, 'heavy')" in waiter, True)
    # AND IT IS EXECUTED, because an import error is exactly what the review
    # found: a substring check reads the same as a comment, and the whole reason
    # this defect survived is that nothing ever ran the generated script.
    #
    # THE RUN CANNOT DISPATCH, BY CONSTRUCTION AND NOT BY LUCK. The first draft
    # of this check let the waiter reach the real `launch()` and relied on the
    # effort refusal to stop it. A mutation run with that refusal removed then
    # tried to start a live agent. So `D.launch` is replaced in the child before
    # the waiter reaches it, and the stub PRINTS what it was called with, which
    # is a stronger check as well as a safe one. The wait loop is also short
    # circuited: with a real Agda agent live it would otherwise sleep for ever.
    stub = ("import launcher as D\n"
            "D.agda_holders = lambda reg: {}\n"
            "D.agda_heap_sum_over = lambda reg, tier: ''\n"
            "D.territory_in_flight = lambda brief, task: None\n"
            "D.launch = lambda *a, **k: print('LAUNCH effort=%r tier=%r harness=%r'\n"
            "                                 % (k.get('effort'), k.get('tier'),"
            " D.HARNESS)) or 0\n")
    safe = waiter.replace("import launcher as D\n", stub)
    check("the stub replaced the import line, so the child cannot dispatch",
          safe != waiter, True)
    ran = subprocess.run([sys.executable, "-c", safe], capture_output=True,
                         text=True, cwd=str(ROOT), timeout=180,
                         env=dict(os.environ, PATH=SAFE_PATH))
    check("the waiter runs to completion under a real interpreter", ran.returncode, 0)
    check("no ModuleNotFoundError, which is exactly what the old line raised",
          "ModuleNotFoundError" in ran.stderr, False)
    check_true("it reaches D.launch, which is the line after the wait loop",
               "LAUNCH " in ran.stdout)
    check_true("carrying the effort and the tier it was queued with",
               "effort='max' tier='heavy'" in ran.stdout)
    check_true("and the harness the queue pinned, not the fresh module default",
               "harness='herdr-claude'" in ran.stdout)
    check_true("and it prints the queue result the orchestrator reads",
               "QUEUE RESULT rc=0" in ran.stdout)

    # ------------------------------------------------------------------ R4
    print("R4: an unreadable brief is REFUSED, and it used to be a traceback")
    r = cli("check", "agents/tasks/ZZ-NOT-A-TASK/ZZ-NOT-A-TASK.md")
    check("a missing brief exits 1, the code this file gives a refusal",
          r.returncode, 1)
    check_true("with a message and not a FileNotFoundError",
               "does not exist" in r.stderr)
    check("and no traceback reaches the operator",
          "Traceback" in r.stderr, False)
    r = cli("check", "agents/tasks")
    check("a DIRECTORY where a brief is expected also exits 1", r.returncode, 1)
    check_true("and says it is a directory", "DIRECTORY" in r.stderr)
    check("with no IsADirectoryError", "IsADirectoryError" in r.stderr, False)
    binary = tmp / "agents" / "tasks" / "ZZ-6-6"
    binary.mkdir(parents=True, exist_ok=True)
    notutf8 = binary / "ZZ-6-6.md"
    notutf8.write_bytes(b"# brief\n\xff\xfe not utf-8\n")
    got = defects_for(mod, tmp, notutf8)
    check_true("a brief that is not UTF-8 is refused rather than decoded",
               got and "not UTF-8" in got[0])

    def funnel_result(m, path) -> str:
        s, m.ROOT = m.ROOT, tmp
        try:
            out = m.launch_defects(path, "workspace-write", False)
            return "refused" if out else "no defect"
        except FileNotFoundError:
            return "FileNotFoundError"
        except IsADirectoryError:
            return "IsADirectoryError"
        finally:
            m.ROOT = s

    check("the funnel REFUSES a missing brief", funnel_result(mod, missing), "refused")
    check("and REFUSES a directory",
          funnel_result(mod, tmp / "agents" / "tasks"), "refused")

    # ------------------------------------------------------------------ R5
    print("R5: a claude harness with no effort is refused twice, at both codes")
    r = cli("run", "zz-effort", "README.md", "--harness", "herdr-claude")
    check("the command line refuses it as a USAGE error, exit 2", r.returncode, 2)
    check_true("and says which values are legal", "low, medium, high" in r.stderr)
    check("it never reached the funnel, so no brief refusal is printed",
          "not pinned" in r.stderr, False)
    r = cli("run", "zz-effort", "README.md", "--harness", "herdr")
    check("a CODEX harness with no effort is untouched: it reaches the funnel "
          "and stops at the brief, exit 1", r.returncode, 1)
    check_true("on the pinning refusal and not on the effort",
               "not pinned" in r.stderr and "--effort" not in r.stderr)
    # THE BARE COMMAND FOLLOWS WHATEVER `default_harness()` RESOLVES TODAY, and
    # that is a live number rather than a literal: edit 5 sets only the three
    # FALLBACKS, and `dispatch_policy.py` still answers until section 7.1 row 21
    # retires it. So the check branches on the resolved kind, and both branches
    # assert something that can fail.
    r = cli("run", "zz-effort", "README.md")
    if mod.HERDR_KIND.get(default_harness) == "claude":
        check(f"the default harness resolves to {default_harness}, a claude kind, "
              f"so the bare command is refused as a usage error", r.returncode, 2)
    else:
        check(f"the default harness resolves to {default_harness}, which is not a "
              f"claude kind, so the bare command reaches the funnel instead",
              r.returncode, 1)
        check("and the effort refusal did not fire on it",
              "--effort is required" in r.stderr, False)
    check("either way, a retired dispatch_policy leaves the default at a claude "
          "kind, which is what makes the refusal load-bearing after row 21",
          mod.HERDR_KIND.get(load_launcher("absent").HARNESS), "claude")
    # THE SECOND REFUSAL, at the funnel, for a caller that never sees argparse.
    # D3: a check one entry point performs is not a check.
    mod.HARNESS = "herdr-claude"
    rc, cmd, _, err = capture_launch(
        mod, tmp, task="ZZ-1-1", brief=brief, agda=False,
        sandbox="workspace-write", model="claude-opus-5", effort="", tier="wide")
    check("launch() itself refuses an empty effort, exit 1", rc, 1)
    check("and it never spawned anything", cmd, None)
    check_true("with a message naming heads.toml as the value's home",
               "heads.toml" in err)
    mod.HARNESS = "herdr"
    rc, cmd, _, _ = capture_launch(
        mod, tmp, task="ZZ-1-1", brief=brief, agda=False,
        sandbox="workspace-write", model="deepseek-v4-pro", effort="", tier="wide")
    check("a codex launch with no effort still runs, so the refusal is scoped "
          "to the claude kind", rc, 0)
    mod.HARNESS = "herdr-claude"
    rc, cmd, _, err = capture_launch(
        mod, tmp, task="ZZ-1-1", brief=brief, agda=False,
        sandbox="workspace-write", model="claude-opus-5", effort="max", tier="nope")
    check("an unknown tier is refused rather than silently defaulted", rc, 1)
    check_true("and the message names the tiers that exist", "wide" in err)
    mod.HARNESS = default_harness              # leave the module as it was found

    # ------------------------------------------------------- the runtime state
    print("the runtime state is .pod-state/, which fact 4 and prune_logs both "
          "already assume")
    check("the registry sits under the ignored runtime directory",
          mod.STATE, ROOT / ".pod-state")
    check("and the worker transcripts sit where prune_logs() looks for them",
          mod.LOGS, ROOT / ".pod-state" / "logs")
    ignored = subprocess.run(["git", "check-ignore", "-q", ".pod-state"],
                             cwd=str(ROOT), capture_output=True)
    # WHY THIS CHECK IS NOT DECORATION. Fact 4 is `git status --porcelain
    # --untracked-files=all` at `scripts/pod/facts.py:316`. A registry file and
    # one log per dispatch written OUTSIDE an ignored path are counted as files
    # the worker changed, so the launcher would corrupt the fact the program
    # routes on. `scripts/pod/.state`, the old home, is not ignored.
    check("git ignores it, so fact 4 never counts a launcher file as a "
          "worker's change", ignored.returncode, 0)
    stale = subprocess.run(["git", "check-ignore", "-q", "scripts/pod/.state"],
                           cwd=str(ROOT), capture_output=True)
    check("and the old home was NOT ignored, which is what made the move "
          "necessary", stale.returncode, 1)

    print("the fixture can fail: the PRISTINE dispatcher refuses the same brief")
    pris = load_pristine()
    if pris is None:
        print("  note the pristine dispatcher is absent on this machine "
              "(it is git-ignored), so this comparison did not run")
    else:
        saved = pris.ROOT
        pris.ROOT = tmp
        try:
            got = pris.launch_defects(brief, "workspace-write", False)
        finally:
            pris.ROOT = saved
        check("R4 IS REPAIRED HERE AND NOWHERE ELSE: the unedited funnel still "
              "raises on the same missing brief",
              funnel_result(pris, missing), "FileNotFoundError")
        check_true("the unedited funnel refuses the POD fixture", len(got) > 0)
        check_true("it refuses on the missing tier line (row 3)",
                   any("tier:" in d for d in got))
        check_true("it refuses on the missing RETURN section (row 8)",
                   any("RETURN" in d for d in got))
        check_true("it refuses on the missing evidence standard (row 9)",
                   any("checkable evidence" in d for d in got))
        check_true("it refuses on the missing DD4 statement (row 11)",
                   any("DD4" in d for d in got))
        check("the unedited HERDR_KIND has no claude entry",
              "herdr-claude" in pris.HERDR_KIND, False)
        check("the unedited launch() takes no effort parameter",
              "effort" in inspect.signature(pris.launch).parameters, False)
        check("and the unedited caliber is the bare -M8g R13 forbids",
              getattr(pris, "AGDA_HEAP", None), "-M8g")

    print("dev/pod/heads.toml: the five heads, the limits and the two tiers")
    check("the file declares its version", heads.get("version"), 1)
    check("the five slots are exactly AD2's, AD24's and AD25's",
          sorted(heads["heads"]),
          ["coder", "coder_adversarial", "maintainer", "mathematician",
           "mathematician_adversarial"])
    # THE EMPTY STRING JOINED THEM on 2026-08-18, when the owner ruled the two coder
    # slots onto `pi` vendors. `--effort` is a claude CLI flag and a pi head has no
    # equivalent, so a pi row carries "" and the launcher omits the flag.
    check("legal.efforts is the claude CLI's five values plus the pi empty string",
          heads["legal"]["efforts"], ["", "low", "medium", "high", "xhigh", "max"])
    check("legal.models carries the six VERIFIED claude strings plus the two pi models",
          heads["legal"]["models"],
          ["claude-opus-5", "claude-fable-5", "claude-sonnet-5",
           "opus", "fable", "sonnet", "glm-5.3", "deepseek-v4-pro"])
    # **THE TWO PI MODELS ARE NOT READ-BACK VERIFIED.** [LJ-4-0] ran `claude -p` twice
    # per claude string; no equivalent ran for these two, so the first dispatch on
    # either is also its verification. The provider map is what makes them reachable.
    check("each pi model names its provider, which is NOT its family name",
          heads["legal"]["pi_provider"],
          {"glm-5.3": "zai", "deepseek-v4-pro": "deepseek"})
    check("claude-haiku-5 is excluded, because the client refuses it",
          "claude-haiku-5" in heads["legal"]["models"], False)
    check("a DATE SUFFIX is excluded too, and it is the harder case: [LJ-4-0] "
          "measured that it passes the client and fails at the API with a 404",
          [m for m in heads["legal"]["models"] if m[-1].isdigit() and len(m) > 16],
          [])
    # THE OWNER'S RULING OF 2026-08-18 replaced A12's four siblings and kept its own row.
    check("A12's maintainer head is claude-opus-5 at effort high",
          (heads["heads"]["maintainer"]["model"],
           heads["heads"]["maintainer"]["effort"]), ("claude-opus-5", "high"))
    for slot, row in heads["heads"].items():
        check(f"{slot} names a legal model", row["model"] in heads["legal"]["models"], True)
        check(f"{slot} names a legal effort", row["effort"] in heads["legal"]["efforts"], True)
        check(f"{slot} runs on a harness the launcher serves",
              row["harness"] in ("herdr-claude", "herdr-pi"), True)
        check(f"{slot}: a pi head carries no effort and a claude head carries one",
              (row["harness"] == "herdr-pi") == (row["effort"] == ""), True)
        # A CLAUDE HEAD NEVER READS THIS COLUMN: `--permission-mode` is hardcoded to
        # `auto` for the `claude` kind at `scripts/pod/launcher.py:1353`. The value is
        # still pinned here because codex reads it as `-s` and `validate()` refuses a
        # `read-only` brief that orders a write.
        check(f"{slot} pins a sandbox codex can take and validate() will not refuse",
              row["sandbox"], "acceptEdits")
        check(f"{slot} names a harness the launcher accepts",
              row["harness"] in mod.HERDR_HARNESSES, True)
        check(f"{slot} names an effort the launcher's argparse accepts",
              row["effort"] in mod.LEGAL_EFFORTS, True)
    limits = heads["limits"]
    # `parked_max` joined on 2026-08-19, owner's ruling: rule (d)'s threshold moved from a
    # hardcoded 3 to a named limit, so the number has one home and the tests read it.
    check("the limits block holds all six keys section 6.1 names",
          sorted(limits),
          ["agda_deadline_s", "attempt_max", "exclusive_max_load1",
           "parked_max", "tick_seconds", "worker_deadline_s"])
    check_true("the Agda deadline clears the widest measured acceptance run, "
               "300.81 s at [LJ-4-0] gap B3", limits["agda_deadline_s"] > 300.81)
    check("A14's WIDE tier admits four concurrent Agda writers",
          heads["tiers"]["wide"]["slots"], 4)
    check("A14's HEAVY tier admits two", heads["tiers"]["heavy"]["slots"], 2)
    check("the WIDE caliber is R13's, and the heap cap does not move",
          heads["tiers"]["wide"]["heap"], "-A64m -I0 -M8g")
    check("the HEAVY caliber raises only the cap",
          heads["tiers"]["heavy"]["heap"], "-A64m -I0 -M12g")
    check("the mixed worst case is held at or under 32 GB",
          heads["tiers"]["shared"]["max_heap_sum_gb"], 32)
    check("slots three and four need system free memory above 25 percent",
          heads["tiers"]["shared"]["free_memory_pct_for_extra"], 25)
    check("C-12's per-process backstop returns with A13",
          heads["tiers"]["shared"]["per_process_backstop_gb"], 14)
    check("and C-12's system free floor with it",
          heads["tiers"]["shared"]["system_free_floor_pct"], 8)
    # THIS CHECK USED TO BE `4*8 + 2*12 > 32`, which is 64 > 32 and cannot fail
    # once the four numbers above are pinned. It read as a safety property and
    # asserted a tautology. The three below are the property A14 actually states,
    # and each one fails on a different bad edit of this file.
    cap = heads["tiers"]["shared"]["max_heap_sum_gb"]
    wide_gb, heavy_gb = 8, 12
    check("a FULL wide tier fits the cap exactly, which is why four is the "
          "number: 4 x 8 = 32",
          heads["tiers"]["wide"]["slots"] * wide_gb <= cap, True)
    check("a FULL heavy tier fits under it: 2 x 12 = 24",
          heads["tiers"]["heavy"]["slots"] * heavy_gb <= cap, True)
    check("and the two tiers full TOGETHER do not fit, which is why admits() "
          "must do arithmetic and not count slots",
          heads["tiers"]["wide"]["slots"] * wide_gb
          + heads["tiers"]["heavy"]["slots"] * heavy_gb > cap, True)
    check("the tier calibers state the gigabyte figures this arithmetic uses",
          (f"-M{wide_gb}g" in heads["tiers"]["wide"]["heap"],
           f"-M{heavy_gb}g" in heads["tiers"]["heavy"]["heap"]), (True, True))

    print("heads.toml names its loader and its read-back executor, and both exist")
    # THE FILE MAKES TWO CLAIMS ABOUT OTHER FILES. A comment that names a file
    # nobody wrote is worse than no comment. Neither module is imported here:
    # the check is that the named symbol EXISTS where the comment says. The
    # DIRECTION of the read-back rule is that module's own suite to prove.
    loader = ROOT / "scripts" / "pod" / "heads.py"
    check("the loader named in the header exists", loader.is_file(), True)
    if loader.is_file():
        names = [n.name for n in ast.walk(ast.parse(loader.read_text(encoding="utf-8")))
                 if isinstance(n, ast.FunctionDef)]
        check("and it defines load_heads(), which the launcher calls",
              "load_heads" in names, True)
    check("the read-back executor named in the model comment exists",
          POD.is_file(), True)
    if POD.is_file():
        names = [n.name for n in ast.walk(ast.parse(POD.read_text(encoding="utf-8")))
                 if isinstance(n, ast.FunctionDef)]
        check("and it defines model_readback_ok(), so the rule is built and not "
              "only documented", "model_readback_ok" in names, True)
    # THE LOADER REFUSES WHAT heads.toml PROMISES IT REFUSES. The launcher's own
    # tier numbers rest on this, so the wiring is checked here even though the
    # loader belongs to another module.
    if mod.HEADS_MOD is not None:
        doctored = tmp / "bad-heads.toml"
        good = HEADS.read_text(encoding="utf-8")
        doctored.write_text(
            good.replace('mathematician             = { model = "claude-opus-5"',
                         'mathematician             = { model = "claude-haiku-5"'),
            encoding="utf-8")
        try:
            mod.HEADS_MOD.load_heads(path=doctored, cache=False)
            got = "accepted"
        except mod.HEADS_MOD.HeadsError as exc:
            got = "refused" if "legal.models" in str(exc) else f"refused: {exc}"
        check("a model outside legal.models is refused by the loader the "
              "launcher uses", got, "refused")
        doctored.write_text(good.replace('effort = "max"', 'effort = "ultra"', 1),
                            encoding="utf-8")
        try:
            mod.HEADS_MOD.load_heads(path=doctored, cache=False)
            got = "accepted"
        except mod.HEADS_MOD.HeadsError as exc:
            got = "refused" if "legal.efforts" in str(exc) else f"refused: {exc}"
        check("and an effort outside legal.efforts", got, "refused")
    else:                                         # pragma: no cover
        print("  note the heads loader did not import, so its refusals were "
              "not exercised")

    print("the pane layout: right for a new column, down once to fill it")

    _ly = (ROOT / "scripts" / "pod" / "launcher.py").read_text(encoding="utf-8")
    # SCOPE EVERY CHECK TO THE SPLIT BLOCK. `--direction right` also appears in the
    # file's own prose 56 KB earlier, so a whole-file index comparison compares a
    # comment with a call and reads the order backwards.
    _blk = _ly[_ly.index("COLF="):_ly.index("HERDR pane=$PANE")]
    check("a DOWN split exists, and it splits the recorded open column",
          "--direction down" in _blk and "$OPEN" in _blk, True)
    check("a RIGHT split exists, and its usual target is the RIGHTMOST column",
          "--direction right" in _blk and "$FROM" in _blk, True)
    check("DOWN is tried FIRST, so a half-empty column fills before a new one opens",
          _blk.index("--direction down") < _blk.index("--direction right"), True)
    # MEASURED 2026-08-18: splitting BASE reverses the column order and halves BASE at
    # every new column. BASE survives as the fallback for the first column and for a
    # rightmost pane herdr no longer has.
    check("BASE is the FALLBACK and never the usual target",
          "FROM=" in _blk and "$BASE" in _blk, True)
    check("the rightmost column is recorded, so the grid grows left to right",
          "HERDR_RIGHT_FILE = STATE /" in _ly and "$RIGHTF" in _blk, True)
    check("the open column is CLEARED whichever way the down split went, so DOWN "
          "can never happen twice in one column",
          _blk.count("$COLF") >= 3, True)
    # EQUAL WIDTHS. A `pane split` halves its target, so columns come out 130, 65, 32,
    # 32 without this. MEASURED 2026-08-18 before and after: the cure gives 65, 65, 65,
    # 64, and six columns go from a 16-wide fourth to 43 each.
    check("a new COLUMN is followed by the equaliser, and a down-split is not",
          "EQUALISE" in _blk
          and _blk.index("EQUALISE") > _blk.index("--direction right"), True)
    check("the equaliser can never fail a dispatch",
          "|| true" in _blk[_blk.index("EQUALISE"):], True)
    check("the column file lives under .pod-state, beside the other runtime state",
          "HERDR_COL_FILE = STATE /" in _ly, True)

    print()
    if FAILED:
        print(f"FAIL: {len(FAILED)} failing check(s)")
        for f in FAILED:
            print(f"  - {f}")
        return 1
    print("PASS: 0 failing check(s)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
