#!/usr/bin/env python3
"""Never-commit checker: a staged file inside a LIVE agent's write territory must not enter a commit.

**THE INCIDENT THIS GATE EXISTS FOR, MEASURED.** Two directory-wide `git add -A` calls on
2026-08-13 swept a sibling agent's work in progress into the orchestrator's commit
(`dev/JOURNAL.md`, the [LJ-1.187] entry; `93b224e`, `a37e3fd`), and the retired route's C-1
([L3.2], July 2026) is the same shape one route earlier. The habit rule "commit by explicit
path" is recorded and it is unenforced. This script is the enforcement: the act is
mechanical, visible, and a gate cannot be skipped.

**WHAT A LIVE AGENT'S WRITE TERRITORY IS, and where it comes from.** The dispatch registry
(`.claude/skills/codex-dispatch/.state/registry.json`) records live agents with their brief
paths, MEASURED by [LJ-1.189]. A record's territory is derived from the record's OWN data,
never from a code-to-directory table:

  1. The task directory: the parent directory of the record's brief path. A brief at
     `agents/tasks/LJ-1-191/LJ-1.191.md` owns `agents/tasks/LJ-1-191/`, where its report
     and probes land.
  2. The write scope its brief declares: every path token in the brief's `SCOPE (write)`
     section, plus directory prefixes for tokens that end in `/`. `dispatch.py` already
     computes the same scope for its own clash refusal (`write_paths`); this script reads
     the scope WIDER, because a commit sweep is blind to the file type the clash check
     filters for: `Makefile`, `agents/tasks/...` reports, and `.claude/...` grants are all
     real territory here.

**THE ONE EXEMPTION, and it is measured, not hoped.** The orchestrator commits a task's
brief WHILE its agent is live. MEASURED 2026-08-14, three of the last five dispatches:
`4ae98f3` staged `LJ-1.186.md` 18 seconds after LJ-1.186 started, `82dd1fb` staged
`LJ-1.188.md` 52 seconds after LJ-1.188 started, and `8eb2ba0` staged all five briefs
LJ-1.190 to LJ-1.194 while all five agents were live. The brief is the one file the
orchestrator owns inside a live task directory: the agent never writes it, and committing
it changes nothing on disk. So the registry-named brief path of each LIVE record is exempt,
and nothing else in a live territory is. A report is committed POST-MORTEM: MEASURED,
LJ-1.186's final message was written at 10:03:40 and its report was committed at 10:05:13,
93 seconds after the agent had finished, so the exemption cannot hide a swept-in report.

**WHEN A RECORD COUNTS AS LIVE.** The same semantics as `dispatch.py`'s `alive()` (LT-2 and
LT-5): the pid exists per `os.kill(pid, 0)` (EPERM counts as existing), and when a start time
is recorded it must match `ps -o lstart=`. ONE DELIBERATE DIFFERENCE: a record WITHOUT a
non-empty `proc_start` is NOT counted live. Without a start time, a recycled pid cannot be
distinguished from the original process (LT-5), and an adopted-era record read as live would
invent a territory the gate must not invent. MEASURED: every record whose brief lives under
`agents/tasks/` carries a `proc_start` (0 exceptions in the registry), so the stricter rule
cannot under-fire on any live-era agent. A record with a live pid and no start time is
reported in the output, never silently ignored.

**A CORRUPT REGISTRY REFUSES, NEVER CLEARS.** A gate that cannot read its own state must
stop, not proceed as though no agent were live (the LT-12 lesson, applied in `dispatch.py`'s
`load()` and recorded there). A corrupt JSON is copied aside with a timestamp, named, and
exit status 2 is returned, so `make check` sees it and the commit is blocked loudly rather
than let through on a guess.

Exit status: 0 clean, 1 a staged/tracked file lies in a live territory, 2 usage error or
unreadable registry.
"""

from __future__ import annotations

import errno
import json
import os
import re
import subprocess
import sys
import time
from pathlib import Path

# LJ-1.291: the root is found by walking up to the repository marker, never by
# counting directories; `scripts/repo_root.py` holds the one walk. LJ-1.295:
# this script lives in a group directory under scripts/, so the SCRIPTS root,
# where `repo_root.py` and `agents_tree.py` sit flat, is found the same way,
# by walking up to `repo_root.py` itself; the group directory joins sys.path
# for siblings imported by bare name.
_HERE = Path(__file__).resolve()
sys.path.insert(0, str(_HERE.parent))
_SCRIPTS = next((p for p in _HERE.parents if (p / "repo_root.py").is_file()), None)
if _SCRIPTS is None:
    raise FileNotFoundError(
        f"no repo_root.py above {_HERE}: refusing to guess the scripts root (C-43)")
sys.path.insert(0, str(_SCRIPTS))
from repo_root import find_root  # noqa: E402

ROOT = find_root(__file__)

#: The one registry this dispatcher writes. `--registry` overrides it: the tests and any
#: future dispatcher point here, so the gate is not bolted to one JSON file (DD4).
REGISTRY = ROOT / ".claude" / "skills" / "codex-dispatch" / ".state" / "registry.json"

#: `R` IS IN THIS FILTER AND IT WAS NOT BEFORE. A staged RENAME was invisible to the probe
#: gate: MEASURED 2026-08-13 at [LJ-1.141], 257 staged renames were invisible to
#: `--diff-filter=ACM`. A rename INTO a live territory is a sweep like any other, and
#: `--name-only` reports the DESTINATION path, which is the path the rule is about.
STAGED_FILTER = "--diff-filter=ACMR"

#: The prohibition shapes a SCOPE (write) section carries. A unit that FORBIDS a write
#: grants nothing, and counting it as territory would make the gate refuse files an agent
#: was told not to touch. Same filter as `dispatch.py`'s `write_paths` ([L3.32-T249]).
PROHIBITION = re.compile(r"\bnever\b|\bread-only\b|\bdo not (write|touch)\b", re.I)

SCOPE_HEADING = re.compile(r"##\s*SCOPE\s*\(write\)(.*?)(?=\n##\s|\Z)", re.S | re.I)

#: The un-backticked path shape `dispatch.py` reads (`write_paths`), kept so a scope that
#: names `src/...` in prose is still territory.
SCOPE_PATH = re.compile(r"`?((?:src|dev|scripts|_build)/[\w./-]+\.(?:lagda\.md|agda|md|toml|py))`?")

#: Extensions that make a bare token (no slash) a file name rather than a command word.
KNOWN_SUFFIX = (".md", ".py", ".toml", ".json", ".agda", ".sh", ".txt", ".yaml", ".yml",
                ".lock", ".css", ".js", ".html")


# --------------------------------------------------------------------------- registry


def load_registry(path: Path) -> dict:
    """The registry's `dispatches` map, or a REFUSAL for a corrupt file (exit 2)."""
    if not path.exists():
        return {}
    try:
        data = json.loads(path.read_text())
    except json.JSONDecodeError as exc:
        broken = path.with_name(f"{path.name}.corrupt-{int(time.time())}")
        try:
            broken.write_text(path.read_text())
        except OSError:
            pass
        print(f"check-live-territory: REFUSING. The registry {path} is corrupt ({exc}).",
              file=sys.stderr)
        print(f"  A copy is at {broken.name}. Agents may still be running.", file=sys.stderr)
        print("  Repair the JSON, or move it aside deliberately once `pgrep -f codex` has",
              file=sys.stderr)
        print("  confirmed nothing is live. An unreadable registry is never read as empty.",
              file=sys.stderr)
        sys.exit(2)
    if not isinstance(data, dict):
        print(f"check-live-territory: REFUSING. The registry {path} is not a JSON object.",
              file=sys.stderr)
        sys.exit(2)
    d = data.get("dispatches", {})
    return d if isinstance(d, dict) else {}


def proc_start_of(pid: int) -> str | None:
    """The process start time, or None when `ps` could not be consulted at all.

    The distinction is load-bearing (dispatch.py's LT-2/LT-5, [L3.32-T119]): None means we
    cannot look, "" means ps ran and found nothing, a string is the start time.
    """
    try:
        out = subprocess.run(["ps", "-o", "lstart=", "-p", str(pid)],
                             capture_output=True, text=True)
    except OSError:
        return None
    if out.returncode not in (0, 1):
        return None
    return out.stdout.strip()


def record_live(rec: dict) -> tuple[bool, bool]:
    """(live, verifiable) for one registry record.

    live follows dispatch.py's `alive()`: the pid exists per os.kill (EPERM means it
    exists and we cannot signal it), and a recorded start time must match `ps`. A record
    WITHOUT a non-empty proc_start is (False, False): not counted live, because a
    recycled pid cannot be told from the original process (LT-5). That is the deliberate
    difference from dispatch.py, justified by MEASURED registry facts in the docstring.
    """
    try:
        pid = int(rec.get("pid", 0) or 0)
    except (TypeError, ValueError):
        return False, False
    if pid <= 0:
        return False, True
    try:
        os.kill(pid, 0)
    except ProcessLookupError:
        return False, True
    except PermissionError:
        pass                      # exists, owned by someone else
    except OSError as exc:
        if exc.errno == errno.ESRCH:
            return False, True
    started = rec.get("proc_start") or ""
    if not started:
        return False, False       # alive-looking pid, but no way to verify it is ours
    now = proc_start_of(pid)
    if now is None:
        return True, True         # ps unusable; trust os.kill, like dispatch.py LT-5
    if now == "":
        return False, True        # ps ran and found nothing: the process is gone
    return now == started, True


# --------------------------------------------------------------------------- territory


def repo_rel(p: Path) -> str | None:
    """The repo-relative POSIX path of `p`, or None when it lies outside the repo."""
    try:
        rp = p.resolve()
    except OSError:
        return None
    try:
        rel = rp.relative_to(ROOT.resolve())
    except ValueError:
        return None
    return rel.as_posix()


def scope_units(brief: Path) -> list[str]:
    """The logical units of a brief's SCOPE (write) section, prohibitions dropped.

    The unit join is dispatch.py's [L3.32-T249] fix: a wrapped prohibition puts "Never"
    on one line and its paths on the next, so per-line filtering lets the forbidden paths
    survive. A new unit starts at a blank line, a bullet or a heading.
    """
    try:
        text = brief.read_text(encoding="utf-8")
    except OSError:
        return []
    m = SCOPE_HEADING.search(text)
    if not m:
        return []
    units, cur = [], ""
    for ln in m.group(1).split("\n"):
        if not ln.strip() or re.match(r"\s*([-*+]|\d+\.|#)", ln):
            if cur:
                units.append(cur)
            cur = ln
        else:
            cur = (cur + " " + ln).strip() if cur else ln
    if cur:
        units.append(cur)
    return [u for u in units if not PROHIBITION.search(u)]


def territory_files(brief: Path) -> tuple[set[str], set[str]]:
    """(exact files, directory prefixes) a brief's write scope GRANTS, in repo terms.

    A token that ends in `/` grants its directory: `.claude/skills/<your-name>/` strips
    the placeholder and grants the prefix `.claude/skills/`, because the agent's own
    subdirectory is chosen at runtime and cannot be named in advance. A token with a
    placeholder that does not end in `/` names nothing and grants nothing: the gate
    cannot see it, exactly as `dispatch.py`'s `open_grant` cannot compare it.
    """
    files: set[str] = set()
    dirs: set[str] = set()
    for unit in scope_units(brief):
        for tok in re.findall(r"`([^`]+)`", unit):
            tok = tok.strip()
            if not tok:
                continue
            if "<" in tok:                        # a placeholder: grant the literal prefix
                head = tok[: tok.index("<")]
                if head.endswith("/") and head.strip("/"):
                    dirs.add(head)
                continue
            if tok.endswith("/"):
                if tok.strip("/"):
                    dirs.add(tok)
                continue
            if "/" in tok or tok.endswith(KNOWN_SUFFIX) or (ROOT / tok).exists():
                files.add(tok)
        for m in SCOPE_PATH.finditer(unit):       # the un-backticked dispatch.py shape
            files.add(m.group(1))
    return files, dirs


def live_territories(reg: dict) -> tuple[list[tuple[str, dict, dict]], list[tuple[str, dict]]]:
    """(live, unverifiable) records, each live record with its computed territory.

    Territory shape: {brief: {rel path}, taskdir: "agents/tasks/<CODE>/" or None,
    files: set, dirs: set}. Derived from the record's own brief path and brief content,
    never from a code-to-directory table, so any registry shape and any future
    dispatcher is served (DD4).
    """
    live, unverifiable = [], []
    for name, rec in reg.items():
        is_live, verifiable = record_live(rec)
        if not verifiable and not is_live:
            unverifiable.append((name, rec))
        if not is_live:
            continue
        brief = Path(rec.get("brief", ""))
        rel_brief = repo_rel(brief)
        terr = {"brief": {rel_brief} if rel_brief else set(),
                "taskdir": None, "files": set(), "dirs": set()}
        parent = Path(rel_brief).parent if rel_brief else None
        if parent and str(parent) not in ("", "."):
            terr["taskdir"] = parent.as_posix() + "/"
        files, dirs = territory_files(brief)
        terr["files"] = files
        terr["dirs"] = dirs
        live.append((name, rec, terr))
    return live, unverifiable


def declared_live(reg: dict) -> list[tuple[str, dict, dict]]:
    """Live agents the REGISTRY CANNOT SEE, taken from the task index's own rows.

    **THE HOLE THIS CLOSES, MEASURED 2026-08-15.** The registry above is written by
    `.claude/skills/codex-dispatch/dispatch.py`. **An in-harness dispatch passes through
    NO tool**, so under a mode whose default head is in-harness this gate is blind to
    every default-case agent, and the incident it exists for happens again with the gate
    green. It did: `[LJ-1.309]`, `[LJ-1.311]` and `[LJ-1.317]` each reported their
    in-progress report being swept into an orchestrator commit, three separate agents,
    one evening. DD17 already names this coverage inversion for the DD4 and DD18
    refusals; this is the third gate it hits and the row did not name it.

    **THE SECOND SOURCE IS THE TASK INDEX, because it is the ONE record kept for every
    dispatch whatever the head** (`dev/PLAN.md` section 11, section 6.0 rule 6: register
    BEFORE starting). A row whose verdict cell still reads `DISPATCHED`, `QUEUED` or
    `PENDING` declares a task nobody has audited, so its directory must not be staged.
    `dispatch.py status` already shouts when such a row outlives its return, so the
    record is kept honest by an alarm rather than by memory.

    **THE DIRECTORY COMES FROM THE FILESYSTEM, NEVER FROM A NAMING TABLE**, which is the
    rule the module docstring states. For each declared-live code this globs
    `agents/tasks/*/<CODE>.md` and takes the brief it finds. A code with no brief on disk
    is not yet a territory and is skipped in silence.

    A code already live in the registry is skipped here, so a herdr dispatch is reported
    once and not twice.
    """
    plan = ROOT / "dev" / "PLAN.md"
    if not plan.exists():
        return []
    seen = {n.upper() for n in reg}
    out: list[tuple[str, dict, dict]] = []
    open_words = ("DISPATCHED", "QUEUED", "PENDING")
    for line in plan.read_text(encoding="utf-8").splitlines():
        if not line.startswith("| "):
            continue
        cells = [c.strip() for c in line.split("|")]
        if len(cells) < 5:
            continue
        code, verdict = cells[1], cells[3]
        if not re.fullmatch(r"[A-Za-z0-9.\-]+", code) or code.upper() in seen:
            continue
        if not verdict.upper().startswith(open_words):
            continue
        briefs = sorted((ROOT / "agents" / "tasks").glob(f"*/{code}.md"))
        if not briefs:
            continue
        brief = briefs[0]
        rel_brief = repo_rel(brief)
        if not rel_brief:
            continue
        terr = {"brief": {rel_brief}, "taskdir": Path(rel_brief).parent.as_posix() + "/",
                "files": set(), "dirs": set()}
        files, dirs = territory_files(brief)
        terr["files"], terr["dirs"] = files, dirs
        out.append((code, {"pid": 0, "declared": True}, terr))
        seen.add(code.upper())
    return out


def in_territory(f: str, terr: dict, check_scope: bool) -> str | None:
    """The reason `f` lies in this territory, or None.

    The registry-named brief path is the ONE exemption: the orchestrator commits it while
    the agent is live, MEASURED at `4ae98f3`, `82dd1fb` and `8eb2ba0`. Nothing else in a
    live territory is exempt.

    The write-scope half is a STAGED-only concern. A scope file is almost always a
    PRE-EXISTING tracked file the agent is authorized to EDIT (a brief names `Makefile`
    or `scripts/...` that the tree already tracks), so a tracked-mode audit cannot tell
    the pre-existing file from the live edit; checking it would fire on every normal
    tree. Only the task directory is new while the agent is live, so only it survives
    into tracked mode, where a swept-in report or probe is what it catches.
    """
    if f in terr["brief"]:
        return None
    if terr["taskdir"] and f.startswith(terr["taskdir"]):
        return f"the file lies inside its task directory {terr['taskdir']}"
    if check_scope:
        if f in terr["files"]:
            return "the file is named in its brief's write scope"
        for d in terr["dirs"]:
            if f.startswith(d):
                return f"the file lies under a directory its brief grants ({d})"
    return None


# --------------------------------------------------------------------------- modes


def staged() -> list[str]:
    return subprocess.run(
        ["git", "diff", "--cached", "--name-only", STAGED_FILTER],
        cwd=ROOT, capture_output=True, text=True, check=True,
    ).stdout.split("\n")


def tracked() -> list[str]:
    return subprocess.run(
        ["git", "ls-files"], cwd=ROOT, capture_output=True, text=True, check=True
    ).stdout.split("\n")


def main(argv: list[str]) -> int:
    mode, registry = None, REGISTRY
    i = 1
    while i < len(argv):
        arg = argv[i]
        if arg in ("--staged", "--check"):
            if mode is not None:
                print(f"check-live-territory: `{arg}` and `--{mode}` are two modes; pass one.",
                      file=sys.stderr)
                return 2
            mode = arg[2:]
        elif arg == "--registry":
            i += 1
            if i >= len(argv):
                print("check-live-territory: `--registry` needs a path.", file=sys.stderr)
                return 2
            registry = Path(argv[i])
        else:
            print("check-live-territory: usage: --staged | --check [--registry PATH]",
                  file=sys.stderr)
            return 2
        i += 1
    mode = mode or "check"

    reg = load_registry(registry)
    live, unverifiable = live_territories(reg)
    # The registry sees only what `dispatch.py` launched. Everything in-harness is
    # invisible to it, so the task index supplies the rest. See `declared_live`.
    live = live + declared_live(reg)

    files = [f for f in (staged() if mode == "staged" else tracked()) if f]
    bad: list[tuple[str, str, int, str]] = []
    for f in files:
        for name, rec, terr in live:
            if (why := in_territory(f, terr, check_scope=(mode == "staged"))):
                bad.append((f, name, int(rec.get("pid", 0) or 0), why))

    if bad:
        where = "staged for commit" if mode == "staged" else "tracked in the repository"
        print(f"check-live-territory: {len(bad)} file(s) {where} inside a LIVE agent's "
              f"write territory:", file=sys.stderr)
        for f, name, pid, why in bad:
            print(f"  {f}\n      agent {name} is live (pid {pid}); {why}", file=sys.stderr)
        print("", file=sys.stderr)
        print("A staged file inside a live agent's territory is a defect with nothing left",
              file=sys.stderr)
        print("to judge: the sweep or the edit lands on work that is still in flight.",
              file=sys.stderr)
        print("", file=sys.stderr)
        if mode == "staged":
            print("Unstage them and commit the rest:", file=sys.stderr)
            print(f"    git restore --staged {' '.join(dict.fromkeys(f for f, _, _, _ in bad))}",
                  file=sys.stderr)
        print("Commit by explicit path, or wait for the agent to finish.", file=sys.stderr)
        return 1

    note = ""
    if unverifiable:
        note = (f"; {len(unverifiable)} record(s) skipped (live pid, no start time): "
                + ", ".join(n for n, _ in unverifiable))
    scope = f"{len(files)} staged" if mode == "staged" else f"{len(files)} tracked"
    print(f"check-live-territory: clean ({scope} files, {len(live)} live agent(s), no file "
          f"in a live territory{note})")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
