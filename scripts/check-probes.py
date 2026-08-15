#!/usr/bin/env python3
"""Never-commit checker: a probe under src/, and any generated file, must not enter the repository.

**THE OWNER'S RULING OF 2026-08-13 CHANGED WHAT A PROBE IS.** A probe pairs one-to-one with its
report, lives beside it in `agents/tasks/`, is tracked, and is NEVER deleted. `bedrock.agda-lib`
carries `agents/tasks` as a second Agda include root, so an agent writes the probe in its FINAL
home, runs it there, and nothing ever moves it again. That is what the root buys: write-and-run
in place, so no citation into a probe is ever rewritten a second time.

**A FINISHED PROBE IS TEXT.** Nothing typechecks it after its task closes. Its claim is true of
the tree at its date and is never re-verified, which is already true of every report in `agents/`.
A probe must typecheck only WHILE its task runs, and the agent running it is what checks it.

So this script is now ONE rule with one exemption:

- **Probes are never committed under `src/`** (`dev/LESSONS.md` D-1). On 2026-08-04 a single
  `git add -A src/` committed 13 probe files, 3,274 lines, which had to be untracked afterwards.
  **That rule is not weakened by anything here.**
- **The ONE exemption is `agents/tasks/`,** where a probe is tracked on purpose.
- **Generated files are never committed**: anything under `_build/`, the woven mono-lingual
  `.lagda.md` copies that `make gen` produces, and any `.agdai` anywhere. An interface file is a
  build output; Agda writes it into `_build/`, never beside the source. MEASURED 2026-08-13:
  `agents/tasks/ProbeLJ1141A.agdai` landed at `_build/2.8.0/agda/agents/tasks/`.

`.gitignore` already covers `src/`, which is why this script exists rather than not existing: an
ignore rule is a default, not a gate. `git add -f` walks straight past it, a pattern that does not
match a new naming shape silently stops covering it, and neither case produces any signal at all.
This script is the gate. It runs in two places:

  check-probes.py --check      every TRACKED file; this is what `make check` runs, and it
                               catches anything that got in historically or past a bypass
  check-probes.py --staged     the STAGED files only; this is what the pre-commit hook runs,
                               and it is what stops the commit before it happens

**WHAT WAS RETIRED HERE, and it is not deleted.** `[LJ-1.138]` built a probe LIFECYCLE on
2026-08-13: `--gate`, `--stale`, `--sweep`, `--index`, a live-task trigger read off
`dev/PLAN.md`, a four-verdict classifier and a 24-hour deletion floor. The owner retired all of
it the same afternoon, because a probe that is never deleted needs no rule for when to delete it.
The frozen code is `archive/scripts/check-probes-lifecycle.py` with its suite
`archive/scripts/tests/test_probe_lifecycle.py`, and `archive/scripts/README.md` records what
it got right and what would reopen it.

Exit status: 0 clean, 1 violations found, 2 usage error.
"""

from __future__ import annotations

import re
import subprocess
import sys
from pathlib import Path

# LJ-1.291: the root is found by walking up to the repository marker, never by
# counting directories; `scripts/repo_root.py` holds the one walk.
sys.path.insert(0, str(Path(__file__).resolve().parent))
from repo_root import find_root  # noqa: E402

ROOT = find_root(__file__)


#: The ONE directory where a probe may be tracked. Owner's ruling, 2026-08-13: a probe pairs
#: one-to-one with its report and lives beside it. The exemption is this prefix and nothing else,
#: so `src/` stays absolutely protected; that rule was bought on 2026-08-04 with 13 committed
#: probe files and it is not weakened here.
#:
#: It is a PREFIX, not a word: `archive/src/2026-08-07-arm-a/L/Probe.agda` is still refused, and
#: so is `agents/ProbeX.agda`, because the exemption is the tasks tree and not the word `agents`.
#: [LJ-1.142] merged the briefs into this tree, so a probe now sits beside BOTH halves of
#: its task record: the brief that ordered it and the report that reads it.
PROBE_HOME = "agents/tasks/"


def classify(path: str) -> str | None:
    """Return the rule a path breaks, or None. Matching is on shape, not on an ignore list."""
    p = Path(path)
    # An interface file is a build output and never belongs in the repository, exempt directory
    # or not. Agda writes it under _build/, so one here means somebody put it here.
    if p.suffix == ".agdai":
        return "compiled interface (a build output, never committed, not even in agents/tasks/)"
    # Probe files: the doctrine names src/Probe*.agda, but a probe is a probe wherever it is
    # written and whatever extension it carries, so match the basename shape anywhere. The
    # single exemption is agents/tasks/, the probe's home since the ruling of 2026-08-13.
    if not path.startswith(PROBE_HOME):
        if p.name.startswith("Probe") and p.suffix in {".agda", ".md"}:
            return (f"probe file outside its home (D-1, owner's ruling 2026-08-13: a probe lives "
                    f"in {PROBE_HOME} beside its report; src/ is forbidden absolutely)")
        if p.name.startswith("Probe") and p.name.endswith(".lagda.md"):
            return (f"probe file outside its home (D-1: a probe lives in {PROBE_HOME} beside "
                    f"its report)")
    # Generated: the build tree, and the woven mono-lingual copies.
    if path.startswith("_build/"):
        return "generated file under _build/ (never committed)"
    if "/woven/" in path or path.startswith("woven/"):
        return "woven mono-lingual copy (a `make gen` output, never committed)"
    return None


def tracked() -> list[str]:
    return subprocess.run(
        ["git", "ls-files"], cwd=ROOT, capture_output=True, text=True, check=True
    ).stdout.split("\n")


#: `R` IS IN THIS FILTER AND IT WAS NOT BEFORE. A staged RENAME was invisible to this gate.
#: MEASURED 2026-08-13 at [LJ-1.141]: 257 probe renames were staged, `--diff-filter=ACM`
#: reported ZERO of them, and `ACMR` reported all 254 whose names the pattern matches. The hole
#: mattered little while probes were untracked, because a probe had nothing to be renamed FROM.
#: It matters now: a tracked probe can be `git mv`-ed straight into `src/` and the pre-commit
#: hook would have passed it. `--name-only` reports the DESTINATION path for a rename, which is
#: the path the rule is about.
STAGED_FILTER = "--diff-filter=ACMR"


def staged() -> list[str]:
    return subprocess.run(
        ["git", "diff", "--cached", "--name-only", STAGED_FILTER],
        cwd=ROOT, capture_output=True, text=True, check=True,
    ).stdout.split("\n")


#: THE MISFILED-PROBE CHECK, added 2026-08-13 by the owner's ruling (B6).
#:
#: D-1's enforcement is honest and THIN: of its six rules only one, `src/` is
#: refused, had a machine. `[LJ-1.141]` priced this one at about fifteen lines
#: and named the gap rather than closing it.
#:
#: MY FIRST VERSION WAS WRONG AND THE CORPUS SAID SO IMMEDIATELY. It asked
#: whether a probe's name agrees with its directory's code, and that assumption
#: was MEASURED FALSE the same afternoon: `[LJ-1.143]` placed 55 DD25 probes on
#: evidence from eight reviews, so `ProbeDD25A.agda` sits correctly in
#: `LJ-1-27/` and its name agrees with nothing. The T-series adds a second
#: shape, `ProbeT126.agda` in `L3-32-T126/`. Naive agreement flagged about a
#: hundred correctly-filed files.
#:
#: SO THE RULE IS NARROWER, and it fires on a CONTRADICTION rather than on a
#: disagreement: a probe whose name matches a task directory that EXISTS, while
#: the probe sits in a DIFFERENT one. `ProbeLJ1120A.agda` in `LJ-1-133/` is
#: caught, because `LJ-1-120/` is a real directory it should be in. A name that
#: matches no directory says nothing and is left alone.
#:
#: THE HONEST LIMIT. It cannot see a probe whose name carries no code at all,
#: and `[LJ-1.143]` measured twelve of those. It cannot see one filed under a
#: task that is real but wrong when the name matches that wrong task. It
#: removes only the case where the tree itself holds the contradiction.
PROBE_CODE = re.compile(r"^Probe([A-Za-z]+[0-9][A-Za-z0-9]*?)[A-Z]?\.agda$", re.ASCII)


def _task_dirs() -> dict[str, str]:
    """Every task directory, keyed by its code with separators removed."""
    out = {}
    for base in (ROOT / "agents" / "tasks", ROOT / "agents" / "tasks" / "archive"):
        if not base.is_dir():
            continue
        for d in base.iterdir():
            if d.is_dir() and d.name != "archive":
                out[d.name.replace("-", "").upper()] = d.name
    return out


def misfiled(files: list[str]) -> list[tuple[str, str]]:
    dirs = _task_dirs()
    out = []
    for f in files:
        parts = f.split("/")
        if len(parts) < 3 or parts[0] != "agents" or parts[1] != "tasks":
            continue
        m = PROBE_CODE.match(parts[-1])
        if not m:
            continue
        claimed = m.group(1).upper()
        home = parts[-2].replace("-", "").upper()
        if claimed in dirs and claimed != home:
            out.append((f, f"the name matches task `{dirs[claimed]}`, which exists, "
                           f"but the file sits in `{parts[-2]}`"))
    return out


def main(argv: list[str]) -> int:
    mode = None
    for arg in argv[1:]:
        if arg in ("--staged", "--check"):
            if mode is not None:
                print(f"check-probes: `{arg}` and `--{mode}` are two modes; pass one.",
                      file=sys.stderr)
                return 2
            mode = arg[2:]
        else:
            print(__doc__, file=sys.stderr)
            return 2
    mode = mode or "check"

    files = [f for f in (staged() if mode == "staged" else tracked()) if f]
    bad = [(f, why) for f in files if (why := classify(f))] + misfiled(files)

    if bad:
        where = "staged for commit" if mode == "staged" else "tracked in the repository"
        print(f"check-probes: {len(bad)} file(s) {where} that must never be committed:",
              file=sys.stderr)
        for f, why in bad:
            print(f"  {f}\n      {why}", file=sys.stderr)
        print("", file=sys.stderr)
        if mode == "staged":
            print("Unstage them and commit the rest:", file=sys.stderr)
            print(f"    git restore --staged {' '.join(f for f, _ in bad)}", file=sys.stderr)
            print("Never use `git add -A src/` while probes are on disk; stage explicit paths.",
                  file=sys.stderr)
            print(f"A probe you MEANT to keep belongs in {PROBE_HOME}, beside its report.",
                  file=sys.stderr)
        else:
            print("Untrack them, keeping the files on disk:", file=sys.stderr)
            print(f"    git rm --cached {' '.join(f for f, _ in bad)}", file=sys.stderr)
        return 1

    scope = "staged" if mode == "staged" else f"{len(files)} tracked"
    print(f"check-probes: clean ({scope} files, no probe outside {PROBE_HOME} "
          f"and no generated file)")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
