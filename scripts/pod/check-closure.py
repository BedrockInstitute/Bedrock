#!/usr/bin/env python3
"""The tree physics the POD's acceptance runner needs: closure, the archive boundary, the
empty parameterized module, and the unwired new master.

WHY THIS FILE EXISTS. `make check` typechecks EXACTLY ONE file, `src/Everything.lagda.md`,
which is what makes it a trusted single invocation. The cost is that a master nobody
imports is never typechecked at all and the gate still goes green. Measured on the tree
the day the rule was written: 123 masters, 122 imported, one gap, and that gap was a real
in-progress chapter.

WHY IT IS SPLIT OUT OF `scripts/gate/check-tree.py`
(`dev/memos/L9-pod-program-design.md` section 7.2, cutover step 7). AD13 leaves a hole. A
task writes a new master `src/L/Foo.lagda.md`, never edits `src/Everything.lagda.md`, and
passes: Agda is green on the file, the consumer set is empty, and `make check` never reads
`L.Foo`. But `scripts/measure/ledger.py:123-126` counts it, so `src/` records a net gain
from code the trophy does not depend on, and the digest prints it as progress. The check
gets three program-side homes: acceptance conjunct 3, pre-flight P16, and the digest's
orphan master count.

THE FOUR SUBCHECKS THIS FILE KEEPS, and each has a ruled disposition:

- **closure**, FAIL. Every tracked master under `src/` is in `Everything`'s import list,
  and every imported name has a master.
- **archive**, FAIL. No live master imports a module whose only home is `archive/`. The
  archive is unwired and ungated by design, so an import across the boundary drags
  unchecked code into the checked tree. This is DD13's mechanised half and the archive
  grows at the cutover. **The name `closure` runs it too**, because every caller asks for
  `closure` and this invariant would otherwise have no runner. `GROUPS` below is that
  expansion and it carries the measurement.
- **closure-new**, WARN. An UNTRACKED master that is not wired. Its author must wire it
  before committing, but it must not block anyone else. Section 4.3.2 case 1 relies on
  this signal to pick the verification target.
- **module-body**, WARN. A parameterized module header whose body is not indented deeper
  is an EMPTY module: Agda accepts it, the parameter is out of scope, and the
  declarations meant to be inside it silently are not (LESSONS C-11).

WHAT LEFT, and where each half went. `check_retiring` is RETIRED: it already returns `[]`
on every run, because `dev/ledger.toml` sets `retire_suspended`. `check_shared_cjk` moves
into `lint-prose.py` and `check_spdx` into `lint-agda.py`. `--gate-debt`, `--gate-passed`
and `LAST_GATE` are RETIRED with the batched-gate protocol they served: the acceptance
runner typechecks at every return, so no gate debt is left to count.

Usage:
  check-closure.py --check         run every invariant over the working tree
  check-closure.py --check NAME    closure, archive, closure-new or module-body.
                                   `closure` runs the whole FAIL class, which is
                                   `closure` and `archive` together
Exit status: 0 clean, 1 a FAIL-class violation, 2 usage error.
"""

from __future__ import annotations

import re
import subprocess
import sys
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
SRC = ROOT / "src"
EVERYTHING = SRC / "Everything.lagda.md"
ARCHIVE = ROOT / "archive"

FENCE = re.compile(r"```agda\n(.*?)```", re.S)


def masters() -> list[Path]:
    """The working tree, not the index: a new untracked master must not escape the audit."""
    return sorted(p for p in SRC.rglob("*.lagda.md"))


def module_of(p: Path) -> str:
    return str(p.relative_to(SRC)).removesuffix(".lagda.md").replace("/", ".")


def code_of(p: Path) -> str:
    return "\n".join(FENCE.findall(p.read_text(encoding="utf-8")))


def imported_modules() -> set[str]:
    """The module names the catalog imports. ONE parser, three readers.

    `check_closure`, `check_closure_new` and `facts.verification_target` all ask which
    masters are wired. Section 4.3.2 case 1 picks the verification target from this
    answer, so a second copy of the regex could send the acceptance run at the wrong file.
    """
    if not EVERYTHING.exists():
        return set()
    return set(re.findall(r"^import ([A-Za-z0-9_.]+)", code_of(EVERYTHING), re.M))


def _tracked_or_staged() -> set[str]:
    """Paths git knows about. An UNTRACKED master is not in the repository yet, so an
    unwired one is a warning to its author, not a reason to block someone else's commit:
    that distinction was missing and a concurrent agent's half-written new chapter blocked
    an unrelated commit twice on 2026-08-05."""
    out = set()
    for args in (["git", "ls-files"], ["git", "diff", "--cached", "--name-only"]):
        out |= set(subprocess.run(args, cwd=ROOT, capture_output=True,
                                  text=True).stdout.split("\n"))
    return {f for f in out if f}


def check_closure() -> list[str]:
    if not EVERYTHING.exists():
        return ["src/Everything.lagda.md is missing; the trusted gate has no root"]
    imported = imported_modules()
    known = _tracked_or_staged()
    bad = []
    for p in masters():
        if p == EVERYTHING:
            continue
        name = module_of(p)
        if name not in imported:
            rel = str(p.relative_to(ROOT))
            if rel not in known:
                continue  # untracked: reported by the closure-new WARN check instead
            bad.append(
                f"{rel}: module `{name}` is not in Everything's import list, "
                f"so it is NEVER TYPECHECKED and the gate still goes green. "
                f"Add `import {name}` to src/Everything.lagda.md in reading order.")
    for name in sorted(imported):
        if not (SRC / (name.replace(".", "/") + ".lagda.md")).exists():
            bad.append(f"src/Everything.lagda.md imports `{name}`, which has no master")
    return bad


def check_archive() -> list[str]:
    if not ARCHIVE.is_dir():
        return []
    archived = set()
    for p in ARCHIVE.rglob("*.lagda.md"):
        m = re.search(r"^module\s+([A-Za-z0-9_.]+)", code_of(p), re.M)
        if m:
            archived.add(m.group(1))
    live = {module_of(p) for p in masters()}
    # A module re-created under src/ is a revival and is legal (archived D20 allows copy-out).
    only_archived = archived - live
    bad = []
    for p in masters():
        for name in re.findall(r"^\s*(?:open )?import ([A-Za-z0-9_.]+)", code_of(p), re.M):
            if name in only_archived:
                bad.append(f"{p.relative_to(ROOT)} imports `{name}`, which lives only in "
                           f"archive/. Archived D20: nothing imports across the boundary; "
                           f"copy it out into src/ if it is genuinely needed again")
    return bad


def check_closure_new() -> list[str]:
    """WARN: an UNTRACKED master that is not wired. Its author must wire it before
    committing, but it must not block anyone else."""
    if not EVERYTHING.exists():
        return []
    imported = imported_modules()
    known = _tracked_or_staged()
    out = []
    for p in masters():
        rel = str(p.relative_to(ROOT))
        if p == EVERYTHING or rel in known or module_of(p) in imported:
            continue
        out.append(f"{rel}: a NEW untracked master, not yet in Everything. Wire it before "
                   f"committing it, or it will never be typechecked")
    return out


def check_module_body() -> list[str]:
    """WARN class: C-11's silent empty parameterized module."""
    warn = []
    for p in masters():
        lines = code_of(p).split("\n")
        for i, line in enumerate(lines):
            m = re.match(r"^(\s*)module\s+\S+\s*\(.*\)\s*where\s*$", line)
            if not m:
                continue
            indent = len(m.group(1))
            nxt = next((l for l in lines[i + 1:] if l.strip()), None)
            if nxt is not None and (len(nxt) - len(nxt.lstrip())) <= indent:
                warn.append(f"{p.relative_to(ROOT)}: `{line.strip()[:60]}` has a body at or "
                            f"left of its own column, so the module is EMPTY and its "
                            f"parameter is out of scope (C-11)")
    return warn


CHECKS = {
    "closure": (check_closure, "FAIL"),
    "archive": (check_archive, "FAIL"),
    "closure-new": (check_closure_new, "WARN"),
    "module-body": (check_module_body, "WARN"),
}

#: THE NAME `closure` RUNS BOTH FAIL-CLASS INVARIANTS, and this line is the fix for a
#: defect the cutover created. BEFORE: `make check` ran `check-tree.py --check` with NO
#: name, so every invariant ran, `check_archive` included. AFTER: all four callers ask for
#: `closure` alone (`Makefile`, `scripts/git-hooks/pre-commit`, `scripts/pod/accept.py`
#: conjunct 3 and `scripts/pod/preflight.py` P16), so `check_archive` had no runner at all
#: while `dev/memos/L9-pod-program-design.md:2395` still calls it DD13's mechanised half
#: "at conjunct 3 and P16". Expanding the NAME rather than editing the four callers keeps
#: one word as the FAIL class, so a fifth FAIL invariant joins here and reaches every
#: caller at once. `CHECKS` itself is unchanged, so `--check archive` still runs one.
#: MEASURED 2026-08-18: both invariants exit 0 over the tree today, so this turns nothing
#: red.
GROUPS = {"closure": ("closure", "archive")}


def main(argv: list[str]) -> int:
    names = [a for a in argv[1:] if not a.startswith("-")]
    flags = [a for a in argv[1:] if a.startswith("-")]
    if any(f != "--check" for f in flags):
        print(__doc__, file=sys.stderr)
        return 2
    selected = names or list(CHECKS)
    if any(n not in CHECKS for n in selected):
        print(f"check-closure: unknown check; pick from {', '.join(CHECKS)}", file=sys.stderr)
        return 2
    # The name is validated FIRST and expanded second, so an unknown name still exits 2.
    expanded = []
    for n in selected:
        for one in GROUPS.get(n, (n,)):
            if one not in expanded:
                expanded.append(one)
    selected = expanded

    status = 0
    for name in selected:
        fn, klass = CHECKS[name]
        hits = fn()
        if not hits:
            continue
        for h in hits:
            print(f"check-closure [{name}/{klass}]: {h}", file=sys.stderr)
        if klass == "FAIL":
            status = 1
    if status == 0:
        print(f"check-closure: clean ({len(masters())} masters; {', '.join(selected)})")
    return status


if __name__ == "__main__":
    sys.exit(main(sys.argv))
