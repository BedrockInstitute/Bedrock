#!/usr/bin/env python3
"""Whole-tree invariants that the per-file linters structurally cannot see.

`lint-agda.py` and `lint-prose.py` read one file at a time, so nothing has ever checked the
properties that are about the tree AS A WHOLE. This script does, and it exists because one of
those properties is the project's only documented false-green mode.

The checks, each with the rule it enforces and why it is here rather than left to review:

- **closure** (PLAN section 7 rule 3). Every master under `src/` must be in the import list of
  `src/Everything.lagda.md`. `make check` typechecks EXACTLY ONE file, `Everything`, which is
  what makes it a trusted single invocation; the cost is that a master nobody imports is never
  typechecked at all and the gate still goes green. PLAN has specified this audit since the
  beginning and nothing implemented it. Measured on the tree the day it was written: 123
  masters, 122 imported, one gap, and that gap was a real in-progress chapter.

- **archive** (D20). No live master may import a module whose only home is `archive/`. The
  archive is unwired and ungated by design, so an import across the boundary would drag
  unchecked code into the checked tree. Matters from the retirement surgery onward.

- **shared-cjk** (LESSONS C-8, STYLE-i18n). Prose outside any `<!--lang-->` block is SHARED and
  is copied verbatim into every language's page, so a CJK sentence written there appears
  untranslated in the English book. No linter looked for this.

- **spdx** (D4, AGENTS.md). Licensing has one source of truth, `REUSE.toml`. An in-file
  SPDX identifier header is a second one. (This paragraph deliberately avoids spelling the
  tag out: the check reads file HEADS, and an earlier draft flagged its own docstring.)

- **retiring** (D18 plus D20), WARN ONLY. A SURVIVING master that imports a module booked for
  retirement is a debt: at the surgery, that import must be re-homed or the chapter breaks.
  It warns rather than fails because the whole point of the transition period is that both
  trees coexist (D15's two-step), so a crossing is legal today and lethal later. Measured on
  the day it was added: seven surviving masters crossed the boundary, one of them committed
  that same hour, which is why this had to become a check rather than a note. `Everything` is
  exempt: it is the catalog and is rewired wholesale at the surgery.

- **module-body** (LESSONS C-11), WARN ONLY. A parameterized module header whose body is not
  indented deeper is an EMPTY module: Agda accepts it, the parameter is out of scope, and the
  declarations meant to be inside it silently are not. It warns rather than fails because
  layout has edge cases this predicate does not model, and a false failure on a legitimate
  layout would cost more than the trap.

DELIBERATELY NOT CHECKED, decided 2026-08-05 after [L3.32-T60] proposed them:

- *module name equals file path*: Agda already rejects it (`ModuleNameDoesntMatchFileName`),
  verified, so a check here is unreachable whenever the typechecker passes. Dead weight.
- *no single-capital import alias, no ASCII prime in a public name*: the only alias hit is in
  a chapter already booked for retirement, so a gate would force work on code that is about to
  be archived, and a prime is a normal Agda idiom for a variant, so the rule would misfire on
  future code. Left to review, where a human can tell a provenance name from a variant.
- *a PLAN row's opening status word*: the predicate "opens non-terminal, later says DONE"
  cannot tell a goal's status from a sub-item's. On the real tree it flagged a row whose DONE
  belongs to one candidate inside a survey, which is a false positive, and a status gate that
  cries wolf on the status register is worse than none.

GATE DEBT. The expensive part of a full `agda src/Everything.lagda.md` is not its twelve
minutes, which run in the background, but the QUIET TREE it needs for all of them: no agent may
write a master while it runs, so every full gate costs one dispatch window. `--gate-debt`
measures what has accumulated since the last green one, so the decision to spend a window is
made on a number instead of a feeling.

Usage:
  check-tree.py --check         run every invariant over the working tree (what make check runs)
  check-tree.py --gate-debt     in-fence lines and commits since the last recorded green gate
  check-tree.py --gate-passed   record HEAD as the last green full gate
  check-tree.py --check NAME    run one: closure, archive, shared-cjk, spdx, module-body
Exit status: 0 clean, 1 a FAIL-class violation, 2 usage error.
"""

from __future__ import annotations

import re
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
SRC = ROOT / "src"
EVERYTHING = SRC / "Everything.lagda.md"
ARCHIVE = ROOT / "archive"

FENCE = re.compile(r"```agda\n(.*?)```", re.S)
MARKER = re.compile(r"<!--\s*(en|zh|ja|/)\s*-->")
CJK = re.compile(r"[　-〿㐀-䶿一-鿿！-～]")


def masters() -> list[Path]:
    """The working tree, not the index: a new untracked master must not escape the audit."""
    return sorted(p for p in SRC.rglob("*.lagda.md"))


def module_of(p: Path) -> str:
    return str(p.relative_to(SRC)).removesuffix(".lagda.md").replace("/", ".")


def code_of(p: Path) -> str:
    return "\n".join(FENCE.findall(p.read_text(encoding="utf-8")))


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
    imported = set(re.findall(r"^import ([A-Za-z0-9_.]+)", code_of(EVERYTHING), re.M))
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
    # A module re-created under src/ is a revival and is legal (D20 allows copy-out).
    only_archived = archived - live
    bad = []
    for p in masters():
        for name in re.findall(r"^\s*(?:open )?import ([A-Za-z0-9_.]+)", code_of(p), re.M):
            if name in only_archived:
                bad.append(f"{p.relative_to(ROOT)} imports `{name}`, which lives only in "
                           f"archive/. D20: nothing imports across the archive boundary; "
                           f"copy it out into src/ if it is genuinely needed again")
    return bad


def check_shared_cjk() -> list[str]:
    """Prose outside every language marker is shared and reaches the English book verbatim."""
    bad = []
    for p in masters():
        text = p.read_text(encoding="utf-8")
        in_fence = False
        lang = None
        for n, line in enumerate(text.split("\n"), 1):
            if line.startswith("```"):
                in_fence = not in_fence
                continue
            if in_fence:
                continue
            if (m := MARKER.search(line)):
                lang = None if m.group(1) == "/" else m.group(1)
                continue
            if lang is None and CJK.search(line):
                bad.append(f"{p.relative_to(ROOT)}:{n}: CJK in SHARED prose (outside any "
                           f"<!--en|zh|ja--> block). Shared prose is copied verbatim into "
                           f"every language, so this would appear untranslated in the "
                           f"English book. Wrap it in a language block")
    return bad


def check_spdx() -> list[str]:
    bad = []
    for p in ROOT.rglob("*"):
        if not p.is_file() or p.name == "REUSE.toml":
            continue
        parts = p.relative_to(ROOT).parts
        if parts and parts[0] in {".git", "_build", ".venv", "node_modules", "LICENSES"}:
            continue
        try:
            # An SPDX header is a HEADER: it sits in the file's opening comment block. Scanning
            # the whole file made this check false-positive on its own source, which carries the
            # string as a literal. Bounding it to the head both matches the rule as written and
            # kills the self-match.
            head = "\n".join(p.read_text(encoding="utf-8", errors="ignore").split("\n")[:30])
        except OSError:
            continue
        if "SPDX-License" + "-Identifier" in head:
            bad.append(f"{p.relative_to(ROOT)}: in-file SPDX header. Licensing has one source "
                       f"of truth, REUSE.toml (D4); delete the header")
    return bad


def check_closure_new() -> list[str]:
    """WARN: an UNTRACKED master that is not wired. Its author must wire it before
    committing, but it must not block anyone else."""
    if not EVERYTHING.exists():
        return []
    imported = set(re.findall(r"^import ([A-Za-z0-9_.]+)", code_of(EVERYTHING), re.M))
    known = _tracked_or_staged()
    out = []
    for p in masters():
        rel = str(p.relative_to(ROOT))
        if p == EVERYTHING or rel in known or module_of(p) in imported:
            continue
        out.append(f"{rel}: a NEW untracked master, not yet in Everything. Wire it before "
                   f"committing it, or it will never be typechecked")
    return out


def check_retiring() -> list[str]:
    """WARN class: a surviving master importing a chapter booked for retirement."""
    try:
        import tomllib
        data = tomllib.loads((ROOT / "dev" / "ledger.toml").read_text())
    except Exception as exc:
        return [f"could not read dev/ledger.toml ({exc}); the retirement boundary is UNCHECKED"]

    def retires(f: str) -> bool:
        for e in data.get("retire", []):
            if "prefix" in e and f.startswith(e["prefix"]) and f not in e.get("except", []):
                return True
            if e.get("path") == f:
                return True
        return False

    rel = [str(p.relative_to(ROOT)) for p in masters()]
    doomed = {module_of(ROOT / f): f for f in rel if retires(f)}
    warn = []
    for f in rel:
        if retires(f) or f.endswith("Everything.lagda.md"):
            continue
        code = code_of(ROOT / f)
        hits = sorted({m for m in re.findall(r"^\s*(?:open )?import ([A-Za-z0-9_.]+)", code, re.M)
                       if m in doomed})
        for h in hits:
            warn.append(f"{f} imports `{h}`, which D18 retires. Legal now, lethal at the "
                        f"surgery: this import must be re-homed or the chapter breaks. "
                        f"Every crossing is retirement-surgery work that the ledger's "
                        f"surgery row must carry")
    return warn


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


LAST_GATE = ROOT / "_build" / ".last-gate"


def gate_debt() -> tuple[int, int, str]:
    """(commits, in-fence lines added, base sha) since the last recorded green gate."""
    import subprocess
    base = LAST_GATE.read_text().strip() if LAST_GATE.exists() else ""
    if not base:
        return -1, -1, ""
    n = subprocess.run(["git", "rev-list", "--count", f"{base}..HEAD"], cwd=ROOT,
                       capture_output=True, text=True).stdout.strip()
    added = 0
    diff = subprocess.run(["git", "diff", "-U0", f"{base}..HEAD", "--", "src/"],
                          cwd=ROOT, capture_output=True, text=True).stdout
    in_fence = False
    for line in diff.split("\n"):
        if line.startswith("+```agda"):
            in_fence = True
            continue
        if in_fence and line.startswith("+```"):
            in_fence = False
            continue
        if line.startswith("+") and not line.startswith("+++") and line[1:].strip():
            added += 1
    return int(n or 0), added, base


CHECKS = {
    "closure": (check_closure, "FAIL"),
    "archive": (check_archive, "FAIL"),
    "shared-cjk": (check_shared_cjk, "FAIL"),
    "spdx": (check_spdx, "FAIL"),
    "closure-new": (check_closure_new, "WARN"),
    "retiring": (check_retiring, "WARN"),
    "module-body": (check_module_body, "WARN"),
}


def main(argv: list[str]) -> int:
    names = [a for a in argv[1:] if not a.startswith("-")]
    flags = [a for a in argv[1:] if a.startswith("-")]
    if any(f not in {"--check", "--gate-debt", "--gate-passed"} for f in flags):
        print(__doc__, file=sys.stderr)
        return 2
    if "--gate-passed" in flags:
        import subprocess
        sha = subprocess.run(["git", "rev-parse", "HEAD"], cwd=ROOT,
                             capture_output=True, text=True).stdout.strip()
        LAST_GATE.parent.mkdir(parents=True, exist_ok=True)
        LAST_GATE.write_text(sha + "\n")
        print(f"check-tree: recorded {sha[:9]} as the last green full gate")
        return 0
    if "--gate-debt" in flags:
        n, added, base = gate_debt()
        if n < 0:
            print("check-tree: no green gate recorded yet; run one and then --gate-passed")
            return 0
        print(f"check-tree: since {base[:9]}, {n} commit(s) and about {added} added lines "
              f"under src/.")
        print("  Batch trigger (D28): a full gate is due at 3 to 4 returns or about 1,000 "
              "added lines, whichever comes first, because each gate costs one quiet "
              f"dispatch window. Currently {'DUE' if (n >= 4 or added >= 1000) else 'not yet due'}.")
        return 0
    selected = names or list(CHECKS)
    if any(n not in CHECKS for n in selected):
        print(f"check-tree: unknown check; pick from {', '.join(CHECKS)}", file=sys.stderr)
        return 2

    status = 0
    for name in selected:
        fn, klass = CHECKS[name]
        hits = fn()
        if not hits:
            continue
        for h in hits:
            print(f"check-tree [{name}/{klass}]: {h}", file=sys.stderr)
        if klass == "FAIL":
            status = 1
    if status == 0:
        print(f"check-tree: clean ({len(masters())} masters; "
              f"{', '.join(selected)})")
    return status


if __name__ == "__main__":
    sys.exit(main(sys.argv))
