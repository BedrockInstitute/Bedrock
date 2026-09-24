#!/usr/bin/env python3
"""Agda code linter for Bedrock masters (the ```agda fences of src/**/*.lagda.md).

Report-only checks (prose is lint-prose.py's business; STYLE-agda.md is the law):

  A [options]       the file's first pragma is exactly
                    {-# OPTIONS --cubical --safe --guardedness #-}        (STYLE-agda §1)
  B [bare-open]     every `open import` carries a using and/or renaming
                    clause (`hiding` alone does not qualify)              (STYLE-agda §2)
  C [unused-import] imports are *necessary*: every name bound by a
                    using/renaming clause of an import or a plain `open`,
                    and the handle of every qualified `import M [as A]`,
                    is actually used outside the binding clauses.
                    (*Sufficiency* is exactly what `agda` typechecking
                    enforces, so it is not re-checked here.)
  D [forbidden]     no `postulate`, no TERMINATING/NON_TERMINATING/
                    NO_TERMINATION_CHECK/NO_POSITIVITY_CHECK pragma, no
                    interaction holes (`{!...!}` or a bare `?`), and no
                    qualified zero-level empty type `Empty.⊥`             (STYLE-agda §1–2)
  F [empty-open]    only Base.Prelude may `open import` the
                    Cubical.Data.Empty module family                      (STYLE-agda §2)
  G [prelude-import] Cubical modules owned by Base.Prelude may not be
                    imported again elsewhere, qualified or renamed;
                    Unit vocabulary already exported by Prelude is not re-imported
  E [hprop-snd]     propositionhood certificates use `⟨ P ⟩isProp`, not
                    the representation-level projection `P .snd`
  H [trailing-blank] an Agda code fence ends on its last code line, with no
                    blank or whitespace-only line before the closing fence
  I [private-module] private and its first module declaration share one line,
                    including aliases and declarations separated by prose

Exemptions:
  - The designated hub modules (BARE_OPEN_HUBS: curated re-export preludes,
    designed to be opened wholesale) may be opened bare, skipping B.
  - An import whose lines (or the line just above it) contain `lint-agda: keep`
    in a comment skips B/C, for genuine cases the heuristics cannot see
    (e.g. instance-only imports).
  - `open import ... public` re-exports skip C (they are interface, not use).
  - names ending in `-syntax` skip C (used through their notation, so the
    name itself never re-appears).

Known limits (v1, deliberate): the same name imported from two modules and
used once leaves both imports unflagged (false negatives over false
positives); usage detection is lexical (token-level), not scope-aware.

Usage:
  lint-agda.py [--check] [--staged] [FILE ...]
  with no FILE, scans src/**/*.lagda.md. `--staged` scans the staged masters
  only, which is what the pre-commit hook wants. Exit 1 on any violation.

`--check` also runs check_spdx() over the whole tree, and `--staged` runs it
over the staged files. DD22 bans an in-file SPDX header.
"""

import glob
import re
import subprocess
import sys
from pathlib import Path   # cutover step 7: check_spdx() needs it

# The repository root. `check_spdx()` reads it and NOTHING defined it until
# 2026-08-18, so the moved check raised NameError on its first call.
ROOT = Path(__file__).resolve().parent.parent.parent

sys.path.insert(0, str(ROOT / 'scripts/site'))
from agda_lint import *
from site_config import SiteConfig
_project = SiteConfig.load(ROOT / 'site/project.json', root=ROOT)
_policy = AgdaPolicy(**_project.values['agda_policy'])
OPTIONS_EXPECTED = list(_policy.options)
BARE_OPEN_HUBS = set(_policy.bare_open_hubs)
PRELUDE_PUBLIC_NAMES = {key: set(value) for key, value in _policy.prelude_public_names.items()}

def lint_file(path):
    return lint_text(Path(path).read_text(encoding='utf-8'), _policy)

# ---- CLI -------------------------------------------------------------------

def tracked_masters():
    """All masters on disk, tracked or not: a new file must not escape the gate
    merely by not being committed yet."""
    return sorted(glob.glob("src/**/*.lagda.md", recursive=True))


def main(argv):
    # PARSE THE FLAGS, do not drop them. Until 2026-08-18 this line read
    # `given = [a for a in argv if not a.startswith("--")]`, which threw every
    # option away in silence: `--check` did nothing and the hook's `--staged`
    # bought a whole-tree scan.
    check = "--check" in argv
    staged = "--staged" in argv
    unknown = [a for a in argv
               if a.startswith("-") and a not in ("--check", "--staged")]
    if unknown:
        sys.stderr.write(f"unknown option: {unknown[0]}\n")
        return 2
    given = [a for a in argv if not a.startswith("-")]
    files = [f for f in given if f.endswith(".lagda.md")]
    if not given:
        # No explicit FILE. `--staged` scans what this commit changes; anything
        # else scans all masters (src/ only; a new file must not escape the gate
        # merely by not being committed yet).
        files = staged_masters() if staged else tracked_masters()
    # Outside every gate (archived D20, live DD13): archive paths are dropped.
    #
    # `agents/` is dropped for the same reason `scripts/gate/lint-prose.py:448` drops it, and
    # AGENTS.md states the rule: an agent's brief, report and probe are a RECORD, and a
    # record is never rewritten. Style is a rule for code the project maintains.
    #
    # MEASURED 2026-08-15: [LJ-1.266] priced step 6 in seconds by copying
    # src/L/Condensation.lagda.md into its task directory four times, one arm per
    # treatment. The copies inherit the master's using-lists, and the appended content
    # uses fewer of those names, so the linter reported 27 unused imports in the ARMS of
    # a finished experiment. Repairing them would edit the thing that was measured and
    # would invalidate the 2.38 s/line figure (C-32). This is the first time a task
    # directory held a `.lagda.md` at all; probes there are `.agda`, which is why the two
    # linters disagreed for so long without anyone noticing.
    files = [f for f in files
             if not f.startswith("archive/") and not f.startswith("agents/")]
    total = 0
    for path in files:
        for lineno, rule, msg in lint_file(path):
            print(f"{path}:{lineno}: [{rule}] {msg}")
            total += 1
    if total:
        print(f"lint-agda: {total} violation(s)")
    rc = 1 if total else 0

    # DD22, the in-file SPDX ban. It fires at `make check` over the whole tree
    # and at the pre-commit hook over the staged files. A bare FILE list runs
    # the lint alone, because a caller that names a master asks for a lint.
    if check or staged:
        spdx = check_spdx(staged_files() if staged else None)
        for msg in spdx:
            print(msg)
        if spdx:
            print(f"lint-agda: {len(spdx)} in-file SPDX header(s)")
            rc = 1
    return rc


# ---------------------------------------------------------------------------
# MOVED HERE BY THE POD CUTOVER, step 7, 2026-08-18. It lived in
# scripts/gate/check-tree.py, which the cutover splits: the closure half became
# scripts/pod/check-closure.py and this half had no home. **Moving it is what
# keeps the check alive**: archiving check-tree.py without this move would have
# retired a live check in silence, which is the failure clause W4 exists for.
# ---------------------------------------------------------------------------
def check_spdx(paths=None) -> list[str]:
    """DD22: licensing has ONE source of truth, REUSE.toml, so no file carries an
    in-file SPDX header.

    `paths` scopes the scan. `None` means the whole tree, which is the `--check`
    and conjunct 6 caliber. The pre-commit hook passes the STAGED files instead,
    because a whole-tree scan costs 5.48 s over 6,230 files (measured 2026-08-18)
    and a hook must stay cheap. A header enters the tree inside a file that
    somebody edits, so the staged scope catches it at the commit that adds it.
    """
    bad = []
    for p in (ROOT.rglob("*") if paths is None else paths):
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
                       f"of truth, REUSE.toml (archived D4, live DD22); delete the header")
    return bad


# ---------------------------------------------------------------------------
# WIRED 2026-08-18. The move above landed the function BELOW the `__main__`
# guard and named a global `ROOT` this file did not define, so in script mode
# the `def` never ran and an import-mode call raised NameError. DD22 was
# therefore unenforced from the cutover until now, while the cutover commit
# fc676cb reported it moved and verified. `main()` calls it on both the
# `--check` and the `--staged` path.
# ---------------------------------------------------------------------------
def staged_masters():
    """The masters this commit adds or changes.

    THE HOOK ASKED FOR THIS AND DID NOT GET IT. scripts/git-hooks/pre-commit
    passes `--staged`, and the old argument parser dropped every `--` token, so
    the hook silently scanned the whole tree. Coverage was wider, not narrower,
    but one pre-existing violation anywhere then blocked every unrelated commit
    under the hook's `set -e`. This mirrors scripts/gate/lint-prose.py:438-442.
    """
    return sorted(f for f in git_lines(["diff", "--cached", "--name-only",
                                        "--diff-filter=ACM"])
                  if f.endswith(".lagda.md"))


def staged_files():
    """Every staged path, for the SPDX scan. It is not limited to masters."""
    return [ROOT / f for f in
            git_lines(["diff", "--cached", "--name-only", "--diff-filter=ACM"])
            if (ROOT / f).is_file()]


def git_lines(args):
    try:
        out = subprocess.run(["git", *args], cwd=ROOT,
                             capture_output=True, text=True, check=True).stdout
    except (subprocess.CalledProcessError, FileNotFoundError):
        return []
    return [l for l in out.splitlines() if l]


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
