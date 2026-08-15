#!/usr/bin/env python3
"""LJ-1.290: move `scripts/*.py` into subdirectories and repair every path that breaks.

THIS SCRIPT IS NOT A `git mv` LOOP, AND THAT IS THE WHOLE FINDING. Twenty-four of the
thirty-four scripts derive the repository root by counting directories up from `__file__`
(`ROOT = Path(__file__).resolve().parent.parent`). One directory deeper, that expression
names `<repo>/scripts` instead of `<repo>`. Some scripts then crash; some report CLEAN over
an empty file set. So a move is a code change to every file it touches.

MODES

  --plan        print the mapping and every rewrite site; change nothing.
  --naive       move the files ONLY, with no code repair. This mode exists to MEASURE what
                a careless move does. Never use it for the real migration.
  --apply       move the files and repair every path this script knows about.
  --root DIR    operate on DIR instead of the repository this file sits in. Use it to run
                the migration against a copy.
  --no-git      use `os.replace` instead of `git mv` (for a copy that is not a repository).

WHAT `--apply` REPAIRS, and each entry is a measured site, not a precaution.

  1. ROOT DEPTH. `Path(__file__).resolve().parent.parent` gains one `.parent` in every
     moved script. 24 sites.
  2. SIBLING IMPORT PATH. `sys.path.insert(0, str(Path(__file__).resolve().parent))` becomes
     the scripts ROOT, so a checker in `gate/` still imports `agents_tree` from `dispatch/`.
     10 sites.
  3. SIBLING LOAD BY FILENAME. Three scripts load a sibling by an explicit path
     (`check-glossary.py` -> `lint-prose.py`, `check-ratio.py` -> `check-timing.py`,
     `check-timing.py` -> `obligations.py`, `check-dev-docs.py` -> `check-rule-ids.py`).
     Each literal is rewritten to the target's new home.
  4. THE NON-RECURSIVE GLOB. `check-rule-ids.py` scans `(ROOT / "scripts").glob("*.py")`.
     After a move that glob sees almost nothing and still exits 0. It becomes `rglob`.
  5. THE DISPATCH POINTER. `check-dispatch-policy.py` holds the literal
     `scripts/dispatch_policy.py`, which governed documents must contain.
  6. CITATIONS in `Makefile`, `.github/workflows/`, `scripts/git-hooks/`, `scripts/tests/`,
     `scripts/README.md`, `dev/` (live documents only) and `AGENTS.md`.

WHAT IT DOES NOT TOUCH, BY RULE, and the report prices each one.

  * `agents/**` and `agents/tasks/archive/**`: frozen records (C-41).
  * `dev/JOURNAL.md` and `dev/memos/**`: dated records. `check-rule-ids.py` already exempts
     both for this reason, so this script treats them the same way.
  * `archive/**`: outside every gate by construction.
  * `.claude/**`: untracked tooling, outside the write scope of this task.
"""

from __future__ import annotations

import argparse
import os
import re
import subprocess
import sys
from pathlib import Path

# --------------------------------------------------------------------------------------
# THE MAPPING. The group is named for WHEN the script runs and WHO runs it, because that
# is the question a reader arrives with. The report states the eight ambiguous cases.
# --------------------------------------------------------------------------------------

MAPPING: dict[str, str] = {
    # gate/ : runs inside `make check` or a git hook. A red one stops a commit.
    "check-agents-guard.py":       "gate",
    "check-archive-cited.py":      "gate",
    "check-build-manifest.py":     "gate",
    "check-dd25-review-named.py":  "gate",
    "check-dd4-stated.py":         "gate",
    "check-dev-docs.py":           "gate",
    "check-fences.py":             "gate",
    "check-glossary.py":           "gate",
    "check-live-territory.py":     "gate",
    "check-premises-stated.py":    "gate",
    "check-probes.py":             "gate",
    "check-rule-ids.py":           "gate",
    "check-task-index.py":         "gate",
    "check-tree.py":               "gate",
    "lint-agda.py":                "gate",
    "lint-prose.py":               "gate",
    # dispatch/ : everything about running and auditing a dispatch.
    "check-dispatch-policy.py":    "dispatch",
    "check-sources-read.py":       "dispatch",
    "dd25-record.py":              "dispatch",
    "rules.py":                    "dispatch",
    # measure/ : costs seconds to minutes, runs Agda, or reports a number. Never a gate.
    "check-ratio.py":              "measure",
    "check-timing.py":             "measure",
    "check-unbound-hyp.py":        "measure",
    "deletion-test.py":            "measure",
    "ledger.py":                   "measure",
    "obligations.py":              "measure",
    # site/ : the publishing pipeline and the deploy.
    "extract-types.py":            "site",
    "gen-depmap.py":               "site",
    "i18n_markers.py":             "site",   # every importer is in site/; see PLACEMENT
    "link-check.py":               "site",
    "render-site.py":              "site",
    "weave-i18n.py":               "site",
    "depmap-template.html":        "site",   # gen-depmap.py reads it from its own directory
    # ops/ : machine safety.
    "agda-watchdog.sh":            "ops",
}

# PLACEMENT RULE FOR A SHARED MODULE, and it is the reason the top level is not a
# leftover bucket. **A module that another script imports lives in the SHALLOWEST
# directory that contains every importer.** The rule is mechanical, so a test can
# enforce it (C-48), and it decides every case in this tree without a judgement call:
#
#   agents_tree.py      importers in gate/ AND dispatch/  -> scripts/     (flat)
#   dispatch_policy.py  importer in dispatch/, plus `.claude/skills/codex-dispatch/
#                       dispatch.py`, which inserts `<repo>/scripts`      -> scripts/ (flat)
#   i18n_markers.py     every importer in site/                           -> site/
#   ledger.py           importers check-ratio, deletion-test              -> measure/
#   check-timing.py     importer check-ratio                              -> measure/
#   obligations.py      importer check-timing                             -> measure/
#   lint-prose.py       importer check-glossary                           -> gate/
#   check-rule-ids.py   importer check-dev-docs                           -> gate/
#
# THE CONSEQUENCE IS WHY THIS MAPPING IS CHEAP: all six load-a-sibling-by-filename
# couples land INSIDE one group, so not one of those literals needs rewriting, and
# `dispatch_policy.py` staying flat means `.claude/` needs NO edit at all.
KEEP_FLAT = {"README.md", "agents_tree.py", "dispatch_policy.py"}

# Repairs a mechanical rewrite must NOT make on its own, because each changes BEHAVIOUR.
MANUAL_STEPS = [
    "scripts/gate/check-agents-guard.py:56  THE PROBE MUST TRY BOTH HOMES.\n"
    "     This script writes the GUARD_PATHS constant. It does NOT rewrite the probe,\n"
    "     because a regex that edits control flow is the shape a wrong choice hides in\n"
    "     (C-43). Replace the single `git cat-file -e {commit}:{GUARD_PATH}` probe with a\n"
    "     loop over GUARD_PATHS that returns true when ANY of them exists.\n"
    "     WHY: the audit judges only a commit whose own tree carries the path. MEASURED\n"
    "     on the copy: baseline exit 1 (a real finding); after a bare literal rewrite,\n"
    "     exit 0 with `0 guarded commit(s)`. The whole history stops being judged and\n"
    "     nothing says so. This is C-41 inside a checker.",
    "scripts/README.md  IT IS THE ONLY DECLARED TAXONOMY AND IT IS NOW WRONG.\n"
    "     642 lines, organised by pipeline and topic, with no directory grouping. After\n"
    "     the move it describes a layout that does not exist. Rewrite its headings to the\n"
    "     six groups, or the repository holds two taxonomies and DD19 is broken.",
    "AGENTS.md  15 citations, 9 distinct scripts, and the edit is DD19-GATED.\n"
    "     `scripts/check-dev-docs.py` runs the `agents-enforcers` subcheck inside\n"
    "     `make check`: every `scripts/*.py` path named in AGENTS.md must EXIST. So the\n"
    "     move cannot land without an AGENTS.md edit, and an AGENTS.md edit cannot land\n"
    "     without the owner's ruling and a dated `AGENTS-diff-approved:` trailer.\n"
    "     THE MOVE AND THE RULEBOOK EDIT ARE ONE COMMIT, or the gate is red between them.",
]
KEEP_DIRS = {"tests", "git-hooks", "__pycache__"}

# Live text files whose citations are rewritten. A dated record is NOT here.
CITATION_FILES: list[str] = [
    "Makefile",
    "AGENTS.md",
    "CLAUDE.md",
    "scripts/README.md",
    "scripts/git-hooks/pre-commit",
    "scripts/git-hooks/commit-msg",
    ".github/workflows/pages.yml",
    ".github/workflows/cloudflare.yml",
]
CITATION_GLOBS: list[str] = [
    "scripts/tests/*.py",
    "dev/*.md",
    "dev/*.toml",
]
# Dated records under dev/. Never rewritten, for the reason check-rule-ids.py names.
CITATION_EXCLUDE = {"dev/JOURNAL.md"}

SCRIPT_PATH_RE = re.compile(r"scripts/([A-Za-z0-9_.-]+\.(?:py|sh|html))")


def new_rel(name: str) -> str | None:
    """`check-tree.py` -> `gate/check-tree.py`; None when the file does not move."""
    group = MAPPING.get(name)
    return f"{group}/{name}" if group else None


# --------------------------------------------------------------------------------------
# The in-file repairs.
# --------------------------------------------------------------------------------------

def repair_source(text: str, name: str) -> tuple[str, list[str]]:
    """Repair one moved script. Returns the new text and a list of what changed."""
    notes: list[str] = []
    before = text

    # 1. ROOT depth. Every `resolve().parent.parent` in a moved script gains one level.
    text, n = re.subn(r"(\.resolve\(\)\.parent\.parent)(?!\.parent)", r"\1.parent", text)
    if n:
        notes.append(f"root-depth x{n}")

    # 2. Sibling import path. `sys.path.insert(0, str(Path(__file__).resolve().parent))`
    #    inserted `scripts/` before the move and inserts the GROUP directory after it.
    #    WHERE IT MUST POINT DEPENDS ON WHERE THE IMPORTED MODULE WENT, and getting it
    #    wrong in either direction breaks an import. MEASURED on the copy: raising it
    #    unconditionally broke `deletion-test.py` and `check-ratio.py`, which import
    #    `ledger` from their OWN group, with `No module named 'ledger'`.
    #      imports a FLAT module (agents_tree, dispatch_policy) -> .parent.parent
    #      imports a module in its own group                    -> leave it alone
    #    Rule 1 does not reach this line: it carries ONE `.parent`, not two.
    flat_mods = {"agents_tree", "dispatch_policy"}
    imported = set(re.findall(r"^\s*(?:import|from)\s+([a-z_]+)", text, re.M))
    if imported & flat_mods:
        text, n = re.subn(
            r"sys\.path\.insert\(0, str\(Path\(__file__\)\.resolve\(\)\.parent\)\)",
            "sys.path.insert(0, str(Path(__file__).resolve().parent.parent))",
            text,
        )
        if n:
            notes.append(f"syspath-to-scripts-root x{n}")

    # `sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))` needs NO change:
    # `render-site.py` and `gen-depmap.py` import `i18n_markers`, which moves WITH them
    # into site/, so the inserted directory is still the one that holds the module.

    # 3. Sibling load by filename. `HERE` and `Path(__file__).parent` name the GROUP
    #    directory after the move, so every sibling literal needs its group prefix.
    for sib in sorted(MAPPING, key=len, reverse=True):
        target = new_rel(sib)
        if target is None or sib == name:
            continue
        group = MAPPING[sib]
        mygroup = MAPPING.get(name)
        if group == mygroup:
            continue                      # still a true sibling; the literal still works
        rel = f"../{group}/{sib}"
        # os.path.join(HERE, "lint-prose.py")
        new_text, n = re.subn(
            rf'(os\.path\.join\([A-Za-z_]+, )"{re.escape(sib)}"',
            rf'\1"{rel}"', text)
        if n:
            notes.append(f"sibling-join {sib} x{n}")
            text = new_text
        # _load("lint_prose", "lint-prose.py") / _load_sibling(..., "check-rule-ids.py")
        new_text, n = re.subn(
            rf'(_load(?:_sibling)?\([^,]+, )"{re.escape(sib)}"',
            rf'\1"{rel}"', text)
        if n:
            notes.append(f"sibling-load {sib} x{n}")
            text = new_text
        # Path(__file__).resolve().parent / "check-timing.py"  (after rule 1 it is
        # ...parent.parent, i.e. scripts/), and Path(__file__).parent / "obligations.py"
        new_text, n = re.subn(
            rf'(Path\(__file__\)(?:\.resolve\(\))?\.parent) / "{re.escape(sib)}"',
            rf'\1.parent / "{group}/{sib}"', text)
        if n:
            notes.append(f"sibling-path {sib} x{n}")
            text = new_text
        # ROOT / "scripts" / filename  is handled by the citation pass below.

    # 3b. `check-dev-docs.py` loads its sibling from `ROOT / "scripts" / filename`, which
    #     is the scripts ROOT and not its own directory, so an intra-group couple still
    #     breaks. This is the one load site the group rule does not save.
    #     The cure makes it SELF-RELATIVE, which is the pattern the other three load
    #     sites already use and which no future move can break again.
    new_text, n = re.subn(r'ROOT / "scripts" / filename',
                          'Path(__file__).resolve().parent / filename', text)
    if n:
        notes.append(f"root-scripts-load x{n}")
        text = new_text

    # 3c. THE SELF-ANCHOR. `check-agents-guard.py` judges only a commit whose own tree
    #     carries GUARD_PATH. Rewriting that literal to the new path makes EVERY commit
    #     in history read as pre-guard and the audit passes green judging nothing.
    #     MEASURED on the copy: baseline exit 1 (a real finding), rewritten exit 0 with
    #     `0 guarded commit(s)`. So the checker must accept BOTH homes. This is C-41
    #     inside a checker, and it is a BEHAVIOUR change, printed as such.
    if name == "check-agents-guard.py":
        new_text, n = re.subn(
            r'^GUARD_PATH = "scripts/check-agents-guard\.py"$',
            'GUARD_PATH = "scripts/gate/check-agents-guard.py"\n'
            '# C-41: the guard kept its old home as a second accepted name. Without it,\n'
            '# every commit made before the move reads as pre-guard and the history audit\n'
            '# goes green over the whole record. Never drop this line.\n'
            'GUARD_PATHS = ("scripts/gate/check-agents-guard.py",\n'
            '               "scripts/check-agents-guard.py")',
            text, flags=re.M)
        if n:
            notes.append("guard-path-both (BEHAVIOUR CHANGE, needs the hand patch)")
            text = new_text

    # 4. The non-recursive glob that would silently narrow.
    new_text, n = re.subn(r'\(ROOT / "scripts"\)\.glob\("\*\.py"\)',
                          '(ROOT / "scripts").rglob("*.py")', text)
    if n:
        notes.append(f"glob-to-rglob x{n}")
        text = new_text

    # 5 and 6. Any literal `scripts/<name>` inside a script.
    text, moved = rewrite_citations(text)
    if moved:
        notes.append(f"citations x{moved}")

    return text, (notes if text != before else [])


def rewrite_citations(text: str) -> tuple[str, int]:
    """Rewrite every `scripts/<file>` literal that names a moved file."""
    count = 0

    def sub(m: re.Match) -> str:
        nonlocal count
        rel = new_rel(m.group(1))
        if rel is None:
            return m.group(0)
        count += 1
        return f"scripts/{rel}"

    return SCRIPT_PATH_RE.sub(sub, text), count


# A suite does NOT write `scripts/check-tree.py`. It writes the basename as one component
# of a path expression: `ROOT / "scripts" / "check-dev-docs.py"`,
# `os.path.join(HERE, "..", "lint-agda.py")`, `_load("check_glossary",
# "check-glossary.py")`. MEASURED: the citation rewriter above matches NONE of these, and
# every one of the 13 suites in `make test` broke on the first pass because of it.
BARE_NAME_RE = re.compile(r'"([A-Za-z0-9_.-]+\.(?:py|sh|html))"')


def rewrite_bare_names(text: str) -> tuple[str, int]:
    """Rewrite a moved script's BARE basename inside a path expression."""
    count = 0

    def sub(m: re.Match) -> str:
        nonlocal count
        rel = new_rel(m.group(1))
        if rel is None:
            return m.group(0)
        count += 1
        return f'"{rel}"'

    return BARE_NAME_RE.sub(sub, text), count


# --------------------------------------------------------------------------------------
# Driver.
# --------------------------------------------------------------------------------------

def move(root: Path, name: str, rel: str, use_git: bool) -> None:
    src = root / "scripts" / name
    dst = root / "scripts" / rel
    dst.parent.mkdir(parents=True, exist_ok=True)
    if use_git:
        subprocess.run(["git", "mv", str(src.relative_to(root)), str(dst.relative_to(root))],
                       cwd=root, check=True)
    else:
        os.replace(src, dst)


def main(argv: list[str]) -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--plan", action="store_true")
    ap.add_argument("--naive", action="store_true")
    ap.add_argument("--apply", action="store_true")
    ap.add_argument("--root", default=None)
    ap.add_argument("--no-git", action="store_true")
    args = ap.parse_args(argv)

    root = Path(args.root).resolve() if args.root else Path(__file__).resolve().parents[3]
    scripts = root / "scripts"
    if not scripts.is_dir():
        sys.exit(f"no scripts/ under {root}")

    on_disk = {p.name for p in scripts.iterdir()
               if p.is_file() and p.name not in KEEP_FLAT}
    unmapped = on_disk - set(MAPPING)
    missing = set(MAPPING) - on_disk
    if unmapped:
        print(f"UNMAPPED (the migration refuses to guess): {sorted(unmapped)}")
    if missing:
        print(f"MAPPED BUT ABSENT: {sorted(missing)}")
    if unmapped and args.apply:
        sys.exit("refusing to apply with an unmapped file; a misc/ bucket is forbidden (C-43)")

    if args.plan:
        for group in sorted(set(MAPPING.values())):
            members = sorted(n for n, g in MAPPING.items() if g == group)
            print(f"\nscripts/{group}/  ({len(members)})")
            for n in members:
                print(f"    {n}")
        print(f"\nunchanged: scripts/README.md, scripts/tests/, scripts/git-hooks/")
        return 0

    if not (args.naive or args.apply):
        sys.exit("pass --plan, --naive or --apply")

    use_git = not args.no_git

    # Move first, so the repairs run against the new tree.
    for name in sorted(MAPPING):
        rel = new_rel(name)
        if rel and (scripts / name).is_file():
            move(root, name, rel, use_git)
    print(f"moved {len(MAPPING)} file(s)")

    if args.naive:
        print("NAIVE MODE: no path was repaired. This tree is expected to be broken.")
        return 0

    # Repair the moved scripts.
    for name in sorted(MAPPING):
        rel = new_rel(name)
        if rel is None or not name.endswith((".py", ".sh")):
            continue
        path = scripts / rel
        if not path.is_file():
            continue
        text = path.read_text(encoding="utf-8")
        new, notes = repair_source(text, name)
        if notes:
            path.write_text(new, encoding="utf-8")
            print(f"  repaired {rel}: {', '.join(notes)}")

    # Repair the citations in the live consumers.
    targets: list[Path] = [root / p for p in CITATION_FILES]
    for g in CITATION_GLOBS:
        targets += sorted(root.glob(g))
    seen: set[Path] = set()
    for path in targets:
        if path in seen or not path.is_file():
            continue
        seen.add(path)
        if str(path.relative_to(root)) in CITATION_EXCLUDE:
            print(f"  SKIPPED (dated record): {path.relative_to(root)}")
            continue
        text = path.read_text(encoding="utf-8")
        new, n = rewrite_citations(text)
        extra = 0
        if path.parent.name == "tests":
            new, extra = rewrite_bare_names(new)
            # `test_i18n.py` inserts `<scripts>/..` and then imports `i18n_markers`, which
            # moves into site/ with its three importers. The insert must follow it.
            # This edit changes NO literal the two rewriters see, so the write must be
            # decided by comparing the text, never by their counters.
            new = new.replace(
                'sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), ".."))',
                'sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)),'
                ' "..", "site"))')
        if new != text:
            path.write_text(new, encoding="utf-8")
            print(f"  rewrote {path.relative_to(root)}: {n} citation(s), "
                  f"{extra} bare name(s)")

    print("\nNOT rewritten, by rule: agents/**, archive/**, dev/JOURNAL.md, .claude/**")
    print("\n" + "=" * 78)
    print("THE MIGRATION IS NOT FINISHED. Three steps are NOT mechanical:")
    for i, step in enumerate(MANUAL_STEPS, 1):
        print(f"\n{i}. {step}")
    print("=" * 78)
    # Exit 3, never 0. A migration that says `done` while three hand steps are open is
    # the escape hatch C-43 names.
    return 3


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
