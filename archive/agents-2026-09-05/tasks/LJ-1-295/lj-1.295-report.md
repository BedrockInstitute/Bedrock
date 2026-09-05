# LJ-1.295 report: MOVE `scripts/` into subdirectories (option C)

STATUS: COMPLETE. Every mapped file moved with `git mv`, every tracked consumer repaired,
baselines captured before and after on the same tree, nothing committed.

## 0. THE VERDICT

1. **The move is done and the tree is green everywhere it was green before.** 39 of 40
   individually run tools reproduce their baseline exit code. The four suites that were
   red before are red in the same way. The ONE new red is `check-dev-docs.py`, and it is
   the expected one: 15 `agents-enforcers` defects, one per AGENTS.md line that names a
   moved script by its old flat path. AGENTS.md is the owner's (DD19); the exact lines
   are in section 6.
2. **All four gates `[LJ-1.290]` named as false-green risks hold their FULL counts.**
   `check-probes.py`: clean, 2,631 tracked files before, 2,644 after, the delta being
   exactly the 13 files of the `[LJ-1.293]` commit that landed mid-run (MEASURED,
   `git show --stat 2300777`). `check-agents-guard.py`: byte-identical output,
   `clean (18 guarded commit(s), 30 pre-guard)`, because `GUARD_HOMES` now judges
   history at BOTH homes. `check-rule-ids.py`: byte-identical,
   `clean (45 files, 153 lessons, 67 decisions)`. `check-live-territory.py`: clean,
   3 live agents, and it correctly sees the 35 staged renames.
3. **A mid-run commit is the only source of count drift.** The orchestrator committed
   `[LJ-1.293]` at 17:21:29, between my baseline (17:19:29) and after (17:32:48) passes.
   Every changed counter (+1 brief, +13 tracked files, +3 declared toolchain files,
   +1 cited code) traces to it and to a new sibling's task directory appearing on disk;
   none traces to the move. The environment snapshots in `baseline/env.txt` and
   `after/env.txt` record both HEADs.

## 1. The orchestrator correction, applied and recorded

The owner's correction of 2026-08-15, delivered mid-task:

1. **The out-of-repo-consumer exception for `dispatch_policy.py` is CANCELLED.** It moved
   to `scripts/dispatch/dispatch_policy.py` with `git mv`, beside its one tracked
   importer `check-dispatch-policy.py`. The brief's rule 2 is dead; the README states
   ONE placement rule.
2. **`.claude/skills/codex-dispatch/dispatch.py` was NOT edited.** The lines the owner
   must change are in section 7.
3. **`scripts/tests/test_dispatch_clock.py` was checked and updated**: its
   `sys.path.insert` at `:39` now points at `scripts/dispatch`. Suite-16 passes
   (exit 0, byte-identical counts).
4. **The README carries one paragraph naming the accepted breakage**, per the owner's
   second correction: option C stands, no shim, no resolver, and the README says where
   an old flat citation's basename lives now.

## 2. Baselines against post-move output

Harness: `agents/tasks/LJ-1-295/run-checks.sh` (the 20 python invocations `make check`
wires in, the no-Agda extras, and all 16 suites, each captured to stdout/stderr/exit).
NOT RUN, per the brief: `make check` itself, Agda, `reuse` (binary absent, MEASURED
`which reuse`), `typecheck` (names no script; INFERRED unaffected), `dd25-record`
(writes PLAN). The Agda-coupled `check-ratio.py`/`check-timing.py`/`deletion-test.py`
were compile-checked and import-checked only; full behavior INFERRED, not measured.

| checker | baseline | after | attribution |
|---|---|---|---|
| markers, lint, lint-agda, glossary, ledger, tree, fences, rules, taskindex, agentsguard, ruleids, buildmanifest, switch, unboundhyp, ledgerbrief | exit 0, byte-identical | same | identical |
| probes | clean (2631 tracked files) | clean (2644) | +13 = mid-run commit |
| liveterr | clean (0 staged, 3 live) | clean (35 staged, 3 live) | 35 = my staged renames |
| dispatchpolicy | OK, 594 briefs | OK, 595 briefs | mid-run commit |
| dd4 | 186 of 198 | 187 of 199 | mid-run commit |
| archivecited | 149 of 223 | 150 of 224 | mid-run commit |
| taskindex | 595 codes, 611 rows | 596, 612 | mid-run commit |
| buildmanifest | 508 declared | 511 declared | `[LJ-1.293]` toolchain runs |
| premises | exit 1, 14 briefs | exit 1, same list | pre-existing red, unchanged |
| devdocs | clean (6 subchecks) | **exit 1, 15 defects** | AGENTS.md old paths; section 6 |
| sourcesread | 607 lines | 608 | `LJ-1.297: no brief` on disk |
| suites 01-08, 12, 13, 16 | exit 0 | exit 0 | suites 06/07: hash-order noise and the checker printing its own NEW path in an ok-line |
| suites 09, 11, 14, 15 | exit 1 | exit 1 | the four pre-existing failures, unchanged in kind; 11 lists two new sibling `__pycache__` dirs, 14 tmp-path noise |
| NEW: test_scripts_layout | (did not exist) | 4 tests, OK | new machinery, section 5 |

**The four named gates, specifically** (the brief's abort criterion): probes 2,644
tracked files, NOT 55; agentsguard 18 guarded / 30 pre-guard, NOT 0; ruleids 45/153/67,
scanning the full recursive set (`rglob`, `[LJ-1.291]`'s repair); liveterr full tree.
`make -n check` resolves all 20 invocations (MEASURED); `make -n test` shows the 13
suites plus the new one; all 7 hook path lines and `commit-msg` resolve (MEASURED).

## 3. What the move was

35 files moved with `git mv` (33 `.py`, `agda-watchdog.sh`, `depmap-template.html`):
`gate/` 16, `dispatch/` 5 (including `dispatch_policy.py` per the correction),
`measure/` 6, `site/` 6 plus the template, `ops/` 1. Flat and unmoved: `agents_tree.py`,
`repo_root.py`, `README.md`, `tests/`, `git-hooks/`. No file resisted its group; the
migration map covered every file and the new `test_scripts_layout.py` pins the map to
the tree. There is no `misc/` bucket (C-43).

**The anchor repair, which is the real code change.** Every moved script that computes
ROOT (24 of them) carries a new stamped anchor: the group's own directory goes on
`sys.path` for bare-name siblings, and the SCRIPTS root, where `repo_root.py` and
`agents_tree.py` sit flat, is found by walking up from the file to `repo_root.py`
itself, refusing loudly when absent (C-43). No moved script counts directories, which
keeps `[LJ-1.291]`'s contract. `scripts/repo_root.py`'s docstring now documents both
stamped shapes. Intra-group couples needed no rewrite: `check-ratio.py` loads
`check-timing.py` self-relatively, `check-timing.py` loads `obligations.py`
self-relatively, `check-glossary.py` loads `lint-prose.py` from its own directory.
One exception was repaired by hand: `check-dev-docs.py` loaded `check-rule-ids.py` from
`ROOT / "scripts" / filename`, which is `[LJ-1.290]`'s defect 2 verbatim; it now loads
from its own directory, which no future move can break.

**The C-42 sweep found a fifth silent-degradation site** the chain had not named:
`agda-watchdog.sh` computed `ROOT` as `dirname $0`/.. . After the move that resolves to
`scripts/`, so the watchdog would have kept killing runaway agda while silently writing
its log to `scripts/_build/tools/` (MEASURED by reading the script; the failure itself
INFERRED, not run: it is a daemon). Repaired with a shell walk to `.git`, matching
`repo_root.py`'s marker and its loud refusal.

**Citations into edited scripts were re-derived, not just re-pathed** (C-40): 9
`file:line` citations in `dev/ledger.toml`, `dev/LESSONS.md`,
`dev/build-manifest.toml` and `lint-prose.py`'s comment now name the new path AND the
re-measured line (for example `scripts/measure/ledger.py:404-446` became
`:414-456`; `check-probes.py:20-23` and `ledger.py:50` and `:56` sit above the anchor
and did not move). `lint-agda.py`'s citation of `lint-prose.py:446` stays valid because
that file was moved but never edited. Same-line edits only; every edited dev document's
line count is asserted unchanged.

## 4. The two workflow edits, and the deploy

`.github/workflows/cloudflare.yml:43` and `.github/workflows/pages.yml:51` both now run
`python3 scripts/site/link-check.py _build/site` (MEASURED, both files edited in this
change). The two edits land together with the move, so no merge to `main` can run one
workflow against a path the other still expects.

## 5. `scripts/README.md`: one placement rule, and the breakage said aloud

Rewritten in place (642 lines to about 560; it remains the ONLY taxonomy, DD19). The
layout table comes first, then:

**THE ONE PLACEMENT RULE**: a module that another script imports lives in the
shallowest directory that contains every importer. `repo_root.py` and `agents_tree.py`
are flat BY THIS RULE (no shallower directory holds all their importers), not by
exception; a consumer outside this repository is not an importer for placement. The
table in the README names every couple and its resolution.

**The breakage paragraph** (owner's second correction): citations written before
LJ-1.295 name the flat layout, the basename of nothing changed, the owner ruled
option C on 2026-08-15 to accept the dangling reader pointers, there is no shim and no
resolver, and a reader who meets `scripts/foo.py` in an older brief or report should
look for `foo.py` under the subdirectories.

**C-48, answered with machinery, not a wish**: the README states that the GROUP choice
is review-only, and that two parts are mechanical, enforced by the NEW
`scripts/tests/test_scripts_layout.py` (wired into `make test` in the same change):
the directory set under `scripts/` is pinned (no `misc/` bucket can appear silently),
the flat `.py` set is pinned to the two cross-group modules, the README's layout table
must match every group directory member-for-member, and each flat module must have
importers in at least two groups, which is the placement rule checked by machine.

## 6. AGENTS.md: what the owner must change (DD19; I did not touch it)

**The brief said 8 lines with paths. MEASURED: 15 lines carry 9 distinct `scripts/*.py`
paths** (the brief missed `AGENTS.md:23`, `check-dd4-stated.py`). Every one now names a
path that does not exist, and `check-dev-docs.py`'s `agents-enforcers` subcheck reports
exactly these 15 (after-pass output, `after/devdocs.out`):

| line | old path | new path |
|---|---|---|
| :17 | `python3 scripts/rules.py --for <kind>` | `scripts/dispatch/rules.py` |
| :23 | `scripts/check-dd4-stated.py` | `scripts/gate/check-dd4-stated.py` |
| :49 | `scripts/check-agents-guard.py` | `scripts/gate/check-agents-guard.py` |
| :70 | `python3 scripts/lint-prose.py <files>` | `scripts/gate/lint-prose.py` |
| :71 | `python3 scripts/rules.py --for <kind>` | `scripts/dispatch/rules.py` |
| :74 | `python3 scripts/ledger.py --brief` | `scripts/measure/ledger.py` |
| :77 | `python3 scripts/lint-prose.py --fix` | `scripts/gate/lint-prose.py` |
| :96 | `scripts/rules.py` | `scripts/dispatch/rules.py` |
| :97 | `scripts/check-rule-ids.py` | `scripts/gate/check-rule-ids.py` |
| :98 | `scripts/dispatch_policy.py` | `scripts/dispatch/dispatch_policy.py` |
| :99 | `scripts/check-task-index.py` | `scripts/gate/check-task-index.py` |
| :100 | `scripts/ledger.py --check` | `scripts/measure/ledger.py` |
| :102 | `scripts/lint-prose.py` | `scripts/gate/lint-prose.py` |
| :111 | `scripts/ledger.py --brief` | `scripts/measure/ledger.py` |
| :143 | `scripts/check-probes.py` | `scripts/gate/check-probes.py` |

**Whether BARE NAMES keep the subcheck green: YES, and that is why I recommend against
them (MEASURED from the code).** The subcheck is
`scripts/gate/check-dev-docs.py:143` `SCRIPT_REF = re.compile(r"scripts/[A-Za-z0-9_./-]+\.py")`
applied at `check_agents_enforcers`. A bare name like `ledger.py` matches nothing, so
the subcheck returns an empty list and is green, but it then verifies NOTHING: the
enforcement-point contract in the table's third column would name checkers no machine
checks (C-48). The regex's character class already contains `/`, so a subdirectory path
such as `scripts/gate/check-probes.py` matches and is verified to exist. Full new paths
keep the subcheck green AND live. Bare names would decouple AGENTS.md from the layout
permanently, at the price of a vacuous gate; that trade is the owner's to rule, and
these are both of its sides.

## 7. The other owner-held lines (outside my territory, reported only)

* **`.claude/skills/codex-dispatch/dispatch.py`** (untracked, the orchestrator's tool):
  `:111` `_POLICY_DIR = str(ROOT / "scripts")` must become
  `str(ROOT / "scripts" / "dispatch")`; the import at `:124`
  (`import dispatch_policy as POLICY`) then works unchanged. Also `:2383`
  `rules_py = ROOT / "scripts" / "rules.py"` must become
  `ROOT / "scripts" / "dispatch" / "rules.py"`, and the reader-facing string at
  `:2400` names `scripts/rules.py`. Until `:111` and `:2383` change, the dispatcher
  falls back and refuses loudly (its own design), never silently.
* **`dev/PLAN.md`**: 20 lines carry stale flat paths (lines 76, 241, 254, 255, 265,
  410, 424, 497, 506, 507, 510, 513, 514, 515, 518, 519, 589, 643, 743, 943; 30
  occurrences). Four also carry ledger line numbers that my anchor edit shifted:
  `:241` and `:265` `404-446` to `414-456`, `:254` `404-407` to `414-417`; `:255`'s
  `:50` did not move. No gate resolves these; they are reader pointers.
* **`docs/README.md:30`** names `scripts/lint-prose.py`; the new path is
  `scripts/gate/lint-prose.py`.
* **`.gitignore:28`** names `scripts/check-probes.py` in a comment; the new path is
  `scripts/gate/check-probes.py`.
* **Frozen, correct as history, deliberately untouched**: `dev/JOURNAL.md` (7),
  `dev/memos/` (9), `agents/` (3,225 reader citations), `archive/` throughout.

## 8. Files that resisted their group

**None (MEASURED: the map covered all 37 files under `scripts/`, and the new layout
suite proves the tree matches the README table member-for-member).** The eight
ambiguous scripts `[LJ-1.290]` named all took their mapped group. `dispatch_policy.py`
moved into `dispatch/` under the owner's cancelled-exception correction, not under the
placement rule's pressure: its one tracked importer sits there.

## 9. DD4

This task writes no mathematics. Shape only: a reader CAN place a new script without
asking (one question, when does it run, answered by the table; an imported module by
the one rule, checked by the new suite), and the taxonomy survives the script count
doubling (a doubled tree adds rows to the same five groups; the pinned directory set
forces a SIXTH group to be a deliberate, reviewed edit to the suite, not a drift).

## 10. Negatives, marked

* MEASURED: no stale flat script path remains in `scripts/`, `Makefile`,
  `.github/workflows/`, `scripts/git-hooks/`, or the 11 editable `dev/` documents.
* MEASURED: `make -n check` and `make -n test` resolve every invocation; hook paths
  resolve; `check-probes.py --staged` is clean over the 35 staged renames.
* MEASURED: all 35 moves are staged as renames (`git status` R entries), so history
  follows.
* INFERRED, not measured: the deploy (runs only on merge to `main`; both workflow lines
  verified by reading), `typecheck` and `reuse` (no script path in either), and the
  Agda-coupled measurement tools' full behavior (compile and import verified only).
* INFERRED: `[LJ-1.290]`'s baselines were one day old (D-10); I re-derived every count
  I acted on, and two of the brief's own numbers moved: tracked files 2,425 to 2,631
  (then 2,644 mid-run), and AGENTS.md's "8 paths" is 15 lines / 9 distinct paths.

## 11. P-l, D-26

`[LJ-1.290]` tested its migration on a copy; this run executed on the tree itself. The
cure for that difference is that my baselines and after-passes were captured on THIS
tree, before and after, checker by checker, with environment snapshots pinning both
HEADs and every delta attributed. D-26 (a well-founded key needs generation data) does
not bear on directory layout, and I say so rather than pretend it does.

## ARCHIVE USED (DD18)

* `archive/dev/TASKS-archived.md:157`, the `L3.32-T122` row: a bulk move was right in
  the move and wrong in the CHECKLIST, and review caught it. TAKEN AS SHAPE: the cure
  here is per-checker before/after capture on the real tree, not a checklist of edited
  paths.
* `agents/tasks/LJ-1-290/lj-1.290-report.md`, read WHOLE (the brief's SCOPE): the
  layout, the placement analysis, the four named false-green sites, and the migration
  design this run executed.

## LITERATURE USED (DD18)

No mathematical literature bears on directory layout. WHY NOT applies to the whole
corpus.

## FILES THIS TASK WROTE

* `agents/tasks/LJ-1-295/lj-1.295-report.md`, this report, written early (C-22).
* `agents/tasks/LJ-1-295/run-checks.sh`, the harness.
* `agents/tasks/LJ-1-295/baseline/`, `after/`, the two captures with env snapshots.
* `scripts/`: 35 files moved into `gate/`, `dispatch/`, `measure/`, `site/`, `ops/`;
  24 anchors rewritten; `check-dev-docs.py` sibling load made self-relative;
  `agda-watchdog.sh` root walk; `repo_root.py` docstring; `scripts/README.md`
  rewritten; `scripts/tests/test_scripts_layout.py` new.
* `scripts/tests/`: 14 suites' path loads updated.
* `Makefile`: 29 path replacements plus the new suite in `make test`.
* `.github/workflows/cloudflare.yml`, `pages.yml`: one line each.
* `scripts/git-hooks/pre-commit` (7 lines), `commit-msg` (1 line).
* `dev/`: 97 path occurrences across 11 files, plus 9 re-measured line numbers.
* NOT touched: `AGENTS.md`, `CLAUDE.md`, `dev/PLAN.md`, `src/`, `.claude/`, `agents/`
  beyond this directory, `dev/JOURNAL.md`, `dev/memos/`, `docs/`, `archive/`.
