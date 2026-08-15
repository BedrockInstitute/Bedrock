# LJ-1.291 report: repair the hard-coded depth anchors in `scripts/`

STATUS: COMPLETE. 26 existing files repaired plus one new module; no file moved, renamed
or deleted under `scripts/`; nothing committed; the depth-test copies were deleted after
the demonstration, as the brief ordered.

## 0. The verdict

**26 scripts repaired. The depth test passes: the repaired `check-probes.py` reports
`clean (2388 tracked files ...)` from its home in `scripts/` and the SAME
`clean (2388 tracked files ...)` from one level deeper inside the repository, run
unchanged.** For contrast, the PRE-REPAIR gate copied to the same deeper place reports
`clean (2 tracked files ...)`, also exit 0: the silent false green this task exists to
remove, reproduced beside its cure (MEASURED, `depth-A-B-C.txt` and `depth-D-H.txt` in
this directory).

Every checker reproduces its baseline exit code, and every content difference in the
after-pass is attributed to the `LJ-1.293` dispatch landing BETWEEN the two passes
(MEASURED, section 6). No count changed because of the repair.

## 1. Premises re-derived (C-44)

* **24 files match `parent.parent`** (MEASURED, `grep -l parent.parent scripts/*.py | wc -l`).
  All 24 are ROOT computations (MEASURED, every match inspected): 22 assign `ROOT =`, and
  2 join a path directly (`scripts/dd25-record.py:28` to `dev/PLAN.md`,
  `scripts/dispatch_policy.py:140` to `dev/vendors.toml`, line numbers pre-edit). No
  unrelated use exists. The brief's count of 24 is CONFIRMED.
* **`scripts/check-probes.py:53` and `scripts/check-live-territory.py:68`** both read
  `ROOT = Path(__file__).resolve().parent.parent` (MEASURED, pre-edit). Both are gates
  (MEASURED, `Makefile:76` and `Makefile:87`).
* **`scripts/check-agents-guard.py:47`** held
  `GUARD_PATH = "scripts/check-agents-guard.py"` (MEASURED, pre-edit). Its anchors are the
  LITERAL path and the INHERITED CWD: `git log -- AGENTS.md` resolves its pathspec against
  the CWD. MEASURED: the pre-repair guard run from `scripts/` prints
  `clean (0 guarded commit(s), 0 pre-guard)` and exits 0, judging nothing
  (`depth-D-H.txt` section G). That is the silent false green the brief named, in the
  sharpest case, reproduced.
* **`scripts/check-rule-ids.py:308`** used `(ROOT / "scripts").glob("*.py")`,
  non-recursive (MEASURED, pre-edit). Repaired to `rglob` at
  `scripts/check-rule-ids.py:311`. The `scripts/tests/*.py` files that rglob also
  enumerates are DROPPED by `SERIES_SKIP_DIRS = {"tests"}` at
  `scripts/check-rule-ids.py:177`, applied at `:316`, so the scan set is unchanged today
  (MEASURED: byte-identical checker output).
* **The tracked count today is 2388** at the time of the depth test (MEASURED,
  `git ls-files | wc -l`; 2386 at baseline, before the orchestrator's mid-run commit).
  The brief's 2369 and [LJ-1.290]'s 2425 are both stale; the defect demonstration does
  not depend on the value.
* **`dispatch_policy.py` and `agents_tree.py` keep their import surface**: no name, path
  or signature moved. MEASURED: the dispatcher's own import shape
  (`sys.path.insert(0, ROOT / "scripts")` then `import dispatch_policy`) still yields
  `CONFIG_PATH = <root>/dev/vendors.toml` and `agents_tree.ROOT = <root>`, and
  `default_harness()` still answers (simulation in the session log;
  `scripts/tests/test_dispatch_clock.py` and `test_agents_tree.py` outputs byte-identical).

## 2. The shared anchor: where it lives and why

* **Helper**: one new module, `scripts/repo_root.py`: one function
  `find_root(start=None)` at `:48` and one constant `MARKER = ".git"` at `:45`. Every
  converted script carries the same three-line anchor, for example
  `scripts/check-probes.py:55-58`: put `scripts/` on `sys.path`, import `find_root`,
  call it with `__file__`.
* **Marker**: `.git`, not `AGENTS.md`, for three measured reasons. (1) Every gate here
  runs git or reads the tracked tree, so `.git` presence is the exact precondition for
  the script to function at all. (2) `.git` is a FILE in a worktree, and six live
  worktrees sit under `.claude/worktrees/` (MEASURED, `find`), so the test is
  `exists()`, never `is_dir()`. (3) MEASURED by `find`: no other `.git` exists under
  the repository, so a walk from any tracked script stops at the true root and cannot
  stop early.
* **Refusal, not fallback** (C-43, C-48): a walk that reaches the top of the filesystem
  without a marker raises `FileNotFoundError` (`scripts/repo_root.py:59`). MEASURED:
  `find_root('/tmp')` refuses with a named error and no guess (`depth-D-H.txt` section
  H); a copied gate whose helper is missing refuses with `ModuleNotFoundError`, exit 1
  (`depth-D-H.txt` section D). No fallback path exists in the module (MEASURED, read).
* **Why this is not a second home (DD19)**: no module in this repository owns "find the
  repository root". `agents_tree.py` owns the shape of `agents/tasks/`;
  `dispatch_policy.py` owns the dispatch switch and the vendor floor. Root-finding never
  had any home, which IS the defect: 24 private copies. `scripts/repo_root.py` is its
  first and only home. The three-line anchor in each script is machinery that names no
  marker and owns no walk, so nothing canonical lives twice.

## 3. The repair, file by file

26 existing files edited, all under `scripts/`:

* 24 depth anchors converted to `ROOT = find_root(__file__)` (line numbers post-edit):
  `agents_tree.py:61`, `check-archive-cited.py:55`, `check-build-manifest.py:35`,
  `check-dd25-review-named.py:91`, `check-dd4-stated.py:67`, `check-dev-docs.py:90`,
  `check-dispatch-policy.py:70`, `check-fences.py:44`, `check-live-territory.py:73`,
  `check-premises-stated.py:85`, `check-probes.py:58`, `check-ratio.py:72`,
  `check-rule-ids.py:61`, `check-sources-read.py:50`, `check-task-index.py:45`,
  `check-timing.py:61`, `check-tree.py:86`, `check-unbound-hyp.py:53`,
  `dd25-record.py:33` (`PLAN = find_root(__file__) / "dev" / "PLAN.md"`),
  `deletion-test.py`, `dispatch_policy.py`
  (`CONFIG_PATH = find_root(__file__) / "dev" / "vendors.toml"`), `ledger.py`,
  `obligations.py`, `rules.py`.
* `check-agents-guard.py:46-71`: marker-walk ROOT; every git call runs `cwd=ROOT`, so
  the `AGENTS.md` pathspec resolves from the root and never from the caller's seat; the
  self-anchor is DERIVED (`Path(__file__).resolve().relative_to(ROOT).as_posix()`) with
  the historical literal `scripts/check-agents-guard.py` retained in `GUARD_HOMES`
  (`:63-67`), so a future move cannot silently unjudge history. That is [LJ-1.290]
  Result 2's cure. Today the tuple dedupes to exactly the old literal, so behavior is
  unchanged (MEASURED, byte-identical output).
* `check-rule-ids.py:311`: `.glob("*.py")` to `.rglob("*.py")`.
* Plus: `scripts/repo_root.py` written, and one row for it added to `scripts/README.md`
  beside `agents_tree.py`'s section.
* All 34 scripts compile (MEASURED, `.venv/bin/python -m py_compile` over
  `scripts/*.py`). `grep parent.parent scripts/*.py` matches ONE line after the repair:
  the docstring in `repo_root.py` that documents the retired defect (MEASURED).
* `make -n check` resolves all 20 script invocations (MEASURED).

## 4. Baselines against post-edit output

Harness: `agents/tasks/LJ-1-291/run-checks.sh`, run twice (baseline 16:55:22, after
16:58:56). It captures the 20 python checkers wired into `make check` (`Makefile:36`),
3 edited-but-ungated scripts that run without Agda, all 16 test suites, and an
environment snapshot (tracked count, HEAD, porcelain, sha256 of every `.md` under
`agents/tasks/`, live processes).

**Exit codes: 39 of 39 identical, checker for checker and suite for suite (MEASURED,
byte compare of every `.exit`).**

**Byte-identical stdout and stderr**: markers, lint, lint-agda, glossary, ledger, tree,
fences, ruleids-a, ruleids-b, devdocs, agentsguard, dd25, premises, buildmanifest,
sources-read, unbound-hyp, dd25-record, and 12 of 16 suites (01-06, 08-10, 12-15).
`check-rule-ids.py` re-run after the README row and the new module: still byte-identical
(MEASURED). `lint-prose.py --check` on this report and harness: exit 0, no em dash.

**Content differences, every one attributed (MEASURED)**: the orchestrator committed
`8711a6f` at 16:56:37, between the two passes, adding
`agents/tasks/LJ-1-293/LJ-1.293.md`, its report skeleton and one `dev/PLAN.md` row
(`git show --stat 8711a6f`), and dispatched LJ-1.293 live:

| checker | baseline | after | cause |
|---|---|---|---|
| probes | clean (2386 tracked files | clean (2388 tracked files | +2 tracked files, the LJ-1.293 commit |
| liveterritory | 2 live agent(s) | 3 live agent(s) | LJ-1.293 registered live |
| taskindex | 591 cited codes | 592 cited codes | the new PLAN row |
| dispatchpolicy | 590 brief(s) read | 591 brief(s) read | the new brief on disk |
| dd4 | 182 of 194 brief(s) | 183 of 195 brief(s) | the new brief states DD4 |
| archivecited | 145 of 218 brief(s) | 146 of 219 brief(s) | the new brief cites an archive |
| suite-16 | 591 cited codes | 592 cited codes | the new PLAN row |
| suite-07 | `Ran 20 tests in 0.006s` | `0.007s` | timing noise |
| suite-11 | tmp paths in the failure text | different tmp paths | tmpdir names; the failure is pre-existing and identical in kind |
| suite-16 | set printed `{T101, T1, T88}` | `{T88, T1, T101}` | hash-order noise |

The 73-item drift list in `archivecited.err` is byte-identical apart from the counter
line (MEASURED, `diff` of the tail). No difference traces to the repair: the six
drifted counters read the git index, the registry, PLAN rows and brief files on disk,
and the repair touches none of those.

**PRE-EXISTING RED, captured before any edit of mine (reported per the abort
criterion, not repaired)**: `check-premises-stated.py` exits 1 with 13 brief(s) carrying
a trigger and no declared premises (baseline/premises.err). Four suites exit 1:
`test_agents_tree`, `test_premises_stated`, `test_ratio_baseline`, `test_ratio_noise`,
the same four [LJ-1.290] measured failing identically before and after its migration
copy.

**NOT RUN**: `typecheck` (brief forbids Agda) and `reuse` (binary absent, MEASURED,
`which reuse`). INFERRED unaffected: `typecheck` names no script, and `REUSE.toml`
puts `scripts/**` under the default license bucket. `make check` itself was not run;
the orchestrator runs it.

## 5. The depth test

All outputs kept in `agents/tasks/LJ-1-291/depth-A-B-C.txt` and `depth-D-H.txt`; the
copied gates themselves were deleted afterwards, as the brief ordered.

* **A, fresh reference from `scripts/`**: probes `clean (2388 tracked files ...)`;
  guard `clean (18 guarded commit(s), 30 pre-guard)`; rule-ids
  `clean (45 files, 153 lessons, 67 decisions)`.
* **B, the old defect**: the PRE-REPAIR `check-probes.py` (from commit `92f558f`)
  copied one level deeper, run unchanged: `clean (2 tracked files ...)`, exit 0. It
  guarded the two files the orchestrator had just committed into
  `agents/tasks/LJ-1-291/` and called the tree clean. MEASURED.
* **C, repaired `check-rule-ids.py` one level deeper** with `agents_tree.py` and
  `repo_root.py` beside it: `clean (45 files, 153 lessons, 67 decisions)`, identical to
  the original. MEASURED.
* **D, refusal**: a repaired gate copied deeper WITHOUT the helper refuses with
  `ModuleNotFoundError`, exit 1. Loud, never a guess. MEASURED.
* **E, the depth test proper**: repaired `check-probes.py` one level deeper, run
  unchanged: `clean (2388 tracked files ...)`, the SAME count as the original.
  Repaired `check-agents-guard.py` one level deeper: `clean (18 guarded commit(s),
  30 pre-guard)`, the SAME counts as the original. MEASURED.
* **F, cwd independence**: the repaired guard run from `scripts/`: the SAME
  18/30 counts. The old code from the same seat said `0 guarded commit(s), 0 pre-guard`
  (section G). MEASURED.
* **H, the refusal contract**: `find_root('/tmp')` raises `FileNotFoundError` naming
  the marker and the start. MEASURED.

## 6. Scripts that could not use the anchor

**None of the 24 failed to convert** (MEASURED: all compile; every one that runs without
Agda is byte-identical; the three Agda-coupled ones, `check-ratio.py`, `check-timing.py`
and `deletion-test.py`, compile and import with `ROOT` resolving to the true root,
MEASURED by import; their full behavior is INFERRED, not measured, because the brief
forbids running Agda).

**The C-42 sweep found cousin anchors the brief did not name, reported and left
untouched** because they compute no root and the repair of a CWD anchor is a separate
ruling:

* `scripts/lint-agda.py:366`: `glob.glob("src/**/*.lagda.md")` relative to the CWD.
  MEASURED: run from `scripts/` it scans nothing and exits 0, a silent false green of
  the same species with a different trigger (the caller's seat, not the file's depth).
* `scripts/lint-prose.py:433`: no-argument mode runs `git ls-files` in the inherited
  CWD. MEASURED: run from `scripts/` it exits 0 over a near-empty set.
* `scripts/check-glossary.py:38-40,286`: relative glossary paths plus inherited-cwd
  git. MEASURED: run from `scripts/` it fails LOUDLY (exit 2, `glossary not found`), so
  it is fail-closed, not a false green.
* `weave-i18n.py`, `extract-types.py`, `gen-depmap.py`, `render-site.py`,
  `link-check.py`, `i18n_markers.py` take their targets from argv or their own
  directory and compute no root. Nothing to convert. MEASURED, read.

## 7. DD4

**A new script does NOT get the anchor for free: it must copy the same three lines, and
today NO mechanical enforcement point exists**; the named review step is this task's
depth test, and a one-line gate (refuse any `parent.parent` root under `scripts/` in a
new `scripts/tests/` suite) would give it one. That is for the orchestrator to wire;
this brief's write scope allowed edits to existing files only. The task still writes
the walk once, in `scripts/repo_root.py`; the 26 anchors are one stamped shape, not 26
judgements.

## ARCHIVE USED (DD18)

* `archive/dev/TASKS-archived.md:157`, the `L3.32-T122` row: a sixteen-master archival
  move was right in the move and wrong in its CHECKLIST, and review caught the range
  defect. TAKEN AS SHAPE, never as a claim: a bulk repair is verified by running the
  thing repaired at two depths, not by a list of edited paths.
* `agents/tasks/LJ-1-290/lj-1.290-report.md`, read WHOLE first as the SCOPE section
  ordered: the depth finding (its section 5), the three named false-green sites
  (Results 1 and 2, defect 4), and its Step 1 recommendation, which is this task. The
  taxonomy and migration work are NOT this task and were not touched.

## LITERATURE USED (DD18)

No mathematical literature bears on a repository path anchor. WHY NOT applies to the
whole corpus.

## FILES THIS TASK WROTE

* `agents/tasks/LJ-1-291/lj-1.291-report.md`, this report, written early and filled
  incrementally (C-22).
* `agents/tasks/LJ-1-291/run-checks.sh`, the baseline/after harness.
* `agents/tasks/LJ-1-291/baseline/` and `agents/tasks/LJ-1-291/after/`, the two
  captures, with `env.txt` snapshots each.
* `agents/tasks/LJ-1-291/depth-A-B-C.txt`, `depth-D-H.txt`, the depth-test transcripts.
* Under `scripts/`: `repo_root.py` new; 26 existing files edited as listed in section 3;
  one row added to `scripts/README.md`. The depth-test copies were deleted.
