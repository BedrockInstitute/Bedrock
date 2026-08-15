# LJ-1.290 report: sort `scripts/` into subdirectories

STATUS: COMPLETE. No file under `scripts/` moved, was renamed, or was deleted. The whole
migration ran against copies.

## 0. THE VERDICT, in three lines

1. **THE MOVE IS SAFE AND I TESTED IT.** 24 of 25 checkers and 16 of 16 test suites give
   byte-identical exit codes and output line counts before and after. The one difference is
   a silent false-green I found, and it needs a hand patch.
2. **THE MOVE DOES NOT FIX THE DEFECT IT EXPOSES.** 24 scripts hard-code their own DEPTH.
   The move increments that number. The next reorganisation pays the same bill again.
3. **SO I RECOMMEND SPLITTING IT.** Do the depth repair FIRST. It costs ZERO citations, it
   carries all the engineering value, and I measured it working. Then rule on the move,
   whose remaining cost is 3,225 reader citations and two document rewrites.

## 1. Blast radius, re-derived (C-44)

Pattern: `scripts/[A-Za-z0-9_-]+\.(py|sh|html)`. It matches a top-level script path and does
NOT match `scripts/tests/test_*.py`.

| where | brief said | I measured | note |
|---|---:|---:|---|
| `agents/` | 3,123 | **3,225** in 778 files | frozen records |
| `dev/` | 134 | **142** | see the split below |
| `Makefile` | 26 | **26 invocations**, 46 tokens | see the split below |
| `.github/workflows/` | 2 | **2** | `pages.yml:51`, `cloudflare.yml:43` |
| `.claude/` | thousands | **31,264** | untracked, out of scope |
| `scripts/` itself | not given | **112** | self-references |
| `docs/`, `src/`, `archive/`, root `*.md` | not given | **62** | not in the brief's table |

**Every class the brief named is LOW.** The direction matters: the citation cost is larger
than the brief priced it.

**THE `dev/` 142 IS NOT ALL REWRITABLE, and the brief's word "live" hides that.**
MEASURED: `dev/JOURNAL.md` holds **7** and `dev/memos/` holds **9**. Both are DATED RECORDS.
`scripts/check-rule-ids.py:176-183` already exempts both trees for that exact reason, in its
own words: a dated entry is true of its own moment and nobody rewrites it. So **16 of the
142 belong to the frozen class, not the live one**, and only **126** are rewritable.

**THE `Makefile` 26 SPLITS FOUR WAYS.** 26 recipe lines invoke a top-level script
(`Makefile:52` to `:213`); 13 recipe lines invoke a test (`:230-242`); 2 lines name
`scripts/git-hooks` (`:261-262`); 6 COMMENT lines name a script without running it (`:72`,
`:85`, `:99`, `:130`, `:194`, `:196`). A migration must edit all four classes.

**A PRE-EXISTING DANGLING CITATION, MEASURED.** `dev/memos/L3.32-context-layering.md:138`
cites `scripts/check-rules.py`. That file does not exist and has not for some time. So the
repository ALREADY carries a dead script citation in a dated record and nothing broke. That
is one data point, not a licence for 3,225.

## 2. THE CATEGORIES, from reading the scripts

I opened all 34 `.py` files, `agda-watchdog.sh`, `scripts/README.md` (642 lines) and both
git hooks. The grouping question a reader actually arrives with is **when does this run and
who runs it**, not what topic it is about, because the same topic spans a gate and a build
step: `weave-i18n.py --check` is in `make check` (`Makefile:58`) and `weave-i18n.py --gen`
builds the site (`Makefile:202`).

| group | why it exists | members |
|---|---|---|
| `scripts/` (flat) | the modules another script IMPORTS BY NAME across groups | `agents_tree.py`, `dispatch_policy.py` |
| `scripts/gate/` (16) | runs inside `make check` or a git hook; a red one stops a commit | `check-agents-guard`, `check-archive-cited`, `check-build-manifest`, `check-dd25-review-named`, `check-dd4-stated`, `check-dev-docs`, `check-fences`, `check-glossary`, `check-live-territory`, `check-premises-stated`, `check-probes`, `check-rule-ids`, `check-task-index`, `check-tree`, `lint-agda`, `lint-prose` |
| `scripts/dispatch/` (4) | everything about running and auditing a dispatch | `check-dispatch-policy`, `check-sources-read`, `dd25-record`, `rules` |
| `scripts/measure/` (6) | costs seconds to minutes, runs Agda, or reports a number; never a gate | `check-ratio`, `check-timing`, `check-unbound-hyp`, `deletion-test`, `ledger`, `obligations` |
| `scripts/site/` (5 + 1 asset) | the publishing pipeline and the deploy | `extract-types`, `gen-depmap`, `i18n_markers`, `link-check`, `render-site`, `weave-i18n`, `depmap-template.html` |
| `scripts/ops/` (1) | machine safety | `agda-watchdog.sh` |

Unchanged: `scripts/README.md`, `scripts/tests/`, `scripts/git-hooks/`.

### THE PLACEMENT RULE FOR A SHARED MODULE, and it is mechanical

**A module that another script imports lives in the SHALLOWEST directory that contains
every importer.** No judgement call is needed, and it decides every case in this tree:

| module | importers | lands in |
|---|---|---|
| `agents_tree.py` | 6, in `gate/` AND `dispatch/` | `scripts/` (flat) |
| `dispatch_policy.py` | 1 in `dispatch/`, plus `.claude/.../dispatch.py:112-124` | `scripts/` (flat) |
| `i18n_markers.py` | 3, all in `site/` | `site/` |
| `ledger.py` | `check-ratio`, `deletion-test` | `measure/` |
| `check-timing.py` | `check-ratio` | `measure/` |
| `obligations.py` | `check-timing` | `measure/` |
| `lint-prose.py` | `check-glossary` | `gate/` |
| `check-rule-ids.py` | `check-dev-docs` | `gate/` |

**THIS RULE IS WHY THE MAPPING IS CHEAP.** All six load-a-sibling-by-filename couples land
INSIDE one group, so not one of those literals needs rewriting. And keeping
`dispatch_policy.py` flat means **`.claude/` needs NO edit at all**, which removes the
out-of-scope change the brief expected.

### DD4 (shape only, no mathematics here)

The taxonomy survives a doubling: a new script is placed by one question ("when does it
run?"), and an imported module is placed by a rule a test can check. A reader places a new
script without asking. The one weak group is `ops/`, which holds a single file today.

### THE AMBIGUOUS SCRIPTS, named rather than forced (8 of 34, 24 percent)

1. **`ledger.py`.** `--check` gates (`Makefile:64`); `--brief` is the project's ONLY
   admissible standing figure. I put it in `measure/`. A reader hunting "what gates a
   commit" will not find it. GENUINELY AMBIGUOUS.
2. **`weave-i18n.py`.** Gates at `Makefile:58` and `git-hooks/pre-commit:41`; builds at
   `Makefile:202`. I put it in `site/`. GENUINELY AMBIGUOUS.
3. **`rules.py`.** `--check` gates (`Makefile:124`), but `AGENTS.md:17` calls it the first
   command an agent runs. I put it in `dispatch/`. GENUINELY AMBIGUOUS.
4. **`check-dispatch-policy.py`.** A GATE about DISPATCH. I put it in `dispatch/` because
   its subject decides more for a reader than its schedule. AMBIGUOUS.
5. **`check-sources-read.py`.** An audit aid that exits 0 always. `dispatch/` by subject,
   an advisory by behaviour. AMBIGUOUS.
6. **`check-ratio.py` and `check-timing.py`.** Named `check-` like the gates, and both are
   MEASUREMENTS that run Agda. **The NAME lies about the category.** That is evidence the
   flat directory misleads today, and a subdirectory does not repair a wrong name.
7. **`check-unbound-hyp.py`.** Advisory static analysis over `src/`. It fits `measure/` only
   loosely; it measures nothing in seconds. AMBIGUOUS.
8. **`link-check.py`.** The ONLY script the deploy runs. `site/` by subject, but its real
   category is "CI", and this taxonomy has no CI group because it would hold one file.

**No `misc/` bucket exists and the migration REFUSES to run with an unmapped file** (C-43).

### DEAD SCRIPTS: none, and I state the negative as MEASURED

**MEASURED: no script has zero callers.** Nine have no `make` target and no hook, and each
has a named caller elsewhere: `agents_tree.py` (6 importers), `dispatch_policy.py` (imported
by `check-dispatch-policy.py` and by `.claude/.../dispatch.py:124`), `i18n_markers.py` (3
importers), `obligations.py` (imported by `check-timing.py` and by
`scripts/tests/test_obligations.py`), `link-check.py` (the two workflows), `check-timing.py`
(imported by `check-ratio.py`), `check-sources-read.py`, `check-unbound-hyp.py`,
`dd25-record.py` and `agda-watchdog.sh` (each run by hand, each documented). **INFERRED, not
measured:** that the four hand-run tools are still WANTED. Nothing mechanical records a
last-run date, so I cannot measure use, only reachability.

## 3. THE PER-CLASS CITATION HANDLING

### `.github/workflows/` (2). THE DEPLOY.

Both lines run `python3 scripts/link-check.py _build/site`. Both become
`scripts/site/link-check.py`. VERIFIED on the copy: both rewritten, and the target resolves.

**IF ONLY ONE OF THE TWO IS EDITED, THIS HAPPENS.** The two workflows are separate jobs on
the same trigger. `pages.yml` publishes to GitHub Pages and `cloudflare.yml` publishes to
Cloudflare. Editing one leaves the other running a path that does not exist, so its step
exits non-zero and that job fails on merge to `main`. **The failure is per-target, so ONE
site deploys and the other does not, and the repository is then serving two different
versions of the book.** That is worse than both failing, because a red job is noticed and a
stale mirror is not. The two edits are one commit or they are a defect.

### `Makefile` (26 invocations + 13 tests + 2 hook lines + 6 comments)

Mechanical. VERIFIED on the copy with `make -n check`: **all 20 `check:` invocations resolve
to a real migrated path.** The 6 comment lines are rewritten too, because a comment naming a
dead path is the same dangling pointer with a smaller audience.

### `dev/` (126 live, 16 frozen)

The 126 in `dev/*.md` and `dev/*.toml` are rewritten. **`dev/JOURNAL.md` (7) and
`dev/memos/` (9) are NOT**, because `check-rule-ids.py:176-183` already declares both trees
dated records. Rewriting them would contradict the rule the repository states about itself.
So **16 dev citations join the frozen set**, and the brief's "134 live documents,
rewritable" is wrong in kind for 16 of them.

### `.claude/` (31,264). NOTHING FOR YOU TO CHANGE.

`.claude/skills/codex-dispatch/dispatch.py:111-113` inserts `<repo>/scripts` on `sys.path`
and imports `dispatch_policy` at `:124`; `:2383` reads `ROOT / "scripts" / "rules.py"`.

**Under this mapping `dispatch_policy.py` DOES NOT MOVE, so `:111-124` needs no edit.** The
one required change is `:2383`, `ROOT / "scripts" / "rules.py"` becomes
`ROOT / "scripts" / "dispatch" / "rules.py"`. That is ONE LINE. I did not change it.
The remaining 31,000-odd references are session logs, which are records.

### `agents/` (3,225). THE DECISION. Four options, priced.

**FIRST, WHAT ACTUALLY CONSUMES THEM. MEASURED: nothing mechanical does.**
`check-rule-ids.py:183` sets `SERIES_SKIP_TREES = ("agents/",)`; `lint-prose.py:446` drops
`agents/`; no checker resolves a script path found inside `agents/`. **So the breakage is
entirely a READER cost and never a gate cost.** That single measurement changes the price.

**Option A: a mapping table in `scripts/README.md`.**
Price: about 40 lines, written once. An enforcement point EXISTS and is cheap: a subcheck in
`check-dev-docs.py` (about 15 lines) asserting every table row resolves and every
`scripts/**/*.py` appears. Weakness: the reader must know the table is there.

**Option B: thin shims at the 34 old paths.**
Price: 34 permanent files, about 100 lines. Every one of the 3,225 citations still RUNS.
**REFUTED BY ITS OWN GOAL:** the directory then holds 34 shims PLUS 6 subdirectories, so it
is more cluttered than it is today. It also doubles what `check-probes.py`,
`check-rule-ids.py` and the `agents-enforcers` gate see. C-43 names this shape exactly.
DO NOT DO THIS.

**Option C: accept the breakage, say so plainly.**
Price: 3,225 dangling reader pointers. Evidence on the marginal harm is one data point:
`dev/memos/L3.32-context-layering.md:138` already cites a script that does not exist and
nothing broke. One is not 3,225.

**Option D, which I recommend: make the NAME resolve, not the path.**
Every one of the 3,225 citations contains the BASENAME, and **the basename does not change**.
C-41 asks that a retired name carry its home at every citation. You cannot write the home
into 3,225 frozen records, but you can make the name resolve from one command. Price: a
`scripts/where.py` resolver (about 30 lines), the Option A table, and the Option A subcheck.
Total about 85 lines with a real enforcement point (C-48). **It is the smallest thing that
satisfies C-41 without editing one frozen record.**

## 4. THE MIGRATION SCRIPT AND WHAT I TESTED

`agents/tasks/LJ-1-290/migrate-scripts.py`. Modes: `--plan`, `--naive` (move only, to
measure carelessness), `--apply`, `--root DIR`, `--no-git`. **`--apply` exits 3, never 0**,
because three steps are not mechanical and a migration that says "done" over open work is
the escape hatch C-43 names.

### THE TEST BED

A runnable shadow of the whole repository (2,425 tracked files, its own throwaway git
history) in the session scratchpad, so no nested `.git` lands under `agents/`. The
deliverable copy the brief asked for is at `agents/tasks/LJ-1-290/copy/`, holding the
MIGRATED `scripts/`, `Makefile` and both workflows; the pristine original is `scripts/`
itself, one level up, so a reviewer diffs the two directly. Harness:
`agents/tasks/LJ-1-290/run-checkers.sh`.

### RESULT 1: THE NAIVE MOVE PRODUCES TWO SILENT FALSE-GREENS

`git mv` only, no code repair. Most checkers crash loudly. **Two do not.**

| checker | baseline | after a naive move |
|---|---|---|
| `check-probes.py --check` | exit 0, `clean (2425 tracked files ...)` | **exit 0**, `clean (55 tracked files ...)` |
| `check-live-territory.py --check` | exit 0, `clean (2425 tracked files ...)` | **exit 0**, `clean (55 tracked files ...)` |

Cause: both run `git ls-files` with `cwd=ROOT`, and `ROOT` became `<repo>/scripts`. **Two
NEVER-COMMIT gates stopped guarding 2,370 files and reported clean.** The only signal is a
count in a message nobody reads. That is C-48 in the machinery itself.

### RESULT 2: A THIRD SILENT FALSE-GREEN, IN THE AGENTS.md GUARD

`scripts/check-agents-guard.py:47` holds `GUARD_PATH = "scripts/check-agents-guard.py"`. The
history audit judges only a commit whose OWN tree carries that path. MEASURED on the copy:
baseline exit 1 (a real finding); after a plain literal rewrite, **exit 0 with
`0 guarded commit(s), 1 pre-guard`**. **The whole history stops being judged and nothing says
so.** The cure is to accept BOTH homes. That is C-41 inside a checker. The migration writes
the constant and REFUSES to rewrite the probe, because a regex that edits control flow is
the shape a wrong choice hides in.

### RESULT 3: THE FULL MIGRATION REPRODUCES THE BASELINE

25 checkers and 16 test suites, run in the shadow before and after.

* **Checkers: 24 of 25 identical** in exit code and output line count. The single difference
  is `check-agents-guard.py`, which is Result 2 waiting for its hand patch.
* **Test suites: 16 of 16 identical.** Four fail in BOTH trees for reasons that predate the
  move (`test_ratio_baseline`, `test_agents_tree`, `test_premises_stated`,
  `test_ratio_noise`), and they fail the same way with the same message.
* `make -n check`: all 20 invocations resolve.
* Both workflow lines resolve. All 7 hook paths resolve. All 9 AGENTS.md enforcer paths
  resolve, which is what the `agents-enforcers` gate demands.

### WHAT I COULD NOT TEST

* **`agda` and `make check`.** Forbidden by the brief. So `typecheck` and `reuse` are
  UNTESTED. `typecheck` names no script and `reuse` runs an external tool over `REUSE.toml`,
  which carries no `scripts/` path (`REUSE.toml:26-30` puts `scripts/**` under the default),
  so INFERRED, not measured: neither is affected.
* **`make site`, `make gen`, `make types`.** They run Agda. `render-site.py`,
  `extract-types.py` and `gen-depmap.py` are therefore INFERRED-only. Their coupling is
  narrow and I read each: `gen-depmap.py:172` opens `depmap-template.html` from its own
  directory (the template moves with it), and `render-site.py:31` and `gen-depmap.py:23`
  insert their own directory to import `i18n_markers`, which moves with them into `site/`.
* **The deploy.** It runs only on merge to `main`. I verified the path resolves; I did not
  run the workflow.
* **`.claude/`.** Out of scope, unread beyond the three lines the brief named.

### FOUR DEFECTS MY OWN MIGRATION HAD, AND ALL FOUR CAME FROM MEASURING

Recorded because they are the price of doing this by hand rather than by test.

1. Raising `sys.path` unconditionally broke `deletion-test.py` and `check-ratio.py`, which
   import `ledger` from their OWN group: `No module named 'ledger'`. The insert must follow
   the module, not the depth.
2. `check-dev-docs.py` loads its sibling from `ROOT / "scripts" / filename`, which is the
   scripts root and NOT its own directory, so an intra-group couple still broke. Cured by
   making it self-relative, which no future move can break again.
3. **All 13 suites in `make test` broke on the first pass.** A suite does not write
   `scripts/check-tree.py`; it writes the basename as a path COMPONENT
   (`ROOT / "scripts" / "check-dev-docs.py"`). The citation rewriter matched none of them.
4. `check-rule-ids.py:308` globs `(ROOT / "scripts").glob("*.py")`, which is NOT recursive.
   After a move it would silently scan almost nothing and still exit 0. Changed to `rglob`.

**Defect 4 is the same species as Results 1 and 2.** Three of the four silent-degradation
sites in this repository are in the checkers themselves.

## 5. DD13: PRICED FROM THE REWRITE SIDE

The question is not "how do we move these 34 files". It is what `scripts/` would look like
laid out fresh today.

**Fresh today, no script would compute the repository root by counting `..`.** It would find
a MARKER. Today 24 files write `ROOT = Path(__file__).resolve().parent.parent`, and that one
expression is the entire reason a move is a code change instead of a rename. It also caused
all three silent false-greens.

**THE DIFFERENCE IS NOT THE DIRECTORY STRUCTURE. IT IS THE DEPTH COUPLING.** And the move
does not remove the coupling; it increments the number. A second reorganisation pays the
same bill again, and re-runs the same three false-green risks.

**I MEASURED THE ALTERNATIVE rather than asserting it (P-l).** I wrote a marker-walk root,
converted `check-tree.py`, `check-probes.py` and `check-fences.py` to use it, and ran them at
BOTH depths:

| script | flat | one level deeper, NO edit |
|---|---|---|
| `check-tree.py` | exit 0, `clean (96 masters ...)` | exit 0, `clean (96 masters ...)` |
| `check-probes.py` | exit 0, `clean (2425 tracked files ...)` | exit 0, `clean (2425 tracked files ...)` |
| `check-fences.py` | exit 0, `clean (96 masters ...)` | exit 0, `clean (96 masters ...)` |

Identical output at both depths, and the tracked count stays 2,425 rather than collapsing to
55. HONEST LIMIT: the prototype still needs `_root` reachable on `sys.path`, which is one
uniform line per script. Inlining the three-line walk removes even that.

**THE COMPARISON.** Both changes touch the same 24 files once. The increment buys one
tidier directory and leaves the coupling. The marker buys a directory layout that is free to
change forever and removes the cause of three measured false-greens. **Same edit, same
files, strictly more value, and ZERO citations move.**

## 6. WHAT THE OWNER MUST RULE, AND WHAT IS DD19-GATED

1. **`AGENTS.md` names 15 script paths, 9 distinct** (`AGENTS.md:17` to `:143`).
   `check-dev-docs.py`'s `agents-enforcers` subcheck runs INSIDE `make check` and fails when
   a named `scripts/*.py` does not exist. **So the move cannot land without an `AGENTS.md`
   edit, and an `AGENTS.md` edit cannot land without the owner's ruling and a dated
   `AGENTS-diff-approved:` trailer (DD19).** The move and the rulebook edit are ONE COMMIT
   or the gate is red between them.
2. **`scripts/README.md` is 642 lines and is the ONLY declared taxonomy** (read whole). It is
   organised by pipeline and topic, with no directory grouping. After the move it describes a
   layout that does not exist. It must be rewritten in the same commit, or the repository
   holds two taxonomies and DD19 is broken.
3. **The `check-agents-guard.py` probe patch** (Result 2). Three lines, by hand.

## 7. RECOMMENDATION

**PROCEED, BUT NOT AS ONE MOVE. SPLIT IT.**

**STEP 1, and I recommend it whatever is ruled on step 2: REMOVE THE DEPTH COUPLING.**
Convert the 24 hard-coded `parent.parent`s to a marker walk. **ZERO citations change. ZERO
frozen records break. No `AGENTS.md` edit. No `scripts/README.md` rewrite. No deploy risk.**
`make check` proves it, and I measured three scripts working at two depths. This step carries
all the engineering value the owner's instruction is reaching for, and it is what makes the
three silent false-greens impossible rather than merely repaired once.

**STEP 2, only if the owner still wants the subdirectories.** After step 1 the move is a
genuine `git mv` plus the citation rewrites, because nothing computes depth any more. Its
remaining cost is honest and small in machinery and large in reading: 3,225 frozen reader
citations, plus 16 in `dev/` dated records, plus the two document rewrites, plus one line in
`.claude/`. Buy Option D at about 85 lines so the NAME still resolves.

**WHEN TO RUN IT.** No agent may be live: the move breaks `scripts/ledger.py`,
`scripts/rules.py`, `scripts/lint-prose.py` and `scripts/lint-agda.py` by path, and every
live agent holds those paths. The deploy runs on merge to `main`, so the workflow edit must
be in the same commit as the move. Sequence: quiet the tree, run `--apply`, apply the three
hand steps, run `make check` to green, then commit the move plus `AGENTS.md` plus
`scripts/README.md` plus both workflows as ONE commit with the `AGENTS-diff-approved:`
trailer.

**IF THE OWNER WANTS ONE SENTENCE:** the tidiness costs 3,225 dangling reader pointers and
buys nothing a gate can see; the depth repair costs nothing and removes a defect class that
has already produced three silent false-greens in this tree. Do the second first.

## ARCHIVE USED (DD18)

* `archive/dev/TASKS-archived.md:157`, the `L3.32-T122` row: sixteen masters archived in one
  arm, "All moved, ARCHIVE.md written; **its wiring checklist had one range defect, caught**".
  TAKEN AS SHAPE, never as a claim: the retired route's bulk move was correct in the move and
  wrong in the CHECKLIST, and review caught it. That is why this task's deliverable is a
  tested script rather than a list of paths, and why the migration exits 3 with its open
  steps named instead of exiting 0.
* `scripts/README.md`, read whole (642 lines). It declares a taxonomy by pipeline and topic
  and names no directory grouping, so this report proposes the FIRST directory taxonomy and
  the README must be rewritten with it rather than beside it (DD19).

## LITERATURE USED (DD18)

None, and the reason is one line: no mathematical literature bears on directory layout.
WHY NOT applies to the whole corpus.

## FILES THIS TASK WROTE

* `agents/tasks/LJ-1-290/LJ-1.290.md`, the pinned brief.
* `agents/tasks/LJ-1-290/lj-1.290-report.md`, this report.
* `agents/tasks/LJ-1-290/migrate-scripts.py`, the migration, tested.
* `agents/tasks/LJ-1-290/run-checkers.sh`, the harness.
* `agents/tasks/LJ-1-290/copy/`, the migrated copy of `scripts/`, `Makefile` and both
  workflows. Nothing under `scripts/` moved, was renamed, or was deleted.
