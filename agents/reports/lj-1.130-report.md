# LJ-1.130 report: the agent tree moved out of `_build/` and under git

Status: **DONE.** Every checker is green. Nothing is committed; the working tree holds the move.

This report stays in `_build/` by the brief's instruction. It is the last report written there.

## 1. Counts

| Quantity | Count |
|---|---|
| Reports moved live, to `agents/reports/` | **41** |
| Reports moved to archive, to `agents/reports/archive/` | **452** |
| Briefs moved, to `agents/briefs/` | **406** |
| `README.md` written | **1** |
| **Total files now tracked under `agents/`** | **900** |
| Citations rewritten in `dev/` | **278** |
| Citations rewritten in `scripts/` | **5** |
| Script path constants and globs repointed | **8** |
| Docstrings and help strings corrected | **6** |
| `REUSE.toml` entries added | **2 paths in 1 block** |
| **Prose violations NOT fixed, because of the exemption** | **1,133** |

That last figure is the point of the exemption: **1,109 violations in 74 archived reports plus
24 in 10 briefs. I fixed none of them, and none is a defect in anything the project runs on.**

## 2. What moved, and with which command

**Every moved file was untracked, so every move used plain `mv`, then `git add`.**
`git mv` moved nothing, because `_build/` is gitignored and `git ls-files _build/` was empty.
MEASURED before the move.

I deleted nothing. The only removal was the directory `_build/briefs/`, which was empty after
its 406 files moved out. An empty directory holds no content.

`_build/` now holds exactly the 20 data files the owner ruled stay (9 `.txt` profiles, 6
`.log` runs, `dashboard.html`, `lj-1.69-time.py`, 3 more logs and scripts), this report, and
the untouched subdirectories including `_build/2.8.0/` and `_build/literature/`.

## 3. Licensing: the owner's three-way split, verified per file

`REUSE.toml` gained `agents/**` and `dev/**` in the existing CC-BY-NC-SA-4.0 override block,
with a comment recording the owner's principle. `scripts/**` was not touched and stays AGPL.

**I added no `archive/**` exception, and none is needed.** The owner's principle dissolves the
conflict I found in the survey: an agent document is CC from birth, so no move can relicense
it. `agents/reports/archive/` is inside `agents/`, not inside the top-level `archive/`, so the
two rules never meet.

Verified per file with `reuse spdx`, not by reading the config:

| Path | Resolved licence |
|---|---|
| `agents/README.md` | CC-BY-NC-SA-4.0 |
| `agents/reports/lj-1.129-report.md` | CC-BY-NC-SA-4.0 |
| `agents/reports/archive/k1-report.md` | CC-BY-NC-SA-4.0 |
| `dev/PLAN.md` | CC-BY-NC-SA-4.0 |
| `dev/ledger.toml` | CC-BY-NC-SA-4.0 |
| `scripts/lint-prose.py` | **AGPL-3.0-only** |
| `Makefile` | **AGPL-3.0-only** |

`reuse lint`: **1269 / 1269 files, compliant.** Up from 369 / 369.

## 4. The lint exemption

`scripts/lint-prose.py:437` now excludes `agents/` beside `archive/`, with an eight-line
comment giving the reason in the shape that file already uses: a brief and a report are frozen
records, a gate over them can only force an edit to a record, and the same reasoning exempts
`dev/JOURNAL.md` at `scripts/check-rule-ids.py:83`. The comment records the measured figure,
1,109 and 24, so a later reader can see what the exemption is worth.

The exemption covers all three modes of `target_files`, including the pre-commit hook, which
lints staged files by explicit path. MEASURED in the survey: identical bytes give 39 violations
outside the exemption and 0 inside it.

## 5. Citations

**Before: 301 in `dev/`, of 149 unique targets. After: 23, of 8 unique targets.**

| Class | Count | Action |
|---|---|---|
| To an archived report | 261 | rewritten to `agents/reports/archive/` |
| To a live report | 4 | rewritten to `agents/reports/` |
| To a named brief | 6 | rewritten to `agents/briefs/` |
| Directory and prose references describing the old layout | 7 | rewritten by hand, see below |
| To `_build/literature`, `_build/tools`, `_build/2.8.0`, the `.txt` profiles, bare `_build/` | 22 | **left alone; the targets did not move** |
| To `_build/workbench.md` | 1 | **left alone, see section 8** |

**All 22 surviving citations resolve.** Verified by testing each path with `-e`. The single
exception is `_build/workbench.md`, which was dangling before this task.

The seven hand-written repairs were statements about where things live, not file citations,
and each was false after the move: `dev/PLAN.md:21-22`, `dev/ORCHESTRATION.md:167,211,360`,
`dev/LESSONS.md:1056`, `dev/memos/working-mechanisms.md:60`, and `dev/memos/L3.29-b-pivot.md:10`.

That last one deserves a note. It read that the reports "live in `_build/`, which is git-ignored
and volatile. This memo is their durable home." **That premise is now false**, and it was the
memo's stated reason for copying tables instead of citing them. I recorded the change and kept
the memo's judgment intact rather than rewriting its reasoning.

I also corrected `dev/PLAN.md:609`, this task's own index row, which described the layout the
owner replaced. It was 210 characters against the 200-character cap on first write;
`check-task-index.py` caught it and I cut it to 189.

## 6. Scripts repointed

Found by search, not from the survey's count. **The search found more than the survey priced:
8 path sites, not 5.** The survey measured the briefs alone; the reports moved too.

| File and line | Change |
|---|---|
| `scripts/check-rule-ids.py:167` | briefs glob to `agents/briefs` |
| `scripts/check-dev-docs.py:356` | briefs glob to `agents/briefs` |
| `scripts/check-task-index.py:41` | `BRIEFS` to `agents/briefs` |
| `scripts/check-dispatch-policy.py:73` | `BRIEFS` to `agents/briefs` |
| `scripts/check-sources-read.py:45` | `BRIEFS` to `agents/briefs` |
| `scripts/check-dev-docs.py:357` | **sweep corpus** `_build/*.md` to `agents/reports/` AND `agents/reports/archive/` |
| `scripts/check-dev-docs.py:363` | `own_files` self-exclusion path |
| `scripts/check-probes.py:86-88` | **the report corpus** that protects a probe from deletion |

That second-to-last row would have been a silent failure. `check-dev-docs.py --sweep` finds
LESSONS entries cited nowhere; had I repointed only the briefs, the sweep would have lost 493
reports from its corpus and started reporting entries as uncited. The `check-probes.py` row is
worse: it decides whether a probe may be deleted by asking whether a report names it. Left
pointing at `_build/`, it would have found zero reports and refused every deletion, or, read
the other way, lost the protection D-1 exists to give.

Six docstrings and help strings were corrected where the move made them false:
`check-rule-ids.py:31,147`, `check-task-index.py:10`, `check-dev-docs.py:64`,
`check-dispatch-policy.py:32`, and five prose strings in `check-probes.py`.

`check-rule-ids.py:147` had claimed the briefs "are not tracked". **They are now.**
`check-dispatch-policy.py:32` had explained that it cannot date a brief because "`_build/` is
never committed". **That reason is now wrong**, so I rewrote it to say the limit is the
checker's use of mtime, not a fact about the tree. I did not change its behavior.

Five citations in `scripts/` pointed at moved reports and were rewritten:
`scripts/dd25-record.py:15` and four fixture rows in `scripts/tests/test_task_index.py`.

## 7. Checkers, every one with its result

| Command | Result |
|---|---|
| `scripts/lint-prose.py --check` | **exit 0** |
| `scripts/weave-i18n.py --check` | exit 0 |
| `scripts/lint-agda.py --check` | exit 0 |
| `scripts/check-glossary.py --check` | exit 0 |
| `scripts/ledger.py --check` | exit 0, standing 28,617 unchanged |
| `scripts/check-probes.py --check` | exit 0, **1,287 tracked files** |
| `scripts/check-tree.py --check` | exit 0, 87 masters |
| `scripts/check-fences.py --check` | exit 0 |
| `scripts/check-rule-ids.py` | exit 0 |
| `scripts/rules.py --check` | exit 0 |
| `scripts/check-dev-docs.py` | **exit 0** |
| `scripts/check-task-index.py` | **exit 0**, 431 codes, all within 200 characters |
| `scripts/check-agents-guard.py` | exit 0 |
| `scripts/check-dispatch-policy.py` | **exit 0, 406 briefs read from the new path** |
| `scripts/check-sources-read.py` | exit 0, audit aid |
| `reuse lint` | **exit 0, 1269 / 1269** |
| pre-commit hook, gate 1, `check-probes.py --staged` | exit 0 |
| pre-commit hook, gate 2, `lint-prose.py` on 916 staged files | exit 0 |

I did not run `make check`. I did not run Agda. I did not touch `_build/2.8.0/` or `src/`.

### The test suite, and two failures that are NOT mine

I ran all eight suites. Six pass. **Two fail, and both failed before I touched anything.**

- `scripts/tests/test_dev_docs.py`, 30/31: the case "AGENTS.md one word over 2,200 fires".
  **PRE-EXISTING, MEASURED.** `git show HEAD:scripts/check-dev-docs.py` gives
  `AGENTS_WORD_CAP = 2300`, byte-identical to my version. The owner raised the cap from 2,200
  on 2026-08-10 and the test at `scripts/tests/test_dev_docs.py:87` was never updated.
- `scripts/tests/test_ratio_baseline.py`: the case "the bucket EQUALS the cone".
  **PRE-EXISTING, MEASURED.** `git status --short scripts/check-ratio.py
  scripts/tests/test_ratio_baseline.py` returns nothing. I edited neither file.

**I did not fix either.** Silently repairing an unrelated defect hides it, which is the same
rule the coordinator applied to `_build/workbench.md`. Both are now reported.

## 8. What I deliberately left broken

`dev/ORCHESTRATION.md:528` cites `_build/workbench.md`, which does not exist. It says the file
"was deleted on" a date, so the citation is about a deletion and reads as history. **It was
dangling before this task and it is dangling now. I left it, as instructed.**

## 9. The `AGENTS.md` lines for the owner

**I did not edit `AGENTS.md`.** DD19 requires the owner's ruling and a dated
`AGENTS-diff-approved:` trailer. Two places now describe a layout that no longer exists.

**First, the Never list.** It currently reads "commit generated files (anything under
`_build/`)". A report and a brief are now tracked and are not build output. Proposed:

> **Never:** commit build output (anything under `_build/`) or probe files
> (`src/Probe*.agda`). **An agent report and a brief are deliverables, not build output:**
> they belong in `agents/`, tracked.

**Second, the routing row at `AGENTS.md:105`**, which currently sends probe reports and briefs
to `_build/`. Proposed replacement:

> | **Route memos, digested literature** | `dev/memos/`, `dev/literature/` | n/a |
> | **Agent reports and briefs.** Every dispatch writes one of each. Live reports in `agents/reports/`, older in `agents/reports/archive/`, every brief in `agents/briefs/`. All tracked, all CC, all exempt from the prose linter because a record is never rewritten | `agents/README.md` | review |

**Third, a boundary line worth its space**, because the exemption is easy to misread as
laxness:

> **Never rewrite a brief or a report.** Correct it in the next one. `agents/` is exempt from
> `lint-prose.py` for exactly this reason.

**The cap.** `AGENTS.md` is 2,199 words against the 2,300 cap at
`scripts/check-dev-docs.py:105`. The three blocks above are about 130 words and one row is
deleted. **It fits.** MEASURED with `check-dev-docs.py`, green today.

## 10. Two things the move gained, unasked

- **`make clean` can no longer destroy the record.** `Makefile:180` runs
  `find _build -mindepth 1 -maxdepth 1 ! -name literature -exec rm -rf {} +`. Before today
  that command stood one keystroke from 493 reports and 406 briefs. `dev/LESSONS.md:1829-1831`
  records that this exact path already cost the project four kits.
- **git can now date a brief.** `check-dispatch-policy.py` still reads mtime, so the
  capability is available but unused. Wiring it is a separate task.

## 11. State of the working tree

**Nothing is committed. Nothing is pushed.**

928 files staged: 900 new under `agents/`, plus `REUSE.toml`, 13 files under `dev/` and 10
under `scripts/`. `git status` shows no unstaged residue and no untracked strays.

Two observations that are not mine. The session-start snapshot listed
`src/L/Condensation.lagda.md` as modified; it is clean now, and two commits appeared during my
run (`fe0cae3`, `21446f2`). **The orchestrator committed while I worked.** I touched nothing
under `src/`.

## 12. ARCHIVE USED

`archive/dev/README.md` and the four `*-archived.md` files at `archive/dev/`, read to confirm
the shape of an archived developer record before writing `agents/README.md`. `REUSE.toml:31-38`,
the `archive/**` rule, read to confirm the owner's principle removes the conflict rather than
patching it. I took no content from the archive.
