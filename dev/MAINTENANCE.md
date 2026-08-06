# MAINTENANCE.md: keeping the dev/ documents from decaying

The dev/ documents decay. On 2026-08-06 every instance below was found by
accident, none by a gate. This file records the maintenance mechanism built by
`[L3.32-T110]`: a commit gate, an on-demand sweep, and the review steps that
stay review, so each decay mode has exactly one enforcement point. The checks
live in `scripts/check-dev-docs.py`; every threshold's full argument is in
`_build/l3.32-t110-report.md` section 3.

## The gate: `make check` runs these six

All six are cheap pure-Python reads and none needs Agda, so the commit gate
stays fast. A defect blocks the commit, which is the point: decay found here is
found by a gate, not by accident.

| check | what it enforces | threshold | why this number |
|---|---|---:|---|
| `agents-size` | AGENTS.md word count (whitespace tokens, the `wc -w` unit) | 2,200 | current green 1,784; the failed state was 3,450, so 2,200 is 23 percent above green and 1,250 words below the failure. The file auto-loads into every session, so the cap is a context budget, and a legitimate single edit is tens of words, not hundreds. |
| `plan-cell-size` | any table cell in dev/PLAN.md | 1,600 | current largest cell 1,125 (`L3.32-F5`); the failed state was 12,634, 11.2x the current maximum. 1,600 is 42 percent above the current maximum and 7.9x below the failure; the largest legitimate ruling cell (`D28`) is 572, so a cell over 1,600 is a document inside a table, which the JOURNAL taxonomy reserves for dev/JOURNAL.md. |
| `lessons-imported-routing` | a LESSONS entry whose heading says "imported from/into" must appear in a dev/rules.toml bundle or trigger | none (invariant) | imported entries arrive whole from outside, with no local measurement forcing discovery; that is the class that sat uncited for five days. Only the import marker counts: "imported names" and "imported operations" (`R-34`, `R-38`, `C-21`) are code prose. |
| `plan-section0-date` | the `## 0.` heading date must be no older than the newest date in the section's own body | none (invariant) | the heading is the "as of" contract; a body describing newer work than its heading is the measured decay ("days behind the work it described"). |
| `memo-status-form` | a `**STATUS:` header in dev/memos/ must state a verdict word | none (invariant) | the verdict vocabulary is STANDING, PARTIAL, SUPERSEDED, WRONG, REFUTED, NOT BUILT. Whether a refutation HAS happened is a reading judgment (below); this check keeps a header that exists honest. |
| `agents-enforcers` | every `scripts/*.py` named in AGENTS.md's rules table must exist | none (invariant) | the table's third column is the enforcement-point contract; a named enforcer that vanished would make the contract a wish. |

## The sweep: on-demand, informational, exit 0

`python3 scripts/check-dev-docs.py --sweep`, run at each dispatch batch and
whenever a LESSONS entry lands. It lists:

- LESSONS entries that are unrouted in dev/rules.toml AND cited nowhere in the
  live corpus, any brief, or any report under `_build/`. The maintenance
  mechanism's own files do not count as citations: a sweep that cleared an
  entry by mentioning it in its own documentation would be circular. A new
  entry starts with zero citations, so it surfaces here until it is routed or
  an independent document cites it. First run (2026-08-06) surfaced `C-17`, a
  three-day-old lesson nothing routed or cited.
- Section 11 cells over the 600-word episode-scale line. 600 is the largest
  legitimate ruling cell (`D28`, 572) plus a margin; a status cell above it is
  carrying episode content, which belongs in dev/JOURNAL.md. First run listed
  `L3.32-F2` (786) and `L3.32-F5` (1,125), which predate the `[T108]` slim of
  the main `L3.32` row and are the next candidates for the same extraction.

## How a threshold is raised

A cap that anyone may raise silently is not a cap. The gate thresholds are
constants in `scripts/check-dev-docs.py`, and raising one is a ruling, not an
edit:

1. Only the owner may raise a threshold. An agent may not, and a silent edit
   to the constant is a violation.
2. The change must carry a numbered decision in dev/PLAN.md section 3 that
   records the measured reason: the new measured size class, and why the old
   cap no longer fits it. A number without a reason is a guess.
3. The old and new values, the date, and the decision ID are entered in the
   threshold record below.

### Threshold record

| date | threshold | from | to | decision |
|---|---|---:|---:|---|
| 2026-08-06 | `agents-size` | (new) | 2,200 | owner's brief `[L3.32-T110]` |
| 2026-08-06 | `plan-cell-size` | (new) | 1,600 | owner's brief `[L3.32-T110]` |
| 2026-08-06 | episode-scale (sweep line) | (new) | 600 | owner's brief `[L3.32-T110]` |

## Deliberately not automated, and the review step that catches each

- **Whether a memo's diagnosis was refuted.** Detecting a refutation is
  reading. Enforcement point: dev/ORCHESTRATION.md section 6's return audit
  adds or updates the memo's `**STATUS:` blockquote in the same dispatch that
  refutes the memo, and `memo-status-form` keeps any header that exists honest.
- **Whether AGENTS.md text duplicates a checker.** Detecting duplication is
  reading. Enforcement point: adversarial review of any change to AGENTS.md's
  rules table (the `[L3.32-T109]` pattern), plus the `agents-size` cap, which
  keeps the file small enough that the review is cheap.
- **Struck-decision references and foreign rule IDs.** Already enforced by
  `scripts/check-rule-ids.py`, in the gate. Not rebuilt here: a duplicate
  checker splits the canonical home, which is the failure this repository
  names most often.
- **Episode versus ruling classification below the size caps.** The sweep
  surfaces section 11 cells over 600 words; the extraction itself is the
  JOURNAL surgery that `[T108]` runs.

## Expected red on 2026-08-06

`plan-section0-date` fires on the tree as delivered: the `## 0.` heading is
dated 2026-08-04 while the section describes work dated 2026-08-06. This is
the decay the dispatch names, not a threshold artifact. The fix is one line in
the PLAN rewrite: set the heading date to the newest date the section
describes.
