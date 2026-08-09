# archive/dev: the retired route's developer records

Moved here 2026-08-09 by the owner's instruction. These four files were
`dev/*-archived.md`; they are the record of the internalization route, which
the two-tower bridge route replaced (`dev/PLAN.md` DD2). The rules of the
archive are [archive/README.md](../README.md): frozen, outside every gate,
nothing imports across the boundary.

**They live under `archive/` and not `dev/` because they are evidence, not
working documents.** A developer reading `dev/` should see what binds today.

| File | What it holds | Read it when |
|---|---|---|
| `DECISIONS-archived.md` | The whole `D` ruling series, D1 to D39 | You need what the retired route ruled, or what a consolidated `DD` row dropped. `scripts/check-rule-ids.py` reads this file, so a `D` citation still resolves |
| `TASKS-archived.md` | All 264 `L3.32-T` dispatch rows | You need what a dispatch actually found. `scripts/check-task-index.py` reads this file, so an `L3.32-T` citation still resolves |
| `JOURNAL-archived.md` | The 4,260-line execution journal | You need WHY, and the other three cannot answer. It is long; do not read it through |
| `STATUS-archived.md` | The 96 goal rows of `dev/PLAN.md` section 11 | You need a retired goal's full status text. Section 11 keeps the top level and the route switches only |

## Nothing here is renumbered or rewritten

Every file is exactly as it was on the day it was archived. Hundreds of
citations across `dev/LESSONS.md`, the memos, the briefs and the commit
history point at these codes. Renumbering would falsify all of them, and a
code that means one thing in a commit message and another here is a trap.

## Two of these files are still READ BY MACHINE

`check-rule-ids.py` and `check-task-index.py` resolve citations against
`DECISIONS-archived.md` and `TASKS-archived.md`. **Moving or renaming either
file breaks a gate**, so both checkers name their path in one constant near
the top. That is deliberate: the path is stated once and changing it is one
edit.

## The archive-survey mechanism

DD19 makes surveying these a brief SECTION rather than a hope. Every brief
carries an **ARCHIVE** section naming what may bear on the task; every return
carries an **ARCHIVE USED** section naming what it read and took, at
`file:line`. `dev/LESSONS.md` is NOT archived and still binds.
