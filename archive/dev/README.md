# archive/dev: the retired route's developer records

Moved here 2026-08-09 by the owner's instruction. These four files were
`dev/*-archived.md`; they are the record of the internalization route, which
the two-tower bridge route replaced (`dev/PLAN.md` DD2). The archive rules are
[archive/README.md](../README.md): frozen, outside every gate, nothing imports
across the boundary. The rule set is [AGENTS.md](../../AGENTS.md).

**They live under `archive/` and not `dev/` because they are evidence, not
working documents.** A developer reading `dev/` should see what binds today.

| File | What it holds | Read it when |
|---|---|---|
| `DECISIONS-archived.md` | The whole `D` ruling series, D1 to D39 | You need what the retired route ruled, or what a consolidated `DD` row dropped |
| `TASKS-archived.md` | All 265 `L3.32-T` dispatch rows | You need what a dispatch actually found |
| `JOURNAL-archived.md` | The 4,280-line execution journal | You need WHY, and the other three cannot answer. It is long; do not read it through |
| `STATUS-archived.md` | The 96 goal rows of `dev/PLAN.md` section 11 | You need a retired goal's full status text. Section 11 keeps the top level and the route switches only |

## Nothing here is renumbered or rewritten

Every file is exactly as it was on the day it was archived. Hundreds of
citations across `dev/LESSONS.md`, the memos, the briefs and the commit
history point at these codes. Renumbering would falsify all of them, and a
code that means one thing in a commit message and another here is a trap.

## Two gates read these files

`check-task-index.py` and `check-rule-ids.py` resolve citations against
`TASKS-archived.md` and `DECISIONS-archived.md`, and both run green in
`make check`. **So renaming a file here breaks a gate and every citation.**

## The archive survey

A brief carries an `## ARCHIVE` section naming what may bear on the task, and
the return answers it. `check-dd18-survey.py` gates the return half. **DD18,
not DD19, is the ruling** that made the survey a brief section.
