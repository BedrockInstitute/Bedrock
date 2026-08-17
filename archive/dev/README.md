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
| `DECISIONS-archived.md` | The whole `D` ruling series, D1 to D39 | You need what the retired route ruled, or what a consolidated `DD` row dropped |
| `TASKS-archived.md` | All 265 `L3.32-T` dispatch rows | You need what a dispatch actually found |
| `JOURNAL-archived.md` | The 4,280-line execution journal | You need WHY, and the other three cannot answer. It is long; do not read it through |
| `STATUS-archived.md` | The 96 goal rows of `dev/PLAN.md` section 11 | You need a retired goal's full status text. Section 11 keeps the top level and the route switches only |

## Nothing here is renumbered or rewritten

Every file is exactly as it was on the day it was archived. Hundreds of
citations across `dev/LESSONS.md`, the memos, the briefs and the commit
history point at these codes. Renumbering would falsify all of them, and a
code that means one thing in a commit message and another here is a trap.

## Nothing here is read by machine, from the POD cutover onward

Two gates resolve citations against `DECISIONS-archived.md` and
`TASKS-archived.md` today, and both run green in `make check`. At the cutover
`check-task-index.py` RETIRES and `check-rule-ids.py`
is narrowed to `dev/LESSONS.md` and `dev/rules.toml` (`dev/POD.md` section 7.1,
rows 14 and 15). After that a citation into these files is resolved by a reader
and by nothing else. Renaming a file here breaks no gate and every citation.

## The archive survey

A brief carries an `## ARCHIVE` section naming what may bear on the task, and the
return answers it; `check-dd18-survey.py` gates the return half. At the cutover
the POD program will search these files mechanically at brief build and inject
the result, under `dev/POD.md` section 7.4, which this file does not restate. **DD18, not DD19, is the ruling** that made the
survey a brief section; this paragraph named the wrong code until 2026-08-17.
