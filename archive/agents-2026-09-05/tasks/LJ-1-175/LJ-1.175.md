# LJ-1.175: sum Route A-prime to ONE total, or name exactly what blocks the sum

tier: opus (version `override`, set 2026-08-13; the head for every case is in
`scripts/dispatch_policy.py`, which is the only place the tables live)

## GOAL

**`[LJ-1.8]` is the trophy row and it has been blocked on one thing since
`[LJ-1.131]`: Route A-prime has no TOTAL.**

**Six blocks are priced. A5's last unknown dissolved yesterday. Nobody has
summed them.**

Give me ONE number for Route A-prime, in lines, with the basis of every block
named. **If the sum cannot be made, name exactly which block blocks it and
why.** Both are complete deliverables.

## WHY NOW, and it is not a new measurement

**Nothing here needs a probe.** Every block price is already on disk in a task
report. This task is arithmetic over measurements, plus the judgement of which
figures are still live and which were superseded.

**That judgement is the whole task.** `[LJ-1.131]` priced the route at 760 to
1,320 and `[LJ-1.136]` SUPERSEDED it. `[LJ-1.136]` then priced A5's risk as
seconds and not lines. Three later tasks changed A5 again. **A sum that adds a
superseded figure is worse than no sum.**

## WHAT IS MEASURED, and each row is somebody else's measurement

| finding | source |
|---|---:|
| Route A-prime at 760 to 1,320, SUPERSEDED on price | `[LJ-1.131]` |
| block A2 GO at 207 lines | `[LJ-1.134]` |
| the remaining blocks gated, both probes GO; A5's risk is seconds at 2.594 s per line | `[LJ-1.136]` |
| two L-graphs compose with NO second `hasReplacementL`, 2.50 s | `[LJ-1.152]` |
| the identity graph CARVES by separation, 1.73 s against 254.22 | `[LJ-1.154]` |
| **`CSB` DISSOLVED. A5 carries ZERO replacement. New gate `LeastCardInj`, 44 lines at 100.64 s** | `[LJ-1.156]` |

**`[LJ-1.156]` is the newest and it dissolved the block that held the sum
hostage. Start there and work backwards.**

## WHAT TO DO

1. **Build the block table.** Seven blocks, A1 to A7. For each: its line price,
   its seconds if measured, the task that set it, at `file:line`, and whether
   any later task superseded it.
2. **Sum it.** ONE number, per DD8, and name the basis of every term.
3. **Name every gap.** A block with no price is a gap, not a zero. **A block
   priced only by analogy is a gap too**, because P-l says a price from a
   comparable elsewhere is a hypothesis.
4. **Say what the total means for `[LJ-1.8]`.** Does the trophy row unblock, or
   does it need something else as well?

## THE ABORT CRITERION, fixed BEFORE the run (D-1)

- **SUMMED.** Every block has a live price and the total holds. Report the
  number, the table and the gaps. STOP.
- **BLOCKED, AND NAMED.** One or more blocks have no live price. **Report the
  partial sum, the named blocks and what each one needs**, which is a probe, a
  ruling or a build. **This is a complete answer and it is not a failure.**
- **THE BLOCKS DO NOT PARTITION.** If the seven blocks overlap, or if work
  moved between them, say so. **That result changes how the route is managed and
  it is worth more than a number.**

## THE TRAP, and it has caught this project twice

**A figure quoted from a paragraph is not a measurement.** `[LJ-1.168]` measured
that the 5,047 line figure was NEVER measured. It came from a retired ledger row
and `[LJ-1.10]` had already called it a false anchor. It survived because three
documents repeated it.

**So for every figure you carry into the sum, give `file:line` in the REPORT
that measured it, never in a plan paragraph that repeats it.**

**`scripts/ledger.py --brief` is the only admissible source for a standing size
figure.** A block price is not a standing figure, but the base it adds onto is.

## WHAT YOU MUST NOT DO

- **DO NOT RUN AGDA. A sibling is measuring seconds on the heaviest cluster in
  the tree right now.** This task needs no Agda at all. **If you believe it
  does, stop and say why instead of running it.**
- **Do not edit any master, any brief or any report.** Briefs and reports are
  frozen records. You write your own report and nothing else.
- **Do not re-price a block by analogy.** P-l. If a block has no measurement,
  it is a gap and you name it as one.
- Never `src/Everything.lagda.md`. Never commit, never push, never
  `git checkout .`, `git stash`, `git reset --hard` or `git clean`.
- Do not run `make check`; I run it.

## THE CLASSIFICATION I WANT ON EVERY NEGATIVE

**MEASURED or INFERRED, in those words.** 「This block has no price」 is MEASURED
only if you searched every report and say which search.

## DD4

**Maximize the code the two proofs share, and write it generic.** One rule, two
ends, no metric and no checker.

**Here DD4 has a specific and answerable form: how much of Route A-prime's total
is GENERIC, so the J tower re-instantiates instead of paying again?**
`[LJ-1.154]` made its carve generic in the index type and the family, and
recorded that 90 of its lines re-instantiate. **Give me that column for every
block you price.** A total with a generic column is worth more than a total.

## ARCHIVE (DD18)

- **`agents/tasks/LJ-1-156/`**, read the report WHOLE. **The newest and the one
  that dissolved the blocking unknown.**
- **`agents/tasks/LJ-1-136/lj-1.136-report.md`**, read WHOLE. It superseded
  `[LJ-1.131]` on price and it gated the remaining blocks.
- `agents/tasks/LJ-1-131/lj-1.131-report.md`: the seven-block split itself.
- `agents/tasks/LJ-1-134/`, `LJ-1-152/`, `LJ-1-154/`: the block measurements.
- **`archive/dev/TASKS-archived.md` and `STATUS-archived.md`.** The retired
  route also priced work at these sites. **Take SHAPE from the archive, never a
  claim**, and say what would not transfer.

Return an **ARCHIVE USED** section at `file:line`.

## LITERATURE (DD18)

**Nothing in the literature prices a formalization. Say so in one line.**

## SCOPE (read)

`agents/tasks/LJ-1-156/` FIRST, then `agents/tasks/LJ-1-136/`.

## SCOPE (write)

`agents/tasks/LJ-1-175/` only. **No master, no other task directory.**

## MANDATORY RULES

Run `.venv/bin/python scripts/rules.py --for recon` and read every statement.

- **DD8.** An estimate is ONE best-effort number and it names its basis.
- **P-l.** A price from a comparable elsewhere is a hypothesis, not a price.
- **C-41.** A retired numbering series carries its home at every citation.
- **C-31, C-32, C-33, C-34, C-36, C-37, C-39, C-40, D-10, D-26, D-29, D-30.
  I-5.**

## CONSTRAINTS

- Count with `.venv/bin/python scripts/ledger.py`.
- Run `.venv/bin/python scripts/lint-prose.py --check` on anything you write.
- DD23 freezes mathematical prose.
- Evidence is `file:line`. Write ASD-STE100.

## RETURN

**Lead with the total, or with the named blocker.** One number, or one sentence
naming what stops it. Then the block table with the basis of every row at
`file:line`. Then the generic column. Then the gaps. Then what `[LJ-1.8]` still
needs. **Mark every negative MEASURED or INFERRED.**
