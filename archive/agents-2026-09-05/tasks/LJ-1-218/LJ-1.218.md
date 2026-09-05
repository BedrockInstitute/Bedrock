# LJ-1.218: LJ-1.9's audit: the wing's ratio and its net removable lines

tier: pi (deepseek-subagent-mode), **model `deepseek-v4-flash`**: this audit
reads and measures with existing tools and runs NO Agda, so it takes flash and
holds no Agda slot.

## GOAL

**`[LJ-1.9]` has been 「planned」 since this phase opened and has never run.
`dev/ledger.toml:334` still reads `lines_removable = 0` with the comment
「0 = not yet reported; [LJ-1.9] fills it」 and a source field reading 「OWED by
[LJ-1.9]」.**

**Two deliverables, and the second is the one nobody has ever produced.**

1. **The wing's ratio, cold**, against DD24's bar.
2. **NET REMOVABLE LINES**, which DD5 measure 3 requires: what an independent
   reader says did not need to be there.

**This task is the independent reader.**

## WHY MEASURE 3 EXISTS, and it is a guard against this project

**DD5 records that this project WRITES ITS OWN EXAMINATION PAPER**: phase 1
builds the wing, and `[LJ-2.1]` then measures THAT WING to set the benchmark the
two-tower route must beat. **A long or wasteful wing sets a high benchmark which
the later route clears while being worse in absolute terms.**

**Measure 3 is the compensating mechanism: an independent reader reports what
did not need to be there, and `[LJ-2.1]` records measured, projected and
removable side by side.**

**So your number is not a tidiness figure. It is one of three guards on a
benchmark this project sets for itself.**

## WHAT IS ALREADY MEASURED, so you do not re-derive it

| finding | source |
|---|---|
| the wing at 1.76x, gap 56 to 67 s, and 56 is the safer figure | `[LJ-1.185]` |
| eight of twelve wing masters are already under the bar TOGETHER | `[LJ-1.185]` |
| the Condensation family carries 82 pc of the seconds on 65 pc of the lines | `[LJ-1.185]` |
| the `*Agree` telescope term is SPENT: cured, 42.72 s returned | `[LJ-1.158]` |
| the `Condensation` telescope cure caps at about 5.2 s | `[LJ-1.177]` |
| the 16 s 「last lever」 NEVER EXISTED: a double subtraction | `[LJ-1.185]` |
| the telescope component carries 7,925 of 8,236 ms, and removing it restores 21 FALSE fields | `[LJ-1.214]` |

**Re-measure the RATIO because lines have moved; do not re-derive the levers.**

## THE HARD HALF: what did not need to be there

**Read the wing as a reader, not as its author.** Candidates, and you must give
a LINE COUNT for each you claim:

- **Content with no consumer.** C-35: a delivered block with no consumer is
  UNTESTED. **But `[LJ-1.146]` measured that the whole chain is unconsumed only
  because the trophy is unwritten**, so 「no consumer」 alone does not make a line
  removable here. **Say which side each case falls on.**
- **Content that a generic form would collapse.** `[LJ-1.210]` measured 42 lines
  making a 1,288-line module class-generic. **Is there duplication that one
  parameter would remove?**
- **Content superseded by a later build** and never retired.
- **Dead names, unused imports, and abandoned experiments.**

**A line you cannot name at `file:line` is not a removable line.**

## THE TRAP, and DD24's own row names it

**Do NOT propose removals to improve the ratio.** P-q measured 315 lines removed
buying 11.8 seconds, and DD24's row refuses the shrinking denominator. **A
removable line is one that did not need to be WRITTEN, not one whose deletion
flatters a number.**

**And `lines_removable` is a REPORT, not a licence to delete.** You propose;
nothing is removed by this task.

## THE ABORT CRITERION, fixed BEFORE the run (D-1)

- **BOTH DELIVERED.** The ratio with its run count, and a removable-lines figure
  with every line named. STOP.
- **NOTHING IS REMOVABLE.** **Say so plainly with what you read.** That is a
  real result and it is the one DD5 measure 3 most needs to be honest about: an
  author's own audit that finds nothing is worthless, an independent one that
  finds nothing is evidence.
- **THE RATIO CANNOT BE MEASURED CLEANLY.** Siblings hold Agda slots. **If the
  machine is too loaded, say so and give the removable-lines half.**

## WHAT YOU MUST NOT DO

- **Do not edit any master, and do not remove a line.** This is an audit and its
  report is the whole product.
- **Do not run Agda for a typecheck.** `check-ratio.py` may run if the machine
  is quiet enough, and **you must report the load beside any figure**.
- **Do not dispatch an agent.**
- **A probe goes in `agents/tasks/LJ-1-218/`**, tracked, never deleted.
- **Create your report file in your FIRST five minutes (C-22).** An agent died
  on 2026-08-14 having written nothing.
- Never `src/Everything.lagda.md`. Never commit, never push, never
  `git checkout .`, `git stash`, `git reset --hard` or `git clean`.
- Do not run `make check`; the orchestrator runs it.

## THE INSTRUMENT

**`check-ratio.py`'s ±12.8 percent is a ONE-MODULE BETWEEN-SERIES figure by its
own words at `:72-76`; within-series spread is 0.5 to 4.0 percent.** **Use a
within-series paired design for any seconds figure**, and reverse the order in a
second series to cancel drift, as `[LJ-1.209]` and `[LJ-1.214]` both did.

## THE CLASSIFICATION I WANT ON EVERY NEGATIVE

**MEASURED or INFERRED, in those words.**

## DD4

**Maximize the code the two proofs share, and write it generic.** One rule, two
ends, no metric and no checker.

**DD4 is one of your instruments.** `[LJ-1.210]` and `[LJ-1.213]` measured that
class-generic ports collapse large modules at tiny surfaces. **Ask of the wing:
how much of it is the same content written twice at two carriers?** That is
removable in DD4's sense even when both copies have consumers.

## ARCHIVE (DD18)

- **`agents/tasks/LJ-1-185/lj-1.185-report.md`**, read WHOLE with its
  `runs/`: the ratio, the gap, and the per-master distribution.
- `agents/tasks/LJ-1-214/` and `agents/tasks/LJ-1-209/`: what the wing's seconds
  are actually made of, and the three levers measured void.
- **`dev/ledger.toml`** `[ratio]` and the `gch_wing` roster: **the twelve
  masters you are auditing.**
- `dev/PLAN.md` DD5 measure 3 and DD24, read whole.
- **`archive/dev/TASKS-archived.md`.** **Take SHAPE from the archive, never a
  claim**, and say what would NOT transfer.

Return an **ARCHIVE USED** section at `file:line`.

## LITERATURE (DD18)

**Nothing in the literature governs removability. Say so in one line.**

## SCOPE (read)

`dev/PLAN.md` DD5's three measures FIRST, then `agents/tasks/LJ-1-185/lj-1.185-report.md`.

## SCOPE (write)

`agents/tasks/LJ-1-218/` only. **No master.**

## MANDATORY RULES

Run `.venv/bin/python scripts/rules.py --for review`.

- **D-1.** The abort criterion fixed BEFORE the run.
- **P-l.** A cure or a price measured elsewhere is a hypothesis here.
- **C-42.** A refutation measures the site it names, never its extent.
- **C-36, P-t, P-q, P-m, C-12, C-22, C-39, C-40. DD0, DD8, DD24, D-10, D-26,
  D-29, D-30. I-5.**

## CONSTRAINTS

- Count with `.venv/bin/python scripts/ledger.py`.
- Run `scripts/lint-prose.py --check` and `scripts/lint-agda.py --check`.
- DD23 freezes mathematical prose.
- Evidence is `file:line`. Write ASD-STE100.

## RETURN

**Lead with two numbers: the wing's ratio with its run count and load, and NET
REMOVABLE LINES.** Then every removable line at `file:line` with why it did not
need to be written. Then what you read and did NOT call removable, because that
half is what makes the figure trustworthy. **Mark every finding MEASURED or
INFERRED.**
