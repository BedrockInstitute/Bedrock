# LJ-1.213: gate the chain before porting it, at `Powerset` and `DefAt-stage`

tier: pi (deepseek-subagent-mode), **model `deepseek-v4-pro`**: this task runs
Agda, so it takes pro and holds an Agda slot. **The clock selected the mode.**

## GOAL

**`[LJ-1.210]` dissolved the chapter and it did it by BUILDING, not by
counting.** `L.Coding.Model` is class-generic and typechecks first try, 7.73 s:
**42 lines written, 16 of 1,288 touched, 1,272 verbatim**, with both
instantiations green, 2 lines at `isL` and 19 at the ambient class.

**But it ported 2 of 17 modules, 24 percent, and marked the rest INFERRED.**

**This task measures whether the CHAIN ports at the same rate. Nothing lands in
`src/` until it answers.**

## WHY THE GATE, and it is DD8 rather than caution

**Two figures from `[LJ-1.210]` make the chain a different question from the
module:**

1. **`L.Coding.Powerset` CANNOT be ported alone.** Its port is chained through
   ten suppliers: **17 modules, 5,822 lines, a 125-line census floor.**
2. **The plumbing grows LINEARLY in module count.** The flat telescope repeats
   about **17 lines per module**, so 17 modules cost about **289 lines of
   plumbing** while the shared body grows only in size. **And the record bundle
   that would cut that WALLS today**, which `[LJ-1.210]` measured at a single
   field whose type names `sucV`.

**So the module's rate does not price the chain, and P-l says so.**

## THE TWO THINGS TO BUILD

**1. `L.Coding.Powerset`, class-generic.** `[LJ-1.210]` READ it and reports **7
of its 8 body lines are the same mechanical substitutions**. **Build it and see
whether that holds.**

**2. `DefAt-stage`, 9 lines, which `[LJ-1.210]` names as the ONLY L-specific
content in `Powerset`** and calls **「a corollary, not a chapter」**. **That
phrase is the load-bearing claim of the whole dissolution. Test it.**

## THE ABORT CRITERION, fixed BEFORE the run (D-1)

- **THE CHAIN PORTS AT THE SAME RATE.** Report the written and touched lines for
  both, and the plumbing per module you actually paid. **Then the whole chain is
  fundable and I sequence the landing.** STOP.
- **THE RATE BREAKS.** If `Powerset` or `DefAt-stage` costs materially more per
  line than `Model` did, **say so with both figures.** That re-prices the
  dissolution and is a complete answer.
- **`DefAt-stage` IS A CHAPTER AFTER ALL.** If the 9 lines are 9 lines of
  statement over a body that does not exist, **name what is missing.** That
  would restore `[LJ-1.196]`'s verdict on new evidence and it is the most
  valuable thing you can return.
- **THE PLUMBING DOMINATES.** If 17 lines per module is really 40, **say so**:
  289 against 680 changes whether the chain is worth porting at all.
- **A WALL.** **A single `agda` invocation past 30 MINUTES is a wall**:
  interrupt it, report the elapsed seconds, and bisect. `[LJ-1.210]` hit six
  heap exhaustions and **not one was in the port**: they bisected to its own
  comparison code and to the record-bundle refactor. **Expect the same two
  sources and do not confuse either with a port cost.**

## DO NOT REBUILD WHAT IS BUILT

**`agents/tasks/LJ-1-210/GenModel.agda` is the class-generic `Model`, green.**
**Import it, instantiate it, extend it. Do not write it again.**

**And do not re-litigate the dissolution.** `[LJ-1.196]` said chapter,
`[LJ-1.200]` refuted the word, `[LJ-1.210]` built the answer. **You are pricing
the chain, not reopening the verdict.**

## WHAT YOU MUST NOT DO

- **Do not edit any master.** This is a probe. **Nothing lands in `src/` from
  this task; the orchestrator sequences that after your figures.**
- **Do not attempt the record-bundle refactor.** It walls today and
  `[LJ-1.210]` measured the site. **If the plumbing hurts, report the number and
  stop.**
- **Do not touch `src/L/Choice/Name.lagda.md`.** DD23 blocks a pending change.
- **A probe goes in `agents/tasks/LJ-1-213/`**, tracked, never deleted.
- **ONE agda process, `GHCRTS="-A64m -I0 -M8g"`, cap NEVER raised.** **Report
  the load beside every absolute figure**, discard a warm-up, and take at least
  three kept runs for any figure a decision rests on.
- **Report a heap exhaustion as a wall.** Never raise the cap.
- **Create your report file in your FIRST five minutes (C-22).** An agent died
  on 2026-08-14 having written nothing.
- Never `src/Everything.lagda.md`. Never commit, never push, never
  `git checkout .`, `git stash`, `git reset --hard` or `git clean`.
- Do not run `make check`; the orchestrator runs it.

## THE INSTRUMENT

**`check-ratio.py`'s ±12.8 percent is a ONE-MODULE BETWEEN-SERIES figure by its
own words at `:72-76`; within-series spread is 0.5 to 4.0 percent.** **Use a
within-series paired design for any seconds figure.** `[LJ-1.209]` measured an
83 ms effect that way and correctly refused to call it a cure.

## THE CLASSIFICATION I WANT ON EVERY NEGATIVE

**MEASURED or INFERRED, in those words.** **`[LJ-1.210]`'s 「7 of 8 body lines」
and 「a corollary, not a chapter」 are both READINGS, not builds. You are the
measurement.**

## DD4

**Maximize the code the two proofs share, and write it generic.** One rule, two
ends, no metric and no checker.

**`[LJ-1.210]` measured 19 lines buying the second tower for a 1,288-line
module, the best DD4 figure this project holds.** **Give the same figure for
`Powerset`, and give the PLUMBING figure beside it**, because the plumbing is
the half that grows and DD4 is judged on the whole chain, not on one module.

## ARCHIVE (DD18)

- **`agents/tasks/LJ-1-210/lj-1.210-report.md`** and its probes, read WHOLE.
  **`GenModel.agda` is your starting point and its walls are its own, not
  yours.**
- `agents/tasks/LJ-1-200/LJ-1.200-report.md`: the counts and the `abs₀`
  correction.
- `src/L/Coding/Powerset.lagda.md` and `src/L/Coding/Model.lagda.md`: **read
  where the class actually appears, not the reports about it.**
- **`archive/dev/TASKS-archived.md`.** **Take SHAPE from the archive, never a
  claim**, and say what would NOT transfer.

Return an **ARCHIVE USED** section at `file:line`.

## LITERATURE (DD18)

**`dev/literature/devlin-II5.md:301-302` says Devlin's construction is
class-generic in his own words, and `:370-382` splits II.5 into nine
tower-neutral steps and three per-tower ones.** **`[LJ-1.210]` measured the same
split in Agda. Say whether `Powerset` and `DefAt-stage` fall on the neutral side
or the per-tower side of Devlin's own table.** Return a **LITERATURE USED**
section.

## SCOPE (read)

`agents/tasks/LJ-1-210/lj-1.210-report.md` FIRST, whole.

## SCOPE (write)

`agents/tasks/LJ-1-213/` only. **No master.**

## MANDATORY RULES

Run `.venv/bin/python scripts/rules.py --for probe` and `--for build`.

- **D-1.** The abort criterion fixed BEFORE the run.
- **P-l.** `Model`'s rate is a comparable and NOT a price for `Powerset`.
  **This task is P-l's test case by construction.**
- **C-36.** Write the term you could not write.
- **C-42.** A refutation measures the site it names, never its extent.
- **P-k, P-m, P-t, P-y, C-12, C-22, C-39, C-40. DD0, DD8, DD24, D-10, D-26,
  D-29, D-30. I-5.**

## CONSTRAINTS

- Count with `.venv/bin/python scripts/ledger.py`.
- Run `scripts/lint-prose.py --check` and `scripts/lint-agda.py --check`.
- DD23 freezes mathematical prose.
- Evidence is `file:line`. Write ASD-STE100.

## RETURN

**Lead with whether the chain ports at `Model`'s rate, and with the written and
touched lines for `Powerset` and `DefAt-stage`.** Then the plumbing paid per
module against the projected 17. Then whether `DefAt-stage` is a corollary or a
chapter. Then the seconds with load and run count. Then the DD4 figure for the
CHAIN. **Mark every negative MEASURED or INFERRED.**
