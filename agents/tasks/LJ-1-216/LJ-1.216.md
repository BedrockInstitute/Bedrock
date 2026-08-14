# LJ-1.216: the second instantiation, and it is the port's whole reason

tier: pi (deepseek-subagent-mode), **model `deepseek-v4-pro`**: this task runs
Agda, so it takes pro and holds an Agda slot. **The clock selected the mode.**

## GOAL

**Three reports have now taken `[LJ-1.196]`'s CHAPTER apart, and every
load-bearing claim has been BUILT rather than counted.** `[LJ-1.210]`:
`L.Coding.Model` class-generic, 42 written, 1,272 verbatim, first try.
`[LJ-1.213]`: `Powerset`'s body at 19 written and 370 verbatim, its seven
mechanical substitutions green at `isL`, and `DefAt-stage` measured at **8
non-blank lines, a corollary and not a chapter.**

**ONE THING IS STILL INFERRED, and it is the reason the port exists at all.**

**`[LJ-1.213]` did NOT build a second instantiation. Its DD4 figure is
INFERRED.**

**Build it. Set `M` to the ambient class and typecheck.**

## WHY THIS ONE GATE DECIDES THE LANDING

**DD4 is the whole argument for the port.** A class-generic `Powerset` that only
ever instantiates at `isL` is a refactor that serves ONE tower: it costs 12
plumbing lines and buys nothing that the delivered fixed version did not already
give.

**The port is worth landing if and only if the second instantiation is cheap.**
`[LJ-1.210]` measured 19 lines at the ambient class for a 1,288-line module.
**Measure the same number here.**

## WHAT IS ALREADY GREEN, so you extend rather than rebuild

- **`agents/tasks/LJ-1-213/GenPowersetBodyAtL.agda`**: the transformed body,
  `M = isL`, `M-trans = isL-trans`, seven substitutions, **exit 0**.
- **`agents/tasks/LJ-1-213/GenPowersetAtL.agda`**: the same plus `DefAt-stage`,
  **exit 0**.
- **`agents/tasks/LJ-1-213/DefAtStage.agda`**: the 8-line corollary alone,
  **exit 0**.
- **`agents/tasks/LJ-1-210/GenModel.agda`**: the class-generic `Model`.

**Do not rewrite any of them. Set `M` to the ambient class and see what breaks.**

## THE OBSTRUCTION `[LJ-1.213]` MEASURED, and it may or may not reach you

**`GenPowerset.agda` exits 42 at `:63` with an `UnequalTerms` between the
delivered `𝒮ʟ` and `M`**, because the fixed supplier modules import the tower.
**`[LJ-1.213]` calls that the chain gate and it is an ORDER problem: the
suppliers must port first.**

**But the BODY is green at `isL` without them.** **So the question for you is
whether the body is also green at the ambient class, or whether the tower leaks
in through a supplier the body actually touches.**

**If it leaks, name the supplier at `file:line`. That is the next module to
port, and naming it is a complete answer.**

## THE ABORT CRITERION, fixed BEFORE the run (D-1)

- **CHEAP AT THE SECOND CLASS.** Report the written lines and the seconds.
  **Then the port serves both towers, DD4 is MEASURED rather than inferred, and
  I sequence the landing.** STOP.
- **DEAR AT THE SECOND CLASS.** If the ambient instantiation costs materially
  more than `[LJ-1.210]`'s 19 lines, **say so with both figures.** That re-prices
  the whole port and it is a complete answer.
- **A SUPPLIER LEAKS THE TOWER INTO THE BODY.** **Name it and stop.** That is the
  next module in the order, and it is worth more than a partial build.
- **A WALL.** **A single `agda` invocation past 30 MINUTES is a wall**:
  interrupt, report the elapsed seconds, bisect. **`[LJ-1.215]` measured today
  that a missing clock cap cost 53 percent of a dispatch and produced a verdict
  that was UPHELD BUT MISATTRIBUTED.**

## DO NOT RE-LITIGATE THE DISSOLUTION

**`[LJ-1.196]` said chapter. `[LJ-1.200]` refuted the word. `[LJ-1.210]` and
`[LJ-1.213]` built the answer.** **You are measuring the second tower's price,
not reopening the verdict.**

## WHAT YOU MUST NOT DO

- **Do not edit any master.** This is a probe. **Nothing lands in `src/` from
  this task; the orchestrator sequences that after your figure.**
- **Do not port a supplier.** If one blocks you, NAME it. The order matters and
  a half-ported chain is worse than none.
- **Do not attempt the record-bundle refactor.** It walls; `[LJ-1.210]`
  measured the site.
- **Do not touch `src/L/Choice/Name.lagda.md`.** DD23 blocks a pending change.
- **A probe goes in `agents/tasks/LJ-1-216/`**, tracked, never deleted.
- **ONE agda process, `GHCRTS="-A64m -I0 -M8g"`, cap NEVER raised.** **Report
  the load beside every absolute figure**, discard a warm-up, and take at least
  three kept runs for any figure a decision rests on.
- **Report a heap exhaustion as a wall.** Never raise the cap.
- **Create your report file in your FIRST five minutes (C-22).**
- Never `src/Everything.lagda.md`. Never commit, never push, never
  `git checkout .`, `git stash`, `git reset --hard` or `git clean`.
- Do not run `make check`; the orchestrator runs it.

## THE CLASSIFICATION I WANT ON EVERY NEGATIVE

**MEASURED or INFERRED, in those words.** **The whole point of this task is to
convert ONE inferred figure. Do not hand back another.**

## DD4

**Maximize the code the two proofs share, and write it generic.** One rule, two
ends, no metric and no checker.

**This task IS the DD4 measurement.** Report three numbers: **the shared body,
the plumbing, and the per-tower residual.** `[LJ-1.213]` gives 389, 12 and 8 at
`isL`. **Give the same three at the ambient class**, and say whether the shared
body is the SAME 389 lines or a different set.

## ARCHIVE (DD18)

- **`agents/tasks/LJ-1-213/lj-1.213-report.md`** and its four probes, read
  WHOLE. **They are your starting point and they are green.**
- **`agents/tasks/LJ-1-210/lj-1.210-report.md`**: the 19-line ambient
  instantiation for `Model`, which is your comparable. **P-l: a comparable is
  not a price.**
- `src/L/Coding/Powerset.lagda.md`: **read where the tower actually appears, not
  the reports about it.**
- **`archive/dev/TASKS-archived.md`.** **Take SHAPE from the archive, never a
  claim.**

Return an **ARCHIVE USED** section at `file:line`.

## LITERATURE (DD18)

**`dev/literature/devlin-II5.md:370-382` splits II.5 into nine tower-neutral
steps and three per-tower ones.** **Say whether `Powerset` and `DefAt-stage`
land where Devlin's table puts them.** Return a **LITERATURE USED** section.

## SCOPE (read)

`agents/tasks/LJ-1-213/lj-1.213-report.md` FIRST, whole.

## SCOPE (write)

`agents/tasks/LJ-1-216/` only. **No master.**

## MANDATORY RULES

Run `.venv/bin/python scripts/rules.py --for probe` and `--for build`.

- **D-1.** The abort criterion fixed BEFORE the run.
- **P-l.** `Model`'s 19 lines are a comparable and NOT a price for `Powerset`.
- **C-36.** Write the term you could not write.
- **C-42.** A refutation measures the site it names, never its extent.
- **P-k, P-m, P-y, C-12, C-22, C-39, C-40. DD0, DD8, DD24, D-10, D-26, D-29,
  D-30. I-5.**

## CONSTRAINTS

- Count with `.venv/bin/python scripts/ledger.py`.
- Run `scripts/lint-prose.py --check` and `scripts/lint-agda.py --check`.
- DD23 freezes mathematical prose.
- Evidence is `file:line`. Write ASD-STE100.

## RETURN

**Lead with the ambient instantiation's written lines, against `[LJ-1.210]`'s
19, and whether the port serves both towers.** Then the three DD4 numbers at the
ambient class. Then any supplier that leaks the tower, at `file:line`. Then the
seconds with load and run count. **Mark every negative MEASURED or INFERRED.**
