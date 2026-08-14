# LJ-1.220: parameterize every leak, and census the chain in ONE pass

tier: pi (deepseek-subagent-mode), **model `deepseek-v4-pro`**: this task runs
Agda and holds a slot. **The clock selected the mode.**

## GOAL

**Three dispatches have now walked the chain one brick at a time, and each one
stopped at the next brick.**

| task | what it measured |
|---|---|
| `[LJ-1.213]` | the suppliers import the tower, so the gate is an ORDER: port bottom-up |
| `[LJ-1.216]` | brick one is the DELIVERED `L.Coding.Model`, at `:68` |
| `[LJ-1.219]` | the Model link COMPOSES; brick two is `L.Coding.Recover`, at `:142` |

**At one brick per dispatch, `[LJ-1.213]`'s 17-module chain costs fifteen more
dispatches to census, and the census is not even the port.**

**This task replaces the walk with one measurement. Do not port brick two.
PARAMETERIZE it, and every leak after it, until the body typechecks or you can
say why it cannot.**

## THE METHOD, and it is a measuring instrument rather than a proof

**Start from `agents/tasks/LJ-1-219/JoinAtAmbient.agda`**, which exits 42 at
`:142` with `keyOf`. **Do not rebuild it.**

1. Take the name Agda names. Add it as a MODULE PARAMETER at the ambient class,
   with the type the body needs.
2. Re-run. Agda names the next one.
3. Repeat.

**Every parameter you add is a HYPOTHESIS the probe does not discharge.**
C-38 as extended: a hypothesis is discharged when something SUPPLIES it, and
here NOTHING supplies these. **That is deliberate and you must say so in the
report.** The probe measures the chain's WIDTH. **It proves nothing about
`Powerset` and you must not claim that it does.**

## WHAT THE PROJECT BUYS, and why this is worth an Agda slot

**A complete leak list turns `[LJ-1.213]`'s「17 modules, INFERRED」into a
MEASURED count of the modules the body ACTUALLY touches.** That number prices
the port and nothing else on record does.

**It also converts two INFERRED findings from `[LJ-1.219]`:** `extAt-in` and the
`domAt` trio sit past `:142` and were never reached. **A body that runs to the
end reaches them.**

## THE ABORT CRITERION, fixed BEFORE the run (D-1)

- **EXIT 0 WITH K PARAMETERS.** Report K, every parameter with its home module
  at `file:line`, and the parameter block's line count. **Then the chain's width
  is MEASURED, the port has a price, and I sequence it.** STOP.
- **THE LIST KEEPS GROWING.** If ten iterations have not closed it, **stop and
  report the curve**: parameters after each iteration. **A growth curve is a
  real answer and it prices the chain as surely as a total would.**
- **A PARAMETER CANNOT BE STATED.** If a leaking name's type cannot be written
  at the ambient class without porting its module first, **that is a REAL wall
  and it is the most valuable outcome here.** Name the name, the type, and what
  blocks it. **Then the order is not just an order, it is a dependency, and the
  parameterize instrument is refuted.**
- **A WALL.** **A single `agda` invocation past 20 MINUTES is a wall**:
  interrupt, report the ELAPSED SECONDS, bisect. **Every cut gets the SAME bound
  as its green control, and the control's elapsed time is reported BEFORE any
  cut is interpreted** (`[LJ-1.215]`'s proposed law). `[LJ-1.219]` ran this file
  in 1 to 3 seconds, so a slow run is itself a finding.

## WHAT YOU MUST NOT DO

- **Do not port `L.Coding.Recover` or any other supplier.** This task exists
  because porting one at a time is the thing being replaced.
- **Do not edit any master.** This is a probe. **Nothing lands in `src/`.**
- **Do not weaken the body to make it pass.** If a parameter's type has to be
  guessed, **say the type you wrote and why.** A body that typechecks against a
  wrong hypothesis measures nothing.
- **Do not attempt the record-bundle refactor.** It walls; `[LJ-1.210]` measured
  the site.
- **Do not touch `src/L/Choice/Name.lagda.md`** (DD23), and **do not touch
  anything under `agents/tasks/LJ-1-217/`**: a sibling is re-pricing A6 there.
- **A probe goes in `agents/tasks/LJ-1-220/`**, tracked, never deleted.
- **ONE agda process, `GHCRTS="-A64m -I0 -M8g"`, cap NEVER raised.** Siblings
  are live and one holds the other Agda slot. **Report the load beside every
  absolute figure**, discard a warm-up, and take at least three kept runs for
  any figure a decision rests on.
- **Report a heap exhaustion as a wall.** Never raise the cap.
- **Create your report file in your FIRST five minutes (C-22).**
- Never `src/Everything.lagda.md`. Never commit, never push, never
  `git checkout .`, `git stash`, `git reset --hard` or `git clean`.
- Do not run `make check`; the orchestrator runs it.

## THE CLASSIFICATION I WANT ON EVERY NEGATIVE

**MEASURED or INFERRED, in those words.**

## DD4

**Maximize the code the two proofs share, and write it generic.** One rule, two
ends, no metric and no checker.

**The parameter block is an INSTRUMENT and not DD4 plumbing.** Do not add it to
`[LJ-1.219]`'s 21. **Report the two numbers apart**, because a delivered port
supplies these names and pays nothing for them.

**The DD4 question this task answers: how many modules must go generic before
the shared body serves both towers?** `[LJ-1.213]` says 17 and marks it
INFERRED. **Give the measured count.**

## ARCHIVE (DD18)

- **`agents/tasks/LJ-1-219/lj-1.219-report.md`**, read WHOLE, and
  `JoinAtAmbient.agda`. **It is your starting file and your brief within this
  brief.**
- **`agents/tasks/LJ-1-213/lj-1.213-report.md`**: the 17-module chain, the
  5,822 lines, the 125-line census floor, and the bottom-up reading you are
  testing.
- `agents/tasks/LJ-1-210/lj-1.210-report.md` and `GenModel.agda`: the generic
  Model and its numeral operations at `ProbeLJ1210C.agda:53-70`.
- `src/L/Coding/Recover.lagda.md:84`, `:112-116`: where brick two pins `𝒮ʟ`.
- **`archive/dev/TASKS-archived.md`.** **Take SHAPE from the archive, never a
  claim.**

Return an **ARCHIVE USED** section at `file:line`.

## LITERATURE (DD18)

**`dev/literature/devlin-II5.md:370-382` splits II.5 into nine tower-neutral
steps and three per-tower ones.** **Say whether your measured leak list matches
that split, or whether Agda's module boundaries cut across it.**
`[LJ-1.219]` found they cut across it for `keyOf`. Return a **LITERATURE USED**
section.

## SCOPE (read)

`agents/tasks/LJ-1-219/lj-1.219-report.md` FIRST, whole.

## SCOPE (write)

`agents/tasks/LJ-1-220/` only. **No master.**

## MANDATORY RULES

Run `.venv/bin/python scripts/rules.py --for probe` and read every statement.

- **D-1.** The probe doctrine. The abort criterion is fixed above.
- **P-l.** A cure measured at one site is a hypothesis at another.
- **P-i.** The conversion-explosion playbook, if a run hangs.
- **C-12.** One process, the cap never raised.
- **C-22.** Write the deliverable incrementally.
- **C-36.** Write the term you could not write.
- **C-38 as extended.** A hypothesis is discharged when something SUPPLIES it.
  **Every parameter you add is an undischarged hypothesis.**
- **C-42.** A refutation measures the site it names, never its extent.
- **D-10, R-40. P-k, P-m, P-y, C-39, C-40. DD0, DD8, DD24, D-26, D-29, D-30.
  I-5.**

## CONSTRAINTS

- Count with `.venv/bin/python scripts/ledger.py`.
- Run `scripts/lint-prose.py --check` and `scripts/lint-agda.py --check`.
- DD23 freezes mathematical prose.
- Evidence is `file:line`. Write ASD-STE100.

## RETURN

**Lead with the parameter count and whether the body reached exit 0.** Then the
complete leak list, one row per name: the name, its home module at `file:line`,
and the type you had to write. Then the module count that list implies against
`[LJ-1.213]`'s 17. Then whether `extAt-in` and the `domAt` trio composed. Then
the seconds with load and run count. **Mark every negative MEASURED or
INFERRED.**
