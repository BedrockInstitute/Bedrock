# LJ-1.219: join `GenModel` to `Powerset`'s body, both at the ambient class

tier: pi (deepseek-subagent-mode), **model `deepseek-v4-pro`**: this task runs
Agda and holds a slot. **The clock selected the mode.**

## GOAL

**`[LJ-1.216]` answered「does the port serve BOTH towers」 with NO, and it named
the blocker at `file:line`.**

**MEASURED:** `GenPowersetAtAmbient.agda:68` exits 42. The body declares
`envOneAt` over the ambient structure, while **`tagAtL` and `extAt` come from
the DELIVERED `L.Coding.Model` and produce formulas over the tower**
(`src/L/Coding/Powerset.lagda.md:129`).

**So the leak is a supplier, and that supplier is the one module already ported.**

**`[LJ-1.210]` built `GenModel.agda`, class-generic, green. Join it to
`Powerset`'s generic body and instantiate BOTH at the ambient class.**

## WHY THIS IS THE CHAIN'S FIRST LINK AND NOT A REPAIR

**`[LJ-1.213]` MEASURED that the chain gate is an ORDER, not a wall:** the fixed
suppliers import the tower, so each must port before its consumer can. **It said
port bottom-up.**

**`[LJ-1.216]` then measured WHICH supplier blocks first. This task walks the
first step of that order with two bricks that are already green apart.**

**If they compose, the order is confirmed by construction and the remaining
fifteen modules are a known quantity. If they do not, the order is wrong and
that is worth more than a partial build.**

## WHAT IS GREEN AND MUST NOT BE REBUILT

| file | what it is |
|---|---|
| `agents/tasks/LJ-1-210/GenModel.agda` | class-generic `Model`, exit 0 |
| `agents/tasks/LJ-1-213/GenPowersetBodyAtL.agda` | the transformed body at `isL`, seven substitutions, exit 0 |
| `agents/tasks/LJ-1-213/DefAtStage.agda` | the 8-line corollary alone, exit 0 |
| `agents/tasks/LJ-1-216/GenPowersetAtAmbient.agda` | the failing instantiation, exit 42 at `:68` |

**Read all four. Compose; do not rewrite.**

## THE FIGURE THIS TASK OWES

**`[LJ-1.216]` could give no written-line figure because the body never reached
a valid instantiation. That figure is what the whole port turns on.**

**`[LJ-1.210]` measured 19 lines for `Model`'s ambient instantiation.** **Give
the same number for the JOINED pair**, and give the three DD4 numbers:
**shared body, plumbing, per-tower residual.** `[LJ-1.213]` gives 389, 12 and 8
at `isL`.

## THE ABORT CRITERION, fixed BEFORE the run (D-1)

- **THEY COMPOSE.** Report the ambient instantiation's written lines and the
  three DD4 numbers. **Then the port serves both towers, the order is confirmed
  by construction, and I sequence the landing of the first link.** STOP.
- **THEY COMPOSE BUT DEARLY.** If the joined instantiation costs materially more
  than 19 lines, **say so with both figures.** That re-prices the chain.
- **A SECOND SUPPLIER LEAKS.** **Name it at `file:line` and stop.** That is the
  next brick and naming it is a complete answer. **Do not port it: one link per
  task, so a failure is always attributable.**
- **THE ORDER IS WRONG.** If `Model` and `Powerset` cannot compose generically
  at all, **say why.** That would refute `[LJ-1.213]`'s bottom-up reading and it
  is the most valuable outcome available.
- **A WALL.** **A single `agda` invocation past 30 MINUTES is a wall**:
  interrupt, report the ELAPSED SECONDS, bisect. **Every cut gets the SAME bound
  as its green control, and the control's elapsed time is reported BEFORE any
  cut is interpreted** (`[LJ-1.215]`'s proposed law, applied here).

## WHAT YOU MUST NOT DO

- **Do not edit any master.** This is a probe. **Nothing lands in `src/` from
  this task.**
- **Do not port a second supplier.** Name it and stop.
- **Do not attempt the record-bundle refactor.** It walls; `[LJ-1.210]` measured
  the site.
- **Do not touch `src/L/Choice/Name.lagda.md`** (DD23), and **do not touch
  anything under `agents/tasks/LJ-1-217/`**: a sibling is re-pricing A6 there.
- **A probe goes in `agents/tasks/LJ-1-219/`**, tracked, never deleted.
- **ONE agda process, `GHCRTS="-A64m -I0 -M8g"`, cap NEVER raised.** Two
  siblings are live and one holds the other Agda slot. **Report the load beside
  every absolute figure**, discard a warm-up, and take at least three kept runs
  for any figure a decision rests on.
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

**This task IS the DD4 measurement that `[LJ-1.216]` could not take.** The port
exists for one reason: that the same body serves both towers. **Until an ambient
instantiation typechecks, that reason is INFERRED, and a class-generic module
that only ever instantiates at one class is a refactor with a cost and no
benefit.**

## ARCHIVE (DD18)

- **`agents/tasks/LJ-1-216/lj-1.216-report.md`**, read WHOLE. **It names the
  leak and it is your brief within this brief.**
- **`agents/tasks/LJ-1-213/lj-1.213-report.md`** and its four probes: the body,
  the corollary, the plumbing figure of 12, and the bottom-up reading.
- **`agents/tasks/LJ-1-210/lj-1.210-report.md`** and `GenModel.agda`: the
  class-generic `Model` and its 19-line ambient instantiation.
- `src/L/Coding/Powerset.lagda.md:129` and `src/L/Coding/Model.lagda.md`: **read
  where the tower actually enters, not the reports about it.**
- **`archive/dev/TASKS-archived.md`.** **Take SHAPE from the archive, never a
  claim.**

Return an **ARCHIVE USED** section at `file:line`.

## LITERATURE (DD18)

**`dev/literature/devlin-II5.md:301-302` says Devlin's construction is
class-generic in his own words, and `:370-382` splits II.5 into nine
tower-neutral steps and three per-tower ones.** **Say whether the joined pair
lands where his table puts it.** Return a **LITERATURE USED** section.

## SCOPE (read)

`agents/tasks/LJ-1-216/lj-1.216-report.md` FIRST, whole.

## SCOPE (write)

`agents/tasks/LJ-1-219/` only. **No master.**

## MANDATORY RULES

Run `.venv/bin/python scripts/rules.py --for probe` and `--for build`.

- **D-1.** The abort criterion fixed BEFORE the run.
- **P-l.** `Model`'s 19 lines are a comparable and NOT a price for the pair.
- **C-36.** Write the term you could not write.
- **C-38 as extended.** A hypothesis is discharged when something SUPPLIES it.
- **C-42.** A refutation measures the site it names, never its extent.
- **P-k, P-m, P-y, C-12, C-22, C-39, C-40. DD0, DD8, DD24, D-10, D-26, D-29,
  D-30. I-5.**

## CONSTRAINTS

- Count with `.venv/bin/python scripts/ledger.py`.
- Run `scripts/lint-prose.py --check` and `scripts/lint-agda.py --check`.
- DD23 freezes mathematical prose.
- Evidence is `file:line`. Write ASD-STE100.

## RETURN

**Lead with whether they compose, and with the ambient instantiation's written
lines against `[LJ-1.210]`'s 19.** Then the three DD4 numbers. Then any second
supplier that leaks, at `file:line`, NOT ported. Then the seconds with load and
run count. **Mark every negative MEASURED or INFERRED.**
