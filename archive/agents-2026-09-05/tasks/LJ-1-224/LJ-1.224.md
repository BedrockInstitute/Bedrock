# LJ-1.224: is `[LJ-1.220]`'s exit 0 bought? Check all 22 parameter types

tier: opus (deepseek-subagent-mode). **The switch's ADVERSARIAL row, taken as
the table gives it.** The target was written by pi, so DD17's invariant holds:
the critic is never the same head as the author.

## GOAL

**`[LJ-1.220]` typechecked `Powerset`'s body at the ambient class. EXIT 0.** It
is the first ambient instantiation this project has ever had, and three results
now rest on it: the chain's width is **9 modules and 22 names**, not
`[LJ-1.213]`'s inferred 17; `extAt-in` and the `domAt` trio compose; and
`[LJ-1.219]`'s brick two was never a brick.

**But the body typechecks against 22 PARAMETERS, and every one is an
undischarged hypothesis (C-38).**

**A body proves nothing about hypotheses nobody supplies. Worse, a body over
WEAKENED hypotheses typechecks more easily than the real one.** **So the exit 0
is worth exactly as much as the 22 types are faithful.**

**Check every one.**

## THE ONE TEST, PER PARAMETER

**`agents/tasks/LJ-1-220/lj-1.220-report.md` section 4 gives all 22 rows: the
name, its home at `file:line`, and the type the probe wrote.**

**For each: open the delivered signature at its `file:line` and compare.**

**The parameter is FAITHFUL when the only difference is the carrier**, that is,
the delivered `𝒮ʟ` replaced by the ambient `S` from `𝒮ᵥ ↾ M` with `M = Full`.

**The parameter is WEAKENED when anything else moved**, and these are the shapes
to hunt:

- a hypothesis of the delivered signature is **missing** from the parameter;
- a delivered `Σ` or `∥ ∥₁` became something easier to produce;
- an implicit became explicit, or a quantifier's scope moved;
- the delivered name is a **definition with a reduction** and the parameter is
  opaque, so the body's definitional steps now come free;
- the type is more general than the delivered one **in the argument position**,
  which makes the parameter harder to supply later and is a different defect.

**A parameter that is STRONGER than the delivered name is also a defect**, and a
different one: the census then understates the port, because supplying it will
cost more than porting the module.

## THE FIVE THE REPORT ALREADY FLAGS, and they are the likeliest defect

**`[LJ-1.220]` section 0 says three names「cannot be parameterized, because a
bare parameter cannot express a reduction」**: `GraphWitAt` is pattern-matched,
and `fst (keyS A φ)` must reduce to `pr (# n) (fst (codeS A φ))`. **It
reconstructed them transparently at the ambient class and calls their only
tower-pinning content「the trivial `tt*` proof」.** It also states `Clauses` and
`GraphWitAt` as dependent reconstructions.

**Five reconstructions are five places where the probe WROTE the thing it was
measuring.** **Attack them first.** **Ask of each: does the reconstruction
reduce the same way the delivered one does, and does the body rely on that
reduction?** **If a reconstruction reduces MORE than the delivered name, the
exit 0 is bought and the width is wrong.**

## THE ABORT CRITERION, fixed BEFORE the run (D-1)

- **ALL 22 FAITHFUL AND THE 5 SOUND.** Say what you compared and where. **Then
  the width of 9 and 22 stands, the exit 0 is real, and I sequence the port on
  it.** STOP.
- **N ARE WEAKENED.** Name each, give both signatures at `file:line`, and say
  whether the body actually uses the weakening. **Then the width is a floor and
  not a figure**, and say so in those words.
- **A RECONSTRUCTION IS UNSOUND.** **That is the most valuable outcome here.**
  Name it, show the reduction that differs, and say what the honest form would
  cost.
- **THE BODY IS NOT THE DELIVERED BODY.** If `Probe.agda`'s body differs from
  `src/L/Coding/Powerset.lagda.md` beyond the seven mechanical substitutions
  `[LJ-1.213]` measured, **say which lines moved.** A rewritten body proves
  nothing about the delivered one.
- **A WALL.** **A single `agda` invocation past 20 MINUTES is a wall**:
  interrupt, report the ELAPSED SECONDS, bisect. `[LJ-1.220]` ran this file to
  exit 0, so a slow run is itself a finding.

## HOW TO TEST A SUSPECT PARAMETER, and it is cheap

**Do not re-derive the whole body.** **Replace one suspect parameter with the
FAITHFUL type and re-run.** **If the body still exits 0, that parameter was not
load-bearing and the census row stands. If it fails, you have measured the
weakening and you name the term.**

**One parameter per run. Report the run count.**

## THE AGDA SLOT, and you must read this

**You run in the harness, so `dispatch.py` does NOT count your Agda process.**
**C-12's ceiling here is TWO and a sibling holds the other one.** **You are the
second. Run ONE agda process, `GHCRTS="-A64m -I0 -M8g"`, and never raise the
cap.** **Report a heap exhaustion as a wall.**

**Report the load beside every absolute figure.** The machine is not quiet.

## WHAT YOU MUST NOT DO

- **Do not edit any master, brief or report.** **Write your own report and your
  own probe files, nothing else.**
- **Do not port anything.** This task checks a measurement.
- **Do not touch `agents/tasks/LJ-1-217/` or `LJ-1-223/`.** Two siblings are
  live there. **Copy `agents/tasks/LJ-1-220/Probe.agda` into your own directory
  before you change a line of it.**
- **Do not touch `src/L/Choice/Name.lagda.md`.** DD23 blocks a pending change.
- **A probe goes in `agents/tasks/LJ-1-224/`**, tracked, never deleted.
- **Create your report file in your FIRST five minutes (C-22).**
- Never `src/Everything.lagda.md`. Never commit, never push, never
  `git checkout .`, `git stash`, `git reset --hard` or `git clean`.
- Do not run `make check`; the orchestrator runs it.

## THE CLASSIFICATION I WANT ON EVERY NEGATIVE

**MEASURED or INFERRED, in those words.** **A type comparison you read is
MEASURED. A judgement that the body does not depend on a difference is INFERRED
until you re-run with the faithful type.**

## DD4

**Maximize the code the two proofs share, and write it generic.** One rule, two
ends, no metric and no checker.

**DD4 is what the exit 0 is FOR.** The port exists so one body serves both
towers. **If the 22 parameters are faithful, the shared body is 389 lines and
the second tower costs a 58-line parameter block plus the 9 modules' own ports.
If they are not, that whole accounting moves.** **Give the corrected three
numbers if any row changes: shared body, plumbing, per-tower residual.**

## ARCHIVE (DD18)

- **`agents/tasks/LJ-1-220/lj-1.220-report.md`**, read WHOLE, and
  **`Probe.agda`, read WHOLE.** **The probe is the evidence; the report is its
  account.**
- **`agents/tasks/LJ-1-221/lj-1.221-report.md`**: it reached `[LJ-1.220]`'s
  supply finding independently by reading, and its sections 4 and 6 hold the
  method.
- `agents/tasks/LJ-1-219/lj-1.219-report.md` and `JoinAtAmbient.agda`: the
  starting body and the five names that composed.
- `agents/tasks/LJ-1-213/lj-1.213-report.md`: the seven mechanical
  substitutions and the 389 / 12 / 8 split.
- `agents/tasks/LJ-1-210/GenModel.agda`: the supply list.
- **`src/L/Coding/CodeSet.lagda.md`, `Graph.lagda.md`, `Table.lagda.md`,
  `Slot.lagda.md`, `Sound.lagda.md`, `Unique.lagda.md`, `Sat.lagda.md`,
  `Bridge.lagda.md`, `Uniform.lagda.md`**: **the nine delivered signatures.
  Read them, never a report about them.**
- **`archive/dev/TASKS-archived.md`.** **Take SHAPE from the archive, never a
  claim.**

Return an **ARCHIVE USED** section at `file:line`.

## LITERATURE (DD18)

**Nothing in the literature governs whether an Agda parameter is faithful to a
delivered signature. Say so in one line**, and say separately whether
`dev/literature/devlin-II5.md:387-389`, which says the per-tower content is
exactly two objects, matches a 9-module width. Return a **LITERATURE USED**
section.

## SCOPE (read)

`agents/tasks/LJ-1-220/lj-1.220-report.md` and `Probe.agda` FIRST, both whole.

## SCOPE (write)

`agents/tasks/LJ-1-224/` only. **No master.**

## MANDATORY RULES

Run `.venv/bin/python scripts/rules.py --for probe` and `--for review`.

- **D-1.** The abort criterion is fixed above.
- **C-38 as extended.** A hypothesis is discharged when something SUPPLIES it.
  **This task is C-38's test case: 22 hypotheses and no supplier.**
- **C-12.** One process, the cap never raised. **You are the second slot.**
- **C-22.** Write the deliverable incrementally.
- **C-36.** Write the term you could not write.
- **C-42.** A refutation measures the site it names, never its extent.
- **P-l.** A cure measured at one site is a hypothesis at another.
- **P-i, P-k, P-m, P-y. D-10, D-26. C-39, C-40. DD0, DD4, DD8, DD24. I-5.**

## CONSTRAINTS

- Count with `.venv/bin/python scripts/ledger.py`.
- Run `scripts/lint-prose.py --check` and `scripts/lint-agda.py --check`.
- DD23 freezes mathematical prose.
- Evidence is `file:line` on BOTH sides. Write ASD-STE100.

## RETURN

**Lead with two numbers: how many of the 22 are FAITHFUL, and whether the exit 0
survives.** Then one row per parameter: name, delivered signature at
`file:line`, probe type, FAITHFUL or WEAKENED or STRONGER, and for anything not
faithful, whether the body uses the difference. Then the five reconstructions,
each judged. Then the run count with load. **Mark every negative MEASURED or
INFERRED.**
