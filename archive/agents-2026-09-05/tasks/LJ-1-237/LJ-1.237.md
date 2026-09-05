# LJ-1.237: assemble `sl` and `sc`, now that every wall in front of them is down

tier: pi (deepseek-subagent-mode), **model `deepseek-v4-pro`**: this task runs
Agda and holds a slot. **The clock selected the mode.**

## GOAL

**`sl` and `sc` are the last two open hypotheses of `[LJ-1.7]`, phase 1's
blocking row.** **Three things stood in front of them this morning and all
three are down as of today.**

| wall | state, 2026-08-14 | evidence |
|---|---|---|
| (a) the bounded-against-unbounded decode | **NEVER A WALL** | `[LJ-1.124]` GO at 147 lines, and `[LJ-1.235]` re-ran the probe today, **exit 0** |
| (b) the carrier change | **NOT A WALL** | `liftFo` needs only a PARTIAL map (`src/FOL/Manipulation/Bounding.lagda.md:162`); `satBridge` is delivered with five live consumers (`src/L/Axioms/Separation.lagda.md:449`) |
| (c) the replacement image's stage | **FALLS at 18 lines** | `agents/tasks/LJ-1-235/ProbeLJ1235A.agda`, a SIBLING lemma leaving `hasReplacementL` and its five consumers untouched |

**Assemble them. Convert a FLOOR into a NUMBER.**

## WHAT YOU ARE BUILDING

**`sl = StageLevels`** (`agents/tasks/LJ-1-178/ProbeLJ1178A.agda:360-361`):
the stage believes every ordinal has a level.

**`sc = StageCovered`** (`:405-406`): the stage believes every set lies in a
level.

**Both are hypotheses of `module Whole` at `:486-493`.** **`[LJ-1.228]`
MEASURED that they are ONE object, not two: both consume the same stage-carrier
level-hood instantiation.** **Build the shared object once.**

## THE INGREDIENTS, all delivered or green today

| ingredient | at |
|---|---|
| the bounded decode, both directions | `agents/tasks/LJ-1-124/ProbeLJ1124A.agda:199-209` |
| `hasReplacementL-bound`, the stage bound | `agents/tasks/LJ-1-235/ProbeLJ1235A.agda` |
| `liftFo`, the partial-map lift | `src/FOL/Manipulation/Bounding.lagda.md:162` |
| `mkBoundedFo` and `satBridge` | `src/L/Axioms/Separation.lagda.md:449`, `:150-153` |
| the level-hood formula and its Σ₁ certificate | `src/L/BoundedSubset.lagda.md:74-146` |
| `Σ₂`, `Σ₁-Σ₂`, `reverse` at arity zero | `src/L/BoundedSubset.lagda.md:840-869` |
| the level closure `isL-Lset`, `Lset-suc`, `Lset-mono` | `src/L/Axioms/Basic.lagda.md:154-157`, `:196`, `src/L/Constructible.lagda.md:355` |
| the stage ordinal facts | `src/L/Ordinal/Stages.lagda.md:434`, `:265`, `:164` |
| absoluteness `abs₀`, `σ₁-up` | `src/FOL/Absoluteness.lagda.md:122`, `:182` |
| **`succλ`, ALREADY in the site telescope** | `src/L/BoundedSubset.lagda.md:904`, restated `:1394` |

**`[LJ-1.228]` MEASURED that `sc` holds exactly at LIMIT stages and fails at a
successor. `succλ` is why the site is safe. Use it.**

## THE ABORT CRITERION, fixed BEFORE the run (D-1)

- **BOTH BUILD.** Report the written lines for the shared object and for each
  of `sl` and `sc` on top of it, and the seconds. **Then `[LJ-1.7]`'s four
  hypotheses are three SUPPLIED and one BUILT in shape, and the phase's
  blocking row has a number instead of a floor.** STOP.
- **ONE BUILDS.** Say which, with its lines, and **name what the other still
  needs** (C-36). **A half is a real result here and I would rather have one
  measured than two estimated.**
- **MATERIALLY OVER THE FLOOR.** `[LJ-1.228]` said about 0.15k each, joint
  0.25k to 0.35k, and `[LJ-1.233]` said that is a FLOOR whose direction is UP.
  **If you land far above it, report both figures.** That re-prices the phase
  and it is a complete answer.
- **A FOURTH WALL.** **If something blocks that none of (a), (b) or (c)
  covers, NAME IT at `file:line` and stop.** **That is worth more than a
  partial build**, and today has produced four walls that turned out to be
  three non-walls and one 18-line lemma. **Do not assume a new one is real
  until you have named its term.**
- **A WALL.** **A single `agda` invocation past 20 MINUTES is a wall**:
  interrupt, report the ELAPSED SECONDS, bisect. **Every cut gets the SAME
  bound as its green control, and the control's elapsed time is reported BEFORE
  any cut is interpreted** (`[LJ-1.215]`'s law).

## WHAT YOU MUST NOT DO

- **Do not re-litigate the three walls.** They are settled by measurement
  today. **If one of them does not hold up in practice, that is a finding and
  you report it with the term, but you do not re-derive the wall.**
- **Do not port `L.Coding.Sequence`.** That is the OTHER half of `[LJ-1.7]`'s
  residue, 157 lines, and it is not yours.
- **Do not edit any master.** This is a probe. **Nothing lands in `src/`, and a
  probe under `src/` is forbidden by I-5.**
- **Do not touch `agents/tasks/LJ-1-236/`.** A sibling is live there.
- **Do not touch `src/L/Choice/Name.lagda.md`.** DD23 blocks a pending change.
- **A probe goes in `agents/tasks/LJ-1-237/`**, tracked, never deleted.
- **ONE agda process, `GHCRTS="-A64m -I0 -M8g"`, cap NEVER raised.** **A sibling
  holds the other Agda slot.** **Report the load beside every absolute figure**,
  discard a warm-up, and take at least three kept runs for any figure a decision
  rests on.
- **Report a heap exhaustion as a wall.** Never raise the cap. **`[LJ-1.234]`
  met one today and it was R-34's unpinned `InfinitySet` level meta, cured by
  `module IS = InfinitySet {ℓ}`. Check that before you call a heap wall
  yours.**
- **A probe whose module name predates the one-directory-per-task move needs
  its include path set from the task directory.** `[LJ-1.235]` hit this and
  recorded the cure.
- **Create your report file in your FIRST five minutes (C-22).**
- Never `src/Everything.lagda.md`. Never commit, never push, never
  `git checkout .`, `git stash`, `git reset --hard` or `git clean`.
- Do not run `make check`; the orchestrator runs it.

## CITE THE REPORT THAT MEASURED, NEVER THE ONE THAT QUOTED

**C-44 entered `dev/LESSONS.md` today and its measurement is my own session:
four defective briefs, three of them assertions about the record that one grep
would have refuted.** **If this brief asserts anything you cannot find, say so
and treat it as unproven.**

## THE CLASSIFICATION I WANT ON EVERY NEGATIVE

**MEASURED or INFERRED, in those words.** **This task converts a FLOOR into a
number. Do not hand back another floor.**

## DD4

**Maximize the code the two proofs share, and write it generic.** One rule, two
ends, no metric and no checker.

**`[LJ-1.228]` MEASURED that `sl` and `sc` are ONE per-tower object: Devlin's
C1 row, the level-hood certificate's stage instantiation.** **So the J tower
will need its own, and this is the moment to make that cheap.**

**Write the shared object over a STRUCTURE PARAMETER from its first line.**
**`[LJ-1.210]` measured that retrofitting one costs 42 lines on a 1,288-line
module and writing one at the start costs nothing.** **Say whether the
parameter form cost anything here.**

## ARCHIVE (DD18)

- **`agents/tasks/LJ-1-235/lj-1.235-report.md` and `ProbeLJ1235A.agda`**, read
  WHOLE. **The stage bound and how it comes out.**
- **`agents/tasks/LJ-1-233/lj-1.233-report.md`**, read WHOLE. **It is your map:
  which walls fell, and the `liftFo` plus `satBridge` route in place of the
  erase route.**
- **`agents/tasks/LJ-1-228/lj-1.228-report.md`**: the delivered-component map
  in section 1.1, the band mapping in section 3, and the falsity check in
  section 4.
- **`agents/tasks/LJ-1-178/lj-1.178-report.md` and `ProbeLJ1178A.agda`**: the
  two hypotheses as stated, and section 7 where the debt moved to the stage.
- `agents/tasks/LJ-1-124/lj-1.124-report.md` and `ProbeLJ1124A.agda`: the
  bounded decode, green today.
- **`src/L/BoundedSubset.lagda.md`, `src/L/Hierarchy.lagda.md`,
  `src/L/Ordinal/Stages.lagda.md`: read the source, never a report about it.**
- **`archive/dev/TASKS-archived.md` and `archive/src/2026-08-09-rud-route/`.**
  **This is Devlin's clause (b) and any route must pay it. Take SHAPE from the
  archive, never a claim**, and say what would NOT transfer.

Return an **ARCHIVE USED** section at `file:line`.

## LITERATURE (DD18)

**`dev/literature/devlin-II5.md:374` is the C1 row and `:387-389` is the
two-object verdict.** **`[LJ-1.228]` read `sl` and `sc` as Devlin's clause (b),
the LOCALIZED form. Say whether your build agrees with that reading**, and
whether Devlin proves clause (b) or assumes it. Return a **LITERATURE USED**
section.

## SCOPE (read)

`agents/tasks/LJ-1-233/lj-1.233-report.md` FIRST, whole.

## SCOPE (write)

`agents/tasks/LJ-1-237/` only. **No master.**

## MANDATORY RULES

Run `.venv/bin/python scripts/rules.py --for probe` and `--for build`.

- **D-1.** The abort criterion is fixed above.
- **C-38 as extended.** A hypothesis is discharged when something SUPPLIES it.
  **This task is C-38's target: two hypotheses, and every supplier is now on
  the table.**
- **DD8.** One estimate, and it names its basis.
- **P-l.** The floor is a comparable and NOT your price.
- **C-36.** Write the term you could not write.
- **C-44.** A brief's claim that something was never done is unchecked until
  you check it.
- **C-40, C-42, C-39. I-5, R-34. P-i, P-k, P-m, P-t, P-y, R-40. C-12, C-22.
  DD0, DD24, D-10, D-26, D-29, D-30.**

## CONSTRAINTS

- Count with `.venv/bin/python scripts/ledger.py`.
- Run `scripts/lint-prose.py --check` and `scripts/lint-agda.py --check`.
- DD23 freezes mathematical prose.
- Evidence is `file:line`. Write ASD-STE100.

## RETURN

**Lead with whether `sl` and `sc` BUILD, and with the written lines against
`[LJ-1.228]`'s floor of 0.25k to 0.35k joint.** Then the shared object's lines
apart from each hypothesis's own. Then any fourth wall, named at `file:line`.
Then the seconds with load and run count. Then whether the structure-parameter
form cost anything. **Mark every negative MEASURED or INFERRED.**
