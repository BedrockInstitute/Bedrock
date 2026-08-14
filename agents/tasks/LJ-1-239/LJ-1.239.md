# LJ-1.239: supply `lh`, the one term `[LJ-1.7]` still owes

tier: pi (deepseek-subagent-mode), **model `deepseek-v4-pro`**: this task runs
Agda and holds a slot. **The clock selected the mode.**

## GOAL

**`[LJ-1.237]` collapsed `[LJ-1.7]`'s residue from two hypotheses of unclear
content to ONE term with an exact type.** `sl` builds on it in 14 lines and
`sc` in 38, both green.

**The term:**

```agda
lh : (v b : SL) → IsOrd (fst b) → fst v ≡ Lset (fst b)
   → ⟨ (v ∷ b ∷ []) AbsL.⊨ᵐ embed φ₀ ⟩
```

**It enters `agents/tasks/LJ-1-237/ProbeLJ1237A.agda` as a MODULE PARAMETER.
MEASURED: nothing in `src/` supplies it.**

**Supply it.**

## THE RECIPE, and `[LJ-1.237]` wrote it with every piece at `file:line`

**Four steps, in this order:**

1. **`Lset-defines`** (`src/L/Hierarchy.lagda.md:646`): class-carrier belief in
   the UNBOUNDED graph `LsetGraphAt zero (suc zero)`, from
   `fst v ≡ Lset (fst b)`.
2. **`graph-in`** (`agents/tasks/LJ-1-124/ProbeLJ1124A.agda:205`): the BOUNDED
   `graphBndAt` from the unbounded graph. **It needs the `witnessK` site
   fact.** **This probe is green TODAY, exit 0, re-verified by `[LJ-1.235]`.**
3. **The witness is the internal hierarchy `hierL (fst b)`**, placed in a stage
   by **`hasReplacementL-bound`** (`agents/tasks/LJ-1-235/ProbeLJ1235A.agda`,
   18 lines, green today). **Its bound `βimg` must land below `α` via `succλ`
   and the level closure.**
4. **The carrier move, class to stage, over the Δ₀ matrix `graphBndAt`**, via
   `mkBoundedFo` (`src/L/Axioms/Separation.lagda.md:449`), `liftFo`
   (`src/FOL/Manipulation/Bounding.lagda.md:162`) and `abs₀`
   (`src/FOL/Absoluteness.lagda.md:122`).

## THE DIFFICULTY, ALREADY MET AND NAMED, so you do not rediscover it

**`[LJ-1.237]` MEASURED this and it is step 4's real shape:**

**The stage formula CANNOT be `Cnt.erase` of the class-carrier `LsetGraph`**,
because `LsetGraph` carries coding constants (`numeralL` and the code tags,
`src/L/Coding/Model.lagda.md:586`), so `countFo LsetGraph ≢ 0` and **the `refl`
erase is the only erase that is `refl`.**

**The parameter-free form is `absFo`
(`src/FOL/Manipulation/Parameters.lagda.md:260`), which raises the arity by
`countFo`.** **So the decode-in runs over LIFTED CONSTANTS, not over an erased
closed sentence.** **`[LJ-1.233]` already refuted the erase route
independently.**

## THE ABORT CRITERION, fixed BEFORE the run (D-1)

- **`lh` IS SUPPLIED.** Report the written lines and the seconds. **Then
  `[LJ-1.7]`'s four hypotheses are three SUPPLIED and one BUILT in shape,
  `[LJ-1.228]`'s floor becomes a NUMBER, and phase 1's blocking row moves for
  the first time since it opened.** STOP. **This is the outcome the whole day
  was building toward.**
- **THREE OF FOUR STEPS CLOSE.** **Say which step blocks and NAME its term**
  (C-36). **A named blocker at step 4 is worth more than a partial at step 2**,
  because steps 1 to 3 are all delivered or green.
- **MATERIALLY OVER THE FLOOR.** `[LJ-1.228]` said about 0.15k for the shared
  object, and `[LJ-1.233]` called it a floor with direction UP. **If you land
  far above, report both figures.**
- **A STEP'S PIECE IS NOT WHAT THE RECIPE SAYS.** **`[LJ-1.237]` wrote the
  recipe without running it.** **If a cited piece does not do what the recipe
  claims, say so at `file:line` and treat the recipe as refuted at that step.**
  C-44: a claim is unchecked until you check it.
- **A WALL.** **A single `agda` invocation past 20 MINUTES is a wall**:
  interrupt, report the ELAPSED SECONDS, bisect. **Every cut gets the SAME
  bound as its green control, and the control's elapsed time is reported BEFORE
  any cut is interpreted** (`[LJ-1.215]`'s law). **Your control is
  `ProbeLJ1237A.agda` at 2.19 s.**

## WHAT IS GREEN, so you assemble rather than invent

| file | what it is |
|---|---|
| `agents/tasks/LJ-1-237/ProbeLJ1237A.agda` | `sl` and `sc` over `lh` as a parameter, 168 non-blank, exit 0 |
| `agents/tasks/LJ-1-235/ProbeLJ1235A.agda` | `hasReplacementL-bound`, the stage bound, 18 lines, exit 0 |
| `agents/tasks/LJ-1-124/ProbeLJ1124A.agda` | the bounded decode both ways, 147 lines, exit 0 today |

**Start from `ProbeLJ1237A.agda` and replace the parameter with a proof.**
**Everything else in that file is measured and must not move.**

## WHAT YOU MUST NOT DO

- **Do not rebuild `sl` or `sc`.** They are green at 14 and 38 lines.
- **Do not re-litigate the three walls.** All settled by measurement today.
- **Do not port `L.Coding.Sequence`.** `[LJ-1.238]` may still be live in
  `agents/tasks/LJ-1-238/`. **Do not touch that directory.**
- **Do not edit any master.** This is a probe. **Nothing lands in `src/`, and a
  probe under `src/` is forbidden by I-5.**
- **Do not touch `src/L/Choice/Name.lagda.md`.** DD23 blocks a pending change.
- **A probe goes in `agents/tasks/LJ-1-239/`**, tracked, never deleted.
- **ONE agda process, `GHCRTS="-A64m -I0 -M8g"`, cap NEVER raised.** **Report
  the load beside every absolute figure**, discard a warm-up, and take at least
  three kept runs for any figure a decision rests on.
- **Report a heap exhaustion as a wall.** Never raise the cap. **`[LJ-1.234]`
  met one today and it was R-34's unpinned `InfinitySet` level meta, cured by
  `module IS = InfinitySet {ℓ}`. Check that before you call a heap wall
  yours.**
- **A probe whose module name predates the one-directory-per-task move needs
  its include path set from the task directory**, which `[LJ-1.235]` hit and
  recorded.
- **Create your report file in your FIRST five minutes (C-22).**
- Never `src/Everything.lagda.md`. Never commit, never push, never
  `git checkout .`, `git stash`, `git reset --hard` or `git clean`.
- Do not run `make check`; the orchestrator runs it.

## CITE THE REPORT THAT MEASURED, NEVER THE ONE THAT QUOTED

**C-44 entered `dev/LESSONS.md` today with my own session as its
measurement.** **The recipe above is `[LJ-1.237]`'s READING, not its build. You
are the measurement.**

## THE CLASSIFICATION I WANT ON EVERY NEGATIVE

**MEASURED or INFERRED, in those words.**

## DD4

**Maximize the code the two proofs share, and write it generic.** One rule, two
ends, no metric and no checker.

**`[LJ-1.237]` MEASURED that the joining layer costs ZERO to write generic:
`sl` and `sc` sit over `(α, ordα, φ₀, lh)` and name no tower.** **`lh` is the
per-tower instantiation point, Devlin's C1 row.**

**So write the per-tower proof so the J tower's version is a re-instantiation
and not a re-derivation.** **Say which of your lines are tower-neutral and
which are the L instantiation**, because that split IS the DD4 figure for the
last per-tower object in the phase.

## ARCHIVE (DD18)

- **`agents/tasks/LJ-1-237/lj-1.237-report.md` and `ProbeLJ1237A.agda`**, read
  WHOLE. **Sections 1 and 2 are your brief within this brief.**
- **`agents/tasks/LJ-1-235/lj-1.235-report.md` and `ProbeLJ1235A.agda`**: the
  stage bound and its five untouched consumers.
- **`agents/tasks/LJ-1-233/lj-1.233-report.md`**: which walls fell and why the
  erase route does not close the carrier move.
- `agents/tasks/LJ-1-124/lj-1.124-report.md` and `ProbeLJ1124A.agda`: the
  bounded decode.
- `agents/tasks/LJ-1-228/lj-1.228-report.md`: the delivered-component map and
  the floor.
- **`src/L/Hierarchy.lagda.md`, `src/L/Axioms/Separation.lagda.md`,
  `src/FOL/Manipulation/Bounding.lagda.md`,
  `src/FOL/Manipulation/Parameters.lagda.md`: read the source, never a report
  about it.**
- **`archive/dev/TASKS-archived.md` and `archive/src/2026-08-09-rud-route/`.**
  **This is Devlin's clause (b) and the retired route had to pay it too. Take
  SHAPE from the archive, never a claim.**

Return an **ARCHIVE USED** section at `file:line`.

## LITERATURE (DD18)

**`dev/literature/devlin-II5.md:374` is the C1 row, PER-TOWER, and
`:387-389` says the per-tower content is exactly two objects.** **Say whether
Devlin PROVES the localized level-hood or assumes it**, and if he proves it,
whether his argument is the four steps above. Return a **LITERATURE USED**
section.

## SCOPE (read)

`agents/tasks/LJ-1-237/lj-1.237-report.md` FIRST, whole.

## SCOPE (write)

`agents/tasks/LJ-1-239/` only. **No master.**

## MANDATORY RULES

Run `.venv/bin/python scripts/rules.py --for probe` and `--for build`.

- **D-1.** The abort criterion is fixed above.
- **C-38 as extended.** **A hypothesis is discharged when something SUPPLIES
  it. This task is that sentence, and nothing else.**
- **C-36.** Write the term you could not write.
- **C-44.** The recipe is a reading until you run it.
- **P-l.** The floor is a comparable and NOT your price.
- **DD8.** One estimate, and it names its basis.
- **C-40, C-42, C-39. I-5, R-34. P-i, P-k, P-m, P-t, P-y, R-40. C-12, C-22.
  DD0, DD24, D-10, D-26, D-29, D-30.**

## CONSTRAINTS

- Count with `.venv/bin/python scripts/ledger.py`.
- Run `scripts/lint-prose.py --check` and `scripts/lint-agda.py --check`.
- DD23 freezes mathematical prose.
- Evidence is `file:line`. Write ASD-STE100.

## RETURN

**Lead with whether `lh` is SUPPLIED, and with the written lines against
`[LJ-1.228]`'s floor of about 0.15k.** Then which of the four steps closed and
which did not, each at `file:line`. Then the tower-neutral against L-specific
split. Then the seconds with load and run count. **Mark every negative MEASURED
or INFERRED.**
