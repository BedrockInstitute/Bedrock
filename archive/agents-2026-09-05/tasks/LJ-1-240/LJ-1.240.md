# LJ-1.240: DD25 review of `[LJ-1.239]`, which refuted a type I put in the status screen

tier: opus (deepseek-subagent-mode). **The switch's ADVERSARIAL row, taken as
the table gives it.** The target was written by pi, so DD17's invariant holds:
the critic is never the same head as the author.

## GOAL

**`[LJ-1.239]` refused to supply `lh` and refuted the recipe at step 4.** DD25:
a negative CLOSES a line of work, and this one closes the step phase 1 was
building toward all day.

**The refutation, in one sentence:** **`lh`'s type names `φ₀ : Formula (⊥*) 2`,
a CLOSED parameter-free two-variable level-hood, but the stage level-hood
formula has arity `4 + n`, because its twelve tag numerals live in ENVIRONMENT
SLOTS.** **So the type as stated is not instantiable by the cited pieces.**

**I put that type into `dev/PLAN.md` section 0.0 as the phase's residue. If the
refutation holds, the screen is wrong and I want it corrected today.**

## WHAT I ALREADY RE-DERIVED, so spend your budget elsewhere

- **`src/L/Condensation.lagda.md:1125` reads, in the tree's own words:「numerals
  are slots, so every formula is constant-free.」** **MEASURED.** That single
  comment supports BOTH halves of the refutation: the bounded matrix is
  constant-free, AND its arity carries the slots.
- **`ProbeLJ1239A.agda` is green, exit 0, and its `.agdai` is on disk.**
- **`src/L/Coding/Sequence.lagda.md:52` imports exactly the `DefAt` trio**, as
  `[LJ-1.238]` reported.

## THE FOUR QUESTIONS

**1. IS THE ARITY CLAIM CORRECT?** The probe measured `countFo levelHoodB ≡ 0`
by `refl`, and reports that a `refl` check of `countFo LsetGraph ≡ 0` is
REFUSED. **Re-derive both at the source.** **Then check the arity claim itself:
is the stage level-hood really `4 + n`, and is 2 really what `lh` demands?**

**2. WHOSE DEFECT IS THE TYPE?** **`[LJ-1.237]` wrote `lh`'s type and its
`sl`/`sc` build green ON that type.** **So either the type is fine and the
recipe is wrong, or the type is wrong and `sl`/`sc` are green over an
uninhabitable hypothesis.** **Those are very different states and the project
needs to know which.** **A green build over an uninhabitable hypothesis is the
most dangerous shape on this list, because it looks like progress.**

**3. CAN `lh` BE RESTATED AT THE RIGHT ARITY, and would `sl`/`sc` survive?**
**This is the question that decides the next dispatch.** If restating `lh` at
arity `4 + n` costs `sl` and `sc` their 14 and 38 lines, say so. **If it costs
them nothing, the fix is cheap and I fund it tonight.**

**4. DID MY BRIEF CAUSE IT?** **My brief carried `[LJ-1.237]`'s DIFFICULTY,
which is about the UNBOUNDED `LsetGraph` carrying coding constants.**
**`[LJ-1.239]` measured that step 4 operates on the BOUNDED matrix, which is
constant-free, so the difficulty I wrote was about the wrong object.** **Both
readings reach arity greater than 2, so the conclusion survives. Say whether
the brief's wrong object cost the agent anything.**

## C-42 BOTH DIRECTIONS

**Does the refutation reach FURTHER than `lh`?** **`[LJ-1.228]` priced `sl` and
`sc` at about 0.15k each on `[LJ-1.123]`'s bands, and `[LJ-1.233]` called that a
FLOOR.** **If the object is at arity `4 + n` rather than 2, does the floor still
describe it?**

**Does it reach LESS far?** **Step 1 CLOSED**, measured at
`ProbeLJ1239A.agda:46-48`. **So the refutation is about step 4 alone and three
steps are untouched. Check that.**

## THE ABORT CRITERION, fixed BEFORE the run (D-1)

- **UPHELD.** The type is not instantiable as stated. **Then say what `lh`'s
  RIGHT type is**, or say that determining it needs a probe and name the probe.
- **OVERTURNED.** The type is fine and something else is wrong. **Give the
  evidence at `file:line`.**
- **UPHELD BUT MISATTRIBUTED.** The refutation is right and the CAUSE is the
  brief or `[LJ-1.237]`'s type rather than the recipe. **Six reviews today came
  back this way and I would rather know.**
- **UNDECIDABLE ON THE RECORD.** Say what is missing.

**Then, separately: ONE sentence on what `dev/PLAN.md` section 0.0 should say
about `[LJ-1.7]`'s residue tonight.**

## WHAT YOU MUST NOT DO

- **Do not edit any master, brief or report.** **Write your own report and
  nothing else.** **I write the status screen.**
- **DO NOT RUN AGDA.** Both Agda slots may be taken by siblings.
- **Do not re-litigate the three walls.** All settled by measurement today.
- **Do not price the assembly.** You judge a type and a refutation.
- Never commit, never push, never `git checkout .`, `git stash`,
  `git reset --hard` or `git clean`.
- Do not run `make check`.
- **Create your report file in your FIRST five minutes (C-22).**

## THE CLASSIFICATION I WANT ON EVERY NEGATIVE

**MEASURED or INFERRED, in those words.**

## DD4

**Maximize the code the two proofs share, and write it generic.** One rule, two
ends, no metric and no checker.

**`[LJ-1.237]` MEASURED that the joining layer above `lh` costs ZERO to write
generic, and `[LJ-1.238]` measured `L.Coding.Sequence`'s per-tower residual at
ZERO with 145 of 157 lines verbatim.** **So every DD4 figure in this area says
the same thing: the shared half is large and the per-tower half is small.**
**If `lh`'s real type is `4 + n` rather than 2, say whether that changes which
half it sits in.**

## ARCHIVE (DD18)

- **`agents/tasks/LJ-1-239/lj-1.239-report.md` and `ProbeLJ1239A.agda`**, both
  read WHOLE. **Read the probe, not the report's account of it.**
- **`agents/tasks/LJ-1-237/lj-1.237-report.md` and `ProbeLJ1237A.agda`**: the
  type under attack and the green `sl` and `sc` standing on it.
- `agents/tasks/LJ-1-233/lj-1.233-report.md`: the three walls and why the erase
  route does not close the carrier move.
- `agents/tasks/LJ-1-228/lj-1.228-report.md`: the floor and its bands.
- **`src/L/Condensation.lagda.md:1125`, `:1469-1471`,
  `src/L/Hierarchy.lagda.md:646`, `src/FOL/Manipulation/Parameters.lagda.md:260`:
  read the source, never a report about it.**
- **`archive/dev/TASKS-archived.md` and `archive/src/2026-08-09-rud-route/`.**
  **The retired route had to state a localized level-hood too. Take SHAPE from
  the archive, never a claim.**

Return an **ARCHIVE USED** section at `file:line`.

## LITERATURE (DD18)

**`dev/literature/devlin-II5.md:374` is the C1 row.** **Devlin states the
localized level-hood in one variable or two, not in `4 + n`. Say whether his
statement's shape is achievable here, or whether the slot representation forces
a different arity in any Agda formalization.** Return a **LITERATURE USED**
section.

## SCOPE (read)

`agents/tasks/LJ-1-239/lj-1.239-report.md` FIRST, whole.

## SCOPE (write)

`agents/tasks/LJ-1-240/lj-1.240-report.md` ONLY.

## MANDATORY RULES

Run `.venv/bin/python scripts/rules.py --for review` and read every statement.

- **C-38 as extended.** A hypothesis is discharged when something SUPPLIES it.
  **A green build over an UNINHABITABLE hypothesis is the failure this review
  exists to catch.**
- **D-10.** Price the truth of a recorded residue before pricing its proof.
- **C-42.** A refutation measures the site it names, never its extent.
- **C-44.** A brief's claim is unchecked until you check it. **My brief's
  DIFFICULTY was about the wrong object and `[LJ-1.239]` caught it.**
- **C-22, C-31, C-32, C-33, C-34, C-36, C-37, C-39, C-40. P-l. D-26, D-29,
  D-30. I-5. DD0, DD8, DD24, DD25.**

## CONSTRAINTS

- Run `.venv/bin/python scripts/lint-prose.py --check` on your report.
- **No em dash in any language.**
- Evidence is `file:line` on BOTH sides. Write ASD-STE100.

## RETURN

**Lead with ONE verdict word, then ONE sentence: is `sl`/`sc`'s green build
standing on an uninhabitable hypothesis?** Then the four questions, answered.
Then `lh`'s right type, or the probe that would find it. Then C-42 both
directions. Then what section 0.0 should say tonight. **Mark every negative
MEASURED or INFERRED.**
