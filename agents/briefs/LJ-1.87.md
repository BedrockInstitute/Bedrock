# LJ-1.87: prove witK from the frame hypothesis, and price its supplier

tier: codex (default)

## GOAL

**Close witK, honestly.** Add the stage condition as a frame hypothesis,
prove `witK` from it, and say whether anything can ever supply it.

## CWD

`/Users/alsg/Agentic/Bedrock`, on branch `two-tower-bridge`, **clean at
`8af8206`**. HEAD is green.

## WHAT IS SETTLED, machine-checked

- **`witK` as written is FALSE** (`[LJ-1.84]`): shapedness leaves the arity
  slot free, so a junk member lifts a closed shaped set past the bound.
- **The premise `w ⊆ AllCodes A` kills that refutation** (`[LJ-1.85]`), and
  **the consumer supplies it**: `hasWitnessAt`'s subformula closure lies in
  `AllCodes A` member by member (`src/ProbeLJ185B.agda:58-68`).
- **A stage containing `AllCodes A` EXISTS** (`[LJ-1.86]`,
  `src/ProbeLJ186A.agda:43-45`, green), by definability and not by rank.
- **The proof cannot CHOOSE that stage**: `lam` is a module parameter at
  every frame reaching `witK` (`src/L/BoundedSubset.lagda.md:902-904`,
  `:1144-1146`, `:1396-1401`), and `Adeq`'s existential covers only `K'`.

**So the obligation moves to the frame**, as the hypothesis
`⟨ fst (AllCodes A) ∈ˢ Lset lam ⟩`, the same class as the tower's own
`x ∈ˢ Lset lam` at `:1145-1146`.

## WHAT TO DO

1. **State the frame hypothesis and prove `witK` from it**, together with
   `w ⊆ AllCodes A`. Report the term at `file:line`, machine-checked.
2. **Then price its supplier, and this is the half that matters.**
   `[LJ-1.86]` found that `BoundedSubsetAt` has **no instantiation anywhere**
   (zero hits outside `BoundedSubset.lagda.md`). So the consumer that must
   supply the new hypothesis **does not exist yet**.

   **Ask what would have to supply it**, at `file:line`: the tower's rank
   machinery, `Lset-mono`, `stage`, or something else. **Say whether the
   delivered tree could, and what it would cost.** DD8: one best-effort
   figure that names its basis.

**Do not claim a discharge.** With no instantiation, `witK` repaired is
staged, not discharged, and C-35 applies. **Say that in those words.**

## THE ABORT CRITERION, fixed in advance per D-1

- **`witK` follows from the two premises**: report the term, then the
  supplier's price, and STOP. Do not carry the chain further.
- **It does not follow even with both**: STOP, write the term you could not
  write. **That would mean a fourth statement-level defect and it outranks
  everything else.**
- **Anything walls**: STOP, report the wall with its seconds.

**Work in `src/ProbeLJ187*.agda`.** If you touch a master it is GREEN when
you finish or you revert it.

## C-12, AND THIS IS NOT BOILERPLATE

`[LJ-1.80]` left **SIX agda processes alive at once**, all children of one
wrapper, all on the same probe, none of the earlier ones killed. Each carried
`-M8g`: 48 GB of worst case on a 64 GB machine at load 19. **The owner caught
it; no tool did.**

**ONE agda process at a time. If a check does not return, KILL IT before you
start another, and report the wall with its seconds.**

## WHAT YOU MUST NOT DO

- **Do not weaken any conclusion.** Only the premises change.
- **Do not add a third premise to make it go through** without saying who
  supplies it. **Three times this phase a premise was added that nobody could
  satisfy.**
- **Do not touch anything under `src/L/Coding/` or `src/V/`.**
- **Never `src/Everything.lagda.md`.**
- **Do not raise the heap cap.** C-12.
- **Read line numbers and counts from the source, never from a report.**

## THE CLASSIFICATION I WANT ON EVERY NEGATIVE

State for every negative whether its deciding claim is **MEASURED** or
**INFERRED**, in those words. **A negative that rests on an inference sets no
verdict.**

## DD4

**Maximize the code the two proofs share, and write it generic.** One rule,
two ends, no metric and no checker, so it is stated in every brief and
answered in every return.

**Say whether the frame hypothesis is generic**, so the J tower's frames
carry the same one.

## ARCHIVE (DD18)

- **`_build/lj-1.86-report.md`**, read WHOLE, and `src/ProbeLJ186A.agda`.
  The stage's existence and the frame walk that fixes `lam`.
- **`_build/lj-1.85-report.md`**, read WHOLE, with `src/ProbeLJ185B.agda` and
  `src/ProbeLJ185C.agda`. The premise, its supply point and the red control.
- `_build/lj-1.84-report.md` and `src/ProbeLJ184A.agda`, the refutation.
- `src/L/BoundedSubset.lagda.md:900-960`, `:1140-1160`, `:1390-1410`, the
  frames that fix `lam`.
- `dev/LESSONS.md` **C-38 as extended**, C-35, C-36, D-8, D-30, read WHOLE.
- `archive/rud-route/` for SHAPE only.

Return an **ARCHIVE USED** section at `file:line`.

## LITERATURE (DD18)

**Banked.** `[LJ-1.86]` answered how Devlin gets his bound. Say so in one
line and spend nothing.

## SCOPE (read)

`src/ProbeLJ186A.agda` FIRST, then `src/ProbeLJ185B.agda`, then
`src/L/Condensation.lagda.md:6224-6240`, then
`src/L/BoundedSubset.lagda.md:1140-1160`.

## SCOPE (write)

`src/ProbeLJ187*.agda`, and any master **only if you revert it before
finishing**. Your report is `_build/lj-1.87-report.md`. **Never
`src/Everything.lagda.md`.**

## MANDATORY RULES FOR A BUILD

Run `python3 scripts/rules.py --for build` and read every statement.

- **C-38 as extended.** A hypothesis is discharged when something SUPPLIES
  it. **The second half of this brief is C-38.**
- **C-35.** A block with no consumer is UNTESTED. **Say it in those words.**
- **C-36.** Write the term you could not write.
- **D-8.** One best-effort figure, and it names its basis.
- **D-30.** Price what the CONSUMER needs.
- **P-h.** Module-parameterized, never function-parameterized.
- **P-k, P-l, P-m, P-n, P-o, P-q, P-t, P-u, P-v** as the bundle gives them.
- **P-c, R-36, R-38.** Seal at the birth site; expose with a read lemma.
- **R-35, R-40.** State the membership SHALLOW and climb.
- **I-5.** The inference trap this tree has paid for.
- **C-12.** ONE agda process, cap never raised, **kill a hung check before
  starting another.**
- **C-22.** Write the deliverable incrementally.
- **C-31, C-32, C-33, C-34, C-37.**
- **D-1, D-10, D-26, D-29.**

## CONSTRAINTS

- Never commit, never push, never `git checkout .`, `git stash`,
  `git reset --hard` or `git clean`.
- Typecheck what you touch. Do NOT run `make check`.
- **Run `scripts/check-fences.py --check` before you report anything closed**
  and say the master count.
- Run `scripts/lint-prose.py --check` and `scripts/lint-agda.py --check`.
- DD23 freezes mathematical prose.
- **Report the load average beside every absolute figure.**
- Evidence is `file:line`. Write ASD-STE100.

## RETURN

Write `_build/lj-1.87-report.md` incrementally, skeleton first.

**Lead with whether `witK` follows from the two premises**, with the term at
`file:line` and its seconds. Then who would supply the frame hypothesis and
what it would cost, with the basis named. Then say in those words whether
`witK` is staged or discharged. **Mark every negative MEASURED or INFERRED.**
Then the DD4 answer. Confirm every master is green or untouched.
