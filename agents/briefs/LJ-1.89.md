# LJ-1.89: prove witK by the finite-family route

tier: codex (default)

## GOAL

**Close witK.** The route is found and its decisive step is machine-checked.
**Assemble it end to end.**

## CWD

`/Users/alsg/Agentic/Bedrock`, on branch `two-tower-bridge`, **clean at
`6a3e4ee`**. HEAD is green.

## THE ROUTE, all three steps already measured

`[LJ-1.88]` found that the witness is FINITE and that finiteness carries it.
The steps, each green:

1. **`w ⊆ AllCodes A`** — `clo⊆All`, `src/ProbeLJ185B.agda:58-68`, 1.09 s.
2. **`AllCodes A` has a stage** — `src/ProbeLJ186A.agda:43-45`, 1.61 s, by
   definability and not by rank.
3. **A finite family of members of a stage is a DEFINABLE subset of it** —
   `finSet∈𝒟ₒ` (`src/L/Axioms/Basic.lagda.md:352-354`), and the successor
   stage IS the definable power set (`:196`). `finSet-stage`,
   `src/ProbeLJ188A.agda:56-61`, 1.72 s. **I re-ran this one myself at
   0.70 s user and read the lemma in the source.**

Then `Lset-out` and `𝒟ₒ∋⊆` give `w ⊆ Lset δ₁` for `δ₁ ∈ δ₀`, step 3 gives
`w ∈ Lset (sucV δ₁)`, and `Lset-mono` with `lam` a limit
(`src/L/BoundedSubset.lagda.md:1401`) gives `w ∈ Lset lam`.

**The one input the route needs is the frame hypothesis
`AllCodes A ∈ Lset lam`**, the same class as the frame's own `x ∈ Lset lam`
(`:1402`).

## WHAT TO BUILD

**One probe that assembles the route into a proof of the repaired `witK`**,
end to end, from:

- the frame hypothesis `AllCodes A ∈ Lset lam`;
- the premise `w ⊆ AllCodes A`;
- the delivered finiteness of the subformula closure
  (`src/L/Coding/InL.lagda.md:258-270`).

**Report the term at `file:line`, machine-checked.**

## THE HONEST WORD FOR THE RESULT

**C-38: a hypothesis is discharged when something SUPPLIES it.**
`BoundedSubsetAt` has no instantiation anywhere, so even a proved `witK` is
**STAGED, NOT DISCHARGED**, until a consumer supplies the frame hypothesis.
**Say that in those words**, and say who would supply it.

**Do not report a discharge.** This phase has reported a restatement as a
discharge three times, once in a commit of mine.

## THE ABORT CRITERION, fixed in advance per D-1

- **The assembly typechecks**: report the term and STOP. Do not carry the
  chain further, do not touch `levelIn` or `cover`.
- **A step does not compose**: STOP, write the term you could not write, and
  say which of the three steps fails to join.
- **Anything walls**: STOP, report the wall with its seconds.

**Work in `src/ProbeLJ189*.agda`.** If you touch a master it is GREEN when
you finish or you revert it.

## C-12, AND THIS IS NOT BOILERPLATE

`[LJ-1.80]` left **SIX agda processes alive at once**, all children of one
wrapper, all on the same probe, none killed. Each carried `-M8g`: 48 GB of
worst case on a 64 GB machine at load 19. **The owner caught it; no tool
did.**

**ONE agda process at a time. If a check does not return, KILL IT before you
start another, and report the wall with its seconds.**

## WHAT YOU MUST NOT DO

- **Do not weaken `witK`'s conclusion.**
- **Do not add a premise beyond the frame hypothesis and `w ⊆ AllCodes A`**
  without saying who supplies it.
- **Do not touch anything under `src/L/Coding/` or `src/V/`.**
- **Never `src/Everything.lagda.md`.**
- **Do not raise the heap cap.** C-12.
- **Read line numbers from the source, never from a report.**

## THE CLASSIFICATION I WANT ON EVERY NEGATIVE

State for every negative whether its deciding claim is **MEASURED** or
**INFERRED**, in those words. **A negative that rests on an inference sets no
verdict.**

## DD4

**Maximize the code the two proofs share, and write it generic.** One rule,
two ends, no metric and no checker, so it is stated in every brief and
answered in every return.

**Say whether the assembled route is generic in the stage**, so the J tower's
witness appears the same way.

## ARCHIVE (DD18)

- **`_build/lj-1.88-report.md`**, read WHOLE, and **`src/ProbeLJ188A.agda`**.
  The route and its decisive step.
- `_build/lj-1.87-report.md` and `src/ProbeLJ187B.agda`, the red assembly
  that the finiteness route replaces.
- `_build/lj-1.86-report.md`, `src/ProbeLJ186A.agda`; `_build/lj-1.85-report.md`,
  `src/ProbeLJ185B.agda`.
- `src/L/Axioms/Basic.lagda.md:190-200` and `:346-360`, the definable power
  set and the finite-family lemma. **Read-only.**
- `dev/LESSONS.md` **C-38 as extended**, C-35, C-36, D-30, read WHOLE.
- `archive/rud-route/` for SHAPE only.

Return an **ARCHIVE USED** section at `file:line`.

## LITERATURE (DD18)

**Banked.** `[LJ-1.88]` answered how Devlin bounds his witness. Say so in one
line and spend nothing.

## SCOPE (read)

`src/ProbeLJ188A.agda` FIRST, then `src/L/Axioms/Basic.lagda.md:346-360`,
then `src/L/Coding/InL.lagda.md:258-270`, then
`src/L/Condensation.lagda.md:6224-6240`.

## SCOPE (write)

`src/ProbeLJ189*.agda`, and any master **only if you revert it before
finishing**. Your report is `_build/lj-1.89-report.md`. **Never
`src/Everything.lagda.md`.**

## MANDATORY RULES FOR A BUILD

Run `python3 scripts/rules.py --for build` and read every statement.

- **C-38 as extended.** A hypothesis is discharged when something SUPPLIES
  it.
- **C-35.** A block with no consumer is UNTESTED. **Say it in those words.**
- **C-36.** Write the term you could not write.
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
- **D-1, D-8, D-10, D-26, D-29.**

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

Write `_build/lj-1.89-report.md` incrementally, skeleton first.

**Lead with whether the repaired `witK` is proved**, with the term at
`file:line` and its seconds. Then say in those words whether it is staged or
discharged, and who would supply the frame hypothesis. **Mark every negative
MEASURED or INFERRED.** Then the DD4 answer. Confirm every master is green or
untouched.
