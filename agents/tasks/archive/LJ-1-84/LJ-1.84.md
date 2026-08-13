# LJ-1.84: is witK satisfiable at all, and if so at what stage?

tier: codex (default)

## GOAL

**Ask whether the fact is true before trying to supply it.** `witK` is the
chain's next obligation and it has the shape that has twice turned out to be
unsatisfiable.

## CWD

`/Users/alsg/Agentic/Bedrock`, on branch `two-tower-bridge`, **clean at
`ce66f72`**. HEAD is green.

## THE OBLIGATION

`src/L/Condensation.lagda.md:6227-6229`:

```agda
witK : (w : S) → ⟨ (w ∷ γ) ⊨ ((var (suc x) ∈̇ var zero)
             ∧̇ (closedAt zero ∧̇ shapedAt zero (suc A))) ⟩
     → ⟨ fst w ∈ fst (lookup K γ) ⟩
```

**Every `w` that contains `x`, is closed, and is shaped over `A`, lies in
`K`.**

## WHY I WANT SATISFIABILITY TESTED FIRST

**Twice this phase a telescope turned out to have no inhabitant**, and both
times the shape was a fact quantified over arbitrary sets:

- `TwelveAgree`'s `tagEq` (`[LJ-1.71]`), refuted in one step;
- `KFacts`'s `arityK`, `pairK`, `innerK`, `innerPairK` (`[LJ-1.77]`), refuted
  through `∈-irrefl`.

`witK` quantifies over ALL `w : S`. Its premise is a SATISFACTION condition,
not a membership in something already inside `K`, so **the transitivity route
that supplied `arityK` and `compK` does not reach it**.

**My own reading, and I want it checked rather than trusted.** A closed,
shaped `w` over `A` is a set of codes over `A`, so `w ⊆ AllCodes A`, which is
a set. But `w` ranges over CONSTRUCTIBLE subsets of that, and those can first
appear at arbitrarily high stages. **If `K = Lset λ` is a fixed limit stage,
there may be a constructible closed shaped `w` whose rank is at or above `λ`,
and then `witK` is false at that `K`.** That is INFERRED, and it is exactly
what this dispatch decides.

## THE QUESTION, in order

1. **Is `witK` refutable, as `arityK` was?** If a constructible closed shaped
   `w` of rank at or above `λ` exists for every `λ`, produce the refutation.
   **A machine-checked refutation is the most valuable outcome**, because it
   would mean the chain's statement needs repair before any more supply work.
2. **If it is not refutable, what does `K` have to be?** Say what property of
   `λ` makes `witK` true: closure of the stage under the code-set operation,
   a cardinal condition, or something the delivered tree already has.
3. **Only then, is it supplied at the stage `[LJ-1.80]` used**, or does the
   stage have to be chosen differently?

**Do not build a supply before answering 1 and 2.**

## THE ABORT CRITERION, fixed in advance per D-1

- **`witK` is refutable**: machine-check it, report it at `file:line`, and
  STOP. That is a C-38 finding and it outranks everything else.
- **`witK` is satisfiable and you name the condition on `K`**: report the
  condition, say whether the delivered tree gives it, and STOP.
- **You cannot settle it from the delivered tree**: say so plainly, name what
  would settle it, and STOP. **That is a full deliverable.**

**Work in `src/ProbeLJ184*.agda`.** If you touch a master it is GREEN when
you finish or you revert it.

## C-12, AND THIS IS NOT BOILERPLATE

`[LJ-1.80]` left **SIX agda processes alive at once**, all children of one
wrapper, all on the same probe, none of the earlier ones killed. Each carried
`-M8g`: 48 GB of worst case on a 64 GB machine at load 19. **The owner caught
it; no tool did.**

**ONE agda process at a time. If a check does not return, KILL IT before you
start another, and report the wall with its seconds.**

## WHAT YOU MUST NOT DO

- **Do not weaken `witK` to make it true.** If the honest statement needs a
  premise, say which premise and where a consumer would supply it. That is
  the C-38 repair shape and it is a report, not an edit.
- **Do not add a hypothesis to a construction site.**
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

**If `witK` needs a condition on the stage, say whether the J tower's stages
satisfy the same condition.**

## ARCHIVE (DD18)

- **`_build/lj-1.83-report.md`**, read WHOLE, and **`src/ProbeLJ183A.agda`**.
  The four instantiated modules and the transitivity route that does NOT
  reach `witK`.
- **`_build/lj-1.77-report.md`** and `src/ProbeLJ177A.agda`, the refutation
  shape you may be repeating.
- `_build/lj-1.80-report.md` and `src/ProbeLJ180A.agda`, the stage value.
- `_build/lj-1.52-report.md`, which names what the hull and the stage
  deliver.
- `src/L/Coding/CodeSet.lagda.md`, `AllCodes` and the closed/shaped
  predicates. **Read-only.**
- `dev/LESSONS.md` C-38 as extended, C-35, C-36, D-30, read WHOLE.
- `archive/rud-route/` for SHAPE only.

Return an **ARCHIVE USED** section at `file:line`.

## LITERATURE (DD18)

**This one may matter.** Devlin's condensation chooses the hull of
`L_α ∪ {x}` and its collapse; the bound in the formal proof is the analogue.
`dev/literature/devlin-II5.md` Step C. **Say in two lines what bounds Devlin's
witness**, and whether it is a stage or something else. Return a
**LITERATURE USED** section.

## SCOPE (read)

`src/L/Condensation.lagda.md:6224-6240` FIRST, then
`src/L/Coding/CodeSet.lagda.md`'s closed and shaped predicates, then
`src/ProbeLJ180A.agda`.

## SCOPE (write)

`src/ProbeLJ184*.agda`, and any master **only if you revert it before
finishing**. Your report is `_build/lj-1.84-report.md`. **Never
`src/Everything.lagda.md`.**

## MANDATORY RULES FOR A BUILD

Run `python3 scripts/rules.py --for build` and read every statement.

- **C-38 as extended.** A closure hypothesis over arbitrary sets is refuted
  by regularity; a hypothesis is discharged when something SUPPLIES it.
- **C-36.** Write the term you could not write.
- **C-35.** A block with no consumer is UNTESTED.
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

Write `_build/lj-1.84-report.md` incrementally, skeleton first.

**Lead with whether `witK` is refutable**, and if it is, the machine-checked
term at `file:line`. If it is not, the condition on `K` that makes it true
and whether the tree delivers it. **Mark every negative MEASURED or
INFERRED.** Then what bounds Devlin's witness. Then the DD4 answer. Confirm
every master is green or untouched.
