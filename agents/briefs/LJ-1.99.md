# LJ-1.99: does transitivity of K close entryK, and the arSubK family?

tier: codex (default)

## GOAL

**Test the tie that `[LJ-1.98]` did not reach.** My abort criterion stopped
it at the first candidate. **A second candidate is visible in the frame's own
facts and it is four applications of one delivered field.**

## CWD

`/Users/alsg/Agentic/Bedrock`, on branch `two-tower-bridge`, clean at
`1c43837` except `dev/PLAN.md`. HEAD is green. **A sibling agent holds the
other Agda slot and the load has been above 7.**

## WHAT `[LJ-1.98]` MEASURED, and what my brief stopped it from measuring

It tested ONE tie for `entryK`: the T-slot tie that `domEntryK` states.
**MEASURED not supplied**: the `EnvSet` site binds `z ∈ E` and
`pr x y ∈ z`, never `pr x y ∈ T`
(`src/ProbeLJ198A.agda:87`, exit 42). That measurement stands.

**My abort criterion then said STOP, and it obeyed.** The criterion was
written for a question with one candidate tie. **This question has more than
one, so the criterion was wrong and the return is not the last word.**

## THE SECOND CANDIDATE, from the frame's own facts

**`KFacts.arityK` (`src/L/Condensation.lagda.md:5769-5770`) IS transitivity
into K:**

```agda
arityK : (N v : S) → ⟨ fst v ∈ fst N ⟩ → ⟨ fst N ∈ fst (lookup K γ) ⟩
       → ⟨ fst v ∈ fst (lookup K γ) ⟩
```

**So if `E ∈ K`, the `EnvSet` site's own binders reach the conclusion in four
steps, each of them `arityK`:**

1. `z ∈ E` and `E ∈ K` give `z ∈ K`.
2. `pr x y ∈ z` and `z ∈ K` give `pr x y ∈ K`.
3. the singleton `⁅ x ⁆` is a member of `pr x y`, and `pr x y ∈ K`, so
   `⁅ x ⁆ ∈ K`.
4. `x ∈ ⁅ x ⁆` and `⁅ x ⁆ ∈ K` give `x ∈ K`. The same for `y` through the
   other component.

**This is a chain I inferred by reading. It is INFERRED and it sets no
verdict. Measure it.**

**And `E ∈ K` is not invented either.** The frame's `envK-mem`, `envK-neg`,
`envK-top`, `envK-imp` and `envK-allin`
(`src/L/Condensation/TwelveAgree.lagda.md:98-117`) conclude exactly that
from an `envSetAt` satisfaction, and **`[LJ-1.97]` did NOT refute any of
them.**

## WHAT TO DO

1. **Build the four-step chain** in a probe, from `arityK` alone plus the
   site's binders, and close `entryK`'s conclusion. The L-set level needs
   `prʟ-fst` (`src/L/Coding/Model.lagda.md:329`) and the singleton shape
   `[LJ-1.97]`'s probe used (`pairʟ X X`, `pairʟ-fst`,
   `src/L/Axioms/Numerals.lagda.md:127`). **`src/ProbeLJ197A.agda` already
   builds those pieces. Reuse them.**
2. **Then check the site.** Does the `EnvSet` use site
   (`src/L/Condensation.lagda.md:2815-2817`, and `z`'s binder at
   `:2508-2514`) supply `E ∈ K`, from the frame's `envK-*` family or from a
   binder? **Machine-check it.**
3. **Then do the same for the `arSubK-*` family** (`:121-132`). `[LJ-1.98]`
   read their intended tie as `x ∈ ar → ar ∈ K → x ∈ K`, **which is
   `arityK` exactly, once.** Check whether the site supplies `ar ∈ K`.
4. **Then `succK`, `keyK-un`, `keyK-neg`, `succK-allin`, `keyK-allin`** if
   budget remains. `[LJ-1.98]`'s table says every one of their sites binds
   `ar ∈ K`, and some also `a ∈ K`. **Verify that in the source. It is the
   claim the whole repair rests on and it was never machine-checked.**

## THE ABORT CRITERION, and it is deliberately different this time

**Do NOT stop at the first negative.** `[LJ-1.98]` stopped at one candidate
because I told it to, and the stop hid a live route.

- **Work through steps 1 to 4 in order and report each**, supplied or not
  supplied, with its term or its unsolved meta.
- **Stop only when the budget runs low, or when something walls.** Then
  report how far you reached.
- **If a step is measured not supplied, say so and CONTINUE to the next
  fact.** A per-fact answer is the deliverable.

**Work in `src/ProbeLJ199*.agda`. Do not touch any master.**

## C-12, AND THIS IS NOT BOILERPLATE

`[LJ-1.80]` left **SIX agda processes alive at once**, all children of one
wrapper, all on the same probe, none killed. Each carried `-M8g`: 48 GB of
worst case on a 64 GB machine at load 19. **The owner caught it; no tool
did.**

**ONE agda process at a time, and a sibling agent holds the other slot. If a
check does not return, KILL IT before you start another, and report the wall
with its seconds.**

## WHAT YOU MUST NOT DO

- **Do not weaken any row's conclusion.**
- **Do not invent a tie the site cannot supply.** The tie must be reachable
  from the site's own binders and the frame's unrefuted facts.
- **Do not assume `K` is transitive beyond what `arityK` states.** `arityK`
  is one step. **Four steps are four applications, and each needs its own
  membership. Check every one.**
- **Do not repair, delete or archive any master.**
- **Do not touch anything under `src/L/Coding/` or `src/V/`.**
- **Never `src/Everything.lagda.md`.**
- **Do not raise the heap cap.** C-12.
- **Read line numbers from the source, never from a report.**

## THE CLASSIFICATION I WANT ON EVERY NEGATIVE

State for every negative whether its deciding claim is **MEASURED** or
**INFERRED**, in those words. **A negative that rests on an inference sets no
verdict.** **My four-step chain above is INFERRED. Replace it with a
measurement in either direction.**

## DD4

**Maximize the code the two proofs share, and write it generic.** One rule,
two ends, no metric and no checker, so it is stated in every brief and
answered in every return.

**If the chain closes, it closes generically**: it uses one field and the
pair encoding, nothing about definability. **Say whether the repaired facts
would then be statable at a frame the consumer holds**, which is the test
`[LJ-1.93]` set and the one that matters.

## ARCHIVE (DD18)

- **`_build/lj-1.98-report.md`**, read WHOLE, and `src/ProbeLJ198A.agda`
  and `src/ProbeLJ198B.agda`. **Its table of use sites and intended ties is
  your work list. Verify each in the source.**
- **`src/ProbeLJ197A.agda`**, read WHOLE. **The singleton and pair pieces
  are already built there.**
- `_build/lj-1.97-report.md`, the ten refutations.
- `_build/lj-1.96-report.md` and `src/ProbeLJ196A.agda`, the positive
  pattern for a tied fact at a site.
- `src/L/Condensation.lagda.md:5734-5770`, the 29-field `KFacts`, and
  `:2764-2870`, the `EnvSet` module.
- `dev/LESSONS.md` **C-38 as extended**, C-35, C-36, D-29, D-30, read WHOLE.

Return an **ARCHIVE USED** section at `file:line`.

## LITERATURE (DD18)

**Banked. Spend nothing.** Say so in one line.

## SCOPE (read)

`src/ProbeLJ197A.agda` FIRST, then `src/L/Condensation.lagda.md:2764-2870`,
then `_build/lj-1.98-report.md` section 2.

## SCOPE (write)

`src/ProbeLJ199*.agda` only. Your report is `_build/lj-1.99-report.md`.
**No master. Never `src/Everything.lagda.md`.**

## MANDATORY RULES FOR A BUILD

Run `python3 scripts/rules.py --for build` and `--for probe`, and read every
statement.

- **C-38 as extended.** The tied fact must be conditional and the condition
  must be one the site can supply.
- **C-36.** Write the term you could not write.
- **C-35.** A block with no consumer is UNTESTED.
- **D-30.** Price what the CONSUMER needs.
- **D-1, D-8, D-10, D-26, D-29.**
- **P-h, P-i, P-k, P-l, P-m, P-n, P-o, P-q, P-t, P-u, P-v, P-w** as the
  bundle gives them.
- **P-c, R-36, R-38.** Seal at the birth site; expose with a read lemma.
- **R-35, R-40.** State the membership SHALLOW and climb.
- **I-5.** The inference trap this tree has paid for.
- **C-12.** ONE agda process, cap never raised.
- **C-22.** Write the deliverable incrementally. **Write each fact's answer
  into the report as it lands.**
- **C-31, C-32, C-33, C-34, C-37.**

## CONSTRAINTS

- Never commit, never push, never `git checkout .`, `git stash`,
  `git reset --hard` or `git clean`.
- Do NOT run `make check`.
- Run `scripts/lint-prose.py --check` and `scripts/lint-agda.py --check`.
- DD23 freezes mathematical prose.
- **Report the load average beside every absolute figure.**
- Evidence is `file:line`. Write ASD-STE100.

## RETURN

Write `_build/lj-1.99-report.md` incrementally, skeleton first.

**Lead with whether the four-step chain closes `entryK`**, with the term at
`file:line` and its seconds. Then whether the site supplies `E ∈ K`. Then
the per-fact table for `arSubK-*` and the five key facts: tie, site binder,
SUPPLIED or NOT SUPPLIED, machine-checked or not attempted. **Mark every
negative MEASURED or INFERRED.** Then say plainly whether the measurement
supports repair or retirement. Then the DD4 answer. Confirm no master was
touched.
