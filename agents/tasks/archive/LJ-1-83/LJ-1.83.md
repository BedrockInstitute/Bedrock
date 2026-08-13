# LJ-1.83: supply the code set and its decomposition facts

tier: codex (default)

## GOAL

The chain has its `KFacts` value and stops on the second obligation.
**Supply the code set `C` and the facts `compK` and `unCompK`**, and carry
the chain past `ShapesAgree`.

## CWD

`/Users/alsg/Agentic/Bedrock`, on branch `two-tower-bridge`, **clean at
`30f4fc8`**. HEAD is green.

## WHAT IS SETTLED

**The `KFacts` value reaches the chain.** `src/ProbeLJ180A.agda:186-226`
builds it at the limit stage `K = LsetS lam ordλ`, all twenty-nine fields.
`src/ProbeLJ182A.agda` carries it to the 15-element and 17-element frames by
`KFactsCons` (`:67-71`, `:75-101`), both green, and hands it to
`ShapesAgree`'s `f` parameter (`:117-121`), green.

**The stage is the site.** `Adeq`'s bound `K'` is existentially quantified,
so the proof chooses it; the hull is never required and no `isL` certificate
for `M` or `πX` is missing (`[LJ-1.81]`, and I checked the step myself).

**The block is the SECOND obligation.** `ShapesAgree`
(`src/L/Condensation.lagda.md:5816-5835`) also takes:

```agda
(C : S)
(compK   : (k : ℕ) (c N a b : S) → ⟨ fst c ∈ fst C ⟩
         → fst c ≡ pr (fst N) (pr (# k) (pr (fst a) (fst b)))
         → ⟨ fst N ∈ K-slot ⟩ × ⟨ fst a ∈ K-slot ⟩ × ⟨ fst b ∈ K-slot ⟩)
(unCompK : (k : ℕ) (c N a : S) → ⟨ fst c ∈ fst C ⟩
         → fst c ≡ pr (fst N) (pr (# k) (fst a))
         → ⟨ fst N ∈ K-slot ⟩ × ⟨ fst a ∈ K-slot ⟩)
```

**`KFacts` names only `A`, `K` and the twelve numerals.** No code set.

## THE HYPOTHESIS, and it is a hypothesis

`compK` has the shape `arityK` had, and `arityK` was supplied at the stage
from `layer-trans (Lset-layer lam)`, the stage's transitivity
(`src/ProbeLJ180A.agda:173-175`).

**A code `c ∈ C` that decomposes as a nested Kuratowski pair has its
components inside `c`, a few membership steps down.** On a transitive stage,
if `C` is chosen so that `C`'s members are in `K`, transitivity applied
repeatedly should place `N`, `a` and `b` in `K`.

**Test it. Do not assume it.** `[LJ-1.79]` and `[LJ-1.80]` both found that a
plausible-looking closure fact was not what it seemed.

## WHAT `C` SHOULD BE, and you decide it from the CONSUMER

**D-30: price what the consumer needs.** `C` is a code set, and the chain
above `ShapesAgree` uses it. **Read what `ClosedAgree`, `ShapedAgree`,
`WitnessAgree` and `SatGraphAgree` require of `C`**, and pick the value that
serves them, at `file:line`.

**Do not pick a `C` that makes `compK` easy and the consumers unusable.**
That is the defect this phase has paid for three times: a value at a
convenient site is not a value at the needed site.

**If the consumers force a `C` whose `compK` you cannot supply, that is the
finding.** Write the term you could not write.

## THE ABORT CRITERION, fixed in advance per D-1

- **`C`, `compK` and `unCompK` are supplied and `ShapesAgree` is fully
  instantiated**: carry the chain to the NEXT module that blocks, report
  where, and STOP.
- **A fact cannot be supplied**: STOP, write the term you could not write,
  and say what the stage would have to provide.
- **Anything walls**: STOP, report the wall with its seconds.

**Work in `src/ProbeLJ183*.agda`.** If you touch a master it is GREEN when
you finish or you revert it.

## C-12, AND THIS IS NOT BOILERPLATE

`[LJ-1.80]` left **SIX agda processes alive at once**, all children of one
wrapper, all checking the same probe, none of the earlier ones killed. Each
carried `-M8g`: 48 GB of worst case on a 64 GB machine, at load 19. **The
owner caught it; no tool did.**

**ONE agda process at a time. If a check does not return, KILL IT before you
start another, and report the wall with its seconds.**

## WHAT YOU MUST NOT DO

- **You may not weaken a statement and you may not narrow a direction.**
- **Do not add a hypothesis to make a supply go through.** A value built from
  new assumptions supplies nothing. **If you need an assumption, that IS the
  term you could not write.**
- **Do not touch anything under `src/L/Coding/` or `src/V/`.**
- **Never `src/Everything.lagda.md`.**
- **Do not raise the heap cap.** C-12.
- **Count fields and lines by reading, not by quoting a report.** My last
  brief said `KFacts` had 27 fields; it has 29, and the previous dispatch
  caught me.

## THE CLASSIFICATION I WANT ON EVERY NEGATIVE

State for every negative whether its deciding claim is **MEASURED** or
**INFERRED**, in those words. **A negative that rests on an inference sets no
verdict.**

## DD4

**Maximize the code the two proofs share, and write it generic.** One rule,
two ends, no metric and no checker, so it is stated in every brief and
answered in every return.

**Say whether your `C` and its facts are generic in the stage**, so the J
tower supplies its own the same way.

## ARCHIVE (DD18)

- **`src/ProbeLJ182A.agda`**, read WHOLE. The frames and the first
  instantiation.
- **`src/ProbeLJ180A.agda`**, read WHOLE. **The stage's `KFacts` value and,
  at `:173-175`, the transitivity route you are copying.**
- `_build/lj-1.82-report.md`, read WHOLE. Where the chain blocked and why.
- `_build/lj-1.81-report.md`, why the stage is the site.
- `_build/lj-1.79-report.md`, the repaired closure facts.
- `dev/LESSONS.md` C-38 as extended, C-35, C-36, D-30, D-29, read WHOLE.
- `archive/rud-route/` for SHAPE only.

Return an **ARCHIVE USED** section at `file:line`.

## LITERATURE (DD18)

**Banked.** `[LJ-1.81]` settled what Devlin's bounding set is. Say so in one
line and spend nothing.

## SCOPE (read)

`src/ProbeLJ182A.agda` FIRST, then
`src/L/Condensation.lagda.md:5816-5835` (`ShapesAgree`'s telescope), then
`src/ProbeLJ180A.agda:160-226`, then the consumers' `C` requirements.

## SCOPE (write)

`src/ProbeLJ183*.agda`, and any master **only if you revert it before
finishing**. Your report is `_build/lj-1.83-report.md`. **Never
`src/Everything.lagda.md`.**

## MANDATORY RULES FOR A BUILD

Run `python3 scripts/rules.py --for build` and read every statement.

- **C-38 as extended.** A hypothesis is discharged when something SUPPLIES
  it.
- **D-30.** Price what the CONSUMER needs. **This brief is D-30 applied to
  `C`.**
- **C-35.** A block with no consumer is UNTESTED.
- **C-36.** Write the term you could not write.
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

Write `_build/lj-1.83-report.md` incrementally, skeleton first.

**Lead with whether `C`, `compK` and `unCompK` are supplied**, at
`file:line`, and what `C` you chose and why the consumers accept it. Then how
far the chain then reached and what blocks next. **Mark every negative
MEASURED or INFERRED.** Then the DD4 answer. Confirm every master is green or
untouched.
