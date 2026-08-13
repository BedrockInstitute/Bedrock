# LJ-1.80: build a KFacts value at the hull, or write the term you cannot

tier: codex (default)

## GOAL

**Construct an inhabitant of `KFacts`.** Not a parameter, not a hypothesis:
a value, at the hull, from the hull's own closure properties.

## CWD

`/Users/alsg/Agentic/Bedrock`, on branch `two-tower-bridge`, **clean at
`03c7f0f`**. HEAD is green.

## WHY THIS AND WHY NOW

`KFacts` was uninhabitable and is now repaired (`[LJ-1.79]`). But **repaired
means "no longer known false", not "known true"**. `[LJ-1.77]`'s refutation
no longer typechecks; that is not the same as exhibiting a value.

**Nothing in the tree has ever constructed a `KFacts`.** Every module takes
it as a parameter. By C-35 that makes the whole band untested, and by C-38 a
hypothesis is discharged only when something SUPPLIES it.

**Two defects this phase were found by the first consumer and by nothing
else.** This dispatch is that consumer.

## THE FACTS TO SUPPLY

`KFacts` (`src/L/Condensation.lagda.md:5760-5768` after the repair) needs:

- twelve `tagEq` fields: the twelve numeral slots hold the twelve numerals;
- twelve `numK` fields: each numeral is in `K`;
- `innerK`, `innerPairK`, `pairK`: **`K` is closed under pairing, for
  arguments already in `K`**;
- `carrierK`: the `A` slot's members are in `K`;
- `arityK`: **`K` is transitive**, in the guarded form
  `(N v : S) → v ∈ N → N ∈ K → v ∈ K`.

**Read the repaired record before you build; do not work from this summary.**

## WHERE THE VALUE SHOULD COME FROM

The hull. `src/L/BoundedSubset.lagda.md` builds it, and the Skolem hull of a
set is closed under the operations and, after the Mostowski collapse,
transitive. `hull-closed` and `HullStage` are the names earlier dispatches
used; **find the delivered ones yourself and cite them at `file:line`.**

**You choose where the value is built and you say why.** If the natural site
is `BoundedSubset`, build it there. If the hull as delivered does not give a
closure property, that is the finding.

## THE ACCEPTANCE TEST

**A value of type `KFacts ...` that typechecks.** Report it at `file:line`.

**If you cannot build it, write the term you could not write** (C-36), and
say which field fails and what the hull would have to provide. **That is a
full deliverable and it is the answer the owner needs**, because it would
mean the band's hypotheses are not what the hull supplies.

**Do not weaken a field to make it constructible.** `[LJ-1.79]` guarded the
facts so they are satisfiable in principle; weakening them further to fit
what is convenient is the defect this phase has now paid for three times.

## THE ABORT CRITERION, fixed in advance per D-1

- **A `KFacts` value typechecks**: report it, report the master's seconds,
  and STOP. Do not go on to `levelIn`, `cover` or the post-leaf five.
- **A field cannot be supplied**: STOP at that field, write the term, and say
  what the hull would need.
- **Anything walls**: STOP, revert to green, report the wall with its
  seconds.

**Leave the tree GREEN whatever happens**, and say it is.

## WHAT YOU MUST NOT DO

- **Do not weaken any field of `KFacts`.**
- **Do not add a hypothesis to the site that builds the value.** A `KFacts`
  built from new assumptions supplies nothing: it moves the obligation. **If
  you need an assumption, that IS the term you could not write.**
- **Do not touch anything under `src/L/Coding/` or `src/V/`.**
- **Never `src/Everything.lagda.md`.**
- **Do not raise the heap cap.** C-12.
- Name probes `src/Probe*.agda`, never `.lagda.md`.

## THE CLASSIFICATION I WANT ON EVERY NEGATIVE

State for every negative whether its deciding claim is **MEASURED** or
**INFERRED**, in those words. **A negative that rests on an inference sets no
verdict.**

## DD4

**Maximize the code the two proofs share, and write it generic.** One rule,
two ends, no metric and no checker, so it is stated in every brief and
answered in every return.

**Say whether the construction is generic in the hull**, so the J tower
builds its own `KFacts` the same way, or whether it is specific to the L
tower's hull.

## ARCHIVE (DD18)

- **`_build/lj-1.79-report.md`**, read WHOLE. The repaired forms and their
  suppliers.
- **`_build/lj-1.77-report.md`** and `src/ProbeLJ177A.agda`, the refutation
  that made the repair necessary and no longer applies.
- `_build/lj-1.78-report.md`, the one-row proof that the guards work.
- `_build/lj-1.52-report.md` and `_build/lj-1.51-report.md`, which name the
  hull's delivered properties and what `levelIn`/`cover` still need.
- `dev/LESSONS.md` **C-38 as extended**, C-35, C-36, D-29, D-30, read WHOLE.
- `archive/rud-route/` for SHAPE only.

Return an **ARCHIVE USED** section at `file:line`.

## LITERATURE (DD18)

**The hull's closure is the mathematics you are building against.**
`dev/literature/devlin-II5.md` Step C and
`_build/literature/dev2.txt:1372-1385`. **Say in one line what Devlin's hull
is closed under**, and whether the delivered hull matches. Spend little.

## SCOPE (read)

`src/L/Condensation.lagda.md:5760-5768` (the repaired `KFacts`) FIRST, then
`src/L/BoundedSubset.lagda.md`'s hull construction, then
`_build/lj-1.79-report.md` section 1.

## SCOPE (write)

`src/L/BoundedSubset.lagda.md`, `src/L/Condensation.lagda.md`, and
`src/ProbeLJ180*.agda`. Your report is `_build/lj-1.80-report.md`. **No other
master. Never `src/Everything.lagda.md`.**

## MANDATORY RULES FOR A BUILD

Run `python3 scripts/rules.py --for build` and read every statement.

- **C-38 as extended.** A hypothesis is discharged when something SUPPLIES
  it. **This dispatch is that supply.**
- **C-35.** A block with no consumer is UNTESTED.
- **C-36.** Write the term you could not write.
- **D-29.** A shared layer propagates a fix and a defect at the same rate.
- **D-30.** Price what the CONSUMER needs.
- **P-h.** Module-parameterized, never function-parameterized.
- **P-k, P-l, P-m, P-n, P-o, P-q, P-t, P-u, P-v** as the bundle gives them.
- **P-c, R-36, R-38.** Seal at the birth site; expose with a read lemma.
- **R-35.** State the membership at the SMALL index and climb.
- **R-40.** State a membership witness SHALLOW and climb.
- **I-5.** The inference trap this tree has paid for.
- **C-12.** `GHCRTS="-A64m -I0 -M8g" agda <file>`, ONE process, cap never
  raised.
- **C-22.** Write the deliverable incrementally.
- **C-31, C-32, C-33, C-34, C-37.**
- **D-1, D-8, D-10, D-26.**

## CONSTRAINTS

- Never commit, never push, never `git checkout .`, `git stash`,
  `git reset --hard` or `git clean`.
- Typecheck every master you touch and every consumer. Do NOT run
  `make check`.
- **Run `scripts/check-fences.py --check` before you report anything closed**
  and say the master count.
- Count with `scripts/ledger.py`. Run `scripts/lint-prose.py --check` and
  `scripts/lint-agda.py --check` on every file you touch.
- DD23 freezes mathematical prose. Code and its own comments only.
- **Report the load average beside every absolute figure**, and say if the
  machine was not quiet.
- Evidence is `file:line`. Write ASD-STE100.

## RETURN

Write `_build/lj-1.80-report.md` incrementally, skeleton first.

**Lead with whether a `KFacts` value exists**, at `file:line`, with the
master's seconds. Then, field by field, where each one came from. Then, for
anything you could not build, **the term you could not write and what the
hull would have to provide.** **Mark every negative MEASURED or INFERRED.**
Then the DD4 answer. Confirm the tree is green.
