# LJ-1.97: are the satisfier-in-K facts TRUE?

tier: codex (default)

## GOAL

**Test the family that the last three dispatches all leaned on and none
measured.** `tmKeyK` was refuted. **The same question has never been asked of
the other facts in its family, and a retirement decision is resting on the
answer.**

## CWD

`/Users/alsg/Agentic/Bedrock`, on branch `two-tower-bridge`, clean at
`3ce65f4` except `dev/PLAN.md`. HEAD is green. **A sibling agent holds the
other Agda slot.**

## WHY THIS DISPATCH EXISTS, and it is a correction of my own reading

`[LJ-1.96]` recommended retiring the three split masters. **Its verdict
overreaches its evidence, by its own classification.**

Its section 1 table is what fires its abort criterion. **Most rows of that
table read "MEASURED by listing; INFERRED no derivation".** Its own negative
2 says: "INFERRED FALSE, NOT CLAIMED AS MEASURED... No verdict rests on the
inference alone." **But the verdict does rest on it.** A listing measures
that the consumer does not STATE a fact. It does not measure that the fact
has no derivation, and it does not measure whether the fact is TRUE.

**So the retirement is not ruled and this dispatch is what must come first.**

## THE FAMILY, quoted from the source

The `satisfier-in-K` family, all in
`src/L/Condensation/TwelveAgree.lagda.md`: `envK-mem` `:98-101`, `envK-neg`
`:102-105`, `envK-top` `:106-109`, `envK-imp` `:110-113`, `envK-allin`
`:114-117`, `entryK` `:118-120`, `arSubK-mem` `:121-123`, `arSubK-neg`
`:124-126`, `arSubK-top` `:127-129`, `arSubK-imp` `:130-132`, `envInK-mem`
`:133-136`, `envInK-neg` `:137-140`, `envInK-top` `:141-144`, `envInK-imp`
`:145-148`, `valV` `:149-154`, `valW` `:155-160`, `wKfact` `:161-166`,
`subK₁-and` `:170-175`, `subK₀-and` `:176-181`, `subK₁-imp` `:182-187`,
`subK₀-imp` `:188-193`, `someEnv` `:194`, `subK-neg` `:195-200`, `keyK-neg`
`:201-204`, `succK` `:205-206`, `keyK-un` `:207-208`, `subK-un` `:209-214`,
`consK-exist` `:215-219`, `consK-forall` `:220-223`, `succK-allin`
`:224-228`, `keyK-allin` `:229-235`, `subK-allin` `:236-241`, `consK-allin`
`:242-243`. Plus `valK` `:86-88` and `valK-un` `:89-91`.

**Read every one of them from the source. Do not work from this list.**

## WHAT TO DO, in this order

**1. REFUTE WHAT IS FALSE. This is the cheapest and the most decisive.**

For each, ask the `tmKeyK` question: **is a conclusion universally
quantified over something the premises never constrain, or does it assert a
membership that regularity kills?** **Try to derive `Empty.⊥`.** Copy
`src/ProbeLJ195A.agda`, which is one line of real content.

**Report each as REFUTED or NOT REFUTED, and give the term for every
refutation.** `succK` `:205-206` and `keyK-un` `:207-208` have no premise at
all, per `[LJ-1.95]` section 2. **Start with those two.**

**2. For those that survive, test ONE for derivability.**

Take **`entryK`** (`:118-120`), which `[LJ-1.96]` says has no home because
the consumer holds only the C-slot and T-slot instances (`closedEntryK`
`:6501-6503`, `domEntryK` `:6504-6506`). **Is the general form derivable
from the machine side?** The environment machinery is
`src/L/Coding/Model.lagda.md`. **Say MEASURED yes, MEASURED no with the term
you could not write, or NOT ATTEMPTED.**

**3. Restate the Mem row at the extended frame, if budget remains.**

`[LJ-1.96]` named this the widest unmeasured term: one row at `KFacts` plus
the six site facts plus whatever survives step 1, cold-checked, with the
unsolved metas naming exactly what still has no home. **Do this only after
steps 1 and 2. A partial return on step 1 alone is a good return.**

## THE ABORT CRITERION, fixed in advance per D-1

- **Several of the family are refuted**: STOP after step 1 and report them
  all. **That is a route-level finding: it would mean the twelve-row
  agreement layer's design is wrong and not merely unwired, and it goes to
  the owner.**
- **None is refuted**: that is equally decisive in the other direction.
  Report it plainly, then do step 2.
- **Anything walls**: STOP, report the wall with its seconds.

**Work in `src/ProbeLJ197*.agda`. Do not touch any master. Do not repair, do
not delete, do not archive.**

## C-12, AND THIS IS NOT BOILERPLATE

`[LJ-1.80]` left **SIX agda processes alive at once**, all children of one
wrapper, all on the same probe, none killed. Each carried `-M8g`: 48 GB of
worst case on a 64 GB machine at load 19. **The owner caught it; no tool
did.**

**ONE agda process at a time, and a sibling agent holds the other slot. If a
check does not return, KILL IT before you start another, and report the wall
with its seconds.**

## WHAT YOU MUST NOT DO

- **Do not conclude a fact is false because nothing states it.** That is the
  error this dispatch corrects. **Unstated, underivable and false are three
  different findings.**
- **Do not repair, weaken or delete anything.**
- **Do not touch anything under `src/L/Coding/` or `src/V/`.**
- **Never `src/Everything.lagda.md`.**
- **Do not raise the heap cap.** C-12.
- **Read line numbers from the source, never from a report.**

## THE CLASSIFICATION I WANT ON EVERY NEGATIVE

State for every negative whether its deciding claim is **MEASURED** or
**INFERRED**, in those words. **A negative that rests on an inference sets no
verdict.** **This dispatch exists because a verdict was set on inferences.
Do not repeat that.**

**A refutation is MEASURED. A failure to refute is NOT a measurement that
the fact is true. Say so where it applies.**

## DD4

**Maximize the code the two proofs share, and write it generic.** One rule,
two ends, no metric and no checker, so it is stated in every brief and
answered in every return.

**Say whether a refuted fact, if any, is in content the J tower would also
inherit.**

## ARCHIVE (DD18)

- **`_build/lj-1.96-report.md`**, read WHOLE, and `src/ProbeLJ196A.agda`.
  **Read its section 1 table with the classification column in mind: that is
  what this dispatch tests.**
- **`_build/lj-1.95-report.md`** and **`src/ProbeLJ195A.agda`**, read WHOLE.
  **The refutation shape, and it is one line.**
- `_build/lj-1.93-report.md` and its three probes.
- `_build/lj-1.77-report.md` and `_build/lj-1.71-report.md`, the two earlier
  refutations of the same species.
- `src/L/Condensation/TwelveAgree.lagda.md:45-243`, the whole frame.
- `src/L/Coding/Model.lagda.md`, the environment machinery, for step 2.
- `dev/LESSONS.md` **C-38 as extended**, C-35, C-36, D-29, read WHOLE.

Return an **ARCHIVE USED** section at `file:line`.

## LITERATURE (DD18)

**Banked. Spend nothing.** Say so in one line.

## SCOPE (read)

`src/ProbeLJ195A.agda` FIRST, then
`src/L/Condensation/TwelveAgree.lagda.md:86-243`, then
`_build/lj-1.96-report.md` section 1.

## SCOPE (write)

`src/ProbeLJ197*.agda` only. Your report is `_build/lj-1.97-report.md`.
**No master. Never `src/Everything.lagda.md`.**

## MANDATORY RULES FOR A BUILD

Run `python3 scripts/rules.py --for build` and `--for probe`, and read every
statement.

- **C-38 as extended.** A closure hypothesis about a bounding set must be
  conditional. **The unconditional shape is refuted by regularity, always.**
- **C-36.** Write the term you could not write.
- **C-35.** A block with no consumer is UNTESTED.
- **D-1.** The smallest decisive miniature, then throw it away.
- **D-29, D-26, D-10, D-8, D-30.**
- **P-h, P-i, P-k, P-l, P-m, P-n, P-o, P-q, P-t, P-u, P-v, P-w** as the
  bundle gives them.
- **P-c, R-36, R-38.** Seal at the birth site; expose with a read lemma.
- **R-35, R-40.** State the membership SHALLOW and climb.
- **I-5.** The inference trap this tree has paid for.
- **C-12.** ONE agda process, cap never raised.
- **C-22.** Write the deliverable incrementally. **Write each refutation
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

Write `_build/lj-1.97-report.md` incrementally, skeleton first.

**Lead with the count: how many of the family are REFUTED, and name them**
with their terms at `file:line` and their seconds. Then the full table, one
row per fact, with REFUTED or NOT REFUTED. Then step 2's answer for
`entryK`. Then step 3 if you reached it. **Mark every negative MEASURED or
INFERRED, and never call a failure to refute a proof of truth.** Then the
DD4 answer. Confirm no master was touched.
