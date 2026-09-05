# LJ-1.36: is the leaf reading really 2 seconds PER CLAUSE?

tier: codex (default)

## GOAL

`[LJ-1.35]` measured ONE clause's leaf reading and projected the other eleven
at about 2 seconds each. **It called that projection a hypothesis, not a
price, and it was right to.** Measure enough clauses to turn it into a band.
**This is a PROBE. Throw the code away.**

## CWD

`/Users/alsg/Agentic/Bedrock`, on branch `two-tower-bridge`.

## READ THIS FIRST: A NAMED CURE IS BUILT, NOT DEFERRED

**`dev/LESSONS.md` C-34** was admitted yesterday because two consecutive
returns named a cure, declined to price it, cited P-l, and were both
overturned: 0.334 to 0.0108, and 0.436 to 0.0072. **P-l forbids pricing a cure
by ANALOGY. It does NOT forbid building the cure and MEASURING it.** If you
name a cure, you have committed to building it or to reporting the wall that
stopped you.

## WHY THE RATE IS THE WRONG METER HERE, and `[LJ-1.35]` said so first

`[LJ-1.35]` measured 3.17 s over 132 lines, which I reproduced exactly. That is
0.0240 s per line. **But its own uncertainty 4 is the important sentence:**

> The rate meter is weak at this size. The cone is 1.13 seconds of the 3.19.
> The reading is a fixed per-clause cost, so more lines dilute the rate.
> DD24's seconds-per-line meter mostly measures the cone here.

**So the quantity that decides the block is SECONDS PER CLAUSE, not seconds per
line.** Twelve clauses at about 2 s each is about 24 s of a 99.6 to 147.7 s
budget. At 5 s each it is 60 s and the block is in trouble. **Nobody knows
which, because one clause was measured.**

## THE MEASUREMENT

**Measure the leaf reading for at least THREE more clauses, chosen for
DIFFERENT body shapes**, and report SECONDS PER CLAUSE for each with the cone
subtracted.

- **Choose the clauses by shape, not by convenience.** Say why each one is a
  different shape, and pick the ones you expect to be worst. A soft clause
  measures nothing (`[LJ-1.27]` learned this).
- **Subtract the module-load cone explicitly.** Measure an empty-but-imported
  control in the same session and report both the gross and the net.
- **Report the BAND across clauses**, and say whether 2 s per clause survives.

**GO: the band's top is at or below 3 s per clause.** Twelve clauses cost at
most 36 s and the block funds with room.
**NO-GO: the band's top is at or above 6 s per clause.** Twelve clauses cost 72
s or more, over half the whole budget, and the block needs a re-shape.
**A band that straddles is a real outcome. Report it and say where the mass
sits.**

## THE SECOND THING TO MEASURE, from the same probe

`[LJ-1.35]`'s uncertainty 2:

> The graph witness's own existentials, the code set `C`, the table `T` and the
> carrier `b`, need K-membership too in the substrate's bounded restatement. My
> probe bounds the code and the value, which are the story's own quantifiers.
> The witness memberships are substrate content of the same shape, unmeasured
> here.

**If those three are the same shape, measuring one of them is cheap and it
closes the gap.** Do it in the same probe and say whether they behave like the
story's own quantifiers or worse.

## WHAT IS SETTLED, so you do not re-derive it

- `[LJ-1.5]` delivered condensation block 1: 308 lines, **0.0079 s/line**,
  committed, on the erase route with NO placement (P-u).
- **Leg D funds.** `[LJ-1.34-R]` measured the identical theorem at 0.0079 on my
  own re-run against a return's 0.436. **Do not re-shape leg D.**
- **Δ₀ IS the target.** Delivered `Σ₁`'s only base is `σ-Δ₀`
  (`src/FOL/LevyHierarchy.lagda.md:73-75`), so "Σ₁ over a Σ₀ matrix" and "Δ₀ on
  the matrix" are one target here. **Do not re-open it.**
- **P-v, admitted yesterday:** never force a satisfaction-level conversion
  between two spellings of one formula. **Where the story is yours to write,
  write it in the machine's spelling from the start.** 59 ms against 29,415 ms.
- The substrate's real figures are **5,047 lines** (`_build/lj-1.2-gate.md:126`,
  T257 section 4.2) with an alternative **cone abstraction fork at 1.0 to 1.7k**
  (T51 section 5). **The "2.7 to 3.0k" figure that circulated was wrong** and
  came from a line pricing the whole remainder of route A.

## DD4, WHICH GOES IN EVERY BRIEF

**Maximize the code the two proofs share, and write it generic.** One rule,
two ends. It has NO metric and no checker by the owner's ruling, so it is
stated in every brief and answered in every return; the repetition is its only
enforcement.

`[LJ-1.33-R]` measured that the bound-drop layer is template and AMORTIZES
across clauses: six instantiations cost 1.72 s, so each extra clause was 0.08 s
there and the rate FELL.

**So there are two competing per-clause behaviours on the record: 0.08 s where
the layer amortized, and about 2 s here.** Say which one the leaf reading
follows and why. **If the leaf reading can be made to amortize the same way,
that is the cure, and C-34 says you build it rather than name it.**

## LITERATURE (DD18)

- `dev/literature/devlin-II5.md`, Step C. **Devlin binds every quantifier of
  the Def step by the concrete set `K(u)` INSIDE the matrix**, and says nothing
  about a per-clause cost because he writes the description once. **Say in one
  line whether his single-description shape is available here or whether the
  twelve clauses are a formalization artefact.** That is a real question and it
  may be worth more than the measurement.
- The errata do NOT cover Chapter II section 5. `[LJ-1.14]` verified it. **Do
  not re-check it.**

Return a **LITERATURE USED** section, with WHY NOT for anything skipped.

## ARCHIVE (DD18)

**Read these WHOLE. C-32 exists because a brief of mine named a SECTION and hid
the decisive probe.**

- **`_build/lj-1.35-report.md`** and **`src/ProbeLJ135.agda`**, your starting
  shape and the clause it measured.
- **`_build/lj-1.34-review.md`** and `src/ProbeDD25D5.agda`, the cleared leg D.
- **`_build/lj-1.33-review.md`**, where the layer AMORTIZED at 0.08 s per
  instantiation. **That contrast is your main question.**
- `src/L/Condensation.lagda.md` as delivered, and `_build/lj-1.5-report.md`.
- `src/L/Coding/Powerset.lagda.md` and `src/L/Coding/Model.lagda.md`, where the
  clause bodies live.
- `dev/LESSONS.md` is NOT archived and still binds. **P-l, P-m, P-n, P-t, P-u,
  P-v, D-1, D-10, D-26, C-32, C-33 and C-34 decide this block.**

Return an **ARCHIVE USED** section at `file:line`.

## MANDATORY RULES

**Run BOTH `python3 scripts/rules.py --for probe` and
`python3 scripts/rules.py --for recon`, and read each statement.**

- **D-1.** The smallest decisive miniature, GO or NO-GO with a price.
- **D-10.** Every figure here is a residue. Re-verify.
- **D-26.** Generation data or syntax. Say how it bears.
- **P-l.** Naming a built construction in a statement's TYPE is what costs.
  **It forbids pricing by analogy, not measuring.**
- **P-m.** The rate certifies a content class. **But read `[LJ-1.35]`'s
  uncertainty 4: at this size the meter mostly sees the cone.**
- **P-v.** One spelling, decided at the formula level.
- **C-12.** `GHCRTS="-A64m -I0 -M8g" agda <file>`, ONE process. A heap
  exhaustion is a WALL with its seconds; never raise the cap.
- **C-22.** Write the deliverable incrementally.
- **C-33.** I have tried to name the OBLIGATION and not an entry point. **If I
  named an API where I should have named a job, say so and use the better
  one.**
- **C-34.** Build the cure or report the wall.

## SCOPE (read)

`_build/lj-1.35-report.md` and `src/ProbeLJ135.agda` FIRST, then
`_build/lj-1.33-review.md` for the amortizing contrast, then the clause bodies.

## SCOPE (write)

`src/ProbeLJ136*.agda` only, and `_build/lj-1.36-report.md`. **No master. No
file under `dev/`. Never `src/Everything.lagda.md`.**

## CONSTRAINTS

- **Never commit and never push.**
- **Never `git checkout .`, `git stash`, `git reset --hard` or `git clean`.**
- **Do NOT run `make check`.**
- **Interfaces live in `_build/2.8.0/agda/src/`, NOT beside the source.**
- **Report cold seconds PER CLAUSE, gross and net of the cone**, noise rule:
  under 0.5 s or 5 percent, whichever is larger, is flat.
- **The machine is quiet and both Agda slots are yours.**
- **Evidence is `file:line`.**
- **Either answer is a full success.** Two NO-GOs in this lineage were
  overturned; **that is not pressure to return GO. Return what you measure.**
- Write ASD-STE100 in the report.

## RETURN

Write `_build/lj-1.36-report.md` INCREMENTALLY, skeleton first.

1. **THE VERDICT**, first line: the per-clause band, and GO, NO-GO or straddle.
2. **THE CLAUSES YOU PICKED**, and why each is a different shape.
3. **SECONDS PER CLAUSE**, gross and net of the cone, as a table.
4. **DOES 2 SECONDS SURVIVE?**
5. **THE THREE WITNESS MEMBERSHIPS**: same shape, or worse?
6. **AMORTIZING OR NOT**, against `[LJ-1.33-R]`'s 0.08 s. If a cure exists,
   you built it.
7. **THE PRICE OF THE NEXT BLOCK** on your numbers.
8. **DD4**: template or per-tower, per piece.
9. **LITERATURE USED.** 10. **ARCHIVE USED.** 11. **WHAT I AM NOT SURE OF.**
