# LJ-1.169: `powIter`, the last term with no provenance

tier: opus (version `override`, set 2026-08-13; the head for every case is in
`scripts/dispatch_policy.py`, which is the only place the tables live)

## GOAL

**One term is left in the whole supply chain and it has no source.** Price it,
or prove it cannot be priced.

## WHAT IS LEFT, and the chain either side of it is measured

| | in-fence lines | state |
|---|---:|---|
| the assembly, `levelIn` and `cover` from one face | 17 | **MEASURED GREEN**, `[LJ-1.165]` |
| `K(u)`'s closure layer | 88 | **MEASURED GREEN**, `[LJ-1.166]` |
| pairing at an arbitrary limit | 35, net +15 | **MEASURED GREEN**, `[LJ-1.166]`, drop-in confirmed by `[LJ-1.167]` |
| the satisfaction layer | about 270 | priced from nine delivered comparables, `[LJ-1.168]` |
| **`powIter`** | **?** | **no source anywhere** |

**`[LJ-1.167]` named it:**

```agda
powIter : y ∈ˢ Lset δ → ∥ Σ[ k ∈ ℕ ] 𝒟ₒ y ∈ˢ Lset (sucIter k δ) ∥₁
```

## WHY IT HAS NO SOURCE, MEASURED THREE WAYS

- **Not in the tree as a proof.** It is carried as a HYPOTHESIS twice, under
  two names: `DefOK` (`src/L/Coding/Powerset.lagda.md:445-446`) and `PowOK`
  (`src/L/Coding/Sequence.lagda.md:131`). **Discharged in exactly ONE place**,
  `src/L/Hierarchy.lagda.md:169-171`, **and only after rewriting the value to a
  STAGE** through `isL-𝒟ₒ`. The general argument is not covered.
- **Not in the archive.**
- **NOT PROVED BY DEVLIN.** The closure is a parenthetical on his Lemma 2.4,
  and 2.4's proof reads **「The details are left as an exercise for the
  reader.」** I read that line at `_build/literature/dev2.txt:632`.
- **And the digest DROPS the fact entirely**, which is why no gate in this
  phase priced it.

## WHAT IS ALREADY TRUE, and it is your route

**`[LJ-1.167]` measured that the statement is NOT false.** It is true at every
limit, by rank accounting: **one L-stage absorbs every quantifier complexity,
so the satisfaction set sits at `δ+2` and the definable power at `δ+3`, a
uniform FINITE bump.** Marked INFERRED, and it is the argument to formalise.

**And the kit is already built and has never been used.**
`src/L/Ordinal/StageArith.lagda.md` is **live, green, and has ZERO consumers**
outside the catalog. It holds `sucIter` (`:34-36`), `+ω` (`:41-42`), `closedω`
and `boundCloses`, **and its own comment says it was written for this bound
question.** No brief in this wing has cited it.

**`isL-𝒟ₒ` is the delivered fact at a stage.** Find it, read it, and say what
it assumes.

## THE OBLIGATION, criterion fixed BEFORE the run (D-1)

**Prove `powIter` at a general `δ`, using the rank-accounting argument and the
delivered kit. Report the in-fence line count for THAT ONE lemma.**

- **GO at or below 80 lines.** Then the whole supply chain is priced end to end
  and `[LJ-1.7]` has a number with no gap in it.
- **NO-GO above it, or if the rank accounting needs a fact nothing supplies**:
  name that fact and price it. **A second unsourced term is a finding, not a
  failure.**
- **The rank accounting does NOT work in this tree's `𝒟ₒ`**: **STOP AND SAY SO
  FIRST.** That is the deepest finding available and it would send the supply
  back to the drawing board.

**Do not move the criterion after you see a number.**

## SEARCH BEFORE YOU PRICE. THIS IS THE PHASE'S MOST EXPENSIVE LESSON

**Three misses in five dispatches, all mine:**

- `[LJ-1.163]`: `ElemDown` was already supplied; my grep had excluded the file
  holding it.
- `[LJ-1.166]`: three of four closure classes already proved in
  `src/L/Choice/Name.lagda.md`, cited by no brief in this phase.
- `[LJ-1.167]`: the pairing lemma was in **the immediately preceding
  dispatch's own green probe**, offered in its own report, and I had read that
  report.

**`src/L/Ordinal/StageArith.lagda.md` and `src/L/Choice/` are the two places
this wing keeps failing to look. Look there first, and report what you find
before you report what you build.**

## WHAT YOU MUST NOT DO

- **Do not edit any master.** This is a probe.
- **Do not weaken the statement to make it provable.** A lemma that is true
  because it says nothing is worse than an open one.
- **Do not touch the three `*Agree` masters**, `src/L/Coding/Graph.lagda.md`,
  or `[LJ-1.164]`'s move.
- **A probe goes in `agents/tasks/LJ-1-169/`**, never in `src/`, tracked. **You
  may extend a COPY of an earlier probe; do not edit one in place.**
- **ONE agda process, `GHCRTS="-A64m -I0 -M8g"`, cap NEVER raised. Fix a
  wall-clock criterion in writing before each run.**
- Never `src/Everything.lagda.md`. Never commit, never push, never
  `git checkout .`, `git stash`, `git reset --hard` or `git clean`.
- Do not run `make check`; I run it.

## THE CLASSIFICATION I WANT ON EVERY NEGATIVE

**MEASURED or INFERRED, in those words.**

## DD4

**Maximize the code the two proofs share, and write it generic.** One rule, two
ends, no metric and no checker.

**A rank-accounting argument about stages is tower content if anything is.**
`[LJ-1.168]` measured the statement layer 100 percent template and recommended
writing the SUPPLY fixed, because abstracting the coding cone costs nine times
what it saves. **Say which side yours falls on, and do not price a variant you
did not write.**

## ARCHIVE (DD18)

- **`archive/src/2026-08-09-rud-route/L/Definability.lagda.md`**: the retired
  route's definable power. **Did it prove a closure at a general argument, or
  assume one?**
- `archive/src/2026-08-09-rud-route/L/Axioms/`, which `[LJ-1.167]` MEASURED as
  holding NO general-limit closure.
- **Take SHAPE, never a claim.** `[LJ-1.11]` ruled that route's condensation
  target classically FALSE.
- `agents/tasks/LJ-1-167/lj-1.167-report.md` and `LJ-1-166/`, read WHOLE.
- **`dev/LESSONS.md` C-38 as extended, D-1, P-l, P-i, C-36**, read WHOLE.

Return an **ARCHIVE USED** section at `file:line`.

## LITERATURE (DD18)

`_build/literature/dev2.txt:625-640` and `dev/literature/devlin-II5.md:240-260`.
**Devlin asserts the closure and proves nothing. Say what his 2.2 and 2.3 do
prove, since 2.4's proof says 「as in 2.2 and 2.3」, and whether that pattern
carries the general case.** Return a **LITERATURE USED** section.

## SCOPE (read)

`src/L/Ordinal/StageArith.lagda.md` WHOLE and FIRST, then `isL-𝒟ₒ` wherever it
is, then `src/L/Hierarchy.lagda.md:160-180`.

## SCOPE (write)

`agents/tasks/LJ-1-169/` only. **No master.**

## MANDATORY RULES

Run `.venv/bin/python scripts/rules.py --for probe` and read every statement.

- **D-1, DD8, C-38 as extended, C-35, P-l, P-i, C-12, C-22, C-36, C-39, C-40.**
- **D-10, D-26, D-29, D-30. C-31, C-32, C-33, C-34, C-37. I-5.**

## CONSTRAINTS

- Count with `.venv/bin/python scripts/ledger.py`.
- Run `scripts/lint-prose.py --check` and `scripts/lint-agda.py --check`.
- DD23 freezes mathematical prose.
- Evidence is `file:line`. Write ASD-STE100.

## RETURN

**Lead with what you found already delivered, THEN with GO or NO-GO and the
count.** Then whether the rank accounting formalises. Then what the whole
supply chain now costs end to end. Then the DD4 answer. **Mark every negative
MEASURED or INFERRED.**
