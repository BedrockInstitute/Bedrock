# Review of `StageCountedCoded`

The obligation is NOT written. This file is the obstruction, for the branch
`stop-stated`.

`agents/tasks/LJ-1-533/Probe533.agda` is GREEN, exit 0, three runs
(`runs/full-1.out` to `runs/full-3.out`). It carries no hole and no
postulate. **Every reduction quoted below typechecked.** A hole would have
made each of them a claim.

## THE STATEMENT

```
StageCountedCoded :
    (δ Lδ : S) → IsOrd (fst δ) → (fst Lδ ≡ Lset (fst δ))
  → InjL Lδ δ
```

It is `Probe533.agda:80-83`, named there as `StageCountedCodedᵀ`, and it is
`[LJ-1.523]`'s row B9 (`agents/tasks/LJ-1-523/Probe523.agda:258-261`).

## D-10. THE TYPE IS FALSE, AND THE BRIEF ASKED FOR THIS CHECK FIRST

**The brief's binding is `IsOrd (fst δ)` and nothing else.** No band
membership, no infinitude.

**The `Lδ` slot is not a restriction.** `LsetS`
(`src/L/Axioms/Basic.lagda.md:160-161`) makes the stage of any ordinal an
L-element on the nose, so `refl` fills the third hypothesis. `Probe533.agda:140-141`
is that fact, typechecked.

**So spending the type lands the AMBIENT statement at EVERY ordinal.**
`brief→ambient` (`Probe533.agda:145-150`) is

    StageCountedCodedᵀ
  → (δ : SL.S) → IsOrd (fst δ) → ∥ ⟪ Lset (fst δ) ⟫ ↪ ⟪ fst δ ⟫ ∥₁

by `readL` (`src/L/CantorBernstein.lagda.md:33-38`), and no hypothesis is
added on the way. `brief→ambient-at-numerals` (`Probe533.agda:160-164`)
instantiates it at every numeral `# n`.

**THE DELIVERED CHAPTER REFUSES EXACTLY THAT.** Two `file:line` facts:

1. `stage-card-upper` binds `⟨ α ∈ˢ ω ⟩ → Empty.⊥`
   (`src/L/StageCardinal.lagda.md:564-565`). The infinitude is a
   HYPOTHESIS of the shadow. The brief's type has none.
2. At a finite δ the chapter's own branch does not go to δ. It goes to ω:
   `fin-inj : (δ : S) → ⟨ δ ∈ˢ ω ⟩ → ⟪ Lset δ ⟫ ↪ ⟪ ω ⟫`
   (`src/L/StageCardinal.lagda.md:488-490`), consumed at `:548` by
   `comp-inj (fin-inj δ δ∈ω) (WOEmb.ω-inj α oα infα)`. A chapter that could
   land `⟪ Lset δ ⟫ ↪ ⟪ δ ⟫` at a finite δ would not need that branch and
   would not need `ω-inj` to carry it.

**WHAT I DID NOT MEASURE.** I did not prove `⟪ Lset δ ⟫ ↪ ⟪ δ ⟫` false in
Agda at any named finite δ. Exhibiting the witnesses of `𝒟ₒ (Lset (# 2))`
needs the definability machinery and I did not price it. **What is measured
is that the brief's type is NOT REACHABLE from the delivered shadow**, and
that the shadow's own author excluded the finite case by hypothesis. That
is enough to stop.

## THE CORRECTED TARGET

`Probe533.agda:222-228`:

```
StageCountedCoded′ᵀ : V ℓ → Type (ℓ-suc ℓ)
StageCountedCoded′ᵀ α₀ =
    (δ Lδ : SL.S) → IsOrd (fst δ)
  → ⟨ fst δ ∈ˢ sucV α₀ ⟩ → (⟨ fst δ ∈ˢ ω ⟩ → Empty.⊥)
  → (fst Lδ ≡ Lset (fst δ))
  → InjL Lδ δ
```

Both side conditions of the shadow, added back. **It is not weaker than the
delivered ambient statement**: `corrected→ambient` (`Probe533.agda:264-272`)
recovers `∥ ⟪ Lset (fst δ) ⟫ ↪ ⟪ fst δ ⟫ ∥₁` from it.

**THE BAND CONDITION IS NOT THE BLOCK.** `α₀` is a module parameter of
`L.StageCardinal` (`src/L/StageCardinal.lagda.md:16`), so at a single δ the
consumer takes `α₀ := δ` and `self∈sucV` (`src/V/Model.lagda.md:236-237`)
pays `⟨ δ ∈ˢ sucV δ ⟩`. `shadow-at-self` (`Probe533.agda:209-213`) is that,
typechecked.

## THE BLOCK: NOTHING CODES AN AMBIENT INJECTION

**This is `[LJ-1.414]`'s wall and `[LJ-1.441]`'s wall, at a third site.**
It is not a new obstruction and I do not claim it as one.

The missing type is `AmbToCodeᵀ` (`Probe533.agda:111-114`):

```
AmbToCodeᵀ =
    (a b : SL.S) → ⟪ fst a ⟫ ↪ ⟪ fst b ⟫
  → ∥ Σ[ F ∈ SL.S ] InjCode F a b ∥₁
```

Given it, B9's corrected target follows and NOTHING ELSE is wanted:
`Bill.reduce` (`Probe533.agda:236-241`) is

    reduce : AmbToCodeᵀ → StageCountedCoded′ᵀ α₀

under the shadow's own module telescope. At the site, the narrower
`StageGraphᵀ` (`Probe533.agda:246-252`) suffices and
`Bill.reduce-at-site` (`Probe533.agda:253-259`) spends it.

**WHY NOTHING PAYS IT.** `_↪_` is a bare function with an injectivity proof
(`src/L/Cardinal.lagda.md:47-48`). The only two generators of an L-element
set are `hasSeparationL` (`src/L/Axioms/Full.lagda.md:144-146`) and
`hasReplacementL` (`:277-280`), and **both take a `Formula` in their type**.
An element of `_↪_` carries no `Formula`. This is a type-level fact, not a
count: there is no way to call either generator without one.

## THE SECOND UNPAID INPUT, AND IT IS SMALLER

`L.StageCardinal` also binds an UNTRUNCATED square-law family
(`src/L/StageCardinal.lagda.md:17-19`), written out as `SqFamily`
(`Probe533.agda:183-184`). What `src/` delivers is TRUNCATED:
`sq-trunc-closed` (`src/L/SquareLawClosed.lagda.md:325-328`), re-typed and
typechecked at `Probe533.agda:190-193`. The band and the infinitude match;
only the grade differs.

**THE CORRECTED TARGET'S CONCLUSION IS ITSELF TRUNCATED**, because
`InjL a b = ∥ Σ[ F ∈ S ] InjCode F a b ∥₁` (`src/L/GCH.lagda.md:37-38`). So
a route that builds the coded statement DIRECTLY, rather than through the
untruncated ambient `stage-card-upper`, can spend `sq-trunc-closed` by
`PT.rec`. **The untruncated ambient conclusion cannot.** That is a reason to
prefer a coded restatement at the chapter's own site over a crossing after
the fact, and it is section `## WHAT THE NEXT BRIEF SHOULD KNOW` of the
report.

## WHAT WAS NOT DONE

No axiom, no postulate, no `src/` change. `AmbToCodeᵀ` and `SqFamily` appear
ONLY as hypotheses of reductions, never as inhabited terms. I did not weaken
`InjL` to an ambient injection. I did not rebuild `stage-card-upper` or
`ordL`: both are instantiated or imported. I did not touch B5.

## C-42

**COUNT of `src/` sites that carve the graph of a map as an L-element: 5.**

| site | the `Formula` | the graph |
|---|---|---|
| `src/L/InjChain.lagda.md:339` | `compFo` (`:222`) | composition |
| `src/L/InjChain.lagda.md:480` | `inclFo` (`:445`) | inclusion |
| `src/L/Absorption.lagda.md:413` | `shiftFo` (`:224`) | shift |
| `src/L/Coding/Key.lagda.md:272-273` | `envFoB` (`:246`) | environment |
| `src/L/Coding/Injection.lagda.md:212` | `rangeGraph F` (`:158`) | range of an ALREADY CODED `F` |

**COUNT with a `Formula`: 5. COUNT that take a bare `_↪_`: 0.**

This is my own sweep at today's tree and NOT `[LJ-1.414]`'s. That one
counted 6 by its own criterion (`agents/tasks/LJ-1-414/review-of-amb-to-coded.md`,
section C-42); I did not reuse its number and the two criteria are not the
same.

**AND THE SHAPE EXTENDS FURTHER THAN B9.** `[LJ-1.523]`'s row B10,
`SuccIntoPower = (κ δ : S) → SuccCardL δ κ → InjL δ (𝒫 κ)`
(`agents/tasks/LJ-1-523/Probe523.agda:266-268`), concludes an `InjL` and is
the same shape. **Row B7 is NOT.** `AbsorbsAt`
(`agents/tasks/LJ-1-523/Probe523.agda:234-238`) concludes
`⟪ Lset α ∪ ⁅ x ⁆s ⟫ ↪ ⟪ Lset α ⟫`, an AMBIENT injection. It wants no code
and this obstruction does not touch it. The brief's sentence "B7 and B10 are
the same shape" is half right, and the half that is wrong would have made a
successor brief price B7 against a wall it does not meet.
