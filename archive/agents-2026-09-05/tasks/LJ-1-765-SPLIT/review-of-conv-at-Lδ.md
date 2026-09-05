# Review of `conv-at-Lδ` (LJ-1.765-SPLIT): the type is uninhabited without transport

Task: LJ-1.765-SPLIT. Reviewer: coder. Date of the runs: 2026-09-02.

## THE VERDICT

**NO-GO.** The obligation's type, exactly as the brief spells it
(`agents/tasks/LJ-1-765-SPLIT/LJ-1.765-SPLIT.md:12-14`:

    conv-at-Lδ :
      (δ : S) (a : F.HS.ASt.SL)
      → ⟨ (Lset δ ∷ δ ∷ fst a ∷ []) P652.⊨ₚ P667.matrix₃ ⟩)

is not inhabited, and the reason is the brief's own second NO-GO
class: "the type is uninhabited without transport". It is not a heap
wall and not an elaboration failure: the statement's type elaborates
clean at the heavy caliber, 4.45 s at peak RSS 904658944 B, with the
designed hole the only diagnostic
(`agents/tasks/LJ-1-765-SPLIT/runs/floor765split.out:4-8,25`).
This review states why no body can exist, and records the corrected
targets beside the original (D-10).

## WHY NO BODY EXISTS

### 1. The parameter slot is read unguarded

`matrix₃ = isOrd-at-p ∧̇ φ₃` (`agents/tasks/LJ-1-667/Probe667.agda:73`),
slot order value, parameter, witness (`Probe667.agda:70-73`).
`isOrd-at-p` (`Probe667.agda:59-66`) binds slot 1, the parameter: its
first conjunct is `∀ x ∈ p, ∀ y ∈ x, y ∈ p` and its second is
`∀ x ∈ p, ∀ y ∈ x, ∀ w ∈ y, w ∈ x`. That is the tree's ordinality
matrix at arity 3: the same two conjuncts as `isOrdAt`
(`src/L/BoundedSubset.lagda.md:795-798`), for which the tree carries
the extraction GREEN in both directions:

- `isOrdAt-out : (x : S) → ⟨ (x ∷ []) ⊨ₚ isOrdAt ⟩ → IsOrd x`
  (`src/L/BoundedSubset.lagda.md:813`), proved by direct projection
  on the reading's Π structure (`:814-817`), and
- `isOrdAt-in` (`:818-821`).

The semantics is the Tarskian reading into the hProp algebra:
`γ ⊨ (∀̇∈ t φ) = ⋀ S (λ x → (x ∈ˢ ⟦ t ⟧ γ) ⇒ ((x ∷ γ) ⊨ φ))`
(`src/FOL/Semantics.lagda.md:102`), conjunction on `∧̇`
(`src/FOL/Semantics.lagda.md:94`). So the obligation's reading has,
as its first component, the transitivity proposition about the value
it puts in slot 1. The obligation puts the BARE VARIABLE `δ : S`
there. No row of the telescope (the brief's Build context,
`Probe765Split.agda.txt:52-57`) constrains δ.

**The counterexample is a tree-named set.** Take
`δ₀ := ⁅ sucV ∅ ⁆s`. Both formers are named in the tree:
`⁅_⁆s` with `self∈singl` and `singl-inj`
(`src/V/Coding.lagda.md:140-144,156`), and
`sucV N = N ∪ ⁅ N ⁆s` (cubical
`Cubical/HITs/CumulativeHierarchy/Constructions.agda:160-161`). Then
`sucV ∅ ∈ˢ δ₀` (`self∈singl`) and `∅ ∈ˢ sucV ∅` (the union's second
summand is the singleton of ∅), while `∅ ∈ˢ δ₀` would give
`∅ ≡ sucV ∅` by `singl-inj`, which is false: `∅ ∈ˢ sucV ∅` holds and
`⟨ ¬ (∅ ∈ˢ ∅) ⟩` holds by `∅-empty` (cubical
`Constructions.agda:86-88`). So the ⋀ in the first conjunct is empty
at δ₀, so `⟨ (Lset δ₀ ∷ δ₀ ∷ fst a ∷ []) ⊨ₚ matrix₃ ⟩` is empty for
every a, so a total `conv-at-Lδ` cannot exist.

The tree itself expects this reading to be strong: Probe667's
soundness residue plans to conclude ordinality facts FROM it
(`agents/tasks/LJ-1-667/Probe667.agda:79-91`, "isOrd-at-p is in the
formula so that ... Amb.isOrdAt-out plus Lset-only fire"). And the
predecessor kept the guard in exactly the position the brief dropped:
`grounded-from-complete` carries
`→ (δ : S) → IsOrd δ → ⟨ δ ∈ˢ HS.M ⟩ → ⟨ Lset δ ∈ˢ HS.M ⟩`
(`agents/tasks/LJ-1-765/Probe765.agda.txt:118`) in front of the Sigma
whose third component the brief lifted out
(`agents/tasks/LJ-1-765/Probe765.agda.txt:119-120`).

### 2. The witness slot is read uncarried

Even at ordinal δ, the second conjunct `φ₃` fails for most `fst a`.
`φ₃ = W3.erased` is [LJ-1.520]'s Matrix with the twelve tag slots
bounded by the witness: `three = wrap {2} s4`, the outermost of the
twelve wraps binding `∃̇∈ (var 2)`, the witness slot
(`agents/tasks/LJ-1-667/runs/W3.agda:25-28,56-59,75`), and
`γ ⊨ (∃̇∈ t φ) = ⋁ S (λ x → (x ∈ˢ ⟦ t ⟧ γ) ⊓ ((x ∷ γ) ⊨ φ))`
(`src/FOL/Semantics.lagda.md:103`). At `z := fst a` for an `a` whose
value lacks the tag elements, the join is empty. In
`grounded-from-complete` z is never arbitrary: it arrives from
`hullClosed` carrying `SatIn a ca cp`
(`agents/tasks/LJ-1-765/Probe765.agda.txt:149-158`), which is exactly
the hypothesis `conv0` consumes. The brief's signature has no such
carrier.

### 3. The salvage is closed: pinning the coordinates always costs the wall

The guarded form of the statement (guards restored) is true but is
inhabited only by `amb ∘ conv0`, the transport the brief forbids and
that heap-walls alone: 1454.50 s at peak RSS 5247418368 B at `-M4g`
(`agents/tasks/LJ-1-765/lj-1.765-report.md:16`, premise basis of this
dispatch). There is no third way, because no hull code's value is
definitionally `Lset δ` for a variable δ: `Code` is inductive syntax
with constructors `base` and `wit`
(`src/L/Hull.lagda.md:72-76`), `val (base m) = emb m` and
`val (wit k ψ cs) = Sum.rec (search k ψ (vals cs)) (λ _ → junk)`
(`src/L/Hull.lagda.md:88-91`), while `Lset` is a transfinite
recursion on membership (`src/L/Constructible.lagda.md:215-227`).
The equalities `fst (val ca) ≡ Lset δ` exist only propositionally and
only inside the truncation `codeOf` delivers. So ANY construction of
the reading at `(Lset δ, δ)` from code-level data must subst along
the `⊨ₚ` family, and that primitive is the measured wall: `amb`
heap-exhausted ALONE at 1454.50 s, peak RSS 5247418368 B, EXIT 251
(`agents/tasks/LJ-1-765/lj-1.765-report.md:16-18,113`).

## CORRECTED TARGETS, BESIDE THE ORIGINAL (D-10)

The original target, restated: a conversion export at `(Lset δ, δ)`,
no `amb`, for `[LJ-1.766]` to consume. The findings above say that
target does not exist as a standalone term. Two true variants exist;
both move a statement's TYPE, so both are judgements for the
mathematician, not terms this slot can write:

- **T1, move the coordinates out of the consumer.** A
  `grounded-from-complete` whose Sigma reads at the CODE coordinates
  `⟨ (fst (val ca) ∷ fst (val cp) ∷ z ∷ []) ⊨ₚ matrix₃ ⟩`. Every
  piece of that assembly is measured green: `conv0` (export, 10.41 s,
  `agents/tasks/LJ-1-764/lj-1.764-report.md:4`), `hullClosed`
  (260.11 s, `agents/tasks/LJ-1-765/lj-1.765-report.md:110`), the
  frame (12.63 s, `agents/tasks/LJ-1-765/lj-1.765-report.md:109`), and
  `amb` drops out entirely. The
  price is downstream: the soundness clause must be re-derived at
  code coordinates.
- **T2, restore the guards and re-cut the obligation.** `IsOrd δ` and
  the witness carrier in the signature, at the site clause (iii)
  actually consumes. The third Sigma component then has an
  inhabitant, but it is `mkWit`'s composition, and its non-transport
  half still needs a supplier at pinned coordinates, which finding 3
  says does not exist. T2 therefore reduces to T1 or to a new
  mathematical construction of the reading at `(Lset δ, δ)` that is
  not a transport, which is the 765 report's own escape hatch
  (`agents/tasks/LJ-1-765/lj-1.765-report.md:180-182`).

## WHAT WOULD REOPEN THIS ROUTE

A supplier whose TYPE already reads at `(Lset δ, δ)`: that is, a
mathematical construction of `⟨ (Lset δ ∷ δ ∷ z ∷ []) ⊨ₚ matrix₃ ⟩`
from Completeness or elementarity that never passes through code
coordinates. Finding 3 shows no such construction can be assembled
from the delivered pieces by type-checking alone; it would be new
mathematics, priced by the mathematician.
