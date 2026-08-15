{-# OPTIONS --cubical --safe --guardedness #-}

-- LJ-1.328 probe A. It lands nothing. It runs in agents/tasks/LJ-1-328/.
--
-- PART 1 verifies, by hand-written types and nothing else, that the definable
-- well-order of L is ALREADY an element of the model at EVERY ordinal, with
-- BOTH adequacy directions against the sealed ambient order `orderAt`.
-- Nothing here is new mathematics. The point is that the target statement
-- is derivable from the delivered names alone, at types written out by hand.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-328.ProbeLJ1328A {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula; var; _∧̇_; ∃̇_; ∃̇∈ )
open import FOL.LevyHierarchy using ( Δ₀; Σ₁; δ-∧; δ-∃∈; σ-Δ₀; σ-∃ )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Coding {ℓ} using ( pr )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans; Lset; IsOrd )
open import L.Ordinal {ℓ} using ( mem-ord )
open import L.Coding.Model {ℓ} using ( prʟ; prʟ-fst; prAtL; prAtL-adequate )
open import L.Choice.Step {ℓ} lem using ( Mem; relOf; orderAt )
open import L.Choice.Table {ℓ} lem
  using ( IsRel; Values; Entries; Domain; rel-rep )
open import L.Coding.Sequence {ℓ} lem using ( module RecShape )
open import L.Choice.Order {ℓ} lem
  using ( relL; relL-spec; relL-fill; relL-rep; StepAt; IsTable
        ; graph-only; graph-table; tableAt; table-out; table-in )

open import Cubical.Data.Sigma using ( _×_ )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁; ∣_∣₁; squash₁ )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL renaming ( _⊨ᵐ_ to _⊨_ )

-- PART 1. The target of the task, written out by hand.
--
-- Read it as: at every constructible ordinal α there is an ELEMENT r of the
-- model such that, for two members a and b of the tower at α, the object
-- membership of the coded pair in r holds exactly when the ambient definable
-- well-order at α puts a before b.
IsOrderElement : (α : V ℓ) → IsOrd α → S → Type (ℓ-suc ℓ)
IsOrderElement α oα r =
    ( (a b : Mem (Lset α)) → relOf (orderAt α oα) a b
      → ⟨ pr (fst a) (fst b) ∈ fst r ⟩ )
  × ( (a b : Mem (Lset α)) → ⟨ pr (fst a) (fst b) ∈ fst r ⟩
      → relOf (orderAt α oα) a b )

-- DELIVERED. One line, from the delivered names only.
orderIsAnLSet : (α : V ℓ) (hα : ⟨ isL α ⟩) (oα : IsOrd α)
              → Σ[ r ∈ S ] IsOrderElement α oα r
orderIsAnLSet α hα oα =
  relL α hα oα , (relL-fill α hα oα , relL-rep α hα oα)

-- PART 2. THE RESIDUAL: the order as ONE formula with the STAGE AT A SLOT.
--
-- The delivered `L.Hull`'s `φ<` (src/L/Hull.lagda.md:450-451) pins the order
-- element as a CONSTANT, `con ordL`, so it is one formula PER stage. This
-- part replaces that conjunct by the delivered graph `GraphAt`, which has
-- the stage AND the order element at SLOTS. Nothing else changes.
--
-- The point of the part is to measure what the stage-uniform form costs.

-- `GraphAt` is NOT exported from `L.Choice.Order`: `Described` opens it
-- without `public` (src/L/Choice/Table.lagda.md:406-409). I re-instantiate
-- the same generic module at the same delivered step, so my `R.GraphAt` and
-- the one inside `graph-only` are the same definition.
module R = RecShape StepAt

module Uniform {n : ℕ} (b u v : Fin n) (γ : S ^ n)
               (hβ : ⟨ isL (fst (lookup b γ)) ⟩)
               (oβ : IsOrd (fst (lookup b γ))) where

  ltAt : Formula S n
  ltAt = ∃̇ ( R.GraphAt zero (suc b)
           ∧̇ ∃̇∈ (var zero) (prAtL zero (suc (suc u)) (suc (suc v))) )

  private
    β : V ℓ
    β = fst (lookup b γ)

    r₀ : S
    r₀ = relL β hβ oβ

    tab : S
    tab = tableAt β hβ oβ .fst

    tabspec : IsTable β tab
    tabspec = tableAt β hβ oβ .snd .snd .fst

    reads : Domain tab β × Values tab β
    reads = table-out β oβ tab tabspec

    ents : Entries tab β
    ents c c∈ = ∣ relL (fst c) (snd c) (mem-ord {A = β} oβ (fst c) c∈)
                , table-in β oβ tab tabspec c
                    (relL (fst c) (snd c) (mem-ord {A = β} oβ (fst c) c∈)) c∈
                    (relL-spec (fst c) (snd c) (mem-ord {A = β} oβ (fst c) c∈)) ∣₁

    -- the graph holds of the DELIVERED order element, at the stage in a SLOT
    hgraph : ⟨ (r₀ ∷ γ) ⊨ R.GraphAt zero (suc b) ⟩
    hgraph = graph-table zero (suc b) (r₀ ∷ γ) tab oβ (reads .snd) ents
               (reads .fst) (relL-spec β hβ oβ)

    thePair : S
    thePair = prʟ (lookup u γ) (lookup v γ)

    hpr : ⟨ (thePair ∷ r₀ ∷ γ) ⊨ prAtL zero (suc (suc u)) (suc (suc v)) ⟩
    hpr = subst ⟨_⟩
      (sym (prAtL-adequate zero (suc (suc u)) (suc (suc v)) (thePair ∷ r₀ ∷ γ)))
      (prʟ-fst (lookup u γ) (lookup v γ))

  -- DIRECTION 1. The ambient comparison fills the stage-uniform formula.
  ltAt-fill : (a c : Mem (Lset β))
            → fst a ≡ fst (lookup u γ) → fst c ≡ fst (lookup v γ)
            → relOf (orderAt β oβ) a c → ⟨ γ ⊨ ltAt ⟩
  ltAt-fill a c qa qc lt =
    ∣ r₀ , (hgraph , ∣ thePair , (mem , hpr) ∣₁) ∣₁
    where
    mem : ⟨ fst thePair ∈ fst r₀ ⟩
    mem = subst (λ z → ⟨ z ∈ fst r₀ ⟩)
      (sym (prʟ-fst (lookup u γ) (lookup v γ) ∙ cong₂ pr (sym qa) (sym qc)))
      (relL-fill β hβ oβ a c lt)

  -- DIRECTION 2. The stage-uniform formula reads the ambient comparison back.
  ltAt-rep : (a c : Mem (Lset β))
           → fst a ≡ fst (lookup u γ) → fst c ≡ fst (lookup v γ)
           → ⟨ γ ⊨ ltAt ⟩ → ∥ relOf (orderAt β oβ) a c ∥₁
  ltAt-rep a c qa qc = PT.rec squash₁ atRel
    where
    atPair : (r : S) → IsRel β r
           → Σ[ w ∈ S ] ( ⟨ fst w ∈ fst r ⟩
                        × ⟨ (w ∷ r ∷ γ) ⊨ prAtL zero (suc (suc u)) (suc (suc v)) ⟩ )
           → ∥ relOf (orderAt β oβ) a c ∥₁
    atPair r hr (w , (w∈ , hw)) = ∣ rel-rep β oβ r hr a c inR ∣₁
      where
      qw : fst w ≡ pr (fst (lookup u γ)) (fst (lookup v γ))
      qw = subst ⟨_⟩
        (prAtL-adequate zero (suc (suc u)) (suc (suc v)) (w ∷ r ∷ γ)) hw

      inR : ⟨ pr (fst a) (fst c) ∈ fst r ⟩
      inR = subst (λ z → ⟨ z ∈ fst r ⟩) (qw ∙ cong₂ pr (sym qa) (sym qc)) w∈

    atRel : Σ[ r ∈ S ] ( ⟨ (r ∷ γ) ⊨ R.GraphAt zero (suc b) ⟩
                       × ⟨ (r ∷ γ) ⊨ ∃̇∈ (var zero)
                             (prAtL zero (suc (suc u)) (suc (suc v))) ⟩ )
          → ∥ relOf (orderAt β oβ) a c ∥₁
    atRel (r , (hg , hex)) =
      PT.rec squash₁ (atPair r (graph-only zero (suc b) (r ∷ γ) hg oβ)) hex

  -- NEGATIVE CONTROL 3, and it MEASURES the residual. Uncomment to see the
  -- refusal: the stage-uniform formula is NOT Σ₁, because `R.GraphAt` opens
  -- with an unbounded `∃̇` over the approximation and `R.ApproxAt` then puts
  -- TWO unbounded `∀̇` under it (src/L/Coding/Sequence.lagda.md:286-292).
  -- `Σ₁` has only `σ-Δ₀` and `σ-∃` and `Δ₀` has no `∀̇` constructor
  -- (src/FOL/LevyHierarchy.lagda.md:47-75), so no witness exists.
  -- Σ₁-ltAt : Σ₁ ltAt
  -- Σ₁-ltAt = σ-∃ (σ-Δ₀ (δ-∧ {!!} (δ-∃∈ {!!})))
