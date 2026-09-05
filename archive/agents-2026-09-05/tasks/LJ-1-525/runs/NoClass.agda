{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.525] SPLIT MEASUREMENT.  Probe525.agda sections 1 to 3 only:
-- the match, the generic conversion and the obligation at the site.
-- Sections 4, 5 and 6 are removed.  Against runs/Control525.agda it
-- prices the obligation itself, clear of the chapter load.
--
-- ONE Agda process per run, GHCRTS="-A64m -I0 -M8g", the wide caliber.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-525.runs.NoClass {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula; var; _∈̇_; _∧̇_; ∃̇_; ∃̇∈ )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans; Lset )
open import L.Coding.Model {ℓ} using ( extAt; appAt )
open import L.Coding.Powerset {ℓ} lem using ( DefBody; DefAt )
open import L.Coding.Sequence {ℓ} lem using ( StepBody )
open import L.Condensation {ℓ} lem
  using ( extAtB; extAtB→extAt; module StepB; module StepAtB )

open import LJ-1-522.Probe522 {ℓ} lem using ( IsLimit; defPow-closed-noCode )

open import Cubical.Data.Nat using ( _+_ )
open import Cubical.Data.Vec using ( lookup; _∷_ )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL using ( _^_ ) renaming ( _⊨ᵐ_ to _⊨_ )

-- ---------------------------------------------------------------------
-- SECTION 1.  THE TWO LEAF FORMULAS AT ONE FRAME, AND W3.
--
-- D-10 IS ANSWERED IN THE TYPES.  The machine's leaf is the third
-- conjunct of `StepBody` (src/L/Coding/Sequence.lagda.md:116),
-- `DefAt zero (suc zero)`, and `DefAt u w = extAt u (∃̇ (∃̇ (DefBody w)))`
-- (src/L/Coding/Powerset.lagda.md:443).  So the unbounded leaf's `φ` is
-- NOT `DefBody w`: it is two existentials over it, and those two
-- existentials produce exactly the environment `(v ∷ c ∷ z ∷ γ)` that
-- `defPow-closed-noCode` reads (agents/tasks/LJ-1-522/Probe522.agda:363).
-- The bounded leaf `leafB` (src/L/Condensation.lagda.md:2399-2402) is
-- `extAtB` over the SAME two existentials, each bounded by K.
-- ---------------------------------------------------------------------

-- The machine's leaf condition: `DefAt`'s own body.
leafFo : ∀ {n} → Fin n → Formula S (suc n)
leafFo w = ∃̇ (∃̇ (DefBody w))

-- The bounded leaf's condition: the shape `leafB` puts under `extAtB`.
leafBFo : ∀ {n} → Fin n → Formula S (suc (suc (suc n))) → Formula S (suc n)
leafBFo K ψB = ∃̇∈ (var (suc K)) (∃̇∈ (var (suc (suc K))) ψB)

-- THE MATCH (W3).  `extAtB→extAt`'s third argument, at the leaf's own
-- φ, built from [LJ-1.522].
--
-- MEASURED, AND IT IS THE FINDING OF THIS TASK: the unbounded leaf does
-- NOT carry the recorded value's membership in K, which is
-- `defPow-closed-noCode`'s eighth argument.  What carries it is `bwd`,
-- the machine-to-story direction, which `extAtB→extAt` ALREADY asks
-- for.  So `inK` costs this conversion no hypothesis of its own.
leaf-inK :
    (α : V ℓ) → IsLimit α
  → ∀ {n} (w K : Fin n) (ψB : Formula S (suc (suc (suc n)))) (γ : S ^ n)
  → fst (lookup K γ) ≡ Lset α
  → ⟨ fst (lookup w γ) ∈ fst (lookup K γ) ⟩
  → ((x c v : S) → ⟨ (v ∷ c ∷ x ∷ γ) ⊨ ψB ⟩
                 → ⟨ (v ∷ c ∷ x ∷ γ) ⊨ DefBody w ⟩)
  → ((x : S) → ⟨ (x ∷ γ) ⊨ leafFo w ⟩ → ⟨ (x ∷ γ) ⊨ leafBFo K ψB ⟩)
  → (x : S) → ⟨ (x ∷ γ) ⊨ leafFo w ⟩
  → ⟨ fst x ∈ fst (lookup K γ) ⟩
leaf-inK α lim w K ψB γ qK W∈K leafFwd bwd x hx =
  PT.rec (snd (fst x ∈ fst (lookup K γ)))
    (λ { (c , (cK , hc)) → PT.rec (snd (fst x ∈ fst (lookup K γ)))
      (λ { (v , (vK , hv)) →
        defPow-closed-noCode α lim w K γ qK W∈K x c v vK
          (leafFwd x c v hv) })
      hc })
    (bwd x hx)

-- The story-to-machine direction of the leaf condition.  It is the
-- bounded existentials forgetting their bounds, over the ψ-level leaf
-- agreement.  `LeafAgree.back` (src/L/Condensation.lagda.md:7353-7358)
-- is what supplies that agreement, given its own telescope; this file
-- takes it as a hypothesis and builds nothing of it.
leaf-fwd :
    ∀ {n} (w K : Fin n) (ψB : Formula S (suc (suc (suc n)))) (γ : S ^ n)
  → ((x c v : S) → ⟨ (v ∷ c ∷ x ∷ γ) ⊨ ψB ⟩
                 → ⟨ (v ∷ c ∷ x ∷ γ) ⊨ DefBody w ⟩)
  → (x : S) → ⟨ (x ∷ γ) ⊨ leafBFo K ψB ⟩ → ⟨ (x ∷ γ) ⊨ leafFo w ⟩
leaf-fwd w K ψB γ leafFwd x =
  PT.rec (snd ((x ∷ γ) ⊨ leafFo w))
    (λ { (c , (_ , hc)) →
      PT.rec (snd ((x ∷ γ) ⊨ leafFo w))
        (λ { (v , (_ , hv)) → ∣ c , ∣ v , leafFwd x c v hv ∣₁ ∣₁ })
        hc })

-- ---------------------------------------------------------------------
-- SECTION 2.  THE CONVERSION, AT A GENERIC CARRIER (W2).
--
-- Nothing below is written at a fixed arity or a fixed slot.  The site
-- instances of sections 3 and 4 are instantiations of this one term and
-- add no content.
-- ---------------------------------------------------------------------
leaf-unbounds-gen :
    (α : V ℓ) → IsLimit α
  → ∀ {n} (y K w : Fin n) (ψB : Formula S (suc (suc (suc n)))) (γ : S ^ n)
  → fst (lookup K γ) ≡ Lset α
  → ⟨ fst (lookup w γ) ∈ fst (lookup K γ) ⟩
  → ((x c v : S) → ⟨ (v ∷ c ∷ x ∷ γ) ⊨ ψB ⟩
                 → ⟨ (v ∷ c ∷ x ∷ γ) ⊨ DefBody w ⟩)
  → ((x : S) → ⟨ (x ∷ γ) ⊨ leafFo w ⟩ → ⟨ (x ∷ γ) ⊨ leafBFo K ψB ⟩)
  → ⟨ γ ⊨ extAtB y K (leafBFo K ψB) ⟩
  → ⟨ γ ⊨ DefAt y w ⟩
leaf-unbounds-gen α lim y K w ψB γ qK W∈K leafFwd bwd =
  extAtB→extAt y K (leafBFo K ψB) (leafFo w) γ
    (leaf-fwd w K ψB γ leafFwd)
    bwd
    (leaf-inK α lim w K ψB γ qK W∈K leafFwd bwd)

-- ---------------------------------------------------------------------
-- SECTION 3.  THE OBLIGATION, AT THE SITE.
--
-- `StepB.leafB` (src/L/Condensation.lagda.md:2398-2402) is the bounded
-- leaf, at the body environment d ∷ w ∷ c ∷ z ∷ γ.  Its slot zero is
-- the definable powerset d and its carrier is the step's w at slot one,
-- which is why the conclusion below is `DefAt zero (suc zero)`: the
-- THIRD CONJUNCT OF THE MACHINE'S OWN `StepBody`
-- (src/L/Coding/Sequence.lagda.md:116), at the same environment and the
-- same two slots.  Nothing is restated and no adapter is written: the
-- two sides meet by unfolding.
-- ---------------------------------------------------------------------
leaf-unbounds :
    (α : V ℓ) → IsLimit α
  → ∀ {m} (ψ : Formula S (suc (suc (suc (4 + m))))) (sv b sf K : Fin m)
  → (γ : S ^ (4 + m))
  → fst (lookup (suc (suc (suc (suc K)))) γ) ≡ Lset α
  → ⟨ fst (lookup (suc zero) γ)
      ∈ fst (lookup (suc (suc (suc (suc K)))) γ) ⟩
  → ((x c v : S) → ⟨ (v ∷ c ∷ x ∷ γ) ⊨ ψ ⟩
                 → ⟨ (v ∷ c ∷ x ∷ γ) ⊨ DefBody (suc zero) ⟩)
  → ((x : S) → ⟨ (x ∷ γ) ⊨ leafFo (suc zero) ⟩
             → ⟨ (x ∷ γ) ⊨ leafBFo (suc (suc (suc (suc K)))) ψ ⟩)
  → ⟨ γ ⊨ StepB.leafB {m} ψ sv b sf K ⟩
  → ⟨ γ ⊨ DefAt zero (suc zero) ⟩
leaf-unbounds α lim ψ sv b sf K γ qK W∈K leafFwd bwd =
  leaf-unbounds-gen α lim zero (suc (suc (suc (suc K)))) (suc zero) ψ γ
    qK W∈K leafFwd bwd

