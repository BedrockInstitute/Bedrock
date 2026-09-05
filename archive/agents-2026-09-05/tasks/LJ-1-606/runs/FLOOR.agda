{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1-606]  FLOOR SLICE.  The obligation at a BARE META in the
-- probe's own trimmed frame, run BEFORE any proof (owner's ruling
-- 2026-08-23: measure the floor the elaboration frame itself costs,
-- before four 1800-second timeouts find it the expensive way).
--
-- The hole is the BARE-META shape [LJ-1.598] used and [LJ-1.602]
-- re-measured at 2.81 s (runs/floor-2.out there), NOT the hole under
-- a lambda with a where-definition, which [LJ-1.602] killed at its own
-- 200 s time-box (runs/floor-1.out there, no Agda exit line).
--
-- The frame imports src/ and nothing else, and takes the commute and
-- its three named faces by RESTATEMENT from the probe being built:
-- agents/tasks/LJ-1-606/Probe606.agda, sections 1 and 2.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-606.runs.FLOOR {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax
  using ( Formula; _∈̇_; _≐_; _∧̇_; _∨̇_; _⇒̇_; ¬̇_; ⊤̇; ⊥̇
        ; ∀̇∈; ∃̇∈; ∃̇_ )
open import FOL.LevyHierarchy
  using ( Δ₀; δ-∈; δ-≐; δ-∧; δ-∨; δ-⇒; δ-¬; δ-⊤; δ-⊥; δ-∀∈; δ-∃∈
        ; Σ₁; σ-Δ₀; σ-∃ )
open import FOL.Manipulation.Relabelling using ( mapFo )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ} using ( IsOrd; Lset )
open import L.BoundedSubset {ℓ} lem
  using ( module HullStage; module HullExt; module CollapseIso
        ; module DownReflect )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet; ∅ )
open InfinitySet {ℓ} using ( sucV )
open import Cubical.Data.Vec using ( map; _∷_; [] )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
module SV = hPropStructure 𝒮ᵥ
open SV using ( _∈ˢ_ )

module Frame (lam : SV.S) (ordλ : IsOrd lam)
             (succλ : (d : SV.S) → ⟨ d ∈ˢ lam ⟩ → ⟨ sucV d ∈ˢ lam ⟩)
             (X : SV.S)
             (X⊆Lλ : (z : SV.S) → ⟨ z ∈ˢ X ⟩ → ⟨ z ∈ˢ Lset lam ⟩)
             (∅∈λ : ⟨ ∅ ∈ˢ lam ⟩) where

  module HS = HullStage lam ordλ succλ X X⊆Lλ ∅∈λ
  module HE = HullExt lam ordλ X X⊆Lλ ∅∈λ
  module CI = CollapseIso HS.M HE.hullExt
  module DR = DownReflect lam ordλ X X⊆Lλ ∅∈λ
  module AbsπX = FOL.Absoluteness.Single 𝒮ᵥ
                 (λ x → x ∈ˢ HS.C.πX) HS.C.πX-trans

  -- THE COMMUTE, RESTATED ALONE (Probe606.agda section 1).
  Commute : Type (ℓ-suc ℓ)
  Commute =
    (δ : SV.S) (δ∈M : ⟨ δ ∈ˢ HS.M ⟩) → IsOrd (HS.C.π δ)
    → (Lδ∈M : ⟨ Lset δ ∈ˢ HS.M ⟩)
    → HS.C.π (Lset δ) ≡ Lset (HS.C.π δ)

  -- FACE E, RESTATED (Probe606.agda section 2).
  ElemDownAt : Type (ℓ-suc ℓ)
  ElemDownAt = DR.ElemDown

  -- FACE G+, RESTATED (Probe606.agda section 2).
  GraphStage : Formula CI.I.SM 3 → Type (ℓ-suc ℓ)
  GraphStage ψ =
    (q γ : CI.I.SM) → fst q ≡ Lset (fst γ)
    → ⟨ map DR.inL (q ∷ γ ∷ []) DR.ASt.AbsL.⊨ᵐ mapFo DR.inL (∃̇ ψ) ⟩

  -- FACE G-, RESTATED (Probe606.agda section 2).
  GraphAmbient : Formula CI.I.SM 3 → Type (ℓ-suc ℓ)
  GraphAmbient ψ =
    (x v γ : SV.S) → IsOrd γ
    → ⟨ (x ∷ v ∷ γ ∷ []) AbsπX.⊨ᵛ mapFo CI.I.g ψ ⟩
    → v ≡ Lset γ

  Crossing : Type (ℓ-suc ℓ)
  Crossing =
    Σ[ ψ ∈ Formula CI.I.SM 3 ] ( Δ₀ ψ × GraphStage ψ × GraphAmbient ψ )

  -- the frame's own syntax legs (Probe606.agda section 3)
  mapFo-Δ₀ : {K K' : Type (ℓ-suc ℓ)} {n : ℕ} (f : K → K')
           → (ψ : Formula K n) → Δ₀ ψ → Δ₀ (mapFo f ψ)
  mapFo-Δ₀ f (t ∈̇ u) d = δ-∈
  mapFo-Δ₀ f (t ≐ u) d = δ-≐
  mapFo-Δ₀ f (ψ ∧̇ χ) (δ-∧ d e) = δ-∧ (mapFo-Δ₀ f ψ d) (mapFo-Δ₀ f χ e)
  mapFo-Δ₀ f (ψ ∨̇ χ) (δ-∨ d e) = δ-∨ (mapFo-Δ₀ f ψ d) (mapFo-Δ₀ f χ e)
  mapFo-Δ₀ f (ψ ⇒̇ χ) (δ-⇒ d e) = δ-⇒ (mapFo-Δ₀ f ψ d) (mapFo-Δ₀ f χ e)
  mapFo-Δ₀ f (¬̇ ψ) (δ-¬ d) = δ-¬ (mapFo-Δ₀ f ψ d)
  mapFo-Δ₀ f ⊤̇ d = δ-⊤
  mapFo-Δ₀ f ⊥̇ d = δ-⊥
  mapFo-Δ₀ f (∀̇∈ t ψ) (δ-∀∈ d) = δ-∀∈ (mapFo-Δ₀ f ψ d)
  mapFo-Δ₀ f (∃̇∈ t ψ) (δ-∃∈ d) = δ-∃∈ (mapFo-Δ₀ f ψ d)

  Σ₁-carried : {K K' : Type (ℓ-suc ℓ)} (f : K → K') {n : ℕ}
             → (ψ : Formula K (suc n)) → Δ₀ ψ
             → Σ₁ (mapFo f (∃̇ ψ))
  Σ₁-carried f ψ d = σ-∃ (σ-Δ₀ (mapFo-Δ₀ f ψ d))

  -- THE OBLIGATION AT A BARE META, AT THE NAMED TYPE.
  inner-to-ambient : ElemDownAt → Crossing → Commute
  inner-to-ambient ed kit = ?
