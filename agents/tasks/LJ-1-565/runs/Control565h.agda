{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.565] CONTROL h.  THE SUCCESSOR STEP, IN THE FORM THE
-- MEASUREMENT SAYS IS PAYABLE.
--
-- Control565g: the witness abstract, 1.93 s.  Control565c and
-- Control565f: the same row with the witness computed by `isL-ord`,
-- both walled at ~11 GB.  So this file writes [LJ-1.536]'s successor
-- step against the ABSTRACT-WITNESS target and spends both cures:
--
--   the stage, by `step-suc`   (Control565a, 0.84 s)
--   the witness, by `hierL-irr` (Control565g, a PATH, not a conversion)
--
-- ONE Agda process per run, GHCRTS="-A64m -I0 -M8g", the wide caliber.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-565.runs.Control565h {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; IsOrd; Lset )
open import L.Ordinal {ℓ} using ( suc-ord )
open import L.Hierarchy {ℓ} lem using ( hierL; hierL-spec; hier-unique )
open import LJ-1-536.Probe536 {ℓ} lem
  using ( step; seq; HierBelow; module Adjoin )

open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet )
open InfinitySet {ℓ} using ( sucV )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ

HierBelowH : (γ : V ℓ) → ⟨ isL γ ⟩ → IsOrd γ → Type (ℓ-suc ℓ)
HierBelowH γ hγ oγ = ⟨ fst (hierL γ hγ oγ) ∈ Lset (step 3 γ) ⟩

step-suc : (n : ℕ) (α : V ℓ) → step n (sucV α) ≡ sucV (step n α)
step-suc zero    α = refl
step-suc (suc n) α = cong sucV (step-suc n α)

move : (x α : V ℓ) → ⟨ x ∈ Lset (step 4 α) ⟩ → ⟨ x ∈ Lset (step 3 (sucV α)) ⟩
move x α p = subst (λ w → ⟨ x ∈ Lset w ⟩) (sym (step-suc 3 α)) p

hierL-irr : (β : V ℓ) (h₁ h₂ : ⟨ isL β ⟩) (o₁ o₂ : IsOrd β)
          → hierL β h₁ o₁ ≡ hierL β h₂ o₂
hierL-irr β h₁ h₂ o₁ o₂ =
  hier-unique β (hierL β h₁ o₁) (hierL β h₂ o₂)
    (hierL-spec β h₁ o₁) (hierL-spec β h₂ o₂)

-- THE SUCCESSOR STEP.  [LJ-1.536]'s hypothesis in, the abstract-witness
-- target out.  No conversion between two spellings of anything.
successor-step-H : (α : V ℓ) (oα : IsOrd α)
                   (h : ⟨ isL (sucV α) ⟩) (o : IsOrd (sucV α))
                 → HierBelow α oα → HierBelowH (sucV α) h o
successor-step-H α oα h o hyp =
  subst (λ w → ⟨ fst w ∈ Lset (step 3 (sucV α)) ⟩)
        (hierL-irr (sucV α) _ h _ o)
        (move (fst (seq α oα)) α (Adjoin.seq∈ α oα hyp))
