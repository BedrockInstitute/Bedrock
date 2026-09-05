{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.579] CONTROL a.  IS THE OBLIGATION AN EXISTENCE OR A BOUND?
-- If `stage` already puts `hierL γ` in SOME stage for free, then every
-- route that delivers "some stage" is worth zero lines here, and that
-- includes [LJ-1.560]'s reflection.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-579.runs.Control579a {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ} using ( IsOrd; Lset; isL; Lset-mono )
open import L.Stage {ℓ} lem using ( stage; stage-ord; stage-mem; stage-earliest )
open import L.Hierarchy {ℓ} lem using ( hierL )
open import LJ-1-536.Probe536 {ℓ} lem using ( step; isL-ord; HierBelow )

open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
import Cubical.Data.Empty as Empty

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ

------------------------------------------------------------------------
-- ROW 1.  EXISTENCE IS FREE.  No hypothesis, no induction, no limit.
------------------------------------------------------------------------

hier-somewhere : (γ : V ℓ) (oγ : IsOrd γ)
               → Σ[ σ ∈ V ℓ ] (IsOrd σ × ⟨ fst (hierL γ (isL-ord γ oγ) oγ) ∈ Lset σ ⟩)
hier-somewhere γ oγ = stage x p , (stage-ord x p , stage-mem x p)
  where
  x : V ℓ
  x = fst (hierL γ (isL-ord γ oγ) oγ)
  p : ⟨ isL x ⟩
  p = snd (hierL γ (isL-ord γ oγ) oγ)

------------------------------------------------------------------------
-- ROW 2.  SO THE OBLIGATION IS A BOUND, AND HERE IT IS BOTH WAYS.
------------------------------------------------------------------------

-- The bound BUYS the obligation.
bound→hier : (γ : V ℓ) (oγ : IsOrd γ)
           → ⟨ stage (fst (hierL γ (isL-ord γ oγ) oγ))
                    (snd (hierL γ (isL-ord γ oγ) oγ)) ∈ step 3 γ ⟩
           → HierBelow γ oγ
bound→hier γ oγ lt = Lset-mono lt (stage-mem x p)
  where
  x : V ℓ
  x = fst (hierL γ (isL-ord γ oγ) oγ)
  p : ⟨ isL x ⟩
  p = snd (hierL γ (isL-ord γ oγ) oγ)

-- And the obligation IS the bound: nothing below can hold it.
hier→bound : (γ : V ℓ) (oγ : IsOrd γ) → IsOrd (step 3 γ)
           → HierBelow γ oγ
           → ⟨ step 3 γ ∈ stage (fst (hierL γ (isL-ord γ oγ) oγ))
                                (snd (hierL γ (isL-ord γ oγ) oγ)) ⟩
           → Empty.⊥
hier→bound γ oγ o3 hb = stage-earliest x p (step 3 γ) o3 hb
  where
  x : V ℓ
  x = fst (hierL γ (isL-ord γ oγ) oγ)
  p : ⟨ isL x ⟩
  p = snd (hierL γ (isL-ord γ oγ) oγ)
