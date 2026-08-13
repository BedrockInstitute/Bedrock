{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.96] probe A: does the consumer's domEntryK serve the row
-- `valK` use at the graph frame?
--
-- Every row's `back` computes `ycK = valK c ar a [b] yc c∈ shEq`
-- (e.g. src/L/Condensation.lagda.md:2757, :4216), where yc is the
-- graph-value witness.  The use needs `yc ∈ K`.  At the site the
-- clause decode also binds `hc : ⟨ pr (fst c) (fst yc) ∈ fst (lookup T γ) ⟩`
-- (binClause-out, src/L/Coding/Model.lagda.md:911-917).  The consumer
-- holds domEntryK at the T slot (src/L/Condensation.lagda.md:6504-6506):
--
--   (d e f : S) → (x y : S) → ⟨ pr (fst x) (fst y) ∈ fst (lookup (suc zero) (f ∷ e ∷ d ∷ γ)) ⟩
--     → ⟨ fst x ∈ fst (lookup (suc (suc (suc K))) γ) ⟩ × ⟨ fst y ∈ fst (lookup (suc (suc (suc K))) γ) ⟩
--
-- This module shows the shape closes: the second projection of
-- domEntryK at (c, yc) with the premise hc is exactly the row's
-- needed conclusion.  T and K stay abstract; the slot match at the
-- graph frame (T = suc zero, K = suc^3 K at gamma) is read from the
-- source, not re-checked here.
--
-- Untracked probe; never committed.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module ProbeLJ196A {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans )
open import V.Coding {ℓ} using ( pr )
open import Cubical.Data.Nat using ( _+_ )
open import Cubical.HITs.CumulativeHierarchy.Base using ( _∈_ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL using ( _^_ )

-- The consumer's domEntryK, stated at abstract T and K slots.
module RowValKviaDomEntryK {n : ℕ} (T K : Fin n) (γ : S ^ n)
  (domEntryK : (x y : S) → ⟨ pr (fst x) (fst y) ∈ fst (lookup T γ) ⟩
             → ⟨ fst x ∈ fst (lookup K γ) ⟩
               × ⟨ fst y ∈ fst (lookup K γ) ⟩) where

  -- The row `back`'s needed conclusion for yc, from the graph
  -- membership premise hc that every row's clause decode binds.
  valK-use : (c yc : S) → ⟨ pr (fst c) (fst yc) ∈ fst (lookup T γ) ⟩
           → ⟨ fst yc ∈ fst (lookup K γ) ⟩
  valK-use c yc hc = domEntryK c yc hc .snd
