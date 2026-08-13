{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.152] Probe F.  THE CONTROL FOR PROBE B.
--
-- Probe B is this file plus ONE `hasSeparationL` instance.  Probe A is
-- the baseline for ProbeLJ1136A's LARGER import set, so A cannot be
-- subtracted from B.  This file carries Probe B's import block exactly,
-- so the difference F to B is one separation and nothing else.
--
-- ABORT CRITERION: none.  This is a control, not a decision.
--
-- Tracked probe; ONE agda process under GHCRTS="-A64m -I0 -M8g";
-- never committed to src/.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-152.ProbeLJ1152F {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula; var; _≐_ )
import FOL.Absoluteness
import FOL.ZFModel
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans )
open import L.Axioms.Full {ℓ} lem using ( hasSeparationL )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ

module ModelL = FOL.ZFModel 𝒮ʟ
open ModelL using ( SetOf )

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL using ( _^_ ) renaming ( _⊨ᵐ_ to _⊨_ )

-- ---------------------------------------------------------------------
-- Probe B's module, with the separation REMOVED.  The formula stays, so
-- the difference is the `hasSeparationL` instance alone.
-- ---------------------------------------------------------------------

module OneSep (a : S) where

  φ : Formula S 1
  φ = var zero ≐ var zero

  Pred : S → Ω
  Pred x = (x ∈ˢ a) ⊓ ((x ∷ []) ⊨ φ)

  Goal : Type (ℓ-suc ℓ)
  Goal = isContr (SetOf Pred)
