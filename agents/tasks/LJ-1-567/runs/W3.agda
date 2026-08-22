{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.567] W3.  RecShape AT dom = Square.sqL κ.  TYPE ONLY, Step ABSTRACT.
--
-- WRITTEN FIRST AND TYPECHECKED ALONE, before any other Agda of this
-- task, exactly as the brief orders.  No hole, no postulate.
--
-- The brief names the widest unmeasured term:
--
--     -- RecShape instantiated at dom = Square.sqL κ, TYPE ONLY, Step abstract
--
-- and attaches one question to it: "If `RecShape` will not instantiate
-- there, the formula has nowhere to go."  So this slice writes the three
-- types a consumer of `RecShape` at that domain would ask for, with
-- `Step` left as a module parameter, and inhabits NONE of them.
--
--   ColDomain  RecShape's own `Domain₀` at the carrier of Square.sqL κ.
--   ColApprox  "f is an approximation whose domain is Square.sqL κ."
--   ColGraph   "w is the step at Square.sqL κ, for some approximation."
--
-- THE DOMAIN IS NOT REBUILT HERE.  It is imported from [LJ-1.556]'s
-- probe, agents/tasks/LJ-1-556/Probe556.agda:148 (`sqL`), which is
-- green and tracked.  The brief orders "copy what is green rather than
-- rebuilding it"; an import copies it with no re-derivation at all.
--
-- CALIBER.  The program set GHCRTS="-A64m -I0 -M8g" on this pane.  I
-- did not set it.  One Agda process at a time.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-567.runs.W3 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
import FOL.Absoluteness
open import FOL.Syntax using ( Formula )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans )
open import L.Coding.Sequence {ℓ} lem using ( module RecShape )

import LJ-1-556.Probe556 {ℓ} lem as P556

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ using ( S )

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL using ( _^_ ) renaming ( _⊨ᵐ_ to _⊨_ )

module _ (Step : ∀ {n} → Fin n → Fin n → Fin n → Formula S n) where

  module RS = RecShape Step

  -- The domain enters as ONE environment slot of type `S`.  Nothing in
  -- `RecShape` looks at what is in that slot, so the instantiation is
  -- the same instantiation it would be at any other element of L.
  ColDomain : (κ h : S) → Type (ℓ-suc ℓ)
  ColDomain κ h = RS.Domain₀ h (fst (P556.Square.sqL κ))

  ColApprox : (κ f : S) → Type (ℓ-suc ℓ)
  ColApprox κ f = ⟨ (f ∷ P556.Square.sqL κ ∷ []) ⊨ RS.ApproxAt zero (suc zero) ⟩

  ColGraph : (κ w : S) → Type (ℓ-suc ℓ)
  ColGraph κ w = ⟨ (w ∷ P556.Square.sqL κ ∷ []) ⊨ RS.GraphAt zero (suc zero) ⟩
