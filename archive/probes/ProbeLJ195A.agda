{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.95] probe A: is tmKeyK refutable?
--
-- tmKeyK (src/L/Condensation/TwelveAgree.lagda.md:96) says:
--
--   (k : S) → ⟨ fst k ∈ fst (lookup (suc^6 K) γ') ⟩
--
-- It has no premise.  Apply it at k = lookup (suc^6 K) γ' itself,
-- the element at the K slot.  The conclusion is X ∈ X for
-- X = fst (lookup (suc^6 K) γ'), refuted by the delivered
-- ∈-irrefl (src/V/Hierarchy.lagda.md:155).  No other hypothesis of
-- the frame is used, so the type is empty at every frame.
--
-- Untracked probe; never committed.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module ProbeLJ195A {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ; ∈-irrefl )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans )
open import Cubical.Data.Nat using ( _+_ )
open import Cubical.HITs.CumulativeHierarchy.Base using ( _∈_ )
import Cubical.Data.Empty as Empty

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL using ( _^_ )

module Refute (n : ℕ) (K : Fin (5 + n)) (γ' : S ^ (11 + n)) where

  -- The K slot's underlying set.
  X : S
  X = lookup (suc (suc (suc (suc (suc (suc K)))))) γ'

  -- tmKeyK k says fst k ∈ X for every L-set k.  At k = X itself the
  -- conclusion is X ∈ X, refuted by regularity (∈-irrefl).
  tmKeyK-refutes : (tmKeyK : (k : S) →
                      ⟨ fst k ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ') ⟩)
                 → Empty.⊥
  tmKeyK-refutes tmKeyK = ∈-irrefl (fst X) (tmKeyK X)
