{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.125] probe B: the refutation attempt on envSetK.
--
-- envSetK is conditional.  Both premises are memberships of the K slot.
-- At the abstract frame the only direct forcing attempt is B = ar = X,
-- the K-slot element itself.  Each premise is X ∈ X, refuted by the
-- delivered ∈-irrefl.  The premise barrier is MEASURED.  No refutation
-- term follows, so NOT REFUTED is INFERRED.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module ProbeLJ1125B {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ; ∈-irrefl )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans )
open import L.Coding.EnvSet {ℓ} lem using ( module Generic )

open import Cubical.Data.Nat using ( _+_ )
open import Cubical.Data.FinData using ( Fin )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL renaming ( _⊨ᵐ_ to _⊨_ )

import Cubical.Data.Empty as Empty

module EnvSetKRefute (n : ℕ) (K : Fin (5 + n)) (γ' : S ^ (11 + n)) where

  X : S
  X = lookup (suc (suc (suc (suc (suc (suc K)))))) γ'

  A : V ℓ
  A = fst X

  -- Both premises at B = ar = X are this membership.
  envSetK-premise-refuted :
    ⟨ fst X ∈ fst X ⟩ → Empty.⊥
  envSetK-premise-refuted = ∈-irrefl A

  -- The forced application at X/X needs the refuted premise.
  forced-X-needs-premise :
    ((p q : ⟨ fst X ∈ fst X ⟩)
     → ⟨ fst (Generic.envSetGen X X) ∈ fst X ⟩)
    → (p : ⟨ fst X ∈ fst X ⟩) → Empty.⊥
  forced-X-needs-premise h p = envSetK-premise-refuted p

  -- The same barrier at one numeral member is not a refutation: the
  -- arbitrary frame supplies no numeral-K membership.  So no cycle term
  -- is forced.  NOT REFUTED, INFERRED.
