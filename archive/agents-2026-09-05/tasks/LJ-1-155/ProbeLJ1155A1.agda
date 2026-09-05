-- LJ-1.155, probe A1.  THE FLOOR.
--
-- ONE question, and A2 answers the other half: what does a module cost
-- when it imports NOTHING from the Condensation family?
--
-- The three `*Agree` masters spend 31 to 47 percent of their seconds in
-- `DeadCode.DeadCodeReachable`, a phase that is not type-checking and
-- carries no definition name.  A1 and A2 separate the two candidate
-- causes: the master's own content, or the IMPORT of
-- `L.Condensation`.
--
-- Read with `agda --profile=internal`.

{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-155.ProbeLJ1155A1 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula; var; _∈̇_; _∧̇_ )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans )
open import Cubical.Data.Nat using ( _+_ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL renaming ( _⊨ᵐ_ to _⊨_ )

-- One trivial definition, so the module is not empty.
triv : {n : ℕ} (φ : Formula S n) (γ : S ^ n) → ⟨ γ ⊨ φ ⟩ → ⟨ γ ⊨ φ ⟩
triv φ γ x = x
