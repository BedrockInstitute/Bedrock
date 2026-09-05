{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.560] RED CONTROL.  THIS FILE MUST FAIL TO TYPECHECK.
--
-- It asserts the obligation's first conjunct at an ARBITRARY stage
-- instead of at the single-matrix ladder's limit.  If Agda accepted it,
-- section 3 of the probe would be measuring nothing: the stage would
-- not be load-bearing and `Single.βω` would be decoration.
--
-- Recorded run: runs/red-1.out, exit 42.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-560.runs.Red {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula; ∃̇_ )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans; IsOrd )
open import L.Reflect {ℓ} lem using ( Below; Wit; module Single )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ using ( S )
module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL renaming ( _⊨ᵐ_ to _⊨_ )

red : {k : ℕ} (ψ : Formula S (suc k)) (β : V ℓ) (oβ : IsOrd β)
    → (ρ : S ^ k) → Below β ρ → ⟨ ρ ⊨ (∃̇ ψ) ⟩ → ⟨ Wit ψ ρ β ⟩
red ψ β oβ = Single.closed ψ
