{-# OPTIONS --cubical --safe --guardedness #-}

-- LJ-1.50 control A: the erase-to-Delta-0 certificate transfer stated
-- directly at the CONCRETE leaf.  This is [LJ-1.49]'s 150.13 s
-- baseline, replicated at the same caliber.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module ProbeLJ150Control {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import FOL.Syntax using ( Formula )
open import FOL.LevyHierarchy using ( Δ₀ )
import FOL.Count
open import L.Constructible {ℓ} using ( 𝒮ʟ )
open import L.Condensation {ℓ} lem using ( DefBodyB; Δ₀-DefBodyB )
open import L.BoundedSubset {ℓ} lem using ( erase-Δ₀ )

open hPropStructure 𝒮ᵥ
module CS = hPropStructure 𝒮ʟ

module Cnt = FOL.Count.Count {ℓ = ℓ-suc ℓ} CS.S

-- The leaf at n = 0, arity 8, all sixteen slots at zero.
defb : Formula CS.S 8
defb = DefBodyB {0}
  zero zero zero zero zero zero zero zero
  zero zero zero zero zero zero zero zero

Δ₀-defb : Δ₀ defb
Δ₀-defb = Δ₀-DefBodyB {0}
  zero zero zero zero zero zero zero zero
  zero zero zero zero zero zero zero zero

-- The certificate transfer at the CONCRETE leaf.
transfer-concrete : Δ₀ (Cnt.erase defb refl)
transfer-concrete = erase-Δ₀ defb refl Δ₀-defb
