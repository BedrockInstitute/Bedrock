{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.362] instantiation probe at V.  MEASURES the glue price
-- ([LJ-1.361] part 3 priced it INFERRED at about 30 lines per model)
-- and the check cost of the instantiation content class (P-m).  The
-- structure hypothesis discharges by refl at V, because ≈ˢ there IS
-- the path equality definitionally.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import FOL.ZFStructure using ( ZFStructure; module hPropStructure )

module LJ-1-362.InstanceV {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Model {ℓ} using ( V⊨ZF )
import FOL.Bernstein

≈ˢᵥ-is-path : (x y : ZFStructure.S 𝒮ᵥ)
  → (ZFStructure._≈ˢ_ 𝒮ᵥ x y)
  ≡ ((x ≡ y) , ZFStructure.isSetS 𝒮ᵥ x y)
≈ˢᵥ-is-path x y = refl

module B = FOL.Bernstein lem 𝒮ᵥ ≈ˢᵥ-is-path

CSBᵥ : Type (ℓ-suc ℓ)
CSBᵥ = B.CSB (V⊨ZF lem)

module T = B.Tarski (V⊨ZF lem)
