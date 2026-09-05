{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.362] instantiation bisect at V: module application and the
-- structure hypothesis alone, WITHOUT elaborating CSB's statement or
-- the Tarski module at the concrete carrier.  If this is fast, the
-- 27 min of InstanceV.agda lives in the satisfaction types' of the
-- statement at V (P-n's payable floor), not in the application.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import FOL.ZFStructure using ( ZFStructure; module hPropStructure )
open import FOL.Syntax using ( Formula )

module LJ-1-362.InstanceVBisect {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Model {ℓ} using ( V⊨ZF )
import FOL.Bernstein

≈ˢᵥ-is-path : (x y : ZFStructure.S 𝒮ᵥ)
  → (ZFStructure._≈ˢ_ 𝒮ᵥ x y)
  ≡ ((x ≡ y) , ZFStructure.isSetS 𝒮ᵥ x y)
≈ˢᵥ-is-path x y = refl

module B = FOL.Bernstein lem 𝒮ᵥ ≈ˢᵥ-is-path

-- a small forced use: pure syntax from the applied module
prᵥᵥ : Formula (ZFStructure.S 𝒮ᵥ) 3
prᵥᵥ = B.prAt zero (suc zero) (suc (suc zero))
