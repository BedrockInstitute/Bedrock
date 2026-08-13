{-# OPTIONS --cubical --safe --guardedness #-}

-- DD25 review probe H4: THE MECHANISM.  Two SPELLINGS of one count
-- proof, one in the type and one in the body.  If this is slow while
-- ProbeDD25H3 (one spelling everywhere) is fast, then the cost is a
-- CONVERSION between two spellings of the erase argument, and it is
-- not the structural recursion of `erase-Δ₀`.
--
-- This is P-v's shape at the proof level rather than at the formula
-- level: never force a conversion between two spellings of one thing.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module ProbeDD25H4 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import FOL.Syntax using ( Formula )
open import FOL.LevyHierarchy using ( Δ₀ )
open import FOL.Manipulation.Parameters using ( countFo )
import FOL.Count
open import L.Constructible {ℓ} using ( 𝒮ʟ )
open import L.Condensation {ℓ} lem using ( DefBodyB; Δ₀-DefBodyB )
open import L.BoundedSubset {ℓ} lem using ( erase-Δ₀ )

open hPropStructure 𝒮ᵥ
module CS = hPropStructure 𝒮ʟ

module Cnt = FOL.Count.Count {ℓ = ℓ-suc ℓ} CS.S

defb : Formula CS.S 8
defb = DefBodyB {0}
  zero zero zero zero zero zero zero zero
  zero zero zero zero zero zero zero zero

Δ₀-defb : Δ₀ defb
Δ₀-defb = Δ₀-DefBodyB {0}
  zero zero zero zero zero zero zero zero
  zero zero zero zero zero zero zero zero

count-defb : countFo defb ≡ 0
count-defb = refl

-- The type names the proof; the body spells it `refl`.  ONE spelling
-- difference against ProbeDD25H3.
transfer-concrete : Δ₀ (Cnt.erase defb count-defb)
transfer-concrete = erase-Δ₀ defb refl Δ₀-defb
