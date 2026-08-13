{-# OPTIONS --cubical --safe --guardedness #-}

-- DD25 review probe H3: THE ISOLATION.  This file is ProbeLJ150Control
-- with ONE change: the count proof `countFo defb ≡ 0` is a NAMED
-- definition instead of an inline `refl` written twice.  Nothing else
-- moves.  The formula, the certificate and the call to `erase-Δ₀` are
-- character for character the control's.
--
-- ProbeDD25H1 also added `erased-defb`.  This probe removes it, so the
-- only difference from the control is the name.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module ProbeDD25H3 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

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

-- THE ONLY CHANGE.  The control writes this `refl` twice, inline.
count-defb : countFo defb ≡ 0
count-defb = refl

transfer-concrete : Δ₀ (Cnt.erase defb count-defb)
transfer-concrete = erase-Δ₀ defb count-defb Δ₀-defb
