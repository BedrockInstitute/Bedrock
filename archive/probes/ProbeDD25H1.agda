{-# OPTIONS --cubical --safe --guardedness #-}

-- DD25 review probe H1: the DECOMPOSITION of [LJ-1.50]'s 150 s control.
-- The return measured one lump: `erase-Δ₀ defb refl Δ₀-defb`.  It then
-- attributed the whole lump to the structural recursion of `erase-Δ₀`
-- over the built tree.  That attribution is an inference.  This probe
-- splits the lump into four named definitions, so `--profile=definitions`
-- attributes the seconds itself:
--
--   defb          the built formula
--   Δ₀-defb       the built Delta-0 certificate
--   count-defb    the count proof `countFo defb ≡ 0` by refl
--   erased-defb   `Cnt.erase defb count-defb` (no recursion needed)
--   transfer      `erase-Δ₀ defb count-defb Δ₀-defb`
--
-- The control (ProbeLJ150Control) writes `refl` INLINE, twice, so its
-- count proof is inside the lump.  Here it is a separate definition.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module ProbeDD25H1 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

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

-- The leaf at n = 0, arity 8, all sixteen slots at zero.  Same object
-- as ProbeLJ150Control :28-36.
defb : Formula CS.S 8
defb = DefBodyB {0}
  zero zero zero zero zero zero zero zero
  zero zero zero zero zero zero zero zero

Δ₀-defb : Δ₀ defb
Δ₀-defb = Δ₀-DefBodyB {0}
  zero zero zero zero zero zero zero zero
  zero zero zero zero zero zero zero zero

-- STEP 1.  The count proof alone.
count-defb : countFo defb ≡ 0
count-defb = refl

-- STEP 2.  The erasure alone.  No recursion runs: the type comes from
-- the signature.
erased-defb : Formula (⊥* {ℓ-suc ℓ}) 8
erased-defb = Cnt.erase defb count-defb

-- STEP 3.  The certificate transfer, the return's whole measurement.
transfer-concrete : Δ₀ (Cnt.erase defb count-defb)
transfer-concrete = erase-Δ₀ defb count-defb Δ₀-defb
