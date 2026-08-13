{-# OPTIONS --cubical --safe --guardedness #-}

-- DD25 review probe H7: THE FULL MATRIX, with the count proof NAMED.
--
-- [LJ-1.50] section 3 reports that the full `LevelHood0.matrix`
-- variant does not finish: two stop-bounded attempts, about 570 s and
-- about 520 s, both interrupted, no number.  Both probes
-- (`src/ProbeLJ150MatrixControl.agda:34`,
--  `src/ProbeLJ150MatrixSlots.agda:37`) write `refl` inline.
--
-- This probe is the same obligation with the count proof named once.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module ProbeDD25H7 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import FOL.Syntax using ( Formula )
open import FOL.LevyHierarchy using ( Δ₀ )
open import FOL.Manipulation.Parameters using ( countFo )
import FOL.Count
open import L.Constructible {ℓ} using ( 𝒮ʟ )
open import L.BoundedSubset {ℓ} lem using ( module LevelHood0; erase-Δ₀ )

open hPropStructure 𝒮ᵥ
module CS = hPropStructure 𝒮ʟ

module Cnt = FOL.Count.Count {ℓ = ℓ-suc ℓ} CS.S

module LH0 = LevelHood0
  zero zero zero zero zero zero zero zero zero zero zero zero zero zero
  zero zero zero zero zero zero zero zero zero zero zero zero zero zero

count-matrix : countFo LH0.matrix ≡ 0
count-matrix = refl

transfer-matrix : Δ₀ (Cnt.erase LH0.matrix count-matrix)
transfer-matrix = erase-Δ₀ LH0.matrix count-matrix LH0.Δ₀-matrix
