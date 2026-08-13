{-# OPTIONS --cubical --safe --guardedness #-}

-- LJ-1.50 control B: the erase-to-Delta-0 certificate transfer for the
-- FULL LevelHood matrix, stated directly at the concrete
-- LevelHood0.matrix (n = 0, all slots zero).  [LJ-1.49] stopped this
-- after more than 2.5 minutes; this run reports a real number or a
-- stop with its seconds.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module ProbeLJ150MatrixControl {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import FOL.Syntax using ( Formula )
open import FOL.LevyHierarchy using ( Δ₀ )
import FOL.Count
open import L.Constructible {ℓ} using ( 𝒮ʟ )
open import L.BoundedSubset {ℓ} lem using ( module LevelHood0; erase-Δ₀ )

open hPropStructure 𝒮ᵥ
module CS = hPropStructure 𝒮ʟ

module Cnt = FOL.Count.Count {ℓ = ℓ-suc ℓ} CS.S

module LH0 = LevelHood0
  zero zero zero zero zero zero zero zero zero zero zero zero zero zero
  zero zero zero zero zero zero zero zero zero zero zero zero zero zero

-- The certificate transfer at the CONCRETE matrix.
transfer-matrix : Δ₀ (Cnt.erase LH0.matrix refl)
transfer-matrix = erase-Δ₀ LH0.matrix refl LH0.Δ₀-matrix
