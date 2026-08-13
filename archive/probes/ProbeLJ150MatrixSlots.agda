{-# OPTIONS --cubical --safe --guardedness #-}

-- LJ-1.50 probe B: the erase-to-Delta-0 certificate transfer for the
-- FULL LevelHood matrix, built at VARIABLE SLOTS and instantiated ONCE
-- at the concrete LevelHood0.matrix (n = 0, all slots zero).

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module ProbeLJ150MatrixSlots {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import FOL.Syntax using ( Formula )
open import FOL.LevyHierarchy using ( Δ₀ )
import FOL.Count
open import L.Constructible {ℓ} using ( 𝒮ʟ )
open import L.BoundedSubset {ℓ} lem using ( module LevelHood; module LevelHood0; erase-Δ₀ )
open import Cubical.Data.Nat using ( _+_ )

open hPropStructure 𝒮ᵥ
module CS = hPropStructure 𝒮ʟ

module Cnt = FOL.Count.Count {ℓ = ℓ-suc ℓ} CS.S

-- The matrix transfer at variable slots.
module EraseMatrix {n : ℕ}
  (N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 t0 t1 : Fin (5 + n))
  (M0 M1 M2 M3 M4 M5 M6 M7 M8 M9 M10 M11 s0 s1 : Fin (7 + n)) where

  module LH = LevelHood {n}
    N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 t0 t1
    M0 M1 M2 M3 M4 M5 M6 M7 M8 M9 M10 M11 s0 s1

  transfer : Δ₀ (Cnt.erase LH.levelHoodB refl)
  transfer = erase-Δ₀ LH.levelHoodB refl LH.Δ₀-levelHoodB

-- The concrete matrix transfer: ONE instantiation at the end.
module LH0 = LevelHood0
  zero zero zero zero zero zero zero zero zero zero zero zero zero zero
  zero zero zero zero zero zero zero zero zero zero zero zero zero zero

transfer-matrix : Δ₀ (Cnt.erase LH0.matrix refl)
transfer-matrix = EraseMatrix.transfer {0}
  zero zero zero zero zero zero zero zero zero zero zero zero zero zero
  zero zero zero zero zero zero zero zero zero zero zero zero zero zero
