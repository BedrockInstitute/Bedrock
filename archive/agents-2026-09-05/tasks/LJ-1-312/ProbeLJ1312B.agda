{-# OPTIONS --cubical --safe --guardedness #-}

-- ProbeLJ1312B: the NEGATIVE CONTROL for ProbeLJ1312A.
--
-- ProbeLJ1312A's census is a list of `refl`s.  A `refl` that holds proves
-- nothing unless a WRONG statement of the same shape refuses.  This file
-- holds the wrong statements.  IT IS EXPECTED TO FAIL.  Its refusal is
-- the measurement; its exit code is never 0.
--
-- Run it with the same cap:
--   GHCRTS="-A64m -I0 -M8g" agda agents/tasks/LJ-1-312/ProbeLJ1312B.agda
--
-- This file holds ONE refusal.  ProbeLJ1312C.agda holds the other, so
-- that each error message stands on its own run.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-312.ProbeLJ1312B {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using
  ( Formula; var; _≐_; _∧̇_; ∃̇∈ )
open import L.Constructible {ℓ} using ( 𝒮ʟ )
open import LJ-1-312.ProbeLJ1312A {ℓ} lem using ( module LevelHoodV )

open import Cubical.Data.Nat using ( ℕ; zero; suc; _+_ )

module CS = hPropStructure 𝒮ʟ

module Refuse {n : ℕ}
  (N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 t0 t1 : Fin (5 + n))
  (M0 M1 M2 M3 M4 M5 M6 M7 M8 M9 M10 M11 s0 s1 : Fin (7 + n)) where

  module V = LevelHoodV {n} N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 t0 t1
    M0 M1 M2 M3 M4 M5 M6 M7 M8 M9 M10 M11 s0 s1

  -- REFUSAL 1.  `src/L/BoundedSubset.lagda.md:70-73` says OUTER slot 1 is
  -- the value.  Under that reading the equation pairs BODY slot 2 with
  -- the witness.  The delivered formula pairs BODY slot 1.
  comment-reading : V.levelHoodB
                  ≡ ∃̇∈ (var (suc (suc (suc zero))))
                      (V.G.graphBndAt ∧̇ (var (suc (suc zero)) ≐ var zero))
  comment-reading = refl
