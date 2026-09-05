{-# OPTIONS --cubical --safe --guardedness #-}

-- ProbeLJ1312C: the second NEGATIVE CONTROL for ProbeLJ1312A.
--
-- The delivered `levelHoodB` and the CURED `levelHoodB` are different
-- formulas.  This file states that they are the same.  IT IS EXPECTED TO
-- FAIL.  Its refusal is the measurement; its exit code is never 0.
--
--   GHCRTS="-A64m -I0 -M8g" agda agents/tasks/LJ-1-312/ProbeLJ1312C.agda

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-312.ProbeLJ1312C {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import L.Constructible {ℓ} using ( 𝒮ʟ )
open import LJ-1-312.ProbeLJ1312A {ℓ} lem using
  ( module LevelHoodV; module LevelHoodC )

open import Cubical.Data.Nat using ( ℕ; zero; suc; _+_ )

module CS = hPropStructure 𝒮ʟ

module Refuse {n : ℕ}
  (N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 t0 t1 : Fin (5 + n))
  (M0 M1 M2 M3 M4 M5 M6 M7 M8 M9 M10 M11 s0 s1 : Fin (7 + n)) where

  module V = LevelHoodV {n} N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 t0 t1
    M0 M1 M2 M3 M4 M5 M6 M7 M8 M9 M10 M11 s0 s1

  module C = LevelHoodC {n} N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 t0 t1
    M0 M1 M2 M3 M4 M5 M6 M7 M8 M9 M10 M11 s0 s1

  -- REFUSAL 2.  The delivered formula is not the cured formula.  That is
  -- the whole finding in one line.
  delivered-is-cured : V.levelHoodB ≡ C.levelHoodB
  delivered-is-cured = refl
