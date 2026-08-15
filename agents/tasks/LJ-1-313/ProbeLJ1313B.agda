{-# OPTIONS --cubical --safe --guardedness #-}

-- ProbeLJ1313B: the NEGATIVE CONTROL for ProbeLJ1313A.
--
-- ProbeLJ1313A's census is a list of `refl`s.  A `refl` that holds
-- proves nothing unless a wrong statement of the same shape refuses.
-- This file states that the delivered step frame bounds its leaf at
-- BODY slot 4, the slot the leaf CONTENT points at.  IT IS EXPECTED TO
-- FAIL.  Its refusal is the measurement; its exit code is never 0.
--
--   GHCRTS="-A64m -I0 -M8g" agda agents/tasks/LJ-1-313/ProbeLJ1313B.agda

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-313.ProbeLJ1313B {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula; var; _∧̇_; ∃̇∈ )
open import L.Constructible {ℓ} using ( 𝒮ʟ )
open import L.Condensation {ℓ} lem using ( extAtB )
open import LJ-1-312.ProbeLJ1312A {ℓ} lem using ( module LevelHoodV )

open import Cubical.Data.Nat using ( ℕ; zero; suc; _+_ )

module CS = hPropStructure 𝒮ʟ

module Refuse {n : ℕ}
  (N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 t0 t1 : Fin (5 + n))
  (M0 M1 M2 M3 M4 M5 M6 M7 M8 M9 M10 M11 s0 s1 : Fin (7 + n)) where

  module V = LevelHoodV {n} N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 t0 t1
    M0 M1 M2 M3 M4 M5 M6 M7 M8 M9 M10 M11 s0 s1

  -- REFUSAL.  If the frame pointed where the content points, the two
  -- bounds would be one and the leaf would be sound.  It does not.
  frame-is-content : V.Sb.leafB
                   ≡ extAtB zero
                       (suc (suc (suc (suc zero))))
                       (∃̇∈ (var (suc (suc (suc (suc (suc zero))))))
                         (∃̇∈ (var (suc (suc (suc (suc (suc (suc zero)))))))
                           V.ψs))
  frame-is-content = refl
