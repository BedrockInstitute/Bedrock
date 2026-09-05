{-# OPTIONS --cubical --safe --guardedness #-}

-- ProbeLJ1313A: measure the LEAF BOUND of the delivered `levelHoodB`.
--
-- The question.  `StepB.leafB` bounds the leaf frame by the step's K
-- (`src/L/Condensation.lagda.md:2396-2399`).  The leaf CONTENT is a
-- `DefBodyB` application, and its bound pointer is an argument the
-- caller picks.  `StepAtB` picks `suc (suc (suc (suc zero)))` and there
-- that slot IS the class K (`src/L/Condensation.lagda.md:2441-2445`),
-- so frame and content point at ONE set.  `LevelHood` copies the same
-- literal (`src/L/BoundedSubset.lagda.md:82` and `:90`).  In
-- `LevelHood`'s context the slot under the four step binders is the
-- graph's own function binder `f`, not K.  This file measures where
-- the frame points and where the content points, in the delivered
-- formula and in the [LJ-1.312] cured copy.
--
--   SECTION 1  the tie to the delivered module, and the frame census
--   SECTION 2  the environment arithmetic at n = 0
--
-- The copies come from `LJ-1-312.ProbeLJ1312A`, which is re-run and
-- imported, never changed.  `copy-is-delivered` there pins the copy to
-- `src/L/BoundedSubset.lagda.md:108-111`; the same tie is re-stated
-- here so this file stands alone.
--
-- ProbeLJ1313B.agda is the NEGATIVE CONTROL: it states that the frame
-- points where the content points, and it is expected to FAIL.
--
-- ONE agda process under GHCRTS="-A64m -I0 -M8g".  Tracked, never
-- deleted, and it lives beside its report.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-313.ProbeLJ1313A {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using
  ( Formula; var; _∈̇_; _≐_; _∧̇_; ∃̇_; ∃̇∈; ∀̇∈ )
open import L.Constructible {ℓ} using ( 𝒮ʟ )
open import L.Condensation {ℓ} lem using
  ( DefBodyB; extAtB; module GraphB; module ApproxB; module StepB )
open import L.BoundedSubset {ℓ} lem using ( module LevelHood )
open import LJ-1-312.ProbeLJ1312A {ℓ} lem using
  ( module LevelHoodV; module LevelHoodC )

open import Cubical.Data.Nat using ( ℕ; zero; suc; _+_ )
open import Cubical.Data.Vec using ( Vec; _∷_; []; lookup )

module CS = hPropStructure 𝒮ʟ

-- =====================================================================
-- SECTION 1: THE FRAME CENSUS.
--
-- Every statement is `refl`.  The step frame's own K arithmetic is
-- computed by Agda, so each index below is a MEASUREMENT of the
-- delivered term.
-- =====================================================================

module Census {n : ℕ}
  (N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 t0 t1 : Fin (5 + n))
  (M0 M1 M2 M3 M4 M5 M6 M7 M8 M9 M10 M11 s0 s1 : Fin (7 + n)) where

  module V = LevelHoodV {n} N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 t0 t1
    M0 M1 M2 M3 M4 M5 M6 M7 M8 M9 M10 M11 s0 s1

  module D = LevelHood {n} N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 t0 t1
    M0 M1 M2 M3 M4 M5 M6 M7 M8 M9 M10 M11 s0 s1

  -- MEASUREMENT 0.  The copy is the delivered formula, so every leaf
  -- measured below is a leaf of `src/L/BoundedSubset.lagda.md:108-111`.
  copy-is-delivered : V.levelHoodB ≡ D.levelHoodB
  copy-is-delivered = refl

  -- MEASUREMENT 1.  The graph applies the probe's own A and Sb, so the
  -- frames below are the delivered graph's frames.
  graph-tie : V.G.graphBndAt
            ≡ ∃̇∈ (var (suc (suc (suc zero))))
                (V.A.approxBndAt ∧̇ V.Sb.stepBndAt)
  graph-tie = refl

  -- MEASUREMENT 2.  The step frame bounds its leaf by BODY slot 8, and
  -- hands the leaf content `V.ψs` to the frame.  `V.ψs`'s own bound
  -- pointer is `suc (suc (suc (suc zero)))`, BODY slot 4
  -- (`src/L/BoundedSubset.lagda.md:82`).  Slot 8 and slot 4 differ.
  leaf-frame-s : V.Sb.leafB
               ≡ extAtB zero
                   (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))
                   (∃̇∈ (var (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))
                     (∃̇∈ (var (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))))
                       V.ψs))
  leaf-frame-s = refl

  -- MEASUREMENT 3.  The approximation's inner step frame bounds its
  -- leaf by ITS body slot 10.  `V.ψa`'s own bound pointer is BODY slot
  -- 4 again (`src/L/BoundedSubset.lagda.md:90`).
  leaf-frame-a : V.A.S.leafB
               ≡ extAtB zero
                   (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))
                   (∃̇∈ (var (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))))
                     (∃̇∈ (var (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))))))
                       V.ψa))
  leaf-frame-a = refl

  module C = LevelHoodC {n} N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 t0 t1
    M0 M1 M2 M3 M4 M5 M6 M7 M8 M9 M10 M11 s0 s1

  -- MEASUREMENT 4.  After the [LJ-1.312] cure the step frame bound
  -- moves to BODY slot 9.  The leaf content is `C.V.ψs`, the SAME
  -- content as the delivered one, so its pointer stays at BODY slot 4.
  -- The cure does not move the content pointer.
  leaf-frame-s-cured : C.Sb.leafB
                     ≡ extAtB zero
                         (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))
                         (∃̇∈ (var (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))))
                           (∃̇∈ (var (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))))
                             C.V.ψs))
  leaf-frame-s-cured = refl

  -- MEASUREMENT 5.  The cured approximation frame moves to ITS body
  -- slot 11, and the content pointer stays at 4.
  leaf-frame-a-cured : C.A.S.leafB
                     ≡ extAtB zero
                         (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))))
                         (∃̇∈ (var (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))))))
                           (∃̇∈ (var (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))))))
                             C.V.ψa))
  leaf-frame-a-cured = refl

-- =====================================================================
-- SECTION 2: THE ENVIRONMENT ARITHMETIC, at n = 0.
--
-- The step body's environment is d1 ∷ w1 ∷ c1 ∷ z1 ∷ f ∷ body, where
-- f is the graph's own bounded witness and body = x ∷ a ∷ b ∷ c ∷ d is
-- `levelHoodB`'s body environment ([LJ-1.312] ProbeLJ1312A, Env).  The
-- approximation's step body adds the two domain binders u2 and u1.
-- =====================================================================

module Env (v' c' x2 u1 u2 d1 w1 c1 z1 f x a b c d : CS.S) where

  stepBody : Vec CS.S 10
  stepBody = d1 ∷ w1 ∷ c1 ∷ z1 ∷ f ∷ x ∷ a ∷ b ∷ c ∷ d ∷ []

  -- the delivered step frame bound, slot 8, is OUTER slot 2
  g1 : lookup (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) stepBody ≡ c
  g1 = refl

  -- the content pointer, slot 4, is the function binder f
  g2 : lookup (suc (suc (suc (suc zero)))) stepBody ≡ f
  g2 = refl

  -- the cured step frame bound, slot 9, is OUTER slot 3
  g3 : lookup (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))) stepBody ≡ d
  g3 = refl

  -- `DefBodyB` hands `isCodeBS` the pointer three binders deeper
  -- (`src/L/Condensation.lagda.md:2340-2341`), so at the leaf
  -- environment it reads slot 7, which is f again
  leafEnv : Vec CS.S 13
  leafEnv = v' ∷ c' ∷ x2 ∷ stepBody

  g4 : lookup (suc (suc (suc (suc (suc (suc (suc zero))))))) leafEnv ≡ f
  g4 = refl

  approxBody : Vec CS.S 12
  approxBody = d1 ∷ w1 ∷ c1 ∷ z1 ∷ u2 ∷ u1 ∷ f ∷ x ∷ a ∷ b ∷ c ∷ d ∷ []

  -- the delivered approximation frame bound, slot 10, is OUTER slot 2
  g5 : lookup (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))) approxBody ≡ c
  g5 = refl

  -- the approximation content pointer, slot 4, is the domain binder u2
  g6 : lookup (suc (suc (suc (suc zero)))) approxBody ≡ u2
  g6 = refl

  -- the cured approximation frame bound, slot 11, is OUTER slot 3
  g7 : lookup (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))) approxBody ≡ d
  g7 = refl
