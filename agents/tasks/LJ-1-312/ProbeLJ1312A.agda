{-# OPTIONS --cubical --safe --guardedness #-}

-- ProbeLJ1312A: measure the SLOT ROLES of the delivered `levelHoodB`.
--
-- The question.  `φ₀ = closeN 14 (pins ∧̇ renameFo ρ (erase levelHoodB))`
-- keeps two slots free (ProbeLJ1241A.agda:106-146).  `q'` needs those two
-- to be the graph's VALUE and the graph's ORDINAL.  [LJ-1.310] read the
-- syntax and reported that they are the ORDINAL and a BOUND.  No Agda had
-- run on that reading.  This file runs it.
--
--   SECTION 1  the VERBATIM copy of `LevelHood`, pinned to the delivered
--              module by `copy-is-delivered`, which is `refl`
--   SECTION 2  the role census of the verbatim copy, every line `refl`
--   SECTION 3  the environment arithmetic, every line `refl`
--   SECTION 4  the CURED copy, its Δ₀ certificate and its census
--
-- Nothing here is landed.  The cure lives in SECTION 4 and never in `src/`.
--
-- DD4: `levelHoodB`, `GraphB`, `StepB` and `extAtB` are FOL and bounded-set
-- machinery.  They name no tower and no carrier of either trophy, so a
-- defect here is shared by the AC end and the GCH end, and so is a cure.
--
-- ONE agda process under GHCRTS="-A64m -I0 -M8g".  Tracked, never deleted,
-- and it lives beside its report.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-312.ProbeLJ1312A {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using
  ( Formula; Term; var; _∈̇_; _≐_; _∧̇_; _⇒̇_; ∃̇_; ∃̇∈; ∀̇∈ )
open import FOL.LevyHierarchy using
  ( Δ₀; δ-≐; δ-∧; δ-∃∈; Σ₁; σ-Δ₀; σ-∃ )
open import L.Constructible {ℓ} using ( 𝒮ʟ )
open import L.Condensation {ℓ} lem using
  ( DefBodyB; Δ₀-DefBodyB; extAtB
  ; module GraphB; module ApproxB; module StepB
  )
open import L.BoundedSubset {ℓ} lem using ( module LevelHood; module LevelHood0 )

open import Cubical.Data.Nat using ( ℕ; zero; suc; _+_ )
open import Cubical.Data.Vec using ( Vec; _∷_; []; lookup )

module CS = hPropStructure 𝒮ʟ

-- =====================================================================
-- SECTION 1: THE VERBATIM COPY.
--
-- `src/L/BoundedSubset.lagda.md:74-146`, copied character for character
-- except that the two leaf contents get names.  `copy-is-delivered`
-- below is the certificate that the copy IS the delivered formula.
-- =====================================================================

module LevelHoodV {n : ℕ}
  (N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 t0 t1 : Fin (5 + n))
  (M0 M1 M2 M3 M4 M5 M6 M7 M8 M9 M10 M11 s0 s1 : Fin (7 + n)) where

  m : ℕ
  m = suc (suc (suc (suc (suc n))))

  -- the step leaf, `src/L/BoundedSubset.lagda.md:82-89`
  ψs : Formula CS.S (suc (suc (suc (5 + m))))
  ψs =
    DefBodyB {m} (suc zero) (suc (suc (suc (suc zero))))
      (suc (suc (suc (suc (suc N0))))) (suc (suc (suc (suc (suc N1)))))
      (suc (suc (suc (suc (suc N2))))) (suc (suc (suc (suc (suc N3)))))
      (suc (suc (suc (suc (suc N4))))) (suc (suc (suc (suc (suc N5)))))
      (suc (suc (suc (suc (suc N6))))) (suc (suc (suc (suc (suc N7)))))
      (suc (suc (suc (suc (suc N8))))) (suc (suc (suc (suc (suc N9)))))
      (suc (suc (suc (suc (suc N10))))) (suc (suc (suc (suc (suc N11)))))
      (suc (suc (suc (suc (suc t0))))) (suc (suc (suc (suc (suc t1)))))

  -- the approximation leaf, `src/L/BoundedSubset.lagda.md:90-104`
  ψa : Formula CS.S (suc (suc (suc (7 + m))))
  ψa =
    DefBodyB {suc (suc m)} (suc zero) (suc (suc (suc (suc zero))))
      (suc (suc (suc (suc (suc M0)))))
      (suc (suc (suc (suc (suc M1)))))
      (suc (suc (suc (suc (suc M2)))))
      (suc (suc (suc (suc (suc M3)))))
      (suc (suc (suc (suc (suc M4)))))
      (suc (suc (suc (suc (suc M5)))))
      (suc (suc (suc (suc (suc M6)))))
      (suc (suc (suc (suc (suc M7)))))
      (suc (suc (suc (suc (suc M8)))))
      (suc (suc (suc (suc (suc M9)))))
      (suc (suc (suc (suc (suc M10)))))
      (suc (suc (suc (suc (suc M11)))))
      (suc (suc (suc (suc (suc s0)))))
      (suc (suc (suc (suc (suc s1)))))

  Δ₀-ψs : Δ₀ ψs
  Δ₀-ψs =
    Δ₀-DefBodyB (suc zero) (suc (suc (suc (suc zero))))
      (suc (suc (suc (suc (suc N0))))) (suc (suc (suc (suc (suc N1)))))
      (suc (suc (suc (suc (suc N2))))) (suc (suc (suc (suc (suc N3)))))
      (suc (suc (suc (suc (suc N4))))) (suc (suc (suc (suc (suc N5)))))
      (suc (suc (suc (suc (suc N6))))) (suc (suc (suc (suc (suc N7)))))
      (suc (suc (suc (suc (suc N8))))) (suc (suc (suc (suc (suc N9)))))
      (suc (suc (suc (suc (suc N10))))) (suc (suc (suc (suc (suc N11)))))
      (suc (suc (suc (suc (suc t0))))) (suc (suc (suc (suc (suc t1)))))

  Δ₀-ψa : Δ₀ ψa
  Δ₀-ψa =
    Δ₀-DefBodyB (suc zero) (suc (suc (suc (suc zero))))
      (suc (suc (suc (suc (suc M0)))))
      (suc (suc (suc (suc (suc M1)))))
      (suc (suc (suc (suc (suc M2)))))
      (suc (suc (suc (suc (suc M3)))))
      (suc (suc (suc (suc (suc M4)))))
      (suc (suc (suc (suc (suc M5)))))
      (suc (suc (suc (suc (suc M6)))))
      (suc (suc (suc (suc (suc M7)))))
      (suc (suc (suc (suc (suc M8)))))
      (suc (suc (suc (suc (suc M9)))))
      (suc (suc (suc (suc (suc M10)))))
      (suc (suc (suc (suc (suc M11)))))
      (suc (suc (suc (suc (suc s0)))))
      (suc (suc (suc (suc (suc s1)))))

  -- `src/L/BoundedSubset.lagda.md:105`, the three structural arguments
  module G = GraphB {m} ψs ψa
    zero (suc (suc zero)) (suc (suc (suc zero)))

  -- GraphB's own two inner modules, at GraphB's own arguments
  -- (`src/L/Condensation.lagda.md:2486-2487`).  The `refl` named
  -- `census-graph` below is the certificate that these are GraphB's.
  module A = ApproxB {suc m} ψa
    zero (suc (suc (suc zero))) (suc (suc (suc (suc zero))))

  module Sb = StepB {suc m} ψs
    (suc zero) (suc (suc (suc zero))) zero (suc (suc (suc (suc zero))))

  -- `src/L/BoundedSubset.lagda.md:108-111`
  levelHoodB : Formula CS.S (suc (suc (suc (suc n))))
  levelHoodB =
    ∃̇∈ (var (suc (suc (suc zero))))
      (G.graphBndAt ∧̇ (var (suc zero) ≐ var zero))

  Δ₀-levelHoodB : Δ₀ levelHoodB
  Δ₀-levelHoodB = δ-∃∈ (δ-∧ (G.Δ₀-graphBndAt Δ₀-ψs Δ₀-ψa) δ-≐)

  levelHoodΣ₁ : Formula CS.S (suc (suc (suc n)))
  levelHoodΣ₁ = ∃̇ levelHoodB

  Σ₁-levelHood : Σ₁ levelHoodΣ₁
  Σ₁-levelHood = σ-∃ (σ-Δ₀ Δ₀-levelHoodB)

-- =====================================================================
-- SECTION 2: THE ROLE CENSUS.
--
-- Every statement is `refl`, so every statement is a MEASUREMENT of the
-- delivered term and not a reading of it.
-- =====================================================================

module Census {n : ℕ}
  (N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 t0 t1 : Fin (5 + n))
  (M0 M1 M2 M3 M4 M5 M6 M7 M8 M9 M10 M11 s0 s1 : Fin (7 + n)) where

  module V = LevelHoodV {n} N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 t0 t1
    M0 M1 M2 M3 M4 M5 M6 M7 M8 M9 M10 M11 s0 s1

  module D = LevelHood {n} N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 t0 t1
    M0 M1 M2 M3 M4 M5 M6 M7 M8 M9 M10 M11 s0 s1

  -- MEASUREMENT 0.  The copy is the delivered formula.  Everything below
  -- therefore measures `src/L/BoundedSubset.lagda.md:108-111` itself.
  copy-is-delivered : V.levelHoodB ≡ D.levelHoodB
  copy-is-delivered = refl

  -- MEASUREMENT 1.  The outer bounded existential ranges over OUTER slot
  -- 3, and the equation pairs BODY slot 1, which is OUTER slot 0, with
  -- the witness at BODY slot 0.
  census-outer : V.levelHoodB
               ≡ ∃̇∈ (var (suc (suc (suc zero))))
                   (V.G.graphBndAt ∧̇ (var (suc zero) ≐ var zero))
  census-outer = refl

  -- MEASUREMENT 2.  The graph's own bounded existential ranges over BODY
  -- slot 3, which is OUTER slot 2.  This is a DIFFERENT slot from the
  -- one MEASUREMENT 1 found, and both are bounds.
  census-graph : V.G.graphBndAt
               ≡ ∃̇∈ (var (suc (suc (suc zero))))
                   (V.A.approxBndAt ∧̇ V.Sb.stepBndAt)
  census-graph = refl

  -- MEASUREMENT 3.  The step describes the set at GRAPH-BODY slot 1,
  -- which is the witness of MEASUREMENT 1.  So the VALUE is that
  -- witness, and OUTER slot 0 is equal to it by MEASUREMENT 1.  The
  -- step's own bound is GRAPH-BODY slot 4, which is OUTER slot 2.
  census-step : V.Sb.stepBndAt
              ≡ extAtB (suc zero) (suc (suc (suc (suc zero)))) V.Sb.witB
  census-step = refl

  -- MEASUREMENT 4.  The step's index ranges over WIT slot 4, which is
  -- OUTER slot 1.  So the ORDINAL is OUTER slot 1.
  census-wit : V.Sb.witB
             ≡ ∃̇∈ (var (suc (suc (suc (suc zero)))))
                 (∃̇∈ (var (suc (suc (suc (suc (suc (suc zero)))))))
                   (∃̇∈ (var (suc (suc (suc (suc (suc (suc (suc zero))))))))
                     V.Sb.bodyB))
  census-wit = refl

-- =====================================================================
-- SECTION 2B: THE SECOND SITE (C-42, the extent).
--
-- `LevelHood0.Σ₂` is the only other place in `src/` that puts a bound on
-- `levelHoodB`'s slots.  Its own comment at
-- `src/L/BoundedSubset.lagda.md:854` says the bounded existential ranges
-- over `K`, which the same expression BINDS.  The measurement below says
-- it ranges over slot 2 of an arity-3 environment, which is the ONE slot
-- that stays free in `Σ₂`.  So the same off-by-one appears twice.
-- =====================================================================

module CensusΣ₂
  (N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 t0 t1 : Fin 5)
  (M0 M1 M2 M3 M4 M5 M6 M7 M8 M9 M10 M11 s0 s1 : Fin 7) where

  module L0 = LevelHood0 N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 t0 t1
    M0 M1 M2 M3 M4 M5 M6 M7 M8 M9 M10 M11 s0 s1

  -- MEASUREMENT 4B.
  census-Σ₂ : L0.Σ₂ ≡ ∃̇ (∃̇ (∃̇∈ (var (suc (suc zero))) L0.matrix))
  census-Σ₂ = refl

-- =====================================================================
-- SECTION 3: THE ENVIRONMENT ARITHMETIC.
--
-- Section 2 gives slot numbers in four different environments.  These
-- `refl`s carry each number back to the outer environment, at n = 0.
-- The outer environment is a ∷ b ∷ c ∷ d ∷ [].
-- =====================================================================

module Env (a b c d x f z : CS.S) where

  outer : Vec CS.S 4
  outer = a ∷ b ∷ c ∷ d ∷ []

  body : Vec CS.S 5
  body = x ∷ outer

  graphBody : Vec CS.S 6
  graphBody = f ∷ body

  wit : Vec CS.S 7
  wit = z ∷ graphBody

  -- the value witness is bounded by OUTER slot 3
  e1 : lookup (suc (suc (suc zero))) outer ≡ d
  e1 = refl

  -- the equation's left side is OUTER slot 0
  e2 : lookup (suc zero) body ≡ a
  e2 = refl

  -- the equation's right side is the witness
  e3 : lookup zero body ≡ x
  e3 = refl

  -- the graph machinery is bounded by OUTER slot 2
  e4 : lookup (suc (suc (suc zero))) body ≡ c
  e4 = refl

  -- the step describes the witness, so the VALUE is the witness
  e5 : lookup (suc zero) graphBody ≡ x
  e5 = refl

  -- the step's own bound is OUTER slot 2 again
  e6 : lookup (suc (suc (suc (suc zero)))) graphBody ≡ c
  e6 = refl

  -- the step's index ranges in OUTER slot 1, so the ORDINAL is OUTER 1
  e7 : lookup (suc (suc (suc (suc zero)))) wit ≡ b
  e7 = refl

-- =====================================================================
-- SECTION 4: THE CURED COPY.
--
-- Two lines change against SECTION 1, and no other line changes:
--   `src/L/BoundedSubset.lagda.md:105`
--     zero (suc (suc zero)) (suc (suc (suc zero)))
--   becomes
--     zero (suc (suc (suc zero))) (suc (suc (suc (suc zero))))
--   `src/L/BoundedSubset.lagda.md:111`
--     var (suc zero) ≐ var zero
--   becomes
--     var (suc (suc zero)) ≐ var zero
--
-- The cure gives OUTER slot 1 the VALUE, OUTER slot 2 the ORDINAL and
-- OUTER slot 3 the one bound, and it leaves OUTER slot 0 unused.  The
-- Δ₀ certificate survives unchanged, so the cure costs no classification.
-- =====================================================================

module LevelHoodC {n : ℕ}
  (N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 t0 t1 : Fin (5 + n))
  (M0 M1 M2 M3 M4 M5 M6 M7 M8 M9 M10 M11 s0 s1 : Fin (7 + n)) where

  module V = LevelHoodV {n} N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 t0 t1
    M0 M1 M2 M3 M4 M5 M6 M7 M8 M9 M10 M11 s0 s1

  -- the CURED line 105
  module G = GraphB {V.m} V.ψs V.ψa
    zero (suc (suc (suc zero))) (suc (suc (suc (suc zero))))

  module A = ApproxB {suc V.m} V.ψa
    zero (suc (suc (suc (suc zero)))) (suc (suc (suc (suc (suc zero)))))

  module Sb = StepB {suc V.m} V.ψs
    (suc zero) (suc (suc (suc (suc zero)))) zero
    (suc (suc (suc (suc (suc zero)))))

  -- the CURED line 111
  levelHoodB : Formula CS.S (suc (suc (suc (suc n))))
  levelHoodB =
    ∃̇∈ (var (suc (suc (suc zero))))
      (G.graphBndAt ∧̇ (var (suc (suc zero)) ≐ var zero))

  -- the cure keeps the Δ₀ certificate, line for line
  Δ₀-levelHoodB : Δ₀ levelHoodB
  Δ₀-levelHoodB = δ-∃∈ (δ-∧ (G.Δ₀-graphBndAt V.Δ₀-ψs V.Δ₀-ψa) δ-≐)

  levelHoodΣ₁ : Formula CS.S (suc (suc (suc n)))
  levelHoodΣ₁ = ∃̇ levelHoodB

  Σ₁-levelHood : Σ₁ levelHoodΣ₁
  Σ₁-levelHood = σ-∃ (σ-Δ₀ Δ₀-levelHoodB)

module CensusC {n : ℕ}
  (N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 t0 t1 : Fin (5 + n))
  (M0 M1 M2 M3 M4 M5 M6 M7 M8 M9 M10 M11 s0 s1 : Fin (7 + n)) where

  module C = LevelHoodC {n} N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 t0 t1
    M0 M1 M2 M3 M4 M5 M6 M7 M8 M9 M10 M11 s0 s1

  -- MEASUREMENT 5.  The outer existential still ranges over OUTER slot 3,
  -- and the equation now pairs BODY slot 2, which is OUTER slot 1.
  census-outer : C.levelHoodB
               ≡ ∃̇∈ (var (suc (suc (suc zero))))
                   (C.G.graphBndAt ∧̇ (var (suc (suc zero)) ≐ var zero))
  census-outer = refl

  -- MEASUREMENT 6.  The graph now ranges over BODY slot 4, which is
  -- OUTER slot 3.  That is the SAME bound as MEASUREMENT 5's.  One
  -- bound, not two.
  census-graph : C.G.graphBndAt
               ≡ ∃̇∈ (var (suc (suc (suc (suc zero)))))
                   (C.A.approxBndAt ∧̇ C.Sb.stepBndAt)
  census-graph = refl

  -- MEASUREMENT 7.  The step still describes GRAPH-BODY slot 1, the
  -- witness, and the witness is now OUTER slot 1 by MEASUREMENT 5.  The
  -- step's bound is GRAPH-BODY slot 5, which is OUTER slot 3.
  census-step : C.Sb.stepBndAt
              ≡ extAtB (suc zero) (suc (suc (suc (suc (suc zero)))))
                  C.Sb.witB
  census-step = refl

  -- MEASUREMENT 8.  The step's index now ranges over WIT slot 5, which
  -- is OUTER slot 2.  So the ORDINAL is OUTER slot 2.
  census-wit : C.Sb.witB
             ≡ ∃̇∈ (var (suc (suc (suc (suc (suc zero))))))
                 (∃̇∈ (var (suc (suc (suc (suc (suc (suc (suc zero))))))))
                   (∃̇∈ (var (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))
                     C.Sb.bodyB))
  census-wit = refl

module EnvC (a b c d x f z : CS.S) where

  outer : Vec CS.S 4
  outer = a ∷ b ∷ c ∷ d ∷ []

  body : Vec CS.S 5
  body = x ∷ outer

  graphBody : Vec CS.S 6
  graphBody = f ∷ body

  wit : Vec CS.S 7
  wit = z ∷ graphBody

  -- the equation's left side is now OUTER slot 1, the VALUE
  c2 : lookup (suc (suc zero)) body ≡ b
  c2 = refl

  -- the graph is bounded by OUTER slot 3, the same slot as the outer one
  c4 : lookup (suc (suc (suc (suc zero)))) body ≡ d
  c4 = refl

  -- the step's bound is OUTER slot 3 too
  c6 : lookup (suc (suc (suc (suc (suc zero))))) graphBody ≡ d
  c6 = refl

  -- the step's index ranges in OUTER slot 2, the ORDINAL
  c7 : lookup (suc (suc (suc (suc (suc zero))))) wit ≡ c
  c7 = refl
