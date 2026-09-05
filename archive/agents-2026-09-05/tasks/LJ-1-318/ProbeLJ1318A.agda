{-# OPTIONS --cubical --safe --guardedness #-}

-- ProbeLJ1318A: the landing diff, verified in the DELIVERED structure.
--
-- ProbeLJ1313C proved the cure in a RESTRUCTURED copy: it names the two
-- leaf formulas and their certificates once each.  The delivered module
-- INLINES those four applications.  So the cure lands as SIX line
-- replacements in `src/L/BoundedSubset.lagda.md`, not four: the leaf
-- pointer sits at `:82` and `:90` in the formula and AGAIN at `:116`
-- and `:124` inside the Δ₀ certificate.  This file copies the delivered
-- module verbatim, applies exactly those six replacements and nothing
-- else, ties the result to ProbeLJ1313C's module by refl, and restates
-- the delivered `LevelHood0` over the cured module unchanged.
--
--   Section 1: lines 74 to 146 of the delivered file, six lines edited:
--     `:82`   leaf bound pointer, `suc^4 zero` becomes `suc^9 zero`
--     `:90`   leaf bound pointer, `suc^4 zero` becomes `suc^11 zero`
--     `:105`  `zero (suc^2 zero) (suc^3 zero)` becomes
--             `zero (suc^3 zero) (suc^4 zero)`
--     `:111`  `var (suc zero) ≐ var zero` becomes
--             `var (suc (suc zero)) ≐ var zero`
--     `:116`  certificate mirror of `:82`, same replacement
--     `:124`  certificate mirror of `:90`, same replacement
--   Section 2: refl ties to ProbeLJ1313C's `LevelHoodC2`.
--   Section 3: the delivered `LevelHood0` (lines 840 to 869), ZERO
--     lines edited, over the cured module.  It typechecks because its
--     members are formulas and Levy certificates, never semantic terms.
--
-- ProbeLJ1318B is the control: `:82`, `:90`, `:105`, `:111` cured and
-- the two mirrors left stale.  It must REFUSE.
--
-- Nothing here is landed.  The orchestrator lands any cure.
--
--   GHCRTS="-A64m -I0 -M8g" agda agents/tasks/LJ-1-318/ProbeLJ1318A.agda

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-318.ProbeLJ1318A {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using
  ( Formula; var; _∈̇_; _≐_; _∧̇_; ∃̇_; ∃̇∈ )
open import FOL.LevyHierarchy using
  ( Δ₀; δ-≐; δ-∧; δ-∃∈; Σ₁; σ-Δ₀; σ-∃ )
open import FOL.Manipulation.Relabelling using ( embed )
open import FOL.Manipulation.Renaming using ( renameFo )
open import FOL.Manipulation.Parameters using ( padRight )
open import L.Constructible {ℓ} using ( 𝒮ʟ )
open import L.Condensation {ℓ} lem using
  ( DefBodyB; Δ₀-DefBodyB
  ; module GraphB
  )
open import L.BoundedSubset {ℓ} lem using ( isOrdAt )
import LJ-1-313.ProbeLJ1313C

open import Cubical.Data.Nat using ( ℕ; zero; suc; _+_ )

module CS = hPropStructure 𝒮ʟ
module P13 = LJ-1-313.ProbeLJ1313C {ℓ} lem

-- =====================================================================
-- SECTION 1: THE DELIVERED MODULE, SIX LINES REPLACED IN PLACE.
-- =====================================================================

module LevelHood {n : ℕ}
  (N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 t0 t1 : Fin (5 + n))
  (M0 M1 M2 M3 M4 M5 M6 M7 M8 M9 M10 M11 s0 s1 : Fin (7 + n)) where

  m : ℕ
  m = suc (suc (suc (suc (suc n))))

  module G = GraphB {m}
    (DefBodyB {m} (suc zero) (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))
      (suc (suc (suc (suc (suc N0))))) (suc (suc (suc (suc (suc N1)))))
      (suc (suc (suc (suc (suc N2))))) (suc (suc (suc (suc (suc N3)))))
      (suc (suc (suc (suc (suc N4))))) (suc (suc (suc (suc (suc N5)))))
      (suc (suc (suc (suc (suc N6))))) (suc (suc (suc (suc (suc N7)))))
      (suc (suc (suc (suc (suc N8))))) (suc (suc (suc (suc (suc N9)))))
      (suc (suc (suc (suc (suc N10))))) (suc (suc (suc (suc (suc N11)))))
      (suc (suc (suc (suc (suc t0))))) (suc (suc (suc (suc (suc t1))))))
    (DefBodyB {suc (suc m)} (suc zero) (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))))
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
      (suc (suc (suc (suc (suc s1))))))
    zero (suc (suc (suc zero))) (suc (suc (suc (suc zero))))

  -- The bounded matrix: exists w in K (graph w gamma K and v = w).
  levelHoodB : Formula CS.S (suc (suc (suc (suc n))))
  levelHoodB =
    ∃̇∈ (var (suc (suc (suc zero))))
      (G.graphBndAt ∧̇ (var (suc (suc zero)) ≐ var zero))

  Δ₀-levelHoodB : Δ₀ levelHoodB
  Δ₀-levelHoodB =
    δ-∃∈ (δ-∧ (G.Δ₀-graphBndAt (Δ₀-DefBodyB (suc zero)
              (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))
              (suc (suc (suc (suc (suc N0))))) (suc (suc (suc (suc (suc N1)))))
              (suc (suc (suc (suc (suc N2))))) (suc (suc (suc (suc (suc N3)))))
              (suc (suc (suc (suc (suc N4))))) (suc (suc (suc (suc (suc N5)))))
              (suc (suc (suc (suc (suc N6))))) (suc (suc (suc (suc (suc N7)))))
              (suc (suc (suc (suc (suc N8))))) (suc (suc (suc (suc (suc N9)))))
              (suc (suc (suc (suc (suc N10))))) (suc (suc (suc (suc (suc N11)))))
              (suc (suc (suc (suc (suc t0))))) (suc (suc (suc (suc (suc t1))))))
            (Δ₀-DefBodyB (suc zero) (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))))
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
              (suc (suc (suc (suc (suc s1)))))))
      δ-≐)

  -- The Sigma-1 form: the unbounded witness over the bounded matrix.
  levelHoodΣ₁ : Formula CS.S (suc (suc (suc n)))
  levelHoodΣ₁ = ∃̇ levelHoodB

  Σ₁-levelHood : Σ₁ levelHoodΣ₁
  Σ₁-levelHood = σ-∃ (σ-Δ₀ Δ₀-levelHoodB)

-- =====================================================================
-- SECTION 2: THE TIE TO ProbeLJ1313C, BY refl.
--
-- The inline delivered structure and the restructured copy build ONE
-- term.  So ProbeLJ1313C's census (frame and content coincide on both
-- sides) holds of this landing diff as well.
-- =====================================================================

module Tie {n : ℕ}
  (N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 t0 t1 : Fin (5 + n))
  (M0 M1 M2 M3 M4 M5 M6 M7 M8 M9 M10 M11 s0 s1 : Fin (7 + n)) where

  module L1 = LevelHood {n} N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 t0 t1
    M0 M1 M2 M3 M4 M5 M6 M7 M8 M9 M10 M11 s0 s1

  module C2 = P13.LevelHoodC2 {n} N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 t0 t1
    M0 M1 M2 M3 M4 M5 M6 M7 M8 M9 M10 M11 s0 s1

  tie-B : L1.levelHoodB ≡ C2.levelHoodB
  tie-B = refl

  tie-Σ₁ : L1.levelHoodΣ₁ ≡ C2.levelHoodΣ₁
  tie-Σ₁ = refl

-- =====================================================================
-- SECTION 3: THE DELIVERED `LevelHood0`, ZERO LINES EDITED.
--
-- Lines 840 to 869 of the delivered file, with `LH` instantiating the
-- cured module.  `matrix`, `Σ₂` and `reverse` are FORMULAS and the two
-- certificates are Levy derivations, so the landing cannot break them.
-- Their MEANING under the cured roles is a separate question; this
-- section measures typechecking only.
-- =====================================================================

module LevelHood0
  (N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 t0 t1 : Fin 5)
  (M0 M1 M2 M3 M4 M5 M6 M7 M8 M9 M10 M11 s0 s1 : Fin 7) where

  module LH = LevelHood {0} N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 t0 t1
    M0 M1 M2 M3 M4 M5 M6 M7 M8 M9 M10 M11 s0 s1

  -- The bounded matrix at env w ∷ v ∷ γ ∷ K ∷ [].
  matrix : Formula CS.S 4
  matrix = LH.levelHoodB

  Δ₀-matrix : Δ₀ matrix
  Δ₀-matrix = LH.Δ₀-levelHoodB

  -- The Sigma-1 statement at env γ ∷ []: exists K, v, w in K.
  Σ₂ : Formula CS.S 1
  Σ₂ = ∃̇ (∃̇ (∃̇∈ (var (suc (suc zero))) LH.levelHoodB))

  Σ₁-Σ₂ : Σ₁ Σ₂
  Σ₁-Σ₂ = σ-∃ (σ-∃ (σ-Δ₀ (δ-∃∈ Δ₀-matrix)))

  -- The reverse statement at env y ∷ []: exists K, an ordinal gamma,
  -- v and w in K, with the matrix and y in v.  The matrix and the
  -- ordinal formula are weakened past the accumulating binders.
  reverse : Formula CS.S 1
  reverse =
    ∃̇ (∃̇ ( (renameFo (padRight 2) (embed isOrdAt))
          ∧̇ (∃̇ (∃̇∈ (var (suc (suc zero)))
                ( (renameFo (padRight 1) LH.levelHoodB)
                ∧̇ (var (suc (suc (suc (suc zero)))) ∈̇ var (suc zero)) ))) ))
