{-# OPTIONS --cubical --safe --guardedness #-}

-- ProbeLJ1318B: NEGATIVE CONTROL for the six-line landing diff.
--
-- This file applies the cure exactly as `[LJ-1.313]` counts it: FOUR
-- lines, `:82`, `:90`, `:105`, `:111`, and leaves the two certificate
-- mirror lines `:116` and `:124` at the delivered `suc^4 zero`.  The
-- Δ₀ certificate then states a certificate for the WRONG leaf, so this
-- file must REFUSE.  Its refusal is the measurement that the landing
-- diff is six lines and not four.
--
-- EXPECTED: exit 42, a type error at `Δ₀-levelHoodB`.
--
--   GHCRTS="-A64m -I0 -M8g" agda agents/tasks/LJ-1-318/ProbeLJ1318B.agda

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-318.ProbeLJ1318B {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using
  ( Formula; var; _≐_; _∧̇_; ∃̇∈ )
open import FOL.LevyHierarchy using
  ( Δ₀; δ-≐; δ-∧; δ-∃∈ )
open import L.Constructible {ℓ} using ( 𝒮ʟ )
open import L.Condensation {ℓ} lem using
  ( DefBodyB; Δ₀-DefBodyB
  ; module GraphB
  )

open import Cubical.Data.Nat using ( ℕ; zero; suc; _+_ )

module CS = hPropStructure 𝒮ʟ

module LevelHoodFourOnly {n : ℕ}
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

  levelHoodB : Formula CS.S (suc (suc (suc (suc n))))
  levelHoodB =
    ∃̇∈ (var (suc (suc (suc zero))))
      (G.graphBndAt ∧̇ (var (suc (suc zero)) ≐ var zero))

  -- The delivered certificate, with the two mirror literals left at
  -- `suc^4 zero`.  This is the four-line landing.  It must not check.
  Δ₀-levelHoodB : Δ₀ levelHoodB
  Δ₀-levelHoodB =
    δ-∃∈ (δ-∧ (G.Δ₀-graphBndAt (Δ₀-DefBodyB (suc zero)
              (suc (suc (suc (suc zero))))
              (suc (suc (suc (suc (suc N0))))) (suc (suc (suc (suc (suc N1)))))
              (suc (suc (suc (suc (suc N2))))) (suc (suc (suc (suc (suc N3)))))
              (suc (suc (suc (suc (suc N4))))) (suc (suc (suc (suc (suc N5)))))
              (suc (suc (suc (suc (suc N6))))) (suc (suc (suc (suc (suc N7)))))
              (suc (suc (suc (suc (suc N8))))) (suc (suc (suc (suc (suc N9)))))
              (suc (suc (suc (suc (suc N10))))) (suc (suc (suc (suc (suc N11)))))
              (suc (suc (suc (suc (suc t0))))) (suc (suc (suc (suc (suc t1))))))
            (Δ₀-DefBodyB (suc zero) (suc (suc (suc (suc zero))))
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
