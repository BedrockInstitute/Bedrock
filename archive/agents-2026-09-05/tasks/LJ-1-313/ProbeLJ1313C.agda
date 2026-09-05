{-# OPTIONS --cubical --safe --guardedness #-}

-- ProbeLJ1313C: price the FULL cure, in a copy and never in `src/`.
--
-- ProbeLJ1313A measured that the [LJ-1.312] cure leaves the two leaf
-- content pointers at BODY slot 4, while the leaf frames bound by the
-- one bound.  This file holds the copy with FOUR changed lines against
-- the delivered module: the two [LJ-1.312] lines, and the two leaf
-- bound pointers re-aimed at the slot the frame names.  The census
-- shows frame and content now name ONE slot on each side, and the Δ₀
-- and Σ₁ certificates typecheck unchanged.
--
-- Nothing here is landed.  The orchestrator lands any cure.
--
--   GHCRTS="-A64m -I0 -M8g" agda agents/tasks/LJ-1-313/ProbeLJ1313C.agda

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-313.ProbeLJ1313C {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using
  ( Formula; var; _∈̇_; _≐_; _∧̇_; ∃̇_; ∃̇∈; ∀̇∈ )
open import FOL.LevyHierarchy using
  ( Δ₀; δ-≐; δ-∧; δ-∃∈; Σ₁; σ-Δ₀; σ-∃ )
open import L.Constructible {ℓ} using ( 𝒮ʟ )
open import L.Condensation {ℓ} lem using
  ( DefBodyB; Δ₀-DefBodyB; extAtB
  ; module GraphB; module ApproxB; module StepB
  )

open import Cubical.Data.Nat using ( ℕ; zero; suc; _+_ )

module CS = hPropStructure 𝒮ʟ

-- =====================================================================
-- SECTION 1: THE FOUR-LINE COPY.
--
-- Against `src/L/BoundedSubset.lagda.md:74-146`:
--   `:82`   leaf bound pointer, `suc^4 zero` becomes `suc^9 zero`
--   `:90`   leaf bound pointer, `suc^4 zero` becomes `suc^11 zero`
--   `:105`  structural slots, `zero (suc^2 zero) (suc^3 zero)` becomes
--           `zero (suc^3 zero) (suc^4 zero)`  ([LJ-1.312] Form 1)
--   `:111`  the equation, `var (suc zero)` becomes
--           `var (suc (suc zero))`             ([LJ-1.312] Form 1)
-- =====================================================================

module LevelHoodC2 {n : ℕ}
  (N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 t0 t1 : Fin (5 + n))
  (M0 M1 M2 M3 M4 M5 M6 M7 M8 M9 M10 M11 s0 s1 : Fin (7 + n)) where

  m : ℕ
  m = suc (suc (suc (suc (suc n))))

  ψs : Formula CS.S (suc (suc (suc (5 + m))))
  ψs =
    DefBodyB {m} (suc zero)
      (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))
      (suc (suc (suc (suc (suc N0))))) (suc (suc (suc (suc (suc N1)))))
      (suc (suc (suc (suc (suc N2))))) (suc (suc (suc (suc (suc N3)))))
      (suc (suc (suc (suc (suc N4))))) (suc (suc (suc (suc (suc N5)))))
      (suc (suc (suc (suc (suc N6))))) (suc (suc (suc (suc (suc N7)))))
      (suc (suc (suc (suc (suc N8))))) (suc (suc (suc (suc (suc N9)))))
      (suc (suc (suc (suc (suc N10))))) (suc (suc (suc (suc (suc N11)))))
      (suc (suc (suc (suc (suc t0))))) (suc (suc (suc (suc (suc t1)))))

  ψa : Formula CS.S (suc (suc (suc (7 + m))))
  ψa =
    DefBodyB {suc (suc m)} (suc zero)
      (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))))
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
    Δ₀-DefBodyB (suc zero)
      (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))
      (suc (suc (suc (suc (suc N0))))) (suc (suc (suc (suc (suc N1)))))
      (suc (suc (suc (suc (suc N2))))) (suc (suc (suc (suc (suc N3)))))
      (suc (suc (suc (suc (suc N4))))) (suc (suc (suc (suc (suc N5)))))
      (suc (suc (suc (suc (suc N6))))) (suc (suc (suc (suc (suc N7)))))
      (suc (suc (suc (suc (suc N8))))) (suc (suc (suc (suc (suc N9)))))
      (suc (suc (suc (suc (suc N10))))) (suc (suc (suc (suc (suc N11)))))
      (suc (suc (suc (suc (suc t0))))) (suc (suc (suc (suc (suc t1)))))

  Δ₀-ψa : Δ₀ ψa
  Δ₀-ψa =
    Δ₀-DefBodyB (suc zero)
      (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))))
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

  module G = GraphB {m} ψs ψa
    zero (suc (suc (suc zero))) (suc (suc (suc (suc zero))))

  module A = ApproxB {suc m} ψa
    zero (suc (suc (suc (suc zero)))) (suc (suc (suc (suc (suc zero)))))

  module Sb = StepB {suc m} ψs
    (suc zero) (suc (suc (suc (suc zero)))) zero
    (suc (suc (suc (suc (suc zero)))))

  levelHoodB : Formula CS.S (suc (suc (suc (suc n))))
  levelHoodB =
    ∃̇∈ (var (suc (suc (suc zero))))
      (G.graphBndAt ∧̇ (var (suc (suc zero)) ≐ var zero))

  Δ₀-levelHoodB : Δ₀ levelHoodB
  Δ₀-levelHoodB = δ-∃∈ (δ-∧ (G.Δ₀-graphBndAt Δ₀-ψs Δ₀-ψa) δ-≐)

  levelHoodΣ₁ : Formula CS.S (suc (suc (suc n)))
  levelHoodΣ₁ = ∃̇ levelHoodB

  Σ₁-levelHood : Σ₁ levelHoodΣ₁
  Σ₁-levelHood = σ-∃ (σ-Δ₀ Δ₀-levelHoodB)

-- =====================================================================
-- SECTION 2: THE COINCIDENCE CENSUS.
--
-- On each side the frame bound and the content pointer now name ONE
-- slot: 9 on the step side, 11 on the approximation side.
-- =====================================================================

module CensusC2 {n : ℕ}
  (N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 t0 t1 : Fin (5 + n))
  (M0 M1 M2 M3 M4 M5 M6 M7 M8 M9 M10 M11 s0 s1 : Fin (7 + n)) where

  module C2 = LevelHoodC2 {n} N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 t0 t1
    M0 M1 M2 M3 M4 M5 M6 M7 M8 M9 M10 M11 s0 s1

  graph-tie : C2.G.graphBndAt
            ≡ ∃̇∈ (var (suc (suc (suc (suc zero)))))
                (C2.A.approxBndAt ∧̇ C2.Sb.stepBndAt)
  graph-tie = refl

  -- step side: frame slot 9, content pointer 9
  leaf-frame-s : C2.Sb.leafB
               ≡ extAtB zero
                   (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))
                   (∃̇∈ (var (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))))
                     (∃̇∈ (var (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))))
                       C2.ψs))
  leaf-frame-s = refl

  -- approximation side: frame slot 11, content pointer 11
  leaf-frame-a : C2.A.S.leafB
               ≡ extAtB zero
                   (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))))
                   (∃̇∈ (var (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))))))
                     (∃̇∈ (var (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))))))
                       C2.ψa))
  leaf-frame-a = refl
