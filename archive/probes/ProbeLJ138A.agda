{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.38] PART A: THE BOUNDED STEP AND GRAPH MATRICES.
--
-- The delivered readings are StepAt, ApproxAt and LsetGraphAt
-- (src/L/Coding/Sequence.lagda.md:119-120, :173-176, :182-184).
-- This probe states their bounded restatements at a variable
-- environment with the bound K as a slot, and closes each matrix's
-- Delta-0 certificate from the Delta-0 certificate of the leaf
-- content.  The concrete leaf is the delivered bounded code-set
-- description DefBodyB (src/L/Condensation.lagda.md:2234-2242), whose
-- certificate is delivered (:2244-2251).
--
-- The step matrix is generic in the leaf content ψ, exactly the shape
-- [LJ-1.34-R] measured at 0.0072 s per line (src/ProbeDD25D5.agda),
-- with K a parameter instead of the fixed class-carrier slot.  The
-- approximation and graph matrices ride the same step frame; each
-- nesting level shifts the leaf arity, so each carries its own leaf
-- content.
--
-- Slot convention: a module at arity m states its formula at arity m
-- with its parameters as direct slots; the class-carrier instance is
-- at arity suc n with the parameters lifted and K = 0.  This is the
-- rows' convention (src/L/Condensation.lagda.md:1697-1702).
--
-- Untracked probe; one Agda process under GHCRTS="-A64m -I0 -M8g";
-- never committed; thrown away per D-1.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module ProbeLJ138A {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax
  using ( Formula; var; _∈̇_; _∧̇_; _⇒̇_; ∃̇_; ∀̇_; ∃̇∈; ∀̇∈ )
open import FOL.LevyHierarchy using ( Δ₀; δ-∈; δ-∧; δ-⇒; δ-∀∈; δ-∃∈ )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Coding {ℓ} using ( pr )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans )
open import L.Coding.Model {ℓ} using ( appAt; domAt; prAtL )
open import L.Coding.Sequence {ℓ} lem
  using ( StepAt; ApproxAt; LsetGraphAt )
open import L.Condensation {ℓ} lem
  using ( extAtB; Δ₀-extAtB; Δ₀-appAt; domB; Δ₀-domB
        ; DefBodyB; Δ₀-DefBodyB )
open import Cubical.Data.Nat using ( _+_ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL using ( _^_ ) renaming ( _⊨ᵐ_ to _⊨_ )

-- =====================================================================
-- THE BOUNDED STEP MATRIX, GENERIC IN THE LEAF CONTENT.
--
-- At environment γ : S ^ m with v b f K : Fin m as slots.  The body is
-- at d ∷ w ∷ c ∷ z ∷ γ (4 + m); the leaf is at v' ∷ c' ∷ x ∷ δ with
-- δ = d ∷ w ∷ c ∷ z ∷ γ (5 + m), and ψ lives at arity 3 + (5 + m).
-- The bounds are: c ∈ b, w ∈ K, d ∈ K for the step witnesses; c' ∈ K
-- and v' ∈ K for the leaf's code and value.
-- =====================================================================
module StepB {m : ℕ} (ψ : Formula S (suc (suc (suc (4 + m)))))
            (v b f K : Fin m) where
  leafB : Formula S (4 + m)
  leafB =
    extAtB zero (suc (suc (suc (suc K))))
      (∃̇∈ (var (suc (suc (suc (suc (suc K))))))
        (∃̇∈ (var (suc (suc (suc (suc (suc (suc K))))))) ψ))

  bodyB : Formula S (4 + m)
  bodyB =
    (var (suc (suc zero)) ∈̇ var (suc (suc (suc (suc b)))))
    ∧̇ ( appAt (suc (suc (suc (suc f)))) (suc (suc zero)) (suc zero)
       ∧̇ ( leafB ∧̇ (var (suc (suc (suc zero))) ∈̇ var zero) ) )

  witB : Formula S (suc m)
  witB =
    ∃̇∈ (var (suc b))
      (∃̇∈ (var (suc (suc K)))
        (∃̇∈ (var (suc (suc (suc K))))
          bodyB))

  stepBndAt : Formula S m
  stepBndAt = extAtB v K witB

  Δ₀-leafB : Δ₀ ψ → Δ₀ leafB
  Δ₀-leafB d =
    Δ₀-extAtB zero (suc (suc (suc (suc K))))
      (∃̇∈ (var (suc (suc (suc (suc (suc K))))))
        (∃̇∈ (var (suc (suc (suc (suc (suc (suc K))))))) ψ))
      (δ-∃∈ (δ-∃∈ d))

  Δ₀-bodyB : Δ₀ ψ → Δ₀ bodyB
  Δ₀-bodyB d =
    δ-∧ δ-∈
      (δ-∧ (Δ₀-appAt (suc (suc (suc (suc f))))
                      (suc (suc zero)) (suc zero))
           (δ-∧ (Δ₀-leafB d) δ-∈))

  Δ₀-stepBndAt : Δ₀ ψ → Δ₀ stepBndAt
  Δ₀-stepBndAt d =
    Δ₀-extAtB v K witB
      (δ-∃∈ (δ-∃∈ (δ-∃∈ (Δ₀-bodyB d))))

-- =====================================================================
-- THE CONCRETE STEP MATRIX AT THE CLASS CARRIER.
--
-- At the class carrier the environment is γ : S ^ (suc n) with K at
-- slot zero and v b f at slots suc v, suc b, suc f.  The leaf δ is
-- d ∷ w ∷ c ∷ z ∷ γ (5 + n), and the delivered DefBodyB takes its 16
-- slots there: the carrier at δ slot 1 (the step's w), the bound at
-- δ slot 4 (the class carrier's K), and the twelve row tags and two
-- term slots as parameters.
-- =====================================================================
module StepAtB {n : ℕ} (v b f : Fin n)
  (N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 t0 t1 : Fin (5 + n)) where
  ψ : Formula S (suc (suc (suc (5 + n))))
  ψ = DefBodyB (suc zero) (suc (suc (suc (suc zero))))
        N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 t0 t1

  stepBndAt : Formula S (suc n)
  stepBndAt = StepB.stepBndAt {suc n} ψ (suc v) (suc b) (suc f) zero

  Δ₀-stepBndAt : Δ₀ stepBndAt
  Δ₀-stepBndAt =
    StepB.Δ₀-stepBndAt {suc n} ψ (suc v) (suc b) (suc f) zero
      (Δ₀-DefBodyB (suc zero) (suc (suc (suc (suc zero))))
        N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 t0 t1)

-- =====================================================================
-- THE BOUNDED APPROXIMATION AND GRAPH MATRICES.
--
-- ApproxAt f a = domAt f a ∧̇ ∀̇ (∀̇ (appAt (sh2 f) 1 0
--              ⇒̇ Step zero (suc zero) (sh2 f)))
-- LsetGraphAt w b = ∃̇ (ApproxAt zero (suc b) ∧̇ Step (suc w) (suc b) zero)
-- (src/L/Coding/Sequence.lagda.md:173-176, :182-184).  The bounded
-- restatements bound the two domain variables and the witness function
-- by K, and replace the inner step by the bounded step at the same K
-- shifted past the binders.  Each nesting level shifts the leaf arity,
-- so each matrix carries its own leaf content.
-- =====================================================================
module ApproxB {m : ℕ} (ψ' : Formula S (suc (suc (suc (6 + m)))))
                (f a K : Fin m) where
  module S = StepB {2 + m} ψ' zero (suc zero) (suc (suc f)) (suc (suc K))

  approxBndAt : Formula S m
  approxBndAt =
    domB f a K
    ∧̇ ∀̇∈ (var K)
        (∀̇∈ (var (suc K))
          (appAt (suc (suc f)) (suc zero) zero
          ⇒̇ S.stepBndAt))

  Δ₀-approxBndAt : Δ₀ ψ' → Δ₀ approxBndAt
  Δ₀-approxBndAt d =
    δ-∧ (Δ₀-domB f a K)
        (δ-∀∈ (δ-∀∈ (δ-⇒ (Δ₀-appAt (suc (suc f))
                                    (suc zero) zero)
                         (S.Δ₀-stepBndAt d))))

module GraphB {m : ℕ} (ψs : Formula S (suc (suc (suc (5 + m)))))
              (ψa : Formula S (suc (suc (suc (7 + m)))))
              (w b K : Fin m) where
  module A = ApproxB {1 + m} ψa zero (suc b) (suc K)
  module S = StepB {1 + m} ψs (suc w) (suc b) zero (suc K)

  graphBndAt : Formula S m
  graphBndAt = ∃̇∈ (var K) (A.approxBndAt ∧̇ S.stepBndAt)

  Δ₀-graphBndAt : Δ₀ ψs → Δ₀ ψa → Δ₀ graphBndAt
  Δ₀-graphBndAt ds da =
    δ-∃∈ (δ-∧ (A.Δ₀-approxBndAt da) (S.Δ₀-stepBndAt ds))
