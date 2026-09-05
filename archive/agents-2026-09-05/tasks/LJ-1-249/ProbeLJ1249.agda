{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.249] probe: PORT graph-assembly TO THE CLASS ABSTRACTION.
--
-- [LJ-1.246] specified this probe and [LJ-1.249] passes the
-- specification through unchanged.  It re-points the carrier of the
-- archived green probe ProbeLJ152B from 𝒮ʟ to the (M, M-trans)
-- abstraction that GenSequence already uses, and asks whether
-- graph-assembly still typechecks.
--
-- The BS side (graphBndAt / stepBndAt / approxBndAt) is re-expressed
-- here from the carrier-generic templates StepB / ApproxB / GraphB of
-- L.Condensation, parameterized over the per-tower leaf content ψs and
-- ψa (the DefBodyB instantiations).  The At side (LsetGraphAt /
-- StepAt / ApproxAt / LsetGraph-in) is the generic GenSequence body,
-- parameterized over the DefAt trio.  Only the two leaves are
-- per-tower.
--
-- ONE agda process under GHCRTS="-A64m -I0 -M8g".  Never committed.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

open import FOL.ZFStructure using ( module hPropStructure; Transitive; _↾_ )
open import V.Hierarchy using ( 𝒮ᵥ )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ⁅_,_⁆ ) renaming ( module InfinitySet to Inf )
open Inf using ( #_; sucV )

module LJ-1-249.ProbeLJ1249 {ℓ : Level} (lem : LEM (ℓ-suc ℓ))
  (M : V ℓ → hProp (ℓ-suc ℓ))
  (M-trans : Transitive (𝒮ᵥ {ℓ}) M)
  (numeralL : ℕ → Σ[ x ∈ V ℓ ] ⟨ M x ⟩)
  (numeralL-fst : (k : ℕ) → fst (numeralL k) ≡ # k)
  (pairʟ : (a b : Σ[ x ∈ V ℓ ] ⟨ M x ⟩) → Σ[ x ∈ V ℓ ] ⟨ M x ⟩)
  (pairʟ-fst : (a b : Σ[ x ∈ V ℓ ] ⟨ M x ⟩)
             → fst (pairʟ a b) ≡ ⁅ fst a , fst b ⁆)
  (sucʟ : Σ[ x ∈ V ℓ ] ⟨ M x ⟩ → Σ[ x ∈ V ℓ ] ⟨ M x ⟩)
  (sucʟ-fst : (a : Σ[ x ∈ V ℓ ] ⟨ M x ⟩) → fst (sucʟ a) ≡ sucV (fst a))
  where

open import FOL.Syntax using ( Formula; var; _∈̇_; _∧̇_; _⇒̇_; ∃̇∈; ∀̇∈ )
import FOL.Absoluteness
open import L.Constructible {ℓ} using ( 𝒟ₒ )
import LJ-1-210.GenModel
import LJ-1-238.GenSequence

import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁; ∣_∣₁; squash₁ )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.Data.Nat using ( _+_ )

module GM = LJ-1-210.GenModel {ℓ} M M-trans
              numeralL numeralL-fst pairʟ pairʟ-fst sucʟ sucʟ-fst
open GM using ( appAt )

module GS = LJ-1-238.GenSequence {ℓ} lem M M-trans
              numeralL numeralL-fst pairʟ pairʟ-fst sucʟ sucʟ-fst

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure (𝒮ᵥ {ℓ} ↾ M)

module AbsL = FOL.Absoluteness.Single (𝒮ᵥ {ℓ}) M (λ {x} {y} → M-trans {x} {y})
open AbsL renaming ( _⊨ᵐ_ to _⊨_ )

-- =====================================================================
-- THE BS SIDE, CARRIER-GENERIC.  The bounded extension frame, the
-- bounded domain, and the bounded step / approximation / graph matrices,
-- restated from src/L/Condensation.lagda.md:100-101, :1746-1747,
-- :2390-2425, :2465-2490, at the (M, M-trans) carrier.  Each is generic
-- in the leaf content; only the leaf is per-tower.
-- =====================================================================

extAtB : ∀ {n} → Fin n → Fin n → Formula S (suc n) → Formula S n
extAtB y K φ = ∀̇∈ (var y) φ
             ∧̇ ∀̇∈ (var K) (φ ⇒̇ (var zero ∈̇ var (suc y)))

domB : ∀ {m} → Fin m → Fin m → Fin m → Formula S m
domB f d K =
  ∀̇∈ (var K)
  (((∃̇∈ (var (suc K)) (appAt (suc (suc f)) (suc zero) zero))
      ⇒̇ (var zero ∈̇ var (suc d)))
  ∧̇ ((var zero ∈̇ var (suc d))
      ⇒̇ (∃̇∈ (var (suc K)) (appAt (suc (suc f)) (suc zero) zero))))

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

module GraphB {m : ℕ} (ψs : Formula S (suc (suc (suc (5 + m)))))
              (ψa : Formula S (suc (suc (suc (7 + m)))))
              (w b K : Fin m) where
  module A = ApproxB {1 + m} ψa zero (suc b) (suc K)
  module S = StepB {1 + m} ψs (suc w) (suc b) zero (suc K)

  graphBndAt : Formula S m
  graphBndAt = ∃̇∈ (var K) (A.approxBndAt ∧̇ S.stepBndAt)

-- =====================================================================
-- THE ASSEMBLY, PORTED.  StepAgree and ApproxAgree stay hypotheses.
-- graph-assembly is the same body as ProbeLJ152B.agda:70-88, at the
-- generic carrier.  The per-tower leaf content enters as ψs and ψa
-- (BS) and DefAt (At).
-- =====================================================================

module Body
  (DefAt : ∀ {n} → Fin n → Fin n → Formula S n)
  (DefAt-in : (A : S) → ∀ {n} (u w : Fin n) (γ : S ^ n)
            → fst (lookup w γ) ≡ fst A
            → fst (lookup u γ) ≡ 𝒟ₒ (fst A)
            → ⟨ γ ⊨ DefAt u w ⟩)
  (DefAt-out : (A : S) → ∀ {n} (u w : Fin n) (γ : S ^ n) → GS.DefOK A
             → fst (lookup w γ) ≡ fst A
             → ⟨ γ ⊨ DefAt u w ⟩
             → fst (lookup u γ) ≡ 𝒟ₒ (fst A))
  (ψs : Formula S 13)
  (ψa : Formula S 15)
  where

  module Seq = GS.Body DefAt DefAt-in DefAt-out
  open Seq using ( LsetGraphAt; LsetGraph-in; StepAt; ApproxAt )

  module GB = GraphB {5} ψs ψa zero (suc (suc zero)) (suc (suc (suc zero)))

  -- The site facts of the twelve-row agreement at the graph env: the
  -- tag slots hold the numerals, the recorded values lie in K, the
  -- satisfiers lie in K.  One opaque bundle, as in ProbeLJ152B.
  module _ (SF : (h x w v γ K : S) → Type (ℓ-suc ℓ)) where

    StepAgree : Type (ℓ-suc ℓ)
    StepAgree = (h x w v γ K : S) (sf : SF h x w v γ K)
              → ⟨ (h ∷ x ∷ w ∷ v ∷ γ ∷ K ∷ []) ⊨ GB.S.stepBndAt ⟩
              → ⟨ (h ∷ x ∷ w ∷ v ∷ γ ∷ K ∷ []) ⊨
                   StepAt (suc (suc zero)) (suc (suc (suc (suc zero)))) zero ⟩

    ApproxAgree : Type (ℓ-suc ℓ)
    ApproxAgree = (h x w v γ K : S) (sf : SF h x w v γ K)
                → ⟨ (h ∷ x ∷ w ∷ v ∷ γ ∷ K ∷ []) ⊨ GB.A.approxBndAt ⟩
                → ⟨ (h ∷ x ∷ w ∷ v ∷ γ ∷ K ∷ []) ⊨
                     ApproxAt zero (suc (suc (suc (suc zero)))) ⟩

    graph-assembly : (step : StepAgree) (approx : ApproxAgree)
                   → (x w v γ K : S) (sf : (h' : S) → SF h' x w v γ K)
                   → ⟨ (x ∷ w ∷ v ∷ γ ∷ K ∷ []) ⊨ GB.graphBndAt ⟩
                   → ⟨ (x ∷ w ∷ v ∷ γ ∷ K ∷ []) ⊨
                        LsetGraphAt {5} (suc zero) (suc (suc (suc zero))) ⟩
    graph-assembly step approx x w v γ K sf h =
      PT.rec squash₁ go h
      where
      go : Σ[ h' ∈ S ]
             (⟨ h' ∈ˢ γ ⟩
            × ⟨ (h' ∷ x ∷ w ∷ v ∷ γ ∷ K ∷ []) ⊨
                 (GB.A.approxBndAt ∧̇ GB.S.stepBndAt) ⟩)
         → ⟨ (x ∷ w ∷ v ∷ γ ∷ K ∷ []) ⊨
              LsetGraphAt {5} (suc zero) (suc (suc (suc zero))) ⟩
      go (h' , h∈γ , hahs) =
        LsetGraph-in {5} (suc zero) (suc (suc (suc zero)))
          (x ∷ w ∷ v ∷ γ ∷ K ∷ []) h'
          (approx h' x w v γ K (sf h') (fst hahs))
          (step h' x w v γ K (sf h') (snd hahs))
