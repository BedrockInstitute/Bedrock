{-# OPTIONS --cubical --safe --guardedness #-}

-- LJ-1.340 NEGATIVE CONTROL.  It lands nothing.  It runs in
-- agents/tasks/LJ-1-340/.
--
-- THIS FILE IS THE BASELINE THE GENERIC FORM IS PRICED AGAINST.  It holds
-- the two delivered arguments COPIED VERBATIM, with the seals that sit on
-- them, and nothing else.
--
-- PART A copies src/L/Choice/Stage.lagda.md:172-201 and :255-272.
-- PART B copies src/L/Choice/Step.lagda.md:106-142.
--
-- Both parts import the same modules as ProbeGeneric.agda, so the two
-- files differ ONLY in the argument.  Their seconds are comparable.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-340.ProbeControl {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ} using ( IsOrd; isL; Lset; Lset-out; 𝒟ₒ )
open import L.Ordinal {ℓ} using ( mem-ord; suc-ord )
open import L.Ordinal.Stages {ℓ} lem using ( suc∈or≡ )
open import L.Stage {ℓ} lem
  using ( isLeastOrd; stage; stage-ord; stage-mem; stage-earliest )
open import L.Axioms.Basic {ℓ} using ( Lset-suc )
open import L.Choice.Stage {ℓ} lem
  using ( meets; Inhabited; μ; μ-ord; μ-meets; μ-earliest
        ; IsPredOf; isPropPredOf )

import Cubical.Data.Sum as Sum
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁; squash₁ )
open import Cubical.Data.Sum using ( _⊎_; inl; inr )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet )
open InfinitySet using ( sucV )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ

------------------------------------------------------------------------
-- PART A.  src/L/Choice/Stage.lagda.md:172-201 and :255-272, verbatim.
------------------------------------------------------------------------

private
  below-case : (u σ δ : S) → isLeastOrd (meets u) σ → IsOrd δ
             → ⟨ meets u (sucV δ) ⟩ → ⟨ sucV δ ∈ˢ σ ⟩ → sucV δ ≡ σ
  below-case u σ δ least ordδ m s∈σ =
    Empty.rec (least (sucV δ) (suc-ord ordδ) m s∈σ)

  same-case : (u σ δ : S) → sucV δ ≡ σ → sucV δ ≡ σ
  same-case u σ δ e = e

meet-suc : (u σ : S) → IsOrd σ → ⟨ meets u σ ⟩ → isLeastOrd (meets u) σ
         → ∥ Σ[ δ ∈ S ] IsPredOf σ δ ∥₁
meet-suc u σ ordσ m least = PT.rec squash₁ atMember m
  where
  atCarve : (z : S) → ⟨ z ∈ˢ u ⟩
          → Σ[ δ ∈ S ] (⟨ δ ∈ˢ σ ⟩ × ⟨ z ∈ˢ 𝒟ₒ (Lset δ) ⟩)
          → Σ[ δ ∈ S ] IsPredOf σ δ
  atCarve z z∈u (δ , (δ∈σ , z∈𝒟ₒδ)) = δ , (ordδ , suc≡σ)
    where
    ordδ : IsOrd δ
    ordδ = mem-ord {A = σ} ordσ δ δ∈σ
    metAtSuc : ⟨ meets u (sucV δ) ⟩
    metAtSuc = ∣ z , (z∈u
      , subst (λ w → ⟨ z ∈ˢ w ⟩) (sym (Lset-suc δ)) z∈𝒟ₒδ) ∣₁
    suc≡σ : sucV δ ≡ σ
    suc≡σ = Sum.rec (below-case u σ δ least ordδ metAtSuc) (same-case u σ δ)
      (suc∈or≡ δ σ ordδ ordσ δ∈σ)

  atMember : Σ[ z ∈ S ] (⟨ z ∈ˢ u ⟩ × ⟨ z ∈ˢ Lset σ ⟩)
           → ∥ Σ[ δ ∈ S ] IsPredOf σ δ ∥₁
  atMember (z , (z∈u , z∈Lσ)) = PT.map (atCarve z z∈u) (Lset-out σ z z∈Lσ)

thePred : (u : S) (pu : ⟨ isL u ⟩) (h : Inhabited u)
        → Σ[ δ ∈ S ] IsPredOf (μ u pu h) δ
thePred u pu h = PT.rec (isPropPredOf (μ u pu h)) (λ d → d)
  (meet-suc u (μ u pu h) (μ-ord u pu h) (μ-meets u pu h) (μ-earliest u pu h))

opaque
  defStage : (u : S) → ⟨ isL u ⟩ → Inhabited u → S
  defStage u pu h = thePred u pu h .fst

opaque
  unfolding defStage
  defStage-ord : (u : S) (pu : ⟨ isL u ⟩) (h : Inhabited u)
               → IsOrd (defStage u pu h)
  defStage-ord u pu h = thePred u pu h .snd .fst

  defStage-suc : (u : S) (pu : ⟨ isL u ⟩) (h : Inhabited u)
               → sucV (defStage u pu h) ≡ μ u pu h
  defStage-suc u pu h = thePred u pu h .snd .snd

------------------------------------------------------------------------
-- PART B.  src/L/Choice/Step.lagda.md:106-142, verbatim.
------------------------------------------------------------------------

private
  decideSuc : (x : S) (p : ⟨ isL x ⟩) (δ : S) → IsOrd δ
            → ⟨ x ∈ˢ Lset (sucV δ) ⟩
            → ⟨ sucV δ ∈ˢ stage x p ⟩ ⊎ (sucV δ ≡ stage x p)
            → sucV δ ≡ stage x p
  decideSuc x p δ ordδ m (inl s∈) =
    Empty.rec (stage-earliest x p (sucV δ) (suc-ord ordδ) m s∈)
  decideSuc x p δ ordδ m (inr e) = e

  atCarveStep : (x : S) (p : ⟨ isL x ⟩)
              → Σ[ δ ∈ S ] (⟨ δ ∈ˢ stage x p ⟩ × ⟨ x ∈ˢ 𝒟ₒ (Lset δ) ⟩)
              → Σ[ δ ∈ S ] IsPredOf (stage x p) δ
  atCarveStep x p (δ , (δ∈ , x∈)) = δ , (ordδ , suc≡)
    where
    ordδ : IsOrd δ
    ordδ = mem-ord {A = stage x p} (stage-ord x p) δ δ∈
    atSuc : ⟨ x ∈ˢ Lset (sucV δ) ⟩
    atSuc = subst (λ w → ⟨ x ∈ˢ w ⟩) (sym (Lset-suc δ)) x∈
    suc≡ : sucV δ ≡ stage x p
    suc≡ = decideSuc x p δ ordδ atSuc
      (suc∈or≡ δ (stage x p) ordδ (stage-ord x p) δ∈)

theCarve : (x : S) (p : ⟨ isL x ⟩) → Σ[ δ ∈ S ] IsPredOf (stage x p) δ
theCarve x p = PT.rec (isPropPredOf (stage x p)) (atCarveStep x p)
  (Lset-out (stage x p) x (stage-mem x p))

opaque
  birth : (x : S) → ⟨ isL x ⟩ → S
  birth x p = theCarve x p .fst

opaque
  unfolding birth
  birth-ord : (x : S) (p : ⟨ isL x ⟩) → IsOrd (birth x p)
  birth-ord x p = theCarve x p .snd .fst

  birth-suc : (x : S) (p : ⟨ isL x ⟩) → sucV (birth x p) ≡ stage x p
  birth-suc x p = theCarve x p .snd .snd
