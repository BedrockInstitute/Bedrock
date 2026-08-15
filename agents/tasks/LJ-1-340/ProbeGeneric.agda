{-# OPTIONS --cubical --safe --guardedness #-}

-- LJ-1.340 GENERIC FORM.  It lands nothing.  It runs in
-- agents/tasks/LJ-1-340/.
--
-- THE QUESTION: can the predecessor extraction be written ONCE, generic in
-- the property, so that both delivered sites use it?
--
-- PART 0 is the generic form.  It is generic in the ORDINAL PROPERTY `P`,
--        which is a MODULE parameter and never a field of a record.  A law
--        of this family (C-55) says a hypothesis folded into a record
--        exhausts 8 GB where the same hypothesis is free as a module
--        parameter.
-- PART A is the L.Choice.Stage application, with the seal on top.
-- PART B is the L.Choice.Step application, with the seal on top.
--
-- ProbeControl.agda holds the two delivered arguments verbatim under the
-- same imports.  The two files differ ONLY in the argument.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-340.ProbeGeneric {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

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
-- PART 0.  The generic form.  Written once.
------------------------------------------------------------------------

module _ (P : S → Ω) where

  Carved : S → Type (ℓ-suc ℓ)
  Carved σ = Σ[ δ ∈ S ] (⟨ δ ∈ˢ σ ⟩ × ⟨ P (sucV δ) ⟩)

  private
    below-case : (σ δ : S) → isLeastOrd P σ → IsOrd δ → ⟨ P (sucV δ) ⟩
               → ⟨ sucV δ ∈ˢ σ ⟩ → sucV δ ≡ σ
    below-case σ δ least ordδ m s∈σ =
      Empty.rec (least (sucV δ) (suc-ord ordδ) m s∈σ)

    same-case : (σ δ : S) → sucV δ ≡ σ → sucV δ ≡ σ
    same-case σ δ e = e

    atCarve : (σ : S) → IsOrd σ → isLeastOrd P σ
            → Carved σ → Σ[ δ ∈ S ] IsPredOf σ δ
    atCarve σ ordσ least (δ , (δ∈σ , m)) = δ , (ordδ , suc≡σ)
      where
      ordδ : IsOrd δ
      ordδ = mem-ord {A = σ} ordσ δ δ∈σ
      suc≡σ : sucV δ ≡ σ
      suc≡σ = Sum.rec (below-case σ δ least ordδ m) (same-case σ δ)
        (suc∈or≡ δ σ ordδ ordσ δ∈σ)

  predOf : (σ : S) → IsOrd σ → isLeastOrd P σ → ∥ Carved σ ∥₁
         → Σ[ δ ∈ S ] IsPredOf σ δ
  predOf σ ordσ least = PT.rec (isPropPredOf σ) (atCarve σ ordσ least)

  carveAt : (σ z : S) → ⟨ z ∈ˢ Lset σ ⟩
          → ((δ : S) → ⟨ z ∈ˢ Lset (sucV δ) ⟩ → ⟨ P (sucV δ) ⟩)
          → ∥ Carved σ ∥₁
  carveAt σ z z∈Lσ k = PT.map
    (λ { (δ , (δ∈σ , z∈𝒟)) → δ , (δ∈σ
      , k δ (subst (λ w → ⟨ z ∈ˢ w ⟩) (sym (Lset-suc δ)) z∈𝒟)) })
    (Lset-out σ z z∈Lσ)

------------------------------------------------------------------------
-- PART A.  The L.Choice.Stage application, with :260-272 on top.
------------------------------------------------------------------------

thePred : (u : S) (pu : ⟨ isL u ⟩) (h : Inhabited u)
        → Σ[ δ ∈ S ] IsPredOf (μ u pu h) δ
thePred u pu h = predOf (meets u) (μ u pu h) (μ-ord u pu h) (μ-earliest u pu h)
  (PT.rec squash₁
    (λ { (z , (z∈u , z∈Lσ)) → carveAt (meets u) (μ u pu h) z z∈Lσ
      (λ δ hz → ∣ z , (z∈u , hz) ∣₁) })
    (μ-meets u pu h))

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
-- PART B.  The L.Choice.Step application, with :132-142 on top.
------------------------------------------------------------------------

theCarve : (x : S) (p : ⟨ isL x ⟩) → Σ[ δ ∈ S ] IsPredOf (stage x p) δ
theCarve x p = predOf (λ σ → x ∈ˢ Lset σ) (stage x p) (stage-ord x p)
  (stage-earliest x p)
  (carveAt (λ σ → x ∈ˢ Lset σ) (stage x p) x (stage-mem x p) (λ δ hz → hz))

opaque
  birth : (x : S) → ⟨ isL x ⟩ → S
  birth x p = theCarve x p .fst

opaque
  unfolding birth
  birth-ord : (x : S) (p : ⟨ isL x ⟩) → IsOrd (birth x p)
  birth-ord x p = theCarve x p .snd .fst

  birth-suc : (x : S) (p : ⟨ isL x ⟩) → sucV (birth x p) ≡ stage x p
  birth-suc x p = theCarve x p .snd .snd
