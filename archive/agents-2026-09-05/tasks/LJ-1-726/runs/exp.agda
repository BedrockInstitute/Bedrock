{-# OPTIONS --cubical --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-726.runs.exp {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
import FOL.Semantics
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁; ∣_∣₁; squash₁ )

open import Cubical.Data.Vec using ( lookup )
open import Cubical.Foundations.Prelude using ( transport; cong )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V )

open import L.Constructible {ℓ} using ( 𝒮ʟ )
open import LJ-1-652.Probe652 {ℓ} lem as P652
open import FOL.ZFStructure using ( module hPropStructure )
open hPropStructure 𝒮ᵥ
module CS = hPropStructure 𝒮ʟ

module SemV = FOL.Semantics (hPropAlgebra (ℓ-suc ℓ)) 𝒮ᵥ
open SemV using ( _^_ )
module AtF = SemV.At CS.S fst

Aₓ : Set
Aₓ = V ℓ

go12 : (x₁₁ x₁₀ x₉ x₈ x₇ x₆ x₅ x₄ x₃ x₂ x₁ x₁₂ m : Aₓ) → Aₓ
go12 x₁₁ x₁₀ x₉ x₈ x₇ x₆ x₅ x₄ x₃ x₂ x₁ x₁₂ m =
  PT.rec squash₁ (λ { (c , c∈ , dmb , forallpart) → cstep c c∈ dmb }) (m .snd .snd)
  where
  cstep : (c : Aₓ) → Aₓ → Aₓ → Aₓ
  cstep c c∈ dmb =
    ∣ c , (c∈ ,
      λ x x∈z x∈p →
      PT.rec squash₁ yfun (transport (cong (λ q → q) refl) (dmb x x∈z .snd x∈p))) ∣₁
    where
    yfun : Σ _ (λ y → Σ _ (λ _ → Aₓ)) → Aₓ
    yfun (y , y∈ , appsat) =
      PT.rec squash₁ wfun (transport (cong (λ q → q) refl) appsat)
      where
      wfun : Σ _ (λ w → Σ _ (λ _ → Aₓ)) → Aₓ
      wfun (w , wpair) =
        ∣ y , (y∈ , subst (λ q → q) (sym (wpair .snd)) (wpair .fst)) ∣₁
