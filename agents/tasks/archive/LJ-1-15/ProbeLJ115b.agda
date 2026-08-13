{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module ProbeLJ115b {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Model {ℓ} using ( ∈sucV-inl; self∈sucV )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V )
open import L.Constructible {ℓ} using ( IsOrd; Lset )
open import L.Ordinal {ℓ} using ( suc-ord )
open import L.Ordinal.Stages {ℓ} lem using ( suc∈or≡ )
open import Cubical.Data.Sum as Sum using ( _⊎_; inl; inr )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet )
open InfinitySet using ( sucV )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ

test : (δ : V ℓ) (oδ : IsOrd δ) (β : V ℓ) (oβ : IsOrd β)
     → ⟨ β ∈ˢ δ ⟩ → (⟨ sucV β ∈ˢ δ ⟩ ⊎ (sucV β ≡ δ))
test δ oδ β oβ β∈δ = suc∈or≡ β δ oβ oδ β∈δ

test3 : (δ : V ℓ) (oδ : IsOrd δ) (β : V ℓ) (oβ : IsOrd β)
      → ⟨ β ∈ˢ δ ⟩ → ⟨ sucV β ∈ˢ sucV δ ⟩
test3 δ oδ β oβ β∈δ =
  Sum.rec (λ s∈δ → ∈sucV-inl {A = δ} {x = sucV β} s∈δ)
          (λ s≡δ → subst (λ w → ⟨ w ∈ˢ sucV δ ⟩) (sym s≡δ) (self∈sucV δ))
          (suc∈or≡ β δ oβ oδ β∈δ)
