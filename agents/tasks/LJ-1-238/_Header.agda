{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

open import FOL.ZFStructure using ( module hPropStructure; Transitive; _↾_ )
open import V.Hierarchy using ( 𝒮ᵥ )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ⁅_,_⁆ ) renaming ( module InfinitySet to Inf )
open Inf using ( #_; sucV )

module LJ-1-238.GenSequence {ℓ : Level} (lem : LEM (ℓ-suc ℓ))
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

open import FOL.Syntax using ( Formula; var; _∈̇_; _∧̇_; _⇒̇_; ∃̇_; ∀̇_ )
import FOL.Absoluteness
open import V.Coding {ℓ} using ( pr )
open import L.Constructible {ℓ} using ( 𝒟ₒ )
import LJ-1-210.GenModel

import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁; ∣_∣₁; squash₁ )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )

module GM = LJ-1-210.GenModel {ℓ} M M-trans
              numeralL numeralL-fst pairʟ pairʟ-fst sucʟ sucʟ-fst
open GM
  using ( extAt; extAt-out; extAt-in; extAt-in-both; appAt; appAt-adequate
        ; domAt; domAt-in; domAt-out; prAtL; prAtL-adequate )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure (𝒮ᵥ {ℓ} ↾ M)

module AbsL = FOL.Absoluteness.Single (𝒮ᵥ {ℓ}) M (λ {x} {y} → M-trans {x} {y})
open AbsL renaming ( _⊨ᵐ_ to _⊨_ )

DefOK : S → Type (ℓ-suc ℓ)
DefOK A = (x : V ℓ) → ⟨ x ∈ 𝒟ₒ (fst A) ⟩ → ⟨ M x ⟩

module Body (DefAt : ∀ {n} → Fin n → Fin n → Formula S n)
         (DefAt-in : (A : S) → ∀ {n} (u w : Fin n) (γ : S ^ n)
                   → fst (lookup w γ) ≡ fst A
                   → fst (lookup u γ) ≡ 𝒟ₒ (fst A)
                   → ⟨ γ ⊨ DefAt u w ⟩)
         (DefAt-out : (A : S) → ∀ {n} (u w : Fin n) (γ : S ^ n) → DefOK A
                    → fst (lookup w γ) ≡ fst A
                    → ⟨ γ ⊨ DefAt u w ⟩
                    → fst (lookup u γ) ≡ 𝒟ₒ (fst A))
         where

