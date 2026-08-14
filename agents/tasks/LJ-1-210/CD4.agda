{-# OPTIONS --cubical --safe --guardedness #-}
open import Base.Prelude
open import Base.Truth
open import FOL.ZFStructure using ( Transitive )
open import V.Hierarchy using ( 𝒮ᵥ )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ⁅_,_⁆ ) renaming ( module InfinitySet to Inf )
open Inf using ( #_; sucV )
module LJ-1-210.CD4 where
record ClassData (ℓ : Level) : Type (ℓ-suc (ℓ-suc ℓ)) where
  field
    M : V ℓ → hProp (ℓ-suc ℓ)
    M-trans : Transitive (𝒮ᵥ {ℓ}) M
    numeralL : ℕ → Σ[ x ∈ V ℓ ] ⟨ M x ⟩
    numeralL-fst : (k : ℕ) → fst (numeralL k) ≡ # k
    pairʟ : (a b : Σ[ x ∈ V ℓ ] ⟨ M x ⟩) → Σ[ x ∈ V ℓ ] ⟨ M x ⟩
    pairʟ-fst : (a b : Σ[ x ∈ V ℓ ] ⟨ M x ⟩)
              → fst (pairʟ a b) ≡ ⁅ fst a , fst b ⁆
