{-# OPTIONS --cubical --safe --guardedness #-}
open import Base.Prelude
open import Base.Truth
open import FOL.ZFStructure using ( Transitive )
open import V.Hierarchy using ( 𝒮ᵥ )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  renaming ( module InfinitySet to Inf )
open Inf using ( sucV )
module LJ-1-210.CD5 where
record ClassData (ℓ : Level) : Type (ℓ-suc (ℓ-suc ℓ)) where
  field
    M : V ℓ → hProp (ℓ-suc ℓ)
    M-trans : Transitive (𝒮ᵥ {ℓ}) M
    sucʟ : Σ[ x ∈ V ℓ ] ⟨ M x ⟩ → Σ[ x ∈ V ℓ ] ⟨ M x ⟩
    sucʟ-fst : (a : Σ[ x ∈ V ℓ ] ⟨ M x ⟩) → fst (sucʟ a) ≡ sucV (fst a)
