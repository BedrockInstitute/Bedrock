{-# OPTIONS --cubical --safe --guardedness #-}
open import Base.Prelude
open import Base.Truth
open import V.Hierarchy using ( 𝒮ᵥ )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  renaming ( module InfinitySet to Inf )
open Inf using ( sucV )
-- The SAME type as CD5's walling field, in a module telescope and in a
-- top-level definition. Neither is a record field.
module LJ-1-210.CD6 {ℓ : Level}
  (M : V ℓ → hProp (ℓ-suc ℓ))
  (sucʟ : Σ[ x ∈ V ℓ ] ⟨ M x ⟩ → Σ[ x ∈ V ℓ ] ⟨ M x ⟩)
  (sucʟ-fst : (a : Σ[ x ∈ V ℓ ] ⟨ M x ⟩) → fst (sucʟ a) ≡ sucV (fst a))
  where

SucSpec : Type (ℓ-suc ℓ)
SucSpec = (a : Σ[ x ∈ V ℓ ] ⟨ M x ⟩) → fst (sucʟ a) ≡ sucV (fst a)
