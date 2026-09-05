{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.715] diagnostic round 3: parse hypothesis.  infixr 9 (the union)
-- used in prefix position may swallow (sett X f) ENTIRLY, i.e. parse
-- as (sett X f) applied to a ZF-structure membership: pure parse.
-- Compare the bare and the parenthesized spellings.

open import Base.Prelude
open import Base.Truth

module LJ-1-715.Diag715c {ℓ : Level} where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Model {ℓ} using ( ∈sucV-elim; ∈sucV-inl; self∈sucV )
open import L.Constructible {ℓ}
  using ( isTransV; isPropIsTransV; IsOrd; isPropIsOrd )
open import Cubical.Data.Bool using ( Bool; true; false )
open import Cubical.HITs.CumulativeHierarchy.Base using ( sett )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( _∈ₛ_; ∈∈ₛ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ∅; ∅-empty; ⋃_; union-ax; module InfinitySet )
open InfinitySet using ( sucV )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ

-- parenthesized left argument

unionClParen : (α : S) → Type (ℓ-suc ℓ)
unionClParen α =
  (X : Type ℓ) (f : X → S)
    → ((i : X) → ⟨ f i ∈ˢ α ⟩)
    → ⟨ (⋃ (sett X f)) ∈ˢ α ⟩

-- union on the right, the chapter's own shape, as a control

unionClRight : (α : S) → Type (ℓ-suc ℓ)
unionClRight α =
  (z : S) (X : Type ℓ) (f : X → S)
    → ⟨ z ∈ˢ (⋃ (sett X f)) ⟩ → ⟨ z ∈ˢ α ⟩
