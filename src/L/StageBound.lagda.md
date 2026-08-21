# The stage bound

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module L.StageBound {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ} using ( IsOrd; Lset )
open import L.BoundedSubset {ℓ} lem using
  ( module Devlin55; module UnionKit; module HullStage; IsCardinal; _↪_ )

open import Cubical.Data.Sigma using ( Σ-syntax )
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( _∪_; ⁅_⁆s; module InfinitySet )
open InfinitySet using ( ω; sucV )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ

-- The consumer's square-law family, copied from
-- src/L/BoundedSubset.lagda.md:1388-1390.

SqFam : S → Type (ℓ-suc ℓ)
SqFam α =
  (δ : S) → ⟨ δ ∈ˢ sucV α ⟩ → (⟨ δ ∈ˢ ω ⟩ → Empty.⊥)
  → Σ[ f ∈ (⟪ δ ⟫ × ⟪ δ ⟫ → ⟪ δ ⟫) ]
      ((u v : ⟪ δ ⟫ × ⟪ δ ⟫) → f u ≡ f v → u ≡ v)

-- Instantiation: sq as plain data, two module applications.
-- Telescope of BoundedSubsetAt plus Co, copied unchanged.

module Instantiation
  (κ : S) (ordκ : IsOrd κ) (cardκ : IsCardinal κ) (κ∉ω : ⟨ κ ∈ˢ ω ⟩ → Empty.⊥)
  (α : S) (ordα : IsOrd α) (α∈κ : ⟨ α ∈ˢ κ ⟩) (α∉ω : ⟨ α ∈ˢ ω ⟩ → Empty.⊥)
  (sq : SqFam α)
  (x : S) (x⊆Lα : (z : S) → ⟨ z ∈ˢ x ⟩ → ⟨ z ∈ˢ Lset α ⟩)
  (absorbs : ⟪ Lset α ∪ ⁅ x ⁆s ⟫ ↪ ⟪ Lset α ⟫)
  (lam : S) (ordλ : IsOrd lam) (α∈λ : ⟨ α ∈ˢ lam ⟩)
  (succλ : (d : S) → ⟨ d ∈ˢ lam ⟩ → ⟨ sucV d ∈ˢ lam ⟩)
  (x∈Lλ : ⟨ x ∈ˢ Lset lam ⟩) where

  module BSA = Devlin55.BoundedSubsetAt κ ordκ cardκ κ∉ω
    α ordα α∈κ α∉ω sq
    x x⊆Lα absorbs
    lam ordλ α∈λ succλ x∈Lλ

  module Co
    (levelIn : (δ : S) → IsOrd δ → ⟨ δ ∈ˢ BSA.HS.C.πX ⟩ → ⟨ Lset δ ∈ˢ BSA.HS.C.πX ⟩)
    (cover : (y : S) → ⟨ y ∈ˢ BSA.HS.M ⟩
           → ∥ Σ[ γ ∈ S ] (IsOrd γ × ⟨ γ ∈ˢ BSA.HS.C.πX ⟩ × ⟨ BSA.HS.C.π y ∈ˢ Lset γ ⟩) ∥₁)
    where

    module C = BSA.Co levelIn cover

    theorem : ⟨ x ∈ˢ Lset κ ⟩
    theorem = C.theorem

-- UnionKit and HullStage take no sq, so Co's two hypotheses stay as
-- module parameters, copied unchanged. go applies Instantiation then Co.

module _
  (κ : S) (ordκ : IsOrd κ) (cardκ : IsCardinal κ) (κ∉ω : ⟨ κ ∈ˢ ω ⟩ → Empty.⊥)
  (α : S) (ordα : IsOrd α) (α∈κ : ⟨ α ∈ˢ κ ⟩) (α∉ω : ⟨ α ∈ˢ ω ⟩ → Empty.⊥)
  (x : S) (x⊆Lα : (z : S) → ⟨ z ∈ˢ x ⟩ → ⟨ z ∈ˢ Lset α ⟩)
  (absorbs : ⟪ Lset α ∪ ⁅ x ⁆s ⟫ ↪ ⟪ Lset α ⟫)
  (lam : S) (ordλ : IsOrd lam) (α∈λ : ⟨ α ∈ˢ lam ⟩)
  (succλ : (d : S) → ⟨ d ∈ˢ lam ⟩ → ⟨ sucV d ∈ˢ lam ⟩)
  (x∈Lλ : ⟨ x ∈ˢ Lset lam ⟩) where

  module UK = UnionKit α lam x ordα ordλ α∈λ x⊆Lα x∈Lλ α∉ω
  module HS = HullStage lam ordλ succλ UK.X UK.X⊆Lλ UK.∅∈λ

  module _
    (levelIn : (δ : S) → IsOrd δ → ⟨ δ ∈ˢ HS.C.πX ⟩ → ⟨ Lset δ ∈ˢ HS.C.πX ⟩)
    (cover : (y : S) → ⟨ y ∈ˢ HS.M ⟩
           → ∥ Σ[ γ ∈ S ] (IsOrd γ × ⟨ γ ∈ˢ HS.C.πX ⟩ × ⟨ HS.C.π y ∈ˢ Lset γ ⟩) ∥₁)
    where

    go : SqFam α → ⟨ x ∈ˢ Lset κ ⟩
    go sqf = C.theorem
      where
      module I = Instantiation κ ordκ cardκ κ∉ω
        α ordα α∈κ α∉ω sqf
        x x⊆Lα absorbs
        lam ordλ α∈λ succλ x∈Lλ
      module C = I.Co levelIn cover

    -- One outer PT.rec of Instantiation.Co.theorem, with the chapter's
    -- own isProp witness. The branch is go, with a written type.
    bounded-from-trunc : ∥ SqFam α ∥₁ → ⟨ x ∈ˢ Lset κ ⟩
    bounded-from-trunc h = PT.rec (snd (x ∈ˢ Lset κ)) go h
```

