{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.570] W3.  The widest unmeasured term: `levelIn`, re-ascribed at
-- the frame `gch-from-five` calls it.  TYPE ONLY, no inhabitant.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-570.runs.W3 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ} using ( IsOrd; Lset )
open import L.BoundedSubset {ℓ} lem using ( IsCardinal; _↪_ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet; _∪_; ⁅_⁆s )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫ )
open InfinitySet {ℓ} using ( ω; sucV )
import Cubical.Data.Empty as Empty

import LJ-1-550.Probe550 {ℓ} lem as P550

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
module SV = hPropStructure 𝒮ᵥ
open SV using ( _∈ˢ_ )

-- `levelIn` alone, at `CoHyps`'s telescope (Probe550.agda:215-230).
LevelInAt : Type (ℓ-suc ℓ)
LevelInAt =
    (κ : SV.S) (ordκ : IsOrd κ) (cardκ : IsCardinal κ)
    (κ∉ω : ⟨ κ ∈ˢ ω ⟩ → Empty.⊥)
    (α : SV.S) (ordα : IsOrd α) (α∈κ : ⟨ α ∈ˢ κ ⟩)
    (α∉ω : ⟨ α ∈ˢ ω ⟩ → Empty.⊥)
    (sq : P550.SqLaw α)
    (x : SV.S) (x⊆Lα : (z : SV.S) → ⟨ z ∈ˢ x ⟩ → ⟨ z ∈ˢ Lset α ⟩)
    (absorbs : ⟪ Lset α ∪ ⁅ x ⁆s ⟫ ↪ ⟪ Lset α ⟫)
    (lam : SV.S) (ordλ : IsOrd lam) (α∈λ : ⟨ α ∈ˢ lam ⟩)
    (succλ : (d : SV.S) → ⟨ d ∈ˢ lam ⟩ → ⟨ sucV d ∈ˢ lam ⟩)
    (x∈Lλ : ⟨ x ∈ˢ Lset lam ⟩)
  → P550.Tele.LevelIn κ ordκ cardκ κ∉ω α ordα α∈κ α∉ω sq x x⊆Lα absorbs
      lam ordλ α∈λ succλ x∈Lλ
