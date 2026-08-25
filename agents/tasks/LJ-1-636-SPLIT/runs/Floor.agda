{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.636-split]  FLOOR.  What does the ELABORATION FRAME cost, before
-- any at-ω conclusion is asked for?  This file instantiates
-- `Devlin55.BoundedSubsetAt` at ambient `ω` and stops there: it names NO
-- consequence.  Its price is the floor the standing clause orders me to
-- measure before I attempt the real term.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-636-SPLIT.runs.Floor {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ; ∈-irrefl )
open import V.Model {ℓ} using ( ∈sucV-elim )
open import L.Constructible {ℓ} using ( IsOrd; Lset )
open import L.Ordinal {ℓ} using ( ω-ord )
open import L.InjChain {ℓ} lem using ( squareω )
open import L.BoundedSubset {ℓ} lem using ( IsCardinal; _↪_; module Devlin55 )

open import Cubical.Data.Sigma using ( Σ-syntax; _×_ )
import Cubical.Data.Empty as Empty
open import Cubical.HITs.CumulativeHierarchy.Base using ( setIsSet )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet; _∪_; ⁅_⁆s )
open InfinitySet using ( ω; sucV )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ

-- The `sq` parameter's value type, copied from its binder
-- (src/L/StageCardinal.lagda.md:18-20).
Sq : S → Type ℓ
Sq δ = Σ[ f ∈ (⟪ δ ⟫ × ⟪ δ ⟫ → ⟪ δ ⟫) ]
         ((u v : ⟪ δ ⟫ × ⟪ δ ⟫) → f u ≡ f v → u ≡ v)

-- [LJ-1.636]'s `collapse-at-ω`, Probe636.agda:377-381.  Re-derived, not
-- imported: that probe is on a SIBLING WORKTREE and not on this branch.
collapse-at-ω : (δ : S) → ⟨ δ ∈ˢ sucV ω ⟩ → (⟨ δ ∈ˢ ω ⟩ → Empty.⊥) → δ ≡ ω
collapse-at-ω δ δ∈sucVω infδ =
  ∈sucV-elim {A = ω} {x = δ} (setIsSet δ ω) δ∈sucVω
    (λ δ∈ω → Empty.rec (infδ δ∈ω))
    (λ e → e)

-- [LJ-1.636]'s `param-at-ω`, Probe636.agda:391-392.
param-at-ω : (δ : S) → ⟨ δ ∈ˢ sucV ω ⟩ → (⟨ δ ∈ˢ ω ⟩ → Empty.⊥) → Sq δ
param-at-ω δ δ∈suc infδ = subst Sq (sym (collapse-at-ω δ δ∈suc infδ)) squareω

-- THE FRAME AND NOTHING ELSE.  Every hypothesis that SURVIVES the
-- instantiation is a parameter here; the three that DIE are supplied.
module Frame
  (κ : S) (ordκ : IsOrd κ) (cardκ : IsCardinal κ) (κ∉ω : ⟨ κ ∈ˢ ω ⟩ → Empty.⊥)
  (ω∈κ : ⟨ ω ∈ˢ κ ⟩)
  (x : S) (x⊆Lω : (z : S) → ⟨ z ∈ˢ x ⟩ → ⟨ z ∈ˢ Lset ω ⟩)
  (absorbs : ⟪ Lset ω ∪ ⁅ x ⁆s ⟫ ↪ ⟪ Lset ω ⟫)
  (lam : S) (ordλ : IsOrd lam) (ω∈λ : ⟨ ω ∈ˢ lam ⟩)
  (succλ : (d : S) → ⟨ d ∈ˢ lam ⟩ → ⟨ sucV d ∈ˢ lam ⟩)
  (x∈Lλ : ⟨ x ∈ˢ Lset lam ⟩)
  where

  module B = Devlin55.BoundedSubsetAt
    κ ordκ cardκ κ∉ω
    ω ω-ord ω∈κ (∈-irrefl ω)
    param-at-ω
    x x⊆Lω absorbs
    lam ordλ ω∈λ succλ x∈Lλ

  -- one cheap projection, to force the telescope to elaborate
  floor-witness : S
  floor-witness = B.HS.C.πX
