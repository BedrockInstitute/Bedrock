{-# OPTIONS --cubical --guardedness #-}

-- [LJ-1.584]  D-10 FLOOR.  THE OBLIGATION'S TYPE, WITH A HOLE, IN THE
-- SMALLEST IMPORT SET THAT HOLDS IT.  Nothing is proved here.  This
-- file exists to measure what the STATEMENT costs before anything is
-- claimed about its truth.  `--safe` is off ONLY because of the hole.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫ )
open import Cubical.HITs.CumulativeHierarchy.Constructions using ( module InfinitySet )
open import L.Constructible using ( IsOrd )
import Cubical.Data.Empty as Empty

module LJ-1-584.runs.Floor {ℓ : Level} (lem : LEM (ℓ-suc ℓ))
  (α₀ : V ℓ) (oα₀ : IsOrd α₀)
  (sq : (δ : V ℓ) → ⟨ δ ∈ InfinitySet.sucV α₀ ⟩ → (⟨ δ ∈ InfinitySet.ω {ℓ} ⟩ → Empty.⊥)
      → Σ[ f ∈ (⟪ δ ⟫ × ⟪ δ ⟫ → ⟪ δ ⟫) ]
          ((x y : ⟪ δ ⟫ × ⟪ δ ⟫) → f x ≡ f y → x ≡ y)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Axioms.Basic {ℓ} using ( LsetS )
open import Cubical.Data.Sigma using ( _×_ )
open InfinitySet {ℓ} using ( sucV; ω )
import L.StageCardinal

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
module SV = hPropStructure 𝒮ᵥ
open SV using ( _∈ˢ_ )

module SC = L.StageCardinal {ℓ} lem α₀ oα₀ sq

import LJ-1-568.Probe568 {ℓ} lem α₀ oα₀ sq as P568

-- THE OBLIGATION, WITH A HOLE.  `Def` is IMPORTED, not transcribed.
stage-bound-definable :
    (α : V ℓ) (oα : IsOrd α) (α∈suc : ⟨ α ∈ˢ sucV α₀ ⟩)
    (α∉ω : ⟨ α ∈ˢ ω ⟩ → Empty.⊥)
  → P568.Def (LsetS α oα) (P568.ordS α oα)
      (fst (SC.Upper.stage-card-upper α oα α∈suc α∉ω))
stage-bound-definable = {!!}
