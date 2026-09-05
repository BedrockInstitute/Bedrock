{-# OPTIONS --cubical --safe --guardedness #-}
-- [LJ-1.574] D1.  COST ISOLATION: the imports alone, nothing else.
open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫ )
open import Cubical.HITs.CumulativeHierarchy.Constructions using ( module InfinitySet )
open import L.Constructible using ( IsOrd )
import Cubical.Data.Empty as Empty

module LJ-1-574.runs.D1 {ℓ : Level} (lem : LEM (ℓ-suc ℓ))
  (α₀ : V ℓ) (oα₀ : IsOrd α₀)
  (sq : (δ : V ℓ) → ⟨ δ ∈ InfinitySet.sucV α₀ ⟩ → (⟨ δ ∈ InfinitySet.ω {ℓ} ⟩ → Empty.⊥)
      → Σ[ f ∈ (⟪ δ ⟫ × ⟪ δ ⟫ → ⟪ δ ⟫) ]
          ((x y : ⟪ δ ⟫ × ⟪ δ ⟫) → f x ≡ f y → x ≡ y)) where

import LJ-1-549.Probe549 {ℓ} lem as P549
import LJ-1-554.Probe554 {ℓ} lem as P554
import LJ-1-557.Probe557 {ℓ} lem as P557
import LJ-1-561.Probe561 {ℓ} lem α₀ oα₀ sq as P561
import LJ-1-568.Probe568 {ℓ} lem α₀ oα₀ sq as P568

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ} using ( 𝒮ʟ )
open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ using ( S )

-- one re-ascription each, TYPE ONLY, so the interfaces are actually forced.
d1-residue : (δ κ : S) → Type (ℓ-suc ℓ)
d1-residue = P549.Residue

d1-def : (a b : S) (g : ⟪ fst a ⟫ → ⟪ fst b ⟫) → Type (ℓ-suc ℓ)
d1-def = P568.Def

d1-up : (b : S) → ⟪ fst b ⟫ → S
d1-up = P561.up
