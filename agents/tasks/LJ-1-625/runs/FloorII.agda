{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.625]  Floor for ingredient (ii): a fresh module over exactly
-- (ii)'s measured dependency set, with one inhabited row.  This prices
-- the frame a NEW master for (ii) would elaborate in: five src
-- modules, transitive closure thirty masters (the site chapter's
-- closure).  CALIBER: the program set GHCRTS on this pane; I did not
-- set it.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫ )
open import Cubical.HITs.CumulativeHierarchy.Constructions using ( module InfinitySet )
open import L.Constructible using ( IsOrd )
import Cubical.Data.Empty as Empty

module LJ-1-625.runs.FloorII {ℓ : Level} (lem : LEM (ℓ-suc ℓ))
  (α₀ : V ℓ) (oα₀ : IsOrd α₀)
  (sq : (δ : V ℓ) → ⟨ δ ∈ InfinitySet.sucV α₀ ⟩ → (⟨ δ ∈ InfinitySet.ω {ℓ} ⟩ → Empty.⊥)
      → Σ[ f ∈ (⟪ δ ⟫ × ⟪ δ ⟫ → ⟪ δ ⟫) ]
          ((x y : ⟪ δ ⟫ × ⟪ δ ⟫) → f x ≡ f y → x ≡ y)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁ )
open import L.WellOrder.Base {ℓₚ = ℓ-suc ℓ} using ( SWO; leastOf; IsLeast )
import L.StageCardinal
module SC = L.StageCardinal {ℓ} lem α₀ oα₀ sq
open hPropStructure 𝒮ᵥ using ( _∈ˢ_ )

floor : (δ : V ℓ) (oδ : IsOrd δ) (P : ⟪ δ ⟫ → hProp (ℓ-suc ℓ))
      → ∥ Σ[ a ∈ ⟪ δ ⟫ ] ⟨ P a ⟩ ∥₁
      → Σ[ a ∈ ⟪ δ ⟫ ] IsLeast (SC.OrdSWO.ordSWO δ oδ) P a
floor δ oδ = leastOf (SC.OrdSWO.ordSWO δ oδ) lem
