{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.625]  Floor for ingredient (iv): a fresh module over exactly
-- (iv)'s measured dependency set, with one inhabited row.  This prices
-- the frame a NEW master for (iv) would elaborate in: ten src modules,
-- transitive closure thirty masters.  CALIBER: the program set GHCRTS
-- on this pane; I did not set it.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫ )
open import Cubical.HITs.CumulativeHierarchy.Constructions using ( module InfinitySet )
open import L.Constructible using ( IsOrd )
import Cubical.Data.Empty as Empty

module LJ-1-625.runs.FloorIV {ℓ : Level} (lem : LEM (ℓ-suc ℓ))
  (α₀ : V ℓ) (oα₀ : IsOrd α₀)
  (sq : (δ : V ℓ) → ⟨ δ ∈ InfinitySet.sucV α₀ ⟩ → (⟨ δ ∈ InfinitySet.ω {ℓ} ⟩ → Empty.⊥)
      → Σ[ f ∈ (⟪ δ ⟫ × ⟪ δ ⟫ → ⟪ δ ⟫) ]
          ((x y : ⟪ δ ⟫ × ⟪ δ ⟫) → f x ≡ f y → x ≡ y)) where

open import V.Hierarchy {ℓ} using ( 𝒮ᵥ; ∈-irrefl )
open import V.Presentation {ℓ} using ( member; fiber )
open import FOL.Syntax using ( Formula )
open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Absoluteness
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans; Lset→isL; Lset )
open import L.Ordinal {ℓ} using ( ω-ord; suc-ord; mem-ord )
open import L.Ordinal.Stages {ℓ} lem using ( ord∈Lset-suc )
open import L.Axioms.Basic {ℓ} using ( LsetS )
import L.StageCardinal
open InfinitySet {ℓ} using ( ω; sucV )
module SL = hPropStructure 𝒮ʟ
open SL using ( S )
module SC = L.StageCardinal {ℓ} lem α₀ oα₀ sq

floor : (δ : V ℓ) (oδ : IsOrd δ) → S
floor δ oδ = LsetS δ oδ
