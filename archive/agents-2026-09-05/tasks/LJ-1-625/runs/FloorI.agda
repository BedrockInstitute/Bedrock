{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.625]  Floor for ingredient (i): a fresh module over exactly
-- (i)'s measured dependency set, with one inhabited row.  This prices
-- the frame a NEW master for (i) would elaborate in: five src modules,
-- transitive closure thirteen masters.  CALIBER: the program set
-- GHCRTS on this pane; I did not set it.

open import Base.Prelude
open import Base.Truth
open import Cubical.HITs.CumulativeHierarchy.Base using ( V )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫ )

module LJ-1-625.runs.FloorI {ℓ : Level} where

open import FOL.Syntax using ( Formula )
open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ} using ( Lset; 𝒟ₒ; 𝒟ₒ-inv )
open import L.Definability {ℓ} using ( module DefOf )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁ )
open hPropStructure 𝒮ᵥ using ( _∈ˢ_ )

floor : (δ : V ℓ) → Formula ⟪ Lset δ ⟫ 1 → V ℓ
floor δ φ = DefOf.defSet (Lset δ) φ
