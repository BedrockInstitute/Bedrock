{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.625]  Floor for ingredient (v): a fresh module over exactly
-- (v)'s measured dependency set, with one inhabited row.  This prices
-- the frame a NEW master for (v) would elaborate in: six src modules,
-- transitive closure forty-five masters.  CALIBER: the program set
-- GHCRTS on this pane; I did not set it.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫ )
open import L.Constructible using ( IsOrd )

module LJ-1-625.runs.FloorV {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.Syntax using ( Formula )
open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ} using ( 𝒮ʟ; Lset )
open import L.Axioms.Basic {ℓ} using ( LsetS )
open import L.Coding.CodeSet {ℓ} lem
  using ( keyS; AllCodes; key∈AllCodes; AllCodes-out )
module SL = hPropStructure 𝒮ʟ
open SL using ( S )

floor : (δ : V ℓ) (oδ : IsOrd δ) → Formula ⟪ Lset δ ⟫ 1 → S
floor δ oδ = keyS (LsetS δ oδ)
