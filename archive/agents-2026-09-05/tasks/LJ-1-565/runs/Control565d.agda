{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.565] CONTROL d.  THE SMALLEST ROW LEFT.
--
-- Control565c walls with NO stage move and NO proof obligation beyond
-- `refl` between two spellings of the SAME set.  So this file removes
-- the `refl` too.  It states ONE type synonym and proves NOTHING.
--
-- If FORMING `HierBelow` at a successor is what costs, then no proof
-- body can ever be reached, and [LJ-1.536]'s successor step is not
-- blocked by a conversion at all.
--
-- ONE Agda process per run, GHCRTS="-A64m -I0 -M8g", the wide caliber.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-565.runs.Control565d {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ} using ( 𝒮ʟ; IsOrd )
open import L.Ordinal {ℓ} using ( suc-ord )
open import LJ-1-536.Probe536 {ℓ} lem using ( HierBelow )

open import Cubical.HITs.CumulativeHierarchy.Base using ( V )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet )
open InfinitySet {ℓ} using ( sucV )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ

-- NO PROOF.  NO CONVERSION.  ONE TYPE, FORMED.
Target : (α : V ℓ) (oα : IsOrd α) → Type (ℓ-suc ℓ)
Target α oα = HierBelow (sucV α) (suc-ord oα)
