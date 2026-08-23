{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.565] CONTROL e.  THE MECHANISM, WITH NO PROBE IMPORTED.
--
-- Control565d forms `HierBelow` at a successor for 1.93 s.
-- Control565c adds ONE `refl` between two spellings of that same set
-- and exhausts 11.0 GB.  So the cost is the CONVERSION and nothing
-- else.  This file asks what the conversion touches.
--
-- `hierL` is `hierAt .fst` and `hierAt` is `∈-induction`
-- (src/L/Hierarchy.lagda.md:537-538, :621-622).  A well-founded
-- recursion REDUCES when its argument's accessibility can be exposed,
-- and `sucV` is transparent, so `hierL (sucV α)` is a REDEX while
-- `hierL β` at a variable β is not.
--
-- Row 1 is the variable.  Row 2 is the successor.  Same shape, same
-- file, one difference.
--
-- ONE Agda process per run, GHCRTS="-A64m -I0 -M8g", the wide caliber.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-565.runs.Control565e {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; IsOrd )
open import L.Hierarchy {ℓ} lem using ( hierL )

open import Cubical.HITs.CumulativeHierarchy.Base using ( V )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet )
open InfinitySet {ℓ} using ( sucV )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ

-- ROW 1.  THE ARGUMENT IS A VARIABLE.  `hierL β` is stuck.
hier-var : (β : V ℓ) (hβ : ⟨ isL β ⟩) (oβ : IsOrd β)
         → hierL β hβ oβ ≡ hierL β hβ oβ
hier-var β hβ oβ = refl

-- ROW 2.  THE ARGUMENT IS A TRANSPARENT SUCCESSOR.  Same row.
hier-suc : (α : V ℓ) (h : ⟨ isL (sucV α) ⟩) (o : IsOrd (sucV α))
         → hierL (sucV α) h o ≡ hierL (sucV α) h o
hier-suc α h o = refl
