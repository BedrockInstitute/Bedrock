{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.536] CONTROL e.  THE SMALLEST ROW THAT COULD WALL.
--
-- runs/ctld-0 exhausted 8 GB with three rows in it.  This file keeps
-- ONE, and it mentions no hierarchy, no sequence and no ordinal: only
-- that three successors above a successor are four successors.
--
-- ONE Agda process per run, GHCRTS="-A64m -I0 -M8g", the wide caliber.

open import Base.Prelude
open import Base.Truth

module LJ-1-536.runs.Control536e {ℓ : Level} where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ} using ( 𝒮ʟ; Lset )

open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet )
open InfinitySet {ℓ} using ( sucV )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ

step : ℕ → V ℓ → V ℓ
step zero    γ = γ
step (suc n) γ = sucV (step n γ)

step-conv : (α x : V ℓ) → ⟨ x ∈ Lset (step 4 α) ⟩ → ⟨ x ∈ Lset (step 3 (sucV α)) ⟩
step-conv α x p = p
