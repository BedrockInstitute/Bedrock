{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.607]  RUN, NOT A DELIVERABLE ROW.  The direct untruncation of
-- the band's payload, by propositional-truncation elimination alone.
-- This file EXISTS TO BE REFUSED: the elaborator's own demand for
-- `isProp (sq δ)` is the measurement, and the refusal text is the
-- evidence.  No postulate, no hole-filling: the term below is written
-- the only way the direct route can write it, and the checker answers.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Constructions using ( module InfinitySet )
open import L.Constructible using ( IsOrd )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁ )

module LJ-1-607.runs.DirectRefused {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) (α₀ : V ℓ) (oα₀ : IsOrd α₀) where

  open import FOL.ZFStructure using ( module hPropStructure )
  open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
  open hPropStructure 𝒮ᵥ using ( S; _∈ˢ_ )
  open InfinitySet {ℓ} using ( sucV; ω )
  open import L.Ordinal.SquareLaw {ℓ} lem using ( sq )

  -- The direct route, as the checker sees it.  `PT.rec` demands an
  -- `isProp (sq δ)` first.  The only candidate the route can write is
  -- the trivial one, and it does not check.
  direct : (δ : V ℓ) → ∥ sq δ ∥₁ → sq δ
  direct δ = PT.rec (λ p q → refl)
