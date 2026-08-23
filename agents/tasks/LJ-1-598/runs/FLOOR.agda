{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.598]  FLOOR SLICE.  D-10, BEFORE ANY PROOF.
--
-- `defines-level` is stated at [LJ-1.578]'s own clause (i), taken and
-- not restated, with a HOLE standing in for the term.  The point is the
-- price of the FRAME: the time and peak RSS the import chain and the
-- statement itself cost, before any mathematics is attempted.
--
-- This slice is RED BY DESIGN (one interaction hole).  Nothing is
-- postulated.  Nothing lands in src/.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-598.runs.FLOOR {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ} using ( IsOrd; Lset )
open import L.BoundedSubset {ℓ} lem using ( module HullStage )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet; ∅ )
open import Cubical.Data.Sigma using ( _×_ )
open InfinitySet {ℓ} using ( sucV )

import LJ-1-578.Probe578 {ℓ} lem as P578

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
module SV = hPropStructure 𝒮ᵥ
open SV using ( _∈ˢ_ )

defines-level : (lam : SV.S) (ordλ : IsOrd lam)
  (succλ : (d : SV.S) → ⟨ d ∈ˢ lam ⟩ → ⟨ sucV d ∈ˢ lam ⟩)
  (X : SV.S)
  (X⊆Lλ : (z : SV.S) → ⟨ z ∈ˢ X ⟩ → ⟨ z ∈ˢ Lset lam ⟩)
  (∅∈λ : ⟨ ∅ ∈ˢ lam ⟩)
  → P578.Cert.DefinesLevel lam ordλ succλ X X⊆Lλ ∅∈λ
defines-level lam ordλ succλ X X⊆Lλ ∅∈λ = {! !}
