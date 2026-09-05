{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1-641]  FLOOR SLICE.  THE FRAME'S PRICE, MEASURED BEFORE ANY PROOF.
--
-- The standing coder clause orders the floor priced BEFORE the real
-- proof of a heavy object, and the imports trimmed to the facts this
-- file's own rows use.  The obligation type names exactly six things:
-- SV.S, _∈ˢ_, HS.M, IsOrd, HS.C.π and Lset.  So this slice imports
-- HullStage and NOTHING ELSE from L.BoundedSubset: no CollapseIso, no
-- HullExt, no Formula, no mapFo.  [LJ-1.602]'s frame carried all of
-- them because its clause was a SYNTAX statement; this obligation is a
-- SET-LEVEL equation and does not read a formula anywhere.
--
-- The hole is a BARE META at the named type, the shape [LJ-1.602]
-- priced green at 2.81 s (its runs/floor-2.out) after the
-- lambda-with-where shape was killed at its time-box.
--
-- Nothing is postulated.  Nothing lands in src/.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-641.runs.FLOOR {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ} using ( IsOrd; Lset )
open import L.BoundedSubset {ℓ} lem using ( module HullStage )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet; ∅ )
open InfinitySet {ℓ} using ( sucV )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
module SV = hPropStructure 𝒮ᵥ
open SV using ( _∈ˢ_ )

module Frame (lam : SV.S) (ordλ : IsOrd lam)
             (succλ : (d : SV.S) → ⟨ d ∈ˢ lam ⟩ → ⟨ sucV d ∈ˢ lam ⟩)
             (X : SV.S)
             (X⊆Lλ : (z : SV.S) → ⟨ z ∈ˢ X ⟩ → ⟨ z ∈ˢ Lset lam ⟩)
             (∅∈λ : ⟨ ∅ ∈ˢ lam ⟩) where

  module HS = HullStage lam ordλ succλ X X⊆Lλ ∅∈λ

  -- THE OBLIGATION, at a hole.  The type is the brief's, letter for
  -- letter, and it is [LJ-1.602]'s `Commute`
  -- (agents/tasks/LJ-1-602/Probe602.agda:178-182).
  commute-at-ordinal
    : (δ : SV.S) (δ∈M : ⟨ δ ∈ˢ HS.M ⟩) → IsOrd (HS.C.π δ)
    → (Lδ∈M : ⟨ Lset δ ∈ˢ HS.M ⟩)
    → HS.C.π (Lset δ) ≡ Lset (HS.C.π δ)
  commute-at-ordinal = ?
