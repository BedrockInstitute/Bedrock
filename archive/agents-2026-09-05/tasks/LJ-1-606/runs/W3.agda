{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.606]  W3 SLICE.  TYPE ONLY, TYPECHECKED ALONE, WRITTEN FIRST.
--
-- The brief names the widest unmeasured term: "LJ-1.602's section 3
-- commute, restated alone, TYPE ONLY, capped".  The type below is
-- [LJ-1.602]'s `Commute` letter for letter
-- (agents/tasks/LJ-1-602/Probe602.agda:178-181), which that task
-- measured EQUIVALENT, exactly, to clause (iii) of the level-hood
-- certificate at the clause's own hypotheses
-- (agents/tasks/LJ-1-602/Probe602.agda:189-219): the collapse of the
-- hull's level at delta IS the tower's level at the collapsed index.
-- No formula is chosen and no inhabitant is claimed: this slice is a
-- TYPE.
--
-- Nothing is postulated.  Nothing lands in src/.  No hole.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-606.runs.W3 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

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

  -- THE CROSSING, TYPE ONLY.  This is what clause (iii) needs
  -- ([LJ-1.602], section 3, both directions of the equivalence).
  Commute : Type (ℓ-suc ℓ)
  Commute =
    (δ : SV.S) (δ∈M : ⟨ δ ∈ˢ HS.M ⟩) → IsOrd (HS.C.π δ)
    → (Lδ∈M : ⟨ Lset δ ∈ˢ HS.M ⟩)
    → HS.C.π (Lset δ) ≡ Lset (HS.C.π δ)
