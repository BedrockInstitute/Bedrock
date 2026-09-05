{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.614]  W3 SLICE.  TYPE ONLY, TYPECHECKED ALONE, WRITTEN FIRST.
--
-- The brief names the widest unmeasured term: "the crossing's demand on
-- G+", re-ascribed against `GraphStageAt`.  The crossing's G+ demand is
-- [LJ-1.606]'s `Crossing` (agents/tasks/LJ-1-606/Probe606.agda:178-180),
-- whose second component is `GraphStage ψ` at `:156-159`, and whose only
-- USE of that component is leg 1 of `inner-to-ambient`
-- (agents/tasks/LJ-1-606/Probe606.agda:226-227): at every hull
-- level-pair (q, gamma), the STAGE's inner world satisfies the Sigma-one
-- closure `∃̇` of the RELABELLED hull matrix `mapFo DR.inL (∃̇ ψ)` at the
-- `inL`-image of the pair.
--
-- RE-ASCRIPTED against `GraphStageAt`
-- (agents/tasks/LJ-1-610/Probe610.agda:231-233, imported, not restated):
-- the same pairs, the same reading, the matrix at the STAGE carrier.
-- This is the type below.  Whether the restated face MEETS it is a
-- question about a term, and it is answered in the probe
-- (`slot-accepts`, one line, definitional): W3 prices the DEMAND.
--
-- Nothing is postulated.  Nothing lands in src/.  No hole.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-614.runs.W3 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula; ∃̇_ )
open import FOL.Manipulation.Relabelling using ( mapFo )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ} using ( IsOrd; Lset )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet; ∅ )
open InfinitySet {ℓ} using ( sucV )
open import Cubical.Data.Vec using ( map; _∷_; [] )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
module SV = hPropStructure 𝒮ᵥ
open SV using ( _∈ˢ_ )

import LJ-1-610.Probe610
module P610 = LJ-1-610.Probe610 lem

module Slot (lam : SV.S) (ordλ : IsOrd lam)
            (succλ : (d : SV.S) → ⟨ d ∈ˢ lam ⟩ → ⟨ sucV d ∈ˢ lam ⟩)
            (X : SV.S)
            (X⊆Lλ : (z : SV.S) → ⟨ z ∈ˢ X ⟩ → ⟨ z ∈ˢ Lset lam ⟩)
            (∅∈λ : ⟨ ∅ ∈ˢ lam ⟩) where

  module R = P610.Frame lam ordλ succλ X X⊆Lλ ∅∈λ

  -- THE CROSSING'S G+ SLOT, RE-ASCRIPTED AGAINST GraphStageAt, TYPE
  -- ONLY.  Leg 1's demand (Probe606.agda:226-227) with the matrix at
  -- the stage carrier `R.DR.ASt.SL`: the stage's inner satisfaction of
  -- the Sigma-one closure, at the `inL`-image of every hull level-pair.
  SlotAt : Formula R.DR.ASt.SL 3 → Type (ℓ-suc ℓ)
  SlotAt χ =
    (q γ : R.DR.SM) → fst q ≡ Lset (fst γ)
    → ⟨ map R.DR.inL (q ∷ γ ∷ []) R.DR.ASt.AbsL.⊨ᵐ (∃̇ χ) ⟩
