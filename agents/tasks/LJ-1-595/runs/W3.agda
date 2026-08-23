{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.595]  W3 SLICE.  TYPE ONLY, TYPECHECKED ALONE, WRITTEN FIRST.
--
-- The brief names the widest unmeasured term as "the covering ordinal
-- itself": "the covering ordinal of a hull member, at the stage's inner
-- world, TYPE ONLY".  The question it puts is whether that object can
-- be STATED at the inner world at all.  If it cannot, clause (ii) is
-- about a different object than clause (i) and the estimate is void.
--
-- The type below is the conjunction of clause (ii)'s own adequacy
-- (agents/tasks/LJ-1-578/Probe578.agda:249-251), with the FORMULA
-- removed and the witness existentially bound.  That is exactly "the
-- covering ordinal", stripped of the demand that a formula select it.
--
-- Nothing is postulated.  Nothing lands in src/.  No hole.  No
-- inhabitant is claimed here: this slice is a TYPE.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-595.runs.W3 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ} using ( IsOrd; Lset )
open import L.BoundedSubset {ℓ} lem using ( module HullStage )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet; ∅ )
open import Cubical.Data.Sigma using ( _×_ )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁ )
open InfinitySet {ℓ} using ( sucV )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
module SV = hPropStructure 𝒮ᵥ
open SV using ( _∈ˢ_ )

module Cover (lam : SV.S) (ordλ : IsOrd lam)
             (succλ : (d : SV.S) → ⟨ d ∈ˢ lam ⟩ → ⟨ sucV d ∈ˢ lam ⟩)
             (X : SV.S)
             (X⊆Lλ : (z : SV.S) → ⟨ z ∈ˢ X ⟩ → ⟨ z ∈ˢ Lset lam ⟩)
             (∅∈λ : ⟨ ∅ ∈ˢ lam ⟩) where

  module HS = HullStage lam ordλ succλ X X⊆Lλ ∅∈λ
  module T = HS.H.T

  -- the covering ordinal of a hull member, at the stage's inner world,
  -- TYPE ONLY
  CoveringOrdinal : Type (ℓ-suc ℓ)
  CoveringOrdinal =
    (c : T.Code)
    → ∥ Σ[ a ∈ HS.ASt.SL ]
        ( IsOrd (HS.C.π (fst a))
        × ⟨ fst (T.val c) ∈ˢ Lset (fst a) ⟩ ) ∥₁
