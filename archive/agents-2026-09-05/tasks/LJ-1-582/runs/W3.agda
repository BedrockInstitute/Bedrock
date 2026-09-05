{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.582]  W3 SLICE.  TYPE ONLY, TYPECHECKED ALONE, WRITTEN FIRST.
--
-- The brief names the widest unmeasured term:  "It is uniqueness, not
-- existence.  `Lset δ is the ONLY witness`, stated alone at the inner
-- world, TYPE ONLY."  (agents/tasks/LJ-1-582/LJ-1.582.md, section
-- `## W3, THE WIDEST UNMEASURED TERM`.)
--
-- This slice states it and NOTHING else.  No inhabitant is claimed, no
-- existence half is written, and no formula is chosen.  If uniqueness
-- would not even STATE, the brief ordered me to say so before spending
-- the estimate.
--
-- Nothing is postulated.  Nothing lands in src/.  No hole.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-582.runs.W3 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ} using ( IsOrd; Lset )
open import L.BoundedSubset {ℓ} lem using ( module HullStage )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet; ∅ )
open InfinitySet {ℓ} using ( sucV )
open import Cubical.Data.Sigma using ( _×_ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
module SV = hPropStructure 𝒮ᵥ
open SV using ( _∈ˢ_ )

-- The six slots [LJ-1.570] cut `CoHyps` down to (Probe570.agda:168-176),
-- which is the frame `Cert` is stated over (Probe578.agda:220-225).
module Uniq (lam : SV.S) (ordλ : IsOrd lam)
            (succλ : (d : SV.S) → ⟨ d ∈ˢ lam ⟩ → ⟨ sucV d ∈ˢ lam ⟩)
            (X : SV.S)
            (X⊆Lλ : (z : SV.S) → ⟨ z ∈ˢ X ⟩ → ⟨ z ∈ˢ Lset lam ⟩)
            (∅∈λ : ⟨ ∅ ∈ˢ lam ⟩) where

  module HS = HullStage lam ordλ succλ X X⊆Lλ ∅∈λ
  module T = HS.H.T

  -- "Lset δ is the ONLY witness", for ONE formula, at the STAGE's inner
  -- world.  This is the second component of the pair at
  -- Probe578.agda:238-240 and nothing else: no satisfiability, no
  -- ordinal side condition, no choice of formula.
  OnlyWitness : (c : T.Code) (φ : Formula T.Code 1) → Type (ℓ-suc ℓ)
  OnlyWitness c φ =
    (a : HS.ASt.SL) → ⟨ (a ∷ []) T.⊨c φ ⟩ → fst a ≡ Lset (fst (T.val c))

  -- And the half of clause (i) that asks for a formula which HAS it.
  -- Compare Probe578.agda:234-240: this is that type with the
  -- satisfiability conjunct deleted.
  UniqueDefiner : Type (ℓ-suc ℓ)
  UniqueDefiner =
    (c : T.Code) → IsOrd (HS.C.π (fst (T.val c)))
    → Σ[ φ ∈ Formula T.Code 1 ] OnlyWitness c φ
