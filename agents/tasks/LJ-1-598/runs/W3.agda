{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.598]  W3 SLICE.  TYPE ONLY, TYPECHECKED ALONE, WRITTEN FIRST.
--
-- The brief names the widest unmeasured term: uniqueness, not existence.
-- "Lset δ is the ONLY witness", stated alone at the stage's inner world,
-- TYPE ONLY.  The question it puts is whether the uniqueness half of
-- clause (i) states at the inner world at all, at every code, before any
-- formula is chosen.
--
-- The type below is clause (i)'s own second conjunct
-- (agents/tasks/LJ-1-578/Probe578.agda:239-240), with the existence
-- conjunct removed.  No side condition on the code is kept: the
-- hypothesis `IsOrd (HS.C.π (fst (T.val c)))` belongs to the EXISTENCE
-- problem and uniqueness is asked at every code outright.
--
-- Nothing is postulated.  Nothing lands in src/.  No hole.  No
-- inhabitant is claimed here: this slice is a TYPE.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-598.runs.W3 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ} using ( IsOrd; Lset )
open import L.BoundedSubset {ℓ} lem using ( module HullStage )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet; ∅ )
open import Cubical.Data.Sigma using ( _×_ )
open import FOL.Syntax using ( Formula )
open import Cubical.Data.Vec using ( _∷_; [] )
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
  module T = HS.H.T

  -- W3.  "Lset δ is the ONLY witness of some formula", uniqueness alone,
  -- at the stage's inner world, over the hull's own code alphabet.
  OnlyLevel : Type (ℓ-suc ℓ)
  OnlyLevel =
    (c : T.Code)
    → Σ[ φ ∈ Formula T.Code 1 ]
        ((a : HS.ASt.SL) → ⟨ (a ∷ []) T.⊨c φ ⟩
         → fst a ≡ Lset (fst (T.val c)))
