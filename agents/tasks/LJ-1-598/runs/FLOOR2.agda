{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1-598]  FLOOR SLICE, RESTRUCTURED.  D-10, THE SECOND MEASUREMENT.
--
-- The first floor slice (runs/FLOOR.agda) took clause (i) by import and
-- walled inside the import chain (runs/floor-1.out, exit 251).  The
-- restructure drops every probe import, so the smallest import set that
-- holds the obligation is this one: src/ and nothing else, the frame,
-- the restated clause, and the obligation stated with a HOLE standing
-- in for the term.
--
-- This slice is RED BY DESIGN (one interaction hole).  Nothing is
-- postulated.  Nothing lands in src/.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-598.runs.FLOOR2 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula; con; var; _≐_; _∧̇_; ∃̇_ )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ} using ( IsOrd; Lset )
open import L.BoundedSubset {ℓ} lem using ( module HullStage )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet; ∅ )
open import Cubical.Data.Sigma using ( _×_ )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁; ∣_∣₁ )
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

  ClauseI : Type (ℓ-suc ℓ)
  ClauseI =
    (c : T.Code) → IsOrd (HS.C.π (fst (T.val c)))
    → Σ[ φ ∈ Formula T.Code 1 ]
        ( ∥ Σ[ a ∈ HS.ASt.SL ] ⟨ (a ∷ []) T.⊨c φ ⟩ ∥₁
        × ((a : HS.ASt.SL) → ⟨ (a ∷ []) T.⊨c φ ⟩
           → fst a ≡ Lset (fst (T.val c))) )

defines-level : (lam : SV.S) (ordλ : IsOrd lam)
  (succλ : (d : SV.S) → ⟨ d ∈ˢ lam ⟩ → ⟨ sucV d ∈ˢ lam ⟩)
  (X : SV.S)
  (X⊆Lλ : (z : SV.S) → ⟨ z ∈ˢ X ⟩ → ⟨ z ∈ˢ Lset lam ⟩)
  (∅∈λ : ⟨ ∅ ∈ˢ lam ⟩)
  → Frame.ClauseI lam ordλ succλ X X⊆Lλ ∅∈λ
defines-level lam ordλ succλ X X⊆Lλ ∅∈λ = {! !}
