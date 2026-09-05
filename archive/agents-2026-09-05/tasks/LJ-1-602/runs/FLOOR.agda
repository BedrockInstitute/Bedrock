{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1-602]  FLOOR SLICE.  THE FRAME'S PRICE, MEASURED BEFORE ANY PROOF.
--
-- The brief orders the floor first and peak RSS reported: on this clause
-- the heap is the risk and not the deadline.  The import of [LJ-1.578]'s
-- own file walls under the standing wide cap with warm dependencies
-- ([LJ-1.598], runs/chain-578.out, exit 251 at 15.92 s), so this slice
-- follows that task's RESTRUCTURE: src/-only imports, the frame, and
-- clause (iii) restated text for text, with a HOLE standing in for the
-- obligation term.  The number this slice measures is what the FRAME
-- costs; the hole is the obligation's own price and is red by design.
--
-- Nothing is postulated.  Nothing lands in src/.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-602.runs.FLOOR {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula )
open import FOL.Manipulation.Relabelling using ( mapFo )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ} using ( IsOrd; Lset )
open import L.BoundedSubset {ℓ} lem
  using ( module HullStage; module HullExt; module CollapseIso )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet; ∅ )
open import Cubical.Data.Sigma using ( _×_ )
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
  module HE = HullExt lam ordλ X X⊆Lλ ∅∈λ
  module CI = CollapseIso HS.M HE.hullExt

  -- Clause (iii), restated text for text from
  -- agents/tasks/LJ-1-578/Probe578.agda:503-510.
  DefinesLevelAcross : Type (ℓ-suc ℓ)
  DefinesLevelAcross =
    (δ : SV.S) (δ∈M : ⟨ δ ∈ˢ HS.M ⟩) → IsOrd (HS.C.π δ)
    → (Lδ∈M : ⟨ Lset δ ∈ˢ HS.M ⟩)
    → Σ[ φ ∈ Formula CI.I.SM 1 ]
        ( ⟨ ((Lset δ , Lδ∈M) ∷ []) CI.I.⊨ᵐ φ ⟩
        × ((b : CI.I.SPM) → ⟨ (b ∷ []) CI.I.⊨ᵖᵐ mapFo CI.I.g φ ⟩
           → fst b ≡ Lset (HS.C.π δ)) )

  -- THE OBLIGATION, AT A HOLE.  Red by design; the frame's floor is
  -- what the run measures.  A bare meta at the named type, the shape
  -- [LJ-1.598]'s floor slice used (its runs/FLOOR2.agda:60-61); the
  -- first attempt put the hole under a lambda with a where-definition
  -- and was killed at the 200 s time-box with no Agda exit
  -- (runs/floor-1.out, no EXIT line), so that shape is not measured
  -- and is not priced.
  defines-level-across : DefinesLevelAcross
  defines-level-across = ?
