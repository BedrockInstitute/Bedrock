{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.650] FLOOR, SECOND SHAPE.  The first shape imported
-- LJ-1-595.Probe595 and WALLED on the frame alone
-- (runs/FLOOR-IMPORT595.agda.txt, runs/floor-1.out, exit 251 at
-- 1,911,226,368 bytes against the 2,147,483,648-byte wide cap).  This
-- shape imports src/ only and restates the two predecessor types
-- verbatim, each cited at the line it was read.
--
-- ONE Agda process, caliber from the pane, never set here.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-650.runs.Floor650 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ} using ( IsOrd; Lset )
open import L.BoundedSubset {ℓ} lem using ( module HullStage )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ∅; module InfinitySet )
open import Cubical.Data.Sigma using ( _×_ )
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

  -- agents/tasks/LJ-1-462/Probe462.agda:118-121, verbatim
  LsetCodeOrd : Type (ℓ-suc ℓ)
  LsetCodeOrd =
    (c : T.Code) → IsOrd (fst (T.val c))
    → Σ[ d ∈ T.Code ] (fst (T.val d) ≡ Lset (fst (T.val c)))

  -- agents/tasks/LJ-1-595/Probe595.agda:353-357, verbatim
  CodedCover : Type (ℓ-suc ℓ)
  CodedCover = (c : T.Code)
             → Σ[ d ∈ T.Code ]
                 ( IsOrd (fst (T.val d))
                 × ⟨ fst (T.val c) ∈ˢ Lset (fst (T.val d)) ⟩ )

  -- THE OBLIGATION'S TYPE, and nothing of its proof.
  CodedCoverFromKeystone : Type (ℓ-suc ℓ)
  CodedCoverFromKeystone = LsetCodeOrd → CodedCover
