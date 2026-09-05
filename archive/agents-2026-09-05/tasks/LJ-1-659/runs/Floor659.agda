{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.659] FLOOR.  The frame alone, with the obligation's two ends
-- stated as TYPES and no proof of anything.  It prices what the
-- elaboration frame costs before any term of this task is attempted
-- (coder clause, owner 2026-08-23).
--
-- It takes [LJ-1.651]'s formula BY IMPORT, which is the honest way to
-- take a predecessor's type.  [LJ-1.650] measured that importing
-- LJ-1-595.Probe595 WALLS the wide caliber on the frame alone
-- (agents/tasks/LJ-1-650/lj-1.650-report.md:1, section 1), because that
-- probe chains through 544/550/558/564/570/578.  Probe651 imports NO
-- probe: only src/.  This file measures whether that difference holds.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-659.runs.Floor659 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ} using ( IsOrd; Lset )
open import L.BoundedSubset {ℓ} lem using ( module HullStage )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ∅; module InfinitySet )
open import Cubical.Data.Sigma using ( _×_ )
open import Cubical.Data.Vec using ( Vec; _∷_; [] )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁ )
open InfinitySet {ℓ} using ( sucV )

import LJ-1-651.Probe651
module P651 = LJ-1-651.Probe651 {ℓ} lem

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
module SV = hPropStructure 𝒮ᵥ
open SV using ( _∈ˢ_ )

module Floor (lam : SV.S) (ordλ : IsOrd lam)
             (succλ : (d : SV.S) → ⟨ d ∈ˢ lam ⟩ → ⟨ sucV d ∈ˢ lam ⟩)
             (X : SV.S)
             (X⊆Lλ : (z : SV.S) → ⟨ z ∈ˢ X ⟩ → ⟨ z ∈ˢ Lset lam ⟩)
             (∅∈λ : ⟨ ∅ ∈ˢ lam ⟩) where

  module HS = HullStage lam ordλ succλ X X⊆Lλ ∅∈λ
  module T = HS.H.T
  open T using ( Code; val; _⊨c_ )

  -- [LJ-1.651]'s module, at the SAME telescope.
  module P = P651.HullStage lam ordλ succλ X X⊆Lλ ∅∈λ

  -- THE HYPOTHESIS, AS THE PREDECESSOR DELIVERED IT.
  -- agents/tasks/LJ-1-651/Probe651.agda:141-142.
  LsetFormula : Type ℓ
  LsetFormula = Formula Code 2

  delivered : LsetFormula
  delivered = P.lset-formula

  -- THE TARGET, verbatim from agents/tasks/LJ-1-650/Probe650.agda:322-328.
  LevelFormula : Type (ℓ-suc ℓ)
  LevelFormula =
    Σ[ lv ∈ Formula Code 2 ]
      ( ((v γ : HS.ASt.SL) → ⟨ (v ∷ γ ∷ []) ⊨c lv ⟩ → fst v ≡ Lset (fst γ))
      × ((γ : HS.ASt.SL) → IsOrd (fst γ)
         → ∥ Σ[ v ∈ HS.ASt.SL ]
              ((fst v ≡ Lset (fst γ)) × ⟨ (v ∷ γ ∷ []) ⊨c lv ⟩) ∥₁) )

  -- THE OBLIGATION, AS A TYPE.  Nothing here inhabits it.
  LsetFormulaToLevel : Type (ℓ-suc ℓ)
  LsetFormulaToLevel = LsetFormula → LevelFormula
