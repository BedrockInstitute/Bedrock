{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.671] FLOOR.  The frame alone, with Sound and Complete stated as
-- TYPES and no proof of either law.  It prices what the elaboration
-- frame costs before any term of this task is attempted (coder clause,
-- owner 2026-08-23).
--
-- It takes [LJ-1.651]'s formula BY IMPORT, which is the honest way to
-- take a predecessor's type.  [LJ-1.659] measured that import at 5.82 s
-- and 857,849,856 bytes (agents/tasks/LJ-1-659/lj-1.659-report.md:62-64).
-- This file re-measures the same frame, then adds the two law types.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-671.runs.Floor671 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

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

  SL : Type (ℓ-suc ℓ)
  SL = HS.ASt.SL

  module P = P651.HullStage lam ordλ succλ X X⊆Lλ ∅∈λ

  delivered : Formula Code 2
  delivered = P.lset-formula

  -- Verbatim from agents/tasks/LJ-1-659/Probe659.agda:155-161.
  Sound : Formula Code 2 → Type (ℓ-suc ℓ)
  Sound lf = (γ v : SL) → ⟨ (γ ∷ v ∷ []) ⊨c lf ⟩ → fst v ≡ Lset (fst γ)

  Complete : Formula Code 2 → Type (ℓ-suc ℓ)
  Complete lf = (γ : SL) → IsOrd (fst γ)
              → ∥ Σ[ v ∈ SL ]
                   ((fst v ≡ Lset (fst γ)) × ⟨ (γ ∷ v ∷ []) ⊨c lf ⟩) ∥₁

  -- THE OBLIGATION, AS A TYPE.  Nothing here inhabits it.
  LevelLaws : Type (ℓ-suc ℓ)
  LevelLaws = Σ[ lf ∈ Formula Code 2 ] (Sound lf × Complete lf)
