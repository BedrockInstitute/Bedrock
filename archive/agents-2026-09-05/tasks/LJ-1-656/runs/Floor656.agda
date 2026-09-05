{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.656] FLOOR.  The frame, the obligation's TYPE restated verbatim
-- from the probe that typechecked it, and TWO measurements that decide
-- the route before any proof is attempted.
--
--   src/ ONLY.  [LJ-1.650] measured that importing a predecessor probe
--   two or more links down the LJ chain EXHAUSTS the wide caliber on
--   the frame alone (agents/tasks/LJ-1-650/lj-1.650-report.md:63-73).
--
-- ONE Agda process, caliber from the pane, never set here.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-656.runs.Floor656 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula )
open import FOL.Manipulation.Parameters using ( countFo )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ} using ( IsOrd; Lset; 𝒮ʟ )
open import L.Coding.Sequence {ℓ} lem using ( LsetGraphAt )
open import L.BoundedSubset {ℓ} lem using ( module HullStage )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ∅; module InfinitySet )
open import Cubical.Data.Sigma using ( _×_ )
open import Cubical.Data.Vec using ( _∷_; [] )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁ )
open InfinitySet {ℓ} using ( sucV )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
module SV = hPropStructure 𝒮ᵥ
module CS = hPropStructure 𝒮ʟ
open SV using ( _∈ˢ_ )

-- MEASUREMENT 1 IS NOT IN THIS FILE, BECAUSE IT CANNOT TYPECHECK.  It
-- is runs/COUNT-GRAPH.agda.txt and its run is runs/floor-1.out: the
-- DELIVERED, UNBOUNDED graph formula CARRIES CONSTANTS, so it does not
-- erase to a parameter-free formula and does not embed into `Code`.
-- The brief ordered a file that cannot typecheck to be named
-- `.agda.txt`, and that is where it is.

module Frame (lam : SV.S) (ordλ : IsOrd lam)
             (succλ : (d : SV.S) → ⟨ d ∈ˢ lam ⟩ → ⟨ sucV d ∈ˢ lam ⟩)
             (X : SV.S)
             (X⊆Lλ : (z : SV.S) → ⟨ z ∈ˢ X ⟩ → ⟨ z ∈ˢ Lset lam ⟩)
             (∅∈λ : ⟨ ∅ ∈ˢ lam ⟩) where

  module HS = HullStage lam ordλ succλ X X⊆Lλ ∅∈λ
  module T = HS.H.T
  open T using ( Code; val; _⊨c_ )

  -- agents/tasks/LJ-1-650/Probe650.agda:322-328, verbatim.
  LevelFormula : Type (ℓ-suc ℓ)
  LevelFormula =
    Σ[ lv ∈ Formula Code 2 ]
      ( ((v γ : HS.ASt.SL) → ⟨ (v ∷ γ ∷ []) ⊨c lv ⟩ → fst v ≡ Lset (fst γ))
      × ((γ : HS.ASt.SL) → IsOrd (fst γ)
         → ∥ Σ[ v ∈ HS.ASt.SL ]
              ((fst v ≡ Lset (fst γ)) × ⟨ (v ∷ γ ∷ []) ⊨c lv ⟩) ∥₁) )
