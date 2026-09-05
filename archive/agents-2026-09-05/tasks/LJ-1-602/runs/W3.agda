{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1-602]  W3 SLICE.  TYPE ONLY, TYPECHECKED ALONE, WRITTEN FIRST.
--
-- The brief names the widest unmeasured term: "the formula read in the
-- collapse", clause (iii)'s reading stated ALONE in the collapse, TYPE
-- ONLY, capped at two minutes.  The type below is clause (iii)'s own
-- second conjunct (agents/tasks/LJ-1-578/Probe578.agda:508-510), with
-- the satisfaction conjunct removed: at an index of the hull whose
-- collapse is an ordinal and whose level the hull names, SOME one-free-
-- variable formula over the hull's own constants has the property that
-- EVERY satisfaction of its collapse reading pins the TOWER's level at
-- the collapsed index.  No formula is chosen and no inhabitant is
-- claimed: this slice is a TYPE.
--
-- Nothing is postulated.  Nothing lands in src/.  No hole.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-602.runs.W3 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

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

  -- W3.  Clause (iii)'s collapse reading, ALONE.
  OnlyAcross : Type (ℓ-suc ℓ)
  OnlyAcross =
    (δ : SV.S) (δ∈M : ⟨ δ ∈ˢ HS.M ⟩) → IsOrd (HS.C.π δ)
    → (Lδ∈M : ⟨ Lset δ ∈ˢ HS.M ⟩)
    → Σ[ φ ∈ Formula CI.I.SM 1 ]
        ((b : CI.I.SPM) → ⟨ (b ∷ []) CI.I.⊨ᵖᵐ mapFo CI.I.g φ ⟩
         → fst b ≡ Lset (HS.C.π δ))
