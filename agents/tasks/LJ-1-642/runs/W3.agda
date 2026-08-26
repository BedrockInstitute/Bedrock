{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.642]  W3 SLICE.  TYPES ONLY, TYPECHECKED ALONE, WRITTEN FIRST.
--
-- The brief names the widest unmeasured term: `Det` and `Wit` at a
-- general `ψ`.  Both are [LJ-1.598]'s own types
-- (agents/tasks/LJ-1-598/Probe598.agda:209-215), restated here at the
-- index the brief RULES: `IsOrd` of the code's VALUE and never of its
-- collapse.  The question this slice puts is whether the two state at
-- the stage's inner world at all, over the hull's own code alphabet,
-- before any formula is chosen.
--
-- Nothing is postulated.  Nothing lands in src/.  No hole.  No
-- inhabitant is claimed here: this slice is TWO TYPES.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-642.runs.W3 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ} using ( IsOrd; Lset )
open import L.BoundedSubset {ℓ} lem using ( module HullStage )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet; ∅ )
open import Cubical.Data.Vec using ( _∷_; [] )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁ )
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

  -- W3, FIRST HALF.  DETERMINATION.  A two-slot formula over the hull's
  -- codes, INDEX in slot 0 and VALUE in slot 1, whose every satisfaction
  -- at an ORDINAL index pins the value to the tower there.
  Det : Formula T.Code 2 → Type (ℓ-suc ℓ)
  Det ψ = (b a : HS.ASt.SL) → IsOrd (fst b)
        → ⟨ (b ∷ a ∷ []) T.⊨c ψ ⟩ → fst a ≡ Lset (fst b)

  -- W3, SECOND HALF.  EXISTENCE.  The formula is satisfied at every
  -- ordinal of the stage's inner world.
  Wit : Formula T.Code 2 → Type (ℓ-suc ℓ)
  Wit ψ = (b : HS.ASt.SL) → IsOrd (fst b)
        → ∥ Σ[ a ∈ HS.ASt.SL ] ⟨ (b ∷ a ∷ []) T.⊨c ψ ⟩ ∥₁
