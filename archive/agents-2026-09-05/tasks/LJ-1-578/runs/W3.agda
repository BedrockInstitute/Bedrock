{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.578]  W3 SLICE.  TYPE ONLY, TYPECHECKED ALONE, WRITTEN FIRST.
--
-- The brief names the widest unmeasured term as "whichever of `levelIn`
-- and `cover` [LJ-1.570] marked hardest".  IT IS `cover`, and the mark
-- is that report's own, at two places:
--   * agents/tasks/LJ-1-570/lj-1.570-report.md:85-86  `cover` asks for
--     "the SAME adequacy as `levelIn` ... plus a least-witness
--     selection in the hull".  Strictly more than `levelIn` asks.
--   * :88-90  "Unlike `levelIn` it is general at every consumer": three
--     sites, none restricting the argument, against `levelIn`'s single
--     consumer which that report weakened to successors only
--     (Probe570.agda:360-365).
-- So `levelIn` has a cheap weakening available at its only consumer and
-- `cover` has none.  `cover` is the harder of the two.
--
-- Nothing is postulated.  Nothing lands in src/.  No hole.  No inhabitant
-- is claimed here: this slice is a TYPE.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-578.runs.W3 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ} using ( IsOrd; Lset )
open import L.BoundedSubset {ℓ} lem using ( IsCardinal; _↪_ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet; _∪_; ⁅_⁆s )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫ )
open InfinitySet {ℓ} using ( ω; sucV )
import Cubical.Data.Empty as Empty

import LJ-1-550.Probe550 {ℓ} lem as P550

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
module SV = hPropStructure 𝒮ᵥ
open SV using ( _∈ˢ_ )

-- `cover`, re-ascribed at the frame `gch-from-five` calls it: the
-- seventeen-slot telescope of the bounded subset theorem, which is the
-- frame `P550.CoHyps` is stated over (Probe550.agda:215-230) and the
-- frame `P564.gch-from-five` consumes.
CoverAt : Type (ℓ-suc ℓ)
CoverAt =
    (κ : SV.S) (ordκ : IsOrd κ) (cardκ : IsCardinal κ)
    (κ∉ω : ⟨ κ ∈ˢ ω ⟩ → Empty.⊥)
    (α : SV.S) (ordα : IsOrd α) (α∈κ : ⟨ α ∈ˢ κ ⟩)
    (α∉ω : ⟨ α ∈ˢ ω ⟩ → Empty.⊥)
    (sq : P550.SqLaw α)
    (x : SV.S) (x⊆Lα : (z : SV.S) → ⟨ z ∈ˢ x ⟩ → ⟨ z ∈ˢ Lset α ⟩)
    (absorbs : ⟪ Lset α ∪ ⁅ x ⁆s ⟫ ↪ ⟪ Lset α ⟫)
    (lam : SV.S) (ordλ : IsOrd lam) (α∈λ : ⟨ α ∈ˢ lam ⟩)
    (succλ : (d : SV.S) → ⟨ d ∈ˢ lam ⟩ → ⟨ sucV d ∈ˢ lam ⟩)
    (x∈Lλ : ⟨ x ∈ˢ Lset lam ⟩)
  → P550.Tele.Cover κ ordκ cardκ κ∉ω α ordα α∈κ α∉ω sq x x⊆Lα absorbs
      lam ordλ α∈λ succλ x∈Lλ
