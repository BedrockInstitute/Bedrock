{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.671]  THE PACKED VALUE SATISFIES THE DELIVERED LEVEL-HOOD FORMULA.
--
--   THE BRIEF'S OBLIGATION  sat-at-packed :
--     SatAtPacked delivered
--   where SatAtPacked is verbatim from
--   agents/tasks/LJ-1-663/Probe663.agda:135-138 and delivered is
--   [LJ-1.651]'s lset-formula, taken by import the way [LJ-1.663]
--   took it (Probe663.agda:42-43).  The formula is the arity-2
--   bounded level-hood matrix of the condensation chapter, with all
--   twelve row-tag slots, the bound slot and the two term slots
--   collapsed onto slot zero (dev/glossary.toml row-tokens, the
--   zero instantiation of BoundedSubset's LevelHood0).
--
--   THE STATEMENT:  the packed value, Lset(gamma) as a member of the
--   stage Lset(lam), satisfies the formula at the ordinal gamma.  This
--   is the membership-side half of [LJ-1.659]'s Complete law, and the
--   stop of [LJ-1.663] names it the obligation (Section 7).  The
--   witnesses of the bounded matrix are set-sized and live in the
--   stage (dev/LESSONS.md, the Devlin 2.6(ii) direction of the
--   construction): the bound K is a stage set above Lset(gamma), and
--   the graph witness is the level sequence itself.
--
--   ATTEMPT STATE:  the structural skeleton (K, u, the two truncated
--   ex existentials) is built; the residue is the full satisfaction of
--   the renamed matrix, satU.  The deep witness attempt atk-3 (runs/
--   atk-3.out) capped at 1200 s on one frame step; the red version of
--   this file is preserved as ATK-1-red.agda.txt.  NO-GO: see
--   review-of-sat-at-packed.md.
--
--   This file is a probe.  Nothing here lands in src/.  The report is
--   lj-1.671-report.md, written as the file grows.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-671.runs.ATK-1 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

  open import FOL.ZFStructure using ( module hPropStructure )
  open import FOL.Syntax using ( Formula )
  open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
  open import L.Constructible {ℓ} using ( IsOrd; Lset )
  open import L.BoundedSubset {ℓ} lem using ( module HullStage )
  open import Cubical.HITs.CumulativeHierarchy.Constructions
    using ( ∅; module InfinitySet )
  open import Cubical.Data.Vec using ( _∷_; [] )
  import Cubical.HITs.PropositionalTruncation as PT
  open PT using ( ∥_∥₁; ∣_∣₁ )
  open InfinitySet {ℓ} using ( sucV )

  import LJ-1-663.Probe663
  module P663 = LJ-1-663.Probe663 {ℓ} lem

  open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
  module SV = hPropStructure 𝒮ᵥ
  open SV using ( _∈ˢ_ )

  module Level (lam : SV.S) (ordλ : IsOrd lam)
               (succλ : (d : SV.S) → ⟨ d ∈ˢ lam ⟩ → ⟨ sucV d ∈ˢ lam ⟩)
               (X : SV.S)
               (X⊆Lλ : (z : SV.S) → ⟨ z ∈ˢ X ⟩ → ⟨ z ∈ˢ Lset lam ⟩)
               (∅∈λ : ⟨ ∅ ∈ˢ lam ⟩) where

    module L663 = P663.Level663 lam ordλ succλ X X⊆Lλ ∅∈λ
    open L663 using ( SL; delivered; packed )
    open L663.T using ( Code; _⊨c_ )

    -- Verbatim from agents/tasks/LJ-1-663/Probe663.agda:135-138.
    SatAtPacked : Formula Code 2 → Type (ℓ-suc ℓ)
    SatAtPacked lf =
      (γ : SL) (oγ : IsOrd (fst γ))
      → ⟨ (γ ∷ packed γ oγ ∷ []) ⊨c lf ⟩

    -- The obligation, named.  The term itself is NOT built:
    -- NO-GO, see review-of-sat-at-packed.md.  The deepest green
    -- skeleton reached by this attempt was the structural stub
    -- (K, u, the two truncated ex existentials); the residue is the
    -- full satisfaction of the renamed matrix (runs/atk-2.out
    -- prints the goal type), and the deep witness attempt atk-3
    -- capped at 1200 s on one frame step.  The red file is preserved
    -- as ATK-1-red.agda.txt.
    sat-at-packed : Type (ℓ-suc ℓ)
    sat-at-packed = SatAtPacked delivered
