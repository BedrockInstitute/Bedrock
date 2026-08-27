{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.702]  Row3 re-derived without the module-parameter projection.
--
-- THE OBLIGATION.  `truncated-producer` is [LJ-1.643]'s `Row3`
-- (agents/tasks/LJ-1-643/Probe643.agda:118-122).  Its inhabitant is
-- `ambientCardAbove` (src/L/CardinalAbove.lagda.md:219-221).
--
-- W3.  [LJ-1.643] needed a `module T = Sep a β oβ` projection for Row1
-- (`θ-card` is a field of `module Sep`).  Row3 is a top-level function
-- of `L.CardinalAbove`.  This file does not import `module Sep` and
-- does not project any module field.
--
-- THE FLOOR.  Measured with a hole standing in for the body
-- (runs/Floor.agda.txt, runs/floor-1.out) before this inhabitant landed.
--
-- CALIBER.  The program set GHCRTS on this pane.  I did not set it.
-- One Agda process at a time.  Nothing lands in src/.  No postulate,
-- no hole.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-702.Probe702
  {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ} using ( IsOrd )
open import L.BoundedSubset {ℓ} lem using ( IsCardinal )
open import L.CardinalAbove {ℓ} lem using ( NoInjOrd; ambientCardAbove )
open import Cubical.Data.Sigma using ( _×_ )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁ )

module SV = hPropStructure 𝒮ᵥ
open SV using ( S; _∈ˢ_ )

-- ROW 3, RE-DERIVED.  The type is Probe643.agda:118-122.  The body is
-- the tree's own producer, already applied to the module parameters
-- `{ℓ} lem` by the import.  No `module Sep`.
truncated-producer : NoInjOrd
  → (a : S) → IsOrd a
  → ∥ Σ[ θ ∈ S ] (IsOrd θ × IsCardinal θ × ⟨ a ∈ˢ θ ⟩) ∥₁
truncated-producer = ambientCardAbove
