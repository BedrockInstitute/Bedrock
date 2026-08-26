{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.672] PROBE.  The two readings of the level graph agree.
-- It runs in agents/tasks/LJ-1-672/ and lands nothing in src/.
--
--   THE OBLIGATION  same-as-graph.  SameAsGraph at the matrix
--                   [LJ-1.520] names, BOTH directions, one env.
--                   Copied from Probe520.agda:192-195.
--
--   W3              the direction from LsetGraphAt back to the
--                   Sigma-1 reading.
--
-- ONE Agda process per run, GHCRTS="-A64m -I0 -M2g", the wide caliber,
-- set on the pane by the program and untouched here.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-672.Probe672 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans )
import LJ-1-520.Probe520 {ℓ} lem as P520

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ
module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL using ( _^_ ) renaming ( _⊨ᵐ_ to _⊨_ )

-- THE TYPE THE PREDECESSOR DELIVERED.  Probe520.agda:192-195.
-- Both directions.  Neither half is inhabited there.

SameAsGraph : {n : ℕ} (w b : Fin n) (γ : S ^ n) → Type (ℓ-suc ℓ)
SameAsGraph = P520.SameAsGraph

levelFo-Σ₁ = P520.levelFo-Σ₁

-- W3, GREEN: pins holds of the twelve numerals, at Matrix, both
-- at a dummy tail (Pins) and at the thirteen-slot env (Reverse).
-- The obligation same-as-graph is NOT written.  See
-- review-of-same-as-graph.md.
import LJ-1-672.runs.W3 {ℓ} lem as W3
module Pins {n : ℕ} (γ : S ^ n) = W3.Pins {n} γ
module Reverse {n : ℕ} (w b : Fin n) (γ : S ^ n) (kk : S) = W3.Reverse w b γ kk
