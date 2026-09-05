{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.527] PROBE.  ROW TWO of the six-row chain [LJ-1.525] laid out:
-- the bounded body `StepB.bodyB` becomes the machine's own `StepBody`.
-- It runs in agents/tasks/LJ-1-527/ and lands nothing in src/.
--
--   W3, FIRST      the index match, written alone in runs/W3.agda and
--                  typechecked before this file existed.  `sh4` IS
--                  suc⁴, at both slots.  THEY MEET.
--   REBUILT        row one, [LJ-1.525]'s `leaf-unbounds`, at its
--                  delivered type (agents/tasks/LJ-1-525/Probe525.agda
--                  :150-165).  The brief orders a rebuild and not an
--                  import, so nothing of [LJ-1.525] is imported here.
--                  Its five hypotheses ride into the conclusion of the
--                  obligation, undischarged and unhidden.
--   DELIVERED      body-unbounds, the briefed obligation.
--
-- WHAT IS IMPORTED FROM A PREDECESSOR: `defPow-closed-noCode` and
-- `IsLimit` from [LJ-1.522], which is what row one is BUILT FROM and
-- not row one itself.  Rebuilding that too would rebuild the whole leg.
--
-- ONE Agda process per run, GHCRTS="-A64m -I0 -M8g", the wide caliber,
-- set on the pane by the program and untouched here.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-527.runs.Control527 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula; var; _∈̇_; _∧̇_; ∃̇_; ∃̇∈ )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans; Lset )
open import L.Coding.Model {ℓ} using ( extAt; appAt )
open import L.Coding.Powerset {ℓ} lem using ( DefBody; DefAt )
open import L.Coding.Sequence {ℓ} lem using ( StepBody )
open import L.Condensation {ℓ} lem
  using ( extAtB; extAtB→extAt; module StepB )

open import LJ-1-522.Probe522 {ℓ} lem using ( IsLimit; defPow-closed-noCode )

open import Cubical.Data.Nat using ( _+_ )
open import Cubical.Data.Vec using ( lookup; _∷_ )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL using ( _^_ ) renaming ( _⊨ᵐ_ to _⊨_ )
