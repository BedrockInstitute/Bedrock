{-# OPTIONS --cubical --safe --guardedness #-}

-- LJ-1.340 GENERIC FORM.  It lands nothing.  It runs in
-- agents/tasks/LJ-1-340/.
--
-- THE QUESTION: can the predecessor extraction be written ONCE, generic in
-- the property, so that both delivered sites use it?
--
-- PART 0 is the generic form.  It is generic in the ORDINAL PROPERTY `P`,
--        which is a MODULE parameter and never a field of a record.  A law
--        of this family (C-55) says a hypothesis folded into a record
--        exhausts 8 GB where the same hypothesis is free as a module
--        parameter.
-- PART A is the L.Choice.Stage application, with the seal on top.
-- PART B is the L.Choice.Step application, with the seal on top.
--
-- ProbeControl.agda holds the two delivered arguments verbatim under the
-- same imports.  The two files differ ONLY in the argument.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-340.ProbeEmpty {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ} using ( IsOrd; isL; Lset; Lset-out; 𝒟ₒ )
open import L.Ordinal {ℓ} using ( mem-ord; suc-ord )
open import L.Ordinal.Stages {ℓ} lem using ( suc∈or≡ )
open import L.Stage {ℓ} lem
  using ( isLeastOrd; stage; stage-ord; stage-mem; stage-earliest )
open import L.Axioms.Basic {ℓ} using ( Lset-suc )
open import L.Choice.Stage {ℓ} lem
  using ( meets; Inhabited; μ; μ-ord; μ-meets; μ-earliest
        ; IsPredOf; isPropPredOf )

import Cubical.Data.Sum as Sum
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁; squash₁ )
open import Cubical.Data.Sum using ( _⊎_; inl; inr )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet )
open InfinitySet using ( sucV )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ

-- LJ-1.340 EMPTY CONTROL.  The imports of both probes and NO content.
-- Its seconds are the floor.  A content cost is a probe minus this file.
