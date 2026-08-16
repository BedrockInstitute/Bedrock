{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.381] floor.  The empty-file floor (C-53): the same imports
-- as ProbeLJ1381A.agda, an empty body.  Run beside every seconds
-- figure.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

open import FOL.ZFStructure using ( module hPropStructure; _↾_ )
open import FOL.Syntax using
  ( Formula; Term; var; con; _∈̇_; _≐_; _∧̇_; _∨̇_; _⇒̇_; ¬̇_; ⊤̇; ⊥̇
  ; ∃̇_; ∀̇_; ∃̇∈; ∀̇∈ )
import FOL.Absoluteness
open import FOL.Manipulation.Renaming using ( renameFo; renameTm; liftρ )
open import FOL.Manipulation.Relabelling using ( mapFo; mapTm; embed )
open import FOL.Manipulation.Parameters using ( countFo )
import FOL.Count
open import Cubical.HITs.CumulativeHierarchy.Base using ( V )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ⁅_,_⁆ ) renaming ( module InfinitySet to Inf )
open import Cubical.Data.Unit using ( tt* )
open import Cubical.Data.Nat using ( ℕ; zero; suc; _+_ )
open import Cubical.Data.Vec using ( Vec; lookup; _∷_; []; _++_ )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; squash₁; ∥_∥₁ )

module LJ-1-381.Floor381 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ} using ( 𝒟ₒ; 𝒮ʟ )
open Inf using ( #_; sucV )

import LJ-1-184.ProbeLJ1184A {ℓ} as P184
import LJ-1-297.ProbeLJ1297A {ℓ} lem as P1297A
import LJ-1-297.ProbeLJ1297C {ℓ} as P1297C
import LJ-1-238.GenSequence
import LJ-1-304.ProbeLJ1304A {ℓ} lem as P1304
open import L.Condensation {ℓ} lem using ( DefBodyB )

dummy : ℕ
dummy = zero
