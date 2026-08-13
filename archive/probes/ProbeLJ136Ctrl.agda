{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.36] CONTROL: the module-load cone for ProbeLJ136, with no
-- content at all.  Its cold seconds are the floor that every figure in
-- the report sits on top of.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module ProbeLJ136Ctrl {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax
  using ( Formula; var; _∈̇_; _∧̇_; _⇒̇_; ∃̇_; ∀̇_ )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Coding {ℓ} using ( pr )
open import L.Constructible {ℓ}
  using ( 𝒮ʟ; isL; isL-trans; 𝒟ₒ )
open import L.Coding.Model {ℓ}
  using ( memClauseAt; eqClauseAt; andClauseAt; orClauseAt; impClauseAt
        ; negClauseAt; topClauseAt; botClauseAt; existClauseAt; forallClauseAt
        ; allInClauseAt; exInClauseAt
        ; negClause-out; impClause-out; topClause-out; botClause-out )
open import L.Coding.Powerset {ℓ} lem
  using ( DefBody; DefAt-out; codeAt-out )
open import L.Coding.CodeSet {ℓ} lem using ( keyS )
open import L.Coding.Graph {ℓ} lem
  using ( GraphWitAt; graphAt-out; twelveAt )
open import L.Coding.Sequence {ℓ} lem
  using ( StepAt; StepAt-out; StepOf; PowOK; StepBody )
open import Cubical.Data.Nat using ( _+_ )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Constructions using ( module InfinitySet )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫ )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁; squash₁ )
open InfinitySet using ( #_ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL using ( _^_ ) renaming ( _⊨ᵐ_ to _⊨_ )
