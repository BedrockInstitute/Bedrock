{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.378] THE EMPTY-FILE FLOOR (C-53).  The same imports and the
-- same module header as `ProbeLJ1378A.agda`, with no body.  Its
-- seconds are the floor beneath any figure the probe reports: what
-- loading the scaffold alone costs.
--
-- ONE agda process under GHCRTS="-A64m -I0 -M8g".

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

open import FOL.ZFStructure using ( module hPropStructure; Transitive; _↾_ )
open import FOL.Syntax using
  ( Formula; var; _∈̇_; _∧̇_; _≐_; ∃̇_; ∃̇∈ )
open import FOL.Manipulation.Relabelling using ( embed )
import FOL.Absoluteness
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ⁅_,_⁆ ) renaming ( module InfinitySet to Inf )
open import Cubical.Data.Unit using ( tt*; isPropUnit* )
open import Cubical.Data.Nat using ( _+_ )
open import Cubical.Data.Vec using ( Vec; lookup; _∷_; [] )
open import Cubical.Data.Sigma.Properties using ( Σ≡Prop )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; squash₁; ∥_∥₁ )

module LJ-1-378.Floor378 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Coding {ℓ} using ( pr )
open import L.Constructible {ℓ} using ( 𝒟ₒ )
open Inf using ( #_; sucV )

import LJ-1-184.ProbeLJ1184A {ℓ} as P184
import LJ-1-297.ProbeLJ1297A {ℓ} lem as P1297A
import LJ-1-297.ProbeLJ1297C {ℓ} as P1297C
import LJ-1-297.ProbeLJ1297D {ℓ} lem as P1297D
import LJ-1-302.ProbeLJ1302A {ℓ} lem as P1302A
import LJ-1-304.ProbeLJ1304A {ℓ} lem as P1304
import LJ-1-238.GenSequence

module A = P184.Ambient
module P1241 = P1297A.P1241
open P1297C using ( absFull )

module GS = LJ-1-238.GenSequence {ℓ} lem P1297A.Full
  (λ {x} {y} → P1297A.Full-tr {x} {y})
  (λ k → # k , tt*) (λ k → refl)
  (λ a b → ⁅ fst a , fst b ⁆ , tt*) (λ a b → refl)
  (λ a → sucV (fst a) , tt*) (λ a → refl)

SC : Type (ℓ-suc ℓ)
SC = A.R.SC

module AbsF = FOL.Absoluteness.Single 𝒮ᵥ P1297A.Full
  (λ {x} {y} → P1297A.Full-tr {x} {y})
open AbsF using ( _^_ ) renaming ( _⊨ᵐ_ to _⊨_ )

floor : ℕ
floor = zero
