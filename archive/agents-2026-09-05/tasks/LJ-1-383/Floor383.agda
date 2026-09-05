{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.383] THE EMPTY-BODY FLOOR.  The SAME imports as Probe383.agda
-- and no definition, so the seconds figures in the report are read
-- beside this number (C-53).
--
-- ONE agda process under GHCRTS="-A64m -I0 -M8g".

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

open import FOL.ZFStructure using ( module hPropStructure )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ⁅_,_⁆; ∅ ) renaming ( module InfinitySet to Inf )
open Inf using ( #_; sucV )
open import Cubical.Data.Nat using ( ℕ )
open import Cubical.Data.Sigma using ( _×_ )
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁; ∣_∣₁ )

module LJ-1-383.Floor383 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Coding {ℓ} using ( pr )
open import L.Constructible {ℓ}
  using ( 𝒮ʟ; isL-trans; IsOrd; Lset; Lset-mono )
open import L.Axioms.Numerals {ℓ} using ( numeralL; numeralL-fst )
open import L.Ordinal {ℓ} using ( numeral-ord )
open import L.Ordinal.Stages {ℓ} lem using ( ord∈Lset-suc )

import L.Coding.Model
module GM = L.Coding.Model {ℓ}
open GM using ( prʟ; prʟ-fst )
open GM.AbsL using ( _^_ )

open import L.Condensation {ℓ} lem
  using ( module KFactsNS; module ChainZ; module KTies; module KValue )
open KFactsNS

open import LJ-1-347.Elim347 {ℓ} using ( sgl1-not-numeral )

open hPropStructure 𝒮ʟ using ( S )
