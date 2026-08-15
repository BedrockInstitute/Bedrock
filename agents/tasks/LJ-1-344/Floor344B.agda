{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.344] THE IMPORT-BLOCK FLOOR (C-53).
--
-- `Supply344.agda`'s import block, character for character, and NO
-- definition.  The delta between this file and `Supply344.agda` is the
-- honest cost of the supply itself.  The empty-file floor is
-- `Floor344.agda`.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( var; _∈̇_; _∧̇_; ∃̇_ )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_; setIsSet )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ⁅_,_⁆; ⁅_⁆s; pairing-ax ) renaming ( module InfinitySet to Inf )
open Inf using ( #_ )
open import Cubical.HITs.CumulativeHierarchy.Properties
  using ( ∈∈ₛ; extensionality; _⊆_ )
open import Cubical.Data.Sum using ( inl; inr )
open import Cubical.Data.Nat using ( _+_ )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁ )

module LJ-1-344.Floor344B {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Coding {ℓ} using ( pr )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL-trans )
open import L.Axioms.Numerals {ℓ} using ( numeralL; numeralL-fst )

import L.Coding.Model
module GM = L.Coding.Model {ℓ}
open GM using ( tagAtL; tagAtL-adequate; prʟ; prʟ-fst )
open GM.AbsL using ( _^_ ) renaming ( _⊨ᵐ_ to _⊨_ )

open import L.Coding.Powerset {ℓ} lem
  using ( envOneAt; envOne; envOneAt-out; envOneAt-in )

open import L.Condensation {ℓ} lem using ( module KFactsNS; module DefinesAgree )
open KFactsNS

open hPropStructure 𝒮ʟ using ( S )
