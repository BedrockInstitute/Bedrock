{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.306] re-export test, owner's ruling 2026-08-15.  The landed
-- chapter must re-export the applied family so that consumer files
-- keep their `open import L.Condensation ... using ( module MemAgree )`
-- lines unchanged.  This file is the landed chapter's shape in
-- miniature: the application, then the public open.

open import Base.Prelude
open import Base.Truth

module LJ-1-306.ReexportTest {ℓ : Level} where

open import FOL.ZFStructure using ( Transitive; _↾_ )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ} using ( isL; isL-trans )
open import L.Axioms.Numerals {ℓ}
  using ( numeralL; numeralL-fst; pairʟ; pairʟ-fst; sucʟ; sucʟ-fst )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ⁅_,_⁆; module InfinitySet )
open InfinitySet using ( #_; sucV )

import LJ-1-306.GenAgree

module Fam = LJ-1-306.GenAgree {ℓ} isL isL-trans
               numeralL numeralL-fst pairʟ pairʟ-fst sucʟ sucʟ-fst

open Fam public
