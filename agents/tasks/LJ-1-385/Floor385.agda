{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.385] THE FLOOR (C-53).  The same imports as `Ident385.agda` and
-- `Cross385.agda`, with an EMPTY body.  Every seconds figure in
-- `lj-1.385-report.md` stands against this number.
--
-- ONE agda process under GHCRTS="-A64m -I0 -M8g".

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

open import FOL.ZFStructure using ( module hPropStructure; _↾_ )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ∅ ) renaming ( module InfinitySet to Inf )
open Inf using ( #_; sucV )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁ )

import LJ-1-338.ProbeLeaf338
import LJ-1-341.ProbeTies341

module LJ-1-385.Floor385 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Coding {ℓ} using ( pr )
open import L.Constructible {ℓ} using ( IsOrd )

import LJ-1-297.ProbeLJ1297A {ℓ} lem as P1297A
module PL = LJ-1-338.ProbeLeaf338 {ℓ} lem
module PT341 = LJ-1-341.ProbeTies341 {ℓ} lem
