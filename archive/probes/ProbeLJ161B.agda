{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.61] probe B: the cold interface-load cost of the three
-- imports step 1 added to L.Condensation (L.Coding.Graph,
-- L.Coding.CodeSet, L.Coding.Powerset).  Untracked probe; never
-- committed.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module ProbeLJ161B {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import L.Coding.Graph {ℓ} lem using ( satGraphAt; twelveAt )
open import L.Coding.CodeSet {ℓ} lem using ( hasWitnessAt; keyArityAtL )
open import L.Coding.Powerset {ℓ} lem using ( isCodeAt; DefBody; DefinesAt; envOneAt )
