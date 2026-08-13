{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.122] derivation probe: does the numeral envSet come out as the
-- generic envSetGen at arity nn n? This is a scratch measurement. It is
-- not a master edit.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module ProbeLJ1122A {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans )
open import L.Coding.Model {ℓ}
  using ( numL )
open import L.Coding.EnvSet {ℓ} lem
  using ( envSet; module Generic )
open import L.Coding.Sound {ℓ} lem
  using ( module NumeralFromGeneric )

open import Cubical.Data.Nat using ( ℕ )
open import Cubical.HITs.CumulativeHierarchy.Constructions using ( module InfinitySet )
open InfinitySet using ( #_ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL renaming ( _⊨ᵐ_ to _⊨_ )

module Derive (B : S) (n : ℕ) where
  nn : S
  nn = # n , numL n

  derived : fst (envSet B n) ≡ fst (Generic.envSetGen B nn)
  derived = NumeralFromGeneric.derived B n
