{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.58] probe cone: the import interface of ProbeLJ158A.
-- Untracked probe; never committed.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module ProbeLJ158Cone {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

import FOL.Absoluteness
open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula; var; con; _∧̇_; _∨̇_; _≐_; _∈̇_; ∃̇_; ∃̇∈; ⊤̇ )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Coding {ℓ} using ( pr )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans )
open import L.Axioms.Numerals {ℓ} using ( numeralL; numeralL-fst )
open import L.Coding.Model {ℓ}
  using ( prAtL; prAtL-adequate; arityTagAtL; arityTagAtL-adequate
        ; arityTagPairAtL; arityTagPairAtL-adequate; tagAtL; tagAtL-adequate
        ; tagPairAtL; tagPairAtL-adequate; prʟ; prʟ-fst )
open import L.Coding.Shape {ℓ}
  using ( isTmAt; shapes; binForm; unForm; bothTm; fstTm; noneB; noneU; zeroPay )
open import L.Condensation {ℓ} lem using
  ( arTagBS; arTagPairBS; tagBS; isTmBS; bothTmBS; fstTmBS
  ; binFormBS; unFormBS; shapesBS )
open import Cubical.HITs.CumulativeHierarchy.Constructions using ( module InfinitySet )
open InfinitySet using ( #_ )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_; setIsSet )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁; squash₁ )
open import Cubical.Data.Nat using ( _+_ )
open import Cubical.Data.Sum using ( _⊎_; inl; inr )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL renaming ( _⊨ᵐ_ to _⊨_ )

cone : {n : ℕ} → Fin n → S ^ (1 + n) → Type (ℓ-suc ℓ)
cone A γ = ⟨ γ ⊨ shapesBS A A A A A A A A A A A A A A ⟩

