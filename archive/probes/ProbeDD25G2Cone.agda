{-# OPTIONS --cubical --safe --guardedness #-}

-- DD25 review probe G2: THE CURE.  The constant-carrying chain of the
-- bounded code-set description, restated with the tag numerals as
-- variable slots.  This is the file's own documented house style
-- (src/L/Condensation.lagda.md:1111-1114), which the twelve rows
-- already use through arTagB (:435) and arTagPairB (:450), applied to
-- the four *Bnum leaf helpers that the rows do not use.
--
-- The target: countFo ≡ 0, so Cnt.erase applies with refl, and the
-- Delta-0 certificate survives unchanged.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module ProbeDD25G2Cone {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using
  ( Formula; var; _∈̇_; _≐_; _∧̇_; _∨̇_; _⇒̇_; ⊤̇; ∃̇∈; ∀̇∈ )
open import FOL.LevyHierarchy using
  ( Δ₀; δ-∈; δ-≐; δ-∧; δ-∨; δ-⇒; δ-⊤; δ-∀∈; δ-∃∈ )
open import FOL.Manipulation.Parameters using ( countFo )
open import Cubical.Data.Nat using ( _+_ )
import FOL.Count
open import L.Constructible {ℓ} using ( 𝒮ʟ )
open import L.Absoluteness {ℓ} using ( Δ₀-liftFo )
open import L.Coding.Base {ℓ} using ( Δ₀-prAt )
open import L.Coding.Environment {ℓ} using ( Δ₀-sucAt )
open import L.Coding.Model {ℓ} using ( prAtL; appAt; sucAtL )
open import L.Condensation {ℓ} lem using
  ( bothSameB; Δ₀-bothSameB; oneSameB; Δ₀-oneSameB
  ; oneSuccB; Δ₀-oneSuccB; succSndB; Δ₀-succSndB
  ; extAtB; Δ₀-extAtB )
open import L.BoundedSubset {ℓ} lem using ( erase-Δ₀ )

open hPropStructure 𝒮ʟ

module Cnt = FOL.Count.Count {ℓ = ℓ-suc ℓ} S
