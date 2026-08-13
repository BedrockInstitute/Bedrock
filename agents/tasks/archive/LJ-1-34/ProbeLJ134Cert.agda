{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.34] The concrete Delta-0 certificate attempts.
--
-- This probe is EXPECTED TO FAIL.  It attempts the concrete certificates
-- for the bounded story's step clause.  The failures are the evidence
-- for "is the story Delta-0 now?":
--
--   1. The bounded leaf's two existentials are bounded, but the leaf
--      CONTENT (DefBody) is the delivered content, whose leaves carry
--      unbounded quantifiers (isCodeAt: src/L/Coding/Powerset.lagda.md:
--      297-298 and its keyArityAtL/hasWitnessAt; satGraphAt:
--      :191-192 and the twelveAt frame; DefinesAt: :217-219 with its
--      extAt).  There is no Delta-0 constructor for those.
--
--   2. The story's extAt wrappers (the clause and the DefAt leaf) are
--      unbounded universals.  The Delta-0 data has no constructor for
--      an unbounded universal.
--
-- The template certificate (ProbeLJ134.agda, section 2) closes: the
-- WITNESS SHAPE is Delta-0 for any Delta-0 body.  The concrete body's
-- certificate needs the bounded satisfaction substrate.
--
-- Untracked probe; thrown away per D-1; never committed.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module ProbeLJ134Cert {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax
  using ( Formula; var; _∈̇_; _∧̇_; _⇒̇_; ∃̇_; ∀̇_; ∃̇∈ )
open import FOL.LevyHierarchy using ( Δ₀; δ-∈; δ-∃∈; δ-∀∈; δ-∧ )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Coding {ℓ} using ( pr )
open import L.Constructible {ℓ}
  using ( 𝒮ʟ; isL; isL-trans; 𝒟ₒ )
open import L.Coding.Model {ℓ}
  using ( appAt; extAt; extAt-out; extAt-in; extAt-in-both )
open import L.Coding.Powerset {ℓ} lem
  using ( DefAt; DefBody; isCodeAt )
open import L.Coding.Sequence {ℓ} lem
  using ( StepAt; StepBody )
open import Cubical.Data.Nat using ( _+_ )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ

-- THE LEAF CERTIFICATE.  Bounding the two existentials is not enough:
-- the leaf content DefBody is the delivered content, whose leaves carry
-- unbounded quantifiers.  This does not close.
Δ₀-body : {n : ℕ} (w : Fin n) → Δ₀ (DefBody w)
Δ₀-body w =
  δ-∧ (δ-∃∈ δ-∈) (δ-∧ (δ-∃∈ (δ-∃∈ (δ-∃∈ δ-∈))) (δ-∀∈ δ-∈))

Δ₀-leaf : {n : ℕ} (w K : Fin n)
        → Δ₀ (∃̇∈ (var (suc K)) (∃̇∈ (var (suc (suc K))) (DefBody w)))
Δ₀-leaf w K = δ-∃∈ (δ-∃∈ (Δ₀-body w))
