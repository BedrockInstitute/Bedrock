{-# OPTIONS --cubical --safe --guardedness #-}

-- [DD25 / LJ-1.41 REVIEW] DOES A Δ₀ WITNESS EXIST FOR A TWO-WAY
-- ENVIRONMENT-SET CONDITION?
--
-- The [LJ-1.41] return says NO:
--   "a Δ₀ witness does not exist for the unbounded envSetAt (the
--    hierarchy's Δ₀ has no δ-∀, no δ-∃), so the rows cannot be made
--    equivalent within the Δ₀ constraint."
--
-- The return's own method answers this everywhere else in the file: a
-- Δ₀ witness is never asked of the machine's UNBOUNDED formula.  It is
-- asked of a K-BOUNDED restatement, which then transfers to the
-- machine's formula under site facts.  That is what subValB does for
-- subValAt, what extAtB does for extAt, and what envBndGen does for
-- envOverAt.
--
-- This probe builds the missing piece: the K-bounded restatement of
-- the machine's envSetAt, which is the delivered extAtB applied to the
-- delivered envBndGen, and its Δ₀ certificate.
--
-- EXPECTED: GREEN.  If it is green, "a Δ₀ witness does not exist" is
-- refuted.
--
-- Untracked probe; one Agda process under GHCRTS="-A64m -I0 -M8g";
-- never committed; thrown away per D-1.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module ProbeDD25F41A {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula )
open import FOL.LevyHierarchy using ( Δ₀ )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ} using ( 𝒮ʟ )
open import L.Condensation {ℓ} lem using ( extAtB; Δ₀-extAtB; envBndGen; Δ₀-envBndGen )
open import Cubical.Data.Nat using ( _+_ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ

-- THE MISSING CONJUNCT, WRITTEN.  envSetB is the K-bounded two-way
-- statement "E is exactly the set of environments over ar with values
-- in B, as far as K sees".  Its FIRST conjunct is literally the
-- story's delivered envHyp* shape (∀̇∈ (var E) envBndGen).  The second
-- conjunct is what the story omits.
envSetB : ∀ {n} → (E ar B K : Fin n) → Formula S n
envSetB E ar B K =
  extAtB E K (envBndGen zero (suc E) (suc E) (suc ar) (suc K) (suc B))

-- THE Δ₀ WITNESS.  One line.  The return says this object cannot exist.
Δ₀-envSetB : ∀ {n} (E ar B K : Fin n) → Δ₀ (envSetB E ar B K)
Δ₀-envSetB E ar B K =
  Δ₀-extAtB E K _
    (Δ₀-envBndGen zero (suc E) (suc E) (suc ar) (suc K) (suc B))
