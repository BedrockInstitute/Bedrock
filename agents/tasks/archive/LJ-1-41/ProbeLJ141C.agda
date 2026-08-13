{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.41] THE ENV-HYPOTHESIS STRENGTH, MACHINE-CHECKED.
--
-- The machine's Top clause (src/L/Coding/Model.lagda.md:1278-1282)
-- consumes the STRONG hypothesis envSetAt E (both directions of "E is
-- exactly the set of environments").
--
-- The story's Top row (src/L/Condensation.lagda.md:1099-1109) binds
-- E in K and consumes the WEAK hypothesis envHypT E = "every member
-- of E satisfies envBndGen" (the first direction only).
--
-- This probe asks Agda to hand the story's envHypT to the machine's
-- envSetAt.  EXPECTED: a type error, because envBndGen (bounded,
-- first direction only) is not envSetAt (unbounded, both directions).
--
-- Untracked probe; one Agda process under GHCRTS="-A64m -I0 -M8g";
-- never committed; thrown away per D-1.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module ProbeLJ141C {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans )
open import L.Coding.Model {ℓ} using ( envSetAt )
open import L.Condensation {ℓ} lem using ( envHypT )
open import Cubical.Data.Nat using ( _+_ )
open import Cubical.HITs.CumulativeHierarchy.Base using ( _∈_ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL using ( _^_ ) renaming ( _⊨ᵐ_ to _⊨_ )

-- THE ATTEMPT: use the story's weak env hypothesis where the machine
-- needs its strong one.  The two satisfactions are different formulas.
try : ∀ {m} (B K : Fin (1 + m)) (γ : S ^ (5 + m)) (E : S)
    → ⟨ (E ∷ γ) ⊨ envHypT B K ⟩
    → ⟨ (E ∷ γ) ⊨ envSetAt zero (suc (suc (suc zero))) (suc (suc (suc (suc (suc B))))) ⟩
try B K γ E henv = henv
