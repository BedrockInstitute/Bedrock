{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.98] probe B: the env-set tie closes at the EnvSet site.
--
-- Positive control for ProbeLJ198A.  The row use of entryK
-- (EnvSet, src/L/Condensation.lagda.md:2815-2817) applies the fact
-- at z, an environment: z ∈ E (the env-set slot) and
-- p : pr x y ∈ z.  The site's binders supply z ∈ E directly, so the
-- ENV-SET tie is what the site makes available:
--
--   (z x y : S) → z ∈ E → pr x y ∈ z → x ∈ K × y ∈ K
--
-- This module shows that tied form closes the site-use lemma.
-- The shared frame (TwelveAgree.lagda.md:45-243) has no env-set
-- slot, so the frame cannot state this tied form; the T-slot tie the
-- brief proposes is measured NOT supplied in ProbeLJ198A.
--
-- Untracked probe; never committed.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module ProbeLJ198B {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans )
open import V.Coding {ℓ} using ( pr )
open import Cubical.Data.Nat using ( _+_ )
open import Cubical.HITs.CumulativeHierarchy.Base using ( _∈_ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL using ( _^_ )

module EntryKTieEnv {n : ℕ} (E K : Fin n) (γ : S ^ n)
  (envEntryK : (z x y : S) → ⟨ fst z ∈ fst (lookup E γ) ⟩
             → ⟨ pr (fst x) (fst y) ∈ fst z ⟩
             → ⟨ fst x ∈ fst (lookup K γ) ⟩
               × ⟨ fst y ∈ fst (lookup K γ) ⟩) where

  -- The EnvSet site's needed conclusion, from the site's binders.
  envEntry-use : (z x y : S)
    → ⟨ fst z ∈ fst (lookup E γ) ⟩
    → ⟨ pr (fst x) (fst y) ∈ fst z ⟩
    → ⟨ fst x ∈ fst (lookup K γ) ⟩ × ⟨ fst y ∈ fst (lookup K γ) ⟩
  envEntry-use z x y z∈E p = envEntryK z x y z∈E p
