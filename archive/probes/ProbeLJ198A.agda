{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.98] probe A: does the use site supply entryK's tie?
--
-- entryK (src/L/Condensation/TwelveAgree.lagda.md:118-120) is
-- refuted because z is free.  The brief's candidate tie is the
-- T-slot tie that domEntryK (src/L/Condensation.lagda.md:6504-6506)
-- states:
--
--   (x y : S) → ⟨ pr (fst x) (fst y) ∈ fst (lookup T γ) ⟩
--             → x ∈ K × y ∈ K
--
-- The row use site is the generic EnvSet transfer.  Every row passes
-- entryK into EnvSet (e.g. MemAgree at
-- src/L/Condensation.lagda.md:4201), and EnvSet applies it at
-- `entryK z x y p` (src/L/Condensation.lagda.md:2815-2817).  There,
-- z is an ENVIRONMENT: a member of the env-set slot E, bound by
-- extAtB→extAt (src/L/Condensation.lagda.md:2508-2514), and
-- p : ⟨ pr (fst x) (fst y) ∈ fst z ⟩ is one entry of that
-- environment.
--
-- Module 2 first (green): the tie the site's own binders make
-- available is the ENV-SET tie, z ∈ E.  With that premise on the
-- fact, the site-use lemma closes: the site binds z ∈ E directly.
--
-- Module 1 second (red, as designed): the T-slot tie's premise is
-- ⟨ pr x y ∈ T ⟩.  The site's binders supply z ∈ E and
-- p : pr x y ∈ z; they do not supply pr x y ∈ T.  The site-use
-- lemma from the T-tie cannot be written: the hole below is exactly
-- the absent T-membership, and it stays unsolved (exit 42).
--
-- Untracked probe; never committed.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module ProbeLJ198A {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

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

-- Module 2: the env-set tie, what the site's binders make available.
-- The EnvSet site binds z ∈ E (the env-set slot) and p : pr x y ∈ z.
-- With the env-set tie as the fact's premise, the site-use lemma is
-- exactly the fact's instantiation: green.
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

-- Module 1: the T-slot tie (the brief's candidate, domEntryK).
-- The site's binders are the same as above: z ∈ E and
-- p : pr x y ∈ z.  The T-tie's premise is pr x y ∈ T; the site has
-- no binder for it.  The hole below is that premise, and it stays
-- unsolved: the site-use lemma does not typecheck.
module EntryKTieT {n : ℕ} (T E K : Fin n) (γ : S ^ n)
  (domEntryK : (x y : S) → ⟨ pr (fst x) (fst y) ∈ fst (lookup T γ) ⟩
             → ⟨ fst x ∈ fst (lookup K γ) ⟩
               × ⟨ fst y ∈ fst (lookup K γ) ⟩) where

  -- This term cannot be written: the T-membership of the entry is
  -- not among the site's binders.  Red, as designed.
  envEntry-use : (z x y : S)
    → ⟨ fst z ∈ fst (lookup E γ) ⟩
    → ⟨ pr (fst x) (fst y) ∈ fst z ⟩
    → ⟨ fst x ∈ fst (lookup K γ) ⟩ × ⟨ fst y ∈ fst (lookup K γ) ⟩
  envEntry-use z x y z∈E p = domEntryK x y ?
