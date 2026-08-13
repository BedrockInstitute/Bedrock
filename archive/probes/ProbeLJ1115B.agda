{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.115] probe B: the refutation attempts on EnvSetClosure.
-- RED HALF.
--
-- Probe A shows the bounded half of someEnv is the delivered
-- EnvSet.back transfer, wired at the And-row layout.  The
-- construction half is ONE closure property of K:  the
-- environment-set over an arbitrary arity ar ∈ K with values in the
-- ambient slot exists and lies in K, with the machine's envSetAt
-- satisfaction (`EnvSetClosure`, src/ProbeLJ1115A.agda:91-97).
--
-- This probe tries to refute that need:  derive EnvSetClosure from
-- the delivered machinery.  The only delivered builder is envSet over
-- a NUMERAL (src/L/Coding/EnvSet.lagda.md:183), and the only
-- delivered envSetAt-satisfaction supplier is AmbientHolds, which
-- demands the arity slot equal # m
-- (src/L/Coding/Sound.lagda.md:262-284).  Both attempts below are
-- COMPLETE terms with a type error at the first premise, so the
-- checker sees no hole; the failures are the measurement.
--
-- Attempt 1: the arity membership does not give the numeral equality
-- AmbientHolds needs.  The premise is a membership; the needed fact
-- is an equality.
-- Attempt 2: the delivered envSet's membership in K is not stated by
-- any premise.  The only membership premises in scope are about ar.
--
-- Untracked probe; never committed.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module ProbeLJ1115B {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans )
open import L.Coding.EnvSet {ℓ} lem using ( envSet )
open import ProbeLJ1115A {ℓ} lem using ( module Obligation )

open import Cubical.Data.Nat using ( _+_; ℕ )
open import Cubical.Data.FinData using ( Fin )
open import Cubical.HITs.CumulativeHierarchy.Base using ( _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Constructions using ( module InfinitySet )
open InfinitySet using ( #_ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL using ( _^_ )

module Refute (n : ℕ) (K : Fin (5 + n)) (γ : S ^ (11 + n)) where

  module O = Obligation n K γ
  open O

  -- ATTEMPT 1: the arity must be a numeral for the delivered
  -- builder.  arK is a membership, not an equality.
  -- Hidden for the second measurement; see run 1.
  numeralise : (ar : S) → ⟨ fst ar ∈ fst KS ⟩ → Σ[ m ∈ ℕ ] (fst ar ≡ # m)
  numeralise ar arK = arK

  -- ATTEMPT 2: the delivered envSet's membership in K.  The only
  -- membership premises in scope are about ar; none states
  -- ⟨ envSet B 0 ∈ K ⟩.
  envSet-mem : (ar : S) → ⟨ fst ar ∈ fst KS ⟩ → (B : S)
             → ⟨ fst (envSet B 0) ∈ fst KS ⟩
  envSet-mem ar arK B = arK
