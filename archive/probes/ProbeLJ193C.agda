{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.93] probe C: two representative failed supply attempts.
--
-- The consumer telescope holds no fact about the t0 slot, and its
-- entry fact is pinned to the code slot.  The two attempts below
-- show the concrete type errors: tagEq0 is about the N0 slot, never
-- t0; closedEntryK is the code-slot instance of entryK, never the
-- z-general statement AbstractFrame requires.
--
-- This probe is expected NOT to typecheck.  Untracked probe; never
-- committed.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module ProbeLJ193C {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula; _∧̇_; var; _≐_; _∈̇_ )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Coding {ℓ} using ( pr )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans )
open import L.Axioms.Numerals {ℓ} using ( numeralL )
open import L.Coding.Graph {ℓ} lem using ( twelveAt )
open import L.Coding.Model {ℓ} using ( appAt; closedAt; domAt )
open import L.Condensation {ℓ} lem using ( module KFactsNS; KFactsCons )

open import Cubical.Data.Nat using ( _+_ )
open import Cubical.HITs.CumulativeHierarchy.Base using ( _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Constructions using ( module InfinitySet )
open InfinitySet using ( #_ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL renaming ( _⊨ᵐ_ to _⊨_ )

open KFactsNS
open KFacts

module Attempts (n : ℕ)
  (w K N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 t0 t1 : Fin (5 + n))
  (γ : S ^ (8 + n))
  (kf : KFacts {8 + n} (suc (suc (suc w))) (suc (suc (suc K)))
         (suc (suc (suc N0))) (suc (suc (suc N1)))
         (suc (suc (suc N2))) (suc (suc (suc N3)))
         (suc (suc (suc N4))) (suc (suc (suc N5)))
         (suc (suc (suc N6))) (suc (suc (suc N7)))
         (suc (suc (suc N8))) (suc (suc (suc N9)))
         (suc (suc (suc N10))) (suc (suc (suc N11))) γ)
  (closedEntryK : (d e f : S) → (x y : S)
                 → ⟨ pr (fst x) (fst y) ∈ fst (lookup (suc (suc zero)) (f ∷ e ∷ d ∷ γ)) ⟩
                 → ⟨ fst x ∈ fst (lookup (suc (suc (suc K))) γ) ⟩
                   × ⟨ fst y ∈ fst (lookup (suc (suc (suc K))) γ) ⟩) where

  module At (d e f : S) where

    -- t0eq attempted from the only tag fact the consumer holds: the
    -- consumer's KFacts states tagEq0 about the N0 slot, never about
    -- the t0 slot.  Expected error: N0 != t0.  MEASURED.
    t0eq-attempt : fst (lookup (suc (suc (suc (suc (suc (suc t0)))))) (f ∷ e ∷ d ∷ γ))
                     ≡ fst (numeralL 0)
    t0eq-attempt = kf .tagEq0

    -- entryK attempted from closedEntryK: the consumer's fact is
    -- pinned to the code slot, AbstractFrame's is quantified over
    -- every z.  Expected error: z != lookup (suc (suc zero)) (...).
    -- MEASURED.
    entryK-attempt : (z x y : S) → ⟨ pr (fst x) (fst y) ∈ fst z ⟩
                   → ⟨ fst x ∈ fst (lookup (suc (suc (suc K))) γ) ⟩
                     × ⟨ fst y ∈ fst (lookup (suc (suc (suc K))) γ) ⟩
    entryK-attempt = closedEntryK d e f
