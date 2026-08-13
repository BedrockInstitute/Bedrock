{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.79] probe A: does the LJ-1.77 refutation still apply to the
-- repaired KFacts?
--
-- LJ-1.77 refuted KFacts.arityK as
--   arityK : (N v : S) → ⟨ fst v ∈ fst N ⟩ → ⟨ fst v ∈ fst (lookup K γ) ⟩
-- by N = pairʟ X X (the L-singleton of X), v = X, premise X ∈ {X},
-- conclusion X ∈ X, refuted by ∈-irrefl.
--
-- The repaired field is guarded with the arity's own K-membership:
--   arityK : (N v : S) → ⟨ fst v ∈ fst N ⟩ → ⟨ fst N ∈ fst (lookup K γ) ⟩
--                         → ⟨ fst v ∈ fst (lookup K γ) ⟩
-- The old refutation supplies no ⟨ fst N ∈ fst (lookup K γ) ⟩ for
-- N = pairʟ X X, so it no longer typechecks.  This probe documents
-- that the refutation no longer applies.  It does NOT exhibit an
-- inhabitant of KFacts; that distinction is kept.
--
-- Untracked probe; never committed.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module ProbeLJ179A {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ; ∈-irrefl )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans )
open import L.Axioms.Numerals {ℓ} using ( pairʟ; pairʟ-fst )
open import V.Model {ℓ} using ( pair-singleton )
open import L.Condensation {ℓ} lem using ( module KFactsNS )

open import Cubical.HITs.CumulativeHierarchy.Base using ( _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ⁅_,_⁆; ⁅_⁆s; pairing-ax; module InfinitySet )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( _∈ₛ_; ∈∈ₛ )
open InfinitySet using ( #_ )
import Cubical.Data.Empty as Empty
open import Cubical.Data.Sum as Sum using ( _⊎_; inl; inr )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁ )
open import Cubical.Data.Nat using ( _+_ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL renaming ( _⊨ᵐ_ to _⊨_ )

-- The repaired arityK type: the old refutation needs a third
-- argument (the arity's K-membership) that the singleton case
-- cannot supply.  This module states the repaired type and shows the
-- refutation shape that no longer goes through: given the guarded
-- arityK and ONLY the old two premises, there is no way to apply it.
module RepairedArityK (n : ℕ) (A K N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 : Fin n)
  (γ : S ^ n) where

  X : S
  X = lookup K γ

  N : S
  N = pairʟ X X

  X∈N : ⟨ fst X ∈ fst N ⟩
  X∈N = subst (λ w → ⟨ fst X ∈ w ⟩) (sym (pairʟ-fst X X))
    (∈∈ₛ {a = fst X} {b = ⁅ fst X , fst X ⁆} .snd
      (pairing-ax (fst X) (fst X) (fst X) .snd ∣ inl refl ∣₁))

  -- The guarded arityK cannot be applied to (N X X∈N): it needs
  -- ⟨ fst N ∈ fst (lookup K γ) ⟩, which the old refutation never
  -- had.  The old refutation term (arityK N X X∈N) is therefore a
  -- type error against the repaired field; this is the direct
  -- evidence that the refutation no longer applies.
  -- What the refutation would need, and cannot have: N ∈ K-slot.
  -- This is the missing premise.  MEASURED: the guarded type demands
  -- it; the singleton construction supplies only X ∈ N.
  missing : Type (ℓ-suc ℓ)
  missing = ⟨ fst N ∈ fst (lookup K γ) ⟩
