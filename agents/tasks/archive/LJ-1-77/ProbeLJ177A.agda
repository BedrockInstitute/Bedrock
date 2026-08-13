{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.77] probe A: is KFacts uninhabitable?
--
-- The adversarial review (_build/diag-twelve-row-math.md section 4)
-- claims KFacts has no inhabitant: its arityK field says every set
-- belongs to K, and every v belongs to its own singleton, so
-- X = fst (lookup K γ) belongs to K = itself, refuted by ∈-irrefl.
--
-- This probe machine-checks that refutation: from a value of
-- KFacts.arityK at any K and γ, ⊥.
--
-- Untracked probe; never committed.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module ProbeLJ177A {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ; ∈-irrefl )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans )
open import L.Axioms.Numerals {ℓ} using ( pairʟ; pairʟ-fst )
open import V.Model {ℓ} using ( pair-singleton )
open import L.Condensation {ℓ} lem using
  ( module KFactsNS )

open import Cubical.HITs.CumulativeHierarchy.Base using ( _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ⁅_,_⁆; ⁅_⁆s; pairing-ax; module InfinitySet )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( _∈ₛ_; ∈∈ₛ )
open InfinitySet using ( #_ )
import Cubical.Data.Empty as Empty
import Cubical.Data.Sum as Sum
open Sum using ( _⊎_; inl; inr )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁ )
open import Cubical.Data.Nat using ( _+_ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL renaming ( _⊨ᵐ_ to _⊨_ )

-- =====================================================================
-- THE REFUTATION
-- =====================================================================
module Refute (n : ℕ) (A K N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 : Fin n)
  (γ : S ^ n) where

  X : S
  X = lookup K γ

  -- N = pairʟ X X is the L-singleton of X:
  -- fst N ≡ ⁅ fst X , fst X ⁆ ≡ ⁅ fst X ⁆s
  N : S
  N = pairʟ X X

  -- fst N is the hierarchy singleton of fst X.
  fstN≡singl : fst N ≡ ⁅ fst X ⁆s
  fstN≡singl = pairʟ-fst X X ∙ pair-singleton (fst X)

  X∈pair : ⟨ fst X ∈ ⁅ fst X , fst X ⁆ ⟩
  X∈pair = ∈∈ₛ {a = fst X} {b = ⁅ fst X , fst X ⁆} .snd
    (pairing-ax (fst X) (fst X) (fst X) .snd ∣ inl refl ∣₁)

  -- X ∈ fst N: X ∈ ⁅ X , X ⁆ by pairing, transported along fstN≡singl.
  X∈N : ⟨ fst X ∈ fst (pairʟ X X) ⟩
  X∈N = subst (λ w → ⟨ fst X ∈ w ⟩) (sym (pairʟ-fst X X)) X∈pair

  -- arityK N X : X ∈ N → X ∈ K.  The conclusion is X ∈ X.
  arityK-refutes : (arityK : (N v : S) → ⟨ fst v ∈ fst N ⟩
                           → ⟨ fst v ∈ fst (lookup K γ) ⟩)
                 → Empty.⊥
  arityK-refutes arityK = ∈-irrefl (fst X) (arityK N X X∈N)

-- KFacts itself: the record's arityK field refutes the whole record.
KFacts-refutes : {n : ℕ} (A K N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 : Fin n)
               → (γ : S ^ n)
               → KFactsNS.KFacts A K N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 γ
               → Empty.⊥
KFacts-refutes A K N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 γ f =
  Refute.arityK-refutes _ A K N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 γ
    (f .KFactsNS.KFacts.arityK)
