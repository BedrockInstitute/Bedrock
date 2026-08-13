{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.120] probe C: refutation attempts on the K-closure of the
-- generic environment-set. The delivered KFacts fields close pairs and
-- arities, not powersets/separation. Both attempts are complete terms
-- with a type error, so the checker sees no hole.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module ProbeLJ1120C {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans )
open import L.Coding.Model {ℓ} using ( prʟ )
open import ProbeLJ1120A {ℓ} lem using ( module Generic )

open import Cubical.Data.Nat using ( ℕ; _+_ )
open import Cubical.Data.FinData using ( Fin )
open import Cubical.HITs.CumulativeHierarchy.Base using ( _∈_ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL renaming ( _⊨ᵐ_ to _⊨_ )

module Refute (n : ℕ) (K : Fin (5 + n)) (γ : S ^ (11 + n))
  (BK : ⟨ fst (lookup zero γ) ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩)
  (arityK : (N v : S) → ⟨ fst v ∈ fst N ⟩
          → ⟨ fst N ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩
          → ⟨ fst v ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩)
  (pairK : (a b : S)
         → ⟨ fst a ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩
         → ⟨ fst b ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩
         → ⟨ fst (prʟ a b) ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩)
  where

  module G = Generic (lookup zero γ)

  -- ATTEMPT 1: pairK constructs the L-pair of two copies of the
  -- environment-set, not the environment-set itself. The arity
  -- membership is not a membership of the constructed set.
  fromPairK : (ar : S)
            → ⟨ fst ar ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩
            → ⟨ fst (G.envSetGen ar)
                 ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩
  fromPairK ar arK =
    pairK (G.envSetGen ar) (G.envSetGen ar) arK arK

  -- ATTEMPT 2: arityK climbs a member of the constructed set into K,
  -- but no premise supplies membership of the constructed set itself.
  fromArityK : (ar : S)
             → ⟨ fst ar ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩
             → ⟨ fst (G.envSetGen ar)
                  ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩
  fromArityK ar arK = arK
