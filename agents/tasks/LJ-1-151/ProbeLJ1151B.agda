{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.151] probe B: the frame's `valK`, AS STATED, is refutable.
--
-- `src/L/Condensation/TwelveAgree.lagda.md:155-157` states
--
--   valK : (k : ℕ) (c ar a b yc : S)
--        → ⟨ fst c ∈ fst (lookup (suc (suc zero)) γ') ⟩
--        → fst c ≡ pr (fst ar) (pr (# k) (pr (fst a) (fst b)))
--        → ⟨ fst yc ∈ fst (lookup (suc^6 K) γ') ⟩
--
-- and `yc` occurs in NO premise.  `check-unbound-hyp.py` flags it as
-- rule 1, "conclusion subject unconstrained".  This probe turns that
-- flag into a refutation: the statement, plus ONE clause code of binary
-- shape in the clause set, gives `K ∈ K` and contradicts regularity.
--
-- The refutation needs no property of K beyond `K : S`.  It therefore
-- holds at every instantiation whose clause set holds one binary code.
--
-- THE REFUTATION IS THE `Refute` MODULE ONLY.

open import Base.Prelude
open import Base.Truth

module LJ-1-151.ProbeLJ1151B {ℓ : Level} where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ; ∈-irrefl )
open import V.Coding {ℓ} using ( pr )
open import L.Constructible {ℓ} using ( 𝒮ʟ )

open import Cubical.HITs.CumulativeHierarchy.Base using ( _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet )
open InfinitySet using ( #_ )
import Cubical.Data.Empty as Empty

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ

-- ===================================================================
-- THE REFUTATION.  Every non-blank, non-comment line below is counted.
-- ===================================================================

-- `Cs` is the clause set, `K` the bound.  `c₀` is one clause code of the
-- binary shape: the twelve-row clause set holds such codes, so this is
-- the weakest premise under which the frame's statement is used.
module Refute (Cs K : S) (k : ℕ) (c₀ ar a b : S)
  (c∈ : ⟨ fst c₀ ∈ fst Cs ⟩)
  (shape : fst c₀ ≡ pr (fst ar) (pr (# k) (pr (fst a) (fst b))))
  (valK : (k : ℕ) (c ar a b yc : S)
        → ⟨ fst c ∈ fst Cs ⟩
        → fst c ≡ pr (fst ar) (pr (# k) (pr (fst a) (fst b)))
        → ⟨ fst yc ∈ fst K ⟩) where

  -- Apply the statement at `yc := K` and contradict regularity.
  absurd : Empty.⊥
  absurd = ∈-irrefl (fst K) (valK k c₀ ar a b K c∈ shape)
