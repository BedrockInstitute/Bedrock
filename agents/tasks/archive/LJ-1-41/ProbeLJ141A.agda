{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.41] THE SUCCESSOR-SUBVALUE LEAF, MACHINE-CHECKED.
--
-- The machine's subValSuccAt reads the subformula's value at the
-- SUCCESSOR arity: the adequate target is
-- `pr (pr (sucV ar) a) y ∈ T` (src/L/Coding/Model.lagda.md:1405-1412).
-- The story's subValSuccB (src/L/Condensation.lagda.md:451-456) reads
-- the same layer as `pr (pr ar a) y ∈ T` -- the SAME arity.
--
-- This probe attempts the machine-to-story transfer of the leaf.  If
-- the two readers agreed, the transfer would close with the key-in-K
-- site fact.  EXPECTED: a type error at `out`, because the machine's
-- second witness is pinned to `pr (sucV ar) a` and the story's
-- reader demands `pr ar a`.
--
-- Untracked probe; one Agda process under GHCRTS="-A64m -I0 -M8g";
-- never committed; thrown away per D-1.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module ProbeLJ141A {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula; var; _∧̇_; ∃̇∈ )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans )
open import L.Coding.Model {ℓ} using ( subValSuccAt )
open import L.Condensation {ℓ} lem using ( subValSuccB )
open import Cubical.Data.Nat using ( _+_ )
open import Cubical.HITs.CumulativeHierarchy.Base using ( _∈_ )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; squash₁ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL using ( _^_ ) renaming ( _⊨ᵐ_ to _⊨_ )

-- THE ATTEMPTED LEAF TRANSFER, machine-to-story.  The site fact says
-- every witness lies in K.  The machine's clause supplies z1 and z2;
-- the story's bounded version must reuse them.  The story's second
-- reader is `prAtL zero (suc (suc ar)) (suc (suc a))`, the machine's
-- is `prAtL zero (suc zero) (suc (suc a))`.  They disagree.
out : ∀ {m} (T ar a y K : Fin m) (γ : S ^ m)
    → ((z : S) → ⟨ fst z ∈ fst (lookup K γ) ⟩)
    → ⟨ γ ⊨ subValSuccAt T ar a y ⟩ → ⟨ γ ⊨ subValSuccB T ar a y K ⟩
out T ar a y K γ kk h = PT.rec squash₁
  (λ { (z₁ , (sz₁ , hz₁)) → PT.rec squash₁
    (λ { (z₂ , (p₂ , a₂)) →
      ∣ z₁ , ( kk z₁
             , ( sz₁
               , ∣ z₂ , ( kk z₂ , ( p₂ , a₂ ) ) ∣₁ ) ) ∣₁ })
    hz₁ })
  h
