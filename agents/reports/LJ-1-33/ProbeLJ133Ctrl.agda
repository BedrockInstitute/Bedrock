{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.33] CONTROL: the bounded step clause's own satisfaction,
-- decoded to its own content shape, with NO machine projection and NO
-- DefAt reading.  This separates "the decode against the delivered
-- machine is expensive" from "the bounded step clause's own
-- satisfaction types are expensive".  The story formula is the same
-- StepStory as the main probe; the decode is the identity on the
-- satisfaction's pair shape, so the check cost is type elaboration of
-- the built formulas' satisfactions at variable slots (the block-1
-- clause-to-content class), not proof content.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module ProbeLJ133Ctrl {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax
  using ( Formula; var; _∈̇_; _∧̇_; _⇒̇_; ∃̇_; ∀̇_; ∃̇∈ )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Coding {ℓ} using ( pr )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans; 𝒟ₒ )
open import L.Coding.Model {ℓ} using ( appAt )
open import L.Coding.Powerset {ℓ} lem using ( DefAt )
open import L.Coding.Sequence {ℓ} lem using ( StepBody )
open import L.Condensation {ℓ} lem
open import Cubical.Data.Nat using ( _+_ )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁; squash₁ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ

open AbsL using ( _^_ ) renaming ( _⊨ᵐ_ to _⊨_ )

module StepStory {n : ℕ} (K : Fin (suc n)) (v b f : Fin n) where
  private
    V₁ B₁ F₁ : Fin (suc n)
    V₁ = suc v
    B₁ = suc b
    F₁ = suc f

  Body : Formula S (5 + n)
  Body =
    (var (suc (suc zero)) ∈̇ var (suc (suc (suc (suc (suc b))))))
    ∧̇ ( appAt (suc (suc (suc (suc (suc f)))))
               (suc (suc zero)) (suc zero)
      ∧̇ ( DefAt zero (suc zero)
        ∧̇ (var (suc (suc (suc zero))) ∈̇ var zero) ) )

  StepWit : Formula S (suc (suc n))
  StepWit =
    ∃̇∈ (var (suc (suc b)))
      (∃̇∈ (var (suc (suc K)))
        (∃̇∈ (var (suc (suc (suc K))))
          Body))

  StepIn : Formula S (suc n)
  StepIn = ∀̇ ((var zero ∈̇ var (suc (suc v))) ⇒̇ StepWit)

  StepOut : Formula S (suc n)
  StepOut = ∀̇ (StepWit ⇒̇ (var zero ∈̇ var (suc (suc v))))

  StepBnd : Formula S (suc n)
  StepBnd = StepIn ∧̇ StepOut

-- The content of the bounded step is the satisfaction's own pair shape:
-- the witness content in, and the witness back out.
module StepContent {n : ℕ} (K : Fin (suc n)) (v b f : Fin n) (γ : S ^ suc n) where
  private
    V₁ B₁ F₁ : Fin (suc n)
    V₁ = suc v
    B₁ = suc b
    F₁ = suc f

  Content : Type (ℓ-suc ℓ)
  Content =
      ((z : S) → ⟨ fst z ∈ fst (lookup V₁ γ) ⟩ → ⟨ (z ∷ γ) ⊨ StepStory.StepWit K v b f ⟩)
    × ((z : S) → ⟨ (z ∷ γ) ⊨ StepStory.StepWit K v b f ⟩ → ⟨ fst z ∈ fst (lookup V₁ γ) ⟩)

  -- OUT: the bounded step's satisfaction gives the content.  The body
  -- of this function is the pair projection; the check cost is the
  -- satisfaction types of the built formulas, not proof content.
  bnd-out : ⟨ γ ⊨ StepStory.StepBnd K v b f ⟩ → Content
  bnd-out h = (h .fst , h .snd)

  -- IN: the content assembles the bounded step's satisfaction.
  bnd-in : Content → ⟨ γ ⊨ StepStory.StepBnd K v b f ⟩
  bnd-in g = (g .fst , g .snd)
