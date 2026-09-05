{-# OPTIONS --cubical --safe --guardedness #-}

-- LJ-1.333 probe B.  It lands nothing.  It runs in agents/tasks/LJ-1-333/.
--
-- ONE QUESTION ONLY: does the DELIVERED consumer accept the truncated
-- law?  Probe A measures the SHAPE of the descent.  This file measures
-- the delivered module itself, `L.StageCardinal`, by instantiating it.
--
-- IT LIVES ALONE because the instantiation is expensive.  Probe A
-- carries the mathematics and must stay cheap to iterate.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-333.ProbeLJ1333B {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ} using ( IsOrd; Lset )
open import L.Ordinal.SquareLaw {ℓ} lem using ( sq )
open import L.Cardinal {ℓ} lem using ( _↪_ )
import L.StageCardinal

open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet )
open InfinitySet {ℓ} using ( ω; sucV )
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ using ( S; _∈ˢ_ )

-- The module parameter of `L.StageCardinal`, src/L/StageCardinal.lagda.md:17-19.
SqBelow : S → Type (ℓ-suc ℓ)
SqBelow α = (δ : S) → ⟨ δ ∈ˢ sucV α ⟩ → (⟨ δ ∈ˢ ω ⟩ → Empty.⊥) → sq δ

-- What the limit band actually supplies today: the SAME family, one
-- truncation bar per member.  `limit-truncated`,
-- agents/tasks/LJ-1-332/ProbeLJ1332A.agda:196-204, gives one row of it.
SqBelowT : S → Type (ℓ-suc ℓ)
SqBelowT α = (δ : S) → ⟨ δ ∈ˢ sucV α ⟩ → (⟨ δ ∈ˢ ω ⟩ → Empty.⊥) → ∥ sq δ ∥₁

-- THE UNTRUNCATED CONTROL, WRITTEN FIRST (C-56).  This is `[LJ-1.332]`'s
-- `stage-card-at` re-derived under my own hand, so I quote no term I did
-- not check.  It is the delivered consumer, instantiated.
stage-card-at : (α : S) (oα : IsOrd α) (h : SqBelow α)
              → IsOrd α → ⟨ α ∈ˢ sucV α ⟩ → (⟨ α ∈ˢ ω ⟩ → Empty.⊥)
              → ⟪ Lset α ⟫ ↪ ⟪ α ⟫
stage-card-at α oα h = SC.Upper.stage-card-upper α
  where
  module SC = L.StageCardinal {ℓ} lem α oα h

-- THE ONE STEP THAT WOULD CLOSE THE LEG IF A TRUNCATED LAW SERVED.  It
-- is a choice principle over the bounded ordinals, stated here as a
-- hypothesis and never assumed.  With it the consumer runs truncated;
-- without it nothing joins the pointwise bars into one.
ACBelow : S → Type (ℓ-suc ℓ)
ACBelow α = SqBelowT α → ∥ SqBelow α ∥₁

stage-card-trunc : (α : S) (oα : IsOrd α) → ACBelow α → SqBelowT α
                 → IsOrd α → ⟨ α ∈ˢ sucV α ⟩ → (⟨ α ∈ˢ ω ⟩ → Empty.⊥)
                 → ∥ ⟪ Lset α ⟫ ↪ ⟪ α ⟫ ∥₁
stage-card-trunc α oα ac h oα' α∈sα infα =
  PT.map (λ g → stage-card-at α oα g oα' α∈sα infα) (ac h)

-- =====================================================================
-- CONTROL 4, ON THE DELIVERED CONSUMER.  It was applied, run and
-- reverted.  It is recorded here because nothing typechecks this file
-- once the task closes.
--
--   Offer the POINTWISE-TRUNCATED family where the delivered module
--   takes its own parameter, changing nothing else:
--
--     control4 : (α : S) (oα : IsOrd α) (h : SqBelowT α)
--              → IsOrd α → ⟨ α ∈ˢ sucV α ⟩ → (⟨ α ∈ˢ ω ⟩ → Empty.⊥)
--              → ⟪ Lset α ⟫ ↪ ⟪ α ⟫
--     control4 α oα h = stage-card-at α oα h
--
--   Agda refused, 2 s:
--     error: [UnequalTerms]
--     ∥ sq δ ∥₁ !=<
--     (Σ (⟪ δ ⟫ × ⟪ δ ⟫ → ⟪ δ ⟫)
--      (λ f → (x y : ⟪ δ ⟫ × ⟪ δ ⟫) → f x ≡ f y → x ≡ y))
--     when checking that the expression h has type SqBelow α
--
--   THE DELIVERED CONSUMER REFUSES THE TRUNCATED LAW, and the refusal is
--   not an artefact of probe A's shapes: it is the module itself.
-- =====================================================================
