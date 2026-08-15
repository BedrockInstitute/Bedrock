{-# OPTIONS --cubical --safe --guardedness #-}

-- LJ-1.332 probe B.  It lands nothing.  It runs in agents/tasks/LJ-1-332/.
--
-- ONE QUESTION ONLY: is `SqBelow α` really the module parameter of
-- `L.StageCardinal` (src/L/StageCardinal.lagda.md:17-19)?  This file
-- instantiates the module with it and applies `stage-card-upper`.  If it
-- is green, the report's PART 1 refutation is measured by the type
-- checker and not by reading the telescope.
--
-- IT LIVES ALONE because the instantiation is expensive.  Probe A
-- carries the mathematics and must stay cheap to iterate.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-332.ProbeLJ1332B {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

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

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ using ( S; _∈ˢ_ )

-- The module parameter of `L.StageCardinal`, written out.
SqBelow : S → Type (ℓ-suc ℓ)
SqBelow α = (δ : S) → ⟨ δ ∈ˢ sucV α ⟩ → (⟨ δ ∈ˢ ω ⟩ → Empty.⊥) → sq δ

-- MEASURED, by the type checker and not by reading the telescope:
-- `SqBelow α` IS the module's own parameter type, so this is the only
-- way to name `stage-card-upper` with `α` as its own bound.
stage-card-at : (α : S) (oα : IsOrd α) (h : SqBelow α)
              → IsOrd α → ⟨ α ∈ˢ sucV α ⟩ → (⟨ α ∈ˢ ω ⟩ → Empty.⊥)
              → ⟪ Lset α ⟫ ↪ ⟪ α ⟫
stage-card-at α oα h = SC.Upper.stage-card-upper α
  where
  module SC = L.StageCardinal {ℓ} lem α oα h

-- =====================================================================
-- CONTROL 3, ON THE LEAD'S CIRCULARITY.  It was applied, run and
-- reverted.  It is recorded here because nothing typechecks this file
-- once the task closes.
--
--   Feed `stage-card-at` the DESCENT's hypothesis, which supplies the
--   law only at MEMBERS of alpha, in place of the module's own
--   parameter, which supplies it at alpha too:
--
--     control3 : (α : S) → IsOrd α → ((d : S) → ⟨ d ∈ˢ α ⟩ → sq d)
--              → IsOrd α → ⟨ α ∈ˢ sucV α ⟩ → (⟨ α ∈ˢ ω ⟩ → Empty.⊥)
--              → ⟪ Lset α ⟫ ↪ ⟪ α ⟫
--     control3 α oα ih = stage-card-at α oα (λ δ δ∈sα inf → ih δ δ∈sα)
--
--   Agda refused, 2 s, and it expanded `sucV α` to its union
--   representation while doing so:
--     error: [UnequalTerms]
--     ∥ Σ-syntax (SetStructure.X (UnionStructure ⁅ α , ⁅ α ⁆s ⁆)) ... ∥₁
--     !=< (fst (δ ∈ α))
--     when checking that the expression δ∈sα has type ⟨ δ ∈ˢ α ⟩
--
--   THE MACHINE NAMES THE CIRCULARITY.  The module parameter's range is
--   `sucV α`, so it reaches alpha itself, and the descent's hypothesis
--   never does.  A descent cannot feed `stage-card-upper` at its own
--   site, and `stage-card-upper` therefore cannot supply `sq` there.
-- =====================================================================
