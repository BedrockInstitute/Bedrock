{-# OPTIONS --cubical --safe --guardedness #-}

-- LJ-1.337 probe C.  It lands nothing.  It runs in agents/tasks/LJ-1-337/.
--
-- THE REUSE TEST.  `[LJ-1.335]:298` recorded `sucV` injectivity ABSENT from
-- `src/`, by the literal filter
-- `grep -rn "isPropInit\|sucV-inj\|sucV-injective" src/`.  A semantic search
-- found it LIVE, under the name `ord-suc-inj`, at
-- src/L/Choice/Stage.lagda.md:239.  The token order is reversed, so that
-- pattern cannot match it.
--
-- This file MACHINE-CHECKS the refutation: it names the two types probe A
-- proves for itself, and closes both with the DELIVERED terms.  If either
-- fails, the negative stands.  If both pass, probe A's PART 1 and PART 2
-- are re-derivations of `src/`.
--
-- IT IS SEPARATE from probe A on purpose.  This import costs FOUR masters
-- (`L.Choice.Stage`, `L.Ordinal.Stages`, `L.Rank`, `L.Stage`), measured by
-- agents/tasks/LJ-1-337/probe-imports.py, so probe A carries the
-- dichotomy's own price with no edge to this chapter.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-337.ProbeLJ1337C {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ} using ( IsOrd )
open import L.Choice.Stage {ℓ} lem using ( ord-suc-inj; isPropPredOf )

open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet )
open InfinitySet {ℓ} using ( sucV )
open import Cubical.Data.Sigma using ( _×_ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ using ( S )

-- PROBE A's PART 1, closed by the delivered term.
reuse-sucV-inj : (a b : S) → IsOrd a → sucV a ≡ sucV b → a ≡ b
reuse-sucV-inj = ord-suc-inj

-- PROBE A's PART 2, closed by the delivered term.  The delivered shape
-- carries `sucV δ ≡ σ` where probe A writes `α ≡ sucV γ`, and it carries
-- no membership row, so this is the propositionality and NOT the
-- statement the descent consumes.
reuse-isPropIsSuc : (σ : S) → isProp (Σ[ δ ∈ S ] (IsOrd δ × (sucV δ ≡ σ)))
reuse-isPropIsSuc = isPropPredOf
