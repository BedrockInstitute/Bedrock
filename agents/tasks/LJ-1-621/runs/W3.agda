{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.621]  W3.  THE WIDEST UNMEASURED TERM, as the brief states it:
-- "LJ-1.617's Q, re-ascribed at Upper's induction, TYPE ONLY, capped".
-- This file is that, and nothing else.  It is written FIRST and
-- typechecked ALONE under a cap this task sets at TWO MINUTES.
--
-- Q IS TAKEN VERBATIM from [LJ-1.617]'s probe
-- (agents/tasks/LJ-1-617/Probe617.agda:464-465), and the re-ascription
-- is at Upper's own induction position: `stage-card-upper` is
-- `∈-induction step` at `P` (src/L/StageCardinal.lagda.md:566), and
-- the acceptance row at the bottom of this file puts Q in that
-- position.  It elaborates only if Q is a motive the tree's own
-- induction former accepts.  NO term of this file proves anything
-- about Q; the module parameter below is hypothetical.
--
-- CALIBER.  THE PROGRAM SET GHCRTS ON THIS PANE.  I DID NOT SET IT.
-- ONE AGDA PROCESS AT A TIME.

open import Base.Prelude
open import Base.Truth
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫ )
open import Cubical.HITs.CumulativeHierarchy.Constructions using ( module InfinitySet )
open import L.Constructible using ( IsOrd; Lset )

module LJ-1-621.runs.W3 {ℓ : Level} (α : V ℓ) where

open InfinitySet using ( sucV )
open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ; ∈-induction )
open import Cubical.Data.Sigma using ( Σ-syntax )

open hPropStructure 𝒮ᵥ using ( _∈ˢ_ )

-- The injection type, local, the tree's own shape
-- (src/L/StageCardinal.lagda.md:243-246, restated at
-- src/L/BoundedSubset.lagda.md:1365-1368).
_↪_ : Type ℓ → Type ℓ → Type ℓ
X ↪ Y = Σ[ f ∈ (X → Y) ] ((x y : X) → f x ≡ f y → x ≡ y)

-- Q, VERBATIM.  Compare Upper's own predicate `P`
-- (src/L/StageCardinal.lagda.md:530-532), which fixes the injection's
-- TARGET at each step's OWN ordinal and buys the band: P carries a
-- per-step infinity hypothesis and targets ⟪ γ ⟫.  Q targets ⟪ α ⟫,
-- the FIXED SITE, and drops the infinity clause.
Q : V ℓ → Type (ℓ-suc ℓ)
Q γ = IsOrd γ → ⟨ γ ∈ˢ sucV α ⟩ → ⟪ Lset γ ⟫ ↪ ⟪ α ⟫

-- Q AT UPPER'S INDUCTION POSITION, TYPE ONLY.  The step type is
-- [LJ-1.617]'s own (agents/tasks/LJ-1-617/Probe617.agda:467-468), and
-- the induction type is `stage-card-upper`'s shape with P replaced by
-- Q (src/L/StageCardinal.lagda.md:565-566).
step-at-Q : Type (ℓ-suc ℓ)
step-at-Q = (γ : V ℓ) → ((δ : V ℓ) → ⟨ δ ∈ˢ γ ⟩ → Q δ) → Q γ

induction-at-Q : Type (ℓ-suc ℓ)
induction-at-Q = (γ : V ℓ) → Q γ

-- THE ACCEPTANCE ROW, hypothetical: the tree's own induction former
-- (src/V/Hierarchy.lagda.md:177-179), the one `Upper` runs, takes a
-- step-at-Q to an induction-at-Q.  This elaborates only if the
-- ascription is right; it proves nothing.
module _ (step : step-at-Q) where
  upper-at-Q : induction-at-Q
  upper-at-Q = ∈-induction step
