{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.637]  W3.  THE WIDEST UNMEASURED TERM, as the brief states it:
-- the debt of `class-pred-debt`, "the whole remaining debt of the
-- campaign as one written type", TYPE ONLY, capped.  This file is
-- that, and nothing else.  It is written FIRST and typechecked
-- ALONE under a cap this task sets at TWO MINUTES.
--
-- THE SPINE.  (iii) is the site fiber, one binary function with its
-- injectivity at ONE ordinal; it is the value half of the band
-- parameter applied at the site (the tree's own spend,
-- src/L/BoundedSubset.lagda.md:1410) and the law chapter's own fiber
-- type `sq` (src/L/Ordinal/SquareLaw.lagda.md:685-688).  Q fixes the
-- injection's TARGET at the site, the predicate [LJ-1.617] ran
-- (agents/tasks/LJ-1-617/Probe617.agda:464-465) and [LJ-1.621]
-- delivered (agents/tasks/LJ-1-621/Probe621.agda:128-129).  The
-- step is the limit step of the assembly; its body is what the final
-- file typechecks.  No term of this file proves anything; the module
-- parameters below are hypothetical.
--
-- CALIBER.  THE PROGRAM SET GHCRTS ON THIS PANE.  I DID NOT SET IT.
-- ONE AGDA PROCESS AT A TIME.

open import Base.Prelude
open import Base.Truth
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫ )
open import Cubical.HITs.CumulativeHierarchy.Constructions using ( module InfinitySet )
open import L.Constructible using ( IsOrd; Lset )
import Cubical.Data.Empty as Empty

module LJ-1-637.runs.W3 {ℓ : Level} (α₀ : V ℓ) where

open InfinitySet using ( ω; sucV )
open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ; ∈-induction )
open import Cubical.Data.Sigma using ( Σ-syntax )

open hPropStructure 𝒮ᵥ using ( _∈ˢ_ )

-- The injection type, local, the tree's own shape
-- (src/L/StageCardinal.lagda.md:243-246).
_↪_ : Type ℓ → Type ℓ → Type ℓ
X ↪ Y = Σ[ f ∈ (X → Y) ] ((x y : X) → f x ≡ f y → x ≡ y)

-- (iii), THE EXACT TYPE: the site fiber at the site.
SiteFiber : V ℓ → Type ℓ
SiteFiber β = Σ[ f ∈ (⟪ β ⟫ × ⟪ β ⟫ → ⟪ β ⟫) ]
  ((u v : ⟪ β ⟫ × ⟪ β ⟫) → f u ≡ f v → u ≡ v)

-- Q, THE PREDICATE: the injection's target fixed at the site.
Q : V ℓ → Type (ℓ-suc ℓ)
Q γ = IsOrd γ → ⟨ γ ∈ˢ sucV α₀ ⟩ → ⟪ Lset γ ⟫ ↪ ⟪ α₀ ⟫

-- THE STEP TYPE: the limit step of the assembly, (iii) as a
-- hypothesis, the branch as the induction hypothesis.
step-at-Q : Type (ℓ-suc ℓ)
step-at-Q = SiteFiber α₀
  → (γ : V ℓ) → ((δ : V ℓ) → ⟨ δ ∈ˢ γ ⟩ → Q δ) → Q γ

-- THE OBLIGATION TYPE: the debt, (iii) the only remaining hypothesis.
class-pred-debt-type : Type (ℓ-suc ℓ)
class-pred-debt-type = SiteFiber α₀ → (γ : V ℓ) → Q γ

-- THE ACCEPTANCE ROW, hypothetical: the tree's own induction former
-- (src/V/Hierarchy.lagda.md:177-179) takes a step-at-Q to the
-- induction.  This elaborates only if the ascription is right; it
-- proves nothing.
module _ (step : step-at-Q) where
  class-pred-debt : class-pred-debt-type
  class-pred-debt iii = ∈-induction (step iii)
