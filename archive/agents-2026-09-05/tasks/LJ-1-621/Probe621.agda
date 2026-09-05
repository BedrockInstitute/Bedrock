{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.621]  FIX UPPER'S TARGET AT THE SITE ALPHA, the route [LJ-1.617]
-- named.
--
-- THE OBLIGATION is `upper-at-site` (section 4): from THE PAIRING THE
-- RE-RUN INDUCTION NEEDS, the site fiber (ONE binary function with its
-- injectivity at ONE alpha), it delivers `Upper`'s induction re-run
-- with the predicate's target FIXED at the site alpha.  The predicate
-- is [LJ-1.617]'s Q, verbatim
-- (agents/tasks/LJ-1-617/Probe617.agda:464-465), and it is stated
-- alone, first, capped, in runs/W3.agda:44-45.
--
-- [LJ-1.617]'s PROBE ALREADY BUILDS THE RE-RUN INDUCTION:
-- `site-stage-card = ∈-induction step` at Q
-- (agents/tasks/LJ-1-617/Probe617.agda:470-471).  This file therefore
-- IMPORTS it and restates nothing, per the brief's order.  What this
-- task adds is the packaging the brief names: the induction's demand
-- on ingredient (iii) is made EXPLICIT as the type of the one argument
-- `upper-at-site` takes, so the pairing the induction then needs is
-- read off the obligation itself.
--
-- NOTHING LANDED IN src/.  NO POSTULATE.  NO HOLE IN THE FINAL FORM,
-- so every row is a measurement.
--
-- CALIBER.  THE PROGRAM SET GHCRTS ON THIS PANE.  I DID NOT SET IT.
-- ONE AGDA PROCESS AT A TIME.  Caps are set and reported per run in
-- `runs/`.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫ )
open import Cubical.HITs.CumulativeHierarchy.Constructions using ( module InfinitySet )
open import Cubical.Data.Sigma using ( Σ-syntax )
open import L.Constructible using ( IsOrd; Lset )
import Cubical.Data.Empty as Empty

module LJ-1-621.Probe621 {ℓ : Level} (lem : LEM (ℓ-suc ℓ))
  (α : V ℓ) (oα : IsOrd α)
  (α∉ω : ⟨ α ∈ InfinitySet.ω {ℓ} ⟩ → Empty.⊥) where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Model {ℓ} using ( self∈sucV )
open import LJ-1-594.runs.W3 using ( SqParam )
import LJ-1-617.Probe617
import LJ-1-621.runs.W3 {ℓ} α as W3

open hPropStructure 𝒮ᵥ using ( _∈ˢ_ )
open InfinitySet using ( sucV )

-- =====================================================================
-- SECTION 1.  THE INJECTION TYPE, LOCAL.  The tree's own shape
-- (src/L/StageCardinal.lagda.md:243-246, restated at
-- src/L/BoundedSubset.lagda.md:1365-1368 and at
-- agents/tasks/LJ-1-617/Probe617.agda:107-108).  Stated here because
-- the type of the obligation is written before any module
-- instantiation is in scope.
-- =====================================================================

_↪_ : Type ℓ → Type ℓ → Type ℓ
X ↪ Y = Σ[ f ∈ (X → Y) ] ((x y : X) → f x ≡ f y → x ≡ y)

-- =====================================================================
-- SECTION 2.  THE PAIRING THE RE-RUN INDUCTION THEN NEEDS.  The site
-- fiber: one binary function with its injectivity at ONE ordinal.  It
-- is the type [LJ-1.617]'s telescope binds inline
-- (agents/tasks/LJ-1-617/Probe617.agda:64-66), the value half of
-- `SqParam` applied at the site (the tree's own spend,
-- src/L/BoundedSubset.lagda.md:1410), and the tree's own fiber type
-- `sq` (src/L/Ordinal/SquareLaw.lagda.md:685-688) under a third name
-- to keep the two `sq`s apart ([LJ-1.604]'s naming hazard).
-- =====================================================================

SiteFiber : V ℓ → Type ℓ
SiteFiber β = Σ[ f ∈ (⟪ β ⟫ × ⟪ β ⟫ → ⟪ β ⟫) ]
  ((u v : ⟪ β ⟫ × ⟪ β ⟫) → f u ≡ f v → u ≡ v)

-- And the predicate this file delivers the induction at is the
-- ALONE-TYPECHECKED W3 row, tied by refl so the two cannot drift.
Q-spelled : (γ : V ℓ) → W3.Q γ
          ≡ (IsOrd γ → ⟨ γ ∈ˢ sucV α ⟩ → ⟪ Lset γ ⟫ ↪ ⟪ α ⟫)
Q-spelled γ = refl

-- =====================================================================
-- SECTION 3.  THE RE-RUN INDUCTION, IMPORTED AND NOT RESTATED.
-- [LJ-1.617] runs `∈-induction step` at Q with the target fixed at the
-- site (agents/tasks/LJ-1-617/Probe617.agda:467-471); the step
-- (sections 4 and 5 there) counts every member stage's formulas into
-- ⟪ α ⟫ through `Bound` instantiated ONCE, at the site, on the site
-- fiber (agents/tasks/LJ-1-617/Probe617.agda:126-245, applied at
-- :255-256).  The instantiation below feeds it the one argument its
-- telescope wants: the pairing at the site.
-- =====================================================================

module Run (iii : SiteFiber α) where

  module P617 = LJ-1-617.Probe617 lem α oα α∉ω iii

  -- The imported predicate IS the alone-typechecked Q.
  Q-is-617s : (γ : V ℓ) → W3.Q γ ≡ P617.Q γ
  Q-is-617s γ = refl

  -- The re-run induction itself, imported: the same `∈-induction`
  -- `Upper` runs (src/L/StageCardinal.lagda.md:566), at the predicate
  -- whose target is the FIXED SITE (Probe617.agda:470-471).
  re-run : (γ : V ℓ) → W3.Q γ
  re-run = P617.site-stage-card

-- =====================================================================
-- SECTION 4.  THE OBLIGATION.  Upper's induction re-run with its
-- predicate's target fixed at the site alpha, and the pairing it then
-- needs as the ONE hypothesis of the term: everything else the tree's
-- own `Upper` spends the band on is gone.  Compare `P`
-- (src/L/StageCardinal.lagda.md:530-532) and its consumer's reading at
-- gamma = alpha (src/L/BoundedSubset.lagda.md:1513).
-- =====================================================================

upper-at-site : SiteFiber α → (γ : V ℓ) → W3.Q γ
upper-at-site iii = Run.re-run iii

-- 4.2  THE BILL'S OWN READING at gamma = alpha, the one grain
--      src/L/BoundedSubset.lagda.md:1513 consumes.
upper-at-site-α : SiteFiber α → ⟪ Lset α ⟫ ↪ ⟪ α ⟫
upper-at-site-α iii = upper-at-site iii α oα (self∈sucV α)

-- =====================================================================
-- SECTION 5.  ORIENTATION.  The band product pays the site demand, so
-- the demand this term states is the weaker one.  This row mirrors the
-- tree's own application at src/L/BoundedSubset.lagda.md:1410.
-- =====================================================================

family-pays-the-site : SqParam α → SiteFiber α
family-pays-the-site fam = fam α (self∈sucV α) α∉ω
