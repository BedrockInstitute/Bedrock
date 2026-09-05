{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.536] W3.  THE WIDEST UNMEASURED TERM: the formula at `𝒟ₒ-intro`.
--
-- The brief names it: "[LJ-1.520]'s graded formula, applied at 𝒟ₒ-intro
-- for the sequence", and orders it written FIRST, alone, with the
-- obligation omitted.  This file is that.  It answers three questions
-- and every answer is a term rather than a sentence:
--
--   1. WHAT THE DOOR WANTS.  `Door` is written out and ascribed against
--      `𝒟ₒ-intro` itself, so the shape is checked and not paraphrased.
--   2. WHETHER THE GRADED FORMULA FITS IT.  It does not, and the miss
--      is not a coercion away: `no-Δ₀-levelFo` REFUTES the one property
--      the tree's own stage-separation bridge demands.
--   3. WHAT THE DOOR DOES ACCEPT.  `L.Axioms.Separation.AtStage` is a
--      second door, delivered in src/ and named by none of [LJ-1.230],
--      [LJ-1.494], [LJ-1.517], [LJ-1.530] or [LJ-1.532].  It is
--      re-ascribed here, and a formula that passes it is exhibited.
--
-- ONE Agda process per run, GHCRTS="-A64m -I0 -M8g", the wide caliber,
-- set on the pane by the program and untouched here.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-536.runs.W3 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula; Term; con; var; _∈̇_; _≐_; _∨̇_ )
open import FOL.LevyHierarchy using ( Δ₀; δ-∈; δ-≐; δ-∨; Σ₁ )
open import FOL.Manipulation.Bounding using ( BoundedFo )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Definability {ℓ} using ( module DefOf )
open import L.Constructible {ℓ}
  using ( 𝒮ʟ; isL; isL-trans; IsOrd; Lset; 𝒟ₒ; 𝒟ₒ-intro )
open import L.Axioms.Separation {ℓ} lem using ( module AtStage )
open import LJ-1-520.Probe520 {ℓ} lem using ( levelFo-Σ₁ )

open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫; ⟪_⟫↪ )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁ )
import Cubical.Data.Empty as Empty

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL using () renaming ( _⊨ᵐ_ to _⊨_ )


-- ===================================================================
-- 1.  THE DOOR, WRITTEN OUT AND ASCRIBED AGAINST `𝒟ₒ-intro`.
--
-- src/L/Constructible.lagda.md:301-304.  `door` below is the only
-- evidence that `Door` is that premise and not a paraphrase of it: it
-- typechecks exactly when the two types are the same.
-- ===================================================================

Door : V ℓ → V ℓ → Type (ℓ-suc ℓ)
Door A x = ∥ Σ[ φ ∈ Formula ⟪ A ⟫ 1 ] (DefOf.defSet A φ ≡ x) ∥₁

door : (A x : V ℓ) → Door A x → ⟨ x ∈ 𝒟ₒ A ⟩
door = 𝒟ₒ-intro


-- ===================================================================
-- 2.  WHAT [LJ-1.520] DELIVERED, RE-ASCRIBED FROM ITS OWN PROBE.
--
-- agents/tasks/LJ-1-520/Probe520.agda:171-172, and the audit's F1/F3
-- rule (dev/pod/audit-2026-08-20.md:34) says the hypothesis is the type
-- that predecessor delivered.  It is imported rather than restated, so
-- nothing here can drift from it.
-- ===================================================================

graded : {n : ℕ} (w b : Fin n) → Σ[ ψ ∈ Formula S n ] Σ₁ ψ
graded = levelFo-Σ₁


-- ===================================================================
-- 3.  THE MISS, AS A REFUTATION.
--
-- The door of section 1 is fed by exactly one delivered route in src/,
-- and that route wants `Δ₀`, not `Σ₁`: see section 4.  The graded
-- formula HAS no Δ₀ witness, and this is not an unproved claim: `Δ₀`
-- has no constructor whose index is an unbounded existential
-- (src/FOL/LevyHierarchy.lagda.md:47-57), and `levelFo` is thirteen of
-- them (agents/tasks/LJ-1-520/Probe520.agda:167-169).  Agda checks it
-- by absurd pattern.
-- ===================================================================

no-Δ₀-levelFo : {n : ℕ} (w b : Fin n) → Δ₀ (fst (levelFo-Σ₁ w b)) → Empty.⊥
no-Δ₀-levelFo w b ()


-- ===================================================================
-- 4.  THE SECOND DOOR, WHICH IS DELIVERED AND WHICH NO PREDECESSOR
-- NAMED.  src/L/Axioms/Separation.lagda.md:119-135, :199-231.
--
-- `AtStage σ oσ` carves a subset of `Lset σ` out of an EXTERNAL
-- formula over the class carrier, with two hypotheses and no others:
-- the formula is `Δ₀`, and every CONSTANT in it lies in `Lset σ`
-- (`BoundedFo Below`, src/FOL/Manipulation/Bounding.lagda.md:63-79).
-- Membership in the carved set is then satisfaction of that formula,
-- in BOTH directions.  Every row below is an ascription of a delivered
-- term: it typechecks exactly when the type stated is the type src/ has.
-- ===================================================================

module Bridge (σ : V ℓ) (oσ : IsOrd σ) where
  open AtStage σ oσ

  -- the carved set lands in the definable powerset of the stage.
  b-carve∈ : (ψ : Formula ⟪ Lset σ ⟫ 1) → ⟨ carve ψ ∈ 𝒟ₒ (Lset σ) ⟩
  b-carve∈ = carve∈𝒟ₒ

  -- and it stays inside the stage.
  b-carve⊆ : (ψ : Formula ⟪ Lset σ ⟫ 1) (y : V ℓ)
           → ⟨ y ∈ carve ψ ⟩ → ⟨ y ∈ Lset σ ⟩
  b-carve⊆ = carve⊆

  -- the external formula reaches the stage's own syntax.
  b-lift : (φ : Formula S 1) → BoundedFo Below φ → Formula ⟪ Lset σ ⟫ 1
  b-lift = RL.liftFo

  -- THE TWO DIRECTIONS.  This is what makes the door usable: the
  -- carved set is characterised by satisfaction of the ORIGINAL
  -- formula, at the class carrier, where the tree's lemmas live.
  b-in : (φ : Formula S 1) (h : BoundedFo Below φ) (dφ : Δ₀ φ)
         (m : ⟪ Lset σ ⟫) (xL : ⟨ isL (⟪ Lset σ ⟫↪ m) ⟩)
       → ⟨ ((⟪ Lset σ ⟫↪ m , xL) ∷ []) ⊨ φ ⟩
       → ⟨ ⟪ Lset σ ⟫↪ m ∈ carve (RL.liftFo φ h) ⟩
  b-in = imageIn

  b-out : (φ : Formula S 1) (h : BoundedFo Below φ) (dφ : Δ₀ φ)
          (m : ⟪ Lset σ ⟫) (xL : ⟨ isL (⟪ Lset σ ⟫↪ m) ⟩)
        → ⟨ ⟪ Lset σ ⟫↪ m ∈ carve (RL.liftFo φ h) ⟩
        → ⟨ ((⟪ Lset σ ⟫↪ m , xL) ∷ []) ⊨ φ ⟩
  b-out = imageOut


-- ===================================================================
-- 5.  A FORMULA THAT PASSES THE SECOND DOOR, EXHIBITED.
--
-- "z is a member of the constant h, or z is the constant q".  Two
-- constants, both of which the caller must place inside the stage; no
-- quantifier at all, so `Δ₀` is two constructors.  THIS IS THE
-- SUCCESSOR STEP of the sequence, written as syntax: `hierL (sucV γ)`
-- is `hierL γ` with the one pair at γ adjoined.
-- ===================================================================

adjoin : (h q : S) → Formula S 1
adjoin h q = (var zero ∈̇ con h) ∨̇ (var zero ≐ con q)

Δ₀-adjoin : (h q : S) → Δ₀ (adjoin h q)
Δ₀-adjoin h q = δ-∨ δ-∈ δ-≐

module _ (σ : V ℓ) (oσ : IsOrd σ) where
  open AtStage σ oσ using ( Below )

  Below-adjoin : (h q : S) → Below h → Below q → BoundedFo Below (adjoin h q)
  Below-adjoin h q hh hq = ((_ , hh) , (_ , hq))
