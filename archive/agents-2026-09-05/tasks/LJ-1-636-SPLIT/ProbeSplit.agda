{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.636-split]  HOW FAR DOES THE BILL GET AT AMBIENT ω?
--
-- THE OBLIGATION.  `bill-at-omega`: the strongest consequence of
-- `Devlin55.BoundedSubsetAt` that follows with the AMBIENT set to `ω`
-- and the `sq` parameter instantiated by [LJ-1.636]'s `param-at-ω`,
-- stated as a type with every surviving hypothesis explicit.
--
-- THIS FILE CARRIES NO HOLE AND NO POSTULATE.  Nothing lands in `src/`.
-- It BUILDS NO SQUARE LAW: the one inhabitant used, `squareω`, is
-- already in the tree (src/L/InjChain.lagda.md:184).
--
-- ---------------------------------------------------------------------
-- THE AMBIENT IS `α`, NOT `κ`.  `BoundedSubsetAt`'s telescope
-- (src/L/BoundedSubset.lagda.md:1385-1395) binds TWO ordinals: the
-- cardinal `κ` and the ambient `α`, with `α ∈ κ` and `α ∉ ω`.
-- [LJ-1.636] measured that the `sq` parameter is read at the ambient
-- (its site B, agents/tasks/LJ-1-636/lj-1.636-report.md:27), and
-- `param-at-ω : SqParam ω` types only at `α := ω`.  So this file sets
-- the AMBIENT to `ω` and leaves `κ` free.  Section 4 shows the ambient
-- is exactly where [LJ-1.635]'s at-`ω` half enters, so the brief's
-- premise 4 holds, and that it could enter nowhere else.
--
-- CALIBER.  The program set GHCRTS on this pane; I did not set it.  One
-- Agda process at a time.  The floor was measured before the proof, as
-- the standing clause orders: runs/Floor.agda, runs/floor-2.out, 3.33 s.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-636-SPLIT.ProbeSplit {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ; ∈-irrefl )
open import V.Model {ℓ} using ( ∈sucV-elim )
open import L.Constructible {ℓ} using ( IsOrd; Lset )
open import L.Ordinal {ℓ} using ( ω-ord )
open import L.InjChain {ℓ} lem using ( squareω )
open import L.BoundedSubset {ℓ} lem using ( IsCardinal; _↪_; module Devlin55 )

open import Cubical.Data.Sigma using ( Σ-syntax; _×_ )
import Cubical.Data.Empty as Empty
open import Cubical.HITs.PropositionalTruncation using ( ∥_∥₁ )
open import Cubical.HITs.CumulativeHierarchy.Base using ( setIsSet )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet; _∪_; ⁅_⁆s )
open InfinitySet using ( ω; sucV )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ

-- =====================================================================
-- SECTION 1.  THE THREE HYPOTHESES THAT DIE.
--
-- Setting the ambient to `ω` discharges exactly three of
-- `BoundedSubsetAt`'s parameters, and each is discharged by a term that
-- is already in the tree.  Nothing else in the telescope goes away.
-- =====================================================================

-- The `sq` parameter's value type, copied from its binder
-- (src/L/StageCardinal.lagda.md:17-19).
Sq : S → Type ℓ
Sq δ = Σ[ f ∈ (⟪ δ ⟫ × ⟪ δ ⟫ → ⟪ δ ⟫) ]
         ((u v : ⟪ δ ⟫ × ⟪ δ ⟫) → f u ≡ f v → u ≡ v)

SqParam : S → Type (ℓ-suc ℓ)
SqParam α₀ = (δ : S) → ⟨ δ ∈ˢ sucV α₀ ⟩ → (⟨ δ ∈ˢ ω ⟩ → Empty.⊥) → Sq δ

-- (i) `ordα : IsOrd α` dies into `ω-ord` (src/L/Ordinal.lagda.md:263).
ordα-dies : IsOrd ω
ordα-dies = ω-ord

-- (ii) `α∉ω : ⟨ α ∈ˢ ω ⟩ → ⊥` dies into `∈-irrefl`
-- (src/V/Hierarchy.lagda.md:155).  THIS is the `∈-irrefl ω` the brief's
-- premise 4 names, and at the ambient it is FREE, not a case split.
α∉ω-dies : ⟨ ω ∈ˢ ω ⟩ → Empty.⊥
α∉ω-dies = ∈-irrefl ω

-- (iii) `sq` dies into [LJ-1.636]'s `param-at-ω`.  Re-derived here and
-- NOT imported: `agents/tasks/LJ-1-636/Probe636.agda` is on a SIBLING
-- WORKTREE and is not on this branch.  The two terms below are that
-- probe's lines 377-381 and 391-392, verbatim up to binder names.
collapse-at-ω : (δ : S) → ⟨ δ ∈ˢ sucV ω ⟩ → (⟨ δ ∈ˢ ω ⟩ → Empty.⊥) → δ ≡ ω
collapse-at-ω δ δ∈sucVω infδ =
  ∈sucV-elim {A = ω} {x = δ} (setIsSet δ ω) δ∈sucVω
    (λ δ∈ω → Empty.rec (infδ δ∈ω))
    (λ e → e)

param-at-ω : SqParam ω
param-at-ω δ δ∈suc infδ = subst Sq (sym (collapse-at-ω δ δ∈suc infδ)) squareω

sq-dies : SqParam ω
sq-dies = param-at-ω

-- =====================================================================
-- SECTION 2.  THE FRAME.  Every hypothesis that SURVIVES is a parameter
-- of this module; the three that die are supplied at the application.
-- =====================================================================

module At-ω
  (κ : S) (ordκ : IsOrd κ) (cardκ : IsCardinal κ) (κ∉ω : ⟨ κ ∈ˢ ω ⟩ → Empty.⊥)
  (ω∈κ : ⟨ ω ∈ˢ κ ⟩)
  (x : S) (x⊆Lω : (z : S) → ⟨ z ∈ˢ x ⟩ → ⟨ z ∈ˢ Lset ω ⟩)
  (absorbs : ⟪ Lset ω ∪ ⁅ x ⁆s ⟫ ↪ ⟪ Lset ω ⟫)
  (lam : S) (ordλ : IsOrd lam) (ω∈λ : ⟨ ω ∈ˢ lam ⟩)
  (succλ : (d : S) → ⟨ d ∈ˢ lam ⟩ → ⟨ sucV d ∈ˢ lam ⟩)
  (x∈Lλ : ⟨ x ∈ˢ Lset lam ⟩)
  where

  module B = Devlin55.BoundedSubsetAt
    κ ordκ cardκ κ∉ω
    ω ordα-dies ω∈κ α∉ω-dies
    sq-dies
    x x⊆Lω absorbs
    lam ordλ ω∈λ succλ x∈Lλ

  -- W3's two names, at ambient ω.  BOTH SURVIVE.  They are the
  -- parameters of `Co` (src/L/BoundedSubset.lagda.md:1671-1673),
  -- copied here with the ambient already fixed.  The instantiation
  -- touches neither: the ambient reaches them only through
  -- `UnionKit.X = Lset α ∪ ⁅ x ⁆s` (src/L/BoundedSubset.lagda.md:1149-1150),
  -- which becomes `Lset ω ∪ ⁅ x ⁆s` and stays a hypothesis' subject.
  LevelIn : Type (ℓ-suc ℓ)
  LevelIn = (δ : S) → IsOrd δ → ⟨ δ ∈ˢ B.HS.C.πX ⟩ → ⟨ Lset δ ∈ˢ B.HS.C.πX ⟩

  Cover : Type (ℓ-suc ℓ)
  Cover = (y : S) → ⟨ y ∈ˢ B.HS.M ⟩
        → ∥ Σ[ γ ∈ S ] (IsOrd γ × ⟨ γ ∈ˢ B.HS.C.πX ⟩ × ⟨ B.HS.C.π y ∈ˢ Lset γ ⟩) ∥₁

  conclusion : LevelIn → Cover → ⟨ x ∈ˢ Lset κ ⟩
  conclusion levelIn cover = B.Co.theorem levelIn cover

-- =====================================================================
-- SECTION 3.  THE OBLIGATION.
--
-- The strongest consequence: the bounded-subset lemma's own conclusion,
-- `x ∈ Lset κ`, with the ambient gone from the telescope and the square
-- law paid in full.  Of `BoundedSubsetAt`'s SEVENTEEN parameters four
-- go: the ambient `α` is FIXED to `ω`, and `ordα`, `α∉ω` and `sq` are
-- DISCHARGED by section 1.  Thirteen survive.  `Co`'s `levelIn` and
-- `cover` survive too, so the bill at ambient `ω` costs FIFTEEN.
-- =====================================================================

bill-at-omega :
    (κ : S) (ordκ : IsOrd κ) (cardκ : IsCardinal κ) (κ∉ω : ⟨ κ ∈ˢ ω ⟩ → Empty.⊥)
    (ω∈κ : ⟨ ω ∈ˢ κ ⟩)
    (x : S) (x⊆Lω : (z : S) → ⟨ z ∈ˢ x ⟩ → ⟨ z ∈ˢ Lset ω ⟩)
    (absorbs : ⟪ Lset ω ∪ ⁅ x ⁆s ⟫ ↪ ⟪ Lset ω ⟫)
    (lam : S) (ordλ : IsOrd lam) (ω∈λ : ⟨ ω ∈ˢ lam ⟩)
    (succλ : (d : S) → ⟨ d ∈ˢ lam ⟩ → ⟨ sucV d ∈ˢ lam ⟩)
    (x∈Lλ : ⟨ x ∈ˢ Lset lam ⟩)
  → At-ω.LevelIn κ ordκ cardκ κ∉ω ω∈κ x x⊆Lω absorbs lam ordλ ω∈λ succλ x∈Lλ
  → At-ω.Cover   κ ordκ cardκ κ∉ω ω∈κ x x⊆Lω absorbs lam ordλ ω∈λ succλ x∈Lλ
  → ⟨ x ∈ˢ Lset κ ⟩
bill-at-omega κ ordκ cardκ κ∉ω ω∈κ x x⊆Lω absorbs lam ordλ ω∈λ succλ x∈Lλ =
  At-ω.conclusion κ ordκ cardκ κ∉ω ω∈κ x x⊆Lω absorbs lam ordλ ω∈λ succλ x∈Lλ

-- =====================================================================
-- SECTION 4.  WHICH ORDINAL IS [LJ-1.635]'s `ω`?  THE AMBIENT, NOT `κ`.
--
-- The bill reads `x ⊆ Lset α` and returns `x ∈ Lset κ`, with `α ∈ κ`
-- (src/L/BoundedSubset.lagda.md:1391 and :1737).  So the ordinal whose
-- power set the bill BOUNDS is the AMBIENT `α`, and the module's own
-- `κ` is a cardinal strictly above it.
--
-- [LJ-1.635]'s at-`ω` half is `Concl zf ωʟ`, and `Concl zf κ` is
-- `2^κ = κ⁺` (agents/tasks/LJ-1-635/Probe635.agda:73-76).  Its `ω` is
-- the ordinal BEING BOUNDED, so it is this chapter's ambient.  THE
-- BRIEF'S PREMISE 4 IS RIGHT under that reading, and the term below
-- shows it is the ONLY reading available: if the module's own `κ` were
-- `ω`, the telescope would admit NO ambient at all, because `α ∈ κ`
-- and `α ∉ ω` collide.  The at-`ω` half can enter here through the
-- ambient and nowhere else.
--
-- No site in `src/` picks `κ`: `L.StageBound` is imported once, at
-- src/Everything.lagda.md:396, and nothing consumes it.  `κ` is free
-- here, and the GCH use of this instance is the one that takes
-- `κ := ω⁺`.
-- =====================================================================

no-ambient-at-cardinal-ω :
    (κ : S) → κ ≡ ω
  → (α : S) → ⟨ α ∈ˢ κ ⟩ → (⟨ α ∈ˢ ω ⟩ → Empty.⊥)
  → Empty.⊥
no-ambient-at-cardinal-ω κ κ≡ω α α∈κ α∉ω =
  α∉ω (subst (λ w → ⟨ α ∈ˢ w ⟩) κ≡ω α∈κ)
