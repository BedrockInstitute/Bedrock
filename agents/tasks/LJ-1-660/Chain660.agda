{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.660] PROBE, SECOND FILE.  The chain that stands `levelIn` on
-- [LJ-1.646]'s keystone and ONE level-hood formula, and on nothing else.
-- It runs in agents/tasks/LJ-1-660/ and lands nothing in src/.
--
-- WHY IT IS A SEPARATE FILE AND NOT A SECTION OF `Probe660.agda`.
-- MEASURED, not preferred.  With [LJ-1.653] imported into `Probe660.agda`
-- the peak went from 1,572,847,616 bytes to 1,826,635,776, which is 85 %
-- of the 2,147,483,648-byte wide cap (`runs/p-11.out` against
-- `runs/p-9.out`).  Acceptance runs ONE Agda process per target
-- (`scripts/pod/accept.py:165-167`), so two files under 75 % beat one
-- file at 85 % on a machine the pod shares.  The split changes no
-- mathematics: this file imports the same four probes and adds nothing
-- of its own beyond the composition below.
--
-- THE CHAIN, IN ONE SENTENCE.  [LJ-1.653] reduced step 4 AT ORDINALS to
-- one level-hood formula's soundness and completeness plus [LJ-1.647]'s
-- step 2; [LJ-1.654] discharged the fifth fact; [LJ-1.647] reduced step 2
-- to the keystone.  Composed, `levelIn` takes the keystone and the hood
-- formula, and NOTHING ELSE.
--
-- THE BRIEF'S PREMISE 4 DOES NOT BITE.  It says [LJ-1.653]'s note 3 is
-- stale about `PiReflectsOrd`.  This file takes [LJ-1.653]'s step 4
-- REDUCTION only, which is independent of that note and is green in its
-- own file (agents/tasks/LJ-1-653/lj-1.653-report.md:3).
--
-- Nothing is postulated.  Nothing is holed.  Nothing lands in src/.
-- ONE Agda process per run, GHCRTS="-A64m -I0 -M2g", the wide caliber,
-- set on the pane by the program and untouched here.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-660.Chain660 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ} using ( IsOrd; Lset )
open import L.BoundedSubset {ℓ} lem using ( module HullStage )
open import V.Collapse {ℓ} using ( module Collapse )

import LJ-1-647.Probe647
import LJ-1-649.Probe649
import LJ-1-653.Probe653
import LJ-1-654.Probe654

open import Cubical.Data.Sigma using ( Σ-syntax; _×_ )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ∅; module InfinitySet )
open InfinitySet using ( sucV )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ

module P647 = LJ-1-647.Probe647 {ℓ} lem
module P649 = LJ-1-649.Probe649 {ℓ} lem
module P653 = LJ-1-653.Probe653 {ℓ} lem
module P654 = LJ-1-654.Probe654 {ℓ} lem

module AtSite (lam : S) (ordλ : IsOrd lam)
  (succλ : (d : S) → ⟨ d ∈ˢ lam ⟩ → ⟨ sucV d ∈ˢ lam ⟩)
  (X : S) (X⊆L : (x : S) → ⟨ x ∈ˢ X ⟩ → ⟨ x ∈ˢ Lset lam ⟩)
  (∅∈λ : ⟨ ∅ ∈ˢ lam ⟩) where

  module Site = HullStage lam ordλ succλ X X⊆L ∅∈λ
  module A647 = P647.HullStage lam ordλ succλ X X⊆L ∅∈λ
  module A649 = P649.HullStage lam ordλ succλ X X⊆L ∅∈λ
  module A653 = P653.HullStage lam ordλ succλ X X⊆L ∅∈λ
  module A654 = P654.HullStage lam ordλ succλ X X⊆L ∅∈λ

  -- STEP 4 AT ORDINALS, FROM [LJ-1.653], WITH [LJ-1.647]'s STEP 2 FED IN.
  -- `step4-at-ord-pf` is agents/tasks/LJ-1-653/Probe653.agda's own term
  -- (its top-level `step4-at-ord-status` at :295-306 is this one).
  step4-from-keystone
    : (φ₀ : Formula (⊥* {ℓ-suc ℓ}) 2)
    → A653.HoodCompleteP φ₀ → A653.HoodSoundP φ₀
    → A647.LsetCodeOrd → A649.PiCommuteLsetOrd
  step4-from-keystone φ₀ cp sp lco =
    A653.step4-at-ord-pf φ₀ cp sp (A647.hull-closed-lset lco)

  -- THE WHOLE OF `levelIn`, ON TWO OBJECTS.  `A654.fifth` is
  -- [LJ-1.649]'s own `PiReflectsOrd` inhabited
  -- (agents/tasks/LJ-1-654/Probe654.agda:366-367), so the fifth fact
  -- enters by import and is nowhere restated.
  levelin-from-keystone-and-hood
    : (φ₀ : Formula (⊥* {ℓ-suc ℓ}) 2)
    → A653.HoodCompleteP φ₀ → A653.HoodSoundP φ₀
    → A647.LsetCodeOrd
    → (δ : S) → IsOrd δ → ⟨ δ ∈ˢ Site.C.πX ⟩ → ⟨ Lset δ ∈ˢ Site.C.πX ⟩
  levelin-from-keystone-and-hood φ₀ cp sp lco =
    A649.levelin-from-647-ord-commute A654.fifth (A647.hull-closed-lset lco)
      (step4-from-keystone φ₀ cp sp lco)

  -- AND THE KEYSTONE MAY BE TRUNCATED, which [LJ-1.647] measured
  -- (agents/tasks/LJ-1-647/Probe647.agda:171-173).  [LJ-1.646] need not
  -- choose a code.  The truncated keystone does NOT reach [LJ-1.653]'s
  -- step 4, which wants the untruncated `HullClosedLsetOrd`, so this
  -- variant keeps step 4 as its own hypothesis.
  levelin-from-truncated-keystone
    : A647.LsetCodeOrd∥ → A649.PiCommuteLsetOrd
    → (δ : S) → IsOrd δ → ⟨ δ ∈ˢ Site.C.πX ⟩ → ⟨ Lset δ ∈ˢ Site.C.πX ⟩
  levelin-from-truncated-keystone lco =
    A649.levelin-from-647-ord-commute A654.fifth (A647.hull-closed-lset∥ lco)

  -- THE REAL CONSUMER TAKES IT.  `Site.Condense` is
  -- src/L/BoundedSubset.lagda.md:916-918 itself and its FIRST parameter
  -- is `levelIn`.  `cover` stays a hypothesis: it is unbuilt, and
  -- [LJ-1.654] section 5 built only its `IsOrd γ` conjunct.
  module FeedTheSite
    (φ₀ : Formula (⊥* {ℓ-suc ℓ}) 2)
    (cp : A653.HoodCompleteP φ₀) (sp : A653.HoodSoundP φ₀)
    (lco : A647.LsetCodeOrd)
    (cover : (y : S) → ⟨ y ∈ˢ Site.M ⟩
           → ∥ Σ[ γ ∈ S ]
                 (IsOrd γ × ⟨ γ ∈ˢ Site.C.πX ⟩ × ⟨ Site.C.π y ∈ˢ Lset γ ⟩) ∥₁)
    where
    module Cn =
      Site.Condense (levelin-from-keystone-and-hood φ₀ cp sp lco) cover

-- =====================================================================
-- THE TOP LEVEL, where the witness meter reads a name
-- (`witness = Target.<dotted-name>`, scripts/pod/witness.py:278).
-- =====================================================================

levelin-from-keystone-and-hood : (lam : S) (ordλ : IsOrd lam)
  (succλ : (d : S) → ⟨ d ∈ˢ lam ⟩ → ⟨ sucV d ∈ˢ lam ⟩)
  (X : S) (X⊆L : (x : S) → ⟨ x ∈ˢ X ⟩ → ⟨ x ∈ˢ Lset lam ⟩)
  (∅∈λ : ⟨ ∅ ∈ˢ lam ⟩)
  (φ₀ : Formula (⊥* {ℓ-suc ℓ}) 2)
  → AtSite.A653.HoodCompleteP lam ordλ succλ X X⊆L ∅∈λ φ₀
  → AtSite.A653.HoodSoundP lam ordλ succλ X X⊆L ∅∈λ φ₀
  → AtSite.A647.LsetCodeOrd lam ordλ succλ X X⊆L ∅∈λ
  → (δ : S) → IsOrd δ
  → ⟨ δ ∈ˢ Collapse.πX (HullStage.M lam ordλ succλ X X⊆L ∅∈λ) ⟩
  → ⟨ Lset δ ∈ˢ Collapse.πX (HullStage.M lam ordλ succλ X X⊆L ∅∈λ) ⟩
levelin-from-keystone-and-hood lam ordλ succλ X X⊆L ∅∈λ =
  AtSite.levelin-from-keystone-and-hood lam ordλ succλ X X⊆L ∅∈λ
