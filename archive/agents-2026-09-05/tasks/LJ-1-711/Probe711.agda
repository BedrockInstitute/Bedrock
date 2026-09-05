{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.711] PROBE.  The placement row, priced for truth, then measured.
-- Lands nothing in src/.
--
--   THE OBLIGATION  bound-in-tower.  NOT INHABITED HERE BY DESIGN.
--                   review-of-bound-in-tower.md states the stop.
--   DELIVERED       RestatedRow: the brief's type, verbatim, at the
--                   [LJ-1.698] frame.  Nothing rebuilt (W2): step is
--                   [LJ-1.693]'s, bound-of is [LJ-1.698]'s, and the
--                   limit-supply type is [LJ-1.710]'s, imported.
--                   raise1 / climb: green ceiling planks.  Any future
--                   positive placement, and either corrected shape,
--                   walks its ceilings up through these two lines;
--                   they are new here and shared, so they are written
--                   once at the generic carrier (W2).
--                   leaf-floor: the leaf membership every constant
--                   contributes to mkBoundedFo, read off src directly.
--   SUPPLY          [LJ-1.710] reports NO-GO on bound2-in-limit and
--                   delivers the statement as a well-formed Type plus
--                   a green merge at an own-name family
--                   (lj-1.710-report.md:5-8).  Per the coder clause
--                   that report is taken as the verdict and that Type
--                   is taken as the supply, named Supply710 below.
--                   It is never inhabited here.
--
-- ONE Agda process per run, GHCRTS wide caliber, set on the pane by
-- the program and untouched here.  Nothing is postulated.  No hole.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-711.Probe711 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Model {ℓ} using ( self∈sucV )
open import L.Constructible {ℓ}
  using ( 𝒮ʟ; isL; IsOrd; Lset; Lset-mono )
open import L.Stage {ℓ} lem using ( stage; stage-mem )
open import L.Ordinal {ℓ} using ( bound2 )
open import LJ-1-693.Probe693 {ℓ} lem using ( step )
import LJ-1-698.Probe698 {ℓ} lem as P698
import LJ-1-710.Probe710 {ℓ} as P710

open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( _∈ₛ_ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet )
open InfinitySet using ( sucV )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ
module CS = hPropStructure 𝒮ʟ

-- =====================================================================
-- SECTION 1.  THE BRIEF'S ROW, RESTATED VERBATIM AT ITS FRAME.
--
-- Probe706.agda:65-67 named this type for a general δ-pair; the brief
-- names it at γ oγ hγ.  The type is what [LJ-1.706]'s reduction
-- consumes (below-from-place, Probe706.agda:78-83); the reduction is
-- not rebuilt (W2).
-- =====================================================================

Restated-row : (γ : S) (oγ : IsOrd γ) (hγ : ⟨ isL γ ⟩) → Type (ℓ-suc ℓ)
Restated-row γ oγ hγ =
  ⟨ fst (P698.bound-of γ oγ hγ) ∈ˢ step 3 γ ⟩

-- =====================================================================
-- SECTION 2.  THE SUPPLY AND THE WALL, AS TYPES.
--
-- Verbatim [LJ-1.710] Probe710.agda:47-55.  The tree cannot fund this
-- today: the parity between a writable family and bound2's
-- where-bound family is measured inaccessible and unconvertible
-- (agents/tasks/LJ-1-710/runs/t-e1.out:5-9,
-- agents/tasks/LJ-1-710/runs/t-paths2.out:5-8).  This dispatch does
-- not rebuild it and does not inhabit it.
-- =====================================================================

Supply710 : Type (ℓ-suc ℓ)
Supply710 =
    (α : S) (Lim : P710.IsLimit α)
    (σ₁ σ₂ : S) (o₁ : IsOrd σ₁) (o₂ : IsOrd σ₂)
    (h₁ : ⟨ σ₁ ∈ₛ α ⟩) (h₂ : ⟨ σ₂ ∈ₛ α ⟩)
  → ⟨ fst (bound2 σ₁ σ₂ o₁ o₂) ∈ₛ α ⟩

-- Even fully funded, the supply does not reach this obligation: the
-- ceilings on the way are successor stages such as `step k γ`, and a
-- union-closed LIMIT clause never instances against them.  The brief's
-- premise 5 supplies merge interiority; nothing here pretends it
-- closes a successor-ceiling climb.

-- =====================================================================
-- SECTION 3.  GREEN PLANKS FOR ANY CEILING CLIMB.  Generic carrier:
-- any σ, any x.  Two one-liners and their iteration.
-- =====================================================================

raise1 : (σ : S) {x : S} → ⟨ x ∈ˢ Lset σ ⟩ → ⟨ x ∈ˢ Lset (sucV σ) ⟩
raise1 σ x∈ = Lset-mono (self∈sucV σ) x∈

-- Two and three raises composed, since every ceiling this row meets
-- sits at most three successors above any ceiling it already has.
-- Consumers compose further applications freely; nothing here needs
-- numeral arithmetic, which keeps every reduction judgmental.

raise2 : (σ : S) {x : S}
       → ⟨ x ∈ˢ Lset σ ⟩ → ⟨ x ∈ˢ Lset (sucV (sucV σ)) ⟩
raise2 σ h = raise1 (sucV σ) (raise1 σ h)

raise3 : (σ : S) {x : S}
       → ⟨ x ∈ˢ Lset σ ⟩ → ⟨ x ∈ˢ Lset (sucV (sucV (sucV σ))) ⟩
raise3 σ h = raise1 (sucV (sucV σ)) (raise2 σ h)

-- The same fact read at a constant, straight out of src: this is the
-- exact certificate the con-case of mkBoundedTm hands back, verbatim
-- its components (src/L/Axioms/Separation.lagda.md:431-433, from
-- src/L/Stage.lagda.md:188-189).
leaf-floor : (c : CS.S) → ⟨ fst c ∈ˢ Lset (stage (fst c) (c .snd)) ⟩
leaf-floor c = stage-mem (fst c) (c .snd)

-- =====================================================================
-- SECTION 4.  WHAT IS DELIBERATELY ABSENT.
--
-- No term named `bound-in-tower` stands here.  The brief's premise 5
-- funds the merge at limits; the tree measures (review-of-
-- bound-in-tower.md) that even one node of the placement recursion
-- asks the parity question at a successor ceiling, and that the whole
-- row overshoots `step 3 γ` once relativize's inserted constants are
-- counted at their depths.  The stop, its D-10 pricing, and the exact
-- step the bound reaches live in review-of-bound-in-tower.md, which
-- is the critic's input.
-- =====================================================================
