{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.723] PROBE.  [LJ-1.713]'s chain, transcribed under its true
-- name.  Lands nothing in src/.
--
--   THE OBLIGATION  below-closed-via, declared at the file's TOP
--                   LEVEL, so the witness meter reads
--                   Probe723.agda::below-closed-via.  713 wrote this
--                   assembly as a member of the frame module At713
--                   (worktree LJ-1-713, Probe713.agda:120-130), and
--                   no obligation name landed in the live tree.  The
--                   transcription hoists the frame from module
--                   parameters to seven explicit arguments and
--                   exports the name where the meter reads it.
--
--   HONEST ARITHMETIC  CompletenessFrom is a HYPOTHESIS here, not a
--                   supply: it is a named TYPE
--                   (Probe679.agda:94-95), its inhabitation is
--                   [LJ-1.700]'s obligation, closed NO-GO and upheld
--                   (review-of-LJ-1-700-1.md:167, :174-175).  This
--                   file neither inhabits nor applies it.  The chain
--                   to Completeness carries three open bills: the two
--                   rows ([LJ-1.711], [LJ-1.712]) and cf itself.
--
-- ONE Agda process per run, GHCRTS wide caliber, set on the pane by
-- the program and untouched here.  Nothing is postulated.  No hole.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-723.Probe723 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ} using ( 𝒮ʟ; IsOrd; Lset )
open import Cubical.Data.Vec using ( lookup )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ∅; module InfinitySet )
open InfinitySet {ℓ} using ( sucV )

import LJ-1-652.Probe652 {ℓ} lem as P652
import LJ-1-679.Probe679 {ℓ} lem as P679
import LJ-1-690.Probe690 {ℓ} lem as P690
import LJ-1-697.Probe697 {ℓ} lem as P697
import LJ-1-706.Probe706 {ℓ} lem as P706
import LJ-1-709.Probe709 {ℓ} lem as P709

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ
module CS = hPropStructure 𝒮ʟ

-- =====================================================================
-- THE FRAME.  [LJ-1.679]'s At telescope, not rebuilt (Probe700's
-- module Spend is the precedent).  from-below and CompletenessFrom
-- are delivered inside this frame, so the assembly is stated inside
-- it, and both are instantiated at the SAME eight arguments.
-- =====================================================================

module At723 (lam : S) (ordλ : IsOrd lam)
  (succλ : (d : S) → ⟨ d ∈ˢ lam ⟩ → ⟨ sucV d ∈ˢ lam ⟩)
  (X : S) (X⊆Lλ : (z : S) → ⟨ z ∈ˢ X ⟩ → ⟨ z ∈ˢ Lset lam ⟩)
  (∅∈λ : ⟨ ∅ ∈ˢ lam ⟩)
  (elem : P652.Frame652.A.Elementary lam ordλ succλ X X⊆Lλ ∅∈λ) where

  module A = P679.At lam ordλ succλ X X⊆Lλ ∅∈λ elem
  module B = P697.At lam ordλ succλ X X⊆Lλ ∅∈λ elem

  -- [LJ-1.709]'s delivered arrow is per-family-instance: one
  -- PowIterHyp (global there), one IsOrd at the b-slot, one UP
  -- bridge, one DOWN bridge, one P520.SameAsGraph w b γ out.
  -- The hoisting carries the three local parts over the family and
  -- pays [LJ-1.679]'s unconditional SameHyp.  W2: the arrow is
  -- called, not rebuilt.
  same-hyp-of :
      (pow : P690.PowIterHyp)
    → ({n : ℕ} (w b : Fin n) (γ : _) → IsOrd (fst (lookup b γ)))
    → ({n : ℕ} (w b : Fin n) (γ : _) → P709.Pin.FPin.Bridge {n} w b γ)
    → ({n : ℕ} (w b : Fin n) (γ : _) → P709.Pin.RPin.Bridge {n} w b γ)
    → P679.SameHyp
  same-hyp-of pow ordb up down {n} w b γ =
    P709.Pin.same-as-graph-both {n} w b γ pow
      (ordb w b γ) (up w b γ) (down w b γ)

  -- THE TWO ROWS, THROUGH THE FIRST ARROW.  below-from-place is
  -- called, not rebuilt.  The target names P697.At's Below spelling
  -- on purpose: this is where 693's step and W3's step must convert.
  below-of :
      ((δ : CS.S) (oδ : IsOrd (fst δ)) → P706.Bound-in-tower δ oδ)
    → ((δ : CS.S) (oδ : IsOrd (fst δ)) → P706.Identified δ oδ)
    → (δ : CS.S) (oδ : IsOrd (fst δ)) → B.Below δ oδ
  below-of bound ident δ oδ =
    P706.below-from-place δ oδ (bound δ oδ) (ident δ oδ)

  -- INTO THE SECOND ARROW.  from-below is called, not rebuilt.
  hier-of :
      ((δ : CS.S) (oδ : IsOrd (fst δ)) → P706.Bound-in-tower δ oδ)
    → ((δ : CS.S) (oδ : IsOrd (fst δ)) → P706.Identified δ oδ)
    → A.HierInStage
  hier-of bound ident =
    B.from-below (below-of bound ident)

  -- THE CHAIN, WITH THE FOURTH ARROW HONEST.  cf is the one open
  -- bill: [LJ-1.700]'s obligation, NO-GO'd, no green term in the
  -- tree.  Everything else is consumed at its delivered address.
  below-closed-via :
      A.CompletenessFrom
    → ((δ : CS.S) (oδ : IsOrd (fst δ)) → P706.Bound-in-tower δ oδ)
    → ((δ : CS.S) (oδ : IsOrd (fst δ)) → P706.Identified δ oδ)
    → (pow : P690.PowIterHyp)
    → ({n : ℕ} (w b : Fin n) (γ : _) → IsOrd (fst (lookup b γ)))
    → ({n : ℕ} (w b : Fin n) (γ : _) → P709.Pin.FPin.Bridge {n} w b γ)
    → ({n : ℕ} (w b : Fin n) (γ : _) → P709.Pin.RPin.Bridge {n} w b γ)
    → A.Completeness
  below-closed-via cf bound ident pow ordb up down =
    cf (same-hyp-of pow ordb up down) (hier-of bound ident)

-- =====================================================================
-- THE OBLIGATION NAME, AT THE TOP LEVEL.  The frame is seven explicit
-- arguments; the body consumes 713's member at its delivered address.
-- The dotted-path spellings are the tree's measured forms: a type
-- through parameterised modules at Probe608.agda:182
-- (W3.Site.At.RecGraph∞ ...), a term discharging module parameters at
-- Probe608.agda:184 (Rows.the-graph ...).
-- =====================================================================

below-closed-via :
    (lam : S) (ordλ : IsOrd lam)
  → (succλ : (d : S) → ⟨ d ∈ˢ lam ⟩ → ⟨ sucV d ∈ˢ lam ⟩)
  → (X : S) (X⊆Lλ : (z : S) → ⟨ z ∈ˢ X ⟩ → ⟨ z ∈ˢ Lset lam ⟩)
  → (∅∈λ : ⟨ ∅ ∈ˢ lam ⟩)
  → (elem : P652.Frame652.A.Elementary lam ordλ succλ X X⊆Lλ ∅∈λ)
  → P679.At.CompletenessFrom lam ordλ succλ X X⊆Lλ ∅∈λ elem
  → ((δ : CS.S) (oδ : IsOrd (fst δ)) → P706.Bound-in-tower δ oδ)
  → ((δ : CS.S) (oδ : IsOrd (fst δ)) → P706.Identified δ oδ)
  → (pow : P690.PowIterHyp)
  → ({n : ℕ} (w b : Fin n) (γ : _) → IsOrd (fst (lookup b γ)))
  → ({n : ℕ} (w b : Fin n) (γ : _) → P709.Pin.FPin.Bridge {n} w b γ)
  → ({n : ℕ} (w b : Fin n) (γ : _) → P709.Pin.RPin.Bridge {n} w b γ)
  → P679.At.Completeness lam ordλ succλ X X⊆Lλ ∅∈λ elem
below-closed-via lam ordλ succλ X X⊆Lλ ∅∈λ elem cf bound ident pow ordb up down =
  At723.below-closed-via lam ordλ succλ X X⊆Lλ ∅∈λ elem cf bound ident
    pow ordb up down
