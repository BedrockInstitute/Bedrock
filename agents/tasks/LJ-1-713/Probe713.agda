{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.713] PROBE.  The chain from the two rows toward Completeness,
-- assembled once at one frame.  Lands nothing in src/.
--
--   THE OBLIGATION  below-closed.  NOT INHABITED.
--                   review-of-below-closed.md states the stop: the
--                   brief's fourth supply, [LJ-1.679]'s
--                   CompletenessFrom, is a named TYPE
--                   (Probe679.agda:94-95), not a term, and the
--                   campaign's own dispatch to inhabit it,
--                   [LJ-1.700]'s completeness-from-hier, closed
--                   NO-GO and the critic upheld it
--                   (review-of-LJ-1-700-1.md:145-150).  This run
--                   measured the same fact from the composition side:
--                   runs/floor-1.out:30, [CannotApply] on
--                   A.CompletenessFrom, which is not a function.
--
--   DELIVERED       same-hyp-of:  [LJ-1.709]'s delivered telescope,
--                   hoisted over the family {n} w b gamma, producing
--                   [LJ-1.679]'s unconditional SameHyp.  GREEN: the
--                   floor run accepted it against A.CompletenessFrom's
--                   first input (runs/floor-1.out:30-40, the one
--                   error is the hole, not this argument).
--                   below-of / hier-of: the two rows, through
--                   [LJ-1.706]'s green below-from-place
--                   (Probe706.agda:78), into [LJ-1.697]'s green
--                   from-below (Probe697.agda:81).  This half also
--                   forces the two spellings of `step` (693's, in
--                   P706.Below, and W3's, in P697.At.Below) to one
--                   convertibility, since S = V l by record literal
--                   (src/V/Hierarchy.lagda.md:78-84).
--                   below-closed-via: the full chain with the fourth
--                   arrow taken as the explicit hypothesis it is,
--                   (cf : A.CompletenessFrom).  One frame, all four
--                   consumed, one open bill: cf's inhabitation,
--                   [LJ-1.700]'s obligation, still open.
--
-- ONE Agda process per run, GHCRTS wide caliber, set on the pane by
-- the program and untouched here.  Nothing is postulated.  No hole.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-713.Probe713 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

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

module At713 (lam : S) (ordλ : IsOrd lam)
  (succλ : (d : S) → ⟨ d ∈ˢ lam ⟩ → ⟨ sucV d ∈ˢ lam ⟩)
  (X : S) (X⊆Lλ : (z : S) → ⟨ z ∈ˢ X ⟩ → ⟨ z ∈ˢ Lset lam ⟩)
  (∅∈λ : ⟨ ∅ ∈ˢ lam ⟩)
  (elem : P652.Frame652.A.Elementary lam ordλ succλ X X⊆Lλ ∅∈λ) where

  module A = P679.At lam ordλ succλ X X⊆Lλ ∅∈λ elem
  module B = P697.At lam ordλ succλ X X⊆Lλ ∅∈λ elem

  -- [LJ-1.709]'s delivered arrow is per-family-instance: one
  -- PowIterHyp (global there), one IsOrd at the b-slot, one UP
  -- bridge, one DOWN bridge, one P520.SameAsGraph w b gamma out.
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
-- THE OBLIGATION NAME IS ABSENT ON PURPOSE.  below-closed at the
-- brief's type, two hypotheses and no fourth argument, would have to
-- inhabit A.CompletenessFrom to reach Completeness, and no such term
-- exists: Probe679.agda:94-95 names a type, Probe700.agda:76-79
-- records the obstruction, review-of-LJ-1-700-1.md:145-150 upholds
-- the NO-GO, and runs/floor-1.out:30 measures the [CannotApply] at
-- this frame.  See review-of-below-closed.md.
-- =====================================================================
