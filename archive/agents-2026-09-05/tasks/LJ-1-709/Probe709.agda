{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.709] PROBE.  same-as-graph-both: [LJ-1.699]'s equivalence,
-- both directions written out, at the union of the two directions'
-- hypotheses.  Lands nothing in src/.
--
--   FORWARD  supplied by [LJ-1.690], imported, green
--            (LJ-1-690.Probe690, Pin.same-as-graph-forward-at).
--   REVERSE  supplied by [LJ-1.703], imported from the tracked commit
--            (LJ-1-703.Probe703, last line), NOT restated by hand and
--            NOT taken from [LJ-1.685].  This import is the one thing
--            LJ-1.699 could not do: its reverse lived in the sibling
--            worktree LJ-1-685, off every include path
--            (lj-1.699-report.md:22).  [LJ-1.703] re-derived the
--            reverse and its task closed done, so the program
--            committed the file scripts/pod/pod.py:3673 and this
--            worktree carries it.
--   UNION    the union type of LJ-1.699, unchanged
--            (Probe699.agda:47): one hypothesis telescope
--            (powIter, IsOrd at b, UP bridge, DOWN bridge) shared by
--            both conjuncts, concluded as one pair
--            P520.SameAsGraph w b γ.
--
--   W3       whether the two directions genuinely union at one
--            telescope, measured HERE by this very file: the two
--            bridges coexist as two hypothesis arguments at the ONE
--            matrix Mx (arity M = 13 + n, slots sh13) and neither
--            conjunct spends the other's bridge.
--
-- ONE Agda process per run, GHCRTS="-A64m -I0 -M2g", the wide caliber,
-- set on the pane by the program and untouched here.
-- Nothing is postulated.  No hole in this file.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-709.Probe709 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans; IsOrd )
open import Cubical.Data.Vec using ( lookup )
open import Cubical.Data.Nat using ( _+_ )

import LJ-1-520.Probe520 {ℓ} lem as P520
import LJ-1-690.Probe690 {ℓ} lem as P690
import LJ-1-703.Probe703 {ℓ} lem as P703

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ
module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL using ( _^_ ) renaming ( _⊨ᵐ_ to _⊨_ )

-- W2: written once at a generic arity and generic slots, instantiated
-- by nothing: the obligation IS the generic statement.
module Pin {n : ℕ} (w b : Fin n) (γ : S ^ n) where
  module FPin = P690.Pin {n} w b γ
  module RPin = P703.Pin {n} w b γ

  -- THE OBLIGATION.  One telescope carrying the union of the two
  -- directions' hypotheses; the conclusion is the conjunction
  -- P520.SameAsGraph w b γ (Probe520.agda:192-195).  The forward
  -- conjunct drops the DOWN bridge; the reverse conjunct drops the UP
  -- bridge: neither half spends the other half's bridge.
  same-as-graph-both :
    P690.PowIterHyp →
    IsOrd (fst (lookup b γ)) →
    FPin.Bridge →
    RPin.Bridge →
    P520.SameAsGraph w b γ
  same-as-graph-both pow ord up down =
    ( FPin.same-as-graph-forward-at pow ord up
    , RPin.same-as-graph-reverse-at pow ord down )

same-as-graph-both = Pin.same-as-graph-both
