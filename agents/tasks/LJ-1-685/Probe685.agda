{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.685] PROBE.  The reverse direction of SameAsGraph, at
-- [LJ-1.678]'s k-value, taking powIter and [LJ-1.681]'s bridge as
-- HYPOTHESES.  Lands nothing in src/.
--
--   W3              packing with an explicit formula argument after
--                   the bridge.  Generic pack in runs/PACK.agda,
--                   instantiated at a SEALED matrix in runs/PACKAT.agda.
--   THE OBLIGATION  same-as-graph-reverse.  Graph to Sigma-1.
--
-- ONE Agda process per run, GHCRTS="-A64m -I0 -M2g", the wide caliber,
-- set on the pane by the program and untouched here.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-685.Probe685 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans; Lset; IsOrd; 𝒟ₒ )
open import L.Axioms.Numerals {ℓ} using ( numeralL )
open import L.Coding.Sequence {ℓ} lem using ( LsetGraphAt )
open import L.Ordinal.StageArith {ℓ} lem using ( sucIter )
open import Cubical.Data.Vec using ( lookup )
open import Cubical.Data.Nat using ( _+_ )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁ )

import LJ-1-520.Probe520 {ℓ} lem as P520
import LJ-1-685.runs.LIFT {ℓ} lem as LF
import LJ-1-685.runs.PINS {ℓ} lem as PN
import LJ-1-685.runs.TRANS {ℓ} lem as TR
import LJ-1-685.runs.PACKAT {ℓ} lem as PA

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ
module HV = hPropStructure 𝒮ᵥ
module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL using ( _^_ ) renaming ( _⊨ᵐ_ to _⊨_ )

-- Bound.PowIter's hypothesis (src/L/Coding/Bound.lagda.md:147-152).
-- Taken as a hypothesis.  The reverse body does not spend it: the
-- hypothesized bridge carries LsetGraphAt to graphBndAt.
PowIterHyp : Type (ℓ-suc ℓ)
PowIterHyp = (δ y : V ℓ) → ⟨ y HV.∈ˢ Lset δ ⟩
           → ∥ Σ[ k ∈ ℕ ] ⟨ 𝒟ₒ y HV.∈ˢ Lset (sucIter k δ) ⟩ ∥₁

-- W2: written once at a generic arity and generic slots.
-- k-value instantiates at fst (lookup b γ).  No fixed form.
module Pin {n : ℕ} (w b : Fin n) (γ : S ^ n) where
  module Sl = P520.Slots w b
  module Mx = Sl.Mx
  private
    M : ℕ
    M = 13 + n
    sh13 : Fin n → Fin M
    sh13 i = suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (i)))))))))))))

  -- [LJ-1.681]'s bridge, the type [LJ-1.684] restated
  -- (Probe684.agda:69-72).  Hypothesis.  DOWN, one environment.
  Bridge : Type (ℓ-suc ℓ)
  Bridge = (δ : S ^ M)
         → ⟨ δ ⊨ LsetGraphAt (sh13 w) (sh13 b) ⟩
         → ⟨ δ ⊨ Mx.G.graphBndAt ⟩

  same-as-graph-reverse-at :
    PowIterHyp →
    IsOrd (fst (lookup b γ)) →
    Bridge →
    ⟨ γ ⊨ LsetGraphAt w b ⟩ →
    ⟨ γ ⊨ fst (P520.levelFo-Σ₁ w b) ⟩
  same-as-graph-reverse-at _ ob br hG =
    A.to-levelFo (A.packed (A.from-conj T.htrans P.hpins hgraph))
    where
    module T = TR.At w b γ ob
    module P = PN.At w b γ T.kk
    module A = PA.At w b γ T.kk
    t0 = numeralL 0 ; t1 = numeralL 1 ; t2 = numeralL 2 ; t3 = numeralL 3
    t4 = numeralL 4 ; t5 = numeralL 5 ; t6 = numeralL 6 ; t7 = numeralL 7
    t8 = numeralL 8 ; t9 = numeralL 9 ; t10 = numeralL 10 ; t11 = numeralL 11
    hgraph : ⟨ T.env ⊨ Mx.G.graphBndAt ⟩
    hgraph = br T.env (LF.lift13 w b γ t0 t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 T.kk hG)

same-as-graph-reverse = Pin.same-as-graph-reverse-at
