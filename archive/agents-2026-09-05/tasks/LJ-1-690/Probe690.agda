{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.690] PROBE.  The forward direction of SameAsGraph, at
-- [LJ-1.678]'s k-value telescope, taking powIter and the UP
-- bridge as HYPOTHESES.  Lands nothing in src/.
--
--   W3              unpacking with an explicit formula argument.
--                   Generic unpack in runs/UNPACK.agda, sealed at
--                   Matrix.matrix in runs/UNPACKAT.agda.
--   THE OBLIGATION  same-as-graph-forward.  Sigma-1 to graph.
--
-- ONE Agda process per run, GHCRTS="-A64m -I0 -M2g", the wide caliber,
-- set on the pane by the program and untouched here.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-690.Probe690 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans; Lset; IsOrd; 𝒟ₒ )
open import L.Coding.Sequence {ℓ} lem using ( LsetGraphAt )
open import L.Ordinal.StageArith {ℓ} lem using ( sucIter )
open import Cubical.Data.Vec using ( lookup; _∷_ )
open import Cubical.Data.Nat using ( _+_ )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁ )

import LJ-1-520.Probe520 {ℓ} lem as P520
import LJ-1-690.runs.DROP {ℓ} lem as DR
import LJ-1-690.runs.UNPACK {ℓ} lem as UK
import LJ-1-690.runs.UNPACKAT {ℓ} lem as UA

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ
module HV = hPropStructure 𝒮ᵥ
module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL using ( _^_ ) renaming ( _⊨ᵐ_ to _⊨_ )

-- Bound.PowIter's hypothesis (src/L/Coding/Bound.lagda.md:147-152).
-- Taken as a hypothesis.  The forward body does not spend it: the
-- hypothesized UP bridge carries graphBndAt to LsetGraphAt.
PowIterHyp : Type (ℓ-suc ℓ)
PowIterHyp = (δ y : V ℓ) → ⟨ y HV.∈ˢ Lset δ ⟩
           → ∥ Σ[ k ∈ ℕ ] ⟨ 𝒟ₒ y HV.∈ˢ Lset (sucIter k δ) ⟩ ∥₁

-- W2: written once at a generic arity and generic slots.
-- The k-value telescope is taken (IsOrd at fst (lookup b γ)).
-- The facts field is not spent: the unpacked K is arbitrary.
module Pin {n : ℕ} (w b : Fin n) (γ : S ^ n) where
  module Sl = P520.Slots w b
  module Mx = Sl.Mx
  private
    M : ℕ
    M = 13 + n
    sh13 : Fin n → Fin M
    sh13 i = suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (i)))))))))))))

  -- The bridge this direction spends.  UP.  Dual of [LJ-1.685]
  -- Bridge (Probe685.agda:66-69), which was DOWN.  Hypothesis.
  -- Graph.up (ProbeLJ1162A.agda:218-222) is this direction and
  -- is not rebuilt.
  Bridge : Type (ℓ-suc ℓ)
  Bridge = (δ : S ^ M)
         → ⟨ δ ⊨ Mx.G.graphBndAt ⟩
         → ⟨ δ ⊨ LsetGraphAt (sh13 w) (sh13 b) ⟩

  same-as-graph-forward-at :
    PowIterHyp →
    IsOrd (fst (lookup b γ)) →
    Bridge →
    ⟨ γ ⊨ fst (P520.levelFo-Σ₁ w b) ⟩ →
    ⟨ γ ⊨ LsetGraphAt w b ⟩
  same-as-graph-forward-at _ _ br hφ =
    PT.rec (snd (γ ⊨ LsetGraphAt w b)) go (A.unpacked hφ)
    where
    module A = UA.At w b γ
    go : UK.Wit A.mat γ → ⟨ γ ⊨ LsetGraphAt w b ⟩
    go wt = DR.drop13 w b γ
              (UK.Wit.x0 wt) (UK.Wit.x1 wt) (UK.Wit.x2 wt) (UK.Wit.x3 wt)
              (UK.Wit.x4 wt) (UK.Wit.x5 wt) (UK.Wit.x6 wt) (UK.Wit.x7 wt)
              (UK.Wit.x8 wt) (UK.Wit.x9 wt) (UK.Wit.x10 wt) (UK.Wit.x11 wt)
              (UK.Wit.x12 wt)
              (br env (A.to-graph (UK.Wit.hφ wt)))
      where
      env = UK.Wit.x0 wt ∷ UK.Wit.x1 wt ∷ UK.Wit.x2 wt ∷ UK.Wit.x3 wt
          ∷ UK.Wit.x4 wt ∷ UK.Wit.x5 wt ∷ UK.Wit.x6 wt ∷ UK.Wit.x7 wt
          ∷ UK.Wit.x8 wt ∷ UK.Wit.x9 wt ∷ UK.Wit.x10 wt ∷ UK.Wit.x11 wt
          ∷ UK.Wit.x12 wt ∷ γ

same-as-graph-forward = Pin.same-as-graph-forward-at
