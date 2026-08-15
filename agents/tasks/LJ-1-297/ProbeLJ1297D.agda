{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.297] probe D.  WHAT IS ACTUALLY LEFT IN `AmbientStep`.
--
-- Probe C built the reading transport at the FULL class.  This probe
-- spends it: it SUPPLIES all six of `AmbientStep`'s readings at the
-- AMBIENT carrier, from `[LJ-1.238]`'s generic sequence coding, which
-- delivers them at the INNER reading.
--
-- With the six supplied, `AmbientStep`'s telescope keeps ONE open slot
-- besides the Def-step trio: `q`.  So the residue is `q` ALONE, and `q`
-- is refuted (probe A, probe B).  The phase's obligation is `q'` and
-- nothing beside it.
--
-- ONE agda process under GHCRTS="-A64m -I0 -M8g".

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-297.ProbeLJ1297D {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure; Transitive; _↾_ )
open import FOL.Syntax using ( Formula )
open import FOL.Manipulation.Relabelling using ( embed )
open import L.Constructible {ℓ} using ( 𝒟ₒ )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )

open import Cubical.HITs.CumulativeHierarchy.Base using ( V )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ⁅_,_⁆ ) renaming ( module InfinitySet to Inf )
open Inf using ( #_; sucV )
open import Cubical.Data.Unit using ( tt* )
open import Cubical.Data.Vec using ( _∷_ )
import Cubical.HITs.PropositionalTruncation as PT

import LJ-1-238.GenSequence
import LJ-1-184.ProbeLJ1184A {ℓ} as P184
import LJ-1-184.ProbeLJ1184B {ℓ} lem as P184B
import LJ-1-297.ProbeLJ1297A {ℓ} lem as P1297A
import LJ-1-297.ProbeLJ1297C {ℓ} as P1297C

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))

module A = P184.Ambient
module P1241 = P1297A.P1241
open P1297C using ( absFull )
open P1297A.AbsL using ( _⊨ᵐ_ )

module GS = LJ-1-238.GenSequence {ℓ} lem P1297A.Full
  (λ {x} {y} → P1297A.Full-tr {x} {y})
  (λ k → # k , tt*) (λ k → refl)
  (λ a b → ⁅ fst a , fst b ⁆ , tt*) (λ a b → refl)
  (λ a → sucV (fst a) , tt*) (λ a → refl)

-- The transport, in the two directions the readings need.
toAmb : ∀ {n} (φ : Formula A.R.SC n) (γ : Vec A.R.SC n)
      → ⟨ γ ⊨ᵐ φ ⟩ → ⟨ A.ambient γ φ ⟩
toAmb φ γ = subst ⟨_⟩ (absFull φ γ)

fromAmb : ∀ {n} (φ : Formula A.R.SC n) (γ : Vec A.R.SC n)
        → ⟨ A.ambient γ φ ⟩ → ⟨ γ ⊨ᵐ φ ⟩
fromAmb φ γ = subst ⟨_⟩ (sym (absFull φ γ))

-- =====================================================================
-- THE SUPPLY.  Six readings, delivered at the inner reading by
-- `[LJ-1.238]`, moved to `A.ambient` by probe C.  The Def-step trio
-- stays a hypothesis, so this holds for every Def-step coding.
-- =====================================================================

module Supply
  (DefAt : ∀ {n} → Fin n → Fin n → Formula A.R.SC n)
  (DefAt-in : (X : A.R.SC) → ∀ {n} (u w : Fin n) (γ : Vec A.R.SC n)
            → fst (lookup w γ) ≡ fst X
            → fst (lookup u γ) ≡ 𝒟ₒ (fst X)
            → ⟨ γ ⊨ᵐ DefAt u w ⟩)
  (DefAt-out : (X : A.R.SC) → ∀ {n} (u w : Fin n) (γ : Vec A.R.SC n)
             → GS.DefOK X
             → fst (lookup w γ) ≡ fst X
             → ⟨ γ ⊨ᵐ DefAt u w ⟩
             → fst (lookup u γ) ≡ 𝒟ₒ (fst X))
  where

  module Seq = GS.Body DefAt DefAt-in DefAt-out

  Step* : ∀ {n} → Fin n → Fin n → Fin n → Formula A.R.SC n
  Step* {n} = Seq.StepAt {n}

  Approx* : ∀ {n} → Fin n → Fin n → Formula A.R.SC n
  Approx* {n} = Seq.ApproxAt {n}

  Graph* : ∀ {n} → Fin n → Fin n → Formula A.R.SC n
  Graph* {n} = Seq.LsetGraphAt {n}

  step-out : P184B.Types.StepOutT Step* Approx* Graph*
  step-out v b f γ h = Seq.StepAt-out v b f γ (fromAmb (Step* v b f) γ h)

  step-back : P184B.Types.StepBackT Step* Approx* Graph*
  step-back v b f γ h = Seq.StepAt-back v b f γ (fromAmb (Step* v b f) γ h)

  approx-dom : P184B.Types.ApproxDomT Step* Approx* Graph*
  approx-dom f a γ h = Seq.ApproxAt-dom f a γ (fromAmb (Approx* f a) γ h)

  approx-value : P184B.Types.ApproxValT Step* Approx* Graph*
  approx-value f a γ h = Seq.ApproxAt-value f a γ (fromAmb (Approx* f a) γ h)

  approx-step : P184B.Types.ApproxStepT Step* Approx* Graph*
  approx-step f a γ h c z p =
    toAmb (Step* zero (suc zero) (suc (suc f))) (z ∷ c ∷ γ)
      (Seq.ApproxAt-step f a γ (fromAmb (Approx* f a) γ h) c z p)

  graph-out : P184B.Types.GraphOutT Step* Approx* Graph*
  graph-out w b γ h = PT.map
    (λ { (f , (ha , hs)) →
      f , ( toAmb (Approx* zero (suc b)) (f ∷ γ) ha
          , toAmb (Step* (suc w) (suc b) zero) (f ∷ γ) hs ) })
    (Seq.LsetGraph-out w b γ (fromAmb (Graph* w b) γ h))

  -- ===================================================================
  -- WHAT IS LEFT.  `AmbientStep` with every reading SUPPLIED.  One
  -- hypothesis remains, and it is `q`.
  -- ===================================================================

  module Left (q : Graph* {2} zero (suc zero) ≡ embed P1241.φ₀) where

    module AS = P184B.AmbientStep Step* Approx* Graph*
      step-out step-back approx-dom approx-value approx-step graph-out
      P1241.φ₀ q

    ambHere = AS.amb
