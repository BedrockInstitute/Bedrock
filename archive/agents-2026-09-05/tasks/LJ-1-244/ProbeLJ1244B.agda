{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.244] probe B.  THE DEFINITION ATTEMPT.
--
-- Probe A confirmed `q'` as a HYPOTHESIS typechecks and `amb` comes out
-- (conditional on `q'`).  This probe asks whether `q'` can be DEFINED from
-- the six readings and φ₀ -- the third route's load-bearing claim.
--
--   q' : (γ) → ⟨ ambient γ (embed φ₀) ⟩ → ⟨ ambient γ (Graph zero (suc zero)) ⟩
--
-- With `Graph` a parameter the goal is stuck: the six readings all run FROM
-- Step/Approx/Graph satisfaction TO Lset facts, and nothing runs TO
-- `⟨ Graph ⟩` (the `Graph-in`/`ApproxAt-in`/`StepAt-in` directions are NOT in
-- the telescope).  The hole below is the blocking term.
--
-- ONE agda process under GHCRTS="-A64m -I0 -M8g".

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-244.ProbeLJ1244B {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula )
open import FOL.Manipulation.Relabelling using ( embed )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Coding {ℓ} using ( pr )

import LJ-1-184.ProbeLJ1184A {ℓ} as P184

import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁ )
open import Cubical.Data.Sigma using ( _×_; _,_ )
open import Cubical.Data.Vec using ( Vec; lookup; _∷_; [] )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ

module A = P184.Ambient

module Attempt
  (Step : ∀ {n} → Fin n → Fin n → Fin n → Formula A.R.SC n)
  (Approx : ∀ {n} → Fin n → Fin n → Formula A.R.SC n)
  (Graph : ∀ {n} → Fin n → Fin n → Formula A.R.SC n)
  (Step-out : ∀ {n} (v b f : Fin n) (γ : Vec A.R.SC n)
            → ⟨ A.ambient γ (Step v b f) ⟩ → A.R.PowOK b f γ
            → (z : A.R.SC) → ⟨ fst z ∈ˢ fst (lookup v γ) ⟩
            → ∥ A.R.StepOf b f γ z ∥₁)
  (Step-back : ∀ {n} (v b f : Fin n) (γ : Vec A.R.SC n)
             → ⟨ A.ambient γ (Step v b f) ⟩ → A.R.PowOK b f γ
             → (z : A.R.SC) → A.R.StepOf b f γ z → ⟨ fst z ∈ˢ fst (lookup v γ) ⟩)
  (Approx-dom : ∀ {n} (f a : Fin n) (γ : Vec A.R.SC n)
              → ⟨ A.ambient γ (Approx f a) ⟩ → A.R.Domain₀ (lookup f γ) (fst (lookup a γ)))
  (Approx-value : ∀ {n} (f a : Fin n) (γ : Vec A.R.SC n)
                → ⟨ A.ambient γ (Approx f a) ⟩ → (c : A.R.SC)
                → ⟨ fst c ∈ˢ fst (lookup a γ) ⟩
                → ∥ (Σ[ z ∈ A.R.SC ] ⟨ pr (fst c) (fst z) ∈ˢ fst (lookup f γ) ⟩) ∥₁)
  (Approx-step : ∀ {n} (f a : Fin n) (γ : Vec A.R.SC n)
               → ⟨ A.ambient γ (Approx f a) ⟩ → (c z : A.R.SC)
               → ⟨ pr (fst c) (fst z) ∈ˢ fst (lookup f γ) ⟩
               → ⟨ A.ambient (z ∷ c ∷ γ) (Step zero (suc zero) (suc (suc f))) ⟩)
  (Graph-out : ∀ {n} (w b : Fin n) (γ : Vec A.R.SC n)
             → ⟨ A.ambient γ (Graph w b) ⟩
             → ∥ (Σ[ f ∈ A.R.SC ]
                   ( ⟨ A.ambient (f ∷ γ) (Approx zero (suc b)) ⟩
                   × ⟨ A.ambient (f ∷ γ) (Step (suc w) (suc b) zero) ⟩ )) ∥₁)
  (φ₀ : Formula (⊥* {ℓ-suc ℓ}) 2)
  where

  -- The third route's claim: this must be DEFINED, not assumed.
  q' : (γ : Vec A.R.SC 2)
     → ⟨ A.ambient γ (embed φ₀) ⟩
     → ⟨ A.ambient γ (Graph {2} zero (suc zero)) ⟩
  q' γ h = {!!}
