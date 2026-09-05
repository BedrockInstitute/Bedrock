{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.244] probe A.  `[LJ-1.184]`'s `AmbientStep` with `q` REPLACED BY
-- `q'`, the third-route weakening of `[LJ-1.243]` section 3.1.
--
--   q  : Graph {2} zero (suc zero) ≡ embed φ₀        (both directions, syntax)
--   q' : ⟨ ambient γ (embed φ₀) ⟩ → ⟨ ambient γ (Graph zero (suc zero)) ⟩
--
-- `go` at ProbeLJ1184B.agda:122 spends `sym q` in ONE direction; this probe
-- spends `q'` directly.  NOTHING ELSE CHANGES.  The point of the probe is to
-- confirm that the direction is right and that `amb` still comes out -- and
-- to expose that `q'` is a HYPOTHESIS here, not a term (C-45's audit).
--
-- ONE agda process under GHCRTS="-A64m -I0 -M8g".

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-244.ProbeLJ1244A {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula )
open import FOL.LevyHierarchy using ( Σ₁ )
open import FOL.Manipulation.Relabelling using ( embed )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Collapse {ℓ} using ( isTrans )
open import V.Coding {ℓ} using ( pr )
open import L.Constructible {ℓ} using ( Lset; IsOrd )

import LJ-1-178.ProbeLJ1178A {ℓ} lem as P178
import LJ-1-184.ProbeLJ1184A {ℓ} as P184

import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁ )
open import Cubical.Data.Sigma using ( _×_; _,_ )
open import Cubical.Data.Vec using ( Vec; lookup; _∷_; [] )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ

module A = P184.Ambient

-- =====================================================================
-- The six readings, verbatim from ProbeLJ1184B.agda Types.
-- =====================================================================

module Types
  (Step : ∀ {n} → Fin n → Fin n → Fin n → Formula A.R.SC n)
  (Approx : ∀ {n} → Fin n → Fin n → Formula A.R.SC n)
  (Graph : ∀ {n} → Fin n → Fin n → Formula A.R.SC n)
  where

  StepOutT : Type (ℓ-suc ℓ)
  StepOutT = ∀ {n} (v b f : Fin n) (γ : Vec A.R.SC n)
           → ⟨ A.ambient γ (Step v b f) ⟩ → A.R.PowOK b f γ
           → (z : A.R.SC) → ⟨ fst z ∈ˢ fst (lookup v γ) ⟩
           → ∥ A.R.StepOf b f γ z ∥₁

  StepBackT : Type (ℓ-suc ℓ)
  StepBackT = ∀ {n} (v b f : Fin n) (γ : Vec A.R.SC n)
            → ⟨ A.ambient γ (Step v b f) ⟩ → A.R.PowOK b f γ
            → (z : A.R.SC) → A.R.StepOf b f γ z
            → ⟨ fst z ∈ˢ fst (lookup v γ) ⟩

  ApproxDomT : Type (ℓ-suc ℓ)
  ApproxDomT = ∀ {n} (f a : Fin n) (γ : Vec A.R.SC n)
             → ⟨ A.ambient γ (Approx f a) ⟩
             → A.R.Domain₀ (lookup f γ) (fst (lookup a γ))

  ApproxValT : Type (ℓ-suc ℓ)
  ApproxValT = ∀ {n} (f a : Fin n) (γ : Vec A.R.SC n)
             → ⟨ A.ambient γ (Approx f a) ⟩ → (c : A.R.SC)
             → ⟨ fst c ∈ˢ fst (lookup a γ) ⟩
             → ∥ (Σ[ z ∈ A.R.SC ]
                   ⟨ pr (fst c) (fst z) ∈ˢ fst (lookup f γ) ⟩) ∥₁

  ApproxStepT : Type (ℓ-suc ℓ)
  ApproxStepT = ∀ {n} (f a : Fin n) (γ : Vec A.R.SC n)
              → ⟨ A.ambient γ (Approx f a) ⟩ → (c z : A.R.SC)
              → ⟨ pr (fst c) (fst z) ∈ˢ fst (lookup f γ) ⟩
              → ⟨ A.ambient (z ∷ c ∷ γ)
                    (Step zero (suc zero) (suc (suc f))) ⟩

  GraphOutT : Type (ℓ-suc ℓ)
  GraphOutT = ∀ {n} (w b : Fin n) (γ : Vec A.R.SC n)
            → ⟨ A.ambient γ (Graph w b) ⟩
            → ∥ (Σ[ f ∈ A.R.SC ]
                  ( ⟨ A.ambient (f ∷ γ) (Approx zero (suc b)) ⟩
                  × ⟨ A.ambient (f ∷ γ) (Step (suc w) (suc b) zero) ⟩ )) ∥₁

module AmbientStep
  (Step : ∀ {n} → Fin n → Fin n → Fin n → Formula A.R.SC n)
  (Approx : ∀ {n} → Fin n → Fin n → Formula A.R.SC n)
  (Graph : ∀ {n} → Fin n → Fin n → Formula A.R.SC n)
  (Step-out : Types.StepOutT Step Approx Graph)
  (Step-back : Types.StepBackT Step Approx Graph)
  (Approx-dom : Types.ApproxDomT Step Approx Graph)
  (Approx-value : Types.ApproxValT Step Approx Graph)
  (Approx-step : Types.ApproxStepT Step Approx Graph)
  (Graph-out : Types.GraphOutT Step Approx Graph)
  (φ₀ : Formula (⊥* {ℓ-suc ℓ}) 2)
  (q' : (γ : Vec A.R.SC 2)
      → ⟨ A.ambient γ (embed φ₀) ⟩
      → ⟨ A.ambient γ (Graph {2} zero (suc zero)) ⟩)
  where

  module M = A.R.Machine A.ambient Step Approx Graph
    Step-out Step-back Approx-dom Approx-value Approx-step Graph-out

  go : (γ : Vec A.R.SC 2) → ⟨ A.ambient γ (embed φ₀) ⟩
     → IsOrd (fst (lookup (suc zero) γ))
     → fst (lookup zero γ) ≡ Lset (fst (lookup (suc zero) γ))
  go γ h = M.graph-only zero (suc zero) γ (q' γ h)

  amb : (P : S) (Ptr : isTrans P) → P178.AmbientCross.AmbientRead P Ptr φ₀
  amb P Ptr = A.clause-a fst φ₀ go

  module Discharge
    (a0 : S) (orda0 : IsOrd a0)
    (M : S) (M⊆L : (z : S) → ⟨ z ∈ˢ M ⟩ → ⟨ z ∈ˢ Lset a0 ⟩)
    (P : S) (Ptr : isTrans P)
    (pi : S → S)
    (piIntro : (y : S) → ⟨ y ∈ˢ M ⟩ → ⟨ pi y ∈ˢ P ⟩)
    (piMember : (z : S) → ⟨ z ∈ˢ P ⟩
              → ∥ Σ[ y ∈ S ] (⟨ y ∈ˢ M ⟩ × (pi y ≡ z)) ∥₁)
    where

    module Sx = P178.Site a0 orda0 M M⊆L P Ptr pi piIntro piMember φ₀

    module Closed
      (el : Sx.A.Elementary) (fwd : Sx.IsoFwd) (bwd : Sx.IsoBwd)
      (sl : Sx.StageLevels) (sc : Sx.StageCovered)
      (s₁ : Σ₁ Sx.Cr.φP)
      where

      module W = Sx.Whole el fwd bwd sl sc s₁ (amb P Ptr)

      levelIn : (δ : S) → IsOrd δ → ⟨ δ ∈ˢ P ⟩ → ⟨ Lset δ ∈ˢ P ⟩
      levelIn = W.levelIn

      cover : (y : S) → ⟨ y ∈ˢ M ⟩
            → ∥ Σ[ γ ∈ S ] (IsOrd γ × ⟨ γ ∈ˢ P ⟩ × ⟨ pi y ∈ˢ Lset γ ⟩) ∥₁
      cover = W.cover
