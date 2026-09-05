{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.184] probe B.  THE ACCEPTANCE TEST.
--
-- Probe A builds the read-off generic in the carrier and gives
-- Devlin's clause (a) at the AMBIENT carrier as `clause-a`.  This
-- probe discharges it into [LJ-1.178]'s own shape: it produces
-- `AmbientCross.AmbientRead`, feeds it to `Site.Whole`, and reads
-- `levelIn` and `cover` back out.
--
-- WHAT ENTERS.  Exactly the coded step at the AMBIENT carrier: three
-- formulas and six readings.  That is the residue, and it replaces
-- `amb`.
--
-- ONE agda process under GHCRTS="-A64m -I0 -M8g".

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-184.ProbeLJ1184B {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

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
-- THE RESIDUE: the coded step read AT THE AMBIENT CARRIER.
--
-- These are the delivered objects of `L.Coding.Sequence`
-- (`StepAt` :158, `StepAt-out` :217, `StepAt-back` :221, `ApproxAt`
-- :287, its three projections :296-:317, `LsetGraphAt` and
-- `Graph-out` :330-:340) with `𝒮ʟ` replaced by the ambient carrier.
-- Nothing else is open.
-- =====================================================================

-- The six readings, named once so a consumer can ask for them without
-- re-typing a rank-2 telescope.  P-k: the shape the consumer needs.
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
  (q : Graph {2} zero (suc zero) ≡ embed φ₀)
  where

  module M = A.R.Machine A.ambient Step Approx Graph
    Step-out Step-back Approx-dom Approx-value Approx-step Graph-out

  go : (γ : Vec A.R.SC 2) → ⟨ A.ambient γ (embed φ₀) ⟩
     → IsOrd (fst (lookup (suc zero) γ))
     → fst (lookup zero γ) ≡ Lset (fst (lookup (suc zero) γ))
  go γ h = M.graph-only zero (suc zero) γ
    (subst (λ ψ → ⟨ A.ambient γ ψ ⟩) (sym q) h)

  -- ===================================================================
  -- THE TERM `[LJ-1.178]` COULD NOT WRITE.  Its VERBATIM type, taken
  -- from `agents/tasks/LJ-1-178/ProbeLJ1178A.agda:190-192`.
  -- ===================================================================
  amb : (P : S) (Ptr : isTrans P) → P178.AmbientCross.AmbientRead P Ptr φ₀
  amb P Ptr = A.clause-a fst φ₀ go

  -- ===================================================================
  -- THE DISCHARGE.  `[LJ-1.178]`'s `Site.Whole` took SEVEN inputs and
  -- `amb` was the wall.  Here it is supplied from the residue above,
  -- and only SIX enter.
  -- ===================================================================

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
