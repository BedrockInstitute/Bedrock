{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.184] probe C.  THE BRIEF'S ACCEPTANCE TEST, AT THE REAL SITE.
--
-- `[LJ-1.178]`'s probe B enters `Devlin55.BoundedSubsetAt`, wires
-- `levelIn` and `cover`, applies `BA.Co` and reads `theorem` out.  It
-- left FOUR hypotheses open: `sl`, `sc`, `s₁` and `amb`.
--
-- This probe enters the SAME site entry and supplies `amb` from probe
-- A's carrier-generic read-off.  THREE hypotheses are left, plus the
-- ambient step residue.
--
-- ONE agda process under GHCRTS="-A64m -I0 -M8g".

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-184.ProbeLJ1184C {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula )
open import FOL.LevyHierarchy using ( Σ₁ )
open import FOL.Manipulation.Relabelling using ( embed )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ} using ( Lset; IsOrd )
import L.BoundedSubset {ℓ} lem as BS

import LJ-1-178.ProbeLJ1178A {ℓ} lem as P178A
import LJ-1-178.ProbeLJ1178B {ℓ} lem as P178B
import LJ-1-184.ProbeLJ1184B {ℓ} lem as P184B

import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Data.Sigma using ( _×_; _,_ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet; _∪_; ⁅_⁆s )
open InfinitySet using ( ω; sucV )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ

open BS using ( _↪_ )

module AtSite
  (κ : S) (ordκ : IsOrd κ) (cardκ : BS.IsCardinal κ)
  (κ∉ω : ⟨ κ ∈ˢ ω ⟩ → Empty.⊥)
  (α : S) (ordα : IsOrd α) (α∈κ : ⟨ α ∈ˢ κ ⟩) (α∉ω : ⟨ α ∈ˢ ω ⟩ → Empty.⊥)
  (sq : (δ : S) → ⟨ δ ∈ˢ sucV α ⟩ → (⟨ δ ∈ˢ ω ⟩ → Empty.⊥)
      → Σ[ f ∈ (⟪ δ ⟫ × ⟪ δ ⟫ → ⟪ δ ⟫) ]
          ((u v : ⟪ δ ⟫ × ⟪ δ ⟫) → f u ≡ f v → u ≡ v))
  (x : S) (x⊆Lα : (z : S) → ⟨ z ∈ˢ x ⟩ → ⟨ z ∈ˢ Lset α ⟩)
  (absorbs : _↪_ ⟪ Lset α ∪ ⁅ x ⁆s ⟫ ⟪ Lset α ⟫)
  (lam : S) (ordλ : IsOrd lam) (α∈λ : ⟨ α ∈ˢ lam ⟩)
  (succλ : (d : S) → ⟨ d ∈ˢ lam ⟩ → ⟨ sucV d ∈ˢ lam ⟩)
  (x∈Lλ : ⟨ x ∈ˢ Lset lam ⟩)
  (φ₀ : Formula (⊥* {ℓ-suc ℓ}) 2) where

  module Site178 = P178B.AtSite
    κ ordκ cardκ κ∉ω α ordα α∈κ α∉ω sq x x⊆Lα absorbs
    lam ordλ α∈λ succλ x∈Lλ φ₀

  module BA = Site178.BA

  -- THE AMBIENT STEP RESIDUE.  Three formulas and six readings, at the
  -- AMBIENT carrier.  This module's parameters replace `amb`.
  module Residue
    (AS : ∀ {n} → Fin n → Fin n → Fin n
        → Formula P184B.A.R.SC n)
    (AA AG : ∀ {n} → Fin n → Fin n → Formula P184B.A.R.SC n)
    where

    module T = P184B.Types AS AA AG

    module Step184
      (so : T.StepOutT) (sb : T.StepBackT)
      (ad : T.ApproxDomT) (av : T.ApproxValT) (ast : T.ApproxStepT)
      (gout : T.GraphOutT)
      (q : AG {2} zero (suc zero) ≡ embed φ₀)
      where

      module AS' = P184B.AmbientStep AS AA AG so sb ad av ast gout φ₀ q

      -- THE THREE THAT STAY OPEN.  `amb` is GONE.
      module Open
        (sl : Site178.Sx.StageLevels) (sc : Site178.Sx.StageCovered)
        (s₁ : Σ₁ Site178.Sx.Cr.φP)
        where

        module O = Site178.Open sl sc s₁
          (AS'.amb BA.HS.C.πX BA.HS.C.πX-trans)

        -- AND THE TROPHY'S CONSUMER, ENTERED.
        theorem : ⟨ x ∈ˢ Lset κ ⟩
        theorem = O.theorem
