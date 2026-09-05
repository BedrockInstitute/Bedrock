{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.178] probe B.  THE SITE WIRING.
--
-- Probe A builds `levelIn` and `cover` generically.  This probe wires
-- that build to the REAL site, `Devlin55.BoundedSubsetAt`, with the
-- site's own delivered values, and then applies `Co` and reads
-- `theorem` out.
--
-- Every value the wiring uses is DELIVERED.  What stays open is
-- exactly three named hypotheses of probe A's `Whole` module.
--
-- ONE agda process under GHCRTS="-A64m -I0 -M8g".

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-178.ProbeLJ1178B {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula )
open import FOL.LevyHierarchy using ( Σ₁ )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ} using ( Lset; IsOrd )
import L.BoundedSubset {ℓ} lem as BS
import LJ-1-178.ProbeLJ1178A {ℓ} lem as PA

import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁ )
open import Cubical.Data.Sigma using ( _×_; _,_ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet; _∪_; ⁅_⁆s )
open InfinitySet using ( ω; sucV )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ

open BS using ( _↪_ )

-- =====================================================================
-- THE REAL SITE.  The telescope is `BoundedSubsetAt`'s own
-- (src/L/BoundedSubset.lagda.md:1385-1394), taken abstract: the probe
-- measures the WIRING, not one numeric instance.
-- =====================================================================

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

  module BA = BS.Devlin55.BoundedSubsetAt
    κ ordκ cardκ κ∉ω α ordα α∈κ α∉ω sq x x⊆Lα absorbs
    lam ordλ α∈λ succλ x∈Lλ

  -- DELIVERED: the collapse's satisfaction iso-invariance at the hull.
  module CIso = BS.CollapseIso BA.HS.M BA.HE.hullExt

  -- Probe A's generic build, at the site's own values.
  module Sx = PA.Site lam ordλ
    BA.HS.M BA.HS.H.Hull⊆L
    BA.HS.C.πX BA.HS.C.πX-trans
    BA.HS.C.π BA.HS.C.πX-intro BA.HS.C.πX-member
    φ₀

  -- THE FOUR DELIVERED INPUTS, each checked against probe A's type.
  elem : Sx.A.Elementary
  elem = BA.HEDC.elem

  isoFwd : Sx.IsoFwd
  isoFwd n χ δ = CIso.I.iso-inv n χ δ

  isoBwd : Sx.IsoBwd
  isoBwd n χ δ = CIso.I.iso-inv-bwd n χ δ

  -- THE THREE THAT STAY OPEN.
  module Open
    (sl : Sx.StageLevels) (sc : Sx.StageCovered)
    (s₁ : Σ₁ Sx.Cr.φP)
    (amb : PA.AmbientCross.AmbientRead BA.HS.C.πX BA.HS.C.πX-trans φ₀) where

    module W = Sx.Whole elem isoFwd isoBwd sl sc s₁ amb

    -- The two hypotheses of `Condense`, at their VERBATIM site types.
    levelIn : (δ : S) → IsOrd δ → ⟨ δ ∈ˢ BA.HS.C.πX ⟩ → ⟨ Lset δ ∈ˢ BA.HS.C.πX ⟩
    levelIn = W.levelIn

    cover : (y : S) → ⟨ y ∈ˢ BA.HS.M ⟩
          → ∥ Σ[ γ ∈ S ] (IsOrd γ × ⟨ γ ∈ˢ BA.HS.C.πX ⟩
                          × ⟨ BA.HS.C.π y ∈ˢ Lset γ ⟩) ∥₁
    cover = W.cover

    -- AND THE TROPHY'S CONSUMER, ENTERED.
    module Co = BA.Co levelIn cover

    theorem : ⟨ x ∈ˢ Lset κ ⟩
    theorem = Co.theorem
