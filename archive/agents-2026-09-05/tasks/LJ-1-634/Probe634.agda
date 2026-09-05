{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.634]  PROBE.  THE ONE BINDER.
--
-- [LJ-1.630] landed ingredient (iv)'s site with the IH binder at the
-- constructible carrier Sx = CS.S = Σ V (isL), while its local member
-- stage is a bare V element; the whole-tree check died at the IH
-- application with UnequalTerms, "Σ S (λ x₁ → x₁ ∈ᶜ isL) !=< V ℓ",
-- at that worktree's src/L/BoundedSubset.lagda.md:1433.
-- [LJ-1.608] measured the SAME site GO at the bare V binder
-- (agents/tasks/LJ-1-608/Probe608.agda:177-184). This file states
-- the FIXED binder at StageCardinal's P and applies the IH at a bare
-- V member stage, the one expression 630 failed at:
--   1. ih-type  pins the V binder against this file's P at a bare V.
--   2. ih-apply is the landed IHδ row itself, in the P-body Σ shape
--      the landed site expects.
-- If this probe typechecks, the one binder is the whole defect as far
-- as the site's types are concerned; the whole-tree run settles the
-- price.
--
-- CALIBER. THE PROGRAM SET GHCRTS ON THIS PANE. I DID NOT SET IT.
-- ONE AGDA PROCESS AT A TIME.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫ )
open import Cubical.HITs.CumulativeHierarchy.Constructions using ( module InfinitySet )
open import L.Constructible using ( IsOrd; Lset )
import Cubical.Data.Empty as Empty
import L.StageCardinal

module LJ-1-634.Probe634 {ℓ : Level} (lem : LEM (ℓ-suc ℓ))
  (α₀ : V ℓ) (oα₀ : IsOrd α₀)
  (sq : (δ : V ℓ) → ⟨ δ ∈ InfinitySet.sucV α₀ ⟩
      → (⟨ δ ∈ InfinitySet.ω {ℓ} ⟩ → Empty.⊥)
      → Σ[ f ∈ (⟪ δ ⟫ × ⟪ δ ⟫ → ⟪ δ ⟫) ]
          ((x y : ⟪ δ ⟫ × ⟪ δ ⟫) → f x ≡ f y → x ≡ y)) where

  open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
  open import FOL.ZFStructure using ( module hPropStructure )
  open import Cubical.Data.Sigma using ( _×_ )
  open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
  module SV = hPropStructure 𝒮ᵥ
  open SV using ( _∈ˢ_ )
  open InfinitySet {ℓ} using ( ω; sucV )

  module SC = L.StageCardinal {ℓ} lem α₀ oα₀ sq

  -- 1.  THE FIXED BINDER AGAINST THIS FILE'S P AT A BARE V.
  ih-type : (α : V ℓ) (δ : V ℓ)
    → ⟨ δ ∈ˢ α ⟩
    → ((δ : V ℓ) → ⟨ δ ∈ˢ α ⟩ → SC.Upper.P δ)
    → SC.Upper.P δ
  ih-type α δ δ∈α IH = IH δ δ∈α

  -- 2.  THE LANDED IHδ ROW, AT THE P-BODY Σ THE LANDED SITE EXPECTS.
  ih-apply : (α : V ℓ) (δ : V ℓ)
    → ⟨ δ ∈ˢ α ⟩
    → IsOrd δ → ⟨ δ ∈ˢ sucV α₀ ⟩ → (⟨ δ ∈ˢ ω ⟩ → Empty.⊥)
    → ((δ : V ℓ) → ⟨ δ ∈ˢ α ⟩ → SC.Upper.P δ)
    → Σ[ f ∈ (⟪ Lset δ ⟫ → ⟪ δ ⟫) ]
        ((x y : ⟪ Lset δ ⟫) → f x ≡ f y → x ≡ y)
  ih-apply α δ δ∈α oδ δ∈suc infδ IH = IH δ δ∈α oδ δ∈suc infδ
