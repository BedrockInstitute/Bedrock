{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.489] PROBE.  Does the collapse commute with the
-- definable powerset.  Lands nothing in src/.
--
--   STEP ONE, W3 FIRST  the easier inclusion OneWay.
--                       Obligation omitted.  π is opaque.  Its
--                       law sits inside an unfolding block at
--                       src/V/Collapse.lagda.md:56-59.  This
--                       file spends the exported law at 𝒟ₒ y
--                       and does not open the seal.
--
--   STEP TWO            Membership laws of 𝒟ₒ spent.  The join
--                       of π-compute's right-hand side with
--                       𝒟ₒ (C.π y) is unbuilt.  Formula
--                       transport is unbuilt.  No term named
--                       piCommuteD.  See review-of-piCommuteD.md.
--
-- ONE Agda process per run, GHCRTS="-A64m -I0 -M8g", the wide
-- caliber, set on the pane by the program and untouched here.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-489.Probe489 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ} using ( IsOrd; Lset; 𝒟ₒ; 𝒟ₒ-intro; 𝒟ₒ-inv )
open import L.Definability {ℓ} using ( module DefOf )
open import L.Hull {ℓ} lem using ( module AtStage )
open import V.Collapse {ℓ} using ( module Collapse )
open import FOL.ZFModel 𝒮ᵥ using ( _⊆ˢ_ )
open import FOL.Syntax using ( Formula )

import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁ )

open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ∅; module InfinitySet )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫ )
open InfinitySet using ( sucV )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ

-- Telescope copied from src/L/BoundedSubset.lagda.md:903-916.
-- Line :903 is the module keyword.  Line :916 is `module Condense`.
-- Nothing below that header is copied.  Same cut as
-- Probe477.agda:45-57.

module HullStage (lam : S) (ordλ : IsOrd lam)
  (succλ : (d : S) → ⟨ d ∈ˢ lam ⟩ → ⟨ sucV d ∈ˢ lam ⟩)
  (X : S) (X⊆L : (x : S) → ⟨ x ∈ˢ X ⟩ → ⟨ x ∈ˢ Lset lam ⟩)
  (∅∈λ : ⟨ ∅ ∈ˢ lam ⟩) where

  module ASt = AtStage lam ordλ

  module H = ASt.Hull X X⊆L ∅∈λ

  M : S
  M = H.T.Hull

  module C = Collapse M

  -- =====================================================================
  -- W3.  The easier inclusion, obligation omitted.
  -- Direction tried: left to right.  A member of C.π (𝒟ₒ y) is the
  -- collapse of a hull-filtered member of 𝒟ₒ y.  The question is
  -- whether that image is still DEFINABLE over C.π y.
  -- The converse also needs a preimage in M, so it is the harder
  -- direction.  π-compute spends at 𝒟ₒ y without unfolding π.
  -- =====================================================================

  -- π-compute : (x : S) → π x ≡ step x (λ y _ → π y)
  -- Site: src/V/Collapse.lagda.md:58-59, inside `opaque; unfolding π`.
  -- The type is visible without unfolding.  This term applies the
  -- exported law at 𝒟ₒ y and does not open the seal on π.

  left-compute : (y : S) → C.π (𝒟ₒ y) ≡ _
  left-compute y = C.π-compute (𝒟ₒ y)

  -- The inclusion the brief named as W3.  UNBUILT.  Inhabiting it
  -- needs a defining formula over C.π y for each collapsed
  -- definable subset.  That is elementarity, not a computation.

  OneWay : Type (ℓ-suc ℓ)
  OneWay =
    (y : S) → ⟨ y ∈ˢ M ⟩ → ⟨ C.π (𝒟ₒ y) ⊆ˢ 𝒟ₒ (C.π y) ⟩

  -- =====================================================================
  -- STEP TWO.  Membership laws of 𝒟ₒ spend without unfolding the seal.
  -- The join of π-compute's right-hand side with 𝒟ₒ (C.π y) is the
  -- remaining constructor gap.  Formula transport is the remaining
  -- elementarity gap.  No term named piCommuteD.
  -- =====================================================================

  -- 𝒟ₒ-inv / 𝒟ₒ-intro : src/L/Constructible.lagda.md:301-308,
  -- inside `opaque; unfolding 𝒟ₒ`.  The types are visible without
  -- unfolding.  These terms apply the exported laws and do not
  -- open the seal on 𝒟ₒ.

  d-inv : (A x : S) → ⟨ x ∈ˢ 𝒟ₒ A ⟩ → _
  d-inv = 𝒟ₒ-inv

  d-intro : (A x : S)
          → ∥ Σ[ φ ∈ Formula ⟪ A ⟫ 1 ] (DefOf.defSet A φ ≡ x) ∥₁
          → _
  d-intro = 𝒟ₒ-intro

  -- The join the computation law leaves.  Left is C.step at 𝒟ₒ y,
  -- a sett of π-images of hull-filtered members of 𝒟ₒ y
  -- (src/V/Collapse.lagda.md:47-48).  Right is 𝒟ₒ at C.π y, sealed
  -- (src/L/Constructible.lagda.md:211-213).  A subst along
  -- left-compute failed with [UnequalTerms]
  -- (runs/one-way-subst.out:2).  UNBUILT.

  JoinAtD : Type (ℓ-suc ℓ)
  JoinAtD =
    (y : S) → C.step (𝒟ₒ y) (λ z _ → C.π z) ≡ 𝒟ₒ (C.π y)

  -- What the inclusion still needs after the membership laws spend.
  -- A definable subset of y that lies in M must collapse to a
  -- definable subset of C.π y.  That is formula transport along π.
  -- UNBUILT.

  FormulaTransport : Type (ℓ-suc ℓ)
  FormulaTransport =
    (y : S) → ⟨ y ∈ˢ M ⟩
    → (φ : Formula ⟪ y ⟫ 1)
    → ⟨ DefOf.defSet y φ ∈ˢ M ⟩
    → ∥ Σ[ ψ ∈ Formula ⟪ C.π y ⟫ 1 ]
          (DefOf.defSet (C.π y) ψ ≡ C.π (DefOf.defSet y φ)) ∥₁

  -- Obligation type.  Same shape as the brief named.  UNBUILT.
  -- The name piCommuteD is not in scope.

  PiCommuteD : Type (ℓ-suc ℓ)
  PiCommuteD =
    (y : S) → ⟨ y ∈ˢ M ⟩ → C.π (𝒟ₒ y) ≡ 𝒟ₒ (C.π y)
