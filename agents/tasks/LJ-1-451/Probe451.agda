{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.451] PROBE.  Can the hull's Code name Lset?
-- It runs in agents/tasks/LJ-1-451/ and lands nothing in src/.
--
--   STEP ONE, W3 FIRST  The type LsetCode, obligation omitted.
--                       Code has constructors base and wit only.
--
--   STEP TWO            Omitted. W3 is unbuilt. The obligation is
--                       unbuilt. See review-of-levelIn.md.
--
-- ONE Agda process per run, GHCRTS="-A64m -I0 -M8g", the wide caliber,
-- set on the pane by the program and untouched here.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-451.Probe451 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ} using ( IsOrd; Lset )
open import L.Hull {ℓ} lem using ( module AtStage )
open import V.Collapse {ℓ} using ( module Collapse )

open import Cubical.Data.Sigma using ( Σ-syntax )
open import Cubical.Data.Vec using ( _∷_; [] )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ∅; module InfinitySet )
open InfinitySet using ( sucV )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ

-- Telescope copied from src/L/BoundedSubset.lagda.md:903-914.
-- The brief names :898-916 (comment plus Condense header). Nothing
-- below module Condense is copied.

module HullStage (lam : S) (ordλ : IsOrd lam)
  (succλ : (d : S) → ⟨ d ∈ˢ lam ⟩ → ⟨ sucV d ∈ˢ lam ⟩)
  (X : S) (X⊆L : (x : S) → ⟨ x ∈ˢ X ⟩ → ⟨ x ∈ˢ Lset lam ⟩)
  (∅∈λ : ⟨ ∅ ∈ˢ lam ⟩) where

  module ASt = AtStage lam ordλ

  module H = ASt.Hull X X⊆L ∅∈λ

  M : S
  M = H.T.Hull

  module C = Collapse M

  -- Code constructors in scope: base and wit. There is no third.
  open H.T using ( Code; val; base; wit )

  -- =====================================================================
  -- D-10 STEPS AS TYPES.  Step 1 is delivered. Steps 2 to 4 are unbuilt.
  -- =====================================================================

  -- Step 1. Delivered. Restated so the type is in this file.
  Step1 : Type (ℓ-suc ℓ)
  Step1 = (z : S) → ⟨ z ∈ˢ C.πX ⟩
        → ∥ Σ[ y ∈ S ] (⟨ y ∈ˢ M ⟩ × (C.π y ≡ z)) ∥₁

  step1 : Step1
  step1 = C.πX-member

  -- Step 2. Hull closure under Lset, and collapse commuting with Lset.
  HullClosedLset : Type (ℓ-suc ℓ)
  HullClosedLset =
    (y : S) → ⟨ y ∈ˢ M ⟩ → ⟨ Lset y ∈ˢ M ⟩

  πCommuteLset : Type (ℓ-suc ℓ)
  πCommuteLset =
    (y : S) → ⟨ y ∈ˢ M ⟩ → C.π (Lset y) ≡ Lset (C.π y)

  -- Step 3. W3. Definability of Lset in the hull's language. UNBUILT.
  LsetCode : Type (ℓ-suc ℓ)
  LsetCode =
    (c : Code) → Σ[ d ∈ Code ] (fst (val d) ≡ Lset (fst (val c)))

  -- Step 4. Absoluteness. Same type as πCommuteLset. Unbuilt.

  -- The consumer's obligation. UNBUILT. Not a term named levelIn.
  LevelIn : Type (ℓ-suc ℓ)
  LevelIn =
    (δ : S) → IsOrd δ → ⟨ δ ∈ˢ C.πX ⟩ → ⟨ Lset δ ∈ˢ C.πX ⟩

  -- The missing formula the next brief must order. UNBUILT.
  -- wit is the only constructor that can name a defined object.
  -- It needs a Formula (⊥* {ℓ}) (suc k). No such formula for Lset
  -- is delivered at Formula Code or at Formula (⊥* {ℓ}).
  MissingFormula : Type (ℓ-suc ℓ)
  MissingFormula =
    Σ[ ψ ∈ Formula (⊥* {ℓ}) 2 ]
      ((c : Code) → fst (val (wit 1 ψ (c ∷ []))) ≡ Lset (fst (val c)))
