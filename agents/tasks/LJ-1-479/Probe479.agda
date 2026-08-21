{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.479] PROBE.  HullClosedLset, uniqueness first.
-- It runs in agents/tasks/LJ-1-479/ and lands nothing in src/.
--
--   STEP ONE, W3 FIRST  pins = Lset-only.  Uniqueness of the value
--                       slot, with the extra IsOrd.  Obligation
--                       omitted in the W3-only file.
--
--   STEP TWO            pins-no-ord unbuilt.  hull-ord unbuilt.
--                       HullClosedLset as a Type inside HullOnV.
--                       No term named HullClosedLset at the root.
--                       See review-of-HullClosedLset.md.
--
-- ONE Agda process per run, GHCRTS="-A64m -I0 -M8g", the wide caliber,
-- set on the pane by the program and untouched here.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-479.Probe479 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans; Lset; IsOrd )
open import L.Coding.Sequence {ℓ} lem using ( LsetGraphAt )
open import L.Hierarchy {ℓ} lem using ( Lset-only )
open import L.Hull {ℓ} lem using ( module AtStage )
open import V.Collapse {ℓ} using ( module Collapse )
open import Cubical.Data.FinData using ( Fin )
open import Cubical.Data.Vec using ( lookup )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ∅; module InfinitySet )
open InfinitySet using ( sucV )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL renaming ( _⊨ᵐ_ to _⊨_ )

-- =====================================================================
-- W3.  Uniqueness from Lset-only.  Obligation omitted.
-- Site: src/L/Hierarchy.lagda.md:334-335.
-- =====================================================================

pins : ∀ {n} (w b : Fin n) (γ : S ^ n)
     → ⟨ γ ⊨ LsetGraphAt w b ⟩
     → IsOrd (fst (lookup b γ))
     → fst (lookup w γ) ≡ Lset (fst (lookup b γ))
pins = Lset-only

-- Uniqueness without IsOrd.  Same type as LsetAt-out-brief at
-- agents/tasks/LJ-1-458/Probe458.agda:69-73.  Unbuilt.  This is the
-- uniqueness HullClosedLset needs, and Lset-only does not give it.

pins-no-ord : Type _
pins-no-ord =
    ∀ {n} (w b : Fin n) (γ : S ^ n)
  → ⟨ γ ⊨ LsetGraphAt w b ⟩
  → fst (lookup w γ) ≡ Lset (fst (lookup b γ))

-- =====================================================================
-- D-10 TYPES AT THE HULL.  S above is the class carrier (𝒮ʟ).
-- The hull telescope lives at 𝒮ᵥ, as BoundedSubset:56 and
-- Probe462.agda:42-43 open it.  Nested so the two carriers do not
-- clash.  Obligation omitted: no term named HullClosedLset at the
-- module root.  No feed.  No inHull.  Stop at uniqueness.
-- =====================================================================

module HullOnV where

  -- Qualified: the outer S is the class carrier.  BoundedSubset and
  -- Probe462 open 𝒮ᵥ as the hull carrier.  A second open of S is
  -- [AmbiguousOverloadedProjection].
  module VS = hPropStructure 𝒮ᵥ

  -- Telescope copied from src/L/BoundedSubset.lagda.md:903-914.
  -- Nothing below module Condense is copied.

  module HullStage (lam : VS.S) (ordλ : IsOrd lam)
    (succλ : (d : VS.S) → ⟨ d VS.∈ˢ lam ⟩ → ⟨ sucV d VS.∈ˢ lam ⟩)
    (X : VS.S) (X⊆L : (x : VS.S) → ⟨ x VS.∈ˢ X ⟩ → ⟨ x VS.∈ˢ Lset lam ⟩)
    (∅∈λ : ⟨ ∅ VS.∈ˢ lam ⟩) where

    module ASt = AtStage lam ordλ

    module H = ASt.Hull X X⊆L ∅∈λ

    M : VS.S
    M = H.T.Hull

    module C = Collapse M

    -- The missing source.  Unbuilt.  No lemma in live src/ takes
    -- ⟨ y ∈ˢ M ⟩ to IsOrd y.  mem-ord needs membership in an
    -- ordinal (src/L/Ordinal.lagda.md:221).  Hull⊆L gives
    -- membership in Lset α (src/L/Hull.lagda.md:330-331).

    hull-ord : Type (ℓ-suc ℓ)
    hull-ord = (y : VS.S) → ⟨ y VS.∈ˢ M ⟩ → IsOrd y

    -- Step 2 as the predecessor stated it.  Unbuilt.  Not inhabited.
    -- Site of the type: agents/tasks/LJ-1-462/Probe462.agda:136-138.

    HullClosedLset : Type (ℓ-suc ℓ)
    HullClosedLset =
      (y : VS.S) → ⟨ y VS.∈ˢ M ⟩ → ⟨ Lset y VS.∈ˢ M ⟩
