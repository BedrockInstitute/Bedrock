{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.481] PROBE.  HullClosedLset.  Uniqueness of the witness first.
-- It runs in agents/tasks/LJ-1-481/ and lands nothing in src/.
--
--   STEP ONE, W3 FIRST  pins, from Lset-only.  Obligation omitted.
--                       Uniqueness holds at an ordinal.  IsOrd has
--                       no source at a hull member y.
--
--   STEP TWO            obligation omitted.  See
--                       review-of-HullClosedLset.md.
--
-- ONE Agda process per run, GHCRTS="-A64m -I0 -M8g", the wide caliber,
-- set on the pane by the program and untouched here.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-481.Probe481 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans; Lset; IsOrd )
open import L.Hull {ℓ} lem using ( module AtStage )
open import L.Coding.Sequence {ℓ} lem using ( LsetGraph; LsetGraphAt )
open import L.Hierarchy {ℓ} lem using ( Lset-only )
open import Cubical.Data.FinData using ( Fin )
open import Cubical.Data.Vec using ( lookup )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ∅; module InfinitySet )
open InfinitySet using ( sucV )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ
open hPropStructure 𝒮ᵥ using () renaming ( S to SV; _∈ˢ_ to _∈ᵥ_ )

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL renaming ( _⊨ᵐ_ to _⊨_ )

-- =====================================================================
-- W3.  pins, from Lset-only.  Obligation omitted.
-- Site: src/L/Hierarchy.lagda.md:334-335
-- Quote of that site: Lset-only takes the graph and IsOrd, then
-- concludes the value slot is Lset of the argument slot.
-- =====================================================================

-- The unique satisfier, as Lset, at an ordinal.  Same term as
-- agents/tasks/LJ-1-458/Probe458.agda:62-66.

pins : ∀ {n} (w b : Fin n) (γ : S ^ n)
     → ⟨ γ ⊨ LsetGraphAt w b ⟩
     → IsOrd (fst (lookup b γ))
     → fst (lookup w γ) ≡ Lset (fst (lookup b γ))
pins = Lset-only

-- At most one satisfier at a given index.  Two environments that
-- satisfy the graph at the same ordinal argument have the same value.

pins-at-most-one : ∀ {n} (w b : Fin n) (γ δ : S ^ n)
                 → ⟨ γ ⊨ LsetGraphAt w b ⟩
                 → ⟨ δ ⊨ LsetGraphAt w b ⟩
                 → IsOrd (fst (lookup b γ))
                 → fst (lookup b γ) ≡ fst (lookup b δ)
                 → fst (lookup w γ) ≡ fst (lookup w δ)
pins-at-most-one w b γ δ hg hd ob eq =
  pins w b γ hg ob ∙ cong Lset eq ∙
  sym (pins w b δ hd (subst IsOrd eq ob))

-- The same uniqueness without IsOrd.  Stated.  Unbuilt.
-- Same type as agents/tasks/LJ-1-458/Probe458.agda:69-73.

pins-no-ord : Type _
pins-no-ord =
    ∀ {n} (w b : Fin n) (γ : S ^ n)
  → ⟨ γ ⊨ LsetGraphAt w b ⟩
  → fst (lookup w γ) ≡ Lset (fst (lookup b γ))

-- =====================================================================
-- D-10 TYPES AT THE HULL.  Obligation omitted.  There is no term
-- named HullClosedLset.  The witness meter must report UNRESOLVED.
-- Telescope copied from src/L/BoundedSubset.lagda.md:903-914.
-- Nothing below module Condense is copied.
-- =====================================================================

module HullStage (lam : SV) (ordλ : IsOrd lam)
  (succλ : (d : SV) → ⟨ d ∈ᵥ lam ⟩ → ⟨ sucV d ∈ᵥ lam ⟩)
  (X : SV) (X⊆L : (x : SV) → ⟨ x ∈ᵥ X ⟩ → ⟨ x ∈ᵥ Lset lam ⟩)
  (∅∈λ : ⟨ ∅ ∈ᵥ lam ⟩) where

  module ASt = AtStage lam ordλ

  module H = ASt.Hull X X⊆L ∅∈λ

  M : SV
  M = H.T.Hull

  -- IsOrd at a hull member.  NO SOURCE.  hull-member at
  -- src/L/Hull.lagda.md:337-339 returns a Code, not an ordinal.
  -- Hull⊆L at :330-334 places the member in Lset α.  Code has
  -- constructors base and wit only (:72-74).

  OrdFromHull : Type (ℓ-suc ℓ)
  OrdFromHull = (y : SV) → ⟨ y ∈ᵥ M ⟩ → IsOrd y

  -- Predecessor step 2, restated.  Unbuilt.  Not named HullClosedLset.
  -- Quote: agents/tasks/LJ-1-462/Probe462.agda:136-138.

  ClosedLset : Type (ℓ-suc ℓ)
  ClosedLset =
    (y : SV) → ⟨ y ∈ᵥ M ⟩ → ⟨ Lset y ∈ᵥ M ⟩

  -- The join the brief names, as a type.  Unbuilt.  feed then inHull
  -- gives val (wit ...) ∈ M.  pins replaces that value by Lset y only
  -- with IsOrd y.  OrdFromHull is unbuilt.

  JoinNeedsOrd : Type (ℓ-suc ℓ)
  JoinNeedsOrd = OrdFromHull → ClosedLset
