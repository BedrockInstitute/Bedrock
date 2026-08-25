{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.640]  W3, TYPECHECKED ALONE.
--
-- THE WIDEST UNMEASURED TERM the brief names: "Whether `IsCardinalL κ`
-- pins `κ` as a least element of anything."
--
-- THE ANSWER IN ONE LINE.  It does, and at the CODED predicate only.
-- The tree's least-cardinal site `κL a oa` is least at the AMBIENT
-- predicate.  The two predicates are ordered ONE WAY in the tree, and
-- the missing way is exactly [LJ-1.533]'s `AmbToCodeᵀ`.
--
-- NOTHING IN THIS FILE IS POSTULATED and nothing has a hole.  The two
-- named types `IntToAmb` and `P533.AmbToCodeᵀ` are NAMED, NOT
-- INHABITED, and `gap-is-the-crossing` says the first follows from the
-- second.
--
-- CALIBER.  The program set GHCRTS on this pane.  I did not set it.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-640.runs.W3 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫ )
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁ )
open import L.Constructible {ℓ} using ( 𝒮ʟ; IsOrd )
open import L.Ordinal {ℓ} using ( mem-ord )
open import L.Cardinal {ℓ} lem using ( IsCardinalL; InjCode; _↪_ )
open import L.BoundedSubset {ℓ} lem using ( IsCardinal )
open import L.CardinalAbove {ℓ} lem using ( ambient→internal; ordL )
import LJ-1-533.Probe533
module P533 = LJ-1-533.Probe533 {ℓ} lem

module SV = hPropStructure 𝒮ᵥ
module SL = hPropStructure 𝒮ʟ
open SV using ( _∈ˢ_ )

-- =====================================================================
-- SECTION 1.  THE TWO MINIMALITIES, WRITTEN SIDE BY SIDE.
--
--   `AmbMinimalAt κ` is the shape `c4-from-min` wants at a site
--   (agents/tasks/LJ-1-638/Probe638.agda:215, its second hypothesis,
--   at X := ⟪ fst κ ⟫), and it is the shape `κ-min-atL` delivers
--   (src/L/SquareLawClosed.lagda.md:86-89, at source `fst a`).
-- =====================================================================

AmbMinimalAt : SL.S → Type (ℓ-suc ℓ)
AmbMinimalAt κ =
  (δ : SL.S) → ⟨ fst δ ∈ˢ fst κ ⟩ → ∥ ⟪ fst κ ⟫ ↪ ⟪ fst δ ⟫ ∥₁ → Empty.⊥

-- `IsCardinalL` IS a minimality already, and this row is the identity:
-- it says so at the type level.  The predicate it is least at is the
-- CODED one (src/L/Cardinal.lagda.md:230-233).
coded-minimal :
    (κ : SL.S) → IsCardinalL κ
  → (δ : SL.S) → ⟨ fst δ ∈ˢ fst κ ⟩
  → ∥ Σ[ F ∈ SL.S ] InjCode F κ δ ∥₁ → Empty.⊥
coded-minimal κ c = c

-- The ambient cardinal predicate IS ambient minimality, up to the
-- truncation, which a ⊥-valued goal absorbs.
amb-card→amb-minimal : (κ : SL.S) → IsCardinal (fst κ) → AmbMinimalAt κ
amb-card→amb-minimal κ c δ δ∈κ = PT.rec Empty.isProp⊥ (c (fst δ) δ∈κ)

-- =====================================================================
-- SECTION 2.  THE DIRECTION THE TREE HAS, TAKEN BY IMPORT.
--
--   `ambient→internal` (src/L/CardinalAbove.lagda.md:102-104) runs
--   AMBIENT to INTERNAL through `readL`.  This row is an import check:
--   it typechecks only if the src/ row still has exactly this type.
-- =====================================================================

delivered-direction : (κ : SL.S) → IsCardinal (fst κ) → IsCardinalL κ
delivered-direction = ambient→internal

-- =====================================================================
-- SECTION 3.  THE DIRECTION THE TREE DOES NOT HAVE, AND WHAT IT IS.
--
--   NAMED, NOT INHABITED.  `IntToAmb` is the missing converse.
--   `gap-is-the-crossing` measures that it is not a new wall: it is
--   [LJ-1.533]'s `AmbToCodeᵀ` (agents/tasks/LJ-1-533/Probe533.agda:
--   111-114), TAKEN BY IMPORT AND NOT COPIED, so the two cannot drift.
--   [LJ-1.533] recorded that crossing as having no producer in the
--   tree: "Code buys ambient.  Ambient buys nothing."
-- =====================================================================

IntToAmb : Type (ℓ-suc ℓ)
IntToAmb = (κ : SL.S) → IsOrd (fst κ) → IsCardinalL κ → IsCardinal (fst κ)

gap-is-the-crossing : P533.AmbToCodeᵀ → IntToAmb
gap-is-the-crossing code κ oκ cκ δ δ∈κ f = cκ δᴸ δ∈κ (code κ δᴸ f)
  where
  δᴸ : SL.S
  δᴸ = ordL δ (mem-ord {A = fst κ} oκ δ δ∈κ)
