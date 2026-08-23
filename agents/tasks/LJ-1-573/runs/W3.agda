{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.573]  W3, THE WIDEST UNMEASURED TERM, WRITTEN FIRST AND ALONE.
--
-- The brief names it `SqFam` itself, written as
--
--     -- SqFam α, unfolded one step, TYPE ONLY
--
-- and says: "What the family has to BE decides whether a formula can
-- pick it."  This file is TYPE ONLY: no inhabitant, no hole, no
-- postulate.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-573.runs.W3 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ} using ( 𝒮ʟ; IsOrd )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet )
open InfinitySet {ℓ} using ( ω; sucV )
open import Cubical.HITs.CumulativeHierarchy.Properties
  using ( ⟪_⟫ )
open import Cubical.Data.Sigma using ( _×_ )
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ using ( _∈ˢ_ )

module SV = hPropStructure 𝒮ᵥ
module SL = hPropStructure 𝒮ʟ

-- ---------------------------------------------------------------------
-- 1.  `SqFam (fst κ)` UNFOLDED ONE STEP.  TYPE ONLY.
--
--   Copied from src/L/StageBound.lagda.md:37-40 with `α := fst κ`.
--   READ THE CODOMAIN.  It is a Σ of an AMBIENT function `⟪ δ ⟫ × ⟪ δ ⟫
--   → ⟪ δ ⟫` and a proof that it is injective.  There is no code, no
--   `isL`, no `Lset`, no `𝒮ʟ` and no `⊨` anywhere under the arrow.
--   A formula of the object language can carve nothing here: there is
--   nothing here for it to carve.
-- ---------------------------------------------------------------------

w3-sqfam-at : SL.S → Type (ℓ-suc ℓ)
w3-sqfam-at κ =
    (δ : SV.S) → ⟨ δ ∈ˢ sucV (fst κ) ⟩ → (⟨ δ ∈ˢ ω ⟩ → Empty.⊥)
  → Σ[ f ∈ (⟪ δ ⟫ × ⟪ δ ⟫ → ⟪ δ ⟫) ]
      ((u v : ⟪ δ ⟫ × ⟪ δ ⟫) → f u ≡ f v → u ≡ v)

-- ---------------------------------------------------------------------
-- 2.  THE SAME FAMILY, RE-INDEXED OVER THE MEMBERS OF `sucV (fst κ)`.
--   TYPE ONLY.
--
--   THIS IS THE LINE THAT DECIDES THE TASK.  Collect the binder and the
--   two side conditions into ONE index type and the family becomes a
--   plain `(x : Ix κ) → sq (fst x)`: a Π over an h-SET of a Σ of
--   ambient functions.  That is `SetChoice`'s argument shape letter for
--   letter (src/Base/Choice.lagda.md:54-56).
--
--   AND THE LEVEL IS `ℓ-suc ℓ`, WHICH THE MACHINE MEASURED RATHER THAN
--   ME GUESSING IT.  I first wrote `Ix` at `Type ℓ`, because
--   `⟪ sucV (fst κ) ⟫` and `sq δ` both live at `Type ℓ`.  Agda refused:
--   "Type (ℓ-suc ℓ) != Type ℓ" (agents/tasks/LJ-1-573/runs/w3-1.out:4-5).
--   The reason is the SIDE CONDITIONS.  This chapter's `_∈ˢ_` is read
--   through `TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))`, so
--   `⟨ δ ∈ˢ sucV (fst κ) ⟩` is at `Type (ℓ-suc ℓ)` and it drags the
--   whole index up with it.
--
--   SO THE PRINCIPLE THIS ROW WANTS IS `SetChoice (ℓ-suc ℓ)` AND NOT
--   `SetChoice ℓ`.  That is the owner's own phrase, word for word, in
--   the charge of [LJ-1.376] (agents/tasks/LJ-1-376/LJ-1.376.md:11).
-- ---------------------------------------------------------------------

w3-Ix : SL.S → Type (ℓ-suc ℓ)
w3-Ix κ =
  Σ[ δ ∈ SV.S ]
    (⟨ δ ∈ˢ sucV (fst κ) ⟩ × (⟨ δ ∈ˢ ω ⟩ → Empty.⊥))

w3-sqfam-indexed : SL.S → Type (ℓ-suc ℓ)
w3-sqfam-indexed κ =
    (x : w3-Ix κ)
  → Σ[ f ∈ (⟪ fst x ⟫ × ⟪ fst x ⟫ → ⟪ fst x ⟫) ]
      ((u v : ⟪ fst x ⟫ × ⟪ fst x ⟫) → f u ≡ f v → u ≡ v)

-- ---------------------------------------------------------------------
-- 3.  AND THE ROW ITSELF, ONE STEP FURTHER OUT.  TYPE ONLY.
--
--   `SqCollect` (src/L/StageBound.lagda.md:44-48) at every ordinal
--   L-cardinal.  Its ANTECEDENT is the pointwise truncation and its
--   CONSEQUENT is the truncated family.  Written out, the shape
--   `(Π x . ∥ B x ∥₁) → ∥ Π x . B x ∥₁` is visible with no unfolding
--   at all.
-- ---------------------------------------------------------------------

w3-sqcollect-at : Type (ℓ-suc ℓ)
w3-sqcollect-at =
    (κ : SL.S) → IsOrd (fst κ)
  → (   (δ : SV.S) → ⟨ δ ∈ˢ sucV (fst κ) ⟩ → (⟨ δ ∈ˢ ω ⟩ → Empty.⊥)
      → ∥ Σ[ f ∈ (⟪ δ ⟫ × ⟪ δ ⟫ → ⟪ δ ⟫) ]
            ((u v : ⟪ δ ⟫ × ⟪ δ ⟫) → f u ≡ f v → u ≡ v) ∥₁)
  → ∥ w3-sqfam-at κ ∥₁
