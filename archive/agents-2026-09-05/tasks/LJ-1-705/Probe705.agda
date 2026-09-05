{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.705] PROBE.  The bounding stage of bound-of lies in the
-- bridge's alpha.  Lands nothing in src/.
--
--   THE OBLIGATION  bound-in-alpha.  NOT INHABITED.
--                   review-of-bound-in-alpha.md states the stop.
--   PREDECESSOR     bound-of, Probe698.agda:97-101, GO and total.
--                   empty-in-limit, Probe698.agda:184-185, GO.
--                   through-door is NO-GO there and is not inhabited.
--   NOT INHABITED   ThroughDoor. ApproxInK (532 FALSE).
--
-- D-10.  The target is not shown false.  mkBoundedFo's stage is the
-- bound2-tree of the stages of the formula's constants.  Those
-- constants are γ, Lset γ, and numerals (tagAtL).  arityNumAtL names
-- ωʟ; isCodeAt uses keyArityAtL, not arityNumAtL.  ω is not among
-- this formula's constants.  A limit that contains γ contains
-- sucV γ, and both stage(γ) and stage(Lset γ) sit at or below that.
--
-- WHAT WAS TRIED.  bound2-in-limit (a limit contains bound2 of two
-- of its members) is the lemma the recursion needs.  Under the 698
-- cone it heap-walled at 1.82 GB (runs/p-14.out).  Stripped to a
-- trimmed frame, the sett-membership of Lift Bool did not convert
-- to the pairing reading ⁅ sucV σ₁ , sucV σ₂ ⁆ (runs/p-21.out,
-- UnequalTerms).  bound2's internal f is not our f (runs/p-26.out).
-- The obligation name is absent on purpose.  No postulate.
--
-- ONE Agda process per run, GHCRTS wide caliber, set on the pane by
-- the program and untouched here.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-705.Probe705 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import L.Constructible {ℓ} using ( isL; IsOrd )
open import LJ-1-693.Probe693 {ℓ} lem using ( IsLimit )
open import LJ-1-698.Probe698 {ℓ} lem using ( bound-of )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )

-- =====================================================================
-- SECTION 1.  THE TYPE.  Verbatim the unpaid row of
-- lj-1.698-report.md:42, at the bound-of the predecessor delivered.
-- =====================================================================

the-type : Type (ℓ-suc ℓ)
the-type =
    (α : V ℓ) → IsLimit α
  → (γ : V ℓ) (oγ : IsOrd γ) (hγ : ⟨ isL γ ⟩) → ⟨ γ ∈ α ⟩
  → ⟨ fst (bound-of γ oγ hγ) ∈ α ⟩

-- =====================================================================
-- SECTION 2.  THE OBLIGATION NAME IS ABSENT ON PURPOSE.  No postulate
-- stands in for it.  bound2-in-limit did not close under this
-- caliber; review-of-bound-in-alpha.md states the stop.
-- =====================================================================
