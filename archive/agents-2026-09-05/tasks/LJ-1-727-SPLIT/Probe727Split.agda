{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.727-SPLIT] PROBE.  The supply name the meter can close.
-- Transcribed from [LJ-1.727]'s delivered file: At727's pack, toL,
-- same-at-codes, graph-at-pair and level-at-pair
-- (agents/tasks/LJ-1-727/Probe727.agda:83-145), into a fresh file,
-- so the live meter's obligation Probe727Split.agda::level-at-pair
-- has supply.  Lands nothing in src/.
--
--   THE OBLIGATION  level-at-pair : SameHyp → (ca cp : Code) →
--                   IsOrd (fst (val cp)) → fst (val ca) ≡
--                   Lset (fst (val cp)) → ⟨ (toL (val ca) ∷
--                   toL (val cp) ∷ []) ⊨ᵐ fst (levelFo-Σ₁ zero
--                   (suc zero)) ⟩.  The term 727 delivered green,
--                   exported at its file's top level
--                   (Probe727.agda:166); this file re-measures the
--                   alias form in a fresh file.
--   WHAT IS ABSENT  727's own obligation, CompletenessFrom from the
--                   packing.  Its W3 is answered NO there, the
--                   verdict is
--                   agents/tasks/LJ-1-727/review-of-completeness-from-pack.md,
--                   and the obligation name is absent from this file
--                   on the same grounds: only the supply term moved.
--   WHAT IS TRIMMED  727's hier-at-code, cfp-shape and
--                   bounded-demand (they serve 727's obligation
--                   shape, not the supply term), and the imports
--                   only they used (hierL, Lset→isL).
--
-- ONE Agda process per run, GHCRTS="-A64m -I0 -M2g", the wide
-- caliber, set on the pane by the program and untouched here.
-- Nothing is postulated.  No hole in the delivered file.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-727-SPLIT.Probe727Split {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ}
  using ( 𝒮ʟ; isL; isL-trans; IsOrd; Lset )
open import L.Hierarchy {ℓ} lem using ( Lset-defines )
open import L.Coding.Sequence {ℓ} lem using ( LsetGraphAt )
open import Cubical.Data.Vec using ( _∷_; [] )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ∅; module InfinitySet )
open InfinitySet {ℓ} using ( sucV )

open import LJ-1-652.Probe652 {ℓ} lem as P652
import LJ-1-520.Probe520 {ℓ} lem as P520
import LJ-1-679.Probe679 {ℓ} lem as P679
import LJ-1-721.Probe721 {ℓ} lem as P721

open hPropStructure 𝒮ᵥ
module CS = hPropStructure 𝒮ʟ

-- Hierarchy's own instance (src/L/Hierarchy.lagda.md:78-79): the
-- same Single 𝒮ᵥ isL isL-trans that P520's SameAsGraph and
-- Lset-defines are stated at, so the compositions below elaborate
-- at one satisfaction relation.
module AL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans

open P679 using ( SameHyp )

-- =====================================================================
-- THE FRAME.  Probe679.At's telescope, not rebuilt (Probe700's Spend,
-- Probe721's Pack and Probe727's At727 are the precedents).
-- =====================================================================

module At727Split (lam : S) (ordλ : IsOrd lam)
  (succλ : (d : S) → ⟨ d ∈ˢ lam ⟩ → ⟨ sucV d ∈ˢ lam ⟩)
  (X : S) (X⊆Lλ : (z : S) → ⟨ z ∈ˢ X ⟩ → ⟨ z ∈ˢ Lset lam ⟩)
  (∅∈λ : ⟨ ∅ ∈ˢ lam ⟩)
  (elem : P652.Frame652.A.Elementary lam ordλ succλ X X⊆Lλ ∅∈λ) where

  module A = P679.At lam ordλ succλ X X⊆Lλ ∅∈λ elem
  module F = P652.Frame652 lam ordλ succλ X X⊆Lλ ∅∈λ

  -- -------------------------------------------------------------------
  -- PACK, CONSUMED AT [LJ-1.721]'s EXPORT NAME.  The three components
  -- are read off the packing by its projections, one argument list
  -- earlier than 720's consumption (lj-1.721-report.md:10).
  -- -------------------------------------------------------------------

  pack : P721.PackStage lam ordλ succλ X X⊆Lλ ∅∈λ elem
  pack = P721.pack-stage lam ordλ succλ X X⊆Lλ ∅∈λ elem

  toL : F.HS.ASt.SL → CS.S
  toL = fst pack

  -- Component two, fired.  SameAsGraph at the packed pair, the
  -- [LJ-1.700] firing (Probe700.agda:53-58) at the export name.
  same-at-codes : SameHyp
                → (ca cp : A.Code)
                → P679.SameAsGraph zero (suc zero)
                    (toL (A.val ca) ∷ toL (A.val cp) ∷ [])
  same-at-codes same ca cp = fst (snd pack) same ca cp

  -- -------------------------------------------------------------------
  -- THE GRAPH SIDE, FIRED.  Lset-defines (src/L/Hierarchy.lagda.md:
  -- 644-653) at the packed pair: IsOrd on the parameter and the level
  -- equation give the UNBOUNDED graph reading.
  -- -------------------------------------------------------------------

  graph-at-pair : SameHyp
                → (ca cp : A.Code)
                → IsOrd (fst (A.val cp))
                → fst (A.val ca) ≡ Lset (fst (A.val cp))
                → ⟨ (toL (A.val ca) ∷ toL (A.val cp) ∷ [])
                    AL.⊨ᵐ LsetGraphAt zero (suc zero) ⟩
  graph-at-pair same ca cp ocp q =
    Lset-defines zero (suc zero)
      (toL (A.val ca) ∷ toL (A.val cp) ∷ []) ocp q

  -- -------------------------------------------------------------------
  -- THE SUPPLY TERM.  SameHyp's levelFo direction consumes the graph
  -- reading: the UNBOUNDED level reading at the packed pair.  Green
  -- in [LJ-1.727]; the tracked delivery of THIS task is the same term
  -- under the same name, in a fresh file, so the meter can read it.
  -- -------------------------------------------------------------------

  level-at-pair : SameHyp
                → (ca cp : A.Code)
                → IsOrd (fst (A.val cp))
                → fst (A.val ca) ≡ Lset (fst (A.val cp))
                → ⟨ (toL (A.val ca) ∷ toL (A.val cp) ∷ [])
                    AL.⊨ᵐ fst (P520.levelFo-Σ₁ zero (suc zero)) ⟩
  level-at-pair same ca cp ocp q =
    snd (same-at-codes same ca cp) (graph-at-pair same ca cp ocp q)

-- =====================================================================
-- THE EXPORT.  The supply term at the file's top level, the
-- [LJ-1.709]/[LJ-1.721]/[LJ-1.727] alias form: the module telescope
-- becomes the leading arguments.  This is the name the meter reads.
-- =====================================================================

level-at-pair = At727Split.level-at-pair
