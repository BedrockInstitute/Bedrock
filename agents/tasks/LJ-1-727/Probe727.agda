{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.727] PROBE.  CompletenessFrom from the packing, at
-- [LJ-1.679]'s types.  Lands nothing in src/.
--
--   THE OBLIGATION  completeness-from-pack : SameHyp → HierInStage →
--                   Completeness.  The name is DELIBERATELY ABSENT
--                   from this file, the [LJ-1.718] idiom: the witness
--                   meter reads the truth (MISSING).  The NO-GO is
--                   stated in review-of-completeness-from-pack.md.
--   WHAT IS GREEN   pack consumed at [LJ-1.721]'s export name, all
--                   three components; Lset-defines fired at the
--                   packed pair; and `level-at-pair`, the SUPPLY term:
--                   SameHyp plus IsOrd plus the level equation close
--                   the UNBOUNDED level reading at the packed pair.
--                   Exported at the file's top level, the [LJ-1.721]
--                   alias form, so the successor consumes it.
--   WHAT IS OPEN    the BOUNDED demand.  inBound's matrix is
--                   W3.three at (a, p, z): its table slot IS the
--                   witness z and its twelve numerals are members of
--                   z (agents/tasks/LJ-1-667/runs/W3.agda, Mx and
--                   wrap).  The supply reaches the UNBOUNDED reading,
--                   whose table and numerals are free existentials
--                   (src/L/Condensation.lagda.md:2491, graphBndAt's
--                   own bound excepted).  No hypothesis provides a z.
--
-- Check order: floor with all four bodies holed first (the
-- 2026-08-23 ruling, coder slot file), then the delivered shape,
-- then the warm recheck.  Do not inhabit Completeness.
--
-- ONE Agda process per run, GHCRTS="-A64m -I0 -M2g", the wide
-- caliber, set on the pane by the program and untouched here.
-- Nothing is postulated.  No hole in the delivered file.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-727.Probe727 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ}
  using ( 𝒮ʟ; isL; isL-trans; IsOrd; Lset; Lset→isL )
open import L.Hierarchy {ℓ} lem using ( hierL; Lset-defines )
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
-- Lset-defines are stated at, so the three compositions below
-- elaborate at one satisfaction relation.
module AL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans

open P679 using ( SameHyp )

-- =====================================================================
-- THE FRAME.  Probe679.At's telescope, not rebuilt (Probe700's Spend
-- and Probe721's Pack are the precedents).
-- =====================================================================

module At727 (lam : S) (ordλ : IsOrd lam)
  (succλ : (d : S) → ⟨ d ∈ˢ lam ⟩ → ⟨ sucV d ∈ˢ lam ⟩)
  (X : S) (X⊆Lλ : (z : S) → ⟨ z ∈ˢ X ⟩ → ⟨ z ∈ˢ Lset lam ⟩)
  (∅∈λ : ⟨ ∅ ∈ˢ lam ⟩)
  (elem : P652.Frame652.A.Elementary lam ordλ succλ X X⊆Lλ ∅∈λ) where

  module A = P679.At lam ordλ succλ X X⊆Lλ ∅∈λ elem
  open A using ( HierInStage; Completeness ) renaming
    ( BoundInStage to A-BoundInStage )
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

  -- Component three, fired.  The stage membership of the internal
  -- table at the parameter code.
  hier-at-code : HierInStage
               → (cp : A.Code)
               → (o : IsOrd (fst (A.val cp)))
               → ⟨ fst (hierL (fst (A.val cp)) (toL (A.val cp) .snd) o)
                   ∈ˢ Lset lam ⟩
  hier-at-code hier cp o = snd (snd pack) hier cp o

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
  -- reading: the UNBOUNDED level reading at the packed pair, green.
  -- This is the last honest stop of the graph leg, and it is the
  -- tracked delivery of this task: the successor consumes it at the
  -- top-level name instead of restating the three bodies.
  -- -------------------------------------------------------------------

  level-at-pair : SameHyp
                → (ca cp : A.Code)
                → IsOrd (fst (A.val cp))
                → fst (A.val ca) ≡ Lset (fst (A.val cp))
                → ⟨ (toL (A.val ca) ∷ toL (A.val cp) ∷ [])
                    AL.⊨ᵐ fst (P520.levelFo-Σ₁ zero (suc zero)) ⟩
  level-at-pair same ca cp ocp q =
    snd (same-at-codes same ca cp) (graph-at-pair same ca cp ocp q)

  -- -------------------------------------------------------------------
  -- THE OBLIGATION'S SHAPE, AND THE BOUNDED DEMAND.  Stated as types,
  -- never inhabited, never named completeness-from-pack.
  -- -------------------------------------------------------------------

  cfp-shape : Type (ℓ-suc ℓ)
  cfp-shape = SameHyp → HierInStage → Completeness

  -- The demand the supply must reach, read at
  -- agents/tasks/LJ-1-673/Probe673.agda:93-95.
  bounded-demand : (ca cp : A.Code) → Type (ℓ-suc ℓ)
  bounded-demand ca cp = A-BoundInStage ca cp

-- =====================================================================
-- THE EXPORT.  The supply term at the file's top level, the
-- [LJ-1.709]/[LJ-1.721] alias form: the module telescope becomes the
-- leading arguments.
-- =====================================================================

level-at-pair = At727.level-at-pair

-- Completeness is NOT inhabited here, and the obligation name is
-- absent on purpose.  See review-of-completeness-from-pack.md and
-- lj-1.727-report.md.
