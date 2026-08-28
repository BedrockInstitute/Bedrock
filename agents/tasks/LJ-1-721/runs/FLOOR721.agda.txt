{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.721] PROBE.  [LJ-1.720]'s packing, exported at the name the
-- witness meter reads: pack-stage and PackStage at the FILE'S top
-- level, outside module Pack.  Lands nothing in src/.
--
--   THE OBLIGATION  pack-stage : PackStage, both names at the top
--                   level.  The frame, the three lemmas and the
--                   packing are transcribed verbatim from
--                   Probe720.agda:39-111; the ONE new content is the
--                   export.
--   W3              whether a top-level alias of the nested
--                   pack-stage still checks (the brief, basis
--                   lj-1.720-report.md:13).
--
-- Check order: floor with all bodies holed first (the 2026-08-23
-- ruling, coder slot file), then the delivered shape, then the warm
-- recheck.  Do not inhabit Completeness.
--
-- ONE Agda process per run, GHCRTS="-A64m -I0 -M2g", the wide
-- caliber, set on the pane by the program and untouched here.
-- Nothing is postulated.  No hole in the delivered file.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-721.Probe721 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ} using ( 𝒮ʟ; IsOrd; Lset; Lset→isL )
open import L.Hierarchy {ℓ} lem using ( hierL )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ∅; module InfinitySet )
open InfinitySet {ℓ} using ( sucV )
open import Cubical.Data.Vec using ( _∷_; [] )

open import LJ-1-652.Probe652 {ℓ} lem as P652
import LJ-1-679.Probe679 {ℓ} lem as P679

open hPropStructure 𝒮ᵥ
module CS = hPropStructure 𝒮ʟ

open P679 using ( SameHyp )

-- =====================================================================
-- THE FRAME.  Probe720.Pack's telescope, not rebuilt.
-- =====================================================================

module Pack (lam : S) (ordλ : IsOrd lam)
  (succλ : (d : S) → ⟨ d ∈ˢ lam ⟩ → ⟨ sucV d ∈ˢ lam ⟩)
  (X : S) (X⊆Lλ : (z : S) → ⟨ z ∈ˢ X ⟩ → ⟨ z ∈ˢ Lset lam ⟩)
  (∅∈λ : ⟨ ∅ ∈ˢ lam ⟩)
  (elem : P652.Frame652.A.Elementary lam ordλ succλ X X⊆Lλ ∅∈λ) where

  module A = P679.At lam ordλ succλ X X⊆Lλ ∅∈λ elem
  open A using ( HierInStage; Code; val )
  module F = P652.Frame652 lam ordλ succλ X X⊆Lλ ∅∈λ

  -- [LJ-1.720]'s toL, verbatim.  Codomain explicit: CS.S.
  toL : F.HS.ASt.SL → CS.S
  toL x = fst x , Lset→isL lam ordλ (fst x) (snd x)

  -- [LJ-1.720]'s same-at-codes, verbatim.  Codomain explicit.
  same-at-codes : SameHyp
                → (ca cp : Code)
                → P679.SameAsGraph zero (suc zero)
                    (toL (val ca) ∷ toL (val cp) ∷ [])
  same-at-codes same ca cp =
    same zero (suc zero) (toL (val ca) ∷ toL (val cp) ∷ [])

  -- [LJ-1.720]'s hier-at-code, verbatim.  Codomain explicit.
  hier-at-code : HierInStage
               → (cp : Code)
               → (o : IsOrd (fst (val cp)))
               → ⟨ fst (hierL (fst (val cp)) (toL (val cp) .snd) o)
                   ∈ˢ Lset lam ⟩
  hier-at-code hier cp o = hier (toL (val cp)) o (val cp .snd)

  -- ===================================================================
  -- THE PACKING.  [LJ-1.720]'s PackStage and pack-stage, verbatim
  -- (Probe720.agda:98-111).  The second and third components are
  -- typed AT the packed function, so the packing is coherent, not
  -- three loose pieces; at the binder the pair is read by its own
  -- projections.
  -- ===================================================================

  PackStage : Type (ℓ-suc ℓ)
  PackStage =
    Σ[ pack ∈ (F.HS.ASt.SL → CS.S) ]
    Σ[ same ∈ (SameHyp → (ca cp : Code)
              → P679.SameAsGraph zero (suc zero)
                  (pack (val ca) ∷ pack (val cp) ∷ [])) ]
    ( HierInStage
    → (cp : Code)
    → (o : IsOrd (pack (val cp) .fst))
    → ⟨ fst (hierL (pack (val cp) .fst) (pack (val cp) .snd) o)
        ∈ˢ Lset lam ⟩ )

  pack-stage : PackStage
  pack-stage = toL , same-at-codes , hier-at-code

-- =====================================================================
-- THE EXPORT.  The names the witness meter reads, at the FILE'S top
-- level, the [LJ-1.709] form (Probe709.agda:77): a bare alias of the
-- nested name, no ascription.  The module telescope becomes the
-- leading arguments, so the exported pack-stage is the same packing
-- at its own seven hypotheses.
-- =====================================================================

PackStage = Pack.PackStage

pack-stage = Pack.pack-stage

-- Completeness is NOT inhabited here, and BoundInStage is not
-- reached: this task is the packing at its export name.  See
-- lj-1.721-report.md.
