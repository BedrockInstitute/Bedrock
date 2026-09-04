{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.720] PROBE.  [LJ-1.700]'s three stage lemmas, packed as ONE
-- term, each with an EXPLICIT codomain and no `_`.  Lands nothing in
-- src/.
--
--   THE OBLIGATION  pack-stage.  toL, same-at-codes and
--                   hier-at-code, bodies verbatim from
--                   Probe700.agda:57-74.  The `_` codomain of
--                   Probe700.agda:73, the site the critic named the
--                   likeliest cause of the 2.3 GB kills
--                   (review-of-LJ-1-700-1.md:138-144), is written
--                   out.
--   W3              whether the explicit codomain sits under the
--                   wide cap, measured in runs/.
--
-- Check order: floor with hole bodies first (the 2026-08-23 ruling),
-- then the lemmas one at a time, toL and same-at-codes, then
-- hier-at-code.  Do not inhabit Completeness.
--
-- ONE Agda process per run, GHCRTS="-A64m -I0 -M2g", the wide
-- caliber, set on the pane by the program and untouched here.
-- Nothing is postulated.  No hole.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-720.Probe720 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

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
-- THE FRAME.  Probe700.Spend's telescope, not rebuilt.
-- =====================================================================

module Pack (lam : S) (ordλ : IsOrd lam)
  (succλ : (d : S) → ⟨ d ∈ˢ lam ⟩ → ⟨ sucV d ∈ˢ lam ⟩)
  (X : S) (X⊆Lλ : (z : S) → ⟨ z ∈ˢ X ⟩ → ⟨ z ∈ˢ Lset lam ⟩)
  (∅∈λ : ⟨ ∅ ∈ˢ lam ⟩)
  (elem : P652.Frame652.A.Elementary lam ordλ succλ X X⊆Lλ ∅∈λ) where

  module A = P679.At lam ordλ succλ X X⊆Lλ ∅∈λ elem
  open A using ( HierInStage; Code; val )
  module F = P652.Frame652 lam ordλ succλ X X⊆Lλ ∅∈λ

  -- [LJ-1.700]'s toL, verbatim.  Codomain explicit: CS.S.
  toL : F.HS.ASt.SL → CS.S
  toL x = fst x , Lset→isL lam ordλ (fst x) (snd x)

  -- [LJ-1.700]'s same-at-codes, verbatim.  Codomain explicit.
  same-at-codes : SameHyp
                → (ca cp : Code)
                → P679.SameAsGraph zero (suc zero)
                    (toL (val ca) ∷ toL (val cp) ∷ [])
  same-at-codes same ca cp =
    same zero (suc zero) (toL (val ca) ∷ toL (val cp) ∷ [])

  -- [LJ-1.700]'s hier-at-code, body verbatim, codomain WRITTEN OUT.
  -- The `_` of Probe700.agda:73 becomes the application's own result
  -- type: hier at δ := toL (val cp) lands in the membership of hierL
  -- at the unpacked stage.  fst (toL (val cp)) is definitionally
  -- fst (val cp), so the ascription is the application's type.
  hier-at-code : HierInStage
               → (cp : Code)
               → (o : IsOrd (fst (val cp)))
               → ⟨ fst (hierL (fst (val cp)) (toL (val cp) .snd) o)
                   ∈ˢ Lset lam ⟩
  hier-at-code hier cp o = hier (toL (val cp)) o (val cp .snd)

  -- ===================================================================
  -- THE OBLIGATION.  The three lemmas, packed as one term.  Each
  -- component carries the lemma's own type, explicit; nothing is
  -- inferred.  The second and third components are typed AT the
  -- packed function, so the packing is coherent, not three loose
  -- pieces.  AT the binder the pair is read by its own projections:
  -- pack (val cp) is a bound application and does not reduce, so
  -- .fst/.snd are the only honest names.  At the delivered term the
  -- function IS toL, and toL (val cp) .fst reduces to fst (val cp),
  -- so the components are [LJ-1.700]'s own types there.
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

-- pack-stage is defined.  Completeness is NOT inhabited here, and
-- BoundInStage is not reached: this task is the packing only.  See
-- lj-1.720-report.md.
