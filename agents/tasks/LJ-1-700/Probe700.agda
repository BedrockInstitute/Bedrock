{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.700] PROBE.  CompletenessFrom at [LJ-1.679], SameHyp and
-- HierInStage as HYPOTHESES.  Lands nothing in src/.
--
--   W3              whether SameHyp is free at this frame
--                   (agents/tasks/LJ-1-679/lj-1.679-report.md:1).
--   THE OBLIGATION  completeness-from-hier.  Completeness at
--                   matrix₃ via CompletenessFrom
--                   (Probe679.agda:94-95).  Not defined: the two
--                   hypotheses fire at the packed codes and do not
--                   reach BoundInStage.
--
-- ONE Agda process per run, GHCRTS="-A64m -I0 -M2g", the wide
-- caliber, set on the pane by the program and untouched here.
-- Nothing is postulated.  No hole.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-700.Probe700 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ} using ( 𝒮ʟ; IsOrd; Lset; Lset→isL )
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
-- THE FRAME.  Probe679.At's telescope, not rebuilt.
-- =====================================================================

module Spend (lam : S) (ordλ : IsOrd lam)
  (succλ : (d : S) → ⟨ d ∈ˢ lam ⟩ → ⟨ sucV d ∈ˢ lam ⟩)
  (X : S) (X⊆Lλ : (z : S) → ⟨ z ∈ˢ X ⟩ → ⟨ z ∈ˢ Lset lam ⟩)
  (∅∈λ : ⟨ ∅ ∈ˢ lam ⟩)
  (elem : P652.Frame652.A.Elementary lam ordλ succλ X X⊆Lλ ∅∈λ) where

  module A = P679.At lam ordλ succλ X X⊆Lλ ∅∈λ elem
  open A using ( HierInStage; Code; val )
  module F = P652.Frame652 lam ordλ succλ X X⊆Lλ ∅∈λ

  -- W3.  SameHyp is not free: AbsL's carrier is not 𝒮ʟ.  Members of
  -- Lset lam are constructible (Lset→isL,
  -- src/L/Constructible.lagda.md:405-406), so a stage pair packs.
  toL : F.HS.ASt.SL → CS.S
  toL x = fst x , Lset→isL lam ordλ (fst x) (snd x)

  -- SameHyp applied at the packed codes.  Not free; it applies.
  same-at-codes : SameHyp
                → (ca cp : Code)
                → P679.SameAsGraph zero (suc zero)
                    (toL (val ca) ∷ toL (val cp) ∷ [])
  same-at-codes same ca cp =
    same zero (suc zero) (toL (val ca) ∷ toL (val cp) ∷ [])

  -- HierInStage applied at the parameter code.  The parameter is a
  -- member of the stage because val lands in SL.
  hier-at-code : HierInStage
               → (cp : Code)
               → (o : IsOrd (fst (val cp)))
               → _
  hier-at-code hier cp o = hier (toL (val cp)) o (val cp .snd)

-- completeness-from-hier is NOT defined.  same-at-codes fires SameHyp
-- at the packed codes.  hier-at-code fires HierInStage at the
-- parameter code.  Neither supplies an ambient matrix₃ reading at a
-- stage member, which BoundInStage spends.  See lj-1.700-report.md.
