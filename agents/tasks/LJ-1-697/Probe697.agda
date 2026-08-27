{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.697] PROBE.  HierInStage at [LJ-1.679]'s frame: an adequate
-- K that is a member of Lset lam and contains the approximation.
-- Lands nothing in src/.
--
--   W3              Lset∈suc, ordinal-in, climb, lset-in-stage.
--                   runs/W3.agda.  Lset δ is a member of the stage.
--                   hierL is not that member.
--   THE OBLIGATION  hier-in-stage.  Not lifted until HierBelow pays
--                   the table's placement.  from-below is the
--                   assembly this frame adds: HierBelow → HierInStage.
--
-- ONE Agda process per run, GHCRTS="-A64m -I0 -M2g", the wide
-- caliber, set on the pane by the program and untouched here.
-- Nothing is postulated.  No hole.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-697.Probe697 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ} using ( 𝒮ʟ; IsOrd; Lset; Lset-mono )
open import L.Hierarchy {ℓ} lem using ( hierL )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ∅; module InfinitySet )
open InfinitySet {ℓ} using ( sucV )
open import LJ-1-652.Probe652 {ℓ} lem as P652
import LJ-1-679.Probe679 {ℓ} lem as P679
import LJ-1-697.runs.W3 {ℓ} lem as W3

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ
module CS = hPropStructure 𝒮ʟ

-- =====================================================================
-- THE PREDECESSOR TYPES, TAKEN NOT REBUILT.  W2.
-- =====================================================================

-- Probe679.agda:84-88.  Named, not inhabited, there.  Taken here.
-- CompletenessFrom (Probe679.agda:94-95) is the consumer.  Not this
-- obligation.

-- W3, GREEN in runs/W3.agda.  Lset δ sits inside the stage.
Lset∈suc = W3.Lset∈suc
step = W3.step

-- =====================================================================
-- HIERINSTAGE AT THE LIMIT FRAME.  The assembly from HierBelow is
-- new.  The closed term is not written: HierBelow is unpaid
-- (Probe536.agda:186-187, review-of-StageHigh.md:23-32).
-- =====================================================================

module At (lam : S) (ordλ : IsOrd lam)
  (succλ : (d : S) → ⟨ d ∈ˢ lam ⟩ → ⟨ sucV d ∈ˢ lam ⟩)
  (X : S) (X⊆Lλ : (z : S) → ⟨ z ∈ˢ X ⟩ → ⟨ z ∈ˢ Lset lam ⟩)
  (∅∈λ : ⟨ ∅ ∈ˢ lam ⟩)
  (elem : P652.Frame652.A.Elementary lam ordλ succλ X X⊆Lλ ∅∈λ) where

  open P679.At lam ordλ succλ X X⊆Lλ ∅∈λ elem public
    using ( HierInStage; CompletenessFrom; Completeness; BoundInStage )
  open W3.At lam ordλ succλ public
    using ( climb; ordinal-in; lset-in-stage )

  -- [LJ-1.536]'s HierBelow at this isL witness, not rebuilt.
  -- The type names a successor presentation.  The obligation type
  -- does not (P-l).  Probe536.agda:186-187 used isL-ord; here the
  -- carrier already carries isL as δ .snd.
  Below : (δ : CS.S) (oδ : IsOrd (fst δ)) → Type (ℓ-suc ℓ)
  Below δ oδ =
    ⟨ fst (hierL (fst δ) (δ .snd) oδ) ∈ˢ Lset (step 3 (fst δ)) ⟩

  -- THE ASSEMBLY THIS FRAME ADDS.  ord∈Lset→∈ puts the ordinal in
  -- lam.  climb 3, by succλ three times, puts δ+3 in lam.
  -- Lset-mono carries the table up.  Lset-out is not used: for an
  -- ordinal, ord∈Lset→∈ is the specialised out-lemma
  -- (src/L/Ordinal/Stages.lagda.md:265-268).
  from-below : ((δ : CS.S) (oδ : IsOrd (fst δ)) → Below δ oδ)
             → HierInStage
  from-below hb δ oδ δ∈Lλ =
    Lset-mono {α = lam} {β = step 3 (fst δ)}
      (climb 3 (fst δ) (ordinal-in (fst δ) oδ δ∈Lλ))
      (hb δ oδ)

  from-below-at : (δ : CS.S) (oδ : IsOrd (fst δ))
                → Below δ oδ
                → ⟨ fst δ ∈ˢ Lset lam ⟩
                → ⟨ fst (hierL (fst δ) (δ .snd) oδ) ∈ˢ Lset lam ⟩
  from-below-at δ oδ hb δ∈Lλ =
    Lset-mono {α = lam} {β = step 3 (fst δ)}
      (climb 3 (fst δ) (ordinal-in (fst δ) oδ δ∈Lλ))
      hb

-- CompletenessFrom is a named consumer, not the obligation.  The
-- obligation name hier-in-stage is NOT defined.  The witness meter
-- must read UNRESOLVED.  See review-of-hier-in-stage.md.
