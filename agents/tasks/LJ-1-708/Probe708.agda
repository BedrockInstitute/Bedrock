{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.708] PROBE.  below-direct: [LJ-1.697]'s Below WITHOUT the
-- door.  Lands nothing in src/.
--
--   THE OBLIGATION  below-direct.  Named here, NOT inhabited.  The
--                   stated NO-GO is review-of-below-direct.md.
--   THE QUESTION    whether ord∈Lset→∈ closes the gap [LJ-1.679]'s
--                   critic measured, or whether the gap sits in
--                   succλ instead (LJ-1.708.md, W3).
--   MEASURED        after its only producer fires, the attempt
--                   leaves three unsolved metas: Lset-mono's index
--                   slot beta, its index-membership premise and its
--                   base premise (runs/cand-2.out:6-8,
--                   runs/cand-1.agda.txt:69-71).
--
-- ONE Agda process per run, GHCRTS="-A64m -I0 -M2g", the wide
-- caliber, set on the pane by the program and untouched here.
-- Nothing is postulated.  No hole.  The door-built rows of W3
-- (`Lset∈suc`, `lset-in-stage`, both fire 𝒟ₒ-intro,
-- agents/tasks/LJ-1-697/runs/W3.agda:42-44) are deliberately NOT
-- opened here: the using-list below names only the door-free rows.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-708.Probe708 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ} using ( 𝒮ʟ; IsOrd; Lset; Lset-mono )
open import L.Ordinal.Stages {ℓ} lem using ( ord∈Lset→∈ )
open import L.Hierarchy {ℓ} lem using ( hierL )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ∅; module InfinitySet )
open InfinitySet {ℓ} using ( sucV )
import LJ-1-652.Probe652 {ℓ} lem as P652
import LJ-1-697.runs.W3 {ℓ} lem as W3

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ
module CS = hPropStructure 𝒮ʟ

-- =====================================================================
-- THE FRAME OF [LJ-1.697], UNCHANGED.  The target Below lives there,
-- and premise 5 fixes climb and ordinal-in as known good AT this
-- frame.  The module hypotheses, taken not rebuilt (W2):
--   lam    the limit index            (Probe679.agda:63)
--   succλ  closure under sucV         (Probe679.agda:64)
--   X/X⊆Lλ/∅∈λ/elem  carried inert    (Probe679.agda:65-67); they
--          speak about lam and X, never about step 3 δ, and no row
--          of this file spends them.
-- =====================================================================

module At (lam : S) (ordλ : IsOrd lam)
  (succλ : (d : S) → ⟨ d ∈ˢ lam ⟩ → ⟨ sucV d ∈ˢ lam ⟩)
  (X : S) (X⊆Lλ : (z : S) → ⟨ z ∈ˢ X ⟩ → ⟨ z ∈ˢ Lset lam ⟩)
  (∅∈λ : ⟨ ∅ ∈ˢ lam ⟩)
  (elem : P652.Frame652.A.Elementary lam ordλ succλ X X⊆Lλ ∅∈λ) where

  -- Door-free rows only.  ordinal-in IS ord∈Lset→∈ at this frame;
  -- climb IS succλ iterated (agents/tasks/LJ-1-697/runs/W3.agda:
  -- 55-62).
  open W3.At lam ordλ succλ public
    using ( climb; ordinal-in )

  -- THE TARGET.  Verbatim agents/tasks/LJ-1-697/Probe697.agda:72-74.
  Below : (δ : CS.S) (oδ : IsOrd (fst δ)) → Type (ℓ-suc ℓ)
  Below δ oδ =
    ⟨ fst (hierL (fst δ) (δ .snd) oδ) ∈ˢ Lset (W3.step 3 (fst δ)) ⟩

  -- THE OBLIGATION below-direct.  DELIBERATELY ABSENT FROM THIS
  -- FILE, as at Probe679.agda:97-99 and Probe697.agda (the obligation
  -- name is NOT defined; the witness meter must read UNRESOLVED).
  -- Agda carries no debt form, so the named NO-GO is stated in
  -- review-of-below-direct.md and the measured residual is
  -- runs/cand-2.out.  Its type, for the record:
  --
  --   below-direct : (δ : CS.S) (oδ : IsOrd (fst δ)) → Below δ oδ
  --
  -- Any candidate term must bottom out in a judgment
  -- ⟨ t ∈ˢ Lset w ⟩ whose PRODUCER the licensed triple does not
  -- contain; see review-of-below-direct.md for the boundary rows.
