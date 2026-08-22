{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.529]  W3 WITHOUT THE THREE TYPE ASCRIPTIONS.  This variant exists to
-- make ONE claim of the report checkable: the re-basing is [LJ-1.490]'s
-- `Bound` line for line, and the three extra lines in Probe529.agda are
-- signatures [LJ-1.490] left to inference, not new content.
--
-- The brief names it: THE RE-BASING.
--
--   -- Bound, C and bnd, with swo-rank′ in place of swo-rank
--
-- [LJ-1.521] measured [LJ-1.490]'s `Bound`, `C` and `bnd`
-- (agents/tasks/LJ-1-490/Probe490.agda:211-232) as built on `swo-rank`,
-- the rank [LJ-1.497] refuted, and priced the re-basing at "a re-spelling
-- of eleven lines and not a new proof"
-- (agents/tasks/LJ-1-521/lj-1.521-report.md:305-308).  THREE of the four
-- `InjCode` conjuncts are priced against that figure, so it is written
-- here first, ALONE, with the obligation and the carve omitted.
--
-- If the substitution does not go through, the range clause is not the
-- cheapest of the three and [LJ-1.524]'s triage must be re-read.
--
-- ONE IMPORT OF A PREDECESSOR PROBE, as [LJ-1.524] declared and used
-- (agents/tasks/LJ-1-524/Probe524.agda:70, and its report's section "ONE
-- DEPARTURE FROM THE PREDECESSORS' PRACTICE, DECLARED").
-- `bedrock.agda-lib:2` lists `agents/tasks` as an include root.  The
-- re-basing must be stated at the SAME rank the consumers use, and the
-- consumer is `P521.rank-at′` (agents/tasks/LJ-1-521/Probe521.agda:428),
-- so a rebuilt copy would not be the same term.
--
-- Nothing lands in src/.  Does not postulate.  `swo-rank` does NOT appear.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-529.runs.W3-noasc {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Coding {ℓ} using ( pr )
open import V.Presentation {ℓ} using ( fiber )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans; IsOrd )
open import L.Ordinal {ℓ} using ( boundingOrd )
open import L.InjChain {ℓ} lem using ( module PairBound )
open import L.WellOrder.Base {ℓ} using ( SWO )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫ )

import LJ-1-521.Probe521 {ℓ} lem as P521

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ using ( S )

-- =====================================================================
-- THE RE-BASING.  [LJ-1.490]'s `Bound` (Probe490.agda:211-230) with
-- `P521.swo-rank′` where it has `swo-rank`, and `P521.OrdSWO∈ₛ.w` where
-- it has its own `OrdSWO.w`.
--
-- THE ORDER CHANGES TOO, and that is forced rather than chosen.
-- [LJ-1.490] imports `L.WellOrder.Base {ℓ-suc ℓ}` (Probe490.agda:34) and
-- builds its `SWO` on `_∈ᵗ_`; [LJ-1.521] imports it at `{ℓ}`
-- (Probe521.agda:53) and builds `OrdSWO∈ₛ` on `_∈ₛ_` (Probe521.agda:174-216).
-- `P521.swo-rank′` only accepts the second, and `P521.rank-at′`
-- (Probe521.agda:428-436) runs on `P521.OrdSWO∈ₛ.w (fst a) oa` and no
-- other record, so the pack must be formed at that same `w` or the range
-- clause has no path from the rank to the bounding ordinal.
-- =====================================================================

module Bound′ (a : S) (oa : IsOrd (fst a)) where

  w = P521.OrdSWO∈ₛ.w (fst a) oa

  pack = boundingOrd ⟪ fst a ⟫ (P521.swo-rank′ w) (P521.swo-rank′-ord w)

  β = pack .fst

  oβ = pack .snd .fst

  C : S
  C = β , P521.isL-ord β oβ

  module PB = PairBound a C

  bnd : S
  bnd = PB.bnd

  below : (m : S) (mx : ⟨ fst m ∈ fst a ⟩)
        → ⟨ pr (fst m) (P521.swo-rank′ w (fiber (fst a) mx .fst)) ∈ fst bnd ⟩
  below m mx = PB.below m z mx r∈β
    where
    k = fiber (fst a) mx .fst
    r = P521.swo-rank′ w k
    r∈β : ⟨ r ∈ β ⟩
    r∈β = pack .snd .snd k
    z : S
    z = r , isL-trans {x = β} {y = r} r∈β (snd C)

-- The delivered bound, at [LJ-1.486]'s type (Probe490.agda:233-242) with
-- the refuted rank replaced.  `bnd` is `fst` of this Sigma.
rank-bound′ :
    (a : S) (oa : IsOrd (fst a))
  → Σ[ bnd ∈ S ]
      ((m : S) (mx : ⟨ fst m ∈ fst a ⟩)
        → ⟨ pr (fst m) (P521.swo-rank′ (P521.OrdSWO∈ₛ.w (fst a) oa)
                                       (fiber (fst a) mx .fst))
            ∈ fst bnd ⟩)
rank-bound′ a oa = Rb.bnd , Rb.below
  where
  module Rb = Bound′ a oa
