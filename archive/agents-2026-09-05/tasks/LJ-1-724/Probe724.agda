{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.724] PROBE.  The recording-satisfaction target `table-sat`,
-- the missing fact named by [LJ-1.704]'s review.  Lands nothing in
-- src/.
--
--   OBLIGATION  table-sat.  NOT INHABITED, AND NOT INHABITABLE AS
--               STATED:  the target is FALSE at the top entry of a
--               successor ordinal.  The frame relativizes the
--               recording at A = Lset gamma, and relativization binds
--               every raw existential at con A
--               (FOL/Manipulation/Relativize.lagda.md:57);  the
--               GraphAt conjunct of the recording
--               (L/Coding/Sequence.lagda.md:291,328-329) therefore
--               demands its approximation INSIDE Lset gamma.  At a
--               successor gamma and x = its predecessor, the Step
--               conjunct forces a pair of rank >= x + 2 into that
--               approximation, which Lset gamma cannot hold.
--               review-of-table-sat.md states the NO-GO with the
--               minimal counterexample (gamma = 2, x = 1), the rank
--               argument, and the corrected scope.
--   DELIVERED   frame-wiring:  the Carved frame of [LJ-1.698] plus the
--               Delta-0 certificate its door consumes.
--               ord-in-Lset:  704's stage fact, re-measured at this
--               site;  it is what puts the counterexample's witnesses
--               inside the A-bound.
--   ABSENT      table-sat:  false as stated;  see the review.
--
-- ONE Agda process per run, GHCRTS wide caliber, set on the pane by
-- the program and untouched here.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-724.Probe724 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.LevyHierarchy using ( Δ₀ )
open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ} using ( isL; IsOrd; Lset )
open import L.Ordinal {ℓ} using ( mem-ord )
open import L.Ordinal.Stages {ℓ} lem using ( ord∈Lset-suc; Lset-cumul )
open import LJ-1-698.Probe698 {ℓ} lem using ( recorded-at; module Carved )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ

------------------------------------------------------------------------------
-- Section 1.  The frame and its in-tree stage facts.

module Frame (γ : V ℓ) (oγ : IsOrd γ) (hγ : ⟨ isL γ ⟩) where

  open Carved γ oγ hγ using ( σ; oσ; φᵣ; hφ; carved )

  -- The Delta-0 certificate the door consumes.  698 stated it as
  -- recorded-at (Probe698.agda:87-89);  at the frame's own formula it
  -- is that very term, by definition of φᵣ.
  dφ : Δ₀ φᵣ
  dφ = recorded-at γ oγ hγ

  -- 704's stage fact, re-measured at this site:  a member of the
  -- ordinal lies in the ordinal's own stage.  The counterexample
  -- consumes it to place its witnesses inside the A-bound (the report,
  -- section 2).
  ord-in-Lset : (c : V ℓ) → ⟨ c ∈ˢ γ ⟩ → ⟨ c ∈ˢ Lset γ ⟩
  ord-in-Lset c c∈γ = Lset-cumul c γ
    (mem-ord {γ} oγ c c∈γ) oγ c∈γ
    (ord∈Lset-suc c (mem-ord {γ} oγ c c∈γ))

------------------------------------------------------------------------------
-- Section 2.  The obligation, absent on purpose.
--
--   table-sat : (γ : V ℓ) (oγ : IsOrd γ) (hγ : ⟨ isL γ ⟩)
--                 (x : V ℓ) → ⟨ x ∈ˢ γ ⟩
--               → ⟨ pr x (Lset x) ∈ˢ carved ⟩
--
-- FALSE as stated;  no postulate stands in for it and no weaker form
-- is inhabited under its name.  The counterexample is γ = 2, x = 1:
-- carveSat (L/Axioms/Separation.lagda.md:163-168) reduces the goal to
-- the A-bounded reading of the recording at the pair, and that
-- reading's GraphAt conjunct asks for an approximation f ∈ˢ Lset γ
-- whose Step conjunct covers z' = ∅ ∈ Lset 1 with c = 0, some w',
-- d ≡ 𝒟ₒ w' ∋ ∅ and ⟨ 0 , w' ⟩ ∈ f.  Every member of Lset 2 has rank
-- < 2, while ⟨ 0 , w' ⟩ has rank >= 2, so no such f lies in the bound.
-- The corrected scopes are in review-of-table-sat.md.
--
-- What the next brief keeps from this site:  the reduction above is
-- the door (carveSat plus AtStage's imageIn/imageOut);  the frame's
-- dφ here is its Delta-0 leg;  and Basic.lagda.md:592-599 already
-- carries sgl∈Lset-suc / pr∈Lset-suc, the pairing-in-stage facts the
-- corrected target's fiber work needs.
