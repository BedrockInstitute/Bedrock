{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.704] PROBE.  The carved table versus the L-tower hierarchy.
-- Lands nothing in src/.
--
--   OBLIGATION  carved-is-hier.  NOT INHABITED in-tree.  TRUE in the
--                   model:  at the frame's earliest stage σ = γ + 1 the
--                   A-bounded reading sees no junk, and carved is the
--                   table itself.  review-of-carved-is-hier.md states
--                   the NO-GO (in-tree) with the missing fact.
--   DELIVERED     gamma-below-sigma:  the stage bound of the recording
--                   is a stage fact of the real ordinal.
--                   ord-in-Lset:  a member of an ordinal lies in the
--                   stage of the ordinal (one line on Lset-cumul).
--   ABSENT        carved-is-hier:  its in-tree half, the recording
--                   satisfaction lemma (the 693/698/536 chain), is
--                   written out in section 3.
--
-- ONE Agda process per run, GHCRTS wide caliber, set on the pane by
-- the program and untouched here.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-704.Probe704 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; IsOrd; Lset )
open import L.Ordinal {ℓ} using ( mem-ord )
open import L.Ordinal.Stages {ℓ} lem using ( ord∈Lset-suc; Lset-cumul )
open import Cubical.HITs.CumulativeHierarchy.Constructions using ( module InfinitySet )
open InfinitySet using ( sucV )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V )
open import LJ-1-698.Probe698 {ℓ} lem using ( module Carved )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ

------------------------------------------------------------------------------
-- Section 1.  The frame and its in-tree stage facts.
--
-- The Carved frame of [LJ-1.698] supplies σ, the stage bound of the
-- recording, and carved, the A-bounded reading of the recording at σ.

module Carved704 (γ : V ℓ) (oγ : IsOrd γ) (hγ : ⟨ isL γ ⟩) where

  open Carved γ oγ hγ using ( σ; oσ; φᵣ; hφ; carved )

  -- The bound proved by the 698 frame, as a stage fact of the ordinal:
  -- the ordinal lies in the stage its recording was taken at.
  gamma-below-sigma : ⟨ γ ∈ˢ Lset σ ⟩
  gamma-below-sigma = hφ .fst

  -- A member of the ordinal lies in the stage of the ordinal itself:
  -- the tree's one-line Lset-cumul on the ordinal ladder.
  ord-in-Lset : (c : V ℓ) → ⟨ c ∈ˢ γ ⟩ → ⟨ c ∈ˢ Lset γ ⟩
  ord-in-Lset c c∈γ = Lset-cumul c γ
    (mem-ord {γ} oγ c c∈γ) oγ c∈γ
    (ord∈Lset-suc c (mem-ord {γ} oγ c c∈γ))

------------------------------------------------------------------------------
-- Section 2.  What carved is, stated (the exact shadow).
--
-- The 698 frame picks σ as the EARLIEST stage that bounds the
-- recording:  the constants of φᵣ are con γ and con (Lset γ), and both
-- first appear at stage γ + 1  (Lset-suc, ord∈Lset-suc),  so σ = γ + 1
-- and  Lset σ = 𝒟ₒ (Lset γ).
--
-- Every element of Lset (γ + 1) is a definable SUBSET of Lset γ
-- (defSet⊤≡A;  Def A is all of A plus its subsets).  So every
-- w ∈ Lset σ  satisfies  w ⊆ Lset γ = A:  the A-bounded reading sees
-- the full content of w.  There is no junk in the gap, and the reading
-- of ⟨x, w⟩ is the full reading:  "w is the table below x",  which
-- forces  w ≡ Lset x  and  x ∈ γ  (the stage holds exactly the
-- ordinals below it).
--
-- carved is the table itself,  in the model.  Had the frame taken a
-- HIGHER σ,  junk would enter the gap:  for x ∈ γ the set
-- w' = Lset x ∪ { Lset γ }  sits in Lset (γ + 3),  w' ∩ Lset γ = Lset x,
-- and the A-bounded content of ⟨x, Lset x⟩ holds identically of
-- ⟨x, w'⟩,  inflating the reading above the table.  The equality is a
-- property of the earliest stage,  and the frame sits on it.

------------------------------------------------------------------------------
-- Section 3.  The obligation, absent on purpose.
--
--   carved-is-hier : carved ≡ fst (hierL γ hγ oγ)
--
-- TRUE in the model (section 2),  NOT CONSTRUCTIBLE in-tree.  The
-- A-bounded content of a table entry ⟨x, Lset x⟩ is established only
-- through the tables ⟨u, Lset u⟩ below x,  and that satisfaction chain
-- is the unlanded 693 HierInK (gated by the 698 ThroughDoor / 532
-- FALSE stop) and 536 HierBelow.  Stated,  the missing fact is
--
--   table-sat : (x : V ℓ) → ⟨ x ∈ˢ γ ⟩
--               →  (the A-bounded reading of φᵣ at ⟨ x , Lset x ⟩
--                   holds in the stage model)
--
-- by induction on the ordinal,  with the induction step consuming the
-- table entries below x.  Neither half is landed.  Both inclusions of
-- the obligation wait on it:  hierL ⊆ carved needs it directly,  and
-- the reverse inclusion needs the model-exactness of section 2 as a
-- tree-internal content lemma.  review-of-carved-is-hier.md names it
-- and states the NO-GO.
