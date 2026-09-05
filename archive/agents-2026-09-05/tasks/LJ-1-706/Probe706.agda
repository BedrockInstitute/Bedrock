{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.706] PROBE.  Below, from the identification, as a hypothesis.
-- Lands nothing in src/.
--
--   THE OBLIGATION  below-from-carved.  NOT INHABITED.
--                   review-of-below-from-carved.md states the stop.
--   DELIVERED       Below: [LJ-1.697]'s type at [LJ-1.697]'s carrier
--                   (Probe697.agda:72-74), restated from src/ names.
--                   Identified: [LJ-1.704]'s obligation type, verbatim
--                   at [LJ-1.698]'s frame, taken as a hypothesis here.
--                   Bound-in-tower: the placement row, the one row
--                   between the door and Below.
--                   below-from-place: placement + identification -> Below.
--                   door-lands: where [LJ-1.698]'s door puts the carved
--                   set, one successor above the bounding stage.
--
-- ONE Agda process per run, GHCRTS wide caliber, set on the pane by
-- the program and untouched here.  Nothing is postulated.  No hole.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-706.Probe706 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; IsOrd; Lset; Lset-in )
open import L.Hierarchy {ℓ} lem using ( hierL )
open import LJ-1-693.Probe693 {ℓ} lem using ( step; door-next )
import LJ-1-698.Probe698 {ℓ} lem as P698
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet )
open InfinitySet {ℓ} using ( sucV )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ
module CS = hPropStructure 𝒮ʟ

-- =====================================================================
-- SECTION 1.  THE TYPES.  The codomain is [LJ-1.697]'s Below at
-- [LJ-1.697]'s carrier, restated from src/ names.  It does not depend
-- on [LJ-1.697]'s At parameters, so it is restated at top level rather
-- than importing the Probe652/Probe679 chain that frames them (the
-- floor of that frame is 144.56 s, lj-1.697-report.md:126).  The
-- hypothesis is [LJ-1.704]'s obligation, verbatim at [LJ-1.698]'s
-- frame: the carved set is the table's first projection.
-- =====================================================================

-- [LJ-1.697]'s type (Probe697.agda:72-74).  step is [LJ-1.693]'s
-- (Probe693.agda:82-84), the same iterator [LJ-1.697]'s W3 opens.
Below : (δ : CS.S) (oδ : IsOrd (fst δ)) → Type (ℓ-suc ℓ)
Below δ oδ =
  ⟨ fst (hierL (fst δ) (δ .snd) oδ) ∈ˢ Lset (step 3 (fst δ)) ⟩

-- [LJ-1.704]'s obligation type, verbatim at [LJ-1.698]'s frame
-- (LJ-1.704.md, THE OBLIGATION).  A HYPOTHESIS here.
Identified : (δ : CS.S) (oδ : IsOrd (fst δ)) → Type (ℓ-suc ℓ)
Identified δ oδ =
  P698.Carved.carved (fst δ) oδ (δ .snd) ≡ fst (hierL (fst δ) (δ .snd) oδ)

-- The placement row: mkBoundedFo's bounding stage, a member of the
-- tower over δ.  This is the row the tree does not have.
Bound-in-tower : (δ : CS.S) (oδ : IsOrd (fst δ)) → Type (ℓ-suc ℓ)
Bound-in-tower δ oδ =
  ⟨ fst (P698.bound-of (fst δ) oδ (δ .snd)) ∈ˢ step 3 (fst δ) ⟩

-- =====================================================================
-- SECTION 2.  THE REDUCTION.  Placement and identification jointly
-- pay Below.  Lset-in reads the carved set's 𝒟ₒ-membership at the
-- tower's stage (src/L/Constructible.lagda.md:329-330); subst moves
-- it to the table along the identification.  This is the distance
-- from [LJ-1.704]'s identification to [LJ-1.697]'s Below, measured:
-- exactly the placement row.
-- =====================================================================

below-from-place : (δ : CS.S) (oδ : IsOrd (fst δ))
                 → Bound-in-tower δ oδ → Identified δ oδ → Below δ oδ
below-from-place δ oδ bδ idδ =
  subst (λ w → ⟨ w ∈ˢ Lset (step 3 (fst δ)) ⟩) idδ
    (Lset-in (step 3 (fst δ)) (fst (P698.bound-of (fst δ) oδ (δ .snd)))
       (P698.Carved.carved (fst δ) oδ (δ .snd)) bδ
       (P698.Carved.carved∈𝒟ₒ (fst δ) oδ (δ .snd)))

-- =====================================================================
-- SECTION 3.  WHERE THE DOOR LANDS.  [LJ-1.693]'s door-next
-- (Probe693.agda:109-111), applied to [LJ-1.698]'s delivered door
-- (Probe698.agda:128-129).  Not rebuilt (W2).  The carved set lands
-- one successor above the bounding stage, and that stage is
-- mkBoundedFo's, untracked by the tower.  See the review.
-- =====================================================================

door-lands : (δ : CS.S) (oδ : IsOrd (fst δ))
           → ⟨ P698.Carved.carved (fst δ) oδ (δ .snd)
                ∈ˢ Lset (sucV (fst (P698.bound-of (fst δ) oδ (δ .snd)))) ⟩
door-lands δ oδ =
  door-next (fst (P698.bound-of (fst δ) oδ (δ .snd)))
    (P698.Carved.carved (fst δ) oδ (δ .snd))
    (P698.Carved.carved-door (fst δ) oδ (δ .snd))

-- =====================================================================
-- SECTION 4.  THE OBLIGATION NAME IS ABSENT ON PURPOSE.  No postulate
-- stands in for it.  below-from-carved would be the section 2 type
-- without the placement row, and that row is not in the tree: it is
-- what review-of-below-from-carved.md measures and states.
-- =====================================================================
