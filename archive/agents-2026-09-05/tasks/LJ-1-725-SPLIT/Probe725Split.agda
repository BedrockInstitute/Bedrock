{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.725-SPLIT] PROBE.  stage-read, the reverse inclusion's missing
--                     input, split off [LJ-1.725].  Lands nothing in
--                     src/.
--
--   OBLIGATION  stage-read (the type below, transcribed verbatim from
--               agents/tasks/LJ-1-725/Probe725.agda:251-258).  STATED,
--               NOT INHABITED.  review-of-stage-read.md states the
--               stop with the failing site: the backward half of the
--               set equation must FEED the relativized StepAt's
--               second extAt conjunct at a member of Lset (fst u),
--               and its DefAt payload then demands formula codes and
--               satisfaction-recursion values INSIDE the bound
--               Lset gamma.  No landed lemma bounds keyS, Sat or the
--               environment sets by the carrier's own stage; CodeSet's
--               smallAny returns an unspecified stage.  [LJ-1.724]
--               measured this membrane class failing outright below a
--               fixed finite stage.
--   DELIVERED   Lset-trans-set:  members of members of Lset gamma lie
--                 in Lset gamma (review-of-carved-is-hier.md's
--                 corrected target, half 1).  REAL, one PT.rec over
--                 Lset-out, closed by the landed D-o-membership
--                 refinement and Lset-mono.
--               ord-in-Lset:  a member of an ordinal lies in the
--                 ordinal's own stage.  [LJ-1.724]'s cure
--                 (Probe724.agda:67-71), re-measured at this site
--                 from the landed L.Ordinal.Stages.  REAL.
--   ABSENT      the INHABITANT of stage-read.  No postulate stands in
--               for it and no weaker form is inhabited under its
--               name.  See the review for the corrected target.
--
-- ONE Agda process per run, GHCRTS wide caliber, set on the pane by
-- the program and untouched here.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-725-SPLIT.Probe725Split {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula )
open import FOL.Manipulation.Relativize using ( relativize )
open import Cubical.Data.FinData using ( zero; suc )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁; squash₁ )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ}
  using ( 𝒮ʟ; isL; IsOrd; Lset; isL-trans; Lset-mono; Lset-out; 𝒟ₒ; 𝒟ₒ∋⊆ )
import FOL.Absoluteness
module AbsL725 = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL725 using ( _^_ ) renaming ( _⊨ᵐ_ to _⊨_ )
open import L.Ordinal {ℓ} using ( mem-ord )
open import L.Ordinal.Stages {ℓ} lem using ( ord∈Lset-suc; Lset-cumul )
open import L.Axioms.Basic {ℓ} using ( LsetS )
open import L.Coding.Sequence {ℓ} lem using ( LsetGraphAt )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ
open hPropStructure 𝒮ᵥ using () renaming ( _∈ˢ_ to _∈ˢᵥ_ )

-- =====================================================================
-- SECTION 1.  Lset-trans-set.  Members of members of Lset γ lie in
-- Lset γ.  review-of-carved-is-hier.md's corrected target, half 1.
-- The content is the landed refinement of the operator
-- (a member of D-o A never has a member outside A) plus monotonicity.
-- =====================================================================

Lset-trans-set : (γ a x : V ℓ)
               → ⟨ a ∈ˢᵥ x ⟩ → ⟨ x ∈ˢᵥ Lset γ ⟩ → ⟨ a ∈ˢᵥ Lset γ ⟩
Lset-trans-set γ a x a∈ x∈ = PT.rec (snd (a ∈ˢᵥ Lset γ)) step (Lset-out γ x x∈)
  where
  step : Σ[ δ ∈ V ℓ ] (⟨ δ ∈ˢᵥ γ ⟩ × ⟨ x ∈ˢᵥ 𝒟ₒ (Lset δ) ⟩)
       → ⟨ a ∈ˢᵥ Lset γ ⟩
  step (δ , (δ∈γ , x∈𝒟)) =
    Lset-mono {α = γ} {β = δ} δ∈γ {x = a}
      (𝒟ₒ∋⊆ (Lset δ) x x∈𝒟 a a∈)

-- Two iterates, because a recorded pair's components sit two
-- membership steps below a member of the bound:  c ∈ pr c z and
-- pr c z ∈ fst f₀ put c in Lset γ by Lset-trans-set applied twice.
Lset-trans-set² : (γ a x y : V ℓ)
                → ⟨ a ∈ˢᵥ x ⟩ → ⟨ x ∈ˢᵥ y ⟩ → ⟨ y ∈ˢᵥ Lset γ ⟩
                → ⟨ a ∈ˢᵥ Lset γ ⟩
Lset-trans-set² γ a x y a∈ x∈ y∈ =
  Lset-trans-set γ a x a∈ (Lset-trans-set γ x y x∈ y∈)

-- =====================================================================
-- SECTION 2.  ord-in-Lset.  A member of an ordinal lies in the
-- ordinal's own stage.  [LJ-1.724]'s cure, re-measured here from the
-- landed L.Ordinal.Stages (nothing is imported from that probe).
-- This is what puts every member of fst u inside the relativization's
-- bound, which is the one stage fact the un-guarding spine consumes.
-- =====================================================================

ord-in-Lset : (γ : V ℓ) (oγ : IsOrd γ) (c : V ℓ)
            → ⟨ c ∈ˢᵥ γ ⟩ → ⟨ c ∈ˢᵥ Lset γ ⟩
ord-in-Lset γ oγ c c∈γ =
  Lset-cumul c γ (mem-ord {A = γ} oγ c c∈γ) oγ c∈γ
    (ord∈Lset-suc c (mem-ord {A = γ} oγ c c∈γ))

-- =====================================================================
-- SECTION 3.  THE OBLIGATION'S TYPE.  STATED, NOT INHABITED.
--
-- Transcribed verbatim from Probe725.agda:251-258.  The name is
-- exported at the file's top level as a TYPE;  no inhabitant stands
-- under it, no postulate supports it, and the file carries --safe.
-- review-of-stage-read.md states the stop and the corrected target.
-- =====================================================================

stage-read : Type (ℓ-suc ℓ)
stage-read =
    (γ : V ℓ) (oγ : IsOrd γ) (hγ : ⟨ isL γ ⟩)
    (u z W : S) → ⟨ fst u ∈ γ ⟩ → ⟨ fst z ∈ Lset γ ⟩
  → ⟨ (z ∷ u ∷ W ∷ []) ⊨ relativize (LsetS γ oγ)
                        (LsetGraphAt zero (suc zero)) ⟩
  → fst z ≡ Lset (fst u)

-- The equation splits extensionally into the two inclusions, and the
-- record of this dispatch is which half costs what.  The forward
-- half's extraction sites all discharge by Lset-trans-set (iterated)
-- and ord-in-Lset;  the backward half's fill dies at the DefAt
-- membrane under the bound.  Neither half is inhabited here;  the
-- review carries the site, the price and the corrected target.
