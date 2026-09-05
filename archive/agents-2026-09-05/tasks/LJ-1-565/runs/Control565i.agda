{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.565] PROBE.  StageHigh again, and the door was not what blocked it.
-- It runs in agents/tasks/LJ-1-565/ and lands nothing in src/.
--
--   D-10, FIRST    what step [LJ-1.536] could not take, now that
--                  [LJ-1.562] has paid the door.  The answer is in
--                  that task's OWN stop and it is not the door:
--                  agents/tasks/LJ-1-536/review-of-StageHigh.md:88-91,
--                  "THE LIMIT DID NOT LEAVE", and its report's THE WALL.
--                  Section 0 below states it as a term where it can be.
--   W3, SECOND     runs/W3.agda, typechecked ALONE before this file
--                  existed: `AtStage` at [LJ-1.536]'s formula with BOTH
--                  hypotheses fed.  Exit 0, runs/w3-0.out, 2.07 s.
--   OBLIGATION     stage-high : StageHigh.  Section 5 states it.
--
-- ONE Agda process per run, GHCRTS="-A64m -I0 -M8g", the wide caliber,
-- set on the pane by the program and untouched here.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-565.runs.Control565i {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ; regularityV )
open import L.Constructible {ℓ}
  using ( 𝒮ʟ; isL; IsOrd; isPropIsOrd; Lset )
open import L.Ordinal {ℓ} using ( suc-ord; mem-ord )
open import L.Ordinal.Stages {ℓ} lem using ( suc∈or≡ )
open import L.Hierarchy {ℓ} lem using ( hierL )
open import LJ-1-536.Probe536 {ℓ} lem
  using ( step; isL-ord; seq; HierBelow; module Adjoin
        ; StageHigh; HierBelowAll; reduction; reduction-at
        ; IsLimit; HierBelowLimit )

open import Cubical.Data.Sum using ( _⊎_; inl; inr )
import Cubical.Data.Sum as Sum
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁; ∣_∣₁ )
import Cubical.Induction.WellFounded as WF
open import Cubical.Foundations.Prelude using ( PathP; isProp→PathP )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet )
open InfinitySet {ℓ} using ( sucV )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ



-- [LJ-1.565] CONTROL i.  ONE DELTA STEP ON `HierBelow`, AT A VARIABLE.

unfold-var : (γ : V ℓ) (oγ : IsOrd γ)
           → HierBelow γ oγ
           → ⟨ fst (hierL γ (isL-ord γ oγ) oγ) ∈ Lset (step 3 γ) ⟩
unfold-var γ oγ p = p
