{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.530] CONTROL.  The import list of Probe530.agda and NO term.
-- It measures the chapter load, so the obligation can be priced by
-- subtraction.  Original header follows.
--
-- [LJ-1.530] PROBE.  `dK`: the definable powerset of a recorded value
-- is a member of `K`.  It runs in agents/tasks/LJ-1-530/ and lands
-- nothing in src/.
--
--   W3, FIRST      runs/W3.agda, typechecked before this file existed.
--                  The brief's form is written there as a TYPE and is
--                  NOT inhabited; the corrected form, the same statement
--                  with the member a STAGE, IS inhabited and is what the
--                  obligation consumes.
--   DELIVERED      dK, the briefed obligation, at the frame the site
--                  supplies: K a limit level, and the value table
--                  correct below its own bound.
--   ALSO           zK, four lines on top of dK, because [LJ-1.527]
--                  reported that reduction without measuring it
--                  (agents/tasks/LJ-1-527/lj-1.527-report.md:196-198).
--
-- WHY THE FRAME IS NOT THE BRIEF'S.  The brief's frame gives `w` as an
-- arbitrary member of `K`.  Nothing in the tree puts the definable
-- powerset of an arbitrary member of a level back in that level; the
-- ONLY statement src/ makes about a level and a definable powerset is
-- `Lset-suc` (src/L/Axioms/Basic.lagda.md:196), which is about a STAGE.
-- The site supplies exactly that missing word: `Values`
-- (src/L/Hierarchy.lagda.md:117-119) says a value recorded at an
-- argument below the bound IS the tower there.  This is not a
-- weakening of the obligation: the conclusion is the briefed one, and
-- `Values` is the same hypothesis src/ already spends to discharge
-- `dK`'s `isL` sibling `PowOK` (src/L/Hierarchy.lagda.md:167-170).
--
-- ONE Agda process per run, GHCRTS="-A64m -I0 -M8g", the wide caliber,
-- set on the pane by the program and untouched here.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-530.runs.Control530 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.Syntax using ( ⊤̇ )
open import FOL.ZFStructure using ( module hPropStructure )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Coding {ℓ} using ( pr )
open import L.Definability {ℓ} using ( module DefOf )
open import L.Constructible {ℓ}
  using ( 𝒮ʟ; isL; isL-trans; IsOrd; Lset; 𝒟ₒ; 𝒟ₒ-intro; Lset-in
        ; Lset-layer; layer-trans )
open import L.Axioms.Basic {ℓ} using ( Lset-suc )
open import L.Ordinal {ℓ} using ( ω-ord )
open import L.Ordinal.Stages {ℓ} lem using ( ord∈Lset→∈ )
open import L.Hierarchy {ℓ} lem using ( Values; Domain )

open import Cubical.Data.FinData using ( Fin )
open import Cubical.Data.Vec using ( lookup )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ∅; module InfinitySet )
open InfinitySet using ( sucV; ω; ω-empty; ω-next )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ∈∈ₛ )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL using ( _^_ )

