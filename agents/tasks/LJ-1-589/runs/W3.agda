{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.589] W3.  THE TROPHY'S OMEGA-EXCLUSION, PROPAGATED TO THE SITE
-- ROW 5 SPENDS AT.  TYPE ONLY.
--
-- WRITTEN FIRST AND TYPECHECKED ALONE, before any other Agda of this
-- task, exactly as the brief orders.  No hole, no postulate.
--
-- The brief names the widest unmeasured term:
--
--     -- GCHStatement's fourth hypothesis, propagated to row 5's spend
--     -- site, TYPE ONLY
--
-- Row 5 is `SuccIntoPower` (agents/tasks/LJ-1-558/Probe558.agda:99-102).
-- Its spend site is `gch-route-without-stage`
-- (agents/tasks/LJ-1-558/Probe558.agda:118-128): the `b10 κ δ sc` of
-- line 128.  `GCHStatement`'s fourth hypothesis is
-- `(⟨ fst κ ∈ˢ ω ⟩ → Empty.⊥)` (src/L/GCH.lagda.md:64), and at that
-- spend site it is bound as `κ∉ω` (Probe558.agda:122).
--
-- SO THE QUESTION W3 ASKS IS A TYPE QUESTION AND NOTHING ELSE: can row
-- 5's type carry that clause?  This slice writes the row with the
-- clause in it and nothing else.  It builds no term and it inhabits
-- nothing.  Whether the narrowed row still pays the trophy is the
-- OBLIGATION, and it is not asked here.
--
-- NOTHING IS IMPORTED FROM A PREDECESSOR PROBE.  Row 5's type is
-- rewritten from `src/L/GCH.lagda.md` alone, so this slice measures
-- the clause and not [LJ-1.558]'s import cost.
--
-- CALIBER.  The program set GHCRTS on this pane.  I did not set it.
-- One Agda process at a time.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-589.runs.W3 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ} using ( 𝒮ʟ )
open import L.GCH {ℓ} lem using ( SuccCardL; InjL )
import FOL.ZFModel
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet )
open InfinitySet {ℓ} using ( ω )
import Cubical.Data.Empty as Empty

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ using ( _∈ˢ_ )

module SL = hPropStructure 𝒮ʟ
module ModelL = FOL.ZFModel 𝒮ʟ

-- ROW 5, RESTATED WITH THE TROPHY'S FOURTH HYPOTHESIS.  Only one line
-- differs from `SuccIntoPower` (Probe558.agda:99-102): the third, which
-- is `src/L/GCH.lagda.md:64` copied letter for letter.
SuccIntoPowerInf : ModelL.isZFModel → Type (ℓ-suc ℓ)
SuccIntoPowerInf zf =
    (κ δ : SL.S) → (⟨ fst κ ∈ˢ ω ⟩ → Empty.⊥)
  → SuccCardL δ κ → InjL δ (𝒫 κ)
  where open ModelL.isZFModel zf using ( 𝒫 )
