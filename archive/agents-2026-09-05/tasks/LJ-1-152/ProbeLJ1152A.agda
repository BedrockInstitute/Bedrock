{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.152] Probe A.  THE IMPORT BASELINE, and it is not decoration.
--
-- [LJ-1.136] bisected its 254.22 s run as "graph construction 250.71 s,
-- four conjuncts 3.51 s" (agents/tasks/LJ-1-136/lj-1.136-report.md:1063-1069).
-- That bisection never subtracted the cost of LOADING the imports, so
-- 250.71 is an upper bound on `hasReplacementL` and nothing more.
--
-- This file carries ProbeLJ1136A's import block EXACTLY and no body.
-- Its seconds are the load, so the difference prices the replacement.
--
-- ABORT CRITERION: none.  This is a control, not a decision.
--
-- Tracked probe; ONE agda process under GHCRTS="-A64m -I0 -M8g";
-- never committed to src/.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-152.ProbeLJ1152A {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula )
import FOL.Absoluteness
import FOL.ZFModel
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Coding {ℓ} using ( pr; pr-inj )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans )
open import L.Axioms.Full {ℓ} lem using ( hasReplacementL; hasSeparationL )
open import L.Coding.Model {ℓ}
  using ( prAtL; prAtL-adequate; prʟ; prʟ-fst
        ; svAt; svAt-in; domAt; domAt-intro )

open import ProbeLJ1134A {ℓ} lem using ( injAt; injAt-in )

open import Cubical.HITs.CumulativeHierarchy.Base using ( _∈_; setIsSet )
open import Cubical.Data.Sigma using ( Σ≡Prop; _×_ )
open import Cubical.Functions.Logic using ( ∃[∶]-syntax )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ

module ModelL = FOL.ZFModel 𝒮ʟ
open ModelL using ( SetOf; ℩ )

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL using ( _^_ ) renaming ( _⊨ᵐ_ to _⊨_ )

-- ---------------------------------------------------------------------
-- NO BODY.  One name, so the module is not empty and every import above
-- is still resolved and loaded.
-- ---------------------------------------------------------------------

baseline : S → S
baseline x = x
