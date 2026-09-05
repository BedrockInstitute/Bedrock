{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.154] Probe B.  THE IMPORT BASELINE for Probe A.
--
-- [LJ-1.152] measured that the import block alone costs about 1.18 s
-- (agents/tasks/LJ-1-152/lj-1.152-report.md:133).  Probe A's import
-- block is not that one: it adds `L.Ordinal`, `L.Stage`,
-- `L.Axioms.Basic`, `L.Axioms.Numerals`, `V.Presentation` and the
-- presentation types.  So the baseline is re-measured here rather than
-- carried over.  P-l.
--
-- This file carries Probe A's import block EXACTLY and no body.  The
-- difference prices the carve.
--
-- ABORT CRITERION: none.  This is a control, not a decision.
--
-- Tracked probe; ONE agda process under GHCRTS="-A64m -I0 -M8g";
-- never committed to src/.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-154.ProbeLJ1154B {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula; con; ∃̇∈ )
import FOL.Absoluteness
import FOL.ZFModel
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Coding {ℓ} using ( pr; pr-inj )
open import V.Presentation {ℓ} using ( member; fiber; ↪-inj )
open import L.Constructible {ℓ}
  using ( 𝒮ʟ; isL; isL-trans; IsOrd; Lset; Lset-mono )
open import L.Ordinal {ℓ} using ( boundingOrd )
open import L.Stage {ℓ} lem using ( stage; stage-ord; stage-mem )
open import L.Axioms.Basic {ℓ} using ( LsetS )
open import L.Axioms.Full {ℓ} lem using ( hasSeparationL )
open import L.Axioms.Numerals {ℓ} using ( numeralL )
open import L.Coding.Model {ℓ}
  using ( prAtL; prAtL-adequate; prʟ; prʟ-fst
        ; svAt; svAt-in; domAt; domAt-intro )

open import ProbeLJ1134A {ℓ} lem
  using ( injAt; injAt-in; module Small; module Concrete )

open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_; setIsSet )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫; ⟪_⟫↪ )
open import Cubical.Data.Sigma using ( _×_ )
open import Cubical.Functions.Logic using ( ∃[∶]-syntax )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ

module ModelL = FOL.ZFModel 𝒮ʟ
open ModelL using ( SetOf )

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL using ( _^_ ) renaming ( _⊨ᵐ_ to _⊨_ )

-- ---------------------------------------------------------------------
-- NO BODY.  One name, so the module is not empty and every import above
-- is still resolved and loaded.
-- ---------------------------------------------------------------------

baseline : S → S
baseline x = x
