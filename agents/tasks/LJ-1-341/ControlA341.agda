{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.341] THE CONTROLS.
--
-- CONTROL A.  THE ABSTRACTION IS NOT A DIFFERENT STATEMENT.  `Probe341`
-- quantifies over the slot index `Ki`.  The chapter writes
-- `lookup (suc (suc (suc K))) γ` at src/L/Condensation.lagda.md:7184 and
-- :7186.  This file states the chapter's two hypotheses at the chapter's
-- own index form and DISCHARGES them into the empty type through the
-- probe.  If the abstraction had shifted the statement, this file would
-- not typecheck.
--
-- CONTROL B.  `DefinesAgree`'s own two parameters
-- (src/L/Condensation.lagda.md:6781-6785) carry the plain index `K`, not
-- `suc (suc (suc K))`.  Stated and refuted separately, because
-- `LeafAgree` is the only consumer of `DefinesAgree` in `src/` and a
-- reader must see that BOTH sites fall.
--
-- ONE agda process under GHCRTS="-A64m -I0 -M8g".

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

open import FOL.ZFStructure using ( module hPropStructure )
open import Cubical.HITs.CumulativeHierarchy.Base using ( _∈_ )
import Cubical.Data.Empty as Empty

module LJ-1-341.ControlA341 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import L.Constructible {ℓ} using ( 𝒮ʟ )

import L.Coding.Model
module GM = L.Coding.Model {ℓ}
open GM using ( tagAtL )
open GM.AbsL using ( _^_ ) renaming ( _⊨ᵐ_ to _⊨_ )

open import L.Coding.Powerset {ℓ} lem using ( envOneAt )

open hPropStructure 𝒮ʟ using ( S )

import LJ-1-341.ProbeTies341
module P = LJ-1-341.ProbeTies341 {ℓ} lem

-- =====================================================================
-- CONTROL A.  `LeafAgree`'s site, src/L/Condensation.lagda.md:7183-7186.
-- =====================================================================

module AtLeaf {n : ℕ} (K : Fin n) (γ : S ^ suc (suc (suc n))) where

  module R = P.Refute (suc (suc (suc K))) γ

  -- Type VERBATIM from :7185-7186.
  leaf-defPairK-false :
      ((E z w' : S)
        → ⟨ (w' ∷ E ∷ z ∷ γ) ⊨ tagAtL zero 0 (suc (suc zero)) ⟩
        → ⟨ fst w' ∈ fst (lookup (suc (suc (suc K))) γ) ⟩)
    → Empty.⊥
  leaf-defPairK-false = R.defPairK-false

  -- Type VERBATIM from :7183-7184.
  leaf-envK-false :
      ((E z : S)
        → ⟨ (E ∷ z ∷ γ) ⊨ envOneAt zero (suc zero) ⟩
        → ⟨ fst E ∈ fst (lookup (suc (suc (suc K))) γ) ⟩)
    → Empty.⊥
  leaf-envK-false = R.envK-false

-- =====================================================================
-- CONTROL B.  `DefinesAgree`'s site, src/L/Condensation.lagda.md:6779-6785.
-- =====================================================================

module AtDefines {m : ℕ} (K : Fin m) (γ : S ^ m) where

  module R = P.Refute K γ

  -- Type VERBATIM from :6783-6785, where the parameter is named `pairK`.
  defines-pairK-false :
      ((E z w' : S)
        → ⟨ (w' ∷ E ∷ z ∷ γ) ⊨ tagAtL zero 0 (suc (suc zero)) ⟩
        → ⟨ fst w' ∈ fst (lookup K γ) ⟩)
    → Empty.⊥
  defines-pairK-false = R.defPairK-false

  -- Type VERBATIM from :6781-6782.
  defines-envK-false :
      ((E z : S)
        → ⟨ (E ∷ z ∷ γ) ⊨ envOneAt zero (suc zero) ⟩
        → ⟨ fst E ∈ fst (lookup K γ) ⟩)
    → Empty.⊥
  defines-envK-false = R.envK-false
