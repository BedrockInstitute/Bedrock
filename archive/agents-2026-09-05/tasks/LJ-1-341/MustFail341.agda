{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.341] THE GATE-LIVE CONTROL.  THIS FILE MUST BE RED.
--
-- C-45: `exit 0` is not a supply.  `ProbeTies341.agda` and
-- `ControlA341.agda` are both green in about two seconds, and a green so
-- cheap must be shown to mean something.  This file attempts the ONE
-- proof a reader would try: discharge `defPairK` WITHOUT bounding `z`,
-- from the two `KFacts` fields that do prove the bounded form.
--
-- It must fail, and the error must name the missing fact, which is
-- `⟨ fst z ∈ fst (lookup Ki γ) ⟩`.  Record the error text in the report.
-- Do NOT repair this file.
--
-- ONE agda process under GHCRTS="-A64m -I0 -M8g".

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

open import FOL.ZFStructure using ( module hPropStructure )
open import Cubical.HITs.CumulativeHierarchy.Base using ( _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  renaming ( module InfinitySet to Inf )
open Inf using ( #_ )

module LJ-1-341.MustFail341 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import V.Coding {ℓ} using ( pr )
open import L.Constructible {ℓ} using ( 𝒮ʟ )
open import L.Axioms.Numerals {ℓ} using ( numeralL; numeralL-fst )

import L.Coding.Model
module GM = L.Coding.Model {ℓ}
open GM using ( tagAtL; tagAtL-adequate; prʟ; prʟ-fst )
open GM.AbsL using ( _^_ ) renaming ( _⊨ᵐ_ to _⊨_ )

open hPropStructure 𝒮ʟ using ( S )

module Attempt {n : ℕ} (Ki : Fin n) (γ : S ^ n)
  (pairK : (a c : S) → ⟨ fst a ∈ fst (lookup Ki γ) ⟩
         → ⟨ fst c ∈ fst (lookup Ki γ) ⟩
         → ⟨ fst (prʟ a c) ∈ fst (lookup Ki γ) ⟩)
  (numK0 : ⟨ fst (numeralL 0) ∈ fst (lookup Ki γ) ⟩) where

  -- THE ATTEMPT.  `pairK` wants `z` inside the bound and the telescope
  -- gives no such hypothesis, so `numK0` is offered in its place and the
  -- checker must refuse.
  defPairK-unbounded : (E z w' : S)
                     → ⟨ (w' ∷ E ∷ z ∷ γ) ⊨ tagAtL zero 0 (suc (suc zero)) ⟩
                     → ⟨ fst w' ∈ fst (lookup Ki γ) ⟩
  defPairK-unbounded E z w' h =
    subst (λ u → ⟨ u ∈ fst (lookup Ki γ) ⟩) (sym eq2)
      (pairK (numeralL 0) z numK0 numK0)
    where
    eq : fst w' ≡ pr (# 0) (fst z)
    eq = subst ⟨_⟩
           (tagAtL-adequate zero 0 (suc (suc zero)) (w' ∷ E ∷ z ∷ γ)) h

    eq2 : fst w' ≡ fst (prʟ (numeralL 0) z)
    eq2 = eq ∙ sym (prʟ-fst (numeralL 0) z
                   ∙ cong (λ u → pr u (fst z)) (numeralL-fst 0))
