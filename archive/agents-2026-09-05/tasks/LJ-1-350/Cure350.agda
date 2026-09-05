{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.350] THE REAL BOUND, AND THE TREE ALREADY HAS IT.
--
-- `Refute350.agda` measures that SHAPEDNESS does not save the third
-- shape tie.  This file measures what does.
--
-- THE BOUND IS `arityNumAtL`, src/L/Coding/CodeSet.lagda.md:185-188,
-- delivered, with both adequacy directions delivered beside it
-- (`arityNumAtL-out` :189-197, `arityNumAtL-in` :201-207).  It says
-- exactly「the code is a pair whose first component is in omega」, which
-- is the tie's last conjunct as a FORMULA.
--
-- THE TREE ALREADY SAYS SO, IN ENGLISH.
-- src/L/Condensation/TwelveAgree.lagda.md:302-305:
--
--   The restriction costs the consumers nothing, because the arity at
--   every consuming site IS a numeral: `codesK` gives the code's shape,
--   `arityNumAtL` (L.Coding.CodeSet) says its arity component is a
--   numeral, and `pr-inj` closes both into `fst ar = # n`.
--
-- THIS FILE MEASURES THREE THINGS.
--
--   1. THE CURE.  `arity-cure` derives the tie's last conjunct from
--      `arityNumAtL` and the tie's own equation.  FIVE LINES.
--   2. NON-VACUITY.  The cure runs at a real code with a numeral arity
--      and produces the conjunct.  So it is not vacuous.
--   3. DISCRIMINATION.  `arityNumAtL` REFUTES the countermodel that
--      shapedness admits.  Same code, same file, two bounds.
--
-- ONE agda process under GHCRTS="-A64m -I0 -M8g".

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

open import FOL.ZFStructure using ( module hPropStructure )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ⁅_,_⁆; ∅ ) renaming ( module InfinitySet to Inf )
open Inf using ( #_; sucV )
open import Cubical.Data.Nat using ( ℕ )
open import Cubical.Data.Sigma using ( _×_ )
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁; ∣_∣₁ )

module LJ-1-350.Cure350 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Coding {ℓ} using ( pr; pr-inj )
open import L.Constructible {ℓ} using ( 𝒮ʟ; IsOrd; Lset )
open import L.Axioms.Numerals {ℓ} using ( numeralL; numeralL-fst )

import L.Coding.Model
module GM = L.Coding.Model {ℓ}
open GM using ( prʟ; prʟ-fst )
open GM.AbsL using ( _^_ ) renaming ( _⊨ᵐ_ to _⊨_ )

open import L.Coding.CodeSet {ℓ} lem
  using ( arityNumAtL; arityNumAtL-out; arityNumAtL-in )

open import L.Condensation {ℓ} lem using ( module KFactsNS )
open KFactsNS

open import LJ-1-347.Elim347 {ℓ} using ( sgl1-not-numeral )
open import LJ-1-350.Refute350 {ℓ} lem using ( module Refute )

open hPropStructure 𝒮ʟ using ( S )

-- =====================================================================
-- PART 1.  THE CURE.  FIVE LINES, AND NOTHING ELSE IS NEEDED.
--
-- This is the whole repair of the tie's last conjunct at ONE site.  It
-- is generic in `n` and in the environment, so ONE copy serves every
-- site of the family.
-- =====================================================================

module Cure {n : ℕ} (γ : S ^ n) where

  arity-cure : (k : ℕ) (c N a b : S)
             → ⟨ (c ∷ γ) ⊨ arityNumAtL zero ⟩
             → fst c ≡ pr (fst N) (pr (# k) (pr (fst a) (fst b)))
             → ∥ Σ[ m ∈ ℕ ] (fst N ≡ # m) ∥₁
  arity-cure k c N a b h e = PT.map
    (λ { (m , (z , q)) → m , pr-inj (sym e ∙ q) .fst })
    (arityNumAtL-out zero (c ∷ γ) h)

  -- THE UNARY HALF, for `unCodesK` and `unCompK`.  The same five lines
  -- at one component fewer.
  arity-cure-un : (k : ℕ) (c N a : S)
                → ⟨ (c ∷ γ) ⊨ arityNumAtL zero ⟩
                → fst c ≡ pr (fst N) (pr (# k) (fst a))
                → ∥ Σ[ m ∈ ℕ ] (fst N ≡ # m) ∥₁
  arity-cure-un k c N a h e = PT.map
    (λ { (m , (z , q)) → m , pr-inj (sym e ∙ q) .fst })
    (arityNumAtL-out zero (c ∷ γ) h)

-- =====================================================================
-- PART 2.  NON-VACUITY AND DISCRIMINATION.
--
-- The same countermodel `Refute350.agda` builds, against the other
-- bound.  Shapedness ADMITS it, MEASURED there.  `arityNumAtL` REFUTES
-- it, MEASURED here.  That is the whole finding, in one pair of files.
-- =====================================================================

module Test {n : ℕ} (A K : Fin n) (γ : S ^ n)
  (numK0 : ⟨ fst (numeralL 0) ∈ fst (lookup K γ) ⟩)
  (numK1 : ⟨ fst (numeralL 1) ∈ fst (lookup K γ) ⟩)
  (numK2 : ⟨ fst (numeralL 2) ∈ fst (lookup K γ) ⟩)
  (pairK : (a b : S) → ⟨ fst a ∈ fst (lookup K γ) ⟩
         → ⟨ fst b ∈ fst (lookup K γ) ⟩
         → ⟨ fst (prʟ a b) ∈ fst (lookup K γ) ⟩)
  (carrierK : (v : S) → ⟨ fst v ∈ fst (lookup A γ) ⟩
            → ⟨ fst v ∈ fst (lookup K γ) ⟩)
  (arityK : (N v : S) → ⟨ fst v ∈ fst N ⟩ → ⟨ fst N ∈ fst (lookup K γ) ⟩
          → ⟨ fst v ∈ fst (lookup K γ) ⟩)
  (u : S) (hu : ⟨ fst u ∈ fst (lookup A γ) ⟩) where

  module RF = Refute A K γ numK0 numK1 numK2 pairK carrierK arityK
  module RP = RF.Point u hu
  module C = Cure γ

  -- DISCRIMINATION.  The countermodel shapedness admits is REFUTED by
  -- `arityNumAtL`, at the very same code.
  arityNum-refutes-countermodel
    : ⟨ (RP.cS ∷ γ) ⊨ arityNumAtL zero ⟩ → Empty.⊥
  arityNum-refutes-countermodel h = PT.rec Empty.isProp⊥
    (λ { (m , q) → sgl1-not-numeral m (sym RP.ar-fst ∙ q) })
    (C.arity-cure 2 RP.cS RP.arS u u h RP.codeEq)

  -- NON-VACUITY.  A GOOD code, whose arity IS the numeral one.  It is
  -- ONE ARGUMENT away from the countermodel: `numeralL 1` where the
  -- countermodel writes `sglS (numeralL 1)`.
  gS : S
  gS = prʟ (numeralL 1) (prʟ (numeralL 2) (prʟ u u))

  goodEq : fst gS ≡ pr (fst (numeralL 1)) (pr (# 2) (pr (fst u) (fst u)))
  goodEq = prʟ-fst (numeralL 1) (prʟ (numeralL 2) (prʟ u u))
    ∙ cong (pr (fst (numeralL 1)))
        (prʟ-fst (numeralL 2) (prʟ u u)
          ∙ cong₂ pr (numeralL-fst 2) (prʟ-fst u u))

  -- The cure's hypothesis is INHABITED at the good code, and it is
  -- built and not assumed.
  good-arityNum : ⟨ (gS ∷ γ) ⊨ arityNumAtL zero ⟩
  good-arityNum = arityNumAtL-in zero (gS ∷ γ) 1
    (prʟ (numeralL 2) (prʟ u u))
    (prʟ-fst (numeralL 1) (prʟ (numeralL 2) (prʟ u u))
      ∙ cong (λ w → pr w (fst (prʟ (numeralL 2) (prʟ u u))))
          (numeralL-fst 1))

  -- THE CURE PRODUCES THE TIE'S LAST CONJUNCT AT THE GOOD CODE.
  cured-conjunct : ∥ Σ[ m ∈ ℕ ] (fst (numeralL 1) ≡ # m) ∥₁
  cured-conjunct = C.arity-cure 2 gS (numeralL 1) u u good-arityNum goodEq

  -- CONTROL, THE OTHER HALF.  The conjunct FAILS at the countermodel's
  -- arity, ONE ARGUMENT APART from `cured-conjunct` above.
  countermodel-conjunct-fails
    : ∥ Σ[ m ∈ ℕ ] (fst RP.arS ≡ # m) ∥₁ → Empty.⊥
  countermodel-conjunct-fails = RP.arity-fails
