{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.348] THE SECOND TIE.  DOES `graphWitK`'s MISSING FIELD EXIST
-- AT ANOTHER SORT?
--
-- `[LJ-1.344]` reported: 「its third conclusion, `fst f in K`, is not a
-- `carrierK` call: it needs the carrier as a MEMBER of the bound, and
-- `KFacts` has no such field ... INFERRED that one field and one
-- supplier line close it. I did not build either」.
--
-- THE FIRST HALF IS TRUE.  `KFacts`
-- (src/L/Condensation.lagda.md:6079-6115) has 29 fields and none of
-- them gives `fst (lookup A g) in fst (lookup K g)`.  MEASURED, by
-- reading all 29.
--
-- THE SECOND HALF IS THE QUESTION THIS FILE ANSWERS.  The brief warns
-- that `[LJ-1.344]` predicted a two-line closure that was really eight
-- lines stated a SORT up, and that the same move may apply here.  IT
-- DOES.  The fact is not new mathematics and it is not a new chapter:
-- `src/L/Axioms/Basic.lagda.md:156-158` already writes the hard half
-- inline, and `Lset-in` (src/L/Constructible.lagda.md:319) carries it
-- to the bound.
--
-- ONE agda process under GHCRTS="-A64m -I0 -M8g".

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( ⊤̇ )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ∅ ) renaming ( module InfinitySet to Inf )
open Inf using ( sucV )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁ )

module LJ-1-348.Field348 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Definability {ℓ} using ( module DefOf )
open import L.Constructible {ℓ}
  using ( 𝒮ʟ; IsOrd; Lset; Lset-in; 𝒟ₒ; 𝒟ₒ-intro )

-- =====================================================================
-- PART 1.  THE FIELD, AT THE SORT THE TREE ALREADY STATES IT.
--
-- `isL-Lset` (src/L/Axioms/Basic.lagda.md:156-158) needs exactly
-- 「the stage is a definable subset of itself」and writes it INLINE,
-- with the formula `T`.  It then throws the membership away and keeps
-- only `isL`.  Named, it is the supplier.
-- =====================================================================

Lset∈𝒟ₒ : (β : V ℓ) → ⟨ Lset β ∈ 𝒟ₒ (Lset β) ⟩
Lset∈𝒟ₒ β = 𝒟ₒ-intro (Lset β) (Lset β)
  ∣ ⊤̇ , DefOf.defSet⊤≡A (Lset β) ∣₁

-- THE FIELD.  One line from `Lset-in`, and its ONLY hypothesis is the
-- ordinal membership `KValue` already assumes as `γ∈λ`.  No `IsOrd`, no
-- successor, no limit.
bound-mem : (lam gam : V ℓ) → ⟨ gam ∈ lam ⟩ → ⟨ Lset gam ∈ Lset lam ⟩
bound-mem lam gam h = Lset-in lam gam (Lset gam) h (Lset∈𝒟ₒ gam)

-- =====================================================================
-- PART 2.  THE SAME THING AT `KValue`'s OWN FRAME AND OWN INDICES.
--
-- This is the test `[LJ-1.344]` set for a supply: not a type at the
-- right shape, but the value the chapter's own producer would write.
-- =====================================================================

open import L.Condensation {ℓ} lem using ( module KValue )
open hPropStructure 𝒮ʟ using ( S )

import L.Coding.Model
module GM = L.Coding.Model {ℓ}
open GM.AbsL using ( _^_ )

module AtKValue (lam : V ℓ) (ordλ : IsOrd lam)
                (succλ : (d : V ℓ) → ⟨ d ∈ lam ⟩ → ⟨ sucV d ∈ lam ⟩)
                (∅∈λ : ⟨ ∅ ∈ lam ⟩)
                (gam : V ℓ) (ordγ : IsOrd gam) (γ∈λ : ⟨ gam ∈ lam ⟩) where

  module KV = KValue lam ordλ succλ ∅∈λ gam ordγ γ∈λ

  -- THE PROPOSED FIELD, at the shape a `KFacts` field would carry.
  boundK : ⟨ fst (lookup KV.iA KV.Kenv) ∈ fst (lookup KV.iK KV.Kenv) ⟩
  boundK = bound-mem lam gam γ∈λ

-- =====================================================================
-- PART 3.  WHAT THE FIELD ACTUALLY CLOSES, AND WHAT IT DOES NOT.
--
-- `graphWitK` (src/L/Condensation.lagda.md:7288-7297) has THREE
-- conclusions, not one:
--   < fst d in K >  x  < fst e in K >  x  < fst f in K >.
-- The first conjunct of its premise pins `f` to the CARRIER, so the
-- THIRD conclusion is the field and one `subst`.  The first two are
-- about `d` and `e`, which the premise bounds by `closedAt`, `domAt`,
-- `appAt` and `twelveAt` and by NOTHING above.  That is `witK`'s own
-- defect, and PART 1 of `Refute348.agda` refutes that shape.
-- =====================================================================

open import FOL.Syntax using ( var; _≐_ )
open GM.AbsL renaming ( _⊨ᵐ_ to _⊨_ )

module GraphThird {n : ℕ} (A K : Fin n) (γ : S ^ n)
  (boundK : ⟨ fst (lookup A γ) ∈ fst (lookup K γ) ⟩) where

  -- The index form is `LeafAgree`'s: with `A := suc (suc (suc w))` the
  -- formula below is `var zero ≐ var (suc^6 w)`, verbatim from :7289.
  third : (d e f : S)
        → ⟨ (f ∷ e ∷ d ∷ γ) ⊨ (var zero ≐ var (suc (suc (suc A)))) ⟩
        → ⟨ fst f ∈ fst (lookup K γ) ⟩
  third d e f q = subst (λ u → ⟨ u ∈ fst (lookup K γ) ⟩) (sym q) boundK
