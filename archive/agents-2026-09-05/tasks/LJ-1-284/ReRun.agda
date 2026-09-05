{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.284] the landing proof (C-45).  Exit 0 of a master is not a
-- supply.  This file IMPORTS both masters and uses what they export.
--
-- PART 1  A6.  `L.Absorption` at the concrete ordinal ω: the graph holds
--         a real pair, it runs as an honest injection, and the value is
--         the shift's value.  That is the C-38 guard at this site.
-- PART 2  THE A7 QUESTION, ANSWERED BY THE TYPECHECKER.  A7's `absorbs`
--         hypothesis is `AbsorbsShape` (src/L/GCH.lagda.md:49-53), an
--         unsupplied Pi-parameter at src/L/GCH.lagda.md:69.  Here the
--         delivered `L.Absorption.absorbs` is given THAT type, with no
--         adapter.  Neither master is edited.
-- PART 3  A5 row 3.  `L.InjChain.OrdIncl` at two real ordinals of L, the
--         numerals 1 and 2.
--
-- Tracked; ONE agda process under GHCRTS="-A64m -I0 -M8g".

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-284.ReRun {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ; ∈-irrefl )
open import V.Coding {ℓ} using ( pr )
open import V.Model {ℓ} using ( ∈sucV-inl )
open import V.Presentation {ℓ} using ( fiber )
open import L.Constructible {ℓ} using ( 𝒮ʟ; IsOrd )
open import L.Ordinal {ℓ} using ( ω-ord; #∈ω; numeral-ord )
open import L.Axioms.Infinity {ℓ} lem using ( ωʟ )
open import L.Axioms.Numerals {ℓ}
  using ( numeralL; numeralL-fst; numeralL-suc )
open import L.Absorption {ℓ} lem
  using ( val; absorbs; module ShiftGraph )
open import L.InjChain {ℓ} lem
  using ( module OrdIncl; pairω; pairω-inj; squareω )
open import L.GCH {ℓ} lem using ( AbsorbsShape )
open import L.Ordinal.SquareLaw {ℓ} lem using ( sq )

open import Cubical.HITs.CumulativeHierarchy.Base using ( _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫; ⟪_⟫↪ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet )
open InfinitySet {ℓ} using ( ω; sucV; #_ )
open import Cubical.Data.Sum using ( inr )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ using ( S )

-- ---------------------------------------------------------------------
-- PART 1.  A6 AT ω.  The C-38 guard: not vacuous, and it is the shift.
-- ---------------------------------------------------------------------

module A6Witness where

  module SG = ShiftGraph ωʟ ω-ord (∈-irrefl ω) (λ k → #∈ω k)

  -- The domain is sucV ω, which is inhabited: 0 is a member.
  zero∈D : ⟨ fst (numeralL 0) ∈ fst SG.D ⟩
  zero∈D = ∈sucV-inl {A = ω} {x = fst (numeralL 0)}
    (subst (λ w → ⟨ w ∈ ω ⟩) (sym (numeralL-fst 0)) (#∈ω 0))

  -- The graph HOLDS the pair <0, shift 0>.  Not vacuous.
  inG : ⟨ pr (fst (numeralL 0)) (val SG.D SG.C SG.sh (numeralL 0) zero∈D)
        ∈ fst SG.G ⟩
  inG = SG.pair-in (numeralL 0) zero∈D

  -- The graph RUNS: an honest injection from ⟪sucV ω⟫ into ⟪ω⟫.
  theShift : ⟪ fst SG.D ⟫ → ⟪ fst SG.C ⟫
  theShift = SG.shiftFun

  theShift-inj : (m n : ⟪ fst SG.D ⟫) → theShift m ≡ theShift n → m ≡ n
  theShift-inj = SG.shiftFun-inj

  -- AND IT IS THE SHIFT.
  theShift-val0 : theShift (fiber (fst SG.D) zero∈D .fst)
                ≡ SG.sh (fiber (fst SG.D) zero∈D .fst)
  theShift-val0 = SG.shiftFun-val (fiber (fst SG.D) zero∈D .fst)

-- ---------------------------------------------------------------------
-- PART 2.  A6 DISCHARGES A7's SECOND HYPOTHESIS, ON THE NOSE.
--
-- `AbsorbsShape` is A7's own type, imported from the delivered
-- `src/L/GCH.lagda.md`.  The right-hand side is the delivered
-- `L.Absorption.absorbs`.  No adapter, no eta-expansion, no `subst`.
-- ---------------------------------------------------------------------

absorbsShape : AbsorbsShape
absorbsShape = absorbs

-- ---------------------------------------------------------------------
-- PART 3.  A5 ROW 3 AT TWO REAL ORDINALS OF L, and the two rows that
-- were already delivered, re-asserted through the edited master.
-- ---------------------------------------------------------------------

module Row3Witness where

  one : S
  one = numeralL 1

  two : S
  two = numeralL 2

  oTwo : IsOrd (fst two)
  oTwo = subst IsOrd (sym (numeralL-fst 2)) (numeral-ord 2)

  -- 1 is a member of 2, which is the ordinal fact the module consumes.
  one∈two : ⟨ fst one ∈ fst two ⟩
  one∈two = numeralL-suc 1 one .snd ∣ inr refl ∣₁

  module J = OrdIncl two oTwo one one∈two

  -- 0 is a member of 1, so the domain is NOT empty.
  zero∈one : ⟨ fst (numeralL 0) ∈ fst one ⟩
  zero∈one = numeralL-suc 0 (numeralL 0) .snd ∣ inr refl ∣₁

  -- The graph HOLDS the pair <0,0>.  Not vacuous.
  inG : ⟨ pr (fst (numeralL 0)) (fst (numeralL 0)) ∈ fst J.G ⟩
  inG = J.pair-in (numeralL 0) zero∈one

  -- The graph RUNS, and it is the inclusion.
  theIncl : ⟪ fst one ⟫ → ⟪ fst two ⟫
  theIncl = J.incl

  theIncl-inj : (m n : ⟪ fst one ⟫) → theIncl m ≡ theIncl n → m ≡ n
  theIncl-inj = J.incl-inj

  theIncl-val : (m : ⟪ fst one ⟫) → ⟪ fst two ⟫↪ (theIncl m) ≡ ⟪ fst one ⟫↪ m
  theIncl-val = J.incl-val

-- Row 5 still exports what it exported before the edit.  Row 1's `Comp`
-- is the consumer of the rewritten `PairBound`, and its own re-run is
-- agents/tasks/LJ-1-279/ReRun.agda, which builds a concrete composite.
squareω-again : sq ω
squareω-again = squareω

pairω-runs : ⟪ ω ⟫ × ⟪ ω ⟫ → ⟪ ω ⟫
pairω-runs = pairω

pairω-inj-again : (p q : ⟪ ω ⟫ × ⟪ ω ⟫) → pairω p ≡ pairω q → p ≡ q
pairω-inj-again = pairω-inj
