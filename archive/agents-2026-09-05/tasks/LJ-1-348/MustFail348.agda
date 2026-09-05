{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.348] EXPECTED RED.  DO NOT REPAIR THIS FILE.
--
-- THE CONTROL, after `[LJ-1.341]`'s Control 5 and `[LJ-1.346]`'s
-- Control A.  `[LJ-1.344]` priced `witK`'s cure at 「`[LJ-1.343]`'s
-- repair plus one `carrierK` call」.  `Refute348.Cure` shows the cure
-- IS one call.  This file asks the other half of the question, which
-- decides whether the cure is a repair or only a type: CAN THE CALL
-- SITE PAY THE NEW HYPOTHESIS?
--
-- THE CALL SITE is `WitnessAgree.out`, src/L/Condensation.lagda.md:6717
-- and :6721:
--
--   go (w , (hxw , (hcl , hsh))) = ...
--     wK = witK w (hxw , (hcl , hsh))
--
-- `w` comes out of the UNBOUNDED existential `hasWitnessAt A x`, and
-- the three things bound with it are the formula's three conjuncts.
-- The repaired tie wants a FOURTH thing, `< fst w in fst (lookup A g) >`.
-- Nothing at the site has it.
--
-- WHAT THIS FILE DOES.  It offers the site's own closest candidate,
-- the first conjunct, where the carrier membership is wanted.  Agda
-- must refuse, and the error must NAME the missing fact.  If this file
-- ever goes green, the cure is payable and the refutation is the only
-- finding left standing.
--
-- ONE agda process under GHCRTS="-A64m -I0 -M8g".

open import Base.Prelude
open import Base.Truth

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( var; _∈̇_; _∧̇_ )
open import Cubical.HITs.CumulativeHierarchy.Base using ( _∈_ )

module LJ-1-348.MustFail348 {ℓ : Level} where

open import L.Constructible {ℓ} using ( 𝒮ʟ )

import L.Coding.Model
module GM = L.Coding.Model {ℓ}
open GM using ( closedAt )
open GM.AbsL using ( _^_ ) renaming ( _⊨ᵐ_ to _⊨_ )

open import L.Coding.Shape {ℓ} using ( shapedAt )

open hPropStructure 𝒮ʟ using ( S )

module Attempt {n : ℕ} (A Ki xi : Fin n) (γ : S ^ n)
  (carrierK : (v : S) → ⟨ fst v ∈ fst (lookup A γ) ⟩
            → ⟨ fst v ∈ fst (lookup Ki γ) ⟩) where

  -- The site's data, and only the site's data.
  site : (u : S) → ⟨ (u ∷ γ) ⊨ ((var (suc xi) ∈̇ var zero)
              ∧̇ (closedAt zero ∧̇ shapedAt zero (suc A))) ⟩
       → ⟨ fst u ∈ fst (lookup Ki γ) ⟩
  site u h = carrierK u (h .fst)
