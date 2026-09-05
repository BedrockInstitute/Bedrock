{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.360] EXPECTED RED.  DO NOT REPAIR THIS FILE.
--
-- THE BACK DIRECTION IS THE PRICE, AND THIS CONTROL MEASURES IT.
--
-- The honest restatement changes `hasWitnessAt` itself, so the chain's
-- `WitnessAgree.back` (`src/L/Condensation.lagda.md:6734-6752`), which
-- produces the unbounded predicate FROM the bounded one, must now also
-- produce the new conjunct: every member of the witness is a key with
-- a numeral arity.
--
-- The bounded form `hasWitnessBS` (`src/L/Condensation.lagda.md:1715`)
-- binds the witness BY THE STAGE and carries `closedBS` and `shapedBS`
-- beside it.  This file offers the site's own shapedness, the closest
-- candidate the bounded form has, where the member arity is wanted.
-- Agda refuses, and the error names the missing fact: a shape, not a
-- numeral arity.
--
-- So the restatement's back leg needs the arity conjunct stated in the
-- bounded form too, or a new tie one level up.  That is the
-- orchestrator's to choose (DD23); this file prices the need.
--
-- ONE agda process under GHCRTS="-A64m -I0 -M8g".

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

open import FOL.ZFStructure using ( module hPropStructure )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  renaming ( module InfinitySet to Inf )
open Inf using ( #_ )
open import Cubical.Data.Nat using ( ℕ )

module LJ-1-360.MustFail360 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ} using ( 𝒮ʟ )

import L.Coding.Model
module GM = L.Coding.Model {ℓ}
open GM.AbsL using ( _^_ ) renaming ( _⊨ᵐ_ to _⊨_ )

open import L.Coding.CodeSet {ℓ} lem using ( arityNumAtL )
open import L.Condensation {ℓ} lem using ( shapedBS )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ using ( S )

-- THE BACK SITE, with exactly the facts the bounded form's
-- destructuring binds at the witness frame.
module Back {n : ℕ} (A K N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 : Fin n)
  (γ : S ^ n) (w : S)
  (hshBS : ⟨ (w ∷ γ) ⊨ shapedBS zero (suc A) (suc K)
                     (suc N0) (suc N1) (suc N2) (suc N3) (suc N4)
                     (suc N5) (suc N6) (suc N7) (suc N8) (suc N9)
                     (suc N10) (suc N11) ⟩) where

  -- EXPECTED RED.  `hshBS` is the closest candidate the bounded form
  -- has: the per-member shapedness at the witness.
  no-back : (c : S) → ⟨ fst c ∈ fst w ⟩
          → ⟨ (c ∷ w ∷ γ) ⊨ arityNumAtL zero ⟩
  no-back c hc = hshBS c hc
