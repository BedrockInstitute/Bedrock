{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.350] EXPECTED RED.  DO NOT REPAIR THIS FILE.
--
-- THE LOAD-BEARING CHECK, the one `[LJ-1.341]` set and `[LJ-1.348]`
-- re-ran: a cure that adds a hypothesis is only cheap if the CALL SITE
-- already holds it.
--
-- THE SITE is `WitnessAgree.out.go`, src/L/Condensation.lagda.md:6716
-- to :6732.  It reads
--
--   go (w , (hxw , (hcl , hsh))) = ...
--   module SA = ShapedAgree ... (w :: g) ... (codesK w wK) (unCodesK w wK)
--
-- so the three things bound beside `w` are the read membership, the
-- CLOSEDNESS of `w` and the SHAPEDNESS of `w`.  Nothing else.
--
-- `Cure350.agda` measures that the missing bound is `arityNumAtL` at
-- each member of `w`.  This file offers the site's own shapedness where
-- that is wanted.  Agda refuses, and the error names the missing fact.
--
-- SO THE CURE IS NOT PAYABLE AT THE SITE, and the 24 sites are not a
-- threading job.  Section 5 of the report prices what they are instead.
--
-- ONE agda process under GHCRTS="-A64m -I0 -M8g".

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

open import FOL.ZFStructure using ( module hPropStructure )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet )
open InfinitySet using ( #_ )

module LJ-1-350.MustFail350 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ} using ( 𝒮ʟ )

import L.Coding.Model
module GM = L.Coding.Model {ℓ}
open GM using ( closedAt )
open GM.AbsL using ( _^_ ) renaming ( _⊨ᵐ_ to _⊨_ )

open import L.Coding.Shape {ℓ} using ( shapedAt )
open import L.Coding.CodeSet {ℓ} lem using ( arityNumAtL )

open hPropStructure 𝒮ʟ using ( S )

-- THE SITE, with exactly the data `WitnessAgree.out.go` binds.
module Site {n : ℕ} (A : Fin n) (γ : S ^ n) (w : S)
  (hcl : ⟨ (w ∷ γ) ⊨ closedAt zero ⟩)
  (hsh : ⟨ (w ∷ γ) ⊨ shapedAt zero (suc A) ⟩) where

  -- EXPECTED RED.  `hsh` is the closest candidate the site has.
  no-supplier : (c : S) → ⟨ fst c ∈ fst w ⟩
              → ⟨ (c ∷ w ∷ γ) ⊨ arityNumAtL zero ⟩
  no-supplier c hc = hsh
