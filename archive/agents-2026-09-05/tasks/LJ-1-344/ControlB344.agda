{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.344] CONTROL B.  EXPECTED RED.  NON-VACUITY.
--
-- `Supply344.agda` exhibits a REAL inhabitant of the `envK` premise, at
-- the one-entry environment over the tag NUMERAL ZERO.  If any
-- environment satisfied the premise, the tie would be about nothing and
-- the supply would be decoration.
--
-- This file changes the tag from 0 to 1 and changes NOTHING else.  The
-- tie is unchanged and still true; only the WITNESS dies.  Agda must
-- refuse at the equation that feeds the tie.  The shape is
-- `[LJ-1.338]`'s Control C, at agents/tasks/LJ-1-338/ControlC338.agda.
--
-- ONE agda process under GHCRTS="-A64m -I0 -M8g".

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

open import FOL.ZFStructure using ( module hPropStructure )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ⁅_,_⁆ ) renaming ( module InfinitySet to Inf )
open Inf using ( #_ )

module LJ-1-344.ControlB344 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Coding {ℓ} using ( pr )
open import L.Constructible {ℓ} using ( 𝒮ʟ )
open import L.Axioms.Numerals {ℓ} using ( numeralL )

import L.Coding.Model
module GM = L.Coding.Model {ℓ}
open GM using ( prʟ )
open GM.AbsL using ( _^_ )

open import LJ-1-344.Supply344 {ℓ} lem using ( module TieSupply; envOne-pair )

open hPropStructure 𝒮ʟ using ( S )

module Bad {n : ℕ} (A K : Fin n) (γ : S ^ n)
  (numK0 : ⟨ fst (numeralL 0) ∈ fst (lookup K γ) ⟩)
  (pairK : (a b : S) → ⟨ fst a ∈ fst (lookup K γ) ⟩
         → ⟨ fst b ∈ fst (lookup K γ) ⟩
         → ⟨ fst (prʟ a b) ∈ fst (lookup K γ) ⟩)
  (carrierK : (v : S) → ⟨ fst v ∈ fst (lookup A γ) ⟩
            → ⟨ fst v ∈ fst (lookup K γ) ⟩)
  (arityK : (N v : S) → ⟨ fst v ∈ fst N ⟩ → ⟨ fst N ∈ fst (lookup K γ) ⟩
          → ⟨ fst v ∈ fst (lookup K γ) ⟩) where

  open TieSupply A K γ numK0 pairK carrierK arityK

  -- THE ONE CHANGED CHARACTER: `# 1` where `Supply344.agda` writes `# 0`.
  bad-fires : (E z : S) → ⟨ fst z ∈ fst (lookup A γ) ⟩
            → fst E ≡ ⁅ pr (# 1) (fst z) , pr (# 1) (fst z) ⁆
            → ⟨ fst E ∈ fst (lookup K γ) ⟩
  bad-fires E z hz q = envK-live E z hz (q ∙ sym (envOne-pair (fst z)))
