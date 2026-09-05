{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.344] CONTROL A.  EXPECTED RED.
--
-- THE GATE IS LIVE.  The supply proves the REPAIRED tie and it must NOT
-- prove the pre-repair one.  This file states the pre-repair `envK`,
-- verbatim from commit 26d25a7 as `[LJ-1.345]` read it off the diff, and
-- asks the supply for it.  Agda must refuse, and it must refuse at the
-- missing carrier hypothesis.
--
-- Without this control the supply could be an accident of a weaker type.
--
-- ONE agda process under GHCRTS="-A64m -I0 -M8g".

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

open import FOL.ZFStructure using ( module hPropStructure )
open import Cubical.HITs.CumulativeHierarchy.Base using ( _∈_ )

module LJ-1-344.ControlA344 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ} using ( 𝒮ʟ )
open import L.Axioms.Numerals {ℓ} using ( numeralL )

import L.Coding.Model
module GM = L.Coding.Model {ℓ}
open GM using ( prʟ )
open GM.AbsL using ( _^_ ) renaming ( _⊨ᵐ_ to _⊨_ )

open import L.Coding.Powerset {ℓ} lem using ( envOneAt )

open import LJ-1-344.Supply344 {ℓ} lem using ( module TieSupply )

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

  -- THE PRE-REPAIR TYPE.  No hypothesis bounds `z`.
  envK-unbounded : (E z : S) → ⟨ (E ∷ z ∷ γ) ⊨ envOneAt zero (suc zero) ⟩
                 → ⟨ fst E ∈ fst (lookup K γ) ⟩
  envK-unbounded E z = envK E z
