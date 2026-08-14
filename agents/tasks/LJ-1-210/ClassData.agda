{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.210] the class, bundled.  THIS FILE WALLS.  IT IS KEPT AS THE
-- RECORD OF THE WALL, and `CD1.agda` to `CD6.agda` are its bisect.
--
-- The flat telescope measured in section 4 of the report costs 6
-- pre-module imports plus 11 parameter lines, and EVERY module down the
-- chain repeats both.  This record would carry the same data once, so a
-- module down the chain would take ONE parameter.
--
-- MEASURED WALL: `agda ClassData.agda` exhausts the 8 GB heap at
-- 105.07 s.  The cap was NOT raised.  `CD5.agda` bisects the wall to
-- ONE field, `sucʟ-fst`, and `CD6.agda` puts the IDENTICAL type in a
-- module telescope and in a top-level definition, where it costs
-- 1.41 s.  The cause is not established and I do not guess at it.

open import Base.Prelude
open import Base.Truth

open import FOL.ZFStructure using ( Transitive )
open import V.Hierarchy using ( 𝒮ᵥ )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ⁅_,_⁆ ) renaming ( module InfinitySet to Inf )
open Inf using ( #_; sucV )

module LJ-1-210.ClassData where

record ClassData (ℓ : Level) : Type (ℓ-suc (ℓ-suc ℓ)) where
  field
    M : V ℓ → hProp (ℓ-suc ℓ)
    M-trans : Transitive (𝒮ᵥ {ℓ}) M

  Carrier : Type (ℓ-suc ℓ)
  Carrier = Σ[ x ∈ V ℓ ] ⟨ M x ⟩

  field
    numeralL : ℕ → Carrier
    numeralL-fst : (k : ℕ) → fst (numeralL k) ≡ # k
    pairʟ : Carrier → Carrier → Carrier
    pairʟ-fst : (a b : Carrier) → fst (pairʟ a b) ≡ ⁅ fst a , fst b ⁆
    sucʟ : Carrier → Carrier
    sucʟ-fst : (a : Carrier) → fst (sucʟ a) ≡ sucV (fst a)
