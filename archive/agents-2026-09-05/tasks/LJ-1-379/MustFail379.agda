{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.379] EXPECTED RED.  DO NOT REPAIR THIS FILE.
--
-- THE CONTROL FOR `Back379.agda`'s GREEN, ITS OTHER HALF.
--
-- The green's `har` walks the twelve clauses and closes each member
-- with `arityNumAtL-in`, taking the NUMERAL from the fourth component
-- of the telescope's own `codesK`/`unCodesK`.  This file measures that
-- that component is LOAD-BEARING: without it, the only numeral the
-- flat witness equation carries is the TAG `k`, and a builder who
-- offers the tag where the arity belongs does not typecheck.
--
-- The refusal below is the measurement: the equation `e` speaks about
-- `fst N` in the first component, and nothing in the flat witness
-- says `fst N` is a numeral.  `[LJ-1.368]`'s lesson stands behind
-- this: a green into a truncation-valued motive must be shown to need
-- its inputs, not merely to typecheck.
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
open import Cubical.Data.Nat using ( ℕ )

module LJ-1-379.MustFail379 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Coding {ℓ} using ( pr )
open import L.Constructible {ℓ} using ( 𝒮ʟ )
open import L.Axioms.Numerals {ℓ} using ( numeralL; numeralL-fst )

import L.Coding.Model
module GM = L.Coding.Model {ℓ}
open GM using ( prʟ; prʟ-fst )
open GM.AbsL using ( _^_ ) renaming ( _⊨ᵐ_ to _⊨_ )

open import L.Coding.CodeSet {ℓ} lem using ( arityNumAtL; arityNumAtL-in )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ using ( S )

-- THE FLAT WITNESS EQUATION, with no `codesK` beside it.  The tag `k`
-- is the only numeral in sight, and it is offered where the arity
-- belongs.
module Naive {n : ℕ} (γ : S ^ n) (w : S) where

  naive-bin : (k : ℕ) (c N a b : S) → ⟨ fst c ∈ fst w ⟩
           → fst c ≡ pr (fst N) (pr (# k) (pr (fst a) (fst b)))
           → ⟨ (c ∷ w ∷ γ) ⊨ arityNumAtL zero ⟩
  naive-bin k c N a b hc e =
    arityNumAtL-in zero (c ∷ w ∷ γ) k (prʟ (numeralL k) (prʟ a b))
      (e ∙ cong (λ u → pr u (pr (# k) (pr (fst a) (fst b)))) refl)
