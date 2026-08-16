{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.347] THE NEGATIVE CONTROL THAT MEASURES, POSITIVE HALF.
--
-- A refutation says the statement at ONE site is false.  It must not say
-- the statement is absurd everywhere, or it would be measuring my own
-- assembly and not the site (C-42).  So this file exhibits the arity
-- conjunct HOLDING, at the same shape, one argument away.
--
-- IT DISCRIMINATES.  The same file carries both halves:
--   * the numeral one IS a numeral, so the conjunct is SATISFIABLE;
--   * the singleton of the numeral one is NOT, at every index.
-- Nothing but the choice of the arity element separates them.
--
-- EXPECTED GREEN.  The red half is `ControlR347.agda`.
--
-- ONE agda process under GHCRTS="-A64m -I0 -M8g".

open import Base.Prelude
open import Base.Truth

open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ⁅_,_⁆ ) renaming ( module InfinitySet to Inf )
open Inf using ( #_ )
open import Cubical.Data.Nat using ( ℕ )
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁; ∣_∣₁ )

module LJ-1-347.Control347 {ℓ : Level} where

open import L.Axioms.Numerals {ℓ} using ( numeralL; numeralL-fst )
open import LJ-1-347.Elim347 {ℓ} using ( sgl1-not-numeral )

-- THE CONJUNCT IS SATISFIABLE.  This is the tie's own last conjunct,
-- src/L/Condensation.lagda.md:7245, with the arity slot a real numeral.
-- So the tie is not absurd for every arity, and the refutation measures
-- the SITE.
numeral-arity-holds : ∥ Σ[ n ∈ ℕ ] (fst (numeralL 1) ≡ # n) ∥₁
numeral-arity-holds = ∣ 1 , numeralL-fst 1 ∣₁

-- AND IT FAILS AT THE COUNTERMODEL'S ARITY, at EVERY index.  One
-- argument separates the two lines above and below.
singleton-arity-fails : (m : ℕ) → ⁅ # 1 , # 1 ⁆ ≡ # m → Empty.⊥
singleton-arity-fails = sgl1-not-numeral

-- NON-VACUITY OF THE REFUTATION'S OWN SHAPE.  `Residue347.agda` builds
-- `wS-in-K`, `cS-in-wS` and `codeEq` as CLOSED terms from the delivered
-- record, so the tie is applied to arguments that exist and not to a
-- hypothesis nobody can meet.  See `Residue347.Wire`, exit 0 in 3.16 s.
