{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.347] THE NEGATIVE CONTROL THAT MEASURES, RED HALF.
--
-- EXPECTED RED, exit 42.  A file that is expected to fail is a
-- measurement only when it fails at the line it names.
--
-- THE QUESTION.  Does my refutation turn on the CHOICE of the arity
-- element, or does it prove too much?  If `sgl1-not-numeral` also
-- applied to a genuine numeral, it would refute the conjunct at every
-- site and the countermodel would be measuring my own assembly.
--
-- THE TEST.  Offer it the numeral one instead of the singleton of the
-- numeral one.  Agda must REFUSE.
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

module LJ-1-347.ControlR347 {ℓ : Level} where

open import L.Axioms.Numerals {ℓ} using ( numeralL; numeralL-fst )
open import LJ-1-347.Elim347 {ℓ} using ( sgl1-not-numeral )

-- EXPECTED RED.  `sgl1-not-numeral` wants the SINGLETON of the numeral
-- one.  Here it is offered the numeral one itself.
too-much : (m : ℕ) → fst (numeralL 1) ≡ # m → Empty.⊥
too-much m q = sgl1-not-numeral m q
