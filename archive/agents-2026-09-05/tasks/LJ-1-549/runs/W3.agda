{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.549] W3.  THE FORMULA THAT CARVES THE TABLE FROM δ INTO b.
-- TYPE ONLY.  No inhabitant, no separation, no adequacy.  This slice
-- is typechecked ALONE, before any other Agda of this task, exactly as
-- the brief ordered.
--
-- WHAT IT MEASURES.  The table the obligation needs is
--
--     F  =  { pr α (s α) : α ∈ δ },      s α ⊆ κ,   s injective,
--
-- and a separation carves it out of a bound by ONE `Formula S 1`.
-- This file writes that formula down.  Four conjuncts.  THREE of them
-- are written here from delivered vocabulary.  THE FOURTH, the
-- functional link between the argument and the value, enters as a
-- PARAMETER, because nothing in the tree produces it.
--
-- The bound `powL κ` is the power set of κ inside L.  It needs NO
-- model record: `hasPowerL` (src/L/Axioms/Power.lagda.md:187) is
-- unconditional, and `℩-spec` reads its membership as `⊆ˢ κ` on the
-- nose.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-549.runs.W3 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula; var; con; _∈̇_; _∧̇_; ∃̇_ )
import FOL.ZFModel
open import L.Constructible {ℓ} using ( 𝒮ʟ )
open import L.Axioms.Power {ℓ} lem using ( hasPowerL )
open import L.Coding.Model {ℓ} using ( prAtL )
open import Cubical.Data.FinData using ( Fin; zero; suc )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ using ( S )

module ModelL = FOL.ZFModel 𝒮ʟ
open ModelL using ( ℩ )

-- The power set of κ inside L, as a term of the model, with no `zf`.
powL : S → S
powL κ = ℩ (hasPowerL κ)

-- ==================================================================
-- THE FORMULA.  ARITY 1.  Its one free variable is the separation
-- variable z, the candidate member of the bound.
--
-- FREE VARIABLES AND SLOTS, under the two binders:
--
--     var 2  =  z, the candidate pair          (the separation slot)
--     var 1  =  x, the argument                (bound, outer ∃)
--     var 0  =  y, the value                   (bound, inner ∃)
--
-- CONJUNCT 1.  z is the ordered pair of x and y.        `prAtL`
-- CONJUNCT 2.  x is a member of δ.                      `∈̇ con δ`
-- CONJUNCT 3.  y is a member of the power set of κ,
--              which by `℩-spec` IS `y ⊆ˢ κ`.           `∈̇ con (powL κ)`
-- CONJUNCT 4.  y is THE value at x.                     `Link`  <-- MISSING
-- ==================================================================

TableFo : (δ κ : S) → Formula S 3 → Formula S 1
TableFo δ κ Link =
  ∃̇ ∃̇ ( prAtL (suc (suc zero)) (suc zero) zero
       ∧̇ ( (var (suc zero) ∈̇ con δ)
         ∧̇ ( (var zero ∈̇ con (powL κ)) ∧̇ Link ) ) )
