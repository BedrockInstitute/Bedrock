{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.454] W3 PROBE.  Is the rank DESCRIBABLE as a Formula?
--
--   W3 FIRST  `rank-formula-type`.  The type the brief names:
--             Formula S 2, whose satisfaction at (z ∷ a ∷ []) would
--             say z is the pair of a member of a and that member's
--             rank.  Stated.  Typechecked ALONE.  Obligation omitted.
--
--   Internal  is imported so the checker loads every Formula it
--             delivers.  Those formulas describe the ORDER.  None
--             describes the RANK.  See review-of-rank-graph.md.
--
--   TERM      `rank-graph` is OMITTED.  The brief says: if Internal
--             delivers only the order and not the rank, STOP.
--
-- ONE Agda process per run, GHCRTS as the program set it on this pane.
-- Nothing lands in src/.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-454.Probe454 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula )
open import L.Constructible {ℓ} using ( 𝒮ʟ )
open import L.Choice.Internal {ℓ} lem
  using ( InLimitAt; FreeAt; DenoteBody; NameAt
        ; LexAt; ≺At; LeastNameAt; StepAt; StepBody )
open import Cubical.Data.FinData using ( Fin )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ using ( S )

-- =====================================================================
-- W3.  The type the brief names.  Stated.  Not inhabited.
-- Internal does not deliver an inhabitant.  See the review.
-- =====================================================================

rank-formula-type : Type _
rank-formula-type = Formula S 2

-- What Internal DOES deliver.  Binding the names forces the checker
-- to load them.  Every one is a Formula.  None is the rank.

order-formulas :
    (∀ {n} → Fin n → Formula S n)
  × (∀ {n} → Fin n → Fin n → Fin n → Formula S n)
  × (∀ {n} → Fin n → Fin n → Fin n → Fin n → Formula S (suc n))
  × (∀ {n} → Fin n → Fin n → Fin n → Fin n → Fin n → Fin n → Fin n
           → Formula S n)
  × (∀ {n} → Fin n → Fin n → Fin n → Fin n → Formula S n)
  × (∀ {n} → Fin n → Fin n → Fin n → Fin n
           → Fin n → Fin n → Fin n → Fin n → Formula S n)
  × (∀ {n} → Fin n → Fin n → Fin n → Fin n → Fin n
           → Fin n → Fin n → Fin n → Fin n → Formula S n)
  × (∀ {n} → Fin n → Fin n → Fin n → Fin n → Fin n → Fin n → Fin n
           → Formula S (suc (suc (suc (suc (suc (suc n)))))))
  × (∀ {n} → Fin n → Fin n → Fin n → Fin n → Fin n → Fin n → Fin n
           → Formula S n)
order-formulas =
    InLimitAt
  , FreeAt
  , DenoteBody
  , NameAt
  , LexAt
  , ≺At
  , LeastNameAt
  , StepBody
  , StepAt
