{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.455] W3 PROBE.  Can ≺At's eight Fin-slots become Formula S 1
-- at a fixed `a`?
--
--   W3 FIRST  `orderFo-type`.  The type the brief names:
--             (a : S) → Formula S 1.  Stated.  Typechecked ALONE.
--             Obligation omitted.
--
--   MEASURE   `≺At-at-one` is the only Formula S 1 that ≺At forms
--             without a restatement: Fin 1 has one inhabitant, so
--             every slot is zero, and `a` does not appear.
--             `inclFo-shape` is the live specialisation the brief
--             named as the model.  `pairFo` is what `a` alone CAN
--             fix (the pair of two members).  None of these is
--             the order of `a`.
--
--   TERM      `order-as-set` is OMITTED.  The brief says: if seven
--             slots cannot be fixed from `a` alone, STOP.
--
-- ONE Agda process per run, GHCRTS as the program set it on this pane.
-- Nothing lands in src/.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-455.Probe455 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula; con; ∃̇∈ )
open import L.Constructible {ℓ} using ( 𝒮ʟ )
open import L.Coding.Model {ℓ} using ( prAtL )
open import L.Choice.Internal {ℓ} lem using ( ≺At; StepAt )
open import Cubical.Data.FinData using ( Fin; zero; suc )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ using ( S )

-- =====================================================================
-- W3.  The type the brief names.  Stated.  Not inhabited as the
-- specialisation the brief asks for.  See review-of-order-as-set.md.
-- =====================================================================

orderFo-type : Type _
orderFo-type = (a : S) → Formula S 1

-- The only Formula S 1 that ≺At forms without rewriting its body.
-- Fin 1 has one inhabitant.  Every slot is that inhabitant.
≺At-at-one : Formula S 1
≺At-at-one = ≺At zero zero zero zero zero zero zero zero

-- StepAt, the comparison of two MEMBERS, collapsed the same way.
-- Seven Fin 1 indices, all zero.  Still no use of `a`.
StepAt-at-one : Formula S 1
StepAt-at-one = StepAt zero zero zero zero zero zero zero

-- The shape the brief named.  A set enters as `con`, in a Term
-- position.  Copied from src/L/InjChain.lagda.md:445-446 so the
-- checker sees the specialisation.  Not an import of a probe.
inclFo-shape : S → Formula S 1
inclFo-shape D = ∃̇∈ (con D) (prAtL (suc zero) zero zero)

-- What `a` alone CAN fix in that shape: z is a pair of two members
-- of `a`.  No order.  The two extra Fin-slots of prAtL are the two
-- bound members, not seven name-components.
pairFo : S → Formula S 1
pairFo a = ∃̇∈ (con a) (∃̇∈ (con a) (prAtL (suc (suc zero)) (suc zero) zero))
