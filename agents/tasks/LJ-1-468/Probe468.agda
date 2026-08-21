{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.468]  Restate Internal's order as Formula S 1, with the five
-- background sets in Term position, in the RelCond / appAtC shape.
--
--   EIGHT-ROW TABLE  (reading of ≺At; src/L/Choice/Internal.lagda.md:741-747)
--
--   index  slot  what it names                 home
--   1      R     code-order                    becomes con (pinned)
--   2      P     parameter-order               becomes con
--   3      s₁    first name: skeleton          bound (StepAt's ∃₆)
--   4      a₁    first name: arity             bound
--   5      e₁    first name: environment       bound
--   6      s₂    second name: skeleton         bound
--   7      a₂    second name: arity            bound
--   8      e₂    second name: environment      bound
--
--   No slot has no home.  B, C, C₀ are not among the eight; they
--   are StepAt / LeastNameAt slots (Internal:910, :973) and become
--   con as well.  x and y of StepAt are bound from con B.  The free
--   variable of Formula S 1 is their pair, by prAtL.
--
--   W3 FIRST  `orderFo-type`.  The type the brief names.
--   TERM       `orderFo` restates StepAt as RelCond restates
--              PrecedesAt (src/L/Choice/Before.lagda.md:220-226):
--              pins by var ≐ con, members from ∃̇∈ (con B), pair
--              by prAtL.  StepAt stands at slots as delivered.
--              No conjunct of StepAt is dropped.  w is not read.
--
-- ONE Agda process per run, GHCRTS as the program set it on this pane.
-- Nothing lands in src/.  Do not import a probe.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-468.Probe468 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula; var; con; _≐_; _∧̇_; ∃̇_; ∃̇∈ )
open import L.Constructible {ℓ} using ( 𝒮ʟ )
open import L.Coding.Model {ℓ} using ( prAtL )
open import L.Choice.Internal {ℓ} lem using ( StepAt )
open import Cubical.Data.FinData using ( Fin; zero; suc )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ using ( S )

-- =====================================================================
-- W3.  The type the brief names.
-- =====================================================================

orderFo-type : Type _
orderFo-type = (R P B C C₀ : S) → Formula S 1

-- After five pin binders and two member binders the environment is
--   0 = y, 1 = x, 2 = C₀, 3 = C, 4 = B, 5 = P, 6 = R, 7 = z
-- Closed indices, Internal's s6a shape
-- (src/L/Choice/Internal.lagda.md:902-908).
private
  iY iX iC0 iCs iCar iPar iCod iZ
    : ∀ {n} → Fin (suc (suc (suc (suc (suc (suc (suc (suc n))))))))
  iY   = zero
  iX   = suc zero
  iC0  = suc (suc zero)
  iCs  = suc (suc (suc zero))
  iCar = suc (suc (suc (suc zero)))
  iPar = suc (suc (suc (suc (suc zero))))
  iCod = suc (suc (suc (suc (suc (suc zero)))))
  iZ   = suc (suc (suc (suc (suc (suc (suc zero))))))

-- =====================================================================
-- Obligation.  Five constants in Term position.  One free variable.
-- Shape: RelCond (Before.lagda.md:220-226), which is appAtC's move
-- of a set into a Term, scaled to the five slots StepAt reads.
-- =====================================================================

orderFo : (R P B C C₀ : S) → Formula S 1
orderFo R P B C C₀ =
  ∃̇ ( (var zero ≐ con R)
    ∧̇ ∃̇ ( (var zero ≐ con P)
      ∧̇ ∃̇ ( (var zero ≐ con B)
        ∧̇ ∃̇ ( (var zero ≐ con C)
          ∧̇ ∃̇ ( (var zero ≐ con C₀)
            ∧̇ ∃̇∈ (con B) ( ∃̇∈ (con B)
              ( prAtL iZ iX iY
              ∧̇ StepAt iCod iPar iCar iCs iC0 iX iY ) ) ) ) ) ) )
