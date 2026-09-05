{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.622]  THE TOP RUNG: the landing term, over the four measured
-- parts.  `landing-bisection` IS `CardAboveL`: the same declaration the
-- probe states at agents/tasks/LJ-1-528/Probe528.agda:638-643, now
-- reading its two inputs from the parts that were measured one at a
-- time.  Its own elaboration is the delta this probe attributes.
--
-- Nothing is postulated.  Nothing lands in src/.

open import Base.Prelude
open import Base.Classical using ( LEM )

module LJ-1-622.Probe622 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import LJ-1-622.Part1 {ℓ} lem using ( CardAboveLᵀ )
open import LJ-1-622.Part3 {ℓ} lem using ( noInjOrd→CardAboveLᵀ )
open import LJ-1-622.Part4 {ℓ} lem using ( noInjOrd )

landing-bisection : CardAboveLᵀ
landing-bisection = noInjOrd→CardAboveLᵀ noInjOrd
