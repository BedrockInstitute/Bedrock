{-# OPTIONS --cubical --safe --guardedness #-}

-- LJ-1.209 CONTROL: does an `opaque` definition block conversion for code
-- LATER IN ITS OWN MODULE?  The seal probe defines `isNumeral` at the top of
-- the same module that uses it 46 times.  If `opaque` only sealed against
-- OTHER modules, the seal probe would be a no-op and its flat reading would
-- prove nothing.
--
-- EXPECTED: `sealed→open` FAILS to typecheck, and `unfolded→open` succeeds.
-- Comment `sealed→open` out to get the green half; leave it in to see the
-- refusal.  Both halves are recorded in the report.

module LJ-1-209.ProbeOpaqueReal where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using ( ℕ )

opaque
  isNum : ℕ → Type₀
  isNum n = n ≡ n

-- The green half: inside `unfolding`, the two types are the same type.
opaque
  unfolding isNum

  unfolded→open : (n : ℕ) → isNum n → n ≡ n
  unfolded→open n p = p

-- The red half.  Uncomment ONE line to see Agda refuse it.
-- sealed→open : (n : ℕ) → isNum n → n ≡ n
-- sealed→open n p = p
