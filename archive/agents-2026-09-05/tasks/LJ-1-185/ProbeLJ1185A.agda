-- LJ-1.185, probe A.  ONE question: does Agda's benchmark account NEST the
-- definition phase inside the internal phase?
--
-- `[LJ-1.155]:134-139` and `[LJ-1.145]:86-100` both compute the seconds
-- "billed outside every definition" by SUBTRACTING one cold run from another
-- cold run.  That is arithmetic across two accounts, and it is INFERRED.
-- If Agda nests the accounts, then ONE run with both profile kinds on prints
-- the split directly and the subtraction is no longer needed.
--
-- This probe answers the format question only.  It is deliberately tiny and
-- imports nothing, so it costs milliseconds and no sibling can wall it.
--
-- Read with:
--   agda --profile=internal --profile=definitions --profile=modules

{-# OPTIONS --cubical --safe --guardedness #-}

module LJ-1-185.ProbeLJ1185A where

-- A generic carrier.  Nothing here names a tower, so the file
-- re-instantiates for the J side unchanged (DD4).

data Nat : Set where
  zero : Nat
  suc  : Nat → Nat

-- A module WITH A TELESCOPE.  Checking this telescope is Typing work that
-- belongs to no definition.

module Tele (a b c d e : Nat) where

  inside : Nat
  inside = suc a

  paired : Nat → Nat
  paired n = suc (suc n)

-- A module APPLICATION.  This is the construction `[LJ-1.177]` names.

module App1 = Tele zero zero zero zero zero
module App2 = Tele (suc zero) zero zero zero zero
module App3 = Tele (suc (suc zero)) zero zero zero zero

-- A plain definition, so the definitions account has a named row.

outside : Nat
outside = App1.inside
