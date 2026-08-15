{-# OPTIONS --cubical --safe --guardedness #-}

-- LJ-1.269 Sketch B, step 1: how do macro arguments arrive?
-- Test whether a macro argument with a concrete type arrives as a VALUE
-- (which the macro can pattern-match on) or as a quoted Term.

module LJ-1-269.ProbeLJ1269MacroArgs where

open import Agda.Builtin.Reflection
open import Agda.Builtin.List
open import Agda.Builtin.Nat
open import Agda.Builtin.Unit
open import Agda.Builtin.Bool

-- A macro that receives a Nat argument. We test whether it can compute on it.
macro
  isZero : Nat → Term → TC ⊤
  isZero Nat.zero hole = unify hole (con (quote true) [])
  isZero (Nat.suc n) hole = unify hole (con (quote false) [])

t₁ : Bool
t₁ = isZero 0

t₂ : Bool
t₂ = isZero 5
