{-# OPTIONS --cubical --safe --guardedness #-}

-- LJ-1.269 Sketch B, step 0: does --safe permit reflection AT ALL in this tree?
-- The masters all carry {-# OPTIONS --cubical --safe --guardedness #-}.
-- This minimal probe answers one question: can a macro run under those flags.

module LJ-1-269.ProbeLJ1269ReflSafe where

open import Agda.Builtin.Reflection
open import Agda.Builtin.List
open import Agda.Builtin.Nat
open import Agda.Builtin.Unit

-- A macro that fills its hole with the literal 42.
macro
  answer : Term → TC ⊤
  answer hole = unify hole (lit (nat 42))

-- Use it: if this typechecks, reflection runs under --safe.
x : Nat
x = answer
