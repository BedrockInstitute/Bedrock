{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.619]  LADDER RUNG 3/11: THE CUMULATIVE IMPORTS 1..3, ONE TRIVIAL TERM.
--
-- The order of the eleven is [LJ-1.555]'s count of CardAboveL's
-- dependencies (agents/tasks/LJ-1-555/review-of-CardAboveL-landing.md:56).
-- Rung 11, the top, is agents/tasks/LJ-1-619/Probe619.agda.
-- A fresh Agda process typechecks this rung alone; the peak RSS,
-- the seconds and the exit are in runs/Rung03.out.
--
-- Nothing is postulated.  Nothing lands in src/.

module LJ-1-619.runs.Rung03 where

  open import Base.Prelude
  import L.Cardinal
  import L.BoundedSubset
  import L.CantorBernstein

  import-floor : Type → Type
  import-floor A = A
