{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.619]  LADDER RUNG 8/11: THE CUMULATIVE IMPORTS 1..8, ONE TRIVIAL TERM.
--
-- The order of the eleven is [LJ-1.555]'s count of CardAboveL's
-- dependencies (agents/tasks/LJ-1-555/review-of-CardAboveL-landing.md:56).
-- Rung 11, the top, is agents/tasks/LJ-1-619/Probe619.agda.
-- A fresh Agda process typechecks this rung alone; the peak RSS,
-- the seconds and the exit are in runs/Rung08.out.
--
-- Nothing is postulated.  Nothing lands in src/.

module LJ-1-619.runs.Rung08 where

  open import Base.Prelude
  import L.Cardinal
  import L.BoundedSubset
  import L.CantorBernstein
  import L.InjChain
  import L.Ordinal.Stages
  import L.Ordinal.Linear
  import L.Constructible
  import L.Ordinal

  import-floor : Type → Type
  import-floor A = A
