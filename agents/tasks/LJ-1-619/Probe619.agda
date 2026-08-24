{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.619]  THE IMPORT FLOOR OF A `CardAboveL` LANDING, AT RUNG 11/11.
--
-- THIS FILE IS THE TOP RUNG OF THE LADDER.  It imports exactly the eleven
-- modules that `[LJ-1.555]` counted as `CardAboveL`'s dependencies
-- (agents/tasks/LJ-1-555/review-of-CardAboveL-landing.md:56), in that
-- order, and it defines ONE trivial term.  It does not state `CardAboveL`
-- and it lands nothing in `src/`.
--
-- Rungs 1 through 10 are `runs/Rung01.agda` through `runs/Rung10.agda`:
-- the same imports, cumulative, one fewer at each rung.  A fresh Agda
-- process typechecks each rung alone, and `runs/*.out` carries the
-- peak RSS, the seconds and the exit.
--
-- Nothing is postulated.

module LJ-1-619.Probe619 where

open import Base.Prelude

import L.Cardinal
import L.BoundedSubset
import L.CantorBernstein
import L.InjChain
import L.Ordinal.Stages
import L.Ordinal.Linear
import L.Constructible
import L.Ordinal
import V.Model
import V.Presentation
import V.Hierarchy

import-floor : Type → Type
import-floor A = A
