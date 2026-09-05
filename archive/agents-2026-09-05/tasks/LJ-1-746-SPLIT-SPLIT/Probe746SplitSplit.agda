{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.746-SPLIT-SPLIT] THE OBLIGATION.  One term: the green
-- split spelling of LJ-1.746-SPLIT packaged at the name the meter
-- reads.  graph-mirror is pure glue over runs/PT -- the row types
-- ApproxSlot/StepSlot and the transports approx-split/step-split are
-- PT's, the hypothesis type StepKilledGen is Amb7's -- and adds no
-- proof, no conversion, and no GraphAt assembly.  This is the W3
-- probe: whether the packaged alias converts in a fresh file.
--
-- MEASURED: runs/PT does not re-export Amb7's StepKilledGen into a
-- consumer's scope (runs/scope-pt.out, NotInScope at 11.5-18), so
-- Amb7 is imported directly beside PT, the spelling PT2 used
-- (746-SPLIT runs/PT2.agda.txt:26-27); runs/scope-pt2.out, rc 0.
--
-- ONE Agda process, caliber from the pane, never set here.
-- Nothing is postulated.  No hole in the delivered file.

open import Base.Prelude
open import Base.Classical using ( LEM )

module LJ-1-746-SPLIT-SPLIT.Probe746SplitSplit {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import LJ-1-746-SPLIT-SPLIT.runs.Amb7 {ℓ} lem
open import LJ-1-746-SPLIT-SPLIT.runs.PT {ℓ} lem

graph-mirror : StepKilledGen → ApproxSlot × StepSlot
graph-mirror gen = approx-split gen , step-split gen
