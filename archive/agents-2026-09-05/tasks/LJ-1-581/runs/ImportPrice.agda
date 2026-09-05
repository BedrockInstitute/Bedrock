{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.581]  WHERE THE 200 SECONDS LIVE.
--
-- Probe581 sections 1 to 3 cost 207.73 s (runs/s3-2.out) with EVERY
-- import already compiled, and adding sections 4 to 6 moved that to
-- 202.45 s (runs/s6-1.out).  So the number is not the probe's own
-- lines.  This slice names ONE import and nothing else, so the cost
-- can be attributed rather than guessed.
--
-- TWO RUNS, AND THE FILE CARRIES THE SECOND.  runs/price-1.out named
-- `L.Cardinal {ℓ} lem` and cost 1.65 s; runs/price-2.out names
-- `L.CantorBernstein {ℓ} lem`, the line below, and cost 1.64 s.
-- NEITHER import is the cost.  The 200 s was ONE TERM, and
-- runs/price-3.out found it.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-581.runs.ImportPrice {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import L.CantorBernstein {ℓ} lem using ( readL )
