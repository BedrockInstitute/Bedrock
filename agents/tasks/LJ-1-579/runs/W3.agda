{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.579] W3.  THE WIDEST UNMEASURED TERM IS THE FLOOR ITSELF.
--
-- The brief: "stage-high, STATED with a hole, in the trimmed frame,
-- timed and sized.  Write it FIRST and measure it."
--
-- THE TRIMMED FRAME IS THREE IMPORTS.  `StageHigh` is [LJ-1.536]'s
-- type and this file IMPORTS it rather than restating it, so nothing
-- here can drift from what that task typechecked
-- (agents/tasks/LJ-1-536/Probe536.agda:350-352).
--
-- A HOLE IS NOT AVAILABLE UNDER `--safe`, so the floor is measured in
-- the two forms that ARE, and both are reported:
--   `Obligation`  the type, FORMED.  This is what an empty body costs.
--   `reduction`   [LJ-1.536]'s own green reduction, re-ascribed, which
--                 is the cheapest term whose type IS the obligation up
--                 to one hypothesis.
--
-- ONE Agda process per run, GHCRTS="-A64m -I0 -M8g", the wide caliber,
-- set on the pane by the program and untouched here.

open import Base.Prelude
open import Base.Classical using ( LEM )

module LJ-1-579.runs.W3 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import LJ-1-536.Probe536 {ℓ} lem
  using ( StageHigh; HierBelowAll; reduction )

------------------------------------------------------------------------
-- THE FLOOR.  The obligation's TYPE, formed in the trimmed frame.
------------------------------------------------------------------------

Obligation : Type (ℓ-suc ℓ)
Obligation = StageHigh

------------------------------------------------------------------------
-- THE CHEAPEST TERM AT THAT TYPE, up to one hypothesis.  Re-ascribed
-- from [LJ-1.536], not restated.
------------------------------------------------------------------------

floor-term : HierBelowAll → Obligation
floor-term = reduction
