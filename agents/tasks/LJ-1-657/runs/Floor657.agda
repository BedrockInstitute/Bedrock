{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.657] FLOOR.  What the ELABORATION FRAME costs before any term
-- of this task's own.  Coder clause, owner 2026-08-23: price the frame
-- first, on a heavy object, and trim the imports to the names the rows
-- actually use.
--
--   The two predecessors enter BY IMPORT, which is the honest way to
--   take a predecessor's type (coder clause, owner 2026-08-20).
--   [LJ-1.650] measured that route DEAD for [LJ-1.595]
--   (agents/tasks/LJ-1-650/Probe650.agda:6-14): importing that chain
--   exhausts the wide caliber's 2 GB on the frame alone.  This file
--   measures whether the SAME route is alive for [LJ-1.650],
--   [LJ-1.653] and [LJ-1.649], which import only src/.
--
-- Nothing is postulated.  No hole.  Nothing lands in src/.
-- ONE Agda process, caliber from the pane, never set here.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-657.runs.Floor657 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

import LJ-1-650.Probe650
import LJ-1-653.Probe653
import LJ-1-649.Probe649

module P650 = LJ-1-650.Probe650 {ℓ} lem
module P653 = LJ-1-653.Probe653 {ℓ} lem
module P649 = LJ-1-649.Probe649 {ℓ} lem
