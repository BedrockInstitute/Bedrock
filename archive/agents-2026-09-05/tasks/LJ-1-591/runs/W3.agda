{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.591] W3, ALONE, TYPECHECKED BEFORE ANY OTHER AGDA OF THIS TASK.
--
-- The brief's W3 is "SquareCoded and row 5's square step, imported or
-- restated, side by side, TYPE ONLY".  The widest unmeasured term it
-- names is whether the two can be written in ONE file at all.
--
-- The risk is real and is not notation.  The two live in two probes
-- that were never opened together:
--
--   row 2  `LJ-1-583.Probe583`, which imports `LJ-1-576.Probe576`,
--          `L.CodedShift` and `L.Absorption`;
--   row 5  `LJ-1-581.Probe581`, which imports `LJ-1-556.Probe556`.
--
-- Both take the SAME module telescope, `{ℓ} (lem : LEM (ℓ-suc ℓ))`, so
-- the two applications below are at one ℓ and one `lem`.  No term is
-- written here.  Both types are re-ascribed at `Type (ℓ-suc ℓ)`, which
-- is the level each carries at its own site, so the ascription fails if
-- either is at another level.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-591.runs.W3 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import L.Constructible {ℓ} using ( 𝒮ʟ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ using ( S )

import LJ-1-583.Probe583 {ℓ} lem as P583
import LJ-1-581.Probe581 {ℓ} lem as P581

-- ROW 2's SQUARE.  agents/tasks/LJ-1-583/Probe583.agda:195-196.
RowTwoSquare : Type (ℓ-suc ℓ)
RowTwoSquare = P583.SquareCoded

-- ROW 5's SQUARE-LAW STEP.  agents/tasks/LJ-1-581/Probe581.agda:427-432.
RowFiveSquare : Type (ℓ-suc ℓ)
RowFiveSquare = P581.SquareStepInf

-- AND ROW 5's CONCLUSION, THE ONE OBJECT BOTH ROWS NAME.
-- agents/tasks/LJ-1-581/Probe581.agda:127-128.
RowFiveCoded : S → Type (ℓ-suc ℓ)
RowFiveCoded = P581.Coded
