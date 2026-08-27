{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.685] W3.  Packing with an explicit formula argument.
-- The generic pack is runs/PACK.agda (green, 1.30 s).  This file
-- re-exports it so the W3 name the brief used is a green module.

open import Base.Prelude
open import Base.Classical using ( LEM )

module LJ-1-685.runs.W3 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import LJ-1-685.runs.PACK {ℓ} lem public
