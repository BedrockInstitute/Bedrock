{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.690] W3.  The forward packing is UNPACKING: thirteen
-- existentials at a generic formula.  Thin re-export of UNPACK,
-- the shape [LJ-1.685] landed on after the wall restructure.

open import Base.Prelude
open import Base.Classical using ( LEM )

module LJ-1-690.runs.W3 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import LJ-1-690.runs.UNPACK {ℓ} lem public
