{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.589]  IMPORT PRICE ONLY.  What [LJ-1.558]'s probe costs to
-- bring in, measured alone, before the obligation is built on it.

open import Base.Prelude
open import Base.Classical using ( LEM )

module LJ-1-589.runs.ImportPrice {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

import LJ-1-558.Probe558
module P558 = LJ-1-558.Probe558 {ℓ} lem
