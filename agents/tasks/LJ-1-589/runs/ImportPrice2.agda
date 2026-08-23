{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.589]  IMPORT PRICE ONLY, SECOND MEASUREMENT.  What [LJ-1.564]'s
-- probe costs to bring in, measured alone, before section 7 is built on
-- it.  [LJ-1.564] carries [LJ-1.550] and [LJ-1.558] with it.

open import Base.Prelude
open import Base.Classical using ( LEM )

module LJ-1-589.runs.ImportPrice2 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

import LJ-1-564.Probe564
module P564 = LJ-1-564.Probe564 {ℓ} lem
