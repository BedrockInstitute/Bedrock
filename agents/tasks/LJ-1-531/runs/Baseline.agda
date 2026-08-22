{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.531]  THE IMPORT'S OWN PRICE, so that the obligation's price is
-- the DELTA against it and not the whole file's wall time.  This module
-- imports [LJ-1.521] and defines nothing.

open import Base.Prelude
open import Base.Classical using ( LEM )

module LJ-1-531.runs.Baseline {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

import LJ-1-521.Probe521 {ℓ} lem as P521
