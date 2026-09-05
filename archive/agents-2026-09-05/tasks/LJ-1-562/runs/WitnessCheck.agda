{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.562] WITNESS CHECK.  The meter's own derivation, reproduced.
--
-- `scripts/pod/witness.py:262-282` builds, for each obligation name,
-- a file whose preamble is copied verbatim from above the probe's
-- module header (`split_header`, :165-192), whose module application
-- is `binder_application` of the telescope (:194-201), and whose body
-- is the single line `witness = Target.<dotted-name>`.
--
-- Step 1's preamble, copied verbatim from Probe562.agda.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

-- Steps 2, 3 and 4.

module LJ-1-562.runs.WitnessCheck {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

import LJ-1-562.Probe562
module Target = LJ-1-562.Probe562 {ℓ} lem

witness = Target.constants-bounded
