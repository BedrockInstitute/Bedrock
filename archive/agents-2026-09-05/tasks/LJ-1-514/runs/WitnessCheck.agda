{-# OPTIONS --cubical --safe --guardedness #-}

-- The witness meter of amendment A1, reproduced locally in the form
-- scripts/pod/witness.py derives (witness_source, :260-280): the term
-- reference `witness = Target.<name>`, not an `open ... using`.
-- The obligation must resolve from OUTSIDE the probe, and [LJ-1.494]
-- measured what happens when it does not (runs/witness.out of that task).

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-514.runs.WitnessCheck {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

import LJ-1-514.Probe514
module Target = LJ-1-514.Probe514 {ℓ} lem

witness = Target.graphFo-at-SL
