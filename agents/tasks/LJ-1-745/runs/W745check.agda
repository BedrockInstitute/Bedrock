{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Classical using ( LEM )

module LJ-1-745.runs.W745check {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

import LJ-1-745.Probe745
module Target = LJ-1-745.Probe745 {ℓ} lem

witness = Target.step-killed
