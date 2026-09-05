{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.582]  SLICE S2.  D-10: is the tree's level-hood matrix
-- CONSTANT-FREE, so that it can be erased and re-embedded over the
-- hull's code carrier?  Nothing else is asked here.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-582.runs.S2 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.Manipulation.Parameters using ( countFo )
open import L.BoundedSubset {ℓ} lem using ( module LevelHood0 )

module LH0 = LevelHood0
  zero zero zero zero zero zero zero zero zero zero zero zero zero zero
  zero zero zero zero zero zero zero zero zero zero zero zero zero zero

-- THE ANSWER, AS A TERM.
matrix-constant-free : countFo LH0.matrix ≡ 0
matrix-constant-free = refl
