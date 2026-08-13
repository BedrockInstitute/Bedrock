{-# OPTIONS --cubical --safe --guardedness #-}

-- DD25 review probe G1: decompose countFo of the level-hood matrix.
-- Read the numbers off the type error of `counts ≡ zeros`.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module ProbeDD25G1 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula )
open import FOL.Manipulation.Parameters using ( countFo )
open import L.Constructible {ℓ} using ( 𝒮ʟ )
open import L.Condensation {ℓ} lem using
  ( closedB; shapesB; shapedB; hasWitnessB; isCodeB; DefinesB; envOneBnd
  ; DefBodyB; module SatGraphB; module StepAtB )
open import L.BoundedSubset {ℓ} lem using ( module LevelHood0 )
open import Cubical.Data.Vec using ( Vec; _∷_; [] )

open hPropStructure 𝒮ʟ

module LH0 = LevelHood0
  zero zero zero zero zero zero zero zero zero zero zero zero zero zero
  zero zero zero zero zero zero zero zero zero zero zero zero zero zero

module SG = SatGraphB {0}
  zero zero zero zero zero zero zero zero zero zero zero zero zero zero
  zero zero

module SA = StepAtB {1}
  zero zero zero
  zero zero zero zero zero zero zero zero zero zero zero zero zero zero

counts : Vec ℕ 9
counts =
    countFo (isCodeB {1} zero zero zero)
  ∷ countFo (shapesB {1} zero zero)
  ∷ countFo (closedB {1} zero zero)
  ∷ countFo (DefinesB {1} zero zero zero zero)
  ∷ countFo (envOneBnd {1} zero zero)
  ∷ countFo SG.satGraphB
  ∷ countFo (DefBodyB {0} zero zero zero zero zero zero zero zero
                          zero zero zero zero zero zero zero zero)
  ∷ countFo SA.stepBndAt
  ∷ countFo LH0.matrix
  ∷ []

zeros : Vec ℕ 9
zeros = 29 ∷ 20 ∷ 8 ∷ 4 ∷ 2 ∷ 8 ∷ 41 ∷ 164 ∷ 328 ∷ []

read-the-error : counts ≡ zeros
read-the-error = refl
