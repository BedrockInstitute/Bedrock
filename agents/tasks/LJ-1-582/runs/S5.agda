{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.582]  SLICE S5.  BISECT OF THE runs/s4-1.out HEAP WALL.
-- THREE LINES: the erase, the re-embed, and the inverse.  Nothing else.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-582.runs.S5 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula )
open import FOL.Manipulation.Relabelling using ( embed )
open import FOL.Manipulation.Parameters using ( countFo )
open import L.Constructible {ℓ} using ( 𝒮ʟ )
open import L.BoundedSubset {ℓ} lem using ( module LevelHood0; module Cnt )

module CS = hPropStructure 𝒮ʟ

module LH0 = LevelHood0
  zero zero zero zero zero zero zero zero zero zero zero zero zero zero
  zero zero zero zero zero zero zero zero zero zero zero zero zero zero

cf : countFo LH0.matrix ≡ 0
cf = refl

ψ4 : Formula (⊥* {ℓ-suc ℓ}) 4
ψ4 = Cnt.erase LH0.matrix cf

matCS : Formula CS.S 4
matCS = embed ψ4

matCS≡ : matCS ≡ LH0.matrix
matCS≡ = Cnt.erase-inv LH0.matrix cf
