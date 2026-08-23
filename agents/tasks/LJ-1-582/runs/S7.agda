{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.582]  SLICE S7.  S6 with the implicit formula argument SUPPLIED.
-- THREE LINES: the erase, the re-embed, and the inverse.  Nothing else.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-582.runs.S7 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula )
open import FOL.Manipulation.Relabelling using ( embed; mapΔ₀ )
open import FOL.LevyHierarchy using ( Δ₀ )
import Cubical.Data.Empty as Empty
open import FOL.Manipulation.Parameters using ( countFo )
open import L.Constructible {ℓ} using ( 𝒮ʟ )
open import L.BoundedSubset {ℓ} lem using ( module LevelHood0; module Cnt; erase-Δ₀ )

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

-- THE ONE CHANGE AGAINST runs/S6.agda.txt: `{φ = ψ4}` is written out, so the
-- elaborator never has to decide `mapFo ?f ?φ` against
-- `mapFo Empty.rec* (Cnt.erase LH0.matrix cf)` by normalising the matrix.
Δ₀-ψ4 : Δ₀ ψ4
Δ₀-ψ4 = erase-Δ₀ LH0.matrix cf LH0.Δ₀-matrix

Δ₀-matCS : Δ₀ matCS
Δ₀-matCS = mapΔ₀ Empty.rec* {φ = ψ4} Δ₀-ψ4
