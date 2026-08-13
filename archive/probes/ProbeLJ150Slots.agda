{-# OPTIONS --cubical --safe --guardedness #-}

-- LJ-1.50 probe A: the erase-to-Delta-0 certificate transfer built at
-- VARIABLE SLOTS and instantiated ONCE at the concrete leaf (P-u:
-- certify before you place).  The control is ProbeLJ150Control, the
-- same transfer stated directly at the concrete leaf (the 150.13 s
-- baseline from [LJ-1.49]).

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module ProbeLJ150Slots {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import FOL.Syntax using ( Formula )
open import FOL.LevyHierarchy using ( Δ₀ )
import FOL.Count
open import L.Constructible {ℓ} using ( 𝒮ʟ )
open import L.Condensation {ℓ} lem using ( DefBodyB; Δ₀-DefBodyB )
open import L.BoundedSubset {ℓ} lem using ( erase-Δ₀ )
open import Cubical.Data.Nat using ( _+_ )

open hPropStructure 𝒮ᵥ
module CS = hPropStructure 𝒮ʟ

module Cnt = FOL.Count.Count {ℓ = ℓ-suc ℓ} CS.S

-- The transfer at variable slots.  The elaborator normalizes the
-- built tree once, at variables, and the recursion over the
-- certificate happens in the module telescope.
module EraseLeaf {n : ℕ}
  (w K : Fin (5 + n))
  (N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 t0 t1 : Fin (5 + n)) where

  transfer : Δ₀
    (Cnt.erase
      (DefBodyB w K N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 t0 t1) refl)
  transfer = erase-Δ₀
    (DefBodyB w K N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 t0 t1) refl
    (Δ₀-DefBodyB w K N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 t0 t1)

-- The concrete leaf transfer: ONE instantiation at the end.
transfer-concrete : Δ₀
  (Cnt.erase
    (DefBodyB {0}
      zero zero zero zero zero zero zero zero
      zero zero zero zero zero zero zero zero) refl)
transfer-concrete = EraseLeaf.transfer {0}
  zero zero zero zero zero zero zero zero
  zero zero zero zero zero zero zero zero
