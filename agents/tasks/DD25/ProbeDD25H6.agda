{-# OPTIONS --cubical --safe --guardedness #-}

-- DD25 review probe H6: the return's VARIABLE-SLOT probe, with the
-- count proof NAMED.
--
-- `src/ProbeLJ150Slots.agda:37-42` writes `refl` inline twice, exactly
-- as its control does.  Its 167.64 s therefore compares one artefact
-- with another, and the return reads the 17 s gap as a content-class
-- fact.  This probe repeats the variable-slot transfer with the count
-- proof named once, so the comparison against ProbeDD25H3 is a
-- comparison of SPELLINGS OF THE SLOTS and of nothing else.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module ProbeDD25H6 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import FOL.Syntax using ( Formula )
open import FOL.LevyHierarchy using ( Δ₀ )
open import FOL.Manipulation.Parameters using ( countFo )
import FOL.Count
open import L.Constructible {ℓ} using ( 𝒮ʟ )
open import L.Condensation {ℓ} lem using ( DefBodyB; Δ₀-DefBodyB )
open import L.BoundedSubset {ℓ} lem using ( erase-Δ₀ )
open import Cubical.Data.Nat using ( _+_ )

open hPropStructure 𝒮ᵥ
module CS = hPropStructure 𝒮ʟ

module Cnt = FOL.Count.Count {ℓ = ℓ-suc ℓ} CS.S

-- The transfer at variable slots.  Same shape as ProbeLJ150Slots
-- :33-42, with the count proof named.
module EraseLeaf {n : ℕ}
  (w K : Fin (5 + n))
  (N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 t0 t1 : Fin (5 + n)) where

  φ : Formula CS.S (suc (suc (suc (5 + n))))
  φ = DefBodyB w K N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 t0 t1

  d : Δ₀ φ
  d = Δ₀-DefBodyB w K N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 t0 t1

  count-φ : countFo φ ≡ 0
  count-φ = refl

  transfer : Δ₀ (Cnt.erase φ count-φ)
  transfer = erase-Δ₀ φ count-φ d

-- The concrete leaf transfer: ONE instantiation at the end.
transfer-concrete : Δ₀
  (Cnt.erase (EraseLeaf.φ {0}
      zero zero zero zero zero zero zero zero
      zero zero zero zero zero zero zero zero)
    (EraseLeaf.count-φ {0}
      zero zero zero zero zero zero zero zero
      zero zero zero zero zero zero zero zero))
transfer-concrete = EraseLeaf.transfer {0}
  zero zero zero zero zero zero zero zero
  zero zero zero zero zero zero zero zero
