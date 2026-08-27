{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.703] pins at the thirteen-slot env, from [LJ-1.672]
-- combinators.  No Reverse module (that would rebuild Matrix).
-- Rewritten here so this probe does not import LJ-1-685.runs.*.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-703.runs.PINS {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans )
open import L.Axioms.Numerals {ℓ} using ( numeralL )
open import Cubical.Data.Nat using ( _+_ )

import LJ-1-520.Probe520 {ℓ} lem as P520
import LJ-1-672.runs.W3 {ℓ} lem as W672

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ
module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL using ( _^_ ) renaming ( _⊨ᵐ_ to _⊨_ )

module At {n : ℕ} (w b : Fin n) (γ : S ^ n) (kk : S) where
  module Sl = P520.Slots w b
  private
    M = 13 + n
    n0 n1 n2 n3 n4 n5 n6 n7 n8 n9 n10 n11 : Fin M
    n0  = zero
    n1  = suc zero
    n2  = suc (suc zero)
    n3  = suc (suc (suc zero))
    n4  = suc (suc (suc (suc zero)))
    n5  = suc (suc (suc (suc (suc zero))))
    n6  = suc (suc (suc (suc (suc (suc zero)))))
    n7  = suc (suc (suc (suc (suc (suc (suc zero))))))
    n8  = suc (suc (suc (suc (suc (suc (suc (suc zero)))))))
    n9  = suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))
    n10 = suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))
    n11 = suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))

  env : S ^ M
  env = numeralL 0 ∷ numeralL 1 ∷ numeralL 2 ∷ numeralL 3
      ∷ numeralL 4 ∷ numeralL 5 ∷ numeralL 6 ∷ numeralL 7
      ∷ numeralL 8 ∷ numeralL 9 ∷ numeralL 10 ∷ numeralL 11
      ∷ kk ∷ γ

  hpins : ⟨ env ⊨ Sl.Mx.pins ⟩
  hpins =
    W672.empty0 n0 env refl
    , ( W672.suc-pin 0 n0 n1 env refl refl
    , ( W672.suc-pin 1 n1 n2 env refl refl
    , ( W672.suc-pin 2 n2 n3 env refl refl
    , ( W672.suc-pin 3 n3 n4 env refl refl
    , ( W672.suc-pin 4 n4 n5 env refl refl
    , ( W672.suc-pin 5 n5 n6 env refl refl
    , ( W672.suc-pin 6 n6 n7 env refl refl
    , ( W672.suc-pin 7 n7 n8 env refl refl
    , ( W672.suc-pin 8 n8 n9 env refl refl
    , ( W672.suc-pin 9 n9 n10 env refl refl
    , W672.suc-pin 10 n10 n11 env refl refl ))))))))))
