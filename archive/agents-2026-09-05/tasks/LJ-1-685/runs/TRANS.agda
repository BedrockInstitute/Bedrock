{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.685] transK at the ω-block K.  Bound.trans∈λ, [LJ-1.678] Block.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-685.runs.TRANS {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans; IsOrd )
open import L.Axioms.Basic {ℓ} using ( LsetS )
open import L.Axioms.Numerals {ℓ} using ( numeralL )
open import L.Coding.Bound {ℓ} lem using ( module Bound )
open import Cubical.Data.Vec using ( lookup )
open import Cubical.Data.Nat using ( _+_ )

import LJ-1-520.Probe520 {ℓ} lem as P520
import LJ-1-678.runs.W3 {ℓ} lem as W678

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ
module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL using ( _^_ ) renaming ( _⊨ᵐ_ to _⊨_ )

module At {n : ℕ} (w b : Fin n) (γ : S ^ n)
          (ob : IsOrd (fst (lookup b γ))) where
  open W678.Block (fst (lookup b γ)) ob
  module B = Bound lam ordλ succλ ∅∈λ
  module Sl = P520.Slots w b

  kk : S
  kk = LsetS lam ordλ

  private
    M = 13 + n

  env : S ^ M
  env = numeralL 0 ∷ numeralL 1 ∷ numeralL 2 ∷ numeralL 3
      ∷ numeralL 4 ∷ numeralL 5 ∷ numeralL 6 ∷ numeralL 7
      ∷ numeralL 8 ∷ numeralL 9 ∷ numeralL 10 ∷ numeralL 11
      ∷ kk ∷ γ

  htrans : ⟨ env ⊨ Sl.Mx.transK ⟩
  htrans N N∈K v v∈N =
    B.trans∈λ {x = fst N} {y = fst v} v∈N N∈K
