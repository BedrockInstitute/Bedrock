{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.703] pack13 instantiated at Matrix.matrix, matrix a HYPOTHESIS.
-- Rewritten here so this probe does not import LJ-1-685.runs.*.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-703.runs.PACKAT {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans )
open import L.Axioms.Numerals {ℓ} using ( numeralL )
open import Cubical.Data.Nat using ( _+_ )

import LJ-1-520.Probe520 {ℓ} lem as P520
import LJ-1-703.runs.PACK {ℓ} lem as PK

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ
module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL using ( _^_ ) renaming ( _⊨ᵐ_ to _⊨_ )

module At {n : ℕ} (w b : Fin n) (γ : S ^ n) (kk : S) where
  module Sl = P520.Slots w b
  env = numeralL 0 ∷ numeralL 1 ∷ numeralL 2 ∷ numeralL 3
      ∷ numeralL 4 ∷ numeralL 5 ∷ numeralL 6 ∷ numeralL 7
      ∷ numeralL 8 ∷ numeralL 9 ∷ numeralL 10 ∷ numeralL 11
      ∷ kk ∷ γ

  -- P-t: seal the matrix so pack13 sees an atom, not DefBodyB.
  opaque
    mat : Formula S (13 + n)
    mat = Sl.Mx.matrix

  packed : ⟨ env ⊨ mat ⟩ → ⟨ γ ⊨ PK.Rem.ψ13 mat ⟩
  packed hmatrix =
    PK.pack13 mat
      (numeralL 0) (numeralL 1) (numeralL 2) (numeralL 3)
      (numeralL 4) (numeralL 5) (numeralL 6) (numeralL 7)
      (numeralL 8) (numeralL 9) (numeralL 10) (numeralL 11)
      kk γ hmatrix

  opaque
    unfolding mat
    from-conj : ⟨ env ⊨ Sl.Mx.transK ⟩
              → ⟨ env ⊨ Sl.Mx.pins ⟩
              → ⟨ env ⊨ Sl.Mx.G.graphBndAt ⟩
              → ⟨ env ⊨ mat ⟩
    from-conj t p g = t , (p , g)

    to-levelFo : ⟨ γ ⊨ PK.Rem.ψ13 mat ⟩ → ⟨ γ ⊨ fst (P520.levelFo-Σ₁ w b) ⟩
    to-levelFo = subst (λ φ → ⟨ γ ⊨ φ ⟩) eq
      where
      eq : PK.Rem.ψ13 mat ≡ fst (P520.levelFo-Σ₁ w b)
      eq = refl
