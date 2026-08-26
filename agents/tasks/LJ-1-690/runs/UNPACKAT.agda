{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.690] unpack13 instantiated at Matrix.matrix, matrix a HYPOTHESIS.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-690.runs.UNPACKAT {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans )
open import Cubical.Data.Nat using ( _+_ )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁ )

import LJ-1-520.Probe520 {ℓ} lem as P520
import LJ-1-690.runs.UNPACK {ℓ} lem as UK

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ
module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL using ( _^_ ) renaming ( _⊨ᵐ_ to _⊨_ )

module At {n : ℕ} (w b : Fin n) (γ : S ^ n) where
  module Sl = P520.Slots w b

  -- P-t: seal the matrix so unpack13 sees an atom, not DefBodyB.
  opaque
    mat : Formula S (13 + n)
    mat = Sl.Mx.matrix

  opaque
    unfolding mat
    from-levelFo : ⟨ γ ⊨ fst (P520.levelFo-Σ₁ w b) ⟩ → ⟨ γ ⊨ UK.Rem.ψ13 mat ⟩
    from-levelFo = subst (λ φ → ⟨ γ ⊨ φ ⟩) (sym eq)
      where
      eq : UK.Rem.ψ13 mat ≡ fst (P520.levelFo-Σ₁ w b)
      eq = refl

    to-graph : {δ : S ^ (13 + n)}
             → ⟨ δ ⊨ mat ⟩ → ⟨ δ ⊨ Sl.Mx.G.graphBndAt ⟩
    to-graph h = h .snd .snd

  unpacked : ⟨ γ ⊨ fst (P520.levelFo-Σ₁ w b) ⟩ → ∥ UK.Wit mat γ ∥₁
  unpacked h = UK.unpack13 mat γ (from-levelFo h)
