{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.690] thirteen existentials unpacked at a GENERIC formula.
-- W2: written once, instantiated at Matrix.matrix by the consumer.
-- φ is an argument at every unpack∃, never inferred.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-690.runs.UNPACK {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula; ∃̇_ )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans )
open import Cubical.Data.Nat using ( _+_ )
open import Cubical.Data.Vec using ( _∷_ )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁; ∣_∣₁; squash₁ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ
module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL using ( _^_ ) renaming ( _⊨ᵐ_ to _⊨_ )

unpack∃ : {n : ℕ} (φ : Formula S (suc n)) {δ : S ^ n}
        → ⟨ δ ⊨ ∃̇ φ ⟩ → ∥ Σ[ x ∈ S ] ⟨ (x ∷ δ) ⊨ φ ⟩ ∥₁
unpack∃ _ h = h

bind : {A B : Type (ℓ-suc ℓ)} → ∥ A ∥₁ → (A → ∥ B ∥₁) → ∥ B ∥₁
bind m f = PT.rec squash₁ f m

-- Nested remainder formulas, generic in φ.  Dual of [LJ-1.685] Rem.
module Rem {n : ℕ} (φ : Formula S (13 + n)) where
  ψ1 : Formula S (12 + n)
  ψ1 = ∃̇ φ
  ψ2 : Formula S (11 + n)
  ψ2 = ∃̇ ψ1
  ψ3 : Formula S (10 + n)
  ψ3 = ∃̇ ψ2
  ψ4 : Formula S (9 + n)
  ψ4 = ∃̇ ψ3
  ψ5 : Formula S (8 + n)
  ψ5 = ∃̇ ψ4
  ψ6 : Formula S (7 + n)
  ψ6 = ∃̇ ψ5
  ψ7 : Formula S (6 + n)
  ψ7 = ∃̇ ψ6
  ψ8 : Formula S (5 + n)
  ψ8 = ∃̇ ψ7
  ψ9 : Formula S (4 + n)
  ψ9 = ∃̇ ψ8
  ψ10 : Formula S (3 + n)
  ψ10 = ∃̇ ψ9
  ψ11 : Formula S (2 + n)
  ψ11 = ∃̇ ψ10
  ψ12 : Formula S (1 + n)
  ψ12 = ∃̇ ψ11
  ψ13 : Formula S n
  ψ13 = ∃̇ ψ12

record Wit {n : ℕ} (φ : Formula S (13 + n)) (γ : S ^ n) : Type (ℓ-suc ℓ) where
  constructor mk
  field
    x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 : S
    hφ : ⟨ (x0 ∷ x1 ∷ x2 ∷ x3 ∷ x4 ∷ x5 ∷ x6 ∷ x7 ∷ x8 ∷ x9 ∷ x10 ∷ x11 ∷ x12 ∷ γ) ⊨ φ ⟩

unpack13 : {n : ℕ} (φ : Formula S (13 + n)) (γ : S ^ n)
         → ⟨ γ ⊨ Rem.ψ13 φ ⟩ → ∥ Wit φ γ ∥₁
unpack13 {n} φ γ h =
  bind (unpack∃ R.ψ12 h) λ (x12 , h12) →
  bind (unpack∃ R.ψ11 h12) λ (x11 , h11) →
  bind (unpack∃ R.ψ10 h11) λ (x10 , h10) →
  bind (unpack∃ R.ψ9  h10) λ (x9  , h9)  →
  bind (unpack∃ R.ψ8  h9)  λ (x8  , h8)  →
  bind (unpack∃ R.ψ7  h8)  λ (x7  , h7)  →
  bind (unpack∃ R.ψ6  h7)  λ (x6  , h6)  →
  bind (unpack∃ R.ψ5  h6)  λ (x5  , h5)  →
  bind (unpack∃ R.ψ4  h5)  λ (x4  , h4)  →
  bind (unpack∃ R.ψ3  h4)  λ (x3  , h3)  →
  bind (unpack∃ R.ψ2  h3)  λ (x2  , h2)  →
  bind (unpack∃ R.ψ1  h2)  λ (x1  , h1)  →
  bind (unpack∃ φ     h1)  λ (x0  , h0)  →
  ∣ mk x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 h0 ∣₁
  where
  module R = Rem {n} φ
