{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.703] thirteen existentials packed at a GENERIC formula.
-- W2: written once, instantiated at Matrix.matrix by the consumer.
-- φ is an argument at every pack∃, never inferred.
-- Rewritten here so this probe does not import LJ-1-685.runs.*.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-703.runs.PACK {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula; ∃̇_ )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans )
open import Cubical.Data.Nat using ( _+_ )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ
module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL using ( _^_ ) renaming ( _⊨ᵐ_ to _⊨_ )

pack∃ : {n : ℕ} (φ : Formula S (suc n)) (x : S) {δ : S ^ n}
      → ⟨ (x ∷ δ) ⊨ φ ⟩ → ⟨ δ ⊨ ∃̇ φ ⟩
pack∃ _ x h = ∣ x , h ∣₁

-- Nested remainder formulas, generic in φ.
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

pack13 : {n : ℕ} (φ : Formula S (13 + n))
       → (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 : S)
       → (γ : S ^ n)
       → ⟨ (x0 ∷ x1 ∷ x2 ∷ x3 ∷ x4 ∷ x5 ∷ x6 ∷ x7 ∷ x8 ∷ x9 ∷ x10 ∷ x11 ∷ x12 ∷ γ) ⊨ φ ⟩
       → ⟨ γ ⊨ Rem.ψ13 φ ⟩
pack13 {n} φ x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 γ h =
  pack∃ R.ψ12 x12 {δ = γ} (
  pack∃ R.ψ11 x11 {δ = e12} (
  pack∃ R.ψ10 x10 {δ = e11} (
  pack∃ R.ψ9  x9  {δ = e10} (
  pack∃ R.ψ8  x8  {δ = e9} (
  pack∃ R.ψ7  x7  {δ = e8} (
  pack∃ R.ψ6  x6  {δ = e7} (
  pack∃ R.ψ5  x5  {δ = e6} (
  pack∃ R.ψ4  x4  {δ = e5} (
  pack∃ R.ψ3  x3  {δ = e4} (
  pack∃ R.ψ2  x2  {δ = e3} (
  pack∃ R.ψ1  x1  {δ = e2} (
  pack∃ φ     x0  {δ = e1} h
  ))))))))))))
  where
  module R = Rem {n} φ
  e1  = x1 ∷ x2 ∷ x3 ∷ x4 ∷ x5 ∷ x6 ∷ x7 ∷ x8 ∷ x9 ∷ x10 ∷ x11 ∷ x12 ∷ γ
  e2  = x2 ∷ x3 ∷ x4 ∷ x5 ∷ x6 ∷ x7 ∷ x8 ∷ x9 ∷ x10 ∷ x11 ∷ x12 ∷ γ
  e3  = x3 ∷ x4 ∷ x5 ∷ x6 ∷ x7 ∷ x8 ∷ x9 ∷ x10 ∷ x11 ∷ x12 ∷ γ
  e4  = x4 ∷ x5 ∷ x6 ∷ x7 ∷ x8 ∷ x9 ∷ x10 ∷ x11 ∷ x12 ∷ γ
  e5  = x5 ∷ x6 ∷ x7 ∷ x8 ∷ x9 ∷ x10 ∷ x11 ∷ x12 ∷ γ
  e6  = x6 ∷ x7 ∷ x8 ∷ x9 ∷ x10 ∷ x11 ∷ x12 ∷ γ
  e7  = x7 ∷ x8 ∷ x9 ∷ x10 ∷ x11 ∷ x12 ∷ γ
  e8  = x8 ∷ x9 ∷ x10 ∷ x11 ∷ x12 ∷ γ
  e9  = x9 ∷ x10 ∷ x11 ∷ x12 ∷ γ
  e10 = x10 ∷ x11 ∷ x12 ∷ γ
  e11 = x11 ∷ x12 ∷ γ
  e12 = x12 ∷ γ
