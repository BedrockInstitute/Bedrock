{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import FOL.ZFStructure using ( ZFStructure )
import CardinalBridge

module K10.CohenBooleanPowerSrc {ℓ} (𝒮 : ZFStructure (hPropAlgebra ℓ)) where

open import FOL.Syntax using ( Formula ; var ; ∀̇_ ; _∈̇_ ; _⇒̇_ ; _∧̇_ )
open import FOL.Manipulation.ConstantOccurrences using ( module ZeroOccurrences )
open import FOL.Manipulation.Renaming using ( renameFo )
import CardinalBridge

module CB = CardinalBridge 𝒮
module ZO = ZeroOccurrences (ZFStructure.S 𝒮)

infixr 11 _↔̇_
_↔̇_ : ∀ {K : Type ℓ} {n : ℕ} → Formula K n → Formula K n → Formula K n
φ ↔̇ ψ = (φ ⇒̇ ψ) ∧̇ (ψ ⇒̇ φ)

Src : ℕ → Type ℓ
Src n = Formula (⊥* {ℓ}) n

subsetSrc : Src 2
subsetSrc = ZO.erase CB.Subsetφ refl

subset-shape : subsetSrc
  ≡ ∀̇ ((var zero ∈̇ var (suc zero)) ⇒̇ (var zero ∈̇ var (suc (suc zero))))
subset-shape = refl

powerSrc : Src 2
powerSrc = ZO.erase CB.IsPowerSetφ refl

power-shape : powerSrc
  ≡ ∀̇ ((var zero ∈̇ var (suc zero)) ↔̇ (renameFo CB.pow-emb subsetSrc))
power-shape = refl
