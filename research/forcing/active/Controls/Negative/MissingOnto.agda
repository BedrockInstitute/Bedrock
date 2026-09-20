{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import FOL.ZFStructure using ( ZFStructure )
import OrdinaryProfile
import K7.OrderTypeUniqueness

module Controls.Negative.MissingOnto {ℓ}
  (𝒮 : ZFStructure (hPropAlgebra ℓ))
  (ext : OrdinaryProfile.Extensionality 𝒮)
  (paths : (x y : ZFStructure.S 𝒮)
    → ZFStructure._≈ˢ_ 𝒮 x y ≡ ((x ≡ y) , ZFStructure.isSetS 𝒮 x y))
  (find : OrdinaryProfile.FoundationInduction 𝒮)
  where

open import FOL.ZFStructure using ( module hPropStructure )
open TruthAlgebra (hPropAlgebra ℓ)
open hPropStructure 𝒮
module OrderType = K7.OrderTypeUniqueness 𝒮 ext paths find

with-onto : (f a A r : S) → ⟨ OrderType.CB.isInjection f a A ⟩
  → ⟨ OrderType.Onto f a A ⟩ → ⟨ OrderType.Preserves f a r ⟩
  → ⟨ OrderType.isOrderIso f a A r ⟩
with-onto = OrderType.order-isomorphism

missing-onto : (f a A r : S) → ⟨ OrderType.CB.isInjection f a A ⟩
  → ⟨ OrderType.Preserves f a r ⟩ → ⟨ OrderType.isOrderIso f a A r ⟩
missing-onto f a A r injective preserves =
  with-onto f a A r injective preserves preserves
