{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import FOL.ZFStructure using ( ZFStructure )
import OrdinaryProfile

module K7.OrdinalTypeBounds {ℓ}
  (𝒮 : ZFStructure (hPropAlgebra ℓ))
  (ext : OrdinaryProfile.Extensionality 𝒮)
  (paths : (x y : ZFStructure.S 𝒮)
    → ZFStructure._≈ˢ_ 𝒮 x y ≡ ((x ≡ y) , ZFStructure.isSetS 𝒮 x y))
  (sep : OrdinaryProfile.Separation 𝒮)
  (find : OrdinaryProfile.FoundationInduction 𝒮)
  (lem : LEM ℓ)
  where

open import FOL.ZFStructure using ( module hPropStructure )
open import Cubical.Data.Sum using ( inl; inr )
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
import CardinalBridge
import K7.CardinalOrder

open TruthAlgebra (hPropAlgebra ℓ)
open hPropStructure 𝒮
module Cardinal = CardinalBridge 𝒮

member-cong : (x y z : S) → ⟨ x ≈ˢ y ⟩ → (x ∈ˢ z) ≡ (y ∈ˢ z)
member-cong x y z h = cong (λ t → t ∈ˢ z) (subst ⟨_⟩ (paths x y) h)

base-cong : (x y z : S) → ⟨ y ≈ˢ z ⟩ → (x ∈ˢ y) ≡ (x ∈ˢ z)
base-cong x y z h = cong (x ∈ˢ_) (subst ⟨_⟩ (paths y z) h)

module Order = K7.CardinalOrder.Order 𝒮 ext member-cong base-cong

ordinal-bound : (a w d : S) → ⟨ Cardinal.isOrdinal a ⟩
  → ⟨ Cardinal.isCardinal d ⟩ → ⟨ w ∈ˢ d ⟩
  → ⟨ Cardinal.injectable a w ⟩ → ⟨ a ∈ˢ d ⟩
ordinal-bound a w d oa cd wd aw = PT.rec (snd (a ∈ˢ d))
  (λ { (inl less) → less
     ; (inr rest) → PT.rec (snd (a ∈ˢ d))
       (λ { (inl equal) → Empty.rec (cd .snd w wd
              (Order.injectable-cong a d w equal aw))
          ; (inr greater) → Empty.rec (cd .snd w wd
              (Order.injectable-mono-dom d a w (oa .fst d greater) aw)) }) rest })
  (Order.ord-compare find sep lem a d oa (cd .fst))

through-injection : (pair : OrdinaryProfile.Pairing 𝒮)
  (coll : OrdinaryProfile.Collection 𝒮)
  (a A w d : S) → ⟨ Cardinal.isOrdinal a ⟩
  → ⟨ Cardinal.isCardinal d ⟩ → ⟨ w ∈ˢ d ⟩
  → ⟨ Cardinal.injectable a A ⟩ → ⟨ Cardinal.injectable A w ⟩
  → ⟨ a ∈ˢ d ⟩
through-injection pair coll a A w d oa cd wd aA Aw =
  ordinal-bound a w d oa cd wd
    (Order.injectable-trans sep coll pair a A w aA Aw)
