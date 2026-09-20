{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import FOL.ZFStructure using ( ZFStructure )
import NameKernel
import OrdinaryProfile
import CardinalBridge
import K7.CardinalOrder
import K9.NameGround
import K10.CohenBooleanInjBot

-- Ground injection ω → ω₁ from transitivity, and the Boolean lift
-- combinator inj-top-from. No Pipe. No Force. No Miximal.

module K10.CohenBooleanInjWx
  {ℓ} (𝒮 : ZFStructure (hPropAlgebra ℓ))
  (families : NameKernel.Families 𝒮)
  (accessible : NameKernel.Accessibility 𝒮)
  (images : NameKernel.MemberImage 𝒮)
  (pow : OrdinaryProfile.PowerSet 𝒮)
  (κ w : ZFStructure.S 𝒮)
  (lem : LEM ℓ)
  (paths : (x y : ZFStructure.S 𝒮)
         → (ZFStructure._≈ˢ_ 𝒮 x y) ≡ ((x ≡ y) , ZFStructure.isSetS 𝒮 x y))
  where

open import FOL.ZFStructure using ( module hPropStructure )
open NameKernel.Families families using ( hasCollect )

open TruthAlgebra (hPropAlgebra ℓ)
open hPropStructure 𝒮

module IB = K10.CohenBooleanInjBot 𝒮 families accessible images pow κ w lem paths
module NG = K9.NameGround 𝒮 families accessible images pow κ w
  using ( extensional ; ≈ˢ-paths ; hasPair ; hasSeparation )
module CB = CardinalBridge 𝒮
module CO = K7.CardinalOrder.Order 𝒮 NG.extensional
  (λ x y z e → cong (_∈ˢ z) (subst ⟨_⟩ (NG.≈ˢ-paths x y) e))
  (λ x y z e → cong (x ∈ˢ_) (subst ⟨_⟩ (NG.≈ˢ-paths y z) e))

open IB using ( Nameᴮ ; val ; injSrc ; injBody ; inj-top-from ; checkNm ; emptyEnv ; ⊤B )

module AtCardinal
  (ω₁ : S)
  (hω₁ : ⟨ CB.isCardinal ω₁ ⟩)
  (hw₁ : ⟨ w ∈ˢ ω₁ ⟩)
  where

  subset-w : ⟨ CB.isSubset w ω₁ ⟩
  subset-w = hω₁ .fst .fst w hw₁

  ground-wx : ⟨ CB.injectable w ω₁ ⟩
  ground-wx =
    CO.injectable-incl NG.hasSeparation hasCollect NG.hasPair w ω₁ subset-w

  wx-env = checkNm w ∷ checkNm ω₁ ∷ emptyEnv

  wx-top-from : (σ : Nameᴮ)
    → val injBody (σ ∷ checkNm w ∷ checkNm ω₁ ∷ emptyEnv) ≡ ⊤B
    → val injSrc wx-env ≡ ⊤B
  wx-top-from = inj-top-from (checkNm w) (checkNm ω₁)
