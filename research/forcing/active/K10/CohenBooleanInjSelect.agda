{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import FOL.ZFStructure using ( ZFStructure )
import NameKernel
import OrdinaryProfile
import CardinalBridge
import K8.CountableUnion
import K9.NameGround
import K10.CohenBooleanInjMaps

module K10.CohenBooleanInjSelect
  {ℓ} (𝒮 : ZFStructure (hPropAlgebra ℓ))
  (families : NameKernel.Families 𝒮)
  (accessible : NameKernel.Accessibility 𝒮)
  (images : NameKernel.MemberImage 𝒮)
  (pow : OrdinaryProfile.PowerSet 𝒮)
  (find : OrdinaryProfile.FoundationInduction 𝒮)
  (κ w : ZFStructure.S 𝒮)
  (lem : LEM ℓ)
  (paths : (x y : ZFStructure.S 𝒮)
         → (ZFStructure._≈ˢ_ 𝒮 x y) ≡ ((x ≡ y) , ZFStructure.isSetS 𝒮 x y))
  where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Semantics (hPropAlgebra ℓ) 𝒮 using ( module At )
open import OrdinaryProfile 𝒮 using ( ChoiceSet )
open import CodedVocabulary 𝒮 using ( isKPairΔ )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁ )
open TruthAlgebra (hPropAlgebra ℓ)
open hPropStructure 𝒮
open At S id using ( _⊨_ )
open NameKernel.Families families using ( hasCollect )

module Maps = K10.CohenBooleanInjMaps 𝒮 families accessible images pow κ w lem paths
module NG = K9.NameGround 𝒮 families accessible images pow κ w
  using ( extensional ; ≈ˢ-paths ; hasPair ; hasUnion ; hasSeparation )
module CU = K8.CountableUnion 𝒮 NG.extensional NG.≈ˢ-paths
  NG.hasPair NG.hasUnion pow NG.hasSeparation hasCollect find κ
module CB = CardinalBridge 𝒮

open Maps using ( hitFo )

module AtName (σ p ω₁ : S) where

  φ : _
  φ = hitFo σ p ω₁

  range : S
  range = Maps.Chk.product Maps.Chk.carrier w

  decode-range : (y : S) → ⟨ y ∈ˢ range ⟩
    → ∥ Σ[ r ∈ S ] Σ[ n ∈ S ]
        (⟨ r ∈ˢ Maps.Chk.carrier ⟩ × ⟨ n ∈ˢ w ⟩ × ⟨ isKPairΔ y r n ⟩) ∥₁
  decode-range y hy = Maps.Chk.product-out Maps.Chk.carrier w y hy

  decode-unique : (y r n r' n' : S)
    → ⟨ isKPairΔ y r n ⟩ → ⟨ isKPairΔ y r' n' ⟩
    → (r ≡ r') × (n ≡ n')
  decode-unique y r n r' n' = Maps.Chk.ordered-components y r n r' n'

  HitTotal : Type ℓ
  HitTotal =
    (ξ : S) → ⟨ ξ ∈ˢ ω₁ ⟩
    → ⟨ ⋁ S (λ y → (y ∈ˢ range) ⊓ ((y ∷ ξ ∷ []) ⊨ φ)) ⟩

  HitUnique : Type ℓ
  HitUnique =
    (ξ ξ' y : S) → ⟨ ξ ∈ˢ ω₁ ⟩ → ⟨ ξ' ∈ˢ ω₁ ⟩ → ⟨ y ∈ˢ range ⟩
    → ⟨ (y ∷ ξ ∷ []) ⊨ φ ⟩ → ⟨ (y ∷ ξ' ∷ []) ⊨ φ ⟩
    → ⟨ ξ ≈ˢ ξ' ⟩

  module FromHit (choice : ChoiceSet)
    (total : HitTotal) (unique : HitUnique) where

    inj-to-product : ⟨ CB.injectable ω₁ range ⟩
    inj-to-product = CU.choice-injection choice ω₁ range φ total unique
