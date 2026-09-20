{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import FOL.ZFStructure using ( ZFStructure )
import OrdinaryProfile

module K7.DefinableFamilies {ℓ}
  (𝒮 : ZFStructure (hPropAlgebra ℓ))
  (ext : OrdinaryProfile.Extensionality 𝒮)
  (paths : (x y : ZFStructure.S 𝒮)
    → ZFStructure._≈ˢ_ 𝒮 x y ≡ ((x ≡ y) , ZFStructure.isSetS 𝒮 x y))
  (pair : OrdinaryProfile.Pairing 𝒮) (un : OrdinaryProfile.Union 𝒮)
  (pow : OrdinaryProfile.PowerSet 𝒮) (sep : OrdinaryProfile.Separation 𝒮)
  (coll : OrdinaryProfile.Collection 𝒮)
  (find : OrdinaryProfile.FoundationInduction 𝒮)
  (choice : OrdinaryProfile.ChoiceSet 𝒮) (seed : ZFStructure.S 𝒮)
  where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula )
open import FOL.Semantics (hPropAlgebra ℓ) 𝒮 using ( module At )
open import Cubical.Functions.Logic using ( ⇔toPath )
import Cubical.HITs.PropositionalTruncation as PT
import CardinalBridge
import K7.CardinalOrder
import K8.FamilyImages

open TruthAlgebra (hPropAlgebra ℓ)
open hPropStructure 𝒮
open At S id using ( _⊨_ )
open PT using ( ∣_∣₁ )
module CB = CardinalBridge 𝒮
module Image = K8.FamilyImages 𝒮 ext paths pair un pow sep coll find seed
module GS = Image.GS
module Order = K7.CardinalOrder.Order 𝒮 ext
  (λ x y z e → cong (_∈ˢ z) (GS.≈→≡ e))
  (λ x y z e → cong (x ∈ˢ_) (GS.≈→≡ e))

module AtFamily (β κ : S) (v : S → S) (φ : Formula S 2)
  (reading : (a ξ : S) → ⟨ ξ ∈ˢ β ⟩
    → ((a ∷ ξ ∷ []) ⊨ φ) ≡ (a ≈ˢ v ξ))
  (bounded : (ξ : S) → ⟨ ξ ∈ˢ β ⟩ → ⟨ CB.isSubset (v ξ) κ ⟩)
  where

  family : S
  family = Image.imageIn β (GS.power κ) φ

  family-spec : (a : S) → (a ∈ˢ family)
    ≡ ⋁ S (λ ξ → (ξ ∈ˢ β) ⊓ (a ≈ˢ v ξ))
  family-spec a = ⇔toPath
    (λ ha → PT.map (λ { (ξ , hξ , sat) →
      ξ , hξ , subst ⟨_⟩ (reading a ξ hξ) sat })
      (Image.image-out β (GS.power κ) φ a ha))
    (PT.rec (snd (a ∈ˢ family)) λ { (ξ , hξ , eq) →
      Image.image-in β (GS.power κ) φ ξ a hξ
        (subst (λ t → ⟨ t ∈ˢ GS.power κ ⟩) (sym (GS.≈→≡ eq))
          (subst ⟨_⟩ (sym (GS.power-spec κ (v ξ))) (bounded ξ hξ)))
        (subst ⟨_⟩ (sym (reading a ξ hξ)) eq) })

  family-injection : ⟨ CB.injectable family β ⟩
  family-injection = Image.image-countable choice β (GS.power κ) β φ
    (λ ξ a b hξ _ _ ha hb → subst ⟨_⟩ (sym (paths a b))
      (GS.≈→≡ (subst ⟨_⟩ (reading a ξ hξ) ha)
        ∙ sym (GS.≈→≡ (subst ⟨_⟩ (reading b ξ hξ) hb))))
    (Order.injectable-refl sep coll pair β)

  family-witness : ⟨ ⋁ S (λ F → CB.injectable F β
    ⊓ ⋀ S (λ a → OrdinaryProfile.iff 𝒮 (a ∈ˢ F)
      (⋁ S (λ ξ → (ξ ∈ˢ β) ⊓ (a ≈ˢ v ξ))))) ⟩
  family-witness = ∣ family , family-injection
    , (λ a → subst ⟨_⟩ (family-spec a) , subst ⟨_⟩ (sym (family-spec a))) ∣₁
