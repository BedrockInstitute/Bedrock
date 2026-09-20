{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import FOL.ZFStructure using ( ZFStructure )
import NameKernel
import OrdinaryProfile

module K7.ValueFamilies
  {ℓ} (𝒮 : ZFStructure (hPropAlgebra ℓ))
  (families : NameKernel.Families 𝒮)
  (images : NameKernel.MemberImage 𝒮)
  (pow : OrdinaryProfile.PowerSet 𝒮)
  (find : OrdinaryProfile.FoundationInduction 𝒮)
  (choice : OrdinaryProfile.ChoiceSet 𝒮)
  (seed : ZFStructure.S 𝒮)
  where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula; con; ∃̇∈ )
open import FOL.Semantics (hPropAlgebra ℓ) 𝒮 using ( module At )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁ )
import CardinalBridge
import CodedVocabulary
import K8.GroundSets
import K8.CountableUnion
open import StandardNames 𝒮 using ( ∃-prop )

open TruthAlgebra (hPropAlgebra ℓ)
open hPropStructure 𝒮
open At S id using ( _⊨_ )
open NameKernel.Families families using ( sets; hasCollect )
open NameKernel.Sets sets using ( core; hasUnion; hasSeparation )
open NameKernel.Core core using ( extensional; hasPair; ≈ˢ-paths )
open NameKernel.MemberImage images using ( image; image-spec )

module CB = CardinalBridge 𝒮
module CV = CodedVocabulary 𝒮
module GS = K8.GroundSets.Ground 𝒮 extensional ≈ˢ-paths
  hasPair hasUnion pow hasSeparation seed
module CU = K8.CountableUnion 𝒮 extensional ≈ˢ-paths
  hasPair hasUnion pow hasSeparation hasCollect find seed

-- MemberImage is the inherited realization capability, not a consequence of
-- first-order Collection for an arbitrary host map. Choice below selects a
-- ground graph through a fixed formula, rather than a host family of choices.

module AtFamily (β : S) (v : S → S) where

  family : S
  family = image β (λ x → v (fst x))

  family-spec : (a : S) → (a ∈ˢ family)
    ≡ ⋁ S (λ ξ → (ξ ∈ˢ β) ⊓ (a ≈ˢ v ξ))
  family-spec a = image-spec β (λ x → v (fst x)) a
    ∙ cong (⋁ S) (funExt (λ ξ → ∃-prop (ξ ∈ˢ β) (a ≈ˢ v ξ)))

  table : S
  table = image β (λ x → GS.ordered (v (fst x)) (fst x))

  table-spec : (e : S) → (e ∈ˢ table)
    ≡ ⋁ S (λ ξ → (ξ ∈ˢ β) ⊓ (e ≈ˢ GS.ordered (v ξ) ξ))
  table-spec e = image-spec β (λ x → GS.ordered (v (fst x)) (fst x)) e
    ∙ cong (⋁ S) (funExt (λ ξ → ∃-prop (ξ ∈ˢ β)
      (e ≈ˢ GS.ordered (v ξ) ξ)))

  inverseFormula : Formula S 2
  inverseFormula = ∃̇∈ (con table)
    (CV.prAtˢ zero (suc (suc zero)) (suc zero))

  inverse-in : (ξ : S) → ⟨ ξ ∈ˢ β ⟩
    → ⟨ (ξ ∷ v ξ ∷ []) ⊨ inverseFormula ⟩
  inverse-in ξ hξ = ∣ GS.ordered (v ξ) ξ
    , subst ⟨_⟩ (sym (table-spec (GS.ordered (v ξ) ξ)))
      ∣ ξ , hξ , subst ⟨_⟩
        (sym (≈ˢ-paths (GS.ordered (v ξ) ξ) (GS.ordered (v ξ) ξ))) refl ∣₁
    , GS.ordered-witness (v ξ) ξ ∣₁

  inverse-out : (a ξ : S) → ⟨ (ξ ∷ a ∷ []) ⊨ inverseFormula ⟩ → a ≡ v ξ
  inverse-out a ξ = PT.rec (isSetS a (v ξ)) atEntry
    where
    atEntry : Σ[ e ∈ S ] (⟨ e ∈ˢ table ⟩ × ⟨ CV.isKPairΔ e a ξ ⟩)
      → a ≡ v ξ
    atEntry (e , he , kp) = PT.rec (isSetS a (v ξ)) atIndex
      (subst ⟨_⟩ (table-spec e) he)
      where
      atIndex : Σ[ η ∈ S ] (⟨ η ∈ˢ β ⟩ × ⟨ e ≈ˢ GS.ordered (v η) η ⟩)
        → a ≡ v ξ
      atIndex (η , hη , eq) = fst components ∙ cong v (sym (snd components))
        where
        components : (a ≡ v η) × (ξ ≡ η)
        components = GS.ordered-components e a ξ (v η) η kp
          (subst (λ z → ⟨ CV.isKPairΔ z (v η) η ⟩)
            (sym (GS.≈→≡ eq)) (GS.ordered-witness (v η) η))

  inverse-total : (a : S) → ⟨ a ∈ˢ family ⟩
    → ⟨ ⋁ S (λ ξ → (ξ ∈ˢ β) ⊓ ((ξ ∷ a ∷ []) ⊨ inverseFormula)) ⟩
  inverse-total a ha = PT.map
    (λ { (ξ , hξ , eq) → ξ , hξ
      , subst (λ x → ⟨ (ξ ∷ x ∷ []) ⊨ inverseFormula ⟩)
        (sym (GS.≈→≡ eq)) (inverse-in ξ hξ) })
    (subst ⟨_⟩ (family-spec a) ha)

  selected-injection : (g : S) → ⟨ CU.Selection family β inverseFormula g ⟩
    → ⟨ CB.isInjection g family β ⟩
  selected-injection g hg = hg .fst , hg .snd .fst
    , (λ e he a ξ kp → hg .snd .snd e he a ξ kp .snd .fst)
    , λ e he t ht a ξ b (kp , kq) → subst ⟨_⟩ (sym (≈ˢ-paths a b))
        (inverse-out a ξ (hg .snd .snd e he a ξ kp .snd .snd)
          ∙ sym (inverse-out b ξ (hg .snd .snd t ht b ξ kq .snd .snd)))

  family-injection : ⟨ CB.injectable family β ⟩
  family-injection = PT.map (λ { (g , hg) → g , selected-injection g hg })
    (CU.bounded-choice choice family β inverseFormula inverse-total)

  family-witness : ⟨ ⋁ S (λ F → CB.injectable F β
    ⊓ ⋀ S (λ a → OrdinaryProfile.iff 𝒮 (a ∈ˢ F)
      (⋁ S (λ ξ → (ξ ∈ˢ β) ⊓ (a ≈ˢ v ξ))))) ⟩
  family-witness = ∣ family , family-injection
    , (λ a → subst ⟨_⟩ (family-spec a) , subst ⟨_⟩ (sym (family-spec a))) ∣₁
