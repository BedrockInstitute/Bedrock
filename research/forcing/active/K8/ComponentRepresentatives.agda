{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import FOL.ZFStructure using ( ZFStructure )
import OrdinaryProfile

module K8.ComponentRepresentatives
  {ℓ} (𝒮 : ZFStructure (hPropAlgebra ℓ))
  (ext : OrdinaryProfile.Extensionality 𝒮)
  (paths : (x y : ZFStructure.S 𝒮)
    → ZFStructure._≈ˢ_ 𝒮 x y ≡ ((x ≡ y) , ZFStructure.isSetS 𝒮 x y))
  (pair : OrdinaryProfile.Pairing 𝒮)
  (un : OrdinaryProfile.Union 𝒮)
  (pow : OrdinaryProfile.PowerSet 𝒮)
  (sep : OrdinaryProfile.Separation 𝒮)
  (coll : OrdinaryProfile.Collection 𝒮)
  (find : OrdinaryProfile.FoundationInduction 𝒮)
  (seed : ZFStructure.S 𝒮)
  where

open import FOL.ZFStructure using ( module hPropStructure )
open import Base.Classical using ( LEM )
open import FOL.Syntax using ( Formula; var; con; _∈̇_; _∧̇_; _⇒̇_; ∀̇_; ∀̇∈ )
open import FOL.Semantics (hPropAlgebra ℓ) 𝒮 using ( module At )
open import OrdinaryProfile 𝒮 using ( ChoiceSet; iff )
open import CodedVocabulary 𝒮 using ( subsetΔ )
import CardinalBridge
import K8.GroundSets
import K8.ConnectedComponents
import K8.FamilyImages
import K8.Uncountability
import K8.CountableZFC
import K8.DisjointFamilies
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁; ∣_∣₁ )

open TruthAlgebra (hPropAlgebra ℓ)
open hPropStructure 𝒮
open At S id using ( _⊨_ )
module GS = K8.GroundSets.Ground 𝒮 ext paths pair un pow sep seed
module CB = CardinalBridge 𝒮
module FI = K8.FamilyImages 𝒮 ext paths pair un pow sep coll find seed
module UC = K8.Uncountability 𝒮 ext paths pair un pow sep coll find seed
module CZ = K8.CountableZFC 𝒮 ext paths pair un pow sep coll find seed
module DJ = K8.DisjointFamilies 𝒮 ext paths pair un pow sep seed
open CB using ( _↔̇_ )

module AtOmega (lem : LEM ℓ) (choice : ChoiceSet) (w : S) (hw : ⟨ CB.isOmega w ⟩) where
  module CZω = CZ.AtOmega lem choice w hw

  module Family (F X : S)
    (component-countable : (a : S) → ⟨ a ∈ˢ F ⟩
      → ⟨ CB.injectable
          (K8.ConnectedComponents.Family.component 𝒮 ext paths pair un pow sep coll find seed F X a) w ⟩)
    where
    module CC = K8.ConnectedComponents.Family 𝒮 ext paths pair un pow sep coll find seed F X

    Component : S → S → Ω
    Component D a = ⋀ S (λ b → iff (b ∈ˢ D) ((b ∈ˢ F) ⊓ CC.Reach a b))

    componentFormula : Formula S 2
    componentFormula = ∀̇ ((var zero ∈̇ var (suc zero)) ↔̇
      ((var zero ∈̇ con F) ∧̇ ∀̇∈ (con (GS.power F))
        ((var (suc (suc (suc zero))) ∈̇ var zero) ⇒̇
          (CC.closedAt zero ⇒̇ (var (suc zero) ∈̇ var zero)))))

    component-reading : (D a : S) → ((D ∷ a ∷ []) ⊨ componentFormula) ≡ Component D a
    component-reading D a = refl

    component-witness : (a : S) → ⟨ Component (CC.component a) a ⟩
    component-witness a b = subst ⟨_⟩ (CC.component-spec a b)
      , subst ⟨_⟩ (sym (CC.component-spec a b))

    component-unique : (D a : S) → ⟨ Component D a ⟩ → D ≡ CC.component a
    component-unique D a h = GS.≈→≡ (ext D (CC.component a) λ b →
      (λ hb → component-witness a b .snd (h b .fst hb))
      , (λ hb → h b .snd (component-witness a b .fst hb)))

    Components : S
    Components = FI.imageIn F (GS.power F) componentFormula

    components-in : (a : S) → ⟨ a ∈ˢ F ⟩ → ⟨ CC.component a ∈ˢ Components ⟩
    components-in a ha = FI.image-in F (GS.power F) componentFormula a (CC.component a) ha
      (subst ⟨_⟩ (sym (GS.power-spec F (CC.component a))) (CC.component-sub a))
      (component-witness a)

    components-out : (D : S) → ⟨ D ∈ˢ Components ⟩
      → ⟨ ⋁ S (λ a → (a ∈ˢ F) ⊓ Component D a) ⟩
    components-out D = FI.image-out F (GS.power F) componentFormula D

    members-sub : (D : S) → ⟨ D ∈ˢ Components ⟩ → ⟨ subsetΔ D F ⟩
    members-sub D hD = subst ⟨_⟩ (GS.power-spec F D)
      (FI.image-sub F (GS.power F) componentFormula D hD)

    members-countable : (D : S) → ⟨ D ∈ˢ Components ⟩ → ⟨ CB.injectable D w ⟩
    members-countable D hD = PT.rec (snd (CB.injectable D w))
      (λ { (a , ha , h) → subst (λ t → ⟨ CB.injectable t w ⟩)
        (sym (component-unique D a h)) (component-countable a ha) }) (components-out D hD)

    cover : (a : S) → ⟨ a ∈ˢ F ⟩
      → ⟨ ⋁ S (λ D → (D ∈ˢ Components) ⊓ (a ∈ˢ D)) ⟩
    cover a ha = ∣ CC.component a , components-in a ha , CC.component-self a ha ∣₁

    components-uncountable : ⟨ UC.uncountable w F ⟩ → ⟨ UC.uncountable w Components ⟩
    components-uncountable unF countC = unF
      (CZω.countable-union Components F members-sub cover countC members-countable)

    members-inhabited : (D : S) → ⟨ D ∈ˢ Components ⟩ → ⟨ ⋁ S (λ a → a ∈ˢ D) ⟩
    members-inhabited D hD = PT.map (λ { (a , ha , h) → a ,
      subst (λ t → ⟨ a ∈ˢ t ⟩) (sym (component-unique D a h)) (CC.component-self a ha) })
      (components-out D hD)

    members-disjoint : (D E : S) → ⟨ D ∈ˢ Components ⟩ → ⟨ E ∈ˢ Components ⟩
      → ∥ Σ[ z ∈ S ] (⟨ z ∈ˢ D ⟩ × ⟨ z ∈ˢ E ⟩) ∥₁ → D ≡ E
    members-disjoint D E hD hE common = PT.rec (isSetS D E)
      (λ { (a , ha , da) → PT.rec (isSetS D E)
      (λ { (b , hb , eb) → PT.rec (isSetS D E)
      (λ { (z , zd , ze) → component-unique D a da
        ∙ CC.component-equal lem a z ha
          (subst (λ t → ⟨ z ∈ˢ t ⟩) (component-unique D a da) zd)
        ∙ sym (CC.component-equal lem b z hb
          (subst (λ t → ⟨ z ∈ˢ t ⟩) (component-unique E b eb) ze))
        ∙ sym (component-unique E b eb) }) common }) (components-out E hE) }) (components-out D hD)

    Selected : S → Ω
    Selected c = ⋀ S (λ D → (D ∈ˢ Components) ⇒
      ((⋁ S (λ a → (a ∈ˢ c) ⊓ (a ∈ˢ D))) ⊓
        ⋀ S (λ a → ⋀ S (λ b → (((a ∈ˢ c) ⊓ (a ∈ˢ D)) ⊓
          ((b ∈ˢ c) ⊓ (b ∈ˢ D))) ⇒ (a ≈ˢ b)))))

    module AtSelection (c : S) (selected : ⟨ Selected c ⟩) where

      B : S
      B = GS.separator F (var zero ∈̇ con c)

      B-spec : (a : S) → (a ∈ˢ B) ≡ ((a ∈ˢ F) ⊓ (a ∈ˢ c))
      B-spec a = GS.separator-spec F (var zero ∈̇ con c) a

      B-sub : ⟨ subsetΔ B F ⟩
      B-sub a ha = subst ⟨_⟩ (B-spec a) ha .fst

      B-selected : (a : S) → ⟨ a ∈ˢ B ⟩ → ⟨ a ∈ˢ c ⟩
      B-selected a ha = subst ⟨_⟩ (B-spec a) ha .snd

      onto : (D : S) → ⟨ D ∈ˢ Components ⟩
        → ⟨ ⋁ S (λ b → (b ∈ˢ B) ⊓ ((D ∷ b ∷ []) ⊨ componentFormula)) ⟩
      onto D hD = PT.rec (snd (⋁ S (λ b → (b ∈ˢ B) ⊓ Component D b)))
        (λ { (a , ha , da) → PT.map (λ { (b , bc , bd) → b ,
          subst ⟨_⟩ (sym (B-spec b)) (members-sub D hD b bd , bc)
          , subst (λ t → ⟨ Component t b ⟩)
            (sym (component-unique D a da ∙ CC.component-equal lem a b ha
              (subst (λ t → ⟨ b ∈ˢ t ⟩) (component-unique D a da) bd)))
            (component-witness b) }) (selected D hD .fst) }) (components-out D hD)

      B-uncountable : ⟨ UC.uncountable w F ⟩ → ⟨ UC.uncountable w B ⟩
      B-uncountable unF countB = components-uncountable unF
        (UC.countable-image choice B Components w componentFormula onto
          (λ a D E ha hD hE da ea → subst ⟨_⟩ (sym (paths D E))
            (component-unique D a da ∙ sym (component-unique E a ea))) countB)

      B-disjoint : ⟨ DJ.pairwiseDisjoint B ⟩
      B-disjoint a ha b hb neq z za zb = neq
        (selected (CC.component a) (components-in a (B-sub a ha)) .snd a b
          ((B-selected a ha , CC.component-self a (B-sub a ha))
            , (B-selected b hb , CC.adjacent-in-component a b (B-sub a ha) (B-sub b hb)
              ∣ z , za , zb ∣₁)))

    disjoint-uncountable : ⟨ UC.uncountable w F ⟩
      → ⟨ ⋁ S (λ B → subsetΔ B F ⊓ (UC.uncountable w B ⊓ DJ.pairwiseDisjoint B)) ⟩
    disjoint-uncountable unF = PT.map
      (λ { (c , selected) → AtSelection.B c selected , AtSelection.B-sub c selected
        , AtSelection.B-uncountable c selected unF , AtSelection.B-disjoint c selected })
      (choice Components members-inhabited members-disjoint)
