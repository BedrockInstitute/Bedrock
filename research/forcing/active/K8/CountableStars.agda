{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import FOL.ZFStructure using ( ZFStructure )
import OrdinaryProfile

module K8.CountableStars
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
open import FOL.Syntax using ( Formula; var; con; _∈̇_; _∧̇_; ∀̇_; ∃̇∈ )
open import FOL.Semantics (hPropAlgebra ℓ) 𝒮 using ( module At )
open import CodedVocabulary 𝒮 using ( subsetΔ )
open import OrdinaryProfile 𝒮 using ( ChoiceSet; iff )
import K8.GroundSets
import K8.FamilyImages
import K8.CountableUnion
import CardinalBridge
open import GroundDescription 𝒮 ext paths using ( ext-path )
open import Cubical.Functions.Logic using ( ⇔toPath )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁ )

open TruthAlgebra (hPropAlgebra ℓ)
open hPropStructure 𝒮
open At S id using ( _⊨_ )

module GS = K8.GroundSets.Ground 𝒮 ext paths pair un pow sep seed
module FI = K8.FamilyImages 𝒮 ext paths pair un pow sep coll find seed
module CU = K8.CountableUnion 𝒮 ext paths pair un pow sep coll find seed
module CB = CardinalBridge 𝒮
open CB using ( _↔̇_ )

module Family (F X : S) where
  opaque
    star : S → S
    star x = GS.separator F (con x ∈̇ var zero)

    star-spec : (x b : S) → (b ∈ˢ star x) ≡ ((b ∈ˢ F) ⊓ (x ∈ˢ b))
    star-spec x b = GS.separator-spec F (con x ∈̇ var zero) b

  star-sub : (x : S) → ⟨ subsetΔ (star x) F ⟩
  star-sub x b hb = fst (subst ⟨_⟩ (star-spec x b) hb)

  starSpec : S → S → Ω
  starSpec d x = ⋀ S (λ b → iff (b ∈ˢ d) ((b ∈ˢ F) ⊓ (x ∈ˢ b)))

  starFormula : Formula S 2
  starFormula = ∀̇ ((var zero ∈̇ var (suc zero)) ↔̇
    ((var zero ∈̇ con F) ∧̇ (var (suc (suc zero)) ∈̇ var zero)))

  star-reading : (d x : S) → ((d ∷ x ∷ []) ⊨ starFormula) ≡ starSpec d x
  star-reading d x = refl

  star-witness : (x : S) → ⟨ starSpec (star x) x ⟩
  star-witness x b = subst ⟨_⟩ (star-spec x b) , subst ⟨_⟩ (sym (star-spec x b))

  star-unique : (d x : S) → ⟨ starSpec d x ⟩ → d ≡ star x
  star-unique d x hd = ext-path (λ b →
    ⇔toPath (fst (hd b)) (snd (hd b)) ∙ sym (star-spec x b))

  starFamily : S → S
  starFamily a = FI.imageIn a (GS.power F) starFormula

  star-family-in : (a x : S) → ⟨ x ∈ˢ a ⟩ → ⟨ star x ∈ˢ starFamily a ⟩
  star-family-in a x hx = FI.image-in a (GS.power F) starFormula x (star x) hx
    (subst ⟨_⟩ (sym (GS.power-spec F (star x))) (star-sub x))
    (subst ⟨_⟩ (sym (star-reading (star x) x)) (star-witness x))

  neighborhoodFormula : S → Formula S 1
  neighborhoodFormula a = ∃̇∈ (con a) (var zero ∈̇ var (suc zero))

  meets : S → S → Ω
  meets a b = ⋁ S (λ x → (x ∈ˢ a) ⊓ (x ∈ˢ b))

  opaque
    neighborhood : S → S
    neighborhood a = GS.separator F (neighborhoodFormula a)

    neighborhood-spec : (a b : S)
      → (b ∈ˢ neighborhood a) ≡ ((b ∈ˢ F) ⊓ meets a b)
    neighborhood-spec a b = GS.separator-spec F (neighborhoodFormula a) b

  meets-sym : (a b : S) → ⟨ meets a b ⟩ → ⟨ meets b a ⟩
  meets-sym a b = PT.map (λ { (x , xa , xb) → x , xb , xa })

  neighborhood-countable : ChoiceSet → (a w : S) → ⟨ subsetΔ a X ⟩
    → ⟨ CB.injectable a w ⟩
    → ((x : S) → ⟨ x ∈ˢ X ⟩ → ⟨ CB.injectable (star x) w ⟩)
    → ⟨ CB.injectable (GS.product w w) w ⟩
    → ⟨ CB.injectable (neighborhood a) w ⟩
  neighborhood-countable choice a w sub countA countStars square =
    CU.countable-union choice (starFamily a) (neighborhood a) w
      members-sub cover countFamily members-count square
    where
    countFamily : ⟨ CB.injectable (starFamily a) w ⟩
    countFamily = FI.image-countable choice a (GS.power F) w starFormula
      (λ x d e hx hd he sd se → subst ⟨_⟩ (sym (paths d e))
        (star-unique d x (subst ⟨_⟩ (star-reading d x) sd)
          ∙ sym (star-unique e x (subst ⟨_⟩ (star-reading e x) se)))) countA

    members-sub : (d : S) → ⟨ d ∈ˢ starFamily a ⟩ → ⟨ subsetΔ d (neighborhood a) ⟩
    members-sub d hd b hb = PT.rec (snd (b ∈ˢ neighborhood a))
      (λ { (x , hx , sat) →
        let info = fst (subst ⟨_⟩ (star-reading d x) sat b) hb in
        subst ⟨_⟩ (sym (neighborhood-spec a b))
          (fst info , ∣ x , hx , snd info ∣₁) })
      (FI.image-out a (GS.power F) starFormula d hd)

    cover : (b : S) → ⟨ b ∈ˢ neighborhood a ⟩
      → ⟨ ⋁ S (λ d → (d ∈ˢ starFamily a) ⊓ (b ∈ˢ d)) ⟩
    cover b hb = PT.map
      (λ { (x , hx , xb) → star x , star-family-in a x hx ,
        subst ⟨_⟩ (sym (star-spec x b))
          (fst (subst ⟨_⟩ (neighborhood-spec a b) hb) , xb) })
      (snd (subst ⟨_⟩ (neighborhood-spec a b) hb))

    members-count : (d : S) → ⟨ d ∈ˢ starFamily a ⟩ → ⟨ CB.injectable d w ⟩
    members-count d hd = PT.rec (snd (CB.injectable d w))
      (λ { (x , hx , sat) → subst (λ t → ⟨ CB.injectable t w ⟩)
        (sym (star-unique d x (subst ⟨_⟩ (star-reading d x) sat)))
        (countStars x (sub x hx)) })
      (FI.image-out a (GS.power F) starFormula d hd)

