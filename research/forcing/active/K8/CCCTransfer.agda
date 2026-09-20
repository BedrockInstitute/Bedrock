{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import FOL.ZFStructure using ( ZFStructure )
import OrdinaryProfile

module K8.CCCTransfer
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
open import FOL.Syntax using ( Formula; var; con; ∃̇∈ )
open import FOL.Semantics (hPropAlgebra ℓ) 𝒮 using ( module At )
open import CodedVocabulary 𝒮 using ( subsetΔ; refinesΔ; compatibleΔ )
open import OrdinaryProfile 𝒮 using ( ChoiceSet )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁ )
import K7.CardinalOrder
import K7.ChainConditions
import K7.CompletionTransfer
import K8.CountableUnion
import K8.GroundSets

open TruthAlgebra (hPropAlgebra ℓ)
open hPropStructure 𝒮
open At S id using ( _⊨_ )

module GS = K8.GroundSets.Ground 𝒮 ext paths pair un pow sep seed
module CU = K8.CountableUnion 𝒮 ext paths pair un pow sep coll find seed
module CH = K7.ChainConditions 𝒮 ext paths
module CT = K7.CompletionTransfer 𝒮 ext paths
module CO = K7.CardinalOrder.Order 𝒮 ext
  (λ x y z e → cong (_∈ˢ z) (GS.≈→≡ e))
  (λ x y z e → cong (x ∈ˢ_) (GS.≈→≡ e))

path→≈ : {x y : S} → x ≡ y → ⟨ x ≈ˢ y ⟩
path→≈ {x} {y} e = subst ⟨_⟩ (sym (paths x y)) e

module Transfer
  (choice : ChoiceSet)
  (carrier order B⁺set order⁺ w : S)
  (img : S → S)
  (img-in : (p : S) → ⟨ p ∈ˢ carrier ⟩ → ⟨ img p ∈ˢ B⁺set ⟩)
  (img-mono : (r p : S) → ⟨ r ∈ˢ carrier ⟩ → ⟨ p ∈ˢ carrier ⟩
    → ⟨ refinesΔ order r p ⟩ → ⟨ refinesΔ order⁺ (img r) (img p) ⟩)
  (below : S → S)
  (below-sub : (b p : S) → ⟨ p ∈ˢ below b ⟩ → ⟨ p ∈ˢ carrier ⟩)
  (below-refines : (b p : S) → ⟨ p ∈ˢ below b ⟩
    → ⟨ refinesΔ order⁺ (img p) b ⟩)
  (refines⁺-trans : (u v z : S) → ⟨ refinesΔ order⁺ u v ⟩
    → ⟨ refinesΔ order⁺ v z ⟩ → ⟨ refinesΔ order⁺ u z ⟩)
  (belowFo : Formula S 2)
  (below-reading : (u p : S) → ((p ∷ u ∷ []) ⊨ belowFo) ≡ (p ∈ˢ below u))
  (dense : (u : S) → ⟨ u ∈ˢ B⁺set ⟩
    → ⟨ ⋁ S (λ p → (p ∈ˢ carrier) ⊓ ((p ∷ u ∷ []) ⊨ belowFo)) ⟩)
  where

  module ST = CT.Structural carrier order B⁺set order⁺ img img-in img-mono
    below below-sub below-refines refines⁺-trans
    CH.antichainΔ CH.antichain-use CH.antichain-intro

  select-total : (u : S) → ⟨ u ∈ˢ B⁺set ⟩
    → ⟨ ⋁ S (λ p → (p ∈ˢ carrier) ⊓ ((p ∷ u ∷ []) ⊨ belowFo)) ⟩
  select-total = dense

  ccc-transfer : ⟨ CH.CCC₂ᴵ carrier order w ⟩ → ⟨ CH.CCC₂ᴵ B⁺set order⁺ w ⟩
  ccc-transfer ccc = PT.rec (snd (CH.CCC₂ᴵ B⁺set order⁺ w)) build
    (CU.bounded-choice choice B⁺set carrier belowFo select-total)
    where
    build : Σ[ g ∈ S ] ⟨ CU.Selection B⁺set carrier belowFo g ⟩
      → ⟨ CH.CCC₂ᴵ B⁺set order⁺ w ⟩
    build (g , selected) = CH.ccc-intro B⁺set order⁺ w step
      where
      selRel : S → S → Ω
      selRel u p = CU.Ref g u p

      sel-below : (u p : S) → ⟨ selRel u p ⟩ → ⟨ p ∈ˢ below u ⟩
      sel-below u p h = subst ⟨_⟩ (below-reading u p)
        (CU.selection-value B⁺set carrier belowFo g u p selected h .snd .snd)

      sel-unique : (u p q : S) → ⟨ selRel u p ⟩ → ⟨ selRel u q ⟩ → p ≡ q
      sel-unique u p q hp hq = GS.≈→≡ (CU.ref-single g u p q (selected .fst) hp hq)

      module WS = ST.WithSelection selRel sel-below sel-unique

      imageFormula : S → Formula S 1
      imageFormula d = ∃̇∈ (con d)
        (CU.refAt (con g) (var zero) (var (suc zero)))

      image : S → S
      image d = GS.separator carrier (imageFormula d)

      image-spec : (d y : S) → (y ∈ˢ image d)
        ≡ ((y ∈ˢ carrier) ⊓ ⋁ S (λ u → (u ∈ˢ d) ⊓ selRel u y))
      image-spec d y = GS.separator-spec carrier (imageFormula d) y
        ∙ cong ((y ∈ˢ carrier) ⊓_)
          (cong (⋁ S) (funExt (λ u → cong ((u ∈ˢ d) ⊓_)
            (CU.refAt-reading (con g) (var zero) (var (suc zero)) (u ∷ y ∷ [])))))

      image-sub : (d : S) → ⟨ subsetΔ (image d) carrier ⟩
      image-sub d y hy = subst ⟨_⟩ (image-spec d y) hy .fst

      image-in : (d u y : S) → ⟨ u ∈ˢ d ⟩ → ⟨ selRel u y ⟩
        → ⟨ y ∈ˢ image d ⟩
      image-in d u y hu hsel = subst ⟨_⟩ (sym (image-spec d y))
        (WS.sel-cond u y hsel , ∣ u , hu , hsel ∣₁)

      image-out : (d y : S) → ⟨ y ∈ˢ image d ⟩
        → ⟨ ⋁ S (λ u → (u ∈ˢ d) ⊓ selRel u y) ⟩
      image-out d y hy = subst ⟨_⟩ (image-spec d y) hy .snd

      refFo : Formula S 2
      refFo = CU.refAt (con g) (var (suc zero)) (var zero)

      ref-reading : (u p : S) → ((p ∷ u ∷ []) ⊨ refFo) ≡ selRel u p
      ref-reading u p = CU.refAt-reading (con g) (var (suc zero)) (var zero)
        (p ∷ u ∷ [])

      step : (d : S) → ⟨ subsetΔ d B⁺set ⟩
        → ⟨ CH.antichainΔ B⁺set order⁺ d ⟩ → ⟨ CH.CB.injectable d w ⟩
      step d dsub ac = CO.injectable-trans sep coll pair d (image d) w
        selectedInjection imageCount
        where
        selectedAntichain : ⟨ CH.antichainΔ carrier order (image d) ⟩
        selectedAntichain = WS.sel-antichain d ac dsub (image d) (image-out d)

        imageCount : ⟨ CH.CB.injectable (image d) w ⟩
        imageCount = CH.ccc-use carrier order w (image d) ccc
          (image-sub d) selectedAntichain

        total : (u : S) → ⟨ u ∈ˢ d ⟩
          → ⟨ ⋁ S (λ p → (p ∈ˢ image d) ⊓ ((p ∷ u ∷ []) ⊨ refFo)) ⟩
        total u hu = PT.map
          (λ { (p , hp) → p , image-in d u p hu hp , subst ⟨_⟩ (sym (ref-reading u p)) hp })
          (selected .snd .fst u (dsub u hu))

        unique : (u v p : S) → ⟨ u ∈ˢ d ⟩ → ⟨ v ∈ˢ d ⟩
          → ⟨ p ∈ˢ image d ⟩ → ⟨ (p ∷ u ∷ []) ⊨ refFo ⟩
          → ⟨ (p ∷ v ∷ []) ⊨ refFo ⟩ → ⟨ u ≈ˢ v ⟩
        unique u v p hu hv hp su sv = path→≈
          (WS.sel-injective d u v p ac (dsub u hu) hu (dsub v hv) hv
            (subst ⟨_⟩ (ref-reading u p) su)
            (subst ⟨_⟩ (ref-reading v p) sv))

        selectedInjection : ⟨ CH.CB.injectable d (image d) ⟩
        selectedInjection = CU.choice-injection choice d (image d) refFo total unique
