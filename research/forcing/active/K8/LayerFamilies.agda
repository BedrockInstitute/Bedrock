{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import FOL.ZFStructure using ( ZFStructure )
import OrdinaryProfile

module K8.LayerFamilies
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
open import FOL.Syntax using ( Formula; var; con; _∈̇_; _∧̇_; ∀̇_ )
open import FOL.Semantics (hPropAlgebra ℓ) 𝒮 using ( module At )
open import CodedVocabulary 𝒮 using ( subsetΔ; sepAt; sepAt-reading )
open import K8.FiniteVocabulary 𝒮 using ( finiteIn )
open import OrdinaryProfile 𝒮 using ( ChoiceSet; iff )
open import GroundDescription 𝒮 ext paths using ( ext-path )
open import Cubical.Functions.Logic using ( ⇔toPath )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁ )
import CardinalBridge
import K8.GroundSets
import K8.OmegaPairing
import K8.FiniteEnumeration
import K8.FamilyImages
import K8.CountableZFC
import K8.Uncountability

open TruthAlgebra (hPropAlgebra ℓ)
open hPropStructure 𝒮
open At S id using ( _⊨_ )
module CB = CardinalBridge 𝒮
module GS = K8.GroundSets.Ground 𝒮 ext paths pair un pow sep seed
module OP = K8.OmegaPairing 𝒮 ext paths pair un pow sep coll find seed
module FE = K8.FiniteEnumeration 𝒮 ext paths pair un pow sep find seed
module FI = K8.FamilyImages 𝒮 ext paths pair un pow sep coll find seed
module UC = K8.Uncountability 𝒮 ext paths pair un pow sep coll find seed
open CB using ( _↔̇_ )

module Family (F : S) where

  boundFormula : S → Formula S 1
  boundFormula n = sepAt (OP.injectableAt zero (suc zero)) (n ∷ [])

  bound-reading : (n a : S) → ((a ∷ []) ⊨ boundFormula n) ≡ CB.injectable a n
  bound-reading n a = sepAt-reading (OP.injectableAt zero (suc zero)) (n ∷ []) a
    ∙ OP.injectableAt-reading zero (suc zero) (a ∷ n ∷ [])

  opaque
    layer : S → S
    layer n = GS.separator F (boundFormula n)

    layer-spec : (n a : S) → (a ∈ˢ layer n) ≡ ((a ∈ˢ F) ⊓ CB.injectable a n)
    layer-spec n a = GS.separator-spec F (boundFormula n) a
      ∙ cong ((a ∈ˢ F) ⊓_) (bound-reading n a)

  layer-sub : (n : S) → ⟨ subsetΔ (layer n) F ⟩
  layer-sub n a ha = subst ⟨_⟩ (layer-spec n a) ha .fst

  layer-bound : (n a : S) → ⟨ a ∈ˢ layer n ⟩ → ⟨ CB.injectable a n ⟩
  layer-bound n a ha = subst ⟨_⟩ (layer-spec n a) ha .snd

  Layer : S → S → Ω
  Layer d n = ⋀ S (λ a → iff (a ∈ˢ d) ((a ∈ˢ F) ⊓ CB.injectable a n))

  layerFormula : Formula S 2
  layerFormula = ∀̇ ((var zero ∈̇ var (suc zero)) ↔̇
    ((var zero ∈̇ con F) ∧̇ OP.injectableAt zero (suc (suc zero))))

  layer-reading : (d n : S) → ((d ∷ n ∷ []) ⊨ layerFormula) ≡ Layer d n
  layer-reading d n = cong (⋀ S) (funExt (λ a → cong (iff (a ∈ˢ d))
    (cong ((a ∈ˢ F) ⊓_) (OP.injectableAt-reading zero (suc (suc zero)) (a ∷ d ∷ n ∷ [])))))

  layer-witness : (n : S) → ⟨ Layer (layer n) n ⟩
  layer-witness n a = subst ⟨_⟩ (layer-spec n a) , subst ⟨_⟩ (sym (layer-spec n a))

  layer-unique : (d n : S) → ⟨ Layer d n ⟩ → d ≡ layer n
  layer-unique d n h = ext-path λ a → ⇔toPath (h a .fst) (h a .snd) ∙ sym (layer-spec n a)

  module AtOmega (lem : LEM ℓ) (choice : ChoiceSet) (w : S) (hw : ⟨ CB.isOmega w ⟩) where
    module CZ = K8.CountableZFC.AtOmega 𝒮 ext paths pair un pow sep coll find seed lem choice w hw

    layers : S
    layers = FI.imageIn w (GS.power F) layerFormula

    layers-in : (n : S) → ⟨ n ∈ˢ w ⟩ → ⟨ layer n ∈ˢ layers ⟩
    layers-in n hn = FI.image-in w (GS.power F) layerFormula n (layer n) hn
      (subst ⟨_⟩ (sym (GS.power-spec F (layer n))) (layer-sub n))
      (subst ⟨_⟩ (sym (layer-reading (layer n) n)) (layer-witness n))

    layers-countable : ⟨ CB.injectable layers w ⟩
    layers-countable = FI.image-countable choice w (GS.power F) w layerFormula
      (λ n d e hn hd he sd se → subst ⟨_⟩ (sym (paths d e))
        (layer-unique d n (subst ⟨_⟩ (layer-reading d n) sd)
          ∙ sym (layer-unique e n (subst ⟨_⟩ (layer-reading e n) se))))
      (OP.CO.injectable-refl sep coll pair w)

    uncountable-layer : (X : S)
      → ((a : S) → ⟨ a ∈ˢ F ⟩ → ⟨ finiteIn X a ⟩)
      → ⟨ UC.uncountable w F ⟩
      → ⟨ ⋁ S (λ n → (n ∈ˢ w) ⊓ UC.uncountable w (layer n)) ⟩
    uncountable-layer X each unF = PT.rec (snd target)
      (λ { (d , hd , unD) → PT.map (λ { (n , hn , sat) → n , hn ,
        subst (λ z → ⟨ UC.uncountable w z ⟩)
          (layer-unique d n (subst ⟨_⟩ (layer-reading d n) sat)) unD })
        (FI.image-out w (GS.power F) layerFormula d hd) })
      (CZ.uncountable-union-member layers F
        (λ d hd → subst ⟨_⟩ (GS.power-spec F d)
          (FI.image-sub w (GS.power F) layerFormula d hd))
        (λ a ha → PT.map (λ { (n , hn , bound) → layer n , layers-in n hn ,
          subst ⟨_⟩ (sym (layer-spec n a)) (ha , bound) })
          (FE.finite-size-bound lem w hw X a (each a ha))) layers-countable unF)
      where
      target : Ω
      target = ⋁ S (λ n → (n ∈ˢ w) ⊓ UC.uncountable w (layer n))
