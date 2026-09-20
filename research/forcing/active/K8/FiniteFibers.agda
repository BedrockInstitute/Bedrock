{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import FOL.ZFStructure using ( ZFStructure )
import OrdinaryProfile

module K8.FiniteFibers
  {ℓ} (𝒮 : ZFStructure (hPropAlgebra ℓ))
  (ext : OrdinaryProfile.Extensionality 𝒮)
  (paths : (x y : ZFStructure.S 𝒮)
    → ZFStructure._≈ˢ_ 𝒮 x y ≡ ((x ≡ y) , ZFStructure.isSetS 𝒮 x y))
  (pair : OrdinaryProfile.Pairing 𝒮)
  (un : OrdinaryProfile.Union 𝒮)
  (pow : OrdinaryProfile.PowerSet 𝒮)
  (sep : OrdinaryProfile.Separation 𝒮)
  (seed X Y : ZFStructure.S 𝒮)
  where

open import FOL.ZFStructure using ( module hPropStructure )

open import Base.Classical using ( LEM )
open import FOL.Syntax using ( Formula; var; con; _∈̇_; _⇒̇_; ∀̇∈; ∃̇∈ )
open import FOL.Semantics (hPropAlgebra ℓ) 𝒮 using ( module At )
open import CodedVocabulary 𝒮 using ( subsetΔ; refinesΔ; orderAtˢ )
open import K8.MapVocabulary 𝒮 using ( domainPred; domainAt )
open import K8.FiniteVocabulary 𝒮 using ( finiteIn )
open import K8.FiniteSubsets 𝒮 ext paths pow sep using ( finite-subset )
open import K8.FiniteAmbient 𝒮 ext paths pow sep using ( finite-change-ambient )
import K8.GroundSets
import K8.PartialMaps
import K8.FinitePower
import K8.FiniteProduct
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁ )

open TruthAlgebra (hPropAlgebra ℓ)
open hPropStructure 𝒮
open At S id using ( _⊨_ )

module GS = K8.GroundSets.Ground 𝒮 ext paths pair un pow sep seed
module PM = K8.PartialMaps.Maps 𝒮 ext paths pair un pow sep seed X Y
module FP = K8.FinitePower 𝒮 ext paths pair un pow sep seed PM.W
module Prod = K8.FiniteProduct 𝒮 ext paths pair un pow sep seed

domainBelow : S → S → Ω
domainBelow d p = ⋀ S (λ x → (x ∈ˢ X) ⇒ (domainPred Y p x ⇒ (x ∈ˢ d)))

fiberFormula : S → Formula S 1
fiberFormula d = ∀̇∈ (con X)
  ((∃̇∈ (con Y) (orderAtˢ (suc (suc zero)) (suc zero) zero))
    ⇒̇ (var zero ∈̇ con d))


fiber-reading : (d p : S) → ((p ∷ []) ⊨ fiberFormula d) ≡ domainBelow d p
fiber-reading d p = refl

opaque
  fiber : S → S
  fiber d = GS.separator PM.carrier (fiberFormula d)

  fiber-spec : (d p : S) → (p ∈ˢ fiber d) ≡ ((p ∈ˢ PM.carrier) ⊓ domainBelow d p)
  fiber-spec d p = GS.separator-spec PM.carrier (fiberFormula d) p
    ∙ cong ((p ∈ˢ PM.carrier) ⊓_) (fiber-reading d p)

fiber-bound : (d : S) → ⟨ subsetΔ (fiber d) (GS.power (GS.product d Y)) ⟩
fiber-bound d p hp = subst ⟨_⟩ (sym (GS.power-spec (GS.product d Y) p)) sub
  where
  data' : ⟨ (p ∈ˢ PM.carrier) ⊓ domainBelow d p ⟩
  data' = subst ⟨_⟩ (fiber-spec d p) hp

  pSub : ⟨ subsetΔ p PM.W ⟩
  pSub = fst (fst (subst ⟨_⟩ (PM.carrier-spec p) (fst data')))

  sub : ⟨ subsetΔ p (GS.product d Y) ⟩
  sub z hz = PT.rec (snd (z ∈ˢ GS.product d Y))
    (λ { (x , y , hx , hy , kp) → subst (λ t → ⟨ t ∈ˢ GS.product d Y ⟩)
      (sym (GS.ordered-unique z x y kp))
      (GS.product-in d Y x y (snd data' x hx ∣ y , hy , ∣ z , hz , kp ∣₁ ∣₁) hy) })
    (GS.product-out X Y z (pSub z hz))

fiber-in : (d p : S) → ⟨ p ∈ˢ PM.carrier ⟩
  → ⟨ subsetΔ (PM.domain p) d ⟩ → ⟨ p ∈ˢ fiber d ⟩
fiber-in d p hp sub = subst ⟨_⟩ (sym (fiber-spec d p))
  (hp , λ x hx ev → sub x (subst ⟨_⟩ (sym (PM.domain-spec p x)) (hx , ev)))

finite-fiber : LEM ℓ → (d : S) → ⟨ finiteIn X d ⟩ → ⟨ finiteIn Y Y ⟩
  → ⟨ finiteIn PM.carrier (fiber d) ⟩
finite-fiber lem d hd hy =
  finite-change-ambient (GS.power PM.W) PM.carrier (fiber d)
    (finite-subset lem (GS.power PM.W) (GS.power (GS.product d Y)) (fiber d)
      (FP.powerset-finite lem (GS.product d Y)
        (Prod.finite-product lem X Y d Y hd hy)) (fiber-bound d))
    (λ p hp → fst (subst ⟨_⟩ (fiber-spec d p) hp))

