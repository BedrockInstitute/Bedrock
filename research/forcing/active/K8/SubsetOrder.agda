{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import FOL.ZFStructure using ( ZFStructure )
import OrdinaryProfile

module K8.SubsetOrder
  {ℓ} (𝒮 : ZFStructure (hPropAlgebra ℓ))
  (ext : OrdinaryProfile.Extensionality 𝒮)
  (paths : (x y : ZFStructure.S 𝒮)
    → ZFStructure._≈ˢ_ 𝒮 x y ≡ ((x ≡ y) , ZFStructure.isSetS 𝒮 x y))
  (pair : OrdinaryProfile.Pairing 𝒮)
  (un : OrdinaryProfile.Union 𝒮)
  (pow : OrdinaryProfile.PowerSet 𝒮)
  (sep : OrdinaryProfile.Separation 𝒮)
  (seed : ZFStructure.S 𝒮)
  where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.ZFModel 𝒮 using ( _⊆ˢ_ )
open import FOL.Syntax using ( Formula; var; con; _∧̇_; ∃̇∈ )
open import FOL.Semantics (hPropAlgebra ℓ) 𝒮 using ( module At )
open import OrdinaryProfile 𝒮 using ( iff )
open import CodedVocabulary 𝒮 using
  ( isKPairΔ; refinesΔ; subsetΔ; subsetAtˢ; prAtˢ; sepAt; sepAt-reading )
import K8.GroundSets
import K7.CompletionTransfer
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁; ∣_∣₁ )
open import Cubical.Functions.Logic using ( ⇔toPath )

open TruthAlgebra (hPropAlgebra ℓ)
open hPropStructure 𝒮
open At S id using ( _⊨_ )

module GS = K8.GroundSets.Ground 𝒮 ext paths pair un pow sep seed
module CT = K7.CompletionTransfer 𝒮 ext paths

private
  orderFormula : (b : S) → Formula S 1
  orderFormula b = sepAt
    (∃̇∈ (con b) (∃̇∈ (con b)
      (prAtˢ (suc (suc zero)) (suc zero) zero
        ∧̇ subsetAtˢ (suc zero) zero))) []

opaque
  order : S → S
  order b = GS.separator (GS.product b b) (orderFormula b)

  order-spec : (b z : S)
    → (z ∈ˢ order b) ≡
      (⋁ S (λ u → (u ∈ˢ b) ⊓ ⋁ S (λ v →
        (v ∈ˢ b) ⊓ (isKPairΔ z u v ⊓ subsetΔ u v))))
  order-spec b z = GS.separator-spec (GS.product b b) (orderFormula b) z
    ∙ ⇔toPath
      (λ h → subst ⟨_⟩ (sepAt-reading
        (∃̇∈ (con b) (∃̇∈ (con b)
          (prAtˢ (suc (suc zero)) (suc zero) zero
            ∧̇ subsetAtˢ (suc zero) zero))) [] z) (h .snd))
      (λ h → productMember h , subst ⟨_⟩ (sym (sepAt-reading
        (∃̇∈ (con b) (∃̇∈ (con b)
          (prAtˢ (suc (suc zero)) (suc zero) zero
            ∧̇ subsetAtˢ (suc zero) zero))) [] z)) h)
    where
    productMember :
      ⟨ ⋁ S (λ u → (u ∈ˢ b) ⊓ ⋁ S (λ v →
        (v ∈ˢ b) ⊓ (isKPairΔ z u v ⊓ subsetΔ u v))) ⟩
      → ⟨ z ∈ˢ GS.product b b ⟩
    productMember = PT.rec (snd (z ∈ˢ GS.product b b)) λ
      { (u , hu , rest) → PT.rec (snd (z ∈ˢ GS.product b b))
          (λ { (v , hv , kp , _) → subst (λ t → ⟨ t ∈ˢ GS.product b b ⟩)
            (sym (GS.ordered-unique z u v kp)) (GS.product-in b b u v hu hv) }) rest }

order-in : (b u v : S) → ⟨ u ∈ˢ b ⟩ → ⟨ v ∈ˢ b ⟩
         → ⟨ subsetΔ u v ⟩ → ⟨ GS.ordered u v ∈ˢ order b ⟩
order-in b u v hu hv sub = subst ⟨_⟩ (sym (order-spec b (GS.ordered u v)))
  ∣ u , hu , ∣ v , hv , GS.ordered-witness u v , sub ∣₁ ∣₁

order-out : (b z : S) → ⟨ z ∈ˢ order b ⟩
  → ∥ Σ[ u ∈ S ] Σ[ v ∈ S ]
      (⟨ u ∈ˢ b ⟩ × ⟨ v ∈ˢ b ⟩ × ⟨ isKPairΔ z u v ⟩ × ⟨ subsetΔ u v ⟩) ∥₁
order-out b z h = PT.rec PT.squash₁
  (λ { (u , hu , rest) → PT.map
    (λ { (v , hv , kp , sub) → u , v , hu , hv , kp , sub }) rest })
  (subst ⟨_⟩ (order-spec b z) h)

order-typed : (b : S) →
  ⟨ ⋀ S (λ z → (z ∈ˢ order b) ⇒ ⋁ S (λ u → ⋁ S (λ v →
      (u ∈ˢ b) ⊓ ((v ∈ˢ b) ⊓ isKPairΔ z u v)))) ⟩
order-typed b z hz = PT.map
  (λ { (u , v , hu , hv , kp , _) → u , ∣ v , hu , hv , kp ∣₁ })
  (order-out b z hz)

refines-forward : (b u v : S) → ⟨ u ∈ˢ b ⟩ → ⟨ v ∈ˢ b ⟩
  → ⟨ refinesΔ (order b) u v ⟩ → ⟨ subsetΔ u v ⟩
refines-forward b u v hu hv h = PT.rec (snd (subsetΔ u v)) step h
  where
  step : Σ[ z ∈ S ] (⟨ z ∈ˢ order b ⟩ × ⟨ isKPairΔ z u v ⟩)
       → ⟨ subsetΔ u v ⟩
  step (z , hz , kp) = PT.rec (snd (subsetΔ u v))
    (λ { (u' , v' , hu' , hv' , kp' , sub) x hx →
      let c = GS.ordered-components z u v u' v' kp kp' in
      subst (λ t → ⟨ x ∈ˢ t ⟩) (sym (snd c))
        (sub x (subst (λ t → ⟨ x ∈ˢ t ⟩) (fst c) hx)) })
    (order-out b z hz)

refines-backward : (b u v : S) → ⟨ u ∈ˢ b ⟩ → ⟨ v ∈ˢ b ⟩
  → ⟨ subsetΔ u v ⟩ → ⟨ refinesΔ (order b) u v ⟩
refines-backward b u v hu hv sub =
  ∣ GS.ordered u v , order-in b u v hu hv sub , GS.ordered-witness u v ∣₁

subsetOrder : (b : S) → CT.OrderGraphFor b
subsetOrder b = order b , order-typed b , λ u v hu hv →
  refines-forward b u v hu hv , refines-backward b u v hu hv
