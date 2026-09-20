{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import FOL.ZFStructure using ( ZFStructure )
import NameKernel
import OrdinaryProfile
import Cubical.HITs.PropositionalTruncation as PT
import K8.GroundSets
import K9.BooleanAtomic

module K10.CohenBooleanInjCheck
  {ℓ} (𝒮 : ZFStructure (hPropAlgebra ℓ))
  (families : NameKernel.Families 𝒮)
  (accessible : NameKernel.Accessibility 𝒮)
  (images : NameKernel.MemberImage 𝒮)
  (pow : OrdinaryProfile.PowerSet 𝒮)
  (κ w : ZFStructure.S 𝒮)
  (lem : LEM ℓ)
  where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula ; con ; ∃̇∈ )
open import FOL.Semantics (hPropAlgebra ℓ) 𝒮 using ( module At )
open import CodedVocabulary 𝒮 using ( prAtˢ ; isKPairΔ )
open import Cubical.Functions.Logic using ( ⇔toPath )
open PT using ( ∣_∣₁ ; ∥_∥₁ )

open TruthAlgebra (hPropAlgebra ℓ)
open hPropStructure 𝒮
open At S id using ( _⊨_ )

module BAT = K9.BooleanAtomic 𝒮 families accessible images pow κ w lem
  using ( module NG ; module Checked )
open BAT.NG using ( extensional ; ≈ˢ-paths ; hasPair ; hasUnion ; hasSeparation )
module GS = K8.GroundSets.Ground 𝒮 extensional ≈ˢ-paths
  hasPair hasUnion pow hasSeparation κ
module Img = NameKernel.MemberImage images
open BAT.Checked public using ( check ; check-name )
open BAT.NG using ( module C )

product : S → S → S
product = GS.product

product-in : (a b x y : S) → ⟨ x ∈ˢ a ⟩ → ⟨ y ∈ˢ b ⟩
           → ⟨ GS.ordered x y ∈ˢ product a b ⟩
product-in = GS.product-in

product-out : (a b p : S) → ⟨ p ∈ˢ product a b ⟩
            → ∥ Σ[ x ∈ S ] Σ[ y ∈ S ]
                 (⟨ x ∈ˢ a ⟩ × ⟨ y ∈ˢ b ⟩ × ⟨ isKPairΔ p x y ⟩) ∥₁
product-out = GS.product-out

ordered = GS.ordered
ordered-witness = GS.ordered-witness
ordered-components = GS.ordered-components
ordered-unique = GS.ordered-unique
carrier = C.carrier
order = C.order
separator = GS.separator
separator-spec = GS.separator-spec

checkGraph : S → S
checkGraph β = Img.image β
  (λ ξ → GS.ordered (fst ξ) (check (fst ξ)))

checks : S → Formula S 2
checks β = ∃̇∈ (con (checkGraph β)) (prAtˢ zero (suc (suc zero)) (suc zero))

checks-reading : (β u ξ : S) → ⟨ ξ ∈ˢ β ⟩
  → ((u ∷ ξ ∷ []) ⊨ checks β) ≡ (u ≈ˢ check ξ)
checks-reading β u ξ hξ = ⇔toPath forward backward
  where
  graph-spec : (z : S) → (z ∈ˢ checkGraph β)
    ≡ ⋁ S (λ x → ⋁ ⟨ x ∈ˢ β ⟩ (λ _ → z ≈ˢ GS.ordered x (check x)))
  graph-spec = Img.image-spec β
    (λ x → GS.ordered (fst x) (check (fst x)))

  forward : ⟨ (u ∷ ξ ∷ []) ⊨ checks β ⟩ → ⟨ u ≈ˢ check ξ ⟩
  forward = PT.rec (snd (u ≈ˢ check ξ))
    λ { (z , hz , q) → PT.rec (snd (u ≈ˢ check ξ))
      (λ { (x , hx) → PT.rec (snd (u ≈ˢ check ξ))
        (λ { (_ , e) → conclude z x q e }) hx })
      (subst ⟨_⟩ (graph-spec z) hz) }
    where
    conclude : (z x : S) → ⟨ isKPairΔ z ξ u ⟩
      → ⟨ z ≈ˢ GS.ordered x (check x) ⟩
      → ⟨ u ≈ˢ check ξ ⟩
    conclude z x q e = subst ⟨_⟩
      (sym (≈ˢ-paths u (check ξ)))
      (snd components ∙ cong check (sym (fst components)))
      where
      components : (ξ ≡ x) × (u ≡ check x)
      components = GS.ordered-components z ξ u x (check x) q
        (subst (λ t → ⟨ isKPairΔ t x (check x) ⟩)
          (sym (subst ⟨_⟩ (≈ˢ-paths z (GS.ordered x (check x))) e))
          (GS.ordered-witness x (check x)))

  backward : ⟨ u ≈ˢ check ξ ⟩ → ⟨ (u ∷ ξ ∷ []) ⊨ checks β ⟩
  backward e = ∣ z , member , pair ∣₁
    where
    z : S
    z = GS.ordered ξ (check ξ)
    member : ⟨ z ∈ˢ checkGraph β ⟩
    member = subst ⟨_⟩ (sym (graph-spec z))
      ∣ ξ , ∣ hξ , subst ⟨_⟩ (sym (≈ˢ-paths z z)) refl ∣₁ ∣₁
    pair : ⟨ isKPairΔ z ξ u ⟩
    pair = subst (λ t → ⟨ isKPairΔ z ξ t ⟩)
      (sym (subst ⟨_⟩ (≈ˢ-paths u (check ξ)) e))
      (GS.ordered-witness ξ (check ξ))
