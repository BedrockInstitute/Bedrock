{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import FOL.ZFStructure using ( ZFStructure )

module K8.MapVocabulary {ℓ} (𝒮 : ZFStructure (hPropAlgebra ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax
  using ( Formula; var; _∈̇_; _≐_; _∧̇_; _⇒̇_; ∀̇∈; ∃̇∈ )
open import FOL.Semantics (hPropAlgebra ℓ) 𝒮 using ( module At; _^_ )
open import CodedVocabulary 𝒮 using ( refinesΔ; orderAtˢ; prAtˢ; isKPairΔ )
open import FOL.LevyHierarchy using ( Δ₀; checkΔ₀ )
open import Cubical.Data.Unit using ( tt )

open TruthAlgebra (hPropAlgebra ℓ)
open hPropStructure 𝒮
open At S id using ( _⊨_ )

functional : S → S → S → Ω
functional X Y f =
  ⋀ S (λ x → (x ∈ˢ X) ⇒
  ⋀ S (λ y → (y ∈ˢ Y) ⇒
  ⋀ S (λ z → (z ∈ˢ Y) ⇒
    ((refinesΔ f x y) ⊓ (refinesΔ f x z)) ⇒ (y ≈ˢ z))))

agrees : S → S → S → S → Ω
agrees X Y f g =
  ⋀ S (λ x → (x ∈ˢ X) ⇒
  ⋀ S (λ y → (y ∈ˢ Y) ⇒
  ⋀ S (λ z → (z ∈ˢ Y) ⇒
    ((refinesΔ f x y) ⊓ (refinesΔ g x z)) ⇒ (y ≈ˢ z))))

domainPred : S → S → S → Ω
domainPred Y f x = ⋁ S (λ y → (y ∈ˢ Y) ⊓ refinesΔ f x y)

functionalAt : ∀ {n} → Fin n → Fin n → Fin n → Formula S n
functionalAt X Y f =
  ∀̇∈ (var X) (∀̇∈ (var (suc Y)) (∀̇∈ (var (suc (suc Y)))
    ((orderAtˢ (suc (suc (suc f))) (suc (suc zero)) (suc zero)
      ∧̇ orderAtˢ (suc (suc (suc f))) (suc (suc zero)) zero)
      ⇒̇ (var (suc zero) ≐ var zero))))

domainAt : ∀ {n} → Fin n → Fin n → Fin n → Formula S n
domainAt Y f x = ∃̇∈ (var Y) (orderAtˢ (suc f) (suc x) zero)

functional-reading : ∀ {n} (X Y f : Fin n) (γ : S ^ n)
  → (γ ⊨ functionalAt X Y f)
    ≡ functional (lookup X γ) (lookup Y γ) (lookup f γ)
functional-reading X Y f γ = refl

domain-reading : ∀ {n} (Y f x : Fin n) (γ : S ^ n)
  → (γ ⊨ domainAt Y f x)
    ≡ domainPred (lookup Y γ) (lookup f γ) (lookup x γ)
domain-reading Y f x γ = refl

functional-bounded : ∀ {n} (X Y f : Fin n) → Δ₀ (functionalAt X Y f)
functional-bounded X Y f = checkΔ₀ (functionalAt X Y f) tt

domain-bounded : ∀ {n} (Y f x : Fin n) → Δ₀ (domainAt Y f x)
domain-bounded Y f x = checkΔ₀ (domainAt Y f x) tt
