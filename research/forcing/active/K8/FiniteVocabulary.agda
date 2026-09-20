{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import FOL.ZFStructure using ( ZFStructure )

module K8.FiniteVocabulary {ℓ} (𝒮 : ZFStructure (hPropAlgebra ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax
  using ( Formula; var; _∈̇_; _≐_; _∧̇_; _∨̇_; _⇒̇_; ⊥̇; ∀̇_; ∀̇∈ )
open import FOL.Semantics (hPropAlgebra ℓ) 𝒮 using ( module At; _^_ )
open import CodedVocabulary 𝒮 using ( subsetΔ; subsetAtˢ )
open import FOL.LevyHierarchy using ( Δ₀; checkΔ₀ )
open import Cubical.Data.Unit using ( tt )
open import CardinalBridge 𝒮 using ( _↔̇_ )
open import OrdinaryProfile 𝒮 using ( iff )

open TruthAlgebra (hPropAlgebra ℓ)
open hPropStructure 𝒮
open At S id using ( _⊨_ )

emptyPred : S → Ω
emptyPred e = ⋀ S (λ z → (z ∈ˢ e) ⇒ ⊥)

adjoinPred : S → S → S → Ω
adjoinPred b a x = (x ∈ˢ b) ⊓ (subsetΔ a b
  ⊓ (⋀ S (λ z → (z ∈ˢ b) ⇒ ((z ∈ˢ a) ⊔ (z ≈ˢ x)))))

closedPred : S → S → Ω
closedPred F X =
    (⋀ S (λ e → emptyPred e ⇒ (e ∈ˢ F)))
  ⊓ (⋀ S (λ a → (a ∈ˢ F) ⇒
       ⋀ S (λ x → (x ∈ˢ X) ⇒
       ⋀ S (λ b → adjoinPred b a x ⇒ (b ∈ˢ F)))))

finiteIn : S → S → Ω
finiteIn X a = subsetΔ a X ⊓
  (⋀ S (λ F → closedPred F X ⇒ (a ∈ˢ F)))

emptyAt : ∀ {n} → Fin n → Formula S n
emptyAt e = ∀̇∈ (var e) ⊥̇

adjoinAt : ∀ {n} → Fin n → Fin n → Fin n → Formula S n
adjoinAt b a x = (var x ∈̇ var b) ∧̇ (subsetAtˢ a b
  ∧̇ (∀̇∈ (var b)
       ((var zero ∈̇ var (suc a)) ∨̇ (var zero ≐ var (suc x)))))

closedAt : ∀ {n} → Fin n → Fin n → Formula S n
closedAt F X =
    (∀̇ (emptyAt zero ⇒̇ (var zero ∈̇ var (suc F))))
  ∧̇ (∀̇∈ (var F) (∀̇∈ (var (suc X))
       (∀̇ (adjoinAt zero (suc (suc zero)) (suc zero)
         ⇒̇ (var zero ∈̇ var (suc (suc (suc F))))))))

finiteAt : ∀ {n} → Fin n → Fin n → Formula S n
finiteAt X a = subsetAtˢ a X ∧̇
  (∀̇ (closedAt zero (suc X) ⇒̇ (var (suc a) ∈̇ var zero)))

empty-reading : ∀ {n} (e : Fin n) (γ : S ^ n)
  → (γ ⊨ emptyAt e) ≡ emptyPred (lookup e γ)
empty-reading e γ = refl

adjoin-reading : ∀ {n} (b a x : Fin n) (γ : S ^ n)
  → (γ ⊨ adjoinAt b a x)
    ≡ adjoinPred (lookup b γ) (lookup a γ) (lookup x γ)
adjoin-reading b a x γ = refl

closed-reading : ∀ {n} (F X : Fin n) (γ : S ^ n)
  → (γ ⊨ closedAt F X) ≡ closedPred (lookup F γ) (lookup X γ)
closed-reading F X γ = refl

finite-reading : ∀ {n} (X a : Fin n) (γ : S ^ n)
  → (γ ⊨ finiteAt X a) ≡ finiteIn (lookup X γ) (lookup a γ)
finite-reading X a γ = refl

empty-bounded : ∀ {n} (e : Fin n) → Δ₀ (emptyAt e)
empty-bounded e = checkΔ₀ (emptyAt e) tt

adjoin-bounded : ∀ {n} (b a x : Fin n) → Δ₀ (adjoinAt b a x)
adjoin-bounded b a x = checkΔ₀ (adjoinAt b a x) tt

unionPred : S → S → S → Ω
unionPred u a b = ⋀ S (λ z → iff (z ∈ˢ u) ((z ∈ˢ a) ⊔ (z ∈ˢ b)))

unionAt : ∀ {n} → Fin n → Fin n → Fin n → Formula S n
unionAt u a b = ∀̇ ((var zero ∈̇ var (suc u)) ↔̇
  ((var zero ∈̇ var (suc a)) ∨̇ (var zero ∈̇ var (suc b))))

union-reading : ∀ {n} (u a b : Fin n) (γ : S ^ n)
  → (γ ⊨ unionAt u a b)
    ≡ unionPred (lookup u γ) (lookup a γ) (lookup b γ)
union-reading u a b γ = refl
