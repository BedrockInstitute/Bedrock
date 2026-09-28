{-# OPTIONS --cubical --safe --guardedness #-}
module Boundary where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Structure
open import Cubical.Data.Empty as Empty using (⊥; isProp⊥)
open import Cubical.Data.Unit using (Unit; tt; isPropUnit)
open import Cubical.Relation.Nullary using (¬_; Dec; yes; no)
open import Cubical.HITs.Nullification.Base using (Null)

SmallRepresentative : ∀ {ℓ} → hProp ℓ → Type (ℓ-max ℓ (ℓ-suc ℓ-zero))
SmallRepresentative P = Σ[ Q ∈ hProp ℓ-zero ] (⟨ P ⟩ ≃ ⟨ Q ⟩)

decided-small : ∀ {ℓ} (P : hProp ℓ) → Dec ⟨ P ⟩ → SmallRepresentative P
decided-small P (yes p) = (Unit , isPropUnit) ,
  propBiimpl→Equiv (P .snd) isPropUnit (λ _ → tt) (λ _ → p)
decided-small P (no np) = (⊥ , isProp⊥) ,
  propBiimpl→Equiv (P .snd) isProp⊥ np Empty.rec

pointwise-LEM : ∀ {ℓ} (A : Type ℓ) → ¬ ¬ Dec A
pointwise-LEM A k = k (no (λ a → k (yes a)))

pointwise-resizing : ∀ {ℓ} (P : hProp ℓ) → ¬ ¬ SmallRepresentative P
pointwise-resizing P k = pointwise-LEM ⟨ P ⟩ (λ d → k (decided-small P d))

Stable : ∀ {ℓ} → Type ℓ → Type ℓ
Stable A = ¬ ¬ A → A

decision-stability-implies-LEM : ∀ {ℓ}
  → ((P : hProp ℓ) → Stable (Dec ⟨ P ⟩))
  → (P : hProp ℓ) → Dec ⟨ P ⟩
decision-stability-implies-LEM stable P = stable P (pointwise-LEM ⟨ P ⟩)

representative-stability-implies-resizing : ∀ {ℓ}
  → ((P : hProp ℓ) → Stable (SmallRepresentative P))
  → (P : hProp ℓ) → SmallRepresentative P
representative-stability-implies-resizing stable P = stable P (pointwise-resizing P)

Dense : (ℓ : Level) → Type (ℓ-suc ℓ)
Dense ℓ = Σ[ P ∈ hProp ℓ ] (¬ ¬ ⟨ P ⟩)

DenseDomain : ∀ {ℓ} → Dense ℓ → Type ℓ
DenseDomain d = ⟨ d .fst ⟩

LargeSheaf : ∀ {ℓ} → Type ℓ → Type (ℓ-suc ℓ)
LargeSheaf {ℓ} X = Null (DenseDomain {ℓ}) X
