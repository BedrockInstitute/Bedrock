{-# OPTIONS --cubical --safe --guardedness #-}
-- Orchestrator's own check of [LJ-1.299]'s cross-cutting find.
module ParseCheckOrch where
open import Base.Prelude
open import Cubical.Data.Sigma using ( _×_ ; Σ-syntax ; _,_ ; fst ; snd )

_↪_ : ∀ {ℓ} → Type ℓ → Type ℓ → Type ℓ
A ↪ B = Σ[ f ∈ (A → B) ] ((m n : A) → f m ≡ f n → m ≡ n)

asWritten : ∀ {ℓ} (A : Type ℓ) → Type ℓ
asWritten A = A × A ↪ A

-- MEASURED: the second component of the as-written form is a SELF-injection.
-- This typechecks only if `↪` binds tighter than `×`.
selfInj : ∀ {ℓ} (A : Type ℓ) → asWritten A → (A ↪ A)
selfInj A h = snd h

-- MEASURED: given any element, the as-written hypothesis is INHABITED,
-- because the identity is a self-injection. So it gates nothing.
inhabited : ∀ {ℓ} (A : Type ℓ) → A → asWritten A
inhabited A a = a , ((λ x → x) , λ m n p → p)
