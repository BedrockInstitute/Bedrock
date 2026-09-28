{-# OPTIONS --cubical --safe --guardedness #-}
module DeepNegativeFOL where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma using (_×_)
open import Cubical.Data.Sum using (_⊎_; inl; inr)
open import Cubical.Data.Empty as Empty using (⊥; ⊥*; isProp⊥*)
open import Cubical.Data.Nat using (ℕ; zero; suc)
open import Cubical.Data.FinData using (Fin; zero; suc)
open import Cubical.Data.Vec using (Vec; []; _∷_; lookup)
open import FOL.Syntax
open import FOL.Manipulation.Renaming using (renameTm; renameFo; liftρ)
open import ModalTrees using (NN; unitNN; mapNN; stableNN; propNN)

record Atoms (ℓ : Level) : Type (ℓ-suc ℓ) where
  field
    S : Type ℓ
    Eq Mem : S → S → Type ℓ
    eq-prop : ∀ x y → isProp (Eq x y)
    mem-prop : ∀ x y → isProp (Mem x y)
    eq-stable : ∀ x y → NN (Eq x y) → Eq x y
    mem-stable : ∀ x y → NN (Mem x y) → Mem x y

module Interpret {ℓ : Level} (M : Atoms ℓ) where
  open Atoms M public

  term : ∀ {n} → Term S n → Vec S n → S
  term (con x) γ = x
  term (var i) γ = lookup i γ

  Sat : ∀ {n} → Formula S n → Vec S n → Type ℓ
  Sat (t ∈̇ u) γ = Mem (term t γ) (term u γ)
  Sat (t ≐ u) γ = Eq (term t γ) (term u γ)
  Sat (φ ∧̇ ψ) γ = Sat φ γ × Sat ψ γ
  Sat (φ ∨̇ ψ) γ = NN (Sat φ γ ⊎ Sat ψ γ)
  Sat (φ ⇒̇ ψ) γ = Sat φ γ → Sat ψ γ
  Sat ⊥̇ γ = ⊥*
  Sat (∃̇ φ) γ = NN (Σ[ x ∈ S ] Sat φ (x ∷ γ))
  Sat (∀̇ φ) γ = (x : S) → Sat φ (x ∷ γ)
  Sat (∀̇∈ t φ) γ = (x : S) → Mem x (term t γ) → Sat φ (x ∷ γ)
  Sat (∃̇∈ t φ) γ = NN (Σ[ x ∈ S ] (Mem x (term t γ) × Sat φ (x ∷ γ)))

  sat-prop : ∀ {n} (φ : Formula S n) γ → isProp (Sat φ γ)
  sat-prop (t ∈̇ u) γ = mem-prop _ _
  sat-prop (t ≐ u) γ = eq-prop _ _
  sat-prop (φ ∧̇ ψ) γ = isProp× (sat-prop φ γ) (sat-prop ψ γ)
  sat-prop (φ ∨̇ ψ) γ = propNN
  sat-prop (φ ⇒̇ ψ) γ = isPropΠ λ _ → sat-prop ψ γ
  sat-prop ⊥̇ γ = isProp⊥*
  sat-prop (∃̇ φ) γ = propNN
  sat-prop (∀̇ φ) γ = isPropΠ λ x → sat-prop φ (x ∷ γ)
  sat-prop (∀̇∈ t φ) γ = isPropΠ2 λ x _ → sat-prop φ (x ∷ γ)
  sat-prop (∃̇∈ t φ) γ = propNN

  sat-stable : ∀ {n} (φ : Formula S n) γ → NN (Sat φ γ) → Sat φ γ
  sat-stable (t ∈̇ u) γ = mem-stable _ _
  sat-stable (t ≐ u) γ = eq-stable _ _
  sat-stable (φ ∧̇ ψ) γ v = sat-stable φ γ (mapNN fst v) , sat-stable ψ γ (mapNN snd v)
  sat-stable (φ ∨̇ ψ) γ = stableNN
  sat-stable (φ ⇒̇ ψ) γ v p = sat-stable ψ γ (mapNN (λ f → f p) v)
  sat-stable ⊥̇ γ v = lift (v lower)
  sat-stable (∃̇ φ) γ = stableNN
  sat-stable (∀̇ φ) γ v x = sat-stable φ (x ∷ γ) (mapNN (λ f → f x) v)
  sat-stable (∀̇∈ t φ) γ v x m = sat-stable φ (x ∷ γ) (mapNN (λ f → f x m) v)
  sat-stable (∃̇∈ t φ) γ = stableNN

  FormulaLEM : Type ℓ
  FormulaLEM = ∀ {n} (φ : Formula S n) γ → Sat (φ ∨̇ ¬̇ φ) γ

  negative-formula-lem : FormulaLEM
  negative-formula-lem φ γ k = k (inr (λ p → lift (k (inl p))))

  term-renaming : ∀ {n m} (ρ : Fin n → Fin m) (t : Term S n)
    (γ : Vec S n) (δ : Vec S m) → (∀ i → lookup (ρ i) δ ≡ lookup i γ)
    → term (renameTm ρ t) δ ≡ term t γ
  term-renaming ρ (con x) γ δ e = refl
  term-renaming ρ (var i) γ δ e = e i

  lifted-environment : ∀ {n m} (ρ : Fin n → Fin m)
    (γ : Vec S n) (δ : Vec S m) → (∀ i → lookup (ρ i) δ ≡ lookup i γ)
    → (x : S) (i : Fin (suc n)) → lookup (liftρ ρ i) (x ∷ δ) ≡ lookup i (x ∷ γ)
  lifted-environment ρ γ δ e x zero = refl
  lifted-environment ρ γ δ e x (suc i) = e i

  sat-renaming : ∀ {n m} (ρ : Fin n → Fin m) (φ : Formula S n)
    (γ : Vec S n) (δ : Vec S m) → (∀ i → lookup (ρ i) δ ≡ lookup i γ)
    → Sat (renameFo ρ φ) δ ≡ Sat φ γ
  sat-renaming ρ (t ∈̇ u) γ δ e = cong₂ Mem (term-renaming ρ t γ δ e) (term-renaming ρ u γ δ e)
  sat-renaming ρ (t ≐ u) γ δ e = cong₂ Eq (term-renaming ρ t γ δ e) (term-renaming ρ u γ δ e)
  sat-renaming ρ (φ ∧̇ ψ) γ δ e = cong₂ _×_ (sat-renaming ρ φ γ δ e) (sat-renaming ρ ψ γ δ e)
  sat-renaming ρ (φ ∨̇ ψ) γ δ e = cong₂ (λ P Q → NN (P ⊎ Q))
    (sat-renaming ρ φ γ δ e) (sat-renaming ρ ψ γ δ e)
  sat-renaming ρ (φ ⇒̇ ψ) γ δ e = cong₂ (λ P Q → P → Q)
    (sat-renaming ρ φ γ δ e) (sat-renaming ρ ψ γ δ e)
  sat-renaming ρ ⊥̇ γ δ e = refl
  sat-renaming ρ (∃̇ φ) γ δ e i = NN (Σ[ x ∈ S ]
    sat-renaming (liftρ ρ) φ (x ∷ γ) (x ∷ δ) (lifted-environment ρ γ δ e x) i)
  sat-renaming ρ (∀̇ φ) γ δ e i = (x : S) →
    sat-renaming (liftρ ρ) φ (x ∷ γ) (x ∷ δ) (lifted-environment ρ γ δ e x) i
  sat-renaming ρ (∀̇∈ t φ) γ δ e i = (x : S) → Mem x (term-renaming ρ t γ δ e i) →
    sat-renaming (liftρ ρ) φ (x ∷ γ) (x ∷ δ) (lifted-environment ρ γ δ e x) i
  sat-renaming ρ (∃̇∈ t φ) γ δ e i = NN (Σ[ x ∈ S ]
    (Mem x (term-renaming ρ t γ δ e i) ×
     sat-renaming (liftρ ρ) φ (x ∷ γ) (x ∷ δ) (lifted-environment ρ γ δ e x) i))

  weaken-sat : ∀ {n} (φ : Formula S n) (γ : Vec S n) (x : S)
    → Sat (renameFo suc φ) (x ∷ γ) ≡ Sat φ γ
  weaken-sat φ γ x = sat-renaming suc φ γ (x ∷ γ) (λ i → refl)
