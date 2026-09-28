{-# OPTIONS --cubical --safe --guardedness #-}
module DeepFOLOmega where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma using (_×_)
open import Cubical.Data.Sum using (_⊎_; inl; inr)
open import Cubical.Data.Empty as Empty using (⊥)
open import Cubical.Data.FinData using (zero; suc)
open import Cubical.Data.Vec using ([]; _∷_)
open import FOL.Syntax
open import FOL.Manipulation.Renaming using (renameFo)
open import ModalTrees using (NN; unitNN; mapNN)
open import DeepNegativeFOL

infix 9 _⇔̇_
_⇔̇_ : ∀ {ℓ n} {K : Type ℓ} → Formula K n → Formula K n → Formula K n
φ ⇔̇ ψ = (φ ⇒̇ ψ) ∧̇ (ψ ⇒̇ φ)

module Construction {ℓ} (M : Atoms ℓ) where
  open Interpret M

  EmptyFormula : S → Formula S 0
  EmptyFormula e = ∀̇ (¬̇ (var zero ∈̇ con e))

  SingletonFormula : S → S → Formula S 0
  SingletonFormula e u = ∀̇ ((var zero ∈̇ con u) ⇔̇ (var zero ≐ con e))

  PairFormula : S → S → S → Formula S 0
  PairFormula e u o = ∀̇ ((var zero ∈̇ con o) ⇔̇ ((var zero ≐ con e) ∨̇ (var zero ≐ con u)))

  record ElementarySets : Type ℓ where
    field
      e u o : S
      empty-law : Sat (EmptyFormula e) []
      singleton-law : Sat (SingletonFormula e u) []
      pair-law : Sat (PairFormula e u o) []
      reflexive : ∀ x → Eq x x
      symmetric : ∀ x y → Eq x y → Eq y x
      member-left : ∀ x y a → Eq x y → Mem x a → Mem y a
      member-right : ∀ x a b → Eq a b → Mem x a → Mem x b
      extensional : ∀ a b → (∀ x → (Mem x a → Mem x b) × (Mem x b → Mem x a)) → Eq a b

  module Derived (sets : ElementarySets) (classical : FormulaLEM) where
    open ElementarySets sets

    OmegaFormula : Formula S 0
    OmegaFormula = ∀̇ ((var zero ∈̇ con o) ⇔̇
      (∀̇ ((var zero ∈̇ var (suc zero)) ⇒̇ (var zero ≐ con e))))

    omega-classifies-subsets-of-singleton : Sat OmegaFormula []
    omega-classifies-subsets-of-singleton p = forward , backward
      where
      forward : Mem p o → (x : S) → Mem x p → Eq x e
      forward po x xp = eq-stable x e (mapNN cases (pair-law p .fst po))
        where
        cases : Eq p e ⊎ Eq p u → Eq x e
        cases (inl pe) = Empty.rec (lower (empty-law x (member-right x p e pe xp)))
        cases (inr pu) = singleton-law x .fst (member-right x p u pu xp)

      backward : ((x : S) → Mem x p → Eq x e) → Mem p o
      backward bound = mem-stable p o (mapNN cases (classical (con e ∈̇ con p) []))
        where
        cases : Mem e p ⊎ Sat (¬̇ (con e ∈̇ con p)) [] → Mem p o
        cases (inl ep) = pair-law p .snd (unitNN (inr (extensional p u λ x →
          (λ xp → singleton-law x .snd (bound x xp)) ,
          (λ xu → member-left e x p (symmetric x e (singleton-law x .fst xu)) ep))))
        cases (inr nep) = pair-law p .snd (unitNN (inl (extensional p e λ x →
          (λ xp → Empty.rec (lower (nep (member-left x e p (bound x xp) xp)))) ,
          (λ xe → Empty.rec (lower (empty-law x xe))))))

    RepresentFormula : ∀ {n} → Formula S n → Formula S n
    RepresentFormula φ = ∃̇ ((var zero ∈̇ con o) ∧̇
      ((con e ∈̇ var zero) ⇔̇ renameFo suc φ))

    formula-resizing : ∀ {n} (φ : Formula S n) γ → Sat (RepresentFormula φ) γ
    formula-resizing φ γ = mapNN cases (classical φ γ)
      where
      cases : Sat φ γ ⊎ Sat (¬̇ φ) γ → _
      cases (inl p) = u , pair-law u .snd (unitNN (inr (reflexive u))) ,
        (λ _ → transport (sym (weaken-sat φ γ u)) p) ,
        (λ _ → singleton-law e .snd (reflexive e))
      cases (inr np) = e , pair-law e .snd (unitNN (inl (reflexive e))) ,
        (λ ee → Empty.rec (lower (empty-law e ee))) ,
        (λ q → Empty.rec (lower (np (transport (weaken-sat φ γ e) q))))

    representation-unique : ∀ {n} (φ : Formula S n) γ (p q : S)
      → Mem p o → Mem q o
      → ((Mem e p → Sat φ γ) × (Sat φ γ → Mem e p))
      → ((Mem e q → Sat φ γ) × (Sat φ γ → Mem e q))
      → Eq p q
    representation-unique φ γ p q po qo pf qf = extensional p q λ x →
      (λ xp → member-left e x q
        (symmetric x e (omega-classifies-subsets-of-singleton p .fst po x xp))
        (qf .snd (pf .fst (member-left x e p
          (omega-classifies-subsets-of-singleton p .fst po x xp) xp)))) ,
      (λ xq → member-left e x p
        (symmetric x e (omega-classifies-subsets-of-singleton q .fst qo x xq))
        (pf .snd (qf .fst (member-left x e q
          (omega-classifies-subsets-of-singleton q .fst qo x xq) xq))))
