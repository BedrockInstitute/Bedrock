{-# OPTIONS --cubical --safe --guardedness #-}
module CoverObstructions where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Empty using (⊥; isProp⊥)
open import Cubical.Data.Empty as Empty using ()
open import Cubical.Data.Unit using (Unit; tt)
open import Cubical.Data.Nat using (ℕ; zero; suc)
open import Cubical.Data.Sigma using (_×_)
open import Cubical.Relation.Nullary using (¬_)
import Cubical.HITs.SetQuotients as Q
open import ModalTrees
open import DensePower

module _ {ℓ : Level} {A : Type ℓ} (f : A → Tree ℓ) where
  open Predicate

  Covers : ∀ {ℓ'} {I : Type ℓ'} → (I → Predicate f) → Type (ℓ-max (ℓ-suc ℓ) ℓ')
  Covers {I = I} R = (P : Predicate f) → NN (Σ[ i ∈ I ] Agree f P (R i))

  quotient-representative : ∀ {ℓ' ℓ''} {I : Type ℓ'} {E : I → I → Type ℓ''}
    → (j : I Q./ E) → NN (Σ[ i ∈ I ] Q.[ i ] ≡ j)
  quotient-representative = Q.elimProp (λ _ → propNN) (λ i → unitNN (i , refl))

  quotient-cannot-add-coverage : ∀ {ℓ' ℓ''} {I : Type ℓ'} {E : I → I → Type ℓ''}
    → (R : I Q./ E → Predicate f) → Covers R → Covers (λ i → R Q.[ i ])
  quotient-cannot-add-coverage R cover P = bindNN (cover P) λ { (j , agree) →
    mapNN (λ { (i , e) → i , subst (λ z → Agree f P (R z)) (sym e) agree })
      (quotient-representative j) }

  quotient-preserves-coverage : ∀ {ℓ' ℓ''} {I : Type ℓ'} {E : I → I → Type ℓ''}
    → (R : I Q./ E → Predicate f) → Covers (λ i → R Q.[ i ]) → Covers R
  quotient-preserves-coverage R cover P = mapNN
    (λ { (i , agree) → Q.[ i ] , agree }) (cover P)

  module _ (injective : (i j : A) → Eq (f i) (f j) → i ≡ j) where
    diagonal : (A → Predicate f) → Predicate f
    holds (diagonal R) i = ¬ holds (R i) i
    prop (diagonal R) i = isPropΠ (λ _ → isProp⊥)
    stable (diagonal R) i n p = n (λ k → k p)
    saturated (diagonal R) i j e = subst (λ k → ¬ holds (R k) k) (injective i j e)

    diagonal-differs : (R : A → Predicate f) (i : A) → ¬ Agree f (diagonal R) (R i)
    diagonal-differs R i agree = contradiction (agree i .fst contradiction)
      where
      contradiction : ¬ holds (R i) i
      contradiction p = agree i .snd p p

    no-self-indexed-cover : (R : A → Predicate f) → ¬ Covers R
    no-self-indexed-cover R cover = cover (diagonal R)
      (λ { (i , agree) → diagonal-differs R i agree })

    no-quotient-self-indexed-cover : ∀ {ℓ'} {E : A → A → Type ℓ'}
      → (R : A Q./ E → Predicate f) → ¬ Covers R
    no-quotient-self-indexed-cover R cover =
      no-self-indexed-cover (λ i → R Q.[ i ]) (quotient-cannot-add-coverage R cover)

chain : ℕ → Tree ℓ-zero
chain zero = sup ⊥ Empty.rec
chain (suc n) = sup Unit (λ _ → chain n)

chain-injective : (m n : ℕ) → Eq (chain m) (chain n) → m ≡ n
chain-injective zero zero e = refl
chain-injective zero (suc n) e = Empty.rec (e .snd tt (λ z → z .fst))
chain-injective (suc m) zero e = Empty.rec (e .fst tt (λ z → z .fst))
chain-injective (suc m) (suc n) e = cong suc (chain-injective m n
  (eq-stable (chain m) (chain n) (mapNN snd (e .fst tt))))

infiniteTree : Tree ℓ-zero
infiniteTree = sup ℕ chain

no-countable-cover : (R : ℕ → Predicate chain) → ¬ Covers chain R
no-countable-cover = no-self-indexed-cover chain chain-injective

no-quotient-countable-cover : ∀ {ℓ} {E : ℕ → ℕ → Type ℓ}
  → (R : ℕ Q./ E → Predicate chain) → ¬ Covers chain R
no-quotient-countable-cover = no-quotient-self-indexed-cover chain chain-injective
