{-# OPTIONS --cubical --safe --guardedness #-}
module RelationalExponential where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Bool using (Bool)
open import Cubical.Data.Sigma using (_×_)
open import ModalTrees using (NN; unitNN; mapNN; propNN)
open import BooleanCompletion using (Holds)
open import RelationalTruth using (RelBoolMap; RelAgree; FunctionCover)

module _ {ℓ : Level} (A : Type ℓ) (cover : FunctionCover A) where
  E : Type ℓ
  E = FunctionCover.Index cover

  row : E → RelBoolMap A
  row = FunctionCover.family cover

  At : RelBoolMap A → A → Bool → Type ℓ
  At R a b = Holds (R a .fst b)

  agree-refl : (R : RelBoolMap A) → RelAgree A R R
  agree-refl R a b = (λ p → p) , (λ p → p)

  agree-sym : (R S : RelBoolMap A) → RelAgree A R S → RelAgree A S R
  agree-sym R S e a b = e a b .snd , e a b .fst

  agree-trans : (R S T : RelBoolMap A)
    → RelAgree A R S → RelAgree A S T → RelAgree A R T
  agree-trans R S T e d a b =
    (λ r → d a b .fst (e a b .fst r)) ,
    (λ t → e a b .snd (d a b .snd t))

  agree-prop : (R S : RelBoolMap A) → isProp (RelAgree A R S)
  agree-prop R S = isPropΠ2 λ a b → isProp×
    (isPropΠ (λ _ → S a .fst b .fst .snd))
    (isPropΠ (λ _ → R a .fst b .fst .snd))

  agree-stable : (R S : RelBoolMap A) → NN (RelAgree A R S) → RelAgree A R S
  agree-stable R S n a b =
    (λ r → S a .fst b .snd (mapNN (λ e → e a b .fst r) n)) ,
    (λ s → R a .fst b .snd (mapNN (λ e → e a b .snd s) n))

  Equal : E → E → Type ℓ
  Equal i j = RelAgree A (row i) (row j)

  record NamedMap {c : Level} (C : Type c) : Type (ℓ-max c (ℓ-suc ℓ)) where
    field
      graph : C → E → Type ℓ
      prop : (x : C) (i : E) → isProp (graph x i)
      stable : (x : C) (i : E) → NN (graph x i) → graph x i
      total : (x : C) → NN (Σ[ i ∈ E ] graph x i)
      unique : (x : C) (i j : E) → graph x i → graph x j → Equal i j
      respect : (x : C) (i j : E) → Equal i j → graph x i → graph x j

  module _ {c : Level} {C : Type c} (F : C → RelBoolMap A) where
    curry : NamedMap C
    NamedMap.graph curry x i = RelAgree A (F x) (row i)
    NamedMap.prop curry x i = agree-prop (F x) (row i)
    NamedMap.stable curry x i = agree-stable (F x) (row i)
    NamedMap.total curry x = FunctionCover.covers cover (F x)
    NamedMap.unique curry x i j ci cj = agree-trans (row i) (F x) (row j)
      (agree-sym (F x) (row i) ci) cj
    NamedMap.respect curry x i j e ci = agree-trans (F x) (row i) (row j) ci e

    Uncurry : NamedMap C → C → A → Bool → Type ℓ
    Uncurry K x a b = NN (Σ[ i ∈ E ] (NamedMap.graph K x i × At (row i) a b))

    Realizes : NamedMap C → Type (ℓ-max c ℓ)
    Realizes K = (x : C) (a : A) (b : Bool) →
      (Uncurry K x a b → At (F x) a b) × (At (F x) a b → Uncurry K x a b)

    beta : Realizes curry
    beta x a b =
      (λ n → F x a .fst b .snd
        (mapNN (λ { (i , agree , value) → agree a b .snd value }) n)) ,
      (λ value → mapNN
        (λ { (i , agree) → i , agree , agree a b .fst value })
        (FunctionCover.covers cover (F x)))

    other-to-curry : (K : NamedMap C) → Realizes K
      → (x : C) (i : E) → NamedMap.graph K x i → NamedMap.graph curry x i
    other-to-curry K realizes x i ki a b =
      (λ value → row i a .fst b .snd (mapNN
        (λ { (j , kj , vj) → NamedMap.unique K x j i kj ki a b .fst vj })
        (realizes x a b .snd value))) ,
      (λ vi → realizes x a b .fst (unitNN (i , ki , vi)))

    curry-to-other : (K : NamedMap C) → Realizes K
      → (x : C) (i : E) → NamedMap.graph curry x i → NamedMap.graph K x i
    curry-to-other K realizes x i ci = NamedMap.stable K x i (mapNN
      (λ { (j , kj) → NamedMap.respect K x j i
        (agree-trans (row j) (F x) (row i)
          (agree-sym (F x) (row j) (other-to-curry K realizes x j kj)) ci) kj })
      (NamedMap.total K x))

    eta : (K : NamedMap C) → Realizes K → (x : C) (i : E) →
      (NamedMap.graph K x i → NamedMap.graph curry x i) ×
      (NamedMap.graph curry x i → NamedMap.graph K x i)
    eta K realizes x i = other-to-curry K realizes x i , curry-to-other K realizes x i
