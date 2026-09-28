{-# OPTIONS --cubical --safe --guardedness #-}
module FunctionObjectBoundary where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Bool using (Bool)
open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.Sigma using (_×_)
open import Cubical.Relation.Nullary using (¬_)
open import ModalTrees using (NN; unitNN; mapNN)
open import BooleanCompletion using (Holds)
open import RelationalTruth using (RelBoolMap; RelAgree; FunctionCover;
  functions-to-predicates)
open import SubcountableObstruction using (Subcountable;
  cover-index-not-subcountable; ModalAllSmallSubcountable)
import RelationalExponential as Exponential

At : ∀ {ℓ} {A : Type ℓ} → RelBoolMap A → A → Bool → Type ℓ
At R a b = Holds (R a .fst b)

record BooleanFunctionObject {ℓ : Level} (e g : Level) (A : Type ℓ)
  : Type (ℓ-suc (ℓ-max ℓ (ℓ-max e g))) where
  field
    Carrier : Type ℓ
    Equal : Carrier → Carrier → Type e
    evaluate : Carrier → RelBoolMap A
    evaluate-congruent : (i j : Carrier) → Equal i j
      → RelAgree A (evaluate i) (evaluate j)
    names : RelBoolMap A → Carrier → Type g
    name-total : (R : RelBoolMap A) → NN (Σ[ i ∈ Carrier ] names R i)
    name-unique : (R : RelBoolMap A) (i j : Carrier)
      → names R i → names R j → Equal i j

  applied : RelBoolMap A → A → Bool → Type (ℓ-max ℓ g)
  applied R a b = NN (Σ[ i ∈ Carrier ] (names R i × At (evaluate i) a b))

  field
    beta : (R : RelBoolMap A) (a : A) (b : Bool)
      → (applied R a b → At R a b) × (At R a b → applied R a b)

module _ {ℓ e g : Level} {A : Type ℓ} (object : BooleanFunctionObject e g A) where
  open BooleanFunctionObject object

  named-row-agrees : (R : RelBoolMap A) (i : Carrier)
    → names R i → RelAgree A R (evaluate i)
  named-row-agrees R i named a b =
    (λ value → evaluate i a .fst b .snd (mapNN
      (λ { (j , named-j , value-j) → evaluate-congruent j i
        (name-unique R j i named-j named) a b .fst value-j })
      (beta R a b .snd value))) ,
    (λ value → beta R a b .fst (unitNN (i , named , value)))

  function-object-to-cover : FunctionCover A
  FunctionCover.Index function-object-to-cover = Carrier
  FunctionCover.family function-object-to-cover = evaluate
  FunctionCover.covers function-object-to-cover R = mapNN
    (λ { (i , named) → i , named-row-agrees R i named }) (name-total R)

module _ {ℓ : Level} {A : Type ℓ} (cover : FunctionCover A) where
  cover-to-function-object : BooleanFunctionObject ℓ ℓ A
  BooleanFunctionObject.Carrier cover-to-function-object = FunctionCover.Index cover
  BooleanFunctionObject.Equal cover-to-function-object = Exponential.Equal A cover
  BooleanFunctionObject.evaluate cover-to-function-object = FunctionCover.family cover
  BooleanFunctionObject.evaluate-congruent cover-to-function-object i j e = e
  BooleanFunctionObject.names cover-to-function-object R i =
    RelAgree A R (FunctionCover.family cover i)
  BooleanFunctionObject.name-total cover-to-function-object = FunctionCover.covers cover
  BooleanFunctionObject.name-unique cover-to-function-object R i j ri rj =
    Exponential.agree-trans A cover (FunctionCover.family cover i) R
      (FunctionCover.family cover j) (Exponential.agree-sym A cover R
        (FunctionCover.family cover i) ri) rj
  BooleanFunctionObject.beta cover-to-function-object R a b =
    (λ n → R a .fst b .snd (mapNN
      (λ { (i , agree , value) → agree a b .snd value }) n)) ,
    (λ value → mapNN
      (λ { (i , agree) → i , agree , agree a b .fst value })
      (FunctionCover.covers cover R))

natural-function-carrier-not-subcountable : ∀ {e g}
  → (object : BooleanFunctionObject e g ℕ)
  → ¬ Subcountable (BooleanFunctionObject.Carrier object)
natural-function-carrier-not-subcountable object = cover-index-not-subcountable
  (functions-to-predicates ℕ (function-object-to-cover object))

modal-subcountability-refutes-function-object : ∀ {e g}
  → ModalAllSmallSubcountable → ¬ BooleanFunctionObject e g ℕ
modal-subcountability-refutes-function-object sc object =
  sc (BooleanFunctionObject.Carrier object)
    (natural-function-carrier-not-subcountable object)

modal-subcountability-refutes-negative-function-object : ∀ {e g}
  → ModalAllSmallSubcountable → ¬ NN (BooleanFunctionObject e g ℕ)
modal-subcountability-refutes-negative-function-object sc n =
  n (modal-subcountability-refutes-function-object sc)
