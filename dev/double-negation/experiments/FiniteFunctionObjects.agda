{-# OPTIONS --cubical --safe --guardedness #-}
module FiniteFunctionObjects where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ; zero; suc)
open import Cubical.Data.Fin.Recursive.Base using (Fin) renaming (zero to fzero; suc to fsuc)
open import Cubical.Data.Bool using (Bool)
open import ModalTrees using (NN; unitNN; mapNN; bindNN)
open import BooleanCompletion using (Holds)
open import RelationalTruth using (Pred; PredicateCover; FunctionCover;
  truth-code; code-dense; predicates-to-functions)
open import FunctionObjectBoundary using (BooleanFunctionObject; cover-to-function-object)

finite-shift : ∀ {ℓ} (n : ℕ) (P : Fin n → Type ℓ)
  → ((i : Fin n) → NN (P i)) → NN ((i : Fin n) → P i)
finite-shift zero P each = unitNN (λ ())
finite-shift (suc n) P each = bindNN (each fzero) λ first →
  mapNN (cons first) (finite-shift n (λ i → P (fsuc i)) (λ i → each (fsuc i)))
  where
  cons : P fzero → ((i : Fin n) → P (fsuc i)) → (i : Fin (suc n)) → P i
  cons first rest fzero = first
  cons first rest (fsuc i) = rest i

finite-predicate-cover : (n : ℕ) → PredicateCover (Fin n)
PredicateCover.Index (finite-predicate-cover n) = Fin n → Bool
PredicateCover.family (finite-predicate-cover n) mask i = truth-code (mask i)
PredicateCover.covers (finite-predicate-cover n) P = mapNN
  (λ decisions → (λ i → decisions i .fst) , λ i →
    (λ p → subst Holds (decisions i .snd) p) ,
    (λ q → subst Holds (sym (decisions i .snd)) q))
  (finite-shift n (λ i → Σ[ b ∈ Bool ] P i ≡ truth-code b)
    (λ i → code-dense (P i)))

finite-function-cover : (n : ℕ) → FunctionCover (Fin n)
finite-function-cover n = predicates-to-functions (Fin n) (finite-predicate-cover n)

finite-function-object : (n : ℕ) → BooleanFunctionObject ℓ-zero ℓ-zero (Fin n)
finite-function-object n = cover-to-function-object (finite-function-cover n)
