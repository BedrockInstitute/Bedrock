{-# OPTIONS --cubical --safe --guardedness #-}
module SubcountableObstruction where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.Empty using (⊥)
open import Cubical.Relation.Nullary using (¬_)
open import ModalTrees using (NN; unitNN; mapNN; bindNN; propNN; stableNN)
open import BooleanCompletion using (StableProp; Holds; negated)
open import RelationalTruth using (Pred; PredAgree; PredicateCover; FunctionCover;
  functions-to-predicates)
open import DensePower using (PowerWitness)
open import CoverObstructions using (chain)
open import FunctionPower using (natural-power-to-functions)

record Subcountable (I : Type) : Type₁ where
  field
    domain : ℕ → hProp ℓ-zero
    enumerate : (Σ[ n ∈ ℕ ] domain n .fst) → I
    onto : (i : I) → NN (Σ[ nd ∈ (Σ[ n ∈ ℕ ] domain n .fst) ] enumerate nd ≡ i)

Covers : {I : Type} → (I → Pred ℕ) → Type₁
Covers {I} R = (P : Pred ℕ) → NN (Σ[ i ∈ I ] PredAgree ℕ P (R i))

diagonal : (ℕ → Pred ℕ) → Pred ℕ
diagonal R n = negated (R n n)

no-countable-cover : (R : ℕ → Pred ℕ) → ¬ Covers R
no-countable-cover R cover = cover (diagonal R) λ { (n , agree) →
  contradiction n agree (agree n .fst (contradiction n agree)) }
  where
  contradiction : (n : ℕ) → PredAgree ℕ (diagonal R) (R n) → ¬ Holds (R n n)
  contradiction n agree p = agree n .snd p p

module _ {I : Type} (presentation : Subcountable I) (R : I → Pred ℕ) where
  open Subcountable presentation

  extended : ℕ → Pred ℕ
  extended n k =
    (NN (Σ[ d ∈ domain n .fst ] Holds (R (enumerate (n , d)) k)) , propNN) , stableNN

  extension-agrees : (n : ℕ) (d : domain n .fst)
    → PredAgree ℕ (R (enumerate (n , d))) (extended n)
  extension-agrees n d k =
    (λ value → unitNN (d , value)) ,
    (λ values → R (enumerate (n , d)) k .snd (mapNN
      (λ { (d' , value) → subst (λ q → Holds (R (enumerate (n , q)) k))
        (domain n .snd d' d) value }) values))

  extend-coverage : Covers R → Covers extended
  extend-coverage cover P = bindNN (cover P) λ { (i , agree) →
    mapNN (λ { ((n , d) , e) → n , λ k →
      (λ p → extension-agrees n d k .fst
        (subst (λ j → Holds (R j k)) (sym e) (agree k .fst p))) ,
      (λ value → agree k .snd (subst (λ j → Holds (R j k)) e
        (extension-agrees n d k .snd value))) }) (onto i) }

  no-subcountable-cover : ¬ Covers R
  no-subcountable-cover cover = no-countable-cover extended (extend-coverage cover)

cover-index-not-subcountable : (C : PredicateCover ℕ) → ¬ Subcountable (PredicateCover.Index C)
cover-index-not-subcountable C presentation = no-subcountable-cover presentation
  (PredicateCover.family C) (PredicateCover.covers C)

AllSmallSubcountable : Type₁
AllSmallSubcountable = (I : Type) → Subcountable I

subcountability-refutes-functions : AllSmallSubcountable → ¬ FunctionCover ℕ
subcountability-refutes-functions sc C = cover-index-not-subcountable
  (functions-to-predicates ℕ C) (sc (FunctionCover.Index C))

subcountability-refutes-power : AllSmallSubcountable → ¬ PowerWitness chain
subcountability-refutes-power sc W = subcountability-refutes-functions sc
  (natural-power-to-functions W)

subcountability-refutes-negative-power : AllSmallSubcountable → ¬ NN (PowerWitness chain)
subcountability-refutes-negative-power sc n = n (subcountability-refutes-power sc)

ModalAllSmallSubcountable : Type₁
ModalAllSmallSubcountable = (I : Type) → NN (Subcountable I)

modal-subcountability-refutes-functions : ModalAllSmallSubcountable → ¬ FunctionCover ℕ
modal-subcountability-refutes-functions sc C = sc (FunctionCover.Index C)
  (cover-index-not-subcountable (functions-to-predicates ℕ C))

modal-subcountability-refutes-power : ModalAllSmallSubcountable → ¬ PowerWitness chain
modal-subcountability-refutes-power sc W = modal-subcountability-refutes-functions sc
  (natural-power-to-functions W)
