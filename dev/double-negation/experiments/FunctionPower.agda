{-# OPTIONS --cubical --safe --guardedness #-}
module FunctionPower where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ)
open import ModalTrees using (Tree; Eq; NN; mapNN)
open import BooleanCompletion using (StableProp; Holds)
open import RelationalTruth using (PredicateCover; FunctionCover;
  functions-to-predicates; predicates-to-functions)
open import DensePower using (Predicate; DenseCover; PowerWitness;
  cover-to-power; power-to-cover)
open import CoverObstructions using (chain; chain-injective)

module _ {ℓ : Level} {A : Type ℓ} (f : A → Tree ℓ)
  (injective : (i j : A) → Eq (f i) (f j) → i ≡ j) where

  pack : (A → StableProp ℓ) → Predicate f
  Predicate.holds (pack P) i = Holds (P i)
  Predicate.prop (pack P) i = P i .fst .snd
  Predicate.stable (pack P) i = P i .snd
  Predicate.saturated (pack P) i j e = subst (λ k → Holds (P k)) (injective i j e)

  unpack : Predicate f → A → StableProp ℓ
  unpack P i = (Predicate.holds P i , Predicate.prop P i) , Predicate.stable P i

  predicates-to-cover : PredicateCover A → DenseCover f
  DenseCover.Index (predicates-to-cover C) = PredicateCover.Index C
  DenseCover.family (predicates-to-cover C) i = pack (PredicateCover.family C i)
  DenseCover.covers (predicates-to-cover C) P = PredicateCover.covers C (unpack P)

  cover-to-predicates : DenseCover f → PredicateCover A
  PredicateCover.Index (cover-to-predicates C) = DenseCover.Index C
  PredicateCover.family (cover-to-predicates C) i = unpack (DenseCover.family C i)
  PredicateCover.covers (cover-to-predicates C) P = DenseCover.covers C (pack P)

  functions-to-power : FunctionCover A → PowerWitness f
  functions-to-power C = cover-to-power f
    (predicates-to-cover (functions-to-predicates A C))

  power-to-functions : PowerWitness f → FunctionCover A
  power-to-functions W = predicates-to-functions A
    (cover-to-predicates (power-to-cover f W))

  negative-functions-to-power : NN (FunctionCover A) → NN (PowerWitness f)
  negative-functions-to-power = mapNN functions-to-power

  negative-power-to-functions : NN (PowerWitness f) → NN (FunctionCover A)
  negative-power-to-functions = mapNN power-to-functions

natural-functions-to-power : FunctionCover ℕ → PowerWitness chain
natural-functions-to-power = functions-to-power chain chain-injective

natural-power-to-functions : PowerWitness chain → FunctionCover ℕ
natural-power-to-functions = power-to-functions chain chain-injective
