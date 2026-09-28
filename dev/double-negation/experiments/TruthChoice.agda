{-# OPTIONS --cubical --safe --guardedness #-}
module TruthChoice where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Bool using (Bool; true; false)
open import Cubical.Data.Empty using (isProp⊥)
open import Cubical.Relation.Nullary using (¬_; Dec; yes; no)
open import ModalTrees using (NN)
open import BooleanCompletion using (StableProp; Holds)
open import RelationalTruth using (Classifies; classification-total)

module _ (ℓ : Level) where
  WeakLEM : Type (ℓ-suc ℓ)
  WeakLEM = (P : hProp ℓ) → Dec (¬ P .fst)

  StableLEM : Type (ℓ-suc ℓ)
  StableLEM = (P : StableProp ℓ) → Dec (Holds P)

  TruthChoice : Type (ℓ-suc ℓ)
  TruthChoice = (P : StableProp ℓ) → Σ[ b ∈ Bool ] Classifies P b

  stable-to-weak : StableLEM → WeakLEM
  stable-to-weak decide P = decide
    (((¬ P .fst) , isPropΠ (λ _ → isProp⊥)) , (λ n p → n (λ np → np p)))

  weak-to-stable : WeakLEM → StableLEM
  weak-to-stable weak P with weak (P .fst)
  ... | yes np = no np
  ... | no nnp = yes (P .snd nnp)

  choice-to-stable : TruthChoice → StableLEM
  choice-to-stable choose P with choose P
  ... | true , p = yes p
  ... | false , np = no np

  stable-to-choice : StableLEM → TruthChoice
  stable-to-choice decide P with decide P
  ... | yes p = true , p
  ... | no np = false , np

  choice-to-weak : TruthChoice → WeakLEM
  choice-to-weak choose = stable-to-weak (choice-to-stable choose)

  weak-to-choice : WeakLEM → TruthChoice
  weak-to-choice weak = stable-to-choice (weak-to-stable weak)

  modal-truth-choice : (P : StableProp ℓ) → NN (Σ[ b ∈ Bool ] Classifies P b)
  modal-truth-choice = classification-total
