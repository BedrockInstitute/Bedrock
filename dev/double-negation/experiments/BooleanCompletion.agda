{-# OPTIONS --cubical --safe --guardedness #-}
module BooleanCompletion where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence using (hPropExt)
open import Cubical.Data.Sigma using (_×_; Σ≡Prop)
open import Cubical.Data.Bool using (Bool; true; false; isSetBool; false≢true; true≢false)
open import Cubical.Data.Empty as Empty using (⊥; isProp⊥)
open import Cubical.Relation.Nullary using (¬_; Dec; yes; no)
open import ModalTrees using (NN; unitNN; mapNN; propNN)
open import BooleanPower using (pointwise-decision)

module _ (ℓ : Level) where
  StableProp : Type (ℓ-suc ℓ)
  StableProp = Σ[ P ∈ hProp ℓ ] (NN (P .fst) → P .fst)

module _ {ℓ : Level} where
  Holds : StableProp ℓ → Type ℓ
  Holds P = P .fst .fst

  stable-proof-prop : (P : hProp ℓ) → isProp (NN (P .fst) → P .fst)
  stable-proof-prop P = isPropΠ (λ _ → P .snd)

  stable-prop-ext : (P R : StableProp ℓ)
    → (Holds P → Holds R) → (Holds R → Holds P) → P ≡ R
  stable-prop-ext P R to from = Σ≡Prop stable-proof-prop
    (Σ≡Prop (λ _ → isPropIsProp)
      (hPropExt (P .fst .snd) (R .fst .snd) to from))

  negated : StableProp ℓ → StableProp ℓ
  negated P = ((¬ Holds P) , isPropΠ (λ _ → isProp⊥)) ,
    (λ n p → n (λ k → k p))

  CompletionConditions : (Bool → StableProp ℓ) → Type ℓ
  CompletionConditions ξ = NN (Σ[ b ∈ Bool ] Holds (ξ b)) ×
    ((b c : Bool) → Holds (ξ b) → Holds (ξ c) → b ≡ c)

  conditions-prop : (ξ : Bool → StableProp ℓ) → isProp (CompletionConditions ξ)
  conditions-prop ξ = isProp× propNN
    (isPropΠ (λ b → isPropΠ (λ c → isPropΠ2 (λ _ _ → isSetBool b c))))

  BooleanCompletion : Type (ℓ-suc ℓ)
  BooleanCompletion = Σ[ ξ ∈ (Bool → StableProp ℓ) ] CompletionConditions ξ

  evaluate : BooleanCompletion → StableProp ℓ
  evaluate C = C .fst true

  truth-family : StableProp ℓ → Bool → StableProp ℓ
  truth-family P true = P
  truth-family P false = negated P

  decision-point : (P : StableProp ℓ) → Dec (Holds P)
    → Σ[ b ∈ Bool ] Holds (truth-family P b)
  decision-point P (yes p) = true , p
  decision-point P (no np) = false , np

  truth-unique : (P : StableProp ℓ) (b c : Bool)
    → Holds (truth-family P b) → Holds (truth-family P c) → b ≡ c
  truth-unique P true true _ _ = refl
  truth-unique P true false p np = Empty.rec (np p)
  truth-unique P false true np p = Empty.rec (np p)
  truth-unique P false false _ _ = refl

  complete-truth : StableProp ℓ → BooleanCompletion
  complete-truth P = truth-family P ,
    mapNN (decision-point P) (pointwise-decision (Holds P)) , truth-unique P

  false-excludes-true : (C : BooleanCompletion)
    → Holds (C .fst false) → ¬ Holds (C .fst true)
  false-excludes-true C pf pt = false≢true (C .snd .snd false true pf pt)

  not-true-is-false : (C : BooleanCompletion)
    → ¬ Holds (C .fst true) → Holds (C .fst false)
  not-true-is-false C np = C .fst false .snd (mapNN choose (C .snd .fst))
    where
    choose : (Σ[ b ∈ Bool ] Holds (C .fst b)) → Holds (C .fst false)
    choose (false , p) = p
    choose (true , p) = Empty.rec (np p)

  reconstruction : (C : BooleanCompletion) → complete-truth (evaluate C) ≡ C
  reconstruction C = Σ≡Prop conditions-prop (funExt λ where
    true → refl
    false → stable-prop-ext (negated (evaluate C)) (C .fst false)
      (not-true-is-false C) (false-excludes-true C))

  completion-iso : Iso BooleanCompletion (StableProp ℓ)
  Iso.fun completion-iso = evaluate
  Iso.inv completion-iso = complete-truth
  Iso.rightInv completion-iso _ = refl
  Iso.leftInv completion-iso = reconstruction

  completion-equiv : BooleanCompletion ≃ StableProp ℓ
  completion-equiv = isoToEquiv completion-iso

  SmallCompletion : Type (ℓ-suc ℓ)
  SmallCompletion = Σ[ C ∈ Type ℓ ] (C ≃ BooleanCompletion)

  SmallStableClassifier : Type (ℓ-suc ℓ)
  SmallStableClassifier = Σ[ Ω ∈ Type ℓ ] (Ω ≃ StableProp ℓ)

  small-completion-to-classifier : SmallCompletion → SmallStableClassifier
  small-completion-to-classifier (C , e) = C , compEquiv e completion-equiv

  classifier-to-small-completion : SmallStableClassifier → SmallCompletion
  classifier-to-small-completion (Ω , e) = Ω , compEquiv e (invEquiv completion-equiv)
