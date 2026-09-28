{-# OPTIONS --cubical --safe --guardedness #-}
module QuantifierTransport where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Data.Sigma using (_×_)
open import Cubical.Data.Bool using (Bool; true; false)
open import Cubical.Data.Unit using (tt*)
open import Cubical.Data.Empty as Empty using (⊥)
open import Cubical.Relation.Nullary using (Dec; yes; no)
open import ModalTrees using (NN; unitNN; mapNN; bindNN; propNN)
open import BooleanCompletion using (StableProp; Holds)
open import RelationalTruth using (truth-code; code-dense; classification-path)

module DenseTransport {a b : Level} {A : Type a} {B : Type b}
  (name : B → A) (dense : (x : A) → NN (Σ[ y ∈ B ] x ≡ name y)) where

  module _ {p : Level} (P : A → Type p) where
    all-restrict : ((x : A) → P x) → (y : B) → P (name y)
    all-restrict all y = all (name y)

    all-extend : ((x : A) → NN (P x) → P x)
      → ((y : B) → P (name y)) → (x : A) → P x
    all-extend stable all x = stable x
      (mapNN (λ { (y , e) → subst P (sym e) (all y) }) (dense x))

    all-equiv : ((x : A) → isProp (P x))
      → ((x : A) → NN (P x) → P x)
      → ((x : A) → P x) ≃ ((y : B) → P (name y))
    all-equiv prop stable = propBiimpl→Equiv
      (isPropΠ prop) (isPropΠ (λ y → prop (name y)))
      all-restrict (all-extend stable)

    some-restrict : NN (Σ[ x ∈ A ] P x) → NN (Σ[ y ∈ B ] P (name y))
    some-restrict n = bindNN n λ { (x , px) →
      mapNN (λ { (y , e) → y , subst P e px }) (dense x) }

    some-extend : NN (Σ[ y ∈ B ] P (name y)) → NN (Σ[ x ∈ A ] P x)
    some-extend = mapNN (λ { (y , py) → name y , py })

    some-equiv : NN (Σ[ x ∈ A ] P x) ≃ NN (Σ[ y ∈ B ] P (name y))
    some-equiv = propBiimpl→Equiv propNN propNN some-restrict some-extend

module _ {ℓ p : Level} (P : StableProp ℓ → StableProp p) where
  private module Transport = DenseTransport (truth-code {ℓ}) code-dense

  truth-forall-small : ((Q : StableProp ℓ) → Holds (P Q))
    ≃ ((b : Bool) → Holds (P (truth-code b)))
  truth-forall-small = Transport.all-equiv (λ Q → Holds (P Q))
    (λ Q → P Q .fst .snd) (λ Q → P Q .snd)

  truth-exists-small : NN (Σ[ Q ∈ StableProp ℓ ] Holds (P Q))
    ≃ NN (Σ[ b ∈ Bool ] Holds (P (truth-code b)))
  truth-exists-small = Transport.some-equiv (λ Q → Holds (P Q))

module _ {ℓ : Level} (A : Type ℓ) where
  MaskDense : Type (ℓ-suc ℓ)
  MaskDense = (P : A → StableProp ℓ)
    → NN (Σ[ mask ∈ (A → Bool) ] ((x : A) → P x ≡ truth-code (mask x)))

  StableDecisionShift : Type (ℓ-suc ℓ)
  StableDecisionShift = (P : A → StableProp ℓ)
    → NN ((x : A) → Dec (Holds (P x)))

  code-decision : (b : Bool) → Dec (Holds (truth-code {ℓ} b))
  code-decision true = yes tt*
  code-decision false = no Empty.rec*

  masks-to-decisions : MaskDense → StableDecisionShift
  masks-to-decisions covers P = mapNN
    (λ { (mask , e) x → subst (λ Q → Dec (Holds Q)) (sym (e x))
      (code-decision (mask x)) }) (covers P)

  decision-code : (P : StableProp ℓ) → Dec (Holds P)
    → Σ[ b ∈ Bool ] P ≡ truth-code b
  decision-code P (yes p) = true , classification-path P true p
  decision-code P (no np) = false , classification-path P false np

  decisions-to-masks : StableDecisionShift → MaskDense
  decisions-to-masks shift P = mapNN
    (λ d → (λ x → decision-code (P x) (d x) .fst) ,
      (λ x → decision-code (P x) (d x) .snd)) (shift P)
