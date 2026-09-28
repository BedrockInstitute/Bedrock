{-# OPTIONS --cubical --safe --guardedness #-}
module InternalResizing where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Data.Sigma using (_×_)
open import Cubical.Data.Unit using (Unit; tt; isPropUnit)
open import Cubical.Data.Empty as Empty using (⊥; isProp⊥)
open import Cubical.Relation.Nullary using (Dec; yes; no)
open import ModalTrees using (NN; mapNN; bindNN)
open import BooleanPower using (pointwise-decision)
open import BooleanCompletion using (StableProp; Holds)

Representative : ∀ {ℓ} → StableProp ℓ → Type (ℓ-max ℓ (ℓ-suc ℓ-zero))
Representative P = Σ[ Q ∈ StableProp ℓ-zero ] (Holds P ≃ Holds Q)

decided-resize : ∀ {ℓ} (P : StableProp ℓ) → Dec (Holds P) → Representative P
decided-resize P (yes p) = ((Unit , isPropUnit) , (λ _ → tt)) ,
  propBiimpl→Equiv (P .fst .snd) isPropUnit (λ _ → tt) (λ _ → p)
decided-resize P (no np) = ((⊥ , isProp⊥) , (λ n → n (λ x → x))) ,
  propBiimpl→Equiv (P .fst .snd) isProp⊥ np Empty.rec

internal-LEM-to-resizing : ∀ {ℓ} (P : StableProp ℓ)
  → NN (Dec (Holds P)) → NN (Representative P)
internal-LEM-to-resizing P = mapNN (decided-resize P)

internal-resize : ∀ {ℓ} (P : StableProp ℓ) → NN (Representative P)
internal-resize P = internal-LEM-to-resizing P (pointwise-decision (Holds P))

consume-resizing : ∀ {ℓ ℓ'} (P : StableProp ℓ) {B : Type ℓ'}
  → (NN B → B) → (Representative P → B) → B
consume-resizing P stable use = stable (mapNN use (internal-resize P))

resize-two : ∀ {ℓ ℓ'} (P : StableProp ℓ) (R : StableProp ℓ')
  → NN (Representative P × Representative R)
resize-two P R = bindNN (internal-resize P) λ p →
  mapNN (λ r → p , r) (internal-resize R)
