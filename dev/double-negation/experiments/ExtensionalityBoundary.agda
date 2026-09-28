{-# OPTIONS --cubical --safe --guardedness #-}
module ExtensionalityBoundary where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure
open import Cubical.Data.Empty using (⊥)
open import Cubical.Data.Unit using (Unit; tt)
open import Cubical.Data.Sigma using (_×_)
open import Cubical.Relation.Nullary using (¬_; Dec; isPropDec)
open import Cubical.HITs.CumulativeHierarchy.Base using (V; sett; _∈_)
import Cubical.HITs.PropositionalTruncation as PT
open import Boundary using (pointwise-LEM)

S : Type (ℓ-suc ℓ-zero)
S = V ℓ-zero

emptyV : S
emptyV = sett ⊥ (λ ())

oneV : S
oneV = sett Unit (λ _ → emptyV)

indicator : hProp ℓ-zero → S
indicator P = sett ⟨ P ⟩ (λ _ → emptyV)

_∈ⁿ_ : S → S → Type (ℓ-suc ℓ-zero)
x ∈ⁿ a = ¬ ¬ ⟨ x ∈ a ⟩

HostExtensionality : Type (ℓ-suc ℓ-zero)
HostExtensionality = (a b : S)
  → ((x : S) → ((x ∈ⁿ a) → (x ∈ⁿ b)) × ((x ∈ⁿ b) → (x ∈ⁿ a)))
  → a ≡ b

indicator-membership : (P : hProp ℓ-zero) → ⟨ emptyV ∈ indicator P ⟩ → ⟨ P ⟩
indicator-membership P = PT.rec (P .snd) fst

modal-agreement : (P : hProp ℓ-zero) → ¬ ¬ ⟨ P ⟩
  → (x : S) → ((x ∈ⁿ indicator P) → (x ∈ⁿ oneV))
             × ((x ∈ⁿ oneV) → (x ∈ⁿ indicator P))
modal-agreement P nnP x =
  (λ nnA nB → nnA (λ a → nB (PT.map (λ { (_ , e) → tt , e }) a))) ,
  (λ nnB nA → nnP (λ p → nnB (λ b → nA (PT.map (λ { (_ , e) → p , e }) b))))

host-extensionality-implies-DNE : HostExtensionality
  → (P : hProp ℓ-zero) → ¬ ¬ ⟨ P ⟩ → ⟨ P ⟩
host-extensionality-implies-DNE ext P nnP = indicator-membership P
  (subst (λ a → ⟨ emptyV ∈ a ⟩)
    (sym (ext (indicator P) oneV (modal-agreement P nnP)))
    (PT.∣ tt , refl ∣₁))

host-extensionality-implies-LEM : HostExtensionality
  → (P : hProp ℓ-zero) → Dec ⟨ P ⟩
host-extensionality-implies-LEM ext P =
  host-extensionality-implies-DNE ext (Dec ⟨ P ⟩ , isPropDec (P .snd))
    (pointwise-LEM ⟨ P ⟩)

double-negated-model-implies-consistency : ∀ {ℓ ℓ'}
  {Model : Type ℓ} {ProofOfFalse : Type ℓ'}
  → (Model → ¬ ProofOfFalse) → ¬ ¬ Model → ¬ ProofOfFalse
double-negated-model-implies-consistency sound nnModel proof =
  nnModel (λ model → sound model proof)
