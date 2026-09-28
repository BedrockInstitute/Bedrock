{-# OPTIONS --cubical --safe --guardedness #-}
module SeparationBoundary where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma using (_×_)
open import Cubical.Data.Empty as Empty using (⊥; isProp⊥)
open import Cubical.Data.Unit using (Unit; tt; isPropUnit)
open import Cubical.Relation.Nullary using (Dec; yes; no)
open import ModalTrees
open import BooleanPower using (cut; pointwise-decision)

SmallRepresentative : ∀ {ℓ} → Type ℓ → Type (ℓ-max ℓ (ℓ-suc ℓ-zero))
SmallRepresentative P = Σ[ Q ∈ hProp ℓ-zero ] ((P → Q .fst) × (Q .fst → P))

decided-representative : ∀ {ℓ} {P : Type ℓ} → Dec P → SmallRepresentative P
decided-representative (yes p) = (Unit , isPropUnit) , (λ _ → tt) , (λ _ → p)
decided-representative (no np) = (⊥ , isProp⊥) , np , Empty.rec

pointwise-small : ∀ {ℓ} (P : Type ℓ) → NN (SmallRepresentative P)
pointwise-small P = mapNN decided-representative (pointwise-decision P)

module _ {ℓ : Level} (P : Tree ℓ-zero → Type ℓ)
  {A : Type} (f : A → Tree ℓ-zero) where

  SmallOn : Type (ℓ-max ℓ (ℓ-suc ℓ-zero))
  SmallOn = Σ[ Q ∈ (A → hProp ℓ-zero) ]
    ((i : A) → (P (f i) → Q i .fst) × (Q i .fst → P (f i)))

  SeparationSpec : Tree ℓ-zero → Type (ℓ-max ℓ (ℓ-suc ℓ-zero))
  SeparationSpec b = (x : Tree ℓ-zero) →
    (Mem x b → Mem x (sup A f) × P x) ×
    (Mem x (sup A f) × P x → Mem x b)

  SeparationWitness : Type (ℓ-max ℓ (ℓ-suc ℓ-zero))
  SeparationWitness = Σ[ b ∈ Tree ℓ-zero ] SeparationSpec b

  separation-to-small-family : SeparationWitness → SmallOn
  separation-to-small-family (b , spec) =
    (λ i → Mem (f i) b , mem-prop (f i) b) , λ i →
    (λ p → spec (f i) .snd (unitNN (i , eq-refl (f i)) , p)) ,
    (λ m → spec (f i) .fst m .snd)

  module _ (stable : (x : Tree ℓ-zero) → NN (P x) → P x)
    (ext : (x y : Tree ℓ-zero) → Eq x y → P x → P y) where

    small-family-to-separation : SmallOn → SeparationWitness
    small-family-to-separation (Q , match) = cut f (λ i → Q i .fst) , λ x →
      (λ m → mapNN (λ { ((i , _) , e) → i , e }) m ,
        stable x (mapNN (λ { ((i , q) , e) →
          ext (f i) x (eq-sym x (f i) e) (match i .snd q) }) m)) ,
      (λ { (m , p) → mapNN (λ { (i , e) →
        (i , match i .fst (ext x (f i) e p)) , e }) m })

    modal-small-to-separation : NN SmallOn → NN SeparationWitness
    modal-small-to-separation = mapNN small-family-to-separation

  modal-separation-to-small : NN SeparationWitness → NN SmallOn
  modal-separation-to-small = mapNN separation-to-small-family

module _ {ℓ : Level} (P : Tree ℓ-zero → Type ℓ) (x : Tree ℓ-zero) where
  singleton-small-family : NN (SmallOn P (λ (_ : Unit) → x))
  singleton-small-family = mapNN (λ { (Q , match) → (λ _ → Q) , (λ _ → match) })
    (pointwise-small (P x))

  modal-singleton-separation
    : ((y : Tree ℓ-zero) → NN (P y) → P y)
    → ((y z : Tree ℓ-zero) → Eq y z → P y → P z)
    → NN (SeparationWitness P (λ (_ : Unit) → x))
  modal-singleton-separation stable ext =
    modal-small-to-separation P (λ (_ : Unit) → x) stable ext singleton-small-family

module _ {ℓ : Level} (P : Type ℓ) (x : Tree ℓ-zero) where
  actual-singleton-to-resizing
    : SeparationWitness (λ _ → P) (λ (_ : Unit) → x) → SmallRepresentative P
  actual-singleton-to-resizing w = family .fst tt , family .snd tt
    where
    family : SmallOn (λ _ → P) (λ (_ : Unit) → x)
    family = separation-to-small-family (λ _ → P) (λ (_ : Unit) → x) w
