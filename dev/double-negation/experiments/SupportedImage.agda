{-# OPTIONS --cubical --safe --guardedness #-}
module SupportedImage where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma using (_×_)
open import Cubical.Data.Unit using (Unit; tt)
open import ModalTrees

SmallSupport : ∀ {ℓ} → Type ℓ → Type (ℓ-max ℓ (ℓ-suc ℓ-zero))
SmallSupport X = Σ[ D ∈ Type ] (NN D × (D → X))

support-to-negative : ∀ {ℓ} {X : Type ℓ} → SmallSupport X → NN X
support-to-negative (D , dense , values) = mapNN values dense

point-to-support : ∀ {ℓ} {X : Type ℓ} → X → SmallSupport X
point-to-support x = Unit , unitNN tt , (λ _ → x)

negative-to-negative-support : ∀ {ℓ} {X : Type ℓ} → NN X → NN (SmallSupport X)
negative-to-negative-support = mapNN point-to-support

small-negative-to-support : {X : Type} → NN X → SmallSupport X
small-negative-to-support {X} dense = X , dense , (λ x → x)

module _ {ℓ : Level} {A : Type}
  (R : A → Tree ℓ-zero → Type ℓ)
  (ext : (i : A) (y z : Tree ℓ-zero) → Eq y z → R i y → R i z)
  (unique : (i : A) (y z : Tree ℓ-zero) → R i y → R i z → Eq y z) where

  SupportedValues : Type (ℓ-max ℓ (ℓ-suc ℓ-zero))
  SupportedValues = (i : A) → SmallSupport (Σ[ y ∈ Tree ℓ-zero ] R i y)

  ImageSpec : Tree ℓ-zero → Type (ℓ-max ℓ (ℓ-suc ℓ-zero))
  ImageSpec b = (y : Tree ℓ-zero) →
    (Mem y b → NN (Σ[ i ∈ A ] R i y)) ×
    (NN (Σ[ i ∈ A ] R i y) → Mem y b)

  ImageWitness : Type (ℓ-max ℓ (ℓ-suc ℓ-zero))
  ImageWitness = Σ[ b ∈ Tree ℓ-zero ] ImageSpec b

  module _ (supports : SupportedValues) where
    D : A → Type
    D i = supports i .fst

    dense : (i : A) → NN (D i)
    dense i = supports i .snd .fst

    values : (i : A) → D i → Tree ℓ-zero
    values i d = supports i .snd .snd d .fst

    realizes : (i : A) (d : D i) → R i (values i d)
    realizes i d = supports i .snd .snd d .snd

    supportedImage : Tree ℓ-zero
    supportedImage = sup (Σ[ i ∈ A ] D i) (λ id → values (id .fst) (id .snd))

    supportedImage-spec : ImageSpec supportedImage
    supportedImage-spec y =
      mapNN (λ { ((i , d) , e) → i ,
        ext i (values i d) y (eq-sym y (values i d) e) (realizes i d) }) ,
      (λ m → bindNN m λ { (i , r) → mapNN
        (λ d → (i , d) , unique i y (values i d) r (realizes i d)) (dense i) })

  supports-to-image : SupportedValues → ImageWitness
  supports-to-image supports = supportedImage supports , supportedImage-spec supports

  modal-supports-to-image : NN SupportedValues → NN ImageWitness
  modal-supports-to-image = mapNN supports-to-image

  total-to-pointwise-supports : ((i : A) → NN (Σ[ y ∈ Tree ℓ-zero ] R i y))
    → (i : A) → NN (SmallSupport (Σ[ y ∈ Tree ℓ-zero ] R i y))
  total-to-pointwise-supports total i = negative-to-negative-support (total i)

module _ {A : Type} (R : A → Tree ℓ-zero → Type)
  (B : A → Type) (candidates : (i : A) → B i → Tree ℓ-zero)
  (total : (i : A) → NN (Σ[ b ∈ B i ] R i (candidates i b))) where

  bounded-supports : (i : A) → SmallSupport (Σ[ y ∈ Tree ℓ-zero ] R i y)
  bounded-supports i = (Σ[ b ∈ B i ] R i (candidates i b)) , total i ,
    (λ { (b , r) → candidates i b , r })

  bounded-image
    : (ext : (i : A) (y z : Tree ℓ-zero) → Eq y z → R i y → R i z)
    → (unique : (i : A) (y z : Tree ℓ-zero) → R i y → R i z → Eq y z)
    → ImageWitness R ext unique
  bounded-image ext unique = supports-to-image R ext unique bounded-supports

module _ {A : Type} (R : A → Tree ℓ-zero → Type)
  (ext : (i : A) (y z : Tree ℓ-zero) → Eq y z → R i y → R i z)
  (unique : (i : A) (y z : Tree ℓ-zero) → R i y → R i z → Eq y z)
  (total : (i : A) → NN (Σ[ y ∈ Tree ℓ-zero ] R i y)) where

  image-to-supports : ImageWitness R ext unique → SupportedValues R ext unique
  image-to-supports (sup I g , spec) i = (Σ[ j ∈ I ] R i (g j)) ,
    bindNN (total i) (λ { (y , r) → mapNN
      (λ { (j , e) → j , ext i y (g j) e r }) (spec y .snd (unitNN (i , r))) }) ,
    (λ { (j , r) → g j , r })

  modal-image-to-supports : NN (ImageWitness R ext unique)
    → NN (SupportedValues R ext unique)
  modal-image-to-supports = mapNN image-to-supports
