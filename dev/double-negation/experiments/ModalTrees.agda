{-# OPTIONS --cubical --safe --guardedness #-}
module ModalTrees where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Empty using (⊥; isProp⊥)
open import Cubical.Data.Sigma using (_×_)
open import Cubical.Relation.Nullary using (¬_)

NN : ∀ {ℓ} → Type ℓ → Type ℓ
NN A = ¬ ¬ A

unitNN : ∀ {ℓ} {A : Type ℓ} → A → NN A
unitNN a k = k a

mapNN : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} → (A → B) → NN A → NN B
mapNN f n k = n (λ a → k (f a))

bindNN : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} → NN A → (A → NN B) → NN B
bindNN n f k = n (λ a → f a k)

propNN : ∀ {ℓ} {A : Type ℓ} → isProp (NN A)
propNN = isPropΠ (λ _ → isProp⊥)

stableNN : ∀ {ℓ} {A : Type ℓ} → NN (NN A) → NN A
stableNN n k = n (λ m → m k)

data Tree (ℓ : Level) : Type (ℓ-suc ℓ) where
  sup : (A : Type ℓ) → (A → Tree ℓ) → Tree ℓ

module _ {ℓ : Level} where
  Eq : Tree ℓ → Tree ℓ → Type ℓ
  Eq (sup A f) (sup B g) =
    ((a : A) → NN (Σ[ b ∈ B ] Eq (f a) (g b))) ×
    ((b : B) → NN (Σ[ a ∈ A ] Eq (f a) (g b)))

  eq-prop : (x y : Tree ℓ) → isProp (Eq x y)
  eq-prop (sup A f) (sup B g) =
    isProp× (isPropΠ (λ _ → propNN)) (isPropΠ (λ _ → propNN))

  eq-stable : (x y : Tree ℓ) → NN (Eq x y) → Eq x y
  eq-stable (sup A f) (sup B g) n =
    (λ a → stableNN (mapNN (λ e → e .fst a) n)) ,
    (λ b → stableNN (mapNN (λ e → e .snd b) n))

  eq-refl : (x : Tree ℓ) → Eq x x
  eq-refl (sup A f) =
    (λ a → unitNN (a , eq-refl (f a))) ,
    (λ a → unitNN (a , eq-refl (f a)))

  eq-sym : (x y : Tree ℓ) → Eq x y → Eq y x
  eq-sym (sup A f) (sup B g) e =
    (λ b → mapNN (λ { (a , p) → a , eq-sym (f a) (g b) p }) (e .snd b)) ,
    (λ a → mapNN (λ { (b , p) → b , eq-sym (f a) (g b) p }) (e .fst a))

  eq-trans : (x y z : Tree ℓ) → Eq x y → Eq y z → Eq x z
  eq-trans (sup A f) (sup B g) (sup C h) e d =
    (λ a → bindNN (e .fst a) λ { (b , p) →
      mapNN (λ { (c , q) → c , eq-trans (f a) (g b) (h c) p q }) (d .fst b) }) ,
    (λ c → bindNN (d .snd c) λ { (b , q) →
      mapNN (λ { (a , p) → a , eq-trans (f a) (g b) (h c) p q }) (e .snd b) })

  Mem : Tree ℓ → Tree ℓ → Type ℓ
  Mem x (sup A f) = NN (Σ[ a ∈ A ] Eq x (f a))

  mem-prop : (x a : Tree ℓ) → isProp (Mem x a)
  mem-prop x (sup A f) = propNN

  mem-stable : (x a : Tree ℓ) → NN (Mem x a) → Mem x a
  mem-stable x (sup A f) = stableNN

  mem-left : (x y a : Tree ℓ) → Eq x y → Mem x a → Mem y a
  mem-left x y (sup A f) e = mapNN
    (λ { (i , p) → i , eq-trans y x (f i) (eq-sym x y e) p })

  mem-right : (x a b : Tree ℓ) → Eq a b → Mem x a → Mem x b
  mem-right x (sup A f) (sup B g) e m = bindNN m λ { (i , p) →
    mapNN (λ { (j , q) → j , eq-trans x (f i) (g j) p q }) (e .fst i) }

  extensionality : (a b : Tree ℓ)
    → ((x : Tree ℓ) → (Mem x a → Mem x b) × (Mem x b → Mem x a))
    → Eq a b
  extensionality (sup A f) (sup B g) ext =
    (λ i → ext (f i) .fst (unitNN (i , eq-refl (f i)))) ,
    (λ j → mapNN (λ { (i , p) → i , eq-sym (g j) (f i) p })
      (ext (g j) .snd (unitNN (j , eq-refl (g j)))))

  separate : (a : Tree ℓ) → (Tree ℓ → Type ℓ) → Tree ℓ
  separate (sup A f) P = sup (Σ[ i ∈ A ] P (f i)) (λ ip → f (ip .fst))

  separation : (P : Tree ℓ → Type ℓ)
    → ((x : Tree ℓ) → NN (P x) → P x)
    → ((x y : Tree ℓ) → Eq x y → P x → P y)
    → (a x : Tree ℓ)
    → (Mem x (separate a P) → Mem x a × P x)
       × (Mem x a × P x → Mem x (separate a P))
  separation P stable ext (sup A f) x =
    (λ m →
      mapNN (λ { ((i , p) , e) → i , e }) m ,
      stable x (mapNN (λ { ((i , p) , e) →
        ext (f i) x (eq-sym x (f i) e) p }) m)) ,
    (λ { (m , p) → mapNN (λ { (i , e) → (i , ext x (f i) e p) , e }) m })

  stable-induction : ∀ {ℓ'} (P : Tree ℓ → Type ℓ')
    → ((x : Tree ℓ) → NN (P x) → P x)
    → ((x y : Tree ℓ) → Eq x y → P x → P y)
    → ((a : Tree ℓ) → ((x : Tree ℓ) → Mem x a → P x) → P a)
    → (a : Tree ℓ) → P a
  stable-induction P stable ext step (sup A f) = step (sup A f) λ x m →
    stable x (mapNN (λ { (i , e) → ext (f i) x (eq-sym x (f i) e)
      (stable-induction P stable ext step (f i)) }) m)

  Minimal : Tree ℓ → Tree ℓ → Type (ℓ-suc ℓ)
  Minimal a x = Mem x a × ((y : Tree ℓ) → Mem y x → ¬ Mem y a)

  foundation : (a : Tree ℓ)
    → NN (Σ[ x ∈ Tree ℓ ] Mem x a)
    → NN (Σ[ x ∈ Tree ℓ ] Minimal a x)
  foundation a inhabited no-minimal = inhabited λ { (x , xa) → absent x xa }
    where
    absent : (x : Tree ℓ) → ¬ Mem x a
    absent = stable-induction (λ x → ¬ Mem x a)
      (λ x n m → n (λ k → k m))
      (λ x y e nx my → nx (mem-left y x a (eq-sym x y e) my))
      (λ x ih xa → no-minimal (x , xa , ih))
