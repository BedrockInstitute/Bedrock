{-# OPTIONS --cubical --safe --guardedness #-}
module BooleanPower where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma using (_×_)
open import Cubical.Data.Bool using (Bool; true; false; Dec→Bool; _≟_)
open import Cubical.Data.Empty as Empty using (⊥)
open import Cubical.Relation.Nullary using (Dec; yes; no; ¬_)
open import ModalTrees

decided-stable : ∀ {ℓ} {P : Type ℓ} → Dec P → NN P → P
decided-stable (yes p) _ = p
decided-stable (no np) nnP = Empty.rec (nnP np)

mark-in : ∀ {ℓ} {P : Type ℓ} (d : Dec P) → P → Dec→Bool d ≡ true
mark-in (yes p) _ = refl
mark-in (no np) p = Empty.rec (np p)

mark-out : ∀ {ℓ} {P : Type ℓ} (d : Dec P) → Dec→Bool d ≡ true → P
mark-out (yes p) _ = p
mark-out (no np) e = Empty.rec (false-not-true e)
  where
  false-not-true : ¬ (false ≡ true)
  false-not-true p = Empty.rec (subst (λ b → ifBool b) p false)
    where
    ifBool : Bool → Type
    ifBool false = Bool
    ifBool true = ⊥

pointwise-decision : ∀ {ℓ} (P : Type ℓ) → NN (Dec P)
pointwise-decision P k = k (no (λ p → k (yes p)))

module _ {ℓ : Level} where
  Subset : Tree ℓ → Tree ℓ → Type (ℓ-suc ℓ)
  Subset b a = (x : Tree ℓ) → Mem x b → Mem x a

  cut : {A : Type ℓ} → (A → Tree ℓ) → (A → Type ℓ) → Tree ℓ
  cut {A} f P = sup (Σ[ i ∈ A ] P i) (λ ip → f (ip .fst))

  boolCut : {A : Type ℓ} → (A → Tree ℓ) → (A → Bool) → Tree ℓ
  boolCut {A} f χ = sup (Σ[ i ∈ A ] χ i ≡ true) (λ ip → f (ip .fst))

  boolPower : Tree ℓ → Tree ℓ
  boolPower (sup A f) = sup (A → Bool) (boolCut f)

  cut-subset : {A : Type ℓ} (f : A → Tree ℓ) (P : A → Type ℓ)
    → Subset (cut f P) (sup A f)
  cut-subset f P x = mapNN (λ { ((i , _) , e) → i , e })

  boolCut-subset : {A : Type ℓ} (f : A → Tree ℓ) (χ : A → Bool)
    → Subset (boolCut f χ) (sup A f)
  boolCut-subset f χ x = mapNN (λ { ((i , _) , e) → i , e })

  boolPower-sound : (a b : Tree ℓ) → Mem b (boolPower a) → Subset b a
  boolPower-sound (sup A f) b mb x mx = mem-stable x (sup A f)
    (mapNN (λ { (χ , e) → boolCut-subset f χ x
      (mem-right x b (boolCut f χ) e mx) }) mb)

  module _ {A : Type ℓ} (f : A → Tree ℓ) (b : Tree ℓ) where
    chosen-mask : ((i : A) → Dec (Mem (f i) b)) → A → Bool
    chosen-mask d i = Dec→Bool (d i)

    chosen-cut : (d : (i : A) → Dec (Mem (f i) b))
      → Subset b (sup A f) → Eq b (boolCut f (chosen-mask d))
    chosen-cut d sub = extensionality b (boolCut f (chosen-mask d)) λ x →
      (λ mb → mapNN (λ { (i , e) →
        (i , mark-in (d i) (mem-left x (f i) b e mb)) , e }) (sub x mb)) ,
      (λ mc → mem-stable x b (mapNN (λ { ((i , p) , e) →
        mem-left (f i) x b (eq-sym x (f i) e) (mark-out (d i) p) }) mc))

    boolPower-complete : NN ((i : A) → Dec (Mem (f i) b))
      → Subset b (sup A f) → Mem b (boolPower (sup A f))
    boolPower-complete nnd sub = mapNN
      (λ d → chosen-mask d , chosen-cut d sub) nnd

  DecisionShift : (A : Type ℓ) → Type (ℓ-suc ℓ)
  DecisionShift A = (P : A → Type ℓ)
    → ((i : A) → NN (Dec (P i))) → NN ((i : A) → Dec (P i))

  boolPower-from-shift : {A : Type ℓ} (f : A → Tree ℓ)
    → DecisionShift A → (b : Tree ℓ) → Subset b (sup A f)
    → Mem b (boolPower (sup A f))
  boolPower-from-shift f shift b = boolPower-complete f b
    (shift (λ i → Mem (f i) b) (λ i → pointwise-decision (Mem (f i) b)))

  StableDecisions : (A : Type ℓ) → Type (ℓ-suc ℓ)
  StableDecisions A = (P : A → Type ℓ)
    → ((i : A) → NN (P i) → P i) → NN ((i : A) → Dec (P i))

  boolPower-from-stable-decisions : {A : Type ℓ} (f : A → Tree ℓ)
    → StableDecisions A → (b : Tree ℓ) → Subset b (sup A f)
    → Mem b (boolPower (sup A f))
  boolPower-from-stable-decisions f decide b = boolPower-complete f b
    (decide (λ i → Mem (f i) b) (λ i → mem-stable (f i) b))

  canonical-subset : (a b : Tree ℓ) → Subset b a
    → Eq b (separate a (λ x → Mem x b))
  canonical-subset a b sub = extensionality b (separate a (λ x → Mem x b)) λ x →
    (λ mb → separation (λ y → Mem y b) (λ y → mem-stable y b)
      (λ y z → mem-left y z b) a x .snd (sub x mb , mb)) ,
    (λ mc → separation (λ y → Mem y b) (λ y → mem-stable y b)
      (λ y z → mem-left y z b) a x .fst mc .snd)

  module _ {A : Type ℓ} (f : A → Tree ℓ)
    (injective : (i j : A) → Eq (f i) (f j) → i ≡ j) where

    cut-at : (P : A → Type ℓ) → ((i : A) → NN (P i) → P i)
      → (i : A) → Mem (f i) (cut f P) → P i
    cut-at P stable i m = stable i (mapNN
      (λ { ((j , p) , e) → subst P (sym (injective i j e)) p }) m)

    boolCut-at : (χ : A → Bool) → (i : A)
      → Mem (f i) (boolCut f χ) → χ i ≡ true
    boolCut-at χ i m = decided-stable (χ i ≟ true) (mapNN
      (λ { ((j , p) , e) → subst (λ k → χ k ≡ true)
        (sym (injective i j e)) p }) m)

    equality-decides : (P : A → Type ℓ) → ((i : A) → NN (P i) → P i)
      → (χ : A → Bool) → Eq (cut f P) (boolCut f χ)
      → (i : A) → Dec (P i)
    equality-decides P stable χ e i with χ i ≟ true
    ... | yes t = yes (cut-at P stable i
      (mem-right (f i) (boolCut f χ) (cut f P)
        (eq-sym (cut f P) (boolCut f χ) e)
        (unitNN ((i , t) , eq-refl (f i)))))
    ... | no nt = no (λ p → nt (boolCut-at χ i
      (mem-right (f i) (cut f P) (boolCut f χ) e
        (unitNN ((i , p) , eq-refl (f i))))))

    completeness-needs-simultaneous-decisions :
      ((b : Tree ℓ) → Subset b (sup A f) → Mem b (boolPower (sup A f)))
      → (P : A → Type ℓ) → ((i : A) → NN (P i) → P i)
      → NN ((i : A) → Dec (P i))
    completeness-needs-simultaneous-decisions complete P stable =
      mapNN (λ { (χ , e) → equality-decides P stable χ e })
        (complete (cut f P) (cut-subset f P))
