# Counting formulas

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import FOL.Syntax using
  ( Term; con; var; Formula; _∈̇_; _≐_; _∧̇_; _∨̇_; _⇒̇_; ¬̇_; ⊤̇; ⊥̇; ∃̇_; ∀̇_; ∀̇∈; ∃̇∈ )
open import FOL.Manipulation.Relabelling using ( mapTm; mapFo )
open import FOL.Manipulation.Parameters using ( countTm; countFo )
open import Cubical.Data.Nat using ( _+_; snotz )
import Cubical.Data.Empty as Empty

module FOL.Count {ℓ : Level} where
```

The count: formulas over K with one free variable inject into the disjoint
union over k of the parameter-free arity-k shapes paired with k-tuples of
constants. A constant occurrence becomes a marker variable in the shape;
the tuple lists the constants in traversal order, padded with one copy of
the first constant.

```agda
module Count (K : Type ℓ) where

```
```agda
  -- The boundary case: a formula with no constants closes the shape under
  -- ∃̇; erase removes the constants, and erase-inv re-enters the domain.
  plus-zero-l : {a b : ℕ} → a + b ≡ 0 → a ≡ 0
  plus-zero-l {zero} {b} p = refl
  plus-zero-l {suc a} {b} p = Empty.rec (snotz p)

  plus-zero-r : {a b : ℕ} → a + b ≡ 0 → b ≡ 0
  plus-zero-r {zero} {b} p = p
  plus-zero-r {suc a} {b} p = Empty.rec (snotz p)

  eraseTm : {n : ℕ} (t : Term K n) → countTm t ≡ 0 → Term (⊥* {ℓ}) n
  eraseTm (con a) p = Empty.rec {A = Term (⊥* {ℓ}) _} (snotz p)
  eraseTm (var i) _ = var i

  erase : {n : ℕ} (φ : Formula K n) → countFo φ ≡ 0 → Formula (⊥* {ℓ}) n
  erase (t ∈̇ u) p = eraseTm t (plus-zero-l p) ∈̇ eraseTm u (plus-zero-r p)
  erase (t ≐ u) p = eraseTm t (plus-zero-l p) ≐ eraseTm u (plus-zero-r p)
  erase (φ ∧̇ ψ) p = erase φ (plus-zero-l p) ∧̇ erase ψ (plus-zero-r p)
  erase (φ ∨̇ ψ) p = erase φ (plus-zero-l p) ∨̇ erase ψ (plus-zero-r p)
  erase (φ ⇒̇ ψ) p = erase φ (plus-zero-l p) ⇒̇ erase ψ (plus-zero-r p)
  erase (¬̇ φ) p = ¬̇ erase φ p
  erase ⊤̇ _ = ⊤̇
  erase ⊥̇ _ = ⊥̇
  erase (∃̇ φ) p = ∃̇ erase φ p
  erase (∀̇ φ) p = ∀̇ erase φ p
  erase (∀̇∈ t φ) p = ∀̇∈ (eraseTm t (plus-zero-l p)) (erase φ (plus-zero-r p))
  erase (∃̇∈ t φ) p = ∃̇∈ (eraseTm t (plus-zero-l p)) (erase φ (plus-zero-r p))

  eraseTm-inv : {n : ℕ} (t : Term K n) (p : countTm t ≡ 0)
              → mapTm Empty.rec* (eraseTm t p) ≡ t
  eraseTm-inv (con a) p = Empty.rec (snotz p)
  eraseTm-inv (var i) _ = refl

  erase-inv : {n : ℕ} (φ : Formula K n) (p : countFo φ ≡ 0)
            → mapFo Empty.rec* (erase φ p) ≡ φ
  erase-inv (t ∈̇ u) p =
    cong₂ _∈̇_ (eraseTm-inv t (plus-zero-l p)) (eraseTm-inv u (plus-zero-r p))
  erase-inv (t ≐ u) p =
    cong₂ _≐_ (eraseTm-inv t (plus-zero-l p)) (eraseTm-inv u (plus-zero-r p))
  erase-inv (φ ∧̇ ψ) p =
    cong₂ _∧̇_ (erase-inv φ (plus-zero-l p)) (erase-inv ψ (plus-zero-r p))
  erase-inv (φ ∨̇ ψ) p =
    cong₂ _∨̇_ (erase-inv φ (plus-zero-l p)) (erase-inv ψ (plus-zero-r p))
  erase-inv (φ ⇒̇ ψ) p =
    cong₂ _⇒̇_ (erase-inv φ (plus-zero-l p)) (erase-inv ψ (plus-zero-r p))
  erase-inv (¬̇ φ) p = cong ¬̇_ (erase-inv φ p)
  erase-inv ⊤̇ _ = refl
  erase-inv ⊥̇ _ = refl
  erase-inv (∃̇ φ) p = cong ∃̇_ (erase-inv φ p)
  erase-inv (∀̇ φ) p = cong ∀̇_ (erase-inv φ p)
  erase-inv (∀̇∈ t φ) p =
    cong₂ ∀̇∈ (eraseTm-inv t (plus-zero-l p)) (erase-inv φ (plus-zero-r p))
  erase-inv (∃̇∈ t φ) p =
    cong₂ ∃̇∈ (eraseTm-inv t (plus-zero-l p)) (erase-inv φ (plus-zero-r p))
```
