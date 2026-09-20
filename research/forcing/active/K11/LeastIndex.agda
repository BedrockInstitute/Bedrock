{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module K11.LeastIndex {ℓ} (lem : LEM ℓ) where

import Cubical.Data.Empty as Empty
open import Cubical.Data.Nat.Order
  using ( _<_ ; _≤_ ; ≤-refl ; Trichotomy ; _≟_
        ; ¬-<-zero ; pred-≤-pred ; lt ; eq ; gt )
open import Cubical.Data.Nat.Properties using ( snotz ; injSuc )
open import Cubical.Data.Sum using ( _⊎_ ; inl ; inr )
open import Cubical.Data.Sigma using ( Σ≡Prop )
open import Cubical.Foundations.HLevels using ( isProp× )
import Cubical.HITs.PropositionalTruncation as PT

open TruthAlgebra (hPropAlgebra ℓ)

Least : (P : ℕ → Ω) → Type ℓ
Least P = Σ[ n ∈ ℕ ] (⟨ P n ⟩ × ((m : ℕ) → m < n → ⟨ P m ⟩ → ⊥* {ℓ}))

least-fiber-prop : (P : ℕ → Ω) (n : ℕ)
  → isProp (⟨ P n ⟩ × ((m : ℕ) → m < n → ⟨ P m ⟩ → ⊥* {ℓ}))
least-fiber-prop P n =
  isProp× (snd (P n))
    (isPropΠ (λ m → isPropΠ (λ lm → isPropΠ (λ _ → isProp⊥* {ℓ}))))

isPropLeast : (P : ℕ → Ω) → isProp (Least P)
isPropLeast P (n , u) (n' , v) = Σ≡Prop (least-fiber-prop P) (branch (n ≟ n'))
  where
  branch : Trichotomy n n' → n ≡ n'
  branch (lt n<n') = Empty.rec* (snd v n n<n' (fst u))
  branch (eq n=n') = n=n'
  branch (gt n'<n) = Empty.rec* (snd u n' n'<n (fst v))

Excl : (P : ℕ → Ω) (n : ℕ) → Type ℓ
Excl P n = (m : ℕ) → m ≤ n → ⟨ P m ⟩ → ⊥* {ℓ}

excl-zero-with : (P : ℕ → Ω) → (⟨ P zero ⟩ → ⊥* {ℓ}) → Excl P zero
excl-zero-with P hn m (zero , p) h = Empty.rec* (hn (subst (λ z → ⟨ P z ⟩) p h))
excl-zero-with P hn m (suc k , p) h = Empty.rec (snotz p)

excl-suc : (P : ℕ → Ω) (n : ℕ)
  → Excl P n → (⟨ P (suc n) ⟩ → ⊥* {ℓ}) → Excl P (suc n)
excl-suc P n ex hn m (zero , p) h = hn (subst (λ z → ⟨ P z ⟩) p h)
excl-suc P n ex hn m (suc k , p) h = ex m (k , injSuc p) h

scan : (P : ℕ → Ω) (n : ℕ) → Least P ⊎ Excl P n
scan P zero with lem (P zero)
... | inl h = inl (zero , h , λ m lm → Empty.rec (¬-<-zero lm))
... | inr hn = inr (excl-zero-with P (λ h → Empty.rec (hn h)))
scan P (suc n) with scan P n
... | inl w = inl w
... | inr exn with lem (P (suc n))
...   | inl h = inl (suc n , h , λ m lm → exn m (pred-≤-pred lm))
...   | inr hn = inr (excl-suc P n exn (λ h → Empty.rec (hn h)))

bounded : (P : ℕ → Ω) (n : ℕ) → ⟨ P n ⟩ → Least P
bounded P n h with scan P n
... | inl w = w
... | inr exn = Empty.rec* (exn n ≤-refl h)

leastOf : (P : ℕ → Ω) → PT.∥ Σ[ n ∈ ℕ ] ⟨ P n ⟩ ∥₁ → Least P
leastOf P = PT.rec (isPropLeast P) (λ w → bounded P (fst w) (snd w))
