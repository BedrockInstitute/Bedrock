# Counting formulas

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import FOL.Syntax using
  ( Term; con; var; Formula; _∈̇_; _≐_; _∧̇_; _∨̇_; _⇒̇_; ¬̇_; ⊤̇; ⊥̇; ∃̇_; ∀̇_; ∀̇∈; ∃̇∈ )
open import FOL.Manipulation.Relabelling using ( mapTm; mapFo )
open import FOL.Manipulation.Parameters using ( countTm; countFo; constantsTm; constantsFo )
open import Cubical.Data.Nat using ( _+_; _·_; snotz; +-comm; +-suc; ·-comm; ·-suc; inj-m+ )
open import Cubical.Data.Nat.Order
  using ( _<_; _≤_; ≤-trans; ≤-k+; ≤-sucℕ; zero-≤; suc-≤-suc
        ; Trichotomy; _≟_; isProp≤; ¬m<m; ≤<-trans; <≤-trans; ≤-·k; <-·sk )
open Trichotomy
open import Cubical.Data.FinData using ( toℕ; fromℕ'; toℕ<n; toFromId' )
open import Cubical.Data.FinData.Properties using ( inj-toℕ )
open import Cubical.Data.Vec using () renaming ( _++_ to _++ᵥ_ )
open import Cubical.Data.List using ( List; []; _∷_; _++_ )
open import Cubical.Foundations.Prelude using ( J; transportRefl )
import Cubical.Data.Empty as Empty

module FOL.Count {ℓ : Level} where
```

```agda
-- The square-scheme pairing on ℕ: value (a + b)² + a sits in the interval
-- [s², s² + s] for s = a + b; consecutive intervals are disjoint.
pair : ℕ → ℕ → ℕ
pair a b = (a + b) · (a + b) + a

≤+ : (a b : ℕ) → a ≤ a + b
≤+ a b = b , +-comm b a

ss+1 : (s : ℕ) → s · s + s ≡ s · suc s
ss+1 s = +-comm (s · s) s ∙ sym (·-suc s s)

sq-lt : (s t : ℕ) → s < t → s · s + s < t · t
sq-lt s t s<t = <≤-trans
  (subst (λ w → w < t · suc s) (sym (ss+1 s)) (<-·sk {m = s} {n = t} {k = s} s<t))
  (subst (λ z → z ≤ t · t) (·-comm (suc s) t) (≤-·k {m = suc s} {n = t} {k = t} s<t))

lt-chain : (s t a c : ℕ) → a ≤ s → c ≤ t → s < t → s · s + a < t · t + c
lt-chain s t a c a≤s c≤t s<t =
  <≤-trans (≤<-trans (≤-k+ a≤s) (sq-lt s t s<t)) (c , +-comm c (t · t))

gt-chain : (s t a c : ℕ) → a ≤ s → c ≤ t → t < s → t · t + c < s · s + a
gt-chain s t a c a≤s c≤t t<s =
  <≤-trans (≤<-trans (≤-k+ c≤t) (sq-lt t s t<s)) (a , +-comm a (s · s))

sq-lemma : (s t a c : ℕ) → a ≤ s → c ≤ t → s · s + a ≡ t · t + c → s ≡ t
sq-lemma s t a c a≤s c≤t e with s ≟ t
... | eq s≡t = s≡t
... | lt s<t = Empty.rec (¬m<m {t · t + c}
                  (subst (λ w → w < t · t + c) e (lt-chain s t a c a≤s c≤t s<t)))
... | gt t<s = Empty.rec (¬m<m {s · s + a}
                  (subst (λ w → w < s · s + a) (sym e) (gt-chain s t a c a≤s c≤t t<s)))

pair-inj : (a b c d : ℕ) → pair a b ≡ pair c d → (a ≡ c) × (b ≡ d)
pair-inj a b c d p = go (sq-lemma (a + b) (c + d) a c (≤+ a b) (≤+ c d) p)
  where
  go : a + b ≡ c + d → (a ≡ c) × (b ≡ d)
  go s≡t =
    let a≡c = inj-m+ (subst (λ z → z · z + a ≡ (c + d) · (c + d) + c) s≡t p)
        b≡d = inj-m+ (cong (_+ b) (sym a≡c) ∙ s≡t)
    in a≡c , b≡d
```

```agda
-- Terms over the empty domain are variables only; the constant cases are
-- uninhabited. The formula code tags the twelve constructors.
tcode : ∀ {k} → Term (⊥* {ℓ}) k → ℕ
tcode (con x) = Empty.rec* {A = ℕ} x
tcode (var i) = toℕ i

tcode-inj : ∀ {k} (t u : Term (⊥* {ℓ}) k) → tcode t ≡ tcode u → t ≡ u
tcode-inj (con x) _ _ = Empty.rec* {A = con x ≡ _} x
tcode-inj _ (con y) _ = Empty.rec* {A = _ ≡ con y} y
tcode-inj (var i) (var j) p = cong var (inj-toℕ p)

code : ∀ {k} → Formula (⊥* {ℓ}) k → ℕ
code (t ∈̇ u)  = pair 0 (pair (tcode t) (tcode u))
code (t ≐ u)  = pair 1 (pair (tcode t) (tcode u))
code (a ∧̇ b)  = pair 2 (pair (code a) (code b))
code (a ∨̇ b)  = pair 3 (pair (code a) (code b))
code (a ⇒̇ b)  = pair 4 (pair (code a) (code b))
code (¬̇ a)    = pair 5 (code a)
code ⊤̇        = pair 6 0
code ⊥̇        = pair 7 0
code (∃̇ a)    = pair 8 (code a)
code (∀̇ a)    = pair 9 (code a)
code (∀̇∈ t a) = pair 10 (pair (tcode t) (code a))
code (∃̇∈ t a) = pair 11 (pair (tcode t) (code a))

tagOf : ∀ {k} → Formula (⊥* {ℓ}) k → ℕ
tagOf (t ∈̇ u)  = 0
tagOf (t ≐ u)  = 1
tagOf (a ∧̇ b)  = 2
tagOf (a ∨̇ b)  = 3
tagOf (a ⇒̇ b)  = 4
tagOf (¬̇ a)    = 5
tagOf ⊤̇        = 6
tagOf ⊥̇        = 7
tagOf (∃̇ a)    = 8
tagOf (∀̇ a)    = 9
tagOf (∀̇∈ t a) = 10
tagOf (∃̇∈ t a) = 11

payOf : ∀ {k} → Formula (⊥* {ℓ}) k → ℕ
payOf (t ∈̇ u)  = pair (tcode t) (tcode u)
payOf (t ≐ u)  = pair (tcode t) (tcode u)
payOf (a ∧̇ b)  = pair (code a) (code b)
payOf (a ∨̇ b)  = pair (code a) (code b)
payOf (a ⇒̇ b)  = pair (code a) (code b)
payOf (¬̇ a)    = code a
payOf ⊤̇        = 0
payOf ⊥̇        = 0
payOf (∃̇ a)    = code a
payOf (∀̇ a)    = code a
payOf (∀̇∈ t a) = pair (tcode t) (code a)
payOf (∃̇∈ t a) = pair (tcode t) (code a)

shape : ∀ {k} (φ : Formula (⊥* {ℓ}) k) → code φ ≡ pair (tagOf φ) (payOf φ)
shape (t ∈̇ u)  = refl
shape (t ≐ u)  = refl
shape (a ∧̇ b)  = refl
shape (a ∨̇ b)  = refl
shape (a ⇒̇ b)  = refl
shape (¬̇ a)    = refl
shape ⊤̇        = refl
shape ⊥̇        = refl
shape (∃̇ a)    = refl
shape (∀̇ a)    = refl
shape (∀̇∈ t a) = refl
shape (∃̇∈ t a) = refl
```

```agda
-- Match states what having a given tag looks like; the equation's tag halves
-- are compared by pair-inj, the witness moves the second formula to the first
-- constructor, and peel opens the payloads, recursing on the parts.
Match : ∀ {k} → ℕ → Formula (⊥* {ℓ}) k → Type ℓ
Match {k} 0  φ = Σ[ t ∈ Term (⊥* {ℓ}) k ] (Σ[ u ∈ Term (⊥* {ℓ}) k ] (φ ≡ (t ∈̇ u)))
Match {k} 1  φ = Σ[ t ∈ Term (⊥* {ℓ}) k ] (Σ[ u ∈ Term (⊥* {ℓ}) k ] (φ ≡ (t ≐ u)))
Match {k} 2  φ = Σ[ a ∈ Formula (⊥* {ℓ}) k ] (Σ[ b ∈ Formula (⊥* {ℓ}) k ] (φ ≡ (a ∧̇ b)))
Match {k} 3  φ = Σ[ a ∈ Formula (⊥* {ℓ}) k ] (Σ[ b ∈ Formula (⊥* {ℓ}) k ] (φ ≡ (a ∨̇ b)))
Match {k} 4  φ = Σ[ a ∈ Formula (⊥* {ℓ}) k ] (Σ[ b ∈ Formula (⊥* {ℓ}) k ] (φ ≡ (a ⇒̇ b)))
Match {k} 5  φ = Σ[ a ∈ Formula (⊥* {ℓ}) k ] (φ ≡ (¬̇ a))
Match     6  φ = φ ≡ ⊤̇
Match     7  φ = φ ≡ ⊥̇
Match {k} 8  φ = Σ[ a ∈ Formula (⊥* {ℓ}) (suc k) ] (φ ≡ (∃̇ a))
Match {k} 9  φ = Σ[ a ∈ Formula (⊥* {ℓ}) (suc k) ] (φ ≡ (∀̇ a))
Match {k} 10 φ = Σ[ t ∈ Term (⊥* {ℓ}) k ] (Σ[ a ∈ Formula (⊥* {ℓ}) (suc k) ] (φ ≡ ∀̇∈ t a))
Match {k} 11 φ = Σ[ t ∈ Term (⊥* {ℓ}) k ] (Σ[ a ∈ Formula (⊥* {ℓ}) (suc k) ] (φ ≡ ∃̇∈ t a))
Match     _  _ = Empty.⊥*

matches : ∀ {k} (φ : Formula (⊥* {ℓ}) k) → Match (tagOf φ) φ
matches (t ∈̇ u)  = t , (u , refl)
matches (t ≐ u)  = t , (u , refl)
matches (a ∧̇ b)  = a , (b , refl)
matches (a ∨̇ b)  = a , (b , refl)
matches (a ⇒̇ b)  = a , (b , refl)
matches (¬̇ a)    = a , refl
matches ⊤̇        = refl
matches ⊥̇        = refl
matches (∃̇ a)    = a , refl
matches (∀̇ a)    = a , refl
matches (∀̇∈ t a) = t , (a , refl)
matches (∃̇∈ t a) = t , (a , refl)

code-inj : ∀ {k} (φ ψ : Formula (⊥* {ℓ}) k) → code φ ≡ code ψ → φ ≡ ψ

private
  peel : ∀ {k} (φ ψ : Formula (⊥* {ℓ}) k) → Match (tagOf φ) ψ → payOf φ ≡ payOf ψ → φ ≡ ψ
  peel (t ∈̇ u) ψ (t' , (u' , q)) p =
    cong₂ _∈̇_ (tcode-inj t t' (pair-inj (tcode t) (tcode u) (tcode t') (tcode u') (p ∙ cong payOf q) .fst))
              (tcode-inj u u' (pair-inj (tcode t) (tcode u) (tcode t') (tcode u') (p ∙ cong payOf q) .snd)) ∙ sym q
  peel (t ≐ u) ψ (t' , (u' , q)) p =
    cong₂ _≐_ (tcode-inj t t' (pair-inj (tcode t) (tcode u) (tcode t') (tcode u') (p ∙ cong payOf q) .fst))
              (tcode-inj u u' (pair-inj (tcode t) (tcode u) (tcode t') (tcode u') (p ∙ cong payOf q) .snd)) ∙ sym q
  peel (a ∧̇ b) ψ (a' , (b' , q)) p =
    cong₂ _∧̇_ (code-inj a a' (pair-inj (code a) (code b) (code a') (code b') (p ∙ cong payOf q) .fst))
              (code-inj b b' (pair-inj (code a) (code b) (code a') (code b') (p ∙ cong payOf q) .snd)) ∙ sym q
  peel (a ∨̇ b) ψ (a' , (b' , q)) p =
    cong₂ _∨̇_ (code-inj a a' (pair-inj (code a) (code b) (code a') (code b') (p ∙ cong payOf q) .fst))
              (code-inj b b' (pair-inj (code a) (code b) (code a') (code b') (p ∙ cong payOf q) .snd)) ∙ sym q
  peel (a ⇒̇ b) ψ (a' , (b' , q)) p =
    cong₂ _⇒̇_ (code-inj a a' (pair-inj (code a) (code b) (code a') (code b') (p ∙ cong payOf q) .fst))
              (code-inj b b' (pair-inj (code a) (code b) (code a') (code b') (p ∙ cong payOf q) .snd)) ∙ sym q
  peel (¬̇ a) ψ (a' , q) p = cong ¬̇_ (code-inj a a' (p ∙ cong payOf q)) ∙ sym q
  peel ⊤̇ ψ q p = sym q
  peel ⊥̇ ψ q p = sym q
  peel (∃̇ a) ψ (a' , q) p = cong ∃̇_ (code-inj a a' (p ∙ cong payOf q)) ∙ sym q
  peel (∀̇ a) ψ (a' , q) p = cong ∀̇_ (code-inj a a' (p ∙ cong payOf q)) ∙ sym q
  peel (∀̇∈ t a) ψ (t' , (a' , q)) p =
    cong₂ ∀̇∈ (tcode-inj t t' (pair-inj (tcode t) (code a) (tcode t') (code a') (p ∙ cong payOf q) .fst))
             (code-inj a a' (pair-inj (tcode t) (code a) (tcode t') (code a') (p ∙ cong payOf q) .snd)) ∙ sym q
  peel (∃̇∈ t a) ψ (t' , (a' , q)) p =
    cong₂ ∃̇∈ (tcode-inj t t' (pair-inj (tcode t) (code a) (tcode t') (code a') (p ∙ cong payOf q) .fst))
             (code-inj a a' (pair-inj (tcode t) (code a) (tcode t') (code a') (p ∙ cong payOf q) .snd)) ∙ sym q

code-inj φ ψ e = peel φ ψ
  (subst (λ k → Match k ψ) (sym (tp .fst)) (matches ψ)) (tp .snd)
  where
  tp = pair-inj (tagOf φ) (payOf φ) (tagOf ψ) (payOf ψ) (sym (shape φ) ∙ e ∙ shape ψ)
```

```agda
-- The packaged shape count: per arity, the parameter-free formulas inject
-- into ℕ, with injectivity proved.
shape-count-inj : Σ[ f ∈ ((k : ℕ) → Formula (⊥* {ℓ}) k → ℕ) ]
                    (∀ {k} {φ ψ : Formula (⊥* {ℓ}) k} → f k φ ≡ f k ψ → φ ≡ ψ)
shape-count-inj = (λ k φ → code φ) , (λ {k} {φ} {ψ} p → code-inj φ ψ p)
```

```agda
-- The count: formulas over K with one free variable inject into the disjoint
-- union over k of the parameter-free arity-k shapes paired with k-tuples of
-- constants. A constant occurrence becomes a marker variable in the shape;
-- the tuple lists the constants in traversal order, padded with one copy of
-- the first constant.
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
