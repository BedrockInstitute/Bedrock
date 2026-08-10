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

  +-mono : (x y z : ℕ) → y < z → x + y < x + z
  +-mono x y z p = subst (λ w → w ≤ x + z) (+-suc x y) (≤-k+ {k = x} p)

  n<s→n≤s : {n s : ℕ} → n < s → n ≤ s
  n<s→n≤s {n} {s} p = ≤-trans (≤-sucℕ {n}) p

  +-suc-l : (e' e s : ℕ) → (suc e') + e + s ≡ suc (e' + e + s)
  +-suc-l e' e s = refl

  fit-suc : {n e' e s : ℕ} → n ≤ e' + e + s → suc n ≤ (suc e') + e + s
  fit-suc {n} {e'} {e} {s} p =
    subst (λ w → suc n ≤ w) (sym (+-suc-l e' e s)) (suc-≤-suc p)

  fit-suc2 : {n e e' m : ℕ} → n ≤ (e + e') + m → suc n ≤ (e + (suc e')) + m
  fit-suc2 {n} {e} {e'} {m} p =
    subst (λ w → suc n ≤ w) (sym (cong (λ x → x + m) (+-suc e e'))) (suc-≤-suc p)

  marker-bound : (e e' s : ℕ) → (e + e') + s ≡ e' + e + s
  marker-bound e e' s = cong (λ w → w + s) (+-comm e e')

  marker-lt : (e e' m s : ℕ) → m < s → (e + e') + m < e' + e + s
  marker-lt e e' m s m<s =
    subst (λ w → (e + e') + m < w) (marker-bound e e' s) (+-mono (e + e') m s m<s)

  head : {n : ℕ} → Vec K (suc n) → K
  head (a ∷ _) = a

  snoc : {n : ℕ} → Vec K n → K → Vec K (suc n)
  snoc [] a = a ∷ []
  snoc (x ∷ xs) a = x ∷ snoc xs a

  vecToList : {n : ℕ} → Vec K n → List K
  vecToList [] = []
  vecToList (x ∷ xs) = x ∷ vecToList xs

  vecToList-++ : {a b : ℕ} (xs : Vec K a) (ys : Vec K b)
               → vecToList (xs ++ᵥ ys) ≡ vecToList xs ++ vecToList ys
  vecToList-++ [] ys = refl
  vecToList-++ (x ∷ xs) ys = cong (x ∷_) (vecToList-++ xs ys)

  vecToList-snoc : {n : ℕ} (xs : Vec K n) (a : K)
                 → vecToList (snoc xs a) ≡ vecToList xs ++ (a ∷ [])
  vecToList-snoc [] a = refl
  vecToList-snoc (x ∷ xs) a = cong (x ∷_) (vecToList-snoc xs a)

  vecToList-subst : {n m : ℕ} (q : n ≡ m) (xs : Vec K n)
                  → vecToList (subst (Vec K) q xs) ≡ vecToList xs
  vecToList-subst {n} {m} q xs =
    J (λ m q → vecToList (subst (Vec K) q xs) ≡ vecToList xs)
      (cong vecToList (transportRefl xs)) q

  ++-assoc : (xs ys zs : List K) → (xs ++ ys) ++ zs ≡ xs ++ (ys ++ zs)
  ++-assoc [] ys zs = refl
  ++-assoc (x ∷ xs) ys zs = cong (x ∷_) (++-assoc xs ys zs)
```

```agda
  -- The encoding: a constant becomes the marker variable at (e + e') + m; a
  -- variable keeps its index, carried into the larger shape by the bound.
  encTm : (s m n e e' : ℕ) → m < s → n ≤ e' + e + s → Term K n → Term (⊥* {ℓ}) (e' + e + s)
  encTm s m n e e' m<s n≤s' (con _) =
    var (fromℕ' (e' + e + s) ((e + e') + m) (marker-lt e e' m s m<s))
  encTm s m n e e' m<s n≤s' (var i) =
    var (fromℕ' (e' + e + s) (toℕ i) (≤-trans (toℕ<n i) n≤s'))

  enc : (s m n e e' : ℕ) → m < s → n ≤ e' + e + s → Formula K n → Formula (⊥* {ℓ}) (e' + e + s)
  enc s m n e e' m<s n≤s' (t ∈̇ u)  = encTm s m n e e' m<s n≤s' t ∈̇ encTm s m n e e' m<s n≤s' u
  enc s m n e e' m<s n≤s' (t ≐ u)  = encTm s m n e e' m<s n≤s' t ≐ encTm s m n e e' m<s n≤s' u
  enc s m n e e' m<s n≤s' (φ ∧̇ ψ)  = enc s m n e e' m<s n≤s' φ ∧̇ enc s m n e e' m<s n≤s' ψ
  enc s m n e e' m<s n≤s' (φ ∨̇ ψ)  = enc s m n e e' m<s n≤s' φ ∨̇ enc s m n e e' m<s n≤s' ψ
  enc s m n e e' m<s n≤s' (φ ⇒̇ ψ)  = enc s m n e e' m<s n≤s' φ ⇒̇ enc s m n e e' m<s n≤s' ψ
  enc s m n e e' m<s n≤s' (¬̇ φ)    = ¬̇ enc s m n e e' m<s n≤s' φ
  enc s m n e e' m<s n≤s' ⊤̇        = ⊤̇
  enc s m n e e' m<s n≤s' ⊥̇        = ⊥̇
  enc s m n e e' m<s n≤s' (∃̇ φ) =
    let body = enc s m (suc n) e (suc e') m<s (fit-suc {n = n} {e' = e'} {e = e} {s = s} n≤s') φ
    in ∃̇ body
  enc s m n e e' m<s n≤s' (∀̇ φ) =
    let body = enc s m (suc n) e (suc e') m<s (fit-suc {n = n} {e' = e'} {e = e} {s = s} n≤s') φ
    in ∀̇ body
  enc s m n e e' m<s n≤s' (∀̇∈ t φ) =
    ∀̇∈ (encTm s m n e e' m<s n≤s' t) (enc s m (suc n) e (suc e') m<s (fit-suc {n = n} {e' = e'} {e = e} {s = s} n≤s') φ)
  enc s m n e e' m<s n≤s' (∃̇∈ t φ) =
    ∃̇∈ (encTm s m n e e' m<s n≤s' t) (enc s m (suc n) e (suc e') m<s (fit-suc {n = n} {e' = e'} {e = e} {s = s} n≤s') φ)
```

```agda
  -- The decode walks the shape with the constant list in hand; a variable at
  -- the marker becomes a constant, a variable below the marker is kept.
  decodeTm : (s m n e e' : ℕ) → m < s → m ≤ n → 1 ≤ n → Term (⊥* {ℓ}) (e' + e + s) → List K
           → Term K n × List K
  decodeTm s m n e e' m<s m≤n n≥1 (var i) cs with toℕ i ≟ ((e + e') + m)
  decodeTm s m n e e' m<s m≤n n≥1 (var i) [] | eq _ = var (fromℕ' n 0 n≥1) , []
  decodeTm s m n e e' m<s m≤n n≥1 (var i) (a ∷ cs) | eq _ = con a , cs
  decodeTm s m n e e' m<s m≤n n≥1 (var i) cs | lt _ with toℕ i ≟ n
  decodeTm s m n e e' m<s m≤n n≥1 (var i) cs | lt _ | lt q =
    var (fromℕ' n (toℕ i) q) , cs
  decodeTm s m n e e' m<s m≤n n≥1 (var i) cs | lt _ | _ = var (fromℕ' n 0 n≥1) , cs
  decodeTm s m n e e' m<s m≤n n≥1 (var i) cs | gt _ = var (fromℕ' n 0 n≥1) , cs
  decodeTm s m n e e' m<s m≤n n≥1 (con x) cs = Empty.rec* {A = Term K n × List K} x

  decode : (s m n e e' : ℕ) → m < s → m ≤ n → 1 ≤ n → Formula (⊥* {ℓ}) (e' + e + s) → List K
         → Formula K n × List K
  decode s m n e e' m<s m≤n n≥1 (t ∈̇ u) cs =
    let (t' , cs₁) = decodeTm s m n e e' m<s m≤n n≥1 t cs
        (u' , cs₂) = decodeTm s m n e e' m<s m≤n n≥1 u cs₁
    in t' ∈̇ u' , cs₂
  decode s m n e e' m<s m≤n n≥1 (t ≐ u) cs =
    let (t' , cs₁) = decodeTm s m n e e' m<s m≤n n≥1 t cs
        (u' , cs₂) = decodeTm s m n e e' m<s m≤n n≥1 u cs₁
    in t' ≐ u' , cs₂
  decode s m n e e' m<s m≤n n≥1 (φ ∧̇ ψ) cs =
    let (φ' , cs₁) = decode s m n e e' m<s m≤n n≥1 φ cs
        (ψ' , cs₂) = decode s m n e e' m<s m≤n n≥1 ψ cs₁
    in φ' ∧̇ ψ' , cs₂
  decode s m n e e' m<s m≤n n≥1 (φ ∨̇ ψ) cs =
    let (φ' , cs₁) = decode s m n e e' m<s m≤n n≥1 φ cs
        (ψ' , cs₂) = decode s m n e e' m<s m≤n n≥1 ψ cs₁
    in φ' ∨̇ ψ' , cs₂
  decode s m n e e' m<s m≤n n≥1 (φ ⇒̇ ψ) cs =
    let (φ' , cs₁) = decode s m n e e' m<s m≤n n≥1 φ cs
        (ψ' , cs₂) = decode s m n e e' m<s m≤n n≥1 ψ cs₁
    in φ' ⇒̇ ψ' , cs₂
  decode s m n e e' m<s m≤n n≥1 (¬̇ φ) cs =
    let (φ' , cs₁) = decode s m n e e' m<s m≤n n≥1 φ cs
    in ¬̇ φ' , cs₁
  decode s m n e e' m<s m≤n n≥1 ⊤̇ cs = ⊤̇ , cs
  decode s m n e e' m<s m≤n n≥1 ⊥̇ cs = ⊥̇ , cs
  decode s m n e e' m<s m≤n n≥1 (∃̇ φ) cs =
    let (φ' , cs₁) = decode s m (suc n) e (suc e') m<s (≤-trans m≤n (≤-sucℕ {n}))
                      (suc-≤-suc zero-≤) φ cs
    in ∃̇ φ' , cs₁
  decode s m n e e' m<s m≤n n≥1 (∀̇ φ) cs =
    let (φ' , cs₁) = decode s m (suc n) e (suc e') m<s (≤-trans m≤n (≤-sucℕ {n}))
                      (suc-≤-suc zero-≤) φ cs
    in ∀̇ φ' , cs₁
  decode s m n e e' m<s m≤n n≥1 (∀̇∈ t φ) cs =
    let (t' , cs₁) = decodeTm s m n e e' m<s m≤n n≥1 t cs
        (φ' , cs₂) = decode s m (suc n) e (suc e') m<s (≤-trans m≤n (≤-sucℕ {n}))
                      (suc-≤-suc zero-≤) φ cs₁
    in ∀̇∈ t' φ' , cs₂
  decode s m n e e' m<s m≤n n≥1 (∃̇∈ t φ) cs =
    let (t' , cs₁) = decodeTm s m n e e' m<s m≤n n≥1 t cs
        (φ' , cs₂) = decode s m (suc n) e (suc e') m<s (≤-trans m≤n (≤-sucℕ {n}))
                      (suc-≤-suc zero-≤) φ cs₁
    in ∃̇∈ t' φ' , cs₂
```

```agda
  decodeTm-marker : (s m n e e' : ℕ) → (m<s : m < s) → (m≤n : m ≤ n) → (n≥1 : 1 ≤ n)
                 → (i : Fin (e' + e + s)) → toℕ i ≡ (e + e') + m
                 → (a : K) (l : List K)
                 → decodeTm s m n e e' m<s m≤n n≥1 (var i) (a ∷ l) ≡ (con a , l)
  decodeTm-marker s m n e e' m<s m≤n n≥1 i q a l with toℕ i ≟ ((e + e') + m)
  decodeTm-marker s m n e e' m<s m≤n n≥1 i q a l | eq _ = refl
  decodeTm-marker s m n e e' m<s m≤n n≥1 i q a l | lt r =
    Empty.rec (¬m<m {toℕ i} (subst (λ w → suc (toℕ i) ≤ w) (sym q) r))
  decodeTm-marker s m n e e' m<s m≤n n≥1 i q a l | gt r =
    Empty.rec (¬m<m {toℕ i} (subst (λ w → suc w ≤ toℕ i) (sym q) r))

  decodeTm-kept : (s m n e e' : ℕ) → (m<s : m < s) → (m≤n : m ≤ n) → (n≥1 : 1 ≤ n)
               → (i : Fin (e' + e + s)) → (q1 : toℕ i < (e + e') + m) → (q2 : toℕ i < n)
               → (l : List K)
               → decodeTm s m n e e' m<s m≤n n≥1 (var i) l
                 ≡ (var (fromℕ' n (toℕ i) q2) , l)
  decodeTm-kept s m n e e' m<s m≤n n≥1 i q1 q2 l with toℕ i ≟ ((e + e') + m)
  decodeTm-kept s m n e e' m<s m≤n n≥1 i q1 q2 l | lt _ with toℕ i ≟ n
  decodeTm-kept s m n e e' m<s m≤n n≥1 i q1 q2 l | lt _ | lt r =
    cong₂ _,_
      (cong (λ q → var {K = K} (fromℕ' n (toℕ i) q)) (isProp≤ r q2)) refl
  decodeTm-kept s m n e e' m<s m≤n n≥1 i q1 q2 l | lt _ | eq r =
    Empty.rec (¬m<m {toℕ i} (subst (λ w → suc (toℕ i) ≤ w) (sym r) q2))
  decodeTm-kept s m n e e' m<s m≤n n≥1 i q1 q2 l | lt _ | gt r =
    Empty.rec (¬m<m {toℕ i} (≤-trans (≤-trans q2 (≤-sucℕ {n})) r))
  decodeTm-kept s m n e e' m<s m≤n n≥1 i q1 q2 l | eq r =
    Empty.rec (¬m<m {toℕ i} (subst (λ w → suc (toℕ i) ≤ w) (sym r) q1))
  decodeTm-kept s m n e e' m<s m≤n n≥1 i q1 q2 l | gt r =
    Empty.rec (¬m<m {toℕ i}
      (≤-trans (≤-trans q1 (≤-sucℕ {(e + e') + m})) r))
```

```agda
  decodeTm-inv : (s m n e e' : ℕ) → (m<s : m < s) → (n≤s' : n ≤ e' + e + s)
              → (m≤n : m ≤ n) → (n≤m : n ≤ (e + e') + m) → (n≥1 : 1 ≤ n)
              → (t : Term K n) (l : List K)
              → decodeTm s m n e e' m<s m≤n n≥1 (encTm s m n e e' m<s n≤s' t)
                  (vecToList (constantsTm t) ++ l) ≡ (t , l)
  decodeTm-inv s m n e e' m<s n≤s' m≤n n≤m n≥1 (con a) l =
    let idx = fromℕ' (e' + e + s) ((e + e') + m) (marker-lt e e' m s m<s)
    in decodeTm-marker s m n e e' m<s m≤n n≥1 idx
         (toFromId' (e' + e + s) ((e + e') + m) (marker-lt e e' m s m<s)) a l
  decodeTm-inv s m n e e' m<s n≤s' m≤n n≤m n≥1 (var i) l =
    let p = ≤-trans (toℕ<n i) n≤s'
        idx = fromℕ' (e' + e + s) (toℕ i) p
        t = toFromId' (e' + e + s) (toℕ i) p
        q1 = subst (λ w → w < (e + e') + m) (sym t)
               (≤-trans (toℕ<n i) n≤m)
        q2 = subst (λ w → w < n) (sym t) (toℕ<n i)
    in decodeTm-kept s m n e e' m<s m≤n n≥1 idx q1 q2 l
       ∙ cong (λ w → var w , l)
           (inj-toℕ (toFromId' n (toℕ idx) q2 ∙ t))

  decode-inv : (s m n e e' : ℕ) → (m<s : m < s) → (n≤s' : n ≤ e' + e + s)
             → (m≤n : m ≤ n) → (n≤m : n ≤ (e + e') + m) → (n≥1 : 1 ≤ n)
             → (φ : Formula K n) (l : List K)
             → decode s m n e e' m<s m≤n n≥1 (enc s m n e e' m<s n≤s' φ)
                 (vecToList (constantsFo φ) ++ l) ≡ (φ , l)
  decode-inv s m n e e' m<s n≤s' m≤n n≤m n≥1 (t ∈̇ u) l =
    cong (λ w → decode s m n e e' m<s m≤n n≥1 (encTm s m n e e' m<s n≤s' t ∈̇ encTm s m n e e' m<s n≤s' u) (w ++ l))
         (vecToList-++ (constantsTm t) (constantsTm u))
    ∙ cong (λ w → decode s m n e e' m<s m≤n n≥1 (encTm s m n e e' m<s n≤s' t ∈̇ encTm s m n e e' m<s n≤s' u) w)
         (++-assoc (vecToList (constantsTm t)) (vecToList (constantsTm u)) l)
    ∙ go
    where
    go : decode s m n e e' m<s m≤n n≥1
           (encTm s m n e e' m<s n≤s' t ∈̇ encTm s m n e e' m<s n≤s' u)
           (vecToList (constantsTm t) ++ (vecToList (constantsTm u) ++ l))
         ≡ (t ∈̇ u , l)
    go = let p = decodeTm-inv s m n e e' m<s n≤s' m≤n n≤m n≥1 t (vecToList (constantsTm u) ++ l)
             q = decodeTm-inv s m n e e' m<s n≤s' m≤n n≤m n≥1 u l
         in cong₂ _,_
              (cong₂ _∈̇_ (cong fst p)
                (cong fst (cong (decodeTm s m n e e' m<s m≤n n≥1 (encTm s m n e e' m<s n≤s' u)) (cong snd p) ∙ q)))
              (cong snd (cong (decodeTm s m n e e' m<s m≤n n≥1 (encTm s m n e e' m<s n≤s' u)) (cong snd p) ∙ q))
  decode-inv s m n e e' m<s n≤s' m≤n n≤m n≥1 (t ≐ u) l =
    cong (λ w → decode s m n e e' m<s m≤n n≥1 (encTm s m n e e' m<s n≤s' t ≐ encTm s m n e e' m<s n≤s' u) (w ++ l))
         (vecToList-++ (constantsTm t) (constantsTm u))
    ∙ cong (λ w → decode s m n e e' m<s m≤n n≥1 (encTm s m n e e' m<s n≤s' t ≐ encTm s m n e e' m<s n≤s' u) w)
         (++-assoc (vecToList (constantsTm t)) (vecToList (constantsTm u)) l)
    ∙ go
    where
    go : decode s m n e e' m<s m≤n n≥1
           (encTm s m n e e' m<s n≤s' t ≐ encTm s m n e e' m<s n≤s' u)
           (vecToList (constantsTm t) ++ (vecToList (constantsTm u) ++ l))
         ≡ (t ≐ u , l)
    go = let p = decodeTm-inv s m n e e' m<s n≤s' m≤n n≤m n≥1 t (vecToList (constantsTm u) ++ l)
             q = decodeTm-inv s m n e e' m<s n≤s' m≤n n≤m n≥1 u l
         in cong₂ _,_
              (cong₂ _≐_ (cong fst p)
                (cong fst (cong (decodeTm s m n e e' m<s m≤n n≥1 (encTm s m n e e' m<s n≤s' u)) (cong snd p) ∙ q)))
              (cong snd (cong (decodeTm s m n e e' m<s m≤n n≥1 (encTm s m n e e' m<s n≤s' u)) (cong snd p) ∙ q))
  decode-inv s m n e e' m<s n≤s' m≤n n≤m n≥1 (φ ∧̇ ψ) l =
    cong (λ w → decode s m n e e' m<s m≤n n≥1 (enc s m n e e' m<s n≤s' φ ∧̇ enc s m n e e' m<s n≤s' ψ) (w ++ l))
         (vecToList-++ (constantsFo φ) (constantsFo ψ))
    ∙ cong (λ w → decode s m n e e' m<s m≤n n≥1 (enc s m n e e' m<s n≤s' φ ∧̇ enc s m n e e' m<s n≤s' ψ) w)
         (++-assoc (vecToList (constantsFo φ)) (vecToList (constantsFo ψ)) l)
    ∙ go
    where
    go : decode s m n e e' m<s m≤n n≥1
           (enc s m n e e' m<s n≤s' φ ∧̇ enc s m n e e' m<s n≤s' ψ)
           (vecToList (constantsFo φ) ++ (vecToList (constantsFo ψ) ++ l))
         ≡ (φ ∧̇ ψ , l)
    go = let p = decode-inv s m n e e' m<s n≤s' m≤n n≤m n≥1 φ (vecToList (constantsFo ψ) ++ l)
             q = decode-inv s m n e e' m<s n≤s' m≤n n≤m n≥1 ψ l
         in cong₂ _,_
              (cong₂ _∧̇_ (cong fst p)
                (cong fst (cong (decode s m n e e' m<s m≤n n≥1 (enc s m n e e' m<s n≤s' ψ)) (cong snd p) ∙ q)))
              (cong snd (cong (decode s m n e e' m<s m≤n n≥1 (enc s m n e e' m<s n≤s' ψ)) (cong snd p) ∙ q))
  decode-inv s m n e e' m<s n≤s' m≤n n≤m n≥1 (φ ∨̇ ψ) l =
    cong (λ w → decode s m n e e' m<s m≤n n≥1 (enc s m n e e' m<s n≤s' φ ∨̇ enc s m n e e' m<s n≤s' ψ) (w ++ l))
         (vecToList-++ (constantsFo φ) (constantsFo ψ))
    ∙ cong (λ w → decode s m n e e' m<s m≤n n≥1 (enc s m n e e' m<s n≤s' φ ∨̇ enc s m n e e' m<s n≤s' ψ) w)
         (++-assoc (vecToList (constantsFo φ)) (vecToList (constantsFo ψ)) l)
    ∙ go
    where
    go : decode s m n e e' m<s m≤n n≥1
           (enc s m n e e' m<s n≤s' φ ∨̇ enc s m n e e' m<s n≤s' ψ)
           (vecToList (constantsFo φ) ++ (vecToList (constantsFo ψ) ++ l))
         ≡ (φ ∨̇ ψ , l)
    go = let p = decode-inv s m n e e' m<s n≤s' m≤n n≤m n≥1 φ (vecToList (constantsFo ψ) ++ l)
             q = decode-inv s m n e e' m<s n≤s' m≤n n≤m n≥1 ψ l
         in cong₂ _,_
              (cong₂ _∨̇_ (cong fst p)
                (cong fst (cong (decode s m n e e' m<s m≤n n≥1 (enc s m n e e' m<s n≤s' ψ)) (cong snd p) ∙ q)))
              (cong snd (cong (decode s m n e e' m<s m≤n n≥1 (enc s m n e e' m<s n≤s' ψ)) (cong snd p) ∙ q))
  decode-inv s m n e e' m<s n≤s' m≤n n≤m n≥1 (φ ⇒̇ ψ) l =
    cong (λ w → decode s m n e e' m<s m≤n n≥1 (enc s m n e e' m<s n≤s' φ ⇒̇ enc s m n e e' m<s n≤s' ψ) (w ++ l))
         (vecToList-++ (constantsFo φ) (constantsFo ψ))
    ∙ cong (λ w → decode s m n e e' m<s m≤n n≥1 (enc s m n e e' m<s n≤s' φ ⇒̇ enc s m n e e' m<s n≤s' ψ) w)
         (++-assoc (vecToList (constantsFo φ)) (vecToList (constantsFo ψ)) l)
    ∙ go
    where
    go : decode s m n e e' m<s m≤n n≥1
           (enc s m n e e' m<s n≤s' φ ⇒̇ enc s m n e e' m<s n≤s' ψ)
           (vecToList (constantsFo φ) ++ (vecToList (constantsFo ψ) ++ l))
         ≡ (φ ⇒̇ ψ , l)
    go = let p = decode-inv s m n e e' m<s n≤s' m≤n n≤m n≥1 φ (vecToList (constantsFo ψ) ++ l)
             q = decode-inv s m n e e' m<s n≤s' m≤n n≤m n≥1 ψ l
         in cong₂ _,_
              (cong₂ _⇒̇_ (cong fst p)
                (cong fst (cong (decode s m n e e' m<s m≤n n≥1 (enc s m n e e' m<s n≤s' ψ)) (cong snd p) ∙ q)))
              (cong snd (cong (decode s m n e e' m<s m≤n n≥1 (enc s m n e e' m<s n≤s' ψ)) (cong snd p) ∙ q))
  decode-inv s m n e e' m<s n≤s' m≤n n≤m n≥1 (¬̇ φ) l =
    go
    where
    go : decode s m n e e' m<s m≤n n≥1 (¬̇ enc s m n e e' m<s n≤s' φ)
           (vecToList (constantsFo φ) ++ l) ≡ (¬̇ φ , l)
    go = let p = decode-inv s m n e e' m<s n≤s' m≤n n≤m n≥1 φ l
         in cong₂ _,_ (cong ¬̇_ (cong fst p)) (cong snd p)
  decode-inv s m n e e' m<s n≤s' m≤n n≤m n≥1 ⊤̇ l = refl
  decode-inv s m n e e' m<s n≤s' m≤n n≤m n≥1 ⊥̇ l = refl
  decode-inv s m n e e' m<s n≤s' m≤n n≤m n≥1 (∃̇ φ) l =
    go
    where
    go : decode s m n e e' m<s m≤n n≥1 (∃̇ enc s m (suc n) e (suc e') m<s (fit-suc {n = n} {e' = e'} {e = e} {s = s} n≤s') φ)
           (vecToList (constantsFo φ) ++ l) ≡ (∃̇ φ , l)
    go = let p = decode-inv s m (suc n) e (suc e') m<s (fit-suc {n = n} {e' = e'} {e = e} {s = s} n≤s') (≤-trans m≤n (≤-sucℕ {n}))
                   (fit-suc2 {n = n} {e = e} {e' = e'} {m = m} n≤m) (suc-≤-suc zero-≤) φ l
         in cong₂ _,_ (cong ∃̇_ (cong fst p)) (cong snd p)
  decode-inv s m n e e' m<s n≤s' m≤n n≤m n≥1 (∀̇ φ) l =
    go
    where
    go : decode s m n e e' m<s m≤n n≥1 (∀̇ enc s m (suc n) e (suc e') m<s (fit-suc {n = n} {e' = e'} {e = e} {s = s} n≤s') φ)
           (vecToList (constantsFo φ) ++ l) ≡ (∀̇ φ , l)
    go = let p = decode-inv s m (suc n) e (suc e') m<s (fit-suc {n = n} {e' = e'} {e = e} {s = s} n≤s') (≤-trans m≤n (≤-sucℕ {n}))
                   (fit-suc2 {n = n} {e = e} {e' = e'} {m = m} n≤m) (suc-≤-suc zero-≤) φ l
         in cong₂ _,_ (cong ∀̇_ (cong fst p)) (cong snd p)
  decode-inv s m n e e' m<s n≤s' m≤n n≤m n≥1 (∀̇∈ t φ) l =
    cong (λ w → decode s m n e e' m<s m≤n n≥1 (∀̇∈ (encTm s m n e e' m<s n≤s' t) (enc s m (suc n) e (suc e') m<s (fit-suc {n = n} {e' = e'} {e = e} {s = s} n≤s') φ)) (w ++ l))
         (vecToList-++ (constantsTm t) (constantsFo φ))
    ∙ cong (λ w → decode s m n e e' m<s m≤n n≥1 (∀̇∈ (encTm s m n e e' m<s n≤s' t) (enc s m (suc n) e (suc e') m<s (fit-suc {n = n} {e' = e'} {e = e} {s = s} n≤s') φ)) w)
         (++-assoc (vecToList (constantsTm t)) (vecToList (constantsFo φ)) l)
    ∙ go
    where
    go : decode s m n e e' m<s m≤n n≥1
           (∀̇∈ (encTm s m n e e' m<s n≤s' t) (enc s m (suc n) e (suc e') m<s (fit-suc {n = n} {e' = e'} {e = e} {s = s} n≤s') φ))
           (vecToList (constantsTm t) ++ (vecToList (constantsFo φ) ++ l))
         ≡ (∀̇∈ t φ , l)
    go = let p = decodeTm-inv s m n e e' m<s n≤s' m≤n n≤m n≥1 t (vecToList (constantsFo φ) ++ l)
             q = decode-inv s m (suc n) e (suc e') m<s (fit-suc {n = n} {e' = e'} {e = e} {s = s} n≤s') (≤-trans m≤n (≤-sucℕ {n}))
                   (fit-suc2 {n = n} {e = e} {e' = e'} {m = m} n≤m) (suc-≤-suc zero-≤) φ l
         in cong₂ _,_
              (cong₂ ∀̇∈ (cong fst p)
                (cong fst (cong (decode s m (suc n) e (suc e') m<s (≤-trans m≤n (≤-sucℕ {n}))
                  (suc-≤-suc zero-≤) (enc s m (suc n) e (suc e') m<s (fit-suc {n = n} {e' = e'} {e = e} {s = s} n≤s') φ)) (cong snd p) ∙ q)))
              (cong snd (cong (decode s m (suc n) e (suc e') m<s (≤-trans m≤n (≤-sucℕ {n}))
                  (suc-≤-suc zero-≤) (enc s m (suc n) e (suc e') m<s (fit-suc {n = n} {e' = e'} {e = e} {s = s} n≤s') φ)) (cong snd p) ∙ q))
  decode-inv s m n e e' m<s n≤s' m≤n n≤m n≥1 (∃̇∈ t φ) l =
    cong (λ w → decode s m n e e' m<s m≤n n≥1 (∃̇∈ (encTm s m n e e' m<s n≤s' t) (enc s m (suc n) e (suc e') m<s (fit-suc {n = n} {e' = e'} {e = e} {s = s} n≤s') φ)) (w ++ l))
         (vecToList-++ (constantsTm t) (constantsFo φ))
    ∙ cong (λ w → decode s m n e e' m<s m≤n n≥1 (∃̇∈ (encTm s m n e e' m<s n≤s' t) (enc s m (suc n) e (suc e') m<s (fit-suc {n = n} {e' = e'} {e = e} {s = s} n≤s') φ)) w)
         (++-assoc (vecToList (constantsTm t)) (vecToList (constantsFo φ)) l)
    ∙ go
    where
    go : decode s m n e e' m<s m≤n n≥1
           (∃̇∈ (encTm s m n e e' m<s n≤s' t) (enc s m (suc n) e (suc e') m<s (fit-suc {n = n} {e' = e'} {e = e} {s = s} n≤s') φ))
           (vecToList (constantsTm t) ++ (vecToList (constantsFo φ) ++ l))
         ≡ (∃̇∈ t φ , l)
    go = let p = decodeTm-inv s m n e e' m<s n≤s' m≤n n≤m n≥1 t (vecToList (constantsFo φ) ++ l)
             q = decode-inv s m (suc n) e (suc e') m<s (fit-suc {n = n} {e' = e'} {e = e} {s = s} n≤s') (≤-trans m≤n (≤-sucℕ {n}))
                   (fit-suc2 {n = n} {e = e} {e' = e'} {m = m} n≤m) (suc-≤-suc zero-≤) φ l
         in cong₂ _,_
              (cong₂ ∃̇∈ (cong fst p)
                (cong fst (cong (decode s m (suc n) e (suc e') m<s (≤-trans m≤n (≤-sucℕ {n}))
                  (suc-≤-suc zero-≤) (enc s m (suc n) e (suc e') m<s (fit-suc {n = n} {e' = e'} {e = e} {s = s} n≤s') φ)) (cong snd p) ∙ q)))
              (cong snd (cong (decode s m (suc n) e (suc e') m<s (≤-trans m≤n (≤-sucℕ {n}))
                  (suc-≤-suc zero-≤) (enc s m (suc n) e (suc e') m<s (fit-suc {n = n} {e' = e'} {e = e} {s = s} n≤s') φ)) (cong snd p) ∙ q))
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

```agda
  strip∃ : Formula (⊥* {ℓ}) 0 → Formula K 1
  strip∃ (∃̇ φ) = mapFo Empty.rec* φ
  strip∃ _ = ⊤̇

  one<s : (s : ℕ) → 1 < suc (suc s)
  one<s s = suc-≤-suc (suc-≤-suc (zero-≤ {s}))

  codeByCount : (φ : Formula K 1) (n : ℕ) → (p : countFo φ ≡ n) → Σ[ k ∈ ℕ ] (Formula (⊥* {ℓ}) k × Vec K k)
  codeByCount φ zero p = 0 , (∃̇ erase φ p , [])
  codeByCount φ (suc m) p = suc (suc m)
    , (enc (suc (suc m)) 1 1 0 0 (one<s m) (n<s→n≤s (one<s m)) φ
    , snoc (subst (Vec K) p (constantsFo φ)) (head (subst (Vec K) p (constantsFo φ))))

  encode : Formula K 1 → Σ[ k ∈ ℕ ] (Formula (⊥* {ℓ}) k × Vec K k)
  encode φ = codeByCount φ (countFo φ) refl

  decode-total : Σ[ k ∈ ℕ ] (Formula (⊥* {ℓ}) k × Vec K k) → Formula K 1
  decode-total (zero , (φ , _)) = strip∃ φ
  decode-total (suc zero , _) = ⊤̇
  decode-total (suc (suc k) , (φ , cs)) =
    decode (suc (suc k)) 1 1 0 0 (one<s k) (suc-≤-suc zero-≤) (suc-≤-suc zero-≤)
      φ (vecToList cs) .fst

  encode-decode : (φ : Formula K 1) → decode-total (encode φ) ≡ φ
  encode-decode φ = go (countFo φ) (refl {x = countFo φ})
    where
    go : (n : ℕ) → (p : countFo φ ≡ n) → decode-total (codeByCount φ n p) ≡ φ
    go zero p = erase-inv φ p
    go (suc m) p =
      cong fst (cong (λ w → decode (suc (suc m)) 1 1 0 0 (one<s m) (suc-≤-suc zero-≤)
                          (suc-≤-suc zero-≤)
                          (enc (suc (suc m)) 1 1 0 0 (one<s m) (n<s→n≤s (one<s m)) φ) w)
               (vecToList-snoc (subst (Vec K) p (constantsFo φ))
                 (head (subst (Vec K) p (constantsFo φ)))
                ∙ cong (λ w → w ++ (head (subst (Vec K) p (constantsFo φ)) ∷ []))
                    (vecToList-subst p (constantsFo φ))))
      ∙ cong fst (decode-inv (suc (suc m)) 1 1 0 0 (one<s m)
               (n<s→n≤s {n = 1} {s = suc (suc m)} (one<s m))
               (suc-≤-suc zero-≤) (suc-≤-suc zero-≤) (suc-≤-suc zero-≤)
               φ (head (subst (Vec K) p (constantsFo φ)) ∷ []))

  encode-inj : {φ ψ : Formula K 1} → encode φ ≡ encode ψ → φ ≡ ψ
  encode-inj {φ} {ψ} p =
    sym (encode-decode φ) ∙ cong decode-total p ∙ encode-decode ψ

  count-inj : Σ[ f ∈ (Formula K 1 → Σ[ k ∈ ℕ ] (Formula (⊥* {ℓ}) k × Vec K k)) ]
                (∀ {φ ψ} → f φ ≡ f ψ → φ ≡ ψ)
  count-inj = encode , encode-inj
```

```agda
-- The composed count: the shape-count read through the count. The injection
-- keeps the shape in the image, so its injectivity is structural: dropping
-- the code recovers the count's own pair.
composed-count : {K : Type ℓ}
               → Σ[ f ∈ (Formula K 1 → Σ[ k ∈ ℕ ] (Formula (⊥* {ℓ}) k × (ℕ × Vec K k))) ]
                   ((φ ψ : Formula K 1) → f φ ≡ f ψ → φ ≡ ψ)
composed-count {K} = f , inj
  where
  module C = Count K
  f : Formula K 1 → Σ[ k ∈ ℕ ] (Formula (⊥* {ℓ}) k × (ℕ × Vec K k))
  f φ = let (k , (ψ , cs)) = fst C.count-inj φ in (k , (ψ , (code ψ , cs)))
  drop : Σ[ k ∈ ℕ ] (Formula (⊥* {ℓ}) k × (ℕ × Vec K k))
       → Σ[ k ∈ ℕ ] (Formula (⊥* {ℓ}) k × Vec K k)
  drop (k , (ψ , (n , cs))) = (k , (ψ , cs))
  inj : (φ ψ : Formula K 1) → f φ ≡ f ψ → φ ≡ ψ
  inj φ ψ e = snd C.count-inj {φ = φ} {ψ = ψ} (cong drop e)
```
