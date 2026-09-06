# The ordinal well-order, the Godel pair order and the finite base

This chapter carries three things the tree consumes: the strict
well-order `ordSWO` on the index of an ordinal, the Godel pair order
`_≺_` on the square of that index with its trichotomy, irreflexivity,
transitivity and well-foundedness, and the finite base `FiniteBase`,
which reads a member of omega as a numeral and moves between the index
of a numeral and `Fin`.

The ambient square law itself, the Mostowski collapse it ran through
and the `Init` restriction are retired to
`archive/src-2026-09-06/L/Ordinal/SquareLawAmbient.lagda.md`: nothing in
the tree consumed them.

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module L.Ordinal.SquareLaw {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ; regularityV; ∈-irrefl )
open import V.Model {ℓ} using ( ω-specV; numeralV; numeralV≡# )
open import V.Presentation {ℓ} using ( member; fiber; ↪-inj )
open import L.Constructible {ℓ} using ( IsOrd )
open import L.Ordinal {ℓ} using ( mem-ord; ∈#-elim )
open import V.Coding {ℓ} using ( #-inj′; #mono )
open import L.Ordinal.Linear {ℓ} lem using ( ord-tri )
open import L.Choice.Finite {ℓ} lem using ( natOrder )
open import L.WellOrder.Base {ℓₚ = ℓ-suc ℓ}
  using ( SWO; Tri; lt; eq; gt; leastOf; module SWO )

import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁ )
open import Cubical.Data.Sum using ( _⊎_; inl; inr )
open import Cubical.Data.Sigma using ( Σ≡Prop; ΣPathP )
open import Cubical.Data.Nat using ( _·_ )
import Cubical.Data.Fin.Base as FB
open import Cubical.Data.Fin.Properties using ( factorEquiv; pigeonhole )
open import Cubical.Data.Nat.Order using ( _<_; isProp≤; ≤-refl )
open import Cubical.Foundations.Equiv using ( equivFun; invEq; retEq )
open import Cubical.Foundations.HLevels using ( isProp× )
open import Cubical.HITs.CumulativeHierarchy.Properties
  using ( ⟪_⟫; ⟪_⟫↪ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet )
open InfinitySet using ( #_; ω )
open import Cubical.Induction.WellFounded using ( Acc; acc; WellFounded )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ
```

The lexicographic product of a strict well-order with a well-founded
relation, delivered here because today's tree has no combinator chapter
(the LJ-1.47 probe measured it separately).  Only well-foundedness of
the product is consumed, so only well-foundedness is built.

```agda
connex : {ℓc : Level} {A : Type ℓc} (w : SWO A) (a b : A)
       → (SWO._<∙_ w a b → Empty.⊥) → (SWO._<∙_ w b a → Empty.⊥) → a ≡ b
connex w a b ¬ab ¬ba with SWO.tri∙ w a b
... | lt h = Empty.rec (¬ab h)
... | eq p = p
... | gt h = Empty.rec (¬ba h)


module _ {ℓx ℓy : Level} {X : Type ℓx} {Y : Type ℓy} (u : SWO X)
         (_<ᵥ_ : Y → Y → Type (ℓ-suc ℓ)) (wfv : WellFounded _<ᵥ_) where

  private
    module U = SWO u

  _≺×_ : X × Y → X × Y → Type (ℓ-suc ℓ)
  (a , x) ≺× (b , y) =
    (a U.<∙ b) ⊎ (((a U.<∙ b) → Empty.⊥) × ((b U.<∙ a) → Empty.⊥) × (x <ᵥ y))

  private
    accProd : (a : X) → Acc U._<∙_ a → (x : Y) → Acc _<ᵥ_ x → Acc _≺×_ (a , x)
    accProd a (acc ru) = inner
      where
      inner : (x : Y) → Acc _<ᵥ_ x → Acc _≺×_ (a , x)
      inner x (acc rv) = acc λ where
        (b , y) (inl h) → accProd b (ru b h) y (wfv y)
        (b , y) (inr (¬ba , ¬ab , h)) →
          subst (λ z → Acc _≺×_ (z , y)) (sym (connex u b a ¬ba ¬ab))
            (inner y (rv y h))

  prodWF : WellFounded _≺×_
  prodWF (a , x) = accProd a (U.wf∙ a) x (wfv x)

```

## The order on the index

The membership order on the index of an ordinal, its trichotomy from
`ord-tri` and its well-foundedness from regularity on V.

```agda
module _ (α : S) (oα : IsOrd α) where

  _≺₁_ : ⟪ α ⟫ → ⟪ α ⟫ → Type (ℓ-suc ℓ)
  m ≺₁ n = ⟪ α ⟫↪ m ∈ᵗ ⟪ α ⟫↪ n

  ord-inord : (m : ⟪ α ⟫) → IsOrd (⟪ α ⟫↪ m)
  ord-inord m = mem-ord {A = α} oα (⟪ α ⟫↪ m) (member α m)

  tri₁ : (m n : ⟪ α ⟫) → Tri (m ≺₁ n) (m ≡ n) (n ≺₁ m)
  tri₁ m n = go (ord-tri (⟪ α ⟫↪ m) (ord-inord m) (⟪ α ⟫↪ n) (ord-inord n))
    where
    go : (⟨ ⟪ α ⟫↪ m ∈ˢ ⟪ α ⟫↪ n ⟩
          ⊎ ((⟪ α ⟫↪ m ≡ ⟪ α ⟫↪ n) ⊎ ⟨ ⟪ α ⟫↪ n ∈ˢ ⟪ α ⟫↪ m ⟩))
       → Tri (m ≺₁ n) (m ≡ n) (n ≺₁ m)
    go (inl h)       = lt h
    go (inr (inl p)) = eq (↪-inj {a = α} p)
    go (inr (inr h)) = gt h

  irr₁ : (m : ⟪ α ⟫) → (m ≺₁ m → Empty.⊥)
  irr₁ m h = ∈-irrefl (⟪ α ⟫↪ m) h

  trans₁ : (m n k : ⟪ α ⟫) → m ≺₁ n → n ≺₁ k → m ≺₁ k
  trans₁ m n k h h' = ord-inord k .fst h h'

  acc₁ : (m : ⟪ α ⟫) → Acc _∈ᵗ_ (⟪ α ⟫↪ m) → Acc _≺₁_ m
  acc₁ m (acc r) = acc (λ n n≺m → acc₁ n (r (⟪ α ⟫↪ n) n≺m))

  wf₁ : WellFounded _≺₁_
  wf₁ m = acc₁ m (regularityV (⟪ α ⟫↪ m))

  ordSWO : SWO ⟪ α ⟫
  ordSWO = record
    { _<∙_   = _≺₁_
    ; tri∙   = tri₁
    ; irr∙   = irr₁
    ; trans∙ = trans₁
    ; wf∙    = wf₁ }


```

The maximum on the index, the Godel pair order it grades, and the
well-foundedness of that order through the lexicographic product.

```agda
  _≤₁_ : ⟪ α ⟫ → ⟪ α ⟫ → Type (ℓ-suc ℓ)
  m ≤₁ n = (m ≺₁ n) ⊎ (m ≡ n)

  maxGo : (m n : ⟪ α ⟫) → Tri (m ≺₁ n) (m ≡ n) (n ≺₁ m) → ⟪ α ⟫
  maxGo m n (lt _) = n
  maxGo m n (eq _) = m
  maxGo m n (gt _) = m

  maxOrd : ⟪ α ⟫ → ⟪ α ⟫ → ⟪ α ⟫
  maxOrd m n = maxGo m n (tri₁ m n)

  max-spec : (m n : ⟪ α ⟫) → (m ≤₁ maxOrd m n) × (n ≤₁ maxOrd m n)
  max-spec m n = go (tri₁ m n)
    where
    go : (t : Tri (m ≺₁ n) (m ≡ n) (n ≺₁ m))
       → (m ≤₁ maxGo m n t) × (n ≤₁ maxGo m n t)
    go (lt h) = inl h , inr refl
    go (eq p) = inr refl , inr (sym p)
    go (gt h) = inr refl , inl h

  Pair : Type ℓ
  Pair = ⟪ α ⟫ × ⟪ α ⟫

  _≺_ : Pair → Pair → Type (ℓ-suc ℓ)
  (a , b) ≺ (c , d) =
    (maxOrd a b ≺₁ maxOrd c d)
      ⊎ ((maxOrd a b ≡ maxOrd c d) × ((a ≺₁ c) ⊎ ((a ≡ c) × (b ≺₁ d))))

  tri≺ : (p q : Pair) → Tri (p ≺ q) (p ≡ q) (q ≺ p)
  tri≺ (a , b) (c , d) = M-case (tri₁ (maxOrd a b) (maxOrd c d))
    where
    Y-case : (e : maxOrd a b ≡ maxOrd c d) (f : a ≡ c)
           → Tri (b ≺₁ d) (b ≡ d) (d ≺₁ b)
           → Tri ((a , b) ≺ (c , d)) ((a , b) ≡ (c , d)) ((c , d) ≺ (a , b))
    Y-case e f (lt h) = lt (inr (e , inr (f , h)))
    Y-case e f (gt h) = gt (inr (sym e , inr (sym f , h)))
    Y-case e f (eq g) = eq (cong₂ _,_ f g)

    X-case : (e : maxOrd a b ≡ maxOrd c d)
           → Tri (a ≺₁ c) (a ≡ c) (c ≺₁ a)
           → Tri ((a , b) ≺ (c , d)) ((a , b) ≡ (c , d)) ((c , d) ≺ (a , b))
    X-case e (lt h) = lt (inr (e , inl h))
    X-case e (gt h) = gt (inr (sym e , inl h))
    X-case e (eq f) = Y-case e f (tri₁ b d)

    M-case : Tri (maxOrd a b ≺₁ maxOrd c d)
                 (maxOrd a b ≡ maxOrd c d)
                 (maxOrd c d ≺₁ maxOrd a b)
           → Tri ((a , b) ≺ (c , d)) ((a , b) ≡ (c , d)) ((c , d) ≺ (a , b))
    M-case (lt h) = lt (inl h)
    M-case (gt h) = gt (inl h)
    M-case (eq e) = X-case e (tri₁ a c)

  irr≺ : (p : Pair) → (p ≺ p → Empty.⊥)
  irr≺ (a , b) (inl h)              = irr₁ (maxOrd a b) h
  irr≺ (a , b) (inr (e , inl h))    = irr₁ a h
  irr≺ (a , b) (inr (e , inr (f , h))) = irr₁ b h

  trans≺ : (p q r : Pair) → p ≺ q → q ≺ r → p ≺ r
  trans≺ (a , b) (c , d) (e , f) = goM
    where
    M₁ = maxOrd a b
    M₂ = maxOrd c d
    M₃ = maxOrd e f

    goY : (b ≺₁ d) → (d ≺₁ f) → (b ≺₁ f)
    goY = trans₁ b d f

    goX : ((a ≺₁ c) ⊎ ((a ≡ c) × (b ≺₁ d)))
        → ((c ≺₁ e) ⊎ ((c ≡ e) × (d ≺₁ f)))
        → ((a ≺₁ e) ⊎ ((a ≡ e) × (b ≺₁ f)))
    goX (inl h) (inl h') = inl (trans₁ a c e h h')
    goX (inl h) (inr (e₂ , _)) = inl (subst (λ w → a ≺₁ w) e₂ h)
    goX (inr (e₁ , _)) (inl h') = inl (subst (λ w → w ≺₁ e) (sym e₁) h')
    goX (inr (e₁ , s₁)) (inr (e₂ , s₂)) = inr (e₁ ∙ e₂ , goY s₁ s₂)

    goM : ((M₁ ≺₁ M₂) ⊎ ((M₁ ≡ M₂) × ((a ≺₁ c) ⊎ ((a ≡ c) × (b ≺₁ d)))))
        → ((M₂ ≺₁ M₃) ⊎ ((M₂ ≡ M₃) × ((c ≺₁ e) ⊎ ((c ≡ e) × (d ≺₁ f)))))
        → ((M₁ ≺₁ M₃) ⊎ ((M₁ ≡ M₃) × ((a ≺₁ e) ⊎ ((a ≡ e) × (b ≺₁ f)))))
    goM (inl h) (inl h') = inl (trans₁ M₁ M₂ M₃ h h')
    goM (inl h) (inr (e₂ , _)) = inl (subst (λ w → M₁ ≺₁ w) e₂ h)
    goM (inr (e₁ , _)) (inl h') = inl (subst (λ w → w ≺₁ M₃) (sym e₁) h')
    goM (inr (e₁ , s₁)) (inr (e₂ , s₂)) = inr (e₁ ∙ e₂ , goX s₁ s₂)

  f : Pair → ⟪ α ⟫ × (⟪ α ⟫ × ⟪ α ⟫)
  f (a , b) = maxOrd a b , (a , b)

  f-inj : {p q : Pair} → f p ≡ f q → p ≡ q
  f-inj {a , b} {c , d} e = cong snd e

  _≺²_ : (⟪ α ⟫ × ⟪ α ⟫) → (⟪ α ⟫ × ⟪ α ⟫) → Type (ℓ-suc ℓ)
  _≺²_ = _≺×_ ordSWO _≺₁_ wf₁

  wf² : WellFounded _≺²_
  wf² = prodWF ordSWO _≺₁_ wf₁

  _≺³_ : (⟪ α ⟫ × (⟪ α ⟫ × ⟪ α ⟫)) → (⟪ α ⟫ × (⟪ α ⟫ × ⟪ α ⟫)) → Type (ℓ-suc ℓ)
  _≺³_ = _≺×_ ordSWO _≺²_ wf²

  wf³ : WellFounded _≺³_
  wf³ = prodWF ordSWO _≺²_ wf²

  ¬<₁ : (m : ⟪ α ⟫) {n : ⟪ α ⟫} → m ≡ n → (m ≺₁ n → Empty.⊥)
  ¬<₁ m {n} q h = irr₁ m (subst (λ w → m ≺₁ w) (sym q) h)

  subrel : {p q : Pair} → p ≺ q → f p ≺³ f q
  subrel {a , b} {c , d} (inl h) =
    inl h
  subrel {a , b} {c , d} (inr (e , inl h)) =
    inr (¬<₁ (maxOrd a b) e , ¬<₁ (maxOrd c d) (sym e) , inl h)
  subrel {a , b} {c , d} (inr (e , inr (f , h))) =
    inr (¬<₁ (maxOrd a b) e , ¬<₁ (maxOrd c d) (sym e)
       , inr (¬<₁ a f , ¬<₁ c (sym f) , h))

  wf≺ : WellFounded _≺_
  wf≺ p = go (wf³ (f p))
    where
    go : {q : Pair} → Acc _≺³_ (f q) → Acc _≺_ q
    go {q} (acc r) = acc (λ q' q'≺q → go (r (f q') (subrel {q'} {q} q'≺q)))

```

## The finite base

```agda
module FiniteBase where

  P : (n : ℕ) (m : ⟪ # n ⟫) → ℕ → hProp (ℓ-suc ℓ)
  P n m k = ((k < n) × (⟪ # n ⟫↪ m ≡ # k))
          , isProp× isProp≤ (isSetS (⟪ # n ⟫↪ m) (# k))

  ω-mem→numeral : (β : S) → ⟨ β ∈ˢ ω ⟩ → ∥ Σ[ n ∈ ℕ ] (β ≡ # n) ∥₁
  ω-mem→numeral β β∈ω = PT.map hit (subst ⟨_⟩ (ω-specV β) β∈ω)
    where
    hit : Σ[ n ∈ Lift {ℓ-zero} {ℓ-suc ℓ} ℕ ] ⟨ β ≈ˢ numeralV (lower n) ⟩
        → Σ[ n ∈ ℕ ] (β ≡ # n)
    hit (n , p) = lower n , p ∙ numeralV≡# (lower n)

  toFin : (n : ℕ) → ⟪ # n ⟫ → FB.Fin n
  toFin n m = k , k<n
    where
    s = leastOf natOrder lem (P n m) (∈#-elim n (⟪ # n ⟫↪ m) (member (# n) m))
    k : ℕ
    k = fst s
    k<n : k < n
    k<n = fst (fst (snd s))

  toFin-spec : (n : ℕ) (m : ⟪ # n ⟫) → ⟪ # n ⟫↪ m ≡ # (fst (toFin n m))
  toFin-spec n m = snd (fst (snd s))
    where
    s = leastOf natOrder lem (P n m) (∈#-elim n (⟪ # n ⟫↪ m) (member (# n) m))

  toFin-inj : (n : ℕ) (m₁ m₂ : ⟪ # n ⟫) → toFin n m₁ ≡ toFin n m₂ → m₁ ≡ m₂
  toFin-inj n m₁ m₂ e = ↪-inj {a = # n}
    (toFin-spec n m₁ ∙ cong (λ k → # k) (cong fst e) ∙ sym (toFin-spec n m₂))

  fromFin : (n : ℕ) → FB.Fin n → ⟪ # n ⟫
  fromFin n (k , k<n) = fiber (# n) (#mono k n k<n) .fst

  fromFin-spec : (n : ℕ) (i : FB.Fin n) → ⟪ # n ⟫↪ (fromFin n i) ≡ # (fst i)
  fromFin-spec n (k , k<n) = fiber (# n) (#mono k n k<n) .snd

  fromFin-inj : (n : ℕ) (i₁ i₂ : FB.Fin n) → fromFin n i₁ ≡ fromFin n i₂ → i₁ ≡ i₂
  fromFin-inj n i₁ i₂ e = Σ≡Prop (λ _ → isProp≤)
    (#-inj′ (sym (fromFin-spec n i₁) ∙ cong (⟪ # n ⟫↪) e ∙ fromFin-spec n i₂))

  factor : (n : ℕ) → FB.Fin n × FB.Fin n → FB.Fin (n · n)
  factor n = equivFun (factorEquiv {n = n} {m = n})

  factor-inj : (n : ℕ) (x y : FB.Fin n × FB.Fin n)
             → factor n x ≡ factor n y → x ≡ y
  factor-inj n x y e =
    sym (retEq (factorEquiv {n = n} {m = n}) x)
      ∙ cong (invEq (factorEquiv {n = n} {m = n})) e
      ∙ retEq (factorEquiv {n = n} {m = n}) y

  no-inj-Fin : (n : ℕ) → (f : FB.Fin (suc n) → FB.Fin n)
             → ((x y : FB.Fin (suc n)) → f x ≡ f y → x ≡ y) → Empty.⊥
  no-inj-Fin n f finj = i#j (finj i j feq)
    where
    i = fst (pigeonhole (≤-refl {m = suc n}) f)
    j = fst (snd (pigeonhole (≤-refl {m = suc n}) f))
    prf = snd (snd (pigeonhole (≤-refl {m = suc n}) f))
    i#j = fst prf
    feq : f i ≡ f j
    feq = snd prf

  module AbstractChase (E : ℕ → Type ℓ)
                       (toFinE : (n : ℕ) → E n → FB.Fin n)
                       (toFinE-inj : (n : ℕ) (m₁ m₂ : E n) → toFinE n m₁ ≡ toFinE n m₂ → m₁ ≡ m₂)
                       (fromFinE : (n : ℕ) → FB.Fin n → E n)
                       (fromFinE-inj : (n : ℕ) (i₁ i₂ : FB.Fin n) → fromFinE n i₁ ≡ fromFinE n i₂ → i₁ ≡ i₂) where

    module NoInj (A : Type ℓ) (into : (m : ℕ) → E m → A)
                 (into-inj : (m : ℕ) (i₁ i₂ : E m) → into m i₁ ≡ into m i₂ → i₁ ≡ i₂) where

      no-inj : (n : ℕ) → (f : A → E n × E n)
             → ((x y : A) → f x ≡ f y → x ≡ y) → Empty.⊥
      no-inj n f finj = no-inj-Fin (n · n) g g-inj
        where
        g : FB.Fin (suc (n · n)) → FB.Fin (n · n)
        g i = factor n ( toFinE n (fst (f (into (suc (n · n)) (fromFinE (suc (n · n)) i))))
                       , toFinE n (snd (f (into (suc (n · n)) (fromFinE (suc (n · n)) i)))))
        g-inj : (x y : FB.Fin (suc (n · n))) → g x ≡ g y → x ≡ y
        g-inj x y e = fromFinE-inj (suc (n · n)) x y
          (into-inj (suc (n · n))
            (fromFinE (suc (n · n)) x) (fromFinE (suc (n · n)) y)
            (finj Xx Xy pair-eq))
          where
          Xx : A
          Xx = into (suc (n · n)) (fromFinE (suc (n · n)) x)
          Xy : A
          Xy = into (suc (n · n)) (fromFinE (suc (n · n)) y)
          p-eq : (toFinE n (fst (f Xx)) , toFinE n (snd (f Xx)))
               ≡ (toFinE n (fst (f Xy)) , toFinE n (snd (f Xy)))
          p-eq = factor-inj n
                   (toFinE n (fst (f Xx)) , toFinE n (snd (f Xx)))
                   (toFinE n (fst (f Xy)) , toFinE n (snd (f Xy))) e
          fst-eq : toFinE n (fst (f Xx)) ≡ toFinE n (fst (f Xy))
          fst-eq = cong fst p-eq
          snd-eq : toFinE n (snd (f Xx)) ≡ toFinE n (snd (f Xy))
          snd-eq = cong snd p-eq
          fst-eq′ : fst (f Xx) ≡ fst (f Xy)
          fst-eq′ = toFinE-inj n (fst (f Xx)) (fst (f Xy)) fst-eq
          snd-eq′ : snd (f Xx) ≡ snd (f Xy)
          snd-eq′ = toFinE-inj n (snd (f Xx)) (snd (f Xy)) snd-eq
          pair-eq : f Xx ≡ f Xy
          pair-eq = ΣPathP (fst-eq′ , snd-eq′)
```
