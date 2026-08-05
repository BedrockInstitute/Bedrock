```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module L.Ordinal.SquareLaw {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ; ∈-irrefl )
open import V.Model {ℓ}
  using ( ∈sucV-elim; ∈sucV-inl; self∈sucV; ω-specV; numeralV; numeralV≡# )
open import V.Presentation {ℓ} using ( member; fiber; ↪-inj )
open import L.Constructible {ℓ} using ( IsOrd )
open import L.Ordinal {ℓ}
  using ( mem-ord; suc-ord; ω-ord; #∈ω; ∈#-elim )
open import V.Coding {ℓ} using ( #-inj′; #mono )
open import L.Ordinal.Linear {ℓ} lem using ( ord-tri )
open import L.Ordinal.Pairing {ℓ} lem
  using ( ordSWO; _≺₁_; _≤₁_; maxOrd; max-spec; Pair; _≺_; tri≺; wf≺
        ; trans₁; godSWO; ≺-dec; colPick; colStep; col; col-compute; col-ord
        ; col-mono; col-inj; col-img; τ; module Pairing )
open import L.WellOrder.Base {ℓₚ = ℓ-suc ℓ}
  using ( SWO; Tri; lt; eq; gt; IsLeast; leastOf; natSWO; module SWO )

import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁; squash₁ )
open import Cubical.Data.Sum using ( _⊎_; inl; inr )
open import Cubical.Data.Sigma using ( Σ≡Prop; ΣPathP )
open import Cubical.Data.Nat using ( _·_; snotz; znots; injSuc )
import Cubical.Data.Fin.Base as FB
open import Cubical.Data.Fin.Properties using ( factorEquiv; pigeonhole )
open import Cubical.Data.Nat.Order using ( _<_; isProp≤; ≤-refl )
open import Cubical.Foundations.Equiv
  using ( equivFun; invEq; retEq; idEquiv; _≃_ )
open import Cubical.Foundations.Univalence using ( pathToEquiv )
open import Cubical.Foundations.HLevels using ( isProp× )
open import Cubical.HITs.CumulativeHierarchy.Base using ( sett )
open import Cubical.HITs.CumulativeHierarchy.Properties
  using ( _∈ₛ_; ∈∈ₛ; ⟪_⟫; ⟪_⟫↪; ∈ₛ⟪_⟫↪_ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ⋃_; union-ax; ∅; ∅-empty; module InfinitySet )
open InfinitySet using ( sucV; #_; ω )
open import Cubical.Induction.WellFounded using ( WellFounded; module WFI )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ
```

<!--en-->
## The finite base
<!--zh-->
## 有穷基底
<!--/-->

<!--en-->
The order core needs one fact about finite ordinals: an infinite ordinal's
index does not inject into the square of a finite ordinal. The proof is
counting. The small member type of the numeral `# n` has exactly `n` elements:
the members are the numerals below `# n`, read off by the delivered
membership characterization, and the index is recovered by the least-element
search, which absorbs the truncation into a proposition-valued goal. The two
directions give an injection of `⟪ # n ⟫` into the library's `Fin n` and back,
and the library's factorization and pigeonhole then bound the product and
refute the injection.
<!--zh-->
序核心需要一条关于有穷序数的事实：无穷序数的索引不单射注入有穷序数的平方。证明就是计数。数码 `# n` 的小成员类型恰有 `n` 个元素：成员是 `# n` 之下的数码，由交付的成员关系刻画读出，而索引由极小元搜索还原，后者把截断吸收进命题值的目标。两个方向给出 `⟪ # n ⟫` 到库中 `Fin n` 的单射及其逆，而库的分解与鸽巢原理随即界住积并反驳那条单射。
<!--/-->

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
    s = leastOf natSWO lem (P n m) (∈#-elim n (⟪ # n ⟫↪ m) (member (# n) m))
    k : ℕ
    k = fst s
    k<n : k < n
    k<n = fst (fst (snd s))

  toFin-spec : (n : ℕ) (m : ⟪ # n ⟫) → ⟪ # n ⟫↪ m ≡ # (fst (toFin n m))
  toFin-spec n m = snd (fst (snd s))
    where
    s = leastOf natSWO lem (P n m) (∈#-elim n (⟪ # n ⟫↪ m) (member (# n) m))

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
```

<!--en-->
With the counting in place, the exclusion lemma: an ordinal whose index
injects into the square of a numeral is a numeral. The infinite ordinals are
the ones the core will run on, and for them the injection is refuted by
chasing the injection through the count, the transitivity of `α`, and the
pigeonhole.
<!--zh-->
计数在手，便是排除引理：索引单射注入数码平方的序数是数码。核心将要跑在上面的恰是无穷序数，对它们，那条单射被如下步骤反驳：穿过计数、`α` 的传递性与鸽巢原理把单射追到底。
<!--/-->

```agda
  module _ (α : S) (oα : IsOrd α) (ω∈α : ⟨ ω ∈ˢ α ⟩) where

    numeral-in-α : (m : ℕ) → ⟨ (# m) ∈ˢ α ⟩
    numeral-in-α m = oα .fst (#∈ω m) ω∈α

    numeral-into-α : (m : ℕ) → ⟪ # m ⟫ → ⟪ α ⟫
    numeral-into-α m i = fiber α (oα .fst (member (# m) i) (numeral-in-α m)) .fst

    numeral-into-α-inj : (m : ℕ) (i₁ i₂ : ⟪ # m ⟫)
                       → numeral-into-α m i₁ ≡ numeral-into-α m i₂ → i₁ ≡ i₂
    numeral-into-α-inj m i₁ i₂ e = ↪-inj {a = # m}
      (sym (fiber α (oα .fst (member (# m) i₁) (numeral-in-α m)) .snd)
       ∙ cong (⟪ α ⟫↪) e
       ∙ fiber α (oα .fst (member (# m) i₂) (numeral-in-α m)) .snd)

    no-inj-finite : (n : ℕ) → (f : ⟪ α ⟫ → ⟪ # n ⟫ × ⟪ # n ⟫)
                  → ((x y : ⟪ α ⟫) → f x ≡ f y → x ≡ y) → Empty.⊥
    no-inj-finite n f finj = no-inj-Fin (n · n) g g-inj
      where
      g : FB.Fin (suc (n · n)) → FB.Fin (n · n)
      g i = factor n ( toFin n (fst (f (numeral-into-α (suc (n · n))
                            (fromFin (suc (n · n)) i))))
                     , toFin n (snd (f (numeral-into-α (suc (n · n))
                            (fromFin (suc (n · n)) i)))))
      g-inj : (x y : FB.Fin (suc (n · n))) → g x ≡ g y → x ≡ y
      g-inj x y e = fromFin-inj (suc (n · n)) x y
        (numeral-into-α-inj (suc (n · n))
          (fromFin (suc (n · n)) x) (fromFin (suc (n · n)) y)
          (finj Xx Xy pair-eq))
        where
        Xx : ⟪ α ⟫
        Xx = numeral-into-α (suc (n · n)) (fromFin (suc (n · n)) x)
        Xy : ⟪ α ⟫
        Xy = numeral-into-α (suc (n · n)) (fromFin (suc (n · n)) y)
        p-eq : (toFin n (fst (f Xx)) , toFin n (snd (f Xx)))
             ≡ (toFin n (fst (f Xy)) , toFin n (snd (f Xy)))
        p-eq = factor-inj n
                 (toFin n (fst (f Xx)) , toFin n (snd (f Xx)))
                 (toFin n (fst (f Xy)) , toFin n (snd (f Xy))) e
        fst-eq : toFin n (fst (f Xx)) ≡ toFin n (fst (f Xy))
        fst-eq = cong fst p-eq
        snd-eq : toFin n (snd (f Xx)) ≡ toFin n (snd (f Xy))
        snd-eq = cong snd p-eq
        fst-eq′ : fst (f Xx) ≡ fst (f Xy)
        fst-eq′ = toFin-inj n (fst (f Xx)) (fst (f Xy)) fst-eq
        snd-eq′ : snd (f Xx) ≡ snd (f Xy)
        snd-eq′ = toFin-inj n (snd (f Xx)) (snd (f Xy)) snd-eq
        pair-eq : f Xx ≡ f Xy
        pair-eq = ΣPathP (fst-eq′ , snd-eq′)

  finite-excl : (α : S) (oα : IsOrd α) (ω∈α : ⟨ ω ∈ˢ α ⟩)
              → (β : S) → IsOrd β → ⟨ β ∈ˢ ω ⟩
              → (f : ⟪ α ⟫ → ⟪ β ⟫ × ⟪ β ⟫)
              → ((x y : ⟪ α ⟫) → f x ≡ f y → x ≡ y) → Empty.⊥
  finite-excl α oα ω∈α β oβ β∈ω f finj =
    PT.rec Empty.isProp⊥ go (ω-mem→numeral β β∈ω)
    where
    go : Σ[ n ∈ ℕ ] (β ≡ # n) → Empty.⊥
    go (n , p) = no-inj-finite α oα ω∈α n f' finj'
      where
      e : ⟪ β ⟫ × ⟪ β ⟫ ≃ ⟪ # n ⟫ × ⟪ # n ⟫
      e = pathToEquiv (cong (λ w → ⟪ w ⟫ × ⟪ w ⟫) p)
      f' : ⟪ α ⟫ → ⟪ # n ⟫ × ⟪ # n ⟫
      f' x = equivFun e (f x)
      finj' : (x y : ⟪ α ⟫) → f' x ≡ f' y → x ≡ y
      finj' x y e' = finj x y
        (sym (retEq e (f x)) ∙ cong (invEq e) e' ∙ retEq e (f y))

open FiniteBase
```

<!--en-->
## The order core
<!--zh-->
## 序核心
<!--/-->

<!--en-->
The decisive step, measured in the probe: for an ordinal `α` that is closed
under successors, has the square law at every infinite member, injects into
no infinite member, and has no injection of its index into a finite member's
square, the order type of the canonical well-ordering injects into `α`. The
argument has four pieces. Containment puts every initial segment below a pair
inside the square of the successor of the pair's maximum. The descent reads
the collapse as an initial segment, extracting an honest witness through the
least-element search. The chain then pushes the segment into the maximum's
successor square and, by the smaller-ordinal square law, below `α`. The
exclusion refutes a collapse reaching `α`: the chain would inject `α` into a
member, which the hypotheses forbid; when that member is finite the same
chain stops at the finite exclusion instead. Boundedness then runs the
well-founded recursion that lands every collapse in `α`, and the order type,
the union of the successors of the collapses, injects.
<!--zh-->
决定性的一步，已在探针中测过：对闭于后继、在无穷成员处具备平方律、不单射注入任何无穷成员、且其索引不单射注入任何有穷成员之平方的序数 `α`，典范良序的序型单射注入 `α`。论证有四块。包含性把每一对之下的初始段放进该对最大值的后继之平方。下降经极小元搜索抽出诚实见证，把坍缩读成初始段。链随即把初始段推进最大值的后继之平方，再经更小序数的平方律压到 `α` 之下。排除反驳坍缩触及 `α`：那会让链把 `α` 注入某个成员，为假设所禁；当该成员有穷时，同一条链停在有穷排除处。有界性随即运行良基递归，使每个坍缩都落在 `α` 中，而序型，即坍缩后继之并，随之单射注入。
<!--/-->

```agda
module Core (α : S) (oα : IsOrd α)
  (α-limit : (γ : S) → ⟨ γ ∈ˢ α ⟩ → ⟨ sucV γ ∈ˢ α ⟩)
  (ih : (β : S) → IsOrd β → ⟨ β ∈ˢ α ⟩ → ⟨ ω ∈ˢ β ⟩
      → Σ[ f ∈ (⟪ β ⟫ × ⟪ β ⟫ → ⟪ β ⟫) ]
           ((x y : ⟪ β ⟫ × ⟪ β ⟫) → f x ≡ f y → x ≡ y))
  (no-inj-down : (β : S) → IsOrd β → ⟨ β ∈ˢ α ⟩ → ⟨ ω ∈ˢ β ⟩
               → (f : ⟪ α ⟫ → ⟪ β ⟫)
               → ((m n : ⟪ α ⟫) → f m ≡ f n → m ≡ n) → Empty.⊥)
  (finite-excl : (β : S) → IsOrd β → ⟨ β ∈ˢ ω ⟩
               → (f : ⟪ α ⟫ → ⟪ β ⟫ × ⟪ β ⟫)
               → ((m n : ⟪ α ⟫) → f m ≡ f n → m ≡ n) → Empty.⊥) where

  PairA : Type ℓ
  PairA = Pair α oα

  colA : PairA → S
  colA = col α oα

  _≺'_ : PairA → PairA → Type (ℓ-suc ℓ)
  _≺'_ = _≺_ α oα

  prec1 : ⟪ α ⟫ → ⟪ α ⟫ → Type (ℓ-suc ℓ)
  prec1 = _≺₁_ α oα

  leq : ⟪ α ⟫ → ⟪ α ⟫ → Type (ℓ-suc ℓ)
  leq = _≤₁_ α oα

  max' : ⟪ α ⟫ → ⟪ α ⟫ → ⟪ α ⟫
  max' = maxOrd α oα

  trans1 : (m n k : ⟪ α ⟫) → prec1 m n → prec1 n k → prec1 m k
  trans1 = trans₁ α oα

  tri' : (p q : PairA) → Tri (p ≺' q) (p ≡ q) (q ≺' p)
  tri' = tri≺ α oα

  cm : {p q : PairA} → p ≺' q → ⟨ colA p ∈ˢ colA q ⟩
  cm = col-mono α oα

  ci : {p q : PairA} → colA p ≡ colA q → p ≡ q
  ci = col-inj α oα

  cimg : (q : PairA) (b : S) → ⟨ b ∈ˢ colA q ⟩
       → ∥ Σ[ r ∈ PairA ] (colA r ≡ b) ∥₁
  cimg = col-img α oα

  colo : (p : PairA) → IsOrd (colA p)
  colo = col-ord α oα

  cc : (p : PairA) → colA p ≡ colStep α oα p (λ r _ → colA r)
  cc = col-compute α oα

  wf : WellFounded _≺'_
  wf = wf≺ α oα

  god : SWO PairA
  god = godSWO α oα

  ≺dec : (p q : PairA) → (p ≺' q) ⊎ ((p ≺' q) → Empty.⊥)
  ≺dec = ≺-dec α oα

  τA : S
  τA = τ α oα

  ≤₁→≺₁ : (m n k : ⟪ α ⟫) → leq m n → prec1 n k → prec1 m k
  ≤₁→≺₁ m n k (inl h) h' = trans1 m n k h h'
  ≤₁→≺₁ m n k (inr e) h' = subst (λ w → prec1 w k) (sym e) h'

  ≤₁-subst : (m n n' : ⟪ α ⟫) → leq m n → n ≡ n' → leq m n'
  ≤₁-subst m n n' (inl h) e = inl (subst (λ w → prec1 m w) e h)
  ≤₁-subst m n n' (inr q) e = inr (q ∙ e)

  ≤₁-into-suc : (m n : ⟪ α ⟫) → leq m n → ⟨ ⟪ α ⟫↪ m ∈ˢ sucV (⟪ α ⟫↪ n) ⟩
  ≤₁-into-suc m n (inl h) = ∈sucV-inl h
  ≤₁-into-suc m n (inr e) =
    subst (λ w → ⟨ ⟪ α ⟫↪ w ∈ˢ sucV (⟪ α ⟫↪ n) ⟩) (sym e) (self∈sucV (⟪ α ⟫↪ n))

  fst∈sucmax : {p q : PairA} → p ≺' q
             → ⟨ ⟪ α ⟫↪ (fst p) ∈ˢ sucV (⟪ α ⟫↪ (max' (fst q) (snd q))) ⟩
  fst∈sucmax {a , b} {c , d} (inl h) =
    ∈sucV-inl (≤₁→≺₁ a (max' a b) (max' c d) (max-spec α oα a b .fst) h)
  fst∈sucmax {a , b} {c , d} (inr (e , _)) =
    ≤₁-into-suc a (max' c d)
      (≤₁-subst a (max' a b) (max' c d) (max-spec α oα a b .fst) e)

  snd∈sucmax : {p q : PairA} → p ≺' q
             → ⟨ ⟪ α ⟫↪ (snd p) ∈ˢ sucV (⟪ α ⟫↪ (max' (fst q) (snd q))) ⟩
  snd∈sucmax {a , b} {c , d} (inl h) =
    ∈sucV-inl (≤₁→≺₁ b (max' a b) (max' c d) (max-spec α oα a b .snd) h)
  snd∈sucmax {a , b} {c , d} (inr (e , _)) =
    ≤₁-into-suc b (max' c d)
      (≤₁-subst b (max' a b) (max' c d) (max-spec α oα a b .snd) e)

  Pb : (b : S) → PairA → hProp (ℓ-suc ℓ)
  Pb b r = (colA r ≡ b) , isSetS (colA r) b

  colr≺ : {p : PairA} (b : S) → ⟨ b ∈ˢ colA p ⟩ → (r : PairA)
        → colA r ≡ b → r ≺' p
  colr≺ {p} b b∈ r e = go (tri' r p)
    where
    go : Tri (r ≺' p) (r ≡ p) (p ≺' r) → r ≺' p
    go (lt h) = h
    go (eq q) = Empty.rec
      (∈-irrefl (colA p)
        (subst (λ w → ⟨ w ∈ˢ colA p ⟩) (sym (cong colA (sym q) ∙ e)) b∈))
    go (gt h) = Empty.rec
      (∈-irrefl (colA p)
        (colo p .fst (cm h) (subst (λ w → ⟨ w ∈ˢ colA p ⟩) (sym e) b∈)))

  descent : (p : PairA) (b : S) → ⟨ b ∈ˢ colA p ⟩
          → Σ[ r ∈ PairA ] ((r ≺' p) × (colA r ≡ b))
  descent p b b∈ = fst s , (colr≺ b b∈ (fst s) (fst (snd s)) , fst (snd s))
    where
    s = leastOf god lem (Pb b) (cimg p b b∈)

  g : (p : PairA) (b : S) → ⟨ b ∈ˢ colA p ⟩ → PairA
  g p b b∈ = fst (descent p b b∈)

  g-inj : (p : PairA) {b b' : S} (hb : ⟨ b ∈ˢ colA p ⟩) (hb' : ⟨ b' ∈ˢ colA p ⟩)
        → g p b hb ≡ g p b' hb' → b ≡ b'
  g-inj p {b} {b'} hb hb' e =
    sym (snd (descent p b hb) .snd) ∙ cong colA e ∙ snd (descent p b' hb') .snd

  γp : PairA → S
  γp p = ⟪ α ⟫↪ (max' (fst p) (snd p))

  h₀ : (p : PairA) → (r : PairA) → r ≺' p → ⟪ sucV (γp p) ⟫ × ⟪ sucV (γp p) ⟫
  h₀ p r pr = (fiber β (fst∈sucmax {r} {p} pr) .fst
             , fiber β (snd∈sucmax {r} {p} pr) .fst)
    where
    β : S
    β = sucV (γp p)

  h₀-inj : (p : PairA) {r r' : PairA} (pr : r ≺' p) (pr' : r' ≺' p)
         → h₀ p r pr ≡ h₀ p r' pr' → r ≡ r'
  h₀-inj p {a , b} {a' , b'} pr pr' e = cong₂ _,_ ea eb
    where
    β : S
    β = sucV (γp p)
    ea : a ≡ a'
    ea = ↪-inj {a = α} (sym (fiber β (fst∈sucmax {a , b} {p} pr) .snd)
      ∙ cong (⟪ β ⟫↪) (cong fst e) ∙ fiber β (fst∈sucmax {a' , b'} {p} pr') .snd)
    eb : b ≡ b'
    eb = ↪-inj {a = α} (sym (fiber β (snd∈sucmax {a , b} {p} pr) .snd)
      ∙ cong (⟪ β ⟫↪) (cong snd e) ∙ fiber β (snd∈sucmax {a' , b'} {p} pr') .snd)

  comp₀ : (p : PairA) (e : colA p ≡ α) → ⟪ α ⟫ → ⟪ sucV (γp p) ⟫ × ⟪ sucV (γp p) ⟫
  comp₀ p e m = h₀ p (g p (⟪ α ⟫↪ m) (b∈ m))
                    (snd (descent p (⟪ α ⟫↪ m) (b∈ m)) .fst)
    where
    b∈ : (m : ⟪ α ⟫) → ⟨ ⟪ α ⟫↪ m ∈ˢ colA p ⟩
    b∈ m = subst (λ w → ⟨ ⟪ α ⟫↪ m ∈ˢ w ⟩) (sym e)
      (∈∈ₛ {a = ⟪ α ⟫↪ m} {b = α} .snd (∈ₛ⟪ α ⟫↪ m))

  comp₀-inj : (p : PairA) (e : colA p ≡ α) (m n : ⟪ α ⟫)
            → comp₀ p e m ≡ comp₀ p e n → m ≡ n
  comp₀-inj p e m n e' = ↪-inj {a = α}
    (g-inj p (b∈ m) (b∈ n)
      (h₀-inj p (snd (descent p (⟪ α ⟫↪ m) (b∈ m)) .fst)
                (snd (descent p (⟪ α ⟫↪ n) (b∈ n)) .fst) e'))
    where
    b∈ : (m : ⟪ α ⟫) → ⟨ ⟪ α ⟫↪ m ∈ˢ colA p ⟩
    b∈ m = subst (λ w → ⟨ ⟪ α ⟫↪ m ∈ˢ w ⟩) (sym e)
      (∈∈ₛ {a = ⟪ α ⟫↪ m} {b = α} .snd (∈ₛ⟪ α ⟫↪ m))

  β≠ω : (p : PairA) → sucV (γp p) ≡ ω → Empty.⊥
  β≠ω p e = PT.rec Empty.isProp⊥ go (ω-mem→numeral (γp p) γp∈ω)
    where
    γp∈ω : ⟨ γp p ∈ˢ ω ⟩
    γp∈ω = subst (λ w → ⟨ γp p ∈ˢ w ⟩) e (self∈sucV (γp p))
    go : Σ[ n ∈ ℕ ] (γp p ≡ # n) → Empty.⊥
    go (n , q) = ∈-irrefl ω
      (subst (λ w → ⟨ w ∈ˢ ω ⟩) (sym (cong sucV q) ∙ e) (#∈ω (suc n)))

  exclude : (p : PairA) → colA p ≡ α → Empty.⊥
  exclude p e = go (ord-tri β ordβ ω ω-ord)
    where
    γp∈α : ⟨ γp p ∈ˢ α ⟩
    γp∈α = ∈∈ₛ {a = γp p} {b = α} .snd (∈ₛ⟪ α ⟫↪ (max' (fst p) (snd p)))
    β : S
    β = sucV (γp p)
    ordβ : IsOrd β
    ordβ = suc-ord (mem-ord {A = α} oα (γp p) γp∈α)
    β∈α : ⟨ β ∈ˢ α ⟩
    β∈α = α-limit (γp p) γp∈α
    go : (⟨ β ∈ˢ ω ⟩ ⊎ ((β ≡ ω) ⊎ ⟨ ω ∈ˢ β ⟩)) → Empty.⊥
    go (inl β∈ω) = finite-excl β ordβ β∈ω (comp₀ p e) (comp₀-inj p e)
    go (inr (inl β≡ω)) = β≠ω p β≡ω
    go (inr (inr ω∈β)) = no-inj-down β ordβ β∈α ω∈β comp comp-inj
      where
      k : ⟪ β ⟫ × ⟪ β ⟫ → ⟪ β ⟫
      k = fst (ih β ordβ β∈α ω∈β)
      k-inj : (x y : ⟪ β ⟫ × ⟪ β ⟫) → k x ≡ k y → x ≡ y
      k-inj = snd (ih β ordβ β∈α ω∈β)
      comp : ⟪ α ⟫ → ⟪ β ⟫
      comp m = k (comp₀ p e m)
      comp-inj : (m n : ⟪ α ⟫) → comp m ≡ comp n → m ≡ n
      comp-inj m n e' = comp₀-inj p e m n (k-inj (comp₀ p e m) (comp₀ p e n) e')

  gₚ : (p : PairA) → PairA → S
  gₚ p r = colPick α oα p (λ r _ → colA r) r (≺dec r p)

  gₚ-inl : (p r : PairA) → (rp : r ≺' p) → gₚ p r ≡ sucV (colA r)
  gₚ-inl p r rp = go (≺dec r p)
    where
    go : (d : (r ≺' p) ⊎ ((r ≺' p) → Empty.⊥))
       → colPick α oα p (λ r _ → colA r) r d ≡ sucV (colA r)
    go (inl _) = refl
    go (inr ¬rp) = Empty.rec (¬rp rp)

  gₚ-inr : (p r : PairA) → ((r ≺' p) → Empty.⊥) → gₚ p r ≡ ∅
  gₚ-inr p r ¬rp = go (≺dec r p)
    where
    go : (d : (r ≺' p) ⊎ ((r ≺' p) → Empty.⊥))
       → colPick α oα p (λ r _ → colA r) r d ≡ ∅
    go (inl rp) = Empty.rec (¬rp rp)
    go (inr _) = refl

  colp⊆α : (p : PairA) → ((r : PairA) → r ≺' p → ⟨ colA r ∈ˢ α ⟩)
         → (x : S) → ⟨ x ∈ˢ colA p ⟩ → ⟨ x ∈ˢ α ⟩
  colp⊆α p rec x x∈ = PT.rec (snd (x ∈ˢ α)) viaUnion
    (union-ax (sett PairA (gₚ p)) x .fst
      (∈∈ₛ {a = x} {b = ⋃ (sett PairA (gₚ p))} .fst
        (subst (λ w → ⟨ x ∈ˢ w ⟩) (cc p) x∈)))
    where
    viaUnion : Σ[ v ∈ S ] (⟨ v ∈ₛ sett PairA (gₚ p) ⟩ × ⟨ x ∈ₛ v ⟩) → ⟨ x ∈ˢ α ⟩
    viaUnion (v , (v∈ₛsett , x∈ₛv)) = PT.rec (snd (x ∈ˢ α)) viaFiber
      (∈∈ₛ {a = v} {b = sett PairA (gₚ p)} .snd v∈ₛsett)
      where
      viaFiber : Σ[ r ∈ PairA ] (gₚ p r ≡ v) → ⟨ x ∈ˢ α ⟩
      viaFiber (r , gr≡v) = decide (≺dec r p)
        where
        x∈gr : ⟨ x ∈ₛ gₚ p r ⟩
        x∈gr = subst (λ w → ⟨ x ∈ₛ w ⟩) (sym gr≡v) x∈ₛv
        decide : (r ≺' p) ⊎ ((r ≺' p) → Empty.⊥) → ⟨ x ∈ˢ α ⟩
        decide (inl rp) = ∈sucV-elim {A = colA r} {x = x} (snd (x ∈ˢ α))
          (∈∈ₛ {a = x} {b = sucV (colA r)} .snd
            (subst (λ w → ⟨ x ∈ₛ w ⟩) (gₚ-inl p r rp) x∈gr))
          (λ x∈r → oα .fst x∈r (rec r rp))
          (λ x≡r → subst (λ w → ⟨ w ∈ˢ α ⟩) (sym x≡r) (rec r rp))
        decide (inr ¬rp) = Empty.rec
          (∅-empty x (subst (λ w → ⟨ x ∈ₛ w ⟩) (gₚ-inr p r ¬rp) x∈gr))

  col≤α : (p : PairA) → ((r : PairA) → r ≺' p → ⟨ colA r ∈ˢ α ⟩)
        → ⟨ colA p ∈ˢ α ⟩
  col≤α p rec = go (ord-tri (colA p) (colo p) α oα)
    where
    go : (⟨ colA p ∈ˢ α ⟩ ⊎ ((colA p ≡ α) ⊎ ⟨ α ∈ˢ colA p ⟩)) → ⟨ colA p ∈ˢ α ⟩
    go (inl h) = h
    go (inr (inl e)) = Empty.rec (exclude p e)
    go (inr (inr h)) = Empty.rec (∈-irrefl α (colp⊆α p rec α h))

  module WF = WFI wf

  col∈α : (p : PairA) → ⟨ colA p ∈ˢ α ⟩
  col∈α = WF.induction {P = λ p → ⟨ colA p ∈ˢ α ⟩} step
    where
    step : (p : PairA) → ((r : PairA) → r ≺' p → ⟨ colA r ∈ˢ α ⟩)
         → ⟨ colA p ∈ˢ α ⟩
    step p rec = col≤α p (λ r rp → rec r rp)

  τ⊆α : (x : S) → ⟨ x ∈ˢ τA ⟩ → ⟨ x ∈ˢ α ⟩
  τ⊆α x x∈τ = PT.rec (snd (x ∈ˢ α)) viaUnion
    (union-ax (sett PairA fτ) x .fst
      (∈∈ₛ {a = x} {b = τA} .fst x∈τ))
    where
    fτ : PairA → S
    fτ p = sucV (colA p)
    viaUnion : Σ[ v ∈ S ] (⟨ v ∈ₛ sett PairA fτ ⟩ × ⟨ x ∈ₛ v ⟩) → ⟨ x ∈ˢ α ⟩
    viaUnion (v , (v∈ₛsett , x∈ₛv)) = PT.rec (snd (x ∈ˢ α)) viaFiber
      (∈∈ₛ {a = v} {b = sett PairA fτ} .snd v∈ₛsett)
      where
      viaFiber : Σ[ p ∈ PairA ] (fτ p ≡ v) → ⟨ x ∈ˢ α ⟩
      viaFiber (p , fp≡v) = ∈sucV-elim {A = colA p} {x = x} (snd (x ∈ˢ α))
        (∈∈ₛ {a = x} {b = sucV (colA p)} .snd
          (subst (λ w → ⟨ x ∈ₛ w ⟩) (sym fp≡v) x∈ₛv))
        (λ x∈p → oα .fst x∈p (col∈α p))
        (λ x≡p → subst (λ w → ⟨ w ∈ˢ α ⟩) (sym x≡p) (col∈α p))

  opaque
    bound : ⟪ τA ⟫ → ⟪ α ⟫
    bound m = fiber α (τ⊆α (⟪ τA ⟫↪ m)
      (∈∈ₛ {a = ⟪ τA ⟫↪ m} {b = τA} .snd (∈ₛ⟪ τA ⟫↪ m))) .fst

    bound-inj : {m n : ⟪ τA ⟫} → bound m ≡ bound n → m ≡ n
    bound-inj {m} {n} e =
      ↪-inj {a = τA} (sym eq1 ∙ cong (⟪ α ⟫↪) e ∙ eq2)
      where
      eq1 : ⟪ α ⟫↪ (bound m) ≡ ⟪ τA ⟫↪ m
      eq1 = fiber α (τ⊆α (⟪ τA ⟫↪ m)
        (∈∈ₛ {a = ⟪ τA ⟫↪ m} {b = τA} .snd (∈ₛ⟪ τA ⟫↪ m))) .snd
      eq2 : ⟪ α ⟫↪ (bound n) ≡ ⟪ τA ⟫↪ n
      eq2 = fiber α (τ⊆α (⟪ τA ⟫↪ n)
        (∈∈ₛ {a = ⟪ τA ⟫↪ n} {b = τA} .snd (∈ₛ⟪ τA ⟫↪ n))) .snd
```

<!--en-->
## The cardinal of an ordinal
<!--zh-->
## 序数的基数
<!--/-->

<!--en-->
The reduction names the least ordinal equinumerous with `α`: the least member
of `sucV α` admitting a bijection of its index with `⟪ α ⟫`, found by the
least-element search. The search returns the ordinal honestly, together with
the minimality that no smaller member is equinumerous. What it does not
return, honestly, is the bijection itself: the predicate is a truncation, and
the search's output is propositional, so the witness it carries is the
truncated one. This is the extraction risk the report records; the chapter
uses the cardinal for the two facts that follow, and the transfer is stated
with the honest bijection as a hypothesis rather than silently assumed.
<!--zh-->
归约点名与 `α` 等势的最小序数：`sucV α` 中索引与 `⟪ α ⟫` 双射的最小成员，由极小元搜索找到。搜索诚实地返回该序数，连同极小性：没有更小的成员与之等势。它并不诚实地返回双射本身：谓词是截断，搜索的输出是命题值的，故它携带的见证是截断的。这正是报告所记录的那个提取风险；本章用基数做下面两件事，而转移以诚实双射为假设陈述，而非默然假定。
<!--/-->

```agda
module Card (α : S) (oα : IsOrd α) where

  Eq : S → Type ℓ
  Eq γ = ⟪ α ⟫ ≃ ⟪ γ ⟫

  EqP : S → hProp ℓ
  EqP γ = ∥ Eq γ ∥₁ , squash₁

  EqP' : ⟪ sucV α ⟫ → hProp ℓ
  EqP' γ = EqP (⟪ sucV α ⟫↪ γ)

  w : SWO (⟪ sucV α ⟫)
  w = ordSWO (sucV α) (suc-ord oα)

  least : Σ[ γ ∈ ⟪ sucV α ⟫ ] IsLeast w EqP' γ
  least = leastOf w lem EqP'
    (∣ fiber (sucV α) (self∈sucV α) .fst , ∣ idEquiv ⟪ α ⟫ ∣₁ ∣₁)

  γ-card : ⟪ sucV α ⟫
  γ-card = fst least

  κ : S
  κ = ⟪ sucV α ⟫↪ γ-card

  oκ : IsOrd κ
  oκ = mem-ord {A = sucV α} (suc-ord oα) κ (member (sucV α) γ-card)

  κ∈sα : ⟨ κ ∈ˢ sucV α ⟩
  κ∈sα = member (sucV α) γ-card

  κ-min : (b : ⟪ sucV α ⟫) → ⟨ EqP' b ⟩ → (SWO._<∙_ w b γ-card → Empty.⊥)
  κ-min = snd (snd least)
```

<!--en-->
## The shift
<!--zh-->
## 平移
<!--/-->

<!--en-->
An infinite ordinal is equinumerous with its successor: the top element is
shifted to zero, each numeral to its successor, and everything else stays.
The injection is what the successor step of the square law consumes. The
three cases are decided by membership in `ω` and equality with the top; the
numeral index is recovered by the least-element search, as in the finite
base. Injectivity is the case analysis on the two values, with the two
membership facts of `ω` separating the numerals from the rest.
<!--zh-->
无穷序数与它的后继等势：顶元素平移到零，每个数码平移到其后继，其余不动。这条单射正是平方律后继步所消费的东西。三种情形由是否属于 `ω` 以及与顶是否相等来判定；数码的序号由极小元搜索还原，同有穷基底一样。单射性是对两个取值的分情形，`ω` 的两条成员关系把数码与其余分开。
<!--/-->

```agda
module Shift (γ : S) (oγ : IsOrd γ) (ω∈γ : ⟨ ω ∈ˢ γ ⟩) where

  ∅∈γ : ⟨ ∅ ∈ˢ γ ⟩
  ∅∈γ = oγ .fst (#∈ω 0) ω∈γ

  #+1∈γ : (k : ℕ) → ⟨ (# (suc k)) ∈ˢ γ ⟩
  #+1∈γ k = oγ .fst (#∈ω (suc k)) ω∈γ

  NP : (v : S) → ℕ → hProp (ℓ-suc ℓ)
  NP v k = (v ≡ # k) , isSetS v (# k)

  numeralOf : (v : S) → ⟨ v ∈ˢ ω ⟩ → ℕ
  numeralOf v v∈ω = fst (leastOf natSWO lem (NP v) (ω-mem→numeral v v∈ω))

  numeralOf-spec : (v : S) (v∈ω : ⟨ v ∈ˢ ω ⟩) → v ≡ # (numeralOf v v∈ω)
  numeralOf-spec v v∈ω = fst (snd (leastOf natSWO lem (NP v) (ω-mem→numeral v v∈ω)))

  numeralOf-uniq : (v : S) (p q : ⟨ v ∈ˢ ω ⟩) → numeralOf v p ≡ numeralOf v q
  numeralOf-uniq v p q = #-inj′ (sym (numeralOf-spec v p) ∙ numeralOf-spec v q)

  v-of : ⟪ sucV γ ⟫ → S
  v-of m = ⟪ sucV γ ⟫↪ m

  v-in-γ : (m : ⟪ sucV γ ⟫) → (⟨ v-of m ∈ˢ ω ⟩ → Empty.⊥) → ((v-of m ≡ γ) → Empty.⊥)
         → ⟨ v-of m ∈ˢ γ ⟩
  v-in-γ m ¬ω ¬γ = ∈sucV-elim (snd (v-of m ∈ˢ γ)) (member (sucV γ) m)
    (λ q → q) (λ q → Empty.rec (¬γ q))

  γ∉ω : ⟨ γ ∈ˢ ω ⟩ → Empty.⊥
  γ∉ω γ∈ω = PT.rec Empty.isProp⊥ go (ω-mem→numeral γ γ∈ω)
    where
    go : Σ[ n ∈ ℕ ] (γ ≡ # n) → Empty.⊥
    go (n , q) = ∈-irrefl ω (ω-ord .fst (subst (λ w → ⟨ ω ∈ˢ w ⟩) q ω∈γ) (#∈ω n))

  shift-dec : (m : ⟪ sucV γ ⟫)
            → ⟨ v-of m ∈ˢ ω ⟩ ⊎ (⟨ v-of m ∈ˢ ω ⟩ → Empty.⊥)
            → (v-of m ≡ γ) ⊎ ((v-of m ≡ γ) → Empty.⊥) → ⟪ γ ⟫
  shift-dec m (inl v∈ω) _ = fiber γ (#+1∈γ (numeralOf (v-of m) v∈ω)) .fst
  shift-dec m (inr _) (inl v≡γ) = fiber γ ∅∈γ .fst
  shift-dec m (inr ¬v∈ω) (inr ¬v≡γ) = fiber γ (v-in-γ m ¬v∈ω ¬v≡γ) .fst

  shift : ⟪ sucV γ ⟫ → ⟪ γ ⟫
  shift m = shift-dec m (lem (v-of m ∈ˢ ω)) (lem ((v-of m ≡ γ) , isSetS (v-of m) γ))

  shift-top : (m : ⟪ sucV γ ⟫) → (v-of m ≡ γ) → ⟪ γ ⟫↪ (shift m) ≡ ∅
  shift-top m v≡γ = go (lem (v-of m ∈ˢ ω)) (lem ((v-of m ≡ γ) , isSetS (v-of m) γ))
    where
    go : (d : ⟨ v-of m ∈ˢ ω ⟩ ⊎ (⟨ v-of m ∈ˢ ω ⟩ → Empty.⊥))
       → (e : (v-of m ≡ γ) ⊎ ((v-of m ≡ γ) → Empty.⊥))
       → ⟪ γ ⟫↪ (shift-dec m d e) ≡ ∅
    go (inl v∈ω) _ = Empty.rec (γ∉ω (subst (λ w → ⟨ w ∈ˢ ω ⟩) v≡γ v∈ω))
    go (inr _) (inl _) = fiber γ ∅∈γ .snd
    go (inr ¬v∈ω) (inr ¬v≡γ) = Empty.rec (¬v≡γ v≡γ)

  shift-num : (m : ⟪ sucV γ ⟫) (v∈ω : ⟨ v-of m ∈ˢ ω ⟩)
            → ⟪ γ ⟫↪ (shift m) ≡ # (suc (numeralOf (v-of m) v∈ω))
  shift-num m v∈ω = go (lem (v-of m ∈ˢ ω)) (lem ((v-of m ≡ γ) , isSetS (v-of m) γ))
    where
    go : (d : ⟨ v-of m ∈ˢ ω ⟩ ⊎ (⟨ v-of m ∈ˢ ω ⟩ → Empty.⊥))
       → (e : (v-of m ≡ γ) ⊎ ((v-of m ≡ γ) → Empty.⊥))
       → ⟪ γ ⟫↪ (shift-dec m d e) ≡ # (suc (numeralOf (v-of m) v∈ω))
    go (inl v∈ω') _ =
      fiber γ (#+1∈γ (numeralOf (v-of m) v∈ω')) .snd
        ∙ cong (λ k → # (suc k)) (numeralOf-uniq (v-of m) v∈ω' v∈ω)
    go (inr ¬v∈ω) _ = Empty.rec (¬v∈ω v∈ω)

  shift-other : (m : ⟪ sucV γ ⟫) (¬v∈ω : ⟨ v-of m ∈ˢ ω ⟩ → Empty.⊥)
              (¬v≡γ : (v-of m ≡ γ) → Empty.⊥)
            → ⟪ γ ⟫↪ (shift m) ≡ v-of m
  shift-other m ¬v∈ω ¬v≡γ = go (lem (v-of m ∈ˢ ω)) (lem ((v-of m ≡ γ) , isSetS (v-of m) γ))
    where
    go : (d : ⟨ v-of m ∈ˢ ω ⟩ ⊎ (⟨ v-of m ∈ˢ ω ⟩ → Empty.⊥))
       → (e : (v-of m ≡ γ) ⊎ ((v-of m ≡ γ) → Empty.⊥))
       → ⟪ γ ⟫↪ (shift-dec m d e) ≡ v-of m
    go (inl v∈ω) _ = Empty.rec (¬v∈ω v∈ω)
    go (inr _) (inl v≡γ) = Empty.rec (¬v≡γ v≡γ)
    go (inr x₁) (inr x) = fiber γ (v-in-γ m x₁ x) .snd

  shift-inj : (m₁ m₂ : ⟪ sucV γ ⟫) → shift m₁ ≡ shift m₂ → m₁ ≡ m₂
  shift-inj m₁ m₂ e = go (lem (v₁ ∈ˢ ω)) (lem ((v₁ ≡ γ) , isSetS v₁ γ))
                          (lem (v₂ ∈ˢ ω)) (lem ((v₂ ≡ γ) , isSetS v₂ γ))
    where
    v₁ : S
    v₁ = v-of m₁
    v₂ : S
    v₂ = v-of m₂
    eqv : ⟪ γ ⟫↪ (shift m₁) ≡ ⟪ γ ⟫↪ (shift m₂)
    eqv = cong (⟪ γ ⟫↪) e
    v₁≡v₂ : v₁ ≡ v₂ → m₁ ≡ m₂
    v₁≡v₂ q = ↪-inj {a = sucV γ} q
    go : ⟨ v₁ ∈ˢ ω ⟩ ⊎ (⟨ v₁ ∈ˢ ω ⟩ → Empty.⊥)
       → (v₁ ≡ γ) ⊎ ((v₁ ≡ γ) → Empty.⊥)
       → ⟨ v₂ ∈ˢ ω ⟩ ⊎ (⟨ v₂ ∈ˢ ω ⟩ → Empty.⊥)
       → (v₂ ≡ γ) ⊎ ((v₂ ≡ γ) → Empty.⊥) → m₁ ≡ m₂
    go (inl a₁) _ (inl a₂) _ = v₁≡v₂
      (numeralOf-spec v₁ a₁ ∙ cong (λ k → # k) (injSuc (#-inj′
        (sym (shift-num m₁ a₁) ∙ eqv ∙ shift-num m₂ a₂))) ∙ sym (numeralOf-spec v₂ a₂))
    go (inl a₁) _ (inr ¬a₂) (inl p₂) = Empty.rec
      (snotz (#-inj′ (sym (shift-num m₁ a₁) ∙ eqv ∙ shift-top m₂ p₂)))
    go (inl a₁) _ (inr ¬a₂) (inr ¬p₂) = Empty.rec (¬a₂
      (subst (λ w → ⟨ w ∈ˢ ω ⟩) (sym (shift-num m₁ a₁) ∙ eqv ∙ shift-other m₂ ¬a₂ ¬p₂)
        (#∈ω (suc (numeralOf v₁ a₁)))))
    go (inr ¬a₁) (inl p₁) (inl a₂) _ = Empty.rec
      (znots (#-inj′ (sym (shift-top m₁ p₁) ∙ eqv ∙ shift-num m₂ a₂)))
    go (inr ¬a₁) (inl p₁) (inr ¬a₂) (inl p₂) = v₁≡v₂ (p₁ ∙ sym p₂)
    go (inr ¬a₁) (inl p₁) (inr ¬a₂) (inr ¬p₂) = Empty.rec (¬a₂
      (subst (λ w → ⟨ w ∈ˢ ω ⟩) (sym (shift-top m₁ p₁) ∙ eqv ∙ shift-other m₂ ¬a₂ ¬p₂) (#∈ω 0)))
    go (inr ¬a₁) (inr ¬p₁) (inl a₂) _ = Empty.rec (¬a₁
      (subst (λ w → ⟨ w ∈ˢ ω ⟩)
        (sym (shift-num m₂ a₂) ∙ sym eqv ∙ shift-other m₁ ¬a₁ ¬p₁)
        (#∈ω (suc (numeralOf v₂ a₂)))))
    go (inr ¬a₁) (inr ¬p₁) (inr ¬a₂) (inl p₂) = Empty.rec (¬a₁
      (subst (λ w → ⟨ w ∈ˢ ω ⟩)
        (sym (shift-top m₂ p₂) ∙ sym eqv ∙ shift-other m₁ ¬a₁ ¬p₁) (#∈ω 0)))
    go (inr ¬a₁) (inr ¬p₁) (inr ¬a₂) (inr ¬p₂) = v₁≡v₂
      (sym (shift-other m₁ ¬a₁ ¬p₁) ∙ eqv ∙ shift-other m₂ ¬a₂ ¬p₂)
```

<!--en-->
## The successor step
<!--zh-->
## 后继步
<!--/-->

<!--en-->
The square law at an infinite ordinal passes to its successor: pair the
shifted coordinates by the smaller-ordinal pairing and read the result back
through the successor's index. The shift is an injection, so the successor
pairing is injective. Together with the base at `ω` below, this closes the
square law at every ordinal reached from `ω` by finitely many successors.
<!--zh-->
无穷序数处的平方律传给它的后继：把平移后的坐标交给更小序数的配对，再经后继的索引读回结果。平移是单射，故后继配对单射。与下文 `ω` 处的基底合起来，平方律在从 `ω` 经有穷多步后继可达的每个序数处闭合。
<!--/-->

```agda
module _ (γ : S) (oγ : IsOrd γ) (ω∈γ : ⟨ ω ∈ˢ γ ⟩)
  (sqγ : Σ[ f ∈ (⟪ γ ⟫ × ⟪ γ ⟫ → ⟪ γ ⟫) ]
           ((x y : ⟪ γ ⟫ × ⟪ γ ⟫) → f x ≡ f y → x ≡ y)) where

  open Shift γ oγ ω∈γ

  pair-suc : ⟪ sucV γ ⟫ × ⟪ sucV γ ⟫ → ⟪ sucV γ ⟫
  pair-suc (x , y) = fiber (sucV γ) (∈sucV-inl (member γ (fst sqγ (shift x , shift y)))) .fst

  pair-suc-inj : (p q : ⟪ sucV γ ⟫ × ⟪ sucV γ ⟫) → pair-suc p ≡ pair-suc q → p ≡ q
  pair-suc-inj (x₁ , y₁) (x₂ , y₂) e =
    cong₂ _,_ (shift-inj x₁ x₂ x-eq) (shift-inj y₁ y₂ y-eq)
    where
    p-eq : (shift x₁ , shift y₁) ≡ (shift x₂ , shift y₂)
    p-eq = snd sqγ (shift x₁ , shift y₁) (shift x₂ , shift y₂)
      (↪-inj {a = γ}
        (sym (fiber (sucV γ) (∈sucV-inl (member γ (fst sqγ (shift x₁ , shift y₁)))) .snd)
          ∙ cong (⟪ sucV γ ⟫↪) e
          ∙ fiber (sucV γ) (∈sucV-inl (member γ (fst sqγ (shift x₂ , shift y₂)))) .snd))
    x-eq : shift x₁ ≡ shift x₂
    x-eq = cong fst p-eq
    y-eq : shift y₁ ≡ shift y₂
    y-eq = cong snd p-eq
```



<!--en-->
## The base at `ω`
<!--zh-->
## `ω` 处的基底
<!--/-->

<!--en-->
The base case runs the order core at `ω`. Every member of `ω` is a numeral,
so successor closure holds and the two hypotheses that mention infinite
members are vacuous; the finite exclusion is the counting lemma of the finite
base, instantiated at `ω`, with `ω`'s own transitivity in place of `α`'s. The
core then delivers the bound at `ω`, the consumer's exact shape.
<!--zh-->
基底情形在 `ω` 处运行序核心。`ω` 的每个成员都是数码，故后继封闭成立，两条提到无穷成员的假设空洞，而有穷排除就是有穷基底中的计数引理在 `ω` 处的实例，以 `ω` 自身的传递性代替 `α` 的传递性。核心随即交付 `ω` 处的界，即消费方的确切形状。
<!--/-->

```agda
module CoreAtω where

  ω-limit : (γ : S) → ⟨ γ ∈ˢ ω ⟩ → ⟨ sucV γ ∈ˢ ω ⟩
  ω-limit γ γ∈ω = PT.rec (snd (sucV γ ∈ˢ ω)) go (ω-mem→numeral γ γ∈ω)
    where
    go : Σ[ n ∈ ℕ ] (γ ≡ # n) → ⟨ sucV γ ∈ˢ ω ⟩
    go (n , p) = subst (λ w → ⟨ sucV w ∈ˢ ω ⟩) (sym p) (#∈ω (suc n))

  ω∉β : (β : S) → ⟨ β ∈ˢ ω ⟩ → ⟨ ω ∈ˢ β ⟩ → Empty.⊥
  ω∉β β β∈ω ω∈β = PT.rec Empty.isProp⊥ go (ω-mem→numeral β β∈ω)
    where
    go : Σ[ n ∈ ℕ ] (β ≡ # n) → Empty.⊥
    go (n , p) = ∈-irrefl ω (ω-ord .fst (subst (λ w → ⟨ ω ∈ˢ w ⟩) p ω∈β) (#∈ω n))

  ih-ω : (β : S) → IsOrd β → ⟨ β ∈ˢ ω ⟩ → ⟨ ω ∈ˢ β ⟩
       → Σ[ f ∈ (⟪ β ⟫ × ⟪ β ⟫ → ⟪ β ⟫) ]
            ((x y : ⟪ β ⟫ × ⟪ β ⟫) → f x ≡ f y → x ≡ y)
  ih-ω β oβ β∈ω ω∈β = Empty.rec (ω∉β β β∈ω ω∈β)

  noinj-ω : (β : S) → IsOrd β → ⟨ β ∈ˢ ω ⟩ → ⟨ ω ∈ˢ β ⟩
          → (f : ⟪_⟫ {ℓ} ω → ⟪_⟫ {ℓ} β)
          → ((m n : ⟪_⟫ {ℓ} ω) → f m ≡ f n → m ≡ n) → Empty.⊥
  noinj-ω β oβ β∈ω ω∈β f finj = Empty.rec (ω∉β β β∈ω ω∈β)

  numeral-into-ω : (m : ℕ) → ⟪ # m ⟫ → ⟪ ω ⟫
  numeral-into-ω m i = fiber ω (ω-ord .fst (member (# m) i) (#∈ω m)) .fst

  numeral-into-ω-inj : (m : ℕ) (i₁ i₂ : ⟪ # m ⟫)
                     → numeral-into-ω m i₁ ≡ numeral-into-ω m i₂ → i₁ ≡ i₂
  numeral-into-ω-inj m i₁ i₂ e = ↪-inj {a = # m}
    (sym (fiber ω (ω-ord .fst (member (# m) i₁) (#∈ω m)) .snd)
      ∙ cong (⟪ ω ⟫↪) e
      ∙ fiber ω (ω-ord .fst (member (# m) i₂) (#∈ω m)) .snd)

  no-inj-finite-ω : (n : ℕ) → (f : ⟪ ω ⟫ → ⟪ # n ⟫ × ⟪ # n ⟫)
                  → ((x y : ⟪ ω ⟫) → f x ≡ f y → x ≡ y) → Empty.⊥
  no-inj-finite-ω n f finj = no-inj-Fin (n · n) g g-inj
    where
    g : FB.Fin (suc (n · n)) → FB.Fin (n · n)
    g i = factor n ( toFin n (fst (f (numeral-into-ω (suc (n · n))
                          (fromFin (suc (n · n)) i))))
                   , toFin n (snd (f (numeral-into-ω (suc (n · n))
                          (fromFin (suc (n · n)) i)))))
    g-inj : (x y : FB.Fin (suc (n · n))) → g x ≡ g y → x ≡ y
    g-inj x y e = fromFin-inj (suc (n · n)) x y
      (numeral-into-ω-inj (suc (n · n))
        (fromFin (suc (n · n)) x) (fromFin (suc (n · n)) y)
        (finj Xx Xy pair-eq))
      where
      Xx : ⟪ ω ⟫
      Xx = numeral-into-ω (suc (n · n)) (fromFin (suc (n · n)) x)
      Xy : ⟪ ω ⟫
      Xy = numeral-into-ω (suc (n · n)) (fromFin (suc (n · n)) y)
      p-eq : (toFin n (fst (f Xx)) , toFin n (snd (f Xx)))
           ≡ (toFin n (fst (f Xy)) , toFin n (snd (f Xy)))
      p-eq = factor-inj n
               (toFin n (fst (f Xx)) , toFin n (snd (f Xx)))
               (toFin n (fst (f Xy)) , toFin n (snd (f Xy))) e
      pair-eq : f Xx ≡ f Xy
      pair-eq = ΣPathP
        ( toFin-inj n (fst (f Xx)) (fst (f Xy)) (cong fst p-eq)
        , toFin-inj n (snd (f Xx)) (snd (f Xy)) (cong snd p-eq))

  finite-excl-ω : (β : S) → IsOrd β → ⟨ β ∈ˢ ω ⟩
                → (f : ⟪ ω ⟫ → ⟪ β ⟫ × ⟪ β ⟫)
                → ((x y : ⟪ ω ⟫) → f x ≡ f y → x ≡ y) → Empty.⊥
  finite-excl-ω β oβ β∈ω f finj =
    PT.rec Empty.isProp⊥ go (ω-mem→numeral β β∈ω)
    where
    go : Σ[ n ∈ ℕ ] (β ≡ # n) → Empty.⊥
    go (n , p) = no-inj-finite-ω n f' finj'
      where
      e : ⟪ β ⟫ × ⟪ β ⟫ ≃ ⟪ # n ⟫ × ⟪ # n ⟫
      e = pathToEquiv (cong (λ w → ⟪ w ⟫ × ⟪ w ⟫) p)
      f' : ⟪ ω ⟫ → ⟪ # n ⟫ × ⟪ # n ⟫
      f' x = equivFun e (f x)
      finj' : (x y : ⟪ ω ⟫) → f' x ≡ f' y → x ≡ y
      finj' x y e' = finj x y
        (sym (retEq e (f x)) ∙ cong (invEq e) e' ∙ retEq e (f y))
```

<!--en-->
## Recap
<!--zh-->
## 小结
<!--/-->

<!--en-->
The order core is delivered conditional on four hypotheses: successor
closure, the square law at the infinite members, the absence of injections
into infinite members, and the finite exclusion. The finite base supplies the
last, the shift supplies the successor step of the square law, and the core
closes the base at `ω`. The cardinal of an ordinal is built honestly as the
least equinumerous member, with its minimality; what the search does not
return honestly is the equinumerosity witness, which is truncated. That is
the extraction risk the pairing chapter's report flagged, and it is the piece
the general transfer, from an arbitrary infinite ordinal to its cardinal,
would need: the square law at the ordinals beyond `ω` and its successors
remains named until the witness is carried through the reduction.
<!--zh-->
序核心在四条假设下交付：后继封闭、无穷成员处的平方律、不单射注入无穷成员、以及有穷排除。有穷基底供给末一条，平移供给平方律的后继步，而核心在 `ω` 处闭合基底。序数的基数被诚实地建为与之等势的最小成员，连同其极小性；搜索不诚实返回的是等势见证，它是截断的。这正是配对一章的报告所标记的提取风险，也是一般转移 (从任意无穷序数到其基数) 所需要的件：`ω` 及其后继之外的平方律仍保持具名，直到见证被携带穿过归约。
<!--/-->

<!--en-->
## The initial ordinals, and the truncated law
<!--zh-->
## 初始序数与截断律
<!--/-->

<!--en-->
The counting calls the square law at ordinals beyond `ω`. The honest
equivalence remains unavailable where the transfer bites: the least-of search
returns only the truncation `∥ ⟪ α ⟫ ≃ ⟪ κ ⟫ ∥₁`, so the law at the
non-initial ordinals stays named. The bound itself, however, never needs the
law at a member, and this section delivers it at every initial ordinal. An
ordinal is initial here when it contains `ω`, is closed under successors, and
its index injects into no infinite member's square. The third clause is the
order core's exclusion hypothesis in its sharpest form: the exclusion case
only refutes an injection of the index into the square of a member, so the
square law at that member, which the honest transfer cannot supply, is never
called for. The core's remaining hypotheses are discharged where they stand,
and the honest bound, the pairing chapter's exact hypothesis, is delivered at
every initial ordinal, with the truncated square law as its projection.
The boundary, verified against the delivered definition. "Contains `ω`" is
strict membership, `⟨ ω ∈ˢ α ⟩`, so `ω` itself is not initial in this
chapter's sense: `Init ω` would need `ω ∈ ω`, which `∈-irrefl` refutes. The
law is therefore delivered at every ordinal strictly above `ω` that
satisfies the three clauses, and at no other ordinal. The original account
of this section read the boundary as "from `ω` up", as though `ω` were
included; that reading is corrected here, and the correction is recorded
beside the original rather than silently rewording it, per D-10.
<!--zh-->
计数会在 `ω` 之外的序数处调用平方律。诚实的等价在转移咬住的地方仍不可得：极小元搜索只返回截断 `∥ ⟪ α ⟫ ≃ ⟪ κ ⟫ ∥₁`，故非初始序数处的律仍保持具名。然而界本身从不曾需要成员处的律，本节就在每个初始序数处交付它。本章中，序数称为初始，当它包含 `ω`、闭于后继、且其索引不单射注入任何无穷成员的平方。第三条正是序核心排除假设最锐利的形式：排除情形只须反驳索引对某成员之平方的单射，于是诚实转移无法供给的该成员处平方律，永远不被调用。核心余下的假设就地解除，而诚实的界，即配对一章的确切假设，在每个初始序数处交付，截断平方律作为它的投影。

边界，对照交付的定义核实过。「包含 `ω`」是严格成员关系 `⟨ ω ∈ˢ α ⟩`，故 `ω` 自身在本章的意义下并非初始：`Init ω` 将需要 `ω ∈ ω`，而这被 `∈-irrefl` 反驳。因此律交付于严格高于 `ω` 且满足三条条款的每个序数，此外再无别的序数。本节原先的叙述把边界读作「从 `ω` 起」，仿佛把 `ω` 算在内；这个读法在此更正，并按 D-10 把更正记录在原文旁，而不是悄然改写。
<!--/-->

<!--en-->
What the truncated form gives and does not give. At every initial ordinal it
gives the honest injection of the order type into the ordinal, the pairing
chapter's `bound` hypothesis in the exact shape the counting consumes, and
the truncated square law `∥ sq α ∥₁` as its projection. It does not give the
honest equivalence between the ordinal and its square: that bijection is
exactly what the extraction wall blocks, and no proposition-valued consumer
needs it. It does not give the law at the non-initial ordinals such as
`ω + ω`: the reduction of such a site to its cardinal is the least-of
transfer, which is the counting's own plumbing (its input, the truncated
equinumerosity witness of `Card.least`, is delivered here), and at the
cardinals themselves the counting must still verify the three initiality
clauses, or take them as its cardinal notion.
<!--zh-->
截断形式给出什么、不给什么。在每个初始序数处，它给出序型到该序数的诚实单射，即配对一章的 `bound` 假设，恰为计数消费的确切形状，并以其投影给出截断平方律 `∥ sq α ∥₁`。它不给出序数与其平方之间的诚实等价：那正是提取之墙阻断的双射，而任何命题值的消费方都不需要它。它也不给出 `ω + ω` 这类非初始序数处的律：此类站点归约到其基数所靠的极小元转移，是计数自己的管道 (其输入，即 `Card.least` 的截断等势见证，已在本书交付)，而在基数本身处，计数仍须验证三条初始性条款，或径取之为其基数概念。
<!--/-->

```agda
-- The square law, and its truncated form.
sq : S → Type ℓ
sq α = Σ[ f ∈ (⟪ α ⟫ × ⟪ α ⟫ → ⟪ α ⟫) ]
         ((x y : ⟪ α ⟫ × ⟪ α ⟫) → f x ≡ f y → x ≡ y)

-- An ordinal is initial in this chapter: it has omega as a member (so omega
-- itself is not initial), is closed under successors, and its index injects
-- into no infinite member's square.
Init : S → Type (ℓ-suc ℓ)
Init α = IsOrd α
       × ⟨ ω ∈ˢ α ⟩
       × ((γ : S) → ⟨ γ ∈ˢ α ⟩ → ⟨ sucV γ ∈ˢ α ⟩)
       × ((β : S) → IsOrd β → ⟨ β ∈ˢ α ⟩ → ⟨ ω ∈ˢ β ⟩
          → (f : ⟪ α ⟫ → ⟪ β ⟫ × ⟪ β ⟫)
          → ((m n : ⟪ α ⟫) → f m ≡ f n → m ≡ n) → Empty.⊥)

-- The order core with the no-injection hypothesis in its square form: the
-- law at members is never needed, since the exclusion case refutes an
-- injection of the index into the square of a member directly.
module InitialCore (α : S) (oα : IsOrd α)
  (α-limit : (γ : S) → ⟨ γ ∈ˢ α ⟩ → ⟨ sucV γ ∈ˢ α ⟩)
  (noinj² : (β : S) → IsOrd β → ⟨ β ∈ˢ α ⟩ → ⟨ ω ∈ˢ β ⟩
          → (f : ⟪ α ⟫ → ⟪ β ⟫ × ⟪ β ⟫)
          → ((m n : ⟪ α ⟫) → f m ≡ f n → m ≡ n) → Empty.⊥)
  (finite-excl : (β : S) → IsOrd β → ⟨ β ∈ˢ ω ⟩
               → (f : ⟪ α ⟫ → ⟪ β ⟫ × ⟪ β ⟫)
               → ((m n : ⟪ α ⟫) → f m ≡ f n → m ≡ n) → Empty.⊥) where

  PairA : Type ℓ
  PairA = Pair α oα

  colA : PairA → S
  colA = col α oα

  _≺'_ : PairA → PairA → Type (ℓ-suc ℓ)
  _≺'_ = _≺_ α oα

  prec1 : ⟪ α ⟫ → ⟪ α ⟫ → Type (ℓ-suc ℓ)
  prec1 = _≺₁_ α oα

  leq : ⟪ α ⟫ → ⟪ α ⟫ → Type (ℓ-suc ℓ)
  leq = _≤₁_ α oα

  max' : ⟪ α ⟫ → ⟪ α ⟫ → ⟪ α ⟫
  max' = maxOrd α oα

  trans1 : (m n k : ⟪ α ⟫) → prec1 m n → prec1 n k → prec1 m k
  trans1 = trans₁ α oα

  tri' : (p q : PairA) → Tri (p ≺' q) (p ≡ q) (q ≺' p)
  tri' = tri≺ α oα

  cm : {p q : PairA} → p ≺' q → ⟨ colA p ∈ˢ colA q ⟩
  cm = col-mono α oα

  ci : {p q : PairA} → colA p ≡ colA q → p ≡ q
  ci = col-inj α oα

  cimg : (q : PairA) (b : S) → ⟨ b ∈ˢ colA q ⟩
       → ∥ Σ[ r ∈ PairA ] (colA r ≡ b) ∥₁
  cimg = col-img α oα

  colo : (p : PairA) → IsOrd (colA p)
  colo = col-ord α oα

  cc : (p : PairA) → colA p ≡ colStep α oα p (λ r _ → colA r)
  cc = col-compute α oα

  wf : WellFounded _≺'_
  wf = wf≺ α oα

  god : SWO PairA
  god = godSWO α oα

  ≺dec : (p q : PairA) → (p ≺' q) ⊎ ((p ≺' q) → Empty.⊥)
  ≺dec = ≺-dec α oα

  τA : S
  τA = τ α oα

  ≤₁→≺₁ : (m n k : ⟪ α ⟫) → leq m n → prec1 n k → prec1 m k
  ≤₁→≺₁ m n k (inl h) h' = trans1 m n k h h'
  ≤₁→≺₁ m n k (inr e) h' = subst (λ w → prec1 w k) (sym e) h'

  ≤₁-subst : (m n n' : ⟪ α ⟫) → leq m n → n ≡ n' → leq m n'
  ≤₁-subst m n n' (inl h) e = inl (subst (λ w → prec1 m w) e h)
  ≤₁-subst m n n' (inr q) e = inr (q ∙ e)

  ≤₁-into-suc : (m n : ⟪ α ⟫) → leq m n → ⟨ ⟪ α ⟫↪ m ∈ˢ sucV (⟪ α ⟫↪ n) ⟩
  ≤₁-into-suc m n (inl h) = ∈sucV-inl h
  ≤₁-into-suc m n (inr e) =
    subst (λ w → ⟨ ⟪ α ⟫↪ w ∈ˢ sucV (⟪ α ⟫↪ n) ⟩) (sym e) (self∈sucV (⟪ α ⟫↪ n))

  fst∈sucmax : {p q : PairA} → p ≺' q
             → ⟨ ⟪ α ⟫↪ (fst p) ∈ˢ sucV (⟪ α ⟫↪ (max' (fst q) (snd q))) ⟩
  fst∈sucmax {a , b} {c , d} (inl h) =
    ∈sucV-inl (≤₁→≺₁ a (max' a b) (max' c d) (max-spec α oα a b .fst) h)
  fst∈sucmax {a , b} {c , d} (inr (e , _)) =
    ≤₁-into-suc a (max' c d)
      (≤₁-subst a (max' a b) (max' c d) (max-spec α oα a b .fst) e)

  snd∈sucmax : {p q : PairA} → p ≺' q
             → ⟨ ⟪ α ⟫↪ (snd p) ∈ˢ sucV (⟪ α ⟫↪ (max' (fst q) (snd q))) ⟩
  snd∈sucmax {a , b} {c , d} (inl h) =
    ∈sucV-inl (≤₁→≺₁ b (max' a b) (max' c d) (max-spec α oα a b .snd) h)
  snd∈sucmax {a , b} {c , d} (inr (e , _)) =
    ≤₁-into-suc b (max' c d)
      (≤₁-subst b (max' a b) (max' c d) (max-spec α oα a b .snd) e)

  Pb : (b : S) → PairA → hProp (ℓ-suc ℓ)
  Pb b r = (colA r ≡ b) , isSetS (colA r) b

  colr≺ : {p : PairA} (b : S) → ⟨ b ∈ˢ colA p ⟩ → (r : PairA)
        → colA r ≡ b → r ≺' p
  colr≺ {p} b b∈ r e = go (tri' r p)
    where
    go : Tri (r ≺' p) (r ≡ p) (p ≺' r) → r ≺' p
    go (lt h) = h
    go (eq q) = Empty.rec
      (∈-irrefl (colA p)
        (subst (λ w → ⟨ w ∈ˢ colA p ⟩) (sym (cong colA (sym q) ∙ e)) b∈))
    go (gt h) = Empty.rec
      (∈-irrefl (colA p)
        (colo p .fst (cm h) (subst (λ w → ⟨ w ∈ˢ colA p ⟩) (sym e) b∈)))

  module WF = WFI wf

  opaque
    descent : (p : PairA) (b : S) → ⟨ b ∈ˢ colA p ⟩
            → Σ[ r ∈ PairA ] ((r ≺' p) × (colA r ≡ b))
    descent p b b∈ = fst s , (colr≺ b b∈ (fst s) (fst (snd s)) , fst (snd s))
      where
      s : Σ[ m ∈ PairA ] IsLeast god (Pb b) m
      s = leastOf god lem (Pb b) (cimg p b b∈)

    g : (p : PairA) (b : S) → ⟨ b ∈ˢ colA p ⟩ → PairA
    g p b b∈ = fst (descent p b b∈)

    g-inj : (p : PairA) {b b' : S} (hb : ⟨ b ∈ˢ colA p ⟩) (hb' : ⟨ b' ∈ˢ colA p ⟩)
          → g p b hb ≡ g p b' hb' → b ≡ b'
    g-inj p {b} {b'} hb hb' e =
      sym (snd (descent p b hb) .snd) ∙ cong colA e ∙ snd (descent p b' hb') .snd

    γp : PairA → S
    γp p = ⟪ α ⟫↪ (max' (fst p) (snd p))

    h₀ : (p : PairA) → (r : PairA) → r ≺' p → ⟪ sucV (γp p) ⟫ × ⟪ sucV (γp p) ⟫
    h₀ p r pr = (fiber β (fst∈sucmax {r} {p} pr) .fst
               , fiber β (snd∈sucmax {r} {p} pr) .fst)
      where
      β : S
      β = sucV (γp p)

    h₀-inj : (p : PairA) {r r' : PairA} (pr : r ≺' p) (pr' : r' ≺' p)
           → h₀ p r pr ≡ h₀ p r' pr' → r ≡ r'
    h₀-inj p {a , b} {a' , b'} pr pr' e = cong₂ _,_ ea eb
      where
      β : S
      β = sucV (γp p)
      ea : a ≡ a'
      ea = ↪-inj {a = α} (sym (fiber β (fst∈sucmax {a , b} {p} pr) .snd)
        ∙ cong (⟪ β ⟫↪) (cong fst e) ∙ fiber β (fst∈sucmax {a' , b'} {p} pr') .snd)
      eb : b ≡ b'
      eb = ↪-inj {a = α} (sym (fiber β (snd∈sucmax {a , b} {p} pr) .snd)
        ∙ cong (⟪ β ⟫↪) (cong snd e) ∙ fiber β (snd∈sucmax {a' , b'} {p} pr') .snd)

    comp₀ : (p : PairA) (e : colA p ≡ α) → ⟪ α ⟫ → ⟪ sucV (γp p) ⟫ × ⟪ sucV (γp p) ⟫
    comp₀ p e m = h₀ p (g p (⟪ α ⟫↪ m) (b∈ m))
                      (snd (descent p (⟪ α ⟫↪ m) (b∈ m)) .fst)
      where
      b∈ : (m : ⟪ α ⟫) → ⟨ ⟪ α ⟫↪ m ∈ˢ colA p ⟩
      b∈ m = subst (λ w → ⟨ ⟪ α ⟫↪ m ∈ˢ w ⟩) (sym e)
        (∈∈ₛ {a = ⟪ α ⟫↪ m} {b = α} .snd (∈ₛ⟪ α ⟫↪ m))

    comp₀-inj : (p : PairA) (e : colA p ≡ α) (m n : ⟪ α ⟫)
              → comp₀ p e m ≡ comp₀ p e n → m ≡ n
    comp₀-inj p e m n e' = ↪-inj {a = α}
      (g-inj p (b∈ m) (b∈ n)
        (h₀-inj p (snd (descent p (⟪ α ⟫↪ m) (b∈ m)) .fst)
                  (snd (descent p (⟪ α ⟫↪ n) (b∈ n)) .fst) e'))
      where
      b∈ : (m : ⟪ α ⟫) → ⟨ ⟪ α ⟫↪ m ∈ˢ colA p ⟩
      b∈ m = subst (λ w → ⟨ ⟪ α ⟫↪ m ∈ˢ w ⟩) (sym e)
        (∈∈ₛ {a = ⟪ α ⟫↪ m} {b = α} .snd (∈ₛ⟪ α ⟫↪ m))

    β≠ω : (p : PairA) → sucV (γp p) ≡ ω → Empty.⊥
    β≠ω p e = PT.rec Empty.isProp⊥ go (ω-mem→numeral (γp p) γp∈ω)
      where
      γp∈ω : ⟨ γp p ∈ˢ ω ⟩
      γp∈ω = subst (λ w → ⟨ γp p ∈ˢ w ⟩) e (self∈sucV (γp p))
      go : Σ[ n ∈ ℕ ] (γp p ≡ # n) → Empty.⊥
      go (n , q) = ∈-irrefl ω
        (subst (λ w → ⟨ w ∈ˢ ω ⟩) (sym (cong sucV q) ∙ e) (#∈ω (suc n)))

    exclude : (p : PairA) → colA p ≡ α → Empty.⊥
    exclude p e = go (ord-tri β ordβ ω ω-ord)
      where
      γp∈α : ⟨ γp p ∈ˢ α ⟩
      γp∈α = ∈∈ₛ {a = γp p} {b = α} .snd (∈ₛ⟪ α ⟫↪ (max' (fst p) (snd p)))
      β : S
      β = sucV (γp p)
      ordβ : IsOrd β
      ordβ = suc-ord (mem-ord {A = α} oα (γp p) γp∈α)
      β∈α : ⟨ β ∈ˢ α ⟩
      β∈α = α-limit (γp p) γp∈α
      go : (⟨ β ∈ˢ ω ⟩ ⊎ ((β ≡ ω) ⊎ ⟨ ω ∈ˢ β ⟩)) → Empty.⊥
      go (inl β∈ω) = finite-excl β ordβ β∈ω (comp₀ p e) (comp₀-inj p e)
      go (inr (inl β≡ω)) = β≠ω p β≡ω
      go (inr (inr ω∈β)) = noinj² β ordβ β∈α ω∈β (comp₀ p e) (comp₀-inj p e)

    gₚ : (p : PairA) → PairA → S
    gₚ p r = colPick α oα p (λ r _ → colA r) r (≺dec r p)

    gₚ-inl : (p r : PairA) → (rp : r ≺' p) → gₚ p r ≡ sucV (colA r)
    gₚ-inl p r rp = go (≺dec r p)
      where
      go : (d : (r ≺' p) ⊎ ((r ≺' p) → Empty.⊥))
         → colPick α oα p (λ r _ → colA r) r d ≡ sucV (colA r)
      go (inl _) = refl
      go (inr ¬rp) = Empty.rec (¬rp rp)

    gₚ-inr : (p r : PairA) → ((r ≺' p) → Empty.⊥) → gₚ p r ≡ ∅
    gₚ-inr p r ¬rp = go (≺dec r p)
      where
      go : (d : (r ≺' p) ⊎ ((r ≺' p) → Empty.⊥))
         → colPick α oα p (λ r _ → colA r) r d ≡ ∅
      go (inl rp) = Empty.rec (¬rp rp)
      go (inr _) = refl

    colp⊆α : (p : PairA) → ((r : PairA) → r ≺' p → ⟨ colA r ∈ˢ α ⟩)
           → (x : S) → ⟨ x ∈ˢ colA p ⟩ → ⟨ x ∈ˢ α ⟩
    colp⊆α p rec x x∈ = PT.rec (snd (x ∈ˢ α)) viaUnion
      (union-ax (sett PairA (gₚ p)) x .fst
        (∈∈ₛ {a = x} {b = ⋃ (sett PairA (gₚ p))} .fst
          (subst (λ w → ⟨ x ∈ˢ w ⟩) (cc p) x∈)))
      where
      viaUnion : Σ[ v ∈ S ] (⟨ v ∈ₛ sett PairA (gₚ p) ⟩ × ⟨ x ∈ₛ v ⟩) → ⟨ x ∈ˢ α ⟩
      viaUnion (v , (v∈ₛsett , x∈ₛv)) = PT.rec (snd (x ∈ˢ α)) viaFiber
        (∈∈ₛ {a = v} {b = sett PairA (gₚ p)} .snd v∈ₛsett)
        where
        viaFiber : Σ[ r ∈ PairA ] (gₚ p r ≡ v) → ⟨ x ∈ˢ α ⟩
        viaFiber (r , gr≡v) = decide (≺dec r p)
          where
          x∈gr : ⟨ x ∈ₛ gₚ p r ⟩
          x∈gr = subst (λ w → ⟨ x ∈ₛ w ⟩) (sym gr≡v) x∈ₛv
          decide : (r ≺' p) ⊎ ((r ≺' p) → Empty.⊥) → ⟨ x ∈ˢ α ⟩
          decide (inl rp) = ∈sucV-elim {A = colA r} {x = x} (snd (x ∈ˢ α))
            (∈∈ₛ {a = x} {b = sucV (colA r)} .snd
              (subst (λ w → ⟨ x ∈ₛ w ⟩) (gₚ-inl p r rp) x∈gr))
            (λ x∈r → oα .fst x∈r (rec r rp))
            (λ x≡r → subst (λ w → ⟨ w ∈ˢ α ⟩) (sym x≡r) (rec r rp))
          decide (inr ¬rp) = Empty.rec
            (∅-empty x (subst (λ w → ⟨ x ∈ₛ w ⟩) (gₚ-inr p r ¬rp) x∈gr))

    col≤α : (p : PairA) → ((r : PairA) → r ≺' p → ⟨ colA r ∈ˢ α ⟩)
          → ⟨ colA p ∈ˢ α ⟩
    col≤α p rec = go (ord-tri (colA p) (colo p) α oα)
      where
      go : (⟨ colA p ∈ˢ α ⟩ ⊎ ((colA p ≡ α) ⊎ ⟨ α ∈ˢ colA p ⟩)) → ⟨ colA p ∈ˢ α ⟩
      go (inl h) = h
      go (inr (inl e)) = Empty.rec (exclude p e)
      go (inr (inr h)) = Empty.rec (∈-irrefl α (colp⊆α p rec α h))

    col∈α : (p : PairA) → ⟨ colA p ∈ˢ α ⟩
    col∈α = WF.induction {P = λ p → ⟨ colA p ∈ˢ α ⟩} step
      where
      step : (p : PairA) → ((r : PairA) → r ≺' p → ⟨ colA r ∈ˢ α ⟩)
           → ⟨ colA p ∈ˢ α ⟩
      step p rec = col≤α p (λ r rp → rec r rp)

    τ⊆α : (x : S) → ⟨ x ∈ˢ τA ⟩ → ⟨ x ∈ˢ α ⟩
    τ⊆α x x∈τ = PT.rec (snd (x ∈ˢ α)) viaUnion
      (union-ax (sett PairA fτ) x .fst
        (∈∈ₛ {a = x} {b = τA} .fst x∈τ))
      where
      fτ : PairA → S
      fτ p = sucV (colA p)
      viaUnion : Σ[ v ∈ S ] (⟨ v ∈ₛ sett PairA fτ ⟩ × ⟨ x ∈ₛ v ⟩) → ⟨ x ∈ˢ α ⟩
      viaUnion (v , (v∈ₛsett , x∈ₛv)) = PT.rec (snd (x ∈ˢ α)) viaFiber
        (∈∈ₛ {a = v} {b = sett PairA fτ} .snd v∈ₛsett)
        where
        viaFiber : Σ[ p ∈ PairA ] (fτ p ≡ v) → ⟨ x ∈ˢ α ⟩
        viaFiber (p , fp≡v) = ∈sucV-elim {A = colA p} {x = x} (snd (x ∈ˢ α))
          (∈∈ₛ {a = x} {b = sucV (colA p)} .snd
            (subst (λ w → ⟨ x ∈ₛ w ⟩) (sym fp≡v) x∈ₛv))
          (λ x∈p → oα .fst x∈p (col∈α p))
          (λ x≡p → subst (λ w → ⟨ w ∈ˢ α ⟩) (sym x≡p) (col∈α p))

  bound : ⟪ τA ⟫ → ⟪ α ⟫
  bound m = fiber α (τ⊆α (⟪ τA ⟫↪ m)
    (∈∈ₛ {a = ⟪ τA ⟫↪ m} {b = τA} .snd (∈ₛ⟪ τA ⟫↪ m))) .fst

  bound-inj : {m n : ⟪ τA ⟫} → bound m ≡ bound n → m ≡ n
  bound-inj {m} {n} e =
    ↪-inj {a = τA} (sym eq1 ∙ cong (⟪ α ⟫↪) e ∙ eq2)
    where
    eq1 : ⟪ α ⟫↪ (bound m) ≡ ⟪ τA ⟫↪ m
    eq1 = fiber α (τ⊆α (⟪ τA ⟫↪ m)
      (∈∈ₛ {a = ⟪ τA ⟫↪ m} {b = τA} .snd (∈ₛ⟪ τA ⟫↪ m))) .snd
    eq2 : ⟪ α ⟫↪ (bound n) ≡ ⟪ τA ⟫↪ n
    eq2 = fiber α (τ⊆α (⟪ τA ⟫↪ n)
      (∈∈ₛ {a = ⟪ τA ⟫↪ n} {b = τA} .snd (∈ₛ⟪ τA ⟫↪ n))) .snd

module Initial (α : S) (iα : Init α) where
  opaque
    bound₀ : ⟪ τ α (iα .fst) ⟫ → ⟪ α ⟫
    bound₀ = InitialCore.bound α (iα .fst) (iα .snd .snd .fst) (iα .snd .snd .snd)
              (FiniteBase.finite-excl α (iα .fst) (iα .snd .fst))

    bound₀-inj : {m n : ⟪ τ α (iα .fst) ⟫} → bound₀ m ≡ bound₀ n → m ≡ n
    bound₀-inj = InitialCore.bound-inj α (iα .fst) (iα .snd .snd .fst) (iα .snd .snd .snd)
                   (FiniteBase.finite-excl α (iα .fst) (iα .snd .fst))

    -- The pairing chapter's module, fed its exact hypotheses at this
    -- initial ordinal: the bound is discharged, not assumed.
    module P = Pairing α (iα .fst) bound₀ bound₀-inj

    pair : ⟪ α ⟫ → ⟪ α ⟫ → ⟪ α ⟫
    pair = P.pair

    pair-inj : {a b c d : ⟪ α ⟫} → pair a b ≡ pair c d → (a ≡ c) × (b ≡ d)
    pair-inj = P.pair-inj

    square : sq α
    square = (λ p → pair (fst p) (snd p)) , square-inj
      where
      square-inj : (p q : ⟪ α ⟫ × ⟪ α ⟫)
                 → pair (fst p) (snd p) ≡ pair (fst q) (snd q) → p ≡ q
      square-inj (a , b) (c , d) e = ΣPathP (pair-inj {a} {b} {c} {d} e)

    truncated : ∥ sq α ∥₁
    truncated = ∣ square ∣₁

opaque
  initial-bound : (α : S) (iα : Init α) → ⟪ τ α (iα .fst) ⟫ → ⟪ α ⟫
  initial-bound α iα = Initial.bound₀ α iα

  initial-bound-inj : (α : S) (iα : Init α) {m n : ⟪ τ α (iα .fst) ⟫}
                    → initial-bound α iα m ≡ initial-bound α iα n → m ≡ n
  initial-bound-inj α iα = Initial.bound₀-inj α iα

  initial-square-law : (α : S) → Init α → ∥ sq α ∥₁
  initial-square-law α iα = Initial.truncated α iα
```
