# Ordinal pairing

<!--en-->
The cardinal step of the later chapters needs one fact about ordinals that the
book has not touched: the product of an infinite ordinal's members injects into
the ordinal itself. The classical route to that fact is the canonical
well-ordering of the product, due to Godel, which orders a pair by its larger
coordinate first, then by the first coordinate, then by the second, and then
reads each pair back as the order type of its predecessors. This chapter builds
that well-ordering and the order-type reading of it. What it establishes
honestly, with no postulate and no partial recursion, is the whole of the
classical route except one bound: the collapse is a bijection onto the order
type of the product, and the classical theorem that this order type is
equinumerous to the ordinal itself, the square law of infinite ordinals, is
named as the one remaining theorem, with the arithmetic it needs priced in the
report rather than faked here.
<!--zh-->
后续章节的基数一步需要关于序数的一个本书迄今未触及的事实：无穷序数之成员构成的积，单射地注入该序数自身。通往这一事实的经典路线是积的典范良序，归功于 Godel：先比一对的较大坐标，再比第一坐标，再比第二坐标，然后把每对读回其前驱的序型。本章建造那个良序以及关于它的序型读法。诚实地讲，本章所确立的，是无一处 postulate、无一处部分递归的经典路线的全部，唯有一个界除外：坍缩是积的序型上的双射，而「该序型与该序数本身等势」这条经典定理，即无穷序数的平方律，被点名为唯一余下的定理，它所需的算术在报告中定价，而不在此处假装完成。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module L.Ordinal.Pairing {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ; regularityV; ∈-irrefl )
open import V.Model {ℓ} using ( ∈sucV-elim; self∈sucV )
open import V.Presentation {ℓ} using ( member; fiber; ↪-inj )
open import L.Constructible {ℓ} using ( IsOrd )
open import L.Ordinal {ℓ} using ( mem-ord; suc-ord; setUnion-ord; ∅-ord )
open import L.Ordinal.Linear {ℓ} lem using ( ord-tri )
open import L.WellOrder.Base {ℓₚ = ℓ-suc ℓ}
  using ( SWO; Tri; lt; eq; gt; prodSWO; module SWO )

open import Cubical.Data.Sum using ( _⊎_; inl; inr )
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁; squash₁ )
open import Cubical.HITs.CumulativeHierarchy.Base using ( sett )
open import Cubical.HITs.CumulativeHierarchy.Properties
  using ( _∈ₛ_; ∈∈ₛ; ⟪_⟫; ⟪_⟫↪ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ⋃_; union-ax; ∅; ∅-empty; module InfinitySet )
open InfinitySet using ( sucV )
open import Cubical.Induction.WellFounded
  using ( Acc; acc; WellFounded; module WFI )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ
```

<!--en-->
## The order of an ordinal's members
<!--zh-->
## 序数成员之序
<!--/-->

<!--en-->
Fix an ordinal `α`. Its small index `⟪ α ⟫` presents its members, so membership
inside `α` becomes a strict order on the index: `m` lies below `n` when the set
`m` names belongs to the set `n` names. This is an instance of the well-order
bundle of the choice chapters. Trichotomy is the ordinal comparison of the
linear chapter transported along the injective embedding; irreflexivity and
transitivity are the two halves of ordinality of the members; well-foundedness
is regularity pulled back along the embedding.
<!--zh-->
固定一个序数 `α`。它的索引 `⟪ α ⟫` 呈现其成员，于是 `α` 内的成员关系成为索引上的严格序：当 `m` 所指的集合属于 `n` 所指的集合时，`m` 位于 `n` 之下。这是选择诸章良序束的一个实例。三歧是线性一章的序数比较沿单射嵌入的搬运；非自反与传递是成员序数性的两半；良基是正则性沿嵌入的拉回。
<!--/-->

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

<!--en-->
## The maximum
<!--zh-->
## 最大值
<!--/-->

<!--en-->
The canonical order compares pairs by their larger coordinate, so the chapter
needs the maximum as a function on the index. Ordinal trichotomy decides which
coordinate is larger, and the specification certifies the name: each coordinate
is at most the maximum. The relation `≤₁` is the reflexive closure of the order.
<!--zh-->
典范序以一对中的较大坐标先行比较，故本章需要索引上的最大值函数。序数三歧判定哪个坐标更大，而规格书认证这个名字：每个坐标至多为最大值。关系 `≤₁` 是该序的自反闭包。
<!--/-->

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
```

<!--en-->
## The canonical well-ordering of the product
<!--zh-->
## 积的典范良序
<!--/-->

<!--en-->
Now the product. A pair is ordered below another when its larger coordinate is
smaller, or the larger coordinates agree and the first coordinates compare, or
the larger coordinates and the first coordinates agree and the second
coordinates compare. This is the ordering Devlin records as the basis of
Godel's pairing of the ordinals, and Jech's canonical well-ordering of
`Ord × Ord`; it is read exactly as stated: maximum first, then first, then
second. Trichotomy is trichotomy of the maximum, then of the first coordinate,
then of the second, and well-foundedness is the lexicographic product of the
well-founded member order, which the well-order bundle already stacks, pulled
back along the injection that records a pair with its maximum.
<!--zh-->
然后是积。一对排在另一对之下，当它的较大坐标更小；或较大坐标相同且第一坐标可比；或较大坐标与第一坐标都相同且第二坐标可比。这正是 Devlin 记录为 Godel 序数配对之基的序，也是 Jech 的 `Ord × Ord` 典范良序；它按字面读作：先最大值，再第一坐标，再第二坐标。三歧是先比较最大值、再第一坐标、再第二坐标的三歧；良基性则是良基成员序的字典积，由良序束叠好，再沿「把一对连同其最大值一并记录」的单射拉回。
<!--/-->

```agda
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

  lex2 : SWO (⟪ α ⟫ × ⟪ α ⟫)
  lex2 = prodSWO ordSWO ordSWO

  lex3 : SWO (⟪ α ⟫ × (⟪ α ⟫ × ⟪ α ⟫))
  lex3 = prodSWO ordSWO lex2

  module L3 = SWO lex3

  ¬<₁ : (m : ⟪ α ⟫) {n : ⟪ α ⟫} → m ≡ n → (m ≺₁ n → Empty.⊥)
  ¬<₁ m {n} q h = irr₁ m (subst (λ w → m ≺₁ w) (sym q) h)

  subrel : {p q : Pair} → p ≺ q → f p L3.<∙ f q
  subrel {a , b} {c , d} (inl h) =
    inl h
  subrel {a , b} {c , d} (inr (e , inl h)) =
    inr (¬<₁ (maxOrd a b) e , ¬<₁ (maxOrd c d) (sym e) , inl h)
  subrel {a , b} {c , d} (inr (e , inr (f , h))) =
    inr (¬<₁ (maxOrd a b) e , ¬<₁ (maxOrd c d) (sym e)
       , inr (¬<₁ a f , ¬<₁ c (sym f) , h))

  wf≺ : WellFounded _≺_
  wf≺ p = go (L3.wf∙ (f p))
    where
    go : {q : Pair} → Acc (L3._<∙_) (f q) → Acc _≺_ q
    go {q} (acc r) = acc (λ q' q'≺q → go (r (f q') (subrel {q'} {q} q'≺q)))

  godSWO : SWO Pair
  godSWO = record
    { _<∙_   = _≺_
    ; tri∙   = tri≺
    ; irr∙   = irr≺
    ; trans∙ = trans≺
    ; wf∙    = wf≺ }
```

<!--en-->
The collapse of a well-order into the ordinals, which is the order-type
argument, runs by recursion on the order itself. The step at a pair takes the
union, over all pairs, of the successor of the recursive value where the pair
lies below the current one, and the empty set elsewhere. The union is indexed
by the small type of all pairs, so the filter needs to decide the order at each
pair; this is the chapter's one classical step beyond the comparison that
trichotomy already spends.
<!--zh-->
把良序坍缩进序数的操作，也就是序型论证，沿序本身递归。在某对处的步骤，取所有对上的并：凡位于当前对之下的对，取其递归值的后继，其余取空集。并的索引是小类型「所有对」，故过滤器要在每一对处判定序关系；这是本章在比较 (三歧已为之付款) 之外的唯一一处经典步骤。
<!--/-->

```agda
  ≺₁-dec : (m n : ⟪ α ⟫) → (m ≺₁ n) ⊎ ((m ≺₁ n) → Empty.⊥)
  ≺₁-dec m n = go (tri₁ m n)
    where
    go : Tri (m ≺₁ n) (m ≡ n) (n ≺₁ m) → (m ≺₁ n) ⊎ ((m ≺₁ n) → Empty.⊥)
    go (lt h) = inl h
    go (eq p) = inr (λ h → irr₁ n (subst (λ w → w ≺₁ n) p h))
    go (gt h) = inr (λ h' → irr₁ m (trans₁ m n m h' h))

  ≡₁-dec : (m n : ⟪ α ⟫) → (m ≡ n) ⊎ ((m ≡ n) → Empty.⊥)
  ≡₁-dec m n = go (tri₁ m n)
    where
    go : Tri (m ≺₁ n) (m ≡ n) (n ≺₁ m) → (m ≡ n) ⊎ ((m ≡ n) → Empty.⊥)
    go (lt h) = inr (λ q → irr₁ m (subst (λ w → m ≺₁ w) (sym q) h))
    go (eq p) = inl p
    go (gt h) = inr (λ q → irr₁ n (subst (λ w → n ≺₁ w) q h))

  ≺-dec : (p q : Pair) → (p ≺ q) ⊎ ((p ≺ q) → Empty.⊥)
  ≺-dec (a , b) (c , d) = goM (≺₁-dec (maxOrd a b) (maxOrd c d))
                                (≡₁-dec (maxOrd a b) (maxOrd c d))
    where
    M₁ = maxOrd a b
    M₂ = maxOrd c d

    goY : ((M₁ ≺₁ M₂) → Empty.⊥) → (M₁ ≡ M₂) → ((a ≺₁ c) → Empty.⊥) → (a ≡ c)
        → (b ≺₁ d) ⊎ ((b ≺₁ d) → Empty.⊥)
        → ((a , b) ≺ (c , d)) ⊎ (((a , b) ≺ (c , d)) → Empty.⊥)
    goY ¬h e ¬h' f (inl h'') = inl (inr (e , inr (f , h'')))
    goY ¬h e ¬h' f (inr ¬h'') = inr refuteY
      where
      refuteY : ((a , b) ≺ (c , d)) → Empty.⊥
      refuteY (inl h) = ¬h h
      refuteY (inr (e' , inl x)) = ¬h' x
      refuteY (inr (e' , inr (f' , y))) = ¬h'' y

    goX : ((M₁ ≺₁ M₂) → Empty.⊥) → (M₁ ≡ M₂)
        → (a ≺₁ c) ⊎ ((a ≺₁ c) → Empty.⊥) → (a ≡ c) ⊎ ((a ≡ c) → Empty.⊥)
        → ((a , b) ≺ (c , d)) ⊎ (((a , b) ≺ (c , d)) → Empty.⊥)
    goX ¬h e (inl h') _ = inl (inr (e , inl h'))
    goX ¬h e (inr ¬h') (inl f) = goY ¬h e ¬h' f (≺₁-dec b d)
    goX ¬h e (inr ¬h') (inr ¬f) = inr refuteX
      where
      refuteX : ((a , b) ≺ (c , d)) → Empty.⊥
      refuteX (inl h) = ¬h h
      refuteX (inr (e' , inl x)) = ¬h' x
      refuteX (inr (e' , inr (f' , _))) = ¬f f'

    goM : (M₁ ≺₁ M₂) ⊎ ((M₁ ≺₁ M₂) → Empty.⊥)
        → (M₁ ≡ M₂) ⊎ ((M₁ ≡ M₂) → Empty.⊥)
        → ((a , b) ≺ (c , d)) ⊎ (((a , b) ≺ (c , d)) → Empty.⊥)
    goM (inl h) _ = inl (inl h)
    goM (inr ¬h) (inl e) = goX ¬h e (≺₁-dec a c) (≡₁-dec a c)
    goM (inr ¬h) (inr ¬e) = inr refuteM
      where
      refuteM : ((a , b) ≺ (c , d)) → Empty.⊥
      refuteM (inl h) = ¬h h
      refuteM (inr (e' , _)) = ¬e e'
```

<!--en-->
## The collapse into the ordinals
<!--zh-->
## 坍缩进序数
<!--/-->

<!--en-->
The recursion follows the rank chapter's pattern exactly: a well-founded
recursion on the order, sealed at birth, with the computation rule inside the
seal and every later fact proved against the computation rule. The collapse of
a pair is an ordinal, it increases strictly along the order, and it is
injective, because two pairs with the same collapse would have to be ordered
one way, forcing an ordinal to belong to itself.
<!--zh-->
这个递归完全沿袭秩一章的模式：沿序的良基递归，出生即封，计算规则住在封内，此后每条事实都对照计算规则证明。一对的坍缩是序数，沿序严格增长，且单射，因为坍缩相同的两对若可比较，就会迫使一个序数属于自身。
<!--/-->

```agda
  colPick : (p : Pair) (rec : ∀ r → r ≺ p → S) (r : Pair)
          → (r ≺ p) ⊎ ((r ≺ p) → Empty.⊥) → S
  colPick p rec r (inl pr) = sucV (rec r pr)
  colPick p rec r (inr _)  = ∅

  colStep : (p : Pair) → (∀ r → r ≺ p → S) → S
  colStep p rec = ⋃ (sett Pair (λ r → colPick p rec r (≺-dec r p)))

  module W = WFI wf≺

  opaque
    col : Pair → S
    col = W.induction {P = λ _ → S} colStep

    col-compute : (p : Pair) → col p ≡ colStep p (λ r _ → col r)
    col-compute = W.induction-compute colStep

  col-ord : (p : Pair) → IsOrd (col p)
  col-ord = W.induction {P = λ p → IsOrd (col p)} step
    where
    step : (p : Pair) → (∀ r → r ≺ p → IsOrd (col r)) → IsOrd (col p)
    step p ih = subst IsOrd (sym (col-compute p)) (setUnion-ord Pair g gOrd)
      where
      g : Pair → S
      g r = colPick p (λ r _ → col r) r (≺-dec r p)
      gOrd : (r : Pair) → IsOrd (g r)
      gOrd r = go (≺-dec r p)
        where
        go : (d : (r ≺ p) ⊎ ((r ≺ p) → Empty.⊥))
           → IsOrd (colPick p (λ r _ → col r) r d)
        go (inl pr) = suc-ord (ih r pr)
        go (inr _)  = ∅-ord

  col-mono : {p q : Pair} → p ≺ q → ⟨ col p ∈ˢ col q ⟩
  col-mono {p} {q} pq =
    subst (λ w → ⟨ col p ∈ˢ w ⟩) (sym (col-compute q))
      (∈∈ₛ {a = col p} {b = ⋃ (sett Pair g)} .snd
        (union-ax (sett Pair g) (col p) .snd
          ∣ sucV (col p) , (w∈ₛsett , colp∈ₛsuc) ∣₁))
    where
    g : Pair → S
    g r = colPick q (λ r _ → col r) r (≺-dec r q)
    gq : g p ≡ sucV (col p)
    gq = go (≺-dec p q)
      where
      go : (d : (p ≺ q) ⊎ ((p ≺ q) → Empty.⊥))
         → colPick q (λ r _ → col r) p d ≡ sucV (col p)
      go (inl _) = refl
      go (inr ¬pq) = Empty.rec (¬pq pq)
    w∈ₛsett : ⟨ sucV (col p) ∈ₛ sett Pair g ⟩
    w∈ₛsett = ∈∈ₛ {a = sucV (col p)} {b = sett Pair g} .fst ∣ p , gq ∣₁
    colp∈ₛsuc : ⟨ col p ∈ₛ sucV (col p) ⟩
    colp∈ₛsuc = ∈∈ₛ {a = col p} {b = sucV (col p)} .fst (self∈sucV (col p))

  col-inj : {p q : Pair} → col p ≡ col q → p ≡ q
  col-inj {p} {q} e = go (tri≺ p q)
    where
    go : Tri (p ≺ q) (p ≡ q) (q ≺ p) → p ≡ q
    go (lt pq) = Empty.rec
      (∈-irrefl (col q) (subst (λ w → ⟨ w ∈ˢ col q ⟩) e (col-mono pq)))
    go (eq r)  = r
    go (gt qp) = Empty.rec
      (∈-irrefl (col p) (subst (λ w → ⟨ w ∈ˢ col p ⟩) (sym e) (col-mono qp)))
```

<!--en-->
## The order type
<!--zh-->
## 序型
<!--/-->

<!--en-->
The collapses of all pairs are ordinals, so their successors close into a
single ordinal, the order type of the product: the union of the successors of
the collapses. Every collapse lies inside it, so reading the collapse back
through the fiber of that ordinal's index yields an injection of the product
into the order type, with injectivity transported from the collapse. The
injection is a bijection onto the order type: a member of a collapse sits
inside the successor of the collapse of some earlier pair, so by descent along
the well-order it is itself a collapse, and every member of the order type is
one. This is the order-type certificate the classical route builds on: the
product well-orders canonically, and its order type is exactly `τ`.
<!--zh-->
所有对的坍缩都是序数，故它们的后继收拢进单一序数，即积的序型：坍缩之后继的并。每个坍缩都落在它里面，于是经该序数索引的纤维把坍缩读回来，就得到积到序型的单射，单射性由坍缩搬运。这条单射是到序型上的双射：某坍缩的成员落在某个更早对之坍缩的后继里面，故沿良序下降，它自身就是坍缩，于是序型的每个成员都是坍缩。这正是经典路线所依赖的序型证书：积被典范地良序化，而它的序型恰是 `τ`。
<!--/-->

```agda
  τ : S
  τ = ⋃ (sett Pair (λ p → sucV (col p)))

  τ-ord : IsOrd τ
  τ-ord = setUnion-ord Pair (λ p → sucV (col p)) (λ p → suc-ord (col-ord p))

  col∈τ : (p : Pair) → ⟨ col p ∈ˢ τ ⟩
  col∈τ p = ∈∈ₛ {a = col p} {b = τ} .snd
    (union-ax (sett Pair (λ q → sucV (col q))) (col p) .snd
      ∣ sucV (col p) , (w∈ₛsett , colp∈ₛsuc) ∣₁)
    where
    w∈ₛsett : ⟨ sucV (col p) ∈ₛ sett Pair (λ q → sucV (col q)) ⟩
    w∈ₛsett = ∈∈ₛ {a = sucV (col p)} {b = sett Pair (λ q → sucV (col q))} .fst
      ∣ p , refl ∣₁
    colp∈ₛsuc : ⟨ col p ∈ₛ sucV (col p) ⟩
    colp∈ₛsuc = ∈∈ₛ {a = col p} {b = sucV (col p)} .fst (self∈sucV (col p))

  col→τ : Pair → ⟪ τ ⟫
  col→τ p = fiber τ (col∈τ p) .fst

  col→τ-inj : {p q : Pair} → col→τ p ≡ col→τ q → p ≡ q
  col→τ-inj {p} {q} e =
    col-inj (sym (fiber τ (col∈τ p) .snd)
              ∙ cong (⟪ τ ⟫↪) e
              ∙ fiber τ (col∈τ q) .snd)

  col-img : (q : Pair) (b : S) → ⟨ b ∈ˢ col q ⟩
          → ∥ Σ[ p ∈ Pair ] (col p ≡ b) ∥₁
  col-img = W.induction {P = P} step
    where
    P : Pair → Type (ℓ-suc ℓ)
    P q = (b : S) → ⟨ b ∈ˢ col q ⟩ → ∥ Σ[ p ∈ Pair ] (col p ≡ b) ∥₁

    g : (q : Pair) → Pair → S
    g q r = colPick q (λ r _ → col r) r (≺-dec r q)

    g-inl : (q : Pair) (r : Pair) (pr : r ≺ q) → g q r ≡ sucV (col r)
    g-inl q r pr = go (≺-dec r q)
      where
      go : (d : (r ≺ q) ⊎ ((r ≺ q) → Empty.⊥))
         → colPick q (λ r _ → col r) r d ≡ sucV (col r)
      go (inl _) = refl
      go (inr ¬pr) = Empty.rec (¬pr pr)

    g-inr : (q : Pair) (r : Pair) (¬pr : (r ≺ q) → Empty.⊥) → g q r ≡ ∅
    g-inr q r ¬pr = go (≺-dec r q)
      where
      go : (d : (r ≺ q) ⊎ ((r ≺ q) → Empty.⊥))
         → colPick q (λ r _ → col r) r d ≡ ∅
      go (inl pr) = Empty.rec (¬pr pr)
      go (inr _) = refl

    step : (q : Pair) → (∀ r → r ≺ q → P r) → P q
    step q ih b b∈cq = viaUnion (subst (λ w → ⟨ b ∈ˢ w ⟩) (col-compute q) b∈cq)
      where
      U : S
      U = ⋃ (sett Pair (g q))

      go2 : (v : S) → ⟨ b ∈ₛ v ⟩ → Σ[ r ∈ Pair ] (g q r ≡ v)
          → ∥ Σ[ p ∈ Pair ] (col p ≡ b) ∥₁
      go2 v b∈ₛv (r , gr≡v) = decide (≺-dec r q)
        where
        b∈gr : ⟨ b ∈ₛ g q r ⟩
        b∈gr = subst (λ w → ⟨ b ∈ₛ w ⟩) (sym gr≡v) b∈ₛv

        decide : (r ≺ q) ⊎ ((r ≺ q) → Empty.⊥)
               → ∥ Σ[ p ∈ Pair ] (col p ≡ b) ∥₁
        decide (inl pr) = ∈sucV-elim {A = col r} {x = b} squash₁ b∈sr
          (λ b∈r → ih r pr b b∈r)
          (λ b≡r → ∣ r , sym b≡r ∣₁)
          where
          b∈sr : ⟨ b ∈ˢ sucV (col r) ⟩
          b∈sr = ∈∈ₛ {a = b} {b = sucV (col r)} .snd
            (subst (λ w → ⟨ b ∈ₛ w ⟩) (g-inl q r pr) b∈gr)
        decide (inr ¬pr) =
          Empty.rec (∅-empty b (subst (λ w → ⟨ b ∈ₛ w ⟩) (g-inr q r ¬pr) b∈gr))

      go1 : Σ[ v ∈ S ] (⟨ v ∈ₛ sett Pair (g q) ⟩ × ⟨ b ∈ₛ v ⟩)
          → ∥ Σ[ p ∈ Pair ] (col p ≡ b) ∥₁
      go1 (v , (v∈ₛsett , b∈ₛv)) = PT.rec squash₁ (go2 v b∈ₛv)
        (∈∈ₛ {a = v} {b = sett Pair (g q)} .snd v∈ₛsett)

      viaUnion : ⟨ b ∈ˢ U ⟩ → ∥ Σ[ p ∈ Pair ] (col p ≡ b) ∥₁
      viaUnion b∈ = PT.rec squash₁ go1
        (union-ax (sett Pair (g q)) b .fst
          (∈∈ₛ {a = b} {b = U} .fst b∈))

  col-surj : (b : S) → ⟨ b ∈ˢ τ ⟩ → ∥ Σ[ p ∈ Pair ] (col p ≡ b) ∥₁
  col-surj b b∈τ = PT.rec squash₁ go1
    (union-ax (sett Pair (λ q → sucV (col q))) b .fst
      (∈∈ₛ {a = b} {b = τ} .fst b∈τ))
    where
    go2 : (v : S) → ⟨ b ∈ₛ v ⟩ → Σ[ q ∈ Pair ] (sucV (col q) ≡ v)
        → ∥ Σ[ p ∈ Pair ] (col p ≡ b) ∥₁
    go2 v b∈ₛv (q , sq≡v) = ∈sucV-elim {A = col q} {x = b} squash₁ b∈sq
      (λ b∈q → col-img q b b∈q)
      (λ b≡q → ∣ q , sym b≡q ∣₁)
      where
      b∈sq : ⟨ b ∈ˢ sucV (col q) ⟩
      b∈sq = ∈∈ₛ {a = b} {b = sucV (col q)} .snd
        (subst (λ w → ⟨ b ∈ₛ w ⟩) (sym sq≡v) b∈ₛv)

    go1 : Σ[ v ∈ S ] (⟨ v ∈ₛ sett Pair (λ q → sucV (col q)) ⟩ × ⟨ b ∈ₛ v ⟩)
        → ∥ Σ[ p ∈ Pair ] (col p ≡ b) ∥₁
    go1 (v , (v∈ₛsett , b∈ₛv)) = PT.rec squash₁ (go2 v b∈ₛv)
      (∈∈ₛ {a = v} {b = sett Pair (λ q → sucV (col q))} .snd v∈ₛsett)

  col→τ-surj : (m : ⟪ τ ⟫) → ∥ Σ[ p ∈ Pair ] (col→τ p ≡ m) ∥₁
  col→τ-surj m = PT.map hit (col-surj (⟪ τ ⟫↪ m) (member τ m))
    where
    hit : Σ[ p ∈ Pair ] (col p ≡ ⟪ τ ⟫↪ m) → Σ[ p ∈ Pair ] (col→τ p ≡ m)
    hit (p , e) = p , ↪-inj {a = τ} (fiber τ (col∈τ p) .snd ∙ e)
```

<!--en-->
## The pairing, given the bound
<!--zh-->
## 给定界后的配对
<!--/-->

<!--en-->
The product now bijects onto the ordinal `τ`, the order type of the canonical
well-ordering. The pairing the cardinal step consumes needs one more injection,
of `τ` into `α` itself. The classical theorem that supplies it is the square
law of infinite ordinals, that the product of an infinite ordinal's members is
equinumerous to the ordinal, whose proof in the textbook route runs through
ordinal arithmetic that the tree does not yet carry; the chapter states it as
the bound hypothesis below rather than postulating it. Given the bound, the
pairing and its injectivity in the exact shape the cardinal probe consumes
fall out by composition.
<!--zh-->
积现已双射到序数 `τ`，即典范良序的序型。基数步骤消费的配对还需要一条单射，把 `τ` 注入 `α` 自身。供给它的经典定理是无穷序数的平方律，即无穷序数之成员的积与该序数等势，教科书路线中它的证明要穿过本书尚未拥有的序数算术；本章把它陈述为下面的界假设，而不是 postulate 它。给定这个界，配对及其单射性便以基数探针消费的确切形状经复合得到。
<!--/-->

```agda
  module Pairing (bound : ⟪ τ ⟫ → ⟪ α ⟫)
                 (bound-inj : {m n : ⟪ τ ⟫} → bound m ≡ bound n → m ≡ n) where

    pair : ⟪ α ⟫ → ⟪ α ⟫ → ⟪ α ⟫
    pair a b = bound (col→τ (a , b))

    pair-inj : {a b c d : ⟪ α ⟫} → pair a b ≡ pair c d → (a ≡ c) × (b ≡ d)
    pair-inj {a} {b} {c} {d} e =
      (cong fst (col→τ-inj (bound-inj e)))
      , (cong snd (col→τ-inj (bound-inj e)))
```

<!--en-->
## Recap
<!--zh-->
## 小结
<!--/-->

<!--en-->
For every ordinal `α`, the index of the product carries the canonical
well-ordering, with the four laws certified, and the collapse reads each pair
back as an ordinal, bijectively, onto the order type `τ` of that well-ordering.
None of this uses the infinitude of `α`: the well-ordering and its order type
are pure order theory, classical only through the comparison that the linear
chapter already pays for. What remains is the bound, the classical square law
that `τ` is equinumerous to `α` itself for infinite `α`; the pairing in the
exact shape the cardinal probe consumes is delivered conditional on it, and the
report prices the arithmetic the square law needs.
<!--zh-->
对每个序数 `α`，积的索引带有典范良序，四条定律皆经认证；坍缩把每对双射地读成序数，落在该良序的序型 `τ` 上。这些都用不到 `α` 的无穷性：良序及其序型是纯序理论，经典性仅来自线性一章已然付款的比较。余下的界，即无穷 `α` 时 `τ` 与 `α` 自身等势的经典平方律，正是所缺；基数探针所消费的确切形状的配对在给定该界后交付，而报告为平方律所需的算术定价。
<!--/-->
