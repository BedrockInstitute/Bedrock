# Strict well-orders, and least elements

<!--en-->
One construction ahead needs to *choose*: the axiom of choice, at the end of the
book, has to pick an element out of each cell of a family, and the classical way
to make that choice is to well-order the candidates and take the least one that
qualifies.

The reflection argument was expected to be a second consumer and is not. It was
delivered with no order at all, as a ladder whose limit answers for every matrix
at once, built jointly rather than selected from. So this vocabulary has one
consumer rather than two, and it is `L.Choice.Transversal`{.Agda}, the last
chapter of the book: the search below is what picks a point out of each cell of a
disjoint family.

This chapter provides the vocabulary. A strict well-order on a type is a
relation that is trichotomous, irreflexive, transitive and well founded, bundled
as a record so that later chapters can carry one around as data. The bundle is
level-generic in a way worth one remark: the carrier and the relation take
*separate* universe levels, because the order that Part 4 eventually builds
compares formulas, which are small, by data that mentions ordinals, which are
not.

The theorem is that a non-empty subset has a least element, and it is unique.
Uniqueness is free from trichotomy. Existence is not: deciding, at each step,
whether anything smaller still qualifies is exactly a decision about an
arbitrary predicate, so this is the second place the book spends the excluded
middle. Unlike the first, here the cost buys a genuine choice function rather
than a comparison.

The assumption sits on that one theorem rather than on the chapter, which is
worth doing wherever it can be done: the bundle, the uniqueness of least
elements, and everything a later chapter needs in order to *state* an order are
constructive, and only the search is not.
<!--zh-->
接下来有一个构造需要**选取**：本书末尾的选择公理要从一个族的每一格里挑出一个元素，而作出这个选取的经典方式，是把候选者良序化，再取合格者中最小的那个。

反射论证本来预期是第二个消费方，结果不是。它交付时根本没有用到任何序，而是一道阶梯，其极限一举为每个母式作答，是合起来造出来的、不是从中挑出来的。故这套词汇只有一个消费方、不是两个，那就是本书的最后一章 `L.Choice.Transversal`{.Agda}：下文那场搜索，正是从不交族的每一格里挑出一个点的那件东西。

本章提供相应的词汇。类型上的严格良序，是一个三歧、非自反、传递且良基的关系，打成 record，好让后续章节把它当数据携带。这个束的层级泛型有一点值得说明：载体与关系取**各自独立**的宇宙层级，因为第四部最终造出的那个序比较的是公式 (小的)，而据以比较的数据要提到序数 (不小)。

定理是：非空子集有极小元，且唯一。唯一性由三歧免费得到。存在性则不然：每一步都要判定「是否还有更小的合格者」，那恰是关于任意谓词的一次判定，故这是本书第二次花费排中律。与第一次不同，这里的代价换来的是一个真正的选择函数，而不是一次比较。

这个假设落在那一条定理上，而非落在整章上，而这件事只要做得到就值得做：束、极小元的唯一性，以及后续章节**陈述**一个序所需的一切，都是构造性的，唯有搜索不是。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module L.WellOrder.Base {ℓₚ : Level} where

open import Cubical.Induction.WellFounded using ( Acc; acc; WellFounded )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁; ∣_∣₁; squash₁ )
open import Cubical.Data.Sigma using ( Σ≡Prop )
open import Cubical.Foundations.HLevels using ( isProp×; isPropΠ )
open import Cubical.Relation.Nullary using ( ¬_; isProp¬ )
import Cubical.Data.Empty as Empty
open import Cubical.Data.Sum using ( _⊎_; inl; inr )
open import Cubical.Data.Nat.Order
  using ( _<_; <-trans; ¬m<m; <-wellfounded; Trichotomy; _≟_ )
open Trichotomy
```

<!--en-->
## Trichotomy, as data
<!--zh-->
## 作为数据的三歧
<!--/-->

<!--en-->
Three mutually exclusive alternatives, carried as an inductive type rather than
a nested sum, so that a proof can name the case it is in.
<!--zh-->
三个互斥的可能，以归纳类型而非嵌套的和类型携带，好让证明能点名自己所处的情形。
<!--/-->

```agda
data Tri {ℓ₁ ℓ₂ ℓ₃ : Level} (A : Type ℓ₁) (B : Type ℓ₂) (C : Type ℓ₃)
       : Type (ℓ-max ℓ₁ (ℓ-max ℓ₂ ℓ₃)) where
  lt : A → Tri A B C
  eq : B → Tri A B C
  gt : C → Tri A B C
```

<!--en-->
## The bundle
<!--zh-->
## 束
<!--/-->

<!--en-->
The four laws, packaged. Well-foundedness is the library's accessibility
predicate, which is what makes the least-element search below terminate.
<!--zh-->
四条定律，打包起来。良基性取库的可及性谓词，正是它使下文取极小元的搜索得以终止。
<!--/-->

```agda
record SWO {ℓc : Level} (A : Type ℓc) : Type (ℓ-max ℓc (ℓ-suc ℓₚ)) where
  field
    _<∙_   : A → A → Type ℓₚ
    tri∙   : (a b : A) → Tri (a <∙ b) (a ≡ b) (b <∙ a)
    irr∙   : (a : A) → ¬ a <∙ a
    trans∙ : (a b c : A) → a <∙ b → b <∙ c → a <∙ c
    wf∙    : WellFounded _<∙_
```

<!--en-->
## Least elements
<!--zh-->
## 极小元
<!--/-->

<!--en-->
Being least for a predicate is satisfying it while nothing satisfying it is
strictly smaller. That is a proposition, and so is being *a* least element:
given two, trichotomy rules out both strict cases and leaves equality. This is
what lets the search below deliver an honest element out of a merely truncated
non-emptiness, since a proposition-valued goal absorbs the truncation.
<!--zh-->
对谓词而言的极小，指自身满足它，且没有满足它者严格更小。这是一个命题，而「是一个极小元」也是：给定两个，三歧排除两个严格情形，只留下相等。正是这一点使下面的搜索能从仅仅截断的非空性中交出一个诚实的元素，因为命题值的目标吸收截断。
<!--/-->

```agda
module _ {ℓc : Level} {A : Type ℓc} (w : SWO {ℓc} A) where
  open SWO w

  IsLeast : {ℓ'' : Level} → (A → hProp ℓ'') → A → Type (ℓ-max ℓc (ℓ-max ℓₚ ℓ''))
  IsLeast P a = ⟨ P a ⟩ × ((b : A) → ⟨ P b ⟩ → ¬ b <∙ a)

  isPropIsLeast : {ℓ'' : Level} (P : A → hProp ℓ'') (a : A) → isProp (IsLeast P a)
  isPropIsLeast P a = isProp× (snd (P a)) (isPropΠ λ b → isPropΠ λ _ → isProp¬ _)

  isPropLeastOf : {ℓ'' : Level} (P : A → hProp ℓ'')
                → isProp (Σ[ a ∈ A ] IsLeast P a)
  isPropLeastOf P (m , pm , minm) (m' , pm' , minm') =
    Σ≡Prop (isPropIsLeast P) (decide (tri∙ m m'))
    where
    decide : Tri (m <∙ m') (m ≡ m') (m' <∙ m) → m ≡ m'
    decide (lt m<m') = Empty.rec (minm' m pm m<m')
    decide (eq e)    = e
    decide (gt m'<m) = Empty.rec (minm m' pm' m'<m)
```

<!--en-->
And the search. Start anywhere in the subset and descend: ask whether some
smaller element still satisfies the predicate; if one does, recurse into it,
which terminates because the relation is well founded; if none does, the current
element is least by definition. The question asked at each step is about an
arbitrary predicate, and that is where the excluded middle enters.
<!--zh-->
然后是搜索。从子集中任意一点出发向下走：问是否有更小的元素仍满足该谓词；若有，就递归进去，而这会终止，因为关系良基；若无，当前元素按定义即为极小。每一步所问的问题关乎任意谓词，排中律正是从那里进入的。
<!--/-->

```agda
  leastOf : {ℓ'' : Level} → LEM (ℓ-max ℓc (ℓ-max ℓₚ ℓ''))
          → (P : A → hProp ℓ'')
          → ∥ Σ[ a ∈ A ] ⟨ P a ⟩ ∥₁ → Σ[ a ∈ A ] IsLeast P a
  leastOf {ℓ''} lem P =
    PT.rec (isPropLeastOf P) (λ { (a₀ , pa₀) → go a₀ (wf∙ a₀) pa₀ })
    where
    go : (a : A) → Acc _<∙_ a → ⟨ P a ⟩ → Σ[ m ∈ A ] IsLeast P m
    go a (acc rs) pa = decide (lem (Smaller , squash₁))
      where
      Smaller : Type (ℓ-max ℓc (ℓ-max ℓₚ ℓ''))
      Smaller = ∥ Σ[ b ∈ A ] ((b <∙ a) × ⟨ P b ⟩) ∥₁
      decide : Smaller ⊎ (Smaller → Empty.⊥) → Σ[ m ∈ A ] IsLeast P m
      decide (inl q) = PT.rec (isPropLeastOf P)
        (λ { (b , (b<a , pb)) → go b (rs b b<a) pb }) q
      decide (inr ¬q) = a , (pa , λ b pb b<a → ¬q ∣ b , (b<a , pb) ∣₁)
```

<!--en-->
## The ground order and the pullback
<!--zh-->
## 地面序与拉回
<!--/-->

<!--en-->
The bundle is the interface the choice construction takes, and the two
order-builders it reads directly stay with it. The numbers carry their usual
order, with the relation lifted to this chapter's relation level; trichotomy
and well-foundedness are library facts, lifted. The stacking kit (the unit
ground order, the sum, the product, the length-gated list order, and the
`connex`{.Agda} exchange lemma) lives in
`L.WellOrder.Combinators`{.Agda}.
<!--zh-->
束是选择构造取用的接口，它直接读的两个造序器随束留下。自然数带其通常的序，关系提升到本章的关系层级；三歧与良基是库中现成的事实，提升即得。叠放配件 (单位地面序、和、积、以长度为门的表序，以及兑换引理 `connex`{.Agda}) 住在 `L.WellOrder.Combinators`{.Agda} 里。
<!--/-->

```agda
natSWO : SWO ℕ
natSWO = record
  { _<∙_   = _≺ᴺ_
  ; tri∙   = triᴺ
  ; irr∙   = λ m h → ¬m<m (lower h)
  ; trans∙ = λ m n k h h' → lift (<-trans (lower h) (lower h'))
  ; wf∙    = wfᴺ }
  where
  _≺ᴺ_ : ℕ → ℕ → Type ℓₚ
  m ≺ᴺ n = Lift {ℓ-zero} {ℓₚ} (m < n)

  triᴺ : (m n : ℕ) → Tri (m ≺ᴺ n) (m ≡ n) (n ≺ᴺ m)
  triᴺ m n with m ≟ n
  ... | lt h = lt (lift h)
  ... | eq p = eq p
  ... | gt h = gt (lift h)

  wfᴺ : WellFounded _≺ᴺ_
  wfᴺ n = go n (<-wellfounded n)
    where
    go : (m : ℕ) → Acc _<_ m → Acc _≺ᴺ_ m
    go m (acc r) = acc λ k h → go k (r k (lower h))
```

<!--en-->
And pulling back. An injection into an ordered type induces an order on its
source: compare the images. Trichotomy's equality case is the one place
injectivity is spent, and accessibility transports backwards along the map with
no further argument.
<!--zh-->
最后是拉回。一个到带序型的单射在其源上诱导出一个序：比较像即可。三歧的相等情形是单射性唯一被花费的地方，而可及性沿映射向后搬运，无需更多论证。
<!--/-->

```agda
module _ {ℓx ℓy : Level} {X : Type ℓx} {Y : Type ℓy}
         (v : SWO Y) (f : X → Y) (inj : (a b : X) → f a ≡ f b → a ≡ b) where
  private
    module V = SWO v

    _≺ᶠ_ : X → X → Type ℓₚ
    a ≺ᶠ b = f a V.<∙ f b

    triᶠ : (a b : X) → Tri (a ≺ᶠ b) (a ≡ b) (b ≺ᶠ a)
    triᶠ a b with V.tri∙ (f a) (f b)
    ... | lt h = lt h
    ... | eq p = eq (inj a b p)
    ... | gt h = gt h

    accPull : (a : X) → Acc V._<∙_ (f a) → Acc _≺ᶠ_ a
    accPull a (acc r) = acc λ b h → accPull b (r (f b) h)

  pullSWO : SWO X
  pullSWO = record
    { _<∙_   = _≺ᶠ_
    ; tri∙   = triᶠ
    ; irr∙   = λ a h → V.irr∙ (f a) h
    ; trans∙ = λ a b c h h' → V.trans∙ (f a) (f b) (f c) h h'
    ; wf∙    = λ a → accPull a (V.wf∙ (f a)) }
```

<!--en-->
## Recap
<!--zh-->
## 小结
<!--/-->

<!--en-->
`SWO`{.Agda} bundles a strict well-order, and `leastOf`{.Agda} extracts the least
element of any non-empty subset, uniquely (`isPropLeastOf`{.Agda}). The bundle
is the interface the choice construction takes; it does not care which order it
is handed, which is why the chapter is generic. The excluded middle is spent
once, on the decision at each descent step, and the
level discipline (carrier and relation separately generic) is what will let the
order of Part 4 compare small things by large data. The natural-number order
`natSWO`{.Agda} and the pullback `pullSWO`{.Agda} along an injection stay with
the bundle; the stacking kit (the unit order, the sum, the product, and the
length-gated list order, with `connex`{.Agda} as the exchange lemma) is now its
own chapter, `L.WellOrder.Combinators`{.Agda}.
<!--zh-->
`SWO`{.Agda} 把严格良序打成束，`leastOf`{.Agda} 取出任一非空子集的极小元，且唯一 (`isPropLeastOf`{.Agda})。这个束是选择构造取用的接口；它不在乎拿到的是哪个序，这正是本章泛型的原因。排中律花在一处，即每一步下降时的那次判定，且只记在那一条定理账上：此处其余一切都是构造性的。而层级纪律 (载体与关系各自泛型) 将使第四部的那个序能以大的数据去比较小的东西。自然数序 `natSWO`{.Agda} 与沿单射的拉回 `pullSWO`{.Agda} 随束留下；叠放配件 (单位序、和、积，以及以长度为门的表序，外加兑换引理 `connex`{.Agda}) 现在自成一章，即 `L.WellOrder.Combinators`{.Agda}。
<!--/-->
