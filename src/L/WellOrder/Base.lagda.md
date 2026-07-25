# Strict well-orders, and least elements

<!--en-->
Two constructions ahead need to *choose*: the reflection argument has to pick a
formula out of a set of formulas that would do, and the axiom of choice, at the
end of the book, has to pick an element out of each cell of a family. Both are
the same move, and the classical way to make it is to well-order the candidates
and take the least one that qualifies.

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
接下来有两个构造需要**选取**：反射论证要从一堆合用的公式里挑出一条，而本书末尾的选择公理要从一个族的每一格里挑出一个元素。二者是同一个动作，而作出这个动作的经典方式，是把候选者良序化，再取合格者中最小的那个。

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
## Recap
<!--zh-->
## 小结
<!--/-->

<!--en-->
`SWO`{.Agda} bundles a strict well-order, and `leastOf`{.Agda} extracts the least
element of any non-empty subset, uniquely (`isPropLeastOf`{.Agda}). The bundle
is the interface the reflection argument and the choice construction both take;
neither cares which order it is handed, which is why the chapter is generic. The
excluded middle is spent once, on the decision at each descent step, and the
level discipline (carrier and relation separately generic) is what will let the
order of Part 4 compare small things by large data.
<!--zh-->
`SWO`{.Agda} 把严格良序打成束，`leastOf`{.Agda} 取出任一非空子集的极小元，且唯一 (`isPropLeastOf`{.Agda})。这个束是反射论证与选择构造共同取用的接口；二者都不在乎拿到的是哪个序，这正是本章泛型的原因。排中律花在一处，即每一步下降时的那次判定，且只记在那一条定理账上：此处其余一切都是构造性的。而层级纪律 (载体与关系各自泛型) 将使第四部的那个序能以大的数据去比较小的东西。
<!--/-->
