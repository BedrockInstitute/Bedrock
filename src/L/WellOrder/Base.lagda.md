# Strict well-orders, and least elements

<!--en-->
Strict well-orders support a recurring mathematical operation: choose the least witness of an inhabited property. This chapter introduces the order bundle, proves existence and uniqueness of least elements, and then assembles the natural numbers as the foundational example used by later constructions.

The carrier and relation may live at separate universe levels. Most of the vocabulary is constructive; excluded middle appears only in the descent that finds a least witness.
<!--zh-->
严格良序支撑一个反复出现的数学操作：从一个非空性质中选取最小见证。本章引入良序束，证明极小元的存在与唯一性，并把自然数装配成后续构造使用的基础例子。

载体与关系可以位于不同宇宙层级。大部分词汇都是构造性的；排中律只出现在寻找最小见证的下降过程里。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module L.WellOrder.Base {ℓₚ : Level} where

open import Cubical.Induction.WellFounded using ( Acc; acc; WellFounded )
open import Cubical.Data.Nat using ( ℕ )
open import Cubical.Data.Nat.Order using ( _<_; <-trans; ¬m<m; <-wellfounded; _≟_ )
import Cubical.Data.Nat.Order as NatOrder
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
## The natural numbers, well-ordered
<!--zh-->
## 自然数，良序化
<!--/-->

<!--en-->
The natural numbers give the basic infinite example of a strict well-order and later count construction stages. The library supplies everything about the usual order on the natural
numbers, so the bundle is assembled rather than proved: the trichotomy is the
library's decision procedure with its three-way answer renamed, and
well-foundedness is the library's own.

The lift is bookkeeping and nothing more. A bundle carries its relation at a
single universe level fixed once for the whole chapter, and the order on the
natural numbers lives at the bottom, so it is raised to meet it. It also demonstrates how a low-level relation is used in a universe-polymorphic bundle.
<!--zh-->
自然数给出严格良序的基本无穷例子，随后也用来为构造阶段计数。关于自然数上通常的序，库已备齐一切，故这个束是装配出来的、而非证出来的：三歧取库的判定程序，把它的三路答案改个名；良基性则直接是库自己的。

提升只是记账，别无他意。一个束把它的关系带在为全章一次固定的单一宇宙层级上，而自然数上的序住在最底层，故把它抬上来相会。它也示范如何在宇宙多态的束中使用低层级关系。
<!--/-->

```agda
liftAcc : (n : ℕ) → Acc _<_ n → Acc (λ a b → Lift {ℓ-zero} {ℓₚ} (a < b)) n
liftAcc n (acc r) = acc (λ m h → liftAcc m (r m (lower h)))

natOrder : SWO {ℓ-zero} ℕ
natOrder = record
  { _<∙_   = λ a b → Lift (a < b)
  ; tri∙   = triOf
  ; irr∙   = λ a h → ¬m<m (lower h)
  ; trans∙ = λ a b c h k → lift (<-trans (lower h) (lower k))
  ; wf∙    = λ n → liftAcc n (<-wellfounded n) }
  where
  triOf : (a b : ℕ) → Tri (Lift (a < b)) (a ≡ b) (Lift (b < a))
  triOf a b = fromNat (a ≟ b)
    where
    fromNat : NatOrder.Trichotomy a b → Tri (Lift (a < b)) (a ≡ b) (Lift (b < a))
    fromNat (NatOrder.lt h) = lt (lift h)
    fromNat (NatOrder.eq h) = eq h
    fromNat (NatOrder.gt h) = gt (lift h)
```

<!--en-->
## Recap
<!--zh-->
## 小结
<!--/-->

<!--en-->
`SWO`{.Agda} bundles a strict well-order, and `leastOf`{.Agda} extracts the least
element of any non-empty subset, uniquely (`isPropLeastOf`{.Agda}). The bundle is a generic interface for later constructions, while `natOrder`{.Agda} is its basic infinite instance. Excluded middle is spent once, on the decision at each descent step; the bundle and the natural-number order remain constructive.
<!--zh-->
`SWO`{.Agda} 把严格良序打成束，`leastOf`{.Agda} 取出任一非空子集的极小元，且唯一 (`isPropLeastOf`{.Agda})。这个束是后续构造使用的泛型接口，而 `natOrder`{.Agda} 是它的基本无穷实例。排中律只花在每一步下降的判定上；良序束与自然数序本身仍是构造性的。
<!--/-->
