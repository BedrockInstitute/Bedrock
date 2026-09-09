<!--en-->
# Choice

Choice asserts that a simultaneous choice function merely exists for every family of merely inhabited fibers indexed by a set. This chapter states that principle level by level, proves that it descends to smaller universes, and derives excluded middle from it by Diaconescu’s theorem.
<!--zh-->
# 选择原理

选择原理断言：对一个以集合为指标、每根纤维都仅仅有元的族，也仅仅存在一个同时从所有纤维中取值的选择函数。本章逐宇宙层级陈述这条原理，证明它能下降到较低层级，并用 Diaconescu 定理由此推出排中律。
<!--ja-->
# 選択原理

選択原理は、集合で添字付けられ、各ファイバーが単に要素を持つ族に対して、同時選択関数が単に存在すると主張します。本章ではこの原理を宇宙レベルごとに述べ、低いレベルへ移せることを示し、ディアコネスクの定理によって排中律を導きます。
<!--/-->

<!--en-->
The classical boundary has a second interface. Alongside the excluded middle,
classical mathematics runs on choice, and this chapter states the book's form of
it, one level at a time, in the same interface style as `LEM`{.Agda}.
**Set-level choice** says that over an h-set of indices, truncation commutes
with the product: if every fiber is merely inhabited, then merely, every fiber
is inhabited at once. This is the type-theoretic reading of "a family of
nonempty sets has a choice function", and the h-set restriction on the index is
exactly what makes the principle valid, since over arbitrary types the principle is simply false.
Like the excluded middle, choice is never assumed globally: a chapter that needs
it takes it as a parameter, and the first to do so is the cumulative-hierarchy model theorem.
<!--zh-->
经典边界还有第二个接口。经典数学除排中律外还依靠选择运转，本章陈述本书采用的形式，即逐层级、与 `LEM`{.Agda} 同款的接口风格。**集合层选择**说：在 h-集索引之上，截断与乘积交换：若每根纤维都仅仅有元，则仅仅地，全体纤维一齐有元。这是「非空集族有选择函数」的类型论读法；索引上的 h-集限制正是这条原理成立的关键，因为对任意类型而言它干脆为假。与排中律一样，选择从不全局假设：需要它的章节以参数领取，而第一个领取者是累积层级的模型定理。
<!--/-->

<!--en-->
The two interfaces are not peers, and this chapter proves it on the spot:
**choice proves the excluded middle**. The observation is due to Diaconescu,
with the type-theoretic form by Goodman and Myhill; it means that at each level
the choice interface already implies the whole classical boundary.
<!--zh-->
两个接口并非平级，本章当场证明这一点：**选择证明排中律**。这个观察出自 Diaconescu，类型论形式归于 Goodman 与 Myhill；它意味着在每个层级上，选择接口都能推出整条经典边界。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

module Base.Choice where

open import Base.Prelude
open import Base.Classical using ( LEM )

open import Cubical.Foundations.Prelude using ( Path )
open import Cubical.Foundations.HLevels using ( isOfHLevelLift )
open import Cubical.Data.Bool using ( Bool; true; false; _≟_ )
open import Cubical.Data.Unit using ( Unit*; tt*; isPropUnit* )
open import Cubical.Relation.Nullary using ( Dec; yes; no )
import Cubical.Data.Sum as Sum
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁ )
open import Cubical.HITs.SetQuotients
  using ( _/_; [_]; eq/; squash/; []surjective; effective )
open import Cubical.Relation.Binary.Base using ( module BinaryRelation )
```

<!--en-->
## The principle

Like the excluded middle, choice passes **downward** through the levels: lift
the index set and the fibers one universe up, choose there, lower the choice
function. A single higher instance therefore covers the levels below.
<!--zh-->
## 原理

与排中律一样，选择沿层级**向下**通行：把索引集与纤维抬升到高一层的宇宙，在那里做选择，再把选择函数降回来。于是较高层级上的单个实例覆盖其下诸层。
<!--ja-->
## 原理

排中律と同様に、選択原理は宇宙レベルを下向きに移せます。添字集合と各ファイバーを一つ上の宇宙へ持ち上げ、そこで選択し、その選択関数を元のレベルへ戻すため、高いレベルの一つの仮定がそれより低いレベルをすべて覆います。
<!--/-->

```agda
SetChoice : ∀ ℓ → Type (ℓ-suc ℓ)
SetChoice ℓ = (X : Type ℓ) → isSet X → (B : X → Type ℓ)
            → ((x : X) → ∥ B x ∥₁) → ∥ ((x : X) → B x) ∥₁
```



```agda
lowerSetChoice : ∀ {ℓ} → SetChoice (ℓ-suc ℓ) → SetChoice ℓ
lowerSetChoice sc X setX B inh =
  PT.map (λ f x → lower (f (lift x)))
         (sc (Lift X) (isOfHLevelLift 2 setX)
             (λ x → Lift (B (lower x)))
             (λ x → PT.map lift (inh (lower x))))
```

<!--en-->
## Diaconescu's theorem

The theorem: given set-level choice, **any** proposition `P` can be decided,
proved or refuted. On its face this is absurd, since a decision procedure has
nothing to act on: an arbitrary `P` offers no case to split on. The proof
instead proceeds *geometrically*. Build a little space whose very
shape depends on `P`: it has one point if `P` holds and two points if it fails.
Put one question about that space to the choice principle; the answer necessarily
reveals the shape, and the shape is `P`.
<!--zh-->
## Diaconescu 定理

定理说：给定集合层选择，**任何**命题 `P` 都可判定，即或证明或反驳。乍看这很荒谬，因为判定程序无从下手：任意的 `P` 没有可供分情况处理的切入口。证明的想法是改从**几何**入手。造一个形状依赖于 `P` 的小空间：`P` 成立时它只有一个点，不成立时有两个点。然后用选择原理回答一个关于这个空间的问题；答案必然透露出形状，而形状就是 `P`。
<!--ja-->
## ディアコネスクの定理

命題 `P` に応じて二点が貼り合わされる集合商を作ります。その商上で選択した二つの値を比較すると `P` を判定できるため、集合レベルの選択原理から排中律が従います。
<!--/-->

<!--en-->
Concretely, fix `P`; everything below lives in a module named after the
theorem's author. Take the two booleans and glue them together exactly when
`P` holds. "Gluing" is a **set quotient**: the points are still `true` and
`false`, but a path is added between them whenever the gluing relation says
so, and the result is truncated to an h-set. The relation is best given as a
four-entry table: trivially satisfied on the diagonal, and **literally `P`
itself** in the two mixed squares, so that "the two points are related" and
"`P` holds" are the same proposition by definition. This last clause is the
key to the whole argument, and it will be used twice below.
<!--zh-->
具体地，固定 `P`；以下一切都设在以定理作者命名的模块里。取两个布尔值，恰在 `P` 成立时把它们粘起来。「粘合」指**集合商**：点仍是 `true` 与 `false`，但凡粘合关系在两点之间成立，就添一条路径，最后把结果截断为 h-集。粘合关系最好用一张四格表给出：对角线上平凡成立，混色的两格**就是 `P` 本身**，于是「这两点相关」与「`P` 成立」按定义是同一个命题。最后这一条是全部论证的关键，下文将用到两次。
<!--/-->

```agda
module Diaconescu {ℓ} (P : hProp ℓ) where

  _~_ : Bool → Bool → Type ℓ
  true  ~ true  = Unit*
  false ~ false = Unit*
  _     ~ _     = ⟨ P ⟩

  Glued : Type ℓ
  Glued = Bool / _~_
```

<!--en-->
Because the relation is a table, its certificates are tables too: propositional
in every square, reflexive on the diagonal, symmetric since the table is, and
transitive by reading off whichever mixed square remains. The certificates are
not bookkeeping: they are what lets us apply the library's **effectivity**
theorem, which says that a quotient by a propositional equivalence relation
glues *honestly*: two points end up connected only if the relation actually
related them, never by accident. In other words, a path in the quotient can be
read backwards, recovering the relation that caused it.
<!--zh-->
关系及其证书都由这张表给出：每个表项都是命题，对角线给出自反性，表的对称性给出关系的对称性，传递性则由剩余的混合表项证明。这些证书用于应用库的**有效性**定理。该定理说明，按命题值等价关系取商时，两点在商中相等必然来自原关系对它们的关联；因此，可以从商中的路径恢复对应的关系证明。
<!--/-->

```agda
  ~-prop : BinaryRelation.isPropValued _~_
  ~-prop true  true  = isPropUnit*
  ~-prop false false = isPropUnit*
  ~-prop true  false = P .snd
  ~-prop false true  = P .snd

  ~-refl : (a : Bool) → a ~ a
  ~-refl true  = tt*
  ~-refl false = tt*

  ~-sym : (a b : Bool) → a ~ b → b ~ a
  ~-sym true  true  _ = tt*
  ~-sym false false _ = tt*
  ~-sym true  false p = p
  ~-sym false true  p = p

  ~-trans : (a b c : Bool) → a ~ b → b ~ c → a ~ c
  ~-trans true  _     true  _ _ = tt*
  ~-trans false _     false _ _ = tt*
  ~-trans true  false false p _ = p
  ~-trans false true  true  p _ = p
  ~-trans true  true  false _ p = p
  ~-trans false false true  _ p = p

  ~-equivRel : BinaryRelation.isEquivRel _~_
  ~-equivRel = BinaryRelation.equivRel ~-refl ~-sym ~-trans
```

<!--en-->
The core of the construction is a two-line statement: **the two points of the
quotient coincide exactly when `P` holds**. One direction: if `P` holds, the
table relates `true` to `false`, so the quotient identifies their classes; the
space has collapsed to a single point. The other direction: if the two classes
coincide, effectivity of the gluing says the relation must have related `true` to
`false`, and by the table that relation *is* `P`, so `P` holds. The mixed
square is used in both directions: a `P`-witness feeds the path constructor
directly, and the effectivity theorem's output is already a proof of `P`,
with no decoding and no impossible case to dismiss.
<!--zh-->
构造的核心是一个两行论断：**商的两个点重合，当且仅当 `P` 成立**。一个方向是：若 `P` 成立，表格判定 `true` 与 `false` 相关，商便把两个等价类等同，空间坍缩为一个点。另一个方向是：若两个类重合，粘合的有效性说明关系必定关联 `true` 与 `false`，而表中的这项关系**就是** `P`，所以 `P` 成立。混色格在这里用于两个方向：`P` 的见证直接传给路径构造子，有效性定理的输出本身就是 `P` 的证明，无需解码或排除其他情形。
<!--/-->

```agda
  glue : ⟨ P ⟩ → Path Glued [ true ] [ false ]
  glue p = eq/ true false p

  unglue : Path Glued [ true ] [ false ] → ⟨ P ⟩
  unglue = effective ~-prop ~-equivRel true false
```

<!--en-->
Now the choice principle enters, and here is the single question we ask it:
*hand every point of the glued space a boolean representative.* A **pick** at a
point is a boolean together with the guarantee that its class is that point.
Each point separately is sure to have one, but only *merely* so: a quotient
remembers that its points came from somewhere without remembering from where.
Turning "each point merely has a representative" into one **function** choosing
representatives everywhere at once is exactly what set-level choice does, and
it applies because the glued space is an h-set by construction. Note what the
function cannot do: it was built with no access to `P`, so it answers the same
way whether or not `P` holds; it merely, blindly, picks.
<!--zh-->
现在应用选择原理，要求为粘合空间的每个点选定一个布尔代表元。某点处的一次**选取**由一个布尔值及其等价类等于该点的证明组成。每个点都有这种选取，但只能证明其**仅仅**存在：商保留每个点来自某个代表元，却不指定该代表元。集合层选择把这些逐点的仅仅存在转化为一个选取函数的仅仅存在；它适用于此处，因为粘合空间按构造是 h-集。这个函数的构造不使用 `P`，所以无论 `P` 是否成立，都以同一方式给出选择。
<!--/-->

```agda
  Pick : Glued → Type ℓ
  Pick x = Σ[ b ∈ Bool ] ([ b ] ≡ x)

  pickable : (x : Glued) → ∥ Pick x ∥₁
  pickable = []surjective
```

<!--en-->
The question deserves to be a lemma of its own, so that its type displays
exactly what choice delivers: the mere existence of a picking function defined
on the whole space.
<!--zh-->
这个问题值得单独立为引理，好让类型原样展示选择所给出之物：**仅仅地**存在的一整个选取函数。
<!--/-->

```agda
  merePicker : SetChoice ℓ → ∥ ((x : Glued) → Pick x) ∥₁
  merePicker sc = sc Glued squash/ Pick pickable
```

<!--en-->
Suppose, then, that a picking function `g` is given. Apply it to the two
distinguished points, the class of `true` and the class of `false`, and name
the two boolean representatives it selects, `b₀` and `b₁`. Two lemmas, one
per direction, relate these values to `P`. **If the representatives agree**, their
guarantees give a path from the class of `true` to the class of `b₀`, then
to the class of `b₁`, and finally to the class of `false`; effectivity turns
the equality of the endpoints into a proof of `P`. **If `P` holds**, the two
distinguished points are equal, and the picking function respects that
equality, so `b₀` and `b₁` are equal. (Formally, it suffices to project `g`
along the gluing path; both endpoints are plain booleans, so no transport is
needed.)
<!--zh-->
设选取函数为 `g`。将它分别作用于两个特殊点，即 `true` 的类和 `false` 的类，并把所得布尔代表元记作 `b₀` 与 `b₁`。两个方向的引理把这两个值与 `P` 联系起来。**若代表元一致**，它们各自的保证给出从 `true` 的类到 `b₀` 的类、再到 `b₁` 的类、最后到 `false` 的类的路径；有效性定理把两端相等转化为 `P` 的证明。**若 `P` 成立**，两个特殊点相等，选取函数尊重这条相等，因此 `b₀` 与 `b₁` 相等。(形式化地，只需把 `g` 沿粘合路径投影；两端都是普通布尔值，无需搬运。)
<!--/-->

```agda
  module _ (g : (x : Glued) → Pick x) where

    b₀ : Bool
    b₀ = g [ true ] .fst

    b₁ : Bool
    b₁ = g [ false ] .fst

    agree→P : b₀ ≡ b₁ → ⟨ P ⟩
    agree→P q = unglue (sym (g [ true ] .snd) ∙ cong [_] q ∙ g [ false ] .snd)

    P→agree : ⟨ P ⟩ → b₀ ≡ b₁
    P→agree p i = g (glue p i) .fst
```

<!--en-->
Now decide `P` by looking at the two booleans, which, unlike `P`, **can** be
inspected: two booleans are equal or they are not, mechanically. If `b₀` and
`b₁` agree, the first lemma proves `P`. If they differ, `P` must fail, for had
it held, the second lemma would force them to agree. Either way `P` is
decided, and note what carries the decision: the case split happened on the
finite data that the choice function was forced to commit to, not on
`P` itself.
<!--zh-->
现在改由那两个布尔值来判定 `P`。与 `P` 不同，它们**可以**被检视：两个布尔值要么相等要么不等，机械可判。若 `b₀` 与 `b₁` 一致，第一条引理证出 `P`。若二者相异，`P` 必不成立，因为它若成立，第二条引理将迫使二者一致。无论哪边 `P` 都被判定；经典性正是在此介入：分情形只发生在选择函数被迫取值的那点有限数据上，从头到尾不触及 `P` 自身。
<!--/-->

```agda
    decide : ⟨ P ⟩ Sum.⊎ (⟨ P ⟩ → Empty.⊥)
    decide = fromDec (b₀ ≟ b₁)
      where
      fromDec : Dec (b₀ ≡ b₁) → ⟨ P ⟩ Sum.⊎ (⟨ P ⟩ → Empty.⊥)
      fromDec (yes q) = Sum.inl (agree→P q)
      fromDec (no ne) = Sum.inr (λ p → ne (P→agree p))
```

<!--en-->
One last gap and the theorem assembles. Choice never hands over an actual
picking function, only its *mere* existence. But the goal "`P` or not `P`" is
itself a proposition: the two sides exclude each other, so between any two
decisions there is nothing to distinguish. Into such a goal, mere existence
eliminates as if it were actual, and the proof closes.
<!--zh-->
补上最后一步，定理即告完成。选择并未真正交出选取函数，只交出它的**仅仅**存在。但目标「`P` 或非 `P`」自身是命题：两侧互斥，任何两个判定之间无可区分。对这样的目标，仅仅存在可以当作真实存在来消去，证明就此闭合。
<!--/-->

```agda
  decideIsProp : isProp (⟨ P ⟩ Sum.⊎ (⟨ P ⟩ → Empty.⊥))
  decideIsProp = Sum.isProp⊎ (P .snd) (isPropΠ (λ _ → Empty.isProp⊥)) (λ p np → np p)

choice→lem : ∀ {ℓ} → SetChoice ℓ → LEM ℓ
choice→lem sc P = PT.rec decideIsProp decide (merePicker sc)
  where open Diaconescu P
```

<!--en-->
## Recap

`SetChoice`{.Agda} is the book's choice interface, one level at a time, in the
same shape as `LEM`{.Agda}; and by `choice→lem`{.Agda} it is the stronger of the
two: choice decides every proposition of its level, through the glued booleans,
the `glue`{.Agda}/`unglue`{.Agda} dictionary, and one comparison of chosen
representatives. excluded middle does not in turn yield choice, so the two
interfaces remain distinct. The model chapter applies choice to obtain its choice set,
and closes by using this chapter's theorem: one instance of choice, one
universe up, suffices for all the classical reasoning that follows.
<!--zh-->
## 小结

`SetChoice`{.Agda} 是本书的选择接口，逐层级陈述，形状与 `LEM`{.Agda} 相同；而经 `choice→lem`{.Agda}，它是两者中更强的一个：经由粘合布尔值、`glue`{.Agda}/`unglue`{.Agda} 词典与一次代表元比较，选择判定其层级的每个命题。排中律却推不出选择，所以两个接口依然分立。模型章将把选择用于选择集，并在收尾处应用本章定理：高一层宇宙上的一份选择，即可支持后文所需的全部经典推理。
<!--ja-->
## まとめ

集合レベルの選択原理は宇宙レベルを下へ移り、各レベルで排中律を含みます。したがって、後の `V` のモデル定理は選択原理だけを受け取っても必要な古典的推論を得られます。
<!--/-->
