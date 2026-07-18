# Choice

<!--en-->
The classical boundary has a second interface. Alongside the excluded middle,
classical mathematics runs on choice, and this chapter states the book's form of
it, one level at a time, in the same interface style as `LEM`{.Agda}.
**Set-level choice** says that over an h-set of indices, truncation commutes
with the product: if every fiber is merely inhabited, then merely, every fiber
is inhabited at once. This is the type-theoretic reading of "a family of
nonempty sets has a choice function", and the h-set restriction on the index is
what keeps it honest, since over arbitrary types the principle is simply false.
Like the excluded middle, choice is never assumed globally: a chapter that needs
it takes it as a parameter, and the first to do so is Part 3's summit.

The two interfaces are not peers, and this chapter proves it on the spot:
**choice proves the excluded middle**. The observation is due to Diaconescu,
with the type-theoretic form by Goodman and Myhill; it means that at each level
the choice interface quietly carries the whole classical boundary with it.
<!--zh-->
经典边界还有第二个接口。经典数学除排中律外还依靠选择运转，本章陈述本书采用的形式，逐层级、与 `LEM`{.Agda} 同款的接口风格。**集合层选择**说：在 h-集索引之上，截断与乘积交换：若每根纤维都仅仅有元，则仅仅地，全体纤维一齐有元。这是「非空集族有选择函数」的类型论读法，而索引上的 h-集限制正是它诚实的关键，因为对任意类型这条原理干脆为假。与排中律一样，选择从不全局假设：需要它的章节以参数领取，而第一个领取者是第三部之巅。

两个接口并非平级，本章当场证明这一点：**选择证明排中律**。这个观察出自 Diaconescu，类型论形式归于 Goodman 与 Myhill；它意味着在每个层级上，选择接口都悄悄把整条经典边界背在身上。
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
<!--zh-->
## 原理
<!--/-->

```agda
SetChoice : ∀ ℓ → Type (ℓ-suc ℓ)
SetChoice ℓ = (X : Type ℓ) → isSet X → (B : X → Type ℓ)
            → ((x : X) → ∥ B x ∥₁) → ∥ ((x : X) → B x) ∥₁
```

<!--en-->
Like the excluded middle, choice passes **downward** through the levels: lift
the index set and the fibers one universe up, choose there, lower the choice
function. A single higher instance therefore covers the levels below.
<!--zh-->
与排中律一样，选择沿层级**向下**通行：把索引集与纤维抬高一层宇宙，在那里选择，再把选择函数降回来。于是较高层级上的单个实例覆盖其下诸层。
<!--/-->

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
<!--zh-->
## Diaconescu 定理
<!--/-->

<!--en-->
The theorem: given set-level choice, **any** proposition `P` can be decided,
proved or refuted. On its face this is absurd, since a decision procedure has
nothing to inspect: an arbitrary `P` offers no case to split on. The proof's
idea is to make *geometry* do the inspecting. Build a little space whose very
shape depends on `P`: it has one point if `P` holds and two points if it fails.
Ask choice a single question about that space; the answer cannot help but leak
the shape, and the shape is `P`.

Concretely, fix `P`; everything below lives in a module named after the
theorem's author. Take the two booleans and glue them together exactly when
`P` holds. "Gluing" is a **set quotient**: the points are still `true` and
`false`, but a path is added between them whenever the gluing relation says
so, and the result is truncated to an h-set. The relation is best given as a
four-entry table: trivially satisfied on the diagonal, and **literally `P`
itself** in the two mixed squares, so that "the two points are related" and
"`P` holds" are the same proposition by definition. That last clause is the
whole trick, and it will pay twice below.
<!--zh-->
定理说：给定集合层选择，**任何**命题 `P` 都可判定，即或证明或反驳。乍看这很荒谬，因为判定程序无从下手：任意的 `P` 没有可分情形的把手。证明的想法是让**几何**来下手。造一个形状依赖于 `P` 的小空间：`P` 成立时它只有一个点，不成立时有两个点。然后向选择原理问一个关于这个空间的问题；答案不可能不泄露形状，而形状就是 `P`。

具体地，固定 `P`；以下一切都住在以定理作者命名的模块里。取两个布尔值，恰当 `P` 成立时把它们粘起来。「粘合」指**集合商**：点仍是 `true` 与 `false`，但凡粘合关系点头，两点之间就添一条路径，最后把结果截断为 h-集。粘合关系最好用一张四格表给出：对角线上平凡成立，混色的两格**就是 `P` 本身**，于是「这两点相关」与「`P` 成立」按定义是同一个命题。最后这一款是全部戏法所在，下文将两次兑付。
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
transitive by reading off whichever mixed square survives. The certificates are
not bookkeeping: they are the ticket to the library's **effectivity** theorem,
which says that a quotient by a propositional equivalence relation glues
*honestly*: two points end up connected only if the relation actually related
them, never by accident. In other words, a path in the quotient can be read
backwards, recovering the relation that caused it.
<!--zh-->
关系是表，它的证书也就是表：逐格皆命题，对角线自反，表格对称故关系对称，传递性则读出幸存的那个混色格。证书不是记账：它们是库的**有效性**定理的入场券。该定理说，按命题值等价关系取商，粘合是**诚实**的：两点最终连通，只可能因为关系确实关联过它们，绝无误伤。换句话说，商里的路径可以倒着读，读回引起它的那份关系。
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
The heart of the construction is a two-line dictionary: **the two points of the
quotient coincide exactly when `P` holds**. One direction: if `P` holds, the
table relates `true` to `false`, so the quotient identifies their classes; the
space has collapsed to a single point. The other direction: if the two classes
coincide, honesty of the gluing says the relation must have related `true` to
`false`, and by the table that relation *is* `P`, so `P` holds. This is where
the mixed square pays for the first time, twice over: a `P`-witness feeds the
path constructor directly, and the effectivity theorem's output is already a
proof of `P`, with no decoding and no impossible case to dismiss.
<!--zh-->
构造的心脏是一部两行的词典：**商的两个点重合，当且仅当 `P` 成立**。一个方向：若 `P` 成立，表格便判 `true` 与 `false` 相关，商随之把两个等价类等同起来，空间坍缩为一个点。另一个方向：若两个类重合，粘合的诚实性说明关系必定关联过 `true` 与 `false`，而按表格那份关系**就是** `P`，故 `P` 成立。这正是混色格第一次付账之处，还一次付了两笔：`P` 的见证直接喂给路径构造子，有效性定理的输出本身就已是 `P` 的证明，无须解码，也没有不可能情形要驳。
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
现在选择原理进场，我们只问它一个问题：*给粘合空间的每个点发一个布尔代表元。*某点处的一次**认领**，是一个布尔值，连同「其等价类就是该点」的保证。每个点单独看必有认领，但只是**仅仅**有：商记得自己的点各有来处，却不记得来处是谁。把「每点仅仅有代表元」变成一个一举在处处认领的**函数**，正是集合层选择的本领，而它适用是因为粘合空间按构造是 h-集。留意这个函数做不到的事：它的构造完全接触不到 `P`，故无论 `P` 成立与否它都同样作答；它只是盲目地认领。
<!--/-->

```agda
  Pick : Glued → Type ℓ
  Pick x = Σ[ b ∈ Bool ] ([ b ] ≡ x)

  pickable : (x : Glued) → ∥ Pick x ∥₁
  pickable = []surjective
```

<!--en-->
The question deserves to be a lemma of its own, so that its type displays
exactly what choice delivers: *merely*, a picking function, whole.
<!--zh-->
这个问题值得单独立为引理，好让类型原样展示选择交付的东西：**仅仅地**，一整个认领函数。
<!--/-->

```agda
  merePicker : SetChoice ℓ → ∥ ((x : Glued) → Pick x) ∥₁
  merePicker sc = sc Glued squash/ Pick pickable
```

<!--en-->
Suppose, then, that a picking function `g` is in hand. Apply it to the two
distinguished points, the class of `true` and the class of `false`, and name
the two boolean representatives it selects, `b₀` and `b₁`. These two booleans
are the leak. One lemma per direction ties them to `P`. **If the
representatives agree**, walk the guarantees: the class of `true` connects to
the class of `b₀`, which is the class of `b₁`, which connects to the class of
`false`; so the two points coincide, and the dictionary's backward entry turns
that coincidence into a proof of `P`. **If `P` holds**, the two points *are*
one single point, and a function applied to one point yields one answer, so
`b₀` and `b₁` are forced to be the same boolean. (Formally: project `g` along
the gluing path; both endpoints of the projection are plain booleans, so no
transport is even needed.)
<!--zh-->
于是假设认领函数 `g` 已经在手。把它作用在两个特殊的点上，即 `true` 的类与 `false` 的类，给选出的两个布尔代表元起名 `b₀` 与 `b₁`。这两个布尔值就是泄密者。每个方向一条引理把它们与 `P` 绑在一起。**若代表元一致**，就沿保证走一遍：`true` 的类接到 `b₀` 的类，即 `b₁` 的类，再接到 `false` 的类；于是两点重合，词典的反向条目把这次重合翻译成 `P` 的证明。**若 `P` 成立**，则两点**本是**同一个点，而函数作用在同一个点上只能给出同一个答案，`b₀` 与 `b₁` 被迫是同一个布尔值。(形式化地：把 `g` 沿粘合路径投影，投影的两端都是普通布尔值，连搬运都不需要。)
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
decided, and note where the classical rabbit came out of the hat: the case
split happened on finite data that the choice function was forced to commit to,
not on `P` itself.
<!--zh-->
现在改看那两个布尔值来判定 `P`。与 `P` 不同，它们**可以**被检视：两个布尔值要么相等要么不等，机械可判。若 `b₀` 与 `b₁` 一致，第一条引理证出 `P`。若二者相异，`P` 必不成立，因为它若成立，第二条引理将迫使二者一致。无论哪边 `P` 都被判定；请留意经典兔子从哪顶帽子里蹦出：分情形发生在选择函数被迫表态的有限数据上，从头到尾不在 `P` 自身上。
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
最后一道缺口，定理即合拢。选择从不真正交出认领函数，只交出它的**仅仅**存在。但目标「`P` 或非 `P`」自身是命题：两侧互斥，任何两个判定之间无可区分。对这样的目标，仅仅存在可以当作真实存在来消去，证明就此闭合。
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
<!--zh-->
## 小结
<!--/-->

<!--en-->
`SetChoice`{.Agda} is the book's choice interface, one level at a time, in the
same shape as `LEM`{.Agda}; and by `choice→lem`{.Agda} it is the stronger of the
two: choice decides every proposition of its level, through the glued booleans,
the `glue`{.Agda}/`unglue`{.Agda} dictionary, and one comparison of chosen
representatives. The excluded middle does not return the favour, so the two
interfaces remain distinct. The model chapter spends choice on its choice set,
and closes by cashing this chapter's theorem: one instance of choice, one
universe up, funds the entire classical bill.
<!--zh-->
`SetChoice`{.Agda} 是本书的选择接口，逐层级陈述，与 `LEM`{.Agda} 同款形状；而经 `choice→lem`{.Agda}，它是两者中更强的那个：经由粘合布尔值、`glue`{.Agda}/`unglue`{.Agda} 词典与一次代表元比较，选择判定其层级的每个命题。排中律不回此礼，所以两个接口依然分立。模型章将把选择花在选择集上，并在收尾处兑现本章定理：高一层宇宙上的一份选择，就能付清全部经典账单。
<!--/-->
