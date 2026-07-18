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
open import Cubical.Data.Bool using ( Bool; true; false; true≢false )
import Cubical.Data.Sum as Sum
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁; ∣_∣₁ )
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
## Diaconescu's theorem
<!--zh-->
## Diaconescu 定理
<!--/-->

<!--en-->
Fix a proposition `P`; everything below lives in a module named after the
theorem's author. The proof builds the most economical set that *depends* on
`P`: take the two booleans and glue them together exactly when `P` holds. The
gluing relation says "equal, or else `P`", and the glued set is its set
quotient.
<!--zh-->
固定命题 `P`；以下一切都住在以定理作者命名的模块里。证明构造出**依赖于** `P` 的最经济的集合：取两个布尔值，恰当 `P` 成立时把它们粘起来。粘合关系说「相等，或者 `P`」，粘合集就是它的集合商。
<!--/-->

```agda
module Diaconescu {ℓ} (P : hProp ℓ) where

  R : Bool → Bool → Type ℓ
  R a b = ∥ (a ≡ b) Sum.⊎ ⟨ P ⟩ ∥₁

  Glued : Type ℓ
  Glued = Bool / R
```

<!--en-->
`R` is propositional by its truncation and an equivalence relation by three
routine checks; transitivity chains the equality case and lets any `P`-witness
absorb the rest. These two certificates are not bookkeeping: they are the
ticket to the library's **effectivity** theorem, the right to read a quotient
path backwards.
<!--zh-->
`R` 因截断而是命题值，因三条例行检查而是等价关系；传递性把相等情形串接起来，任何 `P` 见证则吸收其余。这两张证书不是记账：它们是库的**有效性**定理的入场券，即倒着读商路径的权利。
<!--/-->

```agda
  Rprop : BinaryRelation.isPropValued R
  Rprop a b = PT.squash₁

  Requiv : BinaryRelation.isEquivRel R
  Requiv = BinaryRelation.equivRel
    (λ a → ∣ Sum.inl refl ∣₁)
    (λ a b → PT.map (Sum.map sym (λ h → h)))
    (λ a b c → PT.rec2 PT.squash₁ chain)
    where
    chain : {a b c : Bool}
          → (a ≡ b) Sum.⊎ ⟨ P ⟩ → (b ≡ c) Sum.⊎ ⟨ P ⟩ → R _ _
    chain (Sum.inl p) (Sum.inl q) = ∣ Sum.inl (p ∙ q) ∣₁
    chain (Sum.inl p) (Sum.inr h) = ∣ Sum.inr h ∣₁
    chain (Sum.inr h) _           = ∣ Sum.inr h ∣₁
```

<!--en-->
The heart of the construction is a two-line dictionary: **the two classes are
glued exactly when `P` holds**. Forwards, a `P`-witness feeds the quotient's
path constructor. Backwards is where effectivity earns its ticket: a path
between the classes is decoded back into the relation, and the absurd
alternative `true ≡ false` is dismissed.
<!--zh-->
构造的心脏是一部两行的词典：**两个等价类被粘住，当且仅当 `P` 成立**。正向，`P` 的见证喂给商的路径构造子。反向正是有效性兑现入场券之处：类之间的路径被解码回关系，荒谬的备选项 `true ≡ false` 被驳回。
<!--/-->

```agda
  glue : ⟨ P ⟩ → Path Glued [ true ] [ false ]
  glue p = eq/ true false ∣ Sum.inr p ∣₁

  unglue : Path Glued [ true ] [ false ] → ⟨ P ⟩
  unglue e = PT.rec (P .snd)
    (λ { (Sum.inl t≡f) → Empty.rec (true≢false t≡f)
       ; (Sum.inr h)   → h })
    (effective Rprop Requiv true false e)
```

<!--en-->
Now the choice principle enters. A **pick** at a point of the glued set is a
boolean representative together with the path connecting its class to the
point; every point merely has one, because the quotient's points are merely
hit by `[_]`. That is precisely the shape `SetChoice`{.Agda} consumes, and the
glued set is an h-set by construction, so choice will hand over a *function*
picking representatives everywhere at once.
<!--zh-->
现在选择原理进场。粘合集某点处的一次**认领**，是一个布尔代表元，连同把其等价类接到该点的路径；每个点都仅仅拥有一次认领，因为商的点仅仅被 `[_]` 命中。这恰是 `SetChoice`{.Agda} 消费的形状，而粘合集按构造是 h-集，于是选择将交出一个**函数**，一举在处处认领代表元。
<!--/-->

```agda
  Pick : Glued → Type ℓ
  Pick x = Σ[ b ∈ Bool ] ([ b ] ≡ x)

  pickable : (x : Glued) → ∥ Pick x ∥₁
  pickable = []surjective
```

<!--en-->
Suppose, then, that a picking function `g` is in hand, and name the two
representatives it selects at the glued classes. Comparing them decides `P`,
one small lemma per direction. If they agree, the two classes were forced
together, and `unglue`{.Agda} recovers `P`. If `P` holds, the classes *are*
together, and projecting `g` along the gluing path makes the representatives
agree, with no transport gymnastics: `Pick`'s first component is a boolean on
both ends.
<!--zh-->
于是假设认领函数 `g` 已经在手，给它在两个粘合类处选出的代表元起名。比较二者即可判定 `P`，每个方向一条小引理。若二者一致，则两个类曾被迫粘合，`unglue`{.Agda} 反解出 `P`。若 `P` 成立，则两个类**本就**粘在一起，把 `g` 沿粘合路径投影，代表元便一致，且无须任何搬运体操：`Pick` 的第一分量在两端都是布尔值。
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
Two booleans can always be compared, by four cases; the comparison turns the
lemma pair into a decision of `P`.
<!--zh-->
两个布尔值总能比较，四个情形而已；这次比较把上面那对引理变成对 `P` 的判定。
<!--/-->

```agda
    decide : ⟨ P ⟩ Sum.⊎ (⟨ P ⟩ → Empty.⊥)
    decide = fromComparison (compare b₀ b₁)
      where
      compare : (a b : Bool) → (a ≡ b) Sum.⊎ ((a ≡ b) → Empty.⊥)
      compare true  true  = Sum.inl refl
      compare false false = Sum.inl refl
      compare true  false = Sum.inr true≢false
      compare false true  = Sum.inr (λ q → true≢false (sym q))
      fromComparison : (b₀ ≡ b₁) Sum.⊎ ((b₀ ≡ b₁) → Empty.⊥)
                     → ⟨ P ⟩ Sum.⊎ (⟨ P ⟩ → Empty.⊥)
      fromComparison (Sum.inl q)  = Sum.inl (agree→P q)
      fromComparison (Sum.inr ne) = Sum.inr (λ p → ne (P→agree p))
```

<!--en-->
One last observation and the theorem assembles. Deciding a proposition is
itself a proposition (the two sides exclude each other), so the *mere*
existence of a picking function suffices: truncation is eliminated straight
into the decision.
<!--zh-->
最后一个观察，定理即可合拢。判定一个命题本身是命题 (两侧互斥)，于是认领函数的**仅仅**存在就已足够：截断被直接消去到判定里。
<!--/-->

```agda
  decideIsProp : isProp (⟨ P ⟩ Sum.⊎ (⟨ P ⟩ → Empty.⊥))
  decideIsProp = Sum.isProp⊎ (P .snd) (isPropΠ (λ _ → Empty.isProp⊥)) (λ p np → np p)

choice→lem : ∀ {ℓ} → SetChoice ℓ → LEM ℓ
choice→lem sc P = PT.rec decideIsProp decide (sc Glued squash/ Pick pickable)
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
and closes by cashing this chapter's theorem: level-polymorphic choice, alone,
funds the entire classical bill.
<!--zh-->
`SetChoice`{.Agda} 是本书的选择接口，逐层级陈述，与 `LEM`{.Agda} 同款形状；而经 `choice→lem`{.Agda}，它是两者中更强的那个：经由粘合布尔值、`glue`{.Agda}/`unglue`{.Agda} 词典与一次代表元比较，选择判定其层级的每个命题。排中律不回此礼，所以两个接口依然分立。模型章将把选择花在选择集上，并在收尾处兑现本章定理：单凭层级多态的选择，就能付清全部经典账单。
<!--/-->
