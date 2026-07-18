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
Fix a proposition `P`. The proof builds the most economical set that *depends*
on `P`: take the two booleans and glue them together exactly when `P` holds,
a set quotient by the relation "equal, or else `P`". Every point of the quotient
is merely hit by a boolean, so set-level choice picks a boolean representative
for each point, all at once. Now compare the representatives chosen for `[true]`
and `[false]`, a decidable comparison of two booleans. If they coincide, the two
classes were forced together, and by the quotient's effectivity that can only be
because `P` holds. If they differ, `P` must fail: had `P` held, the gluing would
identify `[true]` with `[false]`, and the chosen representatives, being values
of one function, would coincide. Either way `P` is decided, and since deciding a
proposition is itself a proposition, the mere existence of the choice function
suffices.
<!--zh-->
固定命题 `P`。证明构造出**依赖于** `P` 的最经济的集合：取两个布尔值，恰当 `P` 成立时把它们粘起来，即按「相等，或者 `P`」这个关系做集合商。商的每个点都仅仅被某个布尔值命中，于是集合层选择为每个点一齐挑出布尔代表元。现在比较 `[true]` 与 `[false]` 处挑出的代表元，这是两个布尔值之间可判定的比较。若二者重合，则两个等价类被迫粘在一起，而由商的有效性，这只能是因为 `P` 成立。若二者相异，则 `P` 必不成立：倘若 `P` 成立，粘合会把 `[true]` 与 `[false]` 等同起来，而作为同一个函数的取值，挑出的代表元将不得不重合。无论哪边，`P` 都被判定；又因判定一个命题本身是命题，选择函数的仅仅存在就已足够。
<!--/-->

```agda
choice→lem : ∀ {ℓ} → SetChoice ℓ → LEM ℓ
choice→lem {ℓ} sc P = PT.rec propGoal decide (sc X squash/ B inh)
  where
  R : Bool → Bool → Type ℓ
  R a b = ∥ (a ≡ b) Sum.⊎ ⟨ P ⟩ ∥₁

  open BinaryRelation R using ( isPropValued; isEquivRel; equivRel )

  Rprop : isPropValued
  Rprop a b = PT.squash₁

  Requiv : isEquivRel
  Requiv = equivRel
    (λ a → ∣ Sum.inl refl ∣₁)
    (λ a b → PT.map (Sum.map sym (λ h → h)))
    (λ a b c → PT.rec2 PT.squash₁ chain)
    where
    chain : {a b c : Bool}
          → (a ≡ b) Sum.⊎ ⟨ P ⟩ → (b ≡ c) Sum.⊎ ⟨ P ⟩ → R _ _
    chain (Sum.inl p) (Sum.inl q) = ∣ Sum.inl (p ∙ q) ∣₁
    chain (Sum.inl p) (Sum.inr h) = ∣ Sum.inr h ∣₁
    chain (Sum.inr h) _           = ∣ Sum.inr h ∣₁

  X : Type ℓ
  X = Bool / R

  B : X → Type ℓ
  B x = Σ[ b ∈ Bool ] ([ b ] ≡ x)

  inh : (x : X) → ∥ B x ∥₁
  inh = []surjective

  propGoal : isProp (⟨ P ⟩ Sum.⊎ (⟨ P ⟩ → Empty.⊥))
  propGoal = Sum.isProp⊎ (P .snd) (isPropΠ (λ _ → Empty.isProp⊥)) (λ p np → np p)

  decide : ((x : X) → B x) → ⟨ P ⟩ Sum.⊎ (⟨ P ⟩ → Empty.⊥)
  decide g = fromDec (boolDec (g [ true ] .fst) (g [ false ] .fst))
    where
    same : g [ true ] .fst ≡ g [ false ] .fst → ⟨ P ⟩
    same q = PT.rec (P .snd)
      (λ { (Sum.inl t≡f) → Empty.rec (true≢false t≡f)
         ; (Sum.inr h)   → h })
      (effective Rprop Requiv true false
        (sym (g [ true ] .snd) ∙ cong [_] q ∙ g [ false ] .snd))
    differ : (g [ true ] .fst ≡ g [ false ] .fst → Empty.⊥) → ⟨ P ⟩ → Empty.⊥
    differ ne h = ne (λ i → g (eq/ true false ∣ Sum.inr h ∣₁ i) .fst)
    boolDec : (a b : Bool) → (a ≡ b) Sum.⊎ ((a ≡ b) → Empty.⊥)
    boolDec true  true  = Sum.inl refl
    boolDec false false = Sum.inl refl
    boolDec true  false = Sum.inr true≢false
    boolDec false true  = Sum.inr (λ q → true≢false (sym q))
    fromDec : (g [ true ] .fst ≡ g [ false ] .fst)
              Sum.⊎ ((g [ true ] .fst ≡ g [ false ] .fst) → Empty.⊥)
            → ⟨ P ⟩ Sum.⊎ (⟨ P ⟩ → Empty.⊥)
    fromDec (Sum.inl q)  = Sum.inl (same q)
    fromDec (Sum.inr ne) = Sum.inr (differ ne)
```

<!--en-->
Two details deserve their footnote. The comparison of chosen booleans runs
through `differ`{.Agda}'s one-line path: when `P` holds, `eq/`{.Agda} identifies
the two classes, and projecting the choice function along that path *is* the
coincidence of representatives, no transport gymnastics needed. And the quotient's
**effectivity**, recovering `R true false` from `[ true ] ≡ [ false ]`, is the
library's `effective`{.Agda}, available precisely because the gluing relation is
propositional and an equivalence.
<!--zh-->
两处细节值得加注。所选布尔值的比较经 `differ`{.Agda} 的一行路径完成：当 `P` 成立时，`eq/`{.Agda} 等同两个等价类，把选择函数沿这条路径投影，**就是**代表元的重合，无须任何搬运体操。而商的**有效性**，即从 `[ true ] ≡ [ false ]` 反解出 `R true false`，是库的 `effective`{.Agda}，它可用恰因粘合关系是命题值的等价关系。
<!--/-->

<!--en-->
## Recap
<!--zh-->
## 小结
<!--/-->

<!--en-->
`SetChoice`{.Agda} is the book's choice interface, one level at a time, in the
same shape as `LEM`{.Agda}; and by `choice→lem`{.Agda} it is the stronger of the
two: choice decides every proposition of its level. The excluded middle does not
return the favour, so the two interfaces remain distinct. The model chapter
spends choice on its choice set, and closes by cashing this chapter's theorem:
level-polymorphic choice, alone, funds the entire classical bill.
<!--zh-->
`SetChoice`{.Agda} 是本书的选择接口，逐层级陈述，与 `LEM`{.Agda} 同款形状；而经 `choice→lem`{.Agda}，它是两者中更强的那个：选择判定其层级的每个命题。排中律不回此礼，所以两个接口依然分立。模型章将把选择花在选择集上，并在收尾处兑现本章定理：单凭层级多态的选择，就能付清全部经典账单。
<!--/-->
