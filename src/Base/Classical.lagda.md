# The classical boundary

<!--en-->
Set theory as most readers know it is classical: excluded middle is ambient air. The
host, however, is constructive, and this book keeps the boundary between the two
visible as a matter of law. The rule, fixed in the Charter, is that classical
principles enter as **explicit parameters**, never as global assumptions: a chapter
that reasons classically says so in its own interface, the type checker polices the
boundary, and there is not a single `postulate` in this book. This chapter states
the one classical principle everything later appeals to, and banks its two basic
dividends.
<!--zh-->
多数读者熟悉的集合论是经典的：排中律如空气般无处不在。然而宿主是构造性的，本书把两者之间的边界作为法条保持可见。纲领定下的规则是：经典原理一律作为**显式参数**进入，绝不作为全局假设。凡经典论证的章节都在自己的接口上言明，类型检查器守卫这条边界，全书没有一个 `postulate`。本章陈述后文一切经典论证所诉诸的那唯一原理，并存入它的两笔基本红利。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

module Base.Classical where

open import Base.Prelude
open import Base.Truth
open import Cubical.Data.Sum using ( _⊎_; inl; inr )
import Cubical.Data.Empty as Empty
open import Cubical.Data.Bool using ( Bool; true; false )
open import Cubical.Data.Unit using ( tt* )
open import Cubical.Foundations.Equiv using ( _≃_; propBiimpl→Equiv )
open import Cubical.Foundations.Isomorphism using ( iso; isoToEquiv )
open import Cubical.Functions.Logic using ( ⇔toPath )
```

<!--en-->
## The statement
<!--zh-->
## 陈述
<!--/-->

```agda
LEM : ∀ ℓ → Type (ℓ-suc ℓ)
LEM ℓ = (P : hProp ℓ) → ⟨ P ⟩ ⊎ (⟨ P ⟩ → Empty.⊥)
```

<!--en-->
`LEM`{.Agda}` ℓ` says: every proposition at level `ℓ` is either true or false. Why
this particular form? In univalent foundations a type-level global choice or
excluded middle is inconsistent with univalence; what can consistently be assumed is
exactly this propositional form, quantified over `hProp`{.Agda}. The foundation
itself forces the honest phrasing.

A chapter that works classically takes `(lem : ∀ {ℓ} → LEM ℓ)` in its module
telescope and passes it along when importing other classical chapters. The
consequence is worth pausing on: **whether a theorem uses excluded middle is a
compile-time fact.** The classical debt is part of a chapter's type, visible at
every import site, instead of an invisible global axiom; and since nothing is
postulated, the whole book carries Agda's `--safe` seal.
<!--zh-->
`LEM`{.Agda}` ℓ` 说的是：层级 `ℓ` 上的每个命题要么真要么假。为什么取这个形式？在 univalent 基础中，类型层的全局选择或排中律与 univalence 不相容；能够一致地假设的恰是这个对 `hProp`{.Agda} 量化的命题形式。是基础本身逼出了这个诚实的措辞。

经典论证的章节在模块参数表中取 `(lem : ∀ {ℓ} → LEM ℓ)`，并在导入其他经典章节时把它传递下去。这带来一个值得停下体会的后果：**一条定理是否用了排中律，是编译期事实。**经典债务是章节类型的一部分，在每个导入处可见，而不是一条看不见的全局公理；又因为无一处 postulate，全书佩戴 Agda 的 `--safe` 印章。
<!--/-->

<!--en-->
## The first dividend: a small classifier
<!--zh-->
## 第一笔红利：小分类器
<!--/-->

<!--en-->
Classically a proposition has only two possible values, and that innocent remark has
universe-level teeth. First: the entire type of truth values collapses to a
two-element type. `decodeB`{.Agda} sends `true`{.Agda} and `false`{.Agda} to `⊤` and
`⊥`; excluded middle decides any proposition back onto a Boolean; the round trips
below make this an equivalence `Lift Bool ≃ hProp ℓ`, at **every** level `ℓ`.
<!--zh-->
经典地看，命题只有两个可能的值，而这句不起眼的话在宇宙层级上有实实在在的后果。第一：整个真值类型坍缩为二元类型。`decodeB`{.Agda} 把 `true`{.Agda} 与 `false`{.Agda} 送到 `⊤` 与 `⊥`；排中律把任何命题判定回一个布尔值；下面的往返互逆使之成为等价 `Lift Bool ≃ hProp ℓ`，且在**每一个**层级 `ℓ` 上成立。
<!--/-->

```agda
private
  ⊥ₚ : ∀ {ℓ} → hProp ℓ
  ⊥ₚ = ⊥* , isProp⊥*

  decodeB : ∀ {ℓ} → Lift {ℓ-zero} {ℓ} Bool → hProp ℓ
  decodeB (lift true)  = ⊤ₚ where open TruthAlg (hPropAlg) renaming ( ⊤ to ⊤ₚ )
  decodeB (lift false) = ⊥ₚ

  encodeB : ∀ {ℓ} (P : hProp ℓ) → ⟨ P ⟩ ⊎ (⟨ P ⟩ → Empty.⊥) → Lift {ℓ-zero} {ℓ} Bool
  encodeB P (inl _) = lift true
  encodeB P (inr _) = lift false

  secB : ∀ {ℓ} (P : hProp ℓ) (d : ⟨ P ⟩ ⊎ (⟨ P ⟩ → Empty.⊥))
       → decodeB (encodeB P d) ≡ P
  secB P (inl p)  = ⇔toPath (λ _ → p) (λ _ → tt*)
  secB P (inr np) = ⇔toPath (λ ()) (λ p → Empty.rec (np p))

  retrB : ∀ {ℓ} (b : Lift {ℓ-zero} {ℓ} Bool)
          (d : ⟨ decodeB b ⟩ ⊎ (⟨ decodeB b ⟩ → Empty.⊥))
        → encodeB (decodeB b) d ≡ b
  retrB (lift true)  (inl _)  = refl
  retrB (lift true)  (inr n⊤) = Empty.rec (n⊤ tt*)
  retrB (lift false) (inl ())
  retrB (lift false) (inr _)  = refl

lem→smallΩ : ∀ {ℓ} → LEM ℓ → Lift {ℓ-zero} {ℓ} Bool ≃ hProp ℓ
lem→smallΩ lem = isoToEquiv (iso decodeB
  (λ P → encodeB P (lem P))
  (λ P → secB P (lem P))
  (λ b → retrB b (lem (decodeB b))))
```

<!--en-->
## The second dividend: propositional resizing
<!--zh-->
## 第二笔红利：命题降层
<!--/-->

<!--en-->
Second: a proposition living one universe up is equivalent to one living below.
Decide it: if it holds it is equivalent to `⊤`, if it fails it is equivalent to
`⊥`, and both are small. This is **propositional resizing**, and it is the precise
reason classical set theory never worries about which universe a proposition
inhabits. Note the signatures do exact bookkeeping: `lem→resize`{.Agda} consumes
excluded middle at the higher level `ℓ-suc ℓ`, no more.
<!--zh-->
第二：住在高一层宇宙的命题等价于住在低层的命题。判定它：若成立则等价于 `⊤`，若不成立则等价于 `⊥`，而两者都是小的。这就是**命题降层**，也正是经典集合论从不操心命题住在哪个宇宙的确切原因。注意签名做了精确记账：`lem→resize`{.Agda} 恰在较高层级 `ℓ-suc ℓ` 上消费排中律，分毫不多。
<!--/-->

```agda
private
  resizeDec : ∀ {ℓ} (P : hProp (ℓ-suc ℓ)) → ⟨ P ⟩ ⊎ (⟨ P ⟩ → Empty.⊥)
            → Σ[ Q ∈ hProp ℓ ] (⟨ P ⟩ ≃ ⟨ Q ⟩)
  resizeDec {ℓ} P (inl p)  = ⊤ₚ , propBiimpl→Equiv (P .snd) (⊤ₚ .snd) (λ _ → tt*) (λ _ → p)
    where open TruthAlg (hPropAlg {ℓ}) renaming ( ⊤ to ⊤ₚ )
  resizeDec P (inr np) = ⊥ₚ , propBiimpl→Equiv (P .snd) isProp⊥*
                               (λ p → Empty.rec (np p)) (λ ())

lem→resize : ∀ {ℓ} → LEM (ℓ-suc ℓ) → (P : hProp (ℓ-suc ℓ)) → Σ[ Q ∈ hProp ℓ ] (⟨ P ⟩ ≃ ⟨ Q ⟩)
lem→resize lem P = resizeDec P (lem P)
```

<!--en-->
## Recap
<!--zh-->
## 小结
<!--/-->

<!--en-->
Excluded middle is stated as the interface `LEM`{.Agda}, taken by chapters as a
parameter and never assumed globally; the boundary between constructive and
classical mathematics is therefore a compile-time fact. Two dividends are banked:
a small classifier of propositions (`lem→smallΩ`{.Agda}) and propositional resizing
(`lem→resize`{.Agda}). Part 3 will spend exactly these two coins: they redeem, for
the cumulative hierarchy `V`, the smallness assumptions behind full separation and
power set.
<!--zh-->
排中律以接口 `LEM`{.Agda} 的形式陈述，由章节作为参数领取，绝不全局假设；构造与经典数学的边界因此成为编译期事实。存入两笔红利：命题的小分类器 (`lem→smallΩ`{.Agda}) 与命题降层 (`lem→resize`{.Agda})。第三部将恰好花掉这两枚硬币：它们为累积层级 `V` 兑付全分离与幂集背后的小性假设。
<!--/-->
