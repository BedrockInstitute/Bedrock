# Impredicativity

<!--en-->
The host's universes form a ladder, and the ladder poses one recurring question:
does a thing living one floor up have a stand-in below? For **propositions** the
question is the hallmark of *impredicativity*, the world of truth values refusing
to grow with the universe. This chapter mints the vocabulary: what it is for one
proposition to be small, the two sweeping interfaces that assert smallness
wholesale, and their packing. Nothing is assumed and nothing is proven here;
these are interfaces. The next chapter redeems them all from excluded middle,
and Part 3 prices concrete model fields in exactly this currency.
<!--zh-->
宿主的宇宙排成一架梯子，而梯子反复抛出同一个问题：住在高一层的东西，在低层有没有替身？对**命题**而言，这个问题正是**非直谓性**的标志：真值的世界拒绝随宇宙一起膨胀。本章铸下这套词汇：单个命题「是小的」是什么意思，一揽子断言小性的两个接口，以及它们的打包。此处无所假设、亦无所证明；这些是接口。下一章将用排中律把它们全部赎回，第三部则恰以这种货币为具体的模型字段标价。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

module Base.Impredicativity where

open import Base.Prelude
open import Cubical.Foundations.Equiv using ( _≃_ )
```

<!--en-->
## Being small
<!--zh-->
## 何谓小
<!--/-->

<!--en-->
A proposition one universe up **is small** when it is equivalent to some
proposition one universe down. The definition carries the witness: to hold an
inhabitant of `isSmall P`{.Agda} is to hold the small stand-in together with the
equivalence. The smallness chapter of Part 3 will make a whole gymnastics of
passing such witnesses around, earning instances one atom at a time without any
axiom.
<!--zh-->
高一层的命题**是小的**，指它与某个低一层的命题等价。定义随身携带见证：手握 `isSmall P`{.Agda} 的居民，就是手握小替身连同那份等价。第三部的小性一章将把传递这种见证做成一整套体操，逐原子地挣得实例，不花任何公理。
<!--/-->

```agda
isSmall : ∀ {ℓ} → hProp (ℓ-suc ℓ) → Type (ℓ-suc ℓ)
isSmall {ℓ} P = Σ[ Q ∈ hProp ℓ ] (⟨ P ⟩ ≃ ⟨ Q ⟩)
```

<!--en-->
## The two interfaces
<!--zh-->
## 两个接口
<!--/-->

<!--en-->
**Propositional resizing** is the sweeping claim: *every* proposition one
universe up is small. This is the precise reason classical set theory never
worries about which universe a proposition inhabits. Like `LEM`, it is stated
one level at a time.
<!--zh-->
**命题降层**是一揽子断言：高一层的**每个**命题都是小的。这正是经典集合论从不操心命题住在哪个宇宙的确切原因。与 `LEM` 同款，逐层级陈述。
<!--/-->

```agda
Resizing : ∀ ℓ → Type (ℓ-suc (ℓ-suc ℓ))
Resizing ℓ = (P : hProp (ℓ-suc ℓ)) → isSmall P
```

<!--en-->
The second interface speaks not of each proposition but of their totality: the
type of truth values, which lives one universe up, is equivalent to a **small**
type. `HPropSmallness ℓ`{.Agda} asks for a small type equivalent to
`hProp ℓ`{.Agda}, a small classifier of propositions.
<!--zh-->
第二个接口谈的不是单个命题，而是它们的总体：真值类型本住在高一层宇宙，却等价于一个**小**类型。`HPropSmallness ℓ`{.Agda} 索要一个与 `hProp ℓ`{.Agda} 等价的小类型，即命题的小分类器。
<!--/-->

```agda
HPropSmallness : ∀ ℓ → Type (ℓ-suc ℓ)
HPropSmallness ℓ = Σ[ Ω' ∈ Type ℓ ] (Ω' ≃ hProp ℓ)
```

<!--en-->
## The packing
<!--zh-->
## 打包
<!--/-->

<!--en-->
The two instruments share one character, each saying in its own register that
propositions refuse to grow with the universe, and they share their consumers,
so they are packed into one interface, one level at a time. The packing is by
co-consumption, not by implication: neither instrument derives the other (they
descend from two of Voevodsky's separate resizing axioms). The interface says
nothing about any particular structure; it is pure universe-level policy.
<!--zh-->
两件器具共有一种品格，各自以各自的音区说着「命题拒绝随宇宙膨胀」这一句话；它们也共享消费者，于是打包成一个接口，逐层级陈述。打包依据是共同消费而非相互蕴含：两件器具谁也推不出谁 (它们分别源自 Voevodsky 两条分立的 resizing 公理)。这个接口不谈任何特定结构，是纯粹的宇宙层级政策。
<!--/-->

```agda
record Impredicativity (ℓ : Level) : Type (ℓ-suc (ℓ-suc ℓ)) where
  field
    resizing       : Resizing ℓ
    hPropSmallness : HPropSmallness ℓ
```

<!--en-->
## Recap
<!--zh-->
## 小结
<!--/-->

<!--en-->
Smallness of a proposition is an equivalence with a lower stand-in
(`isSmall`{.Agda}); `Resizing`{.Agda} asserts it of every proposition,
`HPropSmallness`{.Agda} of their totality, and `Impredicativity`{.Agda} packs
the two. All of it is vocabulary, none of it is assumed. Next: the one classical
principle this book ever appeals to, and the redemption of this whole chapter
from it.
<!--zh-->
命题的小性即与低层替身的等价 (`isSmall`{.Agda})；`Resizing`{.Agda} 将它断言于每个命题，`HPropSmallness`{.Agda} 断言于它们的总体，`Impredicativity`{.Agda} 把两者打包。以上全是词汇，无一被假设。下一章：本书唯一诉诸的经典原理，以及用它对本章的整体赎回。
<!--/-->
