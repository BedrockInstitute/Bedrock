<!--en-->
# Impredicativity

A proposition is small when it is equivalent to one in a lower universe. This chapter distinguishes propositional resizing, which makes each higher-level proposition small, from a small classifier that presents the whole type of truth values at a lower level, then packages both principles for the hierarchy models.
<!--zh-->
# 非直谓性

一个命题若等价于较低宇宙中的命题，就称为小的。本章区分两项原理：命题降层使每个高层命题都是小的，小分类器则在低层呈现整个真值类型；随后把二者包装起来，供层级模型使用。
<!--ja-->
# 非可述性

命題が低い宇宙の命題と同値であるとき、その命題は小さいといいます。本章では、上位の各命題を小さくする命題リサイズと、真理値型全体を低いレベルで提示する小分類子を区別し、両方の原理を階層モデルのためにまとめます。
<!--/-->

<!--en-->
The host's universes form a ladder, and the ladder poses one recurring question:
does a thing living one floor up have a stand-in below? For **propositions** the
question is the hallmark of *impredicativity*, the world of truth values refusing
to grow with the universe. This chapter mints the vocabulary: what it is for one
proposition to be small, the two sweeping interfaces that assert smallness
wholesale, and their packing. Nothing is assumed and nothing is proven here;
these are interfaces. The next chapter redeems them all from excluded middle,
and the cumulative-hierarchy chapters prices concrete model fields in exactly this currency.
<!--zh-->
宿主的宇宙排成一架梯子，而梯子反复抛出同一个问题：住在高一层的东西，在低层有没有替身？对**命题**而言，这个问题正是**非直谓性**的标志：真值的世界拒绝随宇宙一起膨胀。本章铸下这套词汇：单个命题「是小的」是什么意思，一揽子断言小性的两个接口，以及它们的打包。此处无所假设、亦无所证明；这些是接口。下一章将用排中律把它们全部赎回，累积层级诸章则恰以这种货币为具体的模型字段标价。
<!--/-->



```agda
{-# OPTIONS --cubical --safe --guardedness #-}

module Base.Impredicativity where

open import Base.Prelude
open import Cubical.Foundations.Equiv using ( _≃_ )
```

<!--en-->
## Being small

A proposition one universe up **is small** when it is equivalent to some
proposition one universe down. The definition carries the witness: to hold an
inhabitant of `isSmall P`{.Agda} is to hold the small stand-in together with the
equivalence. The smallness chapter of the cumulative-hierarchy chapters will make a whole gymnastics of
passing such witnesses around, earning instances one atom at a time without any
axiom.
<!--zh-->
## 何谓小

高一层的命题**是小的**，指它与某个低一层的命题等价。定义随身携带见证：手握 `isSmall P`{.Agda} 的居民，就是手握小替身连同那份等价。累积层级诸章的小性一章将把传递这种见证做成一整套体操，逐原子地挣得实例，不花任何公理。
<!--ja-->
## 小さいということ

`isSmall P`{.Agda} は、命題 `P` に対して低い宇宙の命題とその同値を与えます。後の章では、この具体的な証拠を論理結合子や量化子に沿って運びます。
<!--/-->



```agda
isSmall : ∀ {ℓ} → hProp (ℓ-suc ℓ) → Type (ℓ-suc ℓ)
isSmall {ℓ} P = Σ[ Q ∈ hProp ℓ ] (⟨ P ⟩ ≃ ⟨ Q ⟩)
```

<!--en-->
## The two interfaces

**Propositional resizing** is the sweeping claim: *every* proposition one
universe up is small. This is the precise reason classical set theory never
worries about which universe a proposition inhabits. Like `LEM`, it is stated
one level at a time.
<!--zh-->
## 两个接口

**命题降层**是一揽子断言：高一层的**每个**命题都是小的。这正是经典集合论从不操心命题住在哪个宇宙的确切原因。与 `LEM` 同款，逐层级陈述。
<!--ja-->
## 二つのインターフェース

`Resizing`{.Agda} は高い宇宙の各命題に小さい代理を与え、`HPropSmallness`{.Agda} は真理値型 `hProp ℓ`{.Agda} 全体に小分類子を与えます。
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

The two instruments share one character, each saying in its own register that
propositions refuse to grow with the universe, and they share their consumers,
so they are packed into one interface, one level at a time. The packing is by
co-consumption, not by implication: neither instrument derives the other (they
descend from two of Voevodsky's separate resizing axioms). The interface says
nothing about any particular structure; it is pure universe-level policy.
<!--zh-->
## 打包

两件器具共有一种品格，各自以各自的口吻说着「命题拒绝随宇宙膨胀」这一句话；它们也共享消费者，于是打包成一个接口，逐层级陈述。打包依据是共同消费而非相互蕴含：两件器具谁也推不出谁 (它们分别源自 Voevodsky 两条分立的 resizing 公理)。这个接口不谈任何特定结构，是纯粹的宇宙层级政策。
<!--ja-->
## 二つの仮定をまとめる

`Impredicativity ℓ`{.Agda} は命題リサイズと小分類子を一つの record にまとめます。二つを同一視せず、両方を必要とする章へ同じレベルで渡せます。
<!--/-->



```agda
record Impredicativity (ℓ : Level) : Type (ℓ-suc (ℓ-suc ℓ)) where
  field
    resizing       : Resizing ℓ
    hPropSmallness : HPropSmallness ℓ
```

<!--en-->
## Recap

Smallness of a proposition is an equivalence with a lower stand-in
(`isSmall`{.Agda}); `Resizing`{.Agda} asserts it of every proposition,
`HPropSmallness`{.Agda} of their totality, and `Impredicativity`{.Agda} packs
the two. All of it is vocabulary, none of it is assumed. Next: the one classical
principle this book ever appeals to, and the redemption of this whole chapter
from it.
<!--zh-->
## 小结

命题的小性即与低层替身的等价 (`isSmall`{.Agda})；`Resizing`{.Agda} 将它断言于每个命题，`HPropSmallness`{.Agda} 断言于它们的总体，`Impredicativity`{.Agda} 把两者打包。以上全是词汇，无一被假设。下一章：本书唯一诉诸的经典原理，以及用它对本章的整体赎回。
<!--ja-->
## まとめ

小ささは低い宇宙の命題との同値です。命題リサイズと小分類子は異なる小ささの原理であり、`Impredicativity`{.Agda} が両方を明示的に保持します。
<!--/-->
