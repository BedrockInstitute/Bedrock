# The frontier

<!--en-->
This book is built root-first: the main theorem is *stated* now and *finished*
over the remaining parts. That calls for a device, and honesty demands it be
neither a hole nor a postulate. The **frontier** is that device: one record
whose fields are precisely the statements not yet proven, so that the root
theorem of the next chapter is an ordinary theorem *from* the frontier. Every
field here is a debt; every remaining chapter of the book pays some of them;
a field, once proven, is deleted. The record is the live registry of what
separates the book from its unconditional theorem, and when it empties, this
chapter disappears with it.

The debts are exactly the model fields still owed for the constructible
structure `𝒮ʟ`: earlier chapters produced the world, paid the five basic axioms,
all of infinity, separation and replacement in full, and the power set, and the
record below lists, field for field, what the model record still demands. The choice field is stated relative to an arbitrary ZF
model on this carrier, the same structural form the hierarchy's choice took.

The record has already shrunk five times. It opened at eleven fields; the basic
axioms took three, the numeral chain three, the collection of the numerals one
more, reflection took the two comprehension fields together, and
bounding took the power set. This is what the device is for: the list gets shorter, never longer, and the book ends when it
is empty. Infinity was the instructive case. Its four fields were never one debt:
three merely built the chain, which cost nothing, and only the fourth, the claim
that the chain is collected into a set, carried the axiom's real content and with
it the whole of its classical price.
<!--zh-->
本书采取从根开始的构造：主定理**现在**陈述，在余下诸部中**逐步完成**。这需要一件装置，而诚实要求它既不是洞也不是公设。**前沿**就是那件装置：一个 record，其字段恰是尚未证明的陈述，于是下一章的根定理是一条**由**前沿出发的普通定理。这里的每个字段都是一笔债；本书余下的每一章偿还其中若干；字段一经证明即被删除。这个 record 是「离无条件定理还差什么」的实时登记簿，账清之日，本章随之消失。

这些债恰是可构造结构 `𝒮ʟ` 尚欠的模型字段：前几章造出了世界，偿清五条基本公理、整条无穷公理、完整的分离与替换，以及幂集，下面的 record 逐字段列出模型 record 仍然索取的部分。选择字段相对于此载体上任意 ZF 模型陈述，与层级那边的选择取同一结构形式。

这个 record 已经缩过五次。它开张时有十一个字段，基本公理拿走三个，数码链三个，数码的收集又一个，反射一举拿走两条概括字段，界层又拿走幂集。这正是这件装置的用途：单子只会变短，不会变长，簿清之日即成书之时。无穷公理曾是有教益的一例。它那四个字段从来就不是一笔债：三个只是造出那条链，分文不花；唯有第四个，即断言那条链被收集成一个集合，承载着公理的真正内容，以及它全部的经典代价。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth

module L.Frontier {ℓ : Level} where

open import FOL.ZFStructure using ( ZFStructure )
import FOL.ZFModel
open import L.Constructible {ℓ} using ( 𝒮ʟ )

import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open ZFStructure 𝒮ʟ

module ModelL = FOL.ZFModel 𝒮ʟ
open ModelL using ( isZFModel )
```

<!--en-->
The choice statement, packaged first so the record can quantify over the model
supplying the intersection it mentions:
<!--zh-->
先打包选择公理的陈述，好让 record 对「供应其中交运算的模型」量化：
<!--/-->

```agda
ChoiceStatement : isZFModel → Type (ℓ-suc ℓ)
ChoiceStatement zf =
  (a : S)
  → ((x : S) → ⟨ x ∈ˢ a ⟩ → ∥ Σ[ y ∈ S ] ⟨ y ∈ˢ x ⟩ ∥₁)
  → ((x y : S) → ⟨ x ∈ˢ a ⟩ → ⟨ y ∈ˢ a ⟩
       → ∥ Σ[ z ∈ S ] (⟨ z ∈ˢ x ⟩ × ⟨ z ∈ˢ y ⟩) ∥₁ → x ≡ y)
  → ∥ Σ[ c ∈ S ] ((x : S) → ⟨ x ∈ˢ a ⟩
       → isContr (Σ[ z ∈ S ] ⟨ z ∈ˢ (c ∩ x) ⟩)) ∥₁
  where open ModelL.isZFModel zf using ( _∩_ )
```

<!--en-->
And the registry itself. Each field's statement is the corresponding model field
at `𝒮ʟ`, verbatim, so that discharging one is a matter of proving exactly what
the record asks for, with no reshaping at the assembly site.
<!--zh-->
然后是登记簿本身。每个字段的陈述都是模型 record 对应字段在 `𝒮ʟ` 处的原文，于是还清一笔债就是证出 record 索取的那个东西本身，装配处无须任何改形。
<!--/-->

```agda
record Frontier : Type (ℓ-suc (ℓ-suc ℓ)) where
  field
    hasChoiceL : (zf : isZFModel) → ChoiceStatement zf
```

<!--en-->
## Recap
<!--zh-->
## 小结
<!--/-->

<!--en-->
One debt, the verbatim statement of a model field at `𝒮ʟ`, and not a postulate:
it is the hypothesis of the next chapter's theorem, and the book's remaining work
is the shrinking of this record to nothing. Choice, which wants a well-ordering
of `L`, and that wants satisfaction internalized.
<!--zh-->
一笔债，是模型字段在 `𝒮ʟ` 处的原文陈述，且不是公设：它是下一章定理的假设，而本书余下的工作，就是把这个 record 缩减为空。选择，它要 `L` 的良序，而后者要满足关系被内化。
<!--/-->
