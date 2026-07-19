# Structures

<!--en-->
A formula means nothing by itself; it needs a world to be about. For the language
of the previous chapter, a world is a **structure** in the sense of model theory: a
carrier together with interpretations of the two predicate symbols, membership and
equality, taking values in a chosen truth algebra. This chapter defines these
structures, the ways of cutting them down, and the environments that will feed
their elements to formulas.
<!--zh-->
公式自身没有含义；它需要一个被谈论的世界。对上一章的语言而言，世界就是模型论意义上的**结构**：一个载体，连同两个谓词符号 (成员与等词) 的解释，取值于选定的真值代数。本章定义这些结构、裁剪它们的方式，以及将把结构元素喂给公式的环境。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

module FOL.Structure where

open import Base.Prelude
open import Base.Truth
open import Cubical.Foundations.HLevels using ( isSetΣSndProp )
open import Cubical.Data.Sigma using ( Σ≡Prop )
```

<!--en-->
## The record
<!--zh-->
## 结构的 record
<!--/-->

<!--en-->
The conventions again, book-wide: script `𝒮` stands for a structure, `S` for its
carrier, and `x`, `y`, `z` for carrier elements, the "sets" the language speaks of.
The superscript `ˢ` on the two relation fields is another layer mark: it says a
symbol is a **field of the structure at hand**. The membership family now has three members
on the page, one glyph per layer: the library's `∈` (the host), this chapter's
`∈ˢ` (the structure), and the previous chapter's `∈̇` (the syntax).
<!--zh-->
仍先立约定，全书通用：花体 `𝒮` 代表结构，`S` 代表其载体，`x`、`y`、`z` 代表载体元素，即这门语言所谈的「集合」。两个关系字段上的上标 `ˢ` 是又一枚层标记：它宣告一个符号是**当前结构的字段**。至此 `∈` 家族在纸面上已有三员，一字一层：库的 `∈` (宿主)、本章的 `∈ˢ` (结构)、上一章的 `∈̇` (语法)。
<!--/-->

```agda
record ZFStructure {ℓ ℓ'} (𝕋 : TruthAlgebra ℓ ℓ') : Type (ℓ-max (ℓ-suc ℓ) ℓ') where
  open TruthAlgebra 𝕋
  field
    S         : Type ℓ
    isSetS    : isSet S
    _≈ˢ_ _∈ˢ_ : S → S → Ω

  infix 20 _≈ˢ_ _∈ˢ_
```

<!--en-->
Two remarks on the fields. That the structure equality `≈ˢ` is a **field**, rather
than being hard-wired to the host's path equality, is load-bearing: in the forcing
part of the book, equality and membership will be a mutually defined pair of graded
relations, genuine content of the model that no meta-level equality could supply.
On the propositional side nothing is lost: when the hierarchy chapter assembles
the book's instance, it simply takes paths for `≈ˢ`.

And a remark on what is **not** here: no axioms. This record is the bare structure;
well-foundedness, extensionality, and the rest belong to Part 2, where they become
the fields of a model. Everything this part builds consumes only the three
projections above, so any two isomorphic structures are, by the host's structure
identity principle, simply equal, and the whole development transports across.
<!--zh-->
关于字段的两点。结构等词 `≈ˢ` 是**字段**而非硬连到宿主的路径相等，这一点是承重的：在本书的力迫部分，等词与成员将是一对互递归定义的分级关系，是模型的真实内容，任何元层相等都供应不了。命题侧则毫无损失，届时装配本书实例的层级章径直以路径充当 `≈ˢ`。

再说说这里**没有**的东西：公理。这个 record 是裸结构；良基、外延等等属于第二部，在那里它们将成为模型的字段。本部构建的一切只消费上面三个投影，于是任何两个同构的结构，按宿主的结构等同原理，干脆就相等，整个开发沿之搬运。
<!--/-->

<!--en-->
## The propositional side
<!--zh-->
## 命题侧
<!--/-->

<!--en-->
On the propositional side one more form of membership is available: extract the
underlying **type** of `x ∈ˢ y`. The superscript `ᵗ` marks this Type-valued
variant; statements of well-foundedness and proofs by membership induction will
quantify over it.
<!--zh-->
命题侧还有一种成员形式可用：把 `x ∈ˢ y` 的底层**类型**取出来。上标 `ᵗ` 标记这个 Type 值的变体；良基性的陈述与按成员归纳的证明都将对它量化。
<!--/-->

```agda
module _ {ℓ} (𝒮 : ZFStructure (hPropAlgebra ℓ)) where
  open ZFStructure 𝒮

  _∈ᵗ_ : S → S → Type ℓ
  x ∈ᵗ y = ⟨ x ∈ˢ y ⟩

  infix 20 _∈ᵗ_
```

<!--en-->
## Substructures
<!--zh-->
## 子结构
<!--/-->

<!--en-->
`↾` reads "restriction": the textbook's passage from a universe to
$(A, \in \restriction A)$. Given a propositional class `M`, the restricted
structure `𝒮 ↾ M` takes as carrier the pairs of an element with a proof of
membership in `M`, and inherits both relations along the first projection. The
consequence worth savouring: instantiate the whole framework at `𝒮 ↾ M`, and the
constant domain of the syntax automatically contains only members of `M`. "The
parameters may only come from this class" stops being a side condition to police
and becomes the shape of a type; Part 4 builds the constructible universe through
exactly this channel.
<!--zh-->
`↾` 读作「限制」：教科书里从全宇宙过渡到 $(A, \in \restriction A)$ 的那一步。给定命题值的类 `M`，限制结构 `𝒮 ↾ M` 以「元素配上属于 `M` 的证明」的对为载体，两个关系沿第一投影继承。值得品味的后果是：在 `𝒮 ↾ M` 上实例化整个框架，语法的常量域就自动只含 `M` 的成员。「参数只能来自这个类」不再是需要巡查的附加条件，而成为类型的形状；第四部正是经由这条通道构造可构造宇宙。
<!--/-->

```agda
_↾_ : ∀ {ℓ} (𝒮 : ZFStructure (hPropAlgebra ℓ))
    → (ZFStructure.S 𝒮 → hProp ℓ) → ZFStructure (hPropAlgebra ℓ)
_↾_ {ℓ} 𝒮 M = record
  { S      = Σ[ x ∈ S ] ⟨ M x ⟩
  ; isSetS = isSetΣSndProp isSetS (λ x → (M x) .snd)
  ; _≈ˢ_   = λ a b → fst a ≈ˢ fst b
  ; _∈ˢ_   = λ a b → fst a ∈ˢ fst b }
  where open ZFStructure 𝒮

infixl 21 _↾_
```

<!--en-->
The restricted equality compares underlying elements; since membership in a
propositional class is proof-irrelevant, equality of first projections reflects
back to equality of the pairs, so nothing is lost.
<!--zh-->
限制结构的等词比较底层元素；由于隶属命题值的类无关乎证明，第一投影的相等可反射回对的相等，毫无损失。
<!--/-->

```agda
↾-reflects : ∀ {ℓ} {𝒮 : ZFStructure (hPropAlgebra ℓ)} {M : ZFStructure.S 𝒮 → hProp ℓ}
             {a b : ZFStructure.S (𝒮 ↾ M)}
           → fst a ≡ fst b → a ≡ b
↾-reflects {M = M} = Σ≡Prop (λ x → (M x) .snd)
```

<!--en-->
## Environments
<!--zh-->
## 环境
<!--/-->

<!--en-->
One more piece of kit and the table is set for semantics. To evaluate a formula
with `n` free variables, each variable needs a value from the carrier: an
**assignment**, or environment, written `γ` throughout the book. The book's
notation for its type is `S ^ n`{.Agda}, a vector of length `n`, matching the
traditional superscript $S^n$ (`_^_`{.Agda} reads "power"); it is nothing but
notation.
<!--zh-->
再备一件行头，语义的桌子就摆齐了。要对带 `n` 个自由变量的公式求值，每个变量都需要一个来自载体的取值：一份**赋值表**，即环境，全书写作 `γ`。其类型记为 `S ^ n`{.Agda}，长度为 `n` 的向量，对齐传统上标记号 $S^n$ (`_^_`{.Agda} 读作「幂」)；它只是记号。
<!--/-->

```agda
infixl 30 _^_

_^_ : ∀ {ℓ} → Type ℓ → ℕ → Type ℓ
A ^ n = Vec A n
```

<!--en-->
## Recap
<!--zh-->
## 小结
<!--/-->

<!--en-->
A structure is three projections, carrier, equality, membership, valued in a truth
algebra and carrying no axioms; `↾` cuts a structure down to a class with
nothing lost (`↾-reflects`{.Agda}), and
environments `S ^ n`{.Agda} stand ready to feed carrier elements to variables.
Syntax on one side, structures on the other: the next chapter joins them.
<!--zh-->
结构就是三个投影：载体、等词、成员，取值于真值代数，不带公理；`↾` 把结构裁剪到一个类而毫无损失 (`↾-reflects`{.Agda})，环境 `S ^ n`{.Agda} 已就位，随时把载体元素喂给变量。一边是语法，一边是结构：下一章让它们相遇。
<!--/-->
