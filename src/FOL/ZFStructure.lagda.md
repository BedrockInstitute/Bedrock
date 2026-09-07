<!--en-->
# Structures

Before asking whether a universe satisfies any axiom, we must specify the world in which formulas are interpreted. A `ZFStructure`{.Agda} consists of a set-like carrier together with equality and membership valued in a chosen truth algebra; this chapter then defines transitive classes and restriction to a substructure.
<!--zh-->
# 结构

在询问一个宇宙是否满足任何公理之前，必须先指定公式在哪个世界中解释。`ZFStructure`{.Agda} 由一个集合型载体，以及在选定真值代数中取值的相等与隶属关系组成；本章随后定义传递类与结构到子结构的限制。
<!--ja-->
# 構造

ある宇宙が公理を満たすかを問う前に、論理式を解釈する世界を指定する必要があります。`ZFStructure`{.Agda} は集合らしい台と、選んだ真理値代数に値を持つ等号および所属関係からなります。本章ではさらに推移的クラスと部分構造への制限を定義します。
<!--/-->

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

module FOL.ZFStructure where

open import Base.Prelude
open import Base.Truth
open import Cubical.Foundations.HLevels using ( isSetΣSndProp )
open import Cubical.Data.Sigma using ( Σ≡Prop )
```

<!--en-->
## The record

The conventions again, book-wide: script `𝒮` stands for a structure, `S` for its
carrier, and `x`, `y`, `z` for carrier elements, the "sets" the language speaks of.
The superscript `ˢ` on the two relation fields is another layer mark: it says a
symbol is a **field of the structure at hand**. The membership family now has three members
on the page, one glyph per layer: the library's `∈` (the host), this chapter's
`∈ˢ` (the structure), and the previous chapter's `∈̇` (the syntax).
<!--zh-->
## 结构的 record

仍先立约定，全书通用：花体 `𝒮` 代表结构，`S` 代表其载体，`x`、`y`、`z` 代表载体元素，即这门语言所谈的「集合」。两个关系字段上的上标 `ˢ` 是又一枚层标记：它宣告一个符号是**当前结构的字段**。至此 `∈` 家族在纸面上已有三员，一字一层：库的 `∈` (宿主)、本章的 `∈ˢ` (结构)、上一章的 `∈̇` (语法)。
<!--ja-->
## 構造の record

`ZFStructure`{.Agda} は台 `S` が集合であることと、`S` 上の等号 `≈ˢ` および所属 `∈ˢ` を記録します。ここでは外延性や正則性などの公理をまだ要求しません。
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
well-foundedness, extensionality, and the rest belong to the model chapters, where they become
the fields of a model. Everything this part builds consumes only the three
projections above, so any two isomorphic structures are, by the host's structure
identity principle, simply equal, and the whole development transports across.
<!--zh-->
关于字段的两点。结构等词 `≈ˢ` 是**字段**而非硬连到宿主的路径相等，这一点是承重的：在本书的力迫部分，等词与成员将是一对互递归定义的分级关系，是模型的真实内容，任何元层相等都供应不了。命题侧则毫无损失，届时装配本书实例的层级章径直以路径充当 `≈ˢ`。

再说说这里**没有**的东西：公理。这个 record 是裸结构；良基、外延等等属于模型诸章，在那里它们将成为模型的字段。本部构建的一切只消费上面三个投影，于是任何两个同构的结构，按宿主的结构等同原理，干脆就相等，整个开发沿之搬运。
<!--/-->

<!--en-->
## The propositional side

On the propositional side one more form of membership is available: extract the
underlying **type** of `x ∈ˢ y`. The superscript `ᵗ` marks this Type-valued
variant; statements of well-foundedness and proofs by membership induction will
quantify over it. It lives in `hPropStructure`{.Agda}, the propositional side's
way of opening a structure: the module re-exports the three projections and adds
`∈ᵗ`, so one `open` later a chapter writes `y ∈ᵗ x` with no structure argument
in sight.
<!--zh-->
## 命题侧

命题侧还有一种成员形式可用：把 `x ∈ˢ y` 的底层**类型**取出来。上标 `ᵗ` 标记这个 Type 值的变体；良基性的陈述与按成员归纳的证明都将对它量化。它住在 `hPropStructure`{.Agda} 里，即命题侧打开结构的方式：该模块公开再导出三个投影并添上 `∈ᵗ`，一次 `open` 之后，章节径直写 `y ∈ᵗ x`，不见任何结构参数。
<!--ja-->
## 命題として読む

真理値が `hProp` の場合、`hPropStructure` は真理値をその基礎型へ展開し、所属を Type 値の関係 `∈ᵗ` として読めるようにします。
<!--/-->



```agda
module hPropStructure {ℓ} (𝒮 : ZFStructure (hPropAlgebra ℓ)) where
  open ZFStructure 𝒮 public

  _∈ᵗ_ : S → S → Type ℓ
  x ∈ᵗ y = ⟨ x ∈ˢ y ⟩

  infix 20 _∈ᵗ_
```

<!--en-->
## Transitive classes

A class `M` over a carrier is **transitive** when members of its members stay in
it. The absoluteness chapter's theorems consume exactly this hypothesis, and
the constructible-universe development builds its world out of transitive stages; the name is minted here,
beside the memberships it speaks.
<!--zh-->
## 传递类

载体上的类 `M`，若成员的成员仍在其中，称为**传递**。绝对性一章的诸定理消费的恰是这一前提，可构造宇宙诸章的世界也由传递的阶段砌成；名字在此铸下，与它谈论的成员关系为邻。
<!--ja-->
## 推移的クラス

クラス `M` が推移的であるとは、`M` の要素に属する集合が再び `M` に入ることです。この閉包性により、有界量化の意味を周囲の構造とクラス内部で比較できます。
<!--/-->



```agda
Transitive : ∀ {ℓ} (𝒮 : ZFStructure (hPropAlgebra ℓ))
           → (ZFStructure.S 𝒮 → hProp ℓ) → Type ℓ
Transitive 𝒮 M = ∀ {x y} → y ∈ᵗ x → x ∈ᶜ M → y ∈ᶜ M
  where open hPropStructure 𝒮
```

<!--en-->
## Substructures

`↾` reads "restriction": the textbook's passage from a universe to
$(A, \in \restriction A)$. Given a propositional class `M`, the restricted
structure `𝒮 ↾ M` takes as carrier the pairs of an element with a proof of
membership in `M`, and inherits both relations along the first projection. The
consequence worth savouring: instantiate the whole framework at `𝒮 ↾ M`, and the
constant domain of the syntax automatically contains only members of `M`. "The
parameters may only come from this class" stops being a side condition to police
and becomes the shape of a type; the constructible-universe development builds the constructible universe through
exactly this channel.
<!--zh-->
## 子结构

`↾` 读作「限制」：教科书里从全宇宙过渡到 $(A, \in \restriction A)$ 的那一步。给定命题值的类 `M`，限制结构 `𝒮 ↾ M` 以「元素配上属于 `M` 的证明」的对为载体，两个关系沿第一投影继承。值得品味的后果是：在 `𝒮 ↾ M` 上实例化整个框架，语法的常元域就自动只含 `M` 的成员。「参数只能来自这个类」不再是需要巡查的附加条件，而成为类型的形状；可构造宇宙的开发正是经由这条通道构造可构造宇宙。
<!--ja-->
## 部分構造

制限 `𝒮 ↾ M`{.Agda} は、台を `M` に属する要素とその証明の組へ狭め、等号と所属を第一射影に沿って元の構造から引き戻します。この型を定数域に選ぶと、パラメータが自動的に `M` の要素へ限られ、構成可能宇宙の構成はこの仕組みを利用できます。
<!--/-->



```agda
_↾_ : ∀ {ℓ} (𝒮 : ZFStructure (hPropAlgebra ℓ))
    → (ZFStructure.S 𝒮 → hProp ℓ) → ZFStructure (hPropAlgebra ℓ)
_↾_ {ℓ} 𝒮 M = record
  { S      = Σ[ x ∈ S ] (x ∈ᶜ M)
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
## Recap

A structure is three projections, carrier, equality, membership, valued in a truth
algebra and carrying no axioms; transitive classes name the condition the
travelling chapters will keep consuming; `↾` cuts a structure down to a class
with nothing lost (`↾-reflects`{.Agda}).
Syntax on one side, structures on the other: the next chapter joins them.
<!--zh-->
## 小结

结构就是三个投影：载体、等词、成员，取值于真值代数，不带公理；传递类为后文各章反复消费的条件命名；`↾` 把结构裁剪到一个类而毫无损失 (`↾-reflects`{.Agda})。一边是语法，一边是结构：下一章让它们相遇。
<!--ja-->
## まとめ

`ZFStructure`{.Agda} は公理を持たない解釈の舞台です。命題値の場合にはクラスと推移性を定義でき、推移的クラスへの制限から、絶対性を述べる二つ目の構造が得られます。
<!--/-->
