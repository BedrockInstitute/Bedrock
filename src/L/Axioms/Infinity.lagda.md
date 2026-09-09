<!--en-->
# The axiom of infinity in L
<!--zh-->
# L 中的无穷公理
<!--ja-->
# L における無限公理
<!--/-->

<!--en-->
This chapter proves the axiom of infinity for the constructible universe by
showing that the ambient set `ω` is constructible and has exactly the internal
numeral chain as its members.
<!--zh-->
本章证明可构造宇宙中的无穷公理：环境集合 `ω` 是可构造的，且其成员恰为内部数码链。
<!--ja-->
本章では、周囲の集合 `ω` が構成可能であり、その要素が内部の数項列とちょうど一致することを示して、構成可能宇宙の無限公理を証明する。
<!--/-->

<!--en-->
The chain of numerals was built in the previous chapter and cost nothing. What
is left is the axiom itself, which is one step and is where the whole classical
price of infinity is paid.
<!--zh-->
数码链已在上一章造好，分文未花。剩下的是公理本身，只有一步，而无穷公理全部的经典代价都付在这一步上。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module L.Axioms.Infinity {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
import FOL.ZFModel
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL )
open import L.Ordinal {ℓ} using ( suc-ord; ω-ord )
open import L.Ordinal.Stages {ℓ} lem using ( ord∈Lset-suc )
open import L.Axioms.Basic {ℓ} using ( uniqueL )
open import L.Axioms.Numerals {ℓ} using ( numeralL; numeralL-fst )

import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁ )
open import Cubical.Functions.Logic using ( ⇔toPath )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet )
open InfinitySet using ( sucV; ω )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ

module ModelL = FOL.ZFModel 𝒮ʟ
open ModelL using ( SetOf )
```

<!--en-->
## Collecting the chain
<!--zh-->
## 收集这条链
<!--ja-->
## 数項列を集合に集める
<!--/-->

<!--en-->
`isNumeralL`{.Agda} names the internal numeral predicate, and
`hasInfinityL`{.Agda} realizes it with the constructible set `ω` using the two
pinning equations from the numeral chapter.
<!--zh-->
`isNumeralL`{.Agda} 点名内部数码谓词，而 `hasInfinityL`{.Agda} 借助数码章的两条钉死方程，以可构造集合 `ω` 实现该谓词。
<!--ja-->
`isNumeralL`{.Agda} は内部の数項述語を名づけ、`hasInfinityL`{.Agda} は数項の章の二つの指定方程式を用いて、構成可能集合 `ω` によりその述語を実現する。
<!--/-->

<!--en-->
Now the axiom proper. A set whose members are exactly the numerals must be
exhibited inside `L`, and the ambient hierarchy has the obvious candidate,
namely `ω`. What has to be shown is that `ω` is constructible, and the previous
chapter gives it in one line: `ω` is an ordinal, and an ordinal appears at the
stage after itself.

This is the step that uses the excluded middle, and it is worth seeing where
it is used. Not in the chain, which needs none; not in collecting a family,
which no principle here does; but in knowing *which ordinals live at which
stage*, and that is a comparison.
<!--zh-->
现在是公理本身。必须在 `L` 内拿出一个成员恰为诸数码的集合，而环境层级有现成的候选，即 `ω`。要证的是 `ω` 可构造，上一章一行给出：`ω` 是序数，而序数现身于自身之后的那个阶段。

此步使用排中律，具体用在判断各序数属于哪个阶段。数码链本身的构造不需要排中律；本章也没有使用一般的族收集原理。需要经典推理的是序数比较，由它确定收集数码链所需的阶段。
<!--/-->

```agda
ω∈L : ⟨ isL ω ⟩
ω∈L = ∣ sucV ω , (suc-ord ω-ord , ord∈Lset-suc ω ω-ord) ∣₁

ωʟ : S
ωʟ = ω , ω∈L
```

<!--en-->
It remains to check that the members of `ωʟ` are exactly the numerals of the
chain. Membership in `ωʟ` is membership in `ω`, which the library gives as
"merely hit by some library numeral"; the chain's projection equation turns each
of those into a member of the chain, and back. So `ωʟ` realises the numeral
predicate, and extensionality makes it the unique such set.
<!--zh-->
余下要核对的是 `ωʟ` 的成员恰是链上的诸数码。属于 `ωʟ` 就是属于 `ω`，而库把后者给成「仅仅被某个库数码命中」；链的投影等式把其中每一个换成链的成员，反之亦然。于是 `ωʟ` 实现了那个数码谓词，而外延性使它成为唯一这样的集合。
<!--/-->

```agda
isNumeralL : S → Ω
isNumeralL x = ⋁ (Lift {ℓ-zero} {ℓ-suc ℓ} ℕ) (λ n → x ≈ˢ numeralL (lower n))

ω-specL : (x : S) → (x ∈ˢ ωʟ) ≡ isNumeralL x
ω-specL x = ⇔toPath
  (PT.map (λ { (k , p) → lift (lower k)
             , (sym p ∙ sym (numeralL-fst (lower k))) }))
  (PT.map (λ { (n , q) → lift (lower n)
             , (sym (q ∙ numeralL-fst (lower n))) }))

hasInfinityL : isContr (SetOf isNumeralL)
hasInfinityL = uniqueL isNumeralL (ωʟ , ω-specL)
```

<!--en-->
## Recap
<!--zh-->
## 小结
<!--ja-->
## まとめ
<!--/-->

<!--en-->
The constructible set `ω` collects exactly `numeralL`{.Agda}, completing the
model's infinity field under the chapter's excluded-middle parameter.
<!--zh-->
可构造集合 `ω` 恰好收集 `numeralL`{.Agda}，从而在本章的排中律参数下完成模型的无穷字段。
<!--ja-->
構成可能集合 `ω` が `numeralL`{.Agda} をちょうど集め、本章の排中律パラメータの下でモデルの無限フィールドを完成させる。
<!--/-->

<!--en-->
The axiom of infinity is fully established: the chain `numeralL`{.Agda} with its
two pinning equations, and `hasInfinityL`{.Agda} collecting it into a set. Four
fields leave the frontier, and the split between them is the chapter's lesson.
Building the chain required no classical assumption; collecting it required one
comparison of ordinals, and therefore the excluded middle. That is the whole
classical content of infinity in `L`, and it is visible in this chapter's
telescope.
<!--zh-->
无穷公理已经证明：包括数码链 `numeralL`{.Agda}、确定该链的两条方程，以及把它收集成集合的 `hasInfinityL`{.Agda}。前沿由此减少四个字段。本章区分了两个步骤：构造数码链不需要经典假设；把它收集成集合需要一次序数比较，因而使用排中律。这就是 `L` 中无穷公理所需的全部经典内容，并明确出现在本章的参数表中。
<!--/-->
