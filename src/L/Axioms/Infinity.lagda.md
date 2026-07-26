# The axiom of infinity in L

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
<!--/-->

<!--en-->
Now the axiom proper. A set whose members are exactly the numerals must be
exhibited inside `L`, and the ambient hierarchy has the obvious candidate,
namely `ω`. What has to be shown is that `ω` is constructible, and the previous
chapter gives it in one line: `ω` is an ordinal, and an ordinal appears at the
stage after itself.

This is the step that costs the excluded middle, and it is worth seeing where
the cost went. Not into the chain, which was free; not into collecting a family,
which no principle here does; but into knowing *which ordinals live at which
stage*, and that is a comparison.
<!--zh-->
现在是公理本身。必须在 `L` 内拿出一个成员恰为诸数码的集合，而环境层级有现成的候选，即 `ω`。要证的是 `ω` 可构造，上一章一行给出：`ω` 是序数，而序数现身于自身之后的那个阶段。

这就是花费排中律的那一步，值得看清代价花在了哪里。不在链上，链是免费的；不在收集一个族上，此处没有任何原则做那件事；而在于知道**哪些序数住在哪个阶段**，那是一次比较。
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
<!--/-->

<!--en-->
The axiom of infinity is paid in full: the chain `numeralL`{.Agda} with its two
pinning equations, and `hasInfinityL`{.Agda} collecting it into a set. Four
fields leave the frontier, and the split between them is the chapter's lesson.
Building the chain was free; collecting it cost one comparison of ordinals, and
therefore the excluded middle. That is the whole classical content of infinity
in `L`, and it is visible in this chapter's telescope.
<!--zh-->
无穷公理已全额付清：链 `numeralL`{.Agda} 连同它的两条钉死方程，以及把它收集成集合的 `hasInfinityL`{.Agda}。四个字段离开前沿，而二者之间的分野正是本章的教益。造链是免费的；收集它花掉一次序数比较，从而花掉排中律。这就是 `L` 中无穷公理的全部经典内容，而它在本章的参数表里一望可见。
<!--/-->
