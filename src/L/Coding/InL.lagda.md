# Codes are constructible

<!--en-->
A code is a hereditarily finite set built by pairing numerals, so it ought to be
an element of `L`, and this chapter says so. The proof is one induction over the
formula constructors with nothing in it, but the statement is what lets a later
chapter treat a code as an ordinary element of the model rather than as a set of
the hierarchy that happens to be lying around.

It matters more than it looks. A recursion internalized in `L` takes its domain
from a small family of *elements of `L`*, and the family here is the codes; a
graph naming a code as a constant needs that code to be an element of the model,
since the object language of the model has no other kind of constant. Both
requirements are this one lemma.

What is deliberately not proved is that the set of *all* codes is an element of
`L`. Nothing needs it: a recursion over codes puts them inside a stage from the
small index type, one at a time, and cuts back by separation. The set of all
codes is a much harder object than any code, and the difference is the whole
reason it is not here.
<!--zh-->
一个码是由配对数码造出的遗传有穷集，故它理应是 `L` 的元素，而本章就这么说。证明是沿公式构造子的一次归纳，里面什么也没有；但这条陈述使后续章节能把码当作模型的寻常元素，而非当作恰好躺在那里的层级集合。

它比看上去要紧。一个在 `L` 中内化的递归，其定义域取自 `L` **诸元素**的小族，而此处那个族就是诸码；而一个把码点名为常元的图，需要那个码是模型的元素，因为模型的对象语言没有别种常元。这两项要求都是这一条引理。

刻意不证的是「**全体**码之集是 `L` 的元素」。没有东西需要它：对码的递归从小索引类型出发，把它们逐个放进一个阶段，再由分离切回来。全体码之集是比任何单个码都难得多的对象，而这个差别正是它不在此处的全部理由。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth

module L.Coding.InL {ℓ : Level} where

open import FOL.Syntax
  using ( Term; con; var; Formula; _∈̇_; _≐_; _∧̇_; _∨̇_; _⇒̇_; ¬̇_; ⊤̇; ⊥̇
        ; ∃̇_; ∀̇_; ∀̇∈; ∃̇∈ )
open import FOL.Manipulation.Relabelling using ( mapTm; mapFo )
open import V.Coding {ℓ} using ( pr; module VCode )
open import L.Constructible {ℓ} using ( isL )
open import L.Axioms.Numerals {ℓ} using ( numeralL; numeralL-fst )
open import L.Coding.Model {ℓ} using ( prʟ; prʟ-fst )

import Cubical.Data.Empty as Empty
open import Cubical.HITs.CumulativeHierarchy.Base using ( V )
open import Cubical.HITs.CumulativeHierarchy.Constructions using ( module InfinitySet )
open InfinitySet using ( #_ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
```

<!--en-->
## Three building blocks
<!--zh-->
## 三块砖
<!--/-->

<!--en-->
A numeral is constructible because the numeral chain was built inside the model
and its projection equation identifies it with the hierarchy's. A pair is
constructible because the model has pairing and the same equation reads it back.
A tag is a pair with a numeral on the left, so it is both.

Each is the same two-line move: build the thing inside the model, then transport
its membership along the equation saying that reading it out gives the thing.
<!--zh-->
数码可构造，因为数码链是在模型内部造的，而它的投影等式把它与层级的数码认同起来。对可构造，因为模型有配对，而同一条等式把它读回来。标签是左边放数码的对，故两者兼得。

三者都是同样的两行动作：先在模型内部把东西造出来，再沿「读出来就是那个东西」这条等式把它的隶属关系搬过去。
<!--/-->

```agda
numL : (k : ℕ) → ⟨ isL (# k) ⟩
numL k = subst (λ w → ⟨ isL w ⟩) (numeralL-fst k) (numeralL k .snd)

prL : {a b : V ℓ} → ⟨ isL a ⟩ → ⟨ isL b ⟩ → ⟨ isL (pr a b) ⟩
prL {a} {b} pa pb =
  subst (λ w → ⟨ isL w ⟩) (prʟ-fst (a , pa) (b , pb))
    (prʟ (a , pa) (b , pb) .snd)

tagL : (k : ℕ) {x : V ℓ} → ⟨ isL x ⟩ → ⟨ isL (VCode.mkTag k x) ⟩
tagL k px = prL (numL k) px
```

<!--en-->
## The induction
<!--zh-->
## 归纳
<!--/-->

<!--en-->
Terms first. A parameter-free term is a variable, so its code is a tag on a
numeral; the constant case cannot occur, and the empty type says so.

Then the formulas, twelve clauses and no content: each constructor's code is a
tag on either a pair of sub-codes, a single sub-code, or a numeral, and the three
blocks above cover all three shapes. The induction is over the parameter-free
formula rather than its embedding, which costs nothing because embedding is a
relabelling and commutes with every constructor definitionally.
<!--zh-->
先看词项。无参词项是变元，故它的码是数码上的一个标签；常元情形不可能出现，而空类型正是这么说的。

然后是诸公式，十二条子句，毫无内容：每个构造子的码，都是「子码之对」「单个子码」或「数码」三者之一上的标签，而上面三块砖覆盖了这三种形状。归纳沿无参公式而非它的嵌入进行，这不费分文，因为嵌入是一次常量变换，按定义与每个构造子交换。
<!--/-->

```agda
codeTmL : ∀ {n} (t : Term (⊥* {ℓ}) n)
        → ⟨ isL VCode.⌜ mapTm Empty.rec* t ⌝ᵗ ⟩
codeTmL (con c) = Empty.rec* c
codeTmL (var i) = tagL 1 (numL _)

codeL : ∀ {n} (φ : Formula (⊥* {ℓ}) n)
      → ⟨ isL VCode.⌜ mapFo Empty.rec* φ ⌝ ⟩
codeL (t ∈̇ u)  = tagL 0  (prL (codeTmL t) (codeTmL u))
codeL (t ≐ u)  = tagL 1  (prL (codeTmL t) (codeTmL u))
codeL (φ ∧̇ ψ)  = tagL 2  (prL (codeL φ) (codeL ψ))
codeL (φ ∨̇ ψ)  = tagL 3  (prL (codeL φ) (codeL ψ))
codeL (φ ⇒̇ ψ)  = tagL 4  (prL (codeL φ) (codeL ψ))
codeL (¬̇ φ)    = tagL 5  (codeL φ)
codeL ⊤̇        = tagL 6  (numL 0)
codeL ⊥̇        = tagL 7  (numL 0)
codeL (∃̇ φ)    = tagL 8  (codeL φ)
codeL (∀̇ φ)    = tagL 9  (codeL φ)
codeL (∀̇∈ t φ) = tagL 10 (prL (codeTmL t) (codeL φ))
codeL (∃̇∈ t φ) = tagL 11 (prL (codeTmL t) (codeL φ))
```

<!--en-->
## Recap
<!--zh-->
## 小结
<!--/-->

<!--en-->
`codeL`{.Agda} says every code is an element of `L`, and `numL`{.Agda},
`prL`{.Agda} and `tagL`{.Agda} are the three shapes it is built from. With it a
code may be named as a constant of the model's object language, and a family of
codes may be the domain of an internalized recursion.

The set of all codes is still not an element of `L`, and is still not needed.
<!--zh-->
`codeL`{.Agda} 说每个码都是 `L` 的元素，而 `numL`{.Agda}、`prL`{.Agda} 与 `tagL`{.Agda} 是它所由构造的三种形状。有了它，一个码就可以被点名为模型对象语言的常元，而一族码就可以充当某个已内化递归的定义域。

全体码之集仍然不是 `L` 的元素，也仍然不需要是。
<!--/-->
