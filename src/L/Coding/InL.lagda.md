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
open import L.Constructible {ℓ} using ( isL; IsOrd; Lset )
open import L.Coding.Model {ℓ} using ( prʟ; prʟ-fst; numL )
open import L.Coding.Environment {ℓ} using ( env )
open import L.Axioms.Basic {ℓ} using ( finSet; module FinOf )

import Cubical.Data.Empty as Empty
open import Cubical.Data.FinData using ( toℕ )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Constructions using ( module InfinitySet )
open InfinitySet using ( #_ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
```

<!--en-->
## Two building blocks
<!--zh-->
## 两块砖
<!--/-->

<!--en-->
A numeral is constructible for the same reason, and was needed a chapter earlier,
so it lives there. A pair is
constructible because the model has pairing and the same equation reads it back.
A tag is a pair with a numeral on the left, so it is both.

Both are the same two-line move: build the thing inside the model, then transport
its membership along the equation saying that reading it out gives the thing.
<!--zh-->
数码可构造同理，而它早一章就被需要，故住在那里。对可构造，因为模型有配对，而同一条等式把它读回来。标签是左边放数码的对，故两者兼得。

两者都是同样的两行动作：先在模型内部把东西造出来，再沿「读出来就是那个东西」这条等式把它的隶属关系搬过去。
<!--/-->

```agda
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
Terms first. A term is a variable or a constant, and the two are the two tags
that terms carry: a numeral for the variable's index, and the constant's own set
for a constant. So a code is constructible provided the constants it names are,
and the induction takes that as its hypothesis rather than assuming there are
none.

That generality costs one clause and buys the parameters. A formula whose
constants are members of a stage codes to a set of `L` exactly as a
parameter-free one does, which is what lets the recursion below range over the
formulas the constructible hierarchy is actually built from. The parameter-free
case is the instance at the empty type.

Then the formulas, twelve clauses and no content: each constructor's code is a
tag on either a pair of sub-codes, a single sub-code, or a numeral, and the three
blocks above cover all three shapes. The induction is over the parameter-free
formula rather than its embedding, which costs nothing because embedding is a
relabelling and commutes with every constructor definitionally.
<!--zh-->
先看词项。一个词项要么是变元、要么是常元，而两者正是词项所携带的两个标签：变元带它的索引数码，常元带它自己那个集合。故一个码可构造，只要它所点名的诸常元可构造，而这次归纳把那一条取作假设，而非假定根本没有常元。

这份一般性花掉一条子句，换来的是诸参数。常元取自某阶段成员的公式，其编码与无参公式一样是 `L` 的集合，而正是这一点，使下面的递归得以遍历可构造层级实际由之造出的那些公式。无参情形是空类型处的实例。

然后是诸公式，十二条子句，毫无内容：每个构造子的码，都是「子码之对」「单个子码」或「数码」三者之一上的标签，而上面三块砖覆盖了这三种形状。归纳沿无参公式而非它的嵌入进行，这不费分文，因为嵌入是一次常量变换，按定义与每个构造子交换。
<!--/-->

```agda
module _ {K : Type ℓ} (f : K → V ℓ) (h : (k : K) → ⟨ isL (f k) ⟩) where

  codeTmL : ∀ {n} (t : Term K n) → ⟨ isL VCode.⌜ mapTm f t ⌝ᵗ ⟩
  codeTmL (con c) = tagL 0 (h c)
  codeTmL (var i) = tagL 1 (numL _)

  codeL : ∀ {n} (φ : Formula K n) → ⟨ isL VCode.⌜ mapFo f φ ⌝ ⟩
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

codeFreeL : ∀ {n} (φ : Formula (⊥* {ℓ}) n)
          → ⟨ isL VCode.⌜ mapFo Empty.rec* φ ⌝ ⟩
codeFreeL = codeL Empty.rec* (λ ())
```

<!--en-->
## Environments
<!--zh-->
## 环境
<!--/-->

<!--en-->
An environment is a finite set: the keys are the numerals below its length and
the entries are pairs. It is, in fact, *the* finite set of the pairs, on the
nose, because both are the same image of the same lifted index type. Saying so
is one line, and it is the line that lets the finite-family lemma apply to
environments without any further argument.

The consequence is that an environment over a stage is an element of `L`
immediately: its entries are pairs of a numeral with a member of the stage, and
both are in the stage after one step. No recursion on the length, and no
replacement.
<!--zh-->
一个环境是一个有穷集：键是长度以下的诸数码，条目是诸对。事实上它**恰恰就是**那些对构成的有穷集，一分不差，因为两者是同一个被抬升的索引类型的同一个像。把这一点说出来只需一行，而正是这一行使有穷族引理无须任何进一步论证便可施于环境。

由此，落在某阶段之上的环境立刻是 `L` 的元素：它的条目是「数码与该阶段的成员」之对，而两者在一步之后都落在该阶段里。不必沿长度递归，也不必用替换。
<!--/-->

```agda
envIsFinSet : ∀ {n} (g : Fin n → V ℓ)
            → env g ≡ finSet n (λ i → pr (# (toℕ i)) (g i))
envIsFinSet g = refl

envL : (σ : V ℓ) (oσ : IsOrd σ) {n : ℕ} (g : Fin n → V ℓ)
     → ((i : Fin n) → ⟨ pr (# (toℕ i)) (g i) ∈ Lset σ ⟩)
     → ⟨ isL (env g) ⟩
envL σ oσ {n} g h =
  subst (λ w → ⟨ isL w ⟩) (sym (envIsFinSet g))
    (FinOf.finSetL σ oσ n (λ i → pr (# (toℕ i)) (g i)) h)
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

`envL`{.Agda} then puts an environment in `L` with no recursion on its length and
no use of replacement, because an environment is on the nose the finite set of
its entries.

The set of all codes is still not an element of `L`, and is still not needed.
<!--zh-->
`codeL`{.Agda} 说每个码都是 `L` 的元素，而 `numL`{.Agda}、`prL`{.Agda} 与 `tagL`{.Agda} 是它所由构造的三种形状。有了它，一个码就可以被点名为模型对象语言的常元，而一族码就可以充当某个已内化递归的定义域。

`envL`{.Agda} 随后把一个环境放进 `L`，既不沿长度递归，也不用替换，因为一个环境恰恰就是它诸条目构成的有穷集。

全体码之集仍然不是 `L` 的元素，也仍然不需要是。
<!--/-->
