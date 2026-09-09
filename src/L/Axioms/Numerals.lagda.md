<!--en-->
# The numeral chain
<!--zh-->
# 数码链
<!--ja-->
# 数項列
<!--/-->

<!--en-->
This chapter constructs the natural-number chain inside `L` from the model's
empty-set, pairing, and union operations, and proves that it projects to the
ambient von Neumann numerals.
<!--zh-->
本章从模型自身的空集、配对与并运算出发，在 `L` 内构造自然数链，并证明它投影到环境中的冯·诺伊曼数码。
<!--ja-->
本章ではモデル自身の空集合、対、和集合の演算から `L` 内部の自然数列を構成し、それが周囲のフォン・ノイマン数項へ射影されることを証明する。
<!--/-->

<!--en-->
Infinity is stated in this book in its strong form: the numerals form a set. That
statement has two halves, and they are of very different difficulty. First the
chain itself has to exist inside `L`, with zero at the bottom and each numeral
the successor of the last; then that chain has to be *collected*, which is the
axiom proper. This chapter does the first half, and the half is essentially
immediate, because the previous chapter already built everything a successor
is made of.

The point worth watching is a mismatch. Inside the model, the successor of `a`
is `a ∪ {a}`, spelled with the model's own pairing and union, and those are
`℩`-projections out of unique-existence proofs rather than the library's set
operations. Outside, the ambient hierarchy has its own successor, and its own
chain of numerals built from it. The two chains ought to agree, but nothing so
far says they do: one is assembled from contractibility centres, the other from
constructors. So this chapter's real content is a family of **projection
equations**, saying that the model's operations, read through the underlying
set, are the hierarchy's operations. With those in hand the two chains coincide
step by step, and the two pinning equations that the model record demands of a
numeral chain follow by transporting the hierarchy's own facts along them.
<!--zh-->
本书的无穷公理取强形式：数码构成一个集合。这个陈述有两半，难度截然不同。首先，链本身必须存在于 `L` 之内，零在底，每个数码是前一个的后继；然后这条链必须被**收集**起来，那才是公理本身。本章做第一半，而这一半几乎没有难度，因为上一章已经把后继所需的一切都造好了。

值得注意的是一处错位。在模型内部，`a` 的后继是 `a ∪ {a}`，用模型自己的配对与并写出，而那两者是从唯一存在性证明中取出的 `℩` 投影，不是库的集合运算。在外部，环境层级有它自己的后继，以及由此造出的数码链。两条链理应一致，可迄今没有任何东西说它们一致：一条由可缩中心构成，另一条由构造子构成。所以本章真正的内容是一族**投影等式**，说的是模型的运算沿底层集合读出来就是层级的运算。有了它们，两条链逐步重合，而模型 record 向数码链要求的两条方程，也就沿着它们由层级自己的事实推得。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
module L.Axioms.Numerals {ℓ : Level} where

open import FOL.ZFStructure using ( module hPropStructure )
import FOL.ZFModel
open import V.Model {ℓ} using ( pair-singleton; module NumPin )
open import L.Constructible {ℓ} using ( 𝒮ʟ )
open import L.Axioms.Basic {ℓ}
  using ( hasPairL; hasUnionL; module PairOf; module UnionOf; isL-directed; ∅ʟ )

import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.HITs.CumulativeHierarchy.Base using ( setIsSet )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ⁅_,_⁆; ⋃_; module InfinitySet )
open InfinitySet using ( sucV; #_ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ

module ModelL = FOL.ZFModel 𝒮ʟ
open ModelL using ( SetOf; ℩ )
```

<!--en-->
## The model's own operations
<!--zh-->
## 模型自己的运算
<!--ja-->
## モデル自身の演算
<!--/-->

<!--en-->
The definite-description operator extracts canonical empty-set, pairing, and
union operations from their unique-existence proofs and defines the model's
successor from them.
<!--zh-->
摹状词算子从唯一存在证明中抽取典范的空集、配对与并运算，并据此定义模型自身的后继。
<!--ja-->
確定記述の演算子が一意存在の証明から正準的な空集合、対、和集合の演算を取り出し、それらからモデル自身の後者を定義する。
<!--/-->

<!--en-->
Unique existence hands over an operation: the description operator takes the
contractibility proof to its centre. Pairing and union become functions on the
constructible sets, and the successor is written the way the model record writes
it, as the union of a pair of pairs.
<!--zh-->
唯一存在交出一个运算：摹状词算子把可缩性证明送到它的中心。配对与并成为可构造集上的函数，而后继就按模型 record 的写法写出，即一对之对的并。
<!--/-->

<!--en-->
The chain is **sealed**, and the seal is not mere tidiness. Everything below
reads these through their projection equations and nothing reads them through
their construction, so sealing is free here; it is what makes one module
application elsewhere feasible. Instantiating the coding chapter at this model
rather than at the hierarchy means every code is an element of `L` by
construction, and the coding chapter proves its shape lemma by twelve `refl`s,
each of which forces whatever a pair unfolds to through normalization. Unsealed,
that application **does not finish in ten minutes**; sealed, it takes about a
third of a second.

The rule is the development's own, at a scale it had not been seen at: a
constructibility certificate is expensive to carry through conversion, so seal
it where the element is built. What is new is that a *module application* is a
conversion site too, and a large one, since it re-elaborates every definition in
the chapter being applied.
<!--zh-->
这条链是**封住的**，而这道封印不是为了整洁。下面的一切都经诸投影等式读它们，没有谁经它们的构造去读，故封印在此处不花分文；它买到的是别处的一次模块实例化。把编码那一章实例化到这个模型上、而非实例化到层级上，意味着每个码按构造就是 `L` 的元素；而编码那一章用十二个 `refl` 证它的形状引理，每一个都会把「一个对展开成什么」推进归一化。不封，那次实例化**十分钟跑不完**；封了，它耗时约三分之一秒。

本书一贯在元素构造处封印其可构造性证书，以免转换检查反复展开证书；这里同一原则首次作用于更大的规模。新增的观察是：**模块实例化也会触发转换检查**，而且代价很高，因为实例化会重新推导该模块中每个定义。
<!--/-->

```agda
opaque
  pairʟ : S → S → S
  pairʟ a b = ℩ (hasPairL a b)

  unionʟ : S → S
  unionʟ a = ℩ (hasUnionL a)

  sucʟ : S → S
  sucʟ a = unionʟ (pairʟ a (pairʟ a a))
```

<!--en-->
## Projection equations
<!--zh-->
## 投影等式
<!--ja-->
## 射影方程式
<!--/-->

<!--en-->
Contractibility identifies the extracted operations with the ambient hierarchy's
empty set, unordered pair, and union, yielding projection equations for the
internal successor.
<!--zh-->
可缩性把抽取出的运算与环境层级中的空集、无序对及并对应起来，从而给出内部后继的投影等式。
<!--ja-->
可縮性により取り出した演算を周囲の階層の空集合、非順序対、和集合と同一視し、内部の後者について射影方程式を得る。
<!--/-->

<!--en-->
Now the mismatch. The centre of a contractibility proof is not, on the face of
it, the set the hierarchy would have built: the proof went through a merely
existing witness, so nothing computes. But contractibility says more than
existence, it says every witness *is* the centre; and the previous chapter's
construction, applied to any stage that works, is a witness. So the two agree.
The truncation is harmless because the goal is an equation between sets, and the
hierarchy's carrier is a set.
<!--zh-->
现在处理那处错位。可缩性证明的中心，表面上并不是层级会造出的那个集合：证明经过了一个仅仅存在的见证，故什么也算不出来。但可缩性说的比存在更多，它说**每个**见证都等于中心；而上一章的构造，施于任何合用的阶段，正是一个见证。于是二者一致。截断在此无害，因为目标是集合之间的等式，而层级的载体是集合。
<!--/-->

```agda
  pairʟ-fst : (a b : S) → fst (pairʟ a b) ≡ ⁅ fst a , fst b ⁆
  pairʟ-fst a b = PT.rec (setIsSet (fst (pairʟ a b)) ⁅ fst a , fst b ⁆)
    (λ { (σ , (oσ , (fa∈ , fb∈))) →
         cong (λ (e : SetOf (PairOf.Q a b)) → fst (fst e))
           (hasPairL a b .snd (PairOf.mkPair a b σ oσ fa∈ fb∈)) })
    (isL-directed (fst a) (fst b) (a .snd) (b .snd))

  unionʟ-fst : (a : S) → fst (unionʟ a) ≡ ⋃ (fst a)
  unionʟ-fst a = PT.rec (setIsSet (fst (unionʟ a)) (⋃ (fst a)))
    (λ { (σ , (oσ , fa∈)) →
         cong (λ (e : SetOf (UnionOf.Q a)) → fst (fst e))
           (hasUnionL a .snd (UnionOf.mkUnion a σ oσ fa∈)) })
    (a .snd)
```

<!--en-->
The successor equation is the three of them composed, plus the hierarchy's own
identification of `{a, a}` with `{a}`: unfold the outer union, then the outer
pair, then the inner pair, then collapse the doubled singleton, and what is left
is the hierarchy's successor.
<!--zh-->
后继的等式就是这三条复合，再加上层级对 `{a, a}` 与 `{a}` 的认同：先展开外层的并，再展开外层的对，再展开内层的对，最后消去重复的单点集，剩下的就是层级的后继。
<!--/-->

```agda
  sucʟ-fst : (a : S) → fst (sucʟ a) ≡ sucV (fst a)
  sucʟ-fst a =
      unionʟ-fst (pairʟ a (pairʟ a a))
    ∙ cong ⋃_ (pairʟ-fst a (pairʟ a a))
    ∙ cong (λ w → ⋃ ⁅ fst a , w ⁆) (pairʟ-fst a a)
    ∙ cong (λ w → ⋃ ⁅ fst a , w ⁆) (pair-singleton (fst a))
```

<!--en-->
## The chain
<!--zh-->
## 链
<!--ja-->
## 数項列の構成
<!--/-->

<!--en-->
Primitive recursion defines `numeralL`{.Agda} from internal zero and successor,
and induction proves `numeralL-fst`{.Agda}, its equality with the ambient numeral.
<!--zh-->
原始递归从内部零与后继定义 `numeralL`{.Agda}，归纳则证明 `numeralL-fst`{.Agda}，即它与环境数码相等。
<!--ja-->
原始再帰により内部の零と後者から `numeralL`{.Agda} を定義し、帰納法で周囲の数項との等しさ `numeralL-fst`{.Agda} を証明する。
<!--/-->

<!--en-->
The chain is now written by ordinary recursion on a natural number, and one
induction says it projects onto the hierarchy's numerals. Zero is the empty set
built in the previous chapter, whose projection is the empty set on the nose.
<!--zh-->
链现在可以沿自然数用普通递归写出，而一次归纳即说明它投影到层级的数码上。零就是上一章造出的空集，其投影严格就是空集。
<!--/-->

```agda
  numeralL : ℕ → S
  numeralL zero    = ∅ʟ
  numeralL (suc n) = sucʟ (numeralL n)

  numeralL-fst : (n : ℕ) → fst (numeralL n) ≡ # n
  numeralL-fst zero    = refl
  numeralL-fst (suc n) = sucʟ-fst (numeralL n) ∙ cong sucV (numeralL-fst n)
```

<!--en-->
## The two pinning equations
<!--zh-->
## 两条成员方程
<!--ja-->
## 二つの指定方程式
<!--/-->

<!--en-->
`numeralL-zero`{.Agda} proves that internal zero has no members, while
`numeralL-suc`{.Agda} characterizes the next numeral as the preceding members
together with its predecessor.
<!--zh-->
`numeralL-zero`{.Agda} 证明内部零没有成员，而 `numeralL-suc`{.Agda} 刻画下一数码的成员恰为前一数码的成员及前一数码自身。
<!--ja-->
`numeralL-zero`{.Agda} は内部の零に要素がないことを示し、`numeralL-suc`{.Agda} は次の数項の要素が直前の数項の要素とその数項自身からなることを特徴づける。
<!--/-->

<!--en-->
The model record does not take the chain on trust: it demands that zero be
empty and that each successor have exactly the members of its predecessor
together with the predecessor itself, both stated through membership rather than
through the derived operations. That phrasing is deliberate, and it is what makes
these two proofs cheap: each is a fact about the hierarchy's numerals,
transported along the projection equation. Nothing here ever unfolds a
description operator.
<!--zh-->
模型 record 不肯轻信这条链：它要求零为空，且每个后继的成员恰是前者的成员连同前者自身，两条都经隶属陈述，而非经派生运算。这个措辞是有意的，也正是这两个证明廉价的原因：每一条都是关于层级数码的事实，沿投影等式搬运过来。全程从不展开摹状词算子。
<!--/-->

```agda
numeralL-zero : (z : S) → ⟨ z ∈ˢ numeralL zero ⟩ → Empty.⊥
numeralL-zero z = NumPin.pinZero (λ k → fst (numeralL k)) numeralL-fst (fst z)

numeralL-suc : (n : ℕ) (z : S)
             → (⟨ z ∈ˢ numeralL (suc n) ⟩
                  → ⟨ (z ∈ˢ numeralL n) ⊔ (z ≈ˢ numeralL n) ⟩)
             × (⟨ (z ∈ˢ numeralL n) ⊔ (z ≈ˢ numeralL n) ⟩
                  → ⟨ z ∈ˢ numeralL (suc n) ⟩)
numeralL-suc n z = NumPin.pinSuc (λ k → fst (numeralL k)) numeralL-fst n (fst z)
```

<!--en-->
## Recap
<!--zh-->
## 小结
<!--ja-->
## まとめ
<!--/-->

<!--en-->
`numeralL`{.Agda} is a constructive internal copy of the von Neumann numerals,
with the exact zero and successor membership laws required by the model record.
<!--zh-->
`numeralL`{.Agda} 是冯·诺伊曼数码的构造性内部副本，并满足模型 record 所需的精确零与后继成员律。
<!--ja-->
`numeralL`{.Agda} はフォン・ノイマン数項の構成的な内部コピーであり、モデルの record が要求する零と後者の正確な所属法則を満たす。
<!--/-->

<!--en-->
`numeralL`{.Agda} is the chain inside `L`, with `numeralL-fst`{.Agda} identifying
it with the hierarchy's own numerals, and `numeralL-zero`{.Agda} and
`numeralL-suc`{.Agda} the two equations the model record demands of it. All of it
is constructive, which is why it is a chapter of its own: the excluded middle
enters infinity only at the collection step, and that step is the next chapter.

The projection equations are reusable beyond the numerals. Anything built from
the model's pairing and union reads, through the underlying set, as the same
thing built from the hierarchy's, and a later chapter needing a numeral as a
constant of the object language takes its constructibility from here rather than
from the axiom.
<!--zh-->
`numeralL`{.Agda} 是 `L` 之内的那条链，`numeralL-fst`{.Agda} 把它与层级自己的数码认同起来，而 `numeralL-zero`{.Agda} 与 `numeralL-suc`{.Agda} 是模型 record 向它索取的两条方程。这一切都是构造性的，这正是它自成一章的理由：排中律只在收集那一步进入无穷公理，而那一步是下一章。

那些投影等式的用处不止于数码。凡由模型的配对与并造出的东西，沿底层集合读出来，就是由层级的配对与并造出的同一个东西；而日后某章若要把一个数码用作对象语言的常元，它的可构造性取自此处，而非取自公理。
<!--/-->
