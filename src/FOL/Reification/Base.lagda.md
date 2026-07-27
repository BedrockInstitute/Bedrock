# Representation

<!--en-->
The reification framework opens here, catalogued ahead of demand: nothing in the
trunk consumes it yet, and its hour comes with the deeper chapters of Part 4,
where formulas for separation and replacement get mass-produced. The model
chapter's confession stands as its charter: building a formula by hand,
correctness proof included, was tolerable exactly once. On one side stand host
predicates, `S ^ n → Ω`: the language in which this book actually states
mathematics. On the other side stand formulas: the currency the axiom fields
insist on. A **representation** is the bridge: a formula bundled with the proof
that it means a given predicate. Manufacturing such bundles is the activity this
framework is named after, *reification*; the next chapter sets up its assembly
line, and this chapter fixes the notion itself.
<!--zh-->
reification 框架在此开篇，预先备案，候单开工：主干至今没有消费它，它的时辰随第四部的深层章节到来，届时分离与替换所需的公式将被批量生产。模型章那句坦白是它的立厂章程：手工造一条公式、附带正确性证明，忍一次尚可。桥的一头是宿主谓词 `S ^ n → Ω`：本书实际陈述数学所用的语言。另一头是公式：公理字段只认的通货。**表示**就是这座桥：一条公式，捆绑着「它的含义恰是给定谓词」的证明。制造这种捆绑正是本框架得名的营生，即 reification；下一章为它架设流水线，本章先把概念本身立好。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import FOL.ZFStructure using ( ZFStructure )

module FOL.Reification.Base {ℓ ℓ'} (𝕋 : TruthAlgebra ℓ ℓ') (𝒮 : ZFStructure 𝕋)
                            {ℓc} (K : Type ℓc) (ι : K → ZFStructure.S 𝒮) where

open import FOL.Syntax using ( Term; Formula )
open import FOL.Semantics 𝕋 𝒮 using ( module At; _^_ )
open At K ι using ( _⊨_; ⟦_⟧ )

open TruthAlgebra 𝕋
open ZFStructure 𝒮
```

<!--en-->
## The notion
<!--zh-->
## 概念
<!--/-->

<!--en-->
A representation is an honest mathematical object, an ordered pair:

> **representation = a formula, paired with its adequacy certificate.**

**Adequacy** is pointwise semantic equality: under every environment, the truth
value the formula activates to equals the predicate's value. Crucially it is a
**path** in `Ω`, not a bi-implication: one can `subst`{.Agda} along it, rewriting
the predicate into the formula's meaning in any context whatsoever. And the
represented thing is a **family**, indexed by environments, rather than a single
object: compositional construction walks under quantifiers, where free variables
accumulate, so "with `n` holes" is the concept itself, not a generalisation of it.

Two variants, by the type of the represented thing: `RepP`{.Agda} represents
predicates by formulas, `RepS`{.Agda} represents set-valued families by terms.
<!--zh-->
表示是一个诚实的数学对象，一个有序对：

> **表示 = 一条公式，配上它的适足性证书。**

**适足性**指逐环境的语义相等：在每张赋值表下，公式激活出的真值恰等于谓词的取值。要紧的是，它是 `Ω` 中的**路径**而非双向蕴含：可以沿它 `subst`{.Agda}，在任何语境中把谓词改写为公式的含义。而被表示者是按环境索引的**族**，不是单个对象：组合式构造要走到量词底下，自由变量随之累积，所以「带 `n` 个洞」就是概念本体，而非它的推广。

按被表示者的类型分两个变体：`RepP`{.Agda} 以公式表示谓词，`RepS`{.Agda} 以词项表示集合值的族。
<!--/-->

```agda
RepP : (n : ℕ) → (S ^ n → Ω) → Type (ℓ-max ℓc (ℓ-max ℓ ℓ'))
RepP n P = Σ[ φ ∈ Formula K n ] (∀ γ → (γ ⊨ φ) ≡ P γ)

RepS : (n : ℕ) → (S ^ n → S) → Type (ℓ-max ℓc ℓ)
RepS n a = Σ[ t ∈ Term K n ] (∀ γ → ⟦ t ⟧ γ ≡ a γ)
```

<!--en-->
An inhabitant of `RepP n P`{.Agda} is exactly "`P` is definable, definition in
hand". Such inhabitants are circulating assets: the certificate leaves the factory
attached to the formula, is machine-checked, and can be handed on and composed;
the next chapter's combinators are precisely the algebra of these assets.
<!--zh-->
`RepP n P`{.Agda} 的居民恰是「`P` 可定义，且定义在手」。这些居民是流通的资产：证书随公式出厂、经机器检查、可转手可复合；下一章的组合子正是这些资产的代数。
<!--/-->

<!--en-->
## The two projections
<!--zh-->
## 两个投影
<!--/-->

<!--en-->
The only exit from an asset to its formula is the first projection, and to its
certificate the second; they get the names their roles deserve. Everything built on
this framework delivers results through `translate`{.Agda}, never by touching
`Formula`{.Agda} constructors directly: the sole doorway keeps the whole
development decoupled from the syntax it produces.
<!--zh-->
从资产取出公式的唯一出口是第一投影，取出证书的是第二投影；两者按角色得名。此框架之上构建的一切都经 `translate`{.Agda} 交付结果，从不直接触碰 `Formula`{.Agda} 的构造子：这扇唯一的门让整个开发与它所产出的语法保持解耦。
<!--/-->

```agda
translate : ∀ {n} {P : S ^ n → Ω} → RepP n P → Formula K n
translate = fst

adequacy : ∀ {n} {P : S ^ n → Ω} (r : RepP n P) → ∀ γ → (γ ⊨ translate r) ≡ P γ
adequacy = snd
```

<!--en-->
## Changing what a representation is said to represent
<!--zh-->
## 改说一个表示表示什么
<!--/-->

<!--en-->
An assembly line composes representations of the predicates its parts happen to
have, and what comes off the end is a representation of the *raw unfolding* of
those parts: nested truncated sums, one layer per bounded quantifier. That is
rarely the predicate anyone wants to read. The reader written by hand states
something like "this set is the ordered pair of those two", and a proof that the
unfolding equals that statement is the reader's own content, which no framework
supplies.

So the two are joined here. Given such a proof, a representation of one predicate
is a representation of the other, and the formula is untouched: only the
certificate changes, by composing with the given path. That the formula is
untouched is what makes this safe to use everywhere. `translate`{.Agda} of the
retargeted asset reduces to `translate`{.Agda} of the original, so anything that
recognised the old formula by its shape still does.

The last export names a representation's predicate. It is the identity on data
and exists only so that a statement can say "the meaning of this asset" without
writing the meaning out again.
<!--zh-->
一条流水线组合的是「其零件恰好具有的谓词」的表示，而从末端出来的，是那些零件**原始展开**的表示：层层嵌套的截断和，每个有界量词一层。那很少是谁想读的谓词。手写的读式陈述的是「这个集合是那两个的有序对」之类的话，而「展开等于那句话」的证明正是该读式自己的内容，任何框架都不供给它。

于是两者在此接上。给定那样一个证明，一个谓词的表示便是另一个谓词的表示，而公式分毫未动：只有证书变了，办法是与给定的道路复合。公式分毫未动，正是这件事到处可用而无害的原因。改标后资产的 `translate`{.Agda} 规约到原资产的 `translate`{.Agda}，故凡按形状认出旧公式的东西，如今照样认得。

最后一个出口为一个表示的谓词命名。它在数据上是恒等，存在的唯一理由是让某个陈述能说「这份资产的含义」，而不必把那个含义再写一遍。
<!--/-->

```agda
retarget : ∀ {n} {P Q : S ^ n → Ω} → (∀ γ → P γ ≡ Q γ) → RepP n P → RepP n Q
retarget e (φ , a) = φ , λ γ → a γ ∙ e γ

predOf : ∀ {n} {P : S ^ n → Ω} → RepP n P → (S ^ n → Ω)
predOf {P = P} _ = P
```

<!--en-->
## Recap
<!--zh-->
## 小结
<!--/-->

<!--en-->
A representation is a formula with its adequacy certificate, adequacy is a path,
and the represented things are environment-indexed families; `translate`{.Agda} and
`adequacy`{.Agda} are the only exits, with `retarget`{.Agda} the join between what
an assembly line produces and what a reader wants stated, and `predOf`{.Agda} a
name for a representation's meaning. Nothing has been built yet: the assembly
line opens next.
<!--zh-->
表示是公式配适足性证书，适足性是路径，被表示者是按环境索引的族；`translate`{.Agda} 与 `adequacy`{.Agda} 是仅有的出口，而 `retarget`{.Agda} 是「流水线产出什么」与「读式想陈述什么」之间的接缝，`predOf`{.Agda} 则为一个表示的含义命名。到此还什么都没造：流水线下一章开张。
<!--/-->
