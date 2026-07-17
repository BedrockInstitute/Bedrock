# Representation

<!--en-->
The bridge announced two chapters ago gets built here. On one side stand host
predicates, `S ^ n → Ω`: the language in which this book actually states
mathematics. On the other side stand formulas, which Part 2's separation and
replacement will insist on. A **representation** is the bridge: a formula bundled
with the proof that it means a given predicate. Manufacturing such bundles is the
activity this framework is named after, *reification*, and the next chapter sets up
its assembly line; this chapter fixes the notion itself.
<!--zh-->
两章之前预告的桥在此动工。桥的一头是宿主谓词 `S ^ n → Ω`：本书实际陈述数学所用的语言。另一头是公式：第二部的分离与替换只认它。**表示**就是这座桥：一条公式，捆绑着「它的含义恰是给定谓词」的证明。制造这种捆绑正是本框架得名的营生，即 reification；下一章为它架设流水线，本章先把概念本身立好。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import FOL.Structure using ( ZFStructure; _^_ )

module FOL.Reification.Base {ℓ ℓ'} (𝕋 : TruthAlg ℓ ℓ') (𝒮 : ZFStructure 𝕋)
                            {ℓc} (K : Type ℓc) (ι : K → ZFStructure.S 𝒮) where

open import FOL.Syntax using ( Term; Formula )
open import FOL.Semantics 𝕋 𝒮 using ( module At )
open At ι using ( _⊨_; ⟦_⟧ )

open TruthAlg 𝕋
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
## Recap
<!--zh-->
## 小结
<!--/-->

<!--en-->
A representation is a formula with its adequacy certificate, adequacy is a path,
and the represented things are environment-indexed families; `translate`{.Agda} and
`adequacy`{.Agda} are the only exits. Nothing has been built yet: the factory
opens next.
<!--zh-->
表示是公式配适足性证书，适足性是路径，被表示者是按环境索引的族；`translate`{.Agda} 与 `adequacy`{.Agda} 是仅有的出口。到此还什么都没造：工厂下一章开张。
<!--/-->
