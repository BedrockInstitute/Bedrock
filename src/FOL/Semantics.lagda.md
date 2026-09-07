<!--en-->
# Semantics

A formula receives meaning only after choosing a truth algebra, a set-theoretic structure, and an interpretation of its constants. This chapter defines term evaluation and formula satisfaction under an environment, then proves the basic laws for changing environments and constant interpretations.
<!--zh-->
# 语义

一条公式只有在选定真值代数、集合论结构与常元解释之后才获得含义。本章定义环境下的词项求值与公式满足关系，再证明改变环境和常元解释时的基本规律。
<!--ja-->
# 意味論

論理式は、真理値代数、集合論的構造、定数の解釈を選んで初めて意味を持ちます。本章では環境のもとでの項の評価と論理式の充足関係を定義し、環境や定数解釈を変えるときの基本法則を証明します。
<!--/-->

<!--en-->
Three things turn syntax into meaning: a structure `𝒮` to be talked about, an
interpretation of the constants, and an environment giving values to the free
variables. The first is a parameter of this whole chapter, along with the truth
algebra it is valued in; the generic development speaks through the abstract `𝕋`,
as the scope discipline prescribes.
<!--zh-->
把语法变成含义需要三样东西：被谈论的结构 `𝒮`、常元的解释，以及给自由变量赋值的环境。第一样连同它取值的真值代数是本章整体的参数；泛型开发按作用域纪律的安排，经抽象的 `𝕋` 说话。
<!--/-->



```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import FOL.ZFStructure using ( ZFStructure )

module FOL.Semantics {ℓ ℓ'} (𝕋 : TruthAlgebra ℓ ℓ') (𝒮 : ZFStructure 𝕋) where

open import FOL.Syntax using
  ( Term; con; var
  ; Formula; _∈̇_; _≐_; _∧̇_; _∨̇_; _⇒̇_; ⊥̇; ∃̇_; ∀̇_; ∀̇∈; ∃̇∈ )

open TruthAlgebra 𝕋
open ZFStructure 𝒮
```

<!--en-->
## Environments

One piece of kit first. To evaluate a formula
with `n` free variables, each variable needs a value from the carrier: an
**assignment**, or environment, written `γ` throughout the book. The book's
notation for its type is `S ^ n`{.Agda}, a vector of length `n`, matching the
traditional superscript $S^n$ (`_^_`{.Agda} reads "power"); it is nothing but
notation.
<!--zh-->
## 环境

先备一件行头。要对带 `n` 个自由变量的公式求值，每个变量都需要一个来自载体的取值：一份**赋值表**，即环境，全书写作 `γ`。其类型记为 `S ^ n`{.Agda}，长度为 `n` 的向量，对齐传统上标记号 $S^n$ (`_^_`{.Agda} 读作「幂」)；它只是记号。
<!--ja-->
## 環境

自由変数が `n` 個ある項や論理式の環境は、構造の台の要素を並べた長さ `n` のベクトルです。`A ^ n`{.Agda} という記法により、変数の個数と環境の長さが型で一致します。
<!--/-->



```agda
infixl 30 _^_

_^_ : ∀ {ℓ''} → Type ℓ'' → ℕ → Type ℓ''
A ^ n = Vec A n
```

<!--en-->
## Evaluation and satisfaction

The remaining ingredient, the constant interpretation `ι : K → S`, is fixed once by
an inner module `At`{.Agda}: everyday work happens under one fixed `ι` (the
canonical case takes the carrier itself as constant domain, with `ι` the identity),
while the occasional lemma that crosses interpretations, such as those at the end
of this chapter, uses qualified names.
<!--zh-->
## 求值与满足

剩下那样原料，常元解释 `ι : K → S`，由内部模块 `At`{.Agda} 一次固定：日常工作在一个固定的 `ι` 下进行 (典范情形以载体自身为常元域，`ι` 取恒等)，偶尔需要跨解释的引理，如本章末那几条，则以限定名访问。
<!--ja-->
## 評価と充足

定数解釈 `ι` と環境 `γ` のもとで、`⟦ t ⟧ γ`{.Agda} は項を集合に評価し、`γ ⊨ φ`{.Agda} は論理式を真理値代数の値に評価します。各構文子は対応する構造または論理演算として解釈されます。
<!--/-->



```agda
module At {ℓc} (K : Type ℓc) (ι : K → S) where
```

<!--en-->
Two readings, both straight from the textbook: `⟦_⟧`{.Agda} reads "the value of",
and `_⊨_`{.Agda} reads "satisfies", with the environment on the left, `γ ⊨ φ`.
Evaluation of a term either asks `ι` (a constant) or looks up the environment (a
variable). Satisfaction is a single structural recursion over the ten
constructors.
<!--zh-->
两个记号都直接来自教科书：`⟦_⟧`{.Agda} 读作「取值」，`_⊨_`{.Agda} 读作「满足」，环境在左，写 `γ ⊨ φ`。词项求值要么问 `ι` (常元)，要么查环境 (变量)。满足关系是对十个构造子的一次结构递归。
<!--/-->

```agda
  ⟦_⟧ : ∀ {n} → Term K n → S ^ n → S
  ⟦ con k ⟧ γ = ι k
  ⟦ var i ⟧ γ = lookup i γ

  infix 6 _⊨_

  _⊨_ : ∀ {n} → S ^ n → Formula K n → Ω
  γ ⊨ (t ∈̇ u)  = ⟦ t ⟧ γ ∈ˢ ⟦ u ⟧ γ
  γ ⊨ (t ≐ u)  = ⟦ t ⟧ γ ≈ˢ ⟦ u ⟧ γ
  γ ⊨ (φ ∧̇ ψ)  = (γ ⊨ φ) ⊓ (γ ⊨ ψ)
  γ ⊨ (φ ∨̇ ψ)  = (γ ⊨ φ) ⊔ (γ ⊨ ψ)
  γ ⊨ (φ ⇒̇ ψ)  = (γ ⊨ φ) ⇒ (γ ⊨ ψ)
  γ ⊨ ⊥̇        = ⊥
  γ ⊨ (∃̇ φ)    = ⋁ S (λ x → (x ∷ γ) ⊨ φ)
  γ ⊨ (∀̇ φ)    = ⋀ S (λ x → (x ∷ γ) ⊨ φ)
  γ ⊨ (∀̇∈ t φ) = ⋀ S (λ x → (x ∈ˢ ⟦ t ⟧ γ) ⇒ ((x ∷ γ) ⊨ φ))
  γ ⊨ (∃̇∈ t φ) = ⋁ S (λ x → (x ∈ˢ ⟦ t ⟧ γ) ⊓ ((x ∷ γ) ⊨ φ))
```

<!--en-->
Look at the right-hand sides: each primitive constructor uses the truth algebra's
corresponding operation, applied to the meanings of the subformulas. Object conjunction means
host conjunction, the object quantifiers mean `⋀` and `⋁` over the carrier; there
is no translation layer in between. A formula with `n` free variables thus means a
function `S ^ n → Ω`{.Agda}, deliberately the same shape as a **predicate** written
directly in the host language; a bridge between the two is catalogued at the
book's tail, and this faithfulness is what will make every plank of that bridge
a one-line congruence.

The two bounded clauses deserve a second look: their quantification is pinned to
the members of `⟦ t ⟧ γ`. The syntax chapter promised that formulas whose
quantifiers are all bounded behave tamely across structures; that behaviour lives
physically in these two lines, and later chapters return to them again and again.
<!--zh-->
看各子句的右端：每个原语构造子都采用真值代数的对应运算，作用在子公式的含义上。对象合取的含义就是宿主合取，对象量词的含义就是载体上的 `⋀` 与 `⋁`，中间没有任何翻译层。于是带 `n` 个自由变量的公式，含义是一个 `S ^ n → Ω`{.Agda} 型的函数，与宿主语言直接写出的**谓词**刻意同形；两者之间的桥编在书末，而这份忠实性将让那座桥的每一块板都归于一行同余。

两条有界子句值得再看一眼：它们的量化被钉在 `⟦ t ⟧ γ` 的成员上。语法章许诺过，全部量词皆有界的公式在结构之间表现驯良；那份驯良物理上就住在这两行里，后面的章节将一次次回到这里。
<!--/-->

<!--en-->
## Recap

Meaning is structural recursion: `⟦_⟧`{.Agda} evaluates terms, `γ ⊨ φ` lands in the
truth algebra, and each clause is the corresponding algebra operation, nothing
more. Formulas with `n` free variables mean functions `S ^ n → Ω`{.Agda}, the same
shape as host predicates. The
one bridge still missing between formulas and predicates is catalogued at the
book's tail, waiting for the day the demand turns industrial.
<!--zh-->
## 小结

含义就是结构递归：`⟦_⟧`{.Agda} 给词项取值，`γ ⊨ φ` 落进真值代数，每条子句恰是对应的代数运算，分毫不多。带 `n` 个自由变量的公式，含义是 `S ^ n → Ω`{.Agda} 型函数，与宿主谓词同形。公式与谓词之间尚缺一座桥；它编在书末，静候需求转入量产的那一天。
<!--ja-->
## まとめ

項の評価は集合を返し、論理式の充足は選ばれた真理値代数の値を返します。自由変数は環境から、定数は `ι` から読み取られるので、後の構文変換はこの二つに対する自然性として検証できます。
<!--/-->
