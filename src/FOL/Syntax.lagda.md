# The object language

<!--en-->
Part 1 begins. The host language has been speaking all along; this part builds the
language that will be **spoken about**: the first-order language of set theory, with
membership and equality as its only predicates, embedded deeply as an inductive
datatype. The host is strictly more expressive, so the embedded `Formula`{.Agda} is
never needed to *say* anything; it exists because later parts study formulas as
mathematical objects: count them, code them, and ask what is definable by them.
This chapter is pure syntax, owing nothing to truth values or structures.
<!--zh-->
第一部开篇。宿主语言从头到尾都在说话；本部要构造的是**被谈论**的语言：以成员与等词为仅有谓词的集合论一阶语言，作为归纳数据类型深嵌入。宿主的表达力严格更强，所以嵌入的 `Formula`{.Agda} 从不用来**说**什么；它存在，是因为后面各部要把公式当作数学对象来研究：数它们、编码它们、追问它们能定义什么。本章是纯语法，不欠真值与结构任何东西。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

module FOL.Syntax where

open import Base.Prelude
```

<!--en-->
## Terms and formulas
<!--zh-->
## 词项与公式
<!--/-->

<!--en-->
Some conventions first, used from here to the end of the book: `t`, `u` stand for
terms, `φ`, `ψ` for formulas, `n`, `m` for numbers of free variables, and `i`, `j`
for variables themselves. A term is either a **constant** or a **variable**. Which
constants exist is a type parameter `K`, the **constant domain**; a variable is an
element of `Fin n`{.Agda}, so a term with `n` free variables can only mention
variables `0` to `n - 1`. Scoping is thereby intrinsic: an out-of-scope term is not
forbidden, it is unrepresentable.
<!--zh-->
先立几个贯穿全书的变量约定：`t`、`u` 代表词项，`φ`、`ψ` 代表公式，`n`、`m` 代表自由变量个数，`i`、`j` 代表变量本身。词项要么是**常量**，要么是**变量**。允许哪些常量是一个类型参数 `K`，称为**常量域**；变量是 `Fin n`{.Agda} 的元素，于是带 `n` 个自由变量的词项只能提及变量 `0` 到 `n - 1`。作用域由此内蕴：越界的词项不是被禁止，而是不可表示。
<!--/-->

```agda
data Term {ℓ} (K : Type ℓ) (n : ℕ) : Type ℓ where
  con : K → Term K n         -- a constant, drawn from the domain K
  var : Fin n → Term K n     -- a de Bruijn variable
```

<!--en-->
Formulas follow, indexed the same way. Every constructor of the object language
carries an **upper dot**: a layer mark, and seeing it tells you at once that a
symbol is syntax, not meaning. Reading them:
`∈̇` is object membership, `≐` object equality, `∧̇ ∨̇ ⇒̇ ¬̇ ⊤̇ ⊥̇` the connectives,
`∃̇ ∀̇` the quantifiers, and `∀̇∈`, `∃̇∈` the **bounded** quantifiers, read "for every
member of" and "for some member of". Binding is by de Bruijn: a quantifier takes a
body with one more free variable, and variable `0` is the one just bound.

Two design decisions are visible in the constructor list. First, **every connective
is a primitive**. In a constructive metatheory `∀`, `∨`, `⇒` cannot be derived from
the others, and making the remaining ones (`⊤̇`, `⊥̇`, `¬̇`) primitive too lets the
next chapters treat every constructor uniformly, one clause each. Second, the
bounded quantifiers earn primitive seats even though `∀̇∈ t φ` could be spelled with
`∀̇`: formulas all of whose quantifiers are bounded behave remarkably tamely across
different structures, and that thread, picked up in the later chapters of this part
and carried into Part 4, wants the bounded forms as first-class syntax. The fixity
table here is the book's single declaration for the object layer, each level chosen
to match the truth-algebra operation it will be interpreted by.
<!--zh-->
公式随后，以同样的方式索引。对象语言的每个构造子都带一个**上点**：这是一枚层标记，见点即知这个符号是语法而非含义。读法：`∈̇` 是对象成员，`≐` 是对象等词，`∧̇ ∨̇ ⇒̇ ¬̇ ⊤̇ ⊥̇` 是联结词，`∃̇ ∀̇` 是量词，`∀̇∈`、`∃̇∈` 是**有界**量词，读作「对……的每个成员」与「对……的某个成员」。约束采用 de Bruijn 方式：量词取一个多一个自由变量的公式体，变量 `0` 即刚被约束的那个。

构造子清单里可以看出两个设计决定。其一，**联结词全部是原语**。在构造性元理论中，`∀`、`∨`、`⇒` 无法从其余联结词派生；把剩下的 (`⊤̇`、`⊥̇`、`¬̇`) 也原语化，则让后续各章对每个构造子一视同仁、一子句一条。其二，有界量词虽然可用 `∀̇` 拼写，仍占有原语席位：全部量词皆有界的公式，在不同结构之间的表现格外驯良，这条线索将贯穿本部后半并延伸进第四部，它需要有界形式作为一等语法。此处的 fixity 表是对象层在全书的唯一一次集中声明，各级刻意与它将被解释成的真值代数运算对齐。
<!--/-->

```agda
infix  18 _≐_ _∈̇_
infixr 12 _∧̇_ _∨̇_
infixr 10 _⇒̇_
infix  13 ¬̇_

data Formula {ℓ} (K : Type ℓ) (n : ℕ) : Type ℓ where
  _∈̇_ _≐_     : Term K n → Term K n → Formula K n        -- atoms: membership, equality
  _∧̇_ _∨̇_ _⇒̇_ : Formula K n → Formula K n → Formula K n  -- binary connectives
  ¬̇_          : Formula K n → Formula K n                -- negation
  ⊤̇ ⊥̇         : Formula K n                              -- truth, falsity
  ∃̇_ ∀̇_       : Formula K (suc n) → Formula K n          -- quantifiers
  ∀̇∈ ∃̇∈       : Term K n → Formula K (suc n) → Formula K n  -- bounded quantifiers
```

<!--en-->
The parameter `K` is where one syntax covers every use the book will make of it:

| choice of `K` | what it gives |
|---|---|
| the carrier of a structure | the working syntax: any set may appear in a formula as a parameter |
| `⊥*`{.Agda} (no constants) | the **closed syntax**: countable and codable, where theories and codes will live |
| a restricted carrier | parameters confined to a class; the shape Part 4 builds `L` with |
<!--zh-->
参数 `K` 让一族语法覆盖全书的所有用途：

| `K` 的取法 | 得到什么 |
|---|---|
| 某结构的载体 | 日常工作语法：任何集合都能以参数身份出现在公式里 |
| `⊥*`{.Agda} (无常量) | **封闭语法**：可数、可编码，理论与码的居所 |
| 受限制的载体 | 参数只许来自某个类；第四部构造 `L` 用的正是这个形状 |
<!--/-->

<!--en-->
## Relabelling constants
<!--zh-->
## 常量重标记
<!--/-->

<!--en-->
The syntax is functorial in its constant domain: a map `K → K'` pushes through a
term or formula, relabelling constants and touching nothing else. One clause per
constructor, each doing the obvious thing.
<!--zh-->
语法对常量域是函子式的：一个映射 `K → K'` 沿词项或公式推送，重标记常量，不碰其他任何东西。一构造子一子句，各做显然之事。
<!--/-->

```agda
mapTm : ∀ {ℓ ℓ'} {K : Type ℓ} {K' : Type ℓ'} {n}
      → (K → K') → Term K n → Term K' n
mapTm f (con k) = con (f k)
mapTm f (var i) = var i

mapFo : ∀ {ℓ ℓ'} {K : Type ℓ} {K' : Type ℓ'} {n}
      → (K → K') → Formula K n → Formula K' n
mapFo f (t ∈̇ u)  = mapTm f t ∈̇ mapTm f u
mapFo f (t ≐ u)  = mapTm f t ≐ mapTm f u
mapFo f (φ ∧̇ ψ)  = mapFo f φ ∧̇ mapFo f ψ
mapFo f (φ ∨̇ ψ)  = mapFo f φ ∨̇ mapFo f ψ
mapFo f (φ ⇒̇ ψ)  = mapFo f φ ⇒̇ mapFo f ψ
mapFo f (¬̇ φ)    = ¬̇ mapFo f φ
mapFo f ⊤̇        = ⊤̇
mapFo f ⊥̇        = ⊥̇
mapFo f (∃̇ φ)    = ∃̇ mapFo f φ
mapFo f (∀̇ φ)    = ∀̇ mapFo f φ
mapFo f (∀̇∈ t φ) = ∀̇∈ (mapTm f t) (mapFo f φ)
mapFo f (∃̇∈ t φ) = ∃̇∈ (mapTm f t) (mapFo f φ)
```

<!--en-->
## Sentences and the closed syntax
<!--zh-->
## 语句与封闭语法
<!--/-->

<!--en-->
A **sentence** is a formula with no free variables; with intrinsic scoping this is
a type, `Formula K 0`, not a side condition. The **closed syntax** additionally has
no constants: its domain is the empty type `⊥*`{.Agda}. From the empty type
anything follows, and `absurd`{.Agda} is that standard elimination; here it
interprets the constants that do not exist, embedding a closed formula into the
syntax over any constant domain whatsoever. The closed syntax is not a rival of the
working syntax but its companion: a syntax whose constants are all sets is too big
to be counted or coded, so whenever a later part needs formulas *as data*, theories
as sets of formulas, codes of formulas inside a model, it is `Closed`{.Agda}
formulas that get collected, with parameters fed through environments instead.
<!--zh-->
**语句**是没有自由变量的公式；作用域既然内蕴，这是一个类型 `Formula K 0`，而非附加条件。**封闭语法**更进一步连常量也没有：其常量域是空类型 `⊥*`{.Agda}。从空类型可以推出一切，`absurd`{.Agda} 就是这条标准消去；在这里它解释那些不存在的常量，把闭公式嵌入任意常量域上的语法。封闭语法不是工作语法的对手，而是它的同伴：常量囊括一切集合的语法太大，数不得也编不得码，因此后面各部凡需要把公式**当数据**用，理论作为公式的集合、模型内部的公式码，收集的都是 `Closed`{.Agda} 公式，参数改经环境喂入。
<!--/-->

```agda
absurd : ∀ {ℓ ℓ'} {A : Type ℓ'} → ⊥* {ℓ} → A
absurd (lift ())

Sentence : ∀ {ℓ} (K : Type ℓ) → Type ℓ
Sentence K = Formula K 0

Closed : ∀ {ℓ} → ℕ → Type ℓ
Closed {ℓ} = Formula (⊥* {ℓ})

embed : ∀ {ℓ ℓ'} {K : Type ℓ'} {n} → Closed {ℓ} n → Formula K n
embed = mapFo absurd
```

<!--en-->
## Recap
<!--zh-->
## 小结
<!--/-->

<!--en-->
The object language is an inductive family `Formula K n`{.Agda}: constant domain as
a parameter, scoping intrinsic through `Fin`{.Agda}, every constructor primitive
and dotted. Around it: functorial relabelling (`mapTm`{.Agda}, `mapFo`{.Agda}),
sentences as a type, and the closed syntax with its `embed`{.Agda}. Note what is
absent: no substitution and no weakening operators anywhere. The design will keep
it that way, and the little variable machinery the book does need arrives later in
this part. First, formulas need something to talk about.
<!--zh-->
对象语言是归纳族 `Formula K n`{.Agda}：常量域作参数，作用域经 `Fin`{.Agda} 内蕴，构造子全原语、全带点。围绕它的：函子式重标记 (`mapTm`{.Agda}、`mapFo`{.Agda})、类型化的语句，以及带 `embed`{.Agda} 的封闭语法。留意缺席者：全篇没有替换算子、没有弱化算子。这个设计将一直保持下去，本书仅需的那一点变量机件在本部稍后登场。眼下，公式先得有可谈论的对象。
<!--/-->
