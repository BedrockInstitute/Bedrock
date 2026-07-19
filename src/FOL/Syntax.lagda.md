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

Two design decisions are visible in the constructor list. First, **every
connective is a primitive**, and the reason is the semantics this language is
headed for: each constructor will mean exactly one truth-algebra operation, and
the algebra is constructive. A classical text can economize, spelling
`φ ∨ ψ` as `¬ (¬ φ ∧ ¬ ψ)`, `∀` as `¬ ∃ ¬`, `φ ⇒ ψ` as `¬ φ ∨ ψ`, because
classically the double negations cancel. Constructively they do not: `¬ ¬ P`
is weaker than `P`, so every one of those spellings would assign the connective
the **wrong meaning**. `∨`, `∀`, `⇒` therefore must be constructors. The
remaining three (`⊤̇`, `⊥̇`, `¬̇`) *could* be spelled honestly, say `¬̇ φ` as
`φ ⇒̇ ⊥̇`; they are primitive anyway so that every later structural recursion
treats every connective alike, one clause each, no encoded special cases.

Second, the bounded quantifiers earn primitive seats even though `∀̇∈ t φ`
could be spelled with `∀̇`. Had they been abbreviations, "every quantifier in
`φ` is bounded" would be a fact about how `φ` happens to be spelled, invisible
to anything that computes over `φ`'s shape. As constructors, boundedness is
shape: later chapters classify formulas by a datatype over their constructors,
and certify "all quantifiers bounded" by a datatype that simply has **no case**
for `∃̇` and `∀̇`, an absence that can only speak if the bounded forms stand on
their own. Formulas of that shape behave remarkably tamely across structures,
a thread picked up once Part 2's model is on the table and carried into
Part 4. The fixity table here is the book's single declaration for the object
layer, each level chosen to match the truth-algebra operation it will be
interpreted by.
<!--zh-->
公式随后，以同样的方式索引。对象语言的每个构造子都带一个**上点**：这是一枚层标记，见点即知这个符号是语法而非含义。读法：`∈̇` 是对象成员，`≐` 是对象等词，`∧̇ ∨̇ ⇒̇ ¬̇ ⊤̇ ⊥̇` 是联结词，`∃̇ ∀̇` 是量词，`∀̇∈`、`∃̇∈` 是**有界**量词，读作「对……的每个成员」与「对……的某个成员」。约束采用 de Bruijn 方式：量词所取的公式体多出一个自由变量，变量 `0` 即刚被约束的那个。

构造子清单里可以看出两个设计决定。其一，**联结词全部是原语**，理由在这门语言即将奔赴的语义：每个构造子将恰好意指一个真值代数运算，而该代数是构造性的。经典教科书可以省笔墨，把 `φ ∨ ψ` 拼作 `¬ (¬ φ ∧ ¬ ψ)`、`∀` 拼作 `¬ ∃ ¬`、`φ ⇒ ψ` 拼作 `¬ φ ∨ ψ`，因为经典地看双重否定会互相抵消。构造性地看它们不抵消：`¬ ¬ P` 严格弱于 `P`，上述每一种拼写都会给联结词指派**错误的含义**。所以 `∨`、`∀`、`⇒` 必须是构造子。剩下三个 (`⊤̇`、`⊥̇`、`¬̇`) 本来**可以**诚实地拼出，例如 `¬̇ φ` 拼作 `φ ⇒̇ ⊥̇`；仍将它们原语化，是为了让后续每一次结构递归对所有联结词一视同仁，一子句一条，不留任何需要特判的编码。

其二，有界量词虽然可用 `∀̇` 拼写，仍占有原语席位。倘若它们只是缩写，「`φ` 的每个量词都有界」就成了关于 `φ` **恰巧如何拼写**的事实，任何在 `φ` 的形状上计算的东西都看不见它。作为构造子，有界性就是形状：后面的章节按构造子给公式分类，用一个对 `∃̇` 与 `∀̇` **不设情形**的归纳数据来证明「量词皆有界」，而这种缺席要能开口说话，有界形式必须自立门户。这种形状的公式在不同结构之间表现格外驯良，这条线索将在第二部的模型落定后重新拾起并延伸进第四部。此处的 fixity 表是对象层在全书的唯一一次集中声明，各级刻意与它将被解释成的真值代数运算对齐。
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
| `⊥*`{.Agda} (no constants) | the **parameter-free formulas**: countable and codable, where theories and codes will live |
| a restricted carrier | parameters confined to a class; the shape Part 4 builds `L` with |
<!--zh-->
参数 `K` 让一族语法覆盖全书的所有用途：

| `K` 的取法 | 得到什么 |
|---|---|
| 某结构的载体 | 日常工作语法：任何集合都能以参数身份出现在公式里 |
| `⊥*`{.Agda} (无常量) | **无参公式**：可数、可编码，理论与码的居所 |
| 受限制的载体 | 参数只许来自某个类；第四部构造 `L` 用的正是这个形状 |
<!--/-->

<!--en-->
## Sentences and parameter-free formulas
<!--zh-->
## 句子与无参公式
<!--/-->

<!--en-->
A **sentence** is a formula with no free variables; with intrinsic scoping this is
a type, `Formula K 0`, not a side condition, and the book gives it no separate
name. **Parameter-free formulas** restrict
along a different, orthogonal axis. A constant is how an ambient set enters a
formula as a parameter; here the constant domain is the empty type `⊥*`{.Agda}, so
there are no parameters at all, while free variables remain; like sentences,
this is just a type, `Formula ⊥* n`, with no separate name. From the empty
type anything follows, so a parameter-free formula can enter the syntax over
any domain whatsoever; the map that performs the entry lives with the
constant-transformation kit at the book's tail. Parameter-free formulas are no rivals of the working
syntax but its companions: a syntax whose constants are all sets is too big to be
counted or coded, so whenever a later part needs formulas *as data*, theories as
sets of formulas, codes of formulas inside a model, it is the parameter-free
formulas that get collected, their parameters fed through environments instead.
<!--zh-->
**句子**是没有自由变量的公式；作用域既然内蕴，这是一个类型 `Formula K 0`，而非附加条件，本书不为它另设名字。**无参公式**限制的是另一条正交的轴。常量是外部集合以参数身份进入公式的通道；这里常量域取空类型 `⊥*`{.Agda}，参数于是全然没有，而自由变量照旧；与句子一样，这只是一个类型 `Formula ⊥* n`，本书不为它另设名字。从空类型可以推出一切，所以无参公式可以进入任意常量域上的语法；执行这次进入的映射编在书末的常量变换章里。无参公式不是工作语法的对手，而是它的同伴：常量囊括一切集合的语法太大，数不得也编不得码，因此后面各部凡需要把公式**当数据**用，理论作为公式的集合、模型内部的公式码，收集的都是无参公式，参数改经环境喂入。
<!--/-->

<!--en-->
## Recap
<!--zh-->
## 小结
<!--/-->

<!--en-->
The object language is an inductive family `Formula K n`{.Agda}: constant domain as
a parameter, scoping intrinsic through `Fin`{.Agda}, every constructor primitive
and dotted. Around it: the parameter-free
formulas, the data axis whose entry map arrives with the relabelling kit at the
book's tail. Note what is absent: no substitution and no weakening operators
anywhere. The design will keep
it that way, and the little variable machinery the book does need arrives later in
the book. First, formulas need something to talk about.
<!--zh-->
对象语言是归纳族 `Formula K n`{.Agda}：常量域作参数，作用域经 `Fin`{.Agda} 内蕴，构造子全原语、全带点。围绕它的：无参公式，这条数据轴的进入映射随书末的常量变换工具组到来。留意缺席者：全篇没有替换算子、没有弱化算子。这个设计将一直保持下去，本书仅需的那一点变量机件在本书稍后登场。眼下，公式先得有可谈论的对象。
<!--/-->
