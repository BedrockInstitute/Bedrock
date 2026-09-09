<!--en-->
# The object language

Set theory will be studied through a first-order object language with constants and de Bruijn variables. This chapter defines its terms and formulas, fixes the notation for membership, equality, connectives, and quantifiers, and distinguishes sentences from formulas that merely have no constants.
<!--zh-->
# 对象语言

本书用带常元与 de Bruijn 变量的一阶对象语言研究集合论。本章定义词项与公式，确定隶属、相等、联结词和量词的记号，并区分句子与仅仅不含常元的公式。
<!--ja-->
# 対象言語

本書では、定数と de Bruijn 変数を持つ一階の対象言語で集合論を調べます。本章では項と論理式を定義し、所属、等号、結合子、量化子の記法を定め、文と単に定数を持たない論理式を区別します。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

module FOL.Syntax where

open import Base.Prelude
```

<!--en-->
## Terms and formulas

A term is either a named constant or one of the `n` free variables. Formulas combine membership and equality atoms with logical connectives and both bounded and unbounded quantifiers.
<!--zh-->
## 词项与公式

词项是一个具名常元，或是 `n` 个自由变量之一。公式由隶属与相等原子式、逻辑联结词以及有界和无界量词组成。
<!--ja-->
## 項と論理式

項は名前を持つ定数か、`n` 個の自由変数の一つです。論理式は所属と等号の原子式を、論理結合子、有界量化子、非有界量化子で組み立てます。
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
先立几个贯穿全书的变量约定：`t`、`u` 代表词项，`φ`、`ψ` 代表公式，`n`、`m` 代表自由变量个数，`i`、`j` 代表变量本身。词项要么是**常元**，要么是**变量**。允许哪些常元是一个类型参数 `K`，称为**常元域**；变量是 `Fin n`{.Agda} 的元素，于是带 `n` 个自由变量的词项只能提及变量 `0` 到 `n - 1`。作用域由此内蕴：越界的词项不是被禁止，而是不可表示。
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

Two design decisions are visible in the constructor list. First, the binary
connectives are primitive, and the reason lies in the semantics this language is
headed for: each constructor will mean exactly one truth-algebra operation, and
the algebra is constructive. A classical text can economize, spelling
`φ ∨ ψ` as `¬ (¬ φ ∧ ¬ ψ)`, `∀` as `¬ ∃ ¬`, `φ ⇒ ψ` as `¬ φ ∨ ψ`, because
classically the double negations cancel. Constructively they do not: `¬ ¬ P`
is weaker than `P`, so every one of those spellings would assign the connective
the **wrong meaning**. `∨`, `∀`, `⇒` therefore must be constructors.
Negation and truth are defined by their meaning: `¬̇ φ` is `φ ⇒̇ ⊥̇`, and `⊤̇` is
`⊥̇ ⇒̇ ⊥̇`.

Second, the bounded quantifiers are primitive in their own right even though `∀̇∈ t φ`
could be spelled with `∀̇`. Had they been abbreviations, "every quantifier in
`φ` is bounded" would be a fact about how `φ` happens to be spelled, invisible
to anything that computes over `φ`'s shape. As constructors, boundedness is
part of the shape of a formula: later chapters classify formulas by a datatype
over their constructors, and certify "all quantifiers bounded" by a datatype
that simply has **no case** for `∃̇` and `∀̇`; expressing this absence
requires the bounded forms to be given independently. Formulas of that shape
behave well across structures, a thread taken up once the model chapters have
established their model and carried into the constructible-universe chapters.
The fixity table here is the book's single declaration for the object
layer, each level chosen to match the truth-algebra operation it will be
interpreted by.
<!--zh-->
公式随后，以同样的方式索引。对象语言的每个构造子都带一个**上点**：这个点就是语法层的标记，见到点即可知道符号指语法而非含义。读法：`∈̇` 是对象成员，`≐` 是对象等词，`∧̇ ∨̇ ⇒̇ ¬̇ ⊤̇ ⊥̇` 是联结词，`∃̇ ∀̇` 是量词，`∀̇∈`、`∃̇∈` 是**有界**量词，读作「对……的每个成员」与「对……的某个成员」。约束采用 de Bruijn 方式：量词所取的公式体多出一个自由变量，变量 `0` 即刚被约束的那个。

构造子清单体现两个设计决定。其一，二元联结词是原语，理由来自这门语言的语义：每个构造子恰好对应一个构造性真值代数运算。经典教科书可以把 `φ ∨ ψ` 写成 `¬ (¬ φ ∧ ¬ ψ)`、把 `∀` 写成 `¬ ∃ ¬`、把 `φ ⇒ ψ` 写成 `¬ φ ∨ ψ`，因为经典逻辑可以消去双重否定；构造逻辑中 `¬ ¬ P` 严格弱于 `P`，这些写法会赋予联结词错误的含义。因此，`∨`、`∀`、`⇒` 必须作为构造子。否定与真则按其含义定义：`¬̇ φ` 即 `φ ⇒̇ ⊥̇`，`⊤̇` 即 `⊥̇ ⇒̇ ⊥̇`。

其二，有界量词虽然可用 `∀̇` 拼写，仍单独作为原语。倘若它们只是缩写，「`φ` 的每个量词都有界」就成了关于 `φ` **恰巧如何拼写**的事实，任何按 `φ` 的形状计算的过程都无法识别它。作为构造子，有界性就是公式形状的一部分：后文按构造子给公式分类，并用对 `∃̇` 与 `∀̇` **不设情形**的归纳数据证明「量词皆有界」；要表达这种缺席，有界形式必须独立给出。这类公式在不同结构之间保持良好性质，模型诸章建立具体模型后将继续使用这一点。此处的 fixity 表集中声明全书对象层符号的优先级，并使各级与对应的真值代数运算一致。
<!--/-->

```agda
infix  18 _≐_ _∈̇_
infixr 12 _∧̇_ _∨̇_
infixr 10 _⇒̇_
infix  13 ¬̇_

data Formula {ℓ} (K : Type ℓ) (n : ℕ) : Type ℓ where
  _∈̇_ _≐_     : Term K n → Term K n → Formula K n
  _∧̇_ _∨̇_ _⇒̇_ : Formula K n → Formula K n → Formula K n
  ⊥̇            : Formula K n
  ∃̇_ ∀̇_       : Formula K (suc n) → Formula K n
  ∀̇∈ ∃̇∈       : Term K n → Formula K (suc n) → Formula K n

¬̇_ : ∀ {ℓ} {K : Type ℓ} {n} → Formula K n → Formula K n
¬̇ φ = φ ⇒̇ ⊥̇

⊤̇ : ∀ {ℓ} {K : Type ℓ} {n} → Formula K n
⊤̇ = ⊥̇ ⇒̇ ⊥̇
```

<!--en-->
The parameter `K` is where one syntax covers every use the book will make of it:

| choice of `K` | what it gives |
|---|---|
| the carrier of a structure | the working syntax: any set may appear in a formula as a parameter |
| `⊥*`{.Agda} (no constants) | the **parameter-free formulas**: countable and codable, where theories and codes will live |
| a restricted carrier | parameters confined to a class; the shape the constructible-universe development builds `L` with |
<!--zh-->
参数 `K` 让一族语法覆盖全书的所有用途：

| `K` 的取法 | 得到什么 |
|---|---|
| 某结构的载体 | 日常工作语法：任何集合都能以参数身份出现在公式里 |
| `⊥*`{.Agda} (无常元) | **无参公式**：可数、可编码，理论与码所在之处 |
| 受限制的载体 | 参数只许来自某个类；可构造宇宙诸章构造 `L` 用的正是这个形状 |
<!--/-->

<!--en-->
## Sentences and parameter-free formulas

A sentence has no free variables, while a parameter-free formula has no constants. These are independent restrictions, and the distinction becomes essential when formulas are coded and evaluated inside a model.
<!--zh-->
## 句子与无参公式

句子没有自由变量，无参公式没有常元。这是两项彼此独立的限制；当公式在模型内部被编码和求值时，这一区分至关重要。
<!--ja-->
## 文とパラメータを持たない論理式

文には自由変数がなく、パラメータを持たない論理式には定数がありません。この二つの条件は独立であり、モデル内部で論理式を符号化して評価するときに重要になります。
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
**句子**是没有自由变量的公式；作用域既然内蕴，这是一个类型 `Formula K 0`，而非附加条件，本书不为它另设名字。**无参公式**限制的是另一条正交的轴。常元是外部集合以参数身份进入公式的通道；这里常元域取空类型 `⊥*`{.Agda}，参数于是全然没有，而自由变量照旧；与句子一样，这只是一个类型 `Formula ⊥* n`，本书不为它另设名字。从空类型可以推出一切，所以无参公式可以进入任意常元域上的语法；执行这次进入的映射编在书末的常元改名章里。无参公式不是工作语法的对手，而是它的同伴：常元囊括一切集合的语法太大，数不得也编不得码，因此后面各部凡需要把公式**当数据**用，理论作为公式的集合、模型内部的公式码，收集的都是无参公式，参数改经环境喂入。
<!--/-->

<!--en-->
## Recap

The inductive syntax records constants, free-variable arity, and quantifier scope in its types. Later chapters can therefore transform formulas while Agda checks that variables remain well scoped.
<!--zh-->
## 小结

归纳语法在类型中记录常元、自由变量元数与量词作用域。因此后续章节变换公式时，Agda 能检查变量始终处于正确作用域。
<!--ja-->
## まとめ

帰納的な構文は、定数、自由変数の個数、量化子の作用域を型に記録します。そのため後の章で論理式を変換するとき、変数の作用域が正しいことを Agda が検査できます。
<!--/-->

<!--en-->
The object language is an inductive family `Formula K n`{.Agda}: constant domain as
a parameter, scoping intrinsic through `Fin`{.Agda}, each constructor dotted. Around it: the parameter-free
formulas, the data axis whose entry map arrives with the relabelling kit at the
book's tail. Note what is absent: no substitution and no weakening operators
anywhere. The design will keep
it that way, and the little variable machinery the book does need arrives later in
the book. First, formulas need something to talk about.
<!--zh-->
对象语言是归纳族 `Formula K n`{.Agda}：常元域作参数，作用域经 `Fin`{.Agda} 内蕴，构造子全带点。与之配套的是无参公式，其进入映射由书末的常元改名工具组给出。值得注意的是，全篇没有替换算子，也没有弱化算子；这一设计将保持下去，本书所需的少量变量机件将在稍后引入。眼下，公式先得有可谈论的对象。
<!--/-->
