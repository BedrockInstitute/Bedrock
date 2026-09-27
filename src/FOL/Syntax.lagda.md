```agda
{-# OPTIONS --cubical --safe --guardedness #-}
module FOL.Syntax where
```

<!--en-->
# The object language
<!--zh-->
# 对象语言
<!--ja-->
# 対象言語
<!--/-->

```agda
open import Base.Prelude
```

<!--en-->

To study set theory mathematically, we must first make its statements into objects we can define, transform and interpret. This chapter builds that **object language**. Its expressions have two independent parameters: a type `K`{.Agda} of constant names and a natural number `n`{.Agda} of available variable positions. The first controls which objects may be named as parameters; the second controls which variables may be mentioned.
<!--zh-->

要从数学上研究集合论，先得把集合论的陈述变成可以定义、变换和解释的对象。本章构造这样的**对象语言**。表达式有两个独立的参数：常元名的类型 `K`{.Agda} 和可用变量位置的个数 `n`{.Agda}。前者决定哪些对象可以作为参数被指名，后者决定可以提及哪些变量。
<!--ja-->

集合論を数学的に研究するには、まずその文を、定義・変換・解釈できる対象にする必要がある。この章では、その**対象言語**を構成する。式には独立な二つのパラメータがある。定数名の型 `K`{.Agda} と、利用できる変数位置の個数 `n`{.Agda} である。前者はパラメータとして名指せる対象を、後者は言及できる変数を定める。
<!--/-->

<!--en-->
The context length belongs to the expression's type. A variable position is an element of `Fin n`{.Agda}: there are exactly `n`{.Agda} possibilities, numbered from 0 to one less than `n`{.Agda}. Forming a quantifier gives its body one additional position for the bound variable. Thus scope is checked when the expression is built: an out-of-range variable is not an ill-behaved term but no term at all.
<!--zh-->
语境长度属于表达式自身的类型。变量位置是 `Fin n`{.Agda} 的元素：恰有 `n`{.Agda} 种可能，从 0 编号到比 `n`{.Agda} 小一的位置。形成量词时，公式体会多出一个位置供被约束变量使用。于是作用域在构造表达式时就受到检查：越界变量并不是不合规范的词项，而是根本无法形成词项。
<!--ja-->
文脈の長さは式自身の型に含まれる。変数位置は `Fin n`{.Agda} の元であり、0 から `n`{.Agda} より一つ小さい位置まで、ちょうど `n`{.Agda} 通りある。量化子を作るとき、その本体には束縛される変数のための位置が一つ増える。したがって作用域は式を構成する時点で検査される。範囲外の変数は不適切な項なのではなく、そもそも項にならない。
<!--/-->

<!--en-->
Terms provide names for objects; formulas make assertions about them. We first define terms, then use them to build formulas. Throughout the book, `t`{.Agda} and `u`{.Agda} stand for terms, `φ`{.Agda} and `ψ`{.Agda} for formulas, and `i`{.Agda} and `j`{.Agda} for variable positions. The type `K`{.Agda} is the **constant domain** for a particular family of expressions; changing the context length does not change that domain.
<!--zh-->
词项为对象提供名字，公式对这些对象作出断言。因此先定义词项，再由词项构造公式。全书以 `t`{.Agda}、`u`{.Agda} 表示词项，以 `φ`{.Agda}、`ψ`{.Agda} 表示公式，以 `i`{.Agda}、`j`{.Agda} 表示变量位置。类型 `K`{.Agda} 是一族表达式的**常元域**；改变语境长度不会改变这个域。
<!--ja-->
項は対象に名前を与え、論理式はその対象について主張する。そこで項を先に定義し、項から論理式を組み立てる。本書を通して、`t`{.Agda} と `u`{.Agda} は項、`φ`{.Agda} と `ψ`{.Agda} は論理式、`i`{.Agda} と `j`{.Agda} は変数位置を表す。型 `K`{.Agda} は一つの式の族の**定数域**であり、文脈の長さを変えてもこの域は変わらない。
<!--/-->

<!--en-->
## Terms

A term is either a constant name from `K`{.Agda} or a variable position from `Fin n`{.Agda}. The type `Term K n`{.Agda} records both choices of domain and context; it does not claim that every available name or position actually occurs. Since these are the only sources of terms, the family lives at the same universe level as `K`{.Agda}.
<!--zh-->
## 词项

词项要么是取自 `K`{.Agda} 的常元名，要么是取自 `Fin n`{.Agda} 的变量位置。类型 `Term K n`{.Agda} 同时记录常元域和变量语境，并不声称每个可用的名字或位置都实际出现。词项只有这两种来源，所以整个类型族与 `K`{.Agda} 同居一个宇宙层级。
<!--ja-->
## 項

項は `K`{.Agda} から取る定数名か、`Fin n`{.Agda} から取る変数位置のいずれかである。型 `Term K n`{.Agda} は定数域と変数文脈の両方を記録するが、利用可能な名前や位置がすべて実際に現れるという意味ではない。項の作り方はこの二つだけなので、型の族全体は `K`{.Agda} と同じ宇宙レベルに置かれる。
<!--/-->

<!--en-->
The declaration introduces the family; the two constructors immediately below give its inhabitants.
<!--zh-->
下面先声明这个类型族，再给出它的两个构造子。
<!--ja-->
まず型の族を宣言し、続けてその二つの構成子を与える。
<!--/-->

```agda
data Term {ℓ} (K : Type ℓ) (n : ℕ) : Type ℓ where
```

<!--en-->
`con`{.Agda} turns an element of `K`{.Agda} into a constant name. It does not yet say which object that name denotes; interpretation comes later. `var`{.Agda} takes an index in `Fin n`{.Agda}. In a context of length two, positions 0 and 1 are available, but position 2 is not. This is a formation rule, not a test applied after a term has been written. A constant term uses no variable positions, yet it can still inhabit `Term K 2`{.Agda}.
<!--zh-->
`con`{.Agda} 将 `K`{.Agda} 的元素变成常元名，尚不指定这个名字指称哪个对象；解释留待后文。`var`{.Agda} 取 `Fin n`{.Agda} 中的索引。语境长度为二时，位置 0 和 1 可用，位置 2 不可用。这是词项的形成规则，而不是写出词项之后再作的检查。常元词项没有使用任何变量位置，却仍可以属于 `Term K 2`{.Agda}。
<!--ja-->
`con`{.Agda} は `K`{.Agda} の元を定数名にする。その名前がどの対象を指すかはまだ指定せず、解釈は後で与える。`var`{.Agda} は `Fin n`{.Agda} の添字を取る。長さ二の文脈では位置 0 と 1 は使えるが、位置 2 は使えない。これは項を書いた後の検査ではなく、項の形成規則である。定数項は変数位置を一つも使わないが、それでも `Term K 2`{.Agda} に属し得る。
<!--/-->

```agda
  con : K → Term K n
  var : Fin n → Term K n
```

<!--en-->
## Formulas

Terms can be compared for membership or equality. These atomic formulas are combined with conjunction, disjunction, implication and quantifiers to form further assertions. The small dot on `∈̇`{.Agda}, `≐`{.Agda}, `∧̇`{.Agda} and the other logical symbols marks the **object language**: for example, `t ∈̇ u`{.Agda} is a formula *about* membership, not the surrounding Agda proposition that two sets satisfy membership. A meaning will be assigned to each formula only when a structure and an interpretation are supplied.
<!--zh-->
## 公式

词项之间可以断言隶属或相等，得到原子公式；再用合取、析取、蕴涵和量词组成更复杂的断言。`∈̇`{.Agda}、`≐`{.Agda}、`∧̇`{.Agda} 等逻辑符号上的小点标记**对象语言**这一层：例如 `t ∈̇ u`{.Agda} 是一个*谈论*隶属的公式，并非周围 Agda 理论中两个集合满足隶属关系的命题。只有给定结构和解释后，公式才获得含义。
<!--ja-->
## 論理式

項の間の所属または等号を主張すると原子論理式ができ、連言、選言、含意、量化子によってさらに複合的な主張を作る。`∈̇`{.Agda}、`≐`{.Agda}、`∧̇`{.Agda} などの論理記号に付く小さな点は、**対象言語**の層を示す。たとえば `t ∈̇ u`{.Agda} は所属に*ついて述べる*論理式であり、周囲の Agda 理論で二つの集合が所属関係を満たすという命題ではない。構造と解釈が与えられて初めて、論理式に意味が定まる。
<!--/-->

<!--en-->
The precedence declarations below govern how Agda parses these symbols. Atomic relations bind more tightly than negation, which binds more tightly than conjunction and disjunction; implication binds least tightly. Both binary connective groups associate to the right, so `φ ⇒̇ ψ ⇒̇ θ`{.Agda} means `φ ⇒̇ (ψ ⇒̇ θ)`{.Agda}. Precedence changes how a written expression is grouped, not which formulas exist.
<!--zh-->
下面的优先级声明规定 Agda 如何解析这些符号。原子关系结合得最紧，其次是否定，再次是合取与析取；蕴涵结合得最松。两组二元联结词都向右结合，因此 `φ ⇒̇ ψ ⇒̇ θ`{.Agda} 表示 `φ ⇒̇ (ψ ⇒̇ θ)`{.Agda}。优先级只决定所写表达式如何分组，不改变哪些公式可以形成。
<!--ja-->
以下の優先順位宣言は、Agda がこれらの記号をどう解析するかを定める。原子関係が最も強く結合し、次に否定、連言と選言が続き、含意が最も弱い。二組の二項結合子はいずれも右結合なので、`φ ⇒̇ ψ ⇒̇ θ`{.Agda} は `φ ⇒̇ (ψ ⇒̇ θ)`{.Agda} を意味する。優先順位が変えるのは書かれた式のまとまり方であり、形成できる論理式の種類ではない。
<!--/-->

```agda
infix  18 _≐_ _∈̇_
infixr 12 _∧̇_ _∨̇_
infixr 10 _⇒̇_
infix  13 ¬̇_
```

<!--en-->
Like `Term K n`{.Agda}, `Formula K n`{.Agda} records the constant domain and the available variable positions. Its atomic constructors compare two terms in that same context. Conjunction, disjunction and implication combine formulas without changing the context, while `⊥̇`{.Agda} represents falsity.

We keep these connectives as constructors because the later interpretation is constructive. Classical rewritings such as `φ ∨̇ ψ`{.Agda} into `¬̇ (¬̇ φ ∧̇ ¬̇ ψ)`{.Agda} generally require double-negation elimination to preserve their intended meanings. Here disjunction and implication receive their own interpretation in `hProp`{.Agda}; they are not abbreviations in terms of negation.
<!--zh-->
与 `Term K n`{.Agda} 一样，`Formula K n`{.Agda} 记录常元域与可用变量位置。它的原子构造子比较同一语境中的两个词项。合取、析取和蕴涵组合公式而不改变语境，`⊥̇`{.Agda} 则表示假。

保留这些联结词作为构造子，是因为后文的解释是构造性的。经典逻辑中可把 `φ ∨̇ ψ`{.Agda} 改写成 `¬̇ (¬̇ φ ∧̇ ¬̇ ψ)`{.Agda}，但要保持预期含义，一般需要双重否定消去。这里的析取和蕴涵在 `hProp`{.Agda} 中各有自己的解释，不是通过否定写出的缩写。
<!--ja-->
`Term K n`{.Agda} と同じく、`Formula K n`{.Agda} は定数域と利用可能な変数位置を記録する。その原子構成子は、同じ文脈にある二つの項を比較する。連言、選言、含意は文脈を変えずに論理式を組み合わせ、`⊥̇`{.Agda} は偽を表す。

これらの結合子を構成子として保つのは、後の解釈が構成的だからである。古典論理では `φ ∨̇ ψ`{.Agda} を `¬̇ (¬̇ φ ∧̇ ¬̇ ψ)`{.Agda} と書き換えられるが、意図した意味を保つには一般に二重否定除去が必要になる。ここでは選言と含意を `hProp`{.Agda} でそれぞれ直接解釈し、否定による略記とはしない。
<!--/-->

```agda
data Formula {ℓ} (K : Type ℓ) (n : ℕ) : Type ℓ where
  _∈̇_ _≐_     : Term K n → Term K n → Formula K n
  _∧̇_ _∨̇_ _⇒̇_ : Formula K n → Formula K n → Formula K n
  ⊥̇            : Formula K n
```

<!--en-->
Quantifiers show why the context length is part of a formula's type. An unbounded quantifier takes a body in `Formula K (suc n)`{.Agda} and produces a formula in `Formula K n`{.Agda}. Inside the body, position 0 is newly bound; each old position moves up by one. For an outer context of length one, the positions look like this:

| location | available positions | what they refer to |
|---|---|---|
| outside the quantifier | 0 | the original free variable |
| inside its body | 0, 1 | the bound variable, then the original free variable |
: A quantifier adds a position at the front of its body’s context

The body need not use its new position. This positional convention, known as de Bruijn indexing, avoids storing variable names or deciding when to rename them. The bounded forms `∀̇∈`{.Agda} and `∃̇∈`{.Agda} read as *for every member of* and *for some member of*. Their bound `t`{.Agda} belongs to the *outer* context `Term K n`{.Agda}; only the body uses the extended context. We keep them as constructors rather than abbreviations: later, formulas with only bounded quantifiers can be recognized directly from their constructors.
<!--zh-->
量词说明了为什么语境长度要写进公式的类型。无界量词取 `Formula K (suc n)`{.Agda} 中的公式体，得到 `Formula K n`{.Agda} 中的公式。公式体内的位置 0 是新约束的变量，原有位置都顺移一位。若外层语境长度为一，位置的对应关系如下：

| 所在位置 | 可用的位置 | 指向什么 |
|---|---|---|
| 量词外 | 0 | 原有的自由变量 |
| 公式体内 | 0、1 | 被约束变量、原有的自由变量 |
: 量词在公式体语境的最前面增加一个位置

公式体可以不使用这个新位置。这种按位置记录作用域的方式称为 de Bruijn 索引，无须在公式中保存变量名，也无须考虑何时改名。有界形式 `∀̇∈`{.Agda} 和 `∃̇∈`{.Agda} 分别读作「对……的每个成员」和「对……的某个成员」。界限 `t`{.Agda} 属于*外层*语境 `Term K n`{.Agda}；只有公式体使用扩展后的语境。这里把有界量词保留为构造子而非缩写，后文便能仅凭构造子识别出所有量词均有界的公式。
<!--ja-->
量化子を見ると、文脈の長さが論理式の型に必要な理由が分かる。非有界量化子は `Formula K (suc n)`{.Agda} の本体を受け取り、`Formula K n`{.Agda} の論理式を返す。本体の位置 0 が新たに束縛された変数で、もとの位置は一つずつずれる。外側の文脈の長さが一の場合、対応は次のとおりである：

| 場所 | 利用できる位置 | 指すもの |
|---|---|---|
| 量化子の外 | 0 | もとの自由変数 |
| 本体の中 | 0、1 | 束縛された変数、もとの自由変数 |
: 量化子は本体の文脈の先頭に位置を一つ加える

本体が新しい位置を使う必要はない。この位置による作用域の表現を de Bruijn 添字という。論理式に変数名を保存せず、改名の時機も考えなくてよい。有界形 `∀̇∈`{.Agda} と `∃̇∈`{.Agda} は、それぞれ「…のすべての元について」「…のある元について」と読む。限界 `t`{.Agda} は*外側*の文脈 `Term K n`{.Agda} に属し、本体だけが拡張された文脈を使う。有界量化子を略記ではなく構成子とすることで、後の章では構成子だけから「すべての量化子が有界」という性質を判定できる。
<!--/-->

```agda
  ∃̇_ ∀̇_       : Formula K (suc n) → Formula K n
  ∀̇∈ ∃̇∈       : Term K n → Formula K (suc n) → Formula K n
```

<!--en-->
Negation illustrates the opposite choice. We define `¬̇ φ`{.Agda} as `φ ⇒̇ ⊥̇`{.Agda}, rather than adding another constructor. A function that inspects a formula therefore sees an implication, not a separate negation case. Under the intended interpretation, this implication expresses the refutation of `φ`{.Agda}.
<!--zh-->
否定则采取另一种方式：将 `¬̇ φ`{.Agda} 定义为 `φ ⇒̇ ⊥̇`{.Agda}，而不再增加构造子。因此，检查公式的函数看到的是蕴涵，不必单设否定的情形。在预期的解释下，这个蕴涵表达的正是对 `φ`{.Agda} 的否证。
<!--ja-->
否定は別の方法を採る。構成子を増やすのではなく、`¬̇ φ`{.Agda} を `φ ⇒̇ ⊥̇`{.Agda} と定義する。したがって論理式を調べる関数が見るのは含意であり、否定のために独立な場合を設ける必要はない。意図する解釈のもとで、この含意は `φ`{.Agda} の反駁を表す。
<!--/-->

```agda
¬̇_ : ∀ {ℓ} {K : Type ℓ} {n} → Formula K n → Formula K n
¬̇ φ = φ ⇒̇ ⊥̇
```

<!--en-->
Truth is likewise defined, not primitive: `⊤̇`{.Agda} unfolds to `⊥̇ ⇒̇ ⊥̇`{.Agda}. The future interpretation needs only its implication and falsity cases to give meaning to both derived symbols. These definitions work for every constant domain and context length.
<!--zh-->
真也由定义给出，而非原始构造子：`⊤̇`{.Agda} 展开为 `⊥̇ ⇒̇ ⊥̇`{.Agda}。后文的解释只需处理蕴涵与假，就能解释这两个派生符号。这些定义对任意常元域和语境长度都适用。
<!--ja-->
真も原始的な構成子ではなく、`⊤̇`{.Agda} を `⊥̇ ⇒̇ ⊥̇`{.Agda} と定義する。後の解釈は含意と偽を扱うだけで、この二つの派生記号にも意味を与えられる。これらの定義は任意の定数域と文脈の長さで使える。
<!--/-->

```agda
⊤̇ : ∀ {ℓ} {K : Type ℓ} {n} → Formula K n
⊤̇ = ⊥̇ ⇒̇ ⊥̇
```

<!--en-->
A single formation rule can serve different interpretations. If `K`{.Agda} is a structure’s carrier, constant symbols can name its elements. Choosing a type of names for a restricted collection limits the available parameters; the empty type `⊥*`{.Agda} permits none. The variable context is a separate choice.

## Sentences and parameter-free formulas

There are two distinct ways to rule out names. A **sentence** has no free variables: its context length is zero, giving `Formula K 0`{.Agda}, but it may still contain constants. A **parameter-free formula** has no constants: its constant domain is `⊥*`{.Agda}, giving `Formula ⊥* n`{.Agda}, but it may still have free variables. Neither needs a separate datatype or code name.

| names available | formula type |
|---|---|
| both | `Formula K n`{.Agda} |
| constants only | `Formula K 0`{.Agda} |
| positions only | `Formula ⊥* n`{.Agda} |
| neither | `Formula ⊥* 0`{.Agda} |
: Free variables and constant names are restricted independently

Because the empty type maps to any `K`{.Agda}, a parameter-free formula can be carried into any constant domain by the later constant-mapping operation. Such formulas can be enumerated without first enumerating the elements of a structure. This does not limit coding to parameter-free syntax: later chapters also code formulas whose constants come from a carrier.

## Recap

The types record which constants and variable positions are available, while the quantifier constructors record how scope changes. They do not yet assign meanings to terms or formulas. To do that, we first need a structure in which their symbols can be interpreted.
<!--zh-->
同一套形成规则可以服务于不同的解释。若 `K`{.Agda} 是某个结构的载体，常元符号就能指名其中的元素；若只为某个受限范围选取名字类型，可用参数就受到限制；取空类型 `⊥*`{.Agda} 则不允许常元。变量语境是另一个独立的选择。

## 句子与无参公式

排除名字有两种不同的方式。**句子**没有自由变量：语境长度为零，得到 `Formula K 0`{.Agda}，但仍可含有常元。**无参公式**没有常元：常元域取空类型 `⊥*`{.Agda}，得到 `Formula ⊥* n`{.Agda}，但仍可含有自由变量。两者都不需要另设数据类型或代码名称。

| 可用的名字 | 公式类型 |
|---|---|
| 两者皆可 | `Formula K n`{.Agda} |
| 仅常元 | `Formula K 0`{.Agda} |
| 仅变量位置 | `Formula ⊥* n`{.Agda} |
| 两者均无 | `Formula ⊥* 0`{.Agda} |
: 自由变量与常元名受彼此独立的限制

空类型可以映入任意 `K`{.Agda}，因此后文的常元映射操作能把无参公式带入任意常元域。无参公式不必先枚举结构的元素，就可以枚举语法。但这并不意味着只有无参语法才能编码；后文也会编码含有载体常元的公式。

## 小结

这些类型记录可用的常元与变量位置，量词构造子则记录作用域如何变化。它们尚未赋予词项和公式含义。要做到这一点，首先需要一个结构，让这些符号有解释的所在。
<!--ja-->
同じ形成規則を異なる解釈に使える。`K`{.Agda} が構造の台なら、定数記号はその元を名指せる。対象を限定した名前の型を選べば利用できるパラメータは制限され、空型 `⊥*`{.Agda} なら定数は一つもない。変数文脈はこれとは独立に選ぶ。

## 文とパラメータを持たない論理式

名前を排除する方法は二つある。**文**には自由変数がない。文脈の長さをゼロにした `Formula K 0`{.Agda} であり、定数は含められる。**パラメータを持たない論理式**には定数がない。定数域を空型 `⊥*`{.Agda} にした `Formula ⊥* n`{.Agda} であり、自由変数は含められる。どちらにも別のデータ型やコード名は設けない。

| 利用できる名前 | 論理式の型 |
|---|---|
| 両方 | `Formula K n`{.Agda} |
| 定数のみ | `Formula K 0`{.Agda} |
| 位置のみ | `Formula ⊥* n`{.Agda} |
| どちらもなし | `Formula ⊥* 0`{.Agda} |
: 自由変数と定数名は独立に制限される

空型から任意の `K`{.Agda} への写像があるので、後の定数写像によって、パラメータを持たない論理式をどの定数域にも移せる。このような論理式なら、構造の元を先に列挙せずに構文を列挙できる。ただし、符号化できるのはそれだけではない。後の章では台の定数を含む論理式も符号化する。

## まとめ

これらの型は利用できる定数と変数位置を記録し、量化子の構成子は作用域の変化を記録する。まだ項や論理式に意味は与えていない。そのためには、まず記号を解釈する構造が必要である。
<!--/-->
