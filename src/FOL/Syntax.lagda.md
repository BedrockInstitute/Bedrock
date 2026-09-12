<!--en-->
# The object language

First-order set theory needs a language whose expressions can later be interpreted, coded, and manipulated inside a model. This chapter defines that raw syntax with its scope built into the types: terms and formulas are indexed by a constant domain and by the length of the available free-variable context. That indexing will let later semantic constructions rule out ill-scoped expressions before interpretation begins.
<!--zh-->
# 对象语言

一阶集合论需要一套语言，使其中的表达式随后能够在模型内得到解释、编码和变换。本章定义这套原始语法，并把作用域直接纳入类型：词项与公式都以常元域和可用自由变量上下文的长度为索引。借助这些索引，后续语义构造在开始解释之前便能排除作用域不合法的表达式。
<!--ja-->
# 対象言語

一階集合論には、後でモデルの内部に解釈し、符号化し、変形できる言語が必要です。この章では、その生の構文を、作用域を型に組み込んだ形で定義します。項と論理式は、定数域と利用可能な自由変数文脈の長さで添字づけられます。この添字づけにより、後の意味論的構成は、解釈を始める前に作用域の正しくない式を排除できます。
<!--/-->

<!--en-->
To reason about first-order set theory inside type theory, we first need its language as a mathematical object: not truth, not models, just the raw strings that formulas are built from. This chapter fixes that syntax once and for all. The one structural commitment worth stating up front is about variables: each formula is built against a finite context of exactly `n` free-variable slots, and a variable is an element of `Fin n`{.Agda}, the type of valid positions `0` through `n - 1`.
<!--zh-->
要在类型论内部讨论一阶集合论，首先需要把它的语言变成一个数学对象：不是真值，不是模型，只是构造公式的原始字符串。本章一次性地固定这套语法。值得先说明的结构性约定只有一条，关于变量：每个公式都建立在恰好 `n` 个自由变量槽位的有限上下文之上，变量是 `Fin n`{.Agda} 的元素，即合法位置 `0` 到 `n - 1`。
<!--ja-->
型理論の内部で一階集合論を論じるには、まずその言語を数学的な対象として持つ必要があります。真理値でもモデルでもなく、論理式が組み立てられる生の記号列だけです。この章はその構文を一度に固定します。最初に述べるべき構造的な約束は変数についての一つだけです。各論理式はちょうど `n` 個の自由変数スロットからなる有限の文脈の上に組み立てられ、変数は `Fin n`{.Agda} の元、つまり `0` から `n - 1` までの有効な位置です。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}
```

<!--en-->
Fixing `n` in advance is what makes scoping a property of the type itself rather than a side condition to check. When a formula is later quantified, its context grows from `n` to `suc n`; the syntax will track that growth, and no term will ever be able to name a variable outside its declared supply.
<!--zh-->
事先固定 `n`，使得作用域成为类型本身的性质，而不是需要另加检查的附加条件。公式随后被量化时，其上下文从 `n` 增长到 `suc n`；语法会记录这一增长，任何词项都无法指涉其声明供给之外的变量。
<!--ja-->
`n` をあらかじめ固定することで、作用域が確認すべき追加条件ではなく型そのものの性質になります。論理式が後に量化されると、その文脈は `n` から `suc n` へと増えます。構文はこの増加を追跡し、宣言された供給の外にある変数を項が名指すことは決してできません。
<!--/-->

```agda

module FOL.Syntax where
```

<!--en-->
Alongside variables, formulas may mention constants. The syntax leaves their collection open by taking an arbitrary type `K` of constant names, fixed uniformly throughout a given formula. Thus `K` records which parameters may be named, while `n` records which free-variable slots may be used; the definitions of terms and formulas now combine these two independent resources.
<!--zh-->
除变量外，公式还可以提到常元。语法以任意类型 `K` 作为常元名的类型，并在一条给定公式中统一固定它，从而不预先限定可用常元的集合。因此，`K` 记录可以指名哪些参数，`n` 则记录可以使用哪些自由变量槽位；接下来对词项与公式的定义将结合这两种彼此独立的资源。
<!--ja-->
変数のほかに、論理式は定数を言及できます。構文は定数名の型として任意の `K` を取り、一つの論理式を通じてそれを一様に固定することで、利用できる定数の集まりをあらかじめ限定しません。したがって `K` はどのパラメータを名指せるかを記録し、`n` はどの自由変数スロットを使えるかを記録します。これから定める項と論理式は、この独立な二つの資源を組み合わせます。
<!--/-->

```agda

open import Base.Prelude
```

<!--en-->
## Terms and formulas

A term is either a named constant or a variable selected from `n` available slots. Formulas combine membership and equality atoms with logical connectives and bounded or unbounded quantifiers.

Some conventions used through the book: `t`, `u` stand for terms, `φ`, `ψ` for formulas, `n`, `m` for free-variable context lengths, and `i`, `j` for variable indices. A term is either a **constant** or a **variable**. The type parameter `K`, the **constant domain**, determines which constants are available; a variable is an element of `Fin n`{.Agda}, so its index lies between `0` and `n - 1`. A term need not mention every available slot. Scoping is intrinsic: an out-of-scope variable is unrepresentable.
<!--zh-->
## 词项与公式

词项是一个具名常元，或从 `n` 个可用槽位中选出的变量。公式由隶属与相等原子式、逻辑联结词以及有界或无界量词组成。

先立几个贯穿全书的变量约定：`t`、`u` 代表词项，`φ`、`ψ` 代表公式，`n`、`m` 代表自由变量上下文的长度，`i`、`j` 代表变量索引。词项要么是**常元**，要么是**变量**。类型参数 `K` 称为**常元域**，决定可用的常元；变量是 `Fin n`{.Agda} 的元素，故其索引介于 `0` 与 `n - 1` 之间。词项无需用到每个可用槽位。作用域由此内蕴：越界变量不可表示。
<!--ja-->
## 項と論理式

項は名前を持つ定数か、`n` 個の利用可能なスロットから選ばれた変数です。論理式は所属と等号の原子式を、論理結合子、有界量化子、非有界量化子で組み立てます。

まず本書を通して使う約束を述べます。`t`、`u` は項、`φ`、`ψ` は論理式、`n`、`m` は自由変数文脈の長さ、`i`、`j` は変数の添字を表します。項は**定数**か**変数**です。型パラメータ `K`、すなわち**定数域**が利用可能な定数を定めます。変数は `Fin n`{.Agda} の元なので、その添字は `0` から `n - 1` の範囲にあります。項が利用可能なすべてのスロットを使う必要はありません。したがってスコープは内在的であり、範囲外の変数は表現できません。
<!--/-->

<!--en-->
A term lives in `Term K n`: against a constant domain `K` and a context of `n` free-variable slots, it is either a constant name or a slot index. With `n = 2`, say, `var 0`, `var 1`, and `con c` are terms in `Term K 2`. What is not available is `var 2`: there is no element of `Fin 2`{.Agda} named `2`, so that expression is not merely rejected after formation; it cannot be formed at all.
<!--zh-->
词项居于 `Term K n`：在常元域 `K` 与 `n` 个自由变量槽位的上下文下，它要么是一个常元名，要么是一个槽位索引。例如取 `n = 2`，`var 0`、`var 1` 与 `con c` 都是 `Term K 2` 中的词项。不可用的是 `var 2`：`Fin 2`{.Agda} 中没有名为 `2` 的元素，所以这个表达式并非先形成再遭拒绝，而是根本无法形成。
<!--ja-->
項は `Term K n` に属します。定数域 `K` と `n` 個の自由変数スロットからなる文脈のもとで、項は定数名かスロットの添字です。たとえば `n = 2` なら、`var 0`、`var 1`、`con c` はいずれも `Term K 2` の項です。使えないのは `var 2` です。`Fin 2`{.Agda} に `2` という元は存在しないため、この式は構成された後で退けられるのではなく、そもそも構成できません。
<!--/-->

```agda
data Term {ℓ} (K : Type ℓ) (n : ℕ) : Type ℓ where
```

<!--en-->
The two displayed constructors give exactly these cases: `con` wraps any inhabitant of `K`, treated purely as a name with no meaning attached yet, and `var` wraps an element of `Fin n`. Note what `n` does not measure: it is not a count of variable occurrences. `con c` and `var 0` both have type `Term K 2` even though neither mentions two slots; `n` bounds which slots may be named, not how often slots are used. For the same reason `n` does not touch the constants, and `Term K n` sits at the universe level of `K` itself.
<!--zh-->
给出的两个构造子恰好就是这两种情形：`con` 包装 `K` 的任意元素，只当作名字，暂不附义；`var` 包装 `Fin n` 的一个元素。注意 `n` 度量的不是什么：它不是变量出现次数的计数。`con c` 与 `var 0` 的类型都是 `Term K 2`，尽管二者都没有提到两个槽位；`n` 约束的是哪些槽位可被指名，而不是槽位被使用的频次。同理，`n` 也不触及常元，`Term K n` 就居于 `K` 本身所在的宇宙层级。
<!--ja-->
示されている 2 つの構成子がちょうどこの場合に対応します。`con` は `K` の任意の元を包み、それをまだ意味の付いていない純粋な名前として扱い、`var` は `Fin n` の元を包みます。`n` が測っていないものに注意してください。`n` は変数の出現回数の計数ではありません。`con c` も `var 0` も、2 つのスロットに言及していないにもかかわらず型は `Term K 2` です。`n` が制約するのはどのスロットを名指せるかであって、スロットの使用頻度ではありません。同様に `n` は定数には関わらないため、`Term K n` は `K` 自身の宇宙レベルに置かれます。
<!--/-->

```agda
  con : K → Term K n
  var : Fin n → Term K n
```

<!--en-->
Formulas follow, indexed the same way. Every constructor of the object language carries an **upper dot**: a layer mark, and seeing it tells you at once that a symbol is syntax, not meaning. Reading them: `∈̇` is object membership, `≐` object equality, `∧̇ ∨̇ ⇒̇ ¬̇ ⊤̇ ⊥̇` the connectives, `∃̇ ∀̇` the quantifiers, and `∀̇∈`, `∃̇∈` the **bounded** quantifiers, read "for every member of" and "for some member of". Binding is by de Bruijn: a quantifier takes a body with one more free variable, and variable `0` is the one just bound.

Two design decisions are visible in the constructor list. First, the binary connectives are primitive, and this is this development's way of giving each connective exactly one truth-algebra operation as its meaning, in a constructive semantics where double-negation elimination is not available in general. A classical text can economize, spelling `φ ∨ ψ` as `¬ (¬ φ ∧ ¬ ψ)`, `∀` as `¬ ∃ ¬`, `φ ⇒ ψ` as `¬ φ ∨ ψ`, because classically the double negations cancel; constructively that argument is not available, so these spellings would not deliver the intended constructive meanings. This development therefore takes `∨`, `∀`, `⇒` as constructors. Negation and truth are defined: `¬̇ φ` is `φ ⇒̇ ⊥̇`, and `⊤̇` is `⊥̇ ⇒̇ ⊥̇`.

Second, the bounded quantifiers are primitive in their own right even though `∀̇∈ t φ` could be spelled with `∀̇`. Had they been abbreviations, "every quantifier in `φ` is bounded" would be a fact about how `φ` happens to be spelled, invisible to anything that computes over `φ`'s shape. As constructors, boundedness is part of the shape of a formula: later chapters classify formulas by a datatype over their constructors, and certify "all quantifiers bounded" by a datatype that simply has **no case** for `∃̇` and `∀̇`; expressing this absence requires the bounded forms to be given independently. Formulas of that shape behave well across structures, a thread taken up once the model chapters have established their model and carried into the constructible-universe chapters.

The block begins with a fixity table: the book's single declaration of the notation levels for the object layer.
<!--zh-->
公式随后，以同样的方式索引。对象语言的每个构造子都带一个**上点**：这个点就是语法层的标记，见到点即可知道符号指语法而非含义。读法：`∈̇` 是对象成员，`≐` 是对象相等，`∧̇ ∨̇ ⇒̇ ¬̇ ⊤̇ ⊥̇` 是联结词，`∃̇ ∀̇` 是量词，`∀̇∈`、`∃̇∈` 是**有界**量词，读作「对……的每个成员」与「对……的某个成员」。约束采用 de Bruijn 方式：量词所取的公式体多出一个自由变量，变量 `0` 即刚被约束的那个。

构造子清单体现两个设计决定。其一，二元联结词是原语，这是本开发给每个联结词恰好指派一个真值代数运算作为其含义的方式，而其所在的构造性语义中双重否定消去并非一般可得。经典教科书可以把 `φ ∨ ψ` 写成 `¬ (¬ φ ∧ ¬ ψ)`、把 `∀` 写成 `¬ ∃ ¬`、把 `φ ⇒ ψ` 写成 `¬ φ ∨ ψ`，因为经典逻辑可以消去双重否定；构造逻辑中这一论证不可用，这些写法无法给出想要的构造性含义。因此本开发将 `∨`、`∀`、`⇒` 取为构造子。否定与真则是定义出来的：`¬̇ φ` 即 `φ ⇒̇ ⊥̇`，`⊤̇` 即 `⊥̇ ⇒̇ ⊥̇`。

其二，有界量词虽然可用 `∀̇` 拼写，仍单独作为原语。倘若它们只是缩写，「`φ` 的每个量词都有界」就成了关于 `φ` **恰巧如何拼写**的事实，任何按 `φ` 的形状计算的过程都无法识别它。作为构造子，有界性就是公式形状的一部分：后文按构造子给公式分类，并用对 `∃̇` 与 `∀̇` **不设情形**的归纳数据证明「量词皆有界」；要表达这种缺席，有界形式必须独立给出。这类公式在不同结构之间保持良好性质，模型诸章建立具体模型后将继续使用这一点，并延伸到可构造宇宙诸章。

本块以 fixity 表开头：这是全书对象层记号层级的唯一集中声明。
<!--ja-->
論理式が続きます。同じように添字づけられています。対象言語の各構成子は**上付きの点**を持ちます。これは層の印であり、点を見ればその記号が意味ではなく構文だとただちに分かります。読み方は次のとおりです。`∈̇` は対象の所属，`≐` は対象言語の等号，`∧̇ ∨̇ ⇒̇ ¬̇ ⊤̇ ⊥̇` は結合子，`∃̇ ∀̇` は量化子，`∀̇∈` と `∃̇∈` は**有界**量化子で、それぞれ「…のすべての元について」「…のある元について」と読みます。束縛は de Bruijn 方式で、量化子は自由変数が 1 つ多い本体を取り、変数 `0` がまさに今束縛されたものです。

構成子の一覧には 2 つの設計決定が現れています。第一に、二項結合子が原始的なのは、各結合子にちょうど 1 つの真理値代数の演算をその意味として与える、この開発のやり方だからです。その意味論は構成的であり、二重否定の消去は一般には使えません。古典的な教科書は二重否定が消えることを利用して、`φ ∨ ψ` を `¬ (¬ φ ∧ ¬ ψ)`、`∀` を `¬ ∃ ¬`、`φ ⇒ ψ` を `¬ φ ∨ ψ` と省略できますが、構成的にはこの論法が使えず、これらの書き方は望まれる構成的な意味を与えられません。そこでこの開発は `∨`、`∀`、`⇒` を構成子として採ります。否定と真は定義されます。`¬̇ φ` は `φ ⇒̇ ⊥̇`、`⊤̇` は `⊥̇ ⇒̇ ⊥̇` です。

第二に、有界量化子は `∀̇` で書き表せるにもかかわらず、それ自身の権利で原始的です。もし省略形なら、「`φ` のすべての量化子が有界である」は `φ` が**たまたまどう書かれているか**についての事実となり、`φ` の形の上を計算する何物にも見えません。構成子としてなら、有界性は論理式の形の一部です。後の章では構成子の上のデータ型で論理式を分類し、`∃̇` と `∀̇` に対して**場合を持たない**データ型によって「量化子はすべて有界」を証明します。この不在を表現するには、有界の形が独立に与えられている必要があります。その形の論理式は構造を越えてよく振る舞い、この系はモデル諸章でモデルが確立されたのち、構成可能宇宙の章へと引き継がれます。

このブロックは結合の優先順位の表から始まります。対象レイヤーの記法の水準に関する本書で唯一の宣言です。
<!--/-->

<!--en-->
These four lines fix how compound formulas parse. Atoms and negation bind tightest (18 and 13), the conjunctive and disjunctive pairs sit in the middle (12, right-associative), and implication is weakest (10, right-associative so that `φ ⇒̇ ψ ⇒̇ θ` groups as `φ ⇒̇ (ψ ⇒̇ θ)`). These are parser declarations about nesting and grouping; with them, well-formed nested formulas read without extra parentheses.
<!--zh-->
这四行确定复合公式的解析方式。原子式与否定结合得最紧 (18 与 13)，合取与析取居中 (12，右结合)，蕴涵最弱 (10，右结合，故 `φ ⇒̇ ψ ⇒̇ θ` 读作 `φ ⇒̇ (ψ ⇒̇ θ)`)。这些是关于嵌套与分组的解析器声明；有了它们，良构的嵌套公式无需额外括号即可读清。
<!--ja-->
この 4 行は複合論理式の構文解析を固定します。原子式と否定が最も強く結合し (18 と 13)、連言と選言がその次 (12、右結合)、含意が最も弱く (10、右結合)、したがって `φ ⇒̇ ψ ⇒̇ θ` は `φ ⇒̇ (ψ ⇒̇ θ)` とグループ化されます。これらは入れ子とグループ化についての構文解析上の宣言であり、これにより整形式の入れ子になった式は余分な括弧なしで読めます。
<!--/-->

```agda
infix  18 _≐_ _∈̇_
infixr 12 _∧̇_ _∨̇_
infixr 10 _⇒̇_
infix  13 ¬̇_
```

<!--en-->
The `Formula` family is indexed exactly like `Term`: by a constant domain `K` and a free-variable count `n`. Its constructors split into three groups. The atoms `_∈̇_` and `_≐_` take two terms and assert object membership or equality between them. The propositional constructors `_∧̇_`, `_∨̇_`, `_⇒̇_` and `⊥̇` build compound formulas recursively; the index `n` is preserved because connectives neither bind nor release variables.
<!--zh-->
`Formula` 族与 `Term` 的索引方式完全相同：常元域 `K` 与自由变量个数 `n`。构造子分三组。原子式 `_∈̇_` 与 `_≐_` 接受两个词项，断言它们之间的对象隶属或相等。命题构造子 `_∧̇_`、`_∨̇_`、`_⇒̇_` 与 `⊥̇` 递归地构造复合公式；联结词既不约束也不释放变量，所以索引 `n` 保持不变。
<!--ja-->
`Formula` 族は `Term` とまったく同じように、定数域 `K` と自由変数の個数 `n` で添字づけられます。構成子は 3 つのグループに分かれます。原子式 `_∈̇_` と `_≐_` は 2 つの項を受け取り、それらの間の対象の所属か等号を主張します。命題的構成子 `_∧̇_`、`_∨̇_`、`_⇒̇_` と `⊥̇` は再帰的に複合論理式を組み立てます。結合子は変数を束縛も解放もしないため、インデックス `n` は保たれます。
<!--/-->

```agda

data Formula {ℓ} (K : Type ℓ) (n : ℕ) : Type ℓ where
  _∈̇_ _≐_     : Term K n → Term K n → Formula K n
  _∧̇_ _∨̇_ _⇒̇_ : Formula K n → Formula K n → Formula K n
  ⊥̇            : Formula K n
```

<!--en-->
The quantifiers close the list, and their types encode de Bruijn binding precisely. `∃̇_` and `∀̇_` take a body of type `Formula K (suc n)` and return a formula over `n` free variables: the body may additionally refer to variable `0`, the one just bound. The bounded forms `∀̇∈` and `∃̇∈` additionally take a term `t` from the outer scope, ranging over the members of `t`; the body is again `Formula K (suc n)`. Because the bounded quantifiers are constructors in their own right, boundedness is readable off the shape of a formula, not off its spelling.
<!--zh-->
量词补全了构造子清单，其类型精确编码了 de Bruijn 约束。`∃̇_` 与 `∀̇_` 取类型为 `Formula K (suc n)` 的公式体，返回带 `n` 个自由变量的公式：公式体可以额外指涉变量 `0`，即刚被约束的那个。有界形式 `∀̇∈` 与 `∃̇∈` 还从外层取一个词项 `t`，遍历 `t` 的成员；公式体同样是 `Formula K (suc n)`。由于有界量词本身就是构造子，有界性可以直接从公式的形状读出，而无需看其拼写。
<!--ja-->
量化子が一覧を締めくくります。その型は de Bruijn 束縛を正確に符号化しています。`∃̇_` と `∀̇_` は型 `Formula K (suc n)` の本体を受け取り、自由変数 `n` 個の論理式を返します。本体はさらに変数 `0`、すなわち今束縛されたものを参照できます。有界の形 `∀̇∈` と `∃̇∈` はさらに外側のスコープから項 `t` を受け取り、`t` の元にわたって動きます。本体はやはり `Formula K (suc n)` です。有界量化子がそれ自体構成子であるため、有界性は論理式の形から直接読み取れ、綴りから読む必要はありません。
<!--/-->

```agda
  ∃̇_ ∀̇_       : Formula K (suc n) → Formula K n
  ∀̇∈ ∃̇∈       : Term K n → Formula K (suc n) → Formula K n
```

<!--en-->
Negation is not a constructor but a defined symbol: `¬̇ φ` is definitionally `φ ⇒̇ ⊥̇`. Any function matching on a `¬̇_` therefore sees an implication to absurdity. The other derived symbols are defined in the same style.
<!--zh-->
否定不是构造子，而是定义出来的符号：`¬̇ φ` 定义上就是 `φ ⇒̇ ⊥̇`。因此任何对 `¬̇_` 做匹配的函数看到的都是指向荒谬的蕴涵。其余的导出符号也以同样方式定义。
<!--ja-->
否定は構成子ではなく定義された記号です。`¬̇ φ` は定義上 `φ ⇒̇ ⊥̇` です。したがって、`¬̇_` に対してマッチする関数が見るのは後件が `⊥̇` である含意です。その他の導出記号も同じやり方で定義されます。
<!--/-->

```agda

¬̇_ : ∀ {ℓ} {K : Type ℓ} {n} → Formula K n → Formula K n
¬̇ φ = φ ⇒̇ ⊥̇
```

<!--en-->
Truth is defined in the same style: `⊤̇` is `⊥̇ ⇒̇ ⊥̇`, implication from absurdity to absurdity. This chapter fixes that syntactic definition without imposing laws on a later truth-value interpretation. Both `¬̇_` and `⊤̇` are level-polymorphic in the same implicit way as the constructors, so they apply uniformly at every constant domain and every variable count.
<!--zh-->
真也以同样方式定义：`⊤̇` 即 `⊥̇ ⇒̇ ⊥̇`，从荒谬到荒谬的蕴涵。本章只固定这一语法定义，并不对后续的真值解释施加定律。`¬̇_` 与 `⊤̇` 和构造子一样对层级多态，在任何常元域与任何变量个数下都统一可用。
<!--ja-->
真も同じ仕方で定義されます。`⊤̇` は `⊥̇ ⇒̇ ⊥̇`、すなわち矛盾から矛盾への含意です。この章で定めるのはこの構文上の定義だけであり、後の真理値による解釈に法則を課すものではありません。`¬̇_` と `⊤̇` は構成子と同じくレベル多態的なので、任意の定数域と任意の変数の個数に対して一様に使えます。
<!--/-->

```agda

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

## Sentences and parameter-free formulas

A sentence has no free variables, while a parameter-free formula has no constants. These are independent restrictions, and the distinction becomes essential when formulas are coded and evaluated inside a model.

A **sentence** is a formula with no free variables; with intrinsic scoping this is a type, `Formula K 0`, not a side condition, and the book gives it no separate name. **Parameter-free formulas** restrict along a different, orthogonal axis. A constant is how an ambient set enters a formula as a parameter; here the constant domain is the empty type `⊥*`{.Agda}, so there are no parameters at all, while free variables remain; like sentences, this is just a type, `Formula ⊥* n`, with no separate name. From the empty type anything follows, so a parameter-free formula can enter the syntax over any domain whatsoever; the map that performs the entry lives with the constant-transformation kit at the book's tail. Parameter-free formulas are no rivals of the working syntax but its companions: a syntax whose constants are all sets is too big to be counted or coded, so whenever a later part needs formulas *as data*, theories as sets of formulas, codes of formulas inside a model, it is the parameter-free formulas that get collected, their parameters fed through environments instead.

## Recap

The inductive syntax records constants, free-variable arity, and quantifier scope in its types. Later chapters can therefore transform formulas while Agda checks that variables remain well scoped.

The object language is an inductive family `Formula K n`{.Agda}: constant domain as a parameter, scoping intrinsic through `Fin`{.Agda}, each constructor dotted. Around it: the parameter-free formulas, the data axis whose entry map arrives with the relabelling kit at the book's tail. Note what is absent: no substitution and no weakening operators anywhere. The design will keep it that way, and the little variable machinery the book does need arrives later in the book. First, formulas need something to talk about.
<!--zh-->
参数 `K` 让一族语法覆盖全书的所有用途：

| `K` 的取法 | 得到什么 |
|---|---|
| 某结构的载体 | 日常工作语法：任何集合都能以参数身份出现在公式里 |
| `⊥*`{.Agda} (无常元) | **无参公式**：可数、可编码，理论与码所在之处 |
| 受限制的载体 | 参数只许来自某个类；可构造宇宙诸章构造 `L` 用的正是这个形状 |

## 句子与无参公式

句子没有自由变量，无参公式没有常元。这是两项彼此独立的限制；当公式在模型内部被编码和求值时，这一区分至关重要。

**句子**是没有自由变量的公式；作用域既然内蕴，这是一个类型 `Formula K 0`，而非附加条件，本书不为它另设名字。**无参公式**限制的是另一条正交的轴。常元是外部集合以参数身份进入公式的通道；这里常元域取空类型 `⊥*`{.Agda}，参数于是全然没有，而自由变量照旧；与句子一样，这只是一个类型 `Formula ⊥* n`，本书不为它另设名字。从空类型可以推出一切，所以无参公式可以进入任意常元域上的语法；执行这次进入的映射编在书末的常元改名章里。无参公式不是工作语法的对手，而是它的同伴：常元囊括一切集合的语法太大，数不得也编不得码，因此后面各部凡需要把公式**当数据**用，理论作为公式的集合、模型内部的公式码，收集的都是无参公式，参数改经环境喂入。

## 小结

归纳语法在类型中记录常元、自由变量元数与量词作用域。因此后续章节变换公式时，Agda 能检查变量始终处于正确作用域。

对象语言是归纳族 `Formula K n`{.Agda}：常元域作参数，作用域经 `Fin`{.Agda} 内蕴，构造子全带点。与之配套的是无参公式，其进入映射由书末的常元改名工具组给出。值得注意的是，全篇没有替换算子，也没有弱化算子；这一设计将保持下去，本书所需的少量变量机件将在稍后引入。眼下，公式先得有可谈论的对象。
<!--ja-->
パラメータ `K` の選択により、一つの構文が本書で必要とされるすべての用途を覆います：

| `K` の選び方 | 得られるもの |
|---|---|
| 構造の台 | 日常の作業用構文：任意の集合がパラメータとして論理式に現れ得る |
| `⊥*`{.Agda} (定数なし) | **パラメータを持たない論理式**：可数で符号化可能であり、理論と符号がここに住む |
| 制限された台 | パラメータをあるクラスに限定する。構成可能宇宙の章で `L` を構成するときの形 |

## 文とパラメータを持たない論理式

文には自由変数がなく、パラメータを持たない論理式には定数がありません。この二つの条件は独立であり、モデル内部で論理式を符号化して評価するときに重要になります。

**文**とは自由変数を持たない論理式のことです。作用域が内在的であるため、これは追加の条件ではなく型 `Formula K 0` そのものであり、本書はこれに別の名前を与えません。**パラメータを持たない論理式**は、これとは直交する別の軸に沿った制限です。定数とは、周囲の集合がパラメータとして論理式に入り込むための通路です。ここでは定数域を空型 `⊥*`{.Agda} とするので、パラメータはまったくなく、自由変数はそのまま残ります。文と同様、これも単なる型 `Formula ⊥* n` であり、別の名前は持ちません。空型からは何でも導けるので、パラメータを持たない論理式は任意の定数域上の構文へ入り込むことができます。この入り込みを実行する写像は、本書末尾の定数の改名の道具立てとともに置かれます。パラメータを持たない論理式は作業用構文の競合相手ではなく、その仲間です。定数としてすべての集合を許す構文は大きすぎて、数え上げることも符号化することもできません。それゆえ、後の部分で論理式を**データとして**扱うとき、つまり理論を論理式の集合として、あるいはモデル内部の論理式の符号として扱うとき、集められるのは常にパラメータを持たない論理式であり、そのパラメータは代わりに環境を通じて供給されます。

## まとめ

帰納的な構文は、定数、自由変数の個数、量化子の作用域を型に記録します。そのため後の章で論理式を変換するとき、変数の作用域が正しいことを Agda が検査できます。

対象言語は帰納的な族 `Formula K n`{.Agda} です。定数域をパラメータとし、作用域は `Fin`{.Agda} によって内在的に記録され、各構成子は点付きです。これを支えるのがパラメータを持たない論理式であり、その入り込みの写像は本書末尾の定数の改名の道具立てとともに現れます。注目すべきは、ここに置かれていないものです。代入も弱化も、どの演算子も本書のどこにもありません。この設計はそのまま保たれ、本書が実際に必要とするわずかな変数の機構は後の章で導入されます。まずは、論理式が語るべき対象が必要です。
<!--/-->
