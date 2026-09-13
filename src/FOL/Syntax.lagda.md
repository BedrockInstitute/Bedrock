<!--en-->
# The object language

Set theory talks about sets, but to prove theorems about set theory itself, its statements must first become mathematical objects in their own right: expressions put together by explicit rules rather than informal convention. This chapter defines that object language by fixing the available constant names, the variable positions that may be referred to, and the rules for forming terms and formulas. The central decision concerns scope. The length of an expression's free-variable context is part of its type, so a reference beyond that context is impossible to write, not merely forbidden.
<!--zh-->
# 对象语言

集合论谈论集合，而要证明关于集合论本身的定理，它的语句必须先成为独立的数学对象，即按明确规则构造的表达式，而不是只靠约定形成的记号。本章定义这个对象语言，确定有哪些常元名、可以指涉哪些变量位置，以及词项与公式的形成规则。全章的中心决定关乎作用域：表达式的自由变量语境长度属于其自身类型，超出该语境的引用根本无法写出，而不只是不被允许。
<!--ja-->
# 対象言語

集合論は集合について語ります。しかし集合論そのものについて定理を証明するには、その文が、明示的な規則で組み立てられる式として、それ自体の数学的対象でなければなりません。この章ではその対象言語を定義し、利用できる定数名、参照できる変数位置、そして項と論理式の形成規則を定めます。本章の中心となる決定は作用域をめぐるものです。式の自由変数文脈の長さはその式自身の型の一部であり、その文脈を超える参照は、禁じられているというより、そもそも書けません。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}
```

<!--en-->
Each formula is written against a finite context of free variables, and the length of that context, a natural number `n`, belongs to the formula's type. A variable is an element of `Fin n`{.Agda}, the type of positions `0` through `n - 1`. The point becomes visible when a quantifier is formed: its body has one more available variable position than the quantified formula itself, so the index grows from `n` to `suc n`. A term therefore cannot mention a variable outside its context, because no such position exists.
<!--zh-->
每条公式都写在一个有限的自由变量语境上，语境的长度，即自然数 `n`，属于公式自身的类型。变量是 `Fin n`{.Agda} 的元素，即位置 `0` 到 `n - 1`。形成量词时，这个设计便直接显现出来：量词的公式体比量化所得的公式多一个可用变量位置，指标随之从 `n` 增到 `suc n`。词项因此不可能提到语境之外的变量，因为那样的位置并不存在。
<!--ja-->
各論理式は有限の自由変数文脈の上に書かれ、その長さにあたる自然数 `n` は論理式自身の型の一部です。変数は `Fin n`{.Agda} の元、つまり位置 `0` から `n - 1` までです。量化子を形成すると、この設計がそのまま現れます。量化子の本体には、量化して得られる論理式より利用できる変数位置が一つ多いため、添字は `n` から `suc n` へ進みます。したがって項は文脈の外の変数に言及できません。そのような位置は存在しないからです。
<!--/-->

```agda

module FOL.Syntax where
```

<!--en-->
Variables determine what a formula may refer to; constants determine what it may name. Besides the context length `n`, a formula is formulated over an arbitrary type `K` of constant symbols, the **constant domain**. The type `K` is chosen once for the whole language, so the names available within a formula never change. These two choices are independent: `K` determines which parameters may be named, while `n` determines how many variable positions may be used. Enlarging one leaves the other unchanged.
<!--zh-->
变量决定公式可以指涉什么，常元决定公式可以指名什么。除语境长度 `n` 外，公式还建立在任意的常元符号类型 `K` 上，`K` 即**常元域**。`K` 对整个语言只取定一次，因此一条公式内部可用的名字不会改变。这两个选取彼此独立：`K` 决定可以指名哪些参数，`n` 决定可以使用多少个变量位置；扩大其一不会影响另一者。
<!--ja-->
変数は論理式が何を参照できるかを決め、定数は何を名指せるかを決めます。文脈の長さ `n` のほかに、論理式は任意の定数記号の型 `K`、すなわち**定数域**の上で述べられます。`K` は言語全体に対して一度だけ選ばれるため、一つの論理式の中で使える名前が変わることはありません。この二つの選択は独立です。`K` は名指せるパラメータを、`n` は使える変数位置の個数を定め、一方を広げても他方は変わりません。
<!--/-->

```agda

open import Base.Prelude
```

<!--en-->
## Terms and formulas

Terms name the objects a formula can talk about, and formulas then assert things about those objects, so terms come first. A term is either a **constant**, a name drawn from `K`, or a **variable**, a position drawn from the `n` available positions. Formulas are built from such terms. They begin with the two atomic forms, membership and equality, and continue through the propositional connectives and the bounded and unbounded quantifiers.

Throughout the book, `t` and `u` range over terms, `φ` and `ψ` over formulas, `n` and `m` over context lengths, and `i` and `j` over variable indices.
<!--zh-->
## 词项与公式

词项指称公式所谈论的对象，公式再对这些对象作出断言，所以先讲词项。词项要么是**常元**，即从 `K` 中取出的名字；要么是**变量**，即从 `n` 个可用位置中取出的一个位置。公式由这样的词项构造而成，起点是词项之间的隶属与相等这两个原子式，再由命题联结词以及有界、无界量词组合。

全书约定：`t`、`u` 表示词项，`φ`、`ψ` 表示公式，`n`、`m` 表示语境长度，`i`、`j` 表示变量索引。
<!--ja-->
## 項と論理式

項は論理式が語る対象を名指し、論理式はその対象について断言します。そこでまず項から始めます。項は、`K` から取った名前である**定数**か、利用可能な `n` 個の位置から取った**変数**のいずれかです。論理式はこのような項から組み立てられます。出発点は項の間の所属と等号という二つの原子式で、そこへ命題結合子と、有界・非有界の量化子が加わります。

本書を通して、`t` と `u` は項を、`φ` と `ψ` は論理式を、`n` と `m` は文脈の長さを、`i` と `j` は変数の添字を表します。
<!--/-->

<!--en-->
Here `Term` is a family of types: choosing a type `K` and a number `n` yields a type `Term K n`, and a term never comes without both. Since a term is nothing more than a name from `K` or a number below `n`, the whole family lives at the same universe level `ℓ` as `K` itself.
<!--zh-->
这里 `Term` 是一个类型族：选定类型 `K` 与数 `n`，便得到类型 `Term K n`，词项从不脱离这二者而存在。词项无非是 `K` 中的一个名字或小于 `n` 的一个数，因此整个族与 `K` 同居宇宙层级 `ℓ`。
<!--ja-->
ここで `Term` は型の族です。型 `K` と数 `n` を選ぶと型 `Term K n` が得られ、項がこの二つなしに現れることはありません。項は `K` の元である名前か `n` 未満の数にすぎないので、族全体は `K` と同じ宇宙レベル `ℓ` に置かれます。
<!--/-->

```agda
data Term {ℓ} (K : Type ℓ) (n : ℕ) : Type ℓ where
```

<!--en-->
The constructor `con` takes an element `c : K` and treats it purely as a name. It has no meaning yet; only an interpretation can determine what it denotes. The constructor `var i` selects the position `i` from `Fin n`. With `n = 2`, the expressions `var 0`, `var 1`, and `con c` are terms of `Term K 2`, while `var 2` is unavailable: `Fin 2`{.Agda} has no element named `2`, so this is an expression that cannot be formed, rather than a term rejected by a later check.

The number `n` determines which positions may be named, not how often they are used. The terms `con c` and `var 0` both have type `Term K 2` although neither mentions two variables, and a formula may use a single position more than once. Formulas will be built from terms of just this kind.
<!--zh-->
构造子 `con` 取 `K` 的一个元素 `c`，只把它当作名字。这个名字暂时没有含义，要等解释给出以后才知道它指称什么。构造子 `var i` 从 `Fin n` 中选出位置 `i`。取 `n = 2` 时，`var 0`、`var 1` 与 `con c` 都是 `Term K 2` 中的词项，而 `var 2` 无法写出：`Fin 2`{.Agda} 中没有名为 `2` 的元素，所以它不是会被事后检查退回的词项，而是根本无法形成的表达式。

自然数 `n` 决定哪些位置可以被指名，而不是它们被使用的次数。`con c` 与 `var 0` 的类型都是 `Term K 2`，尽管二者都没有提到两个变量；一条公式也可以多次使用同一个位置。公式正是由这样的词项构造而成。
<!--ja-->
構成子 `con` は `K` の元 `c` を受け取り、それを純粋に名前として扱います。名前はまだ何も意味しておらず、何を指示するかが分かるのは解釈が与えられてからです。構成子 `var i` は `Fin n` から位置 `i` を選びます。`n = 2` のとき、`var 0`、`var 1`、`con c` はいずれも `Term K 2` の項ですが、`var 2` は書けません。`Fin 2`{.Agda} に `2` という名の元は存在しないので、これは後の検査で退けられる項ではなく、形成できない式です。

自然数 `n` が定めるのは、どの位置を名指せるかであって、位置が何回使われるかではありません。`con c` も `var 0` も二つの変数に言及しないまま型 `Term K 2` を持ち、論理式が一つの位置を何度も使ってもかまいません。論理式はこの種の項から組み立てられます。
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
