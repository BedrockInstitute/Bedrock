<!--en-->
# The object language

Set theory talks about sets, but to prove theorems about set theory itself, its statements must first become mathematical objects in their own right: expressions put together by explicit rules rather than informal convention. This chapter defines that object language by fixing the available constant names, the variable positions that may be referred to, and the rules for forming terms and formulas. The central decision concerns scope. The length of an expression's free-variable context is part of its type, so a reference beyond that context is impossible to write, not merely forbidden.
<!--zh-->
# 对象语言

集合论谈论集合，而要证明关于集合论本身的定理，它的语句必须先成为独立的数学对象，即按明确规则构造的表达式，而不是只靠约定形成的记号。本章定义这个对象语言，确定有哪些常元名、可以指涉哪些变量位置，以及词项与公式的形成规则。全章的中心决定关乎作用域：表达式的自由变量语境长度属于其自身类型，超出该语境的引用根本无法写出，而不只是不被允许。
<!--ja-->
# 対象言語

集合論は集合について語る。しかし集合論そのものについて定理を証明するには、その文が、明示的な規則で組み立てられる式として、それ自体の数学的対象でなければならない。この章ではその対象言語を定義し、利用できる定数名、参照できる変数位置、そして項と論理式の形成規則を定める。本章の中心となる決定は作用域をめぐるものである。式の自由変数文脈の長さはその式自身の型の一部であり、その文脈を超える参照は、禁じられているというより、そもそも書けない。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}
```

<!--en-->
Each formula is written against a finite context of free variables, and the length of that context, a natural number `n`, belongs to the formula's type. A variable is an element of `Fin n`{.Agda}, the type of positions `0` through `n - 1`. The point becomes visible when a quantifier is formed: its body has one more available variable position than the quantified formula itself, so the index grows from `n` to `suc n`. A term therefore cannot mention a variable outside its context, because no such position exists.
<!--zh-->
每条公式都写在一个有限的自由变量语境上，语境的长度，即自然数 `n`，属于公式自身的类型。变量是 `Fin n`{.Agda} 的元素，即位置 `0` 到 `n - 1`。形成量词时，这个设计便直接显现出来：量词的公式体比量化所得的公式多一个可用变量位置，指标随之从 `n` 增到 `suc n`。词项因此不可能提到语境之外的变量，因为那样的位置并不存在。
<!--ja-->
各論理式は有限の自由変数文脈の上に書かれ、その長さにあたる自然数 `n` は論理式自身の型の一部である。変数は `Fin n`{.Agda} の元、つまり位置 `0` から `n - 1` までである。量化子を形成すると、この設計がそのまま現れる。量化子の本体には、量化して得られる論理式より利用できる変数位置が一つ多いため、添字は `n` から `suc n` へ進む。したがって項は文脈の外の変数に言及できない。そのような位置は存在しないからである。
<!--/-->

```agda

module FOL.Syntax where
```

<!--en-->
Variables determine what a formula may refer to; constants determine what it may name. Besides the context length `n`, a formula is formulated over an arbitrary type `K` of constant symbols, the **constant domain**. The type `K` is chosen once for the whole language, so the names available within a formula never change. These two choices are independent: `K` determines which parameters may be named, while `n` determines how many variable positions may be used. Enlarging one leaves the other unchanged.
<!--zh-->
变量决定公式可以指涉什么，常元决定公式可以指名什么。除语境长度 `n` 外，公式还建立在任意的常元符号类型 `K` 上，`K` 即**常元域**。`K` 对整个语言只取定一次，因此一条公式内部可用的名字不会改变。这两个选取彼此独立：`K` 决定可以指名哪些参数，`n` 决定可以使用多少个变量位置；扩大其一不会影响另一者。
<!--ja-->
変数は論理式が何を参照できるかを決め、定数は何を名指せるかを決める。文脈の長さ `n` のほかに、論理式は任意の定数記号の型 `K`、すなわち**定数域**の上で述べられる。`K` は言語全体に対して一度だけ選ばれるため、一つの論理式の中で使える名前が変わることはない。この二つの選択は独立である。`K` は名指せるパラメータを、`n` は使える変数位置の個数を定め、一方を広げても他方は変わらない。
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

項は論理式が語る対象を名指し、論理式はその対象について断言する。そこでまず項から始める。項は、`K` から取った名前である**定数**か、利用可能な `n` 個の位置から取った**変数**のいずれかである。論理式はこのような項から組み立てられる。出発点は項の間の所属と等号という二つの原子式で、そこへ命題結合子と、有界・非有界の量化子が加わる。

本書を通して、`t` と `u` は項を、`φ` と `ψ` は論理式を、`n` と `m` は文脈の長さを、`i` と `j` は変数の添字を表す。
<!--/-->

<!--en-->
Here `Term` is a family of types: choosing a type `K` and a number `n` yields a type `Term K n`, and a term never comes without both. Since a term is nothing more than a name from `K` or a number below `n`, the whole family lives at the same universe level `ℓ` as `K` itself.
<!--zh-->
这里 `Term` 是一个类型族：选定类型 `K` 与数 `n`，便得到类型 `Term K n`，词项从不脱离这二者而存在。词项无非是 `K` 中的一个名字或小于 `n` 的一个数，因此整个族与 `K` 同居宇宙层级 `ℓ`。
<!--ja-->
ここで `Term` は型の族である。型 `K` と数 `n` を選ぶと型 `Term K n` が得られ、項がこの二つなしに現れることはない。項は `K` の元である名前か `n` 未満の数にすぎないので、族全体は `K` と同じ宇宙レベル `ℓ` に置かれる。
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
構成子 `con` は `K` の元 `c` を受け取り、それを純粋に名前として扱う。名前はまだ何も意味しておらず、何を指示するかが分かるのは解釈が与えられてからである。構成子 `var i` は `Fin n` から位置 `i` を選ぶ。`n = 2` のとき、`var 0`、`var 1`、`con c` はいずれも `Term K 2` の項であるが、`var 2` は書けない。`Fin 2`{.Agda} に `2` という名の元は存在しないので、これは後の検査で退けられる項ではなく、形成できない式である。

自然数 `n` が定めるのは、どの位置を名指せるかであって、位置が何回使われるかではない。`con c` も `var 0` も二つの変数に言及しないまま型 `Term K 2` を持ち、論理式が一つの位置を何度も使ってもかまわない。論理式はこの種の項から組み立てられる。
<!--/-->

```agda
  con : K → Term K n
  var : Fin n → Term K n
```

<!--en-->
Formulas are the assertions, as terms were the names. The smallest assertions are the atoms `_∈̇_` and `_≐_`: that one term is a member of another, or that two terms are equal. From atoms, the connectives `∧̇ ∨̇ ⇒̇ ¬̇ ⊤̇ ⊥̇` build compound statements, and the quantifiers `∃̇ ∀̇` range over all objects. Alongside them, `∀̇∈` and `∃̇∈` are the **bounded** quantifiers, read 'for every member of' and 'for some member of'. Every one of these symbols carries a small upper dot. The dot is a layer mark: `∈̇` speaks of membership as the object language states it, one layer removed from the membership relation of the surrounding theory, and a dotted symbol is always syntax rather than meaning.

A quantifier binds a variable, and the syntax records this in the index. Its body has one more available variable position than the quantified formula, and position `0` in the body is the variable just bound. Which occurrences fall under the quantifier is thereby fixed by position alone, in the de Bruijn manner; no name is stored in the formula, so these formation rules need no convention for α-renaming or for distinguishing identically named variables. Nothing in the formula marks whether that extra position is actually used.
<!--zh-->
词项是名字，公式则是断言。最小的断言是原子式 `_∈̇_` 与 `_≐_`：一个词项属于另一个词项，或者两个词项相等。联结词 `∧̇ ∨̇ ⇒̇ ¬̇ ⊤̇ ⊥̇` 由原子式构成复合的陈述，量词 `∃̇ ∀̇` 则遍及一切对象。与之并列，`∀̇∈` 与 `∃̇∈` 是**有界**量词，读作「对……的每个成员」与「对……的某个成员」。这些符号都带一个小小的上点。点是层标记：`∈̇` 说的是对象语言所述的隶属，与周围理论的隶属关系相隔一层；带点的符号永远是语法，而不是含义。

量词约束变量，语法把这个事实记进指标。其公式体比量化后的公式多一个可用变量位置，公式体中的位置 `0` 就是刚被约束的那个变量。哪些出现落在量词的管辖之下，由此仅凭位置确定，这就是 de Bruijn 方式；公式内部不存放名字，因此这些形成规则无需约定 α 改名，也无需区分同名变量。公式本身并不标记那个多出的位置是否真的被使用。
<!--ja-->
項が名前であるのに対し、論理式は断言である。最小の断言が原子式 `_∈̇_` と `_≐_` である。ある項が別の項に属すること、あるいは二つの項が等しいことを述べる。結合子 `∧̇ ∨̇ ⇒̇ ¬̇ ⊤̇ ⊥̇` は原子式から複合的な主張を組み立て、量化子 `∃̇ ∀̇` はすべての対象にわたる。並んで、`∀̇∈` と `∃̇∈` は**有界**量化子で、それぞれ「…のすべての元について」「…のある元について」と読む。これらの記号はみな小さな上付きの点を帯ぶ。点は層の印である。`∈̇` が述べるのは対象言語のいう所属であり、周囲の理論の所属関係から一層だけ離れている。点付きの記号はつねに構文であって、意味ではない。

量化子は変数を束縛する。構文はこの事実を添字に記録する。本体には、量化して得られる論理式より一つ多い利用可能な変数位置があり、本体における位置 `0` が今束縛された変数である。どの出現が量化子の支配下にあるかは、位置だけで定まる。これが de Bruijn 方式である。論理式の内部に名前は保存されないので、この形成規則には α 改名や同名の変数を区別する約束が要らない。その余分な位置が実際に使われるかどうかを、論理式は記録しない。
<!--/-->

<!--en-->
Written inline, compound formulas need an agreed reading order, and these four lines settle it once for the whole object layer. Atoms and negation bind tightest, at levels 18 and 13. Conjunction and disjunction sit in the middle at level 12 and implication weakest at level 10, both pairs right-associative, so a chain `φ ⇒̇ ψ ⇒̇ θ` reads as `φ ⇒̇ (ψ ⇒̇ θ)`, the customary grouping for iterated implication. These are conventions of parsing, not additions to the language; with them, a nested formula reads the way ordinary mathematical prose does, and parentheses appear only where a different grouping is meant. This is the book's single declaration of the object layer's reading levels.
<!--zh-->
复合公式写成一行时，需要商定阅读的次序，这四行把它一次定下，对整个对象层有效。原子式与否定结合得最紧，层级 18 与 13。合取与析取居中，层级 12；蕴涵最弱，层级 10；两对都右结合，于是 `φ ⇒̇ ψ ⇒̇ θ` 读作 `φ ⇒̇ (ψ ⇒̇ θ)`，正是迭代蕴涵的通常分组。这些是解析上的约定，不给语言增添任何东西；有了它们，嵌套公式按普通数学行文的样子即可读清，只有想要的分组不同时才需要括号。这是全书对对象层读取层级的唯一一次宣告。
<!--ja-->
複合論理式を一行に書けば、読む順序を取り決めておく必要がある。この 4 行がそれを一度に定め、対象レイヤー全体に及ぶ。原子式と否定が最も強く結合し、その水準は 18 と 13 である。連言と選言は中央の水準 12、含意は最も弱い水準 10 で、二組の対はいずれも右結合である。したがって `φ ⇒̇ ψ ⇒̇ θ` は `φ ⇒̇ (ψ ⇒̇ θ)` と読まれ、これは反復含意の通常のグループ化である。これらは構文解析上の約束であって、言語への追加ではない。おかげで入れ子の論理式は普通の数学の文章と同じように読め、括弧は異なるグループ化を意図するときにだけ現れる。対象レイヤーの読みの水準を宣言するのは、本書でここ一度きりである。
<!--/-->

```agda
infix  18 _≐_ _∈̇_
infixr 12 _∧̇_ _∨̇_
infixr 10 _⇒̇_
infix  13 ¬̇_
```

<!--en-->
The family `Formula` is indexed exactly like `Term`, by a constant domain `K` and a count `n` of available variable positions. The atoms `_∈̇_` and `_≐_` take two terms of `Term K n` and assert membership or equality between them. The propositional constructors go from formulas to formulas: `_∧̇_`, `_∨̇_` and `_⇒̇_` form conjunction, disjunction and implication, and `⊥̇` is falsity itself. None of them binds or releases a variable, which is why the index stays at `n`; quantifiers change it only when they bind a variable.

That the connectives are constructors rather than abbreviations is a deliberate choice with a semantic reason. Formulas will eventually be read in the host's proposition type `hProp`, and each connective is interpreted by its corresponding direct operation there, not by reduction to other symbols. A classical text can economize, spelling `φ ∨̇ ψ` as `¬̇ (¬̇ φ ∧̇ ¬̇ ψ)`, `∀̇` as `¬̇ ∃̇ ¬̇`, or `φ ⇒̇ ψ` as `¬̇ φ ∨̇ ψ`, because classically double negations cancel. Constructively no such cancellation is generally available, and the substitutions would not deliver the intended meanings. This book therefore keeps `∨̇`, `⇒̇` and the quantifiers as constructors in their own right.
<!--zh-->
`Formula` 族与 `Term` 的索引方式完全相同：常元域 `K` 与可用变量位置的个数 `n`。原子式 `_∈̇_` 与 `_≐_` 取 `Term K n` 中的两个词项，断言它们之间的隶属或相等。命题构造子由公式得到公式：`_∧̇_`、`_∨̇_`、`_⇒̇_` 构成合取、析取与蕴涵，`⊥̇` 就是假本身。它们都不约束也不释放变量，所以指标始终停在 `n`；只有量词在约束变量时才会改变它。

联结词取作构造子而非缩写，是带有语义理由的决定。公式最终要在宿主的命题类型 `hProp` 中被解读，每个联结词都由那里相应的直接运算解释，而不化归为别的符号。经典教科书可以省事，把 `φ ∨̇ ψ` 拼成 `¬̇ (¬̇ φ ∧̇ ¬̇ ψ)`、把 `∀̇` 拼成 `¬̇ ∃̇ ¬̇`、把 `φ ⇒̇ ψ` 拼成 `¬̇ φ ∨̇ ψ`，因为经典逻辑里双重否定会消去。构造性地看，这种消去并非一般可得，替换后的写法给不出想要的含义。因此本书将 `∨̇`、`⇒̇` 与量词直接取为构造子。
<!--ja-->
`Formula` 族は `Term` とまったく同じやり方で、定数域 `K` と利用可能な変数位置の個数 `n` で添字づけられる。原子式 `_∈̇_` と `_≐_` は `Term K n` の二つの項を受け取り、それらの間の所属か等号を断言する。命題的な構成子は、論理式から論理式を作る。`_∧̇_`、`_∨̇_`、`_⇒̇_` は連言、選言、含意を構成し、`⊥̇` は偽そのものである。どれも変数を束縛も解放もしない。だから添字はずっと `n` のままであり、量化子が変数を束縛するときにだけ、この添字が変わる。

結合子を略語ではなく構成子とするのは、意味論的な理由のある決定である。論理式は最終的にホストの命題の型 `hProp` の中で読まれ、各結合子はそこで対応する直接的な演算によって解釈される。他の記号への還元ではない。古典的な教科書は `φ ∨̇ ψ` を `¬̇ (¬̇ φ ∧̇ ¬̇ ψ)`、`∀̇` を `¬̇ ∃̇ ¬̇`、`φ ⇒̇ ψ` を `¬̇ φ ∨̇ ψ` と書き替えて済ませられる。古典論理では二重否定が消えるからである。構成的にはこの消去は一般には使えないので、書き替えた形は望ましい意味を持たない。そこで本書は `∨̇`、`⇒̇`、そして量化子を、そのまま構成子として採る。
<!--/-->

```agda

data Formula {ℓ} (K : Type ℓ) (n : ℕ) : Type ℓ where
  _∈̇_ _≐_     : Term K n → Term K n → Formula K n
  _∧̇_ _∨̇_ _⇒̇_ : Formula K n → Formula K n → Formula K n
  ⊥̇            : Formula K n
```

<!--en-->
The types of the quantifiers state binding precisely. `∃̇_` and `∀̇_` take a body of type `Formula K (suc n)` and return a formula over `n` positions: the body has one more position at its disposal, position `0`, and that is the variable the quantifier binds. The extra position is available, not obliged; a body that never mentions it is a legitimate formula. The bounded forms `∀̇∈` and `∃̇∈` read as 'for every member of' and 'for some member of'. Their bound `t` is a term of the outer context, from `Term K n`, and quantification ranges over the members of `t`; the body is again `Formula K (suc n)`.

The bounded quantifiers could have been spelled with the plain ones, and keeping them as constructors is a second deliberate choice, this time for a reason about syntax itself. Had `∀̇∈ t φ` been an abbreviation, the statement that every quantifier in `φ` is bounded would be a fact about how `φ` happens to be written, invisible to anything that computes over `φ`'s shape. As constructors, boundedness belongs to the shape. Later chapters classify formulas by a datatype with one case per constructor, and certify that all quantifiers are bounded by a datatype having no case for `∃̇` and `∀̇` at all; such a certificate is possible only because the bounded forms are given independently. Formulas of this shape behave well across structures, a thread the model chapters take up and the chapters on the constructible universe carry on.
<!--zh-->
量词的类型精确陈述了约束。`∃̇_` 与 `∀̇_` 取类型为 `Formula K (suc n)` 的公式体，返回 `n` 个位置上的公式：公式体多出一个可支配的位置，即位置 `0`，这正是量词约束的变量。多出的位置只是可用，并非必须；从不提及它的公式体也是合法的公式。有界形式 `∀̇∈` 与 `∃̇∈` 读作「对……的每个成员」与「对……的某个成员」。它们的界限 `t` 是外层语境中的词项，即 `Term K n` 的词项，量化遍及 `t` 的成员；公式体同样是 `Formula K (suc n)`。

有界量词本可用普通量词拼出，仍将其保留为构造子是第二个刻意的决定，这次的理由关乎语法本身。倘若 `∀̇∈ t φ` 只是缩写，「`φ` 的每个量词都有界」就成了关于 `φ` 恰巧如何拼写的事实，任何按 `φ` 形状进行计算的过程都看不见它。作为构造子，有界性属于形状。后续章节将用一个对每个构造子恰设一个情形的数据类型给公式分类，并以一个对 `∃̇` 与 `∀̇` 全然不设情形的数据类型证明所有量词皆有界；这样的证书之所以可能，正因为有界形式是独立给出的。这种形状的公式在不同结构之间表现良好，模型诸章将接手这条线索，可构造宇宙诸章会把它继续下去。
<!--ja-->
量化子の型は、束縛を正確に述べている。`∃̇_` と `∀̇_` は型 `Formula K (suc n)` の本体を受け取り、`n` 個の位置の上の論理式を返す。本体にはもう一つの利用できる位置、すなわち位置 `0` があり、これこそ量化子が束縛する変数である。この余分な位置は利用できるだけで、使う義務はない。それに触れない本体も正当な論理式である。有界の形 `∀̇∈` と `∃̇∈` は、それぞれ「…のすべての元について」「…のある元について」と読む。限界 `t` は外側の文脈の項、すなわち `Term K n` の項であり、量化は `t` の元にわたって行われる。本体はやはり `Formula K (suc n)` である。

有界量化子は普通の量化子で書き表せるのに、構成子として保つのは第二の決定である。今度の理由は構文そのものに関わる。もし `∀̇∈ t φ` が略語なら、「`φ` のすべての量化子が有界である」は `φ` がたまたまどう書かれているかについての事実となり、`φ` の形の上を計算する何物からも見えない。構成子としてなら、有界性は形に属する。後の章では、構成子ごとに場合を一つ持つデータ型で論理式を分類し、`∃̇` と `∀̇` には場合をまったく持たないデータ型によって「量化子はすべて有界」を証明する。そのような証明が可能なのは、有界の形が独立に与えられているからである。この形の論理式は構造を越えてよく振る舞い、この系はモデルの章が受け取り、構成可能宇宙の章へと引き継がれる。
<!--/-->

```agda
  ∃̇_ ∀̇_       : Formula K (suc n) → Formula K n
  ∀̇∈ ∃̇∈       : Term K n → Formula K (suc n) → Formula K n
```

<!--en-->
Negation is not a constructor but a defined symbol: `¬̇ φ` is, by definition, `φ ⇒̇ ⊥̇`. The definition has a visible consequence for computation. A function matching on formulas never encounters a negation as such; it encounters an implication whose consequent is `⊥̇`, and the clause prepared for `_⇒̇_` already covers the case. No separate clause for negation will ever be needed, not even in the semantics.
<!--zh-->
否定不是构造子，而是定义出来的符号：`¬̇ φ` 按定义就是 `φ ⇒̇ ⊥̇`。这个定义有一个可见的计算后果。对公式做匹配的函数遇到的并非否定本身，而是后件为 `⊥̇` 的蕴涵，为 `_⇒̇_` 准备的子句已经覆盖了它。因此永远不必为否定单写子句，语义也不例外。
<!--ja-->
否定は構成子ではなく、定義された記号である。`¬̇ φ` とは定義により `φ ⇒̇ ⊥̇` のことである。この定義には計算上の帰結がある。論理式に対して場合分けする関数が出会うのは否定そのものではなく、後件が `⊥̇` である含意である。`_⇒̇_` のために用意した場合がすでにこれを取り扱う。したがって否定のための独立した場合が今後必要になることはなく、意味論においても同様である。
<!--/-->

```agda

¬̇_ : ∀ {ℓ} {K : Type ℓ} {n} → Formula K n → Formula K n
¬̇ φ = φ ⇒̇ ⊥̇
```

<!--en-->
Truth is defined in the same style: `⊤̇` is `⊥̇ ⇒̇ ⊥̇`, the implication from absurdity to absurdity. Beyond the syntax, nothing is assumed, and the chapter imposes no law on how these symbols will later be read. Since the definitions unfold into constructors, an interpretation handles them by its existing clauses for `_⇒̇_`, with nothing special to arrange. Like the constructors, `¬̇_` and `⊤̇` take the universe level and `K` as implicit arguments, so the same two symbols serve at every constant domain and every variable count.
<!--zh-->
真以同样方式定义：`⊤̇` 即 `⊥̇ ⇒̇ ⊥̇`，从荒谬到荒谬的蕴涵。语法之外别无假设，本章也不为这些符号日后的解读施加任何定律。既然定义会展开为构造子，解释只需用它处理 `_⇒̇_` 的既有子句来对待它们，无须任何特别安排。与构造子一样，`¬̇_` 与 `⊤̇` 把宇宙层级与 `K` 作为隐式参数，同一对符号因此在每个常元域、每个变量个数下都可用。
<!--ja-->
真も同じ仕方で定義される。`⊤̇` とは `⊥̇ ⇒̇ ⊥̇`、すなわち矛盾から矛盾への含意である。構文のほかには何も仮定せず、本章はこれらの記号の今後の読み方に法則を課さない。定義は構成子へと展開されるので、解釈は `_⇒̇_` のための既存の場合によってそれらを扱い、特別な用意は要らない。構成子と同じく、`¬̇_` と `⊤̇` は宇宙レベルと `K` を暗黙の引数として受け取り、同じ二つの記号がすべての定数域とすべての変数の個数で働く。
<!--/-->

```agda

⊤̇ : ∀ {ℓ} {K : Type ℓ} {n} → Formula K n
⊤̇ = ⊥̇ ⇒̇ ⊥̇
```

<!--en-->
A single syntax serves every use the book will make of it; the freedom lies in the choice of the constant domain `K`:

| choice of `K` | what it gives |
|---|---|
| the carrier of a structure | the working syntax: any set may appear in a formula as a parameter |
| `⊥*`{.Agda} (no constants) | the **parameter-free formulas**: countable and codable independently of ambient parameters |
| a restricted carrier | parameters confined to a class; the shape the constructible-universe development builds `L` with |

## Sentences and parameter-free formulas

A sentence has no free variables; a parameter-free formula has no constants. The two restrictions are independent, and the difference matters as soon as formulas are coded and evaluated inside a model.

A **sentence** is a formula with no free variables. Intrinsic scoping makes this a type, `Formula K 0`, rather than a side condition, and the book gives it no separate name. **Parameter-free formulas** restrict along the other axis: the constant domain is the empty type `⊥*`{.Agda}, so no parameter can be named, while free variables remain. This too is simply a type, `Formula ⊥* n`, with no separate name of its own. Because a function out of the empty type exists for every `K`, a parameter-free formula can be read over any constant domain, and the relabelling kit supplies exactly that map. Parameter-free formulas are useful when syntax must be enumerated without first enumerating the surrounding sets; parameters can then be supplied through an environment. They are not the only formulas that can be coded. The coding developed later also treats `Formula S n` directly, including constants drawn from the carrier `S`.

## Recap

The inductive syntax records the constant domain, the length of the free-variable context, and quantifier scope in its types, so later chapters can transform formulas while Agda checks that variables stay in scope.

The object language is the inductive family `Formula K n`{.Agda}: the constant domain as a parameter, scoping intrinsic through `Fin`{.Agda}, every constructor dotted. Alongside it stand the parameter-free formulas, with their entry map in the relabelling kit. Note what is absent: no substitution and no weakening appear anywhere. The design will keep it that way, and what little the book needs for handling variables arrives in later chapters. First, formulas need objects to talk about.
<!--zh-->
一套语法服务全书的每一种用途；自由度在于常元域 `K` 的取法：

| `K` 的取法 | 得到什么 |
|---|---|
| 某结构的载体 | 日常工作语法：任何集合都能以参数身份出现在公式里 |
| `⊥*`{.Agda} (无常元) | **无参公式**：不依赖周围的集合参数即可计数和编码 |
| 受限制的载体 | 参数只许来自某个类；可构造宇宙诸章构造 `L` 用的正是这个形状 |

## 句子与无参公式

句子没有自由变量，无参公式没有常元。两项限制彼此独立；一旦公式要在模型内部被编码和求值，这个区分就变得关键。

**句子**是没有自由变量的公式。作用域既然内蕴，这就是一个类型 `Formula K 0`，而非附加条件，本书不为它另设名字。**无参公式**则沿另一条轴限制：常元域取空类型 `⊥*`{.Agda}，任何参数都无从指名，而自由变量照旧。它同样只是一个类型 `Formula ⊥* n`，没有单独的名字。从空类型出发的函数对任何 `K` 都存在，所以无参公式可以在任何常元域上被解读，常元改名工具组给出的正是这个映射。当语法需要在不先枚举周围集合的前提下被枚举时，无参公式尤其有用，参数可以改由环境提供。但可编码的并不只有无参公式；后面的编码也直接处理 `Formula S n`，其中包括取自载体 `S` 的常元。

## 小结

词项与公式共同把作用域纳入形成规则本身。常元域 `K` 决定可以指名哪些参数，`n` 决定可以使用哪些自由变量位置；二者都不表示名字实际出现的次数。量词只改变公式体的语境长度，de Bruijn 位置则无需变量名便能确定被约束的变量。分别令 `n` 或 `K` 取空的情形，就得到句子或无参公式，两项限制因而始终清楚地彼此独立。
<!--ja-->
一つの構文が本書のあらゆる用途に仕える。自由度は、定数域 `K` の選び方にある：

| `K` の選び方 | 得られるもの |
|---|---|
| 構造の台 | 日常の作業用構文：任意の集合がパラメータとして論理式に現れ得る |
| `⊥*`{.Agda} (定数なし) | **パラメータを持たない論理式**：周囲のパラメータに依存せず可算で符号化できる |
| 制限された台 | パラメータをあるクラスに限定する。構成可能宇宙の章で `L` を構成するときの形 |

## 文とパラメータを持たない論理式

文には自由変数がなく、パラメータを持たない論理式には定数がない。この二つの制限は独立であり、論理式をモデルの内部で符号化して評価する段階になると、この違いが決定的になる。

**文**とは、自由変数を持たない論理式のことである。作用域が内在的であるため、これは追加条件ではなく型 `Formula K 0` そのものであり、本書は別の名前を与えない。**パラメータを持たない論理式**は、別の軸に沿った制限である。定数域を空型 `⊥*`{.Agda} とすれば、名指せるパラメータは一つもなく、自由変数はそのまま残る。これも単なる型 `Formula ⊥* n` であって、独自の名前は持たない。空型からの関数は任意の `K` に対して存在するので、パラメータを持たない論理式はどんな定数域の上でも読むことができ、その映射を与えるのが定数の改名の道具立てである。周囲の集合を先に列挙せず構文を列挙したいとき、パラメータを持たない論理式が役立ち、パラメータは環境から与えられる。ただし、符号化できる論理式がこれだけというわけではない。後の符号化は、台 `S` から取る定数を含む `Formula S n` も直接扱う。

## まとめ

項と論理式は、作用域を形成規則そのものに組み込む。定数域 `K` は名指せるパラメータを定め、`n` は利用できる自由変数位置を定める。どちらも名前が実際に現れる回数を表すものではない。量化子が変えるのは本体の文脈の長さだけであり、de Bruijn 位置によって、名前を使わずに束縛される変数が定まる。`n` と `K` のどちらを空の場合にするかによって、文とパラメータを持たない論理式がそれぞれ得られ、二つの制限は明確に独立したままである。
<!--/-->
