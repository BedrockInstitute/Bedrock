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

Usually we write a claim about sets and ask whether it holds. Here we first ask a different question: what parts make up such a claim, and how can they be combined? Treating the written claim itself as a mathematical object, we build a small **object language**.
<!--zh-->

通常，我们写下一句关于集合的话，接着问它是否成立。本章先换一个问题：这句话由哪些部分组成，又能怎样与别的话组合？我们把写出的陈述本身当作数学对象，为此构造一种小型的**对象语言**。
<!--ja-->

通常、集合についての文を書き、それが成り立つかを問う。ここではまず別の問いを立てる。その文は何からできていて、ほかの文とどう組み合わせられるのか。書かれた主張そのものを数学的な対象として扱うため、小さな**対象言語**を作る。
<!--/-->

<!--en-->
We start with ways to refer to an object, then use those references to make claims, and finally add forms that say *for every* or *there exists*. At each step, the Agda code specifies which written forms are possible. What these forms mean, and whether a claim holds, comes later.
<!--zh-->
我们先看怎样指代一个对象，再用这些写法组成关于对象的陈述，最后加入表达「对每一个」和「存在某个」的写法。每一步的 Agda 代码都会规定哪些组合可以写出。至于这些写法指什么、陈述是否成立，则留待后文。
<!--ja-->
まず対象を指す書き方を用意し、それを使って対象についての主張を作り、最後に「すべての」や「ある」を表す書き方を加える。各段階の Agda コードは、どの組み合わせが書けるかを定める。それらが何を指し、主張が成り立つかどうかは、後で扱う。
<!--/-->

<!--en-->
## Terms

Before saying that one object belongs to another, we need a way to refer to each object. We might choose a name in advance, or leave a numbered place to be filled when the expression is used. A written form that refers to one object in either way is called a **term**.

Let `K`{.Agda} be the type of names chosen in advance. Its elements are **constant names**, and `K`{.Agda} is the **constant domain**. Let `n`{.Agda} count the numbered places currently available. Together these places form a **context**; each place is a **variable position**. The type `Fin n`{.Agda}, introduced in the Prelude, contains precisely the positions 0 through one less than `n`{.Agda}. Thus `Term K n`{.Agda} records the two ways an object can be referred to, before either kind of name has been given a meaning.
<!--zh-->
## 词项

要说一个对象属于另一个对象，先得有指代它们的写法。我们可以预先选好名字，也可以留出一个带编号的位置，等使用这条陈述时再填入对象。这样指代单个对象的写法称为**词项**。

用类型 `K`{.Agda} 收集预先选好的名字，其中的元素称为**常元名**，`K`{.Agda} 称为**常元域**。再用自然数 `n`{.Agda} 记录当前留有多少个带编号的位置；这些位置合起来称为**语境**，其中每个位置称为**变量位置**。《基础词汇》引入的 `Fin n`{.Agda} 恰好包含从 0 到比 `n`{.Agda} 小一的所有位置。因此，`Term K n`{.Agda} 记录了指代对象的两种来源，此时还没有指定任何名字指向什么。
<!--ja-->
## 項

ある対象が別の対象に属すると述べるには、まずそれぞれを指す書き方が要る。あらかじめ名前を選んでもよいし、文を使うときに対象を入れる番号付きの場所を空けておいてもよい。このいずれかの方法で一つの対象を指す書き方を**項**という。

あらかじめ選ぶ名前を型 `K`{.Agda} に集める。その元を**定数名**といい、`K`{.Agda} を**定数域**という。自然数 `n`{.Agda} は、その時点で使える番号付きの場所の個数である。これらの場所を合わせて**文脈**といい、一つひとつを**変数位置**という。「基礎語彙」で導入した `Fin n`{.Agda} には、0 から `n`{.Agda} より一つ小さい位置までがちょうど含まれる。したがって `Term K n`{.Agda} は対象を指す二つの方法を記録するが、どの名前が何を指すかはまだ定めない。
<!--/-->

<!--en-->
The declaration makes these two choices part of a term's type. Changing the number of available positions does not change `K`{.Agda}, and a particular term need not use every name or position available to it. The family lives at the same universe level as `K`{.Agda}.
<!--zh-->
下面把这两项选择写进词项的类型。改变可用位置的个数不会改变 `K`{.Agda}，而一个具体的词项也不必用尽所有名字或位置。这个类型族与 `K`{.Agda} 处于同一宇宙层级。
<!--ja-->
以下では、この二つの選択を項の型に含める。使える位置の個数を変えても `K`{.Agda} は変わらず、個々の項が使える名前や位置をすべて使う必要もない。この型の族は `K`{.Agda} と同じ宇宙レベルにある。
<!--/-->

```agda
data Term {ℓ} (K : Type ℓ) (n : ℕ) : Type ℓ where
```

<!--en-->
The two constructors now say how to make a term. Given a name `k : K`{.Agda}, `con k`{.Agda} is a term made from that name, not the object it will eventually denote. Given a position `i : Fin n`{.Agda}, `var i`{.Agda} refers to the object that will fill that position. In a context of length two, positions 0 and 1 are available, but position 2 cannot be written as a term of that type. A `con`{.Agda} term can still have type `Term K 2`{.Agda} even though it uses neither position. We write `t`{.Agda} and `u`{.Agda} for terms, and `i`{.Agda} and `j`{.Agda} for positions.
<!--zh-->
接着，两个构造子说明如何形成词项。给定名字 `k : K`{.Agda}，`con k`{.Agda} 是用这个名字形成的词项，并不是它将来所指的对象。给定位置 `i : Fin n`{.Agda}，`var i`{.Agda} 指代将来填入该位置的对象。语境长度为二时，位置 0 和 1 可用，位置 2 则根本写不成这种类型的词项。由 `con`{.Agda} 得到的词项即使不使用任何位置，仍可以属于 `Term K 2`{.Agda}。下文以 `t`{.Agda}、`u`{.Agda} 表示词项，以 `i`{.Agda}、`j`{.Agda} 表示位置。
<!--ja-->
続く二つの構成子が項の作り方を示す。名前 `k : K`{.Agda} があれば、`con k`{.Agda} はその名前から作る項であり、後でその名前が指す対象そのものではない。位置 `i : Fin n`{.Agda} があれば、`var i`{.Agda} は後でそこに入る対象を指す。長さ二の文脈では位置 0 と 1 が使えるが、位置 2 はその型の項としてそもそも書けない。`con`{.Agda} で作った項はどの位置も使わないが、それでも `Term K 2`{.Agda} に属し得る。以下では `t`{.Agda} と `u`{.Agda} を項、`i`{.Agda} と `j`{.Agda} を位置に使う。
<!--/-->

```agda
  con : K → Term K n
  var : Fin n → Term K n
```

<!--en-->
## Formulas

Once we can refer to objects, we can write a claim about them. Such a written claim is a **formula**; we use `φ`{.Agda}, `ψ`{.Agda} and `θ`{.Agda} for formulas. The simplest ones say that one term belongs to another or that two terms are equal. These are **atomic formulas**. From them we can write *and*, *or* and *if … then …*, as well as the forms for *every* and *some* introduced below.

The small dot on `∈̇`{.Agda}, `∧̇`{.Agda} and the other logical signs distinguishes a *written claim* in this language from an Agda proposition about objects. For instance, `t ∈̇ u`{.Agda} records a claim about membership; it does not yet say that the objects referred to by `t`{.Agda} and `u`{.Agda} really stand in that relation. The meaning is supplied later.
<!--zh-->
## 公式

有了指代对象的词项，便可以写出关于对象的陈述。这种写出的陈述称为**公式**，下文用 `φ`{.Agda}、`ψ`{.Agda}、`θ`{.Agda} 表示。最简单的公式说的是：一个词项所指的对象属于另一个，或者两者相等；它们称为**原子公式**。在此基础上，还能写「并且」「或者」「如果……那么……」，以及下文要介绍的「每一个」「某个」。

`∈̇`{.Agda}、`∧̇`{.Agda} 等逻辑记号上的小点，用来区分这种*写出的陈述*与 Agda 中关于对象的命题。例如，`t ∈̇ u`{.Agda} 记录了一句关于隶属的话，还没有断言 `t`{.Agda}、`u`{.Agda} 将来所指的对象确实满足隶属关系。它的含义要在后文才确定。
<!--ja-->
## 論理式

対象を指す項ができたので、今度は対象についての主張を書ける。このように書かれた主張を**論理式**といい、以下では `φ`{.Agda}、`ψ`{.Agda}、`θ`{.Agda} で表す。最も単純な論理式は、一方の項が指す対象が他方に属する、または両者が等しいというもので、**原子論理式**と呼ぶ。それらから「かつ」「または」「もし…ならば…」、さらに後で述べる「すべて」や「ある」を書ける。

`∈̇`{.Agda} や `∧̇`{.Agda} などの論理記号に付く小さな点は、この*書かれた主張*と、対象についての Agda の命題を区別する。たとえば `t ∈̇ u`{.Agda} は所属についての主張を記録するだけで、`t`{.Agda} と `u`{.Agda} が後で指す対象の間に所属関係が実際に成り立つとはまだ述べない。その意味は後で与える。
<!--/-->

<!--en-->
Before giving the construction rules, we set how an expression without parentheses is grouped. The two comparisons bind most tightly; then come negation, *and* and *or*, and finally *if … then …*. The latter groups to the right: `φ ⇒̇ ψ ⇒̇ θ`{.Agda} is read as `φ ⇒̇ (ψ ⇒̇ θ)`{.Agda}. These **precedence** declarations affect the reading of an expression, not which formulas can be built.
<!--zh-->
给出形成规则之前，先约定没有括号时怎样分组：两种比较结合得最紧，其次是「非」，再是「并且」「或者」，最后是「如果……那么……」。最后一种向右分组，因此 `φ ⇒̇ ψ ⇒̇ θ`{.Agda} 读作 `φ ⇒̇ (ψ ⇒̇ θ)`{.Agda}。下面的**优先级**声明只决定怎样读已经写出的表达式，不改变哪些公式可以形成。
<!--ja-->
作り方の規則を示す前に、括弧を省いた書き方のまとまり方を定める。二つの比較が最も強く結び付き、次に「でない」、「かつ」「または」、最後に「もし…ならば…」が続く。最後の形は右にまとまり、`φ ⇒̇ ψ ⇒̇ θ`{.Agda} は `φ ⇒̇ (ψ ⇒̇ θ)`{.Agda} と読む。以下の**優先順位**宣言は、書かれた式の読み方を決めるだけで、作れる論理式の種類は変えない。
<!--/-->

```agda
infix  18 _≐_ _∈̇_
infixr 12 _∧̇_ _∨̇_
infixr 10 _⇒̇_
infix  13 ¬̇_
```

<!--en-->
Like terms, formulas retain the choices `K`{.Agda} and `n`{.Agda}. The first two constructors compare terms that can use the same positions. The next three combine already written formulas without changing those positions. `⊥̇`{.Agda} is the form for a claim that is always false. Each is a distinct way to build a formula; the code does not yet decide which claims hold.
<!--zh-->
与词项一样，公式保留 `K`{.Agda} 和 `n`{.Agda} 这两项选择。前两个构造子比较同一语境中的词项；接下来的三个把已有公式组合起来，而不改变可用的位置。`⊥̇`{.Agda} 是永远为假的陈述。它们各自都是形成公式的独立方式；这些代码还不判断哪条陈述成立。
<!--ja-->
項と同じく、論理式にも `K`{.Agda} と `n`{.Agda} の二つの選択が残る。最初の二つの構成子は同じ文脈の項を比較する。続く三つは使える位置を変えずに、すでに書いた論理式を組み合わせる。`⊥̇`{.Agda} は必ず偽になる主張の形である。それぞれが論理式を作る独立の方法であり、このコードはまだどの主張が成り立つかを判定しない。
<!--/-->

```agda
data Formula {ℓ} (K : Type ℓ) (n : ℕ) : Type ℓ where
  _∈̇_ _≐_     : Term K n → Term K n → Formula K n
  _∧̇_ _∨̇_ _⇒̇_ : Formula K n → Formula K n → Formula K n
  ⊥̇            : Formula K n
```

<!--en-->
The forms for *or* and *if … then …* have their own constructors, rather than being rewritten using *not* and *and*. Such rewritings can depend on additional logical rules that we have not assumed. Keeping the forms distinct lets us explain the meaning of each directly in the next chapters.
<!--zh-->
「或者」与「如果……那么……」各有自己的构造子，而不是先用「非」「并且」改写出来。这类改写可能依赖我们尚未假定的额外逻辑规则。保留不同的写法，后文就能分别说明它们的含义。
<!--ja-->
「または」と「もし…ならば…」にはそれぞれ独立の構成子を与え、「でない」や「かつ」を使った書き換えとはしない。そのような書き換えには、まだ仮定していない論理の規則が必要なことがある。形を分けておけば、後の章でそれぞれの意味を直接説明できる。
<!--/-->

<!--en-->
*For every object* and *there exists an object* differ from joining two finished claims: the claim that follows must have a place for the object under discussion. A **quantifier** opens one new position inside that claim. If one position was already available outside, the positions now look like this:

| location | available positions | what they refer to |
|---|---|---|
| outside the quantifier | 0 | the object already available |
| inside its body | 0, 1 | the newly chosen object, then the original one |
: A quantifier adds a position at the front of its body’s context

The new position 0 is called **bound** by the quantifier; the old positions remain **free** with respect to it and shift up by one. In Agda, the body therefore has type `Formula K (suc n)`{.Agda}, while the complete formula has type `Formula K n`{.Agda}. The body need not use its new position. Recording positions this way is called **de Bruijn indexing**: no variable names need to be stored or renamed, and a reference outside the available range cannot be formed.

The other two forms say *for every member of* and *for some member of* a set described by a term `t`{.Agda}. That term is written before the new position is opened, so it has type `Term K n`{.Agda}; only the claim following it uses the extended context. We keep these **bounded quantifiers** as separate constructors, allowing later chapters to recognize a formula that uses only these forms.
<!--zh-->
「对每个对象」与「存在某个对象」不同于连接两条已经写好的陈述：后面的陈述还需要一个位置，指向当前谈论的对象。引入这样一个新位置的写法称为**量词**。如果外面原本有一个可用位置，内外的对应关系如下：

| 所在位置 | 可用的位置 | 指向什么 |
|---|---|---|
| 量词外 | 0 | 原先可以谈论的对象 |
| 公式体内 | 0、1 | 新选取的对象、原有的对象 |
: 量词在公式体语境的最前面增加一个位置

新的位置 0 称为被量词**约束**，原有位置相对于这个量词仍是**自由**的，并顺移一位。因此，在 Agda 中，量词后面的公式体属于 `Formula K (suc n)`{.Agda}，整条公式属于 `Formula K n`{.Agda}。公式体可以不使用新位置。这种按位置记录引用关系的方法称为 **de Bruijn 索引**：无须保存变量名、考虑何时改名，也无法写出越过可用范围的引用。

另外两种写法表示「对某个集合的每个成员」和「对它的某个成员」。描述这个集合的词项 `t`{.Agda} 在新位置出现之前就已写好，因此属于外层的 `Term K n`{.Agda}；只有后面的陈述使用扩展后的语境。它们称为**有界量词**，这里保留为独立的构造子，方便后文识别只使用这些形式的公式。
<!--ja-->
「すべての対象について」や「ある対象が存在する」は、完成した二つの主張をつなぐのとは違う。後に続く主張には、今取り上げている対象を指す場所が必要になる。そのための位置を新しく開く書き方を**量化子**という。外側ですでに位置を一つ使えるなら、内外の対応は次のようになる：

| 場所 | 利用できる位置 | 指すもの |
|---|---|---|
| 量化子の外 | 0 | もとから参照できる対象 |
| 本体の中 | 0、1 | 新しく選ぶ対象、もとの対象 |
: 量化子は本体の文脈の先頭に位置を一つ加える

新しい位置 0 は量化子に**束縛**され、もとの位置はこの量化子に対しては**自由**なまま一つずつ後ろへずれる。そのため Agda では後に続く本体が `Formula K (suc n)`{.Agda} 型で、できあがった論理式が `Formula K n`{.Agda} 型になる。本体は新しい位置を使わなくてもよい。このように位置で参照を記録する方法を **de Bruijn 添字**という。変数名を保存したり、名前の付け替えを考えたりする必要がなく、使える範囲の外も参照できない。

残る二つの形は、「ある集合のすべての元について」と「そのある元について」を表す。集合を表す項 `t`{.Agda} は新しい位置を開く前に書くので、外側の `Term K n`{.Agda} 型である。後に続く主張だけが拡張された文脈を使う。これらを**有界量化子**として独立の構成子にしておくと、後の章でこの形だけを使う論理式を見分けられる。
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
