```agda
{-# OPTIONS --cubical --safe --guardedness #-}
module FOL.Syntax where
```

<!--en-->
# The [object language]{.term-intro #object-language}
<!--zh-->
# [对象语言]{.term-intro #object-language}
<!--ja-->
# [対象言語]{.term-intro #object-language}
<!--/-->

```agda
open import Base.Prelude
```

<!--en-->

Usually we write a claim about sets and ask whether it holds. Here we first ask a different question: what parts make up such a claim, and how can they be combined? Treating the written claim itself as a mathematical object, we build an **object language**.
<!--zh-->

通常，写下关于集合的陈述后，我们会问它是否成立。本章暂且不问真假，先看陈述怎样写成、又怎样组合。为此，我们把陈述的写法本身当作数学对象，构造一门**对象语言**。
<!--ja-->

集合について何かを述べれば、ふつうはそれが成り立つかを問う。本章では真偽をひとまず脇に置き、主張をどう書き、どう組み合わせるかを考える。書かれた形そのものを数学の対象として扱うために、**対象言語**を作る。
<!--/-->

<!--en-->
We start with ways to refer to an object, then use those references to make claims, and finally add forms that say *for every* or *there exists*. At each step, the Agda code specifies which written forms are possible. What these forms mean, and whether a claim holds, comes later.
<!--zh-->
我们先规定怎样指代对象，再用这些写法组成陈述，最后加入「对每个对象」和「存在某个对象」的说法。Agda 代码会逐步划定哪些表达式可以写出。至于它们指什么、陈述是否成立，留待后文再谈。
<!--ja-->
まず対象の指し方を定め、それを使って主張を書き、最後に「どの対象についても」「ある対象について」を表す形を加える。Agda のコードは、その都度どんな式を書けるかを定める。それらが何を指し、主張が成り立つかどうかは、後で考える。
<!--/-->

<!--en-->
Some choices below may seem odd at first. Why prepare names for objects and number the places where objects can be inserted? Why settle the written forms before explaining their meaning, or treat some logical signs as basic and define others from them? These are worthwhile questions, but we need not answer them all at once. Mathematics does not force a single way to define an object language. Many familiar approaches can be shown to express much the same things, though each is convenient for different purposes. We use an established approach, choosing the balance we find best suited to the set theory developed in this book. The reasons for individual choices will become clearer as we interpret and use the expressions later.
<!--zh-->
下面的定义有些取舍乍看可能不太自然：为什么要预先备好对象的名字，又为什么用数字去标记那些可以填入对象的位置？为什么先规定写法、后解释含义？为什么有些逻辑记号作为基本形式，有些则由它们定义出来？这些问题值得带着往下读，不必在本章急于解答。对象语言并没有数学上唯一的标准定义：许多常见方案虽然写法不同，却可以证明在表达能力上大体相当，只是使用起来各有便利。本书采用一种较成熟的方案，并针对后文的集合论研究，在这些便利之间作出我们认为最合适的平衡。随着后文解释和使用这些表达式，具体取舍的理由也会逐渐明朗。
<!--ja-->
以下の定義には、初めは不思議に思える選択もある。対象の名前をあらかじめ用意し、対象を入れる場所を数字で表すのはなぜか。意味より先に書き方を定め、論理記号の一部を基本形として、ほかをそこから定義するのはなぜか。どれも大切な問いだが、本章で一度に答える必要はない。対象言語の定義に、数学的に唯一の標準形があるわけではない。よく使われる方法は、書き方が違っても表現力はおおむね同じだと証明できる場合が多いが、使い勝手にはそれぞれ長所がある。本書では確立された方法の一つを採り、後で扱う集合論に最も適した形になるよう、そうした長所の間でバランスを取っている。後で式の意味を定め、実際に使うにつれて、個々の選択の理由も見えてくる。
<!--/-->

<!--en-->
## [Terms]{.term-intro #object-term}

Before saying that one object belongs to another, we need a way to refer to each object. We might choose a name in advance, or leave a numbered place to be filled when the expression is used. A written form that refers to one object in either way is called a **term**.

Let `K`{.Agda} be the type of names chosen in advance. Its elements are **[constant names]{.term-intro #constant-name}**, and `K`{.Agda} is the **[constant domain]{.term-intro #constant-domain}**. Let `n`{.Agda} count the numbered places currently available. Together these places form a **[context]{.term-intro #variable-context}**; each place is a **[variable position]{.term-intro #variable-position}**. The type `Fin n`{.Agda}, introduced in the Prelude, contains precisely the positions from `0` through one less than `n`{.Agda}. Thus `Term K n`{.Agda} can record either way of referring to an object, without yet assigning a meaning to a name or position.
<!--zh-->
## [词项]{.term-intro #object-term}

要写「一个对象属于另一个对象」，先得有办法指代这两个对象。可以预先给对象取名，也可以留下带编号的位置，等使用表达式时再指定对象。这样指代单个对象的表达式叫作**词项**。

先把预定的名字收进类型 `K`{.Agda}：其中的元素叫作**[常元名]{.term-intro #constant-name}**，`K`{.Agda} 叫作**[常元域]{.term-intro #constant-domain}**。再用自然数 `n`{.Agda} 表示当前有多少个带编号的位置；这些位置合起来是**[语境]{.term-intro #variable-context}**，每个位置是一个**[变元位置]{.term-intro #variable-position}**。《基础词汇》引入的 `Fin n`{.Agda} 正好给出从 `0` 起、到 `n`{.Agda} 的前一个数为止的全部位置。`Term K n`{.Agda} 可以记录这两种指代方式，但尚未规定名字和位置究竟指什么。
<!--ja-->
## [項]{.term-intro #object-term}

ある対象が別の対象に属すると書くには、まず両者を指す表現が要る。名前をあらかじめ決めてもよいし、番号付きの場所を残しておき、式を使うときに対象を割り当ててもよい。こうして一つの対象を指す表現を**項**と呼ぶ。

あらかじめ決める名前を型 `K`{.Agda} に集め、その元を**[定数名]{.term-intro #constant-name}**、`K`{.Agda} を**[定数域]{.term-intro #constant-domain}**と呼ぶ。一方、自然数 `n`{.Agda} は、今使える番号付きの場所の数を表す。場所全体が**[文脈]{.term-intro #variable-context}**で、一つひとつが**[変数位置]{.term-intro #variable-position}**である。「基礎語彙」で導入した `Fin n`{.Agda} は、`0` から `n`{.Agda} の一つ手前までの位置をちょうど含む。`Term K n`{.Agda} は、この二通りで作られる項の型である。ただし、名前や位置が実際に何を指すかはまだ決めない。
<!--/-->

<!--en-->
**Definition** (`Term`{.Agda}) For a universe level `ℓ`{.Agda}, a type `K : Type ℓ`{.Agda}, and a natural number `n : ℕ`{.Agda}, define the inductive type `Term K n : Type ℓ`{.Agda}.
<!--zh-->
**定义** (`Term`{.Agda}) 给定宇宙层级 `ℓ`{.Agda}、类型 `K : Type ℓ`{.Agda} 和自然数 `n : ℕ`{.Agda}，定义归纳类型 `Term K n : Type ℓ`{.Agda}。
<!--ja-->
**定義** (`Term`{.Agda}) 宇宙レベル `ℓ`{.Agda}、型 `K : Type ℓ`{.Agda}、自然数 `n : ℕ`{.Agda} に対し、帰納型 `Term K n : Type ℓ`{.Agda} を定める。
<!--/-->

```agda
data Term {ℓ} (K : Type ℓ) (n : ℕ) : Type ℓ where
```

<!--en-->
Each `k : K`{.Agda} determines a term `con k : Term K n`{.Agda}; each `i : Fin n`{.Agda} determines a term `var i : Term K n`{.Agda}.
<!--zh-->
每个 `k : K`{.Agda} 确定一个词项 `con k : Term K n`{.Agda}；每个 `i : Fin n`{.Agda} 确定一个词项 `var i : Term K n`{.Agda}。
<!--ja-->
各 `k : K`{.Agda} に対して項 `con k : Term K n`{.Agda} を、各 `i : Fin n`{.Agda} に対して項 `var i : Term K n`{.Agda} を定める。
<!--/-->

```agda
  con : K → Term K n
  var : Fin n → Term K n
```

<!--en-->
These constructors produce ways to refer to objects, not the objects themselves. From a name `k : K`{.Agda}, `con k`{.Agda} is a term; from a position `i : Fin n`{.Agda}, `var i`{.Agda} is another. In a context of length two, positions `0` and `1` are available, but `2` is not. A term formed by `con`{.Agda} can nevertheless have type `Term K 2`{.Agda}: it uses no position at all. We write `t`{.Agda} and `u`{.Agda} for terms, and `i`{.Agda} and `j`{.Agda} for positions.
<!--zh-->
这两个构造子形成的是指代对象的写法，而不是对象本身。给定名字 `k : K`{.Agda}，可以写出词项 `con k`{.Agda}；给定位置 `i : Fin n`{.Agda}，可以写出词项 `var i`{.Agda}。若语境长度为二，可用位置只有 `0` 和 `1`，没有 `2`。不过，`con`{.Agda} 形成的词项不占用任何位置，仍可属于 `Term K 2`{.Agda}。下文用 `t`{.Agda}、`u`{.Agda} 表示词项，用 `i`{.Agda}、`j`{.Agda} 表示位置。
<!--ja-->
この二つの構成子が作るのは対象の指し方であり、対象そのものではない。名前 `k : K`{.Agda} から項 `con k`{.Agda} を、位置 `i : Fin n`{.Agda} から項 `var i`{.Agda} を作れる。文脈の長さが二なら使える位置は `0` と `1` だけで、`2` は含まれない。一方、`con`{.Agda} で作る項は位置をまったく使わないので、`Term K 2`{.Agda} 型にも属する。以下、項を `t`{.Agda}、`u`{.Agda}、位置を `i`{.Agda}、`j`{.Agda} と書く。
<!--/-->

<!--en-->
## [Formulas]{.term-intro #object-formula}

Once we can refer to objects, we can write a claim about them. Such a written claim is a **formula**; we use `φ`{.Agda}, `ψ`{.Agda} and `θ`{.Agda} for formulas. The simplest ones say that one term belongs to another or that two terms are equal. These are **[atomic formulas]{.term-intro #atomic-formula}**. From them we can write *and*, *or* and *if … then …*, as well as the forms for *every* and *some* introduced below.
<!--zh-->
## [公式]{.term-intro #object-formula}

有了词项，就能写出关于对象的陈述。这种书面陈述叫作**公式**，下文用 `φ`{.Agda}、`ψ`{.Agda}、`θ`{.Agda} 表示。最简单的公式由两个词项写成，形如「前者属于后者」或「两者相等」。这类公式叫作**[原子公式]{.term-intro #atomic-formula}**。在此基础上，还能写「并且」「或者」「如果……那么……」，以及下文要介绍的「每个」「某个」。
<!--ja-->
## [論理式]{.term-intro #object-formula}

項があれば、対象についての主張を書ける。書かれた主張を**論理式**と呼び、以下では `φ`{.Agda}、`ψ`{.Agda}、`θ`{.Agda} と書く。最も単純なのは、二つの項について所属か等しさを述べる**[原子論理式]{.term-intro #atomic-formula}**である。そこから「かつ」「または」「もし…ならば…」を組み立て、さらに後で「どの対象についても」「ある対象について」という形を加える。
<!--/-->

<!--en-->
Before giving the construction rules, we set how an expression without parentheses is grouped. Membership and equality bind most tightly; then come the negation defined below, *and* and *or*, and finally *if … then …*. The last of these groups to the right: `φ ⇒̇ ψ ⇒̇ θ`{.Agda} is read as `φ ⇒̇ (ψ ⇒̇ θ)`{.Agda}. These **precedence** declarations affect how a formula is read, not which formulas can be built.
<!--zh-->
写公式时常省略括号，因此要先约定各记号如何结合。隶属和相等结合得最紧，其次是稍后定义的「非」，再是「并且」「或者」，最后是「如果……那么……」。最后一种向右结合，所以 `φ ⇒̇ ψ ⇒̇ θ`{.Agda} 读作 `φ ⇒̇ (ψ ⇒̇ θ)`{.Agda}。下面的**优先级**声明只影响公式的读法，不会增减可写出的公式。
<!--ja-->
括弧を省いても読み違えないよう、先に結び付きの強さを決める。所属と等号が最も強く、次が後で定義する「でない」、その次が「かつ」「または」、最後が「もし…ならば…」である。最後の形は右側からまとまるので、`φ ⇒̇ ψ ⇒̇ θ`{.Agda} は `φ ⇒̇ (ψ ⇒̇ θ)`{.Agda} と読む。以下の**優先順位**宣言が変えるのは論理式の読み方であり、作れる論理式は変わらない。
<!--/-->

```agda
infix  18 _≐_ _∈̇_
infixr 12 _∧̇_ _∨̇_
infixr 10 _⇒̇_
infix  13 ¬̇_
```

<!--en-->
The small dot on `∈̇`{.Agda}, `∧̇`{.Agda} and the other logical signs distinguishes a *written claim* in this language from an Agda proposition about objects. For instance, `t ∈̇ u`{.Agda} records a claim about membership; it does not yet say that the objects referred to by `t`{.Agda} and `u`{.Agda} really stand in that relation. The meaning is supplied later.
<!--zh-->
`∈̇`{.Agda}、`∧̇`{.Agda} 等记号上的小点提醒我们：这里写的是对象语言中的陈述，不是直接在 Agda 中提出的命题。例如，`t ∈̇ u`{.Agda} 只是写下一条隶属陈述；`t`{.Agda}、`u`{.Agda} 究竟指什么，以及隶属关系是否成立，都还没有确定。
<!--ja-->
`∈̇`{.Agda} や `∧̇`{.Agda} などに付く点は、対象言語に*書かれた主張*を、Agda で対象について直接述べる命題と区別する。たとえば `t ∈̇ u`{.Agda} は所属を述べる形を記録するだけである。`t`{.Agda} と `u`{.Agda} が何を指し、その所属が成り立つかは、まだ決まっていない。
<!--/-->

<!--en-->
**Definition** (`Formula`{.Agda}) For a universe level `ℓ`{.Agda}, a type `K : Type ℓ`{.Agda}, and a natural number `n : ℕ`{.Agda}, define the inductive type `Formula K n : Type ℓ`{.Agda}.
<!--zh-->
**定义** (`Formula`{.Agda}) 给定宇宙层级 `ℓ`{.Agda}、类型 `K : Type ℓ`{.Agda} 和自然数 `n : ℕ`{.Agda}，定义归纳类型 `Formula K n : Type ℓ`{.Agda}。
<!--ja-->
**定義** (`Formula`{.Agda}) 宇宙レベル `ℓ`{.Agda}、型 `K : Type ℓ`{.Agda}、自然数 `n : ℕ`{.Agda} に対し、帰納型 `Formula K n : Type ℓ`{.Agda} を定める。
<!--/-->

```agda
data Formula {ℓ} (K : Type ℓ) (n : ℕ) : Type ℓ where
```

<!--en-->
The constructors `_∈̇_`{.Agda} and `_≐_`{.Agda} each take two terms of `Term K n`{.Agda} and yield a formula. The constructors `_∧̇_`{.Agda}, `_∨̇_`{.Agda} and `_⇒̇_`{.Agda} each take two formulas of `Formula K n`{.Agda} and yield another. The constructor `⊥̇`{.Agda} takes no arguments.
<!--zh-->
构造子 `_∈̇_`{.Agda} 和 `_≐_`{.Agda} 各取两个 `Term K n`{.Agda} 中的词项，得到一个公式；`_∧̇_`{.Agda}、`_∨̇_`{.Agda} 和 `_⇒̇_`{.Agda} 各取两个 `Formula K n`{.Agda} 中的公式，得到另一个公式；`⊥̇`{.Agda} 不取参数。
<!--ja-->
構成子 `_∈̇_`{.Agda} と `_≐_`{.Agda} はそれぞれ `Term K n`{.Agda} の項を二つ取り、一つの論理式を作る。`_∧̇_`{.Agda}、`_∨̇_`{.Agda}、`_⇒̇_`{.Agda} はそれぞれ `Formula K n`{.Agda} の論理式を二つ取り、新たな論理式を作る。`⊥̇`{.Agda} は引数を取らない。
<!--/-->

```agda
  _∈̇_ _≐_     : Term K n → Term K n → Formula K n
  _∧̇_ _∨̇_ _⇒̇_ : Formula K n → Formula K n → Formula K n
  ⊥̇           : Formula K n
```

<!--en-->
The constructors `∃̇_`{.Agda} and `∀̇_`{.Agda} each take a formula in `Formula K (suc n)`{.Agda} and yield one in `Formula K n`{.Agda}. The constructors `∀̇∈`{.Agda} and `∃̇∈`{.Agda} also take a term in `Term K n`{.Agda}.
<!--zh-->
构造子 `∃̇_`{.Agda} 和 `∀̇_`{.Agda} 各取一个 `Formula K (suc n)`{.Agda} 中的公式，得到 `Formula K n`{.Agda} 中的公式；`∀̇∈`{.Agda} 和 `∃̇∈`{.Agda} 还各取一个 `Term K n`{.Agda} 中的词项。
<!--ja-->
構成子 `∃̇_`{.Agda} と `∀̇_`{.Agda} はそれぞれ `Formula K (suc n)`{.Agda} の論理式を一つ取り、`Formula K n`{.Agda} の論理式を作る。`∀̇∈`{.Agda} と `∃̇∈`{.Agda} は、さらに `Term K n`{.Agda} の項を一つ取る。
<!--/-->

```agda
  ∃̇_ ∀̇_       : Formula K (suc n) → Formula K n
  ∀̇∈ ∃̇∈       : Term K n → Formula K (suc n) → Formula K n
```

<!--en-->
The symbol `⊥̇`{.Agda} is intended to express an always-false claim. For now, the formation rules specify only which formulas can be written, not whether any formula holds. The forms for *or* (`_∨̇_`{.Agda}) and *if … then …* (`_⇒̇_`{.Agda}) have their own constructors, rather than being rewritten using *not* (`¬̇_`{.Agda}) and *and* (`_∧̇_`{.Agda}). Such rewritings can depend on additional logical rules that we have not assumed. Keeping the forms distinct lets us explain the meaning of each directly in the next chapters.
<!--zh-->
`⊥̇`{.Agda} 预定用来表达恒假的陈述。目前这些形成规则只规定哪些公式可以写出，还没有判定任何公式的真假。「或者」的 `_∨̇_`{.Agda} 与「如果……那么……」的 `_⇒̇_`{.Agda} 各有一个构造子，不必先用表示「非」的 `¬̇_`{.Agda} 和表示「并且」的 `_∧̇_`{.Agda} 改写。那样改写有时需要尚未假定的逻辑规则。将几种写法分开，后文便能分别解释它们的含义。
<!--ja-->
`⊥̇`{.Agda} は、常に偽となる主張を表すものとして用意する。今はどの論理式を書けるかを定めるだけで、真偽はまだ判定しない。「または」の `_∨̇_`{.Agda} と「もし…ならば…」の `_⇒̇_`{.Agda} には、それぞれ構成子を用意する。「でない」を表す `¬̇_`{.Agda} や「かつ」を表す `_∧̇_`{.Agda} で書き換えて済ませると、まだ仮定していない論理の規則が必要になる場合がある。形を分けておけば、後でそれぞれの意味を直接与えられる。
<!--/-->

<!--en-->
The constructors `∀̇_`{.Agda} (*for every object*) and `∃̇_`{.Agda} (*there exists an object*) differ from joining two finished claims: the claim that follows must have a place for the object under discussion. A **[quantifier]{.term-intro #object-quantifier}** opens one new position inside that claim. The figure follows the positions when one was already available outside.
<!--zh-->
`∀̇_`{.Agda} 表示「对每个对象」，`∃̇_`{.Agda} 表示「存在某个对象」。它们不是把两条现成陈述接起来：后面的陈述还得指向新谈及的对象。为此，**[量词]{.term-intro #object-quantifier}**会在后续公式中添一个位置。下图以原来已有一个位置为例，展示编号如何变化。
<!--ja-->
`∀̇_`{.Agda} は「どの対象についても」、`∃̇_`{.Agda} は「ある対象について」を表す。これらは、できあがった主張を二つつなぐだけでは書けない。後に続く主張には、新たに取り上げる対象を指す場所が要る。そこで**[量化子]{.term-intro #object-quantifier}**は、後続の論理式に位置を一つ加える。次の図は、もともと一つ位置がある場合に番号がどう変わるかを示す。
<!--/-->

<figure class="book-diagram quantifier-context-figure" id="fig-quantifier-context" aria-describedby="fig-quantifier-context-caption">
<div class="diagram-framed">
<div class="quantifier-context-scene" aria-hidden="true">
<svg class="quantifier-context-geometry" viewBox="0 0 360 275" aria-hidden="true" focusable="false">
<rect class="diagram-space-shape quantifier-context-space" x="28" y="105" width="112" height="112"/>
<rect class="diagram-space-shape quantifier-context-space" x="205" y="74" width="126" height="174"/>
<path class="diagram-guide quantifier-context-divider" d="M218 162 H318"/>
<path class="diagram-map-line quantifier-context-old-path" d="M110 161 C159 161 167 205 247 205"/>
<path class="diagram-map-tip quantifier-context-old-tip" d="M238 199 L248 205 L238 211"/>
<path class="diagram-map-line quantifier-context-new-path" d="M187 98 C215 99 217 128 247 128"/>
<path class="diagram-map-tip quantifier-context-new-tip" d="M238 122 L248 128 L238 134"/>
<circle class="diagram-point quantifier-context-insert" cx="169" cy="98" r="18"/>
<circle class="diagram-point quantifier-context-old-node" cx="85" cy="161" r="25"/>
<circle class="diagram-point quantifier-context-new-node" cx="273" cy="128" r="25"/>
<circle class="diagram-point quantifier-context-old-node" cx="273" cy="205" r="25"/>
</svg>
<span class="quantifier-context-label quantifier-context-heading" style="left:23.33%;top:16.36%">$n = 1$</span>
<span class="quantifier-context-label quantifier-context-heading" style="left:74.17%;top:16.36%">$n + 1 = 2$</span>
<span class="quantifier-context-label quantifier-context-plus" style="left:46.94%;top:35.64%">$+$</span>
<span class="quantifier-context-label quantifier-context-value" style="left:23.61%;top:58.55%">$a$</span>
<span class="quantifier-context-label quantifier-context-value quantifier-context-new-value" style="left:75.83%;top:46.55%">$x$</span>
<span class="quantifier-context-label quantifier-context-value" style="left:75.83%;top:74.55%">$a$</span>
<span class="quantifier-context-label quantifier-context-index" style="left:13.05%;top:58.55%">$0$</span>
<span class="quantifier-context-label quantifier-context-index" style="left:87.5%;top:46.55%">$0$</span>
<span class="quantifier-context-label quantifier-context-index" style="left:87.5%;top:74.55%">$1$</span>
</div>
</div>
<figcaption id="fig-quantifier-context-caption">
<!--en-->
The lower arrow shows the old position `0` becoming `1` while still referring to $a$; the upper arrow shows the quantifier opening a new position `0` for $x$
<!--zh-->
下方箭头表示旧位置 `0` 顺移为 `1`，仍指向 $a$；上方箭头表示量词为 $x$ 新开位置 `0`
<!--ja-->
下の矢印は、もとの位置 `0` が `1` にずれても $a$ を指し続けることを示し、上の矢印は新たに扱う $x$ のために位置 `0` が加わることを示す
<!--/-->
</figcaption>
</figure>

<!--en-->
The new position `0` represents a **[bound variable]{.term-intro #bound-variable}** of the quantifier; the old positions represent **[free variables]{.term-intro #free-variable}** relative to it and shift up by one. In Agda, the body therefore has type `Formula K (suc n)`{.Agda}, while the complete formula has type `Formula K n`{.Agda}. The body need not use its new position. Recording positions this way is called **[de Bruijn indexing]{.term-intro #de-bruijn-indexing}**: no variable names need to be stored or renamed, and a reference outside the available range cannot be formed.

The constructors `∀̇∈`{.Agda} and `∃̇∈`{.Agda} say *for every member of* and *for some member of* a set described by a term `t`{.Agda}. That term is written before the new position is opened, so it has type `Term K n`{.Agda}; only the claim following it uses the extended context. We keep these **[bounded quantifiers]{.term-intro #bounded-quantifier}** as separate constructors, allowing later chapters to recognize a formula that uses only these forms.
<!--zh-->
新增的 `0` 号位置对应这个量词的**[约束变元]{.term-intro #bound-variable}**；原有位置上的变元相对于它仍是**[自由变元]{.term-intro #free-variable}**，编号各向后挪一位。因此，量词内部的公式体属于 `Formula K (suc n)`{.Agda}，整条公式属于 `Formula K n`{.Agda}。公式体也可以不用新位置。这种只记录位置、不保存名字的方法叫作 **[de Bruijn 索引]{.term-intro #de-bruijn-indexing}**：无需为避免重名而更换变元名称，也写不出越过可用范围的引用。

`∀̇∈`{.Agda} 和 `∃̇∈`{.Agda} 把量化范围限定在某个集合的成员中，用词项 `t`{.Agda} 指明这个集合。`t`{.Agda} 在新位置加入前就已写成，所以仍属于外层的 `Term K n`{.Agda}；只有量词后面的公式体使用扩展语境。这两种写法称为**[有界量词]{.term-intro #bounded-quantifier}**，各有独立的构造子，后文便能辨认只使用有界量词的公式。
<!--ja-->
新しい `0` 番の位置が、この量化子の**[束縛変数]{.term-intro #bound-variable}**に当たる。もとの位置にある変数は、この量化子から見れば**[自由変数]{.term-intro #free-variable}**のままで、番号だけが一つ後ろへずれる。したがって量化子の内側の論理式は `Formula K (suc n)`{.Agda} 型、全体は `Formula K n`{.Agda} 型になる。内側で新しい位置を使わなくてもよい。名前を保存せず、位置で参照を記録する方法が **[de Bruijn 添字]{.term-intro #de-bruijn-indexing}**である。名前の衝突を避けるための付け替えが要らず、使える範囲の外を参照する式も作れない。

`∀̇∈`{.Agda} と `∃̇∈`{.Agda} は、項 `t`{.Agda} が指す集合の元に範囲を限る形である。`t`{.Agda} は新しい位置を加える前に書くため、外側の `Term K n`{.Agda} 型のままである。拡張された文脈を使うのは、量化子の内側の論理式だけである。これらを**[有界量化子]{.term-intro #bounded-quantifier}**という独立の構成子にしておけば、後で有界量化子だけを使う論理式を見分けられる。
<!--/-->

<!--en-->
**Definition** (`¬̇_`{.Agda}) The constructors above give the basic forms of formulas; negation needs no additional one. We define `¬̇ φ`{.Agda} as `φ ⇒̇ ⊥̇`{.Agda}. A function that inspects a formula therefore sees an implication, not a separate negation case. Under the intended interpretation, this implication expresses the refutation of `φ`{.Agda}.
<!--zh-->
**定义** (`¬̇_`{.Agda}) 上面的构造子给出了公式的基本形式；否定无须再添一种。我们规定 `¬̇ φ`{.Agda} 就是 `φ ⇒̇ ⊥̇`{.Agda}。因此，递归检查公式时只会遇到蕴涵，无须再处理一种独立的否定情形。后文赋予公式含义时，这个蕴涵便表达对 `φ`{.Agda} 的否定。
<!--ja-->
**定義** (`¬̇_`{.Agda}) ここまでの構成子で論理式の基本形はそろっており、否定のために別の構成子を加える必要はない。`¬̇ φ`{.Agda} を `φ ⇒̇ ⊥̇`{.Agda} と定める。そのため、論理式を再帰的に調べるときは含意の場合を扱えば足り、否定の場合を増やさずに済む。後で意味を与えると、この含意は `φ`{.Agda} の否定を表す。
<!--/-->

```agda
¬̇_ : ∀ {ℓ} {K : Type ℓ} {n} → Formula K n → Formula K n
¬̇ φ = φ ⇒̇ ⊥̇
```

<!--en-->
**Definition** (`⊤̇`{.Agda}) Truth is likewise defined, not primitive: `⊤̇`{.Agda} unfolds to `⊥̇ ⇒̇ ⊥̇`{.Agda}. The future interpretation needs only its implication and falsity cases to give meaning to both derived symbols. These definitions work for every constant domain and context length.
<!--zh-->
**定义** (`⊤̇`{.Agda}) 真也不另设构造子，而规定 `⊤̇`{.Agda} 就是 `⊥̇ ⇒̇ ⊥̇`{.Agda}。所以，后文只需解释蕴涵和假，就能同时解释否定与真。这两项定义不依赖特定的常元域或语境长度。
<!--ja-->
**定義** (`⊤̇`{.Agda}) 真も構成子を増やさず、`⊤̇`{.Agda} を `⊥̇ ⇒̇ ⊥̇`{.Agda} と定める。したがって後では含意と偽を解釈すれば、否定と真にも意味が定まる。どちらの定義も、定数域や文脈の長さを選ばずに使える。
<!--/-->

```agda
⊤̇ : ∀ {ℓ} {K : Type ℓ} {n} → Formula K n
⊤̇ = ⊥̇ ⇒̇ ⊥̇
```

<!--en-->
The same rules for forming terms and formulas work with different choices of `K`{.Agda}. If `K`{.Agda} is a structure’s carrier, constant symbols can name its elements. Restricting the type of names restricts the available constant parameters; choosing the empty type `⊥*`{.Agda} leaves none. The number of variable positions is chosen independently through `n`{.Agda}.

## [Sentences]{.term-intro #object-sentence} and [parameter-free formulas]{.term-intro #parameter-free-formula}

There are two distinct ways to rule out names. A **[sentence]{.term-ref #object-sentence}** has no free variables: its context length is zero, giving `Formula K 0`{.Agda}, but it may still contain constants. A **parameter-free formula** has no constants: its constant domain is `⊥*`{.Agda}, giving `Formula ⊥* n`{.Agda}, but it may still have free variables. Neither needs a separate datatype or code name.

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
词项与公式的形成规则适用于不同的常元域 `K`{.Agda}。若取某个结构的载体作为 `K`{.Agda}，常元就能指名其中的任意元素；若只为一部分对象预留名字，可用的常元便随之减少；若取空类型 `⊥*`{.Agda}，就没有可用的常元。变元位置的数量则由 `n`{.Agda} 独立决定。

## [句子]{.term-intro #object-sentence}与[无参公式]{.term-intro #parameter-free-formula}

我们可以分别禁用两类指代方式。**[句子]{.term-ref #object-sentence}**没有自由变元：把语境长度设为零，便得到 `Formula K 0`{.Agda}，但常元仍可出现。**无参公式**没有常元：把常元域设为空类型 `⊥*`{.Agda}，便得到 `Formula ⊥* n`{.Agda}，但仍可有自由变元。这两类公式都不用另设数据类型或代码名称。

| 可用的指代方式 | 公式类型 |
|---|---|
| 两者皆可 | `Formula K n`{.Agda} |
| 仅常元 | `Formula K 0`{.Agda} |
| 仅变元位置 | `Formula ⊥* n`{.Agda} |
| 两者均无 | `Formula ⊥* 0`{.Agda} |
: 自由变元与常元名可以分别禁用

空类型总能映入任意 `K`{.Agda}，所以后文的常元映射可以把无参公式送入任意常元域。这样，不必先枚举结构的元素，就能枚举无参公式。不过，能编码的并非只有无参公式：后文也会编码带有载体常元的公式。

## 小结

本章只规定词项和公式怎样写：常元与变元位置提供指代方式，量词决定新位置的作用范围。它们究竟指什么、公式何时成立，还没有规定。下一步先建立一个结构，用来解释这些符号。
<!--ja-->
項と論理式の作り方は、定数域 `K`{.Agda} の選び方によらず同じである。ある構造の台を `K`{.Agda} にすれば、その元を定数で名指せる。名前を付ける対象を一部に限れば、使える定数も減る。空型 `⊥*`{.Agda} を選べば、使える定数はない。変数位置の数は `n`{.Agda} で独立に決める。

## [文]{.term-intro #object-sentence}と[パラメータを持たない論理式]{.term-intro #parameter-free-formula}

定数名と変数位置は、それぞれ独立に使わないようにできる。**[文]{.term-ref #object-sentence}**は自由変数を持たない。文脈の長さをゼロにした `Formula K 0`{.Agda} だが、定数は使える。一方、**パラメータを持たない論理式**は定数を持たない。定数域を空型 `⊥*`{.Agda} にした `Formula ⊥* n`{.Agda} だが、自由変数は使える。どちらのためにも別のデータ型やコード名は要らない。

| 使える指し方 | 論理式の型 |
|---|---|
| 両方 | `Formula K n`{.Agda} |
| 定数のみ | `Formula K 0`{.Agda} |
| 位置のみ | `Formula ⊥* n`{.Agda} |
| どちらもなし | `Formula ⊥* 0`{.Agda} |
: 自由変数と定数名は別々に使えなくできる

空型から任意の `K`{.Agda} への写像がある。そこで後の定数写像を使えば、パラメータを持たない論理式をどの定数域にも移せる。構造の元を先に列挙しなくても、この種の論理式なら列挙できる。ただし、符号化できるのはこれだけではない。後の章では、台の元を定数として使う論理式も符号化する。

## まとめ

本章で決めたのは、項と論理式の書き方である。定数と変数位置で対象を指し、量化子で新しい位置の作用域を定める。それらが何を指し、論理式がいつ成り立つかは、まだ決めていない。次は、その記号を解釈するための構造を用意する。
<!--/-->
