<!--en-->
# Truth values

To interpret a first-order formula we must first say what the formula evaluates to. The classical textbook answer fixes the target as a two-element set, the booleans: a formula is either true or false, each connective is given by a truth table, and every formula is decided one way or the other. The value a formula receives is called its **[truth value]{.term-intro #truth-value}**.

This book does not fix that target. A formula is evaluated into a carrier chosen in advance, together with operations that interpret the connectives and the quantifiers. The package of that data is a **[truth algebra]{.term-intro #truth-algebra}**, recorded here as the record `TruthAlgebra`{.Agda}. The chapter then builds the single instance on which the rest of the development runs.

Why leave the target open when only one instance is ever built? Because doing so separates two questions that classical presentations answer at once. A truth algebra says which operations exist; it says nothing about the equations they satisfy. `TruthAlgebra`{.Agda} therefore assumes no associativity, no distributivity, and no lattice or Boolean law. A theorem proved about an arbitrary truth algebra cannot have used a law that was never assumed, so it holds in every instance.

That separation is visible in the development rather than merely promised. The structure record of the next chapter, the satisfaction relation, and four of the chapters that manipulate formulas are all stated over an arbitrary `𝕋 : TruthAlgebra ℓ ℓ'`{.Agda}; only the chapters that build models fix the instance constructed here. Syntax and its manipulation theorems therefore never look inside a truth value.

The chapter proceeds in two stages. It first isolates the carrier and the operations that a truth-value interpretation must supply. It then specializes that interface to propositions, where the corresponding logical operations give a concrete instance. The declaration below opens the module under the options the Prelude explained.
<!--zh-->
# 真值

要解释一阶公式，首先要回答公式求值得到什么。教科书里的经典答案把求值目标固定为二元集，即布尔值：一条公式非真即假，每个联结词由真值表给出，而且每条公式都被判定到某一边。公式所得的那个值，就称为它的**[真值]{.term-intro #truth-value}**。

本书不固定这个目标。公式求值到事先选定的载体之中，并配有解释联结词与量词的运算。把这些数据打包在一起，便得到一个**[真值代数]{.term-intro #truth-algebra}**，本章将其记录为 record `TruthAlgebra`{.Agda}，随后构造后续发展真正运行于其上的那一个实例。

既然全书只构造一个实例，为什么还要让目标保持开放？因为这样才能分开两个在经典讲法中被一并回答的问题：真值代数只说有哪些运算，不说这些运算满足什么等式。因此 `TruthAlgebra`{.Agda} 不假设结合律，不假设分配律，也不假设格律或布尔律。关于任意真值代数证明的定理，不可能用到未曾假设的定律，于是它在每个实例中都成立。

这一分离并非空头许诺，而是在后续发展中看得见：下一章的结构 record、满足关系，以及操作公式的四个章节，都在任意 `𝕋 : TruthAlgebra ℓ ℓ'`{.Agda} 上陈述；只有构造模型的诸章才固定本章所造的实例。因此，语法及其操作定理从不窥探真值的内部。

本章分两步进行：先抽取真值解释必须提供的载体与运算，再把这一接口具体化为命题，并以相应的逻辑运算给出一个具体实例。下面的声明在《基础词汇》已说明的选项下开启本章的模块。
<!--ja-->
# 真理値

一階の論理式を解釈するには、まず論理式が何へ評価されるのかを決めなければなりません。教科書の古典的な答えは対象を二元集合、すなわちブール値に固定します。論理式は真か偽のいずれかであり、各結合子は真理値表で与えられ、どの論理式もいずれか一方に判定されます。論理式が受け取るその値を、その**[真理値]{.term-intro #truth-value}**と呼びます。

本書はこの対象を固定しません。論理式は、あらかじめ選んだ台の中へ評価され、結合子と量化子を解釈する演算がそれに伴います。このデータをひとまとめにしたものが**[真理値代数]{.term-intro #truth-algebra}**であり、本章はそれをレコード `TruthAlgebra`{.Agda} として記録し、続いてこの後の展開が実際に走る唯一の実例を構成します。

実例を一つしか作らないのに、なぜ対象を開いたままにするのでしょうか。古典的な説明が一度に答えてしまう二つの問いを分けるためです。真理値代数はどの演算があるかを述べるだけで、それらが満たす等式については何も述べません。したがって `TruthAlgebra`{.Agda} は結合律も分配律も、束やブール代数の法則も仮定しません。任意の真理値代数について証明された定理は、仮定していない法則を使いようがないので、どの実例でも成り立ちます。

この分離は約束にとどまらず、展開の中に見えます。次章の構造のレコード、充足関係、そして論理式を操作する四つの章は、いずれも任意の `𝕋 : TruthAlgebra ℓ ℓ'`{.Agda} の上で述べられ、実例を固定するのはモデルを構成する諸章だけです。構文とその操作の定理は、真理値の内部を覗くことがありません。

この章は二段階で進みます。まず、真理値解釈が供給しなければならない台と演算を取り出します。次に、このインターフェースを命題に特殊化し、対応する論理演算によって具体的な実例を与えます。以下の宣言は、「基礎語彙」で説明したオプションのもとで本章のモジュールを開きます。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

module Base.Truth where
```

<!--en-->
The basic vocabulary arrives as a block. The Prelude collected it so that later chapters need not list its names one by one, and this chapter draws on a small part of it: `Type`{.Agda} and the level operations for stating sizes, `isSet`{.Agda} for the requirement placed on truth values, and `hProp`{.Agda} with `isSetHProp`{.Agda}, `⊥*`{.Agda} and `isProp⊥*`{.Agda} for the instance built in the second half.
<!--zh-->
基础词汇以整块的形式引入。《基础词汇》一章把它们汇集起来，正是为了让后续章节不必逐个列名；本章用到的只是其中一小部分：`Type`{.Agda} 与层级运算用于陈述大小，`isSet`{.Agda} 用于对真值提出的要求，而 `hProp`{.Agda} 连同 `isSetHProp`{.Agda}、`⊥*`{.Agda} 与 `isProp⊥*`{.Agda} 则服务于后半章构造的实例。
<!--ja-->
基礎語彙はひとまとめに導入されます。「基礎語彙」の章がそれらを集めたのは、後の章が名前を一つずつ挙げずに済むようにするためでした。本章が使うのはその一部です。`Type`{.Agda} とレベルの演算は大きさを述べるために、`isSet`{.Agda} は真理値に課す要求のために、`hProp`{.Agda} と `isSetHProp`{.Agda}、`⊥*`{.Agda}、`isProp⊥*`{.Agda} は後半で構成する実例のために使います。
<!--/-->

```agda

open import Base.Prelude
```

<!--en-->
The next line imports differently. `import X as Y using (...)` makes the listed names available only under the prefix `Y`, unlike the `open import` form, which brings them into scope bare. The prefix is not decoration here: the record declared below has fields of its own called `_⊓_`, `_⊔_`, `_⇒_`, `¬_` and `⊤`, and the library's operations of the same names would collide with them. Keeping the library behind `Logic` lets both live on the page, and every later use shows at a glance which one is meant. The [Agda manual on the module system](https://agda.readthedocs.io/en/v2.8.0/language/module-system.html) describes the two forms in full.
<!--zh-->
下一行的引入方式不同。`import X as Y using (...)` 只让所列名称以前缀 `Y` 的形式可用，而不像 `open import` 那样把它们直接带入作用域。这里的前缀不是装饰：下面声明的 record 自己就有名为 `_⊓_`、`_⊔_`、`_⇒_`、`¬_` 与 `⊤` 的字段，库中同名的运算会与之冲突。把库留在 `Logic` 之后，两者便能同时出现在纸面上，而后文每次使用都一眼可辨指的是哪一个。[Agda 手册的模块系统一节](https://agda.readthedocs.io/en/v2.8.0/language/module-system.html)完整说明了这两种形式。
<!--ja-->
次の行は導入の仕方が異なります。`import X as Y using (...)` は、挙げた名前を接頭辞 `Y` の付いた形でのみ使えるようにします。名前をそのままスコープへ持ち込む `open import` とは違います。ここでの接頭辞は飾りではありません。下で宣言するレコードは `_⊓_`、`_⊔_`、`_⇒_`、`¬_`、`⊤` という自前のフィールドを持ち、同じ名前のライブラリの演算と衝突するからです。ライブラリを `Logic` の後ろに置けば両方を紙面に共存させられ、以降のどの使用箇所でもどちらを指すか一目で分かります。二つの形式については [Agda マニュアルのモジュールシステムの節](https://agda.readthedocs.io/en/v2.8.0/language/module-system.html)が詳しく述べています。
<!--/-->

```agda
import Cubical.Functions.Logic as Logic
  using ( _⊓_; _⊔_; _⇒_; ¬_; ⊤; ∃[]-syntax; ∀[]-syntax )
```

<!--en-->
## The interface

What data must be in hand before formulas can be assigned truth values? The answer is a carrier, a requirement on it, and one operation for each way of forming a compound formula. Nothing else: no equation relating those operations, and no assumption about what a truth value is made of.
<!--zh-->
## 接口

要为公式赋予真值，事先必须握有哪些数据？答案是一个载体、对它的一项要求，以及为每种复合公式的构造方式各配一个运算。除此之外别无他物：既没有关联这些运算的等式，也没有关于真值由什么构成的假设。
<!--ja-->
## インターフェース

論理式に真理値を与える前に、どのようなデータが手元になければならないでしょうか。答えは、台と、それに対する一つの要求と、複合式の作り方ごとに一つずつ用意された演算です。それ以外はありません。演算どうしを結ぶ等式もなければ、真理値が何からできているかという仮定もありません。
<!--/-->

<!--en-->
The record takes two universe levels, and they measure different things. The [carrier]{.term-ref #carrier} `Ω` is a type in `Type ℓ'`{.Agda}, so `ℓ'` measures how large the truth values themselves are. The level `ℓ` is reserved for the index types of the quantifiers, which appear a few lines below; nothing forces a size relation between the two. Because the record contains a type as a field, it lives one universe above both, exactly as `Type ℓ`{.Agda} lives in `Type (ℓ-suc ℓ)`{.Agda}:

<div class="single-line-code"><code>TruthAlgebra ℓ ℓ' : Type (ℓ-suc (ℓ-max ℓ ℓ'))</code></div>
<!--zh-->
record 取两个宇宙层级，它们度量的东西并不相同。[载体]{.term-ref #carrier} `Ω` 是 `Type ℓ'`{.Agda} 中的类型，因此 `ℓ'` 度量真值本身有多大；层级 `ℓ` 留给几行之后出现的量词索引类型，两者之间没有任何大小关系的约束。由于 record 把一个类型作为字段收在其中，它住在比两者都高一层的宇宙里，正如 `Type ℓ`{.Agda} 住在 `Type (ℓ-suc ℓ)`{.Agda} 中：

<div class="single-line-code"><code>TruthAlgebra ℓ ℓ' : Type (ℓ-suc (ℓ-max ℓ ℓ'))</code></div>
<!--ja-->
レコードは二つの宇宙レベルを取り、それぞれ測るものが違います。[台]{.term-ref #carrier} `Ω` は `Type ℓ'`{.Agda} の型なので、`ℓ'` は真理値そのものの大きさを測ります。レベル `ℓ` は数行下に現れる量化子の添字の型のために取ってあり、両者の間に大きさの関係を課すものはありません。レコードは型をフィールドとして含むので、`Type ℓ`{.Agda} が `Type (ℓ-suc ℓ)`{.Agda} に住むのとちょうど同じように、両者より一つ上の宇宙に住みます。

<div class="single-line-code"><code>TruthAlgebra ℓ ℓ' : Type (ℓ-suc (ℓ-max ℓ ℓ'))</code></div>
<!--/-->

```agda
record TruthAlgebra (ℓ ℓ' : Level) : Type (ℓ-suc (ℓ-max ℓ ℓ')) where
  field
    Ω      : Type ℓ'
```

<!--en-->
The one requirement on the carrier is that it be an h-set. Read it as a statement about equality between truth values: two truth values may well be equal, but the proofs that they are equal carry no further distinguishable structure, so <span class="prose-annotation-target">an equation between truth values is itself a proposition</span><aside class="prose-annotation-note">Which is what makes such an equation usable as a truth value in turn. In the instance below the field is discharged by `isSetHProp`{.Agda}, and the model chapter uses that same lemma directly when it checks that realizing a class is a proposition rather than heavier data.</aside>. Without the requirement, "these two formulas receive the same value" would be structure rather than a statement, and could not be handled like any other proposition.
<!--zh-->
对载体只有一项要求：它必须是 h-集合。可以把这项要求读作关于真值之间相等的陈述：两个真值当然可以相等，但「它们相等」的证明之间不再保留可区分的结构，因此<span class="prose-annotation-target">真值之间的等式本身是命题</span><aside class="prose-annotation-note">而这正使得这样的等式反过来又能充当真值。在下面的实例中，这个字段由 `isSetHProp`{.Agda} 兑现；模型一章在检验「实现一个类是命题而非更重的数据」时，直接用的就是同一条引理。</aside>。若没有这项要求，「这两条公式取到同一个值」就成了结构而不是陈述，也就无法像其他命题那样被处理。
<!--ja-->
台に課す要求はただ一つ、それが h-集合であることです。これは真理値の間の等しさについての主張として読めます。二つの真理値が等しいことはあり得ますが、等しいことの証明の間には区別できる構造が残りません。したがって<span class="prose-annotation-target">真理値の間の等式そのものが命題になります</span><aside class="prose-annotation-note">これにより、その等式を今度は真理値として扱えるようになります。下の実例ではこのフィールドを `isSetHProp`{.Agda} が果たし、モデルの章は、クラスの実現がより重いデータではなく命題であることを確かめる際に、まさに同じ補題を直接使います。</aside>。この要求がなければ、「この二つの論理式は同じ値を取る」は主張ではなく構造になってしまい、他の命題と同じようには扱えません。
<!--/-->

```agda
    isSetΩ : isSet Ω
```

<!--en-->
Conjunction, disjunction and implication are the ways of joining two formulas into one, so each is a function taking two truth values to a truth value:

<div class="single-line-code"><code>Ω → Ω → Ω</code></div>

The three names share a single signature line, which declares all of them at that type. This is exactly where the chapter's distinction bites. The field says that an operation named `_⊓_` exists and has that shape. It does not say that `p ⊓ q` equals `q ⊓ p`, nor that `p ⊓ p` equals `p`, nor that `⊓` distributes over `⊔`. A proof that works for an arbitrary truth algebra can only push values through these operations; it cannot rearrange them.
<!--zh-->
合取、析取与蕴涵是把两条公式接成一条的方式，因此各自都是把两个真值送到一个真值的函数：

<div class="single-line-code"><code>Ω → Ω → Ω</code></div>

三个名字共用一行签名，这一行把它们一并声明为该类型。本章的那个区分正是在这里起作用。字段只说存在一个名为 `_⊓_` 的运算且具有这个形状；它并不说 `p ⊓ q` 等于 `q ⊓ p`，不说 `p ⊓ p` 等于 `p`，也不说 `⊓` 对 `⊔` 有分配律。对任意真值代数都成立的证明，只能把值沿着这些运算推送，而不能重新排布它们。
<!--ja-->
連言、選言、含意は二つの論理式を一つに結ぶ方法なので、いずれも二つの真理値を一つの真理値へ送る関数です。

<div class="single-line-code"><code>Ω → Ω → Ω</code></div>

三つの名前は一行のシグネチャを共有し、その一行がまとめて同じ型として宣言します。本章の区別が効くのはまさにここです。フィールドが述べるのは、`_⊓_` という名前の演算があり、この形をしている、ということだけです。`p ⊓ q` が `q ⊓ p` に等しいとも、`p ⊓ p` が `p` に等しいとも、`⊓` が `⊔` に分配するとも述べません。任意の真理値代数について通用する証明は、これらの演算に沿って値を送ることしかできず、値を組み替えることはできません。
<!--/-->

```agda
    _⊓_ _⊔_ _⇒_ : Ω → Ω → Ω
```

<!--en-->
Negation takes one truth value to one, and the two constants are truth values outright, the values a formula receives when it asserts nothing and when it asserts the absurd. The signature names all four even though the object language will not need all of them: it has no negation symbol of its own, since `¬̇ φ` is defined as `φ ⇒̇ ⊥̇`, and likewise `⊤̇` is `⊥̇ ⇒̇ ⊥̇`. The satisfaction clauses of the next chapter accordingly reach for `⊓`, `⊔`, `⇒` and `⊥` among the finitary operations. An algebra of truth values is nevertheless expected to be able to say what its own negation and its own truth are, and the interface asks for them.
<!--zh-->
否定把一个真值送到一个真值，两个常量则直接就是真值：它们分别是公式什么都不断言时与断言荒谬时所取的值。签名把四者一并列出，尽管对象语言并不需要全部：它没有自己的否定符号，因为 `¬̇ φ` 定义为 `φ ⇒̇ ⊥̇`，同样地 `⊤̇` 就是 `⊥̇ ⇒̇ ⊥̇`。于是下一章的满足子句在有限运算中取用的是 `⊓`、`⊔`、`⇒` 与 `⊥`。尽管如此，一个真值代数仍应能说出自己的否定与自己的真，接口也就要求它给出。
<!--ja-->
否定は一つの真理値を一つの真理値へ送り、二つの定数はそのまま真理値です。それぞれ、論理式が何も主張しないときと、不条理を主張するときに受け取る値です。シグネチャは四つすべてを挙げますが、対象言語がそのすべてを必要とするわけではありません。対象言語は自前の否定記号を持たず、`¬̇ φ` は `φ ⇒̇ ⊥̇` として定義され、同様に `⊤̇` は `⊥̇ ⇒̇ ⊥̇` です。したがって次章の充足の節が有限の演算から取るのは `⊓`、`⊔`、`⇒`、`⊥` です。それでも真理値の代数は自分の否定と自分の真を語れるべきであり、インターフェースはそれらを求めます。
<!--/-->

```agda
    ¬_     : Ω → Ω
    ⊤ ⊥    : Ω
```

<!--en-->
Quantifiers have a different shape, and the difference is the point. A quantifier does not combine two values; it combines a whole family of them into one. Given an index type `A` and a family `P : A → Ω`, the two operations form

$$\bigwedge_{x : A} P\,x \qquad\text{and}\qquad \bigvee_{x : A} P\,x,$$

written `⋀ A P` and `⋁ A P`. Their shape is therefore

<div class="single-line-code"><code>(A : Type ℓ) → (A → Ω) → Ω</code></div>

and this is where the level `ℓ` finally earns its place: it is the size of the domain a quantifier may range over. Making the index type an explicit argument keeps that domain visible. In the next chapter the semantics supplies the structure's carrier as the index, so that a universally quantified formula is evaluated by combining the body over every element of the domain:

<div class="single-line-code" data-note="This line is quoted from the satisfaction clauses of the next chapter; it is shown here only to say what the index type will be."><code>γ ⊨ (∀̇ φ)  =  ⋀ S (λ x → (x ∷ γ) ⊨ φ)</code></div>
<!--zh-->
量词的形状与前面不同，而这个不同正是要点所在。量词不是把两个值合并起来，而是把一整族值汇集成一个。给定索引类型 `A` 与族 `P : A → Ω`，两个运算分别形成

$$\bigwedge_{x : A} P\,x \qquad\text{与}\qquad \bigvee_{x : A} P\,x,$$

写作 `⋀ A P` 与 `⋁ A P`。于是它们的形状是

<div class="single-line-code"><code>(A : Type ℓ) → (A → Ω) → Ω</code></div>

层级 `ℓ` 的位置到这里才真正落实：它就是量词可以取遍的那个论域的大小。把索引类型做成显式参数，正是为了让这个论域保持可见。在下一章，语义把结构的载体当作索引供给，于是一条全称公式的求值方式，就是把主体在论域的每个元素上汇集起来：

<div class="single-line-code" data-note="这一行引自下一章的满足子句，此处只是为了说明索引类型将取什么。"><code>γ ⊨ (∀̇ φ)  =  ⋀ S (λ x → (x ∷ γ) ⊨ φ)</code></div>
<!--ja-->
量化子の形はこれまでと異なり、その違いこそが要点です。量化子は二つの値をまとめるのではなく、族全体を一つの値にまとめます。添字の型 `A` と族 `P : A → Ω` が与えられると、二つの演算はそれぞれ

$$\bigwedge_{x : A} P\,x \qquad\text{および}\qquad \bigvee_{x : A} P\,x$$

を作り、`⋀ A P`、`⋁ A P` と書かれます。したがってその形は次のとおりです。

<div class="single-line-code"><code>(A : Type ℓ) → (A → Ω) → Ω</code></div>

レベル `ℓ` がようやく役目を得るのはここです。それは量化子が動きうる領域の大きさです。添字の型を明示的な引数にしておくのは、その領域を見えるようにしておくためです。次章では意味論が構造の台を添字として与えるので、全称の論理式は、本体を領域のすべての要素にわたってまとめることで評価されます。

<div class="single-line-code" data-note="この行は次章の充足の節からの引用であり、添字の型が何になるかを示すためだけに掲げています。"><code>γ ⊨ (∀̇ φ)  =  ⋀ S (λ x → (x ∷ γ) ⊨ φ)</code></div>
<!--/-->

```agda
    ⋀ ⋁    : (A : Type ℓ) → (A → Ω) → Ω
```

<!--en-->
The operations have been named; the next two lines say how expressions built from them are to be read. A fixity declaration gives an operator a precedence number and an associativity: the higher the number, the tighter the operator binds, and `infixr` means that a repeated operator groups to the right. Conjunction and disjunction sit at 12, implication lower at 10, so implication is the loosest of the three and `p ⊓ q ⇒ r` is read as `(p ⊓ q) ⇒ r`. Grouping to the right makes `p ⇒ q ⇒ r` mean `p ⇒ (q ⇒ r)`, the reading under which a chain of implications is a function of its successive hypotheses. Both conventions are the ones ordinary mathematical writing already follows. The [Agda manual on mixfix operators](https://agda.readthedocs.io/en/v2.8.0/language/mixfix-operators.html) gives the general rules.
<!--zh-->
运算已经命名，接下来两行则说明由它们构成的表达式该如何读。结合性声明为一个算符指定优先级数字与结合方向：数字越高结合得越紧，而 `infixr` 表示同一算符重复出现时向右结合。合取与析取取 12，蕴涵取较低的 10，因此蕴涵在三者中结合得最松，`p ⊓ q ⇒ r` 读作 `(p ⊓ q) ⇒ r`。向右结合使 `p ⇒ q ⇒ r` 意为 `p ⇒ (q ⇒ r)`，在这种读法下，一串蕴涵就是以各个前提为自变量的函数。这两条约定都与通常的数学书写一致。[Agda 手册的混合算符一节](https://agda.readthedocs.io/en/v2.8.0/language/mixfix-operators.html)给出了一般规则。
<!--ja-->
演算には名前が付きました。続く二行は、それらから組み立てた式をどう読むかを定めます。結合性の宣言は、演算子に優先順位の数と結合の向きを与えます。数が大きいほど強く結び付き、`infixr` は同じ演算子が繰り返されたとき右に寄せて groupings することを表します。連言と選言は 12、含意はより低い 10 なので、三つの中で含意が最も緩く結び付き、`p ⊓ q ⇒ r` は `(p ⊓ q) ⇒ r` と読まれます。右に寄せる約束により `p ⇒ q ⇒ r` は `p ⇒ (q ⇒ r)` を意味し、この読み方のもとで含意の連なりは、次々に現れる仮定を引数とする関数になります。どちらの約束も、通常の数学の書き方がすでに従っているものです。一般規則は [Agda マニュアルのミックスフィックス演算子の節](https://agda.readthedocs.io/en/v2.8.0/language/mixfix-operators.html)にあります。
<!--/-->

```agda

  infixr 12 _⊓_ _⊔_
  infixr 10 _⇒_
```

<!--en-->
Negation binds tightest of all, at 13, so `¬ p ⊓ q` means `(¬ p) ⊓ q`: the negation applies to `p` alone, again as usual mathematical convention would suggest. It is declared with `infix` rather than `infixr` because it takes a single argument, so there is no repetition to group in either direction.
<!--zh-->
否定的结合力最强，取 13，因此 `¬ p ⊓ q` 意为 `(¬ p) ⊓ q`：否定只作用于 `p`，同样与通常的数学约定一致。它用 `infix` 而不是 `infixr` 声明，因为它只取一个自变量，不存在需要向某个方向归组的重复。
<!--ja-->
否定は 13 で最も強く結び付くので、`¬ p ⊓ q` は `(¬ p) ⊓ q` を意味し、否定は `p` だけに働きます。これもまた通常の数学の約束どおりです。宣言に `infixr` ではなく `infix` を使うのは、引数が一つで、どちらの向きにも寄せるべき繰り返しがないからです。
<!--/-->

```agda
  infix  13 ¬_
```

<!--en-->
## The canonical instance: hProp

The interface is now filled in once, and this single instance carries the entire development. The carrier becomes `hProp ℓ`{.Agda}, the universe of propositions the Prelude introduced. A formula is then assigned a proposition as its value, and satisfaction can be read proof-theoretically: to establish a formula is to inhabit the proposition it was assigned.
<!--zh-->
## 典范实例：hProp

现在把接口填写一次，而这唯一的实例承载了全部后续发展。载体取为 `hProp ℓ`{.Agda}，即《基础词汇》引入的命题宇宙。于是公式的值是一个命题，满足关系也就可以按证明来读：证明一条公式成立，就是给出它所取到的那个命题的元素。
<!--ja-->
## 正準な実例：hProp

ここでインターフェースを一度だけ埋めます。そしてこの唯一の実例が、以後の展開のすべてを支えます。台は「基礎語彙」で導入した命題の宇宙 `hProp ℓ`{.Agda} になります。すると論理式には命題が値として割り当てられ、充足は証明論的に読めます。論理式を示すとは、それに割り当てられた命題の要素を与えることです。
<!--/-->

<!--en-->
The levels follow from that choice. Propositions whose underlying types lie in `Type ℓ`{.Agda} form the type

<div class="single-line-code"><code>hProp ℓ : Type (ℓ-suc ℓ)</code></div>

which sits one universe up, so the carrier level `ℓ'` of the interface is `ℓ-suc ℓ` here, while the quantifier level stays `ℓ`. The instance therefore has type `TruthAlgebra ℓ (ℓ-suc ℓ)`: quantification ranges over types of size `ℓ`, and the values it produces are one size larger. This is the same gap the Prelude described when it observed that a universe is a type in the next universe up.

The level is taken as an explicit argument, so the instance is written `hPropAlgebra ℓ` at every use rather than left to inference. That is the honest choice here: the level does not appear in a way that could be recovered from the surroundings at a call site, and every later chapter names it when it fixes the truth algebra it works over.

The instance itself is written as a record expression: a value for every field, listed between braces and separated by semicolons. It is the alternative to applying a constructor, and it suits a long interface, since each field can be given its own line with its name in front of it. The lines that follow fill the fields in the order the record declared them.
<!--zh-->
层级由这一选择决定。底层类型属于 `Type ℓ`{.Agda} 的命题组成类型

<div class="single-line-code"><code>hProp ℓ : Type (ℓ-suc ℓ)</code></div>

它比 `Type ℓ` 高一层；因此接口中的载体层级 `ℓ'` 在这里是 `ℓ-suc ℓ`，而量词层级仍是 `ℓ`。于是实例的类型是 `TruthAlgebra ℓ (ℓ-suc ℓ)`：量化取遍大小为 `ℓ` 的类型，而它产出的值则大一号。这正是《基础词汇》指出「宇宙本身是上一层宇宙中的类型」时所说的那个落差。

层级取为显式参数，因此每次使用时都写成 `hPropAlgebra ℓ`，而不交给推断。这里这样做是诚实的：在调用处，层级并不以能从上下文回收的方式出现，而后续每一章在固定自己所依托的真值代数时，也都会把它写出来。

实例本身写成一个 record 表达式：为每个字段给出一个值，列在花括号之间，以分号分隔。这是施加构造子之外的另一种写法，适合较长的接口，因为每个字段都可以独占一行，并在前面写上自己的名字。随后各行就按 record 声明字段的顺序逐一填写。
<!--ja-->
レベルはこの選択から定まります。基底の型が `Type ℓ`{.Agda} に属する命題は、

<div class="single-line-code"><code>hProp ℓ : Type (ℓ-suc ℓ)</code></div>

という型をなし、これは一つ上の宇宙にあります。したがってインターフェースの台のレベル `ℓ'` はここでは `ℓ-suc ℓ` であり、量化子のレベルは `ℓ` のままです。実例の型は `TruthAlgebra ℓ (ℓ-suc ℓ)` になります。量化は大きさ `ℓ` の型を動き、生み出される値は一つ大きい、というわけです。これは「基礎語彙」が、宇宙はそれ自身一つ上の宇宙の型である、と述べたときの落差と同じものです。

レベルは明示的な引数として取ります。そのため使用のたびに `hPropAlgebra ℓ` と書き、推論には任せません。ここではそれが誠実な選択です。呼び出し側では、レベルは周囲から回復できる形では現れませんし、以後の各章も、自分が依拠する真理値代数を固定するときにレベルを書き記します。

実例そのものはレコード式として書かれます。すべてのフィールドに値を与え、波括弧の間にセミコロンで区切って並べるのです。構成子を適用する書き方に代わるもので、長いインターフェースに向いています。各フィールドが自分の名前を前に置いて一行を占められるからです。続く各行は、レコードが宣言した順にフィールドを埋めていきます。
<!--/-->

```agda
hPropAlgebra : ∀ ℓ → TruthAlgebra ℓ (ℓ-suc ℓ)
hPropAlgebra ℓ = record
  { Ω      = hProp ℓ
```

<!--en-->
The requirement on the carrier is discharged by a lemma the Prelude already listed: `isSetHProp`{.Agda} says that `hProp ℓ`{.Agda} is an h-set. Propositions may of course differ from one another, but a proof that two of them are equal retains no further structure, which is exactly the condition the interface asked for.
<!--zh-->
对载体的那项要求，由《基础词汇》已经列出的一条引理兑现：`isSetHProp`{.Agda} 说明 `hProp ℓ`{.Agda} 是 h-集合。不同的命题当然可以彼此相异，但「其中两个相等」的证明不再保留更多结构，而这恰好就是接口所要求的条件。
<!--ja-->
台への要求は、「基礎語彙」がすでに挙げていた補題で果たされます。`isSetHProp`{.Agda} は `hProp ℓ`{.Agda} が h-集合であることを述べます。命題どうしが異なることはもちろんありますが、そのうち二つが等しいことの証明にはそれ以上の構造が残りません。これがまさにインターフェースの求めた条件です。
<!--/-->

```agda
  ; isSetΩ = isSetHProp
```

<!--en-->
The three binary connectives are the corresponding operations on propositions. Each takes the underlying types of its arguments, forms a type out of them, and supplies the proof that the result is again a proposition, so that the whole thing is once more an element of the carrier. Conjunction pairs the two underlying types; implication is the function type between them, a proposition because a family of propositions is closed under `Π` types, which is the content of `isPropΠ`{.Agda} from the Prelude; disjunction needs the extra step described in the next paragraph.

One detail makes the fit possible at all. The library states each of these operations for two arguments at possibly different levels and returns a proposition at the larger of the two, whereas the field asks for `Ω → Ω → Ω` with a single `Ω`. Here both arguments are at level `ℓ`, and the larger of a level and itself is that level, so the library's operation has exactly the shape the field requires, with no adjustment.

<details class="prose-disclosure"><summary>Expand the underlying definitions</summary>
<ul><li><code>P ⊓ Q</code> is the product of the underlying types of <code>P</code> and <code>Q</code>.</li><li><code>P ⇒ Q</code> is the function type from the underlying type of <code>P</code> to that of <code>Q</code>.</li><li><code>P ⊔ Q</code> is the disjoint sum of the two underlying types, cut down to a proposition as the next paragraph describes.</li><li><code>¬ P</code> is the function type from the underlying type of <code>P</code> to the empty type.</li><li><code>⊤</code> is a type with exactly one element.</li></ul>
</details>
<!--zh-->
三个二元联结词取命题上的相应运算。每一个都取两个自变量的底层类型，用它们造出一个类型，再给出「所得结果仍是命题」的证明，于是整体又成为载体的一个元素。合取把两个底层类型配成对；蕴涵是二者之间的函数类型，它是命题，因为一族命题在 Π 类型下封闭，这正是《基础词汇》中 `isPropΠ`{.Agda} 的内容；析取则需要下一段所述的额外一步。

有一个细节才使这种对接成为可能。库把这些运算的两个自变量放在可以不同的层级上陈述，返回的命题落在二者中较大的那一层；而字段要求的是只有一个 `Ω` 的 `Ω → Ω → Ω`。这里两个自变量都在层级 `ℓ`，而一个层级与自身中较大的那个仍是它自己，于是库中的运算恰好具有字段所要求的形状，无需任何调整。

<details class="prose-disclosure"><summary>展开底层定义</summary>
<ul><li><code>P ⊓ Q</code> 是 <code>P</code> 与 <code>Q</code> 底层类型的积。</li><li><code>P ⇒ Q</code> 是从 <code>P</code> 的底层类型到 <code>Q</code> 的底层类型的函数类型。</li><li><code>P ⊔ Q</code> 是两个底层类型的不交和，并按下一段所述裁剪为命题。</li><li><code>¬ P</code> 是从 <code>P</code> 的底层类型到空类型的函数类型。</li><li><code>⊤</code> 是恰有一个元素的类型。</li></ul>
</details>
<!--ja-->
三つの二項結合子には、命題上の対応する演算を用います。どれも二つの引数の基底型を取り、それらから型を作り、「結果がふたたび命題である」ことの証明を添えます。こうして全体がふたたび台の要素になります。連言は二つの基底型を対にします。含意は両者の間の関数型であり、命題の族が Π 型について閉じていること、すなわち「基礎語彙」の `isPropΠ`{.Agda} の内容によって命題になります。選言には次の段落で述べる一手間が必要です。

この噛み合わせを可能にしている細部が一つあります。ライブラリはこれらの演算を、二つの引数が異なるレベルにあってもよい形で述べ、結果の命題を二つのうち大きい方のレベルに置きます。一方でフィールドが求めるのは、`Ω` が一つだけの `Ω → Ω → Ω` です。ここでは両方の引数がレベル `ℓ` にあり、あるレベルとそれ自身のうち大きい方はそのレベルなので、ライブラリの演算は調整なしにフィールドの求める形をちょうど持ちます。

<details class="prose-disclosure"><summary>基底の定義を開く</summary>
<ul><li><code>P ⊓ Q</code> は <code>P</code> と <code>Q</code> の基底型の積です。</li><li><code>P ⇒ Q</code> は <code>P</code> の基底型から <code>Q</code> の基底型への関数型です。</li><li><code>P ⊔ Q</code> は二つの基底型の直和を、次の段落で述べるしかたで命題へ切り詰めたものです。</li><li><code>¬ P</code> は <code>P</code> の基底型から空型への関数型です。</li><li><code>⊤</code> はちょうど一つの要素を持つ型です。</li></ul>
</details>
<!--/-->

```agda
  ; _⊓_    = Logic._⊓_
  ; _⊔_    = Logic._⊔_
  ; _⇒_    = Logic._⇒_
```

<!--en-->
Disjunction is the first place where a construction has to be cut down to size. The disjoint sum of two types is not a proposition: an element of it records which side it came from, and two elements from different sides are not equal. **[Propositional truncation]{.term-intro #propositional-truncation}** repairs this. It sends a type to a proposition with the same inhabitedness: whatever was there is still there, in the sense that the truncation has an element exactly when the original did, but all its elements are made equal, so nothing can be read back out about which one it was. Disjunction of propositions is the truncation of the sum, so `p ⊔ q` records that one of the two holds without retaining which.
<!--zh-->
析取是第一处需要把构造裁剪到合适大小的地方。两个类型的不交和并不是命题：它的元素记录着自己来自哪一侧，而来自不同侧的两个元素并不相等。**[命题截断]{.term-intro #propositional-truncation}**修补了这一点。它把一个类型送到一个有元性相同的命题：原先有的仍然有，即截断有元素当且仅当原类型有元素，但它的所有元素都被弄成相等，因此无法再读出那个元素究竟是哪一个。命题的析取就是和的截断，于是 `p ⊔ q` 记录二者之一成立，却不保留是哪一个。
<!--ja-->
選言は、構成を大きさに合わせて切り詰める必要が最初に生じる箇所です。二つの型の直和は命題ではありません。その要素はどちら側から来たかを記録しており、異なる側から来た二つの要素は等しくないからです。**[命題的切り詰め]{.term-intro #propositional-truncation}**がこれを直します。切り詰めは、型を、要素の有無が同じ命題へ送ります。元にあったものはそのまま残り、すなわち切り詰めに要素があるのは元の型に要素があるとき、かつそのときに限ります。しかしその要素はすべて等しくされるので、それがどれであったかを読み戻すことはできません。命題の選言は直和の切り詰めなので、`p ⊔ q` は二つのうち一方が成り立つことを記録しますが、どちらであるかは残しません。
<!--/-->

<!--en-->
Negation and truth are again the library's operations, and here a detail of universe levels shows through. The library's truth is universe-polymorphic,

<div class="single-line-code"><code>⊤ : ∀ {ℓ} → hProp ℓ</code></div>

so it can be reused at whatever level the instance is built. Its falsity is not: it is <span class="prose-annotation-target">built from the empty type that lives at the bottom level</span><aside class="prose-annotation-note">So `Logic.⊥ : hProp ℓ-zero`, and an instance at level `ℓ` cannot take it as the value of its `⊥` field, since the field must be an element of `hProp ℓ`.</aside>, and the next line therefore writes falsity out by hand instead.
<!--zh-->
否定与真同样取库中的运算，而这里透出一个关于宇宙层级的细节。库中的真是宇宙多态的，

<div class="single-line-code"><code>⊤ : ∀ {ℓ} → hProp ℓ</code></div>

因此无论实例在哪一层构造，它都可以照用。库中的假则不然：它<span class="prose-annotation-target">由住在最底层的空类型造出</span><aside class="prose-annotation-note">即 `Logic.⊥ : hProp ℓ-zero`；层级 `ℓ` 上的实例不能拿它充当自己 `⊥` 字段的值，因为该字段必须是 `hProp ℓ` 的元素。</aside>，所以下一行改为把假显式写出。
<!--ja-->
否定と真にもふたたびライブラリの演算を使いますが、ここで宇宙レベルに関する細部が顔を出します。ライブラリの真は宇宙多相であり、

<div class="single-line-code"><code>⊤ : ∀ {ℓ} → hProp ℓ</code></div>

実例をどのレベルで作るとしてもそのまま使えます。偽はそうではありません。それは<span class="prose-annotation-target">最下位のレベルに住む空型から作られており</span><aside class="prose-annotation-note">つまり `Logic.⊥ : hProp ℓ-zero` です。レベル `ℓ` の実例は、`⊥` フィールドの値としてこれを取れません。フィールドは `hProp ℓ` の要素でなければならないからです。</aside>、そのため次の行では偽を手ずから書き下します。
<!--/-->

```agda
  ; ¬_     = Logic.¬_
  ; ⊤      = Logic.⊤
```

<!--en-->
Written out, falsity is the pair `(⊥* , isProp⊥*)`: the Prelude's empty type, which is available at every level, together with the proof that it is a proposition. The pair is an element of `hProp ℓ`{.Agda} because that is what an element of the universe of propositions is, a type with a certificate of propositionhood. It is worth keeping the two apart on the page: `⊥` is a truth value, an element of the carrier, while `⊥*`{.Agda} is the type underlying it in this particular instance.
<!--zh-->
显式写出来，假就是对 `(⊥* , isProp⊥*)`：《基础词汇》中在每个层级都可用的空类型，连同它是命题的证明。这个对之所以是 `hProp ℓ`{.Agda} 的元素，是因为命题宇宙的元素本就是「一个类型加一份命题性证书」。纸面上值得把二者分清：`⊥` 是真值，是载体的元素；而 `⊥*`{.Agda} 是在这个特定实例中位于其底下的类型。
<!--ja-->
書き下せば、偽は対 `(⊥* , isProp⊥*)` です。どのレベルでも使える「基礎語彙」の空型と、それが命題であることの証明の組です。この対が `hProp ℓ`{.Agda} の要素であるのは、命題の宇宙の要素とはまさに、型と命題性の証明書の組だからです。紙の上では二つを分けておく価値があります。`⊥` は真理値であり台の要素、`⊥*`{.Agda} はこの特定の実例でその下にある型です。
<!--/-->

```agda
  ; ⊥      = ⊥* , isProp⊥*
```

<!--en-->
The quantifiers come last. Universal quantification over a family `P : A → hProp ℓ` is the dependent function type `∀ x → ⟨ P x ⟩`, packaged with the proof that it is a proposition: an element of it produces a proof of `P x` for every `x`, which is what a universally quantified statement should offer. Existential quantification is the propositionally truncated dependent pair: it asserts that some `x` satisfies `P` while forgetting which, so the witness cannot be read back out. That asymmetry is deliberate and is felt much later, where getting a genuine function out of such an existential needs a choice principle.

The two library operations take the index type implicitly, inferring it from the family, whereas the interface asks for it explicitly. The small lambdas below are exactly that adjustment: they receive the index type as `A`, pass only the family to the library, and let inference recover what was dropped.
<!--zh-->
量词留在最后。对族 `P : A → hProp ℓ` 的全称量化是依值函数类型 `∀ x → ⟨ P x ⟩`，并配上它是命题的证明：它的元素为每个 `x` 都产出 `P x` 的证明，而这正是一条全称陈述所应提供的。存在量化则是命题截断的依值对：它断言某个 `x` 满足 `P`，却忘去是哪一个，因此见证无法再被读出。这种不对称是刻意的，它的效果要到很晚才显现：要从这样的存在陈述里取出一个真正的函数，需要一条选择原理。

库中这两个运算把索引类型取为隐式参数，从族中推断出来，而接口要求显式给出。下面那两个小的 lambda 做的正是这项调整：它们接收索引类型 `A`，只把族交给库，再让推断补回被丢下的部分。
<!--ja-->
量化子は最後に来ます。族 `P : A → hProp ℓ` に対する全称量化は依存関数型 `∀ x → ⟨ P x ⟩` であり、それが命題であることの証明を添えて包まれます。その要素は各 `x` に `P x` の証明を与えます。これは全称の主張が提供すべきものにほかなりません。存在量化は命題的切り詰めを施した依存対です。ある `x` が `P` を満たすと主張しつつ、どれであるかは忘れるので、証人を読み戻すことはできません。この非対称性は意図されたもので、その効きめはずっと後に現れます。そのような存在の主張から本物の関数を取り出すには、選択原理が要るのです。

ライブラリの二つの演算は添字の型を暗黙の引数として取り、族から推論します。一方インターフェースはそれを明示的に求めます。下の小さなラムダはまさにその調整です。添字の型を `A` として受け取り、族だけをライブラリへ渡し、落とした分は推論に任せます。
<!--/-->

```agda
  ; ⋀      = λ A P → Logic.∀[]-syntax P
  ; ⋁      = λ A P → Logic.∃[]-syntax P }
```

<!--en-->
## Other truth-value instances

Nothing in the definition of `TruthAlgebra`{.Agda} requires its carrier to consist of propositions. Another instance, a two-element algebra or a Boolean algebra of truth values, would have to supply an h-set carrier and every operation in the signature, including the two that act on families indexed by an arbitrary `Type ℓ`{.Agda}.

The two halves of that task are not equally hard. The finitary half is the classical truth table: with two values, conjunction, disjunction, implication and negation are each settled by four cases or two. The infinitary half is the demanding one. To give `⋀ A P` a two-valued answer is to decide whether `P x` holds for every `x` in an arbitrary domain, and deciding that is not something the host supplies for a domain it knows nothing about. A proposition-valued carrier has no such trouble: the conjunction of a family is simply the dependent function type over it, which exists for any family whatsoever. That is the structural reason the canonical instance takes propositions as its truth values rather than two of them.

This chapter constructs only `hPropAlgebra`{.Agda}.
<!--zh-->
## 其他真值实例

`TruthAlgebra`{.Agda} 的定义并不要求载体由命题组成。另一个实例，比如二元代数或真值的布尔代数，仍须给出具有 h-集合性的载体以及签名中的全部运算，其中包括作用于以任意 `Type ℓ`{.Agda} 为索引的族的那两个。

这项任务的两半难度并不相同。有限的那一半就是经典的真值表：只有两个值时，合取、析取、蕴涵与否定各自由四种或两种情形定死。无穷的那一半才是苛刻的。要给 `⋀ A P` 一个二值的答案，就是要判定在任意论域上是否每个 `x` 都使 `P x` 成立，而对一个宿主一无所知的论域，这样的判定并不是现成可得的。命题值的载体没有这个麻烦：一族的合取就是它上面的依值函数类型，而这对任何族都存在。这正是典范实例以命题而不是以两个值作为真值的结构性原因。

本章只构造 `hPropAlgebra`{.Agda}。
<!--ja-->
## 他の真理値の実例

`TruthAlgebra`{.Agda} の定義は、台が命題からなることを要求しません。別の実例、たとえば二元の代数や真理値のブール代数であっても、h-集合である台とシグネチャの全演算を与えなければならず、そこには任意の `Type ℓ`{.Agda} を添字とする族に作用する二つの演算も含まれます。

この仕事の二つの半分は、難しさが同じではありません。有限の側は古典的な真理値表です。値が二つなら、連言・選言・含意・否定はそれぞれ四通りか二通りの場合で決まります。厳しいのは無限の側です。`⋀ A P` に二値の答えを与えるとは、任意の領域のすべての `x` について `P x` が成り立つかを判定することであり、ホストが何も知らない領域について、その判定は与えられていません。命題値の台にはこの困難がありません。族の連言はその上の依存関数型にほかならず、どんな族についても存在するからです。正準な実例が真理値として二つの値ではなく命題を取るのは、この構造的な理由によります。

本章で構成するのは `hPropAlgebra`{.Agda} だけです。
<!--/-->

<!--en-->
## Recap

This chapter fixed what a formula may evaluate to, and did it twice over:

- a **truth algebra** is a carrier of truth values, a requirement that the carrier be an h-set, and one operation per way of forming a compound formula;
- the record states a signature and no laws, so a theorem about an arbitrary truth algebra cannot lean on an equation that was never assumed;
- the binary connectives have the shape `Ω → Ω → Ω`, while the quantifiers combine a whole family indexed by a type of size `ℓ`, which is what the first level of the record is for;
- fixity declarations fix how expressions built from these operations are read, with implication loosest and negation tightest;
- `hPropAlgebra`{.Agda} is the instance the development runs on: truth values are propositions, the h-set requirement is met by `isSetHProp`{.Agda}, disjunction and existential quantification are propositionally truncated, and falsity is written out as `⊥*`{.Agda} with its propositionhood proof because the library's falsity sits at the bottom level.

With truth values in hand, the next chapters can say what a structure interprets the language into, and how a formula is evaluated there.
<!--zh-->
## 小结

本章确定了公式可以求值到什么，并且做了两遍：

- **真值代数**由真值的载体、载体是 h-集合这项要求，以及为每种复合公式构造方式各配的一个运算组成；
- record 只陈述签名而不陈述定律，因此关于任意真值代数的定理无法倚靠未曾假设的等式；
- 二元联结词的形状是 `Ω → Ω → Ω`，量词则汇集以大小为 `ℓ` 的类型为索引的整个族，record 的第一个层级正是为此而设；
- 结合性声明固定了由这些运算构成的表达式该如何读：蕴涵最松，否定最紧；
- `hPropAlgebra`{.Agda} 是后续发展运行于其上的实例：真值即命题，h-集合的要求由 `isSetHProp`{.Agda} 满足，析取与存在量化经过命题截断，而假之所以写成 `⊥*`{.Agda} 连同其命题性证明，是因为库中的假住在最底层。

有了真值，接下来的章节便可以说明结构把语言解释到什么之中，以及公式在其中如何求值。
<!--ja-->
## まとめ

本章は、論理式が何へ評価されうるかを定め、しかもそれを二度行いました。

- **真理値代数**とは、真理値の台と、その台が h-集合であるという要求と、複合式の作り方ごとに一つずつの演算からなります。
- レコードが述べるのはシグネチャだけで法則ではありません。したがって任意の真理値代数についての定理は、仮定されなかった等式に寄りかかれません。
- 二項結合子の形は `Ω → Ω → Ω` であり、量化子は大きさ `ℓ` の型を添字とする族全体をまとめます。レコードの最初のレベルはそのためにあります。
- 結合性の宣言は、これらの演算から組み立てた式の読み方を定めます。含意が最も緩く、否定が最も強く結び付きます。
- `hPropAlgebra`{.Agda} は展開が走る実例です。真理値は命題であり、h-集合の要求は `isSetHProp`{.Agda} が満たし、選言と存在量化は命題的に切り詰められ、偽は `⊥*`{.Agda} と命題性の証明として書き下されます。ライブラリの偽が最下位のレベルに住むからです。

真理値が手に入ったので、次の章からは、構造が言語を何へ解釈するのか、そしてそこで論理式がどう評価されるのかを述べられます。
<!--/-->
