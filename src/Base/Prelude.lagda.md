<!--en-->
# Prelude

When studying set theory, we talk about sets and their elements, relations between sets, and functions from one set to another. A definition tells us what an object is, a theorem states a property it has, and a proof explains why that property holds. In this book, set theory is the **[object theory]{.term-intro #object-theory}** and cubical type theory is the **[metatheory]{.term-intro #metatheory}**: within cubical type theory, we construct models of set theory, interpret its sentences, and prove that these models satisfy the relevant axioms and theorems.

We write and check these constructions and proofs with the Agda proof assistant. Agda provides the formal language and its checking mechanisms, cubical type theory supplies the mathematical foundation for this formalisation, and the Cubical library collects definitions and theorems developed on that foundation. We call this Cubical Agda environment, which supports the formalisation of the object theory, the **[host]{.term-intro #host-environment}**. Thus, later references to a *type in the host*, a *function in the host*, or a *host-level construction* concern the metatheory rather than objects inside a model of set theory.

To read these developments, we first need to become acquainted with the basic vocabulary of the host.

This chapter begins with the basic notions of that language. We will meet them one at a time, considering both what they mean and how they are used in mathematical statements and proofs. There is no need to remember every symbol at once. As the same notions recur in later chapters, their uses will become more familiar; when needed, this chapter provides a place to return to their meanings.

## Traceable vocabulary

To make such references easier, we first explain where these basic notions come from and how to find their definitions.

In later chapters, you will see statements containing `import` near the beginning. They specify which names the chapter imports from which modules, identifying the concepts and results used in the arguments that follow. When a name is unfamiliar, these statements tell you where it comes from; clicking the name takes you to its definition.

The basic vocabulary collected in this chapter is an exception to this convention. These notions occur so frequently throughout the book that we gather them in `Base.Prelude`, which later chapters import as a whole without listing each name again. Here we list the selected definitions from the Cubical library and explain the meanings and uses needed to read this book, without developing each construction and proof inside the library. For further study, you can follow the name links to the original definitions or consult the Cubical library's documentation and learning materials on cubical type theory.

Before introducing this vocabulary, we explain two short lines of code:

<ul><li>The first line specifies the options Agda uses to check this chapter.
<details class="prose-disclosure"><summary>Expand option details</summary>
<ul><li><code>--cubical</code> enables language support for cubical type theory.</li><li><code>--safe</code> enables safe mode, which prohibits declaring unproved axioms and bypassing checks such as termination checking. Theorems that need additional assumptions can still be stated, but those assumptions must appear explicitly as parameters or premises.</li><li><code>--guardedness</code> enables checking associated with corecursive definitions. Such definitions can describe objects whose content continues to unfold, such as infinite sequences; the check constrains recursion so that the required content can be produced progressively. On a first reading, it is enough to know that this is an Agda setting for checking such definitions; its technical details can wait.</li></ul>
</details></li><li>The second line gives the module corresponding to this chapter its name.
Here <code>Base.Prelude</code> is the basic vocabulary module mentioned above. Later chapters use this name to import the vocabulary collected here, and the content following <code>where</code> forms the body of the module.</li></ul>
<!--zh-->
# 基础词汇

学习集合论时，我们谈论集合及其元素，也谈论集合之间的关系和函数。定义告诉我们所讨论的对象是什么，定理陈述这些对象具有怎样的性质，证明则说明这些性质为何成立。本书以集合论为**[对象理论]{.term-intro #object-theory}**，以立方类型论为**[元理论]{.term-intro #metatheory}**：我们在立方类型论中构造集合论的模型，解释集合论的语句，并证明这些模型满足相应的公理与定理。

这些构造和证明使用 Agda 证明助手书写并检查。Agda 提供形式语言和检查机制，立方类型论为这套形式化提供数学基础，Cubical 库则汇集了在此基础上建立的定义与定理。本书把承载对象理论形式化的这套 Cubical Agda 环境简称为**[宿主]{.term-intro #host-environment}**。因此，后文所说的「宿主中的类型」「宿主中的函数」或「宿主层的构造」，都属于元理论一侧，而不是集合论模型内部的对象。

要读懂这些内容，我们先要熟悉宿主中的基础词汇。

本章就从这套语言的基础概念开始。我们将逐个认识它们，既了解其含义，也看看它们如何用于数学陈述与证明。不必急于一次记住所有符号；随着这些概念在后续章节中反复出现，它们的用法会逐渐变得熟悉。需要时，也可以回到本章，重新查阅某个概念的含义。

## 词汇可溯源

为了便于这样的查阅，我们先说明这些基础概念从何而来，以及如何找到它们的定义。

阅读后续章节时，你会在章首看到一些包含 `import` 的语句。它们标明本章从哪些模块引入了哪些名称，相当于说明接下来的论证会用到哪些已有概念和结果。遇到不熟悉的名称时，可以先从这些语句确认它的来源，再点击名称查看具体定义。

本章集中引入的基础词汇是这项约定的一个例外。它们在全书中使用得十分频繁，因此统一收集在 `Base.Prelude` 中，供后续章节整体引入，不再逐个列出。我们会在这里列出所选用的 Cubical 库定义，并说明阅读本书所需的含义与用法，但不逐一展开库内部的构造和证明。希望进一步了解时，可以沿名称链接查阅原始定义，也可以结合 Cubical 库的文档及立方类型论的学习资料继续阅读。

在正式引入这些词汇之前，还有两行简短的代码需要说明：

<ul><li>第一行指定 Agda 检查本章时使用的选项。

<details class="prose-disclosure"><summary>展开选项说明</summary>
<ul><li><code>--cubical</code> 启用立方类型论的语言支持。</li><li><code>--safe</code> 启用安全模式，禁止直接宣告未经证明的公理，以及绕过终止性检查等做法；需要额外假设的定理仍可以书写，但这些假设必须明确出现在其参数或前提中。</li><li><code>--guardedness</code> 启用与余递归定义有关的检查。这类定义可以描述不断产生后续内容的对象，例如无限序列；检查的作用是约束递归的方式，使所需的内容能够逐步产生。初读本章时，只需知道这是 Agda 检查此类定义的一项设置，暂时不必掌握其中的技术细节。</li></ul>
</details></li><li>第二行为本章对应的模块命名。这里的 <code>Base.Prelude</code> 就是前面提到的基础词汇模块。后续章节通过这个名称引入本章汇集的词汇，而 <code>where</code> 之后的内容构成模块的正文。</li></ul>
<!--ja-->
# 基礎語彙

集合論を学ぶとき、私たちは集合とその要素、集合の間の関係や関数について考えます。定義は扱う対象が何であるかを示し、定理はその対象がどのような性質を持つかを述べ、証明はその性質がなぜ成り立つかを明らかにします。本書では、集合論を**[対象理論]{.term-intro #object-theory}**、立方型理論を**[メタ理論]{.term-intro #metatheory}**とします。つまり、立方型理論の中で集合論のモデルを構成し、集合論の文を解釈して、そのモデルが所定の公理や定理を満たすことを証明します。

これらの構成と証明は、証明支援系 Agda を用いて記述し、検査します。Agda は形式言語とその検査機構を提供し、立方型理論はこの形式化の数学的基礎を与え、Cubical ライブラリはその基礎の上で築かれた定義や定理を集めています。本書では、対象理論の形式化を支えるこの Cubical Agda の環境を**[ホスト]{.term-intro #host-environment}**と呼びます。したがって、後に現れる「ホストの型」「ホストの関数」「ホストレベルの構成」はいずれもメタ理論の側に属し、集合論のモデル内部の対象ではありません。

これらを読み解くために、まずはホストの基礎語彙に慣れていきましょう。

本章は、この言語の基礎概念から始めます。一つずつ取り上げ、その意味と、数学の主張や証明での使い方を見ていきます。すべての記号を一度に覚える必要はありません。後の章で同じ概念に繰り返し出会ううちに、その使い方にも慣れていくでしょう。必要なときには本章に戻り、概念の意味を確かめることもできます。

## 語彙の出所をたどる

そのような参照をしやすくするために、まず、これらの基礎概念がどこから来るのか、そして定義をどう探せばよいのかを説明します。

後の章では、冒頭に `import` を含む文が現れます。これは、どのモジュールからどの名前を導入するかを示し、その後の議論で使う既存の概念や結果を明らかにします。見慣れない名前があれば、まずこれらの文で出所を確かめ、名前をクリックして具体的な定義を参照できます。

本章にまとめる基礎語彙は、この約束の例外です。全書を通じて頻繁に使うため、`Base.Prelude` にまとめ、後の章では個々の名前を列挙せずに一括して導入します。ここでは Cubical ライブラリから選んだ定義を列挙し、本書を読むために必要な意味と使い方を説明しますが、ライブラリ内部の構成や証明を一つずつ展開することはしません。さらに学びたい場合は、名前のリンクから元の定義を参照したり、Cubical ライブラリの文書や立方型理論の学習資料を読んだりできます。

これらの語彙を導入する前に、二行の短いコードを説明します。

<ul><li>一行目は、Agda が本章を検査する際のオプションを指定します。

<details class="prose-disclosure"><summary>オプションの説明を開く</summary>
<ul><li><code>--cubical</code> は立方型理論の言語機能を有効にします。</li><li><code>--safe</code> は安全モードを有効にし、未証明の公理の宣言や停止性検査の回避などを禁止します。追加の仮定を必要とする定理も記述できますが、その仮定はパラメータや前提として明示する必要があります。</li><li><code>--guardedness</code> は余再帰的定義に関する検査を有効にします。この種の定義は、無限列のように次々と内容を生成する対象を記述できます。検査は再帰の仕方を制約し、必要な内容を順次生成できるようにします。初読では、そのような定義を検査するための Agda の設定だと理解すれば十分で、技術的な詳細を今すぐ学ぶ必要はありません。</li></ul>
</details></li><li>二行目は、本章に対応するモジュールに名前を付けます。ここでの <code>Base.Prelude</code> は、先ほど述べた基礎語彙のモジュールです。後の章では、この名前を使って本章にまとめた語彙を導入します。<code>where</code> の後に続く内容がモジュールの本体です。</li></ul>
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}
module Base.Prelude where
```

<!--en-->
With the two lines now identified, and the module body located after `where`, we can begin to explore the notions one at a time.
<!--zh-->
至此，两行代码的作用和模块正文的位置都已明确，下面开始逐个认识这些概念。
<!--ja-->
これで二行の役割と、`where` の後にあるモジュール本体が分かりました。ここから概念を一つずつ見ていきましょう。
<!--/-->

<!--en-->
## [Universe levels]{.term-intro #universe-level}

Type theory must distinguish the sizes of types. A type that quantifies over all types would contain itself, so the host sorts types into universes `Type ℓ`{.Agda}, one for each level `ℓ : Level`{.Agda}. Algebraically, universe levels form a join-semilattice with a bottom element, equipped with a successor operator: `ℓ-zero`{.Agda} is the bottom element, `ℓ-suc`{.Agda} is the successor operator and `ℓ-max`{.Agda} is the binary join. Each universe is itself a type:

<div class="single-line-code" data-note="This reader-facing line is Agda-like pseudocode, not a formal Agda code block. It is closer to code than a traditional mathematical display, but it is not promised to compile on its own. In formal precision, it lies between a conventional mathematical display and complete Agda code."><code>Type ℓ : Type (ℓ-suc ℓ)</code></div>

Whenever the book surveys a totality such as "all sets" or "all propositions", the attached level records how large that totality is taken to be.

<!--zh-->
## [宇宙层级]{.term-intro #universe-level}

类型论必须区分类型的大小。若一个类型能够无条件地量化所有类型，它就会包含自身；因此，宿主把类型分入宇宙 `Type ℓ`{.Agda}，每个层级 `ℓ : Level`{.Agda} 对应一个宇宙。从代数上看，宇宙层级形成一个带后继算子的有底并半格：`ℓ-zero`{.Agda} 是底元，`ℓ-suc`{.Agda} 是后继算子，`ℓ-max`{.Agda} 是二元并运算。每个宇宙本身也是类型：

<div class="single-line-code" data-note="这一行是面向读者的记号，不是正式的 Agda 代码块。它是一种接近 Agda 的伪代码：比传统数学公式更贴近代码，但不保证单独编译通过。就形式化的严格程度而言，它处于通常的数学展示和完整 Agda 代码之间。"><code>Type ℓ : Type (ℓ-suc ℓ)</code></div>

本书凡检视「所有集合」或「所有命题」这样的总体，陈述所附的层级就记录了该总体被当作多大。

<!--ja-->
## [宇宙レベル]{.term-intro #universe-level}

型理論では、型の大きさを区別しなければなりません。すべての型を量化する型があれば、それは自分自身を含んでしまいます。そこでホストは、各レベル `ℓ : Level`{.Agda} に一つずつある宇宙 `Type ℓ`{.Agda} へ型を分類します。代数的には、宇宙レベルは後続演算を備えた最小元付き結び半束をなします。`ℓ-zero`{.Agda} が最小元、`ℓ-suc`{.Agda} が後続演算、`ℓ-max`{.Agda} が二項の結びです。各宇宙はそれ自身も型です。

<div class="single-line-code" data-note="この一行は読者のための表記であり、正式な Agda コードブロックではありません。Agda に近い擬似コードで、通常の数学の式よりコードに近い表記ですが、それだけでコンパイルできるとは限りません。形式化の厳密さという点では、通常の数学的な表示と、完全な Agda コードの間に位置します。"><code>Type ℓ : Type (ℓ-suc ℓ)</code></div>

本書が「すべての集合」や「すべての命題」のような全体を扱うとき、主張に付いたレベルが、その全体をどの大きさとして扱うかを記録します。

<!--/-->

```agda
open import Cubical.Foundations.Prelude public
  using ( Type; Level; ℓ-zero; ℓ-suc; ℓ-max )
```

<!--en-->
## [Π types]{.term-intro #pi-type}

Many constructions later in the book need to provide data depending on each object. A Π type expresses this basic relationship.

Given a type `A` and a type `B x` for each `x : A`, we form the Π type:

<div class="single-line-code"><code>(x : A) → B x</code></div>

An element of a Π type is called a **[dependent function]{.term-intro #dependent-function}**. Given a dependent function `f`, it assigns to every `x : A` an element `f x` of `B x`. Because the type of the result depends on the input `x`, only after fixing the input do we know the type in which the corresponding output must lie.

When `B` does not depend on `x`, every output lies in the same type, and the dependent function specialises to an ordinary function:

<div class="single-line-code"><code>A → B</code></div>

An ordinary function gives an output in the same type for every input; a Π type gives, for every `x`, data belonging to the corresponding type `B x`.

<!--zh-->
## [Π 类型]{.term-intro #pi-type}

本书后面的许多构造都需要为每个对象给出一项依赖于它的数据。Π 类型正是表达这种关系的基本形式。

给定一个类型 `A`，以及对每个 `x : A` 指定的类型 `B x`，我们可以构造 Π 类型：

<div class="single-line-code"><code>(x : A) → B x</code></div>

Π 类型的元素称为**[依值函数]{.term-intro #dependent-function}**。给定一个依值函数 `f`，它为每个 `x : A` 给出一个属于 `B x` 的元素 `f x`。由于结果所在的类型取决于输入 `x`，只有确定输入以后，才能确定相应输出应当属于哪个类型。

当 `B` 不依赖 `x` 时，所有输出都属于同一个类型，依值函数便特化为普通函数：

<div class="single-line-code"><code>A → B</code></div>

普通函数为每个输入给出同一类型中的输出；Π 类型则为每个 `x` 给出属于相应类型 `B x` 的数据。

<!--ja-->
## [Π 型]{.term-intro #pi-type}

本書の後の多くの構成では、各対象に対して、それに依存するデータを与える必要があります。Π 型はこの関係を表す基本形です。

型 `A` と、各 `x : A` に対して型 `B x` が与えられたとき、Π 型を作ります。

<div class="single-line-code"><code>(x : A) → B x</code></div>

Π 型の元を**[依存関数]{.term-intro #dependent-function}**と呼びます。依存関数 `f` は、各 `x : A` に対して `B x` の元 `f x` を与えます。結果が属すべき型は入力 `x` に依存するため、入力を定めて初めて対応する出力の型が定まります。

`B` が `x` に依存しない場合、すべての出力は同じ型に属し、依存関数は通常の関数に特化します。

<div class="single-line-code"><code>A → B</code></div>

通常の関数は各入力に対して同じ型の出力を与えますが、Π 型は各 `x` に対して、対応する型 `B x` に属するデータを与えます。

<!--/-->

<!--en-->
## [Σ types]{.term-intro #sigma-type}

Many constructions later in the book need to keep a particular object together with a piece of data that depends on it. A Σ type expresses this basic relationship.

Given a type `A` and a type `B x` for each `x : A`, we form the Σ type:

<div class="single-line-code"><code>`Σ`{.Agda} (x : A) B x</code></div>

An element of a Σ type is called a **[dependent pair]{.term-intro #dependent-pair}**. It is built in two steps: choose `a : A`, then choose an element `b` of `B a`; the resulting pair is written `(a , b)`. We call `a` the **[first component]{.term-intro #first-component}** and `b` the **[second component]{.term-intro #second-component}**. Because the type of the second component depends on `a`, only after fixing the first component do we know the type in which the second must lie.

When `B` does not depend on `x`, every second component lies in the same type, and the dependent pair specialises to an ordinary product:

<div class="single-line-code"><code>A × B  :=  `Σ`{.Agda} (_ : A) B</code></div>

An ordinary product places two independent elements together; a Σ type places a particular `a` together with data belonging to the corresponding type `B a`. Dependent pairs are built with `_,_`{.Agda}, `fst`{.Agda} extracts the first component, and `snd`{.Agda} extracts the second.

A Π type handles "for every `x`, give data depending on `x`"; a Σ type handles "choose an `x`, and keep it together with data depending on it".

The second component may itself be a proof of a property of the first. This book calls a proof carried together with an object so that later reasoning may use the property a **[certificate]{.term-intro #certificate}**. A certificate remains an ordinary Agda proof; the name emphasizes its role in the dependent pair.

<!--zh-->
## [Σ 类型]{.term-intro #sigma-type}

本书后面的许多构造都需要把某个对象与一项依赖于它的数据放在一起。Σ 类型正是表达这种关系的基本形式。

给定一个类型 `A`，以及对每个 `x : A` 指定的类型 `B x`，我们可以构造 Σ 类型：

<div class="single-line-code"><code>`Σ`{.Agda} (x : A) B x</code></div>

Σ 类型的元素称为**[依值对]{.term-intro #dependent-pair}**。它先给出一个 `a : A`，再给出一个属于 `B a` 的元素 `b`，所得的对写作 `(a , b)`。我们把 `a` 称为**[第一分量]{.term-intro #first-component}**，把 `b` 称为**[第二分量]{.term-intro #second-component}**。由于第二分量的类型取决于 `a`，只有确定第一分量以后，才能确定第二分量应当属于哪个类型。

当 `B` 不依赖 `x` 时，所有第二分量都属于同一个类型，依值对便特化为普通的积：

<div class="single-line-code"><code>A × B  :=  `Σ`{.Agda} (_ : A) B</code></div>

普通的积把两个彼此独立的元素放在一起；Σ 类型则把某个 `a` 与属于相应类型 `B a` 的数据放在一起。依值对用 `_,_`{.Agda} 构造，用 `fst`{.Agda} 取出第一分量，用 `snd`{.Agda} 取出第二分量。

Π 类型处理的是「对每个 `x`，给出依赖于 `x` 的数据」；Σ 类型处理的是「选定某个 `x`，并将依赖于它的数据与它放在一起」。

第二分量也可以是关于第一分量的性质证明。本书把这种随对象一同携带、使后续论证能够使用相应性质的证明称为**[证书]{.term-intro #certificate}**。证书仍然是普通的 Agda 证明；这个名称强调的是它在依值对中所起的作用。

<!--ja-->
## [Σ 型]{.term-intro #sigma-type}

本書の後の多くの構成では、ある対象と、それに依存する一つのデータを一緒に保つ必要があります。Σ 型はこの関係を表す基本形です。

型 `A` と、各 `x : A` に対して指定された型 `B x` があるとき、Σ 型を作ります。

<div class="single-line-code"><code>`Σ`{.Agda} (x : A) B x</code></div>

Σ 型の元を**[依存対]{.term-intro #dependent-pair}**と呼びます。まず `a : A` を選び、次に `B a` の元 `b` を選びます。得られた対を `(a , b)` と書きます。`a` を**[第一成分]{.term-intro #first-component}**、`b` を**[第二成分]{.term-intro #second-component}**と呼びます。第二成分の型は `a` に依存するため、第一成分を定めて初めて、第二成分がどの型に属すべきかが決まります。

`B` が `x` に依存しない場合、すべての第二成分は同じ型に属し、依存対は通常の積に特化します。

<div class="single-line-code"><code>A × B  :=  `Σ`{.Agda} (_ : A) B</code></div>

通常の積は互いに独立した二つの元を一緒にしますが、Σ 型は、ある `a` と、対応する型 `B a` に属するデータを一緒にします。依存対は `_,_`{.Agda} で作り、`fst`{.Agda} で第一成分を、`snd`{.Agda} で第二成分を取り出します。

Π 型が扱うのは「すべての `x` に対して、`x` に依存するデータを与えること」です。Σ 型が扱うのは「一つの `x` を選び、それに依存するデータと一緒に収めること」です。

第二成分を、第一成分の性質を示す証明にすることもできます。本書では、後の議論でその性質を使えるよう対象とともに携える証明を**[証明書]{.term-intro #certificate}**と呼びます。証明書は通常の Agda の証明であり、この名前は依存対の中で果たす役割を強調しています。

<!--/-->

```agda
open import Cubical.Data.Sigma public
  using ( Σ; Σ-syntax; _×_; _,_; fst; snd )
```

<!--en-->
## Record types
<!--zh-->
## 记录类型
<!--ja-->
## レコード型
<!--/-->

<!--en-->
A record type can be understood as syntactic sugar for several nested Σ types. For example, suppose we want to package an element `a : A`, an element `b : B a` depending on `a`, and a proof `c : C a b` depending on both. The corresponding nested type is:

<div class="single-line-code"><code>`Σ`{.Agda} (a : A) `Σ`{.Agda} (b : B a) C a b</code></div>

Its elements have the shape:

<div class="single-line-code"><code>(a , (b , c))</code></div>

In Agda, the keyword `record` begins the declaration of such a type, after which its components are given [field]{.term-intro #record-field} names. Constructing an element of the record requires a value for every field. A record declaration may also use the keyword `constructor` to name this operation; that name is the record type's **[constructor]{.term-intro #constructor}**. The constructor accepts the field values in dependency order and assembles them into one record. If three fields correspond to `a`, `b` and `c`, a constructor named `mkR` can present the construction in the flat form:

<div class="single-line-code"><code>mkR a b c</code></div>

This carries the same data as the nested Σ value `(a , (b , c))`{.Agda}, without exposing the nesting. Field names act as [projections]{.term-intro #projection} that retrieve the corresponding components directly. One therefore need not remember the depth of a component or repeatedly compose `fst`{.Agda} and `snd`{.Agda}. Records preserve the dependent structure of nested Σ types while presenting larger packages through a clearer, flat interface. The [Agda documentation on record types](https://agda.readthedocs.io/en/v2.8.0/language/record-types.html) describes their declaration, construction and projections in detail.
<!--zh-->
记录类型可以看作多重嵌套的 Σ 类型的语法糖。例如，要把一个元素 `a : A`、一个依赖于 `a` 的元素 `b : B a`，以及一个依赖于前两者的证明 `c : C a b` 放在一起，可以使用类型：

<div class="single-line-code"><code>`Σ`{.Agda} (a : A) `Σ`{.Agda} (b : B a) C a b</code></div>

其中的元素具有如下嵌套形状：

<div class="single-line-code"><code>(a , (b , c))</code></div>

在 Agda 中，关键字 `record` 开始一个记录类型的声明，随后为其中的各个分量指定[字段]{.term-intro #record-field}名。要构造这个记录类型的元素，就必须为各个字段提供相应的值。记录声明还可以用关键字 `constructor` 为这种构造方式命名；这个名字称为记录类型的**[构造子]{.term-intro #constructor}**。构造子按照字段之间的依赖关系接收各字段的值，再把它们组装成一个记录。例如，若三个字段依次对应 `a`、`b` 和 `c`，构造子 `mkR` 便可以把构造过程展平地写成：

<div class="single-line-code"><code>mkR a b c</code></div>

这与嵌套 Σ 类型的 `(a , (b , c))`{.Agda} 表示同样的数据，只是省去了层层嵌套。字段名则充当[投影]{.term-intro #projection}，可以直接从记录中取出相应分量。因此，使用者不必记忆每个分量位于第几层，也不必反复组合 `fst`{.Agda} 与 `snd`{.Agda}。记录类型既保留了多重 Σ 类型的依赖结构，又通过具名字段和构造子提供了更清楚的平面接口。关于记录的声明、构造和投影，可进一步参阅 [Agda 的记录类型文档](https://agda.readthedocs.io/en/v2.8.0/language/record-types.html)。
<!--ja-->
レコード型は、複数の Σ 型を入れ子にしたものに対する構文糖と考えられます。たとえば、元 `a : A`、`a` に依存する元 `b : B a`、さらにその両方に依存する証明 `c : C a b` を一緒にまとめるとします。対応する入れ子の型は次のものです。

<div class="single-line-code"><code>`Σ`{.Agda} (a : A) `Σ`{.Agda} (b : B a) C a b</code></div>

その元は次の形になります。

<div class="single-line-code"><code>(a , (b , c))</code></div>

Agda では、キーワード `record` がレコード型の宣言を開始し、続いて各成分に[フィールド]{.term-intro #record-field}名を与えます。レコード型の元を構成するには、すべてのフィールドに対応する値を与えなければなりません。レコード宣言では、キーワード `constructor` を使ってこの構成操作に名前を付けることもできます。この名前をレコード型の**[構成子]{.term-intro #constructor}**と呼びます。構成子は依存関係の順にフィールドの値を受け取り、一つのレコードへ組み立てます。三つのフィールドが順に `a`、`b`、`c` に対応するなら、`mkR` という構成子による構成は平らに次のように書けます。

<div class="single-line-code"><code>mkR a b c</code></div>

これは入れ子の Σ 型の値 `(a , (b , c))`{.Agda} と同じデータを表しますが、入れ子を表面に出しません。フィールド名は対応する成分を直接取り出す[射影]{.term-intro #projection}として働きます。そのため、成分が何段目にあるかを覚えたり、`fst`{.Agda} と `snd`{.Agda} を何度も組み合わせたりする必要がありません。レコード型は入れ子になった Σ 型の依存構造を保ちながら、名前付きフィールドと構成子によって大きなデータのまとまりを明瞭な平面インターフェースとして提示します。宣言、構成、射影の詳細は [Agda のレコード型の文書](https://agda.readthedocs.io/en/v2.8.0/language/record-types.html)を参照してください。
<!--/-->

<!--en-->
## Moving between universe levels
<!--zh-->
## 宇宙层级之间的搬移
<!--ja-->
## 宇宙レベル間の移動
<!--/-->

<!--en-->
The Agda type universes used here are not cumulative. An element of `Type ℓ`{.Agda} does not automatically become an element of `Type (ℓ-suc ℓ)`{.Agda}; moving a type between levels requires the explicit operation `Lift`{.Agda}.

`Lift ℓ A`{.Agda} is itself a record type. It has one field, `lower : A`{.Agda}, which stores an element of the original type `A`; its constructor is `lift`{.Agda}. Given `a : A`{.Agda}, the constructor produces `lift a : Lift ℓ A`{.Agda}. Conversely, given `b : Lift ℓ A`{.Agda}, the field projection `lower b`{.Agda} retrieves the stored element of `A`.

The functions `lift`{.Agda} and `lower`{.Agda} are mutually inverse between `A` and `Lift ℓ A`{.Agda}. Two equations state the two directions separately:

<div class="single-line-code"><code>`lower (lift a) ≡ a`{.Agda}</code></div>

<div class="single-line-code"><code>`lift (lower b) ≡ b`{.Agda}</code></div>

The first says that packaging an element and immediately retrieving it returns the original element. The second says that retrieving an element from a lifted record and packaging it again returns the original record. Thus `Lift`{.Agda} changes the universe in which a type is presented and the representation of its elements, without adding or losing mathematical information.

More precisely, if `A` lives in `Type ℓ₁`{.Agda}, then `Lift ℓ₂ A`{.Agda} lives in `Type (ℓ-max ℓ₁ ℓ₂)`{.Agda}. If either universe level is already above the other, `ℓ-max`{.Agda} keeps it; otherwise it gives a common universe level large enough for both. Hence `Lift`{.Agda} does not raise a type by a fixed number of levels. It places the type in a universe large enough for the levels at hand.

A type can always be copied upward in this way, but <span class="prose-annotation-target">there is in general no way to move one down</span><aside class="prose-annotation-note">Propositions (types satisfying `isProp`{.Agda}) are the exception: the <a href="Base.Classical.html">Classical Boundary</a> chapter will show that excluded middle provides exactly the downward direction for them.</aside>.
<!--zh-->
我们使用的 Agda 类型宇宙不是累积的。`Type ℓ`{.Agda} 的元素并不自动成为 `Type (ℓ-suc ℓ)`{.Agda} 的元素；在层级之间搬移类型需要显式运算 `Lift`{.Agda}。

`Lift ℓ A`{.Agda} 本身是一个记录类型。它只有一个字段 `lower : A`{.Agda}，用来保存原类型 `A` 的元素；它的构造子是 `lift`{.Agda}。给定 `a : A`{.Agda}，构造子产生 `lift a : Lift ℓ A`{.Agda}；反过来，给定 `b : Lift ℓ A`{.Agda}，字段投影 `lower b`{.Agda} 取出其中保存的 `A` 的元素。

`lift`{.Agda} 与 `lower`{.Agda} 在 `A` 和 `Lift ℓ A`{.Agda} 之间互为逆函数。这由两条等式分别表达：

<div class="single-line-code"><code>`lower (lift a) ≡ a`{.Agda}</code></div>

<div class="single-line-code"><code>`lift (lower b) ≡ b`{.Agda}</code></div>

第一条等式说，一个元素被装入 `Lift`{.Agda} 后立即取出，仍是原来的元素。第二条等式说，从 `Lift`{.Agda} 中取出元素再重新装入，仍得到原来的记录。因此，`Lift`{.Agda} 改变的是类型所在的宇宙以及元素的表示方式，不会增添或丢失数学信息。

具体来说，若 `A` 位于 `Type ℓ₁`{.Agda}，那么 `Lift ℓ₂ A`{.Agda} 位于 `Type (ℓ-max ℓ₁ ℓ₂)`{.Agda}。如果两个宇宙层级中已经有一个较高，`ℓ-max`{.Agda} 就保留那个层级；否则，它给出足以同时容纳二者的公共宇宙层级。因此，`Lift`{.Agda} 并不是把类型固定抬高若干层，而是把它放入当前所需的足够大的宇宙。

类型总能以这种方式向上复制，但<span class="prose-annotation-target">一般不能向下搬移</span><aside class="prose-annotation-note">命题 (满足 `isProp`{.Agda} 的类型) 是一个例外；<a href="Base.Classical.html">经典边界</a>一章将说明，排中律恰好为命题提供向下搬移的方向。</aside>。
<!--ja-->
ここで使う Agda の型宇宙は累積的ではありません。`Type ℓ`{.Agda} の要素が自動的に `Type (ℓ-suc ℓ)`{.Agda} の要素になるわけではありません。レベル間で型を移すには、明示的な演算 `Lift`{.Agda} が必要です。

`Lift ℓ A`{.Agda} はそれ自身がレコード型です。フィールドは元の型 `A` の元を保存する `lower : A`{.Agda} 一つだけで、構成子は `lift`{.Agda} です。`a : A`{.Agda} を与えると、構成子は `lift a : Lift ℓ A`{.Agda} を作ります。逆に `b : Lift ℓ A`{.Agda} があれば、フィールド射影 `lower b`{.Agda} が保存された `A` の元を取り出します。

`lift`{.Agda} と `lower`{.Agda} は `A` と `Lift ℓ A`{.Agda} の間で互いに逆です。その二つの向きを別々の等式が表します。

<div class="single-line-code"><code>`lower (lift a) ≡ a`{.Agda}</code></div>

<div class="single-line-code"><code>`lift (lower b) ≡ b`{.Agda}</code></div>

第一の等式は、元を包んですぐ取り出せば元の要素に戻ることを述べます。第二の等式は、持ち上げられたレコードから元を取り出して包み直せば、元のレコードに戻ることを述べます。したがって `Lift`{.Agda} は型を提示する宇宙と元の表現を変えますが、数学的な情報を加えたり失ったりしません。

より正確には、`A` が `Type ℓ₁`{.Agda} に住むなら、`Lift ℓ₂ A`{.Agda} は `Type (ℓ-max ℓ₁ ℓ₂)`{.Agda} に住みます。一方の宇宙レベルがすでに他方より高ければ、`ℓ-max`{.Agda} はそのレベルを保ちます。そうでなければ、両方を収めるのに十分な共通の宇宙レベルを与えます。したがって `Lift`{.Agda} は型を決まった段数だけ持ち上げるのではなく、現在の二つのレベルにとって十分大きな宇宙へ型を置きます。

型は常にこの方法で上へコピーできますが、<span class="prose-annotation-target">一般には下へ動かせません</span><aside class="prose-annotation-note">命題 (`isProp`{.Agda} を満たす型) は例外です。<a href="Base.Classical.html">古典的境界</a>の章で、排中律が命題に対する下向きの方向をちょうど与えることを見ます。</aside>。
<!--/-->

```agda
open import Cubical.Foundations.Prelude public
  using ( Lift; lift; lower )
```

<!--en-->
## Equality and [paths]{.term-intro #path}
<!--zh-->
## 相等与[路径]{.term-intro #path}
<!--ja-->
## 等式と[パス]{.term-intro #path}
<!--/-->

<!--en-->
In ordinary mathematical language, `x = y` is a proposition asserting that two objects are equal. In type theory, propositions are represented by types, so equality is represented by a type as well. For two elements `x` and `y` of `A`, `x ≡ y`{.Agda} is the type corresponding to the proposition that `x` and `y` are equal, and its elements are proofs of that equality.

In cubical type theory, such an equality proof is called a **path** from `x` to `y`, and `x ≡ y`{.Agda} is called a path type. A path is therefore not another relation alongside equality: paths are the equality proofs used in this book, and path types are how the book represents equality. A path has a source and a target, so its direction can be reversed and paths can be joined end to end. The basic operations below arise from this structure.

- `refl`{.Agda} is a path from an element to itself and gives reflexivity of equality.
- `sym`{.Agda} reverses a path; a path from `x` to `y` thereby becomes a path from `y` to `x`.
- `_∙_`{.Agda} composes paths whose endpoints meet; a path from `x` to `y` followed by one from `y` to `z` gives a path from `x` to `z`.
- `cong`{.Agda} says that functions preserve equality: equal inputs are sent to equal outputs. `cong₂`{.Agda} is the corresponding binary operation.
- `funExt`{.Agda} turns pointwise equality into equality of functions: if `f x ≡ g x`{.Agda} for every `x`, then `f ≡ g`{.Agda}.
- `transport`{.Agda} moves an element along a path between types; `subst`{.Agda} moves data depending on `x` along `x ≡ y`{.Agda} to data depending on `y`.

For example, given a function `f : A → B`{.Agda}, the action of `cong`{.Agda} can be summarized as:

<div class="single-line-code"><code>`cong f : x ≡ y → f x ≡ f y`{.Agda}</code></div>

This says that `f` can act on an equality path, turning equality between inputs into equality between outputs.

Paths are themselves elements of a type, so two paths can in turn be equal. Equality structure can therefore continue to higher levels: we may ask not only whether two elements are equal, but also whether their equality proofs are equal. The next section introduces a hierarchy that measures how many such levels of equality structure a type retains.

For further details on path types in Cubical Agda, see the [Cubical chapter of the Agda 2.8.0 manual](https://agda.readthedocs.io/en/v2.8.0/language/cubical.html). This section uses only the basic properties needed for the constructions that follow.
<!--zh-->
在通常的数学语言中，`x = y` 是一个关于两个对象相等的命题。在类型论中，命题由类型表示，因此相等也由类型表示：对 `A` 中的两个元素 `x` 和 `y`，`x ≡ y`{.Agda} 是「`x` 与 `y` 相等」这一命题所对应的类型，它的元素就是相等的证明。

在立方类型论中，这种相等证明称为从 `x` 到 `y` 的**路径**，而 `x ≡ y`{.Agda} 称为路径类型。因此，路径并不是相等之外的另一种关系：路径就是本书所使用的相等证明，路径类型就是本书表示相等的方式。路径有起点和终点，因而可以反转方向，也可以首尾相接；下面的基本操作正是从这一结构产生的。

- `refl`{.Agda} 是从一个元素到自身的路径，给出相等的自反性。
- `sym`{.Agda} 反转路径的方向；从 `x` 到 `y` 的路径由此变成从 `y` 到 `x` 的路径。
- `_∙_`{.Agda} 把首尾相接的路径复合起来；从 `x` 到 `y`，再从 `y` 到 `z`，便得到从 `x` 到 `z` 的路径。
- `cong`{.Agda} 说明函数保持相等：函数把相等的输入送到相等的输出。`cong₂`{.Agda} 是相应的二元版本。
- `funExt`{.Agda} 从逐点相等得到函数相等：如果 `f x ≡ g x`{.Agda} 对每个 `x` 都成立，那么 `f ≡ g`{.Agda}。
- `transport`{.Agda} 沿类型之间的路径搬移元素；`subst`{.Agda} 则沿 `x ≡ y`{.Agda}，把依赖于 `x` 的数据搬移为依赖于 `y` 的数据。

例如，给定函数 `f : A → B`{.Agda}，`cong`{.Agda} 的作用可以概括为：

<div class="single-line-code"><code>`cong f : x ≡ y → f x ≡ f y`{.Agda}</code></div>

这表示函数 `f` 可以作用于一条相等路径，把输入之间的相等变成输出之间的相等。

路径本身也是类型中的元素，所以两条路径之间还可以形成新的相等。相等结构由此可以继续向更高层延伸：不仅可以问两个元素是否相等，还可以问它们的相等证明彼此是否相等。下一节将引入一套层次分类，用来衡量一个类型保留了多少层这样的相等结构。

关于 Cubical Agda 中的路径类型，可以参阅 [Agda 2.8.0 手册中的 Cubical 章节](https://agda.readthedocs.io/en/v2.8.0/language/cubical.html)。本节只使用理解后续构造所需的基本性质。
<!--ja-->
通常の数学では、`x = y` は二つの対象が等しいという命題です。型理論では命題を型で表すので、等しさも型で表します。`A` の二つの要素 `x` と `y` に対して、`x ≡ y`{.Agda} は「`x` と `y` が等しい」という命題に対応する型であり、その要素が等しさの証明です。

立方型理論では、この等しさの証明を `x` から `y` への**パス**と呼び、`x ≡ y`{.Agda} をパス型と呼びます。したがって、パスは等しさとは別に置かれた関係ではありません。パスが本書で使う等しさの証明であり、パス型が本書における等しさの表現です。パスには始点と終点があるため、向きを逆にしたり、端と端をつないだりできます。以下の基本操作はこの構造から生まれます。

- `refl`{.Agda} は要素からそれ自身へのパスであり、等しさの反射性を与えます。
- `sym`{.Agda} はパスの向きを逆にします。`x` から `y` へのパスは、これによって `y` から `x` へのパスになります。
- `_∙_`{.Agda} は端点の一致するパスを合成します。`x` から `y` へ進み、続いて `y` から `z` へ進めば、`x` から `z` へのパスが得られます。
- `cong`{.Agda} は関数が等しさを保つこと、すなわち等しい入力を等しい出力へ送ることを述べます。`cong₂`{.Agda} は対応する二引数版です。
- `funExt`{.Agda} は各点での等しさから関数の等しさを与えます。すべての `x` について `f x ≡ g x`{.Agda} ならば、`f ≡ g`{.Agda} です。
- `transport`{.Agda} は型の間のパスに沿って要素を移します。`subst`{.Agda} は `x ≡ y`{.Agda} に沿って、`x` に依存するデータを `y` に依存するデータへ移します。

例えば関数 `f : A → B`{.Agda} があるとき、`cong`{.Agda} の働きは次のようにまとめられます。

<div class="single-line-code"><code>`cong f : x ≡ y → f x ≡ f y`{.Agda}</code></div>

これは関数 `f` が等しさのパスに作用し、入力の間の等しさを出力の間の等しさへ移すことを表します。

パス自身も型の要素なので、二つのパスがさらに等しいかを考えられます。等しさの構造はこのように高い層へ続きます。二つの要素が等しいかだけでなく、その等しさの証明どうしが等しいかも問えるのです。次節では、このような等しさの構造を型が何層まで保つかを測る階層的な分類を導入します。

Cubical Agda のパス型について詳しくは、[Agda 2.8.0 マニュアルの Cubical の章](https://agda.readthedocs.io/en/v2.8.0/language/cubical.html)を参照してください。本節では、後の構成を理解するために必要な基本的性質だけを使います。
<!--/-->

```agda
open import Cubical.Foundations.Prelude public
  using ( _≡_; refl; sym; _∙_; cong; cong₂; transport; subst; funExt )
```

<!--en-->
## [Homotopy levels]{.term-intro #homotopy-level}
<!--zh-->
## [同伦层级]{.term-intro #homotopy-level}
<!--ja-->
## [ホモトピーレベル]{.term-intro #homotopy-level}
<!--/-->

<!--en-->
Paths are themselves elements of types, so new paths can in turn relate paths. Homotopy levels classify types by how much distinguishable structure remains in these equality proofs. They do not measure the size of a type: universe levels handle size, whereas homotopy levels concern how elements and their equality proofs can be distinguished.

- **`isContr A`{.Agda}: `A` is [contractible]{.term-intro #contractible}.** This requires a chosen centre in `A` and, for every `x : A`{.Agda}, a path from the centre to `x`. Thus `A` must be inhabited, and every element is equal to the chosen centre, so no two elements can be distinguished by equality. This book reads the data carried by `isContr`{.Agda} as **[unique existence]{.term-intro #unique-existence}**: the centre supplies existence, and the paths from the centre to every element supply uniqueness.
- **`isProp A`{.Agda}: `A` is a [proposition]{.term-intro #proposition}.** This requires any two elements of `A` to be equal. It neither chooses a centre nor requires `A` to be inhabited; it says only that if proofs of `A` exist, no distinction remains between them. A proposition may therefore have no proof or have a proof, but it cannot have two distinguishable proofs.
- **`isSet A`{.Agda}: `A` is an [h-set]{.term-intro #h-set}.** The prefix marks a notion of the host: an h-set is a type satisfying `isSet`{.Agda}, not a set of the set theory being modelled. The condition does not require every two elements of `A` to be equal. Instead, it requires the path type between any two elements to be a proposition. Elements of `A` may differ, and paths may connect some of them; but once the same source and target are fixed, any two such paths are equal. Distinctions may remain among elements, while no further distinguishable structure remains among their equality proofs.
- **`isProp→isSet`{.Agda}: every proposition is an h-set.** If `A` satisfies `isProp`{.Agda}, then it also satisfies `isSet`{.Agda}. This is an upward movement in homotopy level: it leaves `A` unchanged and derives the weaker condition that any two equality paths are equal from the stronger condition that any two elements are equal. It resembles the universe-level movement performed by `Lift`{.Agda}, since both let the same mathematical object meet a requirement at a higher level. They act on different axes, however. `Lift`{.Agda} changes the universe in which a type is presented and produces an equivalent record copy; `isProp→isSet`{.Agda} changes neither the type nor its universe, but derives one equality property from another.
<!--zh-->
路径本身也是类型中的元素，所以路径之间还可以形成新的路径。同伦层级按照这些相等证明还能保留多少可区分的结构，对类型进行分类。这里衡量的不是类型的大小；类型的大小由宇宙层级处理，同伦层级关心的是元素及其相等证明如何彼此区分。

- **`isContr A`{.Agda}：`A` 是[可缩]{.term-intro #contractible}的。** 这要求在 `A` 中选定一个中心，并为每个 `x : A`{.Agda} 给出一条从中心到 `x` 的路径。因此，`A` 不仅必须有元素，而且所有元素都与选定的中心相等，彼此之间也就无法通过相等加以区分。本书把 `isContr`{.Agda} 携带的这组数据读作**[唯一存在]{.term-intro #unique-existence}**：中心给出存在性，所有元素都等于中心则给出唯一性。
- **`isProp A`{.Agda}：`A` 是[命题]{.term-intro #proposition}。** 这要求 `A` 中任意两个元素都相等。它不要求预先选定中心，甚至不要求 `A` 一定有元素；它只说明，一旦 `A` 有证明，这些证明之间便没有可区分的差别。因此，一个命题可以没有证明，也可以有证明，但不能有两个彼此不同的证明。
- **`isSet A`{.Agda}：`A` 是 [h-集合]{.term-intro #h-set}。** 前缀标明这是宿主层的概念：h-集合指满足 `isSet`{.Agda} 的类型，而不是所建模的集合论中的集合。这不要求 `A` 中任意两个元素都相等，而是要求任意两个元素之间的路径类型本身为命题。换言之，`A` 的元素可以彼此不同，也可以存在连接某些元素的路径；但给定相同的起点和终点以后，两条这样的路径必定相等。元素层面仍可保留差别，相等证明之间则不再保留可区分的更高结构。
- **`isProp→isSet`{.Agda}：命题都是 h-集合。** 如果 `A` 满足 `isProp`{.Agda}，那么它也满足 `isSet`{.Agda}。这可以看成一次同伦层级的向上搬移：我们不改变 `A`，而是从较强的条件「任意两个元素相等」推出较弱的条件「任意两条相等路径彼此相等」。它与 `Lift`{.Agda} 所做的宇宙层级搬移有一点相似：二者都使同一个数学对象满足较高层级的要求。不过，两者作用于不同的层级轴。`Lift`{.Agda} 改变类型所在的宇宙，并产生一个与原类型等价的记录副本；`isProp→isSet`{.Agda} 不改变类型，也不改变它所在的宇宙，只是从已有的相等性质推出另一个相等性质。
<!--ja-->
パス自身も型の要素なので、パスどうしの間にさらにパスを作れます。ホモトピーレベルは、このような等しさの証明に区別できる構造がどれだけ残るかによって型を分類します。型の大きさを測るものではありません。大きさを扱うのは宇宙レベルであり、ホモトピーレベルが扱うのは要素とその等しさの証明をどこまで区別できるかです。

- **`isContr A`{.Agda}：`A` は[可縮]{.term-intro #contractible}である。** これは `A` の中に中心を一つ選び、すべての `x : A`{.Agda} に対して中心から `x` へのパスを与えることを要求します。したがって `A` には要素が存在し、すべての要素が選ばれた中心と等しいので、等しさによって要素を区別できません。本書では `isContr`{.Agda} が持つこのデータを**[一意存在]{.term-intro #unique-existence}**と読みます。中心が存在を与え、すべての要素へのパスが一意性を与えます。
- **`isProp A`{.Agda}：`A` は[命題]{.term-intro #proposition}である。** これは `A` の任意の二要素が等しいことを要求します。中心を選ぶ必要はなく、`A` に要素が存在することさえ要求しません。`A` の証明が存在するなら、それらの間に区別が残らないことだけを述べます。したがって命題には証明がないことも、証明があることもありますが、互いに区別できる二つの証明はあり得ません。
- **`isSet A`{.Agda}：`A` は [h-集合]{.term-intro #h-set}である。** 接頭辞はホストレベルの概念であることを示します。h-集合とは `isSet`{.Agda} を満たす型であり、モデル化される集合論の集合ではありません。これは `A` の任意の二要素が等しいことを要求するのではなく、任意の二要素の間のパス型が命題であることを要求します。`A` の要素は互いに異なっていてよく、その一部を結ぶパスが存在してもかまいません。しかし始点と終点を同じものに固定すれば、その間の任意の二つのパスは等しくなります。要素の間には区別が残り得ますが、等しさの証明の間には、それ以上区別できる構造が残りません。
- **`isProp→isSet`{.Agda}：すべての命題は h-集合である。** `A` が `isProp`{.Agda} を満たせば、`isSet`{.Agda} も満たします。これはホモトピーレベルを上向きに移す操作と見なせます。`A` を変えず、「任意の二要素が等しい」という強い条件から「任意の二つの等しさのパスが等しい」という弱い条件を導きます。この点は `Lift`{.Agda} による宇宙レベルの移動と似ています。どちらも同じ数学的対象を、より高いレベルの要件のもとで扱えるようにするからです。ただし、作用する軸は異なります。`Lift`{.Agda} は型を提示する宇宙を変え、元の型と同値なレコードのコピーを作ります。`isProp→isSet`{.Agda} は型もその宇宙も変えず、一つの等しさの性質から別の性質を導くだけです。
<!--/-->

```agda
open import Cubical.Foundations.Prelude public
  using ( isProp; isSet; isContr; isProp→isSet )
```

<!--en-->
## The universe of propositions
<!--zh-->
## 命题宇宙
<!--ja-->
## 命題の宇宙
<!--/-->

<!--en-->
In cubical type theory, a proposition is a type satisfying `isProp`{.Agda}. This condition makes any two elements of the type equal, so the type retains only the logical information of whether a proof exists, without distinguishing different proofs. An element of the type proves the corresponding proposition; without such an element, the proposition has not yet been proved.

To keep a proposition together with the fact that it is a proposition, the Cubical library uses `hProp ℓ`{.Agda}. This is the type of all propositions at universe level `ℓ`: in other words, `hProp ℓ`{.Agda} is the **universe of propositions** at that level. A `P : hProp ℓ`{.Agda} has two components:

- The first component is the type expressing the proposition, namely the statement of the proposition itself.
- The second component is the certificate that this type satisfies `isProp`{.Agda}.

Thus `P : hProp ℓ`{.Agda} represents a proposition, but does not say that the proposition has already been proved. Its certificate says only that the first component is a proposition; it does not say that the first component has an element.
<!--zh-->
在立方类型论中，命题是满足 `isProp`{.Agda} 的类型。这个条件保证该类型的任意两个元素都相等，因此其中只保留「是否存在证明」这一逻辑信息，不再区分不同的证明。类型具有元素时，相应命题成立；无法构造元素时，则尚未得到该命题的证明。

为了把一个命题连同它具有命题性这一事实放在一起，Cubical 库使用 `hProp ℓ`{.Agda}。它是宇宙层级 `ℓ` 上所有命题组成的类型；换言之，`hProp ℓ`{.Agda} 就是该层级上的**命题宇宙**。一个 `P : hProp ℓ`{.Agda} 包含两个分量：

- 第一分量是表达命题的类型，即命题的表述本身；
- 第二分量是该类型确实满足 `isProp`{.Agda} 的证书。

因此，`P : hProp ℓ`{.Agda} 表示一个命题，却不表示这个命题已经得到证明。它携带的证书只说明第一分量具有命题性，并不说明第一分量中存在元素。
<!--ja-->
立方型理論では、命題とは `isProp`{.Agda} を満たす型です。この条件により、その型の任意の二つの元は等しくなります。したがって、証明どうしを区別せず、証明が存在するかどうかという論理的な情報だけが残ります。型の元を構成すれば対応する命題が成り立つことが示され、元をまだ構成できなければ、その命題の証明はまだ得られていません。

命題を、それが命題であるという事実と一緒に収めるため、Cubical ライブラリでは `hProp ℓ`{.Agda} を使います。これは宇宙レベル `ℓ` にあるすべての命題の型です。言い換えれば、`hProp ℓ`{.Agda} はそのレベルの**命題の宇宙**です。`P : hProp ℓ`{.Agda} は二つの成分を含みます。

- 第一成分は命題を表す型、すなわち命題の記述そのものです。
- 第二成分は、その型が確かに `isProp`{.Agda} を満たすという証明書です。

したがって、`P : hProp ℓ`{.Agda} は命題を表しますが、その命題がすでに証明されているとは主張しません。`P` が持つ証明書は、第一成分が命題であることだけを示し、第一成分に元が存在するとは主張しません。
<!--/-->

<!--en-->
Two basic properties of the proposition universe recur later in the book:

- `isSetHProp`{.Agda} says that `hProp ℓ`{.Agda} is itself an h-set. Propositions may still differ, but equality proofs between propositions contain no distinguishable higher structure.
- `isPropΠ`{.Agda} says that propositions are closed under Π types. If every `B x` is a proposition, then `(x : A) → B x` is also a proposition. Universally quantifying a family of propositions therefore produces another proposition.
<!--zh-->
关于命题宇宙，后文会反复使用两项基本性质：

- `isSetHProp`{.Agda} 表明 `hProp ℓ`{.Agda} 本身是 h-集合。不同命题仍然可以彼此区分，但命题之间的相等证明不再含有可区分的更高结构。
- `isPropΠ`{.Agda} 表明命题对 Π 类型封闭。若每个 `B x` 都是命题，那么 `(x : A) → B x` 也是命题。因此，对一族命题作全称量化，所得结果仍然是命题。
<!--ja-->
命題の宇宙について、後の章で繰り返し使う基本性質が二つあります。

- `isSetHProp`{.Agda} は `hProp ℓ`{.Agda} 自身が h-集合であることを示します。異なる命題は区別できますが、命題間の等しさの証明には、区別できる高次の構造が残りません。
- `isPropΠ`{.Agda} は、命題が Π 型に対して閉じていることを示します。すべての `B x` が命題なら、`(x : A) → B x` も命題です。したがって、命題の族を全称量化して得られる結果も命題です。
<!--/-->

```agda
open import Cubical.Foundations.HLevels public
  using ( hProp; isSetHProp; isPropΠ )
```

<!--en-->
The projection `⟨_⟩`{.Agda} extracts the statement of a proposition. For `P : hProp ℓ`{.Agda}, `⟨ P ⟩`{.Agda} is its first component; to prove the proposition expressed by `P`, we must construct an element of `⟨ P ⟩`{.Agda}. The propositionhood certificate remains in the second component `P .snd`{.Agda}.
<!--zh-->
投影 `⟨_⟩`{.Agda} 用来取出命题的表述。对于 `P : hProp ℓ`{.Agda}，`⟨ P ⟩`{.Agda} 就是它的第一分量；若要证明 `P` 所表达的命题成立，则须构造 `⟨ P ⟩`{.Agda} 的元素。命题性证书仍保存在第二分量 `P .snd`{.Agda} 中。
<!--ja-->
射影 `⟨_⟩`{.Agda} は命題の記述を取り出します。`P : hProp ℓ`{.Agda} に対して、`⟨ P ⟩`{.Agda} はその第一成分です。`P` が表す命題を証明するには、`⟨ P ⟩`{.Agda} の元を構成しなければなりません。命題性の証明書は第二成分 `P .snd`{.Agda} に残ります。
<!--/-->

<!--en-->
An object `P` packages the statement of a proposition together with its propositionhood certificate, so it can be passed as a function argument, returned as a function result or stored in a record field. When we need to state or prove the proposition, we extract the corresponding type through `⟨ P ⟩`{.Agda}.
<!--zh-->
`P` 把命题的表述与命题性证书收在同一个对象中，因此可以整体作为函数的参数、返回值或记录的字段使用。需要陈述或证明这个命题时，再通过 `⟨ P ⟩`{.Agda} 取出相应的类型。
<!--ja-->
`P` は命題の記述とその命題性の証明書を一つの対象にまとめるため、全体を関数の引数や返り値として渡したり、レコードのフィールドに格納したりできます。命題を述べたり証明したりするときは、`⟨ P ⟩`{.Agda} を通して対応する型を取り出します。
<!--/-->

```agda
open import Cubical.Foundations.Structure public
  using ( ⟨_⟩ )
```

<!--en-->
The next section considers propositions that vary with an object.
<!--zh-->
下一节讨论随对象变化的命题。
<!--ja-->
次節では、対象に応じて変化する命題を考えます。
<!--/-->

<!--en-->
## [Classes]{.term-intro #class} and membership
<!--zh-->
## [类]{.term-intro #class}与成员关系
<!--ja-->
## [クラス]{.term-intro #class}と所属関係
<!--/-->

<!--en-->
Here **class** means a class in the sense of set theory, not a type in type theory. Throughout this book, *class* refers to the former and *type* to the latter. The two are closely related in the formalization, but they are not the same notion. A type determines which terms may be its elements; a class selects, by a property, the objects that satisfy it from a domain already given.

This collection of objects under consideration is the class's **domain**. When it is written `A`, the domain is a type `A` whose elements are all the objects currently being classified. Calling `A` a domain says only that a variable `x : A` may range over these objects; it does not equip `A` with membership, operations or any other structure. Later, when we construct a model of set theory, we add a set-theoretic membership relation to `A`. It then also becomes the [carrier]{.term-intro #carrier} of the model, and its elements play the role of sets in that model.

A class over a domain `A` is represented by a function:

<div class="single-line-code"><code>M : A → hProp ℓ</code></div>

For each `x : A`, the proposition `M x` says that `x` has the property specified by the class `M`. Thus `M` does not send `x` to another object that is collected somewhere. It assigns a proposition to each `x`, and the objects satisfying that proposition are precisely the objects belonging to the class.

This explains why we can discuss classes before introducing sets. A class here is a predicate defined in the metatheory. It requires only a domain and the universe of propositions; it neither presupposes that sets have been defined in the object theory nor asserts that the class itself is a set. Once later chapters equip the domain with a set-theoretic structure, such classes can describe the sets in the model that satisfy a chosen property.

Class membership is written `x ∈ᶜ M` and read "x belongs to the class M". Its meaning is the proposition that `M` assigns to `x`:

<div class="single-line-code"><code>x ∈ᶜ M  :=  ⟨ M x ⟩</code></div>

To prove `x ∈ᶜ M` is therefore to construct a proof of `⟨ M x ⟩`{.Agda}. The superscript `ᶜ` marks this as class membership. It distinguishes this host-level predicate from the membership relation between sets that later chapters interpret in a model of set theory: the former says whether an object satisfies a property, whereas the latter is a relation in the object language.
<!--zh-->
这里的「类」是集合论中的 **class**，不是类型论中的 **type**。本书以后约定：**类**专指 class，**类型**专指 type。二者在形式化中关系密切，但不是同一个概念。类型规定哪些项可以作为它的元素；类则在已经给定的一批对象中，用一个性质挑出满足它的对象。

类所考察的这批对象称为它的**论域**。写作 `A` 时，论域就是一个类型 `A`，它的元素是当前接受分类的全部对象。称 `A` 为论域，只说明变量 `x : A` 可以在这些对象中取值，并不表示 `A` 已经具有成员关系、运算或其他结构。后文构造集合论模型时，我们会在 `A` 上加入集合论的成员关系；此时，`A` 也将成为该模型的[载体]{.term-intro #carrier}，它的元素则充当模型中的集合。

论域 `A` 上的类由一个函数表示：

<div class="single-line-code"><code>M : A → hProp ℓ</code></div>

对于每个 `x : A`，命题 `M x` 表示「`x` 具有类 `M` 所规定的性质」。因此，`M` 并不是把 `x` 送到另一个被收集起来的对象，而是为每个 `x` 给出一个关于它的命题。满足这个命题的对象，正是属于该类的对象。

这也解释了为什么我们还没有引入集合，就已经可以讨论类。此处的类是在元理论中定义的谓词，只需要一个论域和命题宇宙，并不需要先在对象理论中定义集合，也不声称这个类本身是一个集合。等到后文在这个论域上加入集合论结构以后，我们便可以用这种类描述模型中满足某项性质的集合。

类的成员关系写作 `x ∈ᶜ M`，读作「`x` 属于类 `M`」。它的含义就是 `M` 为 `x` 指定的命题：

<div class="single-line-code"><code>x ∈ᶜ M  :=  ⟨ M x ⟩</code></div>

因此，证明 `x ∈ᶜ M`，就是构造命题 `⟨ M x ⟩`{.Agda} 的证明。上标 `ᶜ` 表明这里使用的是类的成员关系。它将这个宿主层谓词与后文在集合论模型中解释的集合成员关系区分开来：前者说明一个对象是否满足某项性质，后者则是对象理论语言中的关系。
<!--ja-->
ここでいう**クラス**は集合論における class であり、型理論における type ではありません。本書では以後、前者を**クラス**、後者を**型**と呼び分けます。形式化の中で両者は密接に関係しますが、同じ概念ではありません。型はどの項がその要素になれるかを定め、クラスは、すでに与えられた対象の中から、ある性質を満たすものを選び出します。

クラスが考察する対象の範囲を、そのクラスの**論域**と呼びます。`A` と書くとき、論域は型 `A` であり、その要素が現在分類されるすべての対象です。`A` を論域と呼ぶことは、変数 `x : A` がこれらの対象を動くということだけを表し、`A` に所属関係や演算などの構造がすでに備わっていることを意味しません。後に集合論のモデルを構成するとき、`A` に集合論的な所属関係を加えます。そのとき `A` はモデルの[台]{.term-intro #carrier}にもなり、その要素がモデル内の集合の役割を果たします。

論域 `A` 上のクラスは関数で表されます。

<div class="single-line-code"><code>M : A → hProp ℓ</code></div>

各 `x : A` に対して、命題 `M x` は「`x` がクラス `M` の定める性質を持つ」ことを表します。したがって `M` は、`x` をどこかに集められた別の対象へ送るのではありません。各 `x` に命題を割り当て、その命題を満たす対象が、まさにそのクラスに属する対象です。

これにより、集合をまだ導入していない段階でクラスを論じられる理由も分かります。ここでのクラスはメタ理論で定義される述語であり、必要なのは論域と命題の宇宙だけです。対象理論で集合がすでに定義されていることを前提とせず、クラス自身が集合であるとも主張しません。後にこの論域へ集合論の構造を加えれば、このようなクラスを使って、モデル内である性質を満たす集合を記述できます。

クラスへの所属を `x ∈ᶜ M` と書き、「`x` はクラス `M` に属する」と読みます。その意味は、`M` が `x` に割り当てる命題です。

<div class="single-line-code"><code>x ∈ᶜ M  :=  ⟨ M x ⟩</code></div>

したがって `x ∈ᶜ M` を証明することは、命題 `⟨ M x ⟩`{.Agda} の証明を構成することです。上付きの `ᶜ` は、ここでクラスへの所属を使っていることを示します。これはホストレベルの述語を、後に集合論のモデルで解釈する集合間の所属関係から区別します。前者は対象がある性質を満たすかを述べ、後者は対象言語の関係です。
<!--/-->

```agda
open import Cubical.Foundations.Powerset public
  using () renaming ( _∈_ to _∈ᶜ_ )
```

<!--en-->
## Natural numbers
<!--zh-->
## 自然数
<!--ja-->
## 自然数
<!--/-->

<!--en-->
The natural numbers `ℕ`{.Agda} form an inductive type generated by two constructors. The constructor `zero`{.Agda} is an element of `ℕ`{.Agda}; the constructor `suc`{.Agda} takes any `n : ℕ`{.Agda} to another element `suc n : ℕ`{.Agda}. The rules are

$$\frac{}{\mathsf{zero}:\mathbb{N}}\qquad\frac{n:\mathbb{N}}{\mathsf{suc}\,n:\mathbb{N}}.$$

Every element of `ℕ`{.Agda} is generated from these constructors. Its induction principle accordingly has a case for `zero`{.Agda} and a step that passes from `n` to `suc n`{.Agda}.
<!--zh-->
自然数 `ℕ`{.Agda} 是由两个构造子生成的归纳类型。构造子 `zero`{.Agda} 是 `ℕ`{.Agda} 的元素；构造子 `suc`{.Agda} 把任意 `n : ℕ`{.Agda} 变为另一个元素 `suc n : ℕ`{.Agda}。构造规则为

$$\frac{}{\mathsf{zero}:\mathbb{N}}\qquad\frac{n:\mathbb{N}}{\mathsf{suc}\,n:\mathbb{N}}.$$

`ℕ`{.Agda} 的每个元素都由这两个构造子生成。相应的归纳原理包含 `zero`{.Agda} 情形，以及从 `n` 过渡到 `suc n`{.Agda} 的归纳步骤。
<!--ja-->
自然数 `ℕ`{.Agda} は、二つの構成子から生成される帰納型です。構成子 `zero`{.Agda} は `ℕ`{.Agda} の要素であり、構成子 `suc`{.Agda} は任意の `n : ℕ`{.Agda} から別の要素 `suc n : ℕ`{.Agda} を作ります。構成規則は次のとおりです。

$$\frac{}{\mathsf{zero}:\mathbb{N}}\qquad\frac{n:\mathbb{N}}{\mathsf{suc}\,n:\mathbb{N}}.$$

`ℕ`{.Agda} のすべての要素は、この二つの構成子から生成されます。対応する帰納原理は、`zero`{.Agda} の場合と、`n` から `suc n`{.Agda} へ進む帰納段階からなります。
<!--/-->

<!--en-->
To define a function from `ℕ`{.Agda} by recursion, it is therefore enough to give its value at `zero`{.Agda} and to give the value at `suc n`{.Agda} from the value already obtained at `n`.
<!--zh-->
因此，要递归定义从 `ℕ`{.Agda} 出发的函数，只需给出函数在 `zero`{.Agda} 处的值，并说明如何由已经得到的 `n` 处之值构造 `suc n`{.Agda} 处之值。
<!--ja-->
したがって、`ℕ`{.Agda} からの関数を再帰的に定義するには、`zero`{.Agda} での値と、すでに得られた `n` での値から `suc n`{.Agda} での値を作る方法を与えれば十分です。
<!--/-->

```agda
open import Cubical.Data.Nat public
  using ( ℕ; zero; suc )
```

<!--en-->
## Finite indices
<!--zh-->
## 有限数
<!--ja-->
## 有限添字
<!--/-->

<!--en-->
`Fin`{.Agda} is a family of types indexed by natural numbers. The type `Fin zero`{.Agda} has no constructors. At an index `suc n`{.Agda}, the constructor `zero`{.Agda} gives an element directly, while `suc`{.Agda} sends each element of `Fin n`{.Agda} to an element of `Fin (suc n)`{.Agda}. These constructors obey the rules

$$\frac{}{\mathsf{zero}:\operatorname{Fin}(\operatorname{suc}\,n)}\qquad\frac{i:\operatorname{Fin}(n)}{\mathsf{suc}\,i:\operatorname{Fin}(\operatorname{suc}\,n)}.$$

Consequently `Fin n`{.Agda} has exactly `n` elements: none when `n` is `zero`{.Agda}, and one new element together with a copy of every element of `Fin n`{.Agda} when the index is `suc n`{.Agda}.
<!--zh-->
`Fin`{.Agda} 是以自然数为索引的一族类型。`Fin zero`{.Agda} 没有构造子；当索引为 `suc n`{.Agda} 时，构造子 `zero`{.Agda} 直接给出一个元素，而 `suc`{.Agda} 把 `Fin n`{.Agda} 的每个元素变为 `Fin (suc n)`{.Agda} 的元素。构造规则为

$$\frac{}{\mathsf{zero}:\operatorname{Fin}(\operatorname{suc}\,n)}\qquad\frac{i:\operatorname{Fin}(n)}{\mathsf{suc}\,i:\operatorname{Fin}(\operatorname{suc}\,n)}.$$

因此，`Fin n`{.Agda} 恰有 `n` 个元素：索引为 `zero`{.Agda} 时没有元素；索引由 `n` 变为 `suc n`{.Agda} 时，新增一个元素，并保留由 `Fin n`{.Agda} 的每个元素经 `suc`{.Agda} 构造出的元素。
<!--ja-->
`Fin`{.Agda} は自然数を添字とする型の族です。`Fin zero`{.Agda} には構成子がありません。添字が `suc n`{.Agda} のとき、構成子 `zero`{.Agda} が一つの要素を直接与え、`suc`{.Agda} は `Fin n`{.Agda} の各要素を `Fin (suc n)`{.Agda} の要素へ送ります。構成規則は次のとおりです。

$$\frac{}{\mathsf{zero}:\operatorname{Fin}(\operatorname{suc}\,n)}\qquad\frac{i:\operatorname{Fin}(n)}{\mathsf{suc}\,i:\operatorname{Fin}(\operatorname{suc}\,n)}$$

したがって `Fin n`{.Agda} はちょうど `n` 個の要素をもちます。添字が `zero`{.Agda} のとき要素はなく、`n` から `suc n`{.Agda} へ移ると、一つの新しい要素と、`Fin n`{.Agda} の各要素から `suc`{.Agda} で作られる要素が得られます。
<!--/-->

```agda
open import Cubical.Data.FinData public
  using ( Fin; zero; suc )
```

<!--en-->
## Vectors
<!--zh-->
## 向量
<!--ja-->
## ベクトル
<!--/-->

<!--en-->
A vector `Vec A n`{.Agda} is a list of elements of `A` whose length is part of its type. Its two constructors are expressed by the rules

$$\frac{}{[]:\operatorname{Vec}(A,0)}\qquad\frac{a:A\quad v:\operatorname{Vec}(A,n)}{a∷v:\operatorname{Vec}(A,\operatorname{suc}\,n)}.$$

The constructor `[]`{.Agda} produces an element of `Vec A zero`{.Agda}. Given `a : A`{.Agda} and `v : Vec A n`{.Agda}, the constructor `_∷_`{.Agda} produces `a ∷ v : Vec A (suc n)`{.Agda}. Thus the natural-number index is determined together with the vector. The function `lookup`{.Agda} has type `Fin n → Vec A n → A`{.Agda}; its shared index requires its two arguments to have the same `n`.
<!--zh-->
向量 `Vec A n`{.Agda} 是由 `A` 的元素组成、且长度写入类型的列表。它的两个构造规则可以写成

$$\frac{}{[]:\operatorname{Vec}(A,0)}\qquad\frac{a:A\quad v:\operatorname{Vec}(A,n)}{a∷v:\operatorname{Vec}(A,\operatorname{suc}\,n)}.$$

构造子 `[]`{.Agda} 给出 `Vec A zero`{.Agda} 的元素。给定 `a : A`{.Agda} 和 `v : Vec A n`{.Agda}，构造子 `_∷_`{.Agda} 给出 `a ∷ v : Vec A (suc n)`{.Agda}。自然数索引由此与向量一同确定。函数 `lookup`{.Agda} 的类型是 `Fin n → Vec A n → A`{.Agda}；两个参数共享同一个索引 `n`。
<!--ja-->
ベクトル `Vec A n`{.Agda} は `A` の元からなるリストで、その長さが型の一部になっています。その二つの構成子は、次の推論式で表せます。

$$\frac{}{[]:\operatorname{Vec}(A,0)}\qquad\frac{a:A\quad v:\operatorname{Vec}(A,n)}{a∷v:\operatorname{Vec}(A,\operatorname{suc}\,n)}$$

構成子 `[]`{.Agda} は `Vec A zero`{.Agda} の要素を与えます。`a : A`{.Agda} と `v : Vec A n`{.Agda} が与えられると、構成子 `_∷_`{.Agda} は `a ∷ v : Vec A (suc n)`{.Agda} を与えます。このように自然数の添字はベクトルとともに定まります。関数 `lookup`{.Agda} の型は `Fin n → Vec A n → A`{.Agda} であり、二つの引数は同じ添字 `n` を共有します。
<!--/-->

```agda
open import Cubical.Data.Vec public
  using ( Vec; []; _∷_; lookup )
```

<!--en-->
## The [empty type]{.term-intro #empty-type}
<!--zh-->
## [空类型]{.term-intro #empty-type}
<!--ja-->
## [空型]{.term-intro #empty-type}
<!--/-->

<!--en-->
The empty type `⊥*`{.Agda} is a type with no elements. It has no constructors, so an element of `⊥*`{.Agda} cannot be constructed directly.

If some branch of an argument yields `x : ⊥*`{.Agda}, the assumptions of that branch cannot hold. Since no such `x` exists, it can be eliminated into any type. This is the elimination principle of the empty type:

<div class="single-line-code"><code>⊥* → A</code></div>

This does not compute an element of `A` from actual data. It says that the case needed to supply an input cannot occur, so there is no constructor case to define.
<!--zh-->
空类型 `⊥*`{.Agda} 是没有任何元素的类型。它没有构造子，因此无法直接构造 `⊥*`{.Agda} 的元素。

如果在某个论证分支中得到 `x : ⊥*`{.Agda}，就意味着该分支的前提不可能成立。由于不存在这样的 `x`，我们可以从它消去到任意类型。这就是空类型的消去原理：

<div class="single-line-code"><code>⊥* → A</code></div>

这里并不是从某项实际数据中计算出 `A` 的元素，而是说明：产生输入所需的情形根本不会发生，所以无需给出任何构造分支。
<!--ja-->
空型 `⊥*`{.Agda} は要素を一つももたない型です。構成子がないため、`⊥*`{.Agda} の要素を直接構成することはできません。

ある論証の分岐で `x : ⊥*`{.Agda} が得られたなら、その分岐の仮定は成立しえません。そのような `x` は存在しないので、そこから任意の型へ消去できます。これが空型の消去原理です。

<div class="single-line-code"><code>⊥* → A</code></div>

これは実際のデータから `A` の要素を計算するものではありません。入力を与えるために必要な場合そのものが起こらないため、構成子に対する場合を定義する必要がないことを述べています。
<!--/-->

<!--en-->
`isProp⊥*`{.Agda} states that `⊥*`{.Agda} is a proposition. By definition, this requires any two of its elements to be equal. Since the empty type has no elements, there is no case to compare.
<!--zh-->
`isProp⊥*`{.Agda} 表明 `⊥*`{.Agda} 是命题。按照命题的定义，需要证明其中任意两个元素都相等；但空类型中没有元素，因此不存在需要比较的情形。
<!--ja-->
`isProp⊥*`{.Agda} は、`⊥*`{.Agda} が命題であることを示します。命題の定義に従えば、その任意の二要素が等しいことを示す必要があります。しかし空型には要素がないので、比較すべき場合は存在しません。
<!--/-->

```agda
open import Cubical.Data.Empty public
  using ( ⊥*; isProp⊥* )
```

<!--en-->
## Logical operations on propositions

The proposition universe is closed under the usual logical operations. For propositions `P` and `Q`, the values `P ⊓ Q`, `P ⊔ Q`, `P ⇒ Q` and `¬ P` express conjunction, disjunction, implication and negation. The constants `⊤` and `⊥` express truth and falsity. The indexed operations `⋀ A P` and `⋁ A P` express universal and existential quantification over a type `A`.

Conjunction and universal quantification are already propositions because products and dependent function types preserve propositionhood. Disjunction and existential quantification begin instead with a sum or a dependent pair, whose elements may retain more information than a proposition permits. **[Propositional truncation]{.term-intro #propositional-truncation}** discards that extra information while preserving whether an element exists; applying it makes these two constructions propositions as well.

These names come directly from the operations on `hProp`{.Agda}. Only falsity needs a small level adjustment: the library's empty proposition lives at the bottom universe level, whereas the lifted empty type `⊥*`{.Agda} lets us form an empty proposition at any level. The explicit argument `A` in `⋀ A P` and `⋁ A P` keeps the domain of quantification visible.
<!--zh-->
## 命题的逻辑运算

命题宇宙对通常的逻辑运算封闭。对命题 `P` 与 `Q`，`P ⊓ Q`、`P ⊔ Q`、`P ⇒ Q` 与 `¬ P` 分别表示合取、析取、蕴涵与否定，常量 `⊤` 与 `⊥` 分别表示真与假。带索引的运算 `⋀ A P` 与 `⋁ A P` 则表示在类型 `A` 上作全称量化与存在量化。

积与依值函数类型保持命题性，所以合取与全称量化的结果仍是命题。析取与存在量化却分别从和类型与依值对开始，其中的元素可能保留命题所不需要的额外信息。**[命题截断]{.term-intro #propositional-truncation}**会抹去这些信息，同时保留类型是否有元素；经过截断，这两种构造也成为命题。

这些名称直接取自 `hProp`{.Agda} 上的逻辑运算。只有假命题需要调整宇宙层级：库中的空命题位于最低层宇宙，而提升后的空类型 `⊥*`{.Agda} 可以在任意层级构造空命题。`⋀ A P` 与 `⋁ A P` 显式写出参数 `A`，是为了让量词的论域直接呈现在表达式中。
<!--ja-->
## 命題の論理演算

命題の宇宙は通常の論理演算について閉じています。命題 `P` と `Q` に対して、`P ⊓ Q`、`P ⊔ Q`、`P ⇒ Q`、`¬ P` はそれぞれ連言、選言、含意、否定を表し、定数 `⊤` と `⊥` は真と偽を表します。添字付きの演算 `⋀ A P` と `⋁ A P` は、型 `A` にわたる全称量化と存在量化を表します。

積と依存関数型は命題性を保つので、連言と全称量化の結果はふたたび命題になります。一方、選言と存在量化は直和と依存対から始まり、その要素は命題には不要な情報を残すことがあります。**[命題的切り詰め]{.term-intro #propositional-truncation}**は、要素が存在するかどうかを保ったまま、その余分な情報を捨てます。切り詰めを施せば、この二つの構成も命題になります。

これらの名前は `hProp`{.Agda} 上の論理演算から直接取られます。偽だけには宇宙レベルの小さな調整が必要です。ライブラリの空命題は最下位の宇宙レベルにありますが、持ち上げられた空型 `⊥*`{.Agda} を使えば任意のレベルで空命題を作れます。`⋀ A P` と `⋁ A P` で引数 `A` を明示するのは、量化の領域を式の中に見える形で残すためです。
<!--/-->

```agda
import Cubical.Functions.Logic as Logic

_⊓_ : ∀ {ℓ ℓ'} → hProp ℓ → hProp ℓ' → hProp (ℓ-max ℓ ℓ')
_⊓_ = Logic._⊓_

_⊔_ : ∀ {ℓ ℓ'} → hProp ℓ → hProp ℓ' → hProp (ℓ-max ℓ ℓ')
_⊔_ = Logic._⊔_

_⇒_ : ∀ {ℓ ℓ'} → hProp ℓ → hProp ℓ' → hProp (ℓ-max ℓ ℓ')
_⇒_ = Logic._⇒_

¬_ : ∀ {ℓ} → hProp ℓ → hProp ℓ
¬_ = Logic.¬_

⊤ : ∀ {ℓ} → hProp ℓ
⊤ = Logic.⊤

⊥ : ∀ {ℓ} → hProp ℓ
⊥ = ⊥* , isProp⊥*

⋀ : ∀ {ℓ ℓ'} (A : Type ℓ) → (A → hProp ℓ') → hProp (ℓ-max ℓ ℓ')
⋀ A P = Logic.∀[]-syntax P

⋁ : ∀ {ℓ ℓ'} (A : Type ℓ) → (A → hProp ℓ') → hProp (ℓ-max ℓ ℓ')
⋁ A P = Logic.∃[]-syntax P

infixr 12 _⊓_ _⊔_
infixr 10 _⇒_
infix 3 ¬_
```

<!--en-->
## The identity function
<!--zh-->
## 恒等函数
<!--ja-->
## 恒等関数
<!--/-->

<!--en-->
The identity function `id`{.Agda} accepts an element and returns that same element unchanged. Its type is:
<!--zh-->
恒等函数 `id`{.Agda} 接受一个元素，并原样返回这个元素。它的类型为：
<!--ja-->
恒等関数 `id`{.Agda} は要素を受け取り、その要素を変更せずにそのまま返します。型は次のとおりです。
<!--/-->

```agda
id : ∀ {ℓ} {A : Type ℓ} → A → A
```

<!--en-->
Here `ℓ`{.Agda} is an arbitrary universe level and `A`{.Agda} is an arbitrary type at that level. Since the signature imposes no further condition on `A`{.Agda}, `id`{.Agda} applies to an element of any type.
<!--zh-->
其中，`ℓ`{.Agda} 是任意宇宙层级，`A`{.Agda} 是该层级中的任意类型。由于类型签名没有对 `A`{.Agda} 增加其他条件，`id`{.Agda} 可以作用于任何类型的元素。
<!--ja-->
ここで `ℓ`{.Agda} は任意の宇宙レベル、`A`{.Agda} はそのレベルの任意の型です。型シグネチャは `A`{.Agda} にほかの条件を課していないため、`id`{.Agda} は任意の型の要素に適用できます。
<!--/-->

```agda
id x = x
```

<!--en-->
The input `x`{.Agda} already has the result type `A`{.Agda}, so it can be returned directly. The definition neither changes `x`{.Agda} nor inspects how it was constructed.
<!--zh-->
输入 `x`{.Agda} 本身已经具有结果类型 `A`{.Agda}，所以可以直接作为结果返回。这个定义既不改变 `x`{.Agda}，也不需要分析 `x`{.Agda} 的构造方式。
<!--ja-->
入力 `x`{.Agda} はすでに結果の型 `A`{.Agda} をもつので、そのまま結果として返せます。この定義は `x`{.Agda} を変更せず、`x`{.Agda} がどのように構成されたかを調べる必要もありません。
<!--/-->

<!--en-->
## Recap

This chapter introduced the host-level vocabulary used throughout the book:

- `Type`{.Agda} and `Level`{.Agda} describe type universes and their levels;
- Π types represent dependent functions, and Σ types represent dependent pairs;
- record types flatten nested Σ types through named fields and constructors;
- `Lift`{.Agda} moves types between universe levels;
- path types represent equality, and homotopy levels describe the equality structure retained by a type;
- `hProp`{.Agda} is the universe of propositions, and `⟨_⟩`{.Agda} extracts the statement of a proposition;
- a class is a predicate valued in the universe of propositions, and `_∈ᶜ_`{.Agda} expresses class membership;
- `ℕ`{.Agda}, `Fin`{.Agda} and `Vec`{.Agda} are respectively an inductive type and two families indexed by natural numbers;
- `⊥*`{.Agda} is the empty type, and `id`{.Agda} is the identity function.

Together these notions form the basic formal language adopted in this book.
<!--zh-->
## 小结

本章介绍了书中反复使用的宿主层基础词汇：

- `Type`{.Agda} 与 `Level`{.Agda} 描述类型宇宙及其层级；
- Π 类型表示依值函数，Σ 类型表示依值对；
- 记录类型以具名字段和构造子展平多重嵌套的 Σ 类型；
- `Lift`{.Agda} 在宇宙层级之间搬移类型；
- 路径类型表示相等，同伦层级描述类型所保留的相等结构；
- `hProp`{.Agda} 是命题宇宙，`⟨_⟩`{.Agda} 取出命题的表述；
- 类是取值于命题宇宙的谓词，`_∈ᶜ_`{.Agda} 表示类的成员关系；
- `ℕ`{.Agda}、`Fin`{.Agda} 与 `Vec`{.Agda} 分别是归纳类型和以自然数为索引的类型族；
- `⊥*`{.Agda} 是空类型，`id`{.Agda} 是恒等函数。

这些概念共同组成了本书所采用的基本形式语言。
<!--ja-->
## まとめ

本章では、本書で用いるホストレベルの基礎語彙を導入しました。

- `Type`{.Agda} と `Level`{.Agda} は型宇宙とそのレベルを記述します。
- Π 型は依存関数を、Σ 型は依存対を表します。
- レコード型は、名前付きフィールドと構成子によって、入れ子になった Σ 型を平坦に表します。
- `Lift`{.Agda} は型を宇宙レベル間で移します。
- パス型は等しさを表し、ホモトピーレベルは型に残る等しさの構造を記述します。
- `hProp`{.Agda} は命題の宇宙であり、`⟨_⟩`{.Agda} は命題の記述を取り出します。
- クラスは命題の宇宙に値をとる述語であり、`_∈ᶜ_`{.Agda} はクラスへの所属を表します。
- `ℕ`{.Agda}、`Fin`{.Agda}、`Vec`{.Agda} は、それぞれ帰納型と、自然数を添字とする二つの型族です。
- `⊥*`{.Agda} は空型であり、`id`{.Agda} は恒等関数です。

これらの概念が、本書で採用する基本的な形式言語を構成します。
<!--/-->
