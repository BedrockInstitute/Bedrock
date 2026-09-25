```agda
{-# OPTIONS --cubical --safe --guardedness #-}
module Base.Prelude where
```

<!--en-->
# Prelude
<!--zh-->
# 基础词汇
<!--ja-->
# 基礎語彙
<!--/-->

<!--en-->

In this book, set theory is the **[object theory]{.term-intro #object-theory}** and cubical type theory is the **[metatheory]{.term-intro #metatheory}**: we construct models of set theory, interpret their sentences and prove their properties within cubical type theory. Agda checks the constructions and proofs, while the Cubical library supplies their basic vocabulary. We call this working environment the **[host]{.term-intro #host-environment}**. A host type or function therefore belongs to the metatheory, not to the objects inside a set-theoretic model.

This chapter introduces that vocabulary through its mathematical meaning and use. There is no need to memorize every symbol: later chapters import these notions together from `Base.Prelude`{.Agda}, and you can return here whenever a definition needs refreshing.

## Reading guide

Read the prose first, then the code immediately below it: the code makes the preceding explanation precise. The code automatically displays ∎ at the end of a definition with a type signature and defining equations; helpers inside a `where`{.Agda} clause belong to the enclosing definition. Submodules can be folded to keep the larger argument in view.

Use the [interactive contents](index.html#reading-explorer) to choose a route, or the [dependency graph](index.html#dependency-map) to inspect prerequisites. The learning route at the top of each chapter lists its direct prerequisites and possible continuations. Dashed chapter titles reveal the formal setup or `import`{.Agda} statements without interrupting the prose; parameterized module declarations stay in the body.

Hover over a marked name or expression to inspect its type, and continue through names inside the popup. On a phone, tap to open this information and hold a highlighted node while sliding sideways to select a smaller or larger expression. To inspect a definition, click its name on desktop or use the popup's window button on mobile. The definition window supports back and forward; its enter button, or another click on the same definition inside it, takes you to the actual page.

Keywords and syntax symbols offer short explanations with links to the Agda manual. Terms link back to their introductions. The basic vocabulary first leads here, where its meaning is explained; the visible Cubical imports then lead to the library's original definitions when you want to look deeper.
<!--zh-->

本书以集合论为**[对象理论]{.term-intro #object-theory}**，以立方类型论为**[元理论]{.term-intro #metatheory}**：在立方类型论中构造集合论的模型，解释其语句，并证明其性质。Agda 检查这些构造与证明，Cubical 库提供所需的基础词汇；我们把这套工作环境简称为**[宿主]{.term-intro #host-environment}**。因此，「宿主中的类型或函数」属于元理论，而不是集合论模型内部的对象。

本章从数学含义和实际用法两方面介绍这些词汇。不必一次记住所有符号：后续章节会从 `Base.Prelude`{.Agda} 统一引入它们，遇到不熟悉的概念时，再回到这里查阅即可。

## 阅读指南

阅读时，先看文字，再看紧随其后的代码：代码是前文解释的精确表达。代码会在带类型声明和定义等式的定义末尾自动显示 ∎；`where`{.Agda} 中的辅助定义归属于外层定义。子模块可以折叠，方便把握整体论证。

可以在[交互式目录](index.html#reading-explorer)中选择阅读路线，也可以用[依赖图](index.html#dependency-map)查看先修关系。每章顶部的学习路线列出直接先修和可选后续章节。带虚线的章节标题可以显示形式化设置或 `import`{.Agda} 语句，不打断正文；带参数的模块声明则保留在正文中。

悬停在带标记的名称或表达式上可以查看类型，也可以继续查看弹窗中的名称。手机上轻触即可打开这些信息，按住色块左右滑动可选择更小或更大的表达式。查看定义时，桌面端点击名称，手机端使用提示窗里的窗口按钮。定义窗口支持前进和后退；点击其跳转按钮，或在窗内再次点击当前定义，才会进入实际页面。

关键字和语法符号附有简短解释与 Agda 官方文档链接，术语则可以追溯到首次引入的位置。基础词汇先指向本章的讲解；想进一步了解库内部的定义时，再沿可见的 Cubical 导入代码进入原文。
<!--ja-->

本書では集合論を**[対象理論]{.term-intro #object-theory}**、立方型理論を**[メタ理論]{.term-intro #metatheory}**とする。立方型理論の中で集合論のモデルを構成し、その文を解釈して性質を証明する。Agda が構成と証明を検査し、Cubical ライブラリが基礎語彙を提供する。この環境を**[ホスト]{.term-intro #host-environment}**と呼ぶ。したがって、ホストの型や関数はメタ理論に属し、集合論のモデル内部の対象とは異なる。

本章では、その語彙を数学的な意味と使い方から紹介する。記号を一度に覚える必要はない。後の章では `Base.Prelude`{.Agda} からまとめて導入するので、必要なときにここへ戻り、意味を確かめればよい。

## 読書案内

まず文章を読み、直後のコードでその精確な表現を確かめる。型宣言と定義等式を持つ定義の末尾には、コードが自動的に ∎ を表示する。`where`{.Agda} 内の補助定義は外側の定義に属する。部分モジュールを折り畳むと、議論の全体を見渡しやすい。

[対話型目次](index.html#reading-explorer)で学習ルートを選び、[依存グラフ](index.html#dependency-map)で前提関係を確認できる。各章の冒頭には直接の前提と次に進める章がある。破線の付いた章題から形式化の設定や `import`{.Agda} 文を確認でき、パラメータ付きモジュールの宣言は本文に残る。

印のある名前や式にポインタを重ねると型が現れ、その中の名前も続けて調べられる。携帯端末ではタップして情報を開き、色の付いた節点を押さえたまま左右に動かすと、より小さい式や大きい式を選べる。定義を見るには、デスクトップでは名前をクリックし、携帯端末ではポップアップのウィンドウボタンを使う。定義ウィンドウには前後移動があり、移動ボタン、または本文中の同じ定義の再クリックで実際のページへ進む。

キーワードと構文記号には短い説明と Agda 公式文書へのリンクがあり、用語からは最初の導入箇所へ戻れる。基礎語彙はまず本章の説明へ導く。ライブラリ内部の定義をさらに調べたいときは、表示された Cubical の import コードから原文へ進める。
<!--/-->

<!--en-->
We now explore the mathematical notions collected in this module one at a time.
<!--zh-->
下面逐个认识本模块汇集的数学概念。
<!--ja-->
ここから本モジュールに集めた数学的な概念を一つずつ見ていこう。
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

型理論では、型の大きさを区別しなければならない。すべての型を量化する型があれば、それは自分自身を含んでしまう。そこでホストは、各レベル `ℓ : Level`{.Agda} に一つずつある宇宙 `Type ℓ`{.Agda} へ型を分類する。代数的には、宇宙レベルは後続演算を備えた最小元付き結び半束をなす。`ℓ-zero`{.Agda} が最小元、`ℓ-suc`{.Agda} が後続演算、`ℓ-max`{.Agda} が二項の結びである。各宇宙はそれ自身も型である。

<div class="single-line-code" data-note="この一行は読者のための表記であり、正式な Agda コードブロックではない。Agda に近い擬似コードで、通常の数学の式よりコードに近い表記だが、それだけでコンパイルできるとは限らない。形式化の厳密さという点では、通常の数学的な表示と、完全な Agda コードの間に位置する。"><code>Type ℓ : Type (ℓ-suc ℓ)</code></div>

本書が「すべての集合」や「すべての命題」のような全体を扱うとき、主張に付いたレベルが、その全体をどの大きさとして扱うかを記録する。

<!--/-->

```agda
open import Cubical.Foundations.Prelude public
  using ( Type; Level; ℓ-zero; ℓ-suc; ℓ-max )
```

<!--en-->
The identity function `id`{.Agda} gives a simple example of a definition that works uniformly at every universe level. For an arbitrary level `ℓ`{.Agda} and type `A : Type ℓ`{.Agda}, it accepts an element of `A`{.Agda} and returns that same element:
<!--zh-->
恒等函数 `id`{.Agda} 是一个在每个宇宙层级上都能统一使用的简单例子。给定任意层级 `ℓ`{.Agda} 以及该层级中的类型 `A : Type ℓ`{.Agda}，它接受 `A`{.Agda} 的一个元素，并原样返回这个元素：
<!--ja-->
恒等関数 `id`{.Agda} は、どの宇宙レベルでも一様に使える定義の簡単な例である。任意のレベル `ℓ`{.Agda} と型 `A : Type ℓ`{.Agda} に対して、`A`{.Agda} の要素を受け取り、その要素をそのまま返す。
<!--/-->

```agda
id : ∀ {ℓ} {A : Type ℓ} → A → A
```

<!--en-->
The level and the type are implicit arguments, so callers normally supply only the element. Since that element already has the result type `A`{.Agda}, the defining equation simply returns it without inspecting how it was constructed.
<!--zh-->
层级参数与类型参数都是隐式的，因此调用时通常只需给出元素。这个元素本身已经具有结果类型 `A`{.Agda}，所以定义等式直接返回它，无须分析它是如何构造出来的。
<!--ja-->
レベルと型は暗黙引数なので、通常は要素だけを与えて使う。その要素はすでに結果の型 `A`{.Agda} をもつため、定義式は構成のされ方を調べずに、そのまま返す。
<!--/-->

```agda
id x = x
```

<!--en-->
### Moving between levels
<!--zh-->
### 层级之间的搬移
<!--ja-->
### レベル間の移動
<!--/-->

<!--en-->
The Agda type universes used here are not cumulative. An element of `Type ℓ`{.Agda} does not automatically become an element of `Type (ℓ-suc ℓ)`{.Agda}; moving a type between levels requires the explicit operation `Lift`{.Agda}.

`Lift ℓ A`{.Agda} is a [record type]{.term-ref #record-type} that wraps an element of the original type `A`{.Agda}. Given `a : A`{.Agda}, the function `lift`{.Agda} produces `lift a : Lift ℓ A`{.Agda}. Conversely, given `b : Lift ℓ A`{.Agda}, `lower b`{.Agda} retrieves the stored element of `A`{.Agda}.

The functions `lift`{.Agda} and `lower`{.Agda} are mutually inverse between `A`{.Agda} and `Lift ℓ A`{.Agda}. Two equations state the two directions separately:

<div class="single-line-code"><code>`lower (lift a) ≡ a`{.Agda}</code></div>

<div class="single-line-code"><code>`lift (lower b) ≡ b`{.Agda}</code></div>

The first says that packaging an element and immediately retrieving it returns the original element. The second says that retrieving an element from a lifted record and packaging it again returns the original record. Thus `Lift`{.Agda} changes the universe in which a type is presented and the representation of its elements, without adding or losing mathematical information.

More precisely, if `A`{.Agda} lives in `Type ℓ₁`{.Agda}, then `Lift ℓ₂ A`{.Agda} lives in `Type (ℓ-max ℓ₁ ℓ₂)`{.Agda}. If either universe level is already above the other, `ℓ-max`{.Agda} keeps it; otherwise it gives a common universe level large enough for both. Hence `Lift`{.Agda} does not raise a type by a fixed number of levels. It places the type in a universe large enough for the levels at hand.

A type can always be copied upward in this way, but <span class="prose-annotation-target">there is in general no way to move one down</span><aside class="prose-annotation-note">Propositions (types satisfying `isProp`{.Agda}) are the exception: the <a href="Base.Classical.html">Classical Boundary</a> chapter will show that excluded middle provides exactly the downward direction for them.</aside>.
<!--zh-->
我们使用的 Agda 类型宇宙不是累积的。`Type ℓ`{.Agda} 的元素并不自动成为 `Type (ℓ-suc ℓ)`{.Agda} 的元素；在层级之间搬移类型需要显式运算 `Lift`{.Agda}。

`Lift ℓ A`{.Agda} 是一个[记录类型]{.term-ref #record-type}，把原类型 `A`{.Agda} 的一个元素包装起来。给定 `a : A`{.Agda}，函数 `lift`{.Agda} 产生 `lift a : Lift ℓ A`{.Agda}；反过来，给定 `b : Lift ℓ A`{.Agda}，`lower b`{.Agda} 取出其中保存的 `A`{.Agda} 的元素。

`lift`{.Agda} 与 `lower`{.Agda} 在 `A`{.Agda} 和 `Lift ℓ A`{.Agda} 之间互为逆函数。这由两条等式分别表达：

<div class="single-line-code"><code>`lower (lift a) ≡ a`{.Agda}</code></div>

<div class="single-line-code"><code>`lift (lower b) ≡ b`{.Agda}</code></div>

第一条等式说，一个元素被装入 `Lift`{.Agda} 后立即取出，仍是原来的元素。第二条等式说，从 `Lift`{.Agda} 中取出元素再重新装入，仍得到原来的记录。因此，`Lift`{.Agda} 改变的是类型所在的宇宙以及元素的表示方式，不会增添或丢失数学信息。

具体来说，若 `A`{.Agda} 位于 `Type ℓ₁`{.Agda}，那么 `Lift ℓ₂ A`{.Agda} 位于 `Type (ℓ-max ℓ₁ ℓ₂)`{.Agda}。如果两个宇宙层级中已经有一个较高，`ℓ-max`{.Agda} 就保留那个层级；否则，它给出足以同时容纳二者的公共宇宙层级。因此，`Lift`{.Agda} 并不是把类型固定抬高若干层，而是把它放入当前所需的足够大的宇宙。

类型总能以这种方式向上复制，但<span class="prose-annotation-target">一般不能向下搬移</span><aside class="prose-annotation-note">命题 (满足 `isProp`{.Agda} 的类型) 是一个例外；<a href="Base.Classical.html">经典边界</a>一章将说明，排中律恰好为命题提供向下搬移的方向。</aside>。
<!--ja-->
ここで使う Agda の型宇宙は累積的ではない。`Type ℓ`{.Agda} の要素が自動的に `Type (ℓ-suc ℓ)`{.Agda} の要素になるわけではない。レベル間で型を移すには、明示的な演算 `Lift`{.Agda} が必要である。

`Lift ℓ A`{.Agda} は元の型 `A`{.Agda} の元を一つ包む[レコード型]{.term-ref #record-type}である。`a : A`{.Agda} を与えると、関数 `lift`{.Agda} は `lift a : Lift ℓ A`{.Agda} を作る。逆に `b : Lift ℓ A`{.Agda} があれば、`lower b`{.Agda} が保存された `A`{.Agda} の元を取り出す。

`lift`{.Agda} と `lower`{.Agda} は `A`{.Agda} と `Lift ℓ A`{.Agda} の間で互いに逆である。その二つの向きを別々の等式が表す。

<div class="single-line-code"><code>`lower (lift a) ≡ a`{.Agda}</code></div>

<div class="single-line-code"><code>`lift (lower b) ≡ b`{.Agda}</code></div>

第一の等式は、元を包んですぐ取り出せば元の要素に戻ることを述べる。第二の等式は、持ち上げられたレコードから元を取り出して包み直せば、元のレコードに戻ることを述べる。したがって `Lift`{.Agda} は型を提示する宇宙と元の表現を変えるが、数学的な情報を加えたり失ったりしない。

より正確には、`A`{.Agda} が `Type ℓ₁`{.Agda} に住むなら、`Lift ℓ₂ A`{.Agda} は `Type (ℓ-max ℓ₁ ℓ₂)`{.Agda} に住む。一方の宇宙レベルがすでに他方より高ければ、`ℓ-max`{.Agda} はそのレベルを保つ。そうでなければ、両方を収めるのに十分な共通の宇宙レベルを与える。したがって `Lift`{.Agda} は型を決まった段数だけ持ち上げるのではなく、現在の二つのレベルにとって十分大きな宇宙へ型を置く。

型は常にこの方法で上へコピーできるが、<span class="prose-annotation-target">一般には下へ動かせない</span><aside class="prose-annotation-note">命題 (`isProp`{.Agda} を満たす型) は例外である。<a href="Base.Classical.html">古典的境界</a>の章で、排中律が命題に対する下向きの方向をちょうど与えることを見る。</aside>。
<!--/-->

```agda
open import Cubical.Foundations.Prelude public
  using ( Lift; lift; lower )
```

<!--en-->
## Basic types

The next four constructions organize the data used throughout the book. They let us describe outputs that vary with their inputs, package related data together, distinguish alternatives, and give names to the components of a larger package. Each construction will receive its precise name and form below.
<!--zh-->
## 基本类型

下面四种构造组织了全书反复使用的数据。借助它们，我们可以描述随输入而变化的输出、把相互依赖的数据装在一起、区分不同选择，或为较大数据包的各个分量命名。下文会依次给出每种构造的确切名称和形式。
<!--ja-->
## 基本的な型

以下の四つの構成は、本書を通して用いるデータを組織する。これらを使うと、入力に応じて変わる出力を記述し、関連するデータをまとめ、選択肢を区別し、あるいは大きなデータのまとまりの各成分に名前を付けられる。それぞれの正確な名前と形は、以下で順に導入する。
<!--/-->

<!--en-->
### [Π types]{.term-intro #pi-type}

Many constructions later in the book need to provide data depending on each object. A Π type expresses this basic relationship.

Given a type `A`{.Agda} and a type `B x`{.Agda} for each `x : A`{.Agda}, we form the Π type:

<div class="single-line-code"><code>`(x : A) → B x`{.Agda}</code></div>

An element of a Π type is called a **[dependent function]{.term-intro #dependent-function}**. Given a dependent function `f`{.Agda}, it assigns to every `x : A`{.Agda} an element `f x`{.Agda} of `B x`{.Agda}. Because the type of the result depends on the input `x`{.Agda}, only after fixing the input do we know the type in which the corresponding output must lie.

When `B`{.Agda} does not depend on `x`{.Agda}, every output lies in the same type, and the dependent function specialises to an ordinary function:

<div class="single-line-code"><code>`A → B`{.Agda}</code></div>

An ordinary function gives an output in the same type for every input; a Π type gives, for every `x`{.Agda}, data belonging to the corresponding type `B x`{.Agda}.

<!--zh-->
### [Π 类型]{.term-intro #pi-type}

本书后面的许多构造都需要为每个对象给出一项依赖于它的数据。Π 类型正是表达这种关系的基本形式。

给定一个类型 `A`{.Agda}，以及对每个 `x : A`{.Agda} 指定的类型 `B x`{.Agda}，我们可以构造 Π 类型：

<div class="single-line-code"><code>`(x : A) → B x`{.Agda}</code></div>

Π 类型的元素称为**[依值函数]{.term-intro #dependent-function}**。给定一个依值函数 `f`{.Agda}，它为每个 `x : A`{.Agda} 给出一个属于 `B x`{.Agda} 的元素 `f x`{.Agda}。由于结果所在的类型取决于输入 `x`{.Agda}，只有确定输入以后，才能确定相应输出应当属于哪个类型。

当 `B`{.Agda} 不依赖 `x`{.Agda} 时，所有输出都属于同一个类型，依值函数便特化为普通函数：

<div class="single-line-code"><code>`A → B`{.Agda}</code></div>

普通函数为每个输入给出同一类型中的输出；Π 类型则为每个 `x`{.Agda} 给出属于相应类型 `B x`{.Agda} 的数据。

<!--ja-->
### [Π 型]{.term-intro #pi-type}

本書の後の多くの構成では、各対象に対して、それに依存するデータを与える必要がある。Π 型はこの関係を表す基本形である。

型 `A`{.Agda} と、各 `x : A`{.Agda} に対して型 `B x`{.Agda} が与えられたとき、Π 型を作る。

<div class="single-line-code"><code>`(x : A) → B x`{.Agda}</code></div>

Π 型の元を**[依存関数]{.term-intro #dependent-function}**と呼ぶ。依存関数 `f`{.Agda} は、各 `x : A`{.Agda} に対して `B x`{.Agda} の元 `f x`{.Agda} を与える。結果が属すべき型は入力 `x`{.Agda} に依存するため、入力を定めて初めて対応する出力の型が定まる。

`B`{.Agda} が `x`{.Agda} に依存しない場合、すべての出力は同じ型に属し、依存関数は通常の関数に特化する。

<div class="single-line-code"><code>`A → B`{.Agda}</code></div>

通常の関数は各入力に対して同じ型の出力を与えるが、Π 型は各 `x`{.Agda} に対して、対応する型 `B x`{.Agda} に属するデータを与える。

<!--/-->

<!--en-->
### [Σ types]{.term-intro #sigma-type}

Many constructions later in the book need to keep a particular object together with a piece of data that depends on it. A Σ type expresses this basic relationship.

Given a type `A`{.Agda} and a type `B x`{.Agda} for each `x : A`{.Agda}, we form the Σ type:

<div class="single-line-code"><code>`Σ (x : A) B x`{.Agda}</code></div>

An element of a Σ type is called a **[dependent pair]{.term-intro #dependent-pair}**. It is built in two steps: choose `a : A`{.Agda}, then choose an element `b`{.Agda} of `B a`{.Agda}; the resulting pair is written `(a , b)`{.Agda}. We call `a`{.Agda} the **[first component]{.term-intro #first-component}** and `b`{.Agda} the **[second component]{.term-intro #second-component}**. Because the type of the second component depends on `a`{.Agda}, only after fixing the first component do we know the type in which the second must lie.

The second component may itself be a proof of a property of the first. This book calls a proof carried together with an object so that later reasoning may use the property a **[certificate]{.term-intro #certificate}**. A certificate remains an ordinary Agda proof; the name emphasizes its role in the dependent pair.

When `B`{.Agda} does not depend on `x`{.Agda}, every second component lies in the same type, and the dependent pair specialises to an ordinary product:

<div class="single-line-code"><code>`A × B = Σ (_ : A) B`{.Agda}</code></div>

An ordinary product places two independent elements together; a Σ type places a particular `a`{.Agda} together with data belonging to the corresponding type `B a`{.Agda}. Dependent pairs are built with `_,_`{.Agda}, `fst`{.Agda} extracts the first component, and `snd`{.Agda} extracts the second.

<!--zh-->
### [Σ 类型]{.term-intro #sigma-type}

本书后面的许多构造都需要把某个对象与一项依赖于它的数据放在一起。Σ 类型正是表达这种关系的基本形式。

给定一个类型 `A`{.Agda}，以及对每个 `x : A`{.Agda} 指定的类型 `B x`{.Agda}，我们可以构造 Σ 类型：

<div class="single-line-code"><code>`Σ (x : A) B x`{.Agda}</code></div>

Σ 类型的元素称为**[依值对]{.term-intro #dependent-pair}**。它先给出一个 `a : A`{.Agda}，再给出一个属于 `B a`{.Agda} 的元素 `b`{.Agda}，所得的对写作 `(a , b)`{.Agda}。我们把 `a`{.Agda} 称为**[第一分量]{.term-intro #first-component}**，把 `b`{.Agda} 称为**[第二分量]{.term-intro #second-component}**。由于第二分量的类型取决于 `a`{.Agda}，只有确定第一分量以后，才能确定第二分量应当属于哪个类型。

第二分量也可以是关于第一分量的性质证明。本书把这种随对象一同携带、使后续论证能够使用相应性质的证明称为**[证书]{.term-intro #certificate}**。证书仍然是普通的 Agda 证明；这个名称强调的是它在依值对中所起的作用。

当 `B`{.Agda} 不依赖 `x`{.Agda} 时，所有第二分量都属于同一个类型，依值对便特化为普通的积：

<div class="single-line-code"><code>`A × B = Σ (_ : A) B`{.Agda}</code></div>

普通的积把两个彼此独立的元素放在一起；Σ 类型则把某个 `a`{.Agda} 与属于相应类型 `B a`{.Agda} 的数据放在一起。依值对用 `_,_`{.Agda} 构造，用 `fst`{.Agda} 取出第一分量，用 `snd`{.Agda} 取出第二分量。

<!--ja-->
### [Σ 型]{.term-intro #sigma-type}

本書の後の多くの構成では、ある対象と、それに依存する一つのデータを一緒に保つ必要がある。Σ 型はこの関係を表す基本形である。

型 `A`{.Agda} と、各 `x : A`{.Agda} に対して指定された型 `B x`{.Agda} があるとき、Σ 型を作る。

<div class="single-line-code"><code>`Σ (x : A) B x`{.Agda}</code></div>

Σ 型の元を**[依存対]{.term-intro #dependent-pair}**と呼ぶ。まず `a : A`{.Agda} を選び、次に `B a`{.Agda} の元 `b`{.Agda} を選ぶ。得られた対を `(a , b)`{.Agda} と書く。`a`{.Agda} を**[第一成分]{.term-intro #first-component}**、`b`{.Agda} を**[第二成分]{.term-intro #second-component}**と呼ぶ。第二成分の型は `a`{.Agda} に依存するため、第一成分を定めて初めて、第二成分がどの型に属すべきかが決まる。

第二成分を、第一成分の性質を示す証明にすることもできる。本書では、後の議論でその性質を使えるよう対象とともに携える証明を**[証明書]{.term-intro #certificate}**と呼ぶ。証明書は通常の Agda の証明であり、この名前は依存対の中で果たす役割を強調している。

`B`{.Agda} が `x`{.Agda} に依存しない場合、すべての第二成分は同じ型に属し、依存対は通常の積に特化する。

<div class="single-line-code"><code>`A × B = Σ (_ : A) B`{.Agda}</code></div>

通常の積は互いに独立した二つの元を一緒にするが、Σ 型は、ある `a`{.Agda} と、対応する型 `B a`{.Agda} に属するデータを一緒にする。依存対は `_,_`{.Agda} で作り、`fst`{.Agda} で第一成分を、`snd`{.Agda} で第二成分を取り出す。

<!--/-->

```agda
open import Cubical.Data.Sigma public
  using ( Σ; Σ-syntax; _×_; _,_; fst; snd )
```

<figure class="book-diagram type-comparison" id="fig-pi-sigma" aria-describedby="fig-pi-sigma-caption">
<div class="type-comparison-panels">
<div class="diagram-panel type-comparison-panel">

$$f : \prod_{x:A} B(x)$$

$$\begin{array}{rcl}
x_1 : A & \longmapsto & f(x_1) : B(x_1) \\[8pt]
x_2 : A & \longmapsto & f(x_2) : B(x_2) \\[4pt]
\vdots & & \vdots
\end{array}$$

</div>
<div class="diagram-panel type-comparison-panel">

$$(a,b) : \sum_{x:A} B(x)$$

<div class="sigma-pair">
<svg viewBox="0 0 320 130" aria-hidden="true" focusable="false">
<path class="diagram-guide" d="M75 35 L154 98 M245 35 L166 98"/>
</svg>
<span class="sigma-component sigma-first">$a : A$</span>
<span class="sigma-component sigma-second">$b : B(a)$</span>
<span class="sigma-component sigma-result">$(a,b)$</span>
</div>

</div>
</div>
<figcaption id="fig-pi-sigma-caption">
<!--en-->
A Π type handles "for every `x`{.Agda}, give data depending on `x`{.Agda}"; a Σ type handles "choose an `x`{.Agda}, and keep it together with data depending on it".
<!--zh-->
Π 类型处理的是「对每个 `x`{.Agda}，给出依赖于 `x`{.Agda} 的数据」；Σ 类型处理的是「选定某个 `x`{.Agda}，并将依赖于它的数据与它放在一起」。
<!--ja-->
Π 型が扱うのは「すべての `x`{.Agda} に対して、`x`{.Agda} に依存するデータを与えること」である。Σ 型が扱うのは「一つの `x`{.Agda} を選び、それに依存するデータと一緒に収めること」である。
<!--/-->
</figcaption>
</figure>

<!--en-->
### [Sum types]{.term-intro #sum-type}
<!--zh-->
### [和类型]{.term-intro #sum-type}
<!--ja-->
### [直和型]{.term-intro #sum-type}
<!--/-->

<!--en-->
The sum type `A ⊎ B`{.Agda} is an [inductive type]{.term-intro #inductive-type} whose elements come in two forms. An element `a : A`{.Agda} gives `inl a : A ⊎ B`{.Agda}, while an element `b : B`{.Agda} gives `inr b : A ⊎ B`{.Agda}. These operations are its **[constructors]{.term-intro #constructor}**, with rules

$$\frac{a:A}{\operatorname{inl}\,a:A\mathbin{\uplus}B}\qquad\frac{b:B}{\operatorname{inr}\,b:A\mathbin{\uplus}B}$$

Thus a sum value records both which side was chosen and the element supplied on that side. Pattern matching can recover both pieces of information. The eliminator `⊎-rec`{.Agda} handles the two constructors separately: one branch consumes an `A`{.Agda}, the other consumes a `B`{.Agda}, and both branches must produce the same target type.

$$\mathsf{\uplus\text{-}rec}:(A\to C)\to(B\to C)\to A\mathbin{\uplus}B\to C$$

$$\mathsf{\uplus\text{-}rec}\;f\;g\;x=
\begin{cases}
f(a), & x=\operatorname{inl}\,a,\\
g(b), & x=\operatorname{inr}\,b
\end{cases}$$
<!--zh-->
和类型 `A ⊎ B`{.Agda} 是一种[归纳类型]{.term-intro #inductive-type}，其元素有两种构造方式。给定 `a : A`{.Agda}，可以构造 `inl a : A ⊎ B`{.Agda}；给定 `b : B`{.Agda}，可以构造 `inr b : A ⊎ B`{.Agda}。构造规则为

$$\frac{a:A}{\operatorname{inl}\,a:A\mathbin{\uplus}B}\qquad\frac{b:B}{\operatorname{inr}\,b:A\mathbin{\uplus}B}$$

这里的 `inl`{.Agda} 与 `inr`{.Agda} 称为**[构造子]{.term-intro #constructor}**。因此，和类型的元素同时记录选中了哪一侧，以及该侧所给出的元素；模式匹配可以恢复这两项信息。消去子 `⊎-rec`{.Agda} 分别处理两个构造子：一个分支接收 `A`{.Agda}，另一个分支接收 `B`{.Agda}，两个分支必须产生相同的目标类型。

$$\mathsf{\uplus\text{-}rec}:(A\to C)\to(B\to C)\to A\mathbin{\uplus}B\to C$$

$$\mathsf{\uplus\text{-}rec}\;f\;g\;x=
\begin{cases}
f(a), & x=\operatorname{inl}\,a,\\
g(b), & x=\operatorname{inr}\,b
\end{cases}$$
<!--ja-->
直和 `A ⊎ B`{.Agda} は、二通りの構成法をもつ[帰納型]{.term-intro #inductive-type}である。`a : A`{.Agda} から `inl a : A ⊎ B`{.Agda} を構成でき、`b : B`{.Agda} から `inr b : A ⊎ B`{.Agda} を構成できる。構成規則は次のとおりである。

$$\frac{a:A}{\operatorname{inl}\,a:A\mathbin{\uplus}B}\qquad\frac{b:B}{\operatorname{inr}\,b:A\mathbin{\uplus}B}$$

ここで `inl`{.Agda} と `inr`{.Agda} を**[構成子]{.term-intro #constructor}**と呼ぶ。したがって直和の元は、どちら側が選ばれたかと、その側で与えられた元の両方を記録する。パターンマッチによって、その二つの情報を取り出せる。除去子 `⊎-rec`{.Agda} は二つの構成子を別々に扱う。一方の枝は `A`{.Agda} を、他方の枝は `B`{.Agda} を受け取り、どちらも同じ目的の型を作らなければならない。

$$\mathsf{\uplus\text{-}rec}:(A\to C)\to(B\to C)\to A\mathbin{\uplus}B\to C$$

$$\mathsf{\uplus\text{-}rec}\;f\;g\;x=
\begin{cases}
f(a), & x=\operatorname{inl}\,a,\\
g(b), & x=\operatorname{inr}\,b
\end{cases}$$
<!--/-->

```agda
open import Cubical.Data.Sum public
  using ( _⊎_; inl; inr )
  renaming ( rec to ⊎-rec )
```

<!--en-->
### [Record types]{.term-intro #record-type}
<!--zh-->
### [记录类型]{.term-intro #record-type}
<!--ja-->
### [レコード型]{.term-intro #record-type}
<!--/-->

<!--en-->
A record type can be understood as syntactic sugar for several nested Σ types. For example, suppose we want to package an element `a : A`{.Agda}, an element `b : B a`{.Agda} depending on `a`{.Agda}, and a proof `c : C a b`{.Agda} depending on both. The corresponding nested type is:

<div class="single-line-code"><code>`Σ (a : A) Σ (b : B a) C a b`{.Agda}</code></div>

Its elements have the shape:

<div class="single-line-code"><code>`(a , (b , c))`{.Agda}</code></div>

In Agda, the keyword `record`{.Agda} begins the declaration of such a type, after which its components are given [field]{.term-intro #record-field} names. Constructing an element of the record requires a value for every field. A record declaration may also use the keyword `constructor`{.Agda} to name this operation; that name is the record type's **[constructor]{.term-ref #constructor}**. The constructor accepts the field values in dependency order and assembles them into one record. If three fields correspond to `a`{.Agda}, `b`{.Agda} and `c`{.Agda}, a constructor named `mkR`{.Agda} can present the construction in the flat form:

<div class="single-line-code"><code>`mkR a b c`{.Agda}</code></div>

This carries the same data as the nested Σ value `(a , (b , c))`{.Agda}, without exposing the nesting. Field names act as [projections]{.term-intro #projection} that retrieve the corresponding components directly. One therefore need not remember the depth of a component or repeatedly compose `fst`{.Agda} and `snd`{.Agda}. Records preserve the dependent structure of nested Σ types while presenting larger packages through a clearer, flat interface. The [Agda documentation on record types](https://agda.readthedocs.io/en/v2.8.0/language/record-types.html) describes their declaration, construction and projections in detail.
<!--zh-->
记录类型可以看作多重嵌套的 Σ 类型的语法糖。例如，要把一个元素 `a : A`{.Agda}、一个依赖于 `a`{.Agda} 的元素 `b : B a`{.Agda}，以及一个依赖于前两者的证明 `c : C a b`{.Agda} 放在一起，可以使用类型：

<div class="single-line-code"><code>`Σ (a : A) Σ (b : B a) C a b`{.Agda}</code></div>

其中的元素具有如下嵌套形状：

<div class="single-line-code"><code>`(a , (b , c))`{.Agda}</code></div>

在 Agda 中，关键字 `record`{.Agda} 开始一个记录类型的声明，随后为其中的各个分量指定[字段]{.term-intro #record-field}名。要构造这个记录类型的元素，就必须为各个字段提供相应的值。记录声明还可以用关键字 `constructor`{.Agda} 为这种构造方式命名；这个名字称为记录类型的**[构造子]{.term-ref #constructor}**。构造子按照字段之间的依赖关系接收各字段的值，再把它们组装成一个记录。例如，若三个字段依次对应 `a`{.Agda}、`b`{.Agda} 和 `c`{.Agda}，构造子 `mkR`{.Agda} 便可以把构造过程展平地写成：

<div class="single-line-code"><code>`mkR a b c`{.Agda}</code></div>

这与嵌套 Σ 类型的 `(a , (b , c))`{.Agda} 表示同样的数据，只是省去了层层嵌套。字段名则充当[投影]{.term-intro #projection}，可以直接从记录中取出相应分量。因此，使用者不必记忆每个分量位于第几层，也不必反复组合 `fst`{.Agda} 与 `snd`{.Agda}。记录类型既保留了多重 Σ 类型的依赖结构，又通过具名字段和构造子提供了更清楚的平面接口。关于记录的声明、构造和投影，可进一步参阅 [Agda 的记录类型文档](https://agda.readthedocs.io/en/v2.8.0/language/record-types.html)。
<!--ja-->
レコード型は、複数の Σ 型を入れ子にしたものに対する構文糖と考えられる。たとえば、元 `a : A`{.Agda}、`a`{.Agda} に依存する元 `b : B a`{.Agda}、さらにその両方に依存する証明 `c : C a b`{.Agda} を一緒にまとめるとする。対応する入れ子の型は次のものである。

<div class="single-line-code"><code>`Σ (a : A) Σ (b : B a) C a b`{.Agda}</code></div>

その元は次の形になる。

<div class="single-line-code"><code>`(a , (b , c))`{.Agda}</code></div>

Agda では、キーワード `record`{.Agda} がレコード型の宣言を開始し、続いて各成分に[フィールド]{.term-intro #record-field}名を与える。レコード型の元を構成するには、すべてのフィールドに対応する値を与えなければならない。レコード宣言では、キーワード `constructor`{.Agda} を使ってこの構成操作に名前を付けることもできる。この名前をレコード型の**[構成子]{.term-ref #constructor}**と呼ぶ。構成子は依存関係の順にフィールドの値を受け取り、一つのレコードへ組み立てる。三つのフィールドが順に `a`{.Agda}、`b`{.Agda}、`c`{.Agda} に対応するなら、`mkR`{.Agda} という構成子による構成は平らに次のように書ける。

<div class="single-line-code"><code>`mkR a b c`{.Agda}</code></div>

これは入れ子の Σ 型の値 `(a , (b , c))`{.Agda} と同じデータを表すが、入れ子を表面に出さない。フィールド名は対応する成分を直接取り出す[射影]{.term-intro #projection}として働く。そのため、成分が何段目にあるかを覚えたり、`fst`{.Agda} と `snd`{.Agda} を何度も組み合わせたりする必要がない。レコード型は入れ子になった Σ 型の依存構造を保ちながら、名前付きフィールドと構成子によって大きなデータのまとまりを明瞭な平面インターフェースとして提示する。宣言、構成、射影の詳細は [Agda のレコード型の文書](https://agda.readthedocs.io/en/v2.8.0/language/record-types.html)を参照してほしい。
<!--/-->


<!--en-->
## Equality and [paths]{.term-intro #path}
<!--zh-->
## 相等与[路径]{.term-intro #path}
<!--ja-->
## 等式と[パス]{.term-intro #path}
<!--/-->

<!--en-->
In ordinary mathematics, $x = y$ asserts that two objects are equal. Here we write this assertion as `x ≡ y`{.Agda}: for two elements `x`{.Agda} and `y`{.Agda} of `A`{.Agda}, it is a type whose elements are proofs of their equality.

We reserve `=`{.Agda} for **[judgmental equality]{.term-intro #judgmental-equality}**, where the type system identifies two expressions by its definition and computation rules, as in `id x = x`{.Agda}. In a defining equation, this `=`{.Agda} plays the role often written $\mathrel{:=}$; judgmental equality also includes the consequences of computation. It is a judgment made by the type system, not itself a type in which we must supply a proof. By contrast, `x ≡ y`{.Agda} is a type, and `p : x ≡ y`{.Agda} supplies a proof of equality, playing the role of a proved $x = y$ in ordinary mathematics. When `x`{.Agda} and `y`{.Agda} are judgmentally equal, the constant path `refl`{.Agda} introduced below proves `x ≡ y`{.Agda}; a path between them does not in general make them judgmentally equal.

In cubical type theory, such an equality proof is called a **path** from `x`{.Agda} to `y`{.Agda}, and `x ≡ y`{.Agda} is called a path type. A path is therefore not another relation alongside equality: paths are the equality proofs used in this book, and path types are how the book represents equality. A path has a source and a target, so its direction can be reversed and paths can be joined end to end. The basic operations below arise from this structure.
<!--zh-->
在通常的数学中，$x = y$ 断言两个对象相等。本书把这个断言写作 `x ≡ y`{.Agda}：对 `A`{.Agda} 中的两个元素 `x`{.Agda} 和 `y`{.Agda}，它是一个类型，其中的元素就是二者相等的证明。

我们把 `=`{.Agda} 留给**[判断相等]{.term-intro #judgmental-equality}** (judgmental equality)，即类型系统依据定义与计算规则把两个表达式认作相同，例如 `id x = x`{.Agda}。在给出定义时，这个 `=`{.Agda} 相当于通常写的 $\mathrel{:=}$；判断相等也包括计算所得到的相等。它是类型系统作出的判断，本身并不是一个需要我们提供证明的类型。相比之下，`x ≡ y`{.Agda} 是一个类型，`p : x ≡ y`{.Agda} 给出其中的相等证明，对应于通常数学中需要证明的 $x = y$。若 `x`{.Agda} 与 `y`{.Agda} 判断相等，下面介绍的常值路径 `refl`{.Agda} 就能证明 `x ≡ y`{.Agda}；反过来，二者之间有路径，一般并不意味着它们判断相等。

在立方类型论中，这种相等证明称为从 `x`{.Agda} 到 `y`{.Agda} 的**路径**，而 `x ≡ y`{.Agda} 称为路径类型。因此，路径并不是相等之外的另一种关系：路径就是本书所使用的相等证明，路径类型就是本书表示相等的方式。路径有起点和终点，因而可以反转方向，也可以首尾相接；下面的基本操作正是从这一结构产生的。
<!--ja-->
通常の数学では、$x = y$ は二つの対象が等しいという主張である。本書ではこれを `x ≡ y`{.Agda} と書く。`A`{.Agda} の二つの要素 `x`{.Agda} と `y`{.Agda} に対して、これは両者の等しさの証明を要素とする型である。

`=`{.Agda} は**[判断的等しさ]{.term-intro #judgmental-equality}** (judgmental equality) に用いる。これは型システムが定義と計算の規則に従って二つの式を同じものと認めることであり、`id x = x`{.Agda} がその例である。定義を与える式では、この `=`{.Agda} は通常の $\mathrel{:=}$ に相当するが、判断的等しさには計算から得られる等しさも含まれる。これは型システムが下す判断であって、それ自体が証明を与えるべき型なのではない。一方、`x ≡ y`{.Agda} は型であり、`p : x ≡ y`{.Agda} はその等しさの証明を与え、通常の数学で証明する $x = y$ に対応する。`x`{.Agda} と `y`{.Agda} が判断的に等しければ、以下で紹介する定値パス `refl`{.Agda} によって `x ≡ y`{.Agda} を証明できるが、両者の間にパスがあっても、一般には判断的に等しいとは限らない。

立方型理論では、この等しさの証明を `x`{.Agda} から `y`{.Agda} への**パス**と呼び、`x ≡ y`{.Agda} をパス型と呼ぶ。したがって、パスは等しさとは別に置かれた関係ではない。パスが本書で使う等しさの証明であり、パス型が本書における等しさの表現である。パスには始点と終点があるため、向きを逆にしたり、端と端をつないだりできる。以下の基本操作はこの構造から生まれる。
<!--/-->

<figure class="book-diagram type-comparison path-figure" id="fig-path-operations" aria-describedby="fig-path-operations-caption">
<div class="path-operations">
<section class="diagram-panel path-operation">
<div class="path-stage" style="aspect-ratio:240/190">
<svg viewBox="0 0 240 190" aria-hidden="true" focusable="false">
<circle class="diagram-point" cx="120" cy="95" r="4"/>
</svg>
<span class="path-label" style="left:50%;top:31.5789%">$\operatorname{refl}_x$</span>
<span class="path-label" style="left:50%;top:62.6316%">$x$</span>
</div>
<div class="path-signature">

$$\begin{gathered}\operatorname{refl}_x : x\equiv x\end{gathered}$$

</div>
<!--en-->
`refl`{.Agda} is a path from an element to itself and gives reflexivity of equality.
<!--zh-->
`refl`{.Agda} 是从一个元素到自身的路径，给出相等的自反性。
<!--ja-->
`refl`{.Agda} は要素からそれ自身へのパスであり、等しさの反射性を与える。
<!--/-->

</section>
<section class="diagram-panel path-operation">
<div class="path-stage" style="aspect-ratio:240/190">
<svg viewBox="0 0 240 190" aria-hidden="true" focusable="false">
<path class="diagram-path" d="M35 55 Q120 0 205 55 M35 148 Q120 100 205 148"/><circle class="diagram-point" cx="35" cy="55" r="4"/><circle class="diagram-point" cx="205" cy="55" r="4"/><circle class="diagram-point" cx="35" cy="148" r="4"/><circle class="diagram-point" cx="205" cy="148" r="4"/>
</svg>
<span class="path-label" style="left:7.5%;top:28.9474%">$x$</span>
<span class="path-label" style="left:92.9167%;top:28.9474%">$y$</span>
<span class="path-label" style="left:50%;top:7.36842%">$p$</span>
<span class="path-label" style="left:7.5%;top:77.8947%">$y$</span>
<span class="path-label" style="left:92.9167%;top:77.8947%">$x$</span>
<span class="path-label" style="left:50%;top:87.3684%">$\operatorname{sym}\,p$</span>
<span class="path-label" style="left:50%;top:47.8947%">$\Big\downarrow\mathrlap{\;{\scriptstyle\operatorname{sym}}}$</span>
</div>
<div class="path-signature">

$$\begin{gathered}p:x\equiv y,\quad\operatorname{sym}\,p:y\equiv x\end{gathered}$$

</div>
<!--en-->
`sym`{.Agda} reverses a path; a path from `x`{.Agda} to `y`{.Agda} thereby becomes a path from `y`{.Agda} to `x`{.Agda}.
<!--zh-->
`sym`{.Agda} 反转路径的方向；从 `x`{.Agda} 到 `y`{.Agda} 的路径由此变成从 `y`{.Agda} 到 `x`{.Agda} 的路径。
<!--ja-->
`sym`{.Agda} はパスの向きを逆にする。`x`{.Agda} から `y`{.Agda} へのパスは、これによって `y`{.Agda} から `x`{.Agda} へのパスになる。
<!--/-->

</section>
<section class="diagram-panel path-operation">
<div class="path-stage" style="aspect-ratio:240/190">
<svg viewBox="0 0 240 190" aria-hidden="true" focusable="false">
<path class="diagram-path" d="M35 110 L120 45 L205 110 M35 110 Q120 179 205 110"/><circle class="diagram-point" cx="35" cy="110" r="4"/><circle class="diagram-point" cx="120" cy="45" r="4"/><circle class="diagram-point" cx="205" cy="110" r="4"/>
</svg>
<span class="path-label" style="left:7.5%;top:57.8947%">$x$</span>
<span class="path-label" style="left:50%;top:12.6316%">$y$</span>
<span class="path-label" style="left:92.9167%;top:57.8947%">$z$</span>
<span class="path-label" style="left:27.9167%;top:34.7368%">$p$</span>
<span class="path-label" style="left:73.3333%;top:34.7368%">$q$</span>
<span class="path-label" style="left:50%;top:87.8947%">$p\mathbin{\cdot}q$</span>
</div>
<div class="path-signature">

$$\begin{gathered}p:x\equiv y,\quad q:y\equiv z\\[3pt]p\mathbin{\cdot}q:x\equiv z\end{gathered}$$

</div>
<!--en-->
`_∙_`{.Agda} composes paths whose endpoints meet; a path from `x`{.Agda} to `y`{.Agda} followed by one from `y`{.Agda} to `z`{.Agda} gives a path from `x`{.Agda} to `z`{.Agda}.
<!--zh-->
`_∙_`{.Agda} 把首尾相接的路径复合起来；从 `x`{.Agda} 到 `y`{.Agda}，再从 `y`{.Agda} 到 `z`{.Agda}，便得到从 `x`{.Agda} 到 `z`{.Agda} 的路径。
<!--ja-->
`_∙_`{.Agda} は端点の一致するパスを合成する。`x`{.Agda} から `y`{.Agda} へ進み、続いて `y`{.Agda} から `z`{.Agda} へ進めば、`x`{.Agda} から `z`{.Agda} へのパスが得られる。
<!--/-->

</section>
</div>
<figcaption id="fig-path-operations-caption">
<!--en-->
Three basic path operations: reflexivity, reversal and composition.
<!--zh-->
路径的三种基本操作：自反、反转与复合。
<!--ja-->
パスの三つの基本操作：反射、反転、合成。
<!--/-->
</figcaption>
</figure>

<!--en-->
`cong`{.Agda} applies a function to a path. Given a function `f : A → B`{.Agda} and a path `p : x ≡ y`{.Agda} between its inputs, it constructs a path `cong f p : f x ≡ f y`{.Agda} between its outputs. Thus, fixing `f`{.Agda} gives a function from paths to paths:

<div class="single-line-code"><code>`cong f : x ≡ y → f x ≡ f y`{.Agda}</code></div>

Here both outputs lie in the same type `B`{.Agda}. The diagram shows how `f`{.Agda} sends the endpoints `x`{.Agda} and `y`{.Agda} to `f x`{.Agda} and `f y`{.Agda}, while `cong f`{.Agda} sends the path between them to a path between their images. `cong₂`{.Agda} is the corresponding operation for a function of two inputs.
<!--zh-->
`cong`{.Agda} 把函数作用到路径上。给定函数 `f : A → B`{.Agda} 和输入之间的路径 `p : x ≡ y`{.Agda}，它构造输出之间的路径 `cong f p : f x ≡ f y`{.Agda}。因此，固定 `f`{.Agda} 后，得到的是一个把路径送到路径的函数：

<div class="single-line-code"><code>`cong f : x ≡ y → f x ≡ f y`{.Agda}</code></div>

这里的两个输出都属于同一个类型 `B`{.Agda}。图中，`f`{.Agda} 把端点 `x`{.Agda} 和 `y`{.Agda} 送到 `f x`{.Agda} 和 `f y`{.Agda}，而 `cong f`{.Agda} 把端点之间的路径送到像之间的路径。`cong₂`{.Agda} 是函数有两个输入时的相应操作。
<!--ja-->
`cong`{.Agda} は関数をパスに作用させる。関数 `f : A → B`{.Agda} と入力の間のパス `p : x ≡ y`{.Agda} が与えられると、出力の間のパス `cong f p : f x ≡ f y`{.Agda} を構成する。したがって、`f`{.Agda} を固定すると、パスをパスへ送る関数が得られる。

<div class="single-line-code"><code>`cong f : x ≡ y → f x ≡ f y`{.Agda}</code></div>

ここでは二つの出力は同じ型 `B`{.Agda} に属する。図では、`f`{.Agda} が端点 `x`{.Agda} と `y`{.Agda} を `f x`{.Agda} と `f y`{.Agda} に送り、`cong f`{.Agda} が端点の間のパスを像の間のパスに送る。`cong₂`{.Agda} は二つの入力を持つ関数に対する同様の操作である。
<!--/-->

<figure class="book-diagram type-comparison path-figure" id="fig-path-cong" aria-describedby="fig-path-cong-caption">
<div class="diagram-panel path-single">

$$f : A\to B,\qquad p:x\equiv y$$

<div class="path-stage path-cong-stage" style="aspect-ratio:360/240">
<svg viewBox="0 0 360 240" aria-hidden="true" focusable="false">
<path class="diagram-path" d="M55 60 Q180 5 305 60 M55 185 Q180 130 305 185"/>
<path class="diagram-map-line" d="M55 72 V165 M305 72 V165"/>
<path class="diagram-map-tip" d="M51 158 L55 165 L59 158 M301 158 L305 165 L309 158"/><circle class="diagram-point" cx="55" cy="60" r="4"/><circle class="diagram-point" cx="305" cy="60" r="4"/><circle class="diagram-point" cx="55" cy="185" r="4"/><circle class="diagram-point" cx="305" cy="185" r="4"/>
</svg>
<span class="path-label" style="left:15.2778%;top:15.4167%">$x:A$</span>
<span class="path-label" style="left:84.7222%;top:15.4167%">$y:A$</span>
<span class="path-label" style="left:50%;top:6.25%">$p$</span>
<span class="path-label" style="left:10.8333%;top:48.75%">$f$</span>
<span class="path-label" style="left:89.4444%;top:48.75%">$f$</span>
<span class="path-label" style="left:15.2778%;top:90%">$f(x):B$</span>
<span class="path-label" style="left:84.7222%;top:90%">$f(y):B$</span>
<span class="path-label" style="left:50%;top:56.25%">$\operatorname{cong}\,f\,p$</span>
</div>
</div>
<figcaption id="fig-path-cong-caption">
<!--en-->
`cong`{.Agda}: a function sends a path to a path between the images of its endpoints.
<!--zh-->
`cong`{.Agda}：函数把路径送到端点的像之间的路径。
<!--ja-->
`cong`{.Agda}：関数はパスを、その端点の像の間のパスに送る。
<!--/-->
</figcaption>
</figure>

<!--en-->
`transport`{.Agda} turns a path between types into a function between their elements. Given types `A`{.Agda} and `B`{.Agda} in the same universe and a path `p : A ≡ B`{.Agda}, it constructs a function `transport p`{.Agda} from `A`{.Agda} to `B`{.Agda}. Thus, fixing `p`{.Agda} gives a function from elements to elements:

<div class="single-line-code"><code>`transport p : A → B`{.Agda}</code></div>

Here the types themselves are the endpoints of the path. The diagram shows how `transport`{.Agda} turns this path into a function, which sends an element `a : A`{.Agda} to `transport p a : B`{.Agda}. The path `p`{.Agda} supplies the equality of types; `transport p`{.Agda} performs the movement of elements.
<!--zh-->
`transport`{.Agda} 把类型之间的路径转为元素之间的函数。给定同一宇宙中的类型 `A`{.Agda}、`B`{.Agda} 和路径 `p : A ≡ B`{.Agda}，它构造从 `A`{.Agda} 到 `B`{.Agda} 的函数 `transport p`{.Agda}。因此，固定 `p`{.Agda} 后，得到的是一个把元素送到元素的函数：

<div class="single-line-code"><code>`transport p : A → B`{.Agda}</code></div>

这里的路径以类型本身为端点。图中，`transport`{.Agda} 把这条路径转为函数，再由这个函数把元素 `a : A`{.Agda} 送到 `transport p a : B`{.Agda}。路径 `p`{.Agda} 提供类型的相等，而 `transport p`{.Agda} 执行元素的搬移。
<!--ja-->
`transport`{.Agda} は型の間のパスを、それらの要素を移す関数に変える。同じ宇宙に属する型 `A`{.Agda}、`B`{.Agda} とパス `p : A ≡ B`{.Agda} が与えられると、`A`{.Agda} から `B`{.Agda} への関数 `transport p`{.Agda} を構成する。したがって、`p`{.Agda} を固定すると、要素を要素へ送る関数が得られる。

<div class="single-line-code"><code>`transport p : A → B`{.Agda}</code></div>

ここでは型そのものがパスの端点である。図では、`transport`{.Agda} がこのパスを関数に変え、その関数が要素 `a : A`{.Agda} を `transport p a : B`{.Agda} に送る。パス `p`{.Agda} は型の等しさを与え、`transport p`{.Agda} は要素を移す操作を行う。
<!--/-->

<figure class="book-diagram type-comparison structural-figure" id="fig-type-transport" aria-describedby="fig-type-transport-caption">
<div class="diagram-panel type-comparison-panel">

$$p : A\equiv B$$

<div class="transport-scene">
<div class="diagram-space transport-fiber">

$$a : A$$

</div>
<div class="transport-edge">

$$\xmapsto{\;\operatorname{transport}\,p\;}$$

</div>
<div class="diagram-space transport-fiber">

$$b : B$$

</div>
<div class="transport-family" aria-hidden="true"></div>
<div class="transport-construction">

$$\Big\uparrow\mathrlap{\;{\scriptstyle\operatorname{transport}}}$$

</div>
<div class="transport-family" aria-hidden="true"></div>
<div class="diagram-space transport-base">

$$A : \operatorname{Type}_{\ell}$$

</div>
<div class="path-connection">
<svg viewBox="0 0 120 54" aria-hidden="true" focusable="false">
<path class="diagram-path" d="M8 35 H112"/>
<circle class="diagram-point" cx="8" cy="35" r="3.5"/>
<circle class="diagram-point" cx="112" cy="35" r="3.5"/>
</svg>
<span class="path-connection-label">$p$</span>
</div>
<div class="diagram-space transport-base">

$$B : \operatorname{Type}_{\ell}$$

</div>
</div>

$$b := \operatorname{transport}\,p\,a$$

</div>
<figcaption id="fig-type-transport-caption">
<!--en-->
`transport`{.Agda}: a path between types gives a function between their elements.
<!--zh-->
`transport`{.Agda}：类型之间的路径给出搬移元素的函数。
<!--ja-->
`transport`{.Agda}：型の間のパスから、要素を移す関数を得る。
<!--/-->
</figcaption>
</figure>

<!--en-->
`subst`{.Agda} turns a path between inputs of a type family into a function between the corresponding types. Given a type family `B : A → Type ℓ`{.Agda} and a path `p : x ≡ y`{.Agda}, it constructs a function `subst B p`{.Agda} from `B x`{.Agda} to `B y`{.Agda}. Thus, fixing `B`{.Agda} and `p`{.Agda} gives a function from elements to elements:

<div class="single-line-code"><code>`subst B p : B x → B y`{.Agda}</code></div>

Here the path joins the inputs `x`{.Agda} and `y`{.Agda}, while the elements being moved belong to `B x`{.Agda} and `B y`{.Agda}. The diagram shows how `subst B p`{.Agda} sends `u : B x`{.Agda} to `subst B p u : B y`{.Agda}. `subst2`{.Agda} is the corresponding operation for a type family with two inputs: a path in each input moves data to the type at the new pair.
<!--zh-->
`subst`{.Agda} 把类型族输入之间的路径转为相应类型之间的函数。给定类型族 `B : A → Type ℓ`{.Agda} 和路径 `p : x ≡ y`{.Agda}，它构造从 `B x`{.Agda} 到 `B y`{.Agda} 的函数 `subst B p`{.Agda}。因此，固定 `B`{.Agda} 和 `p`{.Agda} 后，得到的是一个把元素送到元素的函数：

<div class="single-line-code"><code>`subst B p : B x → B y`{.Agda}</code></div>

这里的路径连接输入 `x`{.Agda} 和 `y`{.Agda}，而被搬移的元素属于 `B x`{.Agda} 和 `B y`{.Agda}。图中，`subst B p`{.Agda} 把 `u : B x`{.Agda} 送到 `subst B p u : B y`{.Agda}。`subst2`{.Agda} 是类型族有两个输入时的相应操作：分别给出两个输入上的路径，即可把数据搬移到新输入对所对应的类型中。
<!--ja-->
`subst`{.Agda} は型族の入力の間のパスを、対応する型の間の関数に変える。型族 `B : A → Type ℓ`{.Agda} とパス `p : x ≡ y`{.Agda} が与えられると、`B x`{.Agda} から `B y`{.Agda} への関数 `subst B p`{.Agda} を構成する。したがって、`B`{.Agda} と `p`{.Agda} を固定すると、要素を要素へ送る関数が得られる。

<div class="single-line-code"><code>`subst B p : B x → B y`{.Agda}</code></div>

ここではパスが入力 `x`{.Agda} と `y`{.Agda} を結び、移される要素は `B x`{.Agda} と `B y`{.Agda} に属する。図では、`subst B p`{.Agda} が `u : B x`{.Agda} を `subst B p u : B y`{.Agda} に送る。`subst2`{.Agda} は二つの入力を持つ型族に対する同様の操作である。各入力のパスを与えると、新しい入力の組に対応する型へデータを移す。
<!--/-->

<figure class="book-diagram type-comparison structural-figure" id="fig-path-transport" aria-describedby="fig-path-transport-caption">
<div class="diagram-panel type-comparison-panel">

$$B : A \to \operatorname{Type}_{\ell}, \qquad p : x \equiv y$$

<div class="transport-scene">
<div class="diagram-space transport-fiber">

$$u : B(x)$$

</div>
<div class="transport-edge">

$$\xmapsto{\;\operatorname{subst}\,B\,p\;}$$

</div>
<div class="diagram-space transport-fiber">

$$v : B(y)$$

</div>
<div class="transport-family" aria-hidden="true"></div>
<div></div>
<div class="transport-family" aria-hidden="true"></div>
<div class="diagram-space transport-base">

$$x : A$$

</div>
<div class="path-connection">
<svg viewBox="0 0 120 54" aria-hidden="true" focusable="false">
<path class="diagram-path" d="M8 35 H112"/>
<circle class="diagram-point" cx="8" cy="35" r="3.5"/>
<circle class="diagram-point" cx="112" cy="35" r="3.5"/>
</svg>
<span class="path-connection-label">$p$</span>
</div>
<div class="diagram-space transport-base">

$$y : A$$

</div>
</div>

$$v := \operatorname{subst}\,B\,p\,u$$

</div>
<figcaption id="fig-path-transport-caption">
<!--en-->
`subst`{.Agda}: a path between indices gives a function between the corresponding types.
<!--zh-->
`subst`{.Agda}：指标之间的路径给出相应类型之间的函数。
<!--ja-->
`subst`{.Agda}：添字の間のパスから、対応する型の間の関数を得る。
<!--/-->
</figcaption>
</figure>

<!--en-->
These three operations fit together in the following diagram. Each box represents a type, named at the top; the points inside represent its elements. Arrows between boxes are functions between those types. From `x ≡ y`{.Agda} to `B x → B y`{.Agda}, we can apply `subst B`{.Agda} directly, or first apply `cong B`{.Agda} and then `transport`{.Agda}.
<!--zh-->
这三种操作的联系可以画成下图。每个框表示一个类型，框顶标明类型，框内的点表示它的元素。框之间的箭头表示这些类型之间的函数。从 `x ≡ y`{.Agda} 到 `B x → B y`{.Agda}，可以直接应用 `subst B`{.Agda}，也可以先应用 `cong B`{.Agda}，再应用 `transport`{.Agda}。
<!--ja-->
これら三つの操作の関係を次の図で表す。各枠は型を表し、その型を枠の上部に記す。枠内の点はその要素を表し、枠の間の矢印は型の間の関数を表す。`x ≡ y`{.Agda} から `B x → B y`{.Agda} へは、直接 `subst B`{.Agda} を適用することも、まず `cong B`{.Agda}、次に `transport`{.Agda} を適用することもできる。
<!--/-->

<figure class="book-diagram type-comparison path-figure" id="fig-subst-factorization" aria-describedby="fig-subst-factorization-caption">
<div class="diagram-panel path-single">

$$B : A \to \operatorname{Type}_{\ell}, \qquad x,y:A$$

<div class="path-stage subst-factorization" style="aspect-ratio:640/475">
<svg viewBox="0 0 640 475" aria-hidden="true" focusable="false">
<rect class="diagram-space-shape" x="15" y="15" width="235" height="135"/>
<rect class="diagram-space-shape" x="390" y="15" width="235" height="135"/>
<rect class="diagram-space-shape" x="15" y="295" width="610" height="155"/>
<path class="diagram-map-line" d="M262 87 H378 M152 163 L216 281 M488 163 L424 281"/>
<path class="diagram-map-tip" d="M371 83 L378 87 L371 91 M209 277 L216 281 L216 273 M424 273 L424 281 L431 277"/>
<path class="diagram-path" d="M140 390 Q320 350 500 390"/>
<circle class="diagram-point" cx="132.5" cy="93" r="4"/>
<circle class="diagram-point" cx="507.5" cy="93" r="4"/>
<circle class="diagram-point" cx="140" cy="390" r="4"/>
<circle class="diagram-point" cx="500" cy="390" r="4"/>
</svg>
<span class="path-label" style="left:20.7031%;top:9.05263%">$x\equiv y$</span>
<span class="path-label" style="left:79.2969%;top:9.05263%">$B(x)\equiv B(y)$</span>
<span class="path-label" style="left:50%;top:68%">$B(x)\to B(y)$</span>
<span class="path-label" style="left:20.7031%;top:25.0526%">$p$</span>
<span class="path-label" style="left:79.2969%;top:25.0526%">$\operatorname{cong}\,B\,p$</span>
<span class="path-label" style="left:50%;top:12.8421%">$\operatorname{cong}\,B$</span>
<span class="path-label" style="left:20.3125%;top:47.7895%">$\operatorname{subst}\,B$</span>
<span class="path-label" style="left:79.8438%;top:47.7895%">$\operatorname{transport}$</span>
<span class="path-label" style="left:21.875%;top:88.6316%">$\operatorname{subst}\,B\,p$</span>
<span class="path-label" style="left:78.125%;top:88.6316%">$\operatorname{transport}\,(\operatorname{cong}\,B\,p)$</span>
</div>

</div>
<figcaption id="fig-subst-factorization-caption">

<!--en-->
For each input `p`{.Agda}, the two routes give functions of the same type `B x → B y`{.Agda}. The blue line represents a path between these functions. The proof is omitted here.
<!--zh-->
对每个输入 `p`{.Agda}，两条路线所得的函数都属于同一类型 `B x → B y`{.Agda}。蓝线表示这两个函数之间存在路径。此处省略证明。
<!--ja-->
各入力 `p`{.Agda} に対し、二つの経路から得られる関数は同じ型 `B x → B y`{.Agda} に属する。青い線は、これらの関数の間にパスが存在することを表す。ここでは証明を省略する。
<!--/-->

</figcaption>
</figure>

<!--en-->
`funExt`{.Agda} turns pointwise equality into equality of functions: if `f x ≡ g x`{.Agda} for every `x`{.Agda}, then `f ≡ g`{.Agda}.
<!--zh-->
`funExt`{.Agda} 从逐点相等得到函数相等：如果 `f x ≡ g x`{.Agda} 对每个 `x`{.Agda} 都成立，那么 `f ≡ g`{.Agda}。
<!--ja-->
`funExt`{.Agda} は各点での等しさから関数の等しさを与える。すべての `x`{.Agda} について `f x ≡ g x`{.Agda} ならば、`f ≡ g`{.Agda} である。
<!--/-->

<figure class="book-diagram type-comparison path-figure" id="fig-path-funext" aria-describedby="fig-path-funext-caption">
<div class="diagram-panel path-single">

$$f,g : A\to B$$

<div class="funext-scene">
<div class="diagram-space funext-family">

$$h : \prod_{x:A}\bigl(f(x)\equiv g(x)\bigr)$$

<div class="funext-samples">
<span class="funext-value">$f(x_1)$</span>
<div class="path-connection">
<svg viewBox="0 0 120 54" aria-hidden="true" focusable="false">
<path class="diagram-path" d="M8 35 H112"/>
<circle class="diagram-point" cx="8" cy="35" r="3.5"/>
<circle class="diagram-point" cx="112" cy="35" r="3.5"/>
</svg>
<span class="path-connection-label">$h(x_1)$</span>
</div>
<span class="funext-value">$g(x_1)$</span>
<span class="funext-value">$f(x_2)$</span>
<div class="path-connection">
<svg viewBox="0 0 120 54" aria-hidden="true" focusable="false">
<path class="diagram-path" d="M8 35 H112"/>
<circle class="diagram-point" cx="8" cy="35" r="3.5"/>
<circle class="diagram-point" cx="112" cy="35" r="3.5"/>
</svg>
<span class="path-connection-label">$h(x_2)$</span>
</div>
<span class="funext-value">$g(x_2)$</span>
<span class="funext-value">$\vdots$</span>
<div></div>
<span class="funext-value">$\vdots$</span>
</div>
</div>
<div class="funext-map">
<span class="funext-right">$\xmapsto{\operatorname{funExt}}$</span>
<span class="funext-down">$\Big\downarrow\mathrlap{\;{\scriptstyle\operatorname{funExt}}}$</span>
</div>
<div class="diagram-space funext-result">
<div class="path-stage" style="aspect-ratio:240/150">
<svg viewBox="0 0 240 150" aria-hidden="true" focusable="false">
<path class="diagram-path" d="M35 88 Q120 12 205 88"/><circle class="diagram-point" cx="35" cy="88" r="4"/><circle class="diagram-point" cx="205" cy="88" r="4"/>
</svg>
<span class="path-label" style="left:14.5833%;top:74.6667%">$f$</span>
<span class="path-label" style="left:85.4167%;top:74.6667%">$g$</span>
<span class="path-label" style="left:50%;top:20%">$\operatorname{funExt}\,h$</span>
</div>

$$\operatorname{funExt}\,h : f\equiv g$$

</div>
</div>
</div>
<figcaption id="fig-path-funext-caption">
<!--en-->
`funExt`{.Agda}: paths at every input together give a path between functions.
<!--zh-->
`funExt`{.Agda}：每个输入处的路径共同给出函数之间的路径。
<!--ja-->
`funExt`{.Agda}：すべての入力におけるパスから、関数の間のパスを得る。
<!--/-->
</figcaption>
</figure>

<!--en-->
Paths are themselves elements of a type, so two paths can in turn be equal. Equality structure can therefore continue to higher levels: we may ask not only whether two elements are equal, but also whether their equality proofs are equal. The next section introduces a hierarchy that measures how many such levels of equality structure a type retains.

For further details on path types in Cubical Agda, see the [Cubical chapter of the Agda 2.8.0 manual](https://agda.readthedocs.io/en/v2.8.0/language/cubical.html). This section uses only the basic properties needed for the constructions that follow.
<!--zh-->
路径本身也是类型中的元素，所以两条路径之间还可以形成新的相等。相等结构由此可以继续向更高层延伸：不仅可以问两个元素是否相等，还可以问它们的相等证明彼此是否相等。下一节将引入一套层次分类，用来衡量一个类型保留了多少层这样的相等结构。

关于 Cubical Agda 中的路径类型，可以参阅 [Agda 2.8.0 手册中的 Cubical 章节](https://agda.readthedocs.io/en/v2.8.0/language/cubical.html)。本节只使用理解后续构造所需的基本性质。
<!--ja-->
パス自身も型の要素なので、二つのパスがさらに等しいかを考えられる。等しさの構造はこのように高い層へ続く。二つの要素が等しいかだけでなく、その等しさの証明どうしが等しいかも問えるのである。次節では、このような等しさの構造を型が何層まで保つかを測る階層的な分類を導入する。

Cubical Agda のパス型について詳しくは、[Agda 2.8.0 マニュアルの Cubical の章](https://agda.readthedocs.io/en/v2.8.0/language/cubical.html)を参照してほしい。本節では、後の構成を理解するために必要な基本的性質だけを使う。
<!--/-->

```agda
open import Cubical.Foundations.Prelude public
  using ( _≡_; refl; sym; _∙_; cong; cong₂; transport; subst; subst2; funExt )
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

- **`isContr A`{.Agda}: `A`{.Agda} is [contractible]{.term-intro #contractible}.** This requires a chosen centre in `A`{.Agda} and, for every `x : A`{.Agda}, a path from the centre to `x`{.Agda}. Thus `A`{.Agda} must be inhabited, and every element is equal to the chosen centre, so no two elements can be distinguished by equality. This book reads the data carried by `isContr`{.Agda} as **[unique existence]{.term-intro #unique-existence}**: the centre supplies existence, and the paths from the centre to every element supply uniqueness.
- **`isProp A`{.Agda}: `A`{.Agda} is a [proposition]{.term-intro #proposition}.** This requires any two elements of `A`{.Agda} to be equal. It neither chooses a centre nor requires `A`{.Agda} to be inhabited; it says only that if proofs of `A`{.Agda} exist, no distinction remains between them. A proposition may therefore have no proof or have a proof, but it cannot have two distinguishable proofs.
- **`isSet A`{.Agda}: `A`{.Agda} is an [h-set]{.term-intro #h-set}.** The prefix marks a notion of the host: an h-set is a type satisfying `isSet`{.Agda}, not a set of the set theory being modelled. The condition does not require every two elements of `A`{.Agda} to be equal. Instead, it requires the path type between any two elements to be a proposition. Elements of `A`{.Agda} may differ, and paths may connect some of them; but once the same source and target are fixed, any two such paths are equal. Distinctions may remain among elements, while no further distinguishable structure remains among their equality proofs.
<!--zh-->
路径本身也是类型中的元素，所以路径之间还可以形成新的路径。同伦层级按照这些相等证明还能保留多少可区分的结构，对类型进行分类。这里衡量的不是类型的大小；类型的大小由宇宙层级处理，同伦层级关心的是元素及其相等证明如何彼此区分。

- **`isContr A`{.Agda}：`A`{.Agda} 是[可缩]{.term-intro #contractible}的。** 这要求在 `A`{.Agda} 中选定一个中心，并为每个 `x : A`{.Agda} 给出一条从中心到 `x`{.Agda} 的路径。因此，`A`{.Agda} 不仅必须有元素，而且所有元素都与选定的中心相等，彼此之间也就无法通过相等加以区分。本书把 `isContr`{.Agda} 携带的这组数据读作**[唯一存在]{.term-intro #unique-existence}**：中心给出存在性，所有元素都等于中心则给出唯一性。
- **`isProp A`{.Agda}：`A`{.Agda} 是[命题]{.term-intro #proposition}。** 这要求 `A`{.Agda} 中任意两个元素都相等。它不要求预先选定中心，甚至不要求 `A`{.Agda} 一定有元素；它只说明，一旦 `A`{.Agda} 有证明，这些证明之间便没有可区分的差别。因此，一个命题可以没有证明，也可以有证明，但不能有两个彼此不同的证明。
- **`isSet A`{.Agda}：`A`{.Agda} 是 [h-集合]{.term-intro #h-set}。** 前缀标明这是宿主层的概念：h-集合指满足 `isSet`{.Agda} 的类型，而不是所建模的集合论中的集合。这不要求 `A`{.Agda} 中任意两个元素都相等，而是要求任意两个元素之间的路径类型本身为命题。换言之，`A`{.Agda} 的元素可以彼此不同，也可以存在连接某些元素的路径；但给定相同的起点和终点以后，两条这样的路径必定相等。元素层面仍可保留差别，相等证明之间则不再保留可区分的更高结构。
<!--ja-->
パス自身も型の要素なので、パスどうしの間にさらにパスを作れる。ホモトピーレベルは、このような等しさの証明に区別できる構造がどれだけ残るかによって型を分類する。型の大きさを測るものではない。大きさを扱うのは宇宙レベルであり、ホモトピーレベルが扱うのは要素とその等しさの証明をどこまで区別できるかである。

- **`isContr A`{.Agda}：`A`{.Agda} は[可縮]{.term-intro #contractible}である。** これは `A`{.Agda} の中に中心を一つ選び、すべての `x : A`{.Agda} に対して中心から `x`{.Agda} へのパスを与えることを要求する。したがって `A`{.Agda} には要素が存在し、すべての要素が選ばれた中心と等しいので、等しさによって要素を区別できない。本書では `isContr`{.Agda} が持つこのデータを**[一意存在]{.term-intro #unique-existence}**と読む。中心が存在を与え、すべての要素へのパスが一意性を与える。
- **`isProp A`{.Agda}：`A`{.Agda} は[命題]{.term-intro #proposition}である。** これは `A`{.Agda} の任意の二要素が等しいことを要求する。中心を選ぶ必要はなく、`A`{.Agda} に要素が存在することさえ要求しない。`A`{.Agda} の証明が存在するなら、それらの間に区別が残らないことだけを述べる。したがって命題には証明がないことも、証明があることもあるが、互いに区別できる二つの証明はあり得ない。
- **`isSet A`{.Agda}：`A`{.Agda} は [h-集合]{.term-intro #h-set}である。** 接頭辞はホストレベルの概念であることを示す。h-集合とは `isSet`{.Agda} を満たす型であり、モデル化される集合論の集合ではない。これは `A`{.Agda} の任意の二要素が等しいことを要求するのではなく、任意の二要素の間のパス型が命題であることを要求する。`A`{.Agda} の要素は互いに異なっていてよく、その一部を結ぶパスが存在してもかまわない。しかし始点と終点を同じものに固定すれば、その間の任意の二つのパスは等しくなる。要素の間には区別が残り得るが、等しさの証明の間には、それ以上区別できる構造が残らない。
<!--/-->

<figure class="book-diagram type-comparison hlevel-comparison" id="fig-hlevel-distinction" aria-describedby="fig-hlevel-distinction-caption">
<div class="hlevel-panels">
<section class="diagram-panel hlevel-panel">

$$\operatorname{isContr}(A)$$

<div class="hlevel-assumptions">

$$c,x,y : A$$

</div>
<div class="hlevel-stage">
<svg viewBox="0 0 240 150" aria-hidden="true" focusable="false">
<path class="diagram-path" d="M55 75 L180 35 M55 75 L180 115"/>
<circle class="diagram-centre-ring" cx="55" cy="75" r="11"/>
<circle class="diagram-point" cx="55" cy="75" r="4"/>
<circle class="diagram-point" cx="180" cy="35" r="4"/>
<circle class="diagram-point" cx="180" cy="115" r="4"/>
</svg>
<span class="hlevel-label" style="left:22.9167%;top:66.6667%">$c$</span>
<span class="hlevel-label" style="left:75%;top:10%">$x$</span>
<span class="hlevel-label" style="left:75%;top:91.3333%">$y$</span>
<span class="hlevel-label" style="left:47.5%;top:26%">$h(x)$</span>
<span class="hlevel-label" style="left:47.5%;top:75.3333%">$h(y)$</span>
</div>
<div class="hlevel-definition">

$$c : A,\quad h : \prod_{x:A}(c\equiv x)$$

</div>
<!--en-->
<p class="hlevel-note">A type with a chosen centre to which every element is joined by a path.</p>
<!--zh-->
<p class="hlevel-note">带有选定中心、且每个元素都有路径与中心相连的类型。</p>
<!--ja-->
<p class="hlevel-note">選ばれた中心を持ち、すべての元が中心とパスで結ばれる型。</p>
<!--/-->
</section>
<div class="hlevel-link">
<span class="hlevel-link-right">$\Longrightarrow$</span>
<span class="hlevel-link-down">$\Downarrow$</span>
</div>
<section class="diagram-panel hlevel-panel">

$$\operatorname{isProp}(A)$$

<div class="hlevel-assumptions">

$$x,y : A$$

</div>
<div class="hlevel-stage">
<svg viewBox="0 0 240 150" aria-hidden="true" focusable="false">
<path class="diagram-path" d="M40 85 Q120 10 200 85"/>
<circle class="diagram-point" cx="40" cy="85" r="4"/>
<circle class="diagram-point" cx="200" cy="85" r="4"/>
</svg>
<span class="hlevel-label" style="left:16.6667%;top:73.3333%">$x$</span>
<span class="hlevel-label" style="left:83.3333%;top:73.3333%">$y$</span>
<span class="hlevel-label" style="left:50%;top:19.3333%">$h(x,y)$</span>
</div>
<div class="hlevel-definition">

$$h : \prod_{x,y:A}(x\equiv y)$$

</div>
<!--en-->
<p class="hlevel-note">A proposition may therefore have no proof or have a proof, but it cannot have two distinguishable proofs.</p>
<!--zh-->
<p class="hlevel-note">因此，一个命题可以没有证明，也可以有证明，但不能有两个彼此不同的证明。</p>
<!--ja-->
<p class="hlevel-note">したがって命題には証明がないことも、証明があることもあるが、互いに区別できる二つの証明はあり得ない。</p>
<!--/-->
</section>
<div class="hlevel-link">
<span class="hlevel-link-right">$\Longrightarrow$</span>
<span class="hlevel-link-down">$\Downarrow$</span>
</div>
<section class="diagram-panel hlevel-panel">

$$\operatorname{isSet}(A)$$

<div class="hlevel-assumptions">

$$x,y : A,\quad p,q : x\equiv y$$

</div>
<div class="hlevel-stage">
<svg viewBox="0 0 240 150" aria-hidden="true" focusable="false">
<path class="diagram-higher-path" d="M35 75 Q120 0 205 75 Q120 150 35 75 Z"/>
<path class="diagram-path" d="M35 75 Q120 0 205 75 M35 75 Q120 150 205 75"/>
<circle class="diagram-point" cx="35" cy="75" r="4"/>
<circle class="diagram-point" cx="205" cy="75" r="4"/>
</svg>
<span class="hlevel-label" style="left:6.66667%;top:50%">$x$</span>
<span class="hlevel-label" style="left:93.3333%;top:50%">$y$</span>
<span class="hlevel-label" style="left:50%;top:15.3333%">$p$</span>
<span class="hlevel-label" style="left:50%;top:85.3333%">$q$</span>
<span class="hlevel-label" style="left:50%;top:50%">$p\equiv q$</span>
</div>
<div class="hlevel-definition">

$$h : \prod_{x,y:A}\operatorname{isProp}(x\equiv y)$$

</div>
<!--en-->
<p class="hlevel-note">A type whose equality types are propositions: elements may differ, but any two proofs that they are equal agree.</p>
<!--zh-->
<p class="hlevel-note">相等类型都是命题的类型：元素之间可以有差别，但同一对元素的任意两个相等证明彼此相等。</p>
<!--ja-->
<p class="hlevel-note">等しさの型がすべて命題である型。元は互いに異なりうるが、同じ二元が等しいことの証明は互いに一致する。</p>
<!--/-->
</section>
</div>
<figcaption id="fig-hlevel-distinction-caption">
<!--en-->
A chosen centre, equality of elements, equality of paths: these conditions become successively weaker.
<!--zh-->
选定中心、元素相等、路径相等：这三个条件依次减弱。
<!--ja-->
中心の選択、要素の等しさ、パスの等しさ：これらの条件は順に弱くなる。
<!--/-->
</figcaption>
</figure>

<!--en-->
**`isProp→isSet`{.Agda}: every proposition is an h-set.** If `A`{.Agda} satisfies `isProp`{.Agda}, then it also satisfies `isSet`{.Agda}. This is an upward movement in homotopy level: it leaves `A`{.Agda} unchanged and derives the weaker condition that any two equality paths are equal from the stronger condition that any two elements are equal. It resembles the universe-level movement performed by `Lift`{.Agda}, since both let the same mathematical object meet a requirement at a higher level. They act on different axes, however.
<!--zh-->
**`isProp→isSet`{.Agda}：命题都是 h-集合。** 如果 `A`{.Agda} 满足 `isProp`{.Agda}，那么它也满足 `isSet`{.Agda}。这可以看成一次同伦层级的向上搬移：我们不改变 `A`{.Agda}，而是从较强的条件「任意两个元素相等」推出较弱的条件「任意两条相等路径彼此相等」。它与 `Lift`{.Agda} 所做的宇宙层级搬移有一点相似：二者都使同一个数学对象满足较高层级的要求。不过，两者作用于不同的层级轴。
<!--ja-->
**`isProp→isSet`{.Agda}：すべての命題は h-集合である。** `A`{.Agda} が `isProp`{.Agda} を満たせば、`isSet`{.Agda} も満たす。これはホモトピーレベルを上向きに移す操作と見なせる。`A`{.Agda} を変えず、「任意の二要素が等しい」という強い条件から「任意の二つの等しさのパスが等しい」という弱い条件を導く。この点は `Lift`{.Agda} による宇宙レベルの移動と似ている。どちらも同じ数学的対象を、より高いレベルの要件のもとで扱えるようにするからである。ただし、作用する軸は異なる。
<!--/-->

```agda
open import Cubical.Foundations.Prelude public
  using ( isProp; isSet; isContr; isProp→isSet )
```

<figure class="book-diagram type-comparison structural-figure" id="fig-universe-homotopy" aria-describedby="fig-universe-homotopy-caption">
<div class="diagram-panel type-comparison-panel level-scene">
<!--en-->
<p class="type-comparison-title"><strong>Universe levels</strong></p>
<!--zh-->
<p class="type-comparison-title"><strong>宇宙层级</strong></p>
<!--ja-->
<p class="type-comparison-title"><strong>宇宙レベル</strong></p>
<!--/-->
<div class="diagram-space level-copy">

$$\operatorname{Lift}\,\ell_2\,A : \operatorname{Type}_{\ell\text{-max}(\ell_1,\ell_2)}$$

</div>
<div class="level-lift">

$$\Big\uparrow\mathrlap{\;{\scriptstyle\operatorname{Lift}\,\ell_2}}$$

</div>
<div class="diagram-space level-fixed">

$$A : \operatorname{Type}_{\ell_1}$$

<!--en-->
<p class="type-comparison-title"><strong>Homotopy levels</strong></p>
<!--zh-->
<p class="type-comparison-title"><strong>同伦层级</strong></p>
<!--ja-->
<p class="type-comparison-title"><strong>ホモトピーレベル</strong></p>
<!--/-->
<div class="level-properties">
<div class="level-property">

$$\operatorname{isContr}(A)$$

</div>
<div class="level-implication">

$$\Longrightarrow$$

</div>
<div class="level-property">

$$\operatorname{isProp}(A)$$

</div>
<div class="level-implication">

$$\Longrightarrow$$

</div>
<div class="level-property">

$$\operatorname{isSet}(A)$$

</div>
</div>
</div>
</div>
<figcaption id="fig-universe-homotopy-caption">
<!--en-->
`Lift`{.Agda} changes the universe in which a type is presented and produces a record copy carrying the same data; `isProp→isSet`{.Agda} changes neither the type nor its universe, but derives one equality property from another.
<!--zh-->
`Lift`{.Agda} 改变类型所在的宇宙，并产生一个携带同样数据的记录副本；`isProp→isSet`{.Agda} 不改变类型，也不改变它所在的宇宙，只是从已有的相等性质推出另一个相等性质。
<!--ja-->
`Lift`{.Agda} は型を提示する宇宙を変え、同じデータをもつレコードのコピーを作る。`isProp→isSet`{.Agda} は型もその宇宙も変えず、一つの等しさの性質から別の性質を導くだけである。
<!--/-->
</figcaption>
</figure>

<!--en-->
The two axes in the figure are independent: lifting a type to another universe preserves its homotopy level. The function `isOfHLevelLift`{.Agda} transfers the corresponding certificate to `Lift A`{.Agda}. Its first argument specifies the homotopy level: `0`{.Agda} for contractibility, `1`{.Agda} for propositionhood and `2`{.Agda} for being an h-set. Thus, given `h : isProp A`{.Agda}, the term `isOfHLevelLift 1 h`{.Agda} proves `isProp (Lift A)`{.Agda}; given `h : isSet A`{.Agda}, the term `isOfHLevelLift 2 h`{.Agda} proves `isSet (Lift A)`{.Agda}. This number specifies an equality property, not the target universe of `Lift`{.Agda}.
<!--zh-->
图中的两条轴彼此独立：将类型抬升到另一个宇宙，会保留它的同伦层级。函数 `isOfHLevelLift`{.Agda} 把相应的证书转给 `Lift A`{.Agda}。它的第一个参数指定同伦层级：`0`{.Agda} 表示可缩，`1`{.Agda} 表示命题性，`2`{.Agda} 表示 h-集合性。因此，给定 `h : isProp A`{.Agda}，`isOfHLevelLift 1 h`{.Agda} 就证明 `isProp (Lift A)`{.Agda}；给定 `h : isSet A`{.Agda}，`isOfHLevelLift 2 h`{.Agda} 就证明 `isSet (Lift A)`{.Agda}。这个数字指定的是相等的性质，而非 `Lift`{.Agda} 的目标宇宙。
<!--ja-->
図の二つの軸は独立している。型を別の宇宙へ持ち上げても、そのホモトピーレベルは保たれる。関数 `isOfHLevelLift`{.Agda} は対応する証明を `Lift A`{.Agda} へ移す。最初の引数はホモトピーレベルを指定し、`0`{.Agda} は可縮性、`1`{.Agda} は命題性、`2`{.Agda} は h-集合性を表す。したがって `h : isProp A`{.Agda} があれば `isOfHLevelLift 1 h`{.Agda} は `isProp (Lift A)`{.Agda} を証明し、`h : isSet A`{.Agda} があれば `isOfHLevelLift 2 h`{.Agda} は `isSet (Lift A)`{.Agda} を証明する。この数が指定するのは等しさの性質であり、`Lift`{.Agda} の移動先の宇宙ではない。
<!--/-->

```agda
open import Cubical.Foundations.HLevels public using ( isOfHLevelLift )
```

<!--en-->
## [Type equivalence]{.term-intro #type-equivalence}

Paths compare elements of a common type. To compare types themselves, possibly in different universes, we use `A ≃ B`{.Agda}. This says that a map preserves the information in their elements and paths. The condition is stronger than having functions in both directions: those functions must recover what they started with, in the sense made precise below.

For types `A`{.Agda} and `B`{.Agda}, `A ≃ B`{.Agda} is a [dependent pair]{.term-ref #dependent-pair}. Its [first component]{.term-ref #first-component} is a map `f : A → B`{.Agda}; its [second component]{.term-ref #second-component} is a [certificate]{.term-ref #certificate} depending on `f`{.Agda}. To read this certificate, we first need the following definition.
<!--zh-->
## [类型等价]{.term-intro #type-equivalence}

路径比较同一个类型中的元素。若要比较类型本身，而且允许它们位于不同的宇宙，我们使用 `A ≃ B`{.Agda}，表示一个映射保留了两边元素及路径中的信息。仅仅存在两个方向的函数还不够；来回映射还必须能够恢复出发时的信息，下面将给出精确定义。

对类型 `A`{.Agda} 与 `B`{.Agda}，`A ≃ B`{.Agda} 是一个[依值对]{.term-ref #dependent-pair}。它的[第一分量]{.term-ref #first-component}是映射 `f : A → B`{.Agda}；[第二分量]{.term-ref #second-component}是依赖于 `f`{.Agda} 的[证书]{.term-ref #certificate}。要读懂这份证书，先看下面的定义。
<!--ja-->
## [型同値]{.term-intro #type-equivalence}

パスは共通の型の要素を比較する。型そのものを、異なる宇宙に属する場合も含めて比較するには、`A ≃ B`{.Agda} を使う。これは、写像が両側の要素とパスの情報を保つことを表す。両方向の関数が存在するだけでは足りず、往復によって出発時の情報を復元できなければならない。その条件を以下で正確に述べる。

型 `A`{.Agda} と `B`{.Agda} について、`A ≃ B`{.Agda} は[依存対]{.term-ref #dependent-pair}である。その[第一成分]{.term-ref #first-component}は写像 `f : A → B`{.Agda}、[第二成分]{.term-ref #second-component}は `f`{.Agda} に依存する[証明書]{.term-ref #certificate}である。この証明書を読むために、まず次の定義を見る。
<!--/-->

<!--en-->
For a fixed `b : B`{.Agda}, the **[fibre]{.term-intro #fiber}** of `f`{.Agda} over `b`{.Agda} is the dependent pair type:

<div class="single-line-code"><code>`Σ (a : A) (f a ≡ b)`{.Agda}</code></div>

An element of the fibre has two components. The first is a candidate preimage `a : A`{.Agda}; the second is a path `f a ≡ b`{.Agda} witnessing that this candidate really maps to `b`{.Agda}. An empty fibre means that `b`{.Agda} has no preimage. Elements of a fibre that cannot be identified by a path represent substantively different ways to return from `b`{.Agda} to `A`{.Agda}.

<!--zh-->
对固定的 `b : B`{.Agda}，`f`{.Agda} 在 `b`{.Agda} 上的**[纤维]{.term-intro #fiber}**是下面这个依值对类型：

<div class="single-line-code"><code>`Σ (a : A) (f a ≡ b)`{.Agda}</code></div>

纤维的一个元素由两部分组成：第一分量是一个候选原像 `a : A`{.Agda}，第二分量是一条路径 `f a ≡ b`{.Agda}，证明这个 `a`{.Agda} 的确映到 `b`{.Agda}。纤维为空，表示 `b`{.Agda} 没有原像；纤维中若有彼此不能通过路径等同的元素，则表示从 `b`{.Agda} 返回 `A`{.Agda} 时存在实质不同的选择。

<!--ja-->
固定した `b : B`{.Agda} 上の `f`{.Agda} の**[ファイバー]{.term-intro #fiber}**は、次の依存対型である。

<div class="single-line-code"><code>`Σ (a : A) (f a ≡ b)`{.Agda}</code></div>

ファイバーの要素は二つの成分を持つ。第一成分は原像の候補 `a : A`{.Agda}、第二成分はその候補が実際に `b`{.Agda} へ写ることを示すパス `f a ≡ b`{.Agda} である。ファイバーが空なら `b`{.Agda} に原像はない。ファイバーにパスで同一視できない要素があれば、`b`{.Agda} から `A`{.Agda} へ戻る方法に本質的な違いが残っている。

<!--/-->

```agda
open import Cubical.Foundations.Equiv public using ( _≃_ )
```

<!--en-->
The animation assumes that every fibre is contractible: there is a centre and a family of paths connecting each dependent pair in the fibre to that centre.
<!--zh-->
下面的动画假设每束纤维可缩：存在一个中心，以及一族将纤维中每个依值对连接到中心的路径。
<!--ja-->
以下のアニメーションでは各ファイバーの可縮性を仮定する。すなわち、中心と、ファイバーの各依存対をその中心へ結ぶパスの族が存在する。
<!--/-->

<figure class="book-diagram path-figure fiber-general" id="fig-fiber-general" aria-describedby="fig-fiber-general-caption">
<div class="diagram-framed">

$$F_b=\sum_{a:A}\bigl(f(a)\equiv b\bigr)$$

<div class="path-stage fiber-fan-stage" style="aspect-ratio:680/460">
<svg viewBox="0 0 680 460" aria-hidden="true" focusable="false">
<rect class="diagram-space-shape" x="10" y="20" width="660" height="115"/>
<rect class="diagram-space-shape" x="10" y="185" width="660" height="250"/>
<g class="fiber-bundle" data-fiber="0" data-center-path="M120 390 C80 352 80 289 120 235">
<path class="diagram-map-line fiber-moving-map" d="M48 102 L48 225"/>
<path class="diagram-map-tip fiber-moving-tip" d="M44 218 L48 225 L52 218"/>
<path class="diagram-map-line fiber-moving-map" d="M96 102 L96 225"/>
<path class="diagram-map-tip fiber-moving-tip" d="M92 218 L96 225 L100 218"/>
<path class="diagram-map-line fiber-moving-map" d="M144 102 L144 225"/>
<path class="diagram-map-tip fiber-moving-tip" d="M140 218 L144 225 L148 218"/>
<path class="diagram-map-line fiber-moving-map" d="M192 102 L192 225"/>
<path class="diagram-map-tip fiber-moving-tip" d="M188 218 L192 225 L196 218"/>
<path class="diagram-path fiber-hair" d="M120 390 C33 358 33 292 48 235"/>
<path class="diagram-path fiber-hair" d="M120 390 C63 358 63 292 48 235"/>
<path class="diagram-path fiber-hair" d="M120 390 C81 358 81 292 96 235"/>
<path class="diagram-path fiber-hair" d="M120 390 C111 358 111 292 96 235"/>
<path class="diagram-path fiber-hair" d="M120 390 C129 358 129 292 144 235"/>
<path class="diagram-path fiber-hair" d="M120 390 C159 358 159 292 144 235"/>
<path class="diagram-path fiber-hair" d="M120 390 C177 358 177 292 192 235"/>
<path class="diagram-path fiber-hair" d="M120 390 C207 358 207 292 192 235"/>
<circle class="diagram-point fiber-domain-point" cx="48" cy="98" r="4"/>
<circle class="diagram-point fiber-image-point" cx="48" cy="235" r="4"/>
<circle class="diagram-point fiber-domain-point" cx="96" cy="98" r="4"/>
<circle class="diagram-point fiber-image-point" cx="96" cy="235" r="4"/>
<circle class="diagram-point fiber-domain-point" cx="144" cy="98" r="4"/>
<circle class="diagram-point fiber-image-point" cx="144" cy="235" r="4"/>
<circle class="diagram-point fiber-domain-point" cx="192" cy="98" r="4"/>
<circle class="diagram-point fiber-image-point" cx="192" cy="235" r="4"/>
<circle class="diagram-point fiber-base-point" cx="120" cy="390" r="5"/>
</g>
<g class="fiber-bundle" data-fiber="1" data-center-path="M340 390 C300 352 300 289 340 235">
<path class="diagram-map-line fiber-moving-map" d="M268 102 L268 225"/>
<path class="diagram-map-tip fiber-moving-tip" d="M264 218 L268 225 L272 218"/>
<path class="diagram-map-line fiber-moving-map" d="M316 102 L316 225"/>
<path class="diagram-map-tip fiber-moving-tip" d="M312 218 L316 225 L320 218"/>
<path class="diagram-map-line fiber-moving-map" d="M364 102 L364 225"/>
<path class="diagram-map-tip fiber-moving-tip" d="M360 218 L364 225 L368 218"/>
<path class="diagram-map-line fiber-moving-map" d="M412 102 L412 225"/>
<path class="diagram-map-tip fiber-moving-tip" d="M408 218 L412 225 L416 218"/>
<path class="diagram-path fiber-hair" d="M340 390 C253 358 253 292 268 235"/>
<path class="diagram-path fiber-hair" d="M340 390 C283 358 283 292 268 235"/>
<path class="diagram-path fiber-hair" d="M340 390 C301 358 301 292 316 235"/>
<path class="diagram-path fiber-hair" d="M340 390 C331 358 331 292 316 235"/>
<path class="diagram-path fiber-hair" d="M340 390 C349 358 349 292 364 235"/>
<path class="diagram-path fiber-hair" d="M340 390 C379 358 379 292 364 235"/>
<path class="diagram-path fiber-hair" d="M340 390 C397 358 397 292 412 235"/>
<path class="diagram-path fiber-hair" d="M340 390 C427 358 427 292 412 235"/>
<circle class="diagram-point fiber-domain-point" cx="268" cy="98" r="4"/>
<circle class="diagram-point fiber-image-point" cx="268" cy="235" r="4"/>
<circle class="diagram-point fiber-domain-point" cx="316" cy="98" r="4"/>
<circle class="diagram-point fiber-image-point" cx="316" cy="235" r="4"/>
<circle class="diagram-point fiber-domain-point" cx="364" cy="98" r="4"/>
<circle class="diagram-point fiber-image-point" cx="364" cy="235" r="4"/>
<circle class="diagram-point fiber-domain-point" cx="412" cy="98" r="4"/>
<circle class="diagram-point fiber-image-point" cx="412" cy="235" r="4"/>
<circle class="diagram-point fiber-base-point" cx="340" cy="390" r="5"/>
</g>
<g class="fiber-bundle" data-fiber="2" data-center-path="M560 390 C520 352 520 289 560 235">
<path class="diagram-map-line fiber-moving-map" d="M488 102 L488 225"/>
<path class="diagram-map-tip fiber-moving-tip" d="M484 218 L488 225 L492 218"/>
<path class="diagram-map-line fiber-moving-map" d="M536 102 L536 225"/>
<path class="diagram-map-tip fiber-moving-tip" d="M532 218 L536 225 L540 218"/>
<path class="diagram-map-line fiber-moving-map" d="M584 102 L584 225"/>
<path class="diagram-map-tip fiber-moving-tip" d="M580 218 L584 225 L588 218"/>
<path class="diagram-map-line fiber-moving-map" d="M632 102 L632 225"/>
<path class="diagram-map-tip fiber-moving-tip" d="M628 218 L632 225 L636 218"/>
<path class="diagram-path fiber-hair" d="M560 390 C473 358 473 292 488 235"/>
<path class="diagram-path fiber-hair" d="M560 390 C503 358 503 292 488 235"/>
<path class="diagram-path fiber-hair" d="M560 390 C521 358 521 292 536 235"/>
<path class="diagram-path fiber-hair" d="M560 390 C551 358 551 292 536 235"/>
<path class="diagram-path fiber-hair" d="M560 390 C569 358 569 292 584 235"/>
<path class="diagram-path fiber-hair" d="M560 390 C599 358 599 292 584 235"/>
<path class="diagram-path fiber-hair" d="M560 390 C617 358 617 292 632 235"/>
<path class="diagram-path fiber-hair" d="M560 390 C647 358 647 292 632 235"/>
<circle class="diagram-point fiber-domain-point" cx="488" cy="98" r="4"/>
<circle class="diagram-point fiber-image-point" cx="488" cy="235" r="4"/>
<circle class="diagram-point fiber-domain-point" cx="536" cy="98" r="4"/>
<circle class="diagram-point fiber-image-point" cx="536" cy="235" r="4"/>
<circle class="diagram-point fiber-domain-point" cx="584" cy="98" r="4"/>
<circle class="diagram-point fiber-image-point" cx="584" cy="235" r="4"/>
<circle class="diagram-point fiber-domain-point" cx="632" cy="98" r="4"/>
<circle class="diagram-point fiber-image-point" cx="632" cy="235" r="4"/>
<circle class="diagram-point fiber-base-point" cx="560" cy="390" r="5"/>
</g>
</svg>
<span class="path-label" style="left:7.5000%;top:8.0435%">$A$</span>
<span class="path-label" style="left:7.5000%;top:89.5652%">$B$</span>
<span class="path-label" style="left:53.9706%;top:32.3913%">$f$</span>
<span class="path-label fiber-sample-label" data-fiber="0" style="left:7.0588%;top:16.3043%">$a_{00}$</span>
<span class="path-label fiber-sample-label" data-fiber="0" style="left:14.1176%;top:16.3043%">$a_{01}$</span>
<span class="path-label fiber-sample-label" data-fiber="0" style="left:21.1765%;top:16.3043%">$a_{02}$</span>
<span class="path-label fiber-sample-label" data-fiber="0" style="left:28.2353%;top:16.3043%">$a_{03}$</span>
<span class="path-label fiber-center-label" aria-hidden="true" style="left:17.6471%;top:16.3043%">$a_0$</span>
<span class="path-label" style="left:17.6471%;top:90.2174%">$b_0$</span>
<span class="path-label fiber-sample-label" data-fiber="1" style="left:39.4118%;top:16.3043%">$a_{10}$</span>
<span class="path-label fiber-sample-label" data-fiber="1" style="left:46.4706%;top:16.3043%">$a_{11}$</span>
<span class="path-label fiber-sample-label" data-fiber="1" style="left:53.5294%;top:16.3043%">$a_{12}$</span>
<span class="path-label fiber-sample-label" data-fiber="1" style="left:60.5882%;top:16.3043%">$a_{13}$</span>
<span class="path-label fiber-center-label" aria-hidden="true" style="left:50.0000%;top:16.3043%">$a_1$</span>
<span class="path-label" style="left:50.0000%;top:90.2174%">$b_1$</span>
<span class="path-label fiber-sample-label" data-fiber="2" style="left:71.7647%;top:16.3043%">$a_{20}$</span>
<span class="path-label fiber-sample-label" data-fiber="2" style="left:78.8235%;top:16.3043%">$a_{21}$</span>
<span class="path-label fiber-sample-label" data-fiber="2" style="left:85.8824%;top:16.3043%">$a_{22}$</span>
<span class="path-label fiber-sample-label" data-fiber="2" style="left:92.9412%;top:16.3043%">$a_{23}$</span>
<span class="path-label fiber-center-label" aria-hidden="true" style="left:82.3529%;top:16.3043%">$a_2$</span>
<span class="path-label" style="left:82.3529%;top:90.2174%">$b_2$</span>
</div>
</div>
<figcaption id="fig-fiber-general-caption">
<!--en-->
Click the pulsing fibres to contract; click again to expand. The paths in each tuft merge into a single path $p_i$ from $f(a_i)$ to $b_i$, while the candidate preimages merge into $a_i$. The coincidence depicts equality by paths. The condition for $f$ to be an equivalence is that every fibre is contractible.
<!--zh-->
点击闪烁的三束纤维收拢，再次点击展开。每束路径合并为连接 $f(a_i)$ 与 $b_i$ 的一条路径 $p_i$，原像候选则合并为 $a_i$。这里的重合表示路径意义下的相等。每束纤维可缩，正是 $f$ 成为等价的条件。
<!--ja-->
点滅するファイバーをクリックすると収縮し、もう一度クリックすると広がる。各毛束のパスは $f(a_i)$ と $b_i$ を結ぶ一本のパス $p_i$ に合流し、原像の候補は $a_i$ に合流する。重なりはパスによる等しさを表す。各ファイバーが可縮であることが、$f$ が同値となる条件である。
<!--/-->
</figcaption>
</figure>

<!--en-->
This notion should be distinguished from an [isomorphism]{.term-intro #type-isomorphism}, which explicitly presents maps `f : A → B`{.Agda} and `g : B → A`{.Agda} and the two [round-trip laws]{.term-intro #round-trip-law}: paths `g (f a) ≡ a`{.Agda} for every `a : A`{.Agda} and `f (g b) ≡ b`{.Agda} for every `b : B`{.Agda}. The constructor uses the order `iso f g s r`{.Agda}, where `s : (b : B) → f (g b) ≡ b`{.Agda} and `r : (a : A) → g (f a) ≡ a`{.Agda}. The two notions are related as follows: `iso`{.Agda} packages those data as `Iso A B`{.Agda}, and `isoToEquiv`{.Agda} converts the result into `A ≃ B`{.Agda}. Explicit maps make isomorphisms convenient for constructing examples, while the cubical library uses equivalences as the common interface for transporting type structure.
<!--zh-->
这里的[类型等价]{.term-ref #type-equivalence}需要与[同构]{.term-intro #type-isomorphism}区分：同构显式给出映射 `f : A → B`{.Agda}、`g : B → A`{.Agda} 和两条[往返律]{.term-intro #round-trip-law}：对每个 `a : A`{.Agda} 有路径 `g (f a) ≡ a`{.Agda}，对每个 `b : B`{.Agda} 有路径 `f (g b) ≡ b`{.Agda}。构造子的参数顺序是 `iso f g s r`{.Agda}，其中 `s : (b : B) → f (g b) ≡ b`{.Agda}，`r : (a : A) → g (f a) ≡ a`{.Agda}。二者的联系在于：`iso`{.Agda} 把这些数据打包成 `Iso A B`{.Agda}，`isoToEquiv`{.Agda} 再把所得同构转换为 `A ≃ B`{.Agda}。显式列出映射使同构便于构造具体例子，立方库则以[类型等价]{.term-ref #type-equivalence}作为搬运类型结构的统一接口。
<!--ja-->
この[型同値]{.term-ref #type-equivalence}は[同型]{.term-intro #type-isomorphism}と区別する必要がある。同型は写像 `f : A → B`{.Agda}、`g : B → A`{.Agda} と二つの[往復則]{.term-intro #round-trip-law}を明示的に与える。すなわち、各 `a : A`{.Agda} に対するパス `g (f a) ≡ a`{.Agda} と、各 `b : B`{.Agda} に対するパス `f (g b) ≡ b`{.Agda} である。構成子の引数は `iso f g s r`{.Agda} の順であり、`s : (b : B) → f (g b) ≡ b`{.Agda}、`r : (a : A) → g (f a) ≡ a`{.Agda} である。両者の関係は次のとおりである。`iso`{.Agda} はこれらのデータを `Iso A B`{.Agda} にまとめ、`isoToEquiv`{.Agda} は得られた同型を `A ≃ B`{.Agda} へ変換する。写像を明示する同型は具体例の構成に便利であり、Cubical ライブラリは型の構造を運ぶ共通のインターフェースとして型同値を用いる。
<!--/-->

```agda
open import Cubical.Foundations.Isomorphism public using ( Iso; iso; isoToEquiv )
```

<!--en-->
Given `e : A ≃ B`{.Agda}, we can use the equivalence in either direction. The function `equivFun e : A → B`{.Agda} is its first component; `invEq e : B → A`{.Agda} recovers a preimage using the contractibility certificate. The two composites return their inputs up to paths. In particular, when `A`{.Agda} and `B`{.Agda} are propositions, these functions convert a proof on either side into a proof on the other.
<!--zh-->
给定 `e : A ≃ B`{.Agda}，便可沿两个方向使用这份等价。函数 `equivFun e : A → B`{.Agda} 就是它的第一分量；`invEq e : B → A`{.Agda} 则借助可缩性证书恢复原像。两个方向来回复合，都会在路径意义下返回输入。特别地，当 `A`{.Agda} 与 `B`{.Agda} 都是命题时，这两个函数把任意一边的证明转换为另一边的证明。
<!--ja-->
`e : A ≃ B`{.Agda} があれば、この同値を両方向に使える。関数 `equivFun e : A → B`{.Agda} はその第一成分であり、`invEq e : B → A`{.Agda} は可縮性の証明を用いて原像を復元する。両方向の合成は、パスの意味で入力に戻る。特に `A`{.Agda} と `B`{.Agda} が命題なら、これらの関数は一方の証明を他方の証明へ変換する。
<!--/-->

```agda
open import Cubical.Foundations.Equiv public using ( equivFun; invEq )
```

<!--en-->
An equivalence also preserves the paths between its elements. Write `f = equivFun e`{.Agda}. For `x y : A`{.Agda}, `congEquiv e`{.Agda} gives the equivalence

<div class="single-line-code"><code>`(x ≡ y) ≃ (f x ≡ f y)`{.Agda}</code></div>

Its forward map is `cong f`{.Agda}: it applies the function to a path. Its inverse, `invEq (congEquiv e)`{.Agda}, recovers a path between the original elements from a path between their images. Thus an equivalence lets us both send paths forward and recover them; `cong`{.Agda} for an arbitrary function only supplies the forward operation.
<!--zh-->
类型等价也保留元素之间的路径。记 `f = equivFun e`{.Agda}。对于 `x y : A`{.Agda}，`congEquiv e`{.Agda} 给出类型等价

<div class="single-line-code"><code>`(x ≡ y) ≃ (f x ≡ f y)`{.Agda}</code></div>

它的正向映射是 `cong f`{.Agda}，即把函数作用于路径；逆向映射 `invEq (congEquiv e)`{.Agda} 则从像之间的路径恢复原来元素之间的路径。因此，类型等价既能把路径送过去，也能将其恢复；一般函数的 `cong`{.Agda} 只提供正向操作。
<!--ja-->
型同値は要素間のパスも保つ。`f = equivFun e`{.Agda} と書くと、`x y : A`{.Agda} に対して `congEquiv e`{.Agda} は次の型同値を与える。

<div class="single-line-code"><code>`(x ≡ y) ≃ (f x ≡ f y)`{.Agda}</code></div>

その順写像は `cong f`{.Agda}、すなわち関数をパスに作用させる操作である。逆写像 `invEq (congEquiv e)`{.Agda} は像の間のパスから元の要素間のパスを復元する。したがって型同値ではパスを送ることも復元することもできるが、一般の関数に対する `cong`{.Agda} は順方向の操作だけを与える。
<!--/-->

```agda
open import Cubical.Foundations.Equiv.Properties public using ( congEquiv )
```

<!--en-->
Finally, equivalence preserves homotopy levels, just as `Lift`{.Agda} does. If `h : isProp A`{.Agda}, then `isOfHLevelRespectEquiv 1 e h`{.Agda} proves `isProp B`{.Agda}; if `h : isSet A`{.Agda}, then `isOfHLevelRespectEquiv 2 e h`{.Agda} proves `isSet B`{.Agda}. The index `0`{.Agda} likewise transfers contractibility. Here the certificate follows the equivalence from `A`{.Agda} to `B`{.Agda}, even when their universes differ.
<!--zh-->
最后，类型等价与 `Lift`{.Agda} 一样保留同伦层级。若 `h : isProp A`{.Agda}，则 `isOfHLevelRespectEquiv 1 e h`{.Agda} 证明 `isProp B`{.Agda}；若 `h : isSet A`{.Agda}，则 `isOfHLevelRespectEquiv 2 e h`{.Agda} 证明 `isSet B`{.Agda}。参数 `0`{.Agda} 同样用于传递可缩性。这里，证书沿等价从 `A`{.Agda} 传到 `B`{.Agda}，即使两者的宇宙不同也成立。
<!--ja-->
最後に、型同値は `Lift`{.Agda} と同様にホモトピーレベルを保つ。`h : isProp A`{.Agda} なら `isOfHLevelRespectEquiv 1 e h`{.Agda} は `isProp B`{.Agda} を証明し、`h : isSet A`{.Agda} なら `isOfHLevelRespectEquiv 2 e h`{.Agda} は `isSet B`{.Agda} を証明する。引数 `0`{.Agda} は同じく可縮性を移す。ここでは証明が同値に沿って `A`{.Agda} から `B`{.Agda} へ移り、両者の宇宙が異なってもよい。
<!--/-->

```agda
open import Cubical.Foundations.HLevels public using ( isOfHLevelRespectEquiv )
```

<!--en-->
We can therefore construct a convenient presentation with `Iso`{.Agda}, convert it with `isoToEquiv`{.Agda}, and use the resulting equivalence to move elements, paths and homotopy-level certificates.
<!--zh-->
因此，我们可以用 `Iso`{.Agda} 构造便于操作的呈现，经 `isoToEquiv`{.Agda} 转换，再用所得等价搬移元素、路径和同伦层级证书。
<!--ja-->
したがって `Iso`{.Agda} で扱いやすい提示を構成し、`isoToEquiv`{.Agda} で変換すれば、得られた同値を使って要素、パス、ホモトピーレベルの証明を移せる。
<!--/-->

<!--en-->
## Propositions

The next constructions isolate types that express statements rather than arbitrary data. We first characterize propositionhood, then form the universe of propositions, control existential information by truncation, assemble propositions with logical operations, and finally use proposition-valued predicates to describe classes.
<!--zh-->
## 命题

下面的构造把表达陈述的类型从一般数据类型中区分出来。我们先刻画命题性，再构成命题宇宙，用截断控制存在性信息，用逻辑运算组合命题，最后以命题值谓词描述类。
<!--ja-->
## 命題

以下の構成では、主張を表す型を一般のデータ型から取り分ける。まず命題性を特徴づけ、次に命題の宇宙を作り、切り詰めによって存在情報を制御し、論理演算で命題を組み立て、最後に命題値の述語でクラスを記述する。
<!--/-->

<!--en-->
### Propositionhood
<!--zh-->
### 命题性
<!--ja-->
### 命題性
<!--/-->

<!--en-->
In cubical type theory, a proposition is a type satisfying `isProp`{.Agda}. This condition makes any two elements of the type equal, so the type retains only the logical information of whether a proof exists, without distinguishing different proofs. An element of the type proves the corresponding proposition; without such an element, the proposition has not yet been proved.

Four closure principles recur later in the book:

- `isPropΠ`{.Agda} says that propositions are closed under Π types. If every `B x`{.Agda} is a proposition, then `(x : A) → B x`{.Agda} is also a proposition. Universally quantifying a family of propositions therefore produces another proposition.
- `isProp→`{.Agda} is the non-dependent specialization of `isPropΠ`{.Agda}. If `B`{.Agda} is a proposition, then the function type `A → B`{.Agda} is a proposition, with no propositionhood requirement on its source type `A`{.Agda}.
- `isPropΣ`{.Agda} handles dependent pairs. If `A`{.Agda} and every `B x`{.Agda} are propositions, then `Σ (x : A) (B x)`{.Agda} is also a proposition.
- `isProp×`{.Agda} is the non-dependent specialization of `isPropΣ`{.Agda}. If `A`{.Agda} and `B`{.Agda} are propositions, then a pair consisting of a proof of each is again a proposition: any two such pairs are equal componentwise.
<!--zh-->
在立方类型论中，命题是满足 `isProp`{.Agda} 的类型。这个条件保证该类型的任意两个元素都相等，因此其中只保留「是否存在证明」这一逻辑信息，不再区分不同的证明。类型具有元素时，相应命题成立；无法构造元素时，则尚未得到该命题的证明。

后文会反复使用命题性的四项封闭性质：

- `isPropΠ`{.Agda} 表明命题对 Π 类型封闭。若每个 `B x`{.Agda} 都是命题，那么 `(x : A) → B x`{.Agda} 也是命题。因此，对一族命题作全称量化，所得结果仍然是命题。
- `isProp→`{.Agda} 是 `isPropΠ`{.Agda} 不带依赖时的特例。只要值域 `B`{.Agda} 是命题，函数类型 `A → B`{.Agda} 就是命题，而无须要求定义域 `A`{.Agda} 也是命题。
- `isPropΣ`{.Agda} 处理依值对。若 `A`{.Agda} 和每个 `B x`{.Agda} 都是命题，那么 `Σ (x : A) (B x)`{.Agda} 仍是命题。
- `isProp×`{.Agda} 是 `isPropΣ`{.Agda} 不带依赖时的特例。若 `A`{.Agda} 与 `B`{.Agda} 都是命题，那么同时包含二者证明的对仍是命题：任意两个这样的对都逐分量相等。
<!--ja-->
立方型理論では、命題とは `isProp`{.Agda} を満たす型である。この条件により、その型の任意の二つの元は等しくなる。したがって、証明どうしを区別せず、証明が存在するかどうかという論理的な情報だけが残る。型の元を構成すれば対応する命題が成り立つことが示され、元をまだ構成できなければ、その命題の証明はまだ得られていない。

後の章では、命題性に関する四つの閉性を繰り返し使う。

- `isPropΠ`{.Agda} は、命題が Π 型に対して閉じていることを示す。すべての `B x`{.Agda} が命題なら、`(x : A) → B x`{.Agda} も命題である。したがって、命題の族を全称量化して得られる結果も命題である。
- `isProp→`{.Agda} は `isPropΠ`{.Agda} の依存しない特別な場合である。終域 `B`{.Agda} が命題なら、定義域 `A`{.Agda} が命題であることを仮定しなくても、関数型 `A → B`{.Agda} は命題になる。
- `isPropΣ`{.Agda} は依存対を扱う。`A`{.Agda} と各 `B x`{.Agda} が命題なら、`Σ (x : A) (B x)`{.Agda} も命題になる。
- `isProp×`{.Agda} は `isPropΣ`{.Agda} の依存しない特別な場合である。`A`{.Agda} と `B`{.Agda} が命題なら、それぞれの証明を組にした型も命題である。そのような二つの組は成分ごとに等しくなる。
<!--/-->

```agda
open import Cubical.Foundations.HLevels public
  using ( isPropΠ; isProp→; isPropΣ; isProp× )
```

<!--en-->
Propositionhood also controls equality between proof-carrying dependent pairs. If every possible second component is a proposition, `Σ≡Prop`{.Agda} says that two such pairs are equal as soon as their first components are equal. Their certificates contain no further distinguishable choice, so equality of the underlying objects determines equality of the complete packages.
<!--zh-->
命题性也控制着携带证明的依值对如何相等。若每个可能的第二分量都是命题，`Σ≡Prop`{.Agda} 表明：两个依值对的第一分量相等，就足以推出它们整体相等。证书不携带可进一步区分的选择，所以底层对象相等便能确定整个资料包相等。
<!--ja-->
命題性は、証明を携える依存対の等しさも制御する。可能な第二成分がすべて命題なら、`Σ≡Prop`{.Agda} により、二つの依存対は第一成分が等しいだけで全体として等しくなる。証明書にはそれ以上区別できる選択がないため、基礎となる対象の等しさが梱包全体の等しさを決定する。
<!--/-->

```agda
open import Cubical.Data.Sigma public using ( Σ≡Prop )
```

<!--en-->
### The universe of propositions
<!--zh-->
### 命题宇宙
<!--ja-->
### 命題の宇宙
<!--/-->

<!--en-->
To keep a proposition together with the fact that it is a proposition, the Cubical library uses `hProp ℓ`{.Agda}. This is the type of all propositions at universe level `ℓ`{.Agda}: in other words, `hProp ℓ`{.Agda} is the **universe of propositions** at that level. A `P : hProp ℓ`{.Agda} has two components:

- The first component is the [underlying type]{.term-intro #underlying-type}: the type expressing the proposition, namely the statement of the proposition itself.
- The second component is the certificate that this type satisfies `isProp`{.Agda}.

Thus `P : hProp ℓ`{.Agda} represents a proposition, but does not say that the proposition has already been proved. Its certificate says only that the first component is a proposition; it does not say that the first component has an element.
<!--zh-->
为了把一个命题连同它具有命题性这一事实放在一起，Cubical 库使用 `hProp ℓ`{.Agda}。它是宇宙层级 `ℓ`{.Agda} 上所有命题组成的类型；换言之，`hProp ℓ`{.Agda} 就是该层级上的**命题宇宙**。一个 `P : hProp ℓ`{.Agda} 包含两个分量：

- 第一分量是命题的[底层类型]{.term-intro #underlying-type}，也就是表达命题的类型，即命题的表述本身；
- 第二分量是该类型确实满足 `isProp`{.Agda} 的证书。

因此，`P : hProp ℓ`{.Agda} 表示一个命题，却不表示这个命题已经得到证明。它携带的证书只说明第一分量具有命题性，并不说明第一分量中存在元素。
<!--ja-->
命題を、それが命題であるという事実と一緒に収めるため、Cubical ライブラリでは `hProp ℓ`{.Agda} を使う。これは宇宙レベル `ℓ`{.Agda} にあるすべての命題の型である。言い換えれば、`hProp ℓ`{.Agda} はそのレベルの**命題の宇宙**である。`P : hProp ℓ`{.Agda} は二つの成分を含む。

- 第一成分は命題の[基礎型]{.term-intro #underlying-type}、すなわち命題を表す型であり、命題の記述そのものである。
- 第二成分は、その型が確かに `isProp`{.Agda} を満たすという証明書である。

したがって、`P : hProp ℓ`{.Agda} は命題を表すが、その命題がすでに証明されているとは主張しない。`P`{.Agda} が持つ証明書は、第一成分が命題であることだけを示し、第一成分に元が存在するとは主張しない。
<!--/-->

<!--en-->
The proposition universe is itself an h-set. `isSetHProp`{.Agda} allows propositions to differ, while ensuring that equality proofs between propositions contain no distinguishable higher structure.
<!--zh-->
命题宇宙本身是 h-集合。`isSetHProp`{.Agda} 允许不同命题彼此有别，同时保证命题之间的相等证明不再含有可区分的更高结构。
<!--ja-->
命題の宇宙自身は h-集合である。`isSetHProp`{.Agda} は異なる命題を区別できるままにしつつ、命題間の等しさの証明には区別できる高次の構造が残らないことを保証する。
<!--/-->

```agda
open import Cubical.Foundations.HLevels public
  using ( hProp; isSetHProp )
```

<!--en-->
The projection `⟨_⟩`{.Agda} extracts the statement of a proposition. For `P : hProp ℓ`{.Agda}, `⟨ P ⟩`{.Agda} is its first component; to prove the proposition expressed by `P`{.Agda}, we must construct an element of `⟨ P ⟩`{.Agda}. The notation `⟨ P ⟩isProp`{.Agda} extracts the certificate that this underlying type satisfies `isProp`{.Agda}.
<!--zh-->
投影 `⟨_⟩`{.Agda} 用来取出命题的表述。对于 `P : hProp ℓ`{.Agda}，`⟨ P ⟩`{.Agda} 就是它的第一分量；若要证明 `P`{.Agda} 所表达的命题成立，则须构造 `⟨ P ⟩`{.Agda} 的元素。记号 `⟨ P ⟩isProp`{.Agda} 则取出该底层类型满足 `isProp`{.Agda} 的证书。
<!--ja-->
射影 `⟨_⟩`{.Agda} は命題の記述を取り出す。`P : hProp ℓ`{.Agda} に対して、`⟨ P ⟩`{.Agda} はその第一成分である。`P`{.Agda} が表す命題を証明するには、`⟨ P ⟩`{.Agda} の元を構成しなければならない。記法 `⟨ P ⟩isProp`{.Agda} は、この基礎型が `isProp`{.Agda} を満たすことの証明を取り出す。
<!--/-->

<!--en-->
An object `P`{.Agda} packages the statement of a proposition together with its propositionhood certificate, so it can be passed as a function argument, returned as a function result or stored in a record field. When we need to state or prove the proposition, we extract the corresponding type through `⟨ P ⟩`{.Agda}. The examples below show an empty underlying type and an inhabited one: both carry a propositionhood certificate.
<!--zh-->
`P`{.Agda} 把命题的表述与命题性证书收在同一个对象中，因此可以整体作为函数的参数、返回值或记录的字段使用。需要陈述或证明这个命题时，再通过 `⟨ P ⟩`{.Agda} 取出相应的类型。下图分别示意底层类型为空与有元素的例子：二者都携带命题性证书。
<!--ja-->
`P`{.Agda} は命題の記述とその命題性の証明書を一つの対象にまとめるため、全体を関数の引数や返り値として渡したり、レコードのフィールドに格納したりできる。命題を述べたり証明したりするときは、`⟨ P ⟩`{.Agda} を通して対応する型を取り出す。下図では、基礎型が空である例と元をもつ例を示す。どちらも命題性の証明書をもつ。
<!--/-->

```agda
open import Cubical.Foundations.Structure public
  using ( ⟨_⟩ )

⟨_⟩isProp : ∀ {ℓ} (P : hProp ℓ) → isProp ⟨ P ⟩
⟨ P ⟩isProp = P .snd
```

<figure class="book-diagram type-comparison path-figure" id="fig-proposition-and-proof" aria-describedby="fig-proposition-and-proof-caption">
<div class="diagram-framed type-comparison-panels proposition-proof-panels">
<section class="type-comparison-panel">

$$P=(\langle P\rangle,h_P):\operatorname{hProp}\,\ell$$

<div class="diagram-space">

$$\langle P\rangle:\operatorname{Type}_{\ell}$$

<div class="path-stage" style="aspect-ratio:280/140">
<!--en-->
<span class="path-label" style="left:50%;top:50%">(no elements)</span>
<!--zh-->
<span class="path-label" style="left:50%;top:50%">(没有元素)</span>
<!--ja-->
<span class="path-label" style="left:50%;top:50%">(元がない)</span>
<!--/-->
</div>
</div>

$$h_P:\operatorname{isProp}\langle P\rangle$$

</section>
<section class="type-comparison-panel">

$$Q=(\langle Q\rangle,h_Q):\operatorname{hProp}\,\ell$$

<div class="diagram-space">

$$\langle Q\rangle:\operatorname{Type}_{\ell}$$

<div class="path-stage" style="aspect-ratio:280/140">
<svg viewBox="0 0 280 140" aria-hidden="true" focusable="false">
<path class="diagram-path" d="M60 90 Q140 10 220 90"/>
<circle class="diagram-point" cx="60" cy="90" r="4"/>
<circle class="diagram-point" cx="220" cy="90" r="4"/>
</svg>
<span class="path-label" style="left:21.4286%;top:83%">$p$</span>
<span class="path-label" style="left:78.5714%;top:83%">$q$</span>
<span class="path-label" style="left:50%;top:24%">$h_Q\,p\,q$</span>
</div>
</div>

$$h_Q:\operatorname{isProp}\langle Q\rangle$$

</section>
</div>
<figcaption id="fig-proposition-and-proof-caption">
<!--en-->
The certificate $h_Q$ assigns a path to any two proofs; the curve shows its value $h_Q\,p\,q$ at $p$ and $q$.
<!--zh-->
证书 $h_Q$ 为任意两个证明给出路径；右图的曲线表示它在 $p$、$q$ 上的值 $h_Q\,p\,q$。
<!--ja-->
証明書 $h_Q$ は任意の二つの証明にパスを与える。右図の曲線は、その $p$、$q$ における値 $h_Q\,p\,q$ を表す。
<!--/-->
</figcaption>
</figure>

<!--en-->
### [Propositional truncation]{.term-intro #propositional-truncation}
<!--zh-->
### [命题截断]{.term-intro #propositional-truncation}
<!--ja-->
### [命題的切り詰め]{.term-intro #propositional-truncation}
<!--/-->

<!--en-->
A type may contain more information than a proposition should retain. The [propositional truncation]{.term-ref #propositional-truncation} `∥ A ∥₁`{.Agda} records that `A`{.Agda} has an element while deliberately forgetting which element it is. It is a [higher inductive type]{.term-intro #higher-inductive-type}, abbreviated HIT: its generators include not only points but also paths between points. The point constructor `∣_∣₁`{.Agda} sends each `a : A`{.Agda} to `∣ a ∣₁ : ∥ A ∥₁`{.Agda}; the path constructor `squash₁`{.Agda} identifies every two elements of the truncation. Its defining rules are

$$\frac{a:A}{|a|_1:\|A\|_1}\qquad\frac{x,y:\|A\|_1}{\mathsf{squash}_1(x,y):x=y}$$

Consequently `∥ A ∥₁`{.Agda} is always a proposition, even when `A`{.Agda} carries distinguishable data.

By the **[mere existence]{.term-intro #mere-existence}** of an element of `A`{.Agda}, we mean an element of `∥ A ∥₁`{.Agda}, without specifying an element of `A`{.Agda}. Likewise, saying that an `x : A`{.Agda} satisfying `P x`{.Agda} merely exists means that `∥ Σ[ x ∈ A ] P x ∥₁`{.Agda} has an element. When `P x`{.Agda} is a proposition, this truncated type underlies the logical existential quantification `∃[ x ∶ A ] P x`{.Agda} introduced below.
<!--zh-->
一个类型所携带的信息可能多于命题应当保留的信息。[命题截断]{.term-ref #propositional-truncation} `∥ A ∥₁`{.Agda} 记录 `A`{.Agda} 具有元素，却有意忘去具体是哪一个元素。它是一种[高阶归纳类型]{.term-intro #higher-inductive-type}，简称 HIT：生成它的不仅有点，还有点之间的路径。点构造子 `∣_∣₁`{.Agda} 把每个 `a : A`{.Agda} 送到 `∣ a ∣₁ : ∥ A ∥₁`{.Agda}；路径构造子 `squash₁`{.Agda} 把截断中的任意两个元素认同起来。其定义规则为

$$\frac{a:A}{|a|_1:\|A\|_1}\qquad\frac{x,y:\|A\|_1}{\mathsf{squash}_1(x,y):x=y}$$

因此，即使 `A`{.Agda} 携带可区分的资料，`∥ A ∥₁`{.Agda} 仍然总是命题。

本书说 `A`{.Agda} 的元素**[仅仅存在]{.term-intro #mere-existence}**，意指 `∥ A ∥₁`{.Agda} 有元素，而没有指定 `A`{.Agda} 中的某个元素。同样，说满足 `P x`{.Agda} 的 `x : A`{.Agda} 仅仅存在，意指 `∥ Σ[ x ∈ A ] P x ∥₁`{.Agda} 有元素。当 `P x`{.Agda} 是命题时，这个截断类型就是后文引入的逻辑存在量化 `∃[ x ∶ A ] P x`{.Agda} 的底层类型。
<!--ja-->
型は、命題が保持すべき情報より多くの情報をもつことがある。[命題的切り詰め]{.term-ref #propositional-truncation} `∥ A ∥₁`{.Agda} は、`A`{.Agda} に要素があることを記録しつつ、それがどの要素かを意図的に忘れる。これは[高階帰納型]{.term-intro #higher-inductive-type}、略して HIT である。その生成子には点だけでなく、点の間のパスも含まれる。点構成子 `∣_∣₁`{.Agda} は各 `a : A`{.Agda} を `∣ a ∣₁ : ∥ A ∥₁`{.Agda} へ送り、パス構成子 `squash₁`{.Agda} は切り詰めの任意の二要素を同一視する。その定義規則は次のとおりである。

$$\frac{a:A}{|a|_1:\|A\|_1}\qquad\frac{x,y:\|A\|_1}{\mathsf{squash}_1(x,y):x=y}$$

したがって `A`{.Agda} が区別可能なデータをもっていても、`∥ A ∥₁`{.Agda} は常に命題である。

本書で `A`{.Agda} の要素の**[単なる存在]{.term-intro #mere-existence}**と言うときは、`A`{.Agda} の特定の要素ではなく、`∥ A ∥₁`{.Agda} の要素が与えられることを意味する。同様に、`P x`{.Agda} を満たす `x : A`{.Agda} が単に存在するとは、`∥ Σ[ x ∈ A ] P x ∥₁`{.Agda} に要素があることを意味する。`P x`{.Agda} が命題であるとき、この切り詰められた型が、後で導入する論理的な存在量化 `∃[ x ∶ A ] P x`{.Agda} の基礎となる型である。
<!--/-->

<figure class="book-diagram type-comparison path-figure" id="fig-truncation-witnesses" aria-describedby="fig-truncation-witnesses-caption">
<div class="diagram-framed">
<div class="path-stage diagram-compact-stage" style="aspect-ratio:420/340">
<svg viewBox="0 0 420 340" aria-hidden="true" focusable="false">
<rect class="diagram-space-shape" x="15" y="10" width="390" height="100"/>
<rect class="diagram-space-shape" x="15" y="205" width="390" height="125"/>
<path class="diagram-map-line" d="M95 83 L95 249"/>
<path class="diagram-map-tip" d="M91 242 L95 249 L99 242"/>
<path class="diagram-map-line" d="M325 83 L325 249"/>
<path class="diagram-map-tip" d="M321 242 L325 249 L329 242"/>
<path class="diagram-path" d="M95 253 Q210 350 325 253"/>
<circle class="diagram-point" cx="95" cy="79" r="4"/>
<circle class="diagram-point" cx="325" cy="79" r="4"/>
<circle class="diagram-point" cx="95" cy="253" r="4"/>
<circle class="diagram-point" cx="325" cy="253" r="4"/>
</svg>
<span class="path-label" style="left:50%;top:10.2941%">$A$</span>
<span class="path-label" style="left:22.619%;top:16.4706%">$a$</span>
<span class="path-label" style="left:77.381%;top:16.4706%">$b$</span>
<span class="path-label" style="left:50%;top:45.2941%">$\lvert{-}\rvert_1$</span>
<span class="path-label" style="left:50%;top:66.7647%">$\|A\|_1$</span>
<span class="path-label" style="left:13.0952%;top:74.4118%">$\lvert a\rvert_1$</span>
<span class="path-label" style="left:86.9048%;top:74.4118%">$\lvert b\rvert_1$</span>
<span class="path-label" style="left:50%;top:91.7647%">$\operatorname{squash}_1\,\lvert a\rvert_1\,\lvert b\rvert_1$</span>
</div>
</div>
<figcaption id="fig-truncation-witnesses-caption">
<!--en-->
Given `a b : A`{.Agda}, their images in the truncation are joined by the displayed path. The two images need not be judgmentally equal; `squash₁`{.Agda} supplies their equality proof.
<!--zh-->
给定 `a b : A`{.Agda}，它们在截断中的像由图示路径相连。这两个像未必判断相等；`squash₁`{.Agda} 给出它们之间的相等证明。
<!--ja-->
`a b : A`{.Agda} が与えられると、切り詰めでの像は図のパスで結ばれる。二つの像が判断的に等しいとは限らず、`squash₁`{.Agda} がその等しさの証明を与える。
<!--/-->
</figcaption>
</figure>

<!--en-->
There are two standard ways to use a truncated value. The recursor `rec₁`{.Agda} may expose a representative only while constructing a target already known to be a proposition; this restriction prevents a hidden choice from escaping as ordinary data.

<div class="single-line-code"><code>`rec₁ : isProp P → (A → P) → ∥ A ∥₁ → P`{.Agda}</code></div>
<!--zh-->
使用截断值有两种标准方式。递归子 `rec₁`{.Agda} 只有在目标已经证明为命题时，才允许局部取出一个代表；这项限制防止隐藏的选择逸出为普通资料。

<div class="single-line-code"><code>`rec₁ : isProp P → (A → P) → ∥ A ∥₁ → P`{.Agda}</code></div>
<!--ja-->
切り詰められた値の使い方には、二つの標準的な方法がある。再帰子 `rec₁`{.Agda} が代表を局所的に取り出せるのは、行き先が命題であるとすでに証明されている場合だけである。この制限により、隠された選択が通常のデータとして外へ出ることを防ぐ。

<div class="single-line-code"><code>`rec₁ : isProp P → (A → P) → ∥ A ∥₁ → P`{.Agda}</code></div>
<!--/-->

<figure class="book-diagram type-comparison" id="fig-truncation-rec" aria-describedby="fig-truncation-rec-caption">
<div class="diagram-framed type-comparison-panel">

$$h : \operatorname{isProp}(P), \qquad f : A \to P$$

<div class="factorization-stage">
<svg viewBox="0 0 500 230" aria-hidden="true" focusable="false">
<path class="diagram-map-line" d="M88 50 H315"/>
<path class="diagram-map-tip" d="M306 45 L315 50 L306 55"/>
<path class="diagram-map-line" d="M358 76 V160"/>
<path class="diagram-map-tip" d="M353 151 L358 160 L363 151"/>
<path class="diagram-map-line" d="M72 74 L315 177"/>
<path class="diagram-map-tip" d="M303 179 L315 177 L308 167"/>
</svg>
<span class="factorization-label factorization-source">$A$</span>
<span class="factorization-label factorization-truncated">$\|A\|_1$</span>
<span class="factorization-label factorization-target">$P$</span>
<span class="factorization-label factorization-top-map">$|{-}|_1$</span>
<span class="factorization-label factorization-long-map">$f$</span>
<span class="factorization-label factorization-right-map">$\operatorname{rec}_1\,h\,f$</span>
</div>

$$\operatorname{rec}_1\,h\,f\,(|a|_1) = f(a) \qquad (a : A)$$

</div>
<figcaption id="fig-truncation-rec-caption">
<!--en-->
`rec₁`{.Agda} factors `f : A → P`{.Agda} through the truncation, provided that `P`{.Agda} is a proposition. Both routes give `f a`{.Agda} on a representative `a`{.Agda}.
<!--zh-->
当 `P`{.Agda} 是命题时，`rec₁`{.Agda} 使 `f : A → P`{.Agda} 经由截断分解。对代表 `a`{.Agda}，两条路线都得到 `f a`{.Agda}。
<!--ja-->
`P`{.Agda} が命題ならば、`rec₁`{.Agda} によって `f : A → P`{.Agda} は切り詰めを経由して分解される。代表 `a`{.Agda} に対し、どちらの経路も `f a`{.Agda} を与える。
<!--/-->
</figcaption>
</figure>

<!--en-->
The map `map₁`{.Agda} applies a function `A → B`{.Agda} under the truncation and returns another truncated value.

<div class="single-line-code"><code>`map₁ : (A → B) → ∥ A ∥₁ → ∥ B ∥₁`{.Agda}</code></div>
<!--zh-->
映射 `map₁`{.Agda} 在截断内部应用函数 `A → B`{.Agda}，再返回一个截断值。

<div class="single-line-code"><code>`map₁ : (A → B) → ∥ A ∥₁ → ∥ B ∥₁`{.Agda}</code></div>
<!--ja-->
写像 `map₁`{.Agda} は切り詰めの内側で関数 `A → B`{.Agda} を適用し、再び切り詰められた値を返す。

<div class="single-line-code"><code>`map₁ : (A → B) → ∥ A ∥₁ → ∥ B ∥₁`{.Agda}</code></div>
<!--/-->

```agda
import Cubical.HITs.PropositionalTruncation as PT
open PT public
  using ( ∥_∥₁; ∣_∣₁; squash₁ )
  renaming ( rec to rec₁; map to map₁ )
```

<!--en-->
### Logical operations
<!--zh-->
### 逻辑运算
<!--ja-->
### 論理演算
<!--/-->

<!--en-->
The proposition universe is closed under the usual logical operations. The following subsections construct these operations from the type formers already introduced and explain when propositional truncation is required.
<!--zh-->
命题宇宙对通常的逻辑运算封闭。下面从已经引入的类型构造出发逐项说明这些运算，并解释其中哪些需要命题截断。
<!--ja-->
命題の宇宙は通常の論理演算について閉じている。以下では、すでに導入した型の構成法から各演算を組み立て、どの場合に命題的切り詰めが必要かを説明する。
<!--/-->

<!--en-->
#### Truth
<!--zh-->
#### 真
<!--ja-->
#### 真
<!--/-->

<!--en-->
The unit type represents trivial evidence. Its zero-level form in `Type₀`{.Agda} is written `⊤₀`{.Agda}, and `⊤* {ℓ}`{.Agda} is its lift to an arbitrary universe level `ℓ`{.Agda}. Their unique elements are written `tt`{.Agda} and `tt*`{.Agda}. Since any two elements of a unit type are equal, `isProp⊤*`{.Agda} certifies that `⊤*`{.Agda} is a proposition.
<!--zh-->
单元类型表示平凡的证据。它位于 `Type₀`{.Agda} 的零层级形式记作 `⊤₀`{.Agda}，提升到任意宇宙层级 `ℓ`{.Agda} 后记作 `⊤* {ℓ}`{.Agda}；二者的唯一元素分别记作 `tt`{.Agda} 与 `tt*`{.Agda}。单元类型中的任意两个元素都相等，因此 `isProp⊤*`{.Agda} 证明 `⊤*`{.Agda} 是命题。
<!--ja-->
単元型は自明な証拠を表す。`Type₀`{.Agda} にあるレベル 0 の形を `⊤₀`{.Agda}、任意の宇宙レベル `ℓ`{.Agda} へ持ち上げた形を `⊤* {ℓ}`{.Agda} と書き、それぞれの唯一の要素を `tt`{.Agda} と `tt*`{.Agda} と書く。単元型の任意の二要素は等しいため、`isProp⊤*`{.Agda} は `⊤*`{.Agda} が命題であることを証明する。
<!--/-->

```agda
open import Cubical.Data.Unit public
  using ( tt; tt* )
  renaming ( Unit to ⊤₀; Unit* to ⊤*; isPropUnit* to isProp⊤* )
```

<!--en-->
The true proposition `⊤`{.Agda} and the unit type express the same trivial truth at two different levels of structure. The unit type is the underlying type of `⊤`{.Agda}; pairing `⊤*`{.Agda} with its propositionhood certificate `isProp⊤*`{.Agda} packages it as a proposition at any required universe level. Thus truth lies in the proposition universe because its underlying unit type is inhabited and all its elements are equal.
<!--zh-->
真命题 `⊤`{.Agda} 与单元类型表达的是同一种平凡成立性，只是所处的结构层次不同。单元类型是 `⊤`{.Agda} 的底层类型；把 `⊤*`{.Agda} 与它的命题性证书 `isProp⊤*`{.Agda} 配成一对，便得到所需宇宙层级上的真命题。因此，真属于命题宇宙，因为它的底层单元类型具有元素，且所有元素都相等。
<!--ja-->
真の命題 `⊤`{.Agda} と単元型は、同じ自明な真理を異なる構造のレベルで表す。単元型は `⊤`{.Agda} の基礎型である。`⊤*`{.Agda} とその命題性の証明 `isProp⊤*`{.Agda} を対にすれば、必要な宇宙レベルの真の命題としてまとめられる。したがって真は命題の宇宙に属する。基礎となる単元型には要素があり、そのすべての要素が等しいからである。
<!--/-->

```agda
open import Cubical.Functions.Logic public using ( ⊤ )
```

<!--en-->
#### Falsity
<!--zh-->
#### 假
<!--ja-->
#### 偽
<!--/-->

<!--en-->
The [empty type]{.term-intro #empty-type} represents impossibility. Its zero-level form in `Type₀`{.Agda} is written `⊥₀`{.Agda}, and `⊥* {ℓ}`{.Agda} is its lift to an arbitrary universe level `ℓ`{.Agda}. Neither has elements or constructors. If a branch of an argument nevertheless yields `x : ⊥*`{.Agda}, that branch's assumptions cannot hold, and `x`{.Agda} may be eliminated into any type:

<div class="single-line-code"><code>`⊥₀-rec : ⊥₀ → A`{.Agda}</code></div>

<div class="single-line-code"><code>`⊥*-rec : ⊥* → A`{.Agda}</code></div>

The eliminators `⊥₀-rec`{.Agda} and `⊥*-rec`{.Agda} do not compute an element of `A`{.Agda} from actual data. They say that there is no constructor case to handle. The certificates `isProp⊥`{.Agda} for `⊥₀`{.Agda} and `isProp⊥*`{.Agda} for `⊥*`{.Agda} are immediate for the same reason: there are no two elements whose equality would have to be proved.
<!--zh-->
[空类型]{.term-intro #empty-type}表示不可能性。它位于 `Type₀`{.Agda} 的零层级形式记作 `⊥₀`{.Agda}，提升到任意宇宙层级 `ℓ`{.Agda} 后记作 `⊥* {ℓ}`{.Agda}。二者都没有元素，也没有构造子。如果某个论证分支中仍然得到 `x : ⊥*`{.Agda}，该分支的前提便不可能成立，因而可以把 `x`{.Agda} 消去到任意类型：

<div class="single-line-code"><code>`⊥₀-rec : ⊥₀ → A`{.Agda}</code></div>

<div class="single-line-code"><code>`⊥*-rec : ⊥* → A`{.Agda}</code></div>

消去子 `⊥₀-rec`{.Agda} 与 `⊥*-rec`{.Agda} 并非从实际数据中计算出 `A`{.Agda} 的元素，而是说根本没有需要处理的构造分支。`isProp⊥`{.Agda} 证明 `⊥₀`{.Agda} 是命题，`isProp⊥*`{.Agda} 则证明 `⊥*`{.Agda} 是命题；理由相同：其中不存在两个需要证明为相等的元素。
<!--ja-->
[空型]{.term-intro #empty-type}は不可能性を表す。`Type₀`{.Agda} にあるレベル 0 の形を `⊥₀`{.Agda}、任意の宇宙レベル `ℓ`{.Agda} へ持ち上げた形を `⊥* {ℓ}`{.Agda} と書く。どちらにも要素も構成子もない。それでも論証のある分岐で `x : ⊥*`{.Agda} が得られたなら、その分岐の仮定は成立しえず、`x`{.Agda} を任意の型へ消去できる。

<div class="single-line-code"><code>`⊥₀-rec : ⊥₀ → A`{.Agda}</code></div>

<div class="single-line-code"><code>`⊥*-rec : ⊥* → A`{.Agda}</code></div>

消去子 `⊥₀-rec`{.Agda} と `⊥*-rec`{.Agda} は、実際のデータから `A`{.Agda} の要素を計算するものではない。処理すべき構成子の場合が一つもないことを述べている。`isProp⊥`{.Agda} は `⊥₀`{.Agda} の、`isProp⊥*`{.Agda} は `⊥*`{.Agda} の命題性を示す。理由は同じで、等しさを証明すべき二要素が存在しない。
<!--/-->

```agda
open import Cubical.Data.Empty public
  using ( ⊥*; isProp⊥* )
  renaming ( ⊥ to ⊥₀; rec to ⊥₀-rec; rec* to ⊥*-rec )

open import Cubical.Data.Empty.Properties public using ( isProp⊥ )
```

<!--en-->
The false proposition `⊥`{.Agda} and the empty type express the same impossibility at two different levels of structure. The empty type is the underlying type of `⊥`{.Agda}; pairing `⊥*`{.Agda} with its propositionhood certificate `isProp⊥*`{.Agda} packages it as a proposition at any required universe level. Thus falsity lies in the proposition universe because its underlying empty type has no elements, so all its elements are vacuously equal.
<!--zh-->
假命题 `⊥`{.Agda} 与空类型表达的是同一种不可能性，只是所处的结构层次不同。空类型是 `⊥`{.Agda} 的底层类型；把 `⊥*`{.Agda} 与它的命题性证书 `isProp⊥*`{.Agda} 配成一对，便得到所需宇宙层级上的假命题。因此，假属于命题宇宙，因为它的底层空类型没有元素，所以其中所有元素空虚地相等。
<!--ja-->
偽の命題 `⊥`{.Agda} と空型は、同じ不可能性を異なる構造のレベルで表す。空型は `⊥`{.Agda} の基礎型である。`⊥*`{.Agda} とその命題性の証明 `isProp⊥*`{.Agda} を対にすれば、必要な宇宙レベルの偽の命題としてまとめられる。したがって偽は命題の宇宙に属する。基礎となる空型には要素がないため、そのすべての要素が空虚に等しいからである。
<!--/-->

```agda
⊥ : ∀ {ℓ} → hProp ℓ
⊥ = ⊥* , isProp⊥*
```

<!--en-->
#### Universal quantification
<!--zh-->
#### 全称量化
<!--ja-->
#### 全称量化
<!--/-->

<!--en-->
For a family of propositions `P : A → hProp ℓ'`{.Agda}, universal quantification is the Π type introduced above: a proof is a dependent function that supplies a proof of `P x`{.Agda} for every `x : A`{.Agda}. The form `∀[ x ] P x`{.Agda} lets Agda infer the type of `x`{.Agda}, while `∀[ x ∶ A ] P x`{.Agda} displays it explicitly. No propositional truncation is needed. Each `P x`{.Agda} is a proposition, so any two dependent functions agree pointwise and are equal by function extensionality; this is the closure property `isPropΠ`{.Agda}.
<!--zh-->
对命题族 `P : A → hProp ℓ'`{.Agda}，全称量化就是前文介绍的 Π 类型：它的证明是一个依值函数，为每个 `x : A`{.Agda} 给出 `P x`{.Agda} 的证明。写作 `∀[ x ] P x`{.Agda} 时由 Agda 推断 `x`{.Agda} 的类型；写作 `∀[ x ∶ A ] P x`{.Agda} 时则把这个类型明确列出。这里不需要命题截断。每个 `P x`{.Agda} 都是命题，所以任意两个依值函数逐点相等，再由函数外延性可知它们相等；这正是 `isPropΠ`{.Agda} 所表达的封闭性。
<!--ja-->
命題族 `P : A → hProp ℓ'`{.Agda} に対する全称量化は、先に導入した Π 型である。その証明は、各 `x : A`{.Agda} に `P x`{.Agda} の証明を与える依存関数である。`∀[ x ] P x`{.Agda} と書けば `x`{.Agda} の型を Agda が推論し、`∀[ x ∶ A ] P x`{.Agda} と書けばその型を明示できる。ここでは命題的切り詰めは不要である。各 `P x`{.Agda} が命題なので、任意の二つの依存関数は各点で等しく、関数外延性によって関数そのものも等しくなる。これが `isPropΠ`{.Agda} の表す閉性である。
<!--/-->

```agda
open import Cubical.Functions.Logic public using ( ∀[]-syntax; ∀[∶]-syntax )
```

<!--en-->
#### Implication
<!--zh-->
#### 蕴涵
<!--ja-->
#### 含意
<!--/-->

<!--en-->
`P ⇒ Q`{.Agda} is implication. Its evidence is a function taking each proof of `P`{.Agda} to a proof of `Q`{.Agda}, so implication is the non-dependent special case of the universal quantification just introduced. No propositional truncation is needed: because `Q`{.Agda} is a proposition, any two such functions agree at every input, and function extensionality makes the functions equal. Thus the function type itself is already a proposition, regardless of how many proofs `P`{.Agda} has.
<!--zh-->
`P ⇒ Q`{.Agda} 表示蕴涵。它的证据是一个函数，把 `P`{.Agda} 的每个证明变成 `Q`{.Agda} 的证明，因此蕴涵就是刚刚介绍的全称量化不带依赖时的特例。这里不需要命题截断：由于 `Q`{.Agda} 是命题，任意两个这样的函数在每个输入上都给出相等的结果，再由函数外延性可知两个函数相等。因此，无论 `P`{.Agda} 有多少证明，这个函数类型本身已经是命题。
<!--ja-->
`P ⇒ Q`{.Agda} は含意を表す。その証拠は `P`{.Agda} の各証明を `Q`{.Agda} の証明へ送る関数なので、いま導入した全称量化の、依存しない特別な場合である。ここでは命題的切り詰めは不要である。`Q`{.Agda} が命題であるため、任意の二つの関数は各入力で等しい結果を与え、関数外延性によって関数そのものも等しくなる。したがって `P`{.Agda} に証明がいくつあっても、この関数型はすでに命題である。
<!--/-->

```agda
open import Cubical.Functions.Logic public using ( _⇒_ )
```

<!--en-->
#### Negation
<!--zh-->
#### 否定
<!--ja-->
#### 否定
<!--/-->

<!--en-->
Negation is the special implication `¬ P`{.Agda} from `P`{.Agda} to the empty type underlying falsity: it says that any proof of `P`{.Agda} would yield an impossibility. Unlike general binary implication, negation remains at the universe level of `P`{.Agda}. Its closure under propositionhood can be read directly from two earlier certificates. First, `isProp⊥`{.Agda} says that the zero-level empty target type is a proposition. Then `isProp→`{.Agda} says that a function type is a proposition whenever its target type is, without requiring its source type to be a proposition. Applying it to `isProp⊥`{.Agda} therefore proves that the type underlying `¬ P`{.Agda} is a proposition. No propositional truncation is needed.
<!--zh-->
否定是从 `P`{.Agda} 到假命题底层空类型的特殊蕴涵，记作 `¬ P`{.Agda}：它断言 `P`{.Agda} 的任何证明都会导出不可能性。与一般的二元蕴涵不同，否定仍位于 `P`{.Agda} 所在的宇宙层级。它为何对命题封闭，可以直接由前文的两项证书看出。首先，`isProp⊥`{.Agda} 说明零层级空类型是命题；随后，`isProp→`{.Agda} 说明只要值域是命题，函数类型就是命题，而无须要求定义域也是命题。把 `isProp→`{.Agda} 用于 `isProp⊥`{.Agda}，便证明了 `¬ P`{.Agda} 的底层类型具有命题性。这里不需要命题截断。
<!--ja-->
否定 `¬ P`{.Agda} は、`P`{.Agda} から偽命題の基礎にある空型への特別な含意であり、`P`{.Agda} のどの証明からも不可能性が導かれることを述べる。一般の二項含意とは異なり、否定は `P`{.Agda} と同じ宇宙レベルにある。否定が命題について閉じることは、先に導入した二つの証明書から直接分かる。まず `isProp⊥`{.Agda} は、レベル 0 の空な終域が命題であることを示す。次に `isProp→`{.Agda} は、終域が命題なら、定義域の命題性を仮定せずとも関数型が命題になることを示す。したがって `isProp→`{.Agda} を `isProp⊥`{.Agda} に適用すれば、`¬ P`{.Agda} の基礎型が命題であることが証明される。命題的切り詰めは必要ない。
<!--/-->

```agda
open import Cubical.Functions.Logic public using ( ¬_ )
```

<!--en-->
#### Propositional extensionality
<!--zh-->
#### 命题外延性
<!--ja-->
#### 命題外延性
<!--/-->

<!--en-->
Mutual implication between propositions is called [logical equivalence]{.term-intro #logical-equivalence}. Propositional extensionality turns it into equality inside the proposition universe. Mutual implication packages two instances of the implication introduced above: one function from `P`{.Agda} to `Q`{.Agda} and one from `Q`{.Agda} to `P`{.Agda}. This package uses a product, the non-dependent case of a Σ type. `⇔toPath`{.Agda} turns the two functions into a path `P ≡ Q`{.Agda}. No propositional truncation is involved: since `P`{.Agda} and `Q`{.Agda} are propositions, their individual proofs carry no distinguishable data, so the two implications already express everything needed for their equality. The resulting path type is itself a proposition because `hProp`{.Agda} is a set.
<!--zh-->
命题之间的双向蕴涵称为[逻辑等价]{.term-intro #logical-equivalence}。命题外延性把它变成命题宇宙内部的相等。双向蕴涵把上文引入的蕴涵打包两次：一个函数从 `P`{.Agda} 到 `Q`{.Agda}，另一个函数从 `Q`{.Agda} 到 `P`{.Agda}。这个包是一个积，也就是 Σ 类型不带依赖时的特例。`⇔toPath`{.Agda} 把这两个函数变成路径 `P ≡ Q`{.Agda}。这里不需要命题截断：因为 `P`{.Agda} 与 `Q`{.Agda} 都是命题，各自的证明不携带可区分的资料，所以两向蕴涵已经表达了建立二者相等所需的全部信息。又因为 `hProp`{.Agda} 是集合，所得的路径类型本身也是命题。
<!--ja-->
命題間の双方向の含意を[論理的同値]{.term-intro #logical-equivalence}と呼ぶ。命題外延性は、それを命題の宇宙における等しさへ変える。双方向の含意は、先に導入した含意を二つまとめたものである。一方の関数は `P`{.Agda} から `Q`{.Agda} へ、もう一方は `Q`{.Agda} から `P`{.Agda} へ進む。この組は積、すなわち Σ 型の依存しない特別な場合である。`⇔toPath`{.Agda} はこの二つの関数からパス `P ≡ Q`{.Agda} を作る。ここでも命題的切り詰めは不要である。`P`{.Agda} と `Q`{.Agda} は命題なので、その証明に区別できるデータはなく、二方向の含意が両者の等しさに必要な情報をすべて表すからである。さらに `hProp`{.Agda} は集合なので、得られるパス型も命題である。
<!--/-->

```agda
open import Cubical.Functions.Logic public using ( ⇔toPath )
```

<!--en-->
#### Existential quantification
<!--zh-->
#### 存在量化
<!--ja-->
#### 存在量化
<!--/-->

<!--en-->
Existential quantification begins with the Σ type introduced above. Its dependent pairs contain both a witness `x : A`{.Agda} and a proof of `P x`{.Agda}. Even though every `P x`{.Agda} is a proposition, the witnesses in `A`{.Agda} may be distinguishable, so this Σ type need not be a proposition. The notation therefore applies propositional truncation: `∃[ x ] P x`{.Agda} lets Agda infer the type of the witness, while `∃[ x ∶ A ] P x`{.Agda} states it explicitly, and both forget which witness was chosen while retaining that some witness exists. Existential quantification therefore needs truncation because its untruncated evidence contains an arbitrary element of `A`{.Agda}, whereas the preceding universal quantification and implication do not.
<!--zh-->
存在量化从前文介绍的 Σ 类型出发，其依值对同时包含见证 `x : A`{.Agda} 与 `P x`{.Agda} 的证明。即使每个 `P x`{.Agda} 都是命题，`A`{.Agda} 中的见证仍可能彼此不同，所以这个 Σ 类型未必是命题。因此，这套记法还要加上命题截断：`∃[ x ] P x`{.Agda} 让 Agda 推断见证的类型，`∃[ x ∶ A ] P x`{.Agda} 则明确写出这个类型；二者都忘掉具体选中了哪个见证，只保留某个见证存在。因此，存在量化需要截断，因为未经截断的证据含有 `A`{.Agda} 中的任意元素；前面的全称量化与蕴涵则没有这种额外资料。
<!--ja-->
存在量化は、先に導入した Σ 型から始まる。その依存対は、証人 `x : A`{.Agda} と `P x`{.Agda} の証明をともに含む。各 `P x`{.Agda} が命題でも、`A`{.Agda} の証人どうしは区別できるかもしれないため、この Σ 型は命題とは限らない。そこで、この記法はさらに命題的切り詰めを施す。`∃[ x ] P x`{.Agda} は証人の型を Agda に推論させ、`∃[ x ∶ A ] P x`{.Agda} はその型を明示するが、どちらも選ばれた証人を忘れ、何らかの証人が存在することだけを残す。したがって、切り詰める前の証拠が `A`{.Agda} の任意の要素を含むため、存在量化には切り詰めが必要である。先に見た全称量化と含意には、このような余分なデータはない。
<!--/-->

```agda
open import Cubical.Functions.Logic public using ( ∃[]-syntax; ∃[∶]-syntax )
```

<!--en-->
#### Conjunction
<!--zh-->
#### 合取
<!--ja-->
#### 連言
<!--/-->

<!--en-->
The corresponding non-dependent case of the Σ construction is conjunction. For propositions `P`{.Agda} and `Q`{.Agda}, a proof of `P ⊓ Q`{.Agda} is a pair containing one proof of `P`{.Agda} and one proof of `Q`{.Agda}. Unlike the general existential quantification above, no propositional truncation is needed. Since each component is already a proposition, any two first components are equal and any two second components are equal, so the two pairs are equal; this is exactly the closure property `isProp×`{.Agda}. The conjunction therefore remains a proposition while retaining both of its proofs, and its universe level is the maximum of the two input levels.
<!--zh-->
Σ 构造相应的不带依赖的特例是合取。对命题 `P`{.Agda} 与 `Q`{.Agda}，`P ⊓ Q`{.Agda} 的证明就是一对资料，分别包含 `P`{.Agda} 与 `Q`{.Agda} 的证明。与上面的存在量化不同，这里不需要命题截断。因为两个分量本来都是命题，任意两个第一分量彼此相等，任意两个第二分量也彼此相等，所以两对资料必定相等；这正是 `isProp×`{.Agda} 所表达的封闭性。因此，合取可以保留两边的证明而仍为命题，其宇宙层级取两个输入层级的最大值。
<!--ja-->
Σ 構成に対応する依存しない特別な場合が連言である。命題 `P`{.Agda} と `Q`{.Agda} に対して、`P ⊓ Q`{.Agda} の証明は、`P`{.Agda} の証明と `Q`{.Agda} の証明を一つずつ収めた対である。上の一般的な存在量化とは異なり、ここでは命題的切り詰めは不要である。各成分がすでに命題なので、二つの第一成分は等しく、二つの第二成分も等しくなり、したがって二つの対も等しくなる。これが `isProp×`{.Agda} の表す閉性である。連言は両方の証明を保持したまま命題であり、その宇宙レベルは二つの入力レベルの最大値になる。
<!--/-->

```agda
open import Cubical.Functions.Logic public using ( _⊓_ )
```

<!--en-->
#### Disjunction
<!--zh-->
#### 析取
<!--ja-->
#### 選言
<!--/-->

<!--en-->
The other binary operation is disjunction, `P ⊔ Q`{.Agda}. Before truncation, its evidence has the sum type introduced above: `inl p`{.Agda} records a proof `p`{.Agda} of `P`{.Agda}, while `inr q`{.Agda} records a proof `q`{.Agda} of `Q`{.Agda}. Even when `P`{.Agda} and `Q`{.Agda} are propositions, this sum need not be a proposition. If both sides hold, its left and right constructors still record distinguishable choices. Disjunction therefore applies propositional truncation to the sum. It forgets the chosen constructor and the proof carried by it, retaining only that at least one side holds. The truncation is what makes disjunction proposition-valued.
<!--zh-->
另一个二元运算是析取 `P ⊔ Q`{.Agda}。在截断之前，它的证据就是前文介绍的和类型：`inl p`{.Agda} 记录 `P`{.Agda} 的证明 `p`{.Agda}，`inr q`{.Agda} 记录 `Q`{.Agda} 的证明 `q`{.Agda}。即使 `P`{.Agda} 与 `Q`{.Agda} 都是命题，这个和类型也未必是命题；当两边都成立时，左右两个构造子仍然记录着可区分的选择。因此，析取要对这个和类型作命题截断，忘掉所选构造子及其中携带的证明，只保留「至少一边成立」。正是这一步截断使析取仍然取值于命题。
<!--ja-->
もう一つの二項演算が選言 `P ⊔ Q`{.Agda} である。切り詰める前の証拠は、先に導入した直和型である。`inl p`{.Agda} は `P`{.Agda} の証明 `p`{.Agda} を、`inr q`{.Agda} は `Q`{.Agda} の証明 `q`{.Agda} を記録する。`P`{.Agda} と `Q`{.Agda} がともに命題でも、この直和型は命題とは限らない。両方が成り立つとき、左右の構成子はなお区別できる選択を記録するからである。そこで選言はこの直和型を命題的に切り詰め、選ばれた構成子とその証明を忘れ、少なくとも一方が成り立つことだけを残す。この切り詰めによって、選言は命題値になる。
<!--/-->

```agda
open import Cubical.Functions.Logic public using ( _⊔_ )
```

<!--en-->
### [Classes]{.term-intro #class} and membership
<!--zh-->
### [类]{.term-intro #class}与成员关系
<!--ja-->
### [クラス]{.term-intro #class}と所属関係
<!--/-->

<!--en-->
A proposition that depends on an object can select exactly those objects for which it holds. In set theory, a collection determined in this way by a property is called a class.

Here **class** means a class in the sense of set theory, not a type in type theory. Throughout this book, *class* refers to the former and *type* to the latter. The two are closely related in the formalization, but they are not the same notion. A type determines which terms may be its elements; a class selects, by a property, the objects that satisfy it from an already specified type.

This collection of objects under consideration is the class's **[domain]{.term-intro #domain}**. When it is written `A`{.Agda}, the domain is a type `A`{.Agda} whose elements are all the objects currently being classified. Calling `A`{.Agda} a domain says only that a variable `x : A`{.Agda} may range over these objects; it does not equip `A`{.Agda} with membership, operations or any other structure. Later, when we construct a model of set theory, we add a set-theoretic membership relation to `A`{.Agda}. It then also becomes the [carrier]{.term-intro #carrier} of the model, and its elements play the role of sets in that model.

A class over a domain `A`{.Agda} is represented by a function:

<div class="single-line-code"><code>`M : A → hProp ℓ`{.Agda}</code></div>

For each `x : A`{.Agda}, the proposition `M x`{.Agda} says that `x`{.Agda} has the property specified by the class `M`{.Agda}. Thus `M`{.Agda} does not send `x`{.Agda} to another object that is collected somewhere. It assigns a proposition to each `x`{.Agda}, and the objects satisfying that proposition are precisely the objects belonging to the class.

This explains why we can discuss classes before introducing sets. A class here is a predicate defined in the metatheory. It requires only a domain and the universe of propositions; it neither presupposes that sets have been defined in the object theory nor asserts that the class itself is a set. Once later chapters equip the domain with a set-theoretic structure, such classes can describe the sets in the model that satisfy a chosen property.

Class membership is written `x ∈ᶜ M`{.Agda} and read "`x`{.Agda} belongs to the class `M`{.Agda}". Its meaning is the proposition that `M`{.Agda} assigns to `x`{.Agda}:

<div class="single-line-code"><code>`x ∈ᶜ M  :=  ⟨ M x ⟩`{.Agda}</code></div>

To prove `x ∈ᶜ M`{.Agda} is therefore to construct a proof of `⟨ M x ⟩`{.Agda}. The superscript `ᶜ`{.Agda} marks this as class membership. It distinguishes this host-level predicate from the membership relation between sets that later chapters interpret in a model of set theory: the former says whether an object satisfies a property, whereas the latter is a relation in the object language.
<!--zh-->
一个随对象变化的命题，可以从给定的一批对象中挑出恰好使它成立的对象。集合论把这种由性质划定的对象范围称为类。

这里的「类」是集合论中的 **class**，不是类型论中的 **type**。本书以后约定：**类**专指 class，**类型**专指 type。二者在形式化中关系密切，但不是同一个概念。类型规定哪些项可以作为它的元素；类则在已经给定的一批对象中，用一个性质挑出满足它的对象。

类所考察的这批对象称为它的**[论域]{.term-intro #domain}**。写作 `A`{.Agda} 时，论域就是一个类型 `A`{.Agda}，它的元素是当前接受分类的全部对象。称 `A`{.Agda} 为论域，只说明变量 `x : A`{.Agda} 可以在这些对象中取值，并不表示 `A`{.Agda} 已经具有成员关系、运算或其他结构。后文构造集合论模型时，我们会在 `A`{.Agda} 上加入集合论的成员关系；此时，`A`{.Agda} 也将成为该模型的[载体]{.term-intro #carrier}，它的元素则充当模型中的集合。

论域 `A`{.Agda} 上的类由一个函数表示：

<div class="single-line-code"><code>`M : A → hProp ℓ`{.Agda}</code></div>

对于每个 `x : A`{.Agda}，命题 `M x`{.Agda} 表示「`x`{.Agda} 具有类 `M`{.Agda} 所规定的性质」。因此，`M`{.Agda} 并不是把 `x`{.Agda} 送到另一个被收集起来的对象，而是为每个 `x`{.Agda} 给出一个关于它的命题。满足这个命题的对象，正是属于该类的对象。

这也解释了为什么我们还没有引入集合，就已经可以讨论类。此处的类是在元理论中定义的谓词，只需要一个论域和命题宇宙，并不需要先在对象理论中定义集合，也不声称这个类本身是一个集合。等到后文在这个论域上加入集合论结构以后，我们便可以用这种类描述模型中满足某项性质的集合。

类的成员关系写作 `x ∈ᶜ M`{.Agda}，读作「`x`{.Agda} 属于类 `M`{.Agda}」。它的含义就是 `M`{.Agda} 为 `x`{.Agda} 指定的命题：

<div class="single-line-code"><code>`x ∈ᶜ M  :=  ⟨ M x ⟩`{.Agda}</code></div>

因此，证明 `x ∈ᶜ M`{.Agda}，就是构造命题 `⟨ M x ⟩`{.Agda} 的证明。上标 `ᶜ`{.Agda} 表明这里使用的是类的成员关系。它将这个宿主层谓词与后文在集合论模型中解释的集合成员关系区分开来：前者说明一个对象是否满足某项性质，后者则是对象理论语言中的关系。
<!--ja-->
対象に依存する命題を使うと、与えられた対象のうち、その命題が成り立つものだけを選び出せる。集合論では、このように性質によって定められる対象の範囲をクラスと呼ぶ。

ここでいう**クラス**は集合論における class であり、型理論における type ではない。本書では以後、前者を**クラス**、後者を**型**と呼び分ける。形式化の中で両者は密接に関係するが、同じ概念ではない。型はどの項がその要素になれるかを定め、クラスは、すでに与えられた対象の中から、ある性質を満たすものを選び出す。

クラスが考察する対象の範囲を、そのクラスの**[論域]{.term-intro #domain}**と呼ぶ。`A`{.Agda} と書くとき、論域は型 `A`{.Agda} であり、その要素が現在分類されるすべての対象である。`A`{.Agda} を論域と呼ぶことは、変数 `x : A`{.Agda} がこれらの対象を動くということだけを表し、`A`{.Agda} に所属関係や演算などの構造がすでに備わっていることを意味しない。後に集合論のモデルを構成するとき、`A`{.Agda} に集合論的な所属関係を加える。そのとき `A`{.Agda} はモデルの[台]{.term-intro #carrier}にもなり、その要素がモデル内の集合の役割を果たす。

論域 `A`{.Agda} 上のクラスは関数で表される。

<div class="single-line-code"><code>`M : A → hProp ℓ`{.Agda}</code></div>

各 `x : A`{.Agda} に対して、命題 `M x`{.Agda} は「`x`{.Agda} がクラス `M`{.Agda} の定める性質を持つ」ことを表す。したがって `M`{.Agda} は、`x`{.Agda} をどこかに集められた別の対象へ送るのではない。各 `x`{.Agda} に命題を割り当て、その命題を満たす対象が、まさにそのクラスに属する対象である。

これにより、集合をまだ導入していない段階でクラスを論じられる理由も分かる。ここでのクラスはメタ理論で定義される述語であり、必要なのは論域と命題の宇宙だけである。対象理論で集合がすでに定義されていることを前提とせず、クラス自身が集合であるとも主張しない。後にこの論域へ集合論の構造を加えれば、このようなクラスを使って、モデル内である性質を満たす集合を記述できる。

クラスへの所属を `x ∈ᶜ M`{.Agda} と書き、「`x`{.Agda} はクラス `M`{.Agda} に属する」と読む。その意味は、`M`{.Agda} が `x`{.Agda} に割り当てる命題である。

<div class="single-line-code"><code>`x ∈ᶜ M  :=  ⟨ M x ⟩`{.Agda}</code></div>

したがって `x ∈ᶜ M`{.Agda} を証明することは、命題 `⟨ M x ⟩`{.Agda} の証明を構成することである。上付きの `ᶜ`{.Agda} は、ここでクラスへの所属を使っていることを示す。これはホストレベルの述語を、後に集合論のモデルで解釈する集合間の所属関係から区別する。前者は対象がある性質を満たすかを述べ、後者は対象言語の関係である。
<!--/-->

```agda
open import Cubical.Foundations.Powerset public
  using () renaming ( _∈_ to _∈ᶜ_ )
```

<!--en-->
## More inductive types

The remaining basic data types illustrate several forms of induction. A decision records evidence for one of two answers, Booleans provide two bare labels, natural numbers support recursion, and the indexed families `Fin`{.Agda} and `Vec`{.Agda} record numerical bounds in their types.
<!--zh-->
## 更多归纳类型

余下的基础数据类型展示了几种归纳构造：判定为两个答案之一保存证据，布尔类型提供两个不携带数据的标签，自然数支持递归，而带索引的族 `Fin`{.Agda} 与 `Vec`{.Agda} 则把数值界限记录在类型中。
<!--ja-->
## その他の帰納型

残る基本的なデータ型は、帰納的構成のいくつかの形を示す。判定は二つの答えの一方について証拠を記録し、ブール型はデータを伴わない二つのラベルを与え、自然数は再帰を支え、添字付き族 `Fin`{.Agda} と `Vec`{.Agda} は数値的な境界を型に記録する。
<!--/-->

<!--en-->
### Decidability

To decide a type `A`{.Agda} is to give evidence that determines whether `A`{.Agda} has an inhabitant. A positive answer carries an inhabitant `a : A`{.Agda}; a negative answer carries a refutation `n : A → ⊥₀`{.Agda}, showing that any proposed inhabitant would lead to impossibility. The inductive type `Dec A`{.Agda} packages exactly these two answers. Its constructors obey the rules

$$\frac{a:A}{\mathsf{yes}\,a:\operatorname{Dec}(A)}\qquad\frac{n:A\to\bot_{0}}{\mathsf{no}\,n:\operatorname{Dec}(A)}$$

Thus `yes a`{.Agda} records the positive answer together with its witness, while `no n`{.Agda} records the negative answer together with its refutation. Unlike propositional disjunction, `Dec A`{.Agda} is not truncated: a program may inspect which constructor was returned and use the evidence it carries. Constructing a decision for a particular finite comparison can be entirely constructive. The classical principle introduced in a later chapter is stronger because it supplies such a decision uniformly for every proposition at a chosen universe level.

For an arbitrary type `A`{.Agda}, `Dec A`{.Agda} need not be a proposition: two positive decisions can carry distinguishable inhabitants of `A`{.Agda}. If `A`{.Agda} is a proposition, however, `isPropDec`{.Agda} proves that its decisions are propositions too. Positive witnesses are then equal, negative answers are equal because refutations are proposition-valued, and a positive answer cannot coexist with a negative one.

<!--zh-->
### 可判定性

判定类型 `A`{.Agda}，就是给出足以确定 `A`{.Agda} 是否有元素的证据。肯定回答携带元素 `a : A`{.Agda}；否定回答携带反驳 `n : A → ⊥₀`{.Agda}，说明任何声称属于 `A`{.Agda} 的元素都会导出不可能性。归纳类型 `Dec A`{.Agda} 恰好把这两种回答作为两个构造子，其构造规则为

$$\frac{a:A}{\mathsf{yes}\,a:\operatorname{Dec}(A)}\qquad\frac{n:A\to\bot_{0}}{\mathsf{no}\,n:\operatorname{Dec}(A)}$$

因此，`yes a`{.Agda} 记录肯定回答及其见证，`no n`{.Agda} 则记录否定回答及其反驳。与命题析取不同，`Dec A`{.Agda} 不作命题截断：程序可以检查返回了哪个构造子，并使用它携带的证据。对某项有限比较作出判定，完全可以是构造主义的。将在后面的章节中引入的经典原理则更强：它为指定宇宙层级上的每个命题一致地给出这种判定。

对任意类型 `A`{.Agda} 而言，`Dec A`{.Agda} 未必是命题：两项肯定判定可能携带 `A`{.Agda} 中可区分的元素。但若 `A`{.Agda} 是命题，`isPropDec`{.Agda} 便证明它的判定也是命题。此时，肯定答案所携带的见证彼此相等；否定答案因反驳具有命题性而彼此相等；一肯定一否定则不能并存。

<!--ja-->
### 判定可能性

型 `A`{.Agda} を判定するとは、`A`{.Agda} に要素があるかどうかを確定する証拠を与えることである。肯定的な答えは要素 `a : A`{.Agda} を運び、否定的な答えは反証 `n : A → ⊥₀`{.Agda} を運ぶ。後者は、`A`{.Agda} の要素を仮定すれば不可能性が導かれることを示す。帰納型 `Dec A`{.Agda} は、ちょうどこの二つの答えを構成子としてまとめる。構成規則は次のとおりである。

$$\frac{a:A}{\mathsf{yes}\,a:\operatorname{Dec}(A)}\qquad\frac{n:A\to\bot_{0}}{\mathsf{no}\,n:\operatorname{Dec}(A)}$$

したがって `yes a`{.Agda} は肯定的な答えとその証人を記録し、`no n`{.Agda} は否定的な答えとその反証を記録する。命題的な選言と異なり、`Dec A`{.Agda} は切り詰められない。プログラムは返された構成子を調べ、それが運ぶ証拠を使える。有限な比較の判定は、完全に構成的に作れる。後の章で導入する古典原理がより強いのは、指定した宇宙レベルのすべての命題に、このような判定を一様に与えるからである。

任意の型 `A`{.Agda} に対して、`Dec A`{.Agda} が命題とは限らない。二つの肯定的な判定が、`A`{.Agda} の区別できる元を運びうるからである。しかし `A`{.Agda} が命題なら、`isPropDec`{.Agda} はその判定も命題であることを示す。そのとき、肯定的な答えが運ぶ証人は等しく、否定的な答えは反証が命題値であるため等しく、肯定と否定は同時に成り立たない。

<!--/-->

```agda
open import Cubical.Relation.Nullary public
  using ( Dec; yes; no; isPropDec )
```

<!--en-->
An existing decision can also be converted. To obtain `Dec B`{.Agda} from `Dec A`{.Agda}, we need a function `f : A → B`{.Agda} for the positive case and a function `g : (A → ⊥₀) → (B → ⊥₀)`{.Agda} for the negative case. Then `mapDec f g`{.Agda} performs the conversion: it sends `yes a`{.Agda} to `yes (f a)`{.Agda} and `no n`{.Agda} to `no (g n)`{.Agda}. The positive function alone is insufficient, since a refutation of `A`{.Agda} does not in general refute `B`{.Agda}. A function `r : B → A`{.Agda} supplies the missing negative conversion as `λ n b → n (r b)`{.Agda}.
<!--zh-->
已有的判定也可以转换。要从 `Dec A`{.Agda} 得到 `Dec B`{.Agda}，需要用函数 `f : A → B`{.Agda} 处理肯定情形，并用函数 `g : (A → ⊥₀) → (B → ⊥₀)`{.Agda} 处理否定情形。于是 `mapDec f g`{.Agda} 完成转换：把 `yes a`{.Agda} 送到 `yes (f a)`{.Agda}，把 `no n`{.Agda} 送到 `no (g n)`{.Agda}。只有肯定方向的函数还不够，因为对 `A`{.Agda} 的反驳一般不能反驳 `B`{.Agda}。若另有函数 `r : B → A`{.Agda}，便可用 `λ n b → n (r b)`{.Agda} 补足否定方向。
<!--ja-->
すでに得た判定を変換することもできる。`Dec A`{.Agda} から `Dec B`{.Agda} を得るには、肯定の場合を扱う関数 `f : A → B`{.Agda} と、否定の場合を扱う関数 `g : (A → ⊥₀) → (B → ⊥₀)`{.Agda} が必要になる。`mapDec f g`{.Agda} はこの変換を行い、`yes a`{.Agda} を `yes (f a)`{.Agda} に、`no n`{.Agda} を `no (g n)`{.Agda} に送る。`A`{.Agda} の反証から一般に `B`{.Agda} の反証が得られるわけではないので、肯定側の関数だけでは足りない。関数 `r : B → A`{.Agda} もあれば、`λ n b → n (r b)`{.Agda} を否定側の変換に使える。
<!--/-->

```agda
open import Cubical.Relation.Nullary public using ( mapDec )
```

<!--en-->
### Booleans

The inductive type `Bool`{.Agda} has exactly two constructors, `true`{.Agda} and `false`{.Agda}. Unlike the constructors of a general sum, neither constructor carries further data. Their construction rules are

$$\frac{}{\mathsf{true}:\operatorname{Bool}}\qquad\frac{}{\mathsf{false}:\operatorname{Bool}}$$

Consequently, defining a function out of `Bool`{.Agda} amounts to giving one result for `true`{.Agda} and one for `false`{.Agda}. Booleans are useful when a computation must return one of two distinguishable labels, as in a finite test or a mask. They should not be confused with the propositions truth and falsity introduced above: `true`{.Agda} and `false`{.Agda} are two values of the ordinary data type `Bool`{.Agda}, rather than proofs of propositions.
<!--zh-->
### 布尔类型

归纳类型 `Bool`{.Agda} 恰有两个构造子：`true`{.Agda} 与 `false`{.Agda}。与一般和类型的构造子不同，这两个构造子都不携带额外数据。其构造规则为

$$\frac{}{\mathsf{true}:\operatorname{Bool}}\qquad\frac{}{\mathsf{false}:\operatorname{Bool}}$$

因此，要定义一个以 `Bool`{.Agda} 为输入的函数，只需分别给出输入为 `true`{.Agda} 和 `false`{.Agda} 时的结果。当计算需要返回两个可区分的标签之一时，例如有限测试或掩码，布尔值便很有用。它们不应与上文引入的真命题和假命题混淆：`true`{.Agda} 与 `false`{.Agda} 是普通数据类型 `Bool`{.Agda} 的两个值，而不是命题的证明。
<!--ja-->
### ブール型

帰納型 `Bool`{.Agda} は、ちょうど二つの構成子 `true`{.Agda} と `false`{.Agda} をもつ。一般の直和型の構成子と異なり、どちらも追加のデータを運ばない。構成規則は次のとおりである。

$$\frac{}{\mathsf{true}:\operatorname{Bool}}\qquad\frac{}{\mathsf{false}:\operatorname{Bool}}$$

したがって `Bool`{.Agda} からの関数を定めるには、`true`{.Agda} の場合と `false`{.Agda} の場合の結果を一つずつ与えればよい。ブール値は、有限な判定やマスクのように、計算が区別できる二つのラベルの一方を返すときに役立つ。上で導入した真と偽の命題とは区別しなければならない。`true`{.Agda} と `false`{.Agda} は通常のデータ型 `Bool`{.Agda} の二つの値であり、命題の証明ではない。
<!--/-->

```agda
open import Cubical.Data.Bool public using ( Bool; true; false )
```

<!--en-->
### Natural numbers
<!--zh-->
### 自然数
<!--ja-->
### 自然数
<!--/-->

<!--en-->
The natural numbers `ℕ`{.Agda} form an inductive type generated by two constructors. The constructor `zero`{.Agda} is an element of `ℕ`{.Agda}; the constructor `suc`{.Agda} takes any `n : ℕ`{.Agda} to another element `suc n : ℕ`{.Agda}. The rules are

$$\frac{}{\mathsf{zero}:\mathbb{N}}\qquad\frac{n:\mathbb{N}}{\mathsf{suc}\,n:\mathbb{N}}$$

Every element of `ℕ`{.Agda} is generated from these constructors. Its induction principle accordingly has a case for `zero`{.Agda} and a step that passes from `n`{.Agda} to `suc n`{.Agda}.
<!--zh-->
自然数 `ℕ`{.Agda} 是由两个构造子生成的归纳类型。构造子 `zero`{.Agda} 是 `ℕ`{.Agda} 的元素；构造子 `suc`{.Agda} 把任意 `n : ℕ`{.Agda} 变为另一个元素 `suc n : ℕ`{.Agda}。构造规则为

$$\frac{}{\mathsf{zero}:\mathbb{N}}\qquad\frac{n:\mathbb{N}}{\mathsf{suc}\,n:\mathbb{N}}$$

`ℕ`{.Agda} 的每个元素都由这两个构造子生成。相应的归纳原理包含 `zero`{.Agda} 情形，以及从 `n`{.Agda} 过渡到 `suc n`{.Agda} 的归纳步骤。
<!--ja-->
自然数 `ℕ`{.Agda} は、二つの構成子から生成される帰納型である。構成子 `zero`{.Agda} は `ℕ`{.Agda} の要素であり、構成子 `suc`{.Agda} は任意の `n : ℕ`{.Agda} から別の要素 `suc n : ℕ`{.Agda} を作る。構成規則は次のとおりである。

$$\frac{}{\mathsf{zero}:\mathbb{N}}\qquad\frac{n:\mathbb{N}}{\mathsf{suc}\,n:\mathbb{N}}$$

`ℕ`{.Agda} のすべての要素は、この二つの構成子から生成される。対応する帰納原理は、`zero`{.Agda} の場合と、`n`{.Agda} から `suc n`{.Agda} へ進む帰納段階からなる。
<!--/-->

<!--en-->
To define a function from `ℕ`{.Agda} by recursion, it is therefore enough to give its value at `zero`{.Agda} and to give the value at `suc n`{.Agda} from the value already obtained at `n`{.Agda}.

Addition `_+_`{.Agda} combines two natural-number sizes and is used throughout the syntax chapters to compute the number of available variables after contexts are extended or combined.

$$\mathord{+}:\mathbb N\to\mathbb N\to\mathbb N$$

$$m+n=
\begin{cases}
n, & m=0,\\
\operatorname{suc}(m'+n), & m=\operatorname{suc}(m')
\end{cases}$$
<!--zh-->
因此，要递归定义从 `ℕ`{.Agda} 出发的函数，只需给出函数在 `zero`{.Agda} 处的值，并说明如何由已经得到的 `n`{.Agda} 处之值构造 `suc n`{.Agda} 处之值。

加法 `_+_`{.Agda} 合并两个自然数大小；在后续句法章节中，扩张或拼接语境时可用它计算可用变元的数量。

$$\mathord{+}:\mathbb N\to\mathbb N\to\mathbb N$$

$$m+n=
\begin{cases}
n, & m=0,\\
\operatorname{suc}(m'+n), & m=\operatorname{suc}(m')
\end{cases}$$
<!--ja-->
したがって、`ℕ`{.Agda} からの関数を再帰的に定義するには、`zero`{.Agda} での値と、すでに得られた `n`{.Agda} での値から `suc n`{.Agda} での値を作る方法を与えれば十分である。

加法 `_+_`{.Agda} は二つの自然数の大きさを合わせる。後の構文の章では、文脈を拡張したり連結したりした後に使える変数の個数を計算するために用いる。

$$\mathord{+}:\mathbb N\to\mathbb N\to\mathbb N$$

$$m+n=
\begin{cases}
n, & m=0,\\
\operatorname{suc}(m'+n), & m=\operatorname{suc}(m')
\end{cases}$$
<!--/-->

```agda
open import Cubical.Data.Nat public
  using ( ℕ; zero; suc; _+_ )
```

<!--en-->
### Finite indices
<!--zh-->
### 有限数
<!--ja-->
### 有限添字
<!--/-->

<!--en-->
`Fin`{.Agda} is a family of types indexed by natural numbers. The type `Fin zero`{.Agda} has no constructors. At an index `suc n`{.Agda}, the constructor `zero`{.Agda} gives an element directly, while `suc`{.Agda} sends each element of `Fin n`{.Agda} to an element of `Fin (suc n)`{.Agda}. These constructors obey the rules

$$\frac{}{\mathsf{zero}:\operatorname{Fin}(\operatorname{suc}\,n)}\qquad\frac{i:\operatorname{Fin}(n)}{\mathsf{suc}\,i:\operatorname{Fin}(\operatorname{suc}\,n)}$$

Consequently `Fin n`{.Agda} has exactly `n`{.Agda} elements: none when `n`{.Agda} is `zero`{.Agda}, and one new element together with a copy of every element of `Fin n`{.Agda} when the index is `suc n`{.Agda}.

The function `toℕ`{.Agda} forgets the bound and reads a finite index as a natural number. This forgetful map preserves the numerical position while its result no longer carries the bound in its type.

$$\operatorname{to\mathbb N}:\operatorname{Fin}(n)\to\mathbb N$$

$$\operatorname{to\mathbb N}(i)=
\begin{cases}
0, & i=\mathsf{zero},\\
\operatorname{suc}(\operatorname{to\mathbb N}(j)), & i=\mathsf{suc}\,j
\end{cases}$$
<!--zh-->
`Fin`{.Agda} 是以自然数为索引的一族类型。`Fin zero`{.Agda} 没有构造子；当索引为 `suc n`{.Agda} 时，构造子 `zero`{.Agda} 直接给出一个元素，而 `suc`{.Agda} 把 `Fin n`{.Agda} 的每个元素变为 `Fin (suc n)`{.Agda} 的元素。构造规则为

$$\frac{}{\mathsf{zero}:\operatorname{Fin}(\operatorname{suc}\,n)}\qquad\frac{i:\operatorname{Fin}(n)}{\mathsf{suc}\,i:\operatorname{Fin}(\operatorname{suc}\,n)}$$

因此，`Fin n`{.Agda} 恰有 `n`{.Agda} 个元素：索引为 `zero`{.Agda} 时没有元素；索引由 `n`{.Agda} 变为 `suc n`{.Agda} 时，新增一个元素，并保留由 `Fin n`{.Agda} 的每个元素经 `suc`{.Agda} 构造出的元素。

函数 `toℕ`{.Agda} 忘去界限，把有限索引读作自然数。这个遗忘映射保留索引的数值位置，但结果的类型不再记录原来的界限。

$$\operatorname{to\mathbb N}:\operatorname{Fin}(n)\to\mathbb N$$

$$\operatorname{to\mathbb N}(i)=
\begin{cases}
0, & i=\mathsf{zero},\\
\operatorname{suc}(\operatorname{to\mathbb N}(j)), & i=\mathsf{suc}\,j
\end{cases}$$
<!--ja-->
`Fin`{.Agda} は自然数を添字とする型の族である。`Fin zero`{.Agda} には構成子がない。添字が `suc n`{.Agda} のとき、構成子 `zero`{.Agda} が一つの要素を直接与え、`suc`{.Agda} は `Fin n`{.Agda} の各要素を `Fin (suc n)`{.Agda} の要素へ送る。構成規則は次のとおりである。

$$\frac{}{\mathsf{zero}:\operatorname{Fin}(\operatorname{suc}\,n)}\qquad\frac{i:\operatorname{Fin}(n)}{\mathsf{suc}\,i:\operatorname{Fin}(\operatorname{suc}\,n)}$$

したがって `Fin n`{.Agda} はちょうど `n`{.Agda} 個の要素をもつ。添字が `zero`{.Agda} のとき要素はなく、`n`{.Agda} から `suc n`{.Agda} へ移ると、一つの新しい要素と、`Fin n`{.Agda} の各要素から `suc`{.Agda} で作られる要素が得られる。

関数 `toℕ`{.Agda} は上界を忘れ、有限添字を自然数として読む。この忘却写像は数としての位置を保つが、結果の型には元の上界が記録されない。

$$\operatorname{to\mathbb N}:\operatorname{Fin}(n)\to\mathbb N$$

$$\operatorname{to\mathbb N}(i)=
\begin{cases}
0, & i=\mathsf{zero},\\
\operatorname{suc}(\operatorname{to\mathbb N}(j)), & i=\mathsf{suc}\,j
\end{cases}$$
<!--/-->

```agda
open import Cubical.Data.FinData public
  using ( Fin; zero; suc; toℕ )
```

<!--en-->
### Vectors
<!--zh-->
### 向量
<!--ja-->
### ベクトル
<!--/-->

<!--en-->
A vector `Vec A n`{.Agda} is a list of elements of `A`{.Agda} whose length is part of its type. Its two constructors are expressed by the rules

$$\frac{}{[]:\operatorname{Vec}(A,0)}\qquad\frac{a:A\quad v:\operatorname{Vec}(A,n)}{a∷v:\operatorname{Vec}(A,\operatorname{suc}\,n)}$$

The constructor `[]`{.Agda} produces an element of `Vec A zero`{.Agda}. Given `a : A`{.Agda} and `v : Vec A n`{.Agda}, the constructor `_∷_`{.Agda} produces `a ∷ v : Vec A (suc n)`{.Agda}. Thus the natural-number index is determined together with the vector. The function `lookup`{.Agda} has type `Fin n → Vec A n → A`{.Agda}; its shared index requires its two arguments to have the same `n`{.Agda}.

These indices make the standard vector operations carry useful guarantees. An out-of-range `lookup`{.Agda} cannot be stated because its index must inhabit `Fin n`{.Agda}.

$$\operatorname{lookup}:\operatorname{Fin}(n)\to\operatorname{Vec}(A,n)\to A$$

$$\operatorname{lookup}(i,a\mathbin{∷}v)=
\begin{cases}
a, & i=\mathsf{zero},\\
\operatorname{lookup}(j,v), & i=\mathsf{suc}\,j
\end{cases}$$
<!--zh-->
向量 `Vec A n`{.Agda} 是由 `A`{.Agda} 的元素组成、且长度写入类型的列表。它的两个构造规则可以写成

$$\frac{}{[]:\operatorname{Vec}(A,0)}\qquad\frac{a:A\quad v:\operatorname{Vec}(A,n)}{a∷v:\operatorname{Vec}(A,\operatorname{suc}\,n)}$$

构造子 `[]`{.Agda} 给出 `Vec A zero`{.Agda} 的元素。给定 `a : A`{.Agda} 和 `v : Vec A n`{.Agda}，构造子 `_∷_`{.Agda} 给出 `a ∷ v : Vec A (suc n)`{.Agda}。自然数索引由此与向量一同确定。函数 `lookup`{.Agda} 的类型是 `Fin n → Vec A n → A`{.Agda}；两个参数共享同一个索引 `n`{.Agda}。

这些索引使常用的向量操作自带有用的保证。`lookup`{.Agda} 的索引必须属于 `Fin n`{.Agda}，所以越界访问根本无法写出。

$$\operatorname{lookup}:\operatorname{Fin}(n)\to\operatorname{Vec}(A,n)\to A$$

$$\operatorname{lookup}(i,a\mathbin{∷}v)=
\begin{cases}
a, & i=\mathsf{zero},\\
\operatorname{lookup}(j,v), & i=\mathsf{suc}\,j
\end{cases}$$
<!--ja-->
ベクトル `Vec A n`{.Agda} は `A`{.Agda} の元からなるリストで、その長さが型の一部になっている。その二つの構成子は、次の推論式で表せる。

$$\frac{}{[]:\operatorname{Vec}(A,0)}\qquad\frac{a:A\quad v:\operatorname{Vec}(A,n)}{a∷v:\operatorname{Vec}(A,\operatorname{suc}\,n)}$$

構成子 `[]`{.Agda} は `Vec A zero`{.Agda} の要素を与える。`a : A`{.Agda} と `v : Vec A n`{.Agda} が与えられると、構成子 `_∷_`{.Agda} は `a ∷ v : Vec A (suc n)`{.Agda} を与える。このように自然数の添字はベクトルとともに定まる。関数 `lookup`{.Agda} の型は `Fin n → Vec A n → A`{.Agda} であり、二つの引数は同じ添字 `n`{.Agda} を共有する。

これらの添字により、標準的なベクトル操作そのものが有用な保証を伴う。`lookup`{.Agda} の添字は `Fin n`{.Agda} の元でなければならないため、範囲外の参照はそもそも記述できない。

$$\operatorname{lookup}:\operatorname{Fin}(n)\to\operatorname{Vec}(A,n)\to A$$

$$\operatorname{lookup}(i,a\mathbin{∷}v)=
\begin{cases}
a, & i=\mathsf{zero},\\
\operatorname{lookup}(j,v), & i=\mathsf{suc}\,j
\end{cases}$$
<!--/-->

<!--en-->
For the length-three vector in the figure below, the labels $0,1,2$ abbreviate the `Fin 3`{.Agda} constructors `zero`{.Agda}, `suc zero`{.Agda}, and `suc (suc zero)`{.Agda}.
<!--zh-->
下面取一个长度为三的向量；图中的 $0,1,2$ 分别简写 `Fin 3`{.Agda} 的构造子 `zero`{.Agda}、`suc zero`{.Agda}、`suc (suc zero)`{.Agda}。
<!--ja-->
下図では長さ三のベクトルを取る。図中の $0,1,2$ は `Fin 3`{.Agda} の構成子 `zero`{.Agda}、`suc zero`{.Agda}、`suc (suc zero)`{.Agda} の略記である。
<!--/-->

<figure class="book-diagram type-comparison path-figure" id="fig-fin-vector-lookup" aria-describedby="fig-fin-vector-lookup-caption">
<div class="diagram-framed">
<div class="diagram-indexed">

$$v=a\mathbin{∷}b\mathbin{∷}c\mathbin{∷}[]:\operatorname{Vec}(A,3)$$

<div class="vector-slots"><span>$a$</span><span>$b$</span><span>$c$</span></div>

$$i\mapsto\operatorname{lookup}\,i\,v$$

<div class="path-stage diagram-compact-stage" style="aspect-ratio:420/310">
<svg viewBox="0 0 420 310" aria-hidden="true" focusable="false">
<rect class="diagram-space-shape" x="15" y="15" width="390" height="90"/>
<rect class="diagram-space-shape" x="15" y="205" width="390" height="90"/>
<path class="diagram-map-line" d="M80 85 L80 251"/>
<path class="diagram-map-tip" d="M76 244 L80 251 L84 244"/>
<path class="diagram-map-line" d="M210 85 L210 251"/>
<path class="diagram-map-tip" d="M206 244 L210 251 L214 244"/>
<path class="diagram-map-line" d="M340 85 L340 251"/>
<path class="diagram-map-tip" d="M336 244 L340 251 L344 244"/>
<circle class="diagram-point" cx="80" cy="81" r="4"/>
<circle class="diagram-point" cx="210" cy="81" r="4"/>
<circle class="diagram-point" cx="340" cy="81" r="4"/>
<circle class="diagram-point" cx="80" cy="255" r="4"/>
<circle class="diagram-point" cx="210" cy="255" r="4"/>
<circle class="diagram-point" cx="340" cy="255" r="4"/>
</svg>
<span class="path-label" style="left:50%;top:12.5806%">$\operatorname{Fin}(3)$</span>
<span class="path-label" style="left:19.0476%;top:19.6774%">$0$</span>
<span class="path-label" style="left:50%;top:19.6774%">$1$</span>
<span class="path-label" style="left:80.9524%;top:19.6774%">$2$</span>
<span class="path-label" style="left:9.52381%;top:73.2258%">$A$</span>
<span class="path-label" style="left:19.0476%;top:89.6774%">$a$</span>
<span class="path-label" style="left:50%;top:89.6774%">$b$</span>
<span class="path-label" style="left:80.9524%;top:89.6774%">$c$</span>
</div>
</div>
</div>
<figcaption id="fig-fin-vector-lookup-caption">
<!--en-->
Each column follows one position through the vector, its index, and its lookup result. `Fin 3`{.Agda} provides exactly the three valid indices; the entries `a`{.Agda}, `b`{.Agda}, and `c`{.Agda} may coincide.
<!--zh-->
每一列对齐向量中的一个位置、它的索引和查找结果。`Fin 3`{.Agda} 恰好提供三个合法索引；分量 `a`{.Agda}、`b`{.Agda}、`c`{.Agda} 本身可以相同。
<!--ja-->
各列はベクトルの一つの位置、その添字、参照結果を揃えている。`Fin 3`{.Agda} が与えるのは三つの有効な添字だけであり、成分 `a`{.Agda}、`b`{.Agda}、`c`{.Agda} 自体は同じでもよい。
<!--/-->
</figcaption>
</figure>

<!--en-->
The function `map`{.Agda} applies one function to every entry without changing the length.

$$\operatorname{map}:(A\to B)\to\operatorname{Vec}(A,n)\to\operatorname{Vec}(B,n)$$

$$\operatorname{map}(f,v)=
\begin{cases}
[], & v=[],\\
f(a)\mathbin{∷}\operatorname{map}(f,w), & v=a\mathbin{∷}w
\end{cases}$$
<!--zh-->
函数 `map`{.Agda} 对每个分量应用同一个函数而不改变长度。

$$\operatorname{map}:(A\to B)\to\operatorname{Vec}(A,n)\to\operatorname{Vec}(B,n)$$

$$\operatorname{map}(f,v)=
\begin{cases}
[], & v=[],\\
f(a)\mathbin{∷}\operatorname{map}(f,w), & v=a\mathbin{∷}w
\end{cases}$$
<!--ja-->
関数 `map`{.Agda} は長さを変えずに各成分へ同じ関数を適用する。

$$\operatorname{map}:(A\to B)\to\operatorname{Vec}(A,n)\to\operatorname{Vec}(B,n)$$

$$\operatorname{map}(f,v)=
\begin{cases}
[], & v=[],\\
f(a)\mathbin{∷}\operatorname{map}(f,w), & v=a\mathbin{∷}w
\end{cases}$$
<!--/-->

```agda
open import Cubical.Data.Vec public
  using ( Vec; []; _∷_; lookup; map )
```

<!--en-->
## Recap

This chapter introduced the host-level vocabulary used throughout the book:

- `Type`{.Agda} and `Level`{.Agda} describe type universes and their levels;
- Π types represent dependent functions, Σ types represent dependent pairs, and sum types distinguish values constructed from either of two input types;
- record types flatten nested Σ types through named fields and constructors;
- `Lift`{.Agda} moves types between universe levels;
- path types represent equality; `transport`{.Agda}, `subst`{.Agda} and its two-argument generalization `subst2`{.Agda} move data along paths;
- homotopy levels describe the equality structure retained by a type, while propositionhood is preserved by Π types, Σ types and products; `Σ≡Prop`{.Agda} reduces equality of proof-carrying dependent pairs to equality of their first components;
- type equivalence `A ≃ B`{.Agda} means that every fibre of a map is contractible; `Iso`{.Agda} constructs it from explicit maps and round-trip laws, and the equivalence carries elements, paths and homotopy levels between types;
- `hProp`{.Agda} is the universe of propositions, `isSetHProp`{.Agda} describes its equality structure, and `⟨_⟩`{.Agda} extracts the statement of a proposition;
- propositional truncation `∥ A ∥₁`{.Agda} retains whether `A`{.Agda} is inhabited while forgetting its particular witness; `rec₁`{.Agda} eliminates it into propositions and `map₁`{.Agda} maps it to another truncation;
- truth and falsity, conjunction and disjunction, implication and negation, and universal and existential quantification provide the logical operations on the proposition universe; propositional extensionality turns implications in both directions into equality of propositions;
- a class is a predicate valued in the universe of propositions, and `_∈ᶜ_`{.Agda} expresses class membership;
- `Dec A`{.Agda} retains either an inhabitant of `A`{.Agda} or a refutation, while uniform decisions for arbitrary propositions require an additional principle;
- `Bool`{.Agda} is the two-element data type whose constructors `true`{.Agda} and `false`{.Agda} provide distinguishable computational labels;
- `ℕ`{.Agda} supplies natural numbers and addition, `Fin n`{.Agda} supplies indices below `n`{.Agda}, and `Vec A n`{.Agda} supplies length-indexed sequences with bounded lookup and length-preserving map;

Together these notions form the basic formal language adopted in this book.
<!--zh-->
## 小结

本章介绍了书中反复使用的宿主层基础词汇：

- `Type`{.Agda} 与 `Level`{.Agda} 描述类型宇宙及其层级；
- Π 类型表示依值函数，Σ 类型表示依值对，和类型区分由两个输入类型中哪一侧构造出的元素；
- 记录类型以具名字段和构造子展平多重嵌套的 Σ 类型；
- `Lift`{.Agda} 在宇宙层级之间搬移类型；
- 路径类型表示相等；`transport`{.Agda}、`subst`{.Agda} 及其双参数推广 `subst2`{.Agda} 沿路径搬移数据；
- 同伦层级描述类型保留的相等结构；命题性对 Π 类型、Σ 类型和积封闭，`Σ≡Prop`{.Agda} 把携带证明的依值对相等归结为第一分量相等；
- 类型等价 `A ≃ B`{.Agda} 表示一个映射的每束纤维可缩；`Iso`{.Agda} 通过显式映射与往返律构造它，所得等价在类型之间传递元素、路径与同伦层级；
- `hProp`{.Agda} 是命题宇宙，`isSetHProp`{.Agda} 描述其相等结构，`⟨_⟩`{.Agda} 取出命题的表述；
- 命题截断 `∥ A ∥₁`{.Agda} 保留 `A`{.Agda} 是否有元素，却忘去具体见证；`rec₁`{.Agda} 把它消去到命题，`map₁`{.Agda} 则把它映射到另一个截断；
- 真与假、合取与析取、蕴涵与否定、全称量化与存在量化，构成命题宇宙上的逻辑运算；命题外延性把两个方向的蕴涵变成命题相等；
- 类是取值于命题宇宙的谓词，`_∈ᶜ_`{.Agda} 表示类的成员关系；
- `Dec A`{.Agda} 保留 `A`{.Agda} 的一个元素或一份反驳；若要为任意命题一致地给出这种判定，则还需要额外原理；
- `Bool`{.Agda} 是二元素数据类型，其构造子 `true`{.Agda} 与 `false`{.Agda} 提供两个可区分的计算标签；
- `ℕ`{.Agda} 提供自然数及其加法，`Fin n`{.Agda} 提供小于 `n`{.Agda} 的索引，`Vec A n`{.Agda} 提供带长度索引、不会越界查找且映射后长度不变的序列；

这些概念共同组成了本书所采用的基本形式语言。
<!--ja-->
## まとめ

本章では、本書で用いるホストレベルの基礎語彙を導入した。

- `Type`{.Agda} と `Level`{.Agda} は型宇宙とそのレベルを記述する。
- Π 型は依存関数を、Σ 型は依存対を表し、直和型は二つの入力型のどちら側から構成された元かを区別する。
- レコード型は、名前付きフィールドと構成子によって、入れ子になった Σ 型を平坦に表す。
- `Lift`{.Agda} は型を宇宙レベル間で移す。
- パス型は等しさを表し、`transport`{.Agda}、`subst`{.Agda}、その二引数への一般化 `subst2`{.Agda} はパスに沿ってデータを移す。
- ホモトピーレベルは型に残る等しさの構造を記述する。命題性は Π 型、Σ 型、積について閉じ、`Σ≡Prop`{.Agda} は証明を携える依存対の等しさを第一成分の等しさへ帰着させる。
- 型同値 `A ≃ B`{.Agda} は写像の各ファイバーが可縮であることを表す。`Iso`{.Agda} は明示的な写像と往復則から同値を構成し、得られた同値が型の間で要素、パス、ホモトピーレベルを移す。
- `hProp`{.Agda} は命題の宇宙であり、`isSetHProp`{.Agda} はその等しさの構造を記述し、`⟨_⟩`{.Agda} は命題の記述を取り出す。
- 命題的切り詰め `∥ A ∥₁`{.Agda} は `A`{.Agda} に要素があるかを保ちつつ、具体的な証人を忘れる。`rec₁`{.Agda} はそれを命題へ除去し、`map₁`{.Agda} は別の切り詰めへ写す。
- 真と偽、連言と選言、含意と否定、全称量化と存在量化が、命題の宇宙における論理演算を与える。命題外延性は二方向の含意を命題の等しさへ変える。
- クラスは命題の宇宙に値をとる述語であり、`_∈ᶜ_`{.Agda} はクラスへの所属を表す。
- `Dec A`{.Agda} は `A`{.Agda} の元または反証のいずれかを保持する。任意の命題にこの判定を一様に与えるには、さらなる原理が必要である。
- `Bool`{.Agda} は二要素のデータ型であり、構成子 `true`{.Agda} と `false`{.Agda} が区別できる計算上のラベルを与える。
- `ℕ`{.Agda} は自然数と加法を、`Fin n`{.Agda} は `n`{.Agda} 未満の添字を、`Vec A n`{.Agda} は範囲外参照を許さず写像で長さを保つ長さ付き列を与える。

これらの概念が、本書で採用する基本的な形式言語を構成する。
<!--/-->
