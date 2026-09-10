<!--en-->
# Prelude

Set theory talks about sets, membership and functions; the language in which this book carries out that talk is cubical type theory. Before set theory proper can begin, the two languages need a shared working vocabulary, and this chapter builds it once so that every later chapter can simply use it. The vocabulary is best presented as a small mathematical story rather than a list, so we walk through it question by question, and later sections repeatedly lean on the notions fixed here.

The first question is size. Types are organised into universes `Type ℓ`{.Agda} graded by explicit levels, so every totality the book surveys, such as "all sets" or "all propositions", carries a level saying how large it is. The second question is equality. Here equality is the path type `_≡_`{.Agda}, and an equality proof is data rather than a verdict: the operations `refl`{.Agda}, `sym`{.Agda}, `_∙_`{.Agda}, `cong`{.Agda}, `transport`{.Agda} and `funExt`{.Agda} build and use such data. Building on equality, the third question asks how much equality structure a type carries: the predicates `isProp`{.Agda}, `isSet`{.Agda} and `isContr`{.Agda} measure this, and in particular `isContr`{.Agda} is the book's notion of unique existence. These three ingredients already determine the shape of the rest of the chapter. A truth value is a proposition packaged with its certificate, the type `hProp`{.Agda}; the projection `⟨_⟩`{.Agda} reads out the underlying proposition; and a class over a carrier `A` is a truth-valued predicate whose membership statement is precisely such a projection. Packaging reappears once more in its general form, the dependent pair `Σ`{.Agda}, which holds data together with data that depends on it. On the finite side, counts such as the number of free variables of a formula are recorded by the natural numbers `ℕ`{.Agda}, finite contexts of that size are `Vec`{.Agda}s read at positions of type `Fin n`, and `⊥*`{.Agda} is the type with no inhabitants, the target at which impossible cases are discharged.

One convention of the book's presentation is stated before any mathematics, because it changes how every later page is read.

## Traceable names

The displayed import lists identify the library names that become part of this shared vocabulary. They let a reader trace a symbol to its definition while the surrounding prose explains the mathematical role for which it is being introduced.
<!--zh-->
# 基础词汇

集合论谈论的是集合、隶属与函数；而本书进行这种谈论的语言是立方类型论。在正式开始集合论之前，两种语言需要一套共享的工作词汇；本章一次性把它建立起来，让后续各章直接使用。这套词汇最好作为一个小型的数学故事来呈现，而不是一份清单，因此我们逐个问题地走过它，而后文各节也将反复依赖于这里确定的概念。

第一个问题是大小。类型被组织成由显式层级分级的宇宙 `Type ℓ`{.Agda}，因此本书检视的每个总体，例如「所有集合」或「所有命题」，都带有说明其大小的层级。第二个问题是相等。在这里，相等是路径类型 `_≡_`{.Agda}，相等证明是数据而非判定：`refl`{.Agda}、`sym`{.Agda}、`_∙_`{.Agda}、`cong`{.Agda}、`transport`{.Agda} 与 `funExt`{.Agda} 构造并使用这些数据。在相等之上，第三个问题问一个类型携带多少相等结构：谓词 `isProp`{.Agda}、`isSet`{.Agda} 与 `isContr`{.Agda} 度量这一点，其中 `isContr`{.Agda} 就是本书的**唯一存在**。这三个要素已经决定了本章其余部分的形状。真值是连同其证书一起打包的命题，即类型 `hProp`{.Agda}；投影 `⟨_⟩`{.Agda} 读出底层命题；载体 `A` 上的类是真值谓词，其隶属陈述恰是这样的投影。打包再以一般形式出现一次，即依值对 `Σ`{.Agda}，它把数据与依赖该数据的数据放在一起。在有限方面，诸如公式自由变量个数这样的数目由自然数 `ℕ`{.Agda} 记录；相应大小的有限语境是 `Vec`{.Agda}，在 `Fin n` 类型的位置上读取；`⊥*`{.Agda} 是没有任何元素的类型，不可能的情形在那里被消解。

本书行文的一条规约须在任何数学之前说明，因为它改变后续每一页的读法。

## 名字可溯源

列出的 import 名字标明哪些库概念成为这套共享词汇的一部分。读者可以据此追溯符号的定义，而周围的正文则解释引入该概念所服务的数学目的。
<!--ja-->
# 基礎語彙

集合論が語るのは集合、所属、関数です。本書がその語りを行う言語は立方型理論です。集合論そのものを始める前に、二つの言語は作業用の語彙を共有する必要があり、この章でそれを一度だけ作り、後の章はそのまま使えるようにします。語彙は一覧としてではなく、小さな数学の物語として示すのが最も適しているので、問いを一つずつたどりながら進みます。後の節は、ここで確定した概念に繰り返し立ち返ることになります。

最初の問いは大きさです。型は明示的なレベルで階層付けされた宇宙 `Type ℓ`{.Agda} へと組織されるので、本書が眺める「すべての集合」「すべての命題」のような全体性はどれも、その大きさを示すレベルを持ちます。二つ目の問いは等式です。ここでは等式はパス型 `_≡_`{.Agda} であり、等式の証明は判定ではなくデータです。`refl`{.Agda}、`sym`{.Agda}、`_∙_`{.Agda}、`cong`{.Agda}、`transport`{.Agda}、`funExt`{.Agda} の演算がそのデータを作り、使います。等式の上に立って、三つ目の問いは、型がどれだけの等式構造を持つかを尋ねます。それを測るのが述語 `isProp`{.Agda}、`isSet`{.Agda}、`isContr`{.Agda} で、とりわけ `isContr`{.Agda} は本書の**一意存在**です。この三つの材料が、章の残りの形をすでに決めています。真理値とは、命題をその証明書とともに包んだものであり、型 `hProp`{.Agda} です。射影 `⟨_⟩`{.Agda} が基底の命題を読み出し、台 `A` 上のクラスは真理値をとる述語で、その所属の主張はまさにそのような射影です。パッケージ化はその一般形、依存対 `Σ`{.Agda} でもう一度現れます。これは、データとそのデータに依存するデータを一緒に収めます。有限の側では、論理式の自由変数の個数のような個数は自然数 `ℕ`{.Agda} で記録し、その大きさの有限の文脈は `Vec`{.Agda} で、`Fin n` 型の位置から読み取ります。最後に `⊥*`{.Agda} は要素をひとつも持たない型で、ありえない場合の行き先です。

本書の行文に関する一つの規約は、数学に入る前に述べておく必要があります。それはその後のすべてのページの読み方を変えるからです。

## 名前を追跡できるようにする

表示された import の名前は、どのライブラリ上の概念がこの共通語彙に加わるかを示します。読者はそこから記号の定義をたどり、周囲の本文から、その概念を導入する数学的な役割を読み取れます。
<!--/-->

<!--en-->
This single line fixes the setting in which everything that follows is checked. Because the host is cubical type theory, the equality `_≡_`{.Agda} of the next section is the path type, and judgmental equality remains a separate metatheoretic notion alongside the paths. The `--safe` flag disables the features that could undermine consistency, such as postulates written inside trusted code, so the theorems of the book rest on checked proofs rather than assumed ones. The `--guardedness` flag turns on Agda's guardedness check for definitions.
<!--zh-->
这一行固定了后文一切所经检查的环境。由于宿主是立方类型论，下一节的相等 `_≡_`{.Agda} 是路径类型，而定义性相等是与路径并存的另一个元理论概念。`--safe` 标志禁用可能破坏一致性的特性，例如在受信代码中写 postulate，于是书中的定理都依赖经检查的证明而非假定。`--guardedness` 标志为定义开启 Agda 的完好性检查。
<!--ja-->
この一行が、このあとのすべてが検査される設定を固定します。ホストは立方型理論なので、次節の等式 `_≡_`{.Agda} はパス型であり、定義的等式 (判断的等式) はパスとは別のメタ理論的な概念として並立します。`--safe` フラグは、信頼済みコード内の postulate のように整合性を損ないうる機能を無効にします。したがって本書の定理は、仮定ではなく検査済みの証明に根ざします。`--guardedness` フラグは、定義に対する Agda の guardedness チェックを有効にします。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}
```

<!--en-->
Everything introduced below is gathered under the name `Base.Prelude`, so that a reader of any later chapter can trace a familiar symbol back to this chapter or the next. With the setting fixed, the next section begins the vocabulary itself, one idea at a time.
<!--zh-->
下文引入的一切都归于 `Base.Prelude` 这个名字之下，因此后续任一章的读者都能把熟悉的符号追溯到本章或下一章。环境既已固定，下一节开始逐个引入这套词汇本身。
<!--ja-->
以下で導入するものはすべて `Base.Prelude` という名前のもとに集められます。したがって後の章の読者は、見慣れた記号を本章か次章まで遡れます。設定を固定したうえで、次節から語彙そのものを一つずつ導入していきます。
<!--/-->

```agda

module Base.Prelude where
```

<!--en-->
## The host vocabulary

The first question is size. A type that quantifies over all types would contain itself, and the host avoids this by sorting types into universes `Type ℓ`{.Agda}, one for each level `ℓ : Level`{.Agda}. Levels come with the arithmetic `ℓ-zero`{.Agda}, `ℓ-suc`{.Agda} and `ℓ-max`{.Agda}, and each universe is itself a type: `Type ℓ`{.Agda} lives one level up, in `Type (ℓ-suc ℓ)`{.Agda}. Note what this does not say. The universes here are not cumulative: an element of `Type ℓ`{.Agda} is not automatically an element of `Type (ℓ-suc ℓ)`{.Agda}, and moving a type between levels takes an explicit operation, `Lift`{.Agda}, introduced shortly. Whenever the book surveys a totality, "all sets" or "all propositions", the level attached to the statement records exactly how large the surveyed totality is taken to be.
<!--zh-->
## 宿主词汇

第一个问题是大小。若一个类型能量化所有类型，它就会包含自身；宿主通过把类型分入宇宙 `Type ℓ`{.Agda} 来避免这一点，每个层级 `ℓ : Level`{.Agda} 对应一个宇宙。层级配有算术 `ℓ-zero`{.Agda}、`ℓ-suc`{.Agda}、`ℓ-max`{.Agda}，而且每个宇宙本身也是类型：`Type ℓ`{.Agda} 住在上一层的 `Type (ℓ-suc ℓ)`{.Agda} 中。注意这里没有说什么：这里的宇宙不是累积的，`Type ℓ`{.Agda} 的元素并不自动成为 `Type (ℓ-suc ℓ)`{.Agda} 的元素；在层级之间搬移类型需要一个显式运算 `Lift`{.Agda}，稍后引入。本书凡检视某个总体 (「所有集合」「所有命题」)，陈述所附的层级就记录了该总体被当作多大。
<!--ja-->
## ホスト言語の語彙

最初の問いは大きさです。すべての型を量化する型があれば、それは自分自身を含んでしまいます。ホストはこれを避けるため、型を宇宙 `Type ℓ`{.Agda} へと分類します。各レベル `ℓ : Level`{.Agda} に一つずつです。レベルには算術 `ℓ-zero`{.Agda}、`ℓ-suc`{.Agda}、`ℓ-max`{.Agda} があり、各宇宙はそれ自身も型です。つまり `Type ℓ`{.Agda} は一つ上の `Type (ℓ-suc ℓ)`{.Agda} に住んでいます。ここに何が言われていないかに注意してください。この宇宙は累積的ではありません。`Type ℓ`{.Agda} の元が自動的に `Type (ℓ-suc ℓ)`{.Agda} の元になるわけではなく、レベルの間で型を動かすには明示的な演算 `Lift`{.Agda} が必要で、まもなく導入します。本書が全体性 (「すべての集合」「すべての命題」) を眺めるとき、主張に付いたレベルが、その全体性をどのくらいの大きさとして扱うかを記録します。
<!--/-->

<!--en-->
The block below is the formal anchor for this idea: it presents the universe family, the level type and the three level-forming operations together. One warning belongs at this anchor: these levels are universe levels of the host language, a bookkeeping device for size, and are unrelated to the ordinal-indexed stages of the constructible universe L built later in the book.
<!--zh-->
下面的代码块是这一想法的形式锚点：它把宇宙族、层级类型与三个层级运算一同呈现。在锚点处恰有一句提醒：这些层级是宿主语言的宇宙层级，只是大小的簿记，与后文构造的可构造宇宙 L 中以序数指标的阶段无关。
<!--ja-->
下のコードブロックはこの考えの形式的な锚です。宇宙の族、レベルの型、三つのレベル構成演算を一まとめに提示します。この锚の位置で一度注意しておきます。これらのレベルはホスト言語の宇宙レベルであり、大きさの簿記にすぎず、後で構成される構成可能宇宙 L の序数で番号付けられた段とは無関係です。
<!--/-->

```agda
open import Cubical.Foundations.Prelude public
  using ( Type; Level; ℓ-zero; ℓ-suc; ℓ-max )
```

<!--en-->
The second question is equality. In cubical type theory, `_≡_`{.Agda} is the path type, and an equality proof is data, not a bare verdict. The standard tools come with it: `refl`{.Agda} gives reflexivity, `sym`{.Agda} reverses a path, `_∙_`{.Agda} composes two paths, `cong`{.Agda} and `cong₂`{.Agda} show that applying a function respects equality, `transport`{.Agda} and `subst`{.Agda} carry an inhabitant along a path, and `funExt`{.Agda} turns pointwise equality of functions into an equality of functions. As a small example: to show `suc m ≡ suc n`{.Agda} from `m ≡ n`{.Agda}, apply `cong suc`{.Agda}. Here `suc`{.Agda} is the inductive constructor of the natural numbers, which simply builds the number after `n` from `n`; it is an ordinary function of the host, quite distinct from a set-theoretic successor operation on ordinals, and precisely because it is a function, `cong`{.Agda} lifts the path through it.
<!--zh-->
第二个问题是相等。在立方类型论中，`_≡_`{.Agda} 是路径类型，相等证明是数据而非单纯的判定。它配有标准工具：`refl`{.Agda} 给出自反，`sym`{.Agda} 反转路径，`_∙_`{.Agda} 复合两条路径，`cong`{.Agda} 与 `cong₂`{.Agda} 表明应用函数尊重相等，`transport`{.Agda} 与 `subst`{.Agda} 沿路径搬移元素，`funExt`{.Agda} 把逐点相等的函数变成相等的函数。举个小例子：要从 `m ≡ n`{.Agda} 得到 `suc m ≡ suc n`{.Agda}，应用 `cong suc`{.Agda} 即可。这里的 `suc`{.Agda} 是自然数的归纳构造子，只是从 `n` 构造排在 `n` 之后的那个数；它是宿主的普通函数，与序数上的集合论后继运算截然不同。正因为它是一个函数，`cong`{.Agda} 才能把路径沿它提升。
<!--ja-->
二つ目の問いは等式です。立方型理論では `_≡_`{.Agda} はパス型であり、等式の証明はデータであって、単なる判定ではありません。標準的な道具が伴います。`refl`{.Agda} は反射律を、`sym`{.Agda} はパスの逆を、`_∙_`{.Agda} は二つのパスの合成を与えます。`cong`{.Agda} と `cong₂`{.Agda} は関数の適用が等式を保存することを示し、`transport`{.Agda} と `subst`{.Agda} はパスに沿って元を運び、`funExt`{.Agda} は各点で等しい関数を等しい関数へ変えます。小さな例を挙げると、`m ≡ n`{.Agda} から `suc m ≡ suc n`{.Agda} を得るには `cong suc`{.Agda} を適用します。ここでの `suc`{.Agda} は自然数の帰納的な構成子で、`n` からその次の数を作るだけの、ホストの普通の関数です。序数に対する集合論の後続操作とはまったく別物です。関数であるからこそ、`cong`{.Agda} がパスをその通りに持ち上げられるのです。
<!--/-->

<!--en-->
The block below gathers the whole toolkit of the lead in one place. The grouping from the lead also describes how the book uses it in practice: paths are built with `refl`{.Agda}, `sym`{.Agda} and `_∙_`{.Agda}, carried through functions with `cong`{.Agda}, `cong₂`{.Agda} and `funExt`{.Agda}`, and used to move inhabitants between types with `transport`{.Agda} and `subst`{.Agda}.
<!--zh-->
下面的代码块把导语中的整套工具集中在一处。导语中的分组也描述了本书实际的用法：用 `refl`{.Agda}、`sym`{.Agda} 与 `_∙_`{.Agda} 构造路径，用 `cong`{.Agda}、`cong₂`{.Agda} 与 `funExt`{.Agda} 让路径穿过函数，用 `transport`{.Agda} 与 `subst`{.Agda} 沿路径在类型之间搬移元素。
<!--ja-->
下のコードブロックは、冒頭の道具一式を一か所に集めます。冒頭の分類は、本書での実際の使い方もそのまま述べています。`refl`{.Agda}、`sym`{.Agda}、`_∙_`{.Agda} でパスを作り、`cong`{.Agda}、`cong₂`{.Agda}、`funExt`{.Agda} で関数を通して運び、`transport`{.Agda} と `subst`{.Agda} でパスに沿って型の間を元が移動します。
<!--/-->

```agda
open import Cubical.Foundations.Prelude public
  using ( _≡_; refl; sym; _∙_; cong; cong₂; transport; subst; funExt )
```

<!--en-->
The third question builds directly on equality: how much equality structure does a type carry? The h-level predicates answer it. `isProp A`{.Agda} says any two inhabitants of `A` are equal, `isSet A`{.Agda} says equality of inhabitants of `A` is itself a proposition, and `isContr A`{.Agda} is explicit data: a chosen center element together with, for every element of `A`, a path from it to the center. This book reads `isContr`{.Agda} as **unique existence**, following the convention explained in the Charter; note that the center is chosen, not merely known to exist. Finally `isProp→isSet`{.Agda} connects the levels by showing that every proposition is a set.
<!--zh-->
第三个问题直接建立在相等之上：一个类型携带多少相等结构？h-层级谓词回答它。`isProp A`{.Agda} 说 `A` 的任意两个元素相等；`isSet A`{.Agda} 说 `A` 中元素的相等本身是命题；`isContr A`{.Agda} 则是显式的数据：一个被选定的中心元素，连同对 `A` 的每个元素给出的、从它到中心的路径。依纲领的规约，本书把 `isContr`{.Agda} 读作**唯一存在**；注意中心是被选定的，而不仅是被知道存在。最后，`isProp→isSet`{.Agda} 把层级连起来，说明凡命题皆是集合。
<!--ja-->
三つ目の問いは、等式の上に直接築かれます。型がどれだけの等式構造を持つか。それに答えるのが h-レベルの述語です。`isProp A`{.Agda} は `A` の任意の二つの元が等しいと言い、`isSet A`{.Agda} は `A` の元の間の等式それ自体が命題であると言います。`isContr A`{.Agda} は明示的なデータです。選ばれた中心の元と、`A` のすべての元に対する、そこから中心へのパスです。綱領で説明される規約に従い、本書は `isContr`{.Agda} を**一意存在**と読みます。中心は選ばれるのであって、存在が分かっているだけではないことに注意してください。最後に `isProp→isSet`{.Agda} が両者をつなぎ、すべての命題が集合であることを示します。
<!--/-->

<!--en-->
The block presents these predicates together with the one lemma already singled out, `isProp→isSet`{.Agda}, the direct implication from propositionhood to sethood. Its direction is what makes it usable in practice: whenever a type is already known to be a proposition and a later argument needs to treat its equality types as propositions in turn, this lemma delivers the `isSet`{.Agda} status without further work.
<!--zh-->
此块把上述谓词与已指出的那条引理 `isProp→isSet`{.Agda} 一同呈现，即由命题性到集合性的直接蕴含。它的方向正是其实用之处：当已知某类型是命题，而后文论证需要进一步把其相等类型当作命题对待时，这条引理无需额外工作便给出 `isSet`{.Agda} 资格。
<!--ja-->
このブロックは、これらの述語を、すでに取り上げた一つの補題 `isProp→isSet`{.Agda}、すなわち命題であることから集合であることへの直接的な含意とともに提示します。実践で使えるのはその向きゆえです。型が命題だとすでに分かっていて、後の議論がさらにその等式の型を命題として扱う必要があるとき、この補題は追加の作業なしに `isSet`{.Agda} であることを与えます。
<!--/-->

```agda
open import Cubical.Foundations.Prelude public
  using ( isProp; isSet; isContr; isProp→isSet )
```

<!--en-->
The noncumulativity noted in the previous section creates a practical problem: two types needed side by side may sit at different levels, and no automatic coercion moves one of them up. `Lift`{.Agda} is the explicit remedy: it presents a copy of `A` at a higher level, and `lift`{.Agda} and `lower`{.Agda} move **elements** between `A` and `Lift ℓ A`{.Agda}, mutually inverse. The asymmetry appears at the level of types: a type can always be copied upward, but there is in general no way to move one down. Propositions are the exception: the classical boundary chapter will show that excluded middle provides exactly the downward direction for them.
<!--zh-->
上一节指出的非累积性带来一个实际问题：并排放置的两个类型可能处于不同层级，而没有自动的强制把它们中的一个抬高。`Lift`{.Agda} 是显式的补救办法：它把 `A` 呈现为更高层级的副本，`lift`{.Agda} 与 `lower`{.Agda} 在 `A` 与 `Lift ℓ A`{.Agda} 之间搬运**元素**，两者互逆。不对称出现在类型层面：类型总能向上复制，却一般无法向下搬移。命题是例外：经典边界一章将看到，排中律恰好为命题提供这个向下方向。
<!--ja-->
前節で指摘した非累積性は実践的な問題を生みます。並べて使いたい二つの型が異なるレベルに置かれているかもしれず、片方を自動的に持ち上げる型強制はありません。`Lift`{.Agda} が明示的な対処です。これは `A` をより高いレベルの複製として提示し、`lift`{.Agda} と `lower`{.Agda} が **元**を `A` と `Lift ℓ A`{.Agda} の間で運び、互いに逆です。非対称なのは型の水準です。型は常に上へ複製できますが、一般には下へ動かす方法はありません。命題は例外で、古典的境界の章で、排中律がちょうど命題に対する下向きの方向を与えることを見ます。
<!--/-->

<!--en-->
The round trip between a type and its lifted copy is a good first exercise in the path discipline of the earlier sections. Here `Lift ℓ A`{.Agda} is a one-field record whose field `lower`{.Agda} returns an `A`, and `lift`{.Agda} packages an element of `A` into that record. Because `lower`{.Agda} is the record field, `lower (lift a)`{.Agda} computes back to `a`, and by record eta `lift (lower b)`{.Agda} agrees with `b` for any `b : Lift ℓ A`{.Agda}. What the two functions supply, then, is movement of elements that the type checker already accepts on both sides, so that types sitting at different levels can be handled at one common level; note that the copy of `A` lands at the maximum of the two levels involved, not at a fixed number of steps above it.
<!--zh-->
在类型与其提升副本之间往返，是前几节路径纪律的第一个练习。这里 `Lift ℓ A`{.Agda} 是单字段记录，其字段 `lower`{.Agda} 返回一个 `A`，而 `lift`{.Agda} 把 `A` 的元素装进该记录。由于 `lower`{.Agda} 就是记录字段，`lower (lift a)`{.Agda} 可计算回 `a`；由记录的 η 规则，对任意 `b : Lift ℓ A`{.Agda}，`lift (lower b)`{.Agda} 与 `b` 一致。于是这对函数提供的是两侧类型检查都已接受的元素搬移，使处于不同层级的类型能在同一公共层级上处理；注意 `A` 的副本落在所涉两个层级的最大值处，而不是高出固定的若干层。
<!--ja-->
型とその持ち上げられたコピーの間の往復は、前の節のパスの規律を学ぶよい最初の練習になります。ここで `Lift ℓ A`{.Agda} は一つのフィールドを持つレコードで、そのフィールド `lower`{.Agda} は `A` を返し、`lift`{.Agda} は `A` の元をこのレコードに包みます。`lower`{.Agda} がレコードのフィールドそのものなので、`lower (lift a)`{.Agda} は計算によって `a` に戻り、またレコードの η 規則により、任意の `b : Lift ℓ A`{.Agda} に対して `lift (lower b)`{.Agda} は `b` と一致します。この一組の関数が供給するのは、型検査器が両側で受けつけている元の移動です。これにより、異なるレベルに置かれた型を一つの共通のレベルで扱えます。なお `A` のコピーは、関わる二つのレベルの最大値に着陸するのであって、固定された段数だけ上にあるのではありません。
<!--/-->

```agda
open import Cubical.Foundations.Prelude public
  using ( Lift; lift; lower )
```

<!--en-->
The packaging habit just met with `Lift`{.Agda}, data plus bookkeeping, now meets its logical counterpart. A truth value should not be a bare type: what makes a statement usable as a truth value is that its extension is a proposition, so the certificate must travel with the type. The package is `hProp`{.Agda}, this book's type of truth values. Two facts make it usable in arguments. `isSetHProp`{.Agda} says `hProp`{.Agda} is itself a set, which is what the next chapter's `isSetΩ` field will demand of a truth-value type. And `isPropΠ`{.Agda} says propositions are closed under Π types: if `B x` is a proposition for every `x`, then `(x : A) → B x` is one too, so a universally quantified truth value is again a truth value. The pattern to carry forward is: data is carried together with the certificate that licenses its use.
<!--zh-->
刚才在 `Lift`{.Agda} 见到的打包习惯 (数据加上簿记) 现在遇到它的逻辑对应物。真值不应是裸的类型：一个陈述能作为真值使用，在于其外延是命题，因此证书必须与类型同行。这个包就是 `hProp`{.Agda}，本书的真值类型。两条事实使它可用于论证。`isSetHProp`{.Agda} 说 `hProp`{.Agda} 自身是集合，下一章的 `isSetΩ` 字段对真值类型要求的正是这一点。`isPropΠ`{.Agda} 说命题在 Π 类型下封闭：若对每个 `x`，`B x` 都是命题，则 `(x : A) → B x` 也是命题；因此全称量化的真值仍是真值。要带走的模式是：数据连同许可其使用的证书一起携带。
<!--ja-->
`Lift`{.Agda} で見た、データと簿記をともに運ぶ作法は、今度は論理側の対応物に出会います。真理値とは裸の型であってはなりません。ある主張が真理値として使えるのは、その外延が命題であるからで、したがって証明書は型とともに運ばれなければなりません。その包みが `hProp`{.Agda}、本書の真理値の型です。これを議論で使えるようにするのが二つの事実です。`isSetHProp`{.Agda} は `hProp`{.Agda} 自身が集合であると言い、これが次章の `isSetΩ` フィールドの要求です。また `isPropΠ`{.Agda} は命題が Π 型の下で閉じていると言います。すべての `x` に対し `B x` が命題なら `(x : A) → B x` も命題であり、全称量化された真理値が再び真理値になるのはこのためです。先へ持ち越すべき作法はこうです。データは、その使用を許可する証明書とともに運ばれる。
<!--/-->

<!--en-->
Concretely, an inhabitant of `hProp ℓ`{.Agda} consists of a type in `Type ℓ`{.Agda} together with a proof that it is a proposition, exactly the packaging pattern of the previous sections applied to logic. The two lemmas anchored by this block are the ones just identified: `isSetHProp`{.Agda}, that `hProp`{.Agda} is a set, so the collection of truth values is itself well-behaved at the level of equality; and `isPropΠ`{.Agda}, that a dependent function type into a proposition-valued family is again a proposition, so universal quantification stays inside the world of truth values. Having a truth value in hand, the next question is how to get back to the bare proposition it contains.
<!--zh-->
具体地，`hProp ℓ`{.Agda} 的元素由 `Type ℓ`{.Agda} 中的一个类型连同其为命题的证明组成，正是把前几节的打包模式应用于逻辑。此代码块所锚定的两条引理即刚才所指：`isSetHProp`{.Agda}，`hProp`{.Agda} 是集合，因此真值全体在相等层面本身也是良态的；`isPropΠ`{.Agda}，到命题值族的依值函数类型仍是命题，因此全称量化不越出真值的世界。手握真值之后，下一个问题是：如何回到它所含的裸命题。
<!--ja-->
具体的には、`hProp ℓ`{.Agda} の元は `Type ℓ`{.Agda} の型と、それが命題であることの証明からなります。これは、ここまでの節のパッケージ化の作法を論理に適用したものです。このブロックが据える二つの補題は、先ほど挙げたものです。`hProp`{.Agda} が集合であるという `isSetHProp`{.Agda}。これにより真理値全体も等式の水準で良好に振る舞います。そして命題値の族への依存関数型が再び命題であるという `isPropΠ`{.Agda}。これにより全称量化は真理値の世界の中にとどまります。真理値を手にしたら、次の問いは、その中の裸の命題をどう取り出すかです。
<!--/-->

```agda
open import Cubical.Foundations.HLevels public
  using ( hProp; isSetHProp; isPropΠ )
```

<!--en-->
Everyday reasoning about truth values mostly concerns the proposition, not the certificate, so a package needs a way to be opened just to its type. That is the projection `⟨_⟩`{.Agda}, read "the underlying type of": for `P : hProp ℓ`{.Agda} the statement `⟨ P ⟩`{.Agda} is the underlying proposition, while the proposition-hood proof remains inside as `P .snd`{.Agda}, and the book gives it no separate name. This completes the pattern begun with `hProp`{.Agda}: the type is what one reasons about, the certificate is what licenses it as a truth value.
<!--zh-->
对真值的日常推理大多只关心命题本身，而非证书，因此这个包需要一条只打开到类型层的途径。这就是投影 `⟨_⟩`{.Agda}，读作「……的底层类型」：对 `P : hProp ℓ`{.Agda}，`⟨ P ⟩`{.Agda} 就是底层命题，而命题性证明仍留在包内，即 `P .snd`{.Agda}，本书不为它另设名字。至此 `hProp`{.Agda} 开始的模式完整了：类型是推理的对象，证书是使它成为真值的凭据。
<!--ja-->
真理値についての日常の推論のほとんどは、証明書ではなく命題そのものに関わります。そこで、パッケージを型のところまでだけ開く方法が必要です。それが射影 `⟨_⟩`{.Agda} で、「〜の基底型」と読みます。`P : hProp ℓ`{.Agda} に対し `⟨ P ⟩`{.Agda} が基底の命題であり、命題性の証明は `P .snd`{.Agda} として中に留まります。本書はこれに別の名を与えません。`hProp`{.Agda} で始まった作法がこれでそろいました。型は推論の対象であり、証明書はそれを真理値として認める凭拠です。
<!--/-->

<!--en-->
The projection is defined for any type-with-structure record, and an `hProp`{.Agda} is such a record, so `⟨ P ⟩`{.Agda} extracts the proposition `P` carries. The direction of use is always the same: given a truth value, one asserts or reasons about `⟨ P ⟩`{.Agda}, and the certificate stays inside the package. With truth values and this projection in place, the next notion composes them into predicates.
<!--zh-->
这条投影对任何「带结构的类型」记录皆有定义，而 `hProp`{.Agda} 正是这样的记录，因此 `⟨ P ⟩`{.Agda} 取出命题 `P` 所携带的类型。用法方向始终如一：给定一个真值，要断言或推理的就是 `⟨ P ⟩`{.Agda}，证书留在包内。真值与这条投影就绪后，下一个概念将它们组成谓词。
<!--ja-->
この射影は、任意の「構造付きの型」のレコードに対して定義されており、`hProp`{.Agda} はまさにそのようなレコードなので、`⟨ P ⟩`{.Agda} が命題 `P` の持つ型を取り出します。使い方は常に同じ向きです。真理値が与えられれば、主張や推論の対象は `⟨ P ⟩`{.Agda} であり、証明書はパッケージの中に留まります。真理値とこの射影がそろえば、次の概念はそれらを述語へと組み上げます。
<!--/-->

```agda
open import Cubical.Foundations.Structure public
  using ( ⟨_⟩ )
```

<!--en-->
Two ingredients are now on the table: truth values, and the projection that reads out their propositions. Composing them gives the notion that set theory cannot do without. A **class** over a carrier `A` is a function `M : A → hProp ℓ`{.Agda}, and `x ∈ᶜ M`, read "x belongs to the class M", is precisely `⟨ M x ⟩`{.Agda}, the underlying proposition of the value at `x`. The superscript `ᶜ` marks the notion as a **class**, keeping it distinct from the object-language membership between sets that later chapters interpret inside structures; one is a host-level predicate, the other a relation of the set language.
<!--zh-->
桌上已有两件材料：真值，以及读出其命题的投影。把它们组合起来，便得到集合论不可或缺的概念。载体 `A` 上的**类**是函数 `M : A → hProp ℓ`{.Agda}，而 `x ∈ᶜ M` (读作「x 属于类 M」) 恰是 `⟨ M x ⟩`{.Agda}，即 `x` 处取值的底层命题。上标 `ᶜ` 标示这是**类**，用以把它与后文在结构中解释的集合间对象语言成员关系区分开：一个是宿主层谓词，另一个是集合语言的关系。
<!--ja-->
材料はすでに二つそろっています。真理値と、その命題を読み出す射影です。両者を組み合わせれば、集合論に欠かせない概念が得られます。台 `A` 上の**クラス**とは関数 `M : A → hProp ℓ`{.Agda} のことで、`x ∈ᶜ M` (「x はクラス M に属する」と読みます) はまさに `⟨ M x ⟩`{.Agda}、`x` での値の基底の命題です。上付きの `ᶜ` はこれが**クラス**であることを示し、後の章が構造の中で解釈する集合の間の対象言語の所属とは区別されます。一方はホストレベルの述語であり、他方は集合言語の関係です。
<!--/-->

<!--en-->
The membership relation for subsets is taken here under the new name `_∈ᶜ_`. For a function `M` into `hProp`{.Agda}, the statement `x ∈ᶜ M` unfolds to the underlying proposition `⟨ M x ⟩`{.Agda}, so membership in a class is literally a truth value applied at a point, built from the two pieces of this section. The distinctive superscript exists so that this host-level belonging is never confused, in the text or in the code, with the object-language membership between sets that the later chapters interpret inside structures.
<!--zh-->
子集的成员关系在此以新名字 `_∈ᶜ_` 引入。对取值于 `hProp`{.Agda} 的函数 `M`，`x ∈ᶜ M` 展开为底层命题 `⟨ M x ⟩`{.Agda}，所以类中的隶属就是在某点上应用一个真值，由本节的两个部件构成。显眼的上标是为了让这个宿主层的归属在文稿和代码中都不会与后文在结构中解释的集合间对象语言成员关系相混淆。
<!--ja-->
部分集合に対する所属関係は、ここで新しい名前 `_∈ᶜ_` のもとで取り込まれます。`hProp`{.Agda} への関数 `M` に対し、`x ∈ᶜ M` は基底の命題 `⟨ M x ⟩`{.Agda} へと展開されます。つまりクラスへの所属とは、真値を一点で適用したものであり、この節の二つの部品から組み上がっています。目立つ上付き `ᶜ` があるのは、このホストレベルの所属が、後の章で構造の中で解釈される集合の間の対象言語の所属と、文書でもコードでも混同されないためです。
<!--/-->

```agda
open import Cubical.Foundations.Powerset public
  using () renaming ( _∈_ to _∈ᶜ_ )
```

<!--en-->
The packaging habit met twice already, in `Lift`{.Agda} and in `hProp`{.Agda}, has a general form: the dependent pair. A type `Σ (x : A) B x`{.Agda} pairs an element `a : A` with an element of `B a`, a type that may itself depend on `a`; when the second component does not depend on the first, this specialises to the plain product `A × B`{.Agda}. The book's central use of this is to bundle a set with data depending on that set, for example a constructibility certificate: the certificate is about the very set it accompanies, so only a dependent pair can hold both. Pairs are built with `_,_`{.Agda} and taken apart with `fst`{.Agda} and `snd`{.Agda}.
<!--zh-->
已两次见到的打包习惯，先在 `Lift`{.Agda}，再在 `hProp`{.Agda}，有一个一般形式：依值对。类型 `Σ (x : A) B x`{.Agda} 把元素 `a : A` 与 `B a` 中的元素配对，而 `B a` 本身可以依赖 `a`；当第二分量不依赖第一分量时，它就特化为普通的积 `A × B`{.Agda}。本书对它的核心用法是把集合与依赖该集合的数据捆在一起，例如可构造性证书：证书针对的正是它所伴随的集合，因此只有依值对能同时容纳两者。用 `_,_`{.Agda} 构造对，用 `fst`{.Agda} 与 `snd`{.Agda} 拆分。
<!--ja-->
`Lift`{.Agda} と `hProp`{.Agda} で二度見たパッケージ化の作法には、一般形があります。依存対です。型 `Σ (x : A) B x`{.Agda} は、要素 `a : A` と型 `B a` の要素を対にします。`B a` は `a` に依存して構いません。第二成分が第一成分に依存しない場合は、通常の積 `A × B`{.Agda} に特化します。本書の中心的な使い方は、集合とその集合に依存するデータを束ねることです。たとえば構成可能性の証明書は、伴う集合そのものについてのものなので、両者を収められるのは依存対だけです。対は `_,_`{.Agda} で作り、`fst`{.Agda} と `snd`{.Agda} で分解します。
<!--/-->

<!--en-->
The Sigma types are anchored here, with the sugar `Σ-syntax`{.Agda} for the readable binder notation and the non-dependent special case `_×_`{.Agda}. The connection back to the earlier packages is direct: an `hProp`{.Agda} is itself a dependent pair of a type and its proposition-hood proof, and the projections `fst`{.Agda} and `snd`{.Agda} used on it above are exactly these. With structure and truth values settled, the remaining vocabulary concerns finite data.
<!--zh-->
Sigma 类型在此锚定，配有易读约束写法的便捷记法 `Σ-syntax`{.Agda}，以及非依值特例 `_×_`{.Agda}。与前文各包的联系是直接的：`hProp`{.Agda} 本身就是「类型与其命题性证明」的依值对，上面在其上用的投影 `fst`{.Agda} 与 `snd`{.Agda} 正是这两者。结构与真值就绪后，其余词汇都关于有限数据。
<!--ja-->
Σ 型はここで据えられます。読みやすい束縛記法のための糖衣構文 `Σ-syntax`{.Agda} と、非依存の特別な場合 `_×_`{.Agda} が付随します。先のパッケージとのつながりは直接的です。`hProp`{.Agda} はそれ自体、型とその命題性の証明の依存対であり、そこで使った射影 `fst`{.Agda} と `snd`{.Agda} がまさにこれらです。構造と真理値が済めば、残りの語彙は有限のデータに関するものです。
<!--/-->

```agda
open import Cubical.Data.Sigma public
  using ( Σ; Σ-syntax; _×_; _,_; fst; snd )
```

<!--en-->
Finite data starts with counting, and counting in the host is inductive. The natural numbers `ℕ`{.Agda}, built from `zero`{.Agda} and `suc`{.Agda}, record how many of something there are. Here `suc`{.Agda} is the constructor of the inductive type of natural numbers, sending a number to the next one; it is a host-level notion of counting and should not be confused with the set-theoretic successor of an ordinal, a different operation introduced later. In this development the most prominent role of `ℕ`{.Agda} is as an index type: the first example is the number of free variables of a first-order formula, and that count determines, in later chapters, the shape of the variable environment an interpretation must supply.
<!--zh-->
有限数据从计数开始，而宿主中的计数是归纳式的。自然数 `ℕ`{.Agda} 由 `zero`{.Agda} 与 `suc`{.Agda} 构成，记录某事物有多少个。这里 `suc`{.Agda} 是自然数这一归纳类型的构造子，把一个数送到下一个数；它是宿主层的计数概念，不应与后文引入的序数的集合论后继运算相混淆。在本开发中，`ℕ`{.Agda} 最显要的角色是指标类型：第一个例子是一阶公式的自由变量个数，后文中正是这个数目决定解释所须提供的变量环境的形状。
<!--ja-->
有限のデータは数え上げから始まりますが、ホストでの数え上げは帰納的です。自然数 `ℕ`{.Agda} は `zero`{.Agda} と `suc`{.Agda} から組み上がり、あるものがいくつあるかを記録します。ここでの `suc`{.Agda} は自然数という帰納的な型の構成子であり、数を次の数へ送るものです。これはホストレベルの数え上げの概念であって、後で導入される順序数の集合論的后者という演算とは別物であり、混同してはなりません。この開発で `ℕ`{.Agda} の最も顕著な役割は添字の型です。最初の例が一階論理式の自由変数の個数であり、後の章ではこの個数が解釈の供給すべき変数環境の形を決めます。
<!--/-->

<!--en-->
Counting gets its carrier here, and it is worth pausing on how little is needed. The natural numbers are an inductive type with two constructors: `zero`{.Agda}, and `suc`{.Agda}, which sends a number to the next one. This `suc`{.Agda} is the inductive constructor of `ℕ`{.Agda}, an operation on finite counts; it is not the von Neumann successor of ordinals that set theory builds from `n ∪ {n}`, and the two must not be conflated. The defining feature is the inductive shape: to give a function on `ℕ`{.Agda}, one says what happens at `zero`{.Agda} and what happens at `suc n`{.Agda}, given what happens at `n`. That recursion principle is exactly what makes the numbers usable as indices. A later chapter declares a formula with `n` free variables and builds its variable environment by recursion on the shape of `n`, so the environment ends up with exactly as many slots as the formula declared.
<!--zh-->
计数在这里得到它的载体，而所需的东西之少值得停留一下。自然数是一个由两个构造子构成的归纳类型：`zero`{.Agda}，以及把一个数送到下一个数的 `suc`{.Agda}。这个 `suc`{.Agda} 是 `ℕ`{.Agda} 的归纳构造子，作用在有限计数上；它不是集合论中由 `n ∪ {n}` 构造的序数的冯·诺伊曼后继，两者不可混同。关键在于归纳的形状：要给出 `ℕ`{.Agda} 上的函数，只需说明在 `zero`{.Agda} 处如何，以及在 `suc n`{.Agda} 处如何 (假定已知 `n` 处的结果)。正是这条递归原理使自然数可用作指标。后文某章会声明一个有 `n` 个自由变量的公式，并对 `n` 的形状递归地构造变量环境，于是环境的槽位数恰与公式所声明的数目一致。
<!--ja-->
数え上げにここで担い手が与えられますが、必要なものがいかに少ないかを確認しておく価値があります。自然数は二つの構成子からなる帰納的な型です。`zero`{.Agda} と、数を次の数へ送る `suc`{.Agda} です。この `suc`{.Agda} は `ℕ`{.Agda} の帰納的な構成子であり、有限の個数への演算です。集合論が `n ∪ {n}` から作る順序数のフォン・ノイマン後続とは別物で、両者を混同してはなりません。決定的なのは帰納的な形です。`ℕ`{.Agda} 上の関数を定義するには、`zero`{.Agda} の場合と、`n` の場合が分かっているときの `suc n` の場合を言えばよい。この再帰原理こそが自然数を添字として使える理由です。後の章は自由変数 `n` 個の論理式を宣言し、`n` の形に対する再帰で変数環境を組み立てます。そうしてできる環境の槽の数は、論理式が宣言した個数とちょうど一致します。
<!--/-->

```agda
open import Cubical.Data.Nat public
  using ( ℕ; zero; suc )
```

<!--en-->
A count becomes a working tool only when the counted things can be held in one object and each position can be named, and the host provides the two halves that fit together. A vector `Vec A n`{.Agda} holds exactly `n` elements of `A`, and the finite type `Fin n` names exactly `n` positions. Because the length is part of the vector's type, the guarantee is structural: a function expecting a vector of one length simply cannot accept a vector of another length, and the type checker enforces this before any theorem is stated. This pairing is the book's representation of finite contexts, above all the variable environments of the first-order logic chapters, where a formula with `n` free variables is interpreted against an environment of exactly `n` values. In such an environment, reading the value assigned to a variable is a lookup at that variable's position, and lookup returns a value that may need to be carried along a path of truth values by the transport machinery introduced earlier in the chapter.
<!--zh-->
数目只有当被数的东西能容纳于一个对象、且每个位置能被指称时，才成为可用的工具；宿主提供了恰好契合的两半。向量 `Vec A n`{.Agda} 恰容纳 `n` 个 `A` 的元素，有限类型 `Fin n` 恰指称 `n` 个位置。由于长度是向量类型的一部分，保证是结构性的：期望某一长度的向量的函数根本无法接受另一长度的向量，而类型检查器在任何定理陈述之前就强制了这一点。这一配对是本书表示有限语境的方式，首先是一阶逻辑各章的变量环境：有 `n` 个自由变量的公式，正是在恰含 `n` 个值的环境中被解释的。在这样的环境中，读取某变量被赋予的值就是在该变量的位置上做一次查询，而查询所得的值可能需要用本章前文引入的搬移机制沿真值路径携带。
<!--ja-->
個数が使える道具になるのは、数えられたものを一つの対象に保持でき、しかも各位置を名指せるようになってからです。ホストは、噛み合う二つの半分を提供します。ベクトル `Vec A n`{.Agda} は `A` の元をちょうど `n` 個保持し、有限型 `Fin n` はちょうど `n` 個の位置を名指します。長さがベクトルの型の一部なので、保証は構造的です。ある長さのベクトルを期待する関数は、別の長さのベクトルを受け付けられず、型検査器が定理を述べる前にこれを強制します。この対応が、本書における有限の文脈の表現です。とりわけ一階論理の章の変数環境で、自由変数 `n` 個の論理式は、ちょうど `n` 個の値からなる環境のもとで解釈されます。その環境で変数に割り当てられた値を読むことは、その変数の位置での引き出しであり、引き出された値は、本章前半で導入した輸送の機構によって真理値のパスに沿って運ばれることがあります。
<!--/-->

<!--en-->
The first half of the pairing is built so that the length is carried along by the construction itself: the empty vector `[]`{.Agda} has length `zero`{.Agda}, and adjoining an element with `_∷_`{.Agda} raises the length by one. Reading out the element at a position is the operation `lookup`{.Agda}, and its type requires the position to come from the finite type matching the vector's length, so a read is always in range by construction. When a later chapter reads a variable environment at a variable, the mathematical content of that act is one application of `lookup`{.Agda}.
<!--zh-->
配对的前一半的构造方式使长度由构造过程本身携带：空向量 `[]`{.Agda} 的长度是 `zero`{.Agda}，用 `_∷_`{.Agda} 添入一个元素便把长度加一。读取某位置上的元素是运算 `lookup`{.Agda}，其类型要求位置来自与向量长度匹配的有限类型，因此每次读取按构造必然在范围内。后文某章在某个变量处读取变量环境时，这一动作的数学内容就是一次 `lookup`{.Agda} 的应用。
<!--ja-->
対応の前半は、長さが構成そのものによって運ばれるように作られています。空ベクトル `[]`{.Agda} の長さは `zero`{.Agda} で、`_∷_`{.Agda} で元を一つ付け加えると長さが一つ増えます。ある位置の元を読み出すのが演算 `lookup`{.Agda} で、その型は、位置がベクトルの長さと対応する有限型から来ることを要求します。つまり読み出しは構成の段階で必ず範囲内です。後の章がある変数の位置で変数環境を読むとき、その行為の数学的な中身は `lookup`{.Agda} の一回の適用です。
<!--/-->

```agda
open import Cubical.Data.Vec public
  using ( Vec; []; _∷_; lookup )
```

<!--en-->
The other half of the pairing is `Fin n`, the type with exactly `n` elements. In this book those elements play the role of variables of an `n`-variable formula: a variable is a position, not a natural number, and the positions available in an `n`-variable context are precisely the elements of `Fin n`. This is what ties variables to environments: the positions `lookup`{.Agda} accepts on a vector of length `n` are indexed by the same `Fin n` that types the variables, so reading a variable in an environment is type-correct by construction. An arity `n` fixes the available slots; a formula may leave some slots unused, and the count `n` says how many are available, not how many actually occur.
<!--zh-->
配对的另一半是 `Fin n`，恰有 `n` 个元素的类型。在本书中，这些元素充当 `n` 元公式的变量：变量是位置，不是自然数，而 `n` 元语境可用的位置恰是 `Fin n` 的元素。这正是变量与环境相系之处：长度为 `n` 的向量上 `lookup`{.Agda} 接受的位置，与给变量定型的是同一个 `Fin n`，因此在环境中读取变量按构造就是类型正确的。元数 `n` 固定的是可用槽位；公式可以留下未用的槽位，数目 `n` 说的是有多少槽位可用，而非实际出现多少个变量。
<!--ja-->
対応のもう半分が `Fin n`、元をちょうど `n` 個持つ型です。本書では、その元が `n` 変数論理式の変数の役割を果たします。変数は自然数ではなく位置であり、`n` 変数の文脈で使える位置がまさに `Fin n` の元です。これが変数と環境を結びつけます。長さ `n` のベクトルで `lookup`{.Agda} が受け付ける位置は、変数の型でもある同じ `Fin n` で添字付けされるため、環境での変数の読み出しは構成の段階で型整合です。アリティ `n` が固定するのは使える槽です。論理式が槽を使い切らないこともあり、数 `n` はいくつの槽が使えるかを言うのであって、実際に現れる変数の個数を言うのではありません。
<!--/-->

<!--en-->
The elements of `Fin n` are generated in the same inductive shape as the count `n` itself: the zero-th position, and the successor of a position. Since the constructor names are shared with the natural numbers, the expected type settles each occurrence in the code: where the checker expects a natural number the natural-number constructor is meant, and where it expects a finite index the finite one is.
<!--zh-->
`Fin n` 的元素以与计数 `n` 本身相同的归纳形状生成：第零个位置，以及某个位置的后继。由于构造子名与自然数共用，代码中每一处指哪一个由期望的类型决定：检查器期望自然数时指自然数构造子，期望有限指标时指有限型构造子。
<!--ja-->
`Fin n` の元は、個数 `n` 自身と同じ帰納的な形で生成されます。第零の位置と、ある位置の後続です。構成子の名前は自然数と共用なので、コード中の各出現がどちらを指すかは期待される型で決まります。自然数を期待する箇所では自然数の構成子を、有限添字を期待する箇所では有限型の構成子を指します。
<!--/-->

```agda
open import Cubical.Data.FinData public
  using ( Fin; zero; suc )
```

<!--en-->
One type remains, with a role unlike every type before it: the empty type `⊥*`{.Agda}, the type with no inhabitants. In proofs it serves as the target at which impossible cases are discharged. When an analysis branches, for example over the shape of a number, and one branch presupposes something that cannot happen, the hypothesis of that branch is itself an element of an empty type, and mapping it into `⊥*`{.Agda} discharges the branch. The empty type also connects back to the equality machinery: a proposed position outside a context, or a branch no constructor can supply, yields an element of an empty type, and from there any desired statement follows. Note the star: this is a host-layer **type**, polymorphic in the universe level, not the truth value `⊥` of the next chapter. The distinction matters throughout the book: `⊥*`{.Agda} has no inhabitants at all, while a truth value is an element of the truth algebra, a different kind of object.
<!--zh-->
还剩一个类型，其角色与前面所有类型都不同：空类型 `⊥*`{.Agda}，不含任何元素的类型。在证明中，它充当不可能情形被消解时的行靶。当分析分支，例如按数的形状分支，而某个分支预设了不可能发生的事时，该分支的假设本身就是空类型的元素，把它映入 `⊥*`{.Agda} 便消解了这个分支。空类型也与前面的相等机制相接：语境之外的一个所谓位置，或任何构造子都无法给出的分支，都给出空类型的一个元素，由此任何想要的陈述都能得出。注意星号：这是宿主层的**类型**，对宇宙层级多态，不是下一章的真值 `⊥`。这一区别贯穿全书：`⊥*`{.Agda} 不含任何元素，而真值是真值代数中的元素，属于另一种对象。
<!--ja-->
もう一つ、これまでのどの型とも役割の違う型が残っています。空型 `⊥*`{.Agda}、要素をひとつも持たない型です。証明の中では、ありえない場合が処理されるときの行き先として働きます。たとえば数の形について分析が場合分けをするとき、ある分支が起こりえないことを前提としてしまうなら、その分支の仮定自身が空型の元であり、それを `⊥*`{.Agda} へ写すことでその分支は処理されます。空型は、先の等式の機構ともつながります。文脈の範囲外とされる位置や、どの構成子も与えられない分支は空型の元を与え、そこからは望むどんな主張でも従います。星印に注意してください。これは宇宙レベルに対して多相なホスト言語の**型**であり、次章の真理値 `⊥` ではありません。この区別は本全体を通じて重要です。`⊥*`{.Agda} にはそもそも要素がありませんが、真理値は真理値代数の要素であり、別種の対象です。
<!--/-->

<!--en-->
Alongside the empty type itself comes `isProp⊥*`{.Agda}, the proof that `⊥*`{.Agda} is a proposition. This matters where a statement built on the empty type must be known to be proposition-valued before the h-level machinery from earlier in the chapter applies to it; the emptiness itself is not what is at stake there. Because the type is polymorphic in the universe level, the same empty type serves at whichever level a later definition requires.
<!--zh-->
与空类型本身一同而来的是 `isProp⊥*`{.Agda}，即 `⊥*`{.Agda} 是命题的证明。在若干地方，建立于空类型之上的陈述必须先被知道取命题值，本章前文的 h-层级机制才能应用于它；在那里起作用的不是空性本身。由于该类型对宇宙层级多态，后文任何定义需要哪个层级，同一个空类型就能在那个层级上使用。
<!--ja-->
空型そのものとともに来るのが `isProp⊥*`{.Agda}、`⊥*`{.Agda} が命題であることの証明です。効いてくるのは、空型の上に築かれた主張が命題値をとると先に分かっていなければ、本章前半の h-レベルの機構を適用できないような箇所です。そこで争点になるのは空さそのものではありません。この型は宇宙レベルに対して多相なので、後の定義がどのレベルを必要としても、同じ空型をそのレベルで使えます。
<!--/-->

```agda
open import Cubical.Data.Empty public
  using ( ⊥*; isProp⊥* )
```

<!--en-->
The only function defined in this chapter is the smallest one imaginable: the level-polymorphic identity function. It serves as the book's canonical constant interpretation: a constant standing for the very set it names is interpreted precisely as `id`{.Agda}. Keep in mind the distinction between the object-language constant and its host-language interpretation: `id`{.Agda} lives on the interpretation side.
<!--zh-->
本章定义的唯一一个函数是层级多态的恒等函数 `id`{.Agda}。它用作本书的典范常元解释：将常元解释为该常元所指名的集合。请留意对象语言的常元与宿主语言解释的区别：`id`{.Agda} 属于解释一侧。
<!--ja-->
本章で定義する唯一の関数は、想像しうる最も小さいもの、レベル多相な恒等関数 `id`{.Agda} です。これは本書の正準な定数解釈として使われます。自分が指し示す集合そのものを表す定数は、まさに `id`{.Agda} として解釈されます。対象言語の定数とホスト言語での解釈の区別に注意してください。`id`{.Agda} は解釈の側に属します。
<!--/-->

<!--en-->
The type signature fixes the three ingredients: an implicit universe level `ℓ`{.Agda}, an implicit type `A`{.Agda} at that level, and a function from `A`{.Agda} back to `A`{.Agda}. Nothing constrains `A`{.Agda}, so `id`{.Agda} applies to sets, propositions, functions, whatever a later definition needs.
<!--zh-->
该类型签名确定三个成分：隐式的宇宙层级 `ℓ`{.Agda}、该层级上的隐式类型 `A`{.Agda}，以及从 `A`{.Agda} 到 `A`{.Agda} 的函数。对 `A`{.Agda} 没有任何约束，因此 `id`{.Agda} 可作用于集合、命题、函数，即后续定义所需的任何类型。
<!--ja-->
この型シグネチャは三つの要素を固定します。暗黙の宇宙レベル `ℓ`{.Agda}、そのレベルの暗黙の型 `A`{.Agda}、そして `A`{.Agda} から `A`{.Agda} への関数です。`A`{.Agda} には何の制約もないので、`id`{.Agda} は集合、命題、関数など、後の定義が必要とするどんな型にも適用できます。
<!--/-->

```agda
id : ∀ {ℓ} {A : Type ℓ} → A → A
```

<!--en-->
The defining equation says that the function returns its argument unchanged; this is the complete definition, and no clause for cases is needed. When a constant of the first-order language is later interpreted by naming a specific set, choosing `id`{.Agda} as the interpretation function records that the denotation is exactly the named set.
<!--zh-->
定义等式说明该函数原样返回其变元；这就是完整的定义，无需对情形分类。当一阶语言的常元随后被解释为指称某个特定集合时，选择 `id`{.Agda} 作为解释函数，即记录了其指称恰为被指名的那个集合。
<!--ja-->
定義等式は、この関数が引数をそのまま返すことを述べます。これが定義のすべてで、場合分けの節は不要です。後で一階言語の定数を特定の集合の名指しとして解釈するとき、解釈関数として `id`{.Agda} を選ぶことは、その指示対象が名指された集合そのものであることを記録します。
<!--/-->

```agda
id x = x
```

<!--en-->
## Recap

In scope from here on: universes, paths, h-levels, `hProp`{.Agda} with `⟨_⟩`{.Agda} and the class membership `∈ᶜ`{.Agda}, pairs, `ℕ`{.Agda}, `Vec`{.Agda}, `Fin`{.Agda}, `⊥*`{.Agda}, and the identity `id`{.Agda}. This chapter proves nothing, defines only `id`{.Agda}, and introduces no logic symbols: every notion of the book is introduced in the chapter where it is first needed, and the logic arrives with the truth algebra, next.
<!--zh-->
## 小结

自此进入作用域的有：宇宙、路径、h-层级、`hProp`{.Agda} 与 `⟨_⟩`{.Agda} 及类隶属 `∈ᶜ`{.Agda}、对与积、`ℕ`{.Agda}、`Vec`{.Agda}、`Fin`{.Agda}、`⊥*`{.Agda}，以及恒等 `id`{.Agda}。本章不证明任何东西，定义的只有 `id`{.Agda}，也没有引入逻辑符号：每个概念都在首次需要它的章节引入，逻辑符号将在下一章随真值代数一同引入。
<!--ja-->
## まとめ

以後は、宇宙、パス、h-レベル、`hProp`{.Agda} と `⟨_⟩`{.Agda}、クラス所属 `∈ᶜ`{.Agda}、積、`ℕ`{.Agda}、`Vec`{.Agda}、`Fin`{.Agda}、`⊥*`{.Agda}、恒等写像 `id`{.Agda} を共通語彙として使います。本章で証明したものはなく、定義したのも `id`{.Agda} だけで、論理記号は一切導入していません。本書の各概念は、それが最初に必要となる章で導入され、論理は次章の真理値代数とともに登場します。
<!--/-->
