<!--en-->
# The classical boundary

In a universe-leveled type theory, propositions raise two distinct smallness questions. First, fixing a proposition `P : hProp (ℓ-suc ℓ)`{.Agda}, can we find an equivalent proposition one level down? That is propositional resizing: it speaks proposition by proposition. Second, the type `hProp ℓ`{.Agda} of all level-`ℓ` propositions itself lives in `Type (ℓ-suc ℓ)`{.Agda}; can the whole totality be presented by one small type? That is the small classifier. The two claims have different shapes, and this chapter proves both from one explicit hypothesis.

The hypothesis is excluded middle: every proposition is either true or false. Cubical type theory does not assume it, so each classical proof here receives it as an explicit parameter and records exactly which level instance it uses.
<!--zh-->
# 经典逻辑的边界

在带宇宙层级的类型论中，命题引出两个不同的小性问题。第一，固定命题 `P : hProp (ℓ-suc ℓ)`{.Agda}，能否找到低一层宇宙中与之等价的命题？这就是命题降层：它逐个命题发言。第二，全体 `ℓ` 层命题的类型 `hProp ℓ`{.Agda} 本身住在 `Type (ℓ-suc ℓ)`{.Agda} 中；能否用一个小类型呈现整个总体？这就是小分类器。两项断言形状不同，本章由一条显式假设同时证明二者。

这条假设是排中律：每个命题要么真要么假。Cubical 类型论并不预设它，因此这里的每个经典证明都把它作为显式参数接收，并准确记录使用的是哪个层级的实例。
<!--ja-->
# 古典論理との境界

宇宙レベルをもつ型理論では、命題について二つの異なる小ささの問題が生じます。第一に、命題 `P : hProp (ℓ-suc ℓ)`{.Agda} を固定したとき、一つ下のレベルに同値な命題を見つけられるか。これが命題リサイズで、命題ごとに語る主張です。第二に、レベル `ℓ` の命題全体の型 `hProp ℓ`{.Agda} 自身が `Type (ℓ-suc ℓ)`{.Agda} に住んでいます。この全体を一つの小さな型で提示できるか。これが小分類子です。二つの主張は形が異なりますが、本章は一つの明示的な仮定から両方を証明します。

その仮定が排中律、つまりすべての命題は真か偽かのどちらかだという原理です。Cubical 型理論は排中律を仮定しないため、ここでの古典的な証明はそれぞれそれを明示的な引数として受け取り、どのレベルの実例を使ったかを正確に記録します。
<!--/-->

<!--en-->
Excluded middle is not built into the surrounding type theory. Here it is an explicit hypothesis at a specified universe level, so each result states exactly which family of propositions it can decide. This keeps the constructive definitions separate from the classical step that later supplies their decisions.
<!--zh-->
排中律并未内置于周围的类型论中。这里把它作为指定宇宙层级上的显式假设，因此每项结果都准确表明自己能够判定哪一族命题。这样，构造性的定义便与稍后为其提供判定的经典步骤清楚分开。
<!--ja-->
排中律は周囲の型理論に組み込まれていません。ここでは指定した宇宙レベルの明示的な仮定として受け取るので、各結果はどの命題の族を判定できるかを正確に示します。これにより、構成的な定義と、後でその判定を与える古典的な段階とが分かれます。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

module Base.Classical where
```

<!--en-->
The two smallness questions are given exact shapes in Base.Impredicativity, and this chapter uses that vocabulary unchanged. For a single proposition, `isSmall P` packages a lower-level proposition `Q : hProp ℓ`{.Agda} together with an equivalence of underlying types `⟨ P ⟩ ≃ ⟨ Q ⟩`{.Agda}. The uniform statements then differ in what they quantify over: `Resizing ℓ` asks that every `P : hProp (ℓ-suc ℓ)`{.Agda} carry such data, while `HPropSmallness ℓ` asks for a single type `Ω' : Type ℓ`{.Agda} equivalent to the whole `hProp ℓ`{.Agda} at once. One is a family of per-proposition witnesses, the other one carrier for the totality; this chapter derives each from excluded middle without claiming that either entails the other.
<!--zh-->
两个小性问题在 Base.Impredicativity 中被赋予精确形状，本章原样使用那套词汇。对单个命题，`isSmall P` 打包一个低层命题 `Q : hProp ℓ`{.Agda} 与底层类型间的等价 `⟨ P ⟩ ≃ ⟨ Q ⟩`{.Agda}。两个统一陈述的区别在于量化的对象：`Resizing ℓ` 要求每个 `P : hProp (ℓ-suc ℓ)`{.Agda} 都带有这样的数据，而 `HPropSmallness ℓ` 要求一个与整个 `hProp ℓ`{.Agda} 同时等价的类型 `Ω' : Type ℓ`{.Agda}。前者是逐命题见证的族，后者是呈现总体的单一载体；本章从排中律分别导出二者，而不声称其中一项蕴含另一项。
<!--ja-->
二つの小ささの問題は Base.Impredicativity で正確な形を与えられ、本章はその語彙をそのまま使います。単一の命題に対して `isSmall P` は、低いレベルの命題 `Q : hProp ℓ`{.Agda} と基礎型の間の同値 `⟨ P ⟩ ≃ ⟨ Q ⟩`{.Agda} をまとめて持ちます。一様な主張は何を量化するかで異なります。`Resizing ℓ` はすべての `P : hProp (ℓ-suc ℓ)`{.Agda} がそのようなデータを持つことを要求し、`HPropSmallness ℓ` は全体の `hProp ℓ`{.Agda} と一度に同値な型 `Ω' : Type ℓ`{.Agda} を一つ要求します。前者は命題ごとの証拠の族、後者は全体を提示する単一の台です。本章は排中律から両者をそれぞれ導きますが、一方が他方を含意するとは主張しません。
<!--/-->

```agda

open import Base.Prelude
open import Base.Impredicativity
  using ( isSmall; Resizing; HPropSmallness; Impredicativity )
```

<!--en-->
A decision is small data with a precise type: it is either an inhabitant of the proposition, or a map from the proposition into the empty type, which refutes it. The coproduct `_⊎_`{.Agda} with its two constructors carries exactly this either-or. The Boolean type `Bool`{.Agda} with `true`{.Agda} and `false`{.Agda} will label the two possible truth values, and `tt*`{.Agda} is the lone inhabitant of the unit type that underlies the truth value true.
<!--zh-->
判定是类型精确的小数据：它要么是命题的一个元素，要么是把命题映入空类型从而反驳它的映射。余积 `_⊎_`{.Agda} 及其两个构造子承载的正是这种二选一。布尔类型 `Bool`{.Agda} 与 `true`{.Agda}、`false`{.Agda} 将为两个可能的真值贴标签，而 `tt*`{.Agda} 是真值「真」底层单元类型的唯一元素。
<!--ja-->
判定は型が正確な小さなデータです。命題の元であるか、命題を空型へ写すことで反証する写像であるか、のどちらかです。直和 `_⊎_`{.Agda} とその二つの構成子が担うのはまさにこの二者択一です。ブール型 `Bool`{.Agda} と `true`{.Agda}、`false`{.Agda} は二つの可能な真理値にラベルを付け、`tt*`{.Agda} は真の真理値の底にある単元型の唯一の元です。
<!--/-->

```agda
open import Cubical.Data.Sum using ( _⊎_; inl; inr )
import Cubical.Data.Empty as Empty
open import Cubical.Data.Bool using ( Bool; true; false )
open import Cubical.Data.Unit using ( tt* )
```

<!--en-->
Building the smallness witnesses needs one more thing: how maps between propositions become identities and equivalences. Between two propositions, a pair of maps in both directions can be turned into a path `⇔toPath`{.Agda} (propositional extensionality) or into an equivalence of underlying types `propBiimpl→Equiv`{.Agda}. An isomorphism `iso`{.Agda} packages two maps with the two inverse laws, and `isoToEquiv`{.Agda} reads it as an equivalence. These are the forms of sameness used in the constructions below.
<!--zh-->
构造小性见证还需要一件事：命题之间的映射如何变成同一性与等价。在两个命题之间，双向的一对映射既可以变成路径 `⇔toPath`{.Agda} (命题外延性)，也可以变成底层类型间的等价 `propBiimpl→Equiv`{.Agda}。同构 `iso`{.Agda} 把两个映射与两条逆律打包在一起，`isoToEquiv`{.Agda} 再把它读作等价。下面的构造使用这些形式的「相同」。
<!--ja-->
小ささの証拠を作るにはもう一つ必要なものがあります。命題の間の写像がどう同一性や同値になるかです。二つの命題の間では、両方向の写像の組はパス `⇔toPath`{.Agda} (命題外延性) にも、基礎型の間の同値 `propBiimpl→Equiv`{.Agda} にもなります。同型 `iso`{.Agda} は二つの写像と二つの逆法則を束ね、`isoToEquiv`{.Agda} がそれを同値として読みます。以下の構成では、このような形の「同じである」を用います。
<!--/-->

```agda
open import Cubical.Foundations.Equiv using ( propBiimpl→Equiv )
open import Cubical.Foundations.Isomorphism using ( iso; isoToEquiv )
open import Cubical.Functions.Logic using ( ⇔toPath )
```

<!--en-->
## The statement

Before proving anything, the assumption must be stated with its universe level pinned down. The level index is not decoration: it says at which universe the uniform decision is demanded, and every later theorem can be read off for which classical instance it asks.
<!--zh-->
## 陈述

在证明任何东西之前，必须先把假设连同其宇宙层级陈述清楚。层级指标不是装饰：它说明在哪个宇宙上要求统一判定，后续每个定理都在向读者交代它需要哪个经典实例。
<!--ja-->
## 排中律の主張

何かを証明する前に、仮定を宇宙レベルとともに正確に述べておく必要があります。レベルの添字は飾りではありません。どの宇宙で一様な判定を要求するかを告げており、後の定理はどの古典的実例を求めているのかを読み取ることができます。
<!--/-->

<!--en-->
For each universe level `ℓ`, `LEM ℓ`{.Agda} is a function taking a proposition `P : hProp ℓ`{.Agda} and returning either a proof of `⟨ P ⟩`{.Agda} or a refutation, that is, a map from `⟨ P ⟩`{.Agda} into the empty type. Because it quantifies over all propositions of `hProp ℓ`{.Agda}, its type lives one universe up, in `Type (ℓ-suc ℓ)`{.Agda}. So the statement itself is large, even though each decision it delivers is a single small piece of data, and `LEM ℓ` is asserted one level at a time rather than for all levels at once.
<!--zh-->
对每个宇宙层级 `ℓ`，`LEM ℓ`{.Agda} 是一个函数：取命题 `P : hProp ℓ`{.Agda}，返回 `⟨ P ⟩`{.Agda} 的证明，或一个反驳，即从 `⟨ P ⟩`{.Agda} 映入空类型的映射。由于它量化了 `hProp ℓ`{.Agda} 的所有命题，其类型位于高一层宇宙 `Type (ℓ-suc ℓ)`{.Agda}。因此这个陈述本身是大的，尽管它产出的每个判定都只是一小段数据；而且 `LEM ℓ` 是逐层陈述的，不是同时对所有层级断言。
<!--ja-->
各宇宙レベル `ℓ` に対して `LEM ℓ`{.Agda} は、命題 `P : hProp ℓ`{.Agda} を受け取り、`⟨ P ⟩`{.Agda} の証明か、あるいは `⟨ P ⟩`{.Agda} を空型へ写す反証のどちらかを返す関数です。`hProp ℓ`{.Agda} のすべての命題を量化するため、その型は一つ上の宇宙 `Type (ℓ-suc ℓ)`{.Agda} に住みます。つまり主張そのものは大きくても、生み出される個々の判定は小さなデータのひと塊にすぎず、さらに `LEM ℓ` は全レベル一度にではなく一レベルずつ主張されます。
<!--/-->

```agda
LEM : ∀ ℓ → Type (ℓ-suc ℓ)
LEM ℓ = (P : hProp ℓ) → ⟨ P ⟩ ⊎ (⟨ P ⟩ → Empty.⊥)
```

<!--en-->
The applications will need excluded middle at two different levels, but a proof is often handed only the higher instance `LEM (ℓ-suc ℓ)`{.Agda}. One descent lemma bridges the gap. It is a one-step result, exactly `LEM (ℓ-suc ℓ) → LEM ℓ`{.Agda}: to decide a proposition `P : hProp ℓ`{.Agda}, move its underlying type up one universe, decide the moved proposition there, and bring the verdict back down. Nothing here claims that decisions descend through arbitrarily many levels at once.
<!--zh-->
后面的应用需要在两个不同层级上的排中律，而证明往往只拿到高层实例 `LEM (ℓ-suc ℓ)`{.Agda}。一条降层引理正好补上这个缺口。它是恰好一步的结果，即 `LEM (ℓ-suc ℓ) → LEM ℓ`{.Agda}：要判定命题 `P : hProp ℓ`{.Agda}，把其底层类型抬高一层宇宙，对移动后的命题判定，再把裁决降回来。这里不声称判定可以一次跨越任意多层下降。
<!--ja-->
この後の応用には二つの異なるレベルの排中律が必要になりますが、証明に渡されるのはしばしば高い方の実例 `LEM (ℓ-suc ℓ)`{.Agda} だけです。一段の降下補題がその差を埋めます。結果は正確に一段分、すなわち `LEM (ℓ-suc ℓ) → LEM ℓ`{.Agda} です。命題 `P : hProp ℓ`{.Agda} を判定するには、その基礎型を一つ上の宇宙へ動かし、動かした命題をそこで判定し、判定結果を降ろしてきます。判定が一度に任意の段数を降りるとは主張しません。
<!--/-->

<!--en-->
Given `lem : LEM (ℓ-suc ℓ)`{.Agda} and a proposition `P : hProp ℓ`{.Agda}, the plan is to apply `lem` not to `P` itself but to a lifted copy of `P` living at level `ℓ-suc ℓ`, where the hypothesis applies. The verdict about the copy is then translated back into a verdict about `P`.
<!--zh-->
给定 `lem : LEM (ℓ-suc ℓ)`{.Agda} 与命题 `P : hProp ℓ`{.Agda}，计划不是把 `lem` 用在 `P` 本身上，而是用在住在 `ℓ-suc ℓ` 层、因而假设可适用的 `P` 的抬升副本上，然后再把关于副本的裁决翻译回关于 `P` 的裁决。
<!--ja-->
`lem : LEM (ℓ-suc ℓ)`{.Agda} と命題 `P : hProp ℓ`{.Agda} が与えられたときの計画は、`lem` を `P` 自身ではなく、レベル `ℓ-suc ℓ` に住み仮定が適用できる `P` の持ち上げられたコピーに適用し、そのコピーについての判定を `P` についての判定へ翻訳し戻す、というものです。
<!--/-->

```agda
lowerLEM : ∀ {ℓ} → LEM (ℓ-suc ℓ) → LEM ℓ
lowerLEM {ℓ} lem P = fromLifted (lem lifted)
```

<!--en-->
The lifted proposition has underlying type `Lift ⟨ P ⟩`{.Agda}. Its elements are the elements of `⟨ P ⟩`{.Agda} in the higher universe, and it is a proposition: for elements `x` and `y`, lower both with `lower`, use the propositionhood `P .snd` of `P` to get a path between the lowerings, and apply `cong lift` to lift that path back up. So `lifted` is a legitimate input to `lem`.
<!--zh-->
抬升后的命题底层类型为 `Lift ⟨ P ⟩`{.Agda}，其元素就是高一层宇宙中的 `⟨ P ⟩`{.Agda} 元素，而且它是命题：对元素 `x` 与 `y`，先用 `lower` 把二者降到 `⟨ P ⟩`，用 `P` 的命题性 `P .snd` 得到降像之间的路径，再用 `cong lift` 把该路径抬回上层。于是 `lifted` 是 `lem` 的合法输入。
<!--ja-->
持ち上げられた命題の基礎型は `Lift ⟨ P ⟩`{.Agda} で、その元は一つ上の宇宙における `⟨ P ⟩`{.Agda} の元です。そしてこれは命題です。元 `x` と `y` に対し、`lower` で両者を `⟨ P ⟩` へ降ろし、`P` の命題性 `P .snd` で降ろしたもの同士のパスを得て、`cong lift` でそのパスを上の宇宙へ持ち上げます。こうして `lifted` は `lem` の正当な入力になります。
<!--/-->

```agda
  where
  lifted : hProp (ℓ-suc ℓ)
  lifted = Lift ⟨ P ⟩ , λ x y → cong lift (P .snd (lower x) (lower y))
```

<!--en-->
Translating the verdict needs only `lift` and `lower`, and these travel in the right directions. A proof of `Lift ⟨ P ⟩`{.Agda} lowers with `lower` to a proof of `⟨ P ⟩`{.Agda}. A refutation of `Lift ⟨ P ⟩`{.Agda} composed with `lift` becomes a refutation of `⟨ P ⟩`{.Agda}, since it applies to any proof of `⟨ P ⟩`{.Agda} after lifting. Both cases are pure transport of the decision, with no classical reasoning of their own; the classical step was deciding the lifted proposition.
<!--zh-->
翻译裁决只需要 `lift` 与 `lower`，而它们的方向恰好合适。`Lift ⟨ P ⟩`{.Agda} 的证明经 `lower` 降为 `⟨ P ⟩`{.Agda} 的证明；`Lift ⟨ P ⟩`{.Agda} 的反驳与 `lift` 复合后成为 `⟨ P ⟩`{.Agda} 的反驳，因为它在抬升之后适用于 `⟨ P ⟩`{.Agda} 的任何证明。两种情形都是判定的纯粹搬运，自身不含经典推理；经典的步骤是判定那个抬升后的命题。
<!--ja-->
判定の翻訳に必要なのは `lift` と `lower` だけで、両者はちょうど正しい方向へ進みます。`Lift ⟨ P ⟩`{.Agda} の証明は `lower` で `⟨ P ⟩`{.Agda} の証明へ降り、`Lift ⟨ P ⟩`{.Agda} の反証は `lift` との合成で `⟨ P ⟩`{.Agda} の反証になります。持ち上げた後に `⟨ P ⟩`{.Agda} の任意の証明へ適用できるからです。どちらの場合も判定を運ぶだけの純粋な変換であり、ここに古典的推論はありません。古典的な一歩は、持ち上げられた命題を判定したところで起こっています。
<!--/-->

```agda
  fromLifted : ⟨ lifted ⟩ ⊎ (⟨ lifted ⟩ → Empty.⊥) → ⟨ P ⟩ ⊎ (⟨ P ⟩ → Empty.⊥)
  fromLifted (inl p)  = inl (lower p)
  fromLifted (inr np) = inr (λ p → np (lift p))
```

<!--en-->
## A small classifier from excluded middle

Classically, every proposition at a fixed level is one of two things: true or false. That suggests a two-point classifier. The candidate small representative is `Lift Bool`{.Agda}, with `true`{.Agda} representing the proposition true and `false`{.Agda} representing the proposition false. Two warnings keep the picture honest. A Boolean is a label; the proposition it represents is a separate `hProp` value, and the classifier equates them only up to paths between `hProp` values, never by syntactic identity. And the two endpoints have different sizes: `Lift Bool`{.Agda} lives in `Type ℓ`{.Agda} while `hProp ℓ`{.Agda} lives in `Type (ℓ-suc ℓ)`{.Agda}; an equivalence is allowed to relate types at different levels, and that size gap is precisely the smallness being established.

The construction splits cleanly. Decoding sends each Boolean to its representative proposition. Encoding needs to know, for a given `P`, which case holds, so it takes the decision of `P` as an explicit argument; the two inverse laws are then proved for that data. Excluded middle enters only at the end, to supply such decisions uniformly.
<!--zh-->
## 由排中律得到小分类器

在经典观点下，固定层级的每个命题只有两种可能：真或假。这提示了一个两点的分类器。小代表取 `Lift Bool`{.Agda}，其中 `true`{.Agda} 代表命题「真」，`false`{.Agda} 代表命题「假」。有两点提醒使图景保持准确。布尔值只是标签；它所代表的命题是另一个 `hProp` 值，分类器只按 `hProp` 值之间的路径把它们等同，绝不按语法上的同一。并且两端大小不同：`Lift Bool`{.Agda} 住在 `Type ℓ`{.Agda}，而 `hProp ℓ`{.Agda} 住在 `Type (ℓ-suc ℓ)`{.Agda}；等价可以联系不同层级的类型，这个大小差正是所要建立的小性。

构造分成干净的两步。解码把每个布尔值送到它代表的命题。编码则需要知道给定的 `P` 属于哪种情形，因此把 `P` 的判定作为显式参数；两条逆律随后针对这份数据证明。排中律只在最后出现，用于一致地供给这些判定。
<!--ja-->
## 排中律から得られる小分類子

古典的な見方では、固定したレベルの命題は真か偽かの二つのどちらかです。そこで自然に浮かぶのが二点からなる分類子です。小さな代表の候補は `Lift Bool`{.Agda} で、`true`{.Agda} が真という命題を、`false`{.Agda} が偽という命題を代表します。ここで二つの注意が必要です。ブール値はラベルにすぎず、それが代表する命題は別の `hProp` 値であり、分類子が両者を同一視するのは `hProp` 値の間のパスに関してであって、構文的な同一によってではありません。また両端の大きさは異なります。`Lift Bool`{.Agda} は `Type ℓ`{.Agda} に、`hProp ℓ`{.Agda} は `Type (ℓ-suc ℓ)`{.Agda} に住み、同値は異なるレベルの型を結んでもよく、この大きさの差こそが確立される小ささです。

構成はきれいに二段に分かれます。復号は各ブール値をその代表である命題へ送ります。符号化には、与えられた `P` がどちらの場合かを知る必要があるので、`P` の判定を明示的な引数として受け取ります。二つの逆法則はそのデータに対して証明されます。排中律が現れるのは最後だけで、判定を一様に供給するためです。
<!--/-->

<!--en-->
The two representative propositions are the canonical top proposition `⊤`{.Agda} and bottom proposition `⊥`{.Agda}. The latter is definitionally the pair `(⊥* , isProp⊥*)`{.Agda}, so its underlying type is the empty type `⊥*`{.Agda}. These two are exactly what the Boolean labels will denote.
<!--zh-->
两个代表命题是 `hProp` 中典范的顶命题 `⊤`{.Agda} 与底命题 `⊥`{.Agda}。后者按定义就是对 `(⊥* , isProp⊥*)`{.Agda}，因此其底层类型是空类型 `⊥*`{.Agda}。布尔标签要指称的正是这两个命题。
<!--ja-->
二つの代表命題は、`hProp` における正準な頂命題 `⊤`{.Agda} と底命題 `⊥`{.Agda} です。後者は定義上、対 `(⊥* , isProp⊥*)`{.Agda} そのものであり、その基礎型は空型 `⊥*`{.Agda} です。ブールのラベルが指すのはまさにこの二つの命題です。
<!--/-->

```agda

private
  decodeB : ∀ {ℓ} → Lift {ℓ-zero} {ℓ} Bool → hProp ℓ
```

<!--en-->
Decoding reads a Boolean label and returns the proposition it represents: `lift true`{.Agda} yields `⊤`{.Agda} and `lift false`{.Agda} yields `⊥`{.Agda}. The domain is the lift `Lift {ℓ-zero} {ℓ} Bool`{.Agda} rather than `Bool`{.Agda} itself: `Bool`{.Agda} lives in `Type ℓ-zero`, and its lift is a type of `Type ℓ`, which is what the classifier's statement demands. Note that decoding alone is only a function assigning representatives; that the assignment is faithful in both directions is the content of the two inverse laws below.
<!--zh-->
解码读取布尔标签，返回它所代表的命题：`lift true`{.Agda} 给出 `⊤`{.Agda}，`lift false`{.Agda} 给出 `⊥`{.Agda}。定义域是提升 `Lift {ℓ-zero} {ℓ} Bool`{.Agda} 而非 `Bool`{.Agda} 本身：`Bool`{.Agda} 住在 `Type ℓ-zero`，其提升是 `Type ℓ` 中的类型，这正是分类器陈述所要求的。注意，单独的解码只是一个指派代表的函数；这个指派在两个方向上都忠实，是下面两条逆律的内容。
<!--ja-->
復号はブールのラベルを読んで、それが代表する命題を返します。`lift true`{.Agda} は `⊤`{.Agda} を、`lift false`{.Agda} は `⊥`{.Agda} を返します。定義域は `Bool`{.Agda} 自身ではなく持ち上げの `Lift {ℓ-zero} {ℓ} Bool`{.Agda} です。`Bool`{.Agda} は `Type ℓ-zero` に住み、その持ち上げは `Type ℓ` の型であり、分類子の主張が要求するのはこちらです。復号だけなら代表を割り当てる関数にすぎず、その割り当てが両方向で忠実であることは、後に続く二つの逆法則の内容です。
<!--/-->

```agda
  decodeB (lift true)  = ⊤
  decodeB (lift false) = ⊥
```

<!--en-->
Encoding is the converse assignment: given `P` and a decision of `P`, return the label of the winning case. The decision is an explicit argument, not something the encoder produces itself, so this step uses no excluded middle. Choosing a representative for `P` is thus a two-step affair in general: first decide `P`, then read off the label. The two inverse laws will show the round trips are the identity, one on propositions and one on labels.
<!--zh-->
编码是相反方向的指派：给定 `P` 与 `P` 的一个判定，返回获胜情形的标签。判定是显式参数而非编码器自己产出的，所以这一步不使用排中律。一般而言，为 `P` 选代表是两步的事：先判定 `P`，再读出标签。两条逆律将表明这两趟往返各自是恒等，一趟在命题上，一趟在标签上。
<!--ja-->
符号化は逆向きの割り当てです。`P` と `P` の判定が与えられれば、勝った場合のラベルを返します。判定は明示的な引数であり、符号化器自身が作り出すものではないので、この段階で排中律は使いません。一般に `P` の代表を選ぶのは二段階の作業です。まず `P` を判定し、それからラベルを読み取ります。二つの逆法則は、この往復がそれぞれ恒等であること、一つは命題の上で、もう一つはラベルの上で、示すことになります。
<!--/-->

<!--en-->
The match is on the decision, not on `P`: an inhabitant of the left summand yields `lift true`{.Agda}, one of the right yields `lift false`{.Agda}. The proof or refutation itself is discarded, because the label records only which case held, not a witness. The result type is `Lift {ℓ-zero} {ℓ} Bool`{.Agda}, matching `decodeB`'s domain exactly.
<!--zh-->
匹配对象是判定而非 `P`：左支的元素给出 `lift true`{.Agda}，右支的元素给出 `lift false`{.Agda}。证明或反驳本身被丢弃，因为标签只记录出现的是哪种情形，而不是见证。结果类型是 `Lift {ℓ-zero} {ℓ} Bool`{.Agda}，与 `decodeB` 的定义域严格相配。
<!--ja-->
マッチの対象は `P` ではなく判定です。左の直和項の元なら `lift true`{.Agda} を、右の元なら `lift false`{.Agda} を返します。証明や反証そのものは捨てられます。ラベルが記録するのはどちらの場合だったかだけで、証拠ではないからです。結果の型は `Lift {ℓ-zero} {ℓ} Bool`{.Agda} で、`decodeB` の定義域と正確に一致します。
<!--/-->

```agda
  encodeB : ∀ {ℓ} (P : hProp ℓ) → ⟨ P ⟩ ⊎ (⟨ P ⟩ → Empty.⊥) → Lift {ℓ-zero} {ℓ} Bool
  encodeB P (inl _) = lift true
  encodeB P (inr _) = lift false
```

<!--en-->
The first inverse law says that the representative chosen through a decision has the same truth value as `P`. Concretely, `secB` proves `decodeB (encodeB P d) ≡ P`{.Agda}, a path between `hProp` values. The proof strategy in both cases is the same: give maps in both directions and let propositional extensionality `⇔toPath`{.Agda} assemble the path.
<!--zh-->
第一条逆律说，经由判定选出的代表与 `P` 有相同的真值。具体地，`secB` 证明 `decodeB (encodeB P d) ≡ P`{.Agda}，这是 `hProp` 值之间的一条路径。两种情形的证明策略相同：给出双向的映射，再由命题外延性 `⇔toPath`{.Agda} 组装出路径。
<!--ja-->
最初の逆法則は、判定を通して選ばれた代表が `P` と同じ真理値を持つことを述べます。具体的には `secB` が `decodeB (encodeB P d) ≡ P`{.Agda}、つまり `hProp` 値の間のパスを証明します。どちらの場合も証明の戦略は同じで、両方向の写像を与え、命題外延性 `⇔toPath`{.Agda} にパスを組み立てさせます。
<!--/-->

<!--en-->
If the decision was a proof `p`, the goal is `⊤ ≡ P`{.Agda}. The map from `⊤`{.Agda} to `⟨ P ⟩`{.Agda} is simply `p`, the decided witness; in the reverse direction every input goes to `tt*`{.Agda}, the lone inhabitant of `⊤`{.Agda}. If the decision was a refutation `np`, the goal is `⊥ ≡ P`{.Agda}. Out of `⊥*`{.Agda} there is no constructor to match, which the absurd pattern `λ ()` expresses, and each proof `p` of `⟨ P ⟩`{.Agda} is fed to `np` and eliminated by `Empty.rec`{.Agda}. In both branches the chosen representative is path-equal to `P`, so the encoding round trip loses no truth value.
<!--zh-->
若判定是证明 `p`，目标是 `⊤ ≡ P`{.Agda}。从 `⊤`{.Agda} 到 `⟨ P ⟩`{.Agda} 的映射就是判定所得的见证 `p`；反方向上，所有输入都映到 `⊤`{.Agda} 的唯一元素 `tt*`{.Agda}。若判定是反驳 `np`，目标是 `⊥ ≡ P`{.Agda}。从 `⊥*`{.Agda} 出发没有构造子可匹配，荒谬模式 `λ ()` 表达的正是这一点；`⟨ P ⟩`{.Agda} 的每个证明 `p` 都交给 `np` 并由 `Empty.rec`{.Agda} 消去。两个分支中，所选代表都与 `P` 路径相等，于是编码的往返不丢失任何真值。
<!--ja-->
判定が証明 `p` だった場合、ゴールは `⊤ ≡ P`{.Agda} です。`⊤`{.Agda} から `⟨ P ⟩`{.Agda} への写像は判定で得た証拠 `p` そのものであり、逆方向ではすべての入力が `⊤`{.Agda} の唯一の元 `tt*`{.Agda} に写ります。判定が反証 `np` だった場合、ゴールは `⊥ ≡ P`{.Agda} です。`⊥*`{.Agda} には照合すべき構成子がないことを荒謬パターン `λ ()` が表し、`⟨ P ⟩`{.Agda} の各証明 `p` は `np` に渡され `Empty.rec`{.Agda} で消去されます。どちらの分岐でも選ばれた代表は `P` とパスで等しく、符号化の往復が真理値を失わないことがわかります。
<!--/-->

```agda
  secB : ∀ {ℓ} (P : hProp ℓ) (d : ⟨ P ⟩ ⊎ (⟨ P ⟩ → Empty.⊥))
       → decodeB (encodeB P d) ≡ P
  secB P (inl p)  = ⇔toPath (λ _ → p) (λ _ → tt*)
  secB P (inr np) = ⇔toPath (λ ()) (λ p → Empty.rec (np p))
```

<!--en-->
The second inverse law reads the representative back: `encodeB (decodeB b) d ≡ b`{.Agda}. Here one subtlety is essential. In the assembled classifier the decision `d` will be produced by excluded middle, and nothing guarantees how that decision computes. So `retrB` must hold for **every** decision `d`, not just the ones a particular proof would supply. The proof therefore splits into four cases: two compatible branches compute to `refl`{.Agda}, and two incompatible branches are eliminated as impossible, which also shows the two representatives cannot be confused: `⊤`{.Agda} is inhabited and `⊥`{.Agda} is empty.
<!--zh-->
第二条逆律把代表读回来：`encodeB (decodeB b) d ≡ b`{.Agda}。这里有个关键细节。在组装好的分类器中，判定 `d` 将由排中律产生，而任何东西都不保证那个判定如何计算。所以 `retrB` 必须对**每一个**判定 `d` 成立，而不是只对某个特定证明会供给的判定成立。证明因此分成四种情形：两个相容的分支计算为 `refl`{.Agda}，两个不相容的分支作为不可能而消去；这也表明两个代表不会被混淆，因为 `⊤`{.Agda} 有元素而 `⊥`{.Agda} 为空。
<!--ja-->
第二の逆法則は代表を読み戻します。`encodeB (decodeB b) d ≡ b`{.Agda} です。ここで本質的な注意が一つあります。組み上がった分類子では判定 `d` を排中律が供給しますが、その判定がどのように計算されるかを保証するものは何もありません。したがって `retrB` は、特定の証明が供給しうる判定だけでなく、**すべての**判定 `d` に対して成り立たねばなりません。証明は四つの場合に分かれます。両立する二つの分岐は `refl`{.Agda} に計算され、両立しない二つの分岐は不可能として消去されます。これはまた、`⊤`{.Agda} に要素があり `⊥`{.Agda} が空であることから、二つの代表が混同されえないことも示しています。
<!--/-->

<!--en-->
For `b = lift true`{.Agda}, decoding gives `⊤`{.Agda}. Encoding with a proof returns `lift true`{.Agda}, and the goal is definitionally `refl`{.Agda}. The alleged refutation branch cannot occur: applying it to `tt*`{.Agda}, the inhabitant of `⊤`{.Agda}, would give an element of the empty type, and `Empty.rec`{.Agda} concludes the case from that contradiction.
<!--zh-->
当 `b = lift true`{.Agda} 时，解码得 `⊤`{.Agda}。配以证明编码返回 `lift true`{.Agda}，目标按定义就是 `refl`{.Agda}。所谓反驳的分支不可能出现：把它用于 `⊤`{.Agda} 的元素 `tt*`{.Agda} 会得到空类型的元素，`Empty.rec`{.Agda} 便由这一矛盾结案。
<!--ja-->
`b = lift true`{.Agda} のとき、復号は `⊤`{.Agda} を返します。証明とともに符号化すれば `lift true`{.Agda} が返り、ゴールは定義上 `refl`{.Agda} です。反証の分岐は起こりえません。`⊤`{.Agda} の元 `tt*`{.Agda} に適用すれば空型の元が得られ、`Empty.rec`{.Agda} がこの矛盾から場合を締めくくります。
<!--/-->

```agda
  retrB : ∀ {ℓ} (b : Lift {ℓ-zero} {ℓ} Bool)
          (d : ⟨ decodeB b ⟩ ⊎ (⟨ decodeB b ⟩ → Empty.⊥))
        → encodeB (decodeB b) d ≡ b
  retrB (lift true)  (inl _)  = refl
  retrB (lift true)  (inr n⊤) = Empty.rec (n⊤ tt*)
```

<!--en-->
For `b = lift false`{.Agda}, decoding gives `⊥`{.Agda} with underlying type `⊥*`{.Agda}. An alleged proof of it would be a term of the empty type, so the absurd pattern `()` ends that branch at once; encoding with a refutation returns `lift false`{.Agda}, again by `refl`{.Agda}. Across all four cases, the label returned always equals the label we started from, whichever decision is supplied.
<!--zh-->
当 `b = lift false`{.Agda} 时，解码得 `⊥`{.Agda}，其底层类型为 `⊥*`{.Agda}。它的所谓证明将是空类型的项，荒谬模式 `()` 立即结束该分支；配以反驳编码返回 `lift false`{.Agda}，同样由 `refl`{.Agda} 完成。纵观四种情形，无论供给哪种判定，返回的标签总等于出发时的标签。
<!--ja-->
`b = lift false`{.Agda} のとき、復号は `⊥`{.Agda}、すなわち基礎型 `⊥*`{.Agda} を持つ命題を返します。そのいわゆる証明は空型の項になるはずなので、荒謬パターン `()` がこの分岐を直ちに終わらせ、反証とともに符号化すれば `lift false`{.Agda} が返り、これも `refl`{.Agda} で済みます。四つの場合を通して、どの判定が供給されようとも、返されるラベルは出発点のラベルと等しくなります。
<!--/-->

```agda
  retrB (lift false) (inl ())
  retrB (lift false) (inr _)  = refl
```

<!--en-->
Now the pieces assemble into the classifier promised by `HPropSmallness ℓ`{.Agda}: a type in `Type ℓ`{.Agda} equivalent to `hProp ℓ`{.Agda}. The small type is `Lift Bool`{.Agda}; the equivalence comes from the isomorphism whose forward map is `decodeB`{.Agda} and whose backward map decides `P` and encodes. The two inverse laws are exactly `secB`{.Agda} and `retrB`{.Agda}, each instantiated with decisions from `lem`. This is where excluded middle does its work in this section: it supplies, uniformly, the decisions that the constructive parts take as inputs.
<!--zh-->
现在各部分组装成 `HPropSmallness ℓ`{.Agda} 所承诺的分类器：一个 `Type ℓ`{.Agda} 中的、与 `hProp ℓ`{.Agda} 等价的类型。小类型是 `Lift Bool`{.Agda}；等价来自这样的同构：正向映射是 `decodeB`{.Agda}，反向映射判定 `P` 后编码。两条逆律正是 `secB`{.Agda} 与 `retrB`{.Agda}，各自用来自 `lem` 的判定实例化。排中律在本节的作用就在此处：它一致地供给那些构造性部分作为输入所需的判定。
<!--ja-->
いま部品が `HPropSmallness ℓ`{.Agda} が約束する分類子へと組み上がります。すなわち `Type ℓ`{.Agda} の、`hProp ℓ`{.Agda} と同値な型です。小さな型は `Lift Bool`{.Agda} であり、同値は順方向の写像が `decodeB`{.Agda}、逆方向の写像が `P` を判定して符号化するもので構成されます。二つの逆法則はまさに `secB`{.Agda} と `retrB`{.Agda} で、それぞれ `lem` からの判定で具体化されます。この節で排中律が働くのはここです。構成的な部分が入力として取る判定を、一様に供給するのです。
<!--/-->

<!--en-->
The pair `(Lift Bool , ...)` witnesses `HPropSmallness ℓ`{.Agda}: its first component has type `Type ℓ`{.Agda} and its second is an equivalence `Lift Bool ≃ hProp ℓ`{.Agda}. The level placement is the point: `Lift Bool`{.Agda} : `Type ℓ`{.Agda} while `hProp ℓ`{.Agda} : `Type (ℓ-suc ℓ)`{.Agda}, so a type one universe up acquires a small representative. This is a size statement about levels, not a claim that both sides share a universe; and the equivalence itself rests on the two inverse laws, so a Boolean label and its proposition are identified only up to the paths that `secB` and `retrB` certify.
<!--zh-->
对子 `(Lift Bool , ...)` 是 `HPropSmallness ℓ`{.Agda} 的见证：第一分量类型为 `Type ℓ`{.Agda}，第二分量是等价 `Lift Bool ≃ hProp ℓ`{.Agda}。层级安排正是要点：`Lift Bool`{.Agda} : `Type ℓ`{.Agda} 而 `hProp ℓ`{.Agda} : `Type (ℓ-suc ℓ)`{.Agda}，于是高一宇宙的类型获得了一个小代表。这是关于宇宙层级的尺寸陈述，不是声称两端共享同一个宇宙；而且等价本身依赖两条逆律，因此布尔标签与其命题只是在 `secB` 与 `retrB` 所认证的路径之下被等同。
<!--ja-->
対 `(Lift Bool , ...)` が `HPropSmallness ℓ`{.Agda} の証拠です。第一成分は `Type ℓ`{.Agda} の型で、第二成分は同値 `Lift Bool ≃ hProp ℓ`{.Agda} です。ポイントはレベルの配置にあります。`Lift Bool`{.Agda} : `Type ℓ`{.Agda}、`hProp ℓ`{.Agda} : `Type (ℓ-suc ℓ)`{.Agda} なので、一つ上の宇宙の型が小さな代表を得るのです。これはレベルについてのサイズの主張であって、両端が同じ宇宙に属するとの主張ではありません。さらに同値そのものは二つの逆法則に依存するため、ブールのラベルとその命題が同一視されるのは `secB` と `retrB` が認証するパスに関してだけです。
<!--/-->

```agda
lem→hPropSmallness : ∀ {ℓ} → LEM ℓ → HPropSmallness ℓ
lem→hPropSmallness lem = Lift Bool , isoToEquiv (iso decodeB
  (λ P → encodeB P (lem P))
  (λ P → secB P (lem P))
  (λ b → retrB b (lem (decodeB b))))
```

<!--en-->
## Propositional resizing from excluded middle

The second smallness question is per-proposition. Fix `P : hProp (ℓ-suc ℓ)`{.Agda}; resizing produces a proposition `Q : hProp ℓ`{.Agda} together with an equivalence of underlying types `⟨ P ⟩ ≃ ⟨ Q ⟩`{.Agda}. The same two representatives serve again: if `P` is true, take `⊤`{.Agda}; if false, take `⊥`{.Agda}, both at level `ℓ`. Note the shape of the result: it is an equivalence of the underlying types, not a path between the packaged propositions `P` and `Q`.

Mechanically, the difference from the classifier shows in which tool assembles the sameness: `⇔toPath`{.Agda} built paths of `hProp`; here `propBiimpl→Equiv`{.Agda} takes the two propositionality proofs `P .snd`{.Agda} and `Q .snd`{.Agda} together with the two maps and produces the equivalence.
<!--zh-->
## 由排中律得到命题降层

第二个小性问题是逐命题的。固定 `P : hProp (ℓ-suc ℓ)`{.Agda}，命题降层产出命题 `Q : hProp ℓ`{.Agda} 以及底层类型间的等价 `⟨ P ⟩ ≃ ⟨ Q ⟩`{.Agda}。同样的两个代表再次可用：若 `P` 为真取 `⊤`{.Agda}，若为假取 `⊥`{.Agda}，二者都在 `ℓ` 层。注意结果的形状：它是底层类型间的等价，而不是打包命题 `P` 与 `Q` 之间的路径。

在机制上，与分类器的差别体现在用什么工具组装「相同」：`⇔toPath`{.Agda} 构造的是 `hProp` 的路径；这里则由 `propBiimpl→Equiv`{.Agda} 接收两侧的命题性证明 `P .snd`{.Agda} 与 `Q .snd`{.Agda} 连同两个映射，产出等价。
<!--ja-->
## 排中律から得られる命題リサイズ

第二の小ささの問題は命題ごとのものです。`P : hProp (ℓ-suc ℓ)`{.Agda} を固定すると、リサイズは命題 `Q : hProp ℓ`{.Agda} と基礎型の間の同値 `⟨ P ⟩ ≃ ⟨ Q ⟩`{.Agda} を産み出します。同じ二つの代表が再び使えます。`P` が真なら `⊤`{.Agda} を、偽なら `⊥`{.Agda} を取ります。どちらもレベル `ℓ` に住みます。結果の形に注意してください。基礎となる型の間の同値であって、まとめられた命題 `P` と `Q` の間のパスではありません。

仕組みの上では、分類子との違いは「同じである」を組み立てる道具に現れます。`⇔toPath`{.Agda} は `hProp` のパスを作りましたが、ここでは `propBiimpl→Equiv`{.Agda} が両側の命題性の証明 `P .snd`{.Agda} と `Q .snd`{.Agda} と二つの写像を受け取り、同値を産み出します。
<!--/-->

<!--en-->
Given a decision of `P`, `resizeDec` returns the witness of `isSmall P`. In the true case the witness is `(⊤ , equivalence)`: the map from `⟨ P ⟩`{.Agda} to `⊤`{.Agda} sends every input to `tt*`{.Agda}, and the map back uses the decided proof `p`. Since both sides are propositions, `propBiimpl→Equiv`{.Agda}, fed the propositionality proofs `P .snd`{.Agda} and `⊤ .snd`{.Agda}, turns this pair of maps into an equivalence of underlying types.
<!--zh-->
给定 `P` 的一个判定，`resizeDec` 返回 `isSmall P` 的见证。真情形的见证是 `(⊤ , 等价)`：从 `⟨ P ⟩`{.Agda} 到 `⊤`{.Agda} 的映射把所有输入映到 `tt*`{.Agda}，返回的映射使用判定所得的证明 `p`。由于两侧都是命题，`propBiimpl→Equiv`{.Agda} 在收到命题性证明 `P .snd`{.Agda} 与 `⊤ .snd` 后，把这组映射变成底层类型间的等价。
<!--ja-->
`P` の判定が与えられると、`resizeDec` は `isSmall P` の証拠を返します。真の場合の証拠は `(⊤ , 同値)` です。`⟨ P ⟩`{.Agda} から `⊤`{.Agda} への写像はすべての入力を `tt*`{.Agda} に写し、戻りの写像は判定で得た証明 `p` を使います。両側が命題なので、`propBiimpl→Equiv`{.Agda} は命題性の証明 `P .snd`{.Agda} と `⊤ .snd` を与えられ、この写像の組を基礎型の間の同値に変えます。
<!--/-->

```agda
private
  resizeDec : ∀ {ℓ} (P : hProp (ℓ-suc ℓ)) → ⟨ P ⟩ ⊎ (⟨ P ⟩ → Empty.⊥)
            → isSmall P
  resizeDec P (inl p)  = ⊤ , propBiimpl→Equiv (P .snd) (⊤ .snd) (λ _ → tt*) (λ _ → p)
  resizeDec P (inr np) = ⊥ , propBiimpl→Equiv (P .snd) (⊥ .snd)
```

<!--en-->
In the false case the witness is `(⊥ , equivalence)`, with the same absurd maps as in `secB`{.Agda}: the map from `⟨ P ⟩`{.Agda} kills each proof `p` with the refutation `np` via `Empty.rec`{.Agda}, and the reverse map is absurd on the spot because `⊥*`{.Agda} has no constructor. Both representatives `⊤`{.Agda} and `⊥`{.Agda} live at level `ℓ`, one below `P`, which is exactly the smallness being certified: `Q` is chosen inside `hProp ℓ`{.Agda} and the equivalence connects `⟨ P ⟩`{.Agda} with `⟨ Q ⟩`{.Agda}.
<!--zh-->
假情形的见证是 `(⊥ , 等价)`，映射与 `secB`{.Agda} 中的相同：从 `⟨ P ⟩`{.Agda} 出发的映射用反驳 `np` 经 `Empty.rec`{.Agda} 处理每个证明 `p`，反向映射则当场荒谬，因为 `⊥*`{.Agda} 没有构造子。两个代表 `⊤`{.Agda} 与 `⊥`{.Agda} 都住在比 `P` 低一层的 `ℓ` 层，这正是所要认证的小性：`Q` 取自 `hProp ℓ`{.Agda} 内部，等价连接 `⟨ P ⟩`{.Agda} 与 `⟨ Q ⟩`{.Agda}。
<!--ja-->
偽の場合の証拠は `(⊥ , 同値)` で、写像は `secB`{.Agda} と同じものです。`⟨ P ⟩`{.Agda} からの写像は各証明 `p` を反証 `np` と `Empty.rec`{.Agda} で処理し、逆方向の写像は `⊥*`{.Agda} に構成子がないためその場で荒謬です。代表 `⊤`{.Agda} と `⊥`{.Agda} はどちらも `P` より一段下のレベル `ℓ` に住み、これがまさに認証される小ささです。`Q` は `hProp ℓ`{.Agda} の中から選ばれ、同値が `⟨ P ⟩`{.Agda} と `⟨ Q ⟩`{.Agda} を結びます。
<!--/-->

```agda
                               (λ p → Empty.rec (np p)) (λ ())
```

<!--en-->
Assembling resizing needs only to feed `resizeDec` the decisions it asks for. The hypothesis is one instance of excluded middle at level `ℓ-suc ℓ`, matching the statement's quantification over `hProp (ℓ-suc ℓ)`{.Agda}.
<!--zh-->
组装命题降层只需要把 `resizeDec` 所要的判定喂给它。假设是 `ℓ-suc ℓ` 层级上排中律的一个实例，与陈述对 `hProp (ℓ-suc ℓ)`{.Agda} 的量化相匹配。
<!--ja-->
リサイズの組み立てに必要なのは、`resizeDec` が要求する判定を渡すことだけです。仮定はレベル `ℓ-suc ℓ` の排中律の一つの実例であり、`hProp (ℓ-suc ℓ)`{.Agda} に対する主張の量化と一致します。
<!--/-->

<!--en-->
`lem→resizing` turns `LEM (ℓ-suc ℓ)`{.Agda} into `Resizing ℓ`{.Agda} in one line: for each `P : hProp (ℓ-suc ℓ)`{.Agda}, decide it with `lem` and hand the verdict to `resizeDec`. The level flow is worth reading off the signature: resizing at level `ℓ` consumes a classical decision at `ℓ-suc ℓ`, because the propositions being resized are precisely those one universe up.
<!--zh-->
`lem→resizing` 用一行把 `LEM (ℓ-suc ℓ)`{.Agda} 变为 `Resizing ℓ`{.Agda}：对每个 `P : hProp (ℓ-suc ℓ)`{.Agda}，用 `lem` 判定它，把裁决交给 `resizeDec`。层级流向从签名即可读出：`ℓ` 层的命题降层消耗 `ℓ-suc ℓ` 层的经典判定，因为被降层的命题恰好是高一宇宙的那些。
<!--ja-->
`lem→resizing` は `LEM (ℓ-suc ℓ)`{.Agda} を一行で `Resizing ℓ`{.Agda} に変えます。各 `P : hProp (ℓ-suc ℓ)`{.Agda} に対し、`lem` で判定し、その結果を `resizeDec` に渡すだけです。レベルの流れはシグネチャから読み取れます。レベル `ℓ` の命題リサイズが消費するのは `ℓ-suc ℓ` の古典的判定です。リサイズされる命題がちょうど一つ上の宇宙のものだからです。
<!--/-->

```agda
lem→resizing : ∀ {ℓ} → LEM (ℓ-suc ℓ) → Resizing ℓ
lem→resizing lem P = resizeDec P (lem P)
```

<!--en-->
## Combining the two consequences

The two size controls now come from one hypothesis. A single instance of `LEM (ℓ-suc ℓ)`{.Agda} yields resizing directly, and by descending one step with `lowerLEM`{.Agda} it also yields the classifier. The two principles remain distinct statements: this chapter proves both from the same hypothesis and asserts nothing about whether either implies the other.
<!--zh-->
## 合并两项结论

两项尺寸控制现在来自同一条假设。`LEM (ℓ-suc ℓ)`{.Agda} 的一个实例直接给出命题降层，又经 `lowerLEM`{.Agda} 下降一步给出小分类器。两条原理仍是不同的陈述：本章从同一假设证明二者，但对其中一条是否蕴含另一条不作断言。
<!--ja-->
## 二つの帰結をまとめる

二つのサイズの制御が今や一つの仮定から得られます。`LEM (ℓ-suc ℓ)`{.Agda} の一つの実例が命題リサイズを直接与え、さらに `lowerLEM`{.Agda} で一段降りることで小分類子も与えます。二つの原理は異なる主張のままです。本章は同じ仮定から両方を証明しますが、一方が他方を含意するかどうかについては何も主張しません。
<!--/-->

<!--en-->
The record `Impredicativity ℓ`{.Agda} introduced in "Impredicativity" has two fields, one per principle, and `lem→impredicativity` fills both from a single `lem`. The resizing field is `lem→resizing lem`{.Agda}, which uses the given instance at its own level. The classifier field is `lem→hPropSmallness (lowerLEM lem)`{.Agda}, which first descends to `LEM ℓ` and then builds `Lift Bool ≃ hProp ℓ`{.Agda}. The sharing is a fact about this derivation: both consequences were provable from the same higher-level instance, not a claim that the principles imply each other.
<!--zh-->
「非直谓性」一章中的记录 `Impredicativity ℓ`{.Agda} 有两个字段，每条原理各一个，而 `lem→impredicativity` 用同一个 `lem` 填满两者。降层字段是 `lem→resizing lem`{.Agda}，在该实例自身的层级上使用它。分类器字段是 `lem→hPropSmallness (lowerLEM lem)`{.Agda}，先降到 `LEM ℓ`，再构造 `Lift Bool ≃ hProp ℓ`{.Agda}。共享是关于这个推导的事实：两项结论都从同一个高层实例可证，而不是宣称两条原理相互蕴含。
<!--ja-->
「非可述性」の章のレコード `Impredicativity ℓ`{.Agda} は原理ごとに一つずつ、二つのフィールドを持ち、`lem→impredicativity` は単一の `lem` から両方を満たします。リサイズのフィールドは `lem→resizing lem`{.Agda} で、与えられた実例をそのレベルでそのまま使います。分類子のフィールドは `lem→hPropSmallness (lowerLEM lem)`{.Agda} で、まず `LEM ℓ` まで降りてから `Lift Bool ≃ hProp ℓ`{.Agda} を構成します。この共有はこの導出についての事実、つまり二つの帰結が同じ上位実例から証明できたことであり、原理同士が相互に含意するという主張ではありません。
<!--/-->

```agda
lem→impredicativity : ∀ {ℓ} → LEM (ℓ-suc ℓ) → Impredicativity ℓ
lem→impredicativity lem = record
  { resizing       = lem→resizing lem
  ; hPropSmallness = lem→hPropSmallness (lowerLEM lem) }
```

<!--en-->
## Recap

Excluded middle is the ability to decide every proposition at a stated level, and in this development it always travels as an explicit hypothesis. From one higher-level instance, this chapter obtained both size controls that the vocabulary chapter left unpopulated.

The statements are worth keeping apart. `LEM ℓ`{.Agda} returns, for each `P : hProp ℓ`{.Agda}, a proof or a refutation, and its type sits in `Type (ℓ-suc ℓ)`{.Agda}; `lowerLEM`{.Agda} descends it exactly one successor step. Propositional resizing is per-proposition: `lem→resizing`{.Agda} gives each `P : hProp (ℓ-suc ℓ)`{.Agda} a small `Q : hProp ℓ`{.Agda} with an equivalence `⟨ P ⟩ ≃ ⟨ Q ⟩`{.Agda} of underlying types. The classifier concerns the totality: `lem→hPropSmallness`{.Agda} presents all of `hProp ℓ`{.Agda} by `Lift Bool`{.Agda} with `Lift Bool ≃ hProp ℓ`{.Agda}, the equivalence resting on the two inverse laws `secB`{.Agda} and `retrB`{.Agda}. `lem→impredicativity`{.Agda} packages both; the cumulative-hierarchy chapters consume this interface to meet the smallness demands behind full separation and the power set of `V`.
<!--zh-->
## 小结

排中律是在给定层级上判定每个命题的能力；在本发展中，它始终作为显式假设传递。从一个高层实例出发，本章填满了词汇章留下的两项尺寸控制。

这些陈述值得分开记忆。`LEM ℓ`{.Agda} 对每个 `P : hProp ℓ`{.Agda} 返回证明或反驳，其类型位于 `Type (ℓ-suc ℓ)`{.Agda}；`lowerLEM`{.Agda} 恰好把它下降一个后继步。命题降层是逐命题的：`lem→resizing`{.Agda} 给每个 `P : hProp (ℓ-suc ℓ)`{.Agda} 一个小的 `Q : hProp ℓ`{.Agda} 及底层类型间的等价 `⟨ P ⟩ ≃ ⟨ Q ⟩`{.Agda}。分类器针对总体：`lem→hPropSmallness`{.Agda} 用 `Lift Bool`{.Agda} 呈现整个 `hProp ℓ`{.Agda}，并给出 `Lift Bool ≃ hProp ℓ`{.Agda}，该等价依赖两条逆律 `secB`{.Agda} 与 `retrB`{.Agda}。`lem→impredicativity`{.Agda} 把二者打包；累积层级诸章将使用这一接口，以满足全分离与 `V` 的幂集背后的小性需求。
<!--ja-->
## まとめ

排中律とは、明示したレベルのすべての命題を判定する能力であり、この発展の中ではつねに明示的な仮定として渡されます。一つの上位実例から、本章は語彙の章で空のままだった二つのサイズの制御を満たしました。

これらの主張は区別して覚える価値があります。`LEM ℓ`{.Agda} は各 `P : hProp ℓ`{.Agda} に対して証明か反証かを返し、その型は `Type (ℓ-suc ℓ)`{.Agda} にあります。`lowerLEM`{.Agda} はこれを正確に後続一段だけ降ろします。命題リサイズは命題ごとの主張で、`lem→resizing`{.Agda} は各 `P : hProp (ℓ-suc ℓ)`{.Agda} に小さな `Q : hProp ℓ`{.Agda} と基礎型の間の同値 `⟨ P ⟩ ≃ ⟨ Q ⟩`{.Agda} を与えます。分類子は全体に関する主張で、`lem→hPropSmallness`{.Agda} は `hProp ℓ`{.Agda} 全体を `Lift Bool`{.Agda} で提示し、`Lift Bool ≃ hProp ℓ`{.Agda} を与えます。この同値は二つの逆法則 `secB`{.Agda} と `retrB`{.Agda} に支えられています。`lem→impredicativity`{.Agda} が両者をまとめ、累積階層の諸章はこのインターフェースを使って、全分離と `V` の冪集合の背後にある小ささの要求を満たします。
<!--/-->
