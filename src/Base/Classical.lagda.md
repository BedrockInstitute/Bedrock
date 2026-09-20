<!--en-->
# The classical boundary

In a universe-leveled type theory, propositions raise two distinct smallness questions. First, given `P : hProp 𝒰`{.Agda}, can we find a proposition at a chosen level `𝒱` whose underlying type is equivalent to that of `P`? This is propositional resizing, asked one proposition at a time. Second, can the whole type `hProp 𝒰`{.Agda} be presented by a single type in `Type 𝒱`{.Agda}? This is Ω-resizing. The two claims have different shapes, and this chapter proves both from one explicit hypothesis.

The hypothesis is excluded middle: every proposition of a given level is either true or false. Cubical type theory does not assume it, so each classical proof here receives it as an explicit parameter, and each result records exactly which level instance it uses. Constructive definitions and classical steps stay separate throughout: the constructions decide nothing on their own, and the hypothesis enters only where decisions are consumed.
<!--zh-->
# 经典逻辑的边界

在带宇宙层级的类型论中，命题引出两个不同的大小问题。第一，给定 `P : hProp 𝒰`{.Agda}，能否在指定层级 `𝒱` 找到一个命题，使其底层类型与 `P` 的底层类型等价？这就是命题换级，它逐个命题提出问题。第二，能否用 `Type 𝒱`{.Agda} 中的单一类型呈现整个 `hProp 𝒰`{.Agda}？这就是命题宇宙换级。两项断言形状不同，本章由一条显式假设同时证明二者。

这条假设是排中律：给定层级的每个命题要么真要么假。Cubical 类型论并不预设它，因此这里的每个经典证明都把它作为显式参数接收，每项结果也准确记录所用的是哪个层级的实例。构造性定义与经典步骤全程分开：构造自身不作任何判定，假设只在消耗判定之处进入。
<!--ja-->
# 古典論理との境界

宇宙レベルをもつ型理論では、命題について二つの異なる小ささの問題が生じます。第一に、`P : hProp 𝒰`{.Agda} が与えられたとき、指定したレベル `𝒱` に、基礎型が `P` の基礎型と同値な命題を見つけられるか。これが命題リサイズで、命題ごとに問う問題です。第二に、型 `hProp 𝒰`{.Agda} 全体を `Type 𝒱`{.Agda} の一つの型で提示できるか。これが命題宇宙リサイズです。二つの主張は形が異なりますが、本章は一つの明示的な仮定から両方を証明します。

その仮定が排中律です。所定のレベルのすべての命題は、真か偽かのどちらかだという原理です。Cubical 型理論は排中律を仮定しないため、ここでの古典的な証明はそれぞれそれを明示的な引数として受け取り、各結果はどのレベルの実例を使ったかを正確に記録します。構成的な定義と古典的な段階は終始分かれています。構成そのものは何も判定せず、仮定が現れるのは判定を消費する場所だけです。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

module Base.Classical where
```

<!--en-->
For arbitrary levels `𝒰` and `𝒱`, `ΩResizing 𝒰 𝒱` asks for one type in `Type 𝒱`{.Agda} equivalent to the entire type `hProp 𝒰`{.Agda}. This chapter constructs such a classifier from excluded middle at `𝒰`. The general theorem `ΩResizing→Resizing` then gives `Resizing 𝒰 𝒱`, which assigns each source proposition an equivalent representative at the target level.
<!--zh-->
对任意层级 `𝒰` 与 `𝒱`，`ΩResizing 𝒰 𝒱` 要求 `Type 𝒱`{.Agda} 中有一个与整个 `hProp 𝒰`{.Agda} 类型等价的类型。本章从 `𝒰` 层的排中律构造这样的分类器。一般定理 `ΩResizing→Resizing` 再推出 `Resizing 𝒰 𝒱`，为每个源层命题指派目标层中与之类型等价的代表。
<!--ja-->
任意のレベル `𝒰` と `𝒱` に対して、`ΩResizing 𝒰 𝒱` は型 `hProp 𝒰`{.Agda} 全体と同値な一つの型を `Type 𝒱`{.Agda} に要求します。本章は `𝒰` での排中律からそのような分類子を構成します。一般定理 `ΩResizing→Resizing` はそこから `Resizing 𝒰 𝒱` を導き、各始域命題に終域レベルの同値な代表を割り当てます。
<!--/-->

```agda

open import Base.Prelude
open import Base.Impredicativity
  using ( Resizing; ΩResizing; ΩResizing→Resizing )
```

<!--en-->
What it means to decide a proposition must be fixed before anything is proved. To decide `P` is to produce either a proof of `⟨ P ⟩`{.Agda}, or a map from `⟨ P ⟩`{.Agda} into the empty type, which refutes `P` by turning any proof into an absurdity. The coproduct `_⊎_`{.Agda} with its two constructors carries exactly this either-or, and the disjunction is genuine data: an element knows which side it came from, so a decision can be used in a case analysis. The booleans `Bool`{.Agda} with `true`{.Agda} and `false`{.Agda} will label the two outcomes, and `tt*`{.Agda} is the lone inhabitant of the unit type underlying the proposition true.
<!--zh-->
判定一个命题意味着什么，必须先于一切证明固定下来。判定 `P`，就是给出 `⟨ P ⟩`{.Agda} 的一个证明，或给出从 `⟨ P ⟩`{.Agda} 到空类型的映射：后者把任何证明都变成荒谬，从而反驳 `P`。余积 `_⊎_`{.Agda} 及其两个构造子承载的正是这种二选一，而且这个析取是真实的数据：元素知道自己来自哪一支，因此判定能够逐情形使用。布尔值 `Bool`{.Agda} 与 `true`{.Agda}、`false`{.Agda} 将为两种结果贴标签，`tt*`{.Agda} 则是「真」命题底层单元类型的唯一元素。
<!--ja-->
命題を判定するとは何かを、証明に先立って固定しておきます。`P` を判定するとは、`⟨ P ⟩`{.Agda} の証明を与えるか、`⟨ P ⟩`{.Agda} から空型への写像を与えるかのどちらかです。後者は任意の証明を不条理に変えることで `P` を反証します。直和 `_⊎_`{.Agda} とその二つの構成子が担うのはまさにこの二者択一であり、この選言は本物のデータです。元は自分がどちらの直和項から来たかを知っているので、判定は場合分けで使えます。ブール値 `Bool`{.Agda} と `true`{.Agda}、`false`{.Agda} は二つの結果にラベルを付け、`tt*`{.Agda} は「真」の命題の底にある単元型の唯一の元です。
<!--/-->

```agda
open import Cubical.Data.Sum using ( _⊎_; inl; inr )
import Cubical.Data.Empty as Empty
open import Cubical.Data.Bool using ( Bool; true; false )
open import Cubical.Data.Unit using ( tt* )
```

<!--en-->
The proof will compare objects in two different ways. Between propositions, maps in both directions yield a path of `hProp` values by propositional extensionality `⇔toPath`{.Agda}. Between the whole proposition universe and its Boolean code type, an isomorphism `iso`{.Agda} records an encoder, a decoder, and their two inverse laws; `isoToEquiv`{.Agda} then reads this data as the type equivalence required by Ω-resizing. Thus paths certify that each decoded Boolean has the intended truth value, while a type equivalence presents the entire proposition universe by the Boolean codes.
<!--zh-->
下文会以两种方式比较对象。在命题之间，双向映射经命题外延性 `⇔toPath`{.Agda} 给出 `hProp` 值之间的路径。在整个命题宇宙与布尔编码类型之间，同构 `iso`{.Agda} 记录编码、解码和两条逆律，`isoToEquiv`{.Agda} 再把这些数据读作命题宇宙换级所要求的类型等价。因此，路径证明每个解码所得的命题具有预期真值，而类型等价则用布尔编码呈现整个命题宇宙。
<!--ja-->
以下では、対象を二つの異なる仕方で比較します。命題どうしでは、両方向の写像から命題外延性 `⇔toPath`{.Agda} によって `hProp` 値の間のパスを得ます。命題宇宙全体とブール符号の型との間では、同型 `iso`{.Agda} が符号化、復号、二つの逆法則を記録し、`isoToEquiv`{.Agda} がそのデータを命題宇宙リサイズに必要な型同値として読みます。したがってパスは、復号された各ブール値が意図した真理値をもつことを証明し、型同値は命題宇宙全体をブール符号で提示します。
<!--/-->

```agda
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
For each universe level `ℓ`, `LEM ℓ`{.Agda} is a function taking a proposition `P : hProp ℓ`{.Agda} and returning either a proof of `⟨ P ⟩`{.Agda} or a refutation, that is, a map from `⟨ P ⟩`{.Agda} into the empty type. Because it quantifies over all propositions of `hProp ℓ`{.Agda}, its type lives one universe up, in `Type (ℓ-suc ℓ)`{.Agda}. The statement is therefore large, although each decision it delivers is one small piece of data, and `LEM ℓ` is asserted one level at a time rather than for all levels at once. Note the strength this shape provides: a decision is data, not a proposition, so a hypothesis of excluded middle permits case analysis between a proof and a refutation, rather than merely asserting that one of them exists.
<!--zh-->
对每个宇宙层级 `ℓ`，`LEM ℓ`{.Agda} 是一个函数：取命题 `P : hProp ℓ`{.Agda}，返回 `⟨ P ⟩`{.Agda} 的证明，或一个反驳，即从 `⟨ P ⟩`{.Agda} 映入空类型的映射。由于它量化了 `hProp ℓ`{.Agda} 的所有命题，其类型位于高一层宇宙 `Type (ℓ-suc ℓ)`{.Agda}。因此这个陈述本身是大的，尽管它产出的每个判定都只是一小段数据；而且 `LEM ℓ` 是逐层陈述的，不是同时对所有层级断言。注意这种形状给出的强度：判定是数据而非命题，所以从排中律假设出发，可以在证明与反驳两种情形之间作分支推理，而不只是断言二者之一存在。
<!--ja-->
各宇宙レベル `ℓ` に対して `LEM ℓ`{.Agda} は、命題 `P : hProp ℓ`{.Agda} を受け取り、`⟨ P ⟩`{.Agda} の証明か、あるいは `⟨ P ⟩`{.Agda} を空型へ写す反証のどちらかを返す関数です。`hProp ℓ`{.Agda} のすべての命題を量化するため、その型は一つ上の宇宙 `Type (ℓ-suc ℓ)`{.Agda} に住みます。主張そのものは大きくても、生み出される個々の判定は小さなデータのひと塊にすぎず、さらに `LEM ℓ` は全レベル一度にではなく一レベルずつ主張されます。この形がもたらす強さに注意してください。判定は命題ではなくデータなので、排中律の仮定から、証明の場合と反証の場合に分けて推論できます。どちらかが存在すると主張するだけではありません。
<!--/-->

```agda
LEM : ∀ ℓ → Type (ℓ-suc ℓ)
LEM ℓ = (P : hProp ℓ) → ⟨ P ⟩ ⊎ (⟨ P ⟩ → Empty.⊥)
```

<!--en-->
Applications need excluded middle at more than one level, yet a proof is usually handed only the higher instance `LEM (ℓ-suc ℓ)`{.Agda}. The following descent lemma bridges the gap. It is a one-step result, exactly `LEM (ℓ-suc ℓ) → LEM ℓ`{.Agda}: to decide `P : hProp ℓ`{.Agda}, decide a lifted copy of `P` one universe up and bring the verdict back. Iterating the lemma would descend farther, but the statement itself performs exactly one step.
<!--zh-->
应用需要在不止一个层级上的排中律，而证明拿到的往往只有高层实例 `LEM (ℓ-suc ℓ)`{.Agda}。下面的下降引理补上这个缺口。它是恰好一步的结果，即 `LEM (ℓ-suc ℓ) → LEM ℓ`{.Agda}：要判定 `P : hProp ℓ`{.Agda}，在上一层宇宙判定 `P` 的抬升副本，再把裁决带回。反复应用这条引理当然可以继续下降，但陈述本身每次只走一步。
<!--ja-->
応用では排中律が複数のレベルで要りますが、証明に渡されるのはしばしば高い方の実例 `LEM (ℓ-suc ℓ)`{.Agda} だけです。次の下降補題がその差を埋めます。結果は正確に一段分、すなわち `LEM (ℓ-suc ℓ) → LEM ℓ`{.Agda} です。`P : hProp ℓ`{.Agda} を判定するには、一つ上の宇宙で `P` の持ち上げられたコピーを判定し、その結果を持ち帰ります。この補題を反復すればさらに下降できますが、主張そのものが行うのは一度に一段だけです。
<!--/-->

<!--en-->
The lemma `lowerLEM`{.Agda} states that excluded middle at a successor level implies excluded middle at the level below. Given `lem : LEM (ℓ-suc ℓ)`{.Agda} and a proposition `P : hProp ℓ`{.Agda}, apply `lem` not to `P` itself but to a lifted copy of `P` living at level `ℓ-suc ℓ`, where the hypothesis applies. The verdict about the copy is then translated back into a verdict about `P`.
<!--zh-->
引理 `lowerLEM`{.Agda} 说明后继层级上的排中律蕴含低一层的排中律。给定 `lem : LEM (ℓ-suc ℓ)`{.Agda} 与命题 `P : hProp ℓ`{.Agda}，不把 `lem` 用在 `P` 本身上，而是用在住在 `ℓ-suc ℓ` 层、因而假设可适用的 `P` 的抬升副本上，然后再把关于副本的裁决翻译回关于 `P` 的裁决。
<!--ja-->
補題 `lowerLEM`{.Agda} は、後続レベルでの排中律から、その一つ下のレベルでの排中律が従うことを述べます。`lem : LEM (ℓ-suc ℓ)`{.Agda} と命題 `P : hProp ℓ`{.Agda} が与えられたとき、`lem` を `P` 自身ではなく、レベル `ℓ-suc ℓ` に住み仮定が適用できる `P` の持ち上げられたコピーに適用します。そのコピーについての判定を、`P` についての判定へ翻訳し戻します。
<!--/-->

```agda
lowerLEM : ∀ {ℓ} → LEM (ℓ-suc ℓ) → LEM ℓ
lowerLEM {ℓ} lem P = fromLifted (lem lifted)
```

<!--en-->
The lifted proposition has underlying type `Lift ⟨ P ⟩`{.Agda}. Its elements are the elements of `⟨ P ⟩`{.Agda} in the higher universe, and it is a proposition: for elements `x` and `y`, lower both with `lower`, use the propositionhood `⟨ P ⟩isProp`{.Agda} of `P` to get a path between the lowerings, and apply `cong lift` to lift that path back up. So `lifted` is a legitimate input to `lem`.
<!--zh-->
抬升后的命题底层类型为 `Lift ⟨ P ⟩`{.Agda}，其元素就是高一层宇宙中的 `⟨ P ⟩`{.Agda} 元素，而且它是命题：对元素 `x` 与 `y`，先用 `lower` 把二者降到 `⟨ P ⟩`，用 `P` 的命题性 `⟨ P ⟩isProp`{.Agda} 得到降像之间的路径，再用 `cong lift` 把该路径抬回上层。于是 `lifted` 是 `lem` 的合法输入。
<!--ja-->
持ち上げられた命題の基礎型は `Lift ⟨ P ⟩`{.Agda} で、その元は一つ上の宇宙における `⟨ P ⟩`{.Agda} の元です。そしてこれは命題です。元 `x` と `y` に対し、`lower` で両者を `⟨ P ⟩` へ降ろし、`P` の命題性 `⟨ P ⟩isProp`{.Agda} で降ろしたもの同士のパスを得て、`cong lift` でそのパスを上の宇宙へ持ち上げます。こうして `lifted` は `lem` の正当な入力になります。
<!--/-->

```agda
  where
  lifted : hProp (ℓ-suc ℓ)
  lifted = Lift ⟨ P ⟩ , λ x y → cong lift (⟨ P ⟩isProp (lower x) (lower y))
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
## Ω-resizing from excluded middle

Classically, every proposition at a fixed level is either true or false. That suggests a two-point classifier. The candidate code type is `Lift Bool`{.Agda}, with `true`{.Agda} representing the proposition true and `false`{.Agda} representing the proposition false. Two warnings keep the picture honest. A Boolean is a label, while the proposition it represents is a separate `hProp` value; decoding connects the two descriptions by paths in `hProp`, not by syntactic identity. Moreover, the two types being classified may live at different levels: `Lift {ℓ-zero} {𝒱} Bool`{.Agda} belongs to `Type 𝒱`{.Agda}, whereas `hProp 𝒰`{.Agda} belongs to `Type (ℓ-suc 𝒰)`{.Agda}. The ability of an equivalence to relate types at different levels is exactly what makes this a resizing result.

The construction splits cleanly. Decoding sends each Boolean to its representative proposition. Encoding needs to know, for a given `P`, which case holds, so it takes the decision of `P` as an explicit argument; the two inverse laws are then proved for that data. Excluded middle enters only at the end, to supply such decisions uniformly.
<!--zh-->
## 由排中律得到命题宇宙换级

在经典观点下，固定层级的每个命题非真即假。这提示了一个两点的分类器。编码类型取 `Lift Bool`{.Agda}，其中 `true`{.Agda} 代表命题「真」，`false`{.Agda} 代表命题「假」。有两点提醒使图景保持准确。布尔值只是标签，它所代表的命题是另一个 `hProp` 值；解码通过 `hProp` 中的路径联系这两种描述，而不是宣称它们在语法上相同。并且被分类的两个类型可以位于不同层级：`Lift {ℓ-zero} {𝒱} Bool`{.Agda} 住在 `Type 𝒱`{.Agda}，`hProp 𝒰`{.Agda} 则住在 `Type (ℓ-suc 𝒰)`{.Agda}。等价能够联系不同层级的类型，正是这项结果能实现换级的原因。

构造分成干净的两步。解码把每个布尔值送到它代表的命题。编码则需要知道给定的 `P` 属于哪种情形，因此把 `P` 的判定作为显式参数；两条逆律随后针对这份数据证明。排中律只在最后出现，用于一致地供给这些判定。
<!--ja-->
## 排中律から得られる命題宇宙リサイズ

古典的な見方では、固定したレベルの命題は真か偽かのどちらかです。そこで自然に浮かぶのが二点からなる分類子です。符号の型には `Lift Bool`{.Agda} を取り、`true`{.Agda} が真という命題を、`false`{.Agda} が偽という命題を代表します。ここで二つの注意が必要です。ブール値はラベルにすぎず、それが代表する命題は別の `hProp` 値です。復号は両者の記述を `hProp` のパスで結びますが、構文的に同一だと主張するわけではありません。また分類される二つの型は異なるレベルに住んでもかまいません。`Lift {ℓ-zero} {𝒱} Bool`{.Agda} は `Type 𝒱`{.Agda} に、`hProp 𝒰`{.Agda} は `Type (ℓ-suc 𝒰)`{.Agda} に住みます。同値が異なるレベルの型を結べることこそ、この結果がリサイズを実現できる理由です。

構成はきれいに二段に分かれます。復号は各ブール値をその代表である命題へ送ります。符号化には、与えられた `P` がどちらの場合かを知る必要があるので、`P` の判定を明示的な引数として受け取ります。二つの逆法則はそのデータに対して証明されます。排中律が現れるのは最後だけで、判定を一様に供給するためです。
<!--/-->

<!--en-->
The construction `lem→ΩResizing`{.Agda} shows that excluded middle at the source level presents its proposition universe by Boolean codes at any target level. Its two representative propositions are the canonical top proposition `⊤`{.Agda} and bottom proposition `⊥`{.Agda} of the Prelude's logical operations. The latter is definitionally the pair `(⊥* , isProp⊥*)`{.Agda}, so its underlying type is the empty type `⊥*`{.Agda}. Both are available at every level `𝒰`, which is exactly what lets them serve as representatives inside `hProp 𝒰`{.Agda}; the Boolean labels below will denote precisely these two.
<!--zh-->
构造 `lem→ΩResizing`{.Agda} 表明，源层级上的排中律能在任意目标层级以布尔编码呈现该命题宇宙。它使用的两个代表命题，是《基础词汇》逻辑运算中典范的顶命题 `⊤`{.Agda} 与底命题 `⊥`{.Agda}。后者按定义就是序对 `(⊥* , isProp⊥*)`{.Agda}，因此其底层类型是空类型 `⊥*`{.Agda}。二者在任意层级 `𝒰` 都可用，这正是它们能在 `hProp 𝒰`{.Agda} 内部充任代表的原因；下面的布尔标签指称的恰是这两个命题。
<!--ja-->
構成 `lem→ΩResizing`{.Agda} は、始域レベルでの排中律が、任意の終域レベルにおいて、その命題宇宙をブール符号で提示することを示します。用いる二つの代表命題は、「基礎語彙」の論理演算における正準な頂命題 `⊤`{.Agda} と底命題 `⊥`{.Agda} です。後者は定義上、対 `(⊥* , isProp⊥*)`{.Agda} そのものであり、その基礎型は空型 `⊥*`{.Agda} です。両者は任意のレベル `𝒰` で使えるので、`hProp 𝒰`{.Agda} の中で代表を務められます。後のブールのラベルが指すのはまさにこの二つの命題です。
<!--/-->

```agda

private
  decodeB : ∀ {𝒰 𝒱} → Lift {ℓ-zero} {𝒱} Bool → hProp 𝒰
```

<!--en-->
Decoding reads a Boolean label and returns the proposition it represents: `lift true`{.Agda} yields `⊤`{.Agda} and `lift false`{.Agda} yields `⊥`{.Agda}. Its domain is `Lift {ℓ-zero} {𝒱} Bool`{.Agda} rather than `Bool`{.Agda} itself: `Bool`{.Agda} lives in `Type ℓ-zero`, while the lift lives in the chosen target universe `Type 𝒱`{.Agda}. Decoding alone merely assigns representatives; the two inverse laws below show that no proposition or Boolean code is lost.
<!--zh-->
解码读取布尔标签，返回它所代表的命题：`lift true`{.Agda} 给出 `⊤`{.Agda}，`lift false`{.Agda} 给出 `⊥`{.Agda}。定义域是 `Lift {ℓ-zero} {𝒱} Bool`{.Agda} 而非 `Bool`{.Agda} 本身：`Bool`{.Agda} 住在 `Type ℓ-zero`，其提升则住在指定的目标宇宙 `Type 𝒱`{.Agda}。单独的解码只负责指派代表；下面两条逆律将证明命题与布尔编码都不会在往返中丢失。
<!--ja-->
復号はブールのラベルを読み、それが代表する命題を返します。`lift true`{.Agda} は `⊤`{.Agda} を、`lift false`{.Agda} は `⊥`{.Agda} を返します。定義域は `Bool`{.Agda} 自身ではなく `Lift {ℓ-zero} {𝒱} Bool`{.Agda} です。`Bool`{.Agda} は `Type ℓ-zero` に住み、その持ち上げは指定した終域宇宙 `Type 𝒱`{.Agda} に住みます。復号だけなら代表を割り当てる関数にすぎません。後に続く二つの逆法則が、命題もブール符号も往復で失われないことを示します。
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
The match is on the decision, not on `P`: an inhabitant of the left summand yields `lift true`{.Agda}, one of the right yields `lift false`{.Agda}. The proof or refutation itself is discarded, because the label records only which case held, not a witness. The result type is `Lift {ℓ-zero} {𝒱} Bool`{.Agda}, matching `decodeB`{.Agda}'s domain exactly.
<!--zh-->
匹配对象是判定而非 `P`：左支的元素给出 `lift true`{.Agda}，右支的元素给出 `lift false`{.Agda}。证明或反驳本身被丢弃，因为标签只记录出现的是哪种情形，而不是见证。结果类型是 `Lift {ℓ-zero} {𝒱} Bool`{.Agda}，与 `decodeB`{.Agda} 的定义域严格相配。
<!--ja-->
マッチの対象は `P` ではなく判定です。左の直和項の元なら `lift true`{.Agda} を、右の元なら `lift false`{.Agda} を返します。証明や反証そのものは捨てられます。ラベルが記録するのはどちらの場合だったかだけで、証拠ではないからです。結果の型は `Lift {ℓ-zero} {𝒱} Bool`{.Agda} で、`decodeB`{.Agda} の定義域と正確に一致します。
<!--/-->

```agda
  encodeB : ∀ {𝒰 𝒱} (P : hProp 𝒰) → ⟨ P ⟩ ⊎ (⟨ P ⟩ → Empty.⊥) → Lift {ℓ-zero} {𝒱} Bool
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
  secB : ∀ {𝒰 𝒱} (P : hProp 𝒰) (d : ⟨ P ⟩ ⊎ (⟨ P ⟩ → Empty.⊥))
       → decodeB {𝒰} {𝒱} (encodeB {𝒰} {𝒱} P d) ≡ P
  secB {𝒰} {𝒱} P (inl p)  = ⇔toPath (λ _ → p) (λ _ → tt*)
  secB {𝒰} {𝒱} P (inr np) = ⇔toPath (λ ()) (λ p → Empty.rec (np p))
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
  retrB : ∀ {𝒰 𝒱} (b : Lift {ℓ-zero} {𝒱} Bool)
          (d : ⟨ decodeB {𝒰} {𝒱} b ⟩ ⊎ (⟨ decodeB {𝒰} {𝒱} b ⟩ → Empty.⊥))
        → encodeB {𝒰} {𝒱} (decodeB {𝒰} {𝒱} b) d ≡ b
  retrB {𝒰} {𝒱} (lift true)  (inl _)  = refl
  retrB {𝒰} {𝒱} (lift true)  (inr n⊤) = Empty.rec (n⊤ tt*)
```

<!--en-->
For `b = lift false`{.Agda}, decoding gives `⊥`{.Agda} with underlying type `⊥*`{.Agda}. An alleged proof of it would be a term of the empty type, so the absurd pattern `()` ends that branch at once; encoding with a refutation returns `lift false`{.Agda}, again by `refl`{.Agda}. Across all four cases, the label returned always equals the label we started from, whichever decision is supplied.
<!--zh-->
当 `b = lift false`{.Agda} 时，解码得 `⊥`{.Agda}，其底层类型为 `⊥*`{.Agda}。它的所谓证明将是空类型的项，荒谬模式 `()` 立即结束该分支；配以反驳编码返回 `lift false`{.Agda}，同样由 `refl`{.Agda} 完成。纵观四种情形，无论供给哪种判定，返回的标签总等于出发时的标签。
<!--ja-->
`b = lift false`{.Agda} のとき、復号は `⊥`{.Agda}、すなわち基礎型 `⊥*`{.Agda} を持つ命題を返します。そのいわゆる証明は空型の項になるはずなので、荒謬パターン `()` がこの分岐を直ちに終わらせ、反証とともに符号化すれば `lift false`{.Agda} が返り、これも `refl`{.Agda} で済みます。四つの場合を通して、どの判定が供給されようとも、返されるラベルは出発点のラベルと等しくなります。
<!--/-->

```agda
  retrB {𝒰} {𝒱} (lift false) (inl ())
  retrB {𝒰} {𝒱} (lift false) (inr _)  = refl
```

<!--en-->
Now the pieces assemble into the classifier promised by `ΩResizing 𝒰 𝒱`{.Agda}: the code type `Lift {ℓ-zero} {𝒱} Bool`{.Agda} in `Type 𝒱`{.Agda}, type equivalent to `hProp 𝒰`{.Agda}. The equivalence comes from an isomorphism whose forward map decides each `P` and encodes it, and whose backward map is `decodeB`{.Agda}. Its two inverse laws are `retrB`{.Agda} and `secB`{.Agda}, instantiated with decisions from `lem`. This final assembly is the only place in the construction where excluded middle is invoked: it uniformly supplies the decisions accepted by the otherwise constructive encoder and inverse laws.
<!--zh-->
现在各部分组装成 `ΩResizing 𝒰 𝒱`{.Agda} 所承诺的分类器：编码类型 `Lift {ℓ-zero} {𝒱} Bool`{.Agda} 住在 `Type 𝒱`{.Agda}，并与 `hProp 𝒰`{.Agda} 类型等价。这个等价来自一个同构：正向映射判定每个 `P` 后编码，逆向映射是 `decodeB`{.Agda}；两条逆律则是用 `lem` 所给判定实例化的 `retrB`{.Agda} 与 `secB`{.Agda}。整个构造只在最后组装时调用排中律，它一致地供给编码器和逆律所接收的判定，而这些部件本身仍是构造性的。
<!--ja-->
いま部品が `ΩResizing 𝒰 𝒱`{.Agda} の約束する分類子へと組み上がります。符号の型 `Lift {ℓ-zero} {𝒱} Bool`{.Agda} は `Type 𝒱`{.Agda} に住み、`hProp 𝒰`{.Agda} と型同値です。この同値は、順写像が各 `P` を判定して符号化し、逆写像が `decodeB`{.Agda} である同型から得られます。二つの逆法則は、`lem` が与える判定で具体化した `retrB`{.Agda} と `secB`{.Agda} です。構成全体で排中律を呼び出すのは、この最後の組み立てだけです。符号化器と逆法則はそれ自体構成的なままで、それらが受け取る判定を排中律が一様に供給します。
<!--/-->

<!--en-->
The pair `(Lift Bool , ...)` witnesses `ΩResizing 𝒰 𝒱`{.Agda}: its first component has type `Type 𝒱`{.Agda}, and its second is an equivalence `hProp 𝒰 ≃ Lift Bool`{.Agda}. No ordering between `𝒰` and `𝒱` is assumed. In the downward instance used later, `𝒰 = ℓ-suc ℓ` and `𝒱 = ℓ`, so the proposition universe is presented one level down; the theorem itself is more general and also permits equal or higher target levels. The two inverse laws certify both directions of the equivalence, not merely a surjective labelling of propositions by truth values.
<!--zh-->
序对 `(Lift Bool , ...)` 是 `ΩResizing 𝒰 𝒱`{.Agda} 的见证：第一分量类型为 `Type 𝒱`{.Agda}，第二分量是类型等价 `hProp 𝒰 ≃ Lift Bool`{.Agda}。这里不假设 `𝒰` 与 `𝒱` 有任何大小关系。在后文使用的向下实例中，`𝒰 = ℓ-suc ℓ` 且 `𝒱 = ℓ`，命题宇宙因此被呈现在低一层；但定理本身更一般，也允许目标层级相同或更高。两条逆律认证了等价的两个方向，所以所得结果不只是用真值标签满射地覆盖命题。
<!--ja-->
対 `(Lift Bool , ...)` が `ΩResizing 𝒰 𝒱`{.Agda} の証拠です。第一成分は `Type 𝒱`{.Agda} の型で、第二成分は型同値 `hProp 𝒰 ≃ Lift Bool`{.Agda} です。ここでは `𝒰` と `𝒱` の大小関係を仮定しません。後で使う下向きの実例では `𝒰 = ℓ-suc ℓ`、`𝒱 = ℓ` なので、命題宇宙は一つ下のレベルで提示されます。しかし定理そのものはより一般的で、終域レベルが同じ場合や高い場合も許します。二つの逆法則は同値の両方向を保証しており、単に真理値のラベルで命題を全射的に覆うだけではありません。
<!--/-->

```agda
lem→ΩResizing : ∀ {𝒰 𝒱} → LEM 𝒰 → ΩResizing 𝒰 𝒱
lem→ΩResizing lem = Lift Bool , isoToEquiv (iso
  (λ P → encodeB P (lem P)) decodeB
  (λ b → retrB {𝒰 = _} b (lem (decodeB b)))
  (λ P → secB {𝒱 = _} P (lem P)))
```

<!--en-->
## Propositional resizing as a consequence

The theorem `lem→resizing`{.Agda} states that excluded middle at the source level implies propositional resizing to any target level. The construction above gives the stronger statement `ΩResizing 𝒰 𝒱`{.Agda}: excluded middle presents the whole proposition universe by the two Boolean codes in `Type 𝒱`{.Agda}. Applying the general theorem `ΩResizing→Resizing`{.Agda} then chooses a target-level representative for each source proposition. No second classical construction is needed, and the source and target levels need not be adjacent.
<!--zh-->
## 作为推论的命题换级

定理 `lem→resizing`{.Agda} 说明源层级上的排中律蕴含到任意目标层级的命题换级。上面的构造给出更强的陈述 `ΩResizing 𝒰 𝒱`{.Agda}：排中律以 `Type 𝒱`{.Agda} 中的两个布尔编码呈现整个命题宇宙。再应用一般定理 `ΩResizing→Resizing`{.Agda}，便为每个源层命题选出目标层级的代表。不需要第二套经典构造，源层级与目标层级也不必相邻。
<!--ja-->
## 帰結としての命題リサイズ

定理 `lem→resizing`{.Agda} は、始域レベルでの排中律から任意の終域レベルへの命題リサイズが従うことを述べます。上の構成は、より強い主張 `ΩResizing 𝒰 𝒱`{.Agda} を与えます。排中律によって命題宇宙全体を `Type 𝒱`{.Agda} の二つのブール符号で提示し、一般定理 `ΩResizing→Resizing`{.Agda} を適用して、各始域命題に終域レベルの代表を選びます。別の古典的構成は要らず、始域と終域のレベルが隣接している必要もありません。
<!--/-->

```agda
lem→resizing : ∀ {𝒰 𝒱} → LEM 𝒰 → Resizing 𝒰 𝒱
lem→resizing lem = ΩResizing→Resizing (lem→ΩResizing lem)
```

<!--en-->
## Recap

Excluded middle at an arbitrary source level `𝒰` constructs a Boolean classifier in every target universe `𝒱`, giving `ΩResizing 𝒰 𝒱`{.Agda}. Propositional resizing is then a theorem about that classifier rather than a separate classical axiom. The cumulative-hierarchy chapters use the downward instance `ΩResizing (ℓ-suc ℓ) ℓ`{.Agda}: power set uses its classifier, and full separation uses the resizing derived from it.
<!--zh-->
## 小结

任意源层级 `𝒰` 上的排中律，都能在任意目标宇宙 `𝒱` 中构造布尔分类器，从而给出 `ΩResizing 𝒰 𝒱`{.Agda}。命题换级是关于该分类器的一条定理，而非另一条经典公理。累积层级诸章使用向下实例 `ΩResizing (ℓ-suc ℓ) ℓ`{.Agda}：幂集使用其中的分类器，全分离使用由它导出的命题换级。
<!--ja-->
## まとめ

任意の始域レベル `𝒰` での排中律は、任意の終域宇宙 `𝒱` にブール分類子を構成し、`ΩResizing 𝒰 𝒱`{.Agda} を与えます。命題リサイズは別の古典的公理ではなく、この分類子についての定理です。累積階層の諸章は下向きの実例 `ΩResizing (ℓ-suc ℓ) ℓ`{.Agda} を使い、冪集合は分類子を、完全な分出はそこから導かれる命題リサイズを使います。
<!--/-->
