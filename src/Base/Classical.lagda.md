<!--en-->
# The classical boundary

This book develops classical set theory inside constructive Cubical type theory. Keeping the ambient foundation constructive makes the boundary of classical reasoning visible: definitions and proofs that do not need excluded middle remain constructive, while a theorem that does need it receives it as an explicit parameter. If classical logic were built into the ambient theory from the outset, the statements themselves would no longer reveal that distinction.
<!--zh-->
# 经典逻辑的边界

本书以构造主义的 Cubical 类型论为基础，在其中发展经典集合论。保留构造主义的基础，可以清楚划出经典推理的边界：不需要排中律的定义和证明仍然是构造主义的；真正需要排中律的定理，则把它作为显式参数。如果一开始就在基础理论中预设经典逻辑，定理的陈述本身就无法再显示这种区别。
<!--ja-->
# 古典論理との境界

本書は、構成的な Cubical 型理論を基礎として、その中で古典集合論を展開します。基礎を構成的なまま保つことで、古典的推論との境界が明確になります。排中律を必要としない定義と証明は構成的なまま残り、排中律を本当に必要とする定理だけが、それを明示的な引数として受け取ります。初めから基礎理論に古典論理を組み込めば、定理の主張そのものからこの違いを読み取れなくなります。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

module Base.Classical where
```

<!--en-->
Excluded middle also has an important consequence for the two smallness questions left open in the preceding chapter:

- Propositional resizing: given `P : hProp ℓ₁`{.Agda}, can we find a proposition at a chosen level `ℓ₂` whose underlying type is equivalent to that of `P`?
- Ω-resizing: can the whole type `hProp ℓ₁`{.Agda} be presented by a single type in `Type ℓ₂`{.Agda}?
<!--zh-->
除此之外，排中律还顺便解决了上一章留下的两个命题大小问题：

- 命题换级：给定 `P : hProp ℓ₁`{.Agda}，能否在指定层级 `ℓ₂` 找到一个命题，使其底层类型与 `P` 的底层类型等价？
- 命题宇宙换级：能否用 `Type ℓ₂`{.Agda} 中的单一类型呈现整个 `hProp ℓ₁`{.Agda}？
<!--ja-->
さらに排中律は、前章で残された二つの命題の小ささの問題も同時に解決します。

- 命題リサイズ：`P : hProp ℓ₁`{.Agda} が与えられたとき、指定したレベル `ℓ₂` に、基礎型が `P` の基礎型と同値な命題を見つけられるか。
- 命題宇宙リサイズ：型 `hProp ℓ₁`{.Agda} 全体を `Type ℓ₂`{.Agda} の一つの型で提示できるか。
<!--/-->

```agda

open import Base.Prelude
open import Base.Impredicativity
  using ( Resizing; ΩResizing; ΩResizing→Resizing )
```

<!--en-->
The two claims have different shapes. Excluded middle says that every proposition at a given level is either true or false; that decision lets the proof encode each proposition by one of two Boolean labels. Because propositions inhabit different universes, excluded middle is stated separately at each level: its level-`ℓ` instance decides only propositions in `hProp ℓ`{.Agda}. This chapter first gives that leveled statement, then uses it to solve both smallness problems. Each theorem therefore records the instance it needs.

For arbitrary levels `ℓ₁`{.Agda} and `ℓ₂`{.Agda}, `ΩResizing ℓ₁ ℓ₂`{.Agda} asks for one type in `Type ℓ₂`{.Agda} equivalent to the entire type `hProp ℓ₁`{.Agda}. This chapter constructs such a classifier from excluded middle at `ℓ₁`{.Agda}. Once this small presentation of the whole proposition universe is available, the general theorem `ΩResizing→Resizing`{.Agda} turns it into resizing for individual propositions. We thus obtain `Resizing ℓ₁ ℓ₂`{.Agda}: every source-level proposition has an equivalent representative at the target level.
<!--zh-->
两项断言形状不同。排中律断言给定层级的每个命题要么真要么假；这项判定使证明能够把每个命题编码成两个布尔标签之一。命题分居不同宇宙，因此排中律也按层级分别陈述：`ℓ` 层的排中律只判定 `hProp ℓ`{.Agda} 中的命题。本章先给出这一分层陈述，再用它解决上述两个大小问题；每项定理也相应注明自己需要哪一层的排中律。

对任意层级 `ℓ₁`{.Agda} 与 `ℓ₂`{.Agda}，`ΩResizing ℓ₁ ℓ₂`{.Agda} 要求 `Type ℓ₂`{.Agda} 中有一个与整个 `hProp ℓ₁`{.Agda} 类型等价的类型。本章从 `ℓ₁`{.Agda} 层的排中律构造这样的分类器。有了这个对整个命题宇宙的小表示，便可应用一般定理 `ΩResizing→Resizing`{.Agda}，将命题宇宙换级转化为逐个命题的换级。由此得到 `Resizing ℓ₁ ℓ₂`{.Agda}：源层的每个命题在目标层都有一个与之类型等价的代表。
<!--ja-->
二つの主張は異なる形をしています。排中律は、所定のレベルの各命題が真か偽かのどちらかだと述べ、その判定によって各命題を二つのブールラベルの一方で符号化できます。命題は異なる宇宙に属するため、排中律もレベルごとに述べます。レベル `ℓ` での排中律が判定するのは `hProp ℓ`{.Agda} の命題だけです。本章はまずこのレベル付きの主張を与え、次にそれを使って二つの小ささの問題を解決します。したがって各定理は、必要とする排中律のレベルも明記します。

任意のレベル `ℓ₁`{.Agda} と `ℓ₂`{.Agda} に対して、`ΩResizing ℓ₁ ℓ₂`{.Agda} は型 `hProp ℓ₁`{.Agda} 全体と同値な一つの型を `Type ℓ₂`{.Agda} に要求します。本章は `ℓ₁`{.Agda} での排中律からそのような分類子を構成します。命題宇宙全体のこの小さな表示が得られれば、一般定理 `ΩResizing→Resizing`{.Agda} によって、命題宇宙のリサイズを個々の命題のリサイズへ移せます。こうして `Resizing ℓ₁ ℓ₂`{.Agda}、すなわち始域レベルの各命題が終域レベルに同値な代表をもつことが従います。
<!--/-->

<!--en-->
The proof will compare objects in two different ways. Between propositions, maps in both directions yield a path of `hProp` values by propositional extensionality `⇔toPath`{.Agda}. Between the whole proposition universe and its Boolean code type, an isomorphism `iso`{.Agda} records an encoder, a decoder, and their two inverse laws; `isoToEquiv`{.Agda} then reads this data as the type equivalence required by Ω-resizing. Thus paths certify that each decoded Boolean has the intended truth value, while a type equivalence presents the entire proposition universe by the Boolean codes.
<!--zh-->
下文会以两种方式比较对象。在命题之间，双向映射经命题外延性 `⇔toPath`{.Agda} 给出 `hProp` 值之间的路径。在整个命题宇宙与布尔编码类型之间，同构 `iso`{.Agda} 记录编码、解码和两条逆律，`isoToEquiv`{.Agda} 再把这些数据读作命题宇宙换级所要求的类型等价。因此，路径证明每个解码所得的命题具有预期真值，而类型等价则用布尔编码呈现整个命题宇宙。
<!--ja-->
以下では、対象を二つの異なる仕方で比較します。命題どうしでは、両方向の写像から命題外延性 `⇔toPath`{.Agda} によって `hProp` 値の間のパスを得ます。命題宇宙全体とブール符号の型との間では、同型 `iso`{.Agda} が符号化、復号、二つの逆法則を記録し、`isoToEquiv`{.Agda} がそのデータを命題宇宙リサイズに必要な型同値として読みます。したがってパスは、復号された各ブール値が意図した真理値をもつことを証明し、型同値は命題宇宙全体をブール符号で提示します。
<!--/-->

```agda
open import Cubical.Foundations.Isomorphism using ( iso; isoToEquiv )
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

<!--en-->
This description becomes a type by using the coproduct `_⊎_`{.Agda}. Its constructor `inl` carries a proof of `P`, while `inr` carries a refutation, a function sending every proof of `P` to the empty type. Because an element records which constructor formed it, a decision can be used directly by case analysis.
<!--zh-->
这段描述用余积 `_⊎_`{.Agda} 写成类型。构造子 `inl` 携带 `P` 的证明；`inr` 携带 `P` 的反驳，也就是把 `P` 的每个证明送入空类型的函数。余积的元素会记录自己由哪个构造子生成，因此判定可以直接用于分情形推理。
<!--ja-->
この記述は直和 `_⊎_`{.Agda} によって型になります。構成子 `inl` は `P` の証明を運び、`inr` は `P` の反証、すなわち `P` のどの証明も空型へ送る関数を運びます。直和の元はどちらの構成子から作られたかを記録しているので、判定をそのまま場合分けに使えます。
<!--/-->

```agda

LEM : ∀ ℓ → Type (ℓ-suc ℓ)
LEM ℓ = (P : hProp ℓ) → ⟨ P ⟩ ⊎ (⟨ P ⟩ → ⊥₀)
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
The two parts of the verdict travel in opposite directions. A proof of `Lift ⟨ P ⟩`{.Agda} lowers with `lower` to a proof of `⟨ P ⟩`{.Agda}. For a refutation, a proof of `⟨ P ⟩`{.Agda} is lifted and passed to the given refutation, producing the same contradiction. Both branches merely transport the decision and add no classical reasoning; the classical step was deciding the lifted proposition.
<!--zh-->
裁决的两个部分沿相反方向搬运。`Lift ⟨ P ⟩`{.Agda} 的证明经 `lower` 降为 `⟨ P ⟩`{.Agda} 的证明。对于反驳，先把 `⟨ P ⟩`{.Agda} 的证明抬升，再交给已有的反驳，便得到同一个矛盾。两个分支都只是搬运判定，自身不含经典推理；经典的步骤是判定那个抬升后的命题。
<!--ja-->
判定の二つの部分は反対方向へ運ばれます。`Lift ⟨ P ⟩`{.Agda} の証明は `lower` で `⟨ P ⟩`{.Agda} の証明へ降ろします。反証の場合は、`⟨ P ⟩`{.Agda} の証明を持ち上げて既存の反証に渡すと、同じ矛盾が得られます。どちらの場合も判定を運ぶだけであり、古典的推論は加わりません。古典的な一歩は、持ち上げられた命題を判定したところで起こっています。
<!--/-->

```agda
  fromLifted : ⟨ lifted ⟩ ⊎ (⟨ lifted ⟩ → ⊥₀)
             → ⟨ P ⟩ ⊎ (⟨ P ⟩ → ⊥₀)
  fromLifted (inl p)  = inl (lower p)
  fromLifted (inr np) = inr (λ p → np (lift p))
```

<!--en-->
## Ω-resizing from excluded middle

Classically, every proposition at a fixed level is either true or false. That suggests a two-point classifier. The candidate code type is `Lift Bool`{.Agda}, with `true`{.Agda} representing the proposition true and `false`{.Agda} representing the proposition false. Two warnings keep the picture honest. A Boolean is a label, while the proposition it represents is a separate `hProp` value; decoding connects the two descriptions by paths in `hProp`, not by syntactic identity. Moreover, the two types being classified may live at different levels: `Lift {ℓ-zero} {ℓ₂} Bool`{.Agda} belongs to `Type ℓ₂`{.Agda}, whereas `hProp ℓ₁`{.Agda} belongs to `Type (ℓ-suc ℓ₁)`{.Agda}. The ability of an equivalence to relate types at different levels is exactly what makes this a resizing result.

The construction splits cleanly. Decoding sends each Boolean to its representative proposition. Encoding needs to know, for a given `P`, which case holds, so it takes the decision of `P` as an explicit argument; the two inverse laws are then proved for that data. Excluded middle enters only at the end, to supply such decisions uniformly.
<!--zh-->
## 由排中律得到命题宇宙换级

在经典观点下，固定层级的每个命题非真即假。这提示了一个两点的分类器。编码类型取 `Lift Bool`{.Agda}，其中 `true`{.Agda} 代表命题「真」，`false`{.Agda} 代表命题「假」。有两点提醒使图景保持准确。布尔值只是标签，它所代表的命题是另一个 `hProp` 值；解码通过 `hProp` 中的路径联系这两种描述，而不是宣称它们在语法上相同。并且被分类的两个类型可以位于不同层级：`Lift {ℓ-zero} {ℓ₂} Bool`{.Agda} 住在 `Type ℓ₂`{.Agda}，`hProp ℓ₁`{.Agda} 则住在 `Type (ℓ-suc ℓ₁)`{.Agda}。等价能够联系不同层级的类型，正是这项结果能实现换级的原因。

构造分成干净的两步。解码把每个布尔值送到它代表的命题。编码则需要知道给定的 `P` 属于哪种情形，因此把 `P` 的判定作为显式参数；两条逆律随后针对这份数据证明。排中律只在最后出现，用于一致地供给这些判定。
<!--ja-->
## 排中律から得られる命題宇宙リサイズ

古典的な見方では、固定したレベルの命題は真か偽かのどちらかです。そこで自然に浮かぶのが二点からなる分類子です。符号の型には `Lift Bool`{.Agda} を取り、`true`{.Agda} が真という命題を、`false`{.Agda} が偽という命題を代表します。ここで二つの注意が必要です。ブール値はラベルにすぎず、それが代表する命題は別の `hProp` 値です。復号は両者の記述を `hProp` のパスで結びますが、構文的に同一だと主張するわけではありません。また分類される二つの型は異なるレベルに住んでもかまいません。`Lift {ℓ-zero} {ℓ₂} Bool`{.Agda} は `Type ℓ₂`{.Agda} に、`hProp ℓ₁`{.Agda} は `Type (ℓ-suc ℓ₁)`{.Agda} に住みます。同値が異なるレベルの型を結べることこそ、この結果がリサイズを実現できる理由です。

構成はきれいに二段に分かれます。復号は各ブール値をその代表である命題へ送ります。符号化には、与えられた `P` がどちらの場合かを知る必要があるので、`P` の判定を明示的な引数として受け取ります。二つの逆法則はそのデータに対して証明されます。排中律が現れるのは最後だけで、判定を一様に供給するためです。
<!--/-->

<!--en-->
The construction `lem→ΩResizing`{.Agda} shows that excluded middle at the source level presents its proposition universe by Boolean codes at any target level. Its two representative propositions are the canonical top proposition `⊤`{.Agda} and bottom proposition `⊥`{.Agda} of the Prelude's logical operations. The latter is definitionally the pair `(⊥* , isProp⊥*)`{.Agda}, so its underlying type is the empty type `⊥*`{.Agda}. Both are available at every level `ℓ₁`, which is exactly what lets them serve as representatives inside `hProp ℓ₁`{.Agda}; the Boolean labels below will denote precisely these two.
<!--zh-->
构造 `lem→ΩResizing`{.Agda} 表明，源层级上的排中律能在任意目标层级以布尔编码呈现该命题宇宙。它使用的两个代表命题，是《基础词汇》逻辑运算中典范的顶命题 `⊤`{.Agda} 与底命题 `⊥`{.Agda}。后者按定义就是序对 `(⊥* , isProp⊥*)`{.Agda}，因此其底层类型是空类型 `⊥*`{.Agda}。二者在任意层级 `ℓ₁` 都可用，这正是它们能在 `hProp ℓ₁`{.Agda} 内部充任代表的原因；下面的布尔标签指称的恰是这两个命题。
<!--ja-->
構成 `lem→ΩResizing`{.Agda} は、始域レベルでの排中律が、任意の終域レベルにおいて、その命題宇宙をブール符号で提示することを示します。用いる二つの代表命題は、「基礎語彙」の論理演算における正準な頂命題 `⊤`{.Agda} と底命題 `⊥`{.Agda} です。後者は定義上、対 `(⊥* , isProp⊥*)`{.Agda} そのものであり、その基礎型は空型 `⊥*`{.Agda} です。両者は任意のレベル `ℓ₁` で使えるので、`hProp ℓ₁`{.Agda} の中で代表を務められます。後のブールのラベルが指すのはまさにこの二つの命題です。
<!--/-->

<!--en-->
The promised two labels now enter the construction. `Bool`{.Agda} has exactly the constructors `true`{.Agda} and `false`{.Agda}; after lifting it to the target universe, these labels record whether a proposition was proved or refuted. They carry only the outcome, while `decodeB`{.Agda} below assigns each label its representative proposition.
<!--zh-->
现在引入构造所需的两个标签。`Bool`{.Agda} 恰有 `true`{.Agda} 与 `false`{.Agda} 两个构造子；把它提升到目标宇宙后，这两个标签分别记录命题得到证明还是遭到反驳。标签只记录判定结果，下面的 `decodeB`{.Agda} 再把每个标签指派给相应的代表命题。
<!--ja-->
ここで構成に必要な二つのラベルを導入します。`Bool`{.Agda} の構成子は `true`{.Agda} と `false`{.Agda} のちょうど二つです。これを終域の宇宙へ持ち上げると、命題が証明されたか反証されたかを記録するラベルになります。ラベルが記録するのは判定結果だけであり、以下の `decodeB`{.Agda} が各ラベルに対応する代表命題を割り当てます。
<!--/-->

```agda

open import Cubical.Data.Bool using ( Bool; true; false )

private
  decodeB : ∀ {ℓ₁ ℓ₂} → Lift {ℓ-zero} {ℓ₂} Bool → hProp ℓ₁
```

<!--en-->
Decoding reads a Boolean label and returns the proposition it represents: `lift true`{.Agda} yields `⊤`{.Agda} and `lift false`{.Agda} yields `⊥`{.Agda}. Its domain is `Lift {ℓ-zero} {ℓ₂} Bool`{.Agda} rather than `Bool`{.Agda} itself: `Bool`{.Agda} lives in `Type ℓ-zero`, while the lift lives in the chosen target universe `Type ℓ₂`{.Agda}. Decoding alone merely assigns representatives; the two inverse laws below show that no proposition or Boolean code is lost.
<!--zh-->
解码读取布尔标签，返回它所代表的命题：`lift true`{.Agda} 给出 `⊤`{.Agda}，`lift false`{.Agda} 给出 `⊥`{.Agda}。定义域是 `Lift {ℓ-zero} {ℓ₂} Bool`{.Agda} 而非 `Bool`{.Agda} 本身：`Bool`{.Agda} 住在 `Type ℓ-zero`，其提升则住在指定的目标宇宙 `Type ℓ₂`{.Agda}。单独的解码只负责指派代表；下面两条逆律将证明命题与布尔编码都不会在往返中丢失。
<!--ja-->
復号はブールのラベルを読み、それが代表する命題を返します。`lift true`{.Agda} は `⊤`{.Agda} を、`lift false`{.Agda} は `⊥`{.Agda} を返します。定義域は `Bool`{.Agda} 自身ではなく `Lift {ℓ-zero} {ℓ₂} Bool`{.Agda} です。`Bool`{.Agda} は `Type ℓ-zero` に住み、その持ち上げは指定した終域宇宙 `Type ℓ₂`{.Agda} に住みます。復号だけなら代表を割り当てる関数にすぎません。後に続く二つの逆法則が、命題もブール符号も往復で失われないことを示します。
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
The match is on the decision, not on `P`: an inhabitant of the left summand yields `lift true`{.Agda}, one of the right yields `lift false`{.Agda}. The proof or refutation itself is discarded, because the label records only which case held, not a witness. The result type is `Lift {ℓ-zero} {ℓ₂} Bool`{.Agda}, matching `decodeB`{.Agda}'s domain exactly.
<!--zh-->
匹配对象是判定而非 `P`：左支的元素给出 `lift true`{.Agda}，右支的元素给出 `lift false`{.Agda}。证明或反驳本身被丢弃，因为标签只记录出现的是哪种情形，而不是见证。结果类型是 `Lift {ℓ-zero} {ℓ₂} Bool`{.Agda}，与 `decodeB`{.Agda} 的定义域严格相配。
<!--ja-->
マッチの対象は `P` ではなく判定です。左の直和項の元なら `lift true`{.Agda} を、右の元なら `lift false`{.Agda} を返します。証明や反証そのものは捨てられます。ラベルが記録するのはどちらの場合だったかだけで、証拠ではないからです。結果の型は `Lift {ℓ-zero} {ℓ₂} Bool`{.Agda} で、`decodeB`{.Agda} の定義域と正確に一致します。
<!--/-->

```agda
  encodeB : ∀ {ℓ₁ ℓ₂} (P : hProp ℓ₁) → ⟨ P ⟩ ⊎ (⟨ P ⟩ → ⊥₀) → Lift {ℓ-zero} {ℓ₂} Bool
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
If the decision was a proof `p`, the goal is `⊤ ≡ P`{.Agda}. The map from `⊤`{.Agda} to `⟨ P ⟩`{.Agda} is simply `p`, the decided witness; in the reverse direction every input goes to the unique proof of `⊤`{.Agda}. If the decision was a refutation `np`, the goal is `⊥ ≡ P`{.Agda}. Out of `⊥*`{.Agda} there is no constructor to match, which the absurd pattern `λ ()` expresses; in the other direction `np` itself sends each proof of `⟨ P ⟩`{.Agda} to a contradiction. In both branches the chosen representative is path-equal to `P`, so the encoding round trip loses no truth value.
<!--zh-->
若判定是证明 `p`，目标是 `⊤ ≡ P`{.Agda}。从 `⊤`{.Agda} 到 `⟨ P ⟩`{.Agda} 的映射就是判定所得的见证 `p`；反方向上，所有输入都映到 `⊤`{.Agda} 的唯一证明。若判定是反驳 `np`，目标是 `⊥ ≡ P`{.Agda}。从 `⊥*`{.Agda} 出发没有构造子可匹配，荒谬模式 `λ ()` 表达的正是这一点；另一个方向直接由 `np` 把 `⟨ P ⟩`{.Agda} 的每个证明送入矛盾。两个分支中，所选代表都与 `P` 路径相等，于是编码的往返不丢失任何真值。
<!--ja-->
判定が証明 `p` だった場合、ゴールは `⊤ ≡ P`{.Agda} です。`⊤`{.Agda} から `⟨ P ⟩`{.Agda} への写像は判定で得た証拠 `p` そのものであり、逆方向ではすべての入力を `⊤`{.Agda} の唯一の証明へ送ります。判定が反証 `np` だった場合、ゴールは `⊥ ≡ P`{.Agda} です。`⊥*`{.Agda} には照合すべき構成子がないことを荒謬パターン `λ ()` が表し、逆方向では `np` 自身が `⟨ P ⟩`{.Agda} の各証明を矛盾へ送ります。どちらの分岐でも選ばれた代表は `P` とパスで等しく、符号化の往復が真理値を失わないことがわかります。
<!--/-->

```agda
  secB : ∀ {ℓ₁ ℓ₂} (P : hProp ℓ₁) (d : ⟨ P ⟩ ⊎ (⟨ P ⟩ → ⊥₀))
       → decodeB {ℓ₁} {ℓ₂} (encodeB {ℓ₁} {ℓ₂} P d) ≡ P
  secB {ℓ₁} {ℓ₂} P (inl p)  = ⇔toPath (λ _ → p) (λ _ → tt*)
  secB {ℓ₁} {ℓ₂} P (inr np) = ⇔toPath (λ ()) (λ p → ⊥₀-rec (np p))
```

<!--en-->
The second inverse law reads the representative back: `encodeB (decodeB b) d ≡ b`{.Agda}. Here one subtlety is essential. In the assembled classifier the decision `d` will be produced by excluded middle, and nothing guarantees how that decision computes. So `retrB` must hold for **every** decision `d`, not just the ones a particular proof would supply. The proof therefore splits into four cases: two compatible branches compute to `refl`{.Agda}, and two incompatible branches are eliminated as impossible, which also shows the two representatives cannot be confused: `⊤`{.Agda} is inhabited and `⊥`{.Agda} is empty.
<!--zh-->
第二条逆律把代表读回来：`encodeB (decodeB b) d ≡ b`{.Agda}。这里有个关键细节。在组装好的分类器中，判定 `d` 将由排中律产生，而任何东西都不保证那个判定如何计算。所以 `retrB` 必须对**每一个**判定 `d` 成立，而不是只对某个特定证明会供给的判定成立。证明因此分成四种情形：两个相容的分支计算为 `refl`{.Agda}，两个不相容的分支作为不可能而消去；这也表明两个代表不会被混淆，因为 `⊤`{.Agda} 有元素而 `⊥`{.Agda} 为空。
<!--ja-->
第二の逆法則は代表を読み戻します。`encodeB (decodeB b) d ≡ b`{.Agda} です。ここで本質的な注意が一つあります。組み上がった分類子では判定 `d` を排中律が供給しますが、その判定がどのように計算されるかを保証するものは何もありません。したがって `retrB` は、特定の証明が供給しうる判定だけでなく、**すべての**判定 `d` に対して成り立たねばなりません。証明は四つの場合に分かれます。両立する二つの分岐は `refl`{.Agda} に計算され、両立しない二つの分岐は不可能として消去されます。これはまた、`⊤`{.Agda} に要素があり `⊥`{.Agda} が空であることから、二つの代表が混同されえないことも示しています。
<!--/-->

```agda
  retrB : ∀ {ℓ₁ ℓ₂} (b : Lift {ℓ-zero} {ℓ₂} Bool)
          (d : ⟨ decodeB {ℓ₁} {ℓ₂} b ⟩ ⊎ (⟨ decodeB {ℓ₁} {ℓ₂} b ⟩ → ⊥₀))
        → encodeB {ℓ₁} {ℓ₂} (decodeB {ℓ₁} {ℓ₂} b) d ≡ b
```

<!--en-->
For `b = lift true`{.Agda}, decoding gives `⊤`{.Agda}. Encoding with a proof returns `lift true`{.Agda}, and the goal is definitionally `refl`{.Agda}. The alleged refutation branch cannot occur: applying it to the unique proof of `⊤`{.Agda} would give an element of the empty type, leaving no case to prove.
<!--zh-->
当 `b = lift true`{.Agda} 时，解码得 `⊤`{.Agda}。配以证明编码返回 `lift true`{.Agda}，目标按定义就是 `refl`{.Agda}。所谓反驳的分支不可能出现：把它用于 `⊤`{.Agda} 的唯一证明，就会得到空类型的元素，因此没有需要证明的情形。
<!--ja-->
`b = lift true`{.Agda} のとき、復号は `⊤`{.Agda} を返します。証明とともに符号化すれば `lift true`{.Agda} が返り、ゴールは定義上 `refl`{.Agda} です。反証の分岐は起こりえません。`⊤`{.Agda} の唯一の証明に適用すれば空型の元が得られるため、証明すべき場合は残りません。
<!--/-->

```agda
  retrB {ℓ₁} {ℓ₂} (lift true)  (inl _)  = refl
  retrB {ℓ₁} {ℓ₂} (lift true)  (inr n⊤) = ⊥₀-rec (n⊤ tt*)
```

<!--en-->
For `b = lift false`{.Agda}, decoding gives `⊥`{.Agda} with underlying type `⊥*`{.Agda}. An alleged proof of it would be a term of the empty type, so the absurd pattern `()` ends that branch at once; encoding with a refutation returns `lift false`{.Agda}, again by `refl`{.Agda}. Across all four cases, the label returned always equals the label we started from, whichever decision is supplied.
<!--zh-->
当 `b = lift false`{.Agda} 时，解码得 `⊥`{.Agda}，其底层类型为 `⊥*`{.Agda}。它的所谓证明将是空类型的项，荒谬模式 `()` 立即结束该分支；配以反驳编码返回 `lift false`{.Agda}，同样由 `refl`{.Agda} 完成。纵观四种情形，无论供给哪种判定，返回的标签总等于出发时的标签。
<!--ja-->
`b = lift false`{.Agda} のとき、復号は `⊥`{.Agda}、すなわち基礎型 `⊥*`{.Agda} を持つ命題を返します。そのいわゆる証明は空型の項になるはずなので、荒謬パターン `()` がこの分岐を直ちに終わらせ、反証とともに符号化すれば `lift false`{.Agda} が返り、これも `refl`{.Agda} で済みます。四つの場合を通して、どの判定が供給されようとも、返されるラベルは出発点のラベルと等しくなります。
<!--/-->

```agda
  retrB {ℓ₁} {ℓ₂} (lift false) (inl ())
  retrB {ℓ₁} {ℓ₂} (lift false) (inr _)  = refl
```

<!--en-->
Now the pieces assemble into the classifier promised by `ΩResizing ℓ₁ ℓ₂`{.Agda}: the code type `Lift {ℓ-zero} {ℓ₂} Bool`{.Agda} in `Type ℓ₂`{.Agda}, type equivalent to `hProp ℓ₁`{.Agda}. The equivalence comes from an isomorphism whose forward map decides each `P` and encodes it, and whose backward map is `decodeB`{.Agda}. Its two inverse laws are `retrB`{.Agda} and `secB`{.Agda}, instantiated with decisions from `lem`. This final assembly is the only place in the construction where excluded middle is invoked: it uniformly supplies the decisions accepted by the otherwise constructive encoder and inverse laws.
<!--zh-->
现在各部分组装成 `ΩResizing ℓ₁ ℓ₂`{.Agda} 所承诺的分类器：编码类型 `Lift {ℓ-zero} {ℓ₂} Bool`{.Agda} 住在 `Type ℓ₂`{.Agda}，并与 `hProp ℓ₁`{.Agda} 类型等价。这个等价来自一个同构：正向映射判定每个 `P` 后编码，逆向映射是 `decodeB`{.Agda}；两条逆律则是用 `lem` 所给判定实例化的 `retrB`{.Agda} 与 `secB`{.Agda}。整个构造只在最后组装时调用排中律，它一致地供给编码器和逆律所接收的判定，而这些部件本身仍是构造主义的。
<!--ja-->
いま部品が `ΩResizing ℓ₁ ℓ₂`{.Agda} の約束する分類子へと組み上がります。符号の型 `Lift {ℓ-zero} {ℓ₂} Bool`{.Agda} は `Type ℓ₂`{.Agda} に住み、`hProp ℓ₁`{.Agda} と型同値です。この同値は、順写像が各 `P` を判定して符号化し、逆写像が `decodeB`{.Agda} である同型から得られます。二つの逆法則は、`lem` が与える判定で具体化した `retrB`{.Agda} と `secB`{.Agda} です。構成全体で排中律を呼び出すのは、この最後の組み立てだけです。符号化器と逆法則はそれ自体構成的なままで、それらが受け取る判定を排中律が一様に供給します。
<!--/-->

<!--en-->
The pair `(Lift Bool , ...)` witnesses `ΩResizing ℓ₁ ℓ₂`{.Agda}: its first component has type `Type ℓ₂`{.Agda}, and its second is an equivalence `hProp ℓ₁ ≃ Lift Bool`{.Agda}. No ordering between `ℓ₁` and `ℓ₂` is assumed. In the downward instance used later, `ℓ₁ = ℓ-suc ℓ` and `ℓ₂ = ℓ`, so the proposition universe is presented one level down; the theorem itself is more general and also permits equal or higher target levels. The two inverse laws certify both directions of the equivalence, not merely a surjective labelling of propositions by truth values.
<!--zh-->
序对 `(Lift Bool , ...)` 是 `ΩResizing ℓ₁ ℓ₂`{.Agda} 的见证：第一分量类型为 `Type ℓ₂`{.Agda}，第二分量是类型等价 `hProp ℓ₁ ≃ Lift Bool`{.Agda}。这里不假设 `ℓ₁` 与 `ℓ₂` 有任何大小关系。在后文使用的向下实例中，`ℓ₁ = ℓ-suc ℓ` 且 `ℓ₂ = ℓ`，命题宇宙因此被呈现在低一层；但定理本身更一般，也允许目标层级相同或更高。两条逆律认证了等价的两个方向，所以所得结果不只是用真值标签满射地覆盖命题。
<!--ja-->
対 `(Lift Bool , ...)` が `ΩResizing ℓ₁ ℓ₂`{.Agda} の証拠です。第一成分は `Type ℓ₂`{.Agda} の型で、第二成分は型同値 `hProp ℓ₁ ≃ Lift Bool`{.Agda} です。ここでは `ℓ₁` と `ℓ₂` の大小関係を仮定しません。後で使う下向きの実例では `ℓ₁ = ℓ-suc ℓ`、`ℓ₂ = ℓ` なので、命題宇宙は一つ下のレベルで提示されます。しかし定理そのものはより一般的で、終域レベルが同じ場合や高い場合も許します。二つの逆法則は同値の両方向を保証しており、単に真理値のラベルで命題を全射的に覆うだけではありません。
<!--/-->

```agda
lem→ΩResizing : ∀ {ℓ₁ ℓ₂} → LEM ℓ₁ → ΩResizing ℓ₁ ℓ₂
lem→ΩResizing lem = Lift Bool , isoToEquiv (iso
  (λ P → encodeB P (lem P)) decodeB
  (λ b → retrB {ℓ₁ = _} b (lem (decodeB b)))
  (λ P → secB {ℓ₂ = _} P (lem P)))
```

<!--en-->
## Propositional resizing as a consequence

The theorem `lem→resizing`{.Agda} states that excluded middle at the source level implies propositional resizing to any target level. The construction above gives the stronger statement `ΩResizing ℓ₁ ℓ₂`{.Agda}: excluded middle presents the whole proposition universe by the two Boolean codes in `Type ℓ₂`{.Agda}. Applying the general theorem `ΩResizing→Resizing`{.Agda} then chooses a target-level representative for each source proposition. No second classical construction is needed, and the source and target levels need not be adjacent.
<!--zh-->
## 作为推论的命题换级

定理 `lem→resizing`{.Agda} 说明源层级上的排中律蕴含到任意目标层级的命题换级。上面的构造给出更强的陈述 `ΩResizing ℓ₁ ℓ₂`{.Agda}：排中律以 `Type ℓ₂`{.Agda} 中的两个布尔编码呈现整个命题宇宙。再应用一般定理 `ΩResizing→Resizing`{.Agda}，便为每个源层命题选出目标层级的代表。不需要第二套经典构造，源层级与目标层级也不必相邻。
<!--ja-->
## 帰結としての命題リサイズ

定理 `lem→resizing`{.Agda} は、始域レベルでの排中律から任意の終域レベルへの命題リサイズが従うことを述べます。上の構成は、より強い主張 `ΩResizing ℓ₁ ℓ₂`{.Agda} を与えます。排中律によって命題宇宙全体を `Type ℓ₂`{.Agda} の二つのブール符号で提示し、一般定理 `ΩResizing→Resizing`{.Agda} を適用して、各始域命題に終域レベルの代表を選びます。別の古典的構成は要らず、始域と終域のレベルが隣接している必要もありません。
<!--/-->

```agda
lem→resizing : ∀ {ℓ₁ ℓ₂} → LEM ℓ₁ → Resizing ℓ₁ ℓ₂
lem→resizing lem = ΩResizing→Resizing (lem→ΩResizing lem)
```

<!--en-->
## Recap

Excluded middle at an arbitrary source level `ℓ₁` constructs a Boolean classifier in every target universe `ℓ₂`, giving `ΩResizing ℓ₁ ℓ₂`{.Agda}. Propositional resizing is then a theorem about that classifier rather than a separate classical axiom. The cumulative-hierarchy chapters use the downward instance `ΩResizing (ℓ-suc ℓ) ℓ`{.Agda}: power set uses its classifier, and full separation uses the resizing derived from it.
<!--zh-->
## 小结

任意源层级 `ℓ₁` 上的排中律，都能在任意目标宇宙 `ℓ₂` 中构造布尔分类器，从而给出 `ΩResizing ℓ₁ ℓ₂`{.Agda}。命题换级是关于该分类器的一条定理，而非另一条经典公理。累积层级诸章使用向下实例 `ΩResizing (ℓ-suc ℓ) ℓ`{.Agda}：幂集使用其中的分类器，全分离使用由它导出的命题换级。
<!--ja-->
## まとめ

任意の始域レベル `ℓ₁` での排中律は、任意の終域宇宙 `ℓ₂` にブール分類子を構成し、`ΩResizing ℓ₁ ℓ₂`{.Agda} を与えます。命題リサイズは別の古典的公理ではなく、この分類子についての定理です。累積階層の諸章は下向きの実例 `ΩResizing (ℓ-suc ℓ) ℓ`{.Agda} を使い、冪集合は分類子を、完全な分出はそこから導かれる命題リサイズを使います。
<!--/-->
