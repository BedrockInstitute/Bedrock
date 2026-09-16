<!--en-->
# The power set in L
<!--zh-->
# L 中的幂集
<!--ja-->
# L における冪集合
<!--/-->

<!--en-->
For a constructible set `a`, what should its power set inside `L` contain? The
quantifiers of the model range over its carrier `S`, so the required members are
the constructible model elements `x` that satisfy the internal inclusion
`x ⊆ˢ a`. The ambient hierarchy can form the power set of the underlying
set `A = fst a`, but its membership condition ranges over all of `V ℓ` and
imposes no constructibility requirement. That ambient set can therefore supply
indices, but it cannot simply be returned as the power set in `L`.

The proof follows three mathematical steps. It uses the ambient power set to
obtain a small presentation of all candidates, retains the indices that present
constructible candidates and bounds their stages by one ordinal `β`, then uses
Separation inside `Lset β` to collect exactly the internally included model
elements. The host-level construction provides the bound; the final set itself
is produced inside the constructible model.
<!--zh-->
对可构造集 `a`，`L` 内的幂集究竟应当收集什么？模型的量词遍历其载体 `S`，所以所求幂集的成员是满足内部包含 `x ⊆ˢ a` 的可构造模型元素 `x`。外围层级能对底层集 `A = fst a` 构造幂集，但其成员条件遍历整个`V ℓ`，不附加可构造性要求。因此，这个外围幂集可以提供索引，却不能直接作为`L` 内的幂集返回。

证明分三步进行。先由外围幂集取得全部候选者的小表现，再保留其中呈现可构造候选者的索引，并用同一个序数 `β` 界住它们的诸层；最后在 `Lset β` 中作分离，恰好收集内部包含于`a` 的模型元素。宿主层的构造负责给出上界；最终的集合本身则在可构造模型中形成。
<!--ja-->
構成可能集合 `a` の `L` 内部での冪集合は、何を集めるべきでしょうか。モデルの量化子はその台`S` 上を動くので、必要な要素は、内部の包含 `x ⊆ˢ a` を満たす構成可能なモデル要素`x` です。周囲の階層は基底の集合 `A = fst a` の冪集合を作れますが、その所属条件は `V ℓ` 全体にわたり、構成可能性を要求しません。したがって、その周囲の冪集合は添字を供給できますが、`L` の冪集合としてそのまま返すことはできません。

証明は三段階で進みます。まず周囲の冪集合からすべての候補の小さな表示を得ます。次に、構成可能な候補を表示する添字を残し、それらの段階を一つの順序数 `β` で抑えます。最後に `Lset β` の内部で分出を行い、`a` に内部的に含まれるモデル要素だけを集めます。ホスト側の構成が上界を与え、最終的な集合そのものは構成可能モデル内で作られます。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

```

<!--en-->
The construction needs two kinds of smallness. Propositional resizing replaces
a proposition at the model's truth-value level by an equivalent proposition at
the small index level. The impredicativity package also provides a small
classifier for small propositions, from which the ambient hierarchy can form a
power set. Both are derived from excluded middle. They solve different size
problems and should not be confused: resizing will make constructibility fit
inside a small index type, whereas the classifier builds the ambient power set
that supplies the indices.
<!--zh-->
构造需要两种宇宙大小控制。命题换级把模型真值层级上的命题换成小索引层级上的等价命题；非直谓性包还为小命题提供一个命题宇宙换级，使外围层级能够构成幂集。两者都由排中律推出，却解决不同的大小问题：命题换级使可构造性能够进入小索引类型，分类器则构造提供这些索引的外围幂集。
<!--ja-->
構成には二種類の小ささが必要です。命題リサイズは、モデルの真理値のレベルにある命題を、小さな添字のレベルにある同値な命題へ置き換えます。非可述性のパッケージはさらに、小さな命題のための小さな分類子を与え、周囲の階層で冪集合を作れるようにします。どちらも排中律から導かれますが、解決する大きさの問題は異なります。命題リサイズは構成可能性を小さな添字型に収め、分類子はその添字を供給する周囲の冪集合を構成します。
<!--/-->

```agda
open import Base.Prelude
open import Base.Classical using ( LEM; lem→resizing; lem→ΩResizing )

```

<!--en-->
Fix a universe level `ℓ` and one assumption `lem : LEM (ℓ-suc ℓ)`. The goal is
the model field saying that, for each `a` in `L`, there is a unique model element
whose members are exactly the model elements internally included in `a`.
Uniqueness is packaged by the host type `isContr`; the object-theoretic content
is the power-set axiom, and extensionality supplies its uniqueness. The same
single `lem` reaches the proof through four routes: propositional resizing, the
Ω-resizing for the ambient power set, the canonical stage function, and
the reflection used by full Separation. No further classical assumption is
introduced.
<!--zh-->
固定宇宙层级 `ℓ` 与唯一的假设 `lem : LEM (ℓ-suc ℓ)`。目标模型字段断言：对 `L` 中每个 `a`，恰有一个模型元素，其成员正是内部包含于 `a` 的模型元素。唯一性由宿主类型 `isContr` 打包；对象理论内容是幂集公理，而唯一性来自外延性。同一个 `lem` 经四条路径进入证明：命题换级、外围幂集所需的命题宇宙换级、典范层函数，以及完整分离所用的反射。这里没有引入其他经典假设。
<!--ja-->
宇宙レベル `ℓ` と、ただ一つの仮定 `lem : LEM (ℓ-suc ℓ)` を固定します。目標のモデルフィールドは、`L` の各 `a` に対して、`a` に内部的に含まれるモデル要素をちょうど要素とするモデル要素が一意に存在する、と述べます。一意性はホスト型 `isContr` にまとめられます。対象理論での内容は冪集合公理であり、その一意性は外延性から従います。同じ一つの `lem` が、命題リサイズ、周囲の冪集合のための小さな分類子、正準な段階の関数、完全な分出で用いる反映という四つの経路を通って証明に入ります。別の古典的仮定は加わりません。
<!--/-->

```agda
module L.Axioms.Power {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

```

<!--en-->
Three levels of discourse meet in the proof. Host types organize indices and
proofs. The ambient structure `𝒮ᵥ` has all sets of the cumulative hierarchy as
its elements. The restricted structure `𝒮ʟ` has pairs consisting of an ambient
set and evidence that it is constructible. The formula language supplies the
bounded universal needed to express inclusion inside `𝒮ʟ`. Thus the ambient
structure can enumerate possible subsets, while the restricted structure is
where the object-theoretic power-set axiom must be established.
<!--zh-->
证明同时涉及三个层面。宿主类型组织索引与证明；外围结构 `𝒮ᵥ` 的元素是累积层级中的全部集合；限制结构 `𝒮ʟ` 的元素则是外围集合与其可构造性证据组成的对。公式语言提供在 `𝒮ʟ` 内表达包含关系所需的有界全称量词。因此，外围结构可以枚举可能的子集，而对象理论的幂集公理必须在限制结构中成立。
<!--ja-->
証明では三つの水準を区別します。ホスト型は添字と証明を組織します。周囲の構造 `𝒮ᵥ` の要素は累積階層のすべての集合です。制限された構造 `𝒮ʟ` の要素は、周囲の集合とその構成可能性の証拠との対です。論理式の言語は、`𝒮ʟ` の内部で包含を表すための有界全称量化子を備えています。したがって周囲の構造は部分集合の候補を列挙でき、対象理論の冪集合公理は制限された構造の中で証明されます。
<!--/-->

```agda
open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula; var; con; _∈̇_; ∀̇∈ )
import FOL.Absoluteness
import FOL.ZFModel
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
```

<!--en-->
The ambient hierarchy provides a set `𝒫V A` containing every ambient subset of
`A`, together with its membership specification. The constructible hierarchy
provides the stages `Lset α` and their strict monotonicity: membership in an
earlier stage lifts along `α ∈ β`. For each constructible candidate, the stage
function supplies a canonical ordinal index whose stage contains it. The
bounding lemma then places this small family of ordinal indices strictly below
one ordinal. Although the stage function also proves minimality, this chapter
uses only its ordinality and membership facts.
<!--zh-->
外围层级给出集合 `𝒫V A`，它包含 `A` 的每个外围子集，并带有相应的隶属规格。可构造层级给出诸层 `Lset α` 及其严格单调性：若 `α ∈ β`，早期层中的成员可提升到后期层。对每个可构造候选，层函数给出一个典范序数索引，其对应层包含该候选；上界引理再把这一小族序数索引严格界于同一个序数之下。层函数还证明最小性，但本章只使用序数性与层成员这两条事实。
<!--ja-->
周囲の階層は、`A` の周囲でのすべての部分集合を含む集合 `𝒫V A` と、その所属の仕様を与えます。構成可能階層は段階 `Lset α` とその厳密な単調性を与えます。すなわち `α ∈ β` なら、前の段階への所属を後の段階へ持ち上げられます。各構成可能な候補には、段階の関数が、その候補を含む段階の正準な順序数添字を与えます。上界補題は、この小さな順序数添字の族を一つの順序数の真に下へ収めます。段階の関数は最小性も証明しますが、本章で使うのは順序数性と段階への所属だけです。
<!--/-->

```agda
open import V.Model {ℓ} using ( module Power )
open import L.Constructible {ℓ}
  using ( 𝒮ʟ; isL; isL-trans; IsOrd; Lset; Lset-mono )
open import L.Ordinal {ℓ} using ( boundingOrd )
open import L.Stage {ℓ} lem using ( stage; stage-ord; stage-mem )
```

<!--en-->
Once the ordinal bound `β` is available, `LsetS β oβ` is a model element
known to contain every internal subset under consideration. The remaining
mathematical operation is therefore Separation by the one-variable inclusion
formula. The general theorem `hasSeparationL` accepts arbitrary formulas: it
finds a reflecting stage, replaces the formula there by its bounded
relativization, and applies bounded Separation. The present formula is already
Δ₀, but this invocation still follows that general route. Consequently formula
reflection and the stage construction for the parameter are actual uses of the
same `lem`, even in this bounded instance.
<!--zh-->
得到序数上界 `β` 后，`LsetS β oβ` 是一个模型元素，并且已知它包含所有正在考虑的内部子集。因此，余下的数学操作是按一元包含公式作分离。通用定理 `hasSeparationL`接受任意公式：它先找到反射层，在该层上用公式的有界相对化取代原公式，再应用有界分离。本章的公式本来就是 Δ₀，但这次调用仍经由上述通用路径。因而，即使在这个有界特例中，公式反射以及为参数构造层的步骤，也确实使用了同一个 `lem`。
<!--ja-->
順序数の上界 `β` が得られると、`LsetS β oβ` は、考えている内部部分集合をすべて含むと分かっているモデル要素になります。したがって、残る数学的操作は、包含を表す一変数論理式による分出です。一般定理 `hasSeparationL` は任意の論理式を受け取ります。反映する段階を見つけ、その段階で論理式を有界な相対化に置き換え、有界な分出を適用します。ここでの論理式はすでに Δ₀ ですが、この呼び出しは実際にこの一般的な経路を通ります。そのため、この有界な場合にも、論理式の反映とパラメータの段階の構成は、同じ `lem` の実際の使用です。
<!--/-->

```agda
open import L.Axioms.Basic {ℓ} using ( LsetS )
open import L.Axioms.Full {ℓ} lem using ( hasSeparationL )

```

<!--en-->
Every hierarchy set has a small presentation: a type `⟪P⟫` of indices and an
embedding `⟪P⟫↪` that presents its members. Membership in `P` is the
propositional truncation of a fibre of this embedding. Because the map is an
embedding, each fibre is already a proposition, so `∈-asFiber` may recover the
index and its identifying path without invoking Choice. The equivalence maps
also let the proof move between a resized proposition and its original form.
At the end, propositional extensionality turns two implications into a path of
truth values.
<!--zh-->
层级中的每个集合都有小表现：索引类型 `⟪P⟫` 与呈现其成员的嵌入 `⟪P⟫↪`。属于 `P` 被定义为该嵌入某个纤维的命题截断。由于此映射是嵌入，每个纤维本来就是命题，故 `∈-asFiber` 可以恢复索引及识别它的路径，而无须使用选择公理。等价的两个方向还让证明在降级命题与原命题之间往返。最后，命题外延性把两个方向的蕴含变成真值之间的路径。
<!--ja-->
階層の各集合は小さな表現を持ちます。添字型 `⟪P⟫` と、その要素を呈示する埋め込み `⟪P⟫↪` です。`P` への所属は、この埋め込みのファイバーの命題的切り詰めとして定義されます。写像が埋め込みなので各ファイバーはすでに命題であり、`∈-asFiber` は選択公理を使わずに添字とそれを特定するパスを復元できます。同値の二方向は、リサイズされた命題と元の命題との間の往復にも使われます。最後には命題外延性が、二方向の含意を真理値の間のパスへ変えます。
<!--/-->

```agda
open import Cubical.Foundations.Equiv using ( _≃_; invEq; equivFun )
open import Cubical.Functions.Logic using ( ⇔toPath )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Properties
  using ( ∈-asFiber; ⟪_⟫; ⟪_⟫↪ )
```

<!--en-->
Opening `𝒮ʟ` fixes the unqualified carrier `S` and membership relation for the
rest of the proof. An element of `S` is a constructible set together with its
constructibility evidence; `fst` forgets that evidence and returns its ambient
set. The parameter `ℓ` controls small presentation types such as `⟪P⟫`, while
`V ℓ`, the carrier `S`, and the structures' truth values live at `ℓ-suc ℓ`.
Thus the smallness argument concerns the index type, not the model carrier.
<!--zh-->
打开 `𝒮ʟ` 后，下文无修饰的载体 `S` 与隶属关系都指可构造模型。`S` 的元素由一个可构造集合及其可构造性证据组成；`fst` 忘去证据，返回对应的外围集合。参数 `ℓ` 控制 `⟪P⟫` 一类小表现类型，而 `V ℓ`、载体 `S` 与两套结构的真值都位于 `ℓ-suc ℓ`。因此后面的大小问题针对索引类型，不针对模型载体。
<!--ja-->
`𝒮ʟ` を開くと、以下で修飾なしに書く台 `S` と所属関係は構成可能モデルのものになります。`S` の要素は、構成可能な集合とその構成可能性の証拠との対であり、`fst` は証拠を忘れて周囲の集合を返します。パラメータ `ℓ` は `⟪P⟫` のような小さな表現型のレベルを支配し、`V ℓ`、台 `S`、二つの構造の真理値は `ℓ-suc ℓ` に住みます。したがって後の小ささの議論は添字型についてのものであり、モデルの台についてのものではありません。
<!--/-->

```agda

open hPropStructure 𝒮ʟ

```

<!--en-->
The two model interfaces give two subset relations with the same notation but
different quantifier domains. In `ModelL`, `x ⊆ˢ a` quantifies over `S`, so it
tests only constructible elements. In `ModelV`, the corresponding relation
quantifies over every set in `V ℓ`. The latter is stronger for an arbitrary
left side. When the left side is constructible, transitivity of `L` turns each
of its ambient members into an element of `S`, and this supplies the precise
bridge from internal inclusion to ambient inclusion used below.
<!--zh-->
两个模型接口给出记号相同而量化域不同的两种子集关系。在 `ModelL` 中，`x ⊆ˢ a` 量化 `S`，所以只检验可构造元素；在 `ModelV` 中，对应关系量化 `V ℓ` 中的每个集合。对任意左端而言，后一条件更强。若左端本身可构造，则 `L` 的传递性把它的每个外围成员变成 `S` 的元素，从而给出下文所用的精确桥梁：把内部包含提升为外围包含。
<!--ja-->
二つのモデルのインターフェースは、同じ記法を持ちながら量化域の異なる二つの部分集合関係を与えます。`ModelL` の `x ⊆ˢ a` は `S` 上で量化するため、構成可能な要素だけを調べます。`ModelV` の対応する関係は `V ℓ` のすべての集合上で量化します。任意の左辺に対しては後者の方が強い条件です。左辺自身が構成可能なら、`L` の推移性によってその周囲での各要素を `S` の要素にでき、内部の包含から周囲の包含への、以下で必要となる正確な橋が得られます。
<!--/-->

```agda
module ModelL = FOL.ZFModel 𝒮ʟ
open ModelL using ( SetOf; _⊆ˢ_ )
module ModelV = FOL.ZFModel 𝒮ᵥ

```

<!--en-->
The notation `_⊨_` here is the inner satisfaction relation for formulas over
the carrier `S`, evaluated in the restricted structure `𝒮ʟ`. Constants denote
the model elements that they name, and the restricted membership relation reads
their first projections in the ambient hierarchy. The surrounding
absoluteness module makes an outer reading available as well, but this chapter
does not apply an absoluteness theorem. Its only satisfaction statement is the
direct inner meaning of the bounded inclusion formula.
<!--zh-->
这里的记号 `_⊨_` 是载体 `S` 上公式的内层满足关系，公式在限制结构 `𝒮ʟ` 中求值。常元表示它所指名的模型元素，而限制结构的隶属关系在外围层级中读取这些元素的第一投影。同一模块也提供外层读法，但本章没有应用绝对性定理；此处唯一使用的满足陈述，只是有界包含公式在模型内部的直接含义。
<!--ja-->
ここでの記法 `_⊨_` は、台 `S` 上の論理式を制限された構造 `𝒮ʟ` で評価する内側の充足関係です。定数はそれが名指すモデル要素を表し、制限された所属関係は、その第一射影を周囲の階層で読みます。同じモジュールは外側の読み方も与えますが、本章では絶対性定理を適用しません。ここで使う充足の主張は、有界な包含論理式のモデル内部での直接の意味だけです。
<!--/-->

```agda
module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL renaming ( _⊨ᵐ_ to _⊨_ )

```

<!--en-->
The ambient power-set construction is instantiated with Ω-resizing
obtained from `lem→ΩResizing lem`. This construction uses only the
classifier derived from `ΩResizing`: it represents a characteristic function by a
function into a small type of truth-value codes and forms the corresponding
hierarchy set. Propositional resizing of `isL` is a separate operation and does
not enter this instantiation. Keeping these roles distinct will make the later
index construction transparent.
<!--zh-->
外围幂集构造以 `lem→ΩResizing lem` 给出的命题宇宙换级实例化。这里仅使用由 `ΩResizing` 导出的分类器：特征函数被表示为一个取值于小真值码类型的函数，再由此形成层级中的集合。对 `isL` 作命题换级是另一项独立操作，并不进入这次实例化。区分这两种作用，才能看清稍后的小索引是怎样形成的。
<!--ja-->
周囲の冪集合の構成には、`lem→ΩResizing lem` から得られる小さな分類子を与えます。ここで使うのは `ΩResizing` から導かれる分類子だけです。特性関数を小さな真理値コードの型への関数として表し、それに対応する階層の集合を作ります。`isL` の命題リサイズは別の操作であり、この具体化には入りません。二つの役割を分けることで、後の小さな添字の構成が明確になります。
<!--/-->

```agda
module Pow = Power (lem→ΩResizing lem)
```

<!--en-->
## The condition, as a formula
<!--zh-->
## 作为公式的条件
<!--ja-->
## 包含条件を論理式にする
<!--/-->

<!--en-->
For `a : S`, the formula `subFo a` has one free slot for a candidate `x` and
reads

`for every y in x, y is in a`.

The two occurrences of `var zero` lie in different contexts. Outside the
bounded universal it denotes the candidate `x`; inside the body it denotes the
newly bound member `y`. The term `con a` is allowed because the constant domain
is the model carrier. At the environment `x ∷ []`, the semantics of the bounded
universal reduces directly to `x ⊆ˢ a`. This is internal inclusion, with `y`
ranging over constructible model elements. The formula is Δ₀, even though the
proof later passes it to the general Separation interface.
<!--zh-->
对 `a : S`，公式 `subFo a` 留有一个自由槽位给候选 `x`，读作

「对每个 `y ∈ x`，都有 `y ∈ a`」。

`var zero` 的两次出现位于不同语境。有界全称量词之外的那个表示候选 `x`，量词主体中的那个表示新束缚的成员 `y`。常元域就是模型载体，所以 `con a` 可以直接指名 `a`。在环境 `x ∷ []` 中，有界全称的语义直接化归为 `x ⊆ˢ a`。这是内部包含，其中 `y` 只遍历可构造模型元素。该公式是 Δ₀，尽管后面的证明把它交给一般的分离接口。
<!--ja-->
`a : S` に対して、論理式 `subFo a` は候補 `x` のための自由な枠を一つ持ち、

「すべての `y ∈ x` について `y ∈ a`」

と読みます。二つの `var zero` は異なる文脈にあります。有界全称量化子の外側では候補 `x` を表し、その本体では新しく束縛された要素 `y` を表します。定数域がモデルの台なので、`con a` は `a` を直接名指せます。環境 `x ∷ []` では、有界全称の意味論はそのまま `x ⊆ˢ a` に簡約されます。これは内部の包含であり、`y` は構成可能モデルの要素だけを動きます。この論理式は Δ₀ ですが、後の証明では一般の分出インターフェースに渡されます。
<!--/-->

```agda
subFo : S → Formula S 1
subFo a = ∀̇∈ (var zero) (var zero ∈̇ con a)

```

<!--en-->
## Bounding the constructible subsets
<!--zh-->
## 界住诸可构造子集
<!--ja-->
## 構成可能な部分集合を抑える
<!--/-->

<!--en-->
Fix `a : S`. Its first projection `A` is the same set viewed in the ambient
hierarchy, with the constructibility evidence forgotten. The set
`P = Pow.𝒫V A` satisfies the full ambient power-set specification: membership
in `P` requires only ambient inclusion in `A`, with no constructibility
hypothesis. Thus any nonconstructible ambient subset, if one is present, also
belongs to `P`. Moreover, the construction supplies no proof that `P` itself is
constructible. The proof uses only the small presentation `⟪P⟫` and later
filters its indices by constructibility; `P` is not the power set returned in
the model.
<!--zh-->
固定 `a : S`。它的第一投影 `A` 是忘去可构造性证据后，在外围层级中看到的同一个集合。集合 `P = Pow.𝒫V A` 满足完整的外围幂集规格：属于 `P` 只要求在外围意义下包含于 `A`，不带可构造性前提。因此，若有不可构造的外围子集，`P` 也会收纳它们。而且，这个构造没有给出`P` 本身可构造的证明。本证明只使用小表现 `⟪P⟫`，随后以可构造性筛选其索引；`P` 并不是模型中最终返回的幂集。
<!--ja-->
`a : S` を固定します。その第一射影 `A` は、構成可能性の証拠を忘れて、同じ集合を周囲の階層で見たものです。集合 `P = Pow.𝒫V A` は、周囲での完全な冪集合の仕様を満たします。`P` への所属に必要なのは周囲の意味で `A` に含まれることだけであり、構成可能性の仮定はありません。したがって、構成可能でない周囲の部分集合があれば、それも `P` に属します。また、この構成から `P` 自身の構成可能性は得られません。証明が使うのは小さな表示 `⟪P⟫` だけであり、後でその添字を構成可能性によって選び出します。`P` はモデルで最終的に返される冪集合ではありません。
<!--/-->

```agda
module Bound (a : S) where
  private
    A P : V ℓ
    A = fst a
    P = Pow.𝒫V A
```

<!--en-->
For an ambient set `v`, constructibility `isL v` is a proposition at level
`ℓ-suc ℓ`. Concretely, it is the propositional truncation of the existence of
an ordinal stage containing `v`. Such a proposition is too large to use as the
second component of a type at level `ℓ`. The function `rsz` therefore chooses a
small proposition `Q : hProp ℓ` and an equivalence between its underlying type
and `isL v`. This changes only the universe level of the truth value. It neither
removes the propositional truncation nor selects an ordinal stage.
<!--zh-->
对外围集合 `v`，可构造性 `isL v` 是层级 `ℓ-suc ℓ` 上的命题；具体而言，它是「存在一个包含 `v` 的序数层」这一存在式的命题截断。这个命题太大，不能充当层级 `ℓ` 上类型的第二分量。因此，`rsz` 选出小命题 `Q : hProp ℓ`，并给出其底层类型与 `isL v` 之间的等价。这只改变真值所在的宇宙层级，既不消去命题截断，也不选定任何序数层。
<!--ja-->
周囲の集合 `v` に対する構成可能性 `isL v` は、レベル `ℓ-suc ℓ` の命題です。具体的には、`v` を含む順序数段階が存在するという主張の命題的切り詰めです。この命題は、レベル `ℓ` の型の第二成分に置くには大きすぎます。そこで `rsz` は、小さな命題 `Q : hProp ℓ` と、その基礎型と `isL v` との同値を与えます。変わるのは真理値の宇宙レベルだけです。命題的切り詰めを除去することも、順序数段階を選ぶこともありません。
<!--/-->

```agda

    rsz : (v : V ℓ) → Σ[ Q ∈ hProp ℓ ] (⟨ isL v ⟩ ≃ ⟨ Q ⟩)
    rsz v = lem→resizing lem (isL v)

```

<!--en-->
The host type `Ix` indexes exactly the constructible members of the ambient
power set. An element consists of an index `m : ⟪P⟫`, presenting an ambient
subset of `A`, together with a proof of the resized constructibility proposition
for the presented set. Both components are small, so `Ix : Type ℓ` and the
ordinal bounding lemma can quantify over it. `Ix` is only a host-level index
type. It is neither an element of `L` nor a class defined by an object-language
formula, and it will not become the final power set.
<!--zh-->
宿主类型 `Ix` 恰好索引外围幂集中的可构造成员。它的元素由两部分组成：一个索引 `m : ⟪P⟫`，呈现 `A` 的某个外围子集；以及该被呈现集合之降级后可构造性命题的证明。两个分量都属于目标层级，所以 `Ix : Type ℓ`，序数上界引理可以对它量化。`Ix` 只是宿主层的索引类型，既不是 `L` 的元素，也不是对象语言公式定义的类，更不会成为最终的幂集。
<!--ja-->
ホスト型 `Ix` は、周囲の冪集合のうち構成可能な要素をちょうど添字づけます。その要素は、`A` の周囲での部分集合を呈示する添字 `m : ⟪P⟫` と、呈示された集合についてリサイズされた構成可能性命題の証明との対です。両成分が小さいため `Ix : Type ℓ` となり、順序数の上界補題がその上で量化できます。`Ix` はホスト側の添字型にすぎません。`L` の要素でも、対象言語の論理式で定義されたクラスでもなく、最終的な冪集合にもなりません。
<!--/-->

```agda
  Ix : Type ℓ
  Ix = Σ[ m ∈ ⟪ P ⟫ ] ⟨ rsz (⟪ P ⟫↪ m) .fst ⟩

```

<!--en-->
To find a stage for an index `i : Ix`, the proof first restores the original
constructibility proposition. The inverse of the resizing equivalence sends
`i.snd` from the small proposition back to `isL (⟪P⟫↪ i.fst)`. The result still
asserts only, under propositional truncation, that some ordinal stage contains
the presented set. Thus `unres` reverses the change of universe level but does
not extract a witness from the truncation. The next definition performs the
additional work needed to obtain a definite stage index.
<!--zh-->
要为 `i : Ix` 找到一个层，证明先恢复原来的可构造性命题。降级等价的逆向映射把 `i.snd` 从小命题送回 `isL (⟪P⟫↪ i.fst)`。所得结论仍只在命题截断下断言：某个序数层包含该被呈现集合。因此，`unres` 只逆转宇宙层级的改变，并未从截断中抽取见证；取得确定层索引所需的额外工作由下一个定义完成。
<!--ja-->
`i : Ix` の段階を得るため、まず元の構成可能性命題を復元します。リサイズの同値の逆写像は、`i.snd` を小さな命題から `isL (⟪P⟫↪ i.fst)` へ戻します。得られる主張は依然として、ある順序数段階が呈示された集合を含むという命題的切り詰めにとどまります。したがって `unres` は宇宙レベルの変更を逆にするだけで、切り詰めから証人を取り出しません。確定した段階の添字を得るための追加の仕事は、次の定義が行います。
<!--/-->

```agda
  private
    unres : (i : Ix) → ⟨ isL (⟪ P ⟫↪ (i .fst)) ⟩
    unres i = invEq (rsz (⟪ P ⟫↪ (i .fst)) .snd) (i .snd)

```

<!--en-->
The function `stg` assigns each entry of `Ix` its canonical stage index: the
least ordinal `σ` for which the presented set belongs to `Lset σ`. This is a
separate classical step from resizing. Internally, `stage` uses excluded middle
to decide whether a smaller witness exists during a well-founded descent.
Propositional truncation is eliminated only into `LeastOrd`, whose
propositionhood is proved using ordinal trichotomy and uniqueness of the
remaining evidence. The result is therefore a definite ordinal index without a
general rule for extracting arbitrary truncated witnesses. Only `stage-ord` and
`stage-mem`, not minimality, are used here.
<!--zh-->
函数 `stg` 为 `Ix` 的每个条目指定典范层索引，即使被呈现集合属于 `Lset σ` 的最小序数 `σ`。这是与命题换级不同的另一处经典步骤。在内部，`stage` 作良基下降，并用排中律判定是否存在更小的见证。命题截断只被消去到 `LeastOrd`；该类型的命题性由序数三歧与其余证据的唯一性证明。因此，所得结果是一个确定的序数索引，却没有提供从任意截断见证中抽取数据的一般规则。本章只使用 `stage-ord` 与 `stage-mem`，不用其最小性。
<!--ja-->
関数 `stg` は `Ix` の各項に正準な段階の添字を割り当てます。これは、呈示された集合が `Lset σ` に属するような最小の順序数 `σ` です。この古典的な段階は命題リサイズとは別です。内部で `stage` は整礎的な降下を行い、より小さな証人が存在するかを排中律で判定します。命題的切り詰めを除去する先は `LeastOrd` だけであり、その型が命題であることは順序数の三分律と残りの証拠の一意性から示されます。したがって確定した順序数添字は得られますが、任意の切り詰められた証人からデータを取り出す一般則は得られません。本章で使うのは `stage-ord` と `stage-mem` だけで、最小性は使いません。
<!--/-->

```agda
    stg : Ix → V ℓ
    stg i = stage (⟪ P ⟫↪ (i .fst)) (unres i)

```

<!--en-->
Now `stg : Ix → V ℓ` is a genuinely small family, and `stage-ord` proves that
each value is an ordinal. The lemma `boundingOrd` returns explicit data: an
ordinal `β` together with a proof that every `stg i` is a member of `β`. Its
construction is carried out in the host theory by taking successors of the
given ordinals and then their union. It is not an application of Replacement
inside `L`; no Replacement field is used anywhere in this chapter. The strict
bound is exactly the form later required by `Lset-mono`.
<!--zh-->
此时 `stg : Ix → V ℓ` 是真正的小族，而 `stage-ord` 证明每个取值都是序数。引理 `boundingOrd` 返回显式数据：一个序数 `β`，以及每个 `stg i` 都属于 `β` 的证明。其构造在宿主理论中完成，先取给定诸序数的后继，再对它们取并。这不是在 `L` 内应用替换，本章任何地方都没有使用替换字段。所得严格上界恰是稍后 `Lset-mono` 所要求的形式。
<!--ja-->
ここで `stg : Ix → V ℓ` は実際に小さな族となり、`stage-ord` が各値は順序数であることを示します。補題 `boundingOrd` は、順序数 `β` と、各 `stg i` が `β` に属するという証明を明示的なデータとして返します。この構成はホスト理論で、与えられた順序数の後続を取り、続いてそれらの和集合を取ることで行われます。`L` の内部で置換を適用するのではなく、本章では置換のフィールドを一度も使いません。この厳密な上界は、後で `Lset-mono` が要求する形そのものです。
<!--/-->

```agda
    b = boundingOrd Ix stg (λ i → stage-ord (⟪ P ⟫↪ (i .fst)) (unres i))

```

<!--en-->
The first projection of the bounding data is named `β`. It is an ambient
hierarchy set produced by a host-level construction, and the accompanying proof
will show that it is an ordinal. What later becomes an element of the model is
the stage `Lset β`, packaged by `LsetS β oβ`; the proof does not need to package
`β` itself. Moreover, `β` depends on the stages of all constructible ambient
subsets of `A`, rather than only on the stage of `a`. Such a family-dependent
bound suffices for the power-set axiom, so no condensation estimate is needed.
<!--zh-->
上界数据的第一投影记作 `β`。它是在宿主层构造出的外围层级集合，随后的证明表明它是序数。稍后被包装为模型元素的是层 `Lset β`，即 `LsetS β oβ`；本证明不需要把 `β` 自身包装进模型。此外，`β` 依赖 `A` 的全部可构造外围子集之层，而不只依赖 `a` 自己所在的层。这样一个随整个候选族而定的上界已经足以证明幂集公理，因此不需要凝聚给出的精细估计。
<!--ja-->
上界データの第一射影を `β` と名づけます。これはホスト側の構成で得られた周囲の階層の集合であり、次の証明が順序数であることを示します。後でモデル要素としてまとめられるのは段階 `Lset β`、すなわち `LsetS β oβ` であり、`β` 自身をモデルに入れる必要はありません。また `β` は、`a` 自身の段階だけではなく、`A` の周囲での構成可能なすべての部分集合の段階に依存します。このように候補の族全体に依存する上界で冪集合公理には十分なので、凝縮による精密な評価は必要ありません。
<!--/-->

```agda
  β : V ℓ
  β = b .fst

```

<!--en-->
The proof `oβ` records that the bound is an ordinal. The other component of
`b.snd`, used later as `b.snd.snd i`, says `stg i ∈ β` for every `i : Ix`.
This is strict membership of ordinal indices. Given
`stage-mem : presented-set ∈ Lset (stg i)`, `Lset-mono` uses precisely that
membership to lift the presented set into `Lset β`. Ordinality and this strict
bounding property are the two facts about `β` needed in the remainder.
<!--zh-->
证明 `oβ` 记录上界是序数。`b.snd` 的另一分量稍后写作 `b.snd.snd i`，它对每个 `i : Ix` 断言 `stg i ∈ β`。这是序数索引之间的严格隶属。给定 `stage-mem : presented-set ∈ Lset (stg i)`，`Lset-mono` 恰好利用这条隶属把被呈现集合提升到 `Lset β`。序数性与严格上界性质，就是后续对 `β` 所需的两项事实。
<!--ja-->
証明 `oβ` は、上界が順序数であることを記録します。`b.snd` のもう一つの成分は後で `b.snd.snd i` として使われ、各 `i : Ix` に対して `stg i ∈ β` を述べます。これは順序数添字の厳密な所属です。`stage-mem : presented-set ∈ Lset (stg i)` が与えられると、`Lset-mono` はまさにこの所属を用いて、呈示された集合を `Lset β` へ持ち上げます。順序数性とこの厳密な上界性が、以下で `β` について必要となる二つの事実です。
<!--/-->

```agda
  oβ : IsOrd β
  oβ = b .snd .fst

```

<!--en-->
The lemma `below` states the essential coverage property of the bound. If
`x : S` is internally included in `a`, then its underlying ambient set `fst x`
belongs to `Lset β`. The proof first identifies `fst x` with the member of `P`
presented by a suitable index `i : Ix`. The candidate belongs to
`Lset (stg i)` by `stage-mem`, and `stg i ∈ β` lets `Lset-mono` lift this
membership to `Lset β`. The final `subst` transports the result along the
presenting path. The local definitions below justify the existence and
properties of that particular `i`.
<!--zh-->
引理 `below` 陈述上界的关键覆盖性质：若 `x : S` 内部包含于 `a`，则其底层外围集合 `fst x` 属于 `Lset β`。证明先把 `fst x` 认同为 `P` 的某个小索引 `i : Ix` 所呈现的成员。由 `stage-mem`，该候选属于 `Lset (stg i)`；再由 `stg i ∈ β`，`Lset-mono` 把这条隶属提升到 `Lset β`。最后的 `subst` 沿呈现路径把结论搬到 `fst x`。下面的局部定义说明这个特定索引 `i` 为什么存在并具有所需性质。
<!--ja-->
補題 `below` は上界の本質的な被覆性を述べます。`x : S` が `a` に内部的に含まれるなら、その底となる周囲の集合 `fst x` は `Lset β` に属します。証明ではまず、`fst x` を `P` の要素を呈示する適切な添字 `i : Ix` と同一視します。`stage-mem` により候補は `Lset (stg i)` に属し、`stg i ∈ β` に沿って `Lset-mono` を使えば、この所属を `Lset β` へ持ち上げられます。最後の `subst` は、呈示のパスに沿って結果を `fst x` へ運びます。以下の局所定義が、この特定の `i` の存在と必要な性質を示します。
<!--/-->

```agda
  below : (x : S) → ⟨ x ⊆ˢ a ⟩ → ⟨ fst x ∈ Lset β ⟩
  below x x⊆a =
    subst (λ w → ⟨ w ∈ Lset β ⟩) pa
      (Lset-mono {α = β} {β = stg i} (b .snd .snd i) (stage-mem _ (unres i)))
    where
```

<!--en-->
To obtain the index, first convert internal inclusion into ambient inclusion.
Given an arbitrary ambient member `v ∈ fst x`, transitivity of constructibility
produces `isL v` from `x.snd`; the pair `(v , proof)` is then a model element to
which `x⊆a` applies. Hence `fst x` is an ambient subset of `A`. The reverse
direction of `Pow.power-spec` turns this inclusion into `fst x ∈ P`.
Membership in `P` is a propositionally truncated fibre, but the presentation
map is an embedding, so its fibre is a proposition. Accordingly `∈-asFiber`
returns an actual presentation index and a path `pa` identifying its image with
`fst x`. This is elimination justified by uniqueness, not an application of
Choice.
<!--zh-->
为取得索引，先把内部包含转成外围包含。任取外围成员 `v ∈ fst x`，可构造性的传递性从 `x.snd` 推出 `isL v`；于是对 `(v , proof)` 这个模型元素应用 `x⊆a`，便得 `v ∈ A`。因此 `fst x` 是 `A` 的外围子集，而 `Pow.power-spec` 的逆向把这条包含变成 `fst x ∈ P`。`P` 的隶属是表现纤维的命题截断，但表现映射是嵌入，所以该纤维本身是命题。因此，`∈-asFiber` 可以返回实际的表现索引及路径 `pa`，后者把其像认同为 `fst x`。这是由唯一性许可的截断消去，不是选择公理的应用。
<!--ja-->
添字を得るため、まず内部の包含を周囲の包含へ変えます。周囲での任意の要素 `v ∈ fst x` に対し、構成可能性の推移性は `x.snd` から `isL v` を導きます。そこでモデル要素 `(v , proof)` に `x⊆a` を適用すると `v ∈ A` が得られます。したがって `fst x` は周囲で `A` の部分集合であり、`Pow.power-spec` の逆方向がこの包含を `fst x ∈ P` に変えます。`P` への所属は表現のファイバーの命題的切り詰めですが、表現写像は埋め込みなので、そのファイバー自体が命題です。よって `∈-asFiber` は実際の表現添字と、その像を `fst x` と同一視するパス `pa` を返せます。これは一意性によって許される切り詰めの除去であり、選択公理の適用ではありません。
<!--/-->

```agda
    vsub : ⟨ ModelV._⊆ˢ_ (fst x) A ⟩
    vsub v v∈ = x⊆a (v , isL-trans {x = fst x} {y = v} v∈ (x .snd)) v∈
    fib = ∈-asFiber {a = fst x} {b = P}
            (subst ⟨_⟩ (sym (Pow.power-spec A (fst x))) vsub)
    pa : ⟪ P ⟫↪ (fib .fst) ≡ fst x
```

<!--en-->
The path `pa` completes the recovered presentation index into an element of
`Ix`. Its first component is `fib.fst`. For the second, `sym pa` transports
`x.snd : isL (fst x)` to constructibility of the set presented by that index,
and the forward map of the resizing equivalence encodes this proposition at
level `ℓ`. Thus `i` really indexes the same underlying set as `x`, and its stage
is one of the stages bounded by `β`. Combining `stage-mem`, `b.snd.snd i`, and
`Lset-mono`, then transporting along `pa`, proves the conclusion of `below`.
<!--zh-->
路径 `pa` 把恢复出的表现索引补全为 `Ix` 的元素。第一分量是 `fib.fst`。为构造第二分量，先沿 `sym pa` 把 `x.snd : isL (fst x)` 搬到该索引所呈现集合的可构造性，再用降级等价的正向映射把这个命题编码到层级 `ℓ`。因此，`i` 确实索引与 `x` 底层集合相同的候选，其层也属于被 `β` 界住的族。把 `stage-mem`、`b.snd.snd i` 与 `Lset-mono` 组合起来，再沿 `pa` 运输，就得到 `below` 的结论。
<!--ja-->
パス `pa` によって、復元した表現添字を `Ix` の要素へ完成できます。第一成分は `fib.fst` です。第二成分については、`sym pa` に沿って `x.snd : isL (fst x)` をその添字が呈示する集合の構成可能性へ運び、リサイズ同値の順写像でこの命題をレベル `ℓ` に符号化します。したがって `i` は `x` と同じ底集合を持つ候補を実際に添字づけ、その段階は `β` で抑えられた族の一つです。`stage-mem`、`b.snd.snd i`、`Lset-mono` を組み合わせ、最後に `pa` に沿って運ぶと、`below` の結論が得られます。
<!--/-->

```agda
    pa = fib .snd
    i : Ix
    i = fib .fst
      , equivFun (rsz (⟪ P ⟫↪ (fib .fst)) .snd)
          (subst (λ w → ⟨ isL w ⟩) (sym pa) (x .snd))
```

<!--en-->
## The field
<!--zh-->
## 字段
<!--ja-->
## 冪集合フィールド
<!--/-->

<!--en-->
The type of `hasPowerL` is the exact model-theoretic statement to be proved.
It asks for a contractible type of realizers `p : S` whose membership predicate,
tested at every `x : S`, is `x ⊆ˢ a`. At this point the ambient set `P` has
finished its work: it supplied the index family from which `Bound.β a` was
constructed, but it does not appear in the result.

Applying `hasSeparationL` to the model element
`LsetS (Bound.β a) (Bound.oβ a)` first gives a contractible `SetOf` for the
stronger-looking predicate saying that `x` lies in this stage and satisfies
`subFo a`. The only remaining task is to show that this predicate equals
internal inclusion. The local equality `Q≡` provides that identification, and
the outer `subst` transports the contractible package to the predicate required
by the power-set field.
<!--zh-->
`hasPowerL` 的类型就是要证明的精确模型论陈述。它要求由实现者 `p : S` 组成的类型可缩，而对每个 `x : S`，`p` 的成员谓词都是 `x ⊆ˢ a`。此时外围集合 `P` 已完成它的作用：它提供了用于构造 `Bound.β a` 的索引族，却不出现在结论中。

先把 `hasSeparationL` 应用于模型元素`LsetS (Bound.β a) (Bound.oβ a)`，就得到一个可缩的 `SetOf`，它实现的谓词看上去更强：`x` 属于该层，并且满足 `subFo a`。余下只须证这个谓词等于内部包含。局部等式 `Q≡`给出这个识别，最外层的 `subst` 再把可缩包运输到幂集字段所需的谓词上。
<!--ja-->
`hasPowerL` の型は、証明すべきモデル論的な主張をそのまま述べています。すべての`x : S` において所属述語が `x ⊆ˢ a` であるような実現者 `p : S` からなる型が可縮であることを要求します。この段階で、周囲の集合 `P` は役目を終えています。`Bound.β a` を構成するための添字の族を供給しましたが、結論には現れません。

`hasSeparationL` をモデル要素 `LsetS (Bound.β a) (Bound.oβ a)` に適用すると、まず、`x` がこの段階に属し、かつ `subFo a` を満たすという、見かけ上より強い述語に対する可縮な `SetOf` が得られます。残る仕事は、この述語が内部の包含に等しいと示すことだけです。局所的な等式 `Q≡` がその同一視を与え、外側の `subst` が可縮なパッケージを冪集合のフィールドが要求する述語へ輸送します。
<!--/-->

```agda
hasPowerL : (a : S) → isContr (SetOf (λ x → x ⊆ˢ a))
hasPowerL a =
  subst (λ Q → isContr (SetOf Q)) Q≡
    (hasSeparationL (LsetS (Bound.β a) (Bound.oβ a)) (subFo a))
  where
```

<!--en-->
The remaining equality compares the class cut out by separation with the class
required by the power-set field. Its left-hand side says that `x` lies in the
bounding stage and that `x` satisfies `subFo a`; the satisfaction statement
reduces to the internal inclusion `x ⊆ˢ a`. In the forward direction the proof
therefore discards the stage-membership component. In the reverse direction,
`Bound.below` supplies that component from `x ⊆ˢ a`. Propositional
extensionality turns the two implications into a path at each `x`, and
functional extensionality combines these paths into the predicate equality
`Q≡`. The outer `subst` transports the contractible type of realizers supplied
by separation along this equality. Set extensionality is not used in `Q≡`
itself; it has already supplied the uniqueness packaged by separation.

Thus `hasPowerL a` proves the power-set axiom for the object theory in its exact
model-theoretic form. It gives a contractible type of elements `p : S` such
that, for every `x : S`, membership `x ∈ˢ p` is equivalent to the internal
statement `x ⊆ˢ a`. Both `p` and every candidate `x` range over the carrier of
the constructible model. The ambient power set used earlier only provides a
small index of candidates and is not the set produced here. The single
assumption `LEM (ℓ-suc ℓ)` reaches this construction through propositional
resizing, Ω-resizing, the choice of a canonical stage from
propositionally truncated constructibility, and the reflection used by full
separation.
<!--zh-->
余下的等式比较分离切出的类与幂集字段要求的类。左端说 `x` 属于作为上界的层，并且 `x` 满足 `subFo a`；后一个满足命题化为内部包含 `x ⊆ˢ a`。正向证明因而舍去层成员这一分量。反向证明则由 `x ⊆ˢ a` 应用 `Bound.below` 补出该分量。命题外延性把两个方向的蕴含变成每个 `x` 处的路径，函数外延性再把这些路径合成为谓词等式 `Q≡`。最外层的 `subst` 沿这个等式运输分离所得的可缩实现者类型。`Q≡` 本身不使用集合外延性；分离所打包的一意性已经用过集合外延性。

因此，`hasPowerL a` 以精确的模型论形式证明对象理论的幂集公理。它给出由元素 `p : S` 组成的可缩类型，并且对每个 `x : S`，成员命题 `x ∈ˢ p` 恰与内部陈述 `x ⊆ˢ a` 等价。`p` 与每个候选 `x` 都量化于可构造模型的载体。此前使用的宿主层幂集只提供候选者的小索引，并不是此处得到的集合。唯一的假设 `LEM (ℓ-suc ℓ)` 经命题换级、命题宇宙换级、从命题截断的可构造性中选出典范层，以及完整分离所用的反射，传递到这一构造。
<!--ja-->
残る等式は、分出によって切り出されたクラスと、冪集合フィールドが要求するクラスを比較します。左辺は、`x` が上界となる段階に属し、かつ `subFo a` を満たすと述べます。後半の充足命題は、内部の包含 `x ⊆ˢ a` に簡約されます。したがって順方向の証明は、段階への所属を表す成分を捨てます。逆方向では、`x ⊆ˢ a` に `Bound.below` を適用してその成分を補います。命題外延性は二方向の含意を各 `x` におけるパスへ変え、関数外延性はそれらのパスを述語の等式 `Q≡` にまとめます。最外側の `subst` は、この等式に沿って、分出が与えた実現者の可縮な型を輸送します。`Q≡` 自体は集合の外延性を使いません。分出がまとめた一意性の中ですでに使われています。

したがって `hasPowerL a` は、対象理論の冪集合公理を正確なモデル論的形式で証明します。これは要素 `p : S` からなる可縮な型を与え、すべての `x : S` について、所属命題 `x ∈ˢ p` が内部の主張 `x ⊆ˢ a` と同値であることを示します。`p` も候補となる各 `x` も、構成可能モデルの台の上で量化されています。前に用いた周囲の階層の冪集合は、候補の小さな添字を与えるだけであり、ここで得られる集合ではありません。ただ一つの仮定 `LEM (ℓ-suc ℓ)` は、命題リサイズ、小さな分類器、命題的切り詰めを施した構成可能性からの標準的な段階の選択、そして完全分出が用いる反映を通じて、この構成に届きます。
<!--/-->

```agda
  Q≡ : (λ x → (x ∈ˢ LsetS (Bound.β a) (Bound.oβ a)) ⊓ ((x ∷ []) ⊨ subFo a))
     ≡ (λ x → x ⊆ˢ a)
  Q≡ = funExt (λ x → ⇔toPath
    (λ { (_ , x⊆a) → x⊆a })
    (λ x⊆a → Bound.below a x x⊆a , x⊆a))
```

<!--en-->
## Recap
<!--zh-->
## 小结
<!--ja-->
## まとめ
<!--/-->

<!--en-->
The construction has three distinct roles: the ambient power set supplies a
small presentation, the host theory bounds the stages of its constructible
members, and internal Separation cuts the desired set from that bound.
`L.Model` installs `hasPowerL` as the `hasPower` field of `L⊨ZF`, after which
the record defines the internal operation `𝒫`. The later GCH arguments use this
operation and the specification `℩-spec (hasPower κ)` to pass between membership
and internal inclusion; they never use the auxiliary ambient `Pow.𝒫V`.

The logical account is equally specific. The one assumption
`LEM (ℓ-suc ℓ)` supplies Ω-resizing, propositional resizing, the
canonical stage construction, and formula reflection for full Separation. No
form of Choice, the Replacement field, or condensation is used in this proof.
<!--zh-->
这个构造中的三种作用彼此分明：外围幂集提供小表现，宿主理论界住其可构造成员的诸层，内部分离则从该上界中切出所求集合。`L.Model` 把 `hasPowerL` 装入 `L⊨ZF` 的 `hasPower`字段，随后由这个 record 定义内部运算 `𝒫`。后续 GCH 论证使用此运算与规格`℩-spec (hasPower κ)`，在成员关系与内部包含之间往返；它们从不使用辅助的外围 `Pow.𝒫V`。

逻辑依赖也可以精确列清。唯一的假设 `LEM (ℓ-suc ℓ)` 分别支持命题宇宙换级、命题换级、典范层构造与完整分离所用的公式反射。本证明不使用任何形式的选择、替换字段或凝聚。
<!--ja-->
この構成には、明確に異なる三つの役割があります。周囲の冪集合が小さな表示を供給し、ホスト理論がその構成可能な要素の段階を抑え、内部の分出がその上界から求める集合を切り出します。`L.Model` は `hasPowerL` を `L⊨ZF` の `hasPower` フィールドに組み込み、その後レコードが内部演算 `𝒫` を定義します。後の GCH の議論は、この演算と仕様 `℩-spec (hasPower κ)` を使って所属と内部の包含の間を往復します。補助的な周囲の `Pow.𝒫V` を使うことはありません。

論理的な依存関係も具体的です。唯一の仮定 `LEM (ℓ-suc ℓ)` が、小さな分類子、命題リサイズ、正準な段階の構成、および完全な分出のための論理式の反映を支えます。この証明では、選択、置換のフィールド、凝縮のいずれも使いません。
<!--/-->
