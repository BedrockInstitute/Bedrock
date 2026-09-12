<!--en-->
# Syntax as sets

A model can quantify only over elements of its carrier, whereas terms and formulas initially live in the surrounding type theory. To make syntax available inside the model, this chapter assigns each term and formula an element of the carrier. A code is a tagged pair: the numeric tag identifies the outer constructor, and the payload contains the codes of its immediate parts. Set constants can appear directly as payloads because they already belong to the carrier.

The construction assumes an injective pairing operation and an injective map from natural numbers. These hypotheses make both components recoverable from a tagged pair. The chapter first proves that term codes are injective, then defines formula codes for all ten constructors. It also gives the constant and membership cases of relational coding through `CodesT`{.Agda} and `Codes`{.Agda}. Finally, a tag-indexed description of constructor shapes supports the proof that equal codes determine equal formulas of the same arity.
<!--zh-->
# 作为集合的语法

模型只能对其载体中的元素量化，而词项与公式起初存在于外部的类型论中。为了让模型内部能够使用语法，本章给每个词项和公式指派一个载体元素。一个码是带标签的对：数字标签识别最外层构造子，载荷保存各直接组成部分的码。集合常元已经属于载体，因此可以直接充当载荷。

构造假设有一个单射配对运算和一个从自然数出发的单射；这两个条件保证带标签对的两部分都能恢复。本章先证明词项编码为单射，再为公式的十个构造子定义编码。它还通过 `CodesT`{.Agda} 与 `Codes`{.Agda} 给出关系式编码的常元与隶属情形。最后，由标签索引的构造子形状描述支撑如下证明：同一元数的公式若码相等，则公式相等。
<!--ja-->
# 集合としての構文

モデルが量化できるのは台の元だけですが、項と論理式は初め、外側の型理論にあります。構文をモデルの内部で利用できるように、本章では各項と論理式に台の元を割り当てます。符号はタグ付きの対であり、数のタグが最外側の構成子を識別し、ペイロードが直下の部分の符号を保持します。集合定数はすでに台に属するので、そのままペイロードにできます。

構成では、単射な対の操作と自然数からの単射を仮定します。この二つの仮定により、タグ付き対の両成分を復元できます。まず項の符号化が単射であることを証明し、次に論理式の十個の構成子すべてに符号を定めます。また `CodesT`{.Agda} と `Codes`{.Agda} によって、関係としての符号化のうち定数と所属の場合を与えます。最後に、タグで添字付けた構成子形状の記述を用いて、同じアリティの論理式は符号が等しければ等しいことを証明します。
<!--/-->

<!--en-->
To encode syntax as sets, two operations on the carrier would suffice on their own, but injectivity is what makes decoding possible: if two pieces of syntax received the same set, the coding could not be inverted. This chapter therefore works over a structure `𝒮`{.Agda} of type `ZFStructure`{.Agda} sitting on the hProp algebra at level `ℓ`, and takes the encoding data as explicit module parameters. Every definition below is stated for an arbitrary structure with such data; the cumulative hierarchy will supply an instance in a later chapter.
<!--zh-->
要把语法编码为集合，载体上的两个操作本身就够了，但真正让「解码」成为可能的是单射性：若两段语法得到同一个集合，编码就无法还原。因此本章在层级 `ℓ` 上 hProp 代数上的一个 `ZFStructure`{.Agda} 结构 `𝒮`{.Agda} 中工作，并把编码所需的数据取作显式的模块参数。下面每个定义都对任意一个带这类数据的结构成立；累积层级会在后面的章节中给出实例。
<!--ja-->
構文を集合として符号化するには、台の上の 2 つの操作があれば足りますが、復号を可能にするのは単射性です。もし 2 つの構文が同じ集合に対応してしまったら、符号化を逆にたどれません。そこで本章は、レベル `ℓ` の hProp 代数上の `ZFStructure`{.Agda} である構造 `𝒮`{.Agda} のもとで作業し、符号化に必要なデータを明示的なモジュール引数として取ります。以下の定義はすべて、そのようなデータを持つ任意の構造に対して述べられ、累積階層が後の章で実例を供給します。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import FOL.ZFStructure using ( ZFStructure )

module FOL.Coding {ℓ} (𝒮 : ZFStructure (hPropAlgebra ℓ))
```

<!--en-->
The two pieces of data are an injective pairing and an injective numeral map. `pr` takes two elements of the carrier `S` to their pair, and `pr-inj` says the pairing can be taken apart again: an equality `pr a b ≡ pr c d` returns both `a ≡ c` and `b ≡ d` as a pair of paths. `encℕ` sends each natural number to an element of `S`, and `encℕ-inj` says distinct numbers land at distinct elements. These are exactly the hypotheses the tagged-pair construction will consume; nothing else about `𝒮`{.Agda} enters the chapter.
<!--zh-->
这两份数据是一个单射配对和一个单射数字映射。`pr` 把载体 `S` 的两个元素映为它们的序对，`pr-inj` 说这个配对可以重新拆开：等式 `pr a b ≡ pr c d` 给出 `a ≡ c` 与 `b ≡ d` 两条路径组成的对。`encℕ` 把每个自然数送到 `S` 的一个元素，`encℕ-inj` 说不同的数落在不同的元素上。带标签对的构造消耗的正是这些假设；本章不再使用 `𝒮`{.Agda} 的其他任何内容。
<!--ja-->
2 つのデータとは、単射な対の操作と単射な数の写像です。`pr` は台 `S` の 2 つの元をその対に写し、`pr-inj` はこの対がまた分解できることを述べます。つまり等式 `pr a b ≡ pr c d` から `a ≡ c` と `b ≡ d` という 2 つの道の組が得られます。`encℕ` は各自然数を `S` の元へ送り、`encℕ-inj` は異なる数が異なる元に写ることを述べます。タグ付き対の構成が消費するのはまさにこれらの仮定で、本章は `𝒮`{.Agda} のそれ以外の性質をまったく使いません。
<!--/-->

```agda
  (pr       : ZFStructure.S 𝒮 → ZFStructure.S 𝒮 → ZFStructure.S 𝒮)
  (pr-inj   : ∀ {a b c d} → pr a b ≡ pr c d → (a ≡ c) × (b ≡ d))
  (encℕ     : ℕ → ZFStructure.S 𝒮)
  (encℕ-inj : ∀ {j k} → encℕ j ≡ encℕ k → j ≡ k)
  where
```

<!--en-->
The objects being coded come from the syntax layer: the inductive types `Term`{.Agda} and `Formula`{.Agda}, built from two term constructors (`con` for a set constant, `var` for a variable) and ten formula constructors, from the atoms `_∈̇_` and `_≐_` through the connectives and the bounded and unbounded quantifiers. From the structure itself, only the carrier `S` is used, since coding attaches no set-theoretic operation to syntax. The empty type appears only as the codomain of impossible equations, in proofs that certain codes cannot coincide.
<!--zh-->
被编码的对象来自句法层：归纳类型 `Term`{.Agda} 与 `Formula`{.Agda}，由两个词项构造子 (集合常元 `con` 与变元 `var`) 和十个公式构造子组成，从原子式 `_∈̇_` 与 `_≐_` 一直到联结词以及有界与无界量词。结构本身只用到载体 `S`，因为编码不给语法附加任何集合论运算。空类型只作为不可能等式的值域出现，用于证明某些码不可能重合。
<!--ja-->
符号化される対象は構文層から来ます。すなわち帰納型 `Term`{.Agda} と `Formula`{.Agda} で、項の構成子は 2 つ (集合定数 `con` と変数 `var`)、論理式の構成子は 10 個あり、原子式 `_∈̇_` と `_≐_` から結合子、有界・無界量化子に至ります。構造そのものから使うのは台 `S` だけで、符号化が構文に集合論の演算を付加することはないからです。空型は、特定の符号が一致しえないことを証明するときの、ありえない等式の値域としてだけ現れます。
<!--/-->

```agda

open ZFStructure 𝒮 using ( S )
open import FOL.Syntax
  using ( Term; con; var; Formula
        ; _∈̇_; _≐_; _∧̇_; _∨̇_; _⇒̇_; ⊥̇; ∃̇_; ∀̇_; ∀̇∈; ∃̇∈ )

import Cubical.Data.Empty as Empty
```

<!--en-->
Two small arithmetic facts support the injectivity proofs. First, structurally distinct numerals are never equal: the lemmas `znots` and `snotz` refute `0 ≡ suc k` and `suc j ≡ 0`, and these are exactly the clashes that occur when two formulas with different tags are assumed to share a code. Second, a variable index in `Fin n` is converted to a natural number by `toℕ`, and `inj-toℕ` records that this conversion is injective, so coding a variable by its index loses no information.
<!--zh-->
两个小的算术事实支撑着单射性证明。其一，结构上不同的数字永不相等：引理 `znots` 与 `snotz` 分别否证 `0 ≡ suc k` 与 `suc j ≡ 0`，而带不同标签的两条公式被假设共享一个码时，产生的正是这类冲突。其二，`Fin n` 中的变元序号经 `toℕ` 转换为自然数，`inj-toℕ` 记录这一转换是单射的，因此按序号编码变元不会丢失信息。
<!--ja-->
単射性の証明を支えるのは、2 つの小さな算術的事実です。第一に、構造的に異なる数は決して等しくありません。補題 `znots` と `snotz` がそれぞれ `0 ≡ suc k` と `suc j ≡ 0` を反駁し、異なるタグを持つ 2 つの論理式が同じ符号を共有すると仮定したときに生じる衝突は、まさにこの形をしています。第二に、`Fin n` の変数の添字は `toℕ` で自然数に変換され、`inj-toℕ` はこの変換が単射であることを記録します。したがって添字による変数の符号化で情報は失われません。
<!--/-->

```agda
open import Cubical.Data.Nat using ( znots; snotz )
open import Cubical.Data.FinData using ( toℕ; inj-toℕ )
```

<!--en-->
## Tagged pairs

The one construction: a constructor index paired with a payload. Injectivity comes straight from the two parameters, and the clash pattern packages the case that will recur whenever two different constructors are compared.
<!--zh-->
## 带标签的对

唯一的构造：构造子序号与载荷配成对。单射性直接来自那两个参数，而冲突模式把「两个不同构造子相比较」时反复出现的情况集中处理。
<!--ja-->
## タグ付き対

唯一の構成です。構成子の番号とペイロードを対にします。単射性は 2 つのパラメータから直ちに得られ、衝突パターンは「異なる 2 つの構成子を比較する」という、のちに繰り返し現れる場合を一箇所にまとめます。
<!--/-->

<!--en-->
The building block is `mkTag k x = pr (encℕ k) x`: the tag is the numeral of `k` and the payload is `x`, both elements of `S` since `pr` returns one. A small example shows how the tag separates shapes: the code of a constant will be `mkTag 0 x`, while the code of a variable with index `i` will be `mkTag 1 (encℕ (toℕ i))`. If two tagged pairs were equal, the tags would have to agree; `mkTag-inj` makes this precise, composing `pr-inj` and `encℕ-inj` to return `(j ≡ k) × (x ≡ y)`. Its dual, `clash`, handles the negative case: given a proof that the tags `j` and `k` cannot be equal, it extracts the tag equation from an equality of tagged pairs and contradicts that proof, concluding in any type `A` of the ambient level.
<!--zh-->
基本构件是 `mkTag k x = pr (encℕ k) x`：标签是 `k` 的数字，载荷是 `x`，由于 `pr` 返回 `S` 的元素，二者都在 `S` 中。一个小例子可见标签如何区分形状：常元的码将是 `mkTag 0 x`，而序号为 `i` 的变元的码将是 `mkTag 1 (encℕ (toℕ i))`。若两个带标签对相等，标签必须一致；`mkTag-inj` 把这一点写清楚，复合 `pr-inj` 与 `encℕ-inj` 而返回 `(j ≡ k) × (x ≡ y)`。它的对偶 `clash` 处理否定情形：给定「标签 `j` 与 `k` 不可能相等」的证明，它从带标签对的等式中抽出标签等式，与该证明矛盾，从而在环境层级的任意类型 `A` 中得出结论。
<!--ja-->
基本の部品は `mkTag k x = pr (encℕ k) x` です。タグは `k` の数であり、ペイロードは `x` です。`pr` が `S` の元を返すため、両者とも `S` にあります。小さな例で、タグが形をどう区別するかが分かります。定数の符号は `mkTag 0 x` になり、添字 `i` の変数の符号は `mkTag 1 (encℕ (toℕ i))` になる予定です。2 つのタグ付き対が等しければタグは一致しなければならず、`mkTag-inj` がこれを正確に述べます。`pr-inj` と `encℕ-inj` を合成して `(j ≡ k) × (x ≡ y)` を返します。その双対である `clash` は否定の場合を扱います。タグ `j` と `k` が等しくなりえないことの証明が与えられると、タグ付き対の等式からタグの等式を取り出してその証明と矛盾させ、周囲のレベルの任意の型 `A` で結論します。
<!--/-->

```agda
mkTag : ℕ → S → S
mkTag k x = pr (encℕ k) x

mkTag-inj : ∀ {j k x y} → mkTag j x ≡ mkTag k y → (j ≡ k) × (x ≡ y)
mkTag-inj p = encℕ-inj (pr-inj p .fst) , pr-inj p .snd

clash : ∀ {j k x y} {A : Type ℓ} → (j ≡ k → Empty.⊥) → mkTag j x ≡ mkTag k y → A
```

<!--en-->
The body of `clash` runs this argument in one line. `mkTag-inj p .fst` is the equation `j ≡ k` extracted from the assumed equality of codes; feeding it to the hypothesis `ne` yields an element of the empty type, and `Empty.rec` eliminates that element to return a value of the arbitrary type `A`. Whenever two constructor shapes force numerals `0` and `suc _` to be equal, `clash` converts the arithmetic refutation into the needed conclusion.
<!--zh-->
`clash` 的主体把这一论证写成一行。`mkTag-inj p .fst` 是从假设的码等式中抽出的等式 `j ≡ k`；把它交给假设 `ne` 得到空类型的一个元素，`Empty.rec` 消去该元素，返回任意类型 `A` 中的值。每当两个构造子形状迫使数字 `0` 与 `suc _` 相等时，`clash` 就把这一算术否证转化为所需的结论。
<!--ja-->
`clash` の本体はこの議論を 1 行にまとめます。`mkTag-inj p .fst` は仮定した符号の等式から取り出した等式 `j ≡ k` であり、それを仮定 `ne` に渡すと空型の元が得られ、`Empty.rec` がその元を消去して任意の型 `A` の値を返します。2 つの構成子の形が数 `0` と `suc _` を等しくさせるたびに、`clash` はこの算術的反駁を必要な結論へ変換します。
<!--/-->

```agda
clash ne p = Empty.rec (ne (mkTag-inj p .fst))
```

<!--en-->
## Codes

Terms first, where the promised elegance appears: a set constant needs no encoding, since it is already a set, and only the variable index has to be injected. Terms are separated enough that their injectivity is immediate.
<!--zh-->
## 码

先看项，前文所说那点简洁在此出现：集合常元无须编码，因为它本来就是集合，只有变元的序号要被注入。不同项的码彼此可以分辨，单射性立得。
<!--ja-->
## 項と論理式の符号

まず項からです。ここで前述の工夫が現れます。集合の定数はすでに集合であるため符号化を必要とせず、変数の添字だけを注入すればよいのです。項どうしはよく分離されているので、単射性は直ちに得られます。
<!--/-->

<!--en-->
A term in context `n` codes as an element of `S` by the two clauses above. A constant `con x` gets tag `0` and payload `x`, the set itself: the promised economy, since no encoding of the payload is needed. A variable `var i` gets tag `1` and payload the numeral of `toℕ i`, so the tag and the index live on different sides of the pair and cannot be confused. The injectivity proof splits by the constructors of both terms. In the constant-constant case only the payloads can differ, so `mkTag-inj p .snd` is directly `x ≡ y`, and `cong con` lifts it to `con x ≡ con y`.
<!--zh-->
语境 `n` 中的词项由上面两条子句编码为 `S` 的元素。常元 `con x` 得标签 `0`、载荷 `x`，即该集合本身：这正是前文所说的省事之处，载荷无须另行编码。变元 `var i` 得标签 `1`、载荷 `toℕ i` 的数字，于是标签与序号分处序对的两侧，不会混淆。单射性证明按两个词项的构造子分情形。在常元对常元的情形只有载荷可能不同，故 `mkTag-inj p .snd` 直接就是 `x ≡ y`，再由 `cong con` 提升为 `con x ≡ con y`。
<!--ja-->
文脈 `n` の項は、上の 2 つの節で `S` の元として符号化されます。定数 `con x` はタグ `0` とペイロード `x`、すなわち集合そのものを取ります。ここが前述の省力化で、ペイロードを別途符号化する必要がありません。変数 `var i` はタグ `1` と `toℕ i` の数を取り、タグと添字が対の異なる側に置かれるため混同されません。単射性の証明は両項の構成子で場合分けします。定数対定数の場合、違い得るのはペイロードだけなので、`mkTag-inj p .snd` が直接 `x ≡ y` を与え、`cong con` がこれを `con x ≡ con y` へ持ち上げます。
<!--/-->

```agda
⌜_⌝ᵗ : ∀ {n} → Term S n → S
⌜ con x ⌝ᵗ = mkTag 0 x
⌜ var i ⌝ᵗ = mkTag 1 (encℕ (toℕ i))

⌜⌝ᵗ-inj : ∀ {n} (t u : Term S n) → ⌜ t ⌝ᵗ ≡ ⌜ u ⌝ᵗ → t ≡ u
⌜⌝ᵗ-inj (con x) (con y) p = cong con (mkTag-inj p .snd)
```

<!--en-->
The remaining branches complete the argument. In a mixed case, an equality of codes would force the numerals `0` and `1` to be equal; since `1` is a successor, `znots` or `snotz` refutes this, and `clash` turns the refutation into an equality of terms. In the variable-variable case the payload equation says `encℕ (toℕ i) ≡ encℕ (toℕ j)`; `encℕ-inj` yields `toℕ i ≡ toℕ j`, and `inj-toℕ` promotes it to `i ≡ j`, from which `cong var` gives `var i ≡ var j`. Every branch ends in an equation of terms, so for each fixed `n` the code function is injective on `Term S n`. Note that `n` here is the number of available variable slots, not the number of variables a particular term actually uses.
<!--zh-->
其余分支补完论证。混合情形中，码的相等将迫使数字 `0` 与 `1` 相等；由于 `1` 是后继，`znots` 或 `snotz` 恰好否证这一点，`clash` 再把否证转化为词项等式。变元对变元的情形，载荷等式说 `encℕ (toℕ i) ≡ encℕ (toℕ j)`；`encℕ-inj` 给出 `toℕ i ≡ toℕ j`，`inj-toℕ` 把它提升为 `i ≡ j`，再由 `cong var` 得 `var i ≡ var j`。每个分支都以词项等式收尾，故对每个固定的 `n`，码函数在 `Term S n` 上单射。注意这里的 `n` 是可用的变元槽位数，而不是某个具体词项实际使用的变元个数。
<!--ja-->
残りの分岐が議論を完成させます。混在する場合、符号の等しさは数 `0` と `1` の等しさを強制します。`1` は後続者なので `znots` か `snotz` がこれを反駁し、`clash` がその反駁を項の等式へ変えます。変数対変数の場合、ペイロードの等式は `encℕ (toℕ i) ≡ encℕ (toℕ j)` を意味し、`encℕ-inj` が `toℕ i ≡ toℕ j` を、`inj-toℕ` がさらに `i ≡ j` を与え、`cong var` によって `var i ≡ var j` が得られます。すべての分岐が項の等式で終わるため、固定した `n` ごとに符号関数は `Term S n` 上で単射です。ここでの `n` は利用できる変数スロットの個数であり、個々の項が実際に使う変数の個数ではない点に注意してください。
<!--/-->

```agda
⌜⌝ᵗ-inj (con x) (var j) p = clash znots p
⌜⌝ᵗ-inj (var i) (con y) p = clash snotz p
⌜⌝ᵗ-inj (var i) (var j) p = cong var (inj-toℕ (encℕ-inj (mkTag-inj p .snd)))
```

<!--en-->
Then formulas: ten constructors, ten tags. Binary constructors pair the two sub-codes, unary ones take the sub-code bare, and falsity takes a dummy payload since its tag already determines it.
<!--zh-->
然后是公式：十个构造子，十个标签。二元构造子把两个子码配成对，一元的直接取子码；「假」取一个虚设的载荷，因为标签已经决定了它。
<!--ja-->
次に論理式です。10 個の構成子に 10 個のタグを割り当てます。2 項の構成子は 2 つの部分符号を対にし、1 項のものは部分符号をそのまま受け取り、偽はタグだけで決まるため仮のペイロードを取ります。
<!--/-->

<!--en-->
Formulas use the same tagged-pair scheme, with tags `0` through `4` on the five binary constructors. A membership atom `t ∈̇ u` codes as tag `0` paired with the pair of the two term codes, and equality likewise at tag `1`; each connective pairs the codes of its two immediate subformulas. Compare this with terms: there the payload was a bare set or a numeral, here it may itself be a built-up code, so the whole structure of a formula nests inside payloads. The recursion happens on the host inductive types `Term`{.Agda} and `Formula`{.Agda}, never on the sets themselves.
<!--zh-->
公式沿用同样的带标签对方案，五个二元构造子分得标签 `0` 到 `4`。隶属原子式 `t ∈̇ u` 以标签 `0` 配上两个词项码组成的对来编码，相等式同样在标签 `1`；每个联结词把两条直接子公式的码配成对。与词项对比：那里的载荷是裸集合或数字，而这里的载荷本身可以是由码搭建的复合物，公式的整个结构就这样嵌套在载荷之中。递归发生在宿主的归纳类型 `Term`{.Agda} 与 `Formula`{.Agda} 上，从不在集合自身上进行。
<!--ja-->
論理式も同じタグ付き対の方式を使います。5 つの 2 項構成子にタグ `0` から `4` までを割り当てます。所属の原子式 `t ∈̇ u` はタグ `0` に 2 つの項の符号の対を組み合わせて符号化され、等号も同様にタグ `1` です。各結合子は 2 つの直接の部分論理式の符号を対にします。項と比べると、あちらのペイロードは生の集合か数でしたが、こちらではペイロード自身が組み上がった符号であり得るので、論理式の構造全体がペイロードの中にネスティングします。再帰はホストの帰納型 `Term`{.Agda} と `Formula`{.Agda} の上で起こり、集合の上では決して起こりません。
<!--/-->

```agda
⌜_⌝ : ∀ {n} → Formula S n → S
⌜ t ∈̇ u ⌝   = mkTag 0  (pr ⌜ t ⌝ᵗ ⌜ u ⌝ᵗ)
⌜ t ≐ u ⌝   = mkTag 1  (pr ⌜ t ⌝ᵗ ⌜ u ⌝ᵗ)
⌜ φ ∧̇ ψ ⌝   = mkTag 2  (pr ⌜ φ ⌝ ⌜ ψ ⌝)
⌜ φ ∨̇ ψ ⌝   = mkTag 3  (pr ⌜ φ ⌝ ⌜ ψ ⌝)
```

<!--en-->
Implication takes tag `4` like the other connectives. Falsity `⊥̇` is the one constructor with no parts: its tag `5` alone determines it, so the payload is the dummy numeral `encℕ 0`, present only so every code has the uniform form of a tagged pair. The unbounded quantifiers `∃̇` and `∀̇` are unary; their codes are tag `6` or `7` paired directly with the subformula's code.
<!--zh-->
蕴涵与其他联结词一样取标签 `4`。「假」`⊥̇` 是唯一没有部分的构造子：标签 `5` 本身已决定它，故载荷取虚设的数字 `encℕ 0`，只为让每个码都保持带标签对的统一形状。无界量词 `∃̇` 与 `∀̇` 是一元的，其码是标签 `6` 或 `7` 直接配上子公式的码。
<!--ja-->
含意は他の結合子と同様にタグ `4` を取ります。偽 `⊥̇` は部分を一切持たない唯一の構成子で、タグ `5` だけで決まるため、ペイロードは仮の数 `encℕ 0` です。これは、すべての符号をタグ付き対という統一した形に保つために置かれています。無界量化子 `∃̇` と `∀̇` は単項で、その符号はタグ `6` または `7` に部分論理式の符号を直接対にしたものです。
<!--/-->

```agda
⌜ φ ⇒̇ ψ ⌝   = mkTag 4  (pr ⌜ φ ⌝ ⌜ ψ ⌝)
⌜ ⊥̇ ⌝       = mkTag 5 (encℕ 0)
⌜ ∃̇ φ ⌝     = mkTag 6 ⌜ φ ⌝
⌜ ∀̇ φ ⌝     = mkTag 7 ⌜ φ ⌝
⌜ ∀̇∈ t φ ⌝  = mkTag 8 (pr ⌜ t ⌝ᵗ ⌜ φ ⌝)
```

<!--en-->
The bounded quantifiers close the list with tags `8` and `9`. Each pairs the code of its bounding term with the code of its body. The arities reflect binding: the bounding term lives in the same context `n` as the whole formula, while the body has arity `suc n`, one extra variable slot for the bound variable. With this, every formula constructor has a distinct tag, and the tag plus payload determines the formula, which the next section proves.
<!--zh-->
有界量词以标签 `8` 与 `9` 收尾。各自把界定词项的码与主体的码配成对。元数体现了约束：界定词项与整条公式处于同一语境 `n`，而主体的元数是 `suc n`，为被约束变元多出一个槽位。至此每个公式构造子都有互不相同的标签，而标签加载荷决定公式，这一点将在下一节证明。
<!--ja-->
有界量化子がタグ `8` と `9` で一覧を締めくくります。それぞれ、限定する項の符号と本体の符号を対にします。アリティが束縛を反映しています。限定する項は論理式全体と同じ文脈 `n` に住み、本体のアリティは `suc n` で、束縛される変数のために 1 つ余分なスロットを持ちます。これですべての論理式構成子が互いに異なるタグを持ち、タグとペイロードが論理式を定めることになります。それを次の節で証明します。
<!--/-->

```agda
⌜ ∃̇∈ t φ ⌝  = mkTag 9 (pr ⌜ t ⌝ᵗ ⌜ φ ⌝)
```

<!--en-->
## The coding relation

The module next records the first cases of a relational presentation of coding. `CodesT s t` relates a set to a term, and `Codes s φ` relates a set to a formula. In this file the former contains the constant case and the latter the membership case.
<!--zh-->
## 编码关系

模块接着记录编码的关系式表述的首批情形。`CodesT s t` 把集合与词项关联，`Codes s φ` 把集合与公式关联。本文件中，前者包含常元情形，后者包含隶属情形。
<!--ja-->
## 符号化関係

次に、符号化を関係として表す最初のケースを記録します。`CodesT s t` は集合と項を、`Codes s φ` は集合と論理式を関係づけます。このファイルで前者が持つのは定数の場合、後者が持つのは所属の場合です。
<!--/-->

<!--en-->
`CodesT`{.Agda} has the constructor `c-con`, which relates the code `mkTag 0 x` to the constant `con x`. The constructor `c-∈` of `Codes`{.Agda} takes derivations for the two term codes and relates their paired payload under tag `0` to the membership formula. These declarations cover exactly the cases shown here; the formula-code injectivity proof below proceeds directly from `⌜_⌝`.
<!--zh-->
`CodesT`{.Agda} 的构造子 `c-con` 把码 `mkTag 0 x` 与常元 `con x` 关联起来。`Codes`{.Agda} 的构造子 `c-∈` 接受两个词项码的推导，把标签 `0` 下由二者组成的载荷与隶属公式关联起来。这些声明只覆盖此处列出的情形；下文的公式码单射性证明直接从 `⌜_⌝` 出发。
<!--ja-->
`CodesT`{.Agda} の構成子 `c-con` は、符号 `mkTag 0 x` を定数 `con x` に関係づけます。`Codes`{.Agda} の構成子 `c-∈` は二つの項の符号についての導出を受け取り、タグ `0` のもとで対にしたペイロードを所属論理式に関係づけます。これらの宣言が扱うのは、ここに示された場合だけです。後の論理式符号の単射性は `⌜_⌝` から直接証明されます。
<!--/-->

```agda
data CodesT {n : ℕ} : S → Term S n → Type ℓ where
  c-con : (x : S)     → CodesT (mkTag 0 x) (con x)

data Codes : {n : ℕ} → S → Formula S n → Type ℓ where
  c-∈  : ∀ {n s s'} {t u : Term S n}
       → CodesT s t → CodesT s' u → Codes (mkTag 0 (pr s s')) (t ∈̇ u)
```

<!--en-->
## Codes determine formulas

Two formulas of the same arity with the same code are equal. Rather than compare every pair of the ten constructors directly, the proof separates a formula code into its numeric tag and payload. A type family indexed by the tag describes the corresponding constructor shape, and pairing injectivity supplies equalities of the tags and payloads. The proof then recurses only through the payload components.
<!--zh-->
## 码决定公式

同一元数、同一码的两条公式相等。证明不直接比较十个构造子的每一种配对，而是把公式码分成数字标签与载荷。一个由标签索引的类型族描述相应的构造子形状，配对的单射性则给出标签与载荷的相等。证明随后只沿载荷分量递归。
<!--ja-->
## 符号は論理式を一意に定める

同じアリティを持ち、同じ符号を持つ二つの論理式は等しくなります。十個の構成子のすべての組を直接比較する代わりに、証明は論理式の符号を数値タグとペイロードに分けます。タグで添字づけられた型族が対応する構成子の形を記述し、対の単射性がタグとペイロードの等しさを与えます。その後、証明はペイロードの成分に沿ってのみ再帰します。
<!--/-->

<!--en-->
The section is a proof by tag separation. Its first ingredient, `tagOf`, extracts the constructor index of a formula as a natural number, using the same numbering that `⌜_⌝` used to build codes: membership `0`, equality `1`, conjunction `2`, disjunction `3`. So `⌜_⌝` builds the tag into a set while `tagOf` reads it back out, and the section works because these two numberings agree.
<!--zh-->
本节是一个按标签分离的证明。第一个材料 `tagOf` 把公式的构造子序号作为自然数读出，编号与 `⌜_⌝` 构造码时用的完全相同：隶属 `0`，相等 `1`，合取 `2`，析取 `3`。于是 `⌜_⌝` 把标签构造进集合，`tagOf` 又把标签读出来；本节之所以成立，正是因为这两套编号彼此一致。
<!--ja-->
この節はタグの分離による証明です。最初の材料 `tagOf` は、論理式の構成子の番号を自然数として読み取ります。番号付けは `⌜_⌝` が符号を作るときに使ったものと同じで、所属 `0`、等号 `1`、論理積 `2`、論理和 `3` です。つまり `⌜_⌝` がタグを集合の中に組み込み、`tagOf` がそれを取り出します。この節が成り立つのは、2 つの番号付けが一致しているからです。
<!--/-->

```agda
tagOf : ∀ {n} → Formula S n → ℕ
tagOf (t ∈̇ u)  = 0
tagOf (t ≐ u)  = 1
tagOf (a ∧̇ b)  = 2
tagOf (a ∨̇ b)  = 3
```

<!--en-->
The remaining clauses assign `4` through `9` to implication, falsity, the two unbounded quantifiers, and the two bounded quantifiers. Every formula therefore has a tag in `0` through `9`, and no two constructors share one, which is exactly what makes the tag able to identify the constructor shape.
<!--zh-->
其余子句把 `4` 到 `9` 分配给蕴涵、「假」、两个无界量词与两个有界量词。于是每条公式的标签都在 `0` 到 `9` 之间，且没有两个构造子共享标签，这正是标签能够识别构造子形状的原因。
<!--ja-->
残りの節は、`4` から `9` までを含意、偽、2 つの無界量化子、2 つの有界量化子に割り当てます。これによりすべての論理式は `0` から `9` のタグを持ち、2 つの構成子が同じタグを共有することはありません。タグが構成子の形を特定できるのはまさにこのためです。
<!--/-->

```agda
tagOf (a ⇒̇ b)  = 4
tagOf ⊥̇        = 5
tagOf (∃̇ a)    = 6
tagOf (∀̇ a)    = 7
tagOf (∀̇∈ t a) = 8
```

<!--en-->
The second ingredient, `payOf`, extracts the payload the same way: for membership and equality it is the pair of the two term codes, and for conjunction the pair of the two subformula codes. Each clause is the payload component of the matching clause of `⌜_⌝`, so reading a code with `tagOf` and `payOf` recovers exactly the data `⌜_⌝` put in.
<!--zh-->
第二个材料 `payOf` 以同样方式抽出载荷：隶属与相等是两个词项码的对，合取是两条子公式码的对。每条子句都是 `⌜_⌝` 对应子句的载荷分量，因此用 `tagOf` 与 `payOf` 读一个码，恰好还原出 `⌜_⌝` 放进去的数据。
<!--ja-->
2 つ目の材料 `payOf` は同じ方法でペイロードを取り出します。所属と等号では 2 つの項の符号の対、論理積では 2 つの部分論理式の符号の対です。各節は `⌜_⌝` の対応する節のペイロード成分そのものなので、`tagOf` と `payOf` で符号を読めば、`⌜_⌝` が入れたデータがちょうど復元されます。
<!--/-->

```agda
tagOf (∃̇∈ t a) = 9

payOf : ∀ {n} → Formula S n → S
payOf (t ∈̇ u)  = pr ⌜ t ⌝ᵗ ⌜ u ⌝ᵗ
payOf (t ≐ u)  = pr ⌜ t ⌝ᵗ ⌜ u ⌝ᵗ
payOf (a ∧̇ b)  = pr ⌜ a ⌝ ⌜ b ⌝
```

<!--en-->
Disjunction and implication pair the two sub-codes, and the unbounded quantifiers return the single sub-code. Falsity is the case where extraction must agree with construction by convention: since `⌜ ⊥̇ ⌝` named the dummy numeral `encℕ 0` as payload, `payOf ⊥̇` names the same value rather than omitting the clause.
<!--zh-->
析取与蕴涵把两个子码配成对，无界量词返回单个子码。「假」是抽取必须按约定与构造一致的情形：由于 `⌜ ⊥̇ ⌝` 以虚设数字 `encℕ 0` 为载荷，`payOf ⊥̇` 也取同一个值，而不是省去这条子句。
<!--ja-->
論理和と含意は 2 つの部分符号を対にし、無界量化子は単一の部分符号を返します。偽は、抽出が規約によって構成と一致しなければならない場合です。`⌜ ⊥̇ ⌝` が仮の数 `encℕ 0` をペイロードとして選んだので、`payOf ⊥̇` も節を省かずに同じ値を取ります。
<!--/-->

```agda
payOf (a ∨̇ b)  = pr ⌜ a ⌝ ⌜ b ⌝
payOf (a ⇒̇ b)  = pr ⌜ a ⌝ ⌜ b ⌝
payOf ⊥̇        = encℕ 0
payOf (∃̇ a)    = ⌜ a ⌝
payOf (∀̇ a)    = ⌜ a ⌝
```

<!--en-->
The bounded quantifiers complete `payOf`, each pairing the code of its bounding term with the code of its body. Then `shape` records the bridge between the two directions: for every formula `φ`, the code `⌜ φ ⌝` equals `mkTag (tagOf φ) (payOf φ)`. Since `tagOf` and `payOf` were transcribed from the clauses of `⌜_⌝`, matching on `φ` reduces both sides to the same tagged pair, and each case holds by `refl`.
<!--zh-->
有界量词补完 `payOf`，各自把界定词项的码与主体的码配成对。接着 `shape` 记录两个方向之间的桥梁：对每条公式 `φ`，码 `⌜ φ ⌝` 等于 `mkTag (tagOf φ) (payOf φ)`。由于 `tagOf` 与 `payOf` 是从 `⌜_⌝` 的子句转录而来，对 `φ` 作匹配便把两边归约为同一个带标签对，各情形都由 `refl` 成立。
<!--ja-->
有界量化子が `payOf` を完成させます。それぞれ、限定する項の符号と本体の符号を対にします。続く `shape` は 2 つの方向の間の橋を記録します。すべての論理式 `φ` に対し、符号 `⌜ φ ⌝` は `mkTag (tagOf φ) (payOf φ)` に等しい、というものです。`tagOf` と `payOf` は `⌜_⌝` の節から書き写したものなので、`φ` でマッチングすると両辺が同じタグ付き対に簡約され、各場合は `refl` で成立します。
<!--/-->

```agda
payOf (∀̇∈ t a) = pr ⌜ t ⌝ᵗ ⌜ a ⌝
payOf (∃̇∈ t a) = pr ⌜ t ⌝ᵗ ⌜ a ⌝

shape : ∀ {n} (φ : Formula S n) → ⌜ φ ⌝ ≡ mkTag (tagOf φ) (payOf φ)
shape (t ∈̇ u)  = refl
shape (t ≐ u)  = refl
```

<!--en-->
The clauses shown here carry the same justification for disjunction, implication, falsity and the unbounded existential: in every case the equation is definitional, because `⌜_⌝`, `tagOf` and `payOf` were built from the same recursion on the formula. The next block finishes the remaining constructors and then turns to the converse direction.
<!--zh-->
这里展示的子句为析取、蕴涵、「假」与无界存在量词给出同样的论证：每种情形的等式都是定义性的，因为 `⌜_⌝`、`tagOf` 与 `payOf` 出自对公式的同一套递归。下一块完成其余构造子，然后转向反方向。
<!--ja-->
ここに示した節は、論理和、含意、偽、無界存在量化子に対して同じ根拠を与えます。いずれの場合も等式は定義的です。`⌜_⌝`、`tagOf`、`payOf` が論理式に対する同じ再帰から作られているからです。次のブロックが残りの構成子を完成させ、その後で逆方向に進みます。
<!--/-->

```agda
shape (a ∧̇ b)  = refl
shape (a ∨̇ b)  = refl
shape (a ⇒̇ b)  = refl
shape ⊥̇        = refl
shape (∃̇ a)    = refl
```

<!--en-->
The last `shape` clauses close the bounded cases, and the construction now turns around: given a tag, describe what a formula with that tag looks like. The type family `Match` does this. For tag `k`, `Match k φ` is the type of ways `φ` can arise from a constructor of index `k`: one dependent-pair layer per subformula slot, ending in a path `φ ≡` the constructor applied to those slots. For tags `0` and `1` the slots are two terms, closing with the constructors `_∈̇_` and `_≐_`.
<!--zh-->
最后几条 `shape` 子句了结有界情形，构造到此转了一个方向：给定标签，描述带该标签的公式长什么样。类型族 `Match` 承担这个任务。对标签 `k`，`Match k φ` 是「`φ` 能由序号为 `k` 的构造子产生」的方式所成的类型：每个子公式槽位一层依值序对，末端是一条路径 `φ ≡` 加上构造子作用于这些槽位的结果。对标签 `0` 与 `1`，槽位是两个词项，分别以构造子 `_∈̇_` 与 `_≐_` 收尾。
<!--ja-->
最後の `shape` の節が有界の場合を閉じ、構成はここで逆向きに転じます。タグが与えられたとき、そのタグを持つ論理式がどのような形かを記述します。これを担うのが型族 `Match` です。タグ `k` に対し `Match k φ` は、`φ` が番号 `k` の構成子から生じる仕方の型です。部分論理式のスロットごとに従属対の 1 段があり、最後はそれらのスロットに構成子を適用した結果への道 `φ ≡` で終わります。タグ `0` と `1` ではスロットは 2 つの項で、構成子 `_∈̇_` と `_≐_` で閉じます。
<!--/-->

```agda
shape (∀̇ a)    = refl
shape (∀̇∈ t a) = refl
shape (∃̇∈ t a) = refl

Match : ∀ {n} → ℕ → Formula S n → Type ℓ
Match {n} 0  φ = Σ[ t ∈ Term S n ] (Σ[ u ∈ Term S n ] (φ ≡ (t ∈̇ u)))
```

<!--en-->
Tags `2` through `4` repeat the pattern for the three binary connectives, each demanding two formulas of the same arity `n`. Tag `5` is the degenerate case: falsity has no slots, so `Match 5 φ` is just the single path `φ ≡ ⊥̇`, with no pair at all. This shows how the family adapts to the constructor's shape rather than imposing a uniform arity.
<!--zh-->
标签 `2` 到 `4` 为三个二元联结词重复同一模式，各自要求两条元数同为 `n` 的公式。标签 `5` 是退化情形：「假」没有槽位，故 `Match 5 φ` 就是单条路径 `φ ≡ ⊥̇`，根本没有序对。这表明该族随构造子形状而变化，并不强加统一的元数。
<!--ja-->
タグ `2` から `4` は 3 つの 2 項結合子に対して同じパターンを繰り返し、それぞれアリティが同じ `n` の論理式を 2 つ要求します。タグ `5` は退化した場合です。偽にはスロットがないので、`Match 5 φ` は対をまったく持たず、単一の道 `φ ≡ ⊥̇` そのものです。この族が構成子の形に応じて変化し、統一したアリティを強制しないことが分かります。
<!--/-->

```agda
Match {n} 1  φ = Σ[ t ∈ Term S n ] (Σ[ u ∈ Term S n ] (φ ≡ (t ≐ u)))
Match {n} 2  φ = Σ[ a ∈ Formula S n ] (Σ[ b ∈ Formula S n ] (φ ≡ (a ∧̇ b)))
Match {n} 3  φ = Σ[ a ∈ Formula S n ] (Σ[ b ∈ Formula S n ] (φ ≡ (a ∨̇ b)))
Match {n} 4  φ = Σ[ a ∈ Formula S n ] (Σ[ b ∈ Formula S n ] (φ ≡ (a ⇒̇ b)))
Match     5 φ = φ ≡ ⊥̇
```

<!--en-->
The quantifier tags carry the arity shift. For tags `6` and `7` the single slot is a formula of arity `suc n`; for tags `8` and `9` a term of arity `n` and a body of arity `suc n` fill the two slots, matching the constructors `∀̇∈` and `∃̇∈`. Any other tag has no formulas to describe, so the family closes with the empty type `Empty.⊥*`; `Match` is thereby defined for every natural-number tag.
<!--zh-->
量词标签带有元数变化。标签 `6` 与 `7` 的唯一槽位是元数 `suc n` 的公式；标签 `8` 与 `9` 的两个槽位分别是元数 `n` 的词项与元数 `suc n` 的主体，对应构造子 `∀̇∈` 与 `∃̇∈`。其余标签没有任何公式可描述，故该族以空类型 `Empty.⊥*` 收尾；由此 `Match` 对每个自然数标签都有定义。
<!--ja-->
量化子のタグにはアリティの変化が現れます。タグ `6` と `7` の唯一のスロットはアリティ `suc n` の論理式であり、タグ `8` と `9` ではアリティ `n` の項とアリティ `suc n` の本体が 2 つのスロットを埋め、構成子 `∀̇∈` と `∃̇∈` に対応します。その他のタグに対応する論理式はないので、族は空型 `Empty.⊥*` で閉じられます。これにより `Match` はすべての自然数のタグに対して定義されます。
<!--/-->

```agda
Match {n} 6 φ = Σ[ a ∈ Formula S (suc n) ] (φ ≡ (∃̇ a))
Match {n} 7 φ = Σ[ a ∈ Formula S (suc n) ] (φ ≡ (∀̇ a))
Match {n} 8 φ = Σ[ t ∈ Term S n ] (Σ[ a ∈ Formula S (suc n) ] (φ ≡ ∀̇∈ t a))
Match {n} 9 φ = Σ[ t ∈ Term S n ] (Σ[ a ∈ Formula S (suc n) ] (φ ≡ ∃̇∈ t a))
Match     _  _ = Empty.⊥*
```

<!--en-->
The direction that computes witnesses is easy: `matches φ` builds an inhabitant of `Match (tagOf φ) φ` by recursion on `φ`. A binary formula `a ∧̇ b` supplies the two slots `a` and `b`, and the final path is `refl` because `a ∧̇ b` reassembles from its parts definitionally. For example, the witness for `t ∈̇ u` is the triple `t , (u , refl)`.
<!--zh-->
计算见证的方向是容易的：`matches φ` 通过对 `φ` 的递归构造 `Match (tagOf φ) φ` 的一个元素。二元公式 `a ∧̇ b` 提供两个槽位 `a` 与 `b`，末端的路径是 `refl`，因为 `a ∧̇ b` 按定义等式由其部分重新组装。例如，`t ∈̇ u` 的见证就是三元组 `t , (u , refl)`。
<!--ja-->
証拠を計算する方向は容易です。`matches φ` は `φ` に対する再帰で `Match (tagOf φ) φ` の元を構成します。2 項の論理式 `a ∧̇ b` は 2 つのスロットに `a` と `b` を供給し、最後の道は `refl` です。`a ∧̇ b` がその部分から定義的に組み上がるからです。たとえば `t ∈̇ u` の証拠は三つ組 `t , (u , refl)` です。
<!--/-->

```agda

matches : ∀ {n} (φ : Formula S n) → Match (tagOf φ) φ
matches (t ∈̇ u)  = t , (u , refl)
matches (t ≐ u)  = t , (u , refl)
matches (a ∧̇ b)  = a , (b , refl)
matches (a ∨̇ b)  = a , (b , refl)
```

<!--en-->
The remaining constructors follow the shape of their `Match` rows: falsity contributes just `refl`, each unbounded quantifier pairs its body with `refl`, and each bounded quantifier supplies its bounding term and body. Once the last constructor is covered, `matches` shows that every formula matches its own tag, so the tag alone narrows any formula down to one constructor shape.
<!--zh-->
其余构造子按各自 `Match` 行的形状处理：「假」只贡献 `refl`，每个无界量词把主体与 `refl` 配成对，每个有界量词给出界定词项与主体。覆盖最后一个构造子之后，`matches` 表明每条公式都与自己的标签匹配，于是仅凭标签就能把任何公式缩小到一种构造子形状。
<!--ja-->
残りの構成子は、それぞれの `Match` の行の形に従います。偽は `refl` だけを供給し、各無界量化子は本体と `refl` を対にし、各有界量化子は限定する項と本体を供給します。最後の構成子まで覆うと、`matches` はすべての論理式が自分のタグに適合することを示します。したがってタグだけで、どの論理式も 1 つの構成子の形にまで絞り込めます。
<!--/-->

```agda
matches (a ⇒̇ b)  = a , (b , refl)
matches ⊥̇        = refl
matches (∃̇ a)    = a , refl
matches (∀̇ a)    = a , refl
matches (∀̇∈ t a) = t , (a , refl)
```

<!--en-->
The theorem `⌜⌝-inj` is now within reach: for formulas `φ` and `ψ` of the same arity, an equality `⌜ φ ⌝ ≡ ⌜ ψ ⌝` should force `φ ≡ ψ`. The proof reduces to a helper `go`, stated inside a `private` block so only the theorem is exported. What `go` assumes is exactly what tag separation provides: `ψ` re-presented as a match of `φ`'s tag, and an equality of the payloads `payOf φ ≡ payOf ψ`. From these it must return `φ ≡ ψ`.
<!--zh-->
定理 `⌜⌝-inj` 已近在眼前：对元数相同的公式 `φ` 与 `ψ`，等式 `⌜ φ ⌝ ≡ ⌜ ψ ⌝` 应当强制 `φ ≡ ψ`。证明归约为辅助函数 `go`，它在 `private` 块内给出，使导出的只有定理本身。`go` 的假设恰是标签分离所提供的东西：把 `ψ` 重新呈现为 `φ` 之标签的一次匹配，以及载荷相等 `payOf φ ≡ payOf ψ`。由这些它必须返回 `φ ≡ ψ`。
<!--ja-->
定理 `⌜⌝-inj` はもう目の前です。同じアリティの論理式 `φ` と `ψ` に対し、等式 `⌜ φ ⌝ ≡ ⌜ ψ ⌝` は `φ ≡ ψ` を強制するはずです。証明は補助関数 `go` に帰着し、`go` は `private` ブロックの中で宣言されるため、書き出されるのは定理そのものだけです。`go` が仮定するのは、タグの分離がまさに与えるものです。すなわち `φ` のタグに対する適合として再提示された `ψ` と、ペイロードの等式 `payOf φ ≡ payOf ψ` です。これらから `φ ≡ ψ` を返さなければなりません。
<!--/-->

```agda
matches (∃̇∈ t a) = t , (a , refl)

⌜⌝-inj : ∀ {n} (φ ψ : Formula S n) → ⌜ φ ⌝ ≡ ⌜ ψ ⌝ → φ ≡ ψ

private
  go : ∀ {n} (φ ψ : Formula S n) → Match (tagOf φ) ψ → payOf φ ≡ payOf ψ → φ ≡ ψ
  go (t ∈̇ u) ψ (t' , (u' , q)) p =
```

<!--en-->
The membership clause shows the whole mechanics, so it deserves a slow reading. The match presents `ψ` as `t' ∈̇ u'` up to a path `q : ψ ≡ (t' ∈̇ u')`, but the hypothesis `p` only equates the payloads of `φ` and of `ψ`, not of `t' ∈̇ u'`. Composing `p` with `cong payOf q` transports the equation along `q`, producing `pr ⌜ t ⌝ᵗ ⌜ u ⌝ᵗ ≡ pr ⌜ t' ⌝ᵗ ⌜ u' ⌝ᵗ`, which `pr-inj` splits into equations of the term codes. Each goes through the already-proven `⌜⌝ᵗ-inj`, `cong₂ _∈̇_` rebuilds the constructor on both sides, and `sym q` retargets the right-hand side from `t' ∈̇ u'` to `ψ`. The equality clause repeats this word for word with `_≐_`.
<!--zh-->
隶属子句展示了全部机制，值得细读。匹配把 `ψ` 呈现为差一条路径 `q : ψ ≡ (t' ∈̇ u')` 的 `t' ∈̇ u'`，而假设 `p` 只给出 `φ` 与 `ψ` 的载荷相等，并非 `t' ∈̇ u'` 的载荷。把 `p` 与 `cong payOf q` 复合，等式便沿 `q` 转移，得到 `pr ⌜ t ⌝ᵗ ⌜ u ⌝ᵗ ≡ pr ⌜ t' ⌝ᵗ ⌜ u' ⌝ᵗ`，`pr-inj` 再把它拆成词项码的等式。每条等式经已证的 `⌜⌝ᵗ-inj` 处理，`cong₂ _∈̇_` 在两侧重新装上构造子，末尾的 `sym q` 把右端从 `t' ∈̇ u'` 换回 `ψ`。相等子句把这一切换成 `_≐_` 逐字重演。
<!--ja-->
所属の節に仕組みの全体が表れているので、ゆっくり読む価値があります。適合は `ψ` を道 `q : ψ ≡ (t' ∈̇ u')` のもとで `t' ∈̇ u'` として提示しますが、仮定 `p` が等しいと言うのは `φ` と `ψ` のペイロードであって、`t' ∈̇ u'` のペイロードではありません。`p` に `cong payOf q` を合成すると、等式が `q` に沿って輸送され、`pr ⌜ t ⌝ᵗ ⌜ u ⌝ᵗ ≡ pr ⌜ t' ⌝ᵗ ⌜ u' ⌝ᵗ` が得られます。`pr-inj` がこれを項の符号の等式に分解し、それぞれはすでに証明済みの `⌜⌝ᵗ-inj` を通ります。`cong₂ _∈̇_` が両辺に構成子を組み立て直し、最後の `sym q` が右辺を `t' ∈̇ u'` から `ψ` へ向け直します。等号の節はこれを `_≐_` に替えてそのまま繰り返します。
<!--/-->

```agda
    cong₂ _∈̇_ (⌜⌝ᵗ-inj t t' (pr-inj (p ∙ cong payOf q) .fst))
              (⌜⌝ᵗ-inj u u' (pr-inj (p ∙ cong payOf q) .snd)) ∙ sym q
  go (t ≐ u) ψ (t' , (u' , q)) p =
    cong₂ _≐_ (⌜⌝ᵗ-inj t t' (pr-inj (p ∙ cong payOf q) .fst))
              (⌜⌝ᵗ-inj u u' (pr-inj (p ∙ cong payOf q) .snd)) ∙ sym q
```

<!--en-->
Every binary connective is handled by this one pattern, so the conjunction clause is worth stating as the general recipe. The match is a triple `a' , (b' , q)` with `q : ψ ≡ (a' ∧̇ b')`. The transported payload equation has the shape `pr _ _ ≡ pr _ _`, so `pr-inj` yields equations of the two sub-codes, `⌜⌝-inj` lifts each recursively to an equality of subformulas, `cong₂ _∧̇_` rebuilds `a ∧̇ b ≡ a' ∧̇ b'`, and `sym q` points the right side at `ψ`. This recipe is the whole content of the remaining connective clauses.
<!--zh-->
每个二元联结词都由这一个模式处理，因此把合取子句当作通用配方来陈述是值得的。匹配是三元组 `a' , (b' , q)`，其中 `q : ψ ≡ (a' ∧̇ b')`。转移后的载荷等式形如 `pr _ _ ≡ pr _ _`，`pr-inj` 给出两个子码的等式，`⌜⌝-inj` 递归地把它们提升为子公式的等式，`cong₂ _∧̇_` 重组出 `a ∧̇ b ≡ a' ∧̇ b'`，`sym q` 把右侧指向 `ψ`。这条配方就是其余联结词子句的全部内容。
<!--ja-->
すべての 2 項結合子はこの 1 つのパターンで処理されるので、論理積の節を汎用の処方として述べる価値があります。適合は三つ組 `a' , (b' , q)` で、`q : ψ ≡ (a' ∧̇ b')` が成り立ちます。輸送されたペイロードの等式は `pr _ _ ≡ pr _ _` の形をしているので、`pr-inj` が 2 つの部分符号の等式を与え、`⌜⌝-inj` が再帰的にそれらを部分論理式の等式へ引き上げ、`cong₂ _∧̇_` が `a ∧̇ b ≡ a' ∧̇ b'` を組み立て直し、`sym q` が右辺を `ψ` に向けます。この処方こそが、残りの結合子の節の内容のすべてです。
<!--/-->

```agda
  go (a ∧̇ b) ψ (a' , (b' , q)) p =
    cong₂ _∧̇_ (⌜⌝-inj a a' (pr-inj (p ∙ cong payOf q) .fst))
              (⌜⌝-inj b b' (pr-inj (p ∙ cong payOf q) .snd)) ∙ sym q
  go (a ∨̇ b) ψ (a' , (b' , q)) p =
    cong₂ _∨̇_ (⌜⌝-inj a a' (pr-inj (p ∙ cong payOf q) .fst))
```

<!--en-->
The disjunction and implication clauses instantiate the recipe with their own constructors, changing nothing else. Falsity is the only case with no payload work at all: the match is just `q : ψ ≡ ⊥̇`, so `sym q : ⊥̇ ≡ ψ` is already the required equation, and the payload hypothesis `p` goes unused.
<!--zh-->
析取与蕴涵子句只是用各自的构造子实例化这条配方，其余不变。「假」是唯一完全不需要载荷操作的情形：匹配就是 `q : ψ ≡ ⊥̇`，于是 `sym q : ⊥̇ ≡ ψ` 已是所需的等式，载荷假设 `p` 未被使用。
<!--ja-->
論理和と含意の節は、それぞれの構成子でこの処方を具体化するだけで、他は何も変わりません。偽はペイロードの操作がまったく不要な唯一の場合です。適合は `q : ψ ≡ ⊥̇` だけなので、`sym q : ⊥̇ ≡ ψ` がすでに求める等式であり、ペイロードの仮定 `p` は使われません。
<!--/-->

```agda
              (⌜⌝-inj b b' (pr-inj (p ∙ cong payOf q) .snd)) ∙ sym q
  go (a ⇒̇ b) ψ (a' , (b' , q)) p =
    cong₂ _⇒̇_ (⌜⌝-inj a a' (pr-inj (p ∙ cong payOf q) .fst))
              (⌜⌝-inj b b' (pr-inj (p ∙ cong payOf q) .snd)) ∙ sym q
  go ⊥̇ ψ q p = sym q
```

<!--en-->
The unbounded quantifiers simplify the recipe: the payload is a single sub-code, so the transported equation is directly `⌜ a ⌝ ≡ ⌜ a' ⌝`, and one recursive call wrapped in `cong ∃̇_` or `cong ∀̇_`, closed with `sym q`, suffices. The bounded quantifier `∀̇∈` is where the two levels of coding meet in one constructor: after the `pr-inj` split, the term component is resolved by `⌜⌝ᵗ-inj` and the formula component by the recursive `⌜⌝-inj`, and `cong₂ ∀̇∈` reassembles both, with `sym q` finishing as always.
<!--zh-->
无界量词让配方更简单：载荷是单个子码，转移后的等式直接就是 `⌜ a ⌝ ≡ ⌜ a' ⌝`，一次递归调用包上 `cong ∃̇_` 或 `cong ∀̇_`，再以 `sym q` 收尾即可。有界量词 `∀̇∈` 则是两层编码在一个构造子中相遇之处：经 `pr-inj` 拆分后，项分量由 `⌜⌝ᵗ-inj` 解决，公式分量由递归的 `⌜⌝-inj` 解决，`cong₂ ∀̇∈` 把两者重组，最后照例以 `sym q` 收束。
<!--ja-->
無界量化子では処方が単純になります。ペイロードは単一の部分符号なので、輸送された等式は直接 `⌜ a ⌝ ≡ ⌜ a' ⌝` であり、`cong ∃̇_` か `cong ∀̇_` で包んだ再帰呼び出し 1 回と、最後の `sym q` で足ります。有界量化子 `∀̇∈` は、2 つのレベルの符号化が 1 つの構成子の中で出会う場所です。`pr-inj` で分解した後、項の成分は `⌜⌝ᵗ-inj` が、論理式の成分は再帰的な `⌜⌝-inj` が解決し、`cong₂ ∀̇∈` が両者を組み立て直し、最後はいつものように `sym q` で締めます。
<!--/-->

```agda
  go (∃̇ a) ψ (a' , q) p = cong ∃̇_ (⌜⌝-inj a a' (p ∙ cong payOf q)) ∙ sym q
  go (∀̇ a) ψ (a' , q) p = cong ∀̇_ (⌜⌝-inj a a' (p ∙ cong payOf q)) ∙ sym q
  go (∀̇∈ t a) ψ (t' , (a' , q)) p =
    cong₂ ∀̇∈ (⌜⌝ᵗ-inj t t' (pr-inj (p ∙ cong payOf q) .fst))
             (⌜⌝-inj a a' (pr-inj (p ∙ cong payOf q) .snd)) ∙ sym q
```

<!--en-->
The bounded existential mirrors the bounded universal, completing the ten cases. The top level then assembles the theorem. Given `e : ⌜ φ ⌝ ≡ ⌜ ψ ⌝`, `go` needs a match of `ψ` against the tag of `φ`, but `matches ψ` lives at the tag of `ψ`. These may differ as numbers, so the match is transported: `tp .fst` is a path `tagOf φ ≡ tagOf ψ`, and `subst` along its symmetry re-indexes `matches ψ` to the type `Match (tagOf φ) ψ`, which is exactly what `go` expects.
<!--zh-->
有界存在量词与有界全称平行，十个情形到此齐备。顶层随后组装定理。给定 `e : ⌜ φ ⌝ ≡ ⌜ ψ ⌝`，`go` 需要一个以 `φ` 之标签索引的 `ψ` 的匹配，而 `matches ψ` 位于 `ψ` 的标签处。作为数二者可能不同，因此匹配要被转移：`tp .fst` 是一条路径 `tagOf φ ≡ tagOf ψ`，沿其对称作 `subst` 便把 `matches ψ` 重定索引到类型 `Match (tagOf φ) ψ`，这正是 `go` 所期望的。
<!--ja-->
有界存在量化子は有界全称量化子と対応しており、これで 10 の場合がそろいます。そのうえで大域的な定理が組み立てられます。`e : ⌜ φ ⌝ ≡ ⌜ ψ ⌝` が与えられると、`go` には `φ` のタグで添字づけられた `ψ` の適合が必要ですが、`matches ψ` は `ψ` のタグのところに住んでいます。数として両者は異なり得るので、適合を輸送します。`tp .fst` は道 `tagOf φ ≡ tagOf ψ` であり、その対称に沿って `subst` すると `matches ψ` は型 `Match (tagOf φ) ψ` に添字づけ直され、これは `go` が期待するものとちょうど一致します。
<!--/-->

```agda
  go (∃̇∈ t a) ψ (t' , (a' , q)) p =
    cong₂ ∃̇∈ (⌜⌝ᵗ-inj t t' (pr-inj (p ∙ cong payOf q) .fst))
             (⌜⌝-inj a a' (pr-inj (p ∙ cong payOf q) .snd)) ∙ sym q

⌜⌝-inj φ ψ e = go φ ψ
  (subst (λ k → Match k ψ) (sym (tp .fst)) (matches ψ)) (tp .snd)
```

<!--en-->
The local definition `tp` produces the pair of equations this transport needs. Chaining `sym (shape φ)`, the hypothesis `e`, and `shape ψ` rewrites the assumed equality of codes into an equality `mkTag (tagOf φ) (payOf φ) ≡ mkTag (tagOf ψ) (payOf ψ)` of tagged pairs, and `mkTag-inj` splits it into the tag equation and the payload equation. The tag equation drives the `subst`, the payload equation is `go`'s second argument, and the theorem is complete: no ten-by-ten comparison of constructors, only the tag arithmetic plus recursion on payloads.
<!--zh-->
局部定义 `tp` 造出这一转移所需的一对等式。把 `sym (shape φ)`、假设 `e` 与 `shape ψ` 串起来，码的相等被改写为带标签对之间的等式 `mkTag (tagOf φ) (payOf φ) ≡ mkTag (tagOf ψ) (payOf ψ)`，`mkTag-inj` 再把它拆成标签等式与载荷等式。标签等式驱动 `subst`，载荷等式成为 `go` 的第二个参数，定理就此完成：无需十乘十地比较构造子，只需标签的算术加上沿载荷的递归。
<!--ja-->
局所定義 `tp` が、この輸送に必要な一対の等式を作ります。`sym (shape φ)`、仮定 `e`、`shape ψ` をつなげると、仮定された符号の等式はタグ付き対の間の等式 `mkTag (tagOf φ) (payOf φ) ≡ mkTag (tagOf ψ) (payOf ψ)` に書き換わり、`mkTag-inj` がそれをタグの等式とペイロードの等式に分解します。タグの等式が `subst` を駆動し、ペイロードの等式が `go` の第 2 引数になります。定理はこれで完成です。構成子を十乗十で比較する必要はなく、必要なのはタグの計算とペイロードに沿う再帰だけです。
<!--/-->

```agda
  where
  tp = mkTag-inj (sym (shape φ) ∙ e ∙ shape ψ)
```

<!--en-->
## Recap

Terms and formulas now have codes in `S`: `⌜_⌝`{.Agda} attaches a constructor tag to the codes of the parts, while constants carry their underlying set as payload. The file records the constant and membership cases of relational coding, then proves that one code determines at most one formula of a fixed arity. The construction is generic in an injective pairing and an injection of the naturals.
<!--zh-->
## 小结

词项与公式如今都有 `S` 中的码：`⌜_⌝`{.Agda} 把构造子标签附到各部分的码上，常元则以其底层集合作为载荷。本文件记录关系式编码的常元情形与隶属情形，随后证明在固定元数下一个码至多决定一条公式。整个构造只以单射配对和自然数的单射为参数。
<!--ja-->
## まとめ

項と論理式には `S` の元としての符号が与えられます。`⌜_⌝`{.Agda} は各部分の符号に構成子のタグを付け、定数はその台となる集合をペイロードにします。このファイルは関係による符号化のうち定数と所属の場合を記録し、続いて固定したアリティでは一つの符号が高々一つの論理式を定めることを証明します。この構成は単射な対の演算と自然数の単射をパラメータとします。
<!--/-->
