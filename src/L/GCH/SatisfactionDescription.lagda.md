<!--en-->
# A Δ₀ description of the satisfaction table

The external semantic recursion has already produced the uniform satisfaction table. The question is now how a formula interpreted in `L` can recognize a candidate set as that same graph. We will package the environment tower, formula code domain, the table's two domain conditions, and its ten recursive constructor clauses into a bounded description that later formulas can quantify over.
<!--zh-->
# 满足关系表的 Δ₀ 描述

外部语义递归已经构造出统一满足关系表。现在的问题是，在 `L` 中解释的公式如何把一个候选集合识别为同一张图。我们将把环境塔、公式码域、表的两条定义域条件与十条递归构造子子句封装成一条有界描述，供后续公式量化。
<!--ja-->
# 充足関係表の Δ₀ 記述

外部の意味論的再帰は、すでに一様な充足関係表を構成しています。ここでの問いは、`L` で解釈される論理式が、候補の集合をその同じグラフとしてどのように認識できるかです。環境の塔、論理式の符号領域、表の二つの領域条件、および十個の再帰的な構成子の節を、後の論理式が量化できる一つの有界な記述にまとめます。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

```

<!--en-->
The construction remains relative to excluded middle at level `ℓ-suc ℓ`. This hypothesis supports the coding and satisfaction machinery used below; it is carried explicitly rather than turned into an additional property of the candidate table.
<!--zh-->
这一构造仍以层级 `ℓ-suc ℓ` 上的排中律为条件。该假设支撑下文使用的编码与满足关系构造，但不会变成候选表的一项额外性质，而是始终显式携带。
<!--ja-->
この構成は引き続き、レベル `ℓ-suc ℓ` における排中律を仮定します。この仮定は以下の符号化と充足関係の構成を支えますが、候補の表に新たな性質を付け加えるものではなく、明示的な仮定として保たれます。
<!--/-->

```agda
open import Base.Prelude
open import Base.Classical using ( LEM )

```

<!--en-->
Fix a universe level `ℓ` and this single classical hypothesis. Every object used in the description, from constructible sets to encoded formula keys, lives at the corresponding level, so no stronger classical assumption enters the result.
<!--zh-->
固定宇宙层级 `ℓ` 与这一条经典假设。描述中使用的每个对象，从可构造集合到编码后的公式键，都处在相应层级，因此结论不引入更强的经典假设。
<!--ja-->
宇宙レベル `ℓ` と、この一つの古典的仮定を固定します。構成可能集合から符号化された論理式の鍵まで、記述に使う対象はすべて対応するレベルにあり、結論にこれより強い古典的仮定は入りません。
<!--/-->

```agda
module L.GCH.SatisfactionDescription {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

```

<!--en-->
The final description is built by conjoining three formulas. Its syntactic goal is a `Δ₀` certificate: every quantifier in the description remains bounded. This boundedness is the precise condition that later allows satisfaction in `L` to be compared with satisfaction in the ambient hierarchy.
<!--zh-->
最终描述由三个公式合取而成。其句法目标是一个 `Δ₀` 证书，也就是描述中的每个量词都保持有界。正是这一有界性，使后文能够比较 `L` 内部与外围层级中的满足关系。
<!--ja-->
最終的な記述は三つの論理式の連言として作られます。統語上の目標は `Δ₀` の証拠、すなわち記述中のすべての量化子が有界であることです。この有界性によって、後で `L` の内部の充足関係と周囲の階層における充足関係を比較できます。
<!--/-->

```agda
open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using
  ( Formula; _∧̇_ )
open import FOL.LevyHierarchy using ( Δ₀; δ-∧ )
import FOL.Absoluteness
```

<!--en-->
Three kinds of encoded data must agree. Formula keys belong to the canonical set `AllCodes W`; an arity `k` points to the environment set `envSet W k`; and ordered pairs package keys with their semantic values. Membership in `AllCodes W` reveals a formula key only under propositional truncation, a boundary that every later decoding step preserves.
<!--zh-->
三类编码数据必须彼此一致。公式键属于典范集合 `AllCodes W`；元数 `k` 指向环境集 `envSet W k`；有序对则把键与其语义值包装在一起。`AllCodes W` 的成员只能在命题截断下显露为某个公式键，后面的每一步解码都保留这一边界。
<!--ja-->
三種類の符号化データが互いに整合しなければなりません。論理式の鍵は正準集合 `AllCodes W` に属し、アリティ `k` は環境集合 `envSet W k` を指し、順序対は鍵とその意味論的な値をまとめます。`AllCodes W` の要素が論理式の鍵であることは命題的切り詰めのもとでしか得られず、後の復号もこの境界を保ちます。
<!--/-->

```agda
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Coding {ℓ} using ( pr; pr-inj )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans )
open import L.Coding.EnvironmentSet {ℓ} lem using ( envSet )
open import L.Coding.CodeSet {ℓ} lem using ( AllCodes; AllCodes-out; key∈AllCodes; keyS )
```

<!--en-->
For each genuine formula key, the semantic recursion produces a satisfaction set `SatW ψ`, while the functional table records the corresponding value. The bounded description does not rerun that recursion internally. It lists ten local constructor clauses, and a structural argument shows that any candidate obeying them is pinned to the externally defined value at every genuine key.
<!--zh-->
对每个真实公式键，语义递归产生满足集 `SatW ψ`，函数表则记录相应取值。有界描述并不在内部重新运行这项递归，而是列出十条局部构造子子句，再用结构论证表明：任何满足这些子句的候选表，在每个真实键处都被钉扎到外部定义的取值。
<!--ja-->
各々の実際の論理式の鍵について、意味論的再帰は充足集合 `SatW ψ` を作り、関数的な表は対応する値を記録します。有界な記述は、その再帰を内部でもう一度実行するのではありません。十個の局所的な構成子の節を並べ、構造的な議論によって、それらに従う候補の表が各々の実際の鍵で外部に定義された値へ固定されることを示します。
<!--/-->

```agda
open import L.Coding.UniformSatisfaction {ℓ} lem using ( module Table; val-at )
open import L.Coding.PinnedRecursion {ℓ} lem using ( module Match ) public
open import L.Coding.PinnedRecursion {ℓ} lem using ( module SatSoundC; module SatHoldsC )
open import L.Coding.Quantification {ℓ} using ( f0; down )
open import L.Coding.CodeAlphabet {ℓ} using ( module Alphabet )
```

<!--en-->
The constructor clauses can be read only after their domain is controlled. The candidate code domain must contain all genuine formula keys and admit only such keys, while the environment tower relates each natural-number arity to the environments of that length. These two descriptions supply the induction with exactly the subformula keys and environments it needs.
<!--zh-->
只有先控制定义域，才能读取构造子子句。候选码域必须包含全部真实公式键，并且只容纳这样的键；环境塔则把每个自然数元数与该长度的环境联系起来。这两项描述恰好为归纳提供所需的子公式键与环境。
<!--ja-->
構成子の節を読むには、まずその定義域を制御する必要があります。候補のコード領域は、実際の論理式の鍵をすべて含み、しかもそのような鍵だけを許さなければなりません。環境の塔は各自然数アリティを、その長さの環境と結び付けます。この二つの記述が、帰納に必要な部分論理式の鍵と環境をちょうど供給します。
<!--/-->

```agda
open import L.Coding.CodeDomain {ℓ} using ( Tags; codesAt; Δ₀-codesAt )
open import L.Coding.CodeDomainAdequacy {ℓ} lem
  using ( module CodesSound; module CodesComplete; module CodesHolds )
open import L.Coding.EnvironmentTower {ℓ} lem
  using ( towerAt; Δ₀-towerAt; module Tower; module TowerRead; module TowerHolds )
```

<!--en-->
The remaining object is the graph of the uniform table. Its entries are encoded pairs of a formula key and a satisfaction set. The ten bounded clauses describe how the second component depends on the constructor encoded by the first, and the real graph will provide the completeness witness for those clauses.
<!--zh-->
剩下的对象是统一满足关系表的图。它的条目是由公式键与满足集组成的编码对。十条有界子句描述第二分量如何依赖第一分量所编码的构造子，而真实图将为这些子句提供完备性见证。
<!--ja-->
残る対象は、一様な充足関係表のグラフです。その項目は、論理式の鍵と充足集合からなる符号化された対です。十個の有界な節は、第二成分が第一成分に符号化された構成子からどのように決まるかを記述し、実際のグラフがそれらの節の完全性の証人になります。
<!--/-->

```agda
open import L.Coding.SatisfactionClauses {ℓ} using ( tableAt; Δ₀-tableAt )
open import L.Coding.SatisfactionClauseSemantics {ℓ} lem using ( module Frame; module Bridge )
open import L.Coding.SatisfactionGraphSet {ℓ} lem using ( module SatGraph )

```

<!--en-->
An interpreting environment is a finite vector of constructible sets, and its indices identify the table, working set, code domain, tower, and numeral tags. Dependent pairs express the witnesses returned by the readers. Whenever such a witness is propositionally truncated, it may be used only to prove another proposition, never as globally chosen data.
<!--zh-->
解释环境是可构造集合组成的有限向量，其中的索引标识表、工作集、码域、塔与数码标签。依赖对表达各读式返回的见证。只要见证处在命题截断下，它就只能用于证明另一个命题，不能成为全局选定的数据。
<!--ja-->
解釈環境は構成可能集合の有限ベクトルであり、その添字が表、作業集合、コード領域、塔、数項タグを指定します。依存対は各読みが返す証人を表します。その証人が命題的切り詰めのもとにある場合、別の命題を証明するためにだけ使うことができ、大域的に選ばれたデータにはできません。
<!--/-->

```agda
```

<!--en-->
Natural-number arities are represented inside the cumulative hierarchy by the numerals `# k`. Thus an environment-tower entry is encoded as the pair of `# k` with `envSet W k`. Equality is always asserted between the underlying hierarchy sets, which is the level at which the coding theorems operate.
<!--zh-->
自然数元数在累积层级内部表示为数码 `# k`。因此环境塔的条目被编码为 `# k` 与 `envSet W k` 的有序对。这里的等式始终陈述于底层的层级集合之间，这正是编码定理工作的层面。
<!--ja-->
自然数アリティは、累積階層の内部で数項 `# k` として表されます。したがって環境の塔の項目は、`# k` と `envSet W k` の順序対として符号化されます。等しさは常に階層の底の集合の間で述べられ、符号化定理もこのレベルで働きます。
<!--/-->

```agda
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_; setIsSet )
open import Cubical.HITs.CumulativeHierarchy.Constructions using ( module InfinitySet )
open InfinitySet {ℓ} using ( #_ )

```

<!--en-->
Write `S` for the carrier of the constructible structure. An element of `S` consists of an underlying hierarchy set together with evidence of constructibility. The table readers compare the underlying sets; they do not assert equality of the accompanying constructibility evidence.
<!--zh-->
以 `S` 表示可构造结构的载体。`S` 的元素由一个底层层级集合及其可构造性证据组成。表的读式比较的是底层集合，并不主张随附的可构造性证据相等。
<!--ja-->
構成可能構造の台を `S` と書きます。`S` の要素は、階層の底の集合と、その構成可能性の証拠からなります。表の読みが比較するのは底の集合であり、付随する構成可能性の証拠の等しさは主張しません。
<!--/-->

```agda
open hPropStructure 𝒮ʟ using ( S )

```

<!--en-->
Formulas in this chapter are interpreted inside `L`, with finite environments in `S`. Their boundedness later permits comparison with the ambient hierarchy, but the present soundness argument first works entirely with this internal satisfaction relation.
<!--zh-->
本章的公式在 `L` 内部解释，其有限环境取值于 `S`。这些公式的有界性使后文能够与外围层级比较，但眼下的可靠性论证首先完全在这一内部满足关系中进行。
<!--ja-->
この章の論理式は `L` の内部で解釈され、有限環境は `S` に値を取ります。論理式の有界性によって後で周囲の階層と比較できますが、ここでの健全性の議論はまず、この内部の充足関係だけを用いて進みます。
<!--/-->

```agda
module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans using ( _^_; _⊨ᵐ_ )
open AbsL using ( _^_ ) renaming ( _⊨ᵐ_ to _⊨_ )
```

<!--en-->
## Soundness of the bounded description
<!--zh-->
## 有界描述的可靠性
<!--ja-->
## 有界な記述の健全性
<!--/-->

<!--en-->
For soundness, fix candidate sets `T`, `C`, and `E`, a working set `W`, ten numeral tags, and the environment in which they are read. Assume separately that the tower, code-domain, and table descriptions hold, and align only the working-set slot with `W`. None of the three description hypotheses follows from the other two.
<!--zh-->
为证明可靠性，固定候选集合 `T`、`C`、`E`、工作集 `W`、十个数码标签，以及读取它们的环境。分别假设塔、码域与表的描述成立，并且只把工作集槽与 `W` 对齐。这三项描述假设中，没有一项由另外两项推出。
<!--ja-->
健全性のために、候補集合 `T`、`C`、`E`、作業集合 `W`、十個の数項タグ、そしてそれらを読む環境を固定します。塔、コード領域、表の記述が成り立つことを個別に仮定し、作業集合のスロットだけを `W` と整合させます。三つの記述の仮定のどれも、残りの二つからは従いません。
<!--/-->

```agda
module SatSound {m : ℕ} (T w C E : Fin m) (N : Fin 10 → Fin m) (γ : S ^ m) (W : S)
  (qw : fst (lookup w γ) ≡ fst W) (tg : Tags γ N)
  (hE : ⟨ γ ⊨ towerAt E w (N f0) ⟩) (hC : ⟨ γ ⊨ codesAt C w E N ⟩)
  (hT : ⟨ γ ⊨ tableAt T w C E N ⟩) where
  open Alphabet W
```

<!--en-->
Let `Tv`, `Cv`, and `Ev` denote the underlying sets presented by the candidate table, code domain, and environment tower. The clause semantics supplies the bridge from bounded formulas about these sets to the ambient membership and equality facts needed by the structural argument.
<!--zh-->
用 `Tv`、`Cv`、`Ev` 表示候选表、码域与环境塔所呈现的底层集合。子句语义提供一座桥，把关于这些集合的有界公式转换为结构论证所需的外围隶属与等式事实。
<!--ja-->
候補の表、コード領域、環境の塔が表す底の集合を、それぞれ `Tv`、`Cv`、`Ev` と書きます。節の意味論は、これらの集合についての有界論理式を、構造的な議論に必要な周囲の所属と等しさへ結ぶ橋を与えます。
<!--/-->

```agda
  open Bridge W
  private
    Tv = fst (lookup T γ)
    Cv = fst (lookup C γ)
    Ev = fst (lookup E γ)
```

<!--en-->
Suppose an entry of `Ev` is already presented as the encoded pair of `n` and `F`. Reading the tower yields, under propositional truncation, an arity `k` with `n = # k`; forgetting the accompanying equation `F = envSet W k` gives exactly the arity fact needed to analyze candidate formula keys. The converse tower reading places every genuine arity entry in `Ev`, so genuine keys can also be inserted into `Cv`.
<!--zh-->
设 `Ev` 的一个条目已经呈现为 `n` 与 `F` 的编码对。读取环境塔会在命题截断下给出元数 `k` 及等式 `n = # k`；忘去同时得到的 `F = envSet W k`，便得到分析候选公式键恰好所需的元数事实。反向的塔读式把每个真实元数条目放入 `Ev`，因而也能把真实键插入 `Cv`。
<!--ja-->
`Ev` の項目が、すでに `n` と `F` の符号化された対として表されているとします。塔を読むと、命題的切り詰めのもとでアリティ `k` と等式 `n = # k` が得られます。同時に得られる `F = envSet W k` を忘れると、候補の論理式の鍵を解析するためにちょうど必要なアリティの事実になります。逆向きの塔の読みは各々の実際のアリティの項目を `Ev` に入れるので、実際の鍵を `Cv` に入れることもできます。
<!--/-->

```agda
    module TR = TowerRead E w (N f0) γ W qw (tg f0) hE
    arity : (n F : S) → ⟨ pr (fst n) (fst F) ∈ Ev ⟩ → ∥ Σ[ k ∈ ℕ ] (fst n ≡ # k) ∥₁
    arity n F q∈ = map₁ (λ { (k , (qk , _)) → k , qk }) (TR.entry-out n F q∈)
    module CS = CodesSound C w E N γ W qw tg arity (hC .fst)
    module CC = CodesComplete C w E N γ W qw tg TR.entry-in (hC .snd)
```

<!--en-->
The hypothesis `hT` consists of totality, the on-domain condition, and the ten constructor clauses, and `Frame` supplies their semantic readings. The pinning argument in `SatSoundC` uses totality and the ten clauses together with the tower facts and closure of the candidate code domain. It does not need the on-domain condition, because the entry to be pinned is already given as a pair at a genuine formula key; that condition will instead be used when reading an arbitrary presented table pair below.
<!--zh-->
前提 `hT` 由全定义性、定义域条件与十条构造子子句组成，`Frame` 则提供它们的语义读式。`SatSoundC` 中的钉扎论证把全定义性和十条子句与环境塔事实、候选码域的封闭性结合起来。该论证不需要定义域条件，因为要被钉扎的表项已经作为真实公式键处的一个配对给出；后面读取任意已呈现的表配对时，才会使用定义域条件。
<!--ja-->
仮定 `hT` は、全域性、領域条件、十個の構成子の節からなり、`Frame` はそれらの意味論的な読みを与えます。`SatSoundC` の固定の議論は、全域性と十個の節を、環境の塔に関する事実および候補の符号領域の閉性に組み合わせます。固定すべき表の要素は、すでに実際の論理式の鍵における対として与えられているため、この段階で領域条件は必要ありません。その条件は、後で任意の提示された表の対を読むときに使われます。
<!--/-->

```agda
    module Fr = Frame T w C E N γ tg
    module SC = SatSoundC T w C E N γ W qw tg hE CS.closed hT

```

<!--en-->
The two domain conditions have complementary forms. Totality gives, for every `c` in `Cv`, merely some `y` with `pr c y` in `Tv`. The on-domain condition starts from an arbitrary member `e` of `Tv` and, again under propositional truncation, decomposes it as `pr c y` with `c` in `Cv`. Neither condition chooses values or pair components globally, and neither alone makes the table single-valued.
<!--zh-->
两条定义域条件具有互补的形式。全定义性对 `Cv` 中每个 `c` 仅给出经命题截断的存在性：有某个 `y` 使 `pr c y` 属于 `Tv`。定义域条件则从 `Tv` 的任意成员 `e` 出发，同样在命题截断下把它分解为 `pr c y`，并给出 `c` 属于 `Cv`。两者都不在全局选定取值或配对分量，单凭其中任何一条也不能使该表成为单值关系。
<!--ja-->
二つの領域条件は互いを補う形をしています。全域性は、`Cv` の各 `c` に対し、`pr c y` が `Tv` に属するような `y` が存在することを、命題的切り詰めのもとで与えます。領域条件は `Tv` の任意の要素 `e` から始め、再び命題的切り詰めのもとで、`e` を `pr c y` と分解し、`c` が `Cv` に属することを与えます。どちらも値や対の成分を大域的に選ばず、またどちら一方だけで表が一価の関係になるわけでもありません。
<!--/-->

```agda
    hTot = hT .fst
    hOn = hT .snd .fst
```

<!--en-->
Apply totality to the genuine key of a formula `a`, using the fact that code-domain completeness places that key in `Cv`. The result merely says that some value is paired with the key in `Tv`: the witness remains under propositional truncation. It supplies no chosen value or decoding function, and it will later be eliminated only into a proposition.
<!--zh-->
利用码域完备性把公式 `a` 的真实键放入 `Cv`，再对此键应用全域性。结论仅仅说某个值与该键组成的对属于 `Tv`，见证仍处在命题截断下。这里没有选定值，也没有解码函数；后文只会把它消去到命题中。
<!--ja-->
コード領域の完全性によって論理式 `a` の実際の鍵を `Cv` に入れ、その鍵に全域性を適用します。結論は、ある値とその鍵との対が `Tv` に属することを単に述べ、証人は命題的切り詰めのもとに残ります。選ばれた値も復号関数も得られず、後では命題への消去にだけ使われます。
<!--/-->

```agda
    sub : ∀ {n} (a : Formula Ab n) → ∥ Σ[ ya ∈ S ] ⟨ pr (fst (keyS W a)) (fst ya) ∈ Tv ⟩ ∥₁
    sub a = Fr.total-out hTot (keyS W a) (CC.key-in a)
```

<!--en-->
The pinning predicate says: whenever a value `y` is paired with the key of `ψ` in the candidate table, the underlying set of `y` equals the recursively defined satisfaction set of `ψ`. It pins the underlying set only; the constructibility certificate of `y` and the formula itself are not fixed by it.
<!--zh-->
钉扎谓词说：只要值 `y` 与 `ψ` 的键组成的对属于候选表，`y` 的底层集就等于 `ψ` 的递归满足集。它只钉扎底层集；`y` 的可构造性证书与公式本身都不由它固定。
<!--ja-->
固定の述語は次を言います。値 `y` と `ψ` のキーの対が候補の表に属するならば、`y` の底の集合は `ψ` の再帰的な充足集合の底の集合と等しくなる。固定されるのは底の集合だけです。`y` の構成可能性の証明も、論理式そのものも、これでは固定されません。
<!--/-->

```agda
  Pinned : ∀ {n} (ψ : Formula Ab n) → Type (ℓ-suc ℓ)
  Pinned ψ = (y : S) → ⟨ pr (fst (keyS W ψ)) (fst y) ∈ Tv ⟩ → fst y ≡ fst (SatW ψ)

```

<!--en-->
The proof proceeds by structural recursion on `ψ`. Closure of `Cv` supplies the keys of the immediate subformulas, and totality supplies their table values only under propositional truncation. The recursive hypotheses pin those child values; the matching constructor clause then gives the same extensional condition as the semantic recursion, so extensionality pins the parent value. The fact `CC.key-in ψ` supplies the candidate-domain membership needed to start this argument at the key of `ψ`.
<!--zh-->
证明对 `ψ` 作结构递归。`Cv` 的封闭性给出直接子公式的键，全定义性则只在命题截断下给出这些键处的表取值。递归假设钉扎这些子取值；相应的构造子子句随后给出与语义递归相同的外延条件，因此外延性钉扎父公式的取值。事实 `CC.key-in ψ` 则提供从 `ψ` 的键开始这项论证所需的候选码域隶属。
<!--ja-->
証明は `ψ` の構造再帰によって進みます。`Cv` の閉性が直接の部分論理式の鍵を与え、全域性がその鍵での表の値を命題的切り詰めのもとでのみ与えます。再帰的な仮定はそれらの子の値を固定し、対応する構成子の節は意味論的再帰と同じ外延条件を与えます。そのため、外延性によって親の値が固定されます。`CC.key-in ψ` は、`ψ` の鍵でこの議論を始めるために必要な、候補の符号領域への所属を与えます。
<!--/-->

```agda
  pinned : ∀ {n} (ψ : Formula Ab n) → Pinned ψ
  pinned ψ = SC.pinned ψ (CC.key-in ψ)
```

<!--en-->
Every member of the candidate code domain belongs to the canonical code set. The candidate-key reader reveals an arity, a formula, and a key equation only under propositional truncation. Since the desired canonical membership is a proposition, the witness may be eliminated there and membership transported along its equation; no formula is selected by this argument.
<!--zh-->
候选码域的每个成员都属于典范码集。候选键读式只在命题截断下显露元数、公式与键等式。由于目标的典范隶属是命题，可以把见证消去到该目标，并沿等式搬运隶属；这一论证没有选定公式。
<!--ja-->
候補のコード領域の各要素は正準なコード集合に属します。候補の鍵の読みからアリティ、論理式、鍵の等式が得られるのは、命題的切り詰めのもとだけです。目標である正準集合への所属は命題なので、そこへ証人を消去し、その等式に沿って所属を運べます。この議論は論理式を選びません。
<!--/-->

```agda
  C-out : (c : S) → ⟨ fst c ∈ Cv ⟩ → ⟨ fst c ∈ fst (AllCodes W) ⟩
  C-out c c∈ = rec₁ (snd (fst c ∈ fst (AllCodes W)))
    (λ { (k , ψ , e) → subst (λ u → ⟨ u ∈ fst (AllCodes W) ⟩) (sym e) (key∈AllCodes W ψ) })
    (CS.key-out c c∈)

```

<!--en-->
Conversely, every member of the canonical code set belongs to `Cv`. Canonical membership supplies a formula-key presentation under propositional truncation, and code-domain completeness inserts that key into the candidate domain. Again the witness is used only to prove membership, rather than to define a decoder.
<!--zh-->
反过来，典范码集的每个成员都属于 `Cv`。典范隶属在命题截断下给出公式键的呈现，码域完备性再把该键插入候选域。这里仍只用见证证明隶属，而不据此定义解码器。
<!--ja-->
逆に、正準なコード集合の各要素は `Cv` に属します。正準集合への所属は、命題的切り詰めのもとで論理式の鍵としての表示を与え、コード領域の完全性がその鍵を候補領域に入れます。ここでも証人は所属を証明するためだけに使われ、復号器の定義には使われません。
<!--/-->

```agda
  C-in : (c : S) → ⟨ fst c ∈ fst (AllCodes W) ⟩ → ⟨ fst c ∈ Cv ⟩
  C-in c c∈ = rec₁ (snd (fst c ∈ Cv))
    (λ { (k , ψ , e) → subst (λ u → ⟨ u ∈ Cv ⟩) (sym e) (CC.key-in ψ) })
    (AllCodes-out W c c∈)

```

<!--en-->
The outward tower reading concerns an entry already presented as `pr n F`. Under propositional truncation it yields a natural number `k` with `n = # k` and `F = envSet W k`. It neither chooses `k` globally nor claims that this lemma alone supplies a coded-pair presentation for an arbitrary member of `Ev`.
<!--zh-->
环境塔的向外读式只处理已经呈现为 `pr n F` 的条目。它在命题截断下给出自然数 `k`，使 `n = # k` 且 `F = envSet W k`。它既不全局选定 `k`，也不声称仅凭本引理就能把 `Ev` 的任意成员呈现为编码对。
<!--ja-->
塔の外向きの読みが扱うのは、すでに `pr n F` として表された項目です。命題的切り詰めのもとで自然数 `k` が得られ、`n = # k` かつ `F = envSet W k` となります。`k` を大域的に選ぶことも、この補題だけで `Ev` の任意の要素に符号化された対としての表示を与えることもありません。
<!--/-->

```agda
  E-out : (n F : S) → ⟨ pr (fst n) (fst F) ∈ Ev ⟩
        → ∥ Σ[ k ∈ ℕ ] ((fst n ≡ # k) × (fst F ≡ fst (envSet W k))) ∥₁
  E-out = TR.entry-out

```

<!--en-->
The inward tower reading supplies the complementary fact without propositional truncation: for each given natural number `k`, the standard entry `pr (# k) (envSet W k)` belongs to `Ev`. Together with the previous reading, this controls standard encoded entries in both directions without asserting a chosen arity for every arbitrary tower member.
<!--zh-->
环境塔的向内读式给出互补事实，而且无需命题截断：对每个给定的自然数 `k`，标准条目 `pr (# k) (envSet W k)` 都属于 `Ev`。它与上一条读式共同双向控制标准编码条目，但不主张为塔的每个任意成员选定元数。
<!--ja-->
塔の内向きの読みは、命題的切り詰めを伴わずに補完的な事実を与えます。与えられた各自然数 `k` について、標準的な項目 `pr (# k) (envSet W k)` は `Ev` に属します。前の読みと合わせて標準的な符号化項目を双方向に制御しますが、塔の任意の要素ごとにアリティを選ぶとは主張しません。
<!--/-->

```agda
  E-in : (k : ℕ) → ⟨ pr (# k) (fst (envSet W k)) ∈ Ev ⟩
  E-in = TR.entry-in

```

<!--en-->
The table reading is the heart of the soundness direction. It is stated only for members already presented as the ordered pair of `x` and `y`; arbitrary members of the candidate table are not covered by this lemma.
<!--zh-->
表的读取是可靠性方向的核心。它只对已经呈现为 `x` 与 `y` 的有序对的成员陈述；候选表的任意成员不在本引理覆盖范围内。
<!--ja-->
表の読みは、健全性の方向の中心です。それは、`x` と `y` の順序対としてすでに提示された要素に対してだけ述べられます。候補の表の任意の要素は、この補題の範囲ではありません。
<!--/-->

```agda
  T-out : (x y : S) → ⟨ pr (fst x) (fst y) ∈ Tv ⟩
        → Σ[ mx ∈ ⟨ fst x ∈ fst (AllCodes W) ⟩ ] (fst y ≡ fst (Table.val W W x mx))
  T-out x y h = rec₁ (isPropΣ (snd (fst x ∈ fst (AllCodes W))) (λ mx → setIsSet _ _))
    (λ { (c , yc , (ee , c∈)) → rec₁ (isPropΣ (snd (fst x ∈ fst (AllCodes W))) (λ mx → setIsSet _ _))
      (λ { (k , ψ , e) →
```

<!--en-->
The pairing equation splits into the first components of the two sides, and the code equation identifies the recorded key with the key of some decoded formula; the membership of that formula's key in the canonical code set follows by transport.
<!--zh-->
配对等式拆分出两侧的第一分量，码等式把被记录的键认同为某条解码公式的键；该公式键属于典范码集则由搬运得到。
<!--ja-->
対の等式は両辺の第一成分に分解され、コードの等式が、記録されたキーを、復号されたある論理式のキーと同一視します。その論理式のキーが正準なコード集合に属することは、輸送によって従います。
<!--/-->

```agda
        let q = pr-inj ee
            qx : fst x ≡ fst (keyS W ψ)
            qx = q .fst ∙ e
            mx : ⟨ fst x ∈ fst (AllCodes W) ⟩
            mx = subst (λ u → ⟨ u ∈ fst (AllCodes W) ⟩) (sym qx) (key∈AllCodes W ψ)
```

<!--en-->
Pinning identifies the recorded value with the recursive satisfaction set, and `val-at` identifies that set with the functional table value at the same key. The conclusion contains canonical code-set membership together with an equality of underlying sets. Although it is not propositionally truncated, it can be obtained from the truncated decoding because the entire dependent pair is itself a proposition; it is not computational decoding.
<!--zh-->
钉扎先把被记录值与递归满足集认同，`val-at` 再把该集合与同一键处的函数表取值认同。结论由典范码集隶属及底层集合等式组成。虽然它本身没有命题截断，但整个依赖对本身是命题，所以可以从命题截断下的解码中得到；这并不是计算性的解码。
<!--ja-->
固定によって記録された値を再帰的な充足集合と同一視し、`val-at` によってその集合を同じ鍵における関数的な表の値と同一視します。結論は、正準なコード集合への所属と底の集合の等しさからなります。結論自体は命題的切り詰められていませんが、依存対全体が命題なので、命題的切り詰められた復号から得られます。これは計算的な復号ではありません。
<!--/-->

```agda
        in mx , ( pinned ψ y (subst (λ u → ⟨ u ∈ Tv ⟩) (cong (λ a → pr a (fst y)) qx) h)
                ∙ sym (cong fst (val-at W W ψ x mx qx)) ) })
      (CS.key-out c c∈) })
    (Fr.onC-out hOn (down (lookup T γ) (pr (fst x) (fst y)) h) h)

```

<!--en-->
For the converse table reading, begin with a specified canonical code `x`. Its membership in `AllCodes W` gives, under propositional truncation, a formula `ψ` whose key is `x`. Totality then gives, again under propositional truncation, some candidate value recorded at that formula key.
<!--zh-->
为得到表的反向读式，从一个指定的典范码 `x` 出发。它在 `AllCodes W` 中的隶属在命题截断下给出公式 `ψ`，其键就是 `x`。全域性随后再次在命题截断下给出该公式键处记录的某个候选值。
<!--ja-->
表の逆向きの読みでは、指定された正準コード `x` から始めます。`AllCodes W` への所属により、命題的切り詰めのもとで、鍵が `x` である論理式 `ψ` が得られます。次に全域性から、再び命題的切り詰めのもとで、その論理式の鍵に記録された候補の値が得られます。
<!--/-->

```agda
  T-in : (x : S) (mx : ⟨ fst x ∈ fst (AllCodes W) ⟩) → ⟨ pr (fst x) (fst (Table.val W W x mx)) ∈ Tv ⟩
  T-in x mx = rec₁ (snd (pr (fst x) (fst (Table.val W W x mx)) ∈ Tv))
    (λ { (k , ψ , e) → rec₁ (snd (pr (fst x) (fst (Table.val W W x mx)) ∈ Tv))
      (λ { (y , my) →
        subst (λ u → ⟨ u ∈ Tv ⟩)
```

<!--en-->
The candidate value is pinned to the recursive satisfaction set, and the value lemma aligns it with the functional table value; the membership is then transported along the equation of the ordered pairs. Both eliminations land in the table membership, which is a proposition.
<!--zh-->
候选值被钉扎到递归满足集，值引理把它与函数表值对齐；隶属随即沿有序对等式搬运。两次消去都落在表隶属这一命题上。
<!--ja-->
候補の値は、再帰的な充足の集合に固定され、値の補題がそれを関数的な表の値と整列させます。そして所属が、順序対の等式に沿って運ばれます。どちらの消去も、命題である表の所属に着地します。
<!--/-->

```agda
          (cong₂ pr (sym e) (pinned ψ y my ∙ sym (cong fst (val-at W W ψ x mx e))))
          my })
      (sub ψ) })
    (AllCodes-out W x mx)
```

<!--en-->
## Completeness and the two readings
<!--zh-->
## 完备性与两种读法
<!--ja-->
## 完全性と二つの読み方
<!--/-->

<!--en-->
Completeness starts from concrete semantic objects rather than an arbitrary candidate. The four environment slots are aligned separately with `W`, the real graph `SatGraph.pairs W`, the canonical code set `AllCodes W`, and the real tower `Tower.tower W`; the ten tags are also fixed. These alignments are hypotheses, not consequences of the bounded clauses.
<!--zh-->
完备性从具体的语义对象出发，而不是从任意候选出发。环境中的四个槽分别与 `W`、真实图 `SatGraph.pairs W`、典范码集 `AllCodes W`、真实塔 `Tower.tower W` 对齐，十个标签也被固定。这些对齐是前提，不是有界子句的结论。
<!--ja-->
完全性は任意の候補ではなく、具体的な意味論的対象から始めます。環境の四つのスロットは、それぞれ `W`、実際のグラフ `SatGraph.pairs W`、正準なコード集合 `AllCodes W`、実際の塔 `Tower.tower W` と整合し、十個のタグも固定されます。これらの整合は仮定であり、有界な節から得られる結論ではありません。
<!--/-->

```agda
module SatHolds {m : ℕ} (T w C E : Fin m) (N : Fin 10 → Fin m) (γ : S ^ m) (W : S)
  (qw : fst (lookup w γ) ≡ fst W) (qT : fst (lookup T γ) ≡ fst (SatGraph.pairs W))
  (qC : fst (lookup C γ) ≡ fst (AllCodes W)) (qE : fst (lookup E γ) ≡ fst (Tower.tower W))
  (tg : Tags γ N) where
  open Alphabet W
```

<!--en-->
Write `Tv` and `Cv` for the underlying sets in the table and code-domain slots. The alignments `qT` and `qC` transport their membership facts to the genuine graph and the canonical code set. Consequently, a presented table pair can be read with the graph lemmas, whereas a code is decoded only under propositional truncation. Every equality below still compares underlying hierarchy sets.
<!--zh-->
记表槽与码域槽中的底层集合为 `Tv` 与 `Cv`。对齐 `qT` 与 `qC` 把它们的隶属事实分别搬运到真实图与典范码集中。因此，已呈现的表配对可以用真实图的读式处理，而公式码的解码仍只在命题截断下成立。下面每条等式依然只比较底层层级集合。
<!--ja-->
表と符号領域のスロットにある基礎集合を `Tv` と `Cv` と書きます。同定 `qT` と `qC` は、それらの所属事実をそれぞれ実際のグラフと正準な符号集合へ運びます。したがって、すでに対の形で提示された表の要素はグラフの読みによって扱えますが、符号の復号は命題的切り詰めのもとでのみ得られます。以下の等式はすべて、引き続き階層の基礎集合を比較します。
<!--/-->

```agda
  open Bridge W
  private
    Tv = fst (lookup T γ)
    Cv = fst (lookup C γ)
```

<!--en-->
A table value at a code identified with a formula key equals the recursive satisfaction set of that formula. The proof reads the pair out of the real satisfaction graph, transports its second component through the identification of the presented key with the formula key, and finishes with the value lemma.
<!--zh-->
在与公式键同一视的码处的表值，等于该公式的递归满足集。证明从真实满足图读出该对，沿「被呈现键与公式键」的同一视搬运第二分量，最后以值引理收尾。
<!--ja-->
論理式のキーと同一視された符号のもとでの表の値は、その論理式の再帰的な充足の集合と等しくなります。証明は、本物の充足のグラフから対を読み出し、提示されたキーと論理式のキーの同一視に沿って第二成分を運び、値の補題で締めくくります。
<!--/-->

```agda
    val≡ : ∀ {n} (ψ : Formula Ab n) (c yc : S) → fst c ≡ fst (keyS W ψ)
         → ⟨ pr (fst c) (fst yc) ∈ Tv ⟩ → fst yc ≡ fst (SatW ψ)
    val≡ ψ c yc qc h =
      let p = SatGraph.pairs-out W c yc (subst (λ u → ⟨ pr (fst c) (fst yc) ∈ u ⟩) qT h)
      in p .snd ∙ cong fst (SatGraph.valOf≡ W c (p .fst)) ∙ cong fst (val-at W W ψ c (p .fst) qc)
```

<!--en-->
If a code-domain member is presented as `pr (# n) z`, transporting it into `AllCodes W` permits decoding under propositional truncation: some formula `ψ : Formula Ab n` has payload `z`. This gives neither a chosen formula nor uniqueness of decoding, and therefore does not define a decoding function.
<!--zh-->
若码域成员呈现为 `pr (# n) z`，把它搬入 `AllCodes W` 后便可在命题截断下解码：存在某条公式 `ψ : Formula Ab n`，其载荷为 `z`。这里既没有选定公式，也没有解码唯一性，因而没有定义出解码函数。
<!--ja-->
コード領域の要素が `pr (# n) z` として表されているなら、それを `AllCodes W` へ運ぶことで、命題的切り詰めのもとで復号できます。すなわち、ペイロードが `z` である論理式 `ψ : Formula Ab n` が存在します。論理式は選ばれず、復号の一意性も得られないので、復号関数は定義されません。
<!--/-->

```agda
    decode : (c : S) → ⟨ fst c ∈ Cv ⟩ → (n : ℕ) (z : V ℓ) → fst c ≡ pr (# n) z
           → ∥ Σ[ ψ ∈ Formula Ab n ] (z ≡ cd ψ) ∥₁
    decode c c∈ = Match.decodeAll W c (subst (λ u → ⟨ fst c ∈ u ⟩) qC c∈)
```

<!--en-->
For a candidate code `c`, alignment with the canonical code set makes `c` a valid input to the real graph. Its real graph value provides a table entry, which is transported back along the alignment of `Tv` with `SatGraph.pairs W`. The resulting existence statement remains under propositional truncation, exactly as the totality clause requires.
<!--zh-->
对候选码 `c`，它与典范码集的对齐使 `c` 成为真实图的合法输入。真实图在此码处的取值给出一个表项，再沿 `Tv` 与 `SatGraph.pairs W` 的对齐搬回。所得存在陈述仍处在命题截断下，恰好符合全域性子句的要求。
<!--ja-->
候補コード `c` は、正準なコード集合との整合によって、実際のグラフへの正しい入力になります。そのグラフの値から表の項目を得て、`Tv` と `SatGraph.pairs W` の整合に沿って運び戻します。得られる存在の主張は、全域性の節が要求する通り、命題的切り詰めのもとに残ります。
<!--/-->

```agda
    tot : (c : S) → ⟨ fst c ∈ Cv ⟩ → ∥ Σ[ yc ∈ S ] ⟨ pr (fst c) (fst yc) ∈ Tv ⟩ ∥₁
    tot c c∈ =
      let mx = subst (λ u → ⟨ fst c ∈ u ⟩) qC c∈
      in ∣ SatGraph.valOf W c mx , subst (λ u → ⟨ pr (fst c) (fst (SatGraph.valOf W c mx)) ∈ u ⟩) (sym qT) (SatGraph.pairs-in W c mx) ∣₁

```

<!--en-->
The real graph also supplies the required shape of arbitrary table members. Under propositional truncation, every such member is an encoded pair of some code and its graph value, and that code belongs to `Cv`. This is an existence-only decomposition; it does not choose components for each member.
<!--zh-->
真实图还给出任意表成员所需的形状。在命题截断下，每个这样的成员都是某个码与其图取值组成的编码对，而且该码属于 `Cv`。这只是存在性的分解，并没有为每个成员选定分量。
<!--ja-->
実際のグラフは、任意の表の要素に必要な形も与えます。命題的切り詰めのもとで、その各要素は、あるコードとそのグラフの値からなる符号化された対であり、そのコードは `Cv` に属します。これは存在だけを述べる分解であり、各要素の成分を選ぶものではありません。
<!--/-->

```agda
    onc : (e : S) → ⟨ fst e ∈ Tv ⟩
        → ∥ Σ[ c ∈ S ] Σ[ yc ∈ S ] ((fst e ≡ pr (fst c) (fst yc)) × ⟨ fst c ∈ Cv ⟩) ∥₁
    onc e e∈ = map₁
      (λ { (x , mx , ee) → x , SatGraph.valOf W x mx , (ee , subst (λ u → ⟨ fst x ∈ u ⟩) (sym qC) mx) })
      (SatGraph.pairs-shape W e (subst (λ u → ⟨ fst e ∈ u ⟩) qT e∈))
```

<!--en-->
The inputs to `SatHoldsC.holds` have distinct jobs. The real tower supplies the environment rows, `val≡` identifies values at genuine formula keys, `decode` merely recovers a formula from a shaped code, and `tot` and `onc` establish the two domain conditions. The structural argument then verifies all ten constructor clauses. Whenever it consumes a propositionally truncated arity, formula, or decomposition, it eliminates that witness only into the proposition that the relevant clause is satisfied; no decoder or choice of table values escapes.
<!--zh-->
`SatHoldsC.holds` 的各项输入分工明确。真实环境塔提供环境行，`val≡` 识别真实公式键处的取值，`decode` 只从具有指定形状的码中解出经命题截断的公式，`tot` 与 `onc` 则建立两条定义域条件。结构论证随后验证全部十条构造子子句。它每次使用经命题截断的元数、公式或分解时，都只把见证消去到「相应子句得到满足」这一命题中，不会产生全局解码器或表取值的选择。
<!--ja-->
`SatHoldsC.holds` への入力は異なる役割を担います。実際の環境の塔が環境の行を与え、`val≡` が実際の論理式の鍵での値を同定し、`decode` が形の定まった符号から論理式を命題的切り詰めのもとでのみ復号し、`tot` と `onc` が二つの領域条件を示します。構造的な議論は、続いて十個の構成子の節をすべて検証します。命題的に切り詰められたアリティ、論理式、分解を使うときは、対応する節が満たされるという命題にのみその証人を消去します。復号器や表の値の選択がその外へ出ることはありません。
<!--/-->

```agda
  holds : ⟨ γ ⊨ tableAt T w C E N ⟩
  holds = SatHoldsC.holds W T w C E N γ qw tg
    (TowerHolds.holds E w (N f0) γ W qw qE (tg f0)) val≡ decode tot onc
```

<!--en-->
The sealed formula `satAt` packages three independent descriptions: `towerAt`, `codesAt`, and `tableAt`. The tower component is passed the tag slot `N f0`, which `Tags` identifies with the numeral zero; the code-domain and table components receive the whole ten-slot family `N`. This conjunction by itself adds no equality with the canonical tower, code set, or satisfaction graph.
<!--zh-->
密封公式 `satAt` 封装三条彼此独立的描述：`towerAt`、`codesAt` 与 `tableAt`。环境塔分量接收标签槽 `N f0`，`Tags` 把该槽识别为数码零；码域分量与表分量则接收完整的十槽族 `N`。这项合取本身不会给出候选对象与典范环境塔、码集或满足关系图之间的等式。
<!--ja-->
封じられた論理式 `satAt` は、`towerAt`、`codesAt`、`tableAt` という三つの独立な記述をまとめます。塔の成分にはタグのスロット `N f0` が渡され、`Tags` はそれを数項ゼロと同定します。符号領域と表の成分には、十個のスロットからなる族 `N` 全体が渡されます。この連言自体は、候補の対象と正準な環境の塔、符号集合、または充足関係グラフとの等しさを加えるものではありません。
<!--/-->

```agda
opaque
  satAt : ∀ {m} → Fin m → Fin m → Fin m → Fin m → (Fin 10 → Fin m) → Formula S m
  satAt T w C E N = towerAt E w (N f0) ∧̇ (codesAt C w E N ∧̇ tableAt T w C E N)

```

<!--en-->
Later arguments may treat `satAt` as one bounded predicate rather than repeatedly expanding its three components. Its definition is unfolded in a controlled scope when checking syntactic properties such as membership in the Lévy hierarchy; semantic use proceeds through the projection and completeness results below. Opacity marks this proof boundary and contributes no additional model-theoretic property.
<!--zh-->
后续论证可以把 `satAt` 当作一个完整的有界谓词，无需反复展开它的三个分量。检查它是否属于 Lévy 层级等句法性质时，定义只在受控范围内展开；语义上的使用则通过下面的投影与完备性结果进行。不透明性只标出这道证明边界，并不增加任何模型论性质。
<!--ja-->
後の議論では、`satAt` の三つの成分を繰り返し展開することなく、これを一つの有界述語として扱えます。Lévy 階層への所属などの統語的性質を確かめるときには、定義を限定された範囲で展開します。意味論的に使うときは、以下の射影と完全性の結果を通して扱います。不透明性はこの証明の境界を示すだけであり、モデル理論的な性質を加えるものではありません。
<!--/-->

```agda
opaque
  unfolding satAt

```

<!--en-->
The certificate `Δ₀-satAt` uses closure of the bounded fragment under conjunction to combine the certificates for the three components. It establishes only the syntactic boundedness of `satAt`; it says nothing yet about which sets satisfy the formula. The semantic directions are supplied later by `SatRead` and `sat-complete`.
<!--zh-->
证书 `Δ₀-satAt` 利用有界片段对合取的封闭性，把三个分量的证书组合起来。它只建立 `satAt` 的句法有界性，尚未说明哪些集合满足该公式。后面的 `SatRead` 与 `sat-complete` 才分别提供语义上的两个方向。
<!--ja-->
証明 `Δ₀-satAt` は、有界部分が連言について閉じていることを使い、三つの成分の証明を組み合わせます。ここで得られるのは `satAt` の統語的な有界性だけであり、どの集合がこの論理式を満たすかはまだ述べません。意味論的な二つの方向は、後で `SatRead` と `sat-complete` が与えます。
<!--/-->

```agda
  Δ₀-satAt : ∀ {m} (T w C E : Fin m) (N : Fin 10 → Fin m) → Δ₀ (satAt T w C E N)
  Δ₀-satAt T w C E N = δ-∧ (Δ₀-towerAt E w (N f0)) (δ-∧ (Δ₀-codesAt C w E N) (Δ₀-tableAt T w C E N))

```

<!--en-->
From a proof of `satAt`, one recovers the three precise hypotheses needed for soundness: the environment-tower description, the code-domain description, and the table description. This projection adds no semantic conclusion and supplies no equality with the canonical objects.
<!--zh-->
从 `satAt` 的证明中可以取回可靠性所需的三项精确前提：环境塔描述、码域描述与表描述。这一投影不增加语义结论，也不给出候选对象与典范对象的等式。
<!--ja-->
`satAt` の証明から、健全性に必要な三つの正確な仮定、すなわち環境の塔、コード領域、表の記述を取り出せます。この射影は意味論的な結論を加えず、候補の対象と正準な対象との等しさも与えません。
<!--/-->

```agda
  satAt-out : ∀ {m} (T w C E : Fin m) (N : Fin 10 → Fin m) (γ : S ^ m)
            → ⟨ γ ⊨ satAt T w C E N ⟩
            → ⟨ γ ⊨ towerAt E w (N f0) ⟩ × (⟨ γ ⊨ codesAt C w E N ⟩ × ⟨ γ ⊨ tableAt T w C E N ⟩)
  satAt-out T w C E N γ h = h

```

<!--en-->
Conversely, proofs of those three descriptions combine to establish `satAt`. The construction is purely conjunctive: each component must be supplied independently, so the table clause cannot compensate for a missing tower or code-domain clause.
<!--zh-->
反过来，这三项描述的证明组合起来便得到 `satAt`。这一构造只是合取：每个分量都必须独立给出，表子句不能补偿缺失的塔子句或码域子句。
<!--ja-->
逆に、三つの記述の証明を組み合わせれば `satAt` が得られます。この構成は連言そのものであり、各成分を個別に与える必要があります。表の節によって、欠けた塔やコード領域の節を補うことはできません。
<!--/-->

```agda
  satAt-in : ∀ {m} (T w C E : Fin m) (N : Fin 10 → Fin m) (γ : S ^ m)
           → ⟨ γ ⊨ towerAt E w (N f0) ⟩ → ⟨ γ ⊨ codesAt C w E N ⟩ → ⟨ γ ⊨ tableAt T w C E N ⟩
           → ⟨ γ ⊨ satAt T w C E N ⟩
  satAt-in T w C E N γ hE hC hT = hE , (hC , hT)
```

<!--en-->
`SatRead` is the soundness-facing interface for a candidate satisfying `satAt`. It applies only after the working-set slot has been aligned with `W` and `Tags` has calibrated the numeral slots, and it exports the six precise outward and inward rules proved above. Their original conclusion shapes are retained: the interface neither turns them into blanket set equalities nor exposes selected decoders or witnesses.
<!--zh-->
`SatRead` 是面向可靠性方向的候选对象接口。只有工作集槽已与 `W` 对齐、`Tags` 已校准数码槽且候选对象满足 `satAt` 时，它才适用，并公开上文证得的六条精确向外与向内规则。这些规则保留原有的结论形状：该接口既不把它们改写成笼统的集合等式，也不暴露选定的解码结果或见证。
<!--ja-->
`SatRead` は、`satAt` を満たす候補に対する健全性側の接続口です。作業集合のスロットが `W` と同定され、`Tags` が数項のスロットを整合させた後にのみ適用でき、上で証明した六つの正確な外向きと内向きの規則を公開します。それぞれの結論の形はそのまま保たれます。この接続口は、それらを候補集合と正準集合との一括した等しさに置き換えず、選ばれた復号結果や証人も取り出しません。
<!--/-->

```agda
module SatRead {m : ℕ} (T w C E : Fin m) (N : Fin 10 → Fin m) (γ : S ^ m) (W : S)
  (qw : fst (lookup w γ) ≡ fst W) (tg : Tags γ N) (h : ⟨ γ ⊨ satAt T w C E N ⟩) where
  private
    module SS = SatSound T w C E N γ W qw tg
      (satAt-out T w C E N γ h .fst) (satAt-out T w C E N γ h .snd .fst) (satAt-out T w C E N γ h .snd .snd)
```

<!--en-->
For codes, the two directions compare membership with `AllCodes W`. For tower entries, they read or insert standard pairs `pr (# k) (envSet W k)`. For table entries, they compare a presented pair with the functional table value at a canonical code. Keeping these three conclusion shapes distinct prevents a stronger, unsupported uniqueness claim.
<!--zh-->
对码而言，两个方向比较其与 `AllCodes W` 的隶属。对塔条目而言，两个方向读取或插入标准有序对 `pr (# k) (envSet W k)`。对表项而言，它们把一个已呈现的有序对与典范码处的函数表取值比较。保持这三类结论的形状彼此有别，可以避免无依据的更强唯一性主张。
<!--ja-->
コードについては、二方向の読みが `AllCodes W` への所属を比較します。塔の項目については、標準的な対 `pr (# k) (envSet W k)` を読んだり挿入したりします。表の項目については、提示された対を正準コードにおける関数的な表の値と比較します。この三種類の結論を区別しておくことで、根拠のない強い一意性の主張を避けられます。
<!--/-->

```agda
  open SS public using ( C-out; C-in; E-out; E-in; T-out; T-in )

```

<!--en-->
The converse theorem assumes that the four slots already present the intended objects: `W`, its satisfaction graph, its complete code set, and its environment tower. It also assumes the ten correct numeral tags. These alignments are input data for completeness and are not recovered from `satAt`.
<!--zh-->
反向定理假设四个槽已经呈现预定对象：`W`、它的满足关系图、完整码集与环境塔；同时还假设十个正确的数码标签。这些对齐是完备性的输入数据，并不是从 `satAt` 中恢复出来的。
<!--ja-->
逆向きの定理は、四つのスロットがすでに意図された対象、すなわち `W`、その充足関係のグラフ、完全なコード集合、環境の塔を表していると仮定します。さらに、正しい十個の数項タグも仮定します。これらの整合は完全性への入力であり、`satAt` から復元されるものではありません。
<!--/-->

```agda
sat-complete : ∀ {m} (T w C E : Fin m) (N : Fin 10 → Fin m) (γ : S ^ m) (W : S)
             → fst (lookup w γ) ≡ fst W
             → fst (lookup T γ) ≡ fst (SatGraph.pairs W)
             → fst (lookup C γ) ≡ fst (AllCodes W)
             → fst (lookup E γ) ≡ fst (Tower.tower W)
```

<!--en-->
The conclusion is a satisfaction proof for the already aligned environment. The proof first fills the tower and code-domain components from `qw`, `qE`, `qC`, and the calibrated tags; those alignments remain assumptions throughout. This step introduces no existential witness for a new tower, code set, or graph, and it does not claim that every quadruple satisfying `satAt` is uniquely canonical.
<!--zh-->
结论是这个已对齐环境对 `satAt` 的满足证明。证明先由 `qw`、`qE`、`qC` 与已校准的标签填入环境塔分量和码域分量；这些对齐在整个论证中始终是前提。此步不会引入新环境塔、码集或图的存在见证，也不主张每个满足 `satAt` 的四元组都唯一地等于典范四元组。
<!--ja-->
結論は、すでに整合された環境が `satAt` を満たすことの証明です。証明はまず、`qw`、`qE`、`qC`、整合されたタグを用いて、環境の塔と符号領域の成分を満たします。これらの同定は全体を通じて仮定のままです。この段階は、新しい塔、符号集合、グラフの存在証人を導入せず、`satAt` を満たす四つ組がすべて一意に正準であるとも主張しません。
<!--/-->

```agda
             → Tags γ N → ⟨ γ ⊨ satAt T w C E N ⟩
sat-complete T w C E N γ W qw qT qC qE tg =
  satAt-in T w C E N γ
    (TowerHolds.holds E w (N f0) γ W qw qE (tg f0))
    (CodesHolds.holds C w E N γ W qw qC qE tg)
```

<!--en-->
The final line supplies the table conjunct by reusing `SatHolds.holds`. As proved above, this establishes all of `tableAt`: its two domain conditions and its ten constructor clauses, rather than only the ten clauses. `satAt-in` combines that result with the tower and code-domain conjuncts. Thus `sat-complete` writes already aligned canonical data into the bounded description; the propositionally truncated decoding used inside the table proof exposes no global decoder or selected value.
<!--zh-->
最后一行重用 `SatHolds.holds` 来填入表这一合取项。如上所证，它建立的是 `tableAt` 的全部内容，即两条定义域条件与十条构造子子句，而不只是后十条子句。`satAt-in` 再把它与环境塔合取项、码域合取项组合起来。因此，`sat-complete` 是把已对齐的典范数据写入有界描述的方向；表证明内部使用的命题截断解码不会对外给出全局解码器或选定取值。
<!--ja-->
最後の行は `SatHolds.holds` を再利用して、表の連言項を与えます。上で証明したように、これが示すのは十個の節だけではなく、二つの領域条件と十個の構成子の節を含む `tableAt` 全体です。`satAt-in` がその結果を環境の塔と符号領域の連言項に組み合わせます。したがって `sat-complete` は、すでに整合された正準なデータを有界な記述に書き込む向きです。表の証明内部で用いる命題的に切り詰められた復号から、大域的な復号器や選ばれた値が外に取り出されることはありません。
<!--/-->

```agda
    (SatHolds.holds T w C E N γ W qw qT qC qE tg)
```
