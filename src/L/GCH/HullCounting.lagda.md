<!--en-->
Closing a small set under definable least witnesses should preserve an infinite cardinal bound. This chapter proves inside `L` that if the starting set injects into an infinite cardinal, then so does its Skolem hull.
<!--zh-->
把小集合对可定义的最小见证封闭，应当保持原有的无穷基数界。本章在 `L` 内部证明：若起始集合单射入一个无穷基数，则其 Skolem 壳也单射入该基数。
<!--ja-->
小さな集合を定義可能な最小の証人について閉じても、無限基数による上界は保たれるはずである。この章では、始集合が無限基数へ単射するなら、その Skolem 包も同じ基数へ単射することを `L` の内部で示す。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

```

<!--en-->
Excluded middle supplies local decisions such as whether a member of a union lies in its left summand. Classical reasoning enters through one explicit hypothesis, so the resulting bound records exactly that assumption.
<!--zh-->
排中律提供局部判定，例如并的一个成员是否属于左侧分支。经典推理只通过一条显式假设进入，因此所得的界准确记录这一假设。
<!--ja-->
排中律は、和集合の要素が左側に属するかどうかなどの局所的な判定を与える。古典的推論は一つの明示的な仮定として入り、得られる上界はその仮定を正確に記録する。
<!--/-->

```agda
open import Base.Prelude
open import Cubical.HITs.PropositionalTruncation using ( rec2 )
open import Cubical.Foundations.HLevels using ( isSetΣSndProp )
open import Cubical.Data.Nat using ( znots; snotz )
open import Base.Classical using ( LEM )

```

<!--en-->
Fix a universe level `ℓ` and excluded middle for propositions at level `ℓ-suc ℓ`. The internal sets, coded graphs, and truncated witnesses are all formed relative to this fixed instance.
<!--zh-->
固定宇宙层级 `ℓ`，并假设层级 `ℓ-suc ℓ` 上命题的排中律。内部集合、编码图与截断见证都相对于这个固定实例构造。
<!--ja-->
宇宙レベル `ℓ` と、レベル `ℓ-suc ℓ` の命題に対する排中律を固定する。内部集合、符号化されたグラフ、切り詰められた証人は、すべてこの固定した仮定のもとで構成される。
<!--/-->

```agda
module L.GCH.HullCounting {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

```

<!--en-->
Coded graphs are expressed in the first-order language of equality and membership. Conjunction, disjunction, negation, and existential quantification describe their cases, while satisfaction is interpreted over the ambient cumulative hierarchy.
<!--zh-->
编码图用带相等与隶属的一阶语言表示。合取、析取、否定与存在量化描述各个情形，而满足关系则在外围累积层级中解释。
<!--ja-->
符号化されたグラフは、等号と所属をもつ一階言語で表す。連言、選言、否定、存在量化によって場合を記述し、充足関係は周囲の累積階層で解釈する。
<!--/-->

```agda
open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax
  using ( Formula; var; con; _∈̇_; _≐_; _∧̇_; _∨̇_; ¬̇_; ∃̇_ )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
```

<!--en-->
The argument moves between ordinal stages and their constructible members. Transitivity keeps members inside `L`, while ordinal membership and stage cumulativity place each object in a stage large enough for definable selection.
<!--zh-->
论证在序数层与其中的可构造成员之间往返。传递性保证成员仍在 `L` 中，而序数隶属与层的累积性把每个对象放入足以进行可定义选择的层。
<!--ja-->
議論では順序数段階とその構成可能な要素との間を行き来する。推移性により要素も `L` にとどまり、順序数の所属と段階の累積性により、各対象を定義可能な選択に十分大きい段階へ入れられる。
<!--/-->

```agda
open import V.Coding {ℓ} using ( pr; pr-inj; #-inj )
open import L.Constructible {ℓ}
  using ( 𝒮ʟ; isL; isL-trans; IsOrd; Lset; Lset-mono; Lset-layer; layer-trans )
open import L.Ordinal {ℓ} using ( mem-ord; #∈ω )
open import L.Ordinal.Stages {ℓ} lem using ( Lset-cumul; ord∈Lset-suc )
```

<!--en-->
The counting maps must themselves be sets of `L`. Separation constructs subgraphs, pairing and union build their codes, and adequacy connects the internal formulas for application, single-valuedness, and domains with their set-theoretic meanings.
<!--zh-->
计数映射本身必须是 `L` 中的集合。分离构造子图，配对与并构成其编码，充分性则把应用、单值性与定义域的内部公式同其集合论含义连接起来。
<!--ja-->
数え上げに用いる写像は、それ自身が `L` の集合でなければならない。分出で部分グラフを作り、対と和集合で符号を構成し、妥当性によって適用、一価性、定義域の内部論理式を集合論的な意味と結びつける。
<!--/-->

```agda
open import L.Axioms.Basic {ℓ} using ( LsetS; ∅ʟ )
open import L.Axioms.Full {ℓ} lem using ( hasSeparationL )
open import L.Axioms.Infinity {ℓ} lem using ( ωʟ )
open import L.Axioms.Numerals {ℓ} using ( pairʟ; unionʟ )
open import L.Coding.Model {ℓ} using ( prAtL; prAtL-adequate; prʟ; prʟ-fst; appAt; appAt-adequate; svAt-out; domAt-in )
```

<!--en-->
An internal injection is witnessed by a constructible graph with exact domain, single-valuedness, injectivity, and a range bound. `InjCode` retains a particular graph, whereas `InjL` retains only the proposition that one exists.
<!--zh-->
内部单射由一个可构造图见证，并满足定义域准确、单值、单射和值域有界。`InjCode` 保留具体的图，而 `InjL` 只保留这种图存在这一命题。
<!--ja-->
内部の単射は、定義域が正確で、一価かつ単射的であり、値域に上界をもつ構成可能なグラフによって証される。`InjCode` は具体的なグラフを保ち、`InjL` はその存在命題だけを保つ。
<!--/-->

```agda
open import L.Coding.Expressions {ℓ} using ( numL; tagAtL; tagAtL-adequate )
open import L.Coding.CodeConstructibility {ℓ}
  using ( sglʟ; sglʟ-in; sglʟ-out; cupʟ; cupʟ-inl; cupʟ-inr; cupʟ-out )
open import L.Coding.Injection {ℓ} lem using ( injAt-out; module Extract )
open import L.Cardinal {ℓ} lem using ( InjCode; InjL )
```

<!--en-->
The counting proof composes internal injections. Definable maps turn formulas with unique values into constructible graphs, least-witness selection supplies such maps for Skolem closure, and the internal product provides room for tagged pairs.
<!--zh-->
计数证明复合内部单射。可定义映射把具有唯一值的公式变成可构造图，最小见证选择为 Skolem 封闭提供这种映射，内部乘积则容纳带标签的对。
<!--ja-->
数え上げの証明では内部の単射を合成する。定義可能な写像は一意な値をもつ論理式を構成可能なグラフにし、最小証人の選択は Skolem 閉包にそのような写像を与え、内部の積はタグ付きの対を収める。
<!--/-->

```agda
open import L.InjectionComposition {ℓ} lem using ( inclusion-coded; injl-trans )
open import L.DefinableInjection {ℓ} lem using ( DefinableMap; module Inj )
open import L.GCH.LeastWitnessMap {ℓ} lem using ( module Least )
open import L.GCH.CardinalSquareLaw {ℓ} lem using ( prodL; prodL-in; module Relation )
open import L.InjectionComposition {ℓ} lem using ( appC; appC-adequate )
```

<!--en-->
Least witnesses are selected inside a common constructible stage. Bounding ordinals collect the parameters there, superadequacy stabilizes satisfaction, and the satisfaction graph records the choices as a set of `L`.
<!--zh-->
最小见证在同一个可构造层内选取。界定序数把参数收集于其中，超充分性使满足关系稳定，满足图则把这些选择记录为 `L` 中的集合。
<!--ja-->
最小の証人は一つの共通する構成可能段階の中で選ぶ。有界順序数がパラメータをそこへ集め、強化された十分な段階であることが充足関係を安定させ、充足グラフが選択を `L` の集合として記録する。
<!--/-->

```agda
open import L.Stage {ℓ} lem using ( LeastOrd; isPropLeastOrd; leastOrd; stage; stage-ord; stage-mem )
open import L.Ordinal using ( boundingOrd )
open import L.Coding.EnvironmentSet {ℓ} lem using ( envSet; envSet-in )
open import L.GCH.AdequateStages {ℓ} lem using ( Superadequate )
open import L.Coding.SatisfactionGraphSet {ℓ} lem using ( module SatGraph )
```

<!--en-->
The Skolem hull is obtained by iterating least-witness closure from the starting set. Its constructible presentation supplies stage bounds for selection, while condensation identifies the hull with the corresponding constructible structure.
<!--zh-->
Skolem 壳由起始集合反复施行最小见证封闭而得到。它的可构造呈现提供选择所需的层界，而凝聚把该壳认同为相应的可构造结构。
<!--ja-->
Skolem 包は、始集合から最小証人による閉包を反復して得られる。その構成可能な提示が選択に必要な段階の上界を与え、凝縮が包を対応する構成可能構造と同一視する。
<!--/-->

```agda
open import L.GCH.SkolemHull {ℓ} lem using ( module Frame; module HullStage )
open import L.GCH.ConstructibleHull {ℓ} lem using ( module Condense′; module Telescope )
open import L.GCH.StageCountingTools {ℓ} lem
  using ( isPropInjCode; injcode-resp; injFo; module InjFo; pinAt; pin-in; pin-out; seq-map; Lω
        ; limit-stage-counted )
```

<!--en-->
Each closure step is indexed by a formula code and a finite parameter sequence. Formula shapes are countable, finite sequences over an infinite cardinal are bounded by the square law, and well-founded induction supplies that law for the internal cardinals in the count.
<!--zh-->
每一步封闭都由公式码和有限参数序列索引。公式形状是可数的，无穷基数上的有限序列由平方律给出界，良基归纳则为计数中的内部基数提供这条平方律。
<!--ja-->
各閉包段階は論理式の符号と有限なパラメータ列で添字づけられる。論理式の形は可算であり、無限基数上の有限列は平方則で抑えられ、整礎帰納法が数え上げに現れる内部基数についてその平方則を与える。
<!--/-->

```agda
open import L.GCH.FiniteSequenceCoding {ℓ} lem using ( seqL; seqL-in; seq-count )
open import L.GCH.CardinalSquareLaw {ℓ} lem using ( prod-inj; ω⊆; Goal; module Step )
open import L.Cardinal {ℓ} lem using ( IsCardinalL )
open import V.Hierarchy {ℓ} using ( regularityV )
import Cubical.Induction.WellFounded as WF
```

<!--en-->
When both arguments of a graph are identified by equalities, two-place transport moves a graph-membership proof across both identifications at once. Thus equality replacement remains compatible with the coded relation.
<!--zh-->
当图的两个参数都由等式认同时，二元搬运可同时沿两条等式移动图的隶属证明。因此，等式替换与编码关系保持相容。
<!--ja-->
グラフの二つの引数がそれぞれ等しさで同一視されるとき、二項の移送によってグラフへの所属証明を両方の同一視に沿って一度に移せる。したがって等しさによる置換は符号化された関係と両立する。
<!--/-->

```agda

```

<!--en-->
The tags `0` and `1` are distinct, making the two branches of a tagged injection disjoint. Equality of dependent pairs with proposition-valued fibers reduces to equality of their first components, so constructibility proofs do not affect the count.
<!--zh-->
标签 `0` 与 `1` 不同，因此带标签单射的两个分支互不相交。第二分量为命题的依值对之相等归结为第一分量相等，所以可构造性证明不影响计数。
<!--ja-->
タグ `0` と `1` は異なるので、タグ付き単射の二つの分岐は交わらない。命題値のファイバーをもつ依存対の等しさは第一成分の等しさに帰着するため、構成可能性の証明は数え上げに影響しない。
<!--/-->

```agda
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_; setIsSet )
```

<!--en-->
Von Neumann numerals provide the tags, `ω` collects them, and successor describes their finite progression. The empty set serves as the value of a singleton injection, while propositional truncation records existence without choosing a representative.
<!--zh-->
von Neumann 数码提供标签，`ω` 收集这些数码，后继描述其有限递进。空集充当单点集单射的取值，而命题截断记录存在性却不选择代表。
<!--ja-->
von Neumann 数項をタグに用い、`ω` がそれらを集め、後続が有限な進み方を表す。空集合は単元集合からの単射の値となり、命題的切り詰めは代表を選ばずに存在を記録する。
<!--/-->

```agda
open import Cubical.HITs.CumulativeHierarchy.Constructions using ( module InfinitySet )
open InfinitySet {ℓ} using ( #_; ω; sucV )
open import Cubical.HITs.CumulativeHierarchy.Constructions using ( ∅ )
```

<!--en-->
Existence of a coded injection is propositionally truncated because the count depends only on whether a witnessing graph exists. Elimination is therefore made only into propositions, preserving independence from the choice of graph.
<!--zh-->
编码单射的存在性经过命题截断，因为计数只依赖见证图是否存在。因此截断只消去到命题中，使结果不依赖所选的图。
<!--ja-->
符号化された単射の存在は命題的に切り詰められる。数え上げに必要なのは証人となるグラフの存在だけだからである。したがって除去は命題に対してのみ行い、結果がグラフの選び方に依存しないようにする。
<!--/-->

```agda

```

<!--en-->
For ambient sets, `x ∈ˢ y` is the proposition that `x` belongs to `y`. The domain and range clauses of coded functions ultimately reduce to this relation on underlying sets.
<!--zh-->
对外围集合而言，`x ∈ˢ y` 是 `x` 属于 `y` 这一命题。编码函数的定义域和值域条件最终都归结为底层集合上的这一关系。
<!--ja-->
周囲の集合について、`x ∈ˢ y` は `x` が `y` に属するという命題である。符号化された関数の定義域と値域の条件は、最終的に底集合上のこの関係へ帰着する。
<!--/-->

```agda
open hPropStructure 𝒮ᵥ using ( _∈ˢ_ )

```

<!--en-->
Write `S` for the carrier of the constructible model. Its elements are ambient sets paired with proofs of membership in `L`; since those proofs are propositions, the underlying set determines the constructible element up to equality.
<!--zh-->
以 `S` 表示可构造模型的载体。其元素由外围集合及其属于 `L` 的证明组成；由于这些证明是命题，底层集合在相等意义下唯一确定可构造元素。
<!--ja-->
構成可能モデルの台を `S` と書く。その要素は周囲の集合と、それが `L` に属することの証明との対である。この証明は命題なので、底集合が構成可能な要素を等しさまで一意に定める。
<!--/-->

```agda
module SL = hPropStructure 𝒮ʟ using ( S )
open SL using ( S )

```

<!--en-->
A formula with constructible constants can be evaluated inside `L` and projected to the ambient hierarchy. Transitivity makes the two readings agree, so an internally proved graph statement can be used as ordinary membership between underlying sets.
<!--zh-->
带可构造常元的公式可以在 `L` 内部求值，也可以投影到外围层级。传递性使两种读法一致，因此内部证明的图陈述可作为底层集合之间的普通隶属来使用。
<!--ja-->
構成可能な定数をもつ論理式は `L` の内部で評価でき、周囲の階層へも射影できる。推移性により二つの読み方は一致するので、内部で証明したグラフの主張を底集合間の通常の所属として使える。
<!--/-->

```agda
module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans using ( _^_; _⊨ᵐ_ )
open AbsL using ( _^_ ) renaming ( _⊨ᵐ_ to _⊨_ )
```

<!--en-->
`Holds F x y` means that the ordered pair of the underlying sets of `x` and `y` belongs to the underlying graph `F`. This is the ambient relation represented by every coded application formula in the argument.
<!--zh-->
`Holds F x y` 表示 `x` 与 `y` 的底层集合组成的有序对属于底层图 `F`。这就是论证中每个编码应用公式所表示的外围关系。
<!--ja-->
`Holds F x y` は、`x` と `y` の底集合の順序対が底のグラフ `F` に属することを意味する。これは、議論に現れる各符号化された適用論理式が表す周囲の関係である。
<!--/-->

```agda
Holds : S → S → S → Type (ℓ-suc ℓ)
Holds F x y = ⟨ pr (fst x) (fst y) ∈ fst F ⟩
```

<!--en-->
The element `nn k : S` is the ambient von Neumann numeral `# k` together with its constructibility proof. In particular, `nn 0` and `nn 1` serve as internal tags without leaving `L`.
<!--zh-->
元素 `nn k : S` 由外围的 von Neumann 数码 `# k` 及其可构造性证明组成。特别地，`nn 0` 与 `nn 1` 充当内部标签而不离开 `L`。
<!--ja-->
要素 `nn k : S` は、周囲の von Neumann 数項 `# k` とその構成可能性の証明との対である。とくに `nn 0` と `nn 1` は、`L` の外へ出ることなく内部のタグとして働く。
<!--/-->

```agda
nn : ℕ → S
nn k = # k , numL k

```

<!--en-->
If two elements of `S` have equal underlying sets, then the elements themselves are equal. The second components contain only constructibility proofs, so proof irrelevance lifts equality of the first components to equality of the dependent pairs.
<!--zh-->
若 `S` 的两个元素具有相等的底层集合，则这两个元素本身相等。第二分量只包含可构造性证明，故证明无关性把第一分量的等式提升为依值对的等式。
<!--ja-->
`S` の二つの要素の底集合が等しければ、要素そのものも等しくなる。第二成分は構成可能性の証明だけなので、証明無関係性によって第一成分の等しさを依存対の等しさへ持ち上げられる。
<!--/-->

```agda
S≡ : {x y : S} → fst x ≡ fst y → x ≡ y
S≡ = Σ≡Prop (λ v → snd (isL v))

```

<!--en-->
The carrier `S` is an h-set. Its first component lies in the cumulative hierarchy, which is an h-set, and each fiber of constructibility proofs is a proposition; hence every equality type in `S` is a proposition.
<!--zh-->
载体 `S` 是 h-集合。其第一分量位于本身为 h-集合的累积层级中，而每个可构造性证明纤维都是命题；因此 `S` 中的每个等式类型都是命题。
<!--ja-->
台 `S` は h-集合である。第一成分が属する累積階層は h-集合であり、構成可能性の証明からなる各ファイバーは命題なので、`S` のすべての等式型は命題になる。
<!--/-->

```agda
isSetS : isSet S
isSetS = isSetΣSndProp setIsSet (λ v → snd (isL v))

```

<!--en-->
De Bruijn indices for the first two variable slots are named, since the coded formulas of this chapter never mention more than eight slots at once.
<!--zh-->
前两个变元槽的 De Bruijn 索引被命名，因为本章的编码公式一次至多涉及八个槽位。
<!--ja-->
最初の二つの変数の枠の De Bruijn 索引に名前が付けられる。この章の符号化された論理式は、一度に多くとも八つの枠しか扱わないからである。
<!--/-->

```agda
private
  i0 : ∀ {k} → Fin (suc k)
  i0 = zero
  i1 : ∀ {k} → Fin (suc (suc k))
  i1 = suc i0
```

<!--en-->
The names `i2`, `i3`, and `i4` denote variable positions two, three, and four. Each is one successor beyond the preceding index, with a polymorphic tail `k` keeping the position valid when more variables are available.
<!--zh-->
名称 `i2`、`i3` 与 `i4` 分别表示第二、第三与第四变元位置。每个索引都是前一个索引的后继，多态的尾长 `k` 保证在还有更多可用变元时该位置仍然有效。
<!--ja-->
`i2`、`i3`、`i4` は、それぞれ変数位置 2、3、4 を表す。各添字は直前の添字の後続であり、多相的な末尾の長さ `k` によって、さらに変数が利用できる場合にもその位置が有効に保たれる。
<!--/-->

```agda
  i2 : ∀ {k} → Fin (suc (suc (suc k)))
  i2 = suc i1
  i3 : ∀ {k} → Fin (suc (suc (suc (suc k))))
  i3 = suc i2
  i4 : ∀ {k} → Fin (suc (suc (suc (suc (suc k)))))
```

<!--en-->
After the defining equation for `i4`, the same successor pattern defines positions five and six. These names make the shifts caused by nested binders visible in the types of coded formulas.
<!--zh-->
在补上 `i4` 的定义等式后，同样的后继模式定义第五与第六位置。这些名称使嵌套绑定造成的位移在编码公式的类型中清晰可见。
<!--ja-->
`i4` の定義式を与えた後、同じ後続のパターンで位置 5 と 6 を定める。これらの名前により、入れ子になった束縛子が生む位置のずれを符号化された論理式の型で確認できる。
<!--/-->

```agda
  i4 = suc i3
  i5 : ∀ {k} → Fin (suc (suc (suc (suc (suc (suc k))))))
  i5 = suc i4
  i6 : ∀ {k} → Fin (suc (suc (suc (suc (suc (suc (suc k)))))))
  i6 = suc i5
```

<!--en-->
Slot seven is the last, and the eight indices cover every variable position used in this chapter.
<!--zh-->
第七槽是最后一个；这八个索引覆盖本章用到的每个变元位置。
<!--ja-->
第七の枠が最後であり、この八つの索引が本章で使うすべての変数の位置を覆う。
<!--/-->

```agda
  i7 : ∀ {k} → Fin (suc (suc (suc (suc (suc (suc (suc (suc k))))))))
  i7 = suc i6
```

<!--en-->
An ordinal is contained in its own stage: each member of an ordinal is itself an ordinal, and the cumulative construction places every member of the ordinal into the stage indexed by that ordinal.
<!--zh-->
序数包含于其自身的层：序数的每个成员自身是序数，而累积构造把序数的每个成员放进该序数所索引的层。
<!--ja-->
順序数はその自身の段階に含まれる。順序数の各要素はそれ自身順序数であり、累積的な構成が、順序数のすべての要素をその順序数が索引づける段階の中に置く。
<!--/-->

```agda
ord⊆Lset : (α : V ℓ) → IsOrd α → (z : V ℓ) → ⟨ z ∈ α ⟩ → ⟨ z ∈ Lset α ⟩
ord⊆Lset α oα z z∈α =
  Lset-cumul z α oz oα z∈α (ord∈Lset-suc z oz)
  where
  oz : IsOrd z
```

<!--en-->
Since `z ∈ α` and `α` is an ordinal, `z` is itself an ordinal. This places `z` in its successor stage; cumulativity along `z ∈ α` then gives `z ∈ Lset α`.
<!--zh-->
由于 `z ∈ α` 且 `α` 是序数，`z` 本身也是序数。这使 `z` 属于其后继层；再沿 `z ∈ α` 使用累积性，便得到 `z ∈ Lset α`。
<!--ja-->
`z ∈ α` であり `α` が順序数なので、`z` 自身も順序数である。これにより `z` はその後続段階に属し、さらに `z ∈ α` に沿って累積性を用いると `z ∈ Lset α` が得られる。
<!--/-->

```agda
  oz = mem-ord {A = α} oα z z∈α
```

<!--en-->
Fix constructible sets `D₁` and `D₂`. Their internal binary union is the common domain for combining two injections; its membership principle gives both inclusions and a truncated case split.
<!--zh-->
固定可构造集合 `D₁` 与 `D₂`。它们的内部二元并是合并两个单射时的共同定义域；其隶属原理给出两条包含和一个截断的情形拆分。
<!--ja-->
構成可能集合 `D₁` と `D₂` を固定する。それらの内部の二項和集合は二つの単射をまとめる共通の定義域であり、その所属原理から二つの包含と切り詰められた場合分けが得られる。
<!--/-->

```agda
module Union2 (D₁ D₂ : S) where

```

<!--en-->
The union is the internal union of the two sets.
<!--zh-->
该并即两个集合的内部并。
<!--ja-->
この和は、二つの集合の内部の和である。
<!--/-->

```agda
  D : S
  D = cupʟ D₁ D₂

```

<!--en-->
Left members are included by the left rule of the union.
<!--zh-->
左侧的成员由并的左规则包含进来。
<!--ja-->
左側の要素は、和の左の規則によって含められる。
<!--/-->

```agda
  in₁ : (z : S) → ⟨ fst z ∈ fst D₁ ⟩ → ⟨ fst z ∈ fst D ⟩
  in₁ z = cupʟ-inl D₁ D₂ (fst z)

```

<!--en-->
Right members are included symmetrically.
<!--zh-->
右侧的成员对称地包含进来。
<!--ja-->
右側の要素は対称的に含められる。
<!--/-->

```agda
  in₂ : (z : S) → ⟨ fst z ∈ fst D₂ ⟩ → ⟨ fst z ∈ fst D ⟩
  in₂ z = cupʟ-inr D₁ D₂ (fst z)

```

<!--en-->
If `z ∈ D₁ ∪ D₂`, then it merely belongs to the left side or the right side. The disjunction is propositionally truncated because membership retains that some presentation index names `z`, but not which index supplied it.
<!--zh-->
若 `z ∈ D₁ ∪ D₂`，则仅能断言它属于左侧或右侧。这个析取经过命题截断，因为隶属关系保留某个呈现索引指名 `z` 这一事实，却不保留具体索引。
<!--ja-->
`z ∈ D₁ ∪ D₂` なら、`z` が左側または右側に属することだけが得られる。この選言は命題的に切り詰められている。所属は、ある提示添字が `z` を名指すことを保つが、具体的な添字は保たないからである。
<!--/-->

```agda
  out : (z : S) → ⟨ fst z ∈ fst D ⟩ → ∥ ⟨ fst z ∈ fst D₁ ⟩ ⊎ ⟨ fst z ∈ fst D₂ ⟩ ∥₁
  out z = cupʟ-out D₁ D₂ (fst z)
```

<!--en-->
Let `κ` be a constructible set containing the tags `0` and `1`, and let `E₁` and `E₂` code injections from `D₁` and `D₂` into `κ`. Tagging their values combines them into an injection from `D₁ ∪ D₂` into `κ × κ`. This construction requires no ordinal hypothesis on `κ`.
<!--zh-->
令 `κ` 为包含标签 `0` 与 `1` 的可构造集合，并令 `E₁`、`E₂` 分别编码从 `D₁`、`D₂` 到 `κ` 的单射。给取值加标签，便把它们合成从 `D₁ ∪ D₂` 到 `κ × κ` 的单射。此构造不要求 `κ` 是序数。
<!--ja-->
`κ` をタグ `0` と `1` を含む構成可能集合とし、`E₁` と `E₂` がそれぞれ `D₁` と `D₂` から `κ` への単射を符号化するとする。値にタグを付けると、`D₁ ∪ D₂` から `κ × κ` への一つの単射にまとめられる。この構成では `κ` が順序数である必要はない。
<!--/-->

```agda
module TagUnion (κ : S) (0∈κ : ⟨ # 0 ∈ fst κ ⟩) (1∈κ : ⟨ # 1 ∈ fst κ ⟩)
                (D₁ D₂ E₁ E₂ : S) (c₁ : InjCode E₁ D₁ κ) (c₂ : InjCode E₂ D₂ κ) where

```

<!--en-->
Write `D = D₁ ∪ D₂`. A member of either summand belongs to `D`, and every member of `D` yields a truncated proof that it comes from one of the two summands.
<!--zh-->
记 `D = D₁ ∪ D₂`。任一分支的成员都属于 `D`，而 `D` 的每个成员都给出一条截断证明，说明它来自两个分支之一。
<!--ja-->
`D = D₁ ∪ D₂` と書く。どちらか一方の集合の要素は `D` に属し、`D` の各要素からは、二つの集合のいずれかに由来するという切り詰められた証明が得られる。
<!--/-->

```agda
  open Union2 D₁ D₂ public using ( D; in₁; in₂; out )

```

<!--en-->
Each coded injection extracts its underlying function together with the proof that its graph holds exactly when the coding says so.
<!--zh-->
每个编码单射都提取出其底层函数，连同「图恰好按编码所说成立」的证明。
<!--ja-->
それぞれの符号化された単射は、その底にある関数と、グラフが符号化の言う通りにちょうど成立する証明を抽出する。
<!--/-->

```agda
  module X₁ = Extract E₁ D₁ (fst c₁) (fst (snd c₁)) using ( toFun; toFun-graph )
  module X₂ = Extract E₂ D₂ (fst c₂) (fst (snd c₂)) using ( toFun; toFun-graph )

```

<!--en-->
`Mem z` is the proposition that `z` belongs to the union domain `D`. Carrying this proof with an input supplies exactly the domain evidence needed to evaluate the piecewise function.
<!--zh-->
`Mem z` 是 `z` 属于并定义域 `D` 这一命题。输入连同这条证明，恰好提供分段函数求值所需的定义域证据。
<!--ja-->
`Mem z` は `z` が和集合の定義域 `D` に属するという命題である。入力にこの証明を添えることで、場合分けされた関数を評価するために必要な定義域の証拠がちょうど得られる。
<!--/-->

```agda
  Mem : S → Type (ℓ-suc ℓ)
  Mem z = ⟨ fst z ∈ fst D ⟩

```

<!--en-->
Membership in the left domain is decidable by excluded middle, and the decision is the case split the tagged injection is built on.
<!--zh-->
属于左定义域可由排中律判定，这一判定正是构造带标签单射所依赖的情形拆分。
<!--ja-->
左の定義域への所属は排中律で判定でき、この判定こそ、タグ付きの単射を作るための場合分けである。
<!--/-->

```agda
  Case : S → Type (ℓ-suc ℓ)
  Case z = Dec ⟨ fst z ∈ fst D₁ ⟩

```

<!--en-->
Excluded middle decides, for every member of the union, whether it came from the left domain.
<!--zh-->
排中律对并的每个成员判定其是否来自左定义域。
<!--ja-->
排中律は、和のすべての要素が左の定義域から来たかどうかを判定する。
<!--/-->

```agda
  decide : (z : S) → Case z
  decide z = lem (fst z ∈ fst D₁)

```

<!--en-->
A member outside the left domain must lie in the right domain: the union membership splits into the two sides, and the left side contradicts the assumed failure.
<!--zh-->
不在左定义域的成员必在右定义域：并中的隶属拆成两侧，而左侧与所设的失败矛盾。
<!--ja-->
左の定義域に属さない要素は、右の定義域に属する。和の中の所属は二つの側に分かれ、左側は仮定された失敗と矛盾する。
<!--/-->

```agda
  off : (z : S) → Mem z → (⟨ fst z ∈ fst D₁ ⟩ → ⊥₀) → ⟨ fst z ∈ fst D₂ ⟩
  off z m nmem = rec₁ (snd (fst z ∈ fst D₂))
    (λ { (inl h) → ⊥₀-rec (nmem h) ; (inr h) → h }) (out z m)

```

<!--en-->
The value on each side is the tagged image: the numeral tag zero or one paired with the extracted function value, so the two injections land in disjoint tagged ranges.
<!--zh-->
两侧的取值都是带标签的像：数码标签零或一与提取出的函数值配对，使两个单射落入不相交的带标签值域。
<!--ja-->
それぞれの側の値はタグ付きの像である。数項のタグ 0 か 1 を、抽出された関数の値と対にする。こうして二つの単射は、重ならないタグ付きの値域に着地する。
<!--/-->

```agda
  val : (z : S) → Mem z → Case z → S
  val z m (yes h) = prʟ (nn 0) (X₁.toFun (z , h))
  val z m (no nmem) = prʟ (nn 1) (X₂.toFun (z , off z m nmem))

```

<!--en-->
For `z ∈ D`, the function `fn` decides whether `z ∈ D₁`. It returns `(0,E₁(z))` in the left case and `(1,E₂(z))` in the complementary right case.
<!--zh-->
对 `z ∈ D`，函数 `fn` 判定 `z ∈ D₁` 是否成立。左侧情形返回 `(0,E₁(z))`，互补的右侧情形返回 `(1,E₂(z))`。
<!--ja-->
`z ∈ D` に対し、関数 `fn` は `z ∈ D₁` かどうかを判定する。左の場合は `(0,E₁(z))` を返し、補集合にあたる右の場合は `(1,E₂(z))` を返す。
<!--/-->

```agda
  fn : (z : S) → Mem z → S
  fn z m = val z m (decide z)
```

<!--en-->
The ambient meaning `Wit y z` has two branches. In the left branch, `z ∈ D₁`, and there merely exists `v` with `(z,v) ∈ E₁` such that the underlying set of `y` is `(0,v)`.
<!--zh-->
外围含义 `Wit y z` 分成两个分支。左分支要求 `z ∈ D₁`，并且仅仅存在满足 `(z,v) ∈ E₁` 的 `v`，使 `y` 的底层集合等于 `(0,v)`。
<!--ja-->
周囲での意味 `Wit y z` には二つの分岐がある。左の分岐では `z ∈ D₁` であり、`(z,v) ∈ E₁` を満たす `v` が単に存在して、`y` の底集合が `(0,v)` に等しくなる。
<!--/-->

```agda
  Wit : (y z : S) → Type (ℓ-suc ℓ)
  Wit y z =
      (⟨ fst z ∈ fst D₁ ⟩
        × ∥ Σ[ v ∈ S ] (Holds E₁ z v × (fst y ≡ pr (# 0) (fst v))) ∥₁)
    ⊎ ((⟨ fst z ∈ fst D₁ ⟩ → ⊥₀)
```

<!--en-->
In the right branch, `z ∉ D₁`, and there merely exists `v` with `(z,v) ∈ E₂` such that `y = (1,v)` on underlying sets. The distinct tags rule out equality between outputs from opposite branches.
<!--zh-->
右分支要求 `z ∉ D₁`，并且仅仅存在满足 `(z,v) ∈ E₂` 的 `v`，使底层集合意义下 `y = (1,v)`。两个不同标签排除了相异分支输出相等的可能。
<!--ja-->
右の分岐では `z ∉ D₁` であり、`(z,v) ∈ E₂` を満たす `v` が単に存在して、底集合について `y = (1,v)` となる。異なるタグにより、別々の分岐から得た出力が等しくなることはない。
<!--/-->

```agda
        × ∥ Σ[ v ∈ S ] (Holds E₂ z v × (fst y ≡ pr (# 1) (fst v))) ∥₁)

```

<!--en-->
The graph is written as a two-slot formula: membership in `D₁` conjoined with an existential over the first code, or the negation of that membership conjoined with an existential over the second code. Inside the existential, the injected value and the tag equation are atoms of the coding.
<!--zh-->
图写作二空位公式：属于 `D₁` 与对第一个码的存在量化合取，或该隶属的否定与对第二个码的存在量化合取。存在量词之内，被单射的值与标签等式都是编码的原子。
<!--ja-->
グラフは二つの枠をもつ論理式として書かれる。`D₁` への所属と最初の符号の上の存在量化の連言、あるいはその所属の否定と第二の符号の上の存在量化の連言である。存在量化子の内側では、単射された値とタグの等式が符号化のアトムである。
<!--/-->

```agda
  opaque
    fo : Formula S 2
    fo = ((var i1 ∈̇ con D₁) ∧̇ ∃̇ (appC E₁ i2 i0 ∧̇ tagAtL i1 0 i0))
       ∨̇ ((¬̇ (var i1 ∈̇ con D₁)) ∧̇ ∃̇ (appC E₂ i2 i0 ∧̇ tagAtL i1 1 i0))

```

<!--en-->
Reading the two coding atoms uses their adequacy lemmas: satisfaction of the application atom becomes a membership `Holds E z v`, and satisfaction of the tag atom becomes the equation between `y` and the tagged pair.
<!--zh-->
读取两个编码原子使用其充分性引理：应用原子的满足变成隶属 `Holds E z v`，标记原子的满足变成 `y` 与带标签对的等式。
<!--ja-->
二つの符号化のアトムを読むには、その妥当性の補題を使う。適用のアトムの充足は所属 `Holds E z v` になり、タグのアトムの充足は、`y` とタグ付きの対との等式になる。
<!--/-->

```agda
    private
      rd : (E : S) (k : ℕ) (y z v : S)
         → ⟨ (v ∷ y ∷ z ∷ []) ⊨ appC E i2 i0 ⟩ → ⟨ (v ∷ y ∷ z ∷ []) ⊨ tagAtL i1 k i0 ⟩
         → Holds E z v × (fst y ≡ pr (# k) (fst v))
      rd E k y z v ha ht =
```

<!--en-->
After transport along the two adequacy equivalences, the satisfaction witnesses become the components required by `Wit`: graph membership `Holds E z v` and the equality identifying `y` with the pair tagged by `k`.
<!--zh-->
沿两条充分性等价搬运后，满足见证恰好变成 `Wit` 所需的分量：图隶属 `Holds E z v`，以及把 `y` 认同为带标签 `k` 之对的等式。
<!--ja-->
二つの妥当性の同値に沿って移送すると、充足の証人は `Wit` が要求する成分、すなわちグラフ所属 `Holds E z v` と、`y` をタグ `k` の付いた対と同一視する等しさになる。
<!--/-->

```agda
          subst ⟨_⟩ (appC-adequate E i2 i0 (v ∷ y ∷ z ∷ [])) ha
        , subst ⟨_⟩ (tagAtL-adequate i1 k i0 (v ∷ y ∷ z ∷ [])) ht

```

<!--en-->
Conversely, from `Holds E z v` and the underlying equality `y = (k,v)`, transport backward along adequacy produces satisfaction of the application atom.
<!--zh-->
反过来，由 `Holds E z v` 与底层等式 `y = (k,v)`，沿充分性反向搬运便得到应用原子的满足。
<!--ja-->
逆に、`Holds E z v` と底集合についての等しさ `y = (k,v)` から、妥当性に沿って逆向きに移送すると適用の原子式の充足が得られる。
<!--/-->

```agda
      wr : (E : S) (k : ℕ) (y z v : S)
         → Holds E z v → fst y ≡ pr (# k) (fst v)
         → ⟨ (v ∷ y ∷ z ∷ []) ⊨ appC E i2 i0 ⟩ × ⟨ (v ∷ y ∷ z ∷ []) ⊨ tagAtL i1 k i0 ⟩
      wr E k y z v ha ht =
          subst ⟨_⟩ (sym (appC-adequate E i2 i0 (v ∷ y ∷ z ∷ []))) ha
```

<!--en-->
The same backward transport turns the tagged-pair equality into satisfaction of the tag atom. Together the two proofs reconstruct the conjunction under the existential quantifier.
<!--zh-->
同样的反向搬运把带标签对的等式变成标签原子的满足。两条证明合在一起，便重建存在量词之下的合取。
<!--ja-->
同じ逆向きの移送により、タグ付き対の等しさはタグ原子式の充足になる。二つの証明を合わせると、存在量化子のもとにある連言が再構成される。
<!--/-->

```agda
        , subst ⟨_⟩ (sym (tagAtL-adequate i1 k i0 (v ∷ y ∷ z ∷ []))) ht

```

<!--en-->
Reading a satisfaction proof of `fo` proceeds by its two disjuncts. The left yields `z ∈ D₁` and a truncated `E₁` witness tagged by zero; the right yields `z ∉ D₁` and the corresponding `E₂` witness tagged by one. Applying `rd` inside each truncation gives a truncated inhabitant of `Wit y z`.
<!--zh-->
读取 `fo` 的满足证明时按两个析取支分类。左支给出 `z ∈ D₁` 和带零标签的截断 `E₁` 见证；右支给出 `z ∉ D₁` 和带一标签的相应 `E₂` 见证。在每个截断内部应用 `rd`，便得到 `Wit y z` 的截断元素。
<!--ja-->
`fo` の充足証明は二つの選言肢に分けて読む。左からは `z ∈ D₁` と 0 のタグが付いた切り詰められた `E₁` の証人が得られ、右からは `z ∉ D₁` と 1 のタグが付いた対応する `E₂` の証人が得られる。各切り詰めの内側で `rd` を適用すると、`Wit y z` の切り詰められた要素が得られる。
<!--/-->

```agda
    fo-out : (y z : S) → ⟨ (y ∷ z ∷ []) ⊨ fo ⟩ → ∥ Wit y z ∥₁
    fo-out y z = map₁
      (λ { (inl (h , hv)) → inl (h , map₁ (λ { (v , (ha , ht)) → v , rd E₁ 0 y z v ha ht }) hv)
         ; (inr (h , hv)) → inr ((λ z∈ → lower (h z∈))
             , map₁ (λ { (v , (ha , ht)) → v , rd E₂ 1 y z v ha ht }) hv) })
```

<!--en-->
The inward reading of the graph turns the host-side witness into satisfaction, case by case. In the left case the membership and the truncated entry are transported through the adequacy equations of the application and tag codings; the right case does the same after lifting the refutation of membership into the object-language negation.
<!--zh-->
图的向内读法逐情形把宿主侧见证转成满足。左支中，隶属与截断条目沿应用编码与标签编码的充分性等式运输；右支先把「不属于 `D₁`」的反驳提升为对象语言否定，再做同样处理。
<!--ja-->
グラフの内向きの読み出しは、ホスト側の証人を場合ごとに充足へ変える。左の場合は、所属と切り詰められた項目を、適用とタグの符号化の妥当性の等式に沿って運び、右の場合は、所属しないことの反駁を対象言語の否定へ持ち上げてから同じことをする。
<!--/-->

```agda

    fo-in : (y z : S) → Wit y z → ⟨ (y ∷ z ∷ []) ⊨ fo ⟩
    fo-in y z (inl (h , hv)) =
      ∣ inl (h , map₁ (λ { (v , (ha , ht)) → v , wr E₁ 0 y z v ha ht }) hv) ∣₁
    fo-in y z (inr (h , hv)) =
      ∣ inr ((λ z∈ → lift (h z∈))
```

<!--en-->
The tail of the right case completes the second disjunct: the entry of `E₂` is transported exactly as in the left, with the tag `1` in place of `0`. Both disjuncts are then injected into the truncated existence, and the introduction is finished.
<!--zh-->
右支的末项完成第二个析取支：`E₂` 的条目按左支同样方式运输，只是标签由 `0` 换成 `1`。两个析取支随后被注入截断存在，引入完毕。
<!--ja-->
右の場合の残りが第二の選言肢を完成させる。`E₂` の項目は、タグを `0` から `1` に替えるだけで左と同じように運ばれる。二つの選言肢は切り詰められた存在へ注入され、導入は終わりである。
<!--/-->

```agda
          , map₁ (λ { (v , (ha , ht)) → v , wr E₂ 1 y z v ha ht }) hv) ∣₁

```

<!--en-->
Each coded relation is single-valued: two entries with the same first component have the same second component. This is the first conjunct of the injection code, read out through the adequacy of the application coding.
<!--zh-->
每条被编码关系都是单值的：第一分量相同的两条目第二分量相同。这是注入码的第一个合取项，经应用编码的充分性读出。
<!--ja-->
符号化されたそれぞれの関係は一価である。第一成分を共有する項目は第二成分も共有する。これが注入の符号の最初の連言項で、適用の符号化の妥当性を通して読み出される。
<!--/-->

```agda
  private
    sv₁ : (x y y' : S) → Holds E₁ x y → Holds E₁ x y' → fst y ≡ fst y'
    sv₁ = svAt-out zero (E₁ ∷ D₁ ∷ []) (fst c₁)
    sv₂ : (x y y' : S) → Holds E₂ x y → Holds E₂ x y' → fst y ≡ fst y'
    sv₂ = svAt-out zero (E₂ ∷ D₂ ∷ []) (fst c₂)
```

<!--en-->
Each coded relation is also injective: two entries with the same second component have first components with equal underlying sets. The range clause begins the list: every value of the relation lies in the cardinal.
<!--zh-->
每条被编码关系还是单射的：第二分量相同的两条目，其第一分量的底层集合相等。范围子句开始列出：关系的每个取值都落在基数之中。
<!--ja-->
符号化された関係はさらに単射でもある。第二成分を共有する項目は、第一成分の基礎の集合が等しくなる。範囲の条項はここからはじまり、関係のどの値も基数の中にあると述べる。
<!--/-->

```agda
    ij₁ : (y x x' : S) → Holds E₁ x y → Holds E₁ x' y → fst x ≡ fst x'
    ij₁ = injAt-out zero (E₁ ∷ D₁ ∷ []) (fst (snd (snd c₁)))
    ij₂ : (y x x' : S) → Holds E₂ x y → Holds E₂ x' y → fst x ≡ fst x'
    ij₂ = injAt-out zero (E₂ ∷ D₂ ∷ []) (fst (snd (snd c₂)))
    ran₁ : (x y : S) → Holds E₁ x y → ⟨ fst y ∈ fst κ ⟩
```

<!--en-->
The second range clause completes the data extracted from the two injection codes. For each relation we now have single-valuedness, injectivity, and the fact that every value lies in `κ`; these are the properties used to build the tagged map.
<!--zh-->
第二条范围子句补全了从两份注入码读出的资料。对每条关系，我们现在都有单值性、单射性以及每个取值都属于 `κ`；构造带标签映射所用的正是这些性质。
<!--ja-->
二つ目の値域条件により、二つの単射符号から読み出すデータがそろう。各関係について一価性、単射性、そしてすべての値が `κ` に属することが得られ、タグ付き写像はこれらの性質から構成される。
<!--/-->

```agda
    ran₁ = snd (snd (snd c₁))
    ran₂ : (x y : S) → Holds E₂ x y → ⟨ fst y ∈ fst κ ⟩
    ran₂ = snd (snd (snd c₂))

```

<!--en-->
The witness is constructed from the two cases for a member. If `z ∈ D₁`, its value uses the function extracted from `E₁`; otherwise it uses the function extracted from `E₂` at the resulting member of `D₂`. In either case the extraction supplies both the graph entry and the equation identifying the tagged pair with the chosen value.
<!--zh-->
见证按成员的两种情形构造。若 `z ∈ D₁`，取值使用从 `E₁` 提取的函数；否则，先得到 `z ∈ D₂`，再使用从 `E₂` 提取的函数。两种情形中，提取过程都同时给出图条目，以及把带标签的对认同为所选取值的等式。
<!--ja-->
証人は要素についての二つの場合から構成する。`z ∈ D₁` なら `E₁` から取り出した関数の値を使い、そうでなければ、そこから得られる `z ∈ D₂` に対して `E₂` から取り出した関数の値を使う。どちらの場合も、取り出しによりグラフの項目と、タグ付きの対を選んだ値と同一視する等式の両方が得られる。
<!--/-->

```agda
  wit : (z : S) (m : Mem z) (c : Case z) → Wit (val z m c) z
  wit z m (yes h) = inl (h , ∣ X₁.toFun (z , h)
    , (X₁.toFun-graph (z , h) , prʟ-fst (nn 0) (X₁.toFun (z , h))) ∣₁)
  wit z m (no nmem) = inr (nmem , ∣ X₂.toFun (z , off z m nmem)
    , (X₂.toFun-graph (z , off z m nmem) , prʟ-fst (nn 1) (X₂.toFun (z , off z m nmem))) ∣₁)
```

<!--en-->
Uniqueness in the left case composes three equations: the entry's second component equals the value named by the truncated witness; single-valuedness of `E₁` identifies the two function values; and the pair's first-projection equation says the value is exactly the tagged entry.
<!--zh-->
左支的唯一性复合三条等式：条目的第二分量等于截断见证所名指的取值；`E₁` 的单值性认同两个函数值；而对的第一投影等式说明该取值恰是带标签的条目。
<!--ja-->
左の場合の一意性は、三つの等式を合成する。項目の第二成分が、切り詰められた証人が名指す値に等しいこと。`E₁` の一価性が二つの関数の値を同一視すること。そして対の第一射影の等式が、値がちょうどタグつきの項目であることを述べる。
<!--/-->

```agda

  only : (z : S) (m : Mem z) (c : Case z) (y : S) → Wit y z → fst y ≡ fst (val z m c)
  only z m (yes h) y (inl (_ , hv)) = rec₁ (setIsSet _ _)
    (λ { (v , (hg , hy)) →
       hy ∙ cong (pr (# 0)) (sv₁ z v (X₁.toFun (z , h)) hg (X₁.toFun-graph (z , h)))
          ∙ sym (prʟ-fst (nn 0) (X₁.toFun (z , h))) }) hv
```

<!--en-->
The mixed cases are refuted outright: a member inside `D₁` cannot carry a witness recorded off `D₁`, and conversely. The right-right case is then handled exactly as the left, with `E₂`, the tag `1`, and the off-set function value.
<!--zh-->
交叉情形被直接反驳：属于 `D₁` 的成员不可能带有在 `D₁` 之外记录的见证，反之亦然。随后右右情形完全按左支处理，只是换用 `E₂`、标签 `1` 与偏离集合的函数值。
<!--ja-->
交差する場合はそのまま反駁される。`D₁` の中の要素が、`D₁` の外で記録された証人をもつことはできず、逆もまた然りである。右と右の場合は、`E₂` とタグ `1`、そして外れた要素での関数の値を使って、左とまったく同じように処理される。
<!--/-->

```agda
  only z m (yes h) y (inr (nmem , _)) = ⊥₀-rec (nmem h)
  only z m (no nmem) y (inl (h , _)) = ⊥₀-rec (nmem h)
  only z m (no nmem) y (inr (_ , hv)) = rec₁ (setIsSet _ _)
    (λ { (v , (hg , hy)) →
       hy ∙ cong (pr (# 1)) (sv₂ z v (X₂.toFun (z , off z m nmem)) hg (X₂.toFun-graph (z , off z m nmem)))
```

<!--en-->
The final equation composes the tag identification with the pair's first-projection equation, completing uniqueness. The witness thus determines its value in both cases.
<!--zh-->
最后一条等式复合标签认同与对的第一投影等式，唯一性就此完成。于是两种情形下见证都确定其取值。
<!--ja-->
最後の等式が、タグの同定と対の第一射影の等式を合成し、一意性が完成する。こうして、どちらの場合でも証人はその値を決定する。
<!--/-->

```agda
          ∙ sym (prʟ-fst (nn 1) (X₂.toFun (z , off z m nmem))) }) hv

```

<!--en-->
The value lands in the internal product: the pair of the numeral `0` or `1` with the function value is presented through its first projection equation, and `prodL-in` admits it because both numerals lie in `κ` and the function value lies in `κ` by the range clause.
<!--zh-->
取值落入内部乘积：数码 `0` 或 `1` 与函数值组成的对经其第一投影等式呈现，而 `prodL-in` 予以接纳，因为两个数码都在 `κ` 中，且函数值由范围子句落在 `κ` 中。
<!--ja-->
値は内部の直積に落ちる。数項 `0` か `1` と関数の値の対は、その第一射影の等式を通して提示され、二つの数項が `κ` の中にあり、範囲の条項によって関数の値も `κ` の中にあるので、`prodL-in` がそれを受け入れる。
<!--/-->

```agda
  into : (z : S) (m : Mem z) (c : Case z) → ⟨ fst (val z m c) ∈ˢ fst (prodL κ) ⟩
  into z m (yes h) = subst (λ w → ⟨ w ∈ˢ fst (prodL κ) ⟩) (sym (prʟ-fst (nn 0) (X₁.toFun (z , h))))
    (prodL-in κ (nn 0) (X₁.toFun (z , h)) 0∈κ (ran₁ z (X₁.toFun (z , h)) (X₁.toFun-graph (z , h))))
  into z m (no nmem) = subst (λ w → ⟨ w ∈ˢ fst (prodL κ) ⟩) (sym (prʟ-fst (nn 1) (X₂.toFun (z , off z m nmem))))
    (prodL-in κ (nn 1) (X₂.toFun (z , off z m nmem)) 1∈κ
```

<!--en-->
The right case supplies the range fact from `E₂` and the numeral `1`, completing the membership of both tagged values in the product.
<!--zh-->
右支由 `E₂` 与数码 `1` 供给范围事实，完成两个带标签取值在乘积中的成员资格。
<!--ja-->
右の場合は `E₂` と数項 `1` から範囲の事実を供給し、タグつきの値がどちらも直積の中にあることが揃う。
<!--/-->

```agda
      (ran₂ z (X₂.toFun (z , off z m nmem)) (X₂.toFun-graph (z , off z m nmem))))

```

<!--en-->
These ingredients define a map from the ordinary union `D` to the internal product `prodL κ`. Its value is chosen by the left-biased case distinction, and `into` proves that this tagged value belongs to the product.
<!--zh-->
这些材料定义出从普通并集 `D` 到内部乘积 `prodL κ` 的映射。取值由偏向左支的情形区分决定，`into` 则证明这个带标签的取值属于该乘积。
<!--ja-->
これらの材料から、通常の和集合 `D` から内部直積 `prodL κ` への写像を定める。値は左側を優先する場合分けで選ばれ、`into` がそのタグ付きの値が直積に属することを証明する。
<!--/-->

```agda
  Dmap : DefinableMap
  Dmap = record
    { dom = D ; cod = prodL κ ; fn = fn
    ; into = λ z m → into z m (decide z)
    ; graph = fo
```

<!--en-->
The defining clause feeds the witness into the graph introduction, and uniqueness converts every graph entry into the value at the decided case, transported along the carrier equality. The definable map is complete.
<!--zh-->
定义子句把见证喂给图的引入，而唯一性把每条图条目转换为所选情形下的取值，并沿载体相等运输。可定义映射就此完成。
<!--ja-->
定義の条項が証人をグラフの導入に渡し、一意性が、どのグラフの項目も、決められた場合の値へ、台の等しさに沿って変換する。これで定義可能な写像は完成である。
<!--/-->

```agda
    ; defines = λ z m → fo-in (fn z m) z (wit z m (decide z))
    ; only = λ z m y h → S≡ (rec₁ (setIsSet _ _) (only z m (decide z) y) (fo-out y z h)) }

```

<!--en-->
Injectivity of the tagged map is proved by comparing the decided cases of two inputs. The case analysis has four combinations, and the tagged pair structure separates them cleanly.
<!--zh-->
带标签映射的单射性通过比较两个输入所判定的情形来证明。情形分析有四种组合，而带标签的对结构把它们干净地分开。
<!--ja-->
タグつきの写像の単射性は、二つの入力について決められた場合を比較することで証明する。場合分けには四つの組み合わせがあり、タグつきの対の構造がそれをきれいに分ける。
<!--/-->

```agda
  inj : (z : S) (m : Mem z) (z' : S) (m' : Mem z') → fst (fn z m) ≡ fst (fn z' m') → fst z ≡ fst z'
  inj z m z' m' = go (decide z) (decide z')
    where
    go : (c : Case z) (c' : Case z') → fst (val z m c) ≡ fst (val z' m' c') → fst z ≡ fst z'
    go (yes h) (yes h') q = ij₁ (X₁.toFun (z , h)) z z' (X₁.toFun-graph (z , h))
```

<!--en-->
In the same-tag case, the pair equation is inverted by `pr-inj`: the tags agree, so the equation of the values identifies the two function values, which is exactly the argument the injectivity clause consumes.
<!--zh-->
同标签情形中，对等式由 `pr-inj` 反演：标签一致，故取值的等式认同两个函数值，这正是单射性子句所要的论证。
<!--ja-->
同じタグの場合は、対の等式を `pr-inj` で逆にたどる。タグが一致するので、値の等式が二つの関数の値を同一視し、これが単射性の条項が消費する議論そのものである。
<!--/-->

```agda
      (subst (λ w → ⟨ pr (fst z') w ∈ fst E₁ ⟩) (sym (snd p)) (X₁.toFun-graph (z' , h')))
      where
      p : (# 0 ≡ # 0) × (fst (X₁.toFun (z , h)) ≡ fst (X₁.toFun (z' , h')))
      p = pr-inj (sym (prʟ-fst (nn 0) (X₁.toFun (z , h))) ∙ q ∙ prʟ-fst (nn 0) (X₁.toFun (z' , h')))
    go (yes h) (no nmem') q = ⊥₀-rec (znots (#-inj 0 1 (fst
```

<!--en-->
The mixed-tag cases are impossible: equality of the two values would force the numeral `0` to equal the numeral `1`, contradicted in the two orientations by `znots` and `snotz`. When both inputs take the right branch, injectivity of `E₂` identifies them.
<!--zh-->
标签不同的两种情形都不可能发生：两取值若相等，就会迫使数码 `0` 与数码 `1` 相等，两个方向分别由 `znots` 与 `snotz` 排除。两个输入都走右支时，则由 `E₂` 的单射性认同它们。
<!--ja-->
タグが異なる二つの場合はいずれも不可能である。二つの値が等しければ数項 `0` と数項 `1` が等しくなってしまい、二つの向きはそれぞれ `znots` と `snotz` に反する。両方の入力が右側の場合は、`E₂` の単射性がそれらを同一視する。
<!--/-->

```agda
      (pr-inj (sym (prʟ-fst (nn 0) (X₁.toFun (z , h))) ∙ q ∙ prʟ-fst (nn 1) (X₂.toFun (z' , off z' m' nmem')))))))
    go (no nmem) (yes h') q = ⊥₀-rec (snotz (#-inj 1 0 (fst
      (pr-inj (sym (prʟ-fst (nn 1) (X₂.toFun (z , off z m nmem))) ∙ q ∙ prʟ-fst (nn 0) (X₁.toFun (z' , h')))))))
    go (no nmem) (no nmem') q = ij₂ (X₂.toFun (z , off z m nmem)) z z' (X₂.toFun-graph (z , off z m nmem))
      (subst (λ w → ⟨ pr (fst z') w ∈ fst E₂ ⟩) (sym (snd p)) (X₂.toFun-graph (z' , off z' m' nmem')))
```

<!--en-->
The pair equation for the right-right case splits into the agreement of the tags and of the function values, the latter being what injectivity consumes.
<!--zh-->
右右情形的对等式拆分为标签一致与函数值一致，后者正是单射性所消耗者。
<!--ja-->
右と右の場合の対の等式は、タグの一致と関数の値の一致に分かれ、単射性が消費するのは後者である。
<!--/-->

```agda
      where
      p : (# 1 ≡ # 1) × (fst (X₂.toFun (z , off z m nmem)) ≡ fst (X₂.toFun (z' , off z' m' nmem')))
      p = pr-inj (sym (prʟ-fst (nn 1) (X₂.toFun (z , off z m nmem))) ∙ q
                  ∙ prʟ-fst (nn 1) (X₂.toFun (z' , off z' m' nmem')))

```

<!--en-->
The resulting graph is a coded injection from the ordinary union `D₁ ∪ D₂` into `prodL κ`. The map uses tags in its values to distinguish the two branches, and resolves an element in the overlap through the first branch.
<!--zh-->
所得的图是从普通并集 `D₁ ∪ D₂` 到 `prodL κ` 的编码单射。映射在取值中使用标签区分两支，并把同时属于两边的元素归入第一支。
<!--ja-->
得られたグラフは、通常の和集合 `D₁ ∪ D₂` から `prodL κ` への符号化された単射である。写像は値のタグで二つの枝を区別し、両方に属する要素は第一の枝で扱う。
<!--/-->

```agda
  injL : InjL D (prodL κ)
  injL = Inj.injL Dmap inj
```

<!--en-->
The two premises expose their injection graphs only under propositional truncation. Eliminating both truncations into the proposition `InjL (D₁ ∪ D₂) (prodL κ)` lets the tagged construction be applied to any witnessing pair of graphs, yielding the required mere coded injection.
<!--zh-->
两个前提都只在命题截断下给出各自的注入图。把两层截断消去到命题 `InjL (D₁ ∪ D₂) (prodL κ)`，便可对任意一对见证图应用带标签构造，得到所需的仅仅存在的编码单射。
<!--ja-->
二つの前提は、それぞれの単射グラフを命題的切り詰めのもとでしか与えない。二つの切り詰めを命題 `InjL (D₁ ∪ D₂) (prodL κ)` へ消去すると、どの証人グラフの組にもタグ付き構成を適用でき、必要な符号化単射の単なる存在が得られる。
<!--/-->

```agda
tag-union : (κ : S) → ⟨ # 0 ∈ fst κ ⟩ → ⟨ # 1 ∈ fst κ ⟩
          → (D₁ D₂ : S) → InjL D₁ κ → InjL D₂ κ
          → InjL (unionʟ (pairʟ D₁ D₂)) (prodL κ)
tag-union κ h0 h1 D₁ D₂ = rec2 squash₁
  (λ { (E₁ , c₁) (E₂ , c₂) → TagUnion.injL κ h0 h1 D₁ D₂ E₁ E₂ c₁ c₂ })
```

<!--en-->
The least-predecessor construction is stated generically. It takes an ordinal `γ`, a relation `G`, a domain `D`, and a set `P` of predecessors bounded by the stage `γ`, such that every member of `D` merely has some `G`-predecessor in `P`; the task is to choose one canonically.
<!--zh-->
最小前驱构造以一般形式陈述。它取序数 `γ`、关系 `G`、定义域 `D`，以及被层 `γ` 界住的前驱集 `P`，使得 `D` 的每个成员都「仅仅存在」某个 `P` 中的 `G` 前驱；任务在于典范地选取一个。
<!--ja-->
最小の前者の構成は、一般的な形で述べられる。順序数 `γ`、関係 `G`、定義域 `D`、そして段階 `γ` で抑えられた前者の集合 `P` を受け取り、`D` のすべての要素が `P` の中に `G` の前者を「単に」もつとする。課題は、その一つを正準に選ぶことである。
<!--/-->

```agda
module LeastPre (γ : V ℓ) (oγ : IsOrd γ) (G D P : S)
  (inP : (p z : S) → Holds G p z → ⟨ fst p ∈ fst P ⟩)
  (P⊆L : (p : S) → ⟨ fst p ∈ fst P ⟩ → ⟨ fst p ∈ Lset γ ⟩)
  (have : (z : S) → ⟨ fst z ∈ fst D ⟩ → ∥ Σ[ p ∈ S ] Holds G p z ∥₁) where

```

<!--en-->
Membership in the domain is recorded as a type, so that the argument can carry it alongside the elements.
<!--zh-->
定义域的隶属被记录为一个类型，使论证能把它与元素并肩携带。
<!--ja-->
定義域への所属は型として記録され、議論が要素とともにそれを運べるようにする。
<!--/-->

```agda
  Mem : S → Type (ℓ-suc ℓ)
  Mem z = ⟨ fst z ∈ fst D ⟩

```

<!--en-->
The graph formula is the application clause of the constant `G`: holding at a pair means exactly that the pair belongs to the relation.
<!--zh-->
图公式是常元 `G` 的应用子句：在一对上成立，恰是说该对属于这个关系。
<!--ja-->
グラフの論理式は、定数 `G` の適用の条項である。対の上で成立することは、ちょうどその対が関係に属することを意味する。
<!--/-->

```agda
  private
    graphFo : Formula S 2
    graphFo = appC G i0 i1

```

<!--en-->
The existence hypothesis is moved to the common stage without choosing a predecessor globally. Each truncated predecessor lies in `P`, hence in `Lset γ`, and the adequacy equation turns its relation membership into satisfaction of the graph formula.
<!--zh-->
存在性假设被移到共同的层中，而没有全局选取前驱。每个截断地存在的前驱先属于 `P`，因而属于 `Lset γ`；充分性等式再把它的关系成员资格转成图公式的满足。
<!--ja-->
存在仮定を共通の段階へ移すが、前者を大域的に選ぶことはしない。切り詰めのもとで存在する各前者は `P` に属し、したがって `Lset γ` に属する。さらに妥当性の等式が、その関係への所属をグラフ論理式の充足へ変える。
<!--/-->

```agda
    have-γ : (z : S) → Mem z
           → ∥ Σ[ p ∈ S ] (⟨ fst p ∈ Lset γ ⟩ × ⟨ (p ∷ z ∷ []) ⊨ graphFo ⟩) ∥₁
    have-γ z m = map₁
      (λ { (p , h) → p , P⊆L p (inP p z h)
                       , subst ⟨_⟩ (sym (appC-adequate G i0 i1 (p ∷ z ∷ []))) h })
```

<!--en-->
The original truncated existence supplies the witness that the transport consumes.
<!--zh-->
原有的截断存在供给运输所要消耗的见证。
<!--ja-->
もとの切り詰められた存在が、輸送が消費する証人を供給する。
<!--/-->

```agda
      (have z m)

```

<!--en-->
The stage-order construction now selects, for every member of the domain, the least `G`-predecessor in `Lset γ`. It also supplies a definable graph and the membership readings that identify each input with its selected value.
<!--zh-->
层序构造现在为定义域的每个成员选取 `Lset γ` 中最小的 `G` 前驱。它还给出一个可定义图，以及把每个输入同其所选取值对应起来的成员读式。
<!--ja-->
段階順序による構成は、定義域の各要素に対して `Lset γ` にある最小の `G` 前者を選ぶ。また、定義可能なグラフと、各入力をその選ばれた値に対応させる所属の読み出しも与える。
<!--/-->

```agda
    module Ls = Least γ oγ D graphFo have-γ using ( fn; fn-holds; Dmap; T; T-in; T-out )

```

<!--en-->
The selected least predecessor is the value function of the construction.
<!--zh-->
选出的最小前驱就是该构造的取值函数。
<!--ja-->
選ばれた最小の前者が、この構成の値を与える関数である。
<!--/-->

```agda
  fn : (z : S) → Mem z → S
  fn = Ls.fn

```

<!--en-->
The value satisfies the relation at its input: the internal satisfaction is transported back to the application clause at the environment pairing the value with the input.
<!--zh-->
取值在其输入处满足该关系：内部满足被运回「把取值与输入配成对的环境」处的应用子句。
<!--ja-->
値はその入力で関係を満たす。内部の充足は、値と入力を対にした環境での適用の条項へと運び戻される。
<!--/-->

```agda
  fn-holds : (z : S) (m : Mem z) → Holds G (fn z m) z
  fn-holds z m = subst ⟨_⟩ (appC-adequate G i0 i1 (fn z m ∷ z ∷ [])) (Ls.fn-holds z m)

```

<!--en-->
The definable map is recorded with codomain `P`, the membership of the value being guaranteed by the inward direction of the standing hypothesis.
<!--zh-->
可定义映射以 `P` 为陪域记录，取值的所属由既有假设的向内方向保证。
<!--ja-->
定義可能な写像は、余域を `P` として記録される。値の所属は、既存の仮定の内向きの方向が保証する。
<!--/-->

```agda
  Dmap : DefinableMap
  Dmap = record Ls.Dmap { cod = P ; into = λ z m → inP (fn z m) z (fn-holds z m) }
```

<!--en-->
The graph of the least-predecessor function is an element of `L`, as the stage machinery returns it with its membership description.
<!--zh-->
最小前驱函数的图是 `L` 的元素，层机制连同其隶属描述一并返回。
<!--ja-->
最小の前者の関数のグラフは `L` の要素であり、段階の機構がその所属の記述とともに返す。
<!--/-->

```agda
  T : S
  T = Ls.T

```

<!--en-->
The inward reading exhibits the pair of an input with its selected value as an entry of the graph.
<!--zh-->
向内读式出示「输入与其选出的取值组成的对」是图的一条目。
<!--ja-->
内向きの読み出しは、入力と選ばれた値の対がグラフの項目であることを示す。
<!--/-->

```agda
  T-in : (z : S) (m : Mem z) → ⟨ pr (fst z) (fst (fn z m)) ∈ fst T ⟩
  T-in = Ls.T-in

```

<!--en-->
The outward reading recovers, from every entry, the input together with the equation identifying the second component with the selected value; this is what later arguments use to compare candidates.
<!--zh-->
向外读式从每条条目恢复输入，以及「第二分量等于选出的取值」的等式；后文比较候选者所用的正是它。
<!--ja-->
外向きの読み出しは、すべての項目から、入力と、第二成分を選ばれた値と同一視する等式を復元する。のちの議論が候補を比較するときに使うのはこれである。
<!--/-->

```agda
  T-out : (z e : S) → ⟨ pr (fst z) (fst e) ∈ fst T ⟩
        → Σ[ m ∈ Mem z ] (fst e ≡ fst (fn z m))
  T-out = Ls.T-out
```

<!--en-->
Under the additional hypothesis that the relation is functional, the least-predecessor function becomes injective: the module carries that single assumption.
<!--zh-->
在「该关系为函数性」这一附加假设下，最小前驱函数成为单射：该模块只携带这一条假设。
<!--ja-->
関係が関数的であるという追加の仮定のもとで、最小の前者の関数は単射になる。モジュールが携えるのは、この一つの仮定だけである。
<!--/-->

```agda
  module Functional
    (funct : (p z z' : S) → Holds G p z → Holds G p z' → fst z ≡ fst z') where

```

<!--en-->
If two inputs share a value, the value satisfies the relation at both inputs; the second satisfaction is transported along the equation of the values, and functionality then identifies the two inputs.
<!--zh-->
若两个输入共享取值，则该取值在两个输入处都满足关系；第二个满足沿取值的等式运输，函数性随即认同两个输入。
<!--ja-->
二つの入力が同じ値を共有すれば、その値は両方の入力で関係を満たす。二つ目の充足が値の等式に沿って輸送され、関数性が二つの入力を同一視する。
<!--/-->

```agda
    inj : (z : S) (m : Mem z) (z' : S) (m' : Mem z')
        → fst (fn z m) ≡ fst (fn z' m') → fst z ≡ fst z'
    inj z m z' m' q = funct (fn z m) z z' (fn-holds z m)
      (subst (λ w → ⟨ pr w (fst z') ∈ fst G ⟩) (sym q) (fn-holds z' m'))

```

<!--en-->
The injectivity is packaged into a coded injection from the domain into the predecessor set.
<!--zh-->
单射性被打包为从定义域到前驱集合的编码单射。
<!--ja-->
この単射性は、定義域から前者の集合への、符号化された単射としてまとめられる。
<!--/-->

```agda
    injL : InjL D P
    injL = Inj.injL Dmap inj
```

<!--en-->
The point construction handles an at-most-singleton domain. Given only `0 ∈ κ`, it sends every member of the singleton generated by `a` to the zeroth numeral and obtains a coded injection into `κ`.
<!--zh-->
点构造处理一个至多含一个元素的定义域。只需给定 `0 ∈ κ`，它便把由 `a` 生成的单点集的每个成员送到第零个数码，并得到一条到 `κ` 的编码单射。
<!--ja-->
点の構成は、高々一要素の定義域を扱う。`0 ∈ κ` だけを仮定し、`a` から作った単集合の各要素を零番の数項へ送り、`κ` への符号化された単射を得る。
<!--/-->

```agda
module Point (κ : S) (0∈κ : ⟨ # 0 ∈ fst κ ⟩) (a : S) where

```

<!--en-->
Let `Y` be the constructible singleton generated by `a`. The argument will use only its membership introduction and elimination laws.
<!--zh-->
令 `Y` 为由 `a` 生成的可构造单点集。论证只使用它的成员引入律与消去律。
<!--ja-->
`Y` を `a` から作られる構成可能な単集合とする。議論で使うのは、その所属の導入則と除去則だけである。
<!--/-->

```agda
  Y : S
  Y = sglʟ a

```

<!--en-->
The member `a` belongs to its own singleton, by the introduction reading of the singleton construction.
<!--zh-->
成员 `a` 属于它自己的单点集，由单点构造的引入读式给出。
<!--ja-->
要素 `a` はそれ自身の単集合に属する。一元集合の構成の導入の読み出しによるものである。
<!--/-->

```agda
  Y-in : ⟨ fst a ∈ fst Y ⟩
  Y-in = sglʟ-in a (fst a) refl

```

<!--en-->
The elimination reading says the singleton contains nothing else: any member has `a` as its underlying set.
<!--zh-->
消去读式说明单点集不含其他：任何成员的底层集合都是 `a`。
<!--ja-->
消去の読み出しは、単集合がそれ以外を含まないと言う。どの要素も、基礎の集合は `a` である。
<!--/-->

```agda
  Y-out : (z : S) → ⟨ fst z ∈ fst Y ⟩ → fst z ≡ fst a
  Y-out z = sglʟ-out a (fst z)

```

<!--en-->
The graph is described by the atomic formula with two free slots that equates the value slot with the internal empty set, whose underlying set is the numeral `0`.
<!--zh-->
图由一条含两个自由槽位的原子公式描述；它把取值槽与内部空集相等，而内部空集的底层集合正是数码 `0`。
<!--ja-->
グラフは、二つの自由スロットをもつ原子論理式で記述される。この論理式は値のスロットを内部の空集合と等置し、その底の集合は数項 `0` である。
<!--/-->

```agda
  fo : Formula S 2
  fo = var i0 ≐ con ∅ʟ

```

<!--en-->
The definable map sends the unique input to the zeroth numeral; the codomain membership is the standing fact `0∈κ`.
<!--zh-->
可定义映射把唯一的输入送到第零个数码；陪域隶属即既有事实 `0∈κ`。
<!--ja-->
定義可能な写像は、ただ一つの入力を零番の数項へ送る。余域への所属は、既存の事実 `0∈κ` である。
<!--/-->

```agda
  Dmap : DefinableMap
  Dmap = record
    { dom = Y ; cod = κ ; fn = λ _ _ → nn 0
    ; into = λ _ _ → 0∈κ
    ; graph = fo
```

<!--en-->
The graph holds definitionally, since the atomic sentence equates the numeral with itself; uniqueness holds because both members of the singleton present the same underlying set.
<!--zh-->
图由定义成立，因为原子句把数码与其自身等同；唯一性成立，因为单点集的两个成员呈现同一底层集合。
<!--ja-->
グラフは定義どおりに成立する。原子文が数項をそれ自身と等置するからである。一意性は、単集合の二つの要素が同じ基礎の集合を提示することから成立する。
<!--/-->

```agda
    ; defines = λ z m → refl
    ; only = λ z m y h → S≡ h }

```

<!--en-->
Injectivity composes the two outward readings: both inputs present the same underlying set as `a`, hence they are equal as carrier elements.
<!--zh-->
单射性复合两条向外读式：两个输入都呈现与 `a` 相同的底层集合，故作为载体元素二者相等。
<!--ja-->
単射性は、二つの外向きの読み出しを合成する。どちらの入力も `a` と同じ基礎の集合を提示するので、台の要素として両者は等しいのである。
<!--/-->

```agda
  inj : (z : S) (m : ⟨ fst z ∈ fst Y ⟩) (z' : S) (m' : ⟨ fst z' ∈ fst Y ⟩)
      → fst (nn 0) ≡ fst (nn 0) → fst z ≡ fst z'
  inj z m z' m' _ = Y-out z m ∙ sym (Y-out z' m')

```

<!--en-->
The singleton-to-cardinal injection is packaged in the same form as every other counting piece.
<!--zh-->
单点集到基数的单射与其他计数组件以同一形式打包。
<!--ja-->
単集合から基数への単射は、ほかの計数の部品と同じ形でまとめられる。
<!--/-->

```agda
  injL : InjL Y κ
  injL = Inj.injL Dmap inj
```

<!--en-->
## Counting every finite closure step
<!--zh-->
## 计数每一步有限闭包
<!--ja-->
## 有限な閉包の各段階を数える
<!--/-->

<!--en-->
The counting theorem fixes an ordinal `lam` closed under successor, a start set `X` contained in `Lset lam`, and a proof that `X` is constructible. The elementarity and superadequacy hypotheses provide the closure and least-witness facts for the Skolem hull generated from `X`.
<!--zh-->
计数定理固定一个对后继封闭的序数 `lam`、一个包含于 `Lset lam` 的起点集合 `X`，以及 `X` 可构造的证明。初等性与超充分性假设为从 `X` 生成的 Skolem 壳提供闭包和最小见证性质。
<!--ja-->
計数定理では、後者に閉じた順序数 `lam`、`Lset lam` に含まれる始点集合 `X`、そして `X` が構成可能であることを固定する。初等性と超妥当性の仮定は、`X` から生成される Skolem 包に必要な閉包と最小証人の性質を与える。
<!--/-->

```agda
module Count (lam : V ℓ) (ordλ : IsOrd lam)
  (succλ : (d : V ℓ) → ⟨ d ∈ˢ lam ⟩ → ⟨ sucV d ∈ˢ lam ⟩)
  (X : V ℓ) (X⊆L : (x : V ℓ) → ⟨ x ∈ˢ X ⟩ → ⟨ x ∈ˢ Lset lam ⟩)
  (∅∈λ : ⟨ ∅ ∈ˢ lam ⟩)
  (elem : Frame.A.Elementary lam ordλ succλ X X⊆L ∅∈λ)
```

<!--en-->
The counting target is an internal cardinal `κ` outside `ω`, together with a coded injection of the start into it. The task is to count the whole hull by the same cardinal.
<!--zh-->
计数目标是一个不在 `ω` 中的内部基数 `κ`，连同起点到它的编码单射。任务是以同一基数计数整个壳。
<!--ja-->
計数の目標は、`ω` の外にある内部の基数 `κ` と、始点からそれへの符号化された単射である。課題は、同じ基数で包全体を数えることである。
<!--/-->

```agda
  (sup : Superadequate lam)
  (X-isL : ⟨ isL X ⟩)
  (κ : S) (oκ : IsOrd (fst κ)) (cκ : IsCardinalL κ) (κ∉ω : ⟨ fst κ ∈ˢ ω ⟩ → ⊥₀)
  (base : InjL (X , X-isL) κ) where
```

<!--en-->
The hull is presented as the union of its finite iterates `hullStep n`. One closure step is governed by `Φ`, whose nontrivial branch records a least witness for a formula key and a finite parameter environment over the current iterate.
<!--zh-->
该壳表示为各有限迭代 `hullStep n` 的并。一次闭包步由 `Φ` 控制；它的非平凡分支记录某个公式键与当前迭代上的有限参数环境所确定的最小见证。
<!--ja-->
この包は有限反復 `hullStep n` の和集合として表される。一回の閉包は `Φ` によって定まり、その非自明な枝は、論理式の鍵と現在の反復上の有限なパラメータ環境による最小証人を記録する。
<!--/-->

```agda
  module Cn = Condense′ lam ordλ succλ X X⊆L ∅∈λ elem sup X-isL
    using ( hullStep; hullL; hullStep⊆Hull )
  module B = Telescope.Build lam ordλ succλ X X⊆L ∅∈λ
    using ( A; Body
          ; LeastWitness; leastWitnessFo; leastWitness-in; leastWitness-out
```

<!--en-->
For a least witness, the accompanying data recover a natural length, a finite assignment into the current set, the encoded environment, and membership of the formula key in `Lset ω`. Uniqueness holds after the key and environment have been fixed.
<!--zh-->
对一个最小见证，随附的数据恢复出一个自然数长度、一个到当前集合的有限赋值、相应的编码环境，以及公式键属于 `Lset ω` 的证明。唯一性是在公式键与环境固定之后成立的。
<!--ja-->
最小証人に付随するデータから、自然数の長さ、現在の集合への有限な割り当て、その符号化された環境、そして論理式の鍵が `Lset ω` に属することが得られる。一意性は、鍵と環境を固定した後に成立する。
<!--/-->

```agda
          ; LeastWitnessData; leastWitness-data; leastWitness-unique; witFo-leastWitness
          ; Φ; Φ-out; λ-isL; ω-num; pack )
  module SM = SatGraph B.A using ( pairs; pairs-out; valOf )
```

<!--en-->
The finite iterates come with introduction and elimination rules, and every iterate lies in the full hull. The full hull itself is contained in `Lset lam`; these inclusions keep every set used by the counting construction inside the fixed ambient stage.
<!--zh-->
有限迭代带有成员引入律与消去律，并且每个迭代都包含于整个壳。整个壳又包含于 `Lset lam`；这些包含关系保证计数构造所用的集合始终位于固定的外围层中。
<!--ja-->
有限反復には所属の導入則と除去則があり、各反復は包全体に含まれる。さらに包全体は `Lset lam` に含まれる。これらの包含により、計数構成で使う各集合は固定した周囲の段階内に保たれる。
<!--/-->

```agda
  module It = Telescope.HullIter.It lam ordλ succλ X X⊆L ∅∈λ X-isL B.pack
    using ( Num; iter; iter-in; iter-out; iterUnion-out; ω-num )
  module HSH = HullStage.H lam ordλ succλ X X⊆L ∅∈λ using ( Hull⊆L )
  open Cn using ( hullStep; hullL )
```

<!--en-->
Because `κ` is an ordinal and does not belong to `ω`, it contains every finite numeral. Internal cardinality is not used for this conclusion; it is needed separately for the square law.
<!--zh-->
因为 `κ` 是序数且不属于 `ω`，所以它包含每个有限数码。这个结论不使用内部基数性；内部基数性另用于平方律。
<!--ja-->
`κ` は順序数であり `ω` に属さないので、すべての有限数項を含む。この結論に内部基数性は使われず、内部基数性は別に平方法則で必要になる。
<!--/-->

```agda
  num∈κ : (k : ℕ) → ⟨ # k ∈ fst κ ⟩
  num∈κ k = ω⊆ (fst κ) oκ κ∉ω (# k) (#∈ω k)
```

<!--en-->
The infinite-cardinal square argument gives the coded injection `pairκ : InjL (prodL κ) κ`. It uses all three relevant hypotheses on `κ`: ordinality, internal cardinality, and non-membership in `ω`; the result is an injection, not a bijection.
<!--zh-->
无穷基数平方论证给出编码单射 `pairκ : InjL (prodL κ) κ`。它使用关于 `κ` 的三项相关假设：序数性、内部基数性以及不属于 `ω`；所得结论是单射，而非双射。
<!--ja-->
無限基数の平方に関する議論から、符号化された単射 `pairκ : InjL (prodL κ) κ` が得られる。ここでは `κ` の順序数性、内部基数性、`ω` に属さないことの三つをすべて使う。結論は単射であり、全単射ではない。
<!--/-->

```agda
  pairκ : InjL (prodL κ) κ
  pairκ = WF.WFI.induction regularityV {P = Goal} Step.result (fst κ) (snd κ) oκ cκ κ∉ω

```

<!--en-->
The stage `Lω = Lset ω` injects into `κ` by composition. Limit-stage counting first gives `Lω ↪ ωʟ`, and the inclusion `ω ⊆ κ`, obtained from the ordinality and non-finiteness of `κ`, gives `ωʟ ↪ κ`.
<!--zh-->
层 `Lω = Lset ω` 通过复合单射入 `κ`。极限层计数先给出 `Lω ↪ ωʟ`，再由 `κ` 的序数性与非有限性得到 `ω ⊆ κ`，从而有 `ωʟ ↪ κ`。
<!--ja-->
段階 `Lω = Lset ω` は、単射の合成によって `κ` へ入る。極限段階の計数がまず `Lω ↪ ωʟ` を与え、`κ` の順序数性と非有限性から得られる `ω ⊆ κ` が `ωʟ ↪ κ` を与える。
<!--/-->

```agda
  Lω↪κ : InjL Lω κ
  Lω↪κ = injl-trans Lω ωʟ κ limit-stage-counted
    (inclusion-coded ωʟ κ (λ z hz → ω⊆ (fst κ) oκ κ∉ω z hz))
```

<!--en-->
For one closure step, fix a constructible `Z` contained in `Lset lam` and an actual graph `E` satisfying `InjCode E Z κ`. The goal is to turn this chosen stage injection into the mere coded injection `InjL (Φ Z) κ`.
<!--zh-->
为计数一次闭包步，固定一个包含于 `Lset lam` 的可构造集合 `Z`，以及一个满足 `InjCode E Z κ` 的实际图 `E`。目标是从这条已选定的层注入构造出仅仅存在的编码单射 `InjL (Φ Z) κ`。
<!--ja-->
一回の閉包を数えるため、`Lset lam` に含まれる構成可能な集合 `Z` と、`InjCode E Z κ` を満たす実際のグラフ `E` を固定する。目標は、この選ばれた段階の単射から、符号化単射の単なる存在 `InjL (Φ Z) κ` を構成することである。
<!--/-->

```agda
  module OneStep (Z : S) (Z⊆ : (z : V ℓ) → ⟨ z ∈ˢ fst Z ⟩ → ⟨ z ∈ˢ Lset lam ⟩)
                 (E : S) (cE : InjCode E Z κ) where

```

<!--en-->
`ΦZ = Φ Z` is one closure step. Its membership description has three branches: an old member of `Z`, the empty-set fallback, or a least witness determined by a formula key and a finite parameter environment over `Z`.
<!--zh-->
`ΦZ = Φ Z` 是一次闭包步。其成员描述有三个分支：`Z` 的旧成员、空集后备项，或由公式键与 `Z` 上的有限参数环境确定的最小见证。
<!--ja-->
`ΦZ = Φ Z` は一回の閉包である。その所属の記述には三つの枝がある。`Z` の既存の要素、空集合という予備の場合、または論理式の鍵と `Z` 上の有限なパラメータ環境によって定まる最小証人である。
<!--/-->

```agda
    ΦZ : S
    ΦZ = B.Φ Z
```

<!--en-->
The new part is separated first: `D₂` collects the members of `ΦZ` that are not members of `Z`. Separation inside `L` keeps the new part constructible.
<!--zh-->
先分离出新的部分：`D₂` 收集 `ΦZ` 中不属于 `Z` 的成员。`L` 内部的分离保证新部分可构造。
<!--ja-->
新しい部分をまず分出する。`D₂` は `ΦZ` のうち `Z` に属さない要素を集める。`L` の内部の分出により、新しい部分も構成可能である。
<!--/-->

```agda
    opaque
      D₂ : S
      D₂ = hasSeparationL ΦZ (¬̇ (var i0 ∈̇ con Z)) .fst .fst

```

<!--en-->
Its membership specification says exactly what separation computed: belonging to `D₂` is belonging to `ΦZ` together with the refutation of belonging to `Z`.
<!--zh-->
其隶属规格恰说出分离所计算的内容：属于 `D₂`，就是属于 `ΦZ` 并且不属于 `Z`。
<!--ja-->
その所属の仕様は、分出が計算した内容を正確に述べる。`D₂` への所属とは、`ΦZ` への所属と `Z` への所属の否定を合わせたものである。
<!--/-->

```agda
      D₂-spec : (z : S) → (fst z ∈ fst D₂)
              ≡ ((fst z ∈ fst ΦZ) ⊓ ((z ∷ []) ⊨ ¬̇ (var i0 ∈̇ con Z)))
      D₂-spec z = hasSeparationL ΦZ (¬̇ (var i0 ∈̇ con Z)) .fst .snd z

```

<!--en-->
The introduction rule lifts the refutation of membership into the object level, so an element of `ΦZ` together with a proof that it is not in `Z` enters `D₂`.
<!--zh-->
引入规则把隶属的反驳提升到对象层，于是 `ΦZ` 的元素连同「它不属于 `Z`」的证明即可进入 `D₂`。
<!--ja-->
導入規則は所属の反証を対象レベルへ持ち上げる。したがって `ΦZ` の要素と、それが `Z` に属さないことの証明が揃えば `D₂` に入れる。
<!--/-->

```agda
    opaque
      D₂-in : (z : S) → ⟨ fst z ∈ fst ΦZ ⟩ → (⟨ fst z ∈ fst Z ⟩ → ⊥₀) → ⟨ fst z ∈ fst D₂ ⟩
      D₂-in z h nmem = subst ⟨_⟩ (sym (D₂-spec z)) (h , λ z∈ → lift (nmem z∈))

```

<!--en-->
The elimination rule unpacks membership in `D₂` through the specification, and lowers the object-level refutation back to an ordinary implication.
<!--zh-->
消去规则经该规格拆开 `D₂` 的隶属，并把对象层的反驳降回普通的蕴涵。
<!--ja-->
消去の規則は、仕様を通して `D₂` の所属を展開し、対象レベルの反証を通常の含意へと降ろす。
<!--/-->

```agda
      D₂-out : (z : S) → ⟨ fst z ∈ fst D₂ ⟩ → ⟨ fst z ∈ fst ΦZ ⟩ × (⟨ fst z ∈ fst Z ⟩ → ⊥₀)
      D₂-out z h = r .fst , λ z∈ → lower (r .snd z∈)
        where
        r : ⟨ fst z ∈ fst ΦZ ⟩
          × ⟨ (z ∷ []) ⊨ ¬̇ (var i0 ∈̇ con Z) ⟩
```

<!--en-->
The unpacked statement is a pair: membership in `ΦZ` and satisfaction of the negated atom.
<!--zh-->
展开后的陈述是一个对：属于 `ΦZ`，并且满足那条否定原子。
<!--ja-->
展開された主張は一つの対である。`ΦZ` への所属と、否定された原子の充足である。
<!--/-->

```agda
        r = subst ⟨_⟩ (D₂-spec z) h

```

<!--en-->
Inside the new part, the elements equal to the empty set are separated out as `D∅`.
<!--zh-->
在新的部分内部，等于空集的元素被分离为 `D∅`。
<!--ja-->
新しい部分の内側から、空集合と等しい要素が `D∅` として分出される。
<!--/-->

```agda
    opaque
      D∅ : S
      D∅ = hasSeparationL D₂ (var i0 ≐ con ∅ʟ) .fst .fst

```

<!--en-->
Its specification is the same two-fold pattern: membership in `D₂` together with the equation to the empty set.
<!--zh-->
其规格是同样的双重模式：属于 `D₂`，并且与空集相等。
<!--ja-->
その仕様は同じ二重の型である。`D₂` への所属と、空集合との等式である。
<!--/-->

```agda
      D∅-spec : (z : S) → (fst z ∈ fst D∅)
              ≡ ((fst z ∈ fst D₂) ⊓ ((z ∷ []) ⊨ var i0 ≐ con ∅ʟ))
      D∅-spec z = hasSeparationL D₂ (var i0 ≐ con ∅ʟ) .fst .snd z

```

<!--en-->
An element of `D₂` that equals the empty set enters `D∅` with both data.
<!--zh-->
`D₂` 中等于空集的元素，连同两条数据即可进入 `D∅`。
<!--ja-->
`D₂` の要素で空集合と等しいものは、二つのデータとともに `D∅` に入る。
<!--/-->

```agda
    opaque
      D∅-in : (z : S) → ⟨ fst z ∈ fst D₂ ⟩ → fst z ≡ ∅ → ⟨ fst z ∈ fst D∅ ⟩
      D∅-in z h e = subst ⟨_⟩ (sym (D∅-spec z)) (h , e)

```

<!--en-->
Its elimination is the specification read directly: membership in `D₂` and the equation to the empty set.
<!--zh-->
其消去就是直接读出的规格：属于 `D₂`，以及与空集的等式。
<!--ja-->
その消去は、仕様をそのまま読んだものである。`D₂` への所属と、空集合との等式である。
<!--/-->

```agda
      D∅-out : (z : S) → ⟨ fst z ∈ fst D∅ ⟩ → ⟨ fst z ∈ fst D₂ ⟩ × (fst z ≡ ∅)
      D∅-out z h = subst ⟨_⟩ (D∅-spec z) h

```

<!--en-->
The remainder `Dw` collects the elements of `D₂` that differ from the empty set.
<!--zh-->
剩余部分 `Dw` 收集 `D₂` 中不等于空集的元素。
<!--ja-->
残りの部分 `Dw` は、`D₂` のうち空集合と異なる要素を集める。
<!--/-->

```agda
    opaque
      Dw : S
      Dw = hasSeparationL D₂ (¬̇ (var i0 ≐ con ∅ʟ)) .fst .fst

```

<!--en-->
Its specification mirrors the previous one, with the negated equation in place of the equation.
<!--zh-->
其规格与前一条镜像，只是把等式换成了否定等式。
<!--ja-->
その仕様は前のものと鏡像で、等式の代わりに否定された等式が置かれる。
<!--/-->

```agda
      Dw-spec : (z : S) → (fst z ∈ fst Dw)
              ≡ ((fst z ∈ fst D₂) ⊓ ((z ∷ []) ⊨ ¬̇ (var i0 ≐ con ∅ʟ)))
      Dw-spec z = hasSeparationL D₂ (¬̇ (var i0 ≐ con ∅ʟ)) .fst .snd z

```

<!--en-->
Introduction requires membership in `D₂` and a refutation of equality with the empty set.
<!--zh-->
引入要求属于 `D₂`，并要求对「与空集相等」的反驳。
<!--ja-->
導入には、`D₂` への所属と、空集合との相等の反証が要る。
<!--/-->

```agda
    opaque
      Dw-in : (z : S) → ⟨ fst z ∈ fst D₂ ⟩ → (fst z ≡ ∅ → ⊥₀) → ⟨ fst z ∈ fst Dw ⟩
      Dw-in z h ne = subst ⟨_⟩ (sym (Dw-spec z)) (h , λ q → lift (ne q))

```

<!--en-->
Elimination returns membership in `D₂` and the refutation, lowered from the object level.
<!--zh-->
消去返回 `D₂` 的隶属与那条反驳，后者已从对象层降下。
<!--ja-->
消去は `D₂` への所属と、対象レベルから降ろされた反証を返す。
<!--/-->

```agda
      Dw-out : (z : S) → ⟨ fst z ∈ fst Dw ⟩ → ⟨ fst z ∈ fst D₂ ⟩ × (fst z ≡ ∅ → ⊥₀)
      Dw-out z h = r .fst , λ q → lower (r .snd q)
        where
        r : ⟨ fst z ∈ fst D₂ ⟩
          × ⟨ (z ∷ []) ⊨ ¬̇ (var i0 ≐ con ∅ʟ) ⟩
```

<!--en-->
Two unions provide the bounds needed later. `U₁` contains `Z` and the genuinely new part `D₂`, while `U₃` contains the empty-valued part `D∅` and the nonempty witness part `Dw`. The next lemmas prove the required inclusions into these unions.
<!--zh-->
两个并集给出后续所需的界。`U₁` 包含 `Z` 与真正新增的部分 `D₂`，`U₃` 包含空集部分 `D∅` 与非空见证部分 `Dw`。接下来的引理证明到这两个并集的所需包含关系。
<!--ja-->
二つの和集合が後で必要となる上界を与える。`U₁` は `Z` と真に新しい部分 `D₂` を含み、`U₃` は空集合の部分 `D∅` と空でない証人の部分 `Dw` を含む。続く補題は、これらの和集合への必要な包含を証明する。
<!--/-->

```agda
        r = subst ⟨_⟩ (Dw-spec z) h
    module U₁ = Union2 Z D₂ using ( D; in₁; in₂ )
    module U₃ = Union2 D∅ Dw using ( D; in₁; in₂ )

```

<!--en-->
The closure step is covered by the first union. Each member `z` of `ΦZ` either belongs to `Z` or does not, decided by excluded middle; in both cases `z` is constructible, because `ΦZ` is.
<!--zh-->
闭包步骤被第一个并覆盖。`ΦZ` 的每个成员 `z` 要么属于 `Z` 要么不属于，由排中律判定；两种情形下 `z` 都可构造，因为 `ΦZ` 可构造。
<!--ja-->
閉包の段階は第一の和集合で覆われる。`ΦZ` の各要素 `z` は `Z` に属するか属さないかが排中律で決まり、いずれの場合も `ΦZ` が構成可能なので `z` も構成可能である。
<!--/-->

```agda
    ΦZ⊆ : (z : V ℓ) → ⟨ z ∈ˢ fst ΦZ ⟩ → ⟨ z ∈ˢ fst U₁.D ⟩
    ΦZ⊆ z h = go (lem (z ∈ fst Z))
      where
      zS : S
      zS = z , isL-trans {x = fst ΦZ} {y = z} h (snd ΦZ)
```

<!--en-->
The two cases enter `U₁` through its two union inclusions. A member already in `Z` uses the first inclusion; otherwise `D₂-in` first proves that it belongs to the new part, after which the second inclusion applies.
<!--zh-->
两种情形分别经并集的两条包含映入 `U₁`。已经属于 `Z` 的成员使用第一条包含；否则先由 `D₂-in` 证明它属于新增部分，再使用第二条包含。
<!--ja-->
二つの場合は、和集合への二つの包含によって `U₁` に入る。すでに `Z` に属する要素には第一の包含を使い、そうでなければ `D₂-in` で新しい部分への所属を示してから第二の包含を使う。
<!--/-->

```agda
      go : Dec ⟨ z ∈ fst Z ⟩ → ⟨ z ∈ fst U₁.D ⟩
      go (yes hz) = U₁.in₁ zS hz
      go (no nz) = U₁.in₂ zS (D₂-in zS h nz)

```

<!--en-->
The new part is covered by the second union, by the same excluded-middle argument on the equation with the empty set.
<!--zh-->
新部分被第二个并覆盖，同样是对「与空集相等」这条等式使用排中律。
<!--ja-->
新しい部分は第二の和集合で覆われる。これも空集合との等式についての排中律によるものである。
<!--/-->

```agda
    D₂⊆ : (z : V ℓ) → ⟨ z ∈ˢ fst D₂ ⟩ → ⟨ z ∈ˢ fst U₃.D ⟩
    D₂⊆ z h = go (lem ((z ≡ ∅) , setIsSet z ∅))
      where
      zS : S
      zS = z , isL-trans {x = fst D₂} {y = z} h (snd D₂)
```

<!--en-->
An element equal to the empty set enters through `D∅`; an element distinct from it enters through `Dw`.
<!--zh-->
等于空集的元素经 `D∅` 进入；与之不同的元素经 `Dw` 进入。
<!--ja-->
空集合と等しい要素は `D∅` から入り、異なる要素は `Dw` から入る。
<!--/-->

```agda
      go : Dec (z ≡ ∅) → ⟨ z ∈ fst U₃.D ⟩
      go (yes e) = U₃.in₁ zS (D∅-in zS h e)
      go (no ne) = U₃.in₂ zS (Dw-in zS h ne)
```

<!--en-->
Every member of `D∅` equals `∅`, although `D∅` itself may be empty. Since the numeral `0` belongs to `κ`, inclusion coding therefore gives `D∅ ↪ κ` inside `L`.
<!--zh-->
`D∅` 的每个成员都等于 `∅`，但 `D∅` 本身可能为空。由于数码 `0` 属于 `κ`，包含编码因而在 `L` 内给出 `D∅ ↪ κ`。
<!--ja-->
`D∅` の各要素は `∅` に等しいが、`D∅` 自体は空であるかもしれない。数項 `0` が `κ` に属するので、包含の符号化から `L` の内部で `D∅ ↪ κ` が得られる。
<!--/-->

```agda
    D∅↪κ : InjL D∅ κ
    D∅↪κ = inclusion-coded D∅ κ
      (λ z hz → subst (λ w → ⟨ w ∈ fst κ ⟩)
        (sym (D∅-out (z , isL-trans {x = fst D∅} {y = z} hz (snd D∅)) hz .snd)) (num∈κ 0))
```

<!--en-->
A second union prepares the coding of witnesses: `U₂` joins the elements born by stage `ω` with the finite sequences of members of `Z`.
<!--zh-->
第二个并为见证的编码做准备：`U₂` 连接「诞生于层 `ω` 的元素」与「`Z` 成员的有穷序列」。
<!--ja-->
第二の和集合が証人の符号化の準備をする。`U₂` は、段階 `ω` で生まれる要素と、`Z` の要素の有限列をつなぐ。
<!--/-->

```agda
    module U₂ = Union2 Lω (seqL Z) using ( D; in₁; in₂ )

```

<!--en-->
Let `PB` be the square of `U₂ = Lω ∪ seqL Z`. Every actual witness code `(s,e)`, with `s ∈ Lω` and `e ∈ seqL Z`, lies in `PB`; `PB` is a homogeneous upper bound and also contains pairs that are not valid witness codes.
<!--zh-->
令 `PB` 为 `U₂ = Lω ∪ seqL Z` 的平方。每个实际见证码 `(s,e)`，其中 `s ∈ Lω` 且 `e ∈ seqL Z`，都属于 `PB`；`PB` 是一个齐次上界，也包含并非有效见证码的对。
<!--ja-->
`PB` を `U₂ = Lω ∪ seqL Z` の平方とする。`s ∈ Lω` かつ `e ∈ seqL Z` である実際の証人符号 `(s,e)` はすべて `PB` に属する。ただし `PB` は一様な上界であり、有効な証人符号でない対も含む。
<!--/-->

```agda
    PB : S
    PB = prodL U₂.D

```

<!--en-->
The least-witness formula is pinned at the fixed base `Z`. The resulting five-variable formula `pin₅` is satisfied at the frame `(e,s,z,p,q)` exactly when `z` is the least witness determined by the environment `e` and key `s`; the last two slots are carried by the surrounding frame.
<!--zh-->
最小见证公式在固定基 `Z` 处被钉定。所得的五变元公式 `pin₅` 在框架 `(e,s,z,p,q)` 上成立，恰当且仅当 `z` 是由环境 `e` 与键 `s` 确定的最小见证；最后两个槽位由外围框架携带。
<!--ja-->
最小証人の論理式を固定した基 `Z` に釘付けする。得られる五変数の論理式 `pin₅` は、枠 `(e,s,z,p,q)` において、`z` が環境 `e` と鍵 `s` によって定まる最小証人であるとき、かつそのときに限り満たされる。最後の二つのスロットは周囲の枠が運ぶ。
<!--/-->

```agda
    opaque
      pin₅ : Formula S 5
      pin₅ = pinAt Z B.leastWitnessFo

```

<!--en-->
Inward, a least witness for `z` at the parameter environment `e` with key `s` yields the satisfaction of the pinned formula at the five-slot context.
<!--zh-->
向内：以参数环境 `e` 与键 `s` 给出的 `z` 的最小见证，产生钉定公式在五槽位语境处的满足。
<!--ja-->
内向きには、パラメータの環境 `e` と鍵 `s` による `z` の最小証人が、五スロットの文脈での釘付けされた論理式の充足を与える。
<!--/-->

```agda
      pin₅-in : (e s z p q : S) → B.LeastWitness Z e s z
              → ⟨ (e ∷ s ∷ z ∷ p ∷ q ∷ []) ⊨ pin₅ ⟩
      pin₅-in e s z p q h =
        pin-in Z B.leastWitnessFo (e ∷ s ∷ z ∷ p ∷ q ∷ [])
          (B.leastWitness-in Z e s z p q h)
```

<!--en-->
Outward, satisfaction of the pinned formula unpacks to a least witness, the pinning being inverted by the pinning lemma.
<!--zh-->
向外：钉定公式的满足可拆包为最小见证，钉定的逆操作由钉定引理完成。
<!--ja-->
外向きには、釘付けされた論理式の充足が最小証人へと展開される。釘付けをほどくのは釘付けの補題である。
<!--/-->

```agda

      pin₅-out : (e s z p q : S) → ⟨ (e ∷ s ∷ z ∷ p ∷ q ∷ []) ⊨ pin₅ ⟩
               → B.LeastWitness Z e s z
      pin₅-out e s z p q h =
        B.leastWitness-out Z e s z p q
          (pin-out Z B.leastWitnessFo (e ∷ s ∷ z ∷ p ∷ q ∷ []) h)
```

<!--en-->
The relation to be counted is propositionally truncated. `GW p z` says merely that there are a key `s` and an environment `e` such that `p = (s,e)` and `z` is their least witness.
<!--zh-->
待计数的关系经过命题截断。`GW p z` 仅仅断言存在一个键 `s` 与一个环境 `e`，使 `p = (s,e)`，且 `z` 是由二者确定的最小见证。
<!--ja-->
数える関係は命題的に切り詰められている。`GW p z` は、鍵 `s` と環境 `e` が存在し、`p = (s,e)` であり、`z` がそれらによって定まる最小証人であることを単に述べる。
<!--/-->

```agda
    GW : (p z : S) → Type (ℓ-suc ℓ)
    GW p z = ∥ Σ[ s ∈ S ] Σ[ e ∈ S ]
               ((fst p ≡ pr (fst s) (fst e)) × B.LeastWitness Z e s z) ∥₁
```

<!--en-->
The same relation is written as a formula: two existentials bind the key and the environment, the pairing atom identifies `p`, and the pinned formula carries the witness condition.
<!--zh-->
同一关系也写成公式：两个存在量词绑定键与环境，配对原子确定 `p`，钉定公式承载见证条件。
<!--ja-->
同じ関係は論理式としても書かれる。二つの存在量化子が鍵と環境を束縛し、対の原子が `p` を確定し、釘付けされた論理式が証人の条件を運ぶ。
<!--/-->

```agda
    opaque
      se₃ : Formula S 3
      se₃ = ∃̇ (∃̇ (prAtL i3 i1 i0 ∧̇ pin₅))

```

<!--en-->
Inward: given the pair equation and a least witness, the two witnesses are entered and the pair atom is transported along its adequacy into the object language.
<!--zh-->
向内：给定对等式与最小见证，填入两个见证，并把配对原子沿其充分性传输进对象语言。
<!--ja-->
内向きには、対の等式と最小証人が与えられれば、二つの証人を入れ、対の原子をその妥当性に沿って対象言語へ輸送する。
<!--/-->

```agda
      se₃-in : (z p q s e : S) → fst p ≡ pr (fst s) (fst e)
             → B.LeastWitness Z e s z → ⟨ (z ∷ p ∷ q ∷ []) ⊨ se₃ ⟩
      se₃-in z p q s e qp h =
        ∣ s , ∣ e , ( subst ⟨_⟩ (sym (prAtL-adequate i3 i1 i0 (e ∷ s ∷ z ∷ p ∷ q ∷ []))) qp
                    , pin₅-in e s z p q h ) ∣₁ ∣₁
```

<!--en-->
Outward, the two existentials are consumed one at a time; the first step strips the outer quantifier and keeps the entry `s` with the truncated remainder.
<!--zh-->
向外时逐个消耗两个存在量词；第一步剥去外层量词，保留条目 `s` 与截断的剩余部分。
<!--ja-->
外向きには、二つの存在量化子を一度に一つずつ消費する。最初の段階で外側の量化子をはぎ、項目 `s` と切り詰められた残りを取っておく。
<!--/-->

```agda

      se₃-out : (z p q : S) → ⟨ (z ∷ p ∷ q ∷ []) ⊨ se₃ ⟩ → GW p z
      se₃-out z p q = rec₁ squash₁ at₁
        where
        at₂ : (s : S) → Σ[ e ∈ S ] ( ⟨ (e ∷ s ∷ z ∷ p ∷ q ∷ []) ⊨ prAtL i3 i1 i0 ⟩
                                   × ⟨ (e ∷ s ∷ z ∷ p ∷ q ∷ []) ⊨ pin₅ ⟩ ) → GW p z
```

<!--en-->
After the second existential is opened, adequacy of the pairing atom recovers `p = (s,e)`, and the outward reading of the pinned formula recovers the least-witness condition. These witnesses are then placed back under the propositional truncation defining `GW`.
<!--zh-->
打开第二个存在量词后，配对原子的充分性恢复出 `p = (s,e)`，钉定公式的向外读式则恢复最小见证条件。随后把这些见证重新置于定义 `GW` 的命题截断之下。
<!--ja-->
二つ目の存在量化子を開くと、対を表す原子式の妥当性から `p = (s,e)` が得られ、釘付けされた論理式の外向きの読みから最小証人の条件が得られる。これらの証人を、`GW` を定義する命題的切り詰めの中へ戻す。
<!--/-->

```agda
        at₂ s (e , (qp , h)) = ∣ s , e
          , ( subst ⟨_⟩ (prAtL-adequate i3 i1 i0 (e ∷ s ∷ z ∷ p ∷ q ∷ [])) qp
            , pin₅-out e s z p q h ) ∣₁
        at₁ : Σ[ s ∈ S ] ∥ Σ[ e ∈ S ] ( ⟨ (e ∷ s ∷ z ∷ p ∷ q ∷ []) ⊨ prAtL i3 i1 i0 ⟩
                                      × ⟨ (e ∷ s ∷ z ∷ p ∷ q ∷ []) ⊨ pin₅ ⟩ ) ∥₁ → GW p z
```

<!--en-->
Because `GW p z` is a proposition, the remaining outer truncation can be eliminated into it. Together, `se₃-in` and `se₃-out` give the two implications between the host relation `GW` and satisfaction of its object-language formula.
<!--zh-->
由于 `GW p z` 是命题，剩余的外层截断可以消去到其中。`se₃-in` 与 `se₃-out` 合起来给出宿主关系 `GW` 与其对象语言公式的满足之间的两个方向。
<!--ja-->
`GW p z` は命題なので、残る外側の切り詰めをそこへ消去できる。`se₃-in` と `se₃-out` を合わせると、ホスト側の関係 `GW` と、それを表す対象言語の論理式の充足との間の二つの含意が得られる。
<!--/-->

```agda
        at₁ (s , h) = rec₁ squash₁ (at₂ s) h
```

<!--en-->
Bounded separation constructs a relation `G` inside `L` whose entries are ordered pairs `(p,z)` with `p ∈ PB`, `z ∈ Dw`, and `GW p z`. Thus `G` restricts the least-witness relation to the chosen code pool and the nonempty new part.
<!--zh-->
有界分离在 `L` 内构造关系 `G`；它的条目是有序对 `(p,z)`，其中 `p ∈ PB`、`z ∈ Dw` 且 `GW p z`。因此，`G` 把最小见证关系限制在选定的码池与非空新增部分之间。
<!--ja-->
有界分出により、`L` の内部に関係 `G` を構成する。その項目は、`p ∈ PB`、`z ∈ Dw`、`GW p z` を満たす順序対 `(p,z)` である。したがって `G` は、最小証人の関係を選んだ符号の池と空でない新しい部分の間に制限する。
<!--/-->

```agda
    private
      module WitnessGraph = Relation PB Dw ((var i1 ∈̇ con PB) ∧̇ se₃)
        (λ p z → (fst p ∈ fst PB) ⊓ (GW p z , squash₁))
        (λ p z q h → h .fst , se₃-out z p q (h .snd))
        (λ p z q h → h .fst , rec₁ (snd ((z ∷ p ∷ q ∷ []) ⊨ se₃))
```

<!--en-->
The outward reading of the describing condition is the formula's own outward reading, which returns exactly the data of `GW`.
<!--zh-->
描述条件的外向读法就是公式自身的外向读法，它返回的恰是 `GW` 的数据。
<!--ja-->
記述の条件の外向きの読みは、論理式そのものの外向きの読みであり、返ってくるのはまさに `GW` のデータである。
<!--/-->

```agda
          (λ { (s , e , qp , hw) → se₃-in z p q s e qp hw }) (h .snd))

```

<!--en-->
`G` is the resulting constructible relation, represented as a set of ordered pairs `(p,z)`. It relates a candidate code in `PB` to an element of `Dw` when that code carries least-witness data for the element.
<!--zh-->
`G` 是所得的可构造关系，表示为有序对 `(p,z)` 的集合。当 `PB` 中的候选码携带某个 `Dw` 元素的最小见证数据时，`G` 便把二者关联起来。
<!--ja-->
`G` は、順序対 `(p,z)` の集合として表された構成可能な関係である。`PB` の候補符号が `Dw` の要素について最小証人のデータを運ぶとき、`G` はその符号と要素を関係づける。
<!--/-->

```agda
    G : S
    G = WitnessGraph.rel

```

<!--en-->
Inward: a code `p` in `PB` that, together with `z`, names a least witness through some key and environment, belongs to `G`.
<!--zh-->
向内：`PB` 中的码 `p` 若经由某个键与环境同 `z` 一起指名一个最小见证，则属于 `G`。
<!--ja-->
内向きには、`PB` の符号 `p` が、ある鍵と環境を通して `z` とともに最小証人を名指すなら、`G` に属する。
<!--/-->

```agda
    G-in : (p z : S) → ⟨ fst p ∈ fst PB ⟩ → ⟨ fst z ∈ fst Dw ⟩
         → (s e : S) → fst p ≡ pr (fst s) (fst e)
         → B.LeastWitness Z e s z → Holds G p z
    G-in p z hp hz s e qp h =
      WitnessGraph.into p z hp hz (hp , ∣ s , e , qp , h ∣₁)
```

<!--en-->
Conversely, `Holds G p z` yields both `p ∈ PB` and the propositionally truncated witness data `GW p z`. It does not choose a key and environment outside that truncation.
<!--zh-->
反过来，`Holds G p z` 同时给出 `p ∈ PB` 与经过命题截断的见证数据 `GW p z`。它不会在该截断之外选出键与环境。
<!--ja-->
逆に、`Holds G p z` から `p ∈ PB` と、命題的に切り詰められた証人データ `GW p z` の両方が得られる。切り詰めの外で鍵と環境を選ぶわけではない。
<!--/-->

```agda

    G-out : (p z : S) → Holds G p z → ⟨ fst p ∈ fst PB ⟩ × GW p z
    G-out = WitnessGraph.pair-out
```

<!--en-->
The relation is total on `Dw` only in the truncated sense: every `z ∈ Dw` merely has some `p` with `Holds G p z`. Reading membership in `ΦZ` exposes the three possible reasons why `z` entered the closure step.
<!--zh-->
该关系只在截断意义下对 `Dw` 整体：每个 `z ∈ Dw` 都仅仅存在某个满足 `Holds G p z` 的 `p`。向外读取 `z ∈ ΦZ` 会给出它进入闭包步的三种可能原因。
<!--ja-->
この関係が `Dw` 上で全域的なのは切り詰められた意味においてである。各 `z ∈ Dw` には `Holds G p z` を満たす `p` が単に存在する。`z ∈ ΦZ` を外向きに読むと、`z` が閉包に入った三つの可能な理由が現れる。
<!--/-->

```agda
    have : (z : S) → ⟨ fst z ∈ fst Dw ⟩ → ∥ Σ[ p ∈ S ] Holds G p z ∥₁
    have z hz = rec₁ squash₁ body (B.Φ-out Z z (D₂-out z (Dw-out z hz .fst) .fst))
      where
      body : B.Body Z z → ∥ Σ[ p ∈ S ] Holds G p z ∥₁
      body (inl h) = ⊥₀-rec (D₂-out z (Dw-out z hz .fst) .snd h)
```

<!--en-->
Two of them are already excluded by the separators: `z` cannot be an old member of `Z`, nor the empty set. What remains is the witness case, read through the outward lemma of the witness formula.
<!--zh-->
其中两种已被分离器排除：`z` 不能是 `Z` 的旧成员，也不能是空集。剩下的就是见证情形，经见证公式的外向引理读取。
<!--ja-->
そのうちの二つはすでに分出によって排除されている。`z` は `Z` の古い要素でも空集合でもあり得ない。残るのは証人の場合であり、証人の論理式の外向きの補題を通して読まれる。
<!--/-->

```agda
      body (inr (inl e)) = ⊥₀-rec (Dw-out z hz .snd e)
      body (inr (inr hw)) = rec₁ squash₁ read (B.witFo-leastWitness z Z hw)
        where
        read : Σ[ e ∈ S ] Σ[ s ∈ S ] B.LeastWitness Z e s z
             → ∥ Σ[ p ∈ S ] Holds G p z ∥₁
```

<!--en-->
The witness branch supplies an environment `e`, a key `s`, and a least witness. Its data lemma then gives a natural length `n`, a meta-level assignment `g : Fin n → ⟪Z⟫`, an equation identifying `e` with the encoded environment of `g`, and the membership `s ∈ Lset ω`.
<!--zh-->
见证分支给出环境 `e`、键 `s` 与一个最小见证。其数据引理随后给出自然数长度 `n`、元层赋值 `g : Fin n → ⟪Z⟫`、把 `e` 认同为 `g` 的编码环境的等式，以及成员资格 `s ∈ Lset ω`。
<!--ja-->
証人の枝は、環境 `e`、鍵 `s`、最小証人を与える。そのデータ補題から、自然数の長さ `n`、メタレベルの割り当て `g : Fin n → ⟪Z⟫`、`e` を `g` の符号化された環境と同一視する等式、そして `s ∈ Lset ω` が得られる。
<!--/-->

```agda
        read (e , s , hw') = map₁ at (B.leastWitness-data Z e s z hw')
          where
          at : B.LeastWitnessData Z e s → Σ[ p ∈ S ] Holds G p z
          at (n , g , qe , hs) = prʟ s e
            , G-in (prʟ s e) z
```

<!--en-->
The code `p` is the internal pair of the key and the environment. Its membership in `PB` is built entry by entry: the key enters through `Lω` because it lies in `Lset ω`, and the environment enters through the finite sequences of `Z`, being the environment of a length-`n` assignment into `Z`. The relation then accepts the pair.
<!--zh-->
码 `p` 是键与环境组成的内部对。它属于 `PB` 的证明逐条目建立：键因落在 `Lset ω` 而经 `Lω` 进入，环境因为是「到 `Z` 的长度 `n` 赋值」的环境而经 `Z` 的有限序列进入。随后该关系接受这个对。
<!--ja-->
符号 `p` は鍵と環境の内部の対である。その `PB` への所属は項目ごとに築かれる。鍵は `Lset ω` に属するため `Lω` から入り、環境は `Z` への長さ `n` の割り当ての環境であるため `Z` の有限列から入る。そして関係がこの対を受け入れる。
<!--/-->

```agda
                (subst (λ w → ⟨ w ∈ fst PB ⟩) (sym (prʟ-fst s e))
                  (prodL-in U₂.D s e (U₂.in₁ s hs)
                    (U₂.in₂ e (seqL-in Z n e
                      (subst (λ w → ⟨ w ∈ˢ fst (envSet Z n) ⟩) (sym qe) (envSet-in Z g))))))
                hz s e (prʟ-fst s e) hw'
```

<!--en-->
## Uniqueness for a witness key
<!--zh-->
## 见证键的唯一性
<!--ja-->
## 証人キーに対する一意性
<!--/-->

<!--en-->
The required functionality has the reverse orientation needed for counting: if one fixed code `p` is related both to `z` and to `z'`, then `z` and `z'` have equal underlying sets. Different codes for the same element are still allowed.
<!--zh-->
所需的函数性具有计数论证所需的反向取向：若同一个固定码 `p` 同时关联 `z` 与 `z'`，则 `z` 与 `z'` 的底层集合相等。同一个元素仍可拥有不同的码。
<!--ja-->
必要な関数性は、計数に必要な逆向きの形をしている。一つの固定した符号 `p` が `z` と `z'` の両方に関係するなら、`z` と `z'` の底の集合は等しくなる。同じ要素に異なる符号があることは依然として許される。
<!--/-->

```agda
    funct : (p z z' : S) → Holds G p z → Holds G p z' → fst z ≡ fst z'
    funct p z z' h h' = rec2 (setIsSet (fst z) (fst z')) read (G-out p z h .snd) (G-out p z' h' .snd)
      where
      read : Σ[ s ∈ S ] Σ[ e ∈ S ]
               ((fst p ≡ pr (fst s) (fst e)) × B.LeastWitness Z e s z)
```

<!--en-->
Both relations are read outward, each returning a key, an environment, the pair equation, and a least witness.
<!--zh-->
两条关系都向外读出，各自返回一个键、一个环境、一条对等式与一个最小见证。
<!--ja-->
二つの関係は外向きに読まれ、それぞれ鍵、環境、対の等式、そして最小証人を返す。
<!--/-->

```agda
           → Σ[ s₂ ∈ S ] Σ[ e₂ ∈ S ]
               ((fst p ≡ pr (fst s₂) (fst e₂)) × B.LeastWitness Z e₂ s₂ z')
           → fst z ≡ fst z'
      read (s , e , q , hw) (s₂ , e₂ , q₂ , hw₂) =
        B.leastWitness-unique Z e s z z' hw hw₂'
```

<!--en-->
Both readings express the same fixed `p` as `(s,e)` and `(s₂,e₂)`. Injectivity of ordered-pair coding identifies the two keys and the two environments at the level of underlying sets, and proof irrelevance lifts those equalities to the corresponding elements of `S`.
<!--zh-->
两次读取把同一个固定的 `p` 分别表示为 `(s,e)` 与 `(s₂,e₂)`。有序对编码的单射性在底层集合层面认同两个键与两个环境，证明无关性再把这些等式提升为相应 `S` 元素的等式。
<!--ja-->
二つの読み出しは、同じ固定した `p` をそれぞれ `(s,e)` と `(s₂,e₂)` として表す。順序対の符号化の単射性が、二つの鍵と二つの環境を底の集合の水準で同一視し、証明無関連性がそれらを対応する `S` の要素の等式へ持ち上げる。
<!--/-->

```agda
        where
        ee : (fst s₂ ≡ fst s) × (fst e₂ ≡ fst e)
        ee = pr-inj (sym q₂ ∙ q)
        hw₂' : B.LeastWitness Z e s z'
        hw₂' = subst2 (λ e' s' → B.LeastWitness Z e' s' z')
```

<!--en-->
After transporting the second least-witness proof along those identifications, both proofs concern the same key and environment. Least-witness uniqueness then gives `fst z ≡ fst z'`.
<!--zh-->
沿这些等同运输第二份最小见证证明后，两份证明便针对同一个键与环境。最小见证唯一性于是给出 `fst z ≡ fst z'`。
<!--ja-->
それらの同一視に沿って二つ目の最小証人の証明を輸送すると、二つの証明は同じ鍵と環境に関するものになる。そこで最小証人の一意性から `fst z ≡ fst z'` が得られる。
<!--/-->

```agda
          (S≡ {x = e₂} {y = e} (snd ee)) (S≡ {x = s₂} {y = s} (fst ee)) hw₂
```

<!--en-->
The code pool has a birth stage: `γG` is the stage at which `PB` appears in the hierarchy.
<!--zh-->
码池有自己的诞生层：`γG` 是 `PB` 在层级中出现的那个层。
<!--ja-->
符号の池には誕生の段階がある。`γG` は `PB` が階層に現れる段階である。
<!--/-->

```agda
    γG : V ℓ
    γG = stage (fst PB) (snd PB)

```

<!--en-->
That stage is indexed by an ordinal, which is what the counting lemma requires of it.
<!--zh-->
该层由一个序数索引，这正是计数引理对它的要求。
<!--ja-->
その段階は順序数で添字づけられており、計数の補題が要求するのはこれである。
<!--/-->

```agda
    oγG : IsOrd γG
    oγG = stage-ord (fst PB) (snd PB)

```

<!--en-->
The pool is contained in its birth stage, by the transitivity of the stages: a member of a set born at `γG` belongs to `Lset γG`.
<!--zh-->
池包含于其诞生层，由层的传递性得出：诞生于 `γG` 的集合的成员属于 `Lset γG`。
<!--ja-->
池はその誕生の段階に含まれる。段階の推移性によるものである。`γG` で生まれた集合の要素は `Lset γG` に属する。
<!--/-->

```agda
    PB⊆Lγ : (p : S) → ⟨ fst p ∈ fst PB ⟩ → ⟨ fst p ∈ Lset γG ⟩
    PB⊆Lγ p hp = layer-trans (Lset-layer γG) {x = fst PB} {y = fst p} hp (stage-mem (fst PB) (snd PB))

```

<!--en-->
The hypotheses now instantiate `LeastPre`: every `z ∈ Dw` merely has a related code in `PB`, and a fixed code determines at most one such `z`. Least selection chooses one code for each element and yields `InjL Dw PB`. It does not assert that witness codes were unique beforehand, and this is only the count of the nonempty new part, not yet the full one-step result.
<!--zh-->
这些假设现在实例化 `LeastPre`：每个 `z ∈ Dw` 都仅仅存在某个与之关联的 `PB` 中的码，而固定一个码至多确定一个这样的 `z`。最小选择为每个元素选取一个码，并给出 `InjL Dw PB`。它不声称见证码原本就唯一，而且这里得到的只是非空新增部分的计数，尚非完整的单步结论。
<!--ja-->
これらの仮定によって `LeastPre` を具体化する。各 `z ∈ Dw` には `PB` にある関係づけられた符号が単に存在し、固定した一つの符号はそのような `z` を高々一つ定める。最小選択が各要素について一つの符号を選び、`InjL Dw PB` を与える。証人符号が初めから一意だったとは主張せず、ここで数えたのは空でない新しい部分だけで、閉包一段階全体の結論ではない。
<!--/-->

```agda
    module LP = LeastPre γG oγG G Dw PB (λ p z h → G-out p z h .fst) PB⊆Lγ have
      using ( module Functional )

```

<!--en-->
The least-preimage construction injects the genuinely new witnesses into `PB`. Each `z ∈ Dw` merely has some related code, and the stage order selects the least such code. Codes need not be unique before selection; injectivity follows instead because a fixed code can represent only one witness.
<!--zh-->
最小原像构造把真正新的见证单射入 `PB`。每个 `z ∈ Dw` 仅仅具有某个相关码，而层序选出其中最小者。选取之前码无须唯一；单射性来自一个固定码至多表示一个见证。
<!--ja-->
最小原像の構成は、真に新しい証人を `PB` へ単射する。各 `z ∈ Dw` には関連する符号が単に存在し、段階順序がその最小のものを選ぶ。選択前の符号は一意である必要はない。単射性は、一つの固定した符号が高々一つの証人しか表さないことから従う。
<!--/-->

```agda
    Dw↪PB : InjL Dw PB
    Dw↪PB = LP.Functional.injL funct

```

<!--en-->
The injection `Z ↪ κ` acts coordinatewise on finite sequences, giving `seqL Z ↪ seqL κ`. Composing with finite-sequence counting yields `seqL Z ↪ κ`; this second map requires only that `κ` be an infinite ordinal, not that it be an internal cardinal.
<!--zh-->
单射 `Z ↪ κ` 逐坐标作用于有限序列，得到 `seqL Z ↪ seqL κ`。再与有限序列计数复合，便得到 `seqL Z ↪ κ`；后一个映射只要求 `κ` 是无穷序数，并不要求它是内部基数。
<!--ja-->
単射 `Z ↪ κ` を有限列の各成分に作用させると、`seqL Z ↪ seqL κ` が得られる。これを有限列の数え上げと合成して `seqL Z ↪ κ` を得る。後者に必要なのは `κ` が無限順序数であることだけで、内部の基数である必要はない。
<!--/-->

```agda
    seq↪κ : InjL (seqL Z) κ
    seq↪κ = injl-trans (seqL Z) (seqL κ) κ (seq-map Z κ E cE) (seq-count κ oκ κ∉ω)

```

<!--en-->
First count `U₂.D = Lω ∪ seqL Z`: tagging its two summands gives an injection into `κ × κ`, and `pairκ` folds that product into `κ`. Since `PB = U₂.D × U₂.D`, `prod-inj` lifts this injection to `PB ↪ κ × κ`; a second use of `pairκ` then gives `PB ↪ κ`. The two folds are the steps that use the square law and hence internal cardinality.
<!--zh-->
先计数 `U₂.D = Lω ∪ seqL Z`：给两个分支加标签得到到 `κ × κ` 的单射，再由 `pairκ` 把该乘积折入 `κ`。由于 `PB = U₂.D × U₂.D`，`prod-inj` 把这个单射提升为 `PB ↪ κ × κ`；第二次使用 `pairκ` 才得到 `PB ↪ κ`。两次折叠都使用平方律，因而都依赖内部基数性。
<!--ja-->
まず `U₂.D = Lω ∪ seqL Z` を数える。二つの集合にタグを付けて `κ × κ` へ単射し、`pairκ` でその積を `κ` へ折りたたむ。`PB = U₂.D × U₂.D` なので、`prod-inj` がこの単射を `PB ↪ κ × κ` へ持ち上げ、`pairκ` をもう一度使うと `PB ↪ κ` が得られる。二回の折りたたみは平方則を用いるため、内部の基数性に依存する。
<!--/-->

```agda
    PB↪κ : InjL PB κ
    PB↪κ = injl-trans PB (prodL κ) κ
      (prod-inj U₂.D κ
        (injl-trans U₂.D (prodL κ) κ (tag-union κ (num∈κ 0) (num∈κ 1) Lω (seqL Z) Lω↪κ seq↪κ) pairκ))
      pairκ
```

<!--en-->
Composing the two injections gives the count of the genuinely new witnesses: every such witness is coded by some `p ∈ PB`, and `PB` injects into `κ`, so `Dw` injects into `κ`.
<!--zh-->
复合这两个单射即得真正新见证的计数：每个这样的见证都被某个 `p ∈ PB` 编码，而 `PB` 单射入 `κ`，故 `Dw` 单射入 `κ`。
<!--ja-->
二つの単射を合成すれば、真に新しい証人の数え上げが得られる。そのような証人はそれぞれある `p ∈ PB` で符号化され、`PB` は `κ` へ単射するので、`Dw` も `κ` へ単射する。
<!--/-->

```agda

    Dw↪κ : InjL Dw κ
    Dw↪κ = injl-trans Dw PB κ Dw↪PB PB↪κ

```

<!--en-->
The new part `D₂` is included in `D∅ ∪ Dw`. Here `D∅` contains precisely the new members equal to the empty set and may itself be empty, while `Dw` contains the nonempty witness members. Their two counts are tagged into `κ × κ` and folded by `pairκ`, giving `D₂ ↪ κ`.
<!--zh-->
新部分 `D₂` 包含于 `D∅ ∪ Dw`。其中 `D∅` 恰含等于空集的新成员，并且自身可能为空；`Dw` 则含非空的见证成员。两部分的计数加标签后进入 `κ × κ`，再由 `pairκ` 折叠，得到 `D₂ ↪ κ`。
<!--ja-->
新しい部分 `D₂` は `D∅ ∪ Dw` に含まれる。`D∅` は空集合に等しい新しい要素だけを含み、それ自身が空の場合もある。`Dw` は空でない証人の要素を含む。二つの数え上げにタグを付けて `κ × κ` へ入れ、`pairκ` で折りたたすと `D₂ ↪ κ` が得られる。
<!--/-->

```agda
    D₂↪κ : InjL D₂ κ
    D₂↪κ = injl-trans D₂ U₃.D κ (inclusion-coded D₂ U₃.D D₂⊆)
      (injl-trans U₃.D (prodL κ) κ (tag-union κ (num∈κ 0) (num∈κ 1) D∅ Dw D∅↪κ Dw↪κ) pairκ)

```

<!--en-->
Every member of `ΦZ` lies in `Z ∪ D₂`. The given graph `E` counts `Z`, while the preceding construction counts `D₂`; tagging these injections gives a map into `κ × κ`, and `pairκ` completes the injection `ΦZ ↪ κ`.
<!--zh-->
`ΦZ` 的每个成员都属于 `Z ∪ D₂`。给定图 `E` 计数 `Z`，前面的构造计数 `D₂`；给两条单射加标签可得到到 `κ × κ` 的映射，再由 `pairκ` 完成单射 `ΦZ ↪ κ`。
<!--ja-->
`ΦZ` の各要素は `Z ∪ D₂` に属する。与えられたグラフ `E` が `Z` を数え、先の構成が `D₂` を数える。この二つの単射にタグを付けて `κ × κ` へ写し、`pairκ` と合成すると `ΦZ ↪ κ` が得られる。
<!--/-->

```agda
    result : InjL ΦZ κ
    result = injl-trans ΦZ U₁.D κ (inclusion-coded ΦZ U₁.D ΦZ⊆)
      (injl-trans U₁.D (prodL κ) κ (tag-union κ (num∈κ 0) (num∈κ 1) Z D₂ ∣ E , cE ∣₁ D₂↪κ) pairκ)

```

<!--en-->
`step-count` eliminates the truncated witness of `Z ↪ κ` into the proposition `ΦZ ↪ κ`. It therefore proves a cardinal bound by `κ`, rather than countability, and it does not select a graph witnessing the output injection.
<!--zh-->
`step-count` 把 `Z ↪ κ` 的截断见证消去到命题 `ΦZ ↪ κ` 中。因此它证明的是由 `κ` 给出的基数界，并非可数性；它也不选择见证输出单射的图。
<!--ja-->
`step-count` は `Z ↪ κ` の切り詰められた証人を、命題 `ΦZ ↪ κ` へ除去する。したがって示しているのは `κ` による濃度の上界であり、可算性ではない。また、出力の単射を証すグラフを選択しない。
<!--/-->

```agda
  step-count : (Z : S) → ((z : V ℓ) → ⟨ z ∈ˢ fst Z ⟩ → ⟨ z ∈ˢ Lset lam ⟩)
             → InjL Z κ → InjL (B.Φ Z) κ
  step-count Z Z⊆ = rec₁ squash₁ (λ { (E , cE) → OneStep.result Z Z⊆ E cE })
```

<!--en-->
Every member of every finite closure iterate lies in the ambient stage `Lset lam`: this follows from the iterates being contained in the hull, whose members all lie in the stage.
<!--zh-->
每个有限闭包迭代的成员都位于外围层 `Lset lam` 中：这由诸迭代包含于壳、而壳的成员都在该层中得出。
<!--ja-->
有限閉包の各反復の要素は、すべて周囲の段階 `Lset lam` の中にある。これは、反復が包に含まれ、包の要素がすべて段階の中にあることから従う。
<!--/-->

```agda
  iter⊆L : (n : ℕ) (z : V ℓ) → ⟨ z ∈ˢ fst (hullStep n) ⟩ → ⟨ z ∈ˢ Lset lam ⟩
  iter⊆L n z hz = HSH.Hull⊆L z (Cn.hullStep⊆Hull n z hz)

```

<!--en-->
Natural-number induction gives a separate internal injection for every finite iterate. The base case is the assumed injection of the starting set, and the successor case applies `step-count`. These witnesses remain propositionally truncated, so they cannot simply be chosen simultaneously to count the union.
<!--zh-->
自然数归纳为每个有限迭代分别给出一条内部单射。基础情形使用起始集合的已知单射，后继情形应用 `step-count`。这些见证仍经过命题截断，因而不能直接同时选出并用来计数其并。
<!--ja-->
自然数についての帰納法により、有限な各反復について個別の内部単射が得られる。基底の場合は始集合の仮定された単射を使い、後続の場合は `step-count` を適用する。これらの証人は命題的に切り詰められたままなので、同時に選んでその和集合を数えることはできない。
<!--/-->

```agda
  counted : (n : ℕ) → InjL (hullStep n) κ
  counted zero    = base
  counted (suc n) = step-count (hullStep n) (iter⊆L n) (counted n)
```

<!--en-->
`HoldsAt n σ` is the propositionally truncated assertion that some constructible graph `F ∈ Lset σ` codes an injection `hullStep n ↪ κ`. It records both the stage containing the code and the exact iterate that the code counts.
<!--zh-->
`HoldsAt n σ` 是经过命题截断的断言：某个可构造图 `F ∈ Lset σ` 编码单射 `hullStep n ↪ κ`。它同时记录容纳该码的层以及该码所计数的准确迭代。
<!--ja-->
`HoldsAt n σ` は、ある構成可能なグラフ `F ∈ Lset σ` が単射 `hullStep n ↪ κ` を符号化するという、命題的に切り詰められた主張である。符号を含む段階と、その符号が数える正確な反復の両方を記録する。
<!--/-->

```agda
  HoldsAt : ℕ → V ℓ → hProp (ℓ-suc ℓ)
  HoldsAt n σ = ∥ Σ[ F ∈ S ] (⟨ fst F ∈ Lset σ ⟩ × InjCode F (hullStep n) κ) ∥₁ , squash₁

```

<!--en-->
For each `n`, let `ls n` be the least ordinal stage satisfying `HoldsAt n`. The truncated injection supplied by `counted n` provides existence, and least-ordinal selection is valid because the resulting leastness statement is a proposition.
<!--zh-->
对每个 `n`，令 `ls n` 为满足 `HoldsAt n` 的最小序数层。`counted n` 给出的截断单射提供存在性，而所得最小性陈述是命题，所以可以进行最小序数选择。
<!--ja-->
各 `n` に対し、`HoldsAt n` を満たす最小の順序数段階を `ls n` とする。`counted n` が与える切り詰められた単射から存在が従い、得られる最小性の主張は命題なので、最小順序数を選択できる。
<!--/-->

```agda
  opaque
    ls : (n : ℕ) → LeastOrd (HoldsAt n)
    ls n = rec₁ (isPropLeastOrd (HoldsAt n)) from (counted n)
      where
      from : Σ[ F ∈ S ] InjCode F (hullStep n) κ → LeastOrd (HoldsAt n)
```

<!--en-->
Given a graph `F` coding `hullStep n ↪ κ`, the canonical stage containing `F` is an ordinal and witnesses `HoldsAt n` there. Thus the class of candidate stages is inhabited, and `leastOrd` returns its least member.
<!--zh-->
给定编码 `hullStep n ↪ κ` 的图 `F`，容纳 `F` 的典范层是序数，并见证该处的 `HoldsAt n`。因此候选层类有元素，`leastOrd` 返回其中最小者。
<!--ja-->
`hullStep n ↪ κ` を符号化するグラフ `F` が与えられると、`F` を含む正準な段階は順序数であり、そこで `HoldsAt n` を証する。したがって候補となる段階の類は要素をもち、`leastOrd` がその最小の要素を返す。
<!--/-->

```agda
      from (F , code) = leastOrd (HoldsAt n)
        ∣ stage (fst F) (snd F) , stage-ord (fst F) (snd F)
        , ∣ F , stage-mem (fst F) (snd F) , code ∣₁ ∣₁

```

<!--en-->
The family of least stages `n ↦ ls n`, indexed by the meta-level natural numbers, has a single ordinal bound `γ`. The bounding theorem places every `ls n` strictly below this common ordinal.
<!--zh-->
由元层自然数索引的最小层族 `n ↦ ls n` 具有一个共同的序数界 `γ`。界定定理把每个 `ls n` 严格放在这个公共序数之下。
<!--ja-->
メタレベルの自然数で添字づけられた最小段階の族 `n ↦ ls n` には、一つの共通する順序数の上界 `γ` がある。有界化定理により、各 `ls n` はこの共通順序数より真に下に置かれる。
<!--/-->

```agda
  opaque
    γ : V ℓ
    γ = boundingOrd (Lift {ℓ-zero} {ℓ} ℕ) (λ n → ls (lower n) .fst) (λ n → ls (lower n) .snd .fst) .fst

```

<!--en-->
The bound `γ` is itself an ordinal. Hence `Lset γ` is a legitimate constructible stage in which the separate injection codes can be collected.
<!--zh-->
公共界 `γ` 本身是序数。因此 `Lset γ` 是合法的可构造层，可以在其中收集各条独立的单射码。
<!--ja-->
上界 `γ` 自身も順序数である。したがって `Lset γ` は、個別の単射符号を集められる正当な構成可能段階である。
<!--/-->

```agda
    oγ : IsOrd γ
    oγ = boundingOrd (Lift {ℓ-zero} {ℓ} ℕ) (λ n → ls (lower n) .fst) (λ n → ls (lower n) .snd .fst) .snd .fst

```

<!--en-->
For every natural number `n`, the least stage `ls n` belongs to the common upper bound `γ`. This strict bound is the input needed for monotonicity of the constructible hierarchy.
<!--zh-->
对每个自然数 `n`，最小层 `ls n` 都属于公共上界 `γ`。这条严格界正是使用可构造层级单调性所需的条件。
<!--ja-->
各自然数 `n` について、最小段階 `ls n` は共通の上界 `γ` に属する。この狭義の上界が、構成可能階層の単調性に必要な条件である。
<!--/-->

```agda
    bnd-in : (n : ℕ) → ⟨ ls n .fst ∈ γ ⟩
    bnd-in n = boundingOrd (Lift {ℓ-zero} {ℓ} ℕ) (λ n → ls (lower n) .fst) (λ n → ls (lower n) .snd .fst)
                 .snd .snd (lift n)

```

<!--en-->
A code at a smaller stage becomes a code at the common stage: the iterate's coding is transported into `Lset γ` by stage monotonicity.
<!--zh-->
更小层处的码成为公共层处的码：迭代的编码由层单调性搬运进 `Lset γ`。
<!--ja-->
より小さい段階でのコードは、共通の段階でのコードになる。反復の符号化は、段階の単調性によって `Lset γ` の中へ運ばれる。
<!--/-->

```agda
  code-at-γ : (n : ℕ) → ⟨ HoldsAt n γ ⟩
  code-at-γ n = map₁ raise (ls n .snd .snd .fst)
    where
    raise : Σ[ F ∈ S ] (⟨ fst F ∈ Lset (ls n .fst) ⟩ × InjCode F (hullStep n) κ)
          → Σ[ F ∈ S ] (⟨ fst F ∈ Lset γ ⟩ × InjCode F (hullStep n) κ)
```

<!--en-->
The transport pairs the code with its membership in the larger stage, leaving the code itself untouched; only the stage witness moves.
<!--zh-->
该搬运把码与其在更大层中的隶属配对，码本身不动；移动的只是层见证。
<!--ja-->
この輸送は、コードをそのより大きな段階での所属と対にする。コード自体はそのままで、動くのは段階の証人だけである。
<!--/-->

```agda
    raise (F , h , code) = F , Lset-mono {α = γ} {β = ls n .fst} (bnd-in n) h , code
```

<!--en-->
Let `Lγ` be the constructible set whose underlying set is the common stage `Lset γ`. It serves as one internal domain containing an injection code for every finite iterate.
<!--zh-->
令 `Lγ` 为底层集合等于公共层 `Lset γ` 的可构造集合。它是一个内部定义域，容纳每个有限迭代的单射码。
<!--ja-->
底集合が共通の段階 `Lset γ` である構成可能集合を `Lγ` とする。これは、有限な各反復の単射符号を含む一つの内部の定義域である。
<!--/-->

```agda
  opaque
    Lγ : S
    Lγ = LsetS γ oγ

```

<!--en-->
Its underlying set is the stage `Lset γ`, definitionally.
<!--zh-->
其底层集按定义就是层 `Lset γ`。
<!--ja-->
その底の集合は、定義により段階 `Lset γ` である。
<!--/-->

```agda
    Lγ-fst : fst Lγ ≡ Lset γ
    Lγ-fst = refl

```

<!--en-->
The iterates themselves are collected into one constructible set: `Iter` pairs each internal numeral with the closure iterate it indexes.
<!--zh-->
诸迭代自身也被收集为一个可构造集合：`Iter` 把每个内部数码与其所索引的闭包迭代配对。
<!--ja-->
反復そのものも、一つの構成可能な集合に集められる。`Iter` は、各内部の数項と、それが索引づける閉包の反復とを対にする。
<!--/-->

```agda
    Iter : S
    Iter = It.iter

```

<!--en-->
Each pair of a numeral and its iterate is a member, by the iterated-set introduction.
<!--zh-->
由迭代集合的引入规则，每对「数码与其迭代」都是成员。
<!--ja-->
反復集合の導入により、数項とその反復の各対は要素になる。
<!--/-->

```agda
    Iter-in : (n : ℕ) → ⟨ pr (# n) (fst (hullStep n)) ∈ fst Iter ⟩
    Iter-in = It.iter-in

```

<!--en-->
Conversely, every member is, merely, such a pair, so membership in `Iter` identifies exactly the counted iterates and nothing else.
<!--zh-->
反过来，每个成员都仅仅是这样的对，因此 `Iter` 中的隶属恰指认被计数的迭代，别无其他。
<!--ja-->
逆に、すべての要素は、単に、そのような対である。したがって `Iter` の中の所属は、数え上げられた反復だけを指認し、それ以外は何も指認しない。
<!--/-->

```agda
    Iter-out : (y : S) → ⟨ fst y ∈ fst Iter ⟩ → ∥ Σ[ n ∈ ℕ ] (fst y ≡ pr (# n) (fst (hullStep n))) ∥₁
    Iter-out = It.iter-out

```

<!--en-->
A table witness for a constructible code `F` at an internal numeral `n` consists of two facts: `F` lies in the common stage, and, merely, there is an iterate recorded at `n` for which `F` codes an injection into `κ`.
<!--zh-->
内部数码 `n` 处可构造码 `F` 的表见证由两个事实组成：`F` 位于公共层；并且仅仅地存在记录在 `n` 处的迭代 `Zn`，使 `F` 编码 `Zn` 到 `κ` 的单射。
<!--ja-->
内部の数項 `n` における構成可能なコード `F` の表の証人は、二つの事実からなる。`F` が共通の段階に属すること、そして単に、`n` に記録された反復 `Zn` で、`F` が `Zn` から `κ` への単射を符号化することがあることである。
<!--/-->

```agda
  TabWit : (F n : S) → Type (ℓ-suc ℓ)
  TabWit F n = ⟨ fst F ∈ Lset γ ⟩ × ∥ Σ[ Zn ∈ S ] (Holds Iter n Zn × InjCode F Zn κ) ∥₁

```

<!--en-->
`tabBody` has three free slots for a code `F`, an internal numeral `n`, and an unused relation parameter. It asserts `F ∈ Lset γ` and existentially binds an iterate `Zn` such that `Iter(n,Zn)` and `F` codes an injection `Zn ↪ κ`. The existential quantifier is unbounded over `S`.
<!--zh-->
`tabBody` 有三个自由槽，分别放置码 `F`、内部数码 `n` 和一个未使用的关系参数。它断言 `F ∈ Lset γ`，并存在量化一个迭代 `Zn`，使 `Iter(n,Zn)` 成立且 `F` 编码单射 `Zn ↪ κ`。这个存在量词在 `S` 上无界。
<!--ja-->
`tabBody` には、符号 `F`、内部の数項 `n`、使われない関係パラメータのための三つの自由な位置がある。`F ∈ Lset γ` を主張し、`Iter(n,Zn)` が成り立ち、`F` が単射 `Zn ↪ κ` を符号化するような反復 `Zn` を存在量化する。この存在量化子は `S` 上で非有界である。
<!--/-->

```agda
  opaque
    tabBody : Formula S 3
    tabBody = (var i1 ∈̇ con Lγ) ∧̇ ∃̇ (appC Iter i1 i0 ∧̇ injFo κ i2 i0)

```

<!--en-->
Reading the table body back uses the adequacy of the application atom and the reading of the injection formula, converting satisfaction into the two-component table witness.
<!--zh-->
读回表主体使用应用原子的充分性与单射公式的读取，把满足转换为两分量的表见证。
<!--ja-->
表の本体を読み戻すには、適用のアトムの妥当性と単射の論理式の読みを使い、充足を二成分の表の証人へ変換する。
<!--/-->

```agda
    tab-read : (F n q : S) → ⟨ (n ∷ F ∷ q ∷ []) ⊨ tabBody ⟩ → TabWit F n
    tab-read F n q (hF , h) = subst (λ w → ⟨ fst F ∈ w ⟩) Lγ-fst hF
      , map₁ (λ { (Zn , hI , hc) → Zn
          , subst ⟨_⟩ (appC-adequate Iter i1 i0 (Zn ∷ n ∷ F ∷ q ∷ [])) hI
          , InjFo.read κ i2 i0 (Zn ∷ n ∷ F ∷ q ∷ []) hc }) h
```

<!--en-->
Conversely, a `TabWit F n` witness supplies satisfaction of `tabBody`. Stage membership is transported to membership in `Lγ`, and the iterate relation and injection code are converted back through the adequacy of application and the injection formula.
<!--zh-->
反过来，`TabWit F n` 见证给出 `tabBody` 的满足。层隶属被搬运为属于 `Lγ`，而迭代关系与单射码则经应用公式和单射公式的充分性反向转换。
<!--ja-->
逆に、`TabWit F n` の証人から `tabBody` の充足が得られる。段階への所属を `Lγ` への所属へ移送し、反復関係と単射符号を、適用論理式と単射論理式の妥当性によって逆向きに変換する。
<!--/-->

```agda

    tab-fill : (F n q : S) → TabWit F n → ⟨ (n ∷ F ∷ q ∷ []) ⊨ tabBody ⟩
    tab-fill F n q (hF , h) = subst (λ w → ⟨ fst F ∈ w ⟩) (sym Lγ-fst) hF
      , map₁ (λ { (Zn , hI , hc) → Zn
          , subst ⟨_⟩ (sym (appC-adequate Iter i1 i0 (Zn ∷ n ∷ F ∷ q ∷ []))) hI
          , InjFo.fill κ i2 i0 (Zn ∷ n ∷ F ∷ q ∷ []) hc }) h
```

<!--en-->
The relation defined by `tabBody` is collected as a constructible subset of `Lγ × ω`. Its members are pairs `(F,n)` satisfying the table witness condition; separation may use `tabBody` even though its displayed existential is unbounded, because the available separation principle is full separation.
<!--zh-->
`tabBody` 所定义的关系被收集为 `Lγ × ω` 的一个可构造子集。其成员是满足表见证条件的对 `(F,n)`；尽管 `tabBody` 中显示的存在量词无界，仍可用它进行分离，因为这里采用的是完整分离。
<!--ja-->
`tabBody` が定める関係を、`Lγ × ω` の構成可能な部分集合として集める。その要素は表の証人条件を満たす対 `(F,n)` である。`tabBody` に現れる存在量化子は非有界であるが、ここで使えるのは完全な分出なので、この論理式で分出できる。
<!--/-->

```agda

  private
    module TableGraph = Relation Lγ ωʟ tabBody
      (λ F n → TabWit F n , isProp× (snd (fst F ∈ Lset γ)) squash₁) tab-read tab-fill

```

<!--en-->
Write `Gt` for this constructible relation. A pair `(F,n)` belongs to it exactly when `F ∈ Lset γ` and there merely exists an iterate `Zn` recorded at `n` for which `F` codes an injection into `κ`.
<!--zh-->
以 `Gt` 表示这个可构造关系。对 `(F,n)` 属于它，当且仅当 `F ∈ Lset γ`，并且仅仅存在记录在 `n` 处的迭代 `Zn`，使 `F` 编码从 `Zn` 到 `κ` 的单射。
<!--ja-->
この構成可能な関係を `Gt` と書く。対 `(F,n)` がこれに属するのは、`F ∈ Lset γ` であり、`n` に記録された反復 `Zn` で、`F` が `Zn` から `κ` への単射を符号化するものが単に存在するとき、かつそのときに限る。
<!--/-->

```agda
  Gt : S
  Gt = TableGraph.rel

```

<!--en-->
If `F ∈ Lset γ`, `n ∈ ω`, `Iter(n,Zn)`, and `F` codes `Zn ↪ κ`, then the pair `(F,n)` belongs to `Gt`. The iterate `Zn` is retained only under propositional truncation in the relation's specification.
<!--zh-->
若 `F ∈ Lset γ`、`n ∈ ω`、`Iter(n,Zn)`，且 `F` 编码 `Zn ↪ κ`，则对 `(F,n)` 属于 `Gt`。在该关系的刻画中，迭代 `Zn` 只保留在命题截断之下。
<!--ja-->
`F ∈ Lset γ`、`n ∈ ω`、`Iter(n,Zn)` が成り立ち、`F` が `Zn ↪ κ` を符号化するなら、対 `(F,n)` は `Gt` に属する。この関係の特徴づけでは、反復 `Zn` は命題的切り詰めの下でのみ保持される。
<!--/-->

```agda
  Gt-in : (F n Zn : S) → ⟨ fst F ∈ Lset γ ⟩ → ⟨ fst n ∈ fst ωʟ ⟩
        → Holds Iter n Zn → InjCode F Zn κ → Holds Gt F n
  Gt-in F n Zn hF hn hI code = TableGraph.into F n
    (subst (λ w → ⟨ fst F ∈ w ⟩) (sym Lγ-fst) hF) hn (hF , ∣ Zn , hI , code ∣₁)

```

<!--en-->
Elimination reads a table entry back into the two-component witness.
<!--zh-->
消去把表条目读回两分量见证。
<!--ja-->
除去は、表の項目を二成分の証人へ読み戻す。
<!--/-->

```agda
  Gt-out : (F n : S) → Holds Gt F n → TabWit F n
  Gt-out = TableGraph.pair-out

```

<!--en-->
Every internal numeral in `ω` carries an entry: the iterate it records is some finite closure stage, whose code exists in the common stage by the transport above.
<!--zh-->
`ω` 中的每个内部数码都有表条目：它记录的迭代是某个有限闭包层，其码已由上述搬运存在于公共层。
<!--ja-->
`ω` の中のどの内部の数項にも項目がある。それが記録する反復はある有限の閉包段階であり、そのコードは上の輸送によって共通の段階の中に存在する。
<!--/-->

```agda
  have-code : (n : S) → ⟨ fst n ∈ fst ωʟ ⟩ → ∥ Σ[ F ∈ S ] Holds Gt F n ∥₁
  have-code n hn = rec₁ squash₁ at (It.ω-num n hn)
    where
    at : It.Num n → ∥ Σ[ F ∈ S ] Holds Gt F n ∥₁
    at (k , qk) = map₁
```

<!--en-->
The code is then introduced into the table: the iterate identification is transported along the numeral equation, so the entry records the numeral paired with its own iterate.
<!--zh-->
随后把该码引入表中：迭代同一视沿数码等式搬运，使条目记录的是该数码与其自身迭代配对。
<!--ja-->
そしてコードが表の中に導入される。反復の同一視は数項の等式に沿って運ばれ、項目は、数項とその固有の反復の対を記録する。
<!--/-->

```agda
      (λ { (F , hF , code) → F
         , Gt-in F n (hullStep k) hF hn
             (subst (λ w → ⟨ pr w (fst (hullStep k)) ∈ fst Iter ⟩) (cong fst qk) (Iter-in k)) code })
      (code-at-γ k)

```

<!--en-->
Apply least-preimage selection to `Gt` with domain `ω` and code bound `Lγ`. For every internal numeral it selects the stage-order-least related injection code and collects the pairs `(n,eS(n))` into a constructible table `Te`. This definable selection inside one common stage avoids choosing representatives directly from the truncated family `counted n`.
<!--zh-->
对 `Gt` 应用最小原像选择，以 `ω` 为定义域、`Lγ` 为码界。它为每个内部数码选取层序下最小的相关单射码，并把对 `(n,eS(n))` 收集成可构造表 `Te`。这种在同一公共层内的可定义选择避免了直接从截断族 `counted n` 中挑选代表。
<!--ja-->
`Gt` に最小原像の選択を適用し、定義域を `ω`、符号の上界を `Lγ` とする。各内部数項について段階順序で最小の関連する単射符号を選び、対 `(n,eS(n))` を構成可能な表 `Te` に集める。一つの共通段階内でのこの定義可能な選択により、切り詰められた族 `counted n` から代表を直接選ぶ必要がなくなる。
<!--/-->

```agda
  module Tb = LeastPre γ oγ Gt ωʟ Lγ
    (λ F n h → subst (λ w → ⟨ fst F ∈ w ⟩) (sym Lγ-fst) (Gt-out F n h .fst))
    (λ F hF → subst (λ w → ⟨ fst F ∈ w ⟩) Lγ-fst hF)
    have-code
    using ( T; fn; T-in; T-out; fn-holds )
```

<!--en-->
`Te` is the constructible graph of the selected entries. Its domain is the internal `ω`, and its value at each numeral is the least code related to that numeral by `Gt`.
<!--zh-->
`Te` 是所选条目的可构造图。其定义域是内部的 `ω`，在每个数码处的值是由 `Gt` 与该数码相关的最小码。
<!--ja-->
`Te` は選ばれた項目からなる構成可能なグラフである。その定義域は内部の `ω` であり、各数項での値は `Gt` によってその数項と関係づけられる最小の符号である。
<!--/-->

```agda
  Te : S
  Te = Tb.T

```

<!--en-->
The least-entry function assigns to each internal numeral in `ω` the least table entry coding an injection for the iterate recorded there.
<!--zh-->
最小条目函数给 `ω` 中的每个内部数码指派：为该处记录的迭代编码的最小表条目。
<!--ja-->
最小項目の関数は、`ω` の中の各内部の数項に対して、そこに記録された反復の単射を符号化する最小の表の項目を割り当てる。
<!--/-->

```agda
  eS : (n : S) → ⟨ fst n ∈ fst ωʟ ⟩ → S
  eS = Tb.fn

```

<!--en-->
For every `n ∈ ω`, the ordered pair `(n,eS(n))` belongs to `Te`. Thus `Te` records the selected code as the value at the numeral `n`.
<!--zh-->
对每个 `n ∈ ω`，有序对 `(n,eS(n))` 都属于 `Te`。因此，`Te` 把所选码记录为数码 `n` 处的值。
<!--ja-->
各 `n ∈ ω` について、順序対 `(n,eS(n))` は `Te` に属する。したがって `Te` は、選ばれた符号を数項 `n` での値として記録する。
<!--/-->

```agda
  Te-in : (n : S) (m : ⟨ fst n ∈ fst ωʟ ⟩) → ⟨ pr (fst n) (fst (eS n m)) ∈ fst Te ⟩
  Te-in = Tb.T-in

```

<!--en-->
Conversely, if `(n,F) ∈ Te`, then `n ∈ ω` and the underlying set of `F` equals that of the selected entry `eS(n)`. The membership proof of `n ∈ ω` is proposition-valued, so it does not create additional table values.
<!--zh-->
反过来，若 `(n,F) ∈ Te`，则 `n ∈ ω`，且 `F` 的底层集合等于所选条目 `eS(n)` 的底层集合。`n ∈ ω` 的隶属证明是命题值的，因此不会产生额外的表值。
<!--ja-->
逆に、`(n,F) ∈ Te` なら `n ∈ ω` であり、`F` の底集合は選ばれた項目 `eS(n)` の底集合に等しくなる。`n ∈ ω` の所属証明は命題値なので、それによって別の表の値が生じることはない。
<!--/-->

```agda
  Te-out : (n F : S) → ⟨ pr (fst n) (fst F) ∈ fst Te ⟩
         → Σ[ m ∈ ⟨ fst n ∈ fst ωʟ ⟩ ] (fst F ≡ fst (eS n m))
  Te-out = Tb.T-out
```

<!--en-->
The selected entry `eS(n)` satisfies the second component of `TabWit`: merely some iterate `Zn` is recorded at `n`, and `eS(n)` codes an injection `Zn ↪ κ`. The existential remains truncated because only its existence is part of the table specification.
<!--zh-->
所选条目 `eS(n)` 满足 `TabWit` 的第二分量：仅仅存在记录在 `n` 处的某个迭代 `Zn`，且 `eS(n)` 编码单射 `Zn ↪ κ`。这个存在仍被截断，因为表的刻画只包含其存在性。
<!--ja-->
選ばれた項目 `eS(n)` は `TabWit` の第二成分を満たす。`n` に記録された反復 `Zn` が単に存在し、`eS(n)` は単射 `Zn ↪ κ` を符号化する。この存在は表の特徴づけに存在性だけが含まれるため、切り詰められたままである。
<!--/-->

```agda
  e-wit : (n : S) (m : ⟨ fst n ∈ fst ωʟ ⟩)
        → ∥ Σ[ Zn ∈ S ] (Holds Iter n Zn × InjCode (eS n m) Zn κ) ∥₁
  e-wit n m = Gt-out (eS n m) n (Tb.fn-holds n m) .snd
```

<!--en-->
For the canonical numeral of a natural number `k`, the truncation is eliminated. The table entry at that numeral codes an injection of the iterate `hullStep k` into `κ`; the elimination is legitimate because `InjCode` is a proposition.
<!--zh-->
对自然数 `k` 的典范数码，截断被消去。该数码处的表条目编码了迭代 `hullStep k` 到 `κ` 的单射；由于 `InjCode` 是命题，消去合法。
<!--ja-->
自然数 `k` の正準な数項に対しては、切り詰めが消去される。その数項における表の項目は、反復 `hullStep k` から `κ` への単射を符号化する。`InjCode` が命題であるため、この消去は正当である。
<!--/-->

```agda
  e-code : (k : ℕ) → InjCode (eS (nn k) (#∈ω k)) (hullStep k) κ
  e-code k = rec₁ (isPropInjCode (eS (nn k) (#∈ω k)) (hullStep k) κ) read (e-wit (nn k) (#∈ω k))
    where
    F : S
    F = eS (nn k) (#∈ω k)
```

<!--en-->
The recorded iterate is identified first: a member of the iterate set is, merely, a pair whose numeral component and iterate component can both be read off, and the pairing equations identify the recorded iterate.
<!--zh-->
先确定被记录的迭代：迭代集合的成员仅仅是这样的对，其数码分量与迭代分量都可读出，而配对等式识别出被记录的迭代。
<!--ja-->
まず、記録された反復が特定される。反復の集合の要素は、単に、数項の成分と反復の成分の両方を読み取れる対であり、対の等式が記録された反復を特定する。
<!--/-->

```agda
    read : Σ[ Zn ∈ S ] (Holds Iter (nn k) Zn × InjCode F Zn κ) → InjCode F (hullStep k) κ
    read (Zn , hI , code) = rec₁ (isPropInjCode F (hullStep k) κ) at
      (Iter-out (prʟ (nn k) Zn) (subst (λ w → ⟨ w ∈ fst Iter ⟩) (sym (prʟ-fst (nn k) Zn)) hI))
      where
      at : Σ[ k' ∈ ℕ ] (fst (prʟ (nn k) Zn) ≡ pr (# k') (fst (hullStep k'))) → InjCode F (hullStep k) κ
```

<!--en-->
The numeral equation forces `k'` to be `k`, and the code is transported along the identification of the two iterates, which does not change the code itself.
<!--zh-->
数码等式迫使 `k'` 即 `k`，而码沿两个迭代的同一视被搬运，码本身不变。
<!--ja-->
数項の等式は `k'` が `k` であることを強制し、コードは、二つの反復の同一視に沿って運ばれる。コード自体は変わらない。
<!--/-->

```agda
      at (k' , q) = injcode-resp F F Zn (hullStep k) κ refl
        (snd ee ∙ cong (λ j → fst (hullStep j)) (sym (#-inj k k' (fst ee)))) code
        where
        ee : (# k ≡ # k') × (fst Zn ≡ fst (hullStep k'))
        ee = pr-inj (sym (prʟ-fst (nn k) Zn) ∙ q)
```

<!--en-->
`FinWit p z` merely records an internal numeral `n ∈ ω`, a value `v`, and a table entry `F`. Its equations say `p=(n,v)`, `Te(n)=F`, and `F(z)=v`. Thus `p`, rather than `F`, is the pair code used to count `z`.
<!--zh-->
`FinWit p z` 仅仅记录内部数码 `n ∈ ω`、值 `v` 与表条目 `F`。其中的等式和图隶属表示 `p=(n,v)`、`Te(n)=F` 以及 `F(z)=v`。因此，用于计数 `z` 的对码是 `p`，而不是 `F`。
<!--ja-->
`FinWit p z` は、内部の数項 `n ∈ ω`、値 `v`、表の項目 `F` を単に記録する。その等式とグラフ所属は `p=(n,v)`、`Te(n)=F`、`F(z)=v` を表す。したがって `z` を数えるための対の符号は `F` ではなく `p` である。
<!--/-->

```agda
  FinWit : (p z : S) → Type (ℓ-suc ℓ)
  FinWit p z = ∥ Σ[ n ∈ S ] Σ[ v ∈ S ] Σ[ F ∈ S ]
      ((fst p ≡ pr (fst n) (fst v)) × ⟨ fst n ∈ fst ωʟ ⟩ × Holds Te n F × Holds F z v) ∥₁
```

<!--en-->
`inner₆` is the conjunction of two application statements: the table `Te` maps `n` to the entry `F`, and that entry maps `z` to `v`. With environment `F,v,n,z,p,q`, these are exactly `Holds Te n F` and `Holds F z v`.
<!--zh-->
`inner₆` 是两条应用陈述的合取：表 `Te` 把 `n` 映到条目 `F`，而该条目把 `z` 映到 `v`。在环境 `F,v,n,z,p,q` 中，它们恰是 `Holds Te n F` 与 `Holds F z v`。
<!--ja-->
`inner₆` は二つの適用の主張の連言である。表 `Te` は `n` を項目 `F` へ写し、その項目は `z` を `v` へ写す。環境 `F,v,n,z,p,q` では、これらはちょうど `Holds Te n F` と `Holds F z v` である。
<!--/-->

```agda
  opaque
    inner₆ : Formula S 6
    inner₆ = appC Te i2 i0 ∧̇ appAt i0 i3 i1

```

<!--en-->
Filling the two atoms uses their adequacy lemmas, so a witness record produces the satisfaction of the two application atoms in one environment.
<!--zh-->
填充两个原子使用其充分性引理，于是见证记录在单一环境中产出两个应用原子的满足。
<!--ja-->
二つのアトムの埋め込みには、その妥当性の補題を使う。これにより、証人の記録が、一つの環境のもとで二つの適用のアトムの充足を産み出す。
<!--/-->

```agda
    inner₆-in : (F v n z p q : S) → Holds Te n F → Holds F z v
              → ⟨ (F ∷ v ∷ n ∷ z ∷ p ∷ q ∷ []) ⊨ inner₆ ⟩
    inner₆-in F v n z p q ht hv =
        subst ⟨_⟩ (sym (appC-adequate Te i2 i0 (F ∷ v ∷ n ∷ z ∷ p ∷ q ∷ []))) ht
      , subst ⟨_⟩ (sym (appAt-adequate i0 i3 i1 (F ∷ v ∷ n ∷ z ∷ p ∷ q ∷ []))) hv
```

<!--en-->
Reading the two atoms uses the same adequacy lemmas in the forward direction, recovering the table satisfaction and the graph membership.
<!--zh-->
读取两个原子沿正向使用同样的充分性引理，恢复表满足与图隶属。
<!--ja-->
二つのアトムを読むには、同じ妥当性の補題を順方向に使う。これで表の充足とグラフの所属が回復する。
<!--/-->

```agda

    inner₆-out : (F v n z p q : S) → ⟨ (F ∷ v ∷ n ∷ z ∷ p ∷ q ∷ []) ⊨ inner₆ ⟩
               → Holds Te n F × Holds F z v
    inner₆-out F v n z p q (ht , hv) =
        subst ⟨_⟩ (appC-adequate Te i2 i0 (F ∷ v ∷ n ∷ z ∷ p ∷ q ∷ [])) ht
      , subst ⟨_⟩ (appAt-adequate i0 i3 i1 (F ∷ v ∷ n ∷ z ∷ p ∷ q ∷ [])) hv
```

<!--en-->
`nv₃` has free variables `z,p,q` and existentially binds `n`, then `v`, then `F`. Its body states `p=(n,v)`, `n ∈ ω`, `Te(n)=F`, and `F(z)=v`; the free variable `q` is unused.
<!--zh-->
`nv₃` 的自由变元是 `z,p,q`，并依次存在量化 `n`、`v`、`F`。公式体陈述 `p=(n,v)`、`n ∈ ω`、`Te(n)=F` 与 `F(z)=v`；自由变元 `q` 未被使用。
<!--ja-->
`nv₃` の自由変数は `z,p,q` であり、`n`、`v`、`F` の順に存在量化する。本体は `p=(n,v)`、`n ∈ ω`、`Te(n)=F`、`F(z)=v` を述べ、自由変数 `q` は使われない。
<!--/-->

```agda
  opaque
    nv₃ : Formula S 3
    nv₃ = ∃̇ (∃̇ (prAtL i3 i1 i0 ∧̇ ((var i1 ∈̇ con ωʟ) ∧̇ ∃̇ inner₆)))

```

<!--en-->
Given `p=(n,v)`, `n ∈ ω`, `Te(n)=F`, and `F(z)=v`, the three witnesses `n`, `v`, and `F` fill the nested existential quantifiers. Pairing adequacy supplies the pair atom, and `inner₆-in` supplies the two application atoms.
<!--zh-->
给定 `p=(n,v)`、`n ∈ ω`、`Te(n)=F` 与 `F(z)=v`，三个见证 `n`、`v`、`F` 依次填入嵌套存在量词。配对的充分性给出配对原子，`inner₆-in` 给出两个应用原子。
<!--ja-->
`p=(n,v)`、`n ∈ ω`、`Te(n)=F`、`F(z)=v` が与えられると、三つの証人 `n`、`v`、`F` が入れ子の存在量化子を満たす。対の妥当性が対の原子式を与え、`inner₆-in` が二つの適用の原子式を与える。
<!--/-->

```agda
    nv₃-in : (z p q n v F : S) → fst p ≡ pr (fst n) (fst v) → ⟨ fst n ∈ fst ωʟ ⟩
           → Holds Te n F → Holds F z v → ⟨ (z ∷ p ∷ q ∷ []) ⊨ nv₃ ⟩
    nv₃-in z p q n v F qp hn ht hv =
      ∣ n , ∣ v , ( subst ⟨_⟩ (sym (prAtL-adequate i3 i1 i0 (v ∷ n ∷ z ∷ p ∷ q ∷ []))) qp
                  , ( hn , ∣ F , inner₆-in F v n z p q ht hv ∣₁ ) ) ∣₁ ∣₁
```

<!--en-->
To read `nv₃`, first eliminate the truncated witness for `n`, then the truncated witness for `v`. For fixed `n` and `v`, `Inner n v` retains the pairing atom, membership `n ∈ ω`, and a third truncated existence of an entry `F` satisfying `inner₆`.
<!--zh-->
读取 `nv₃` 时，先消去 `n` 的截断见证，再消去 `v` 的截断见证。固定 `n` 与 `v` 后，`Inner n v` 保留配对原子、隶属关系 `n ∈ ω`，以及满足 `inner₆` 的条目 `F` 的第三层截断存在。
<!--ja-->
`nv₃` を読むには、まず `n` の切り詰められた証人を除去し、次に `v` の切り詰められた証人を除去する。`n` と `v` を固定すると、`Inner n v` は対の原子式、所属 `n ∈ ω`、そして `inner₆` を満たす項目 `F` の三つ目の切り詰められた存在を保持する。
<!--/-->

```agda

    nv₃-out : (z p q : S) → ⟨ (z ∷ p ∷ q ∷ []) ⊨ nv₃ ⟩ → FinWit p z
    nv₃-out z p q = rec₁ squash₁ at₁
      where
      Inner : (n v : S) → Type (ℓ-suc ℓ)
      Inner n v = ⟨ (v ∷ n ∷ z ∷ p ∷ q ∷ []) ⊨ prAtL i3 i1 i0 ⟩
```

<!--en-->
The innermost truncated existence supplies the table entry `F`, not the value `v`, which is already fixed. Pairing adequacy converts the pair atom to `p=(n,v)`, while `inner₆-out` recovers `Te(n)=F` and `F(z)=v`; these data form `FinWit p z`.
<!--zh-->
最内层的截断存在给出表条目 `F`，而不是已经固定的值 `v`。配对的充分性把配对原子转换为 `p=(n,v)`，`inner₆-out` 则恢复 `Te(n)=F` 与 `F(z)=v`；这些数据组成 `FinWit p z`。
<!--ja-->
最も内側の切り詰められた存在が与えるのは表の項目 `F` であり、すでに固定されている値 `v` ではない。対の妥当性が対の原子式を `p=(n,v)` に変換し、`inner₆-out` が `Te(n)=F` と `F(z)=v` を復元する。これらのデータが `FinWit p z` を構成する。
<!--/-->

```agda
                × ( ⟨ fst n ∈ fst ωʟ ⟩ × ∥ Σ[ F ∈ S ] ⟨ (F ∷ v ∷ n ∷ z ∷ p ∷ q ∷ []) ⊨ inner₆ ⟩ ∥₁ )
      at₃ : (n v : S) → Inner n v → FinWit p z
      at₃ n v (qp , (hn , h)) = map₁
        (λ { (F , hi) → n , v , F
           , ( subst ⟨_⟩ (prAtL-adequate i3 i1 i0 (v ∷ n ∷ z ∷ p ∷ q ∷ [])) qp
```

<!--en-->
For fixed `n` and `v`, the innermost conversion produces `FinWit p z`; the two outer eliminations then discharge the truncated choices of `v` and `n`. Thus satisfaction of `nv₃` yields exactly the truncated tuple required by the ambient relation.
<!--zh-->
固定 `n` 与 `v` 后，最内层转换产生 `FinWit p z`；外侧两次消去再依次处理 `v` 与 `n` 的截断选择。因此，`nv₃` 的满足恰好给出外围关系所需的截断元组。
<!--ja-->
`n` と `v` を固定すると、最も内側の変換から `FinWit p z` が得られ、外側の二つの除去が `v` と `n` の切り詰められた選択を順に処理する。したがって `nv₃` の充足から、周囲の関係が要求する切り詰められた組がちょうど得られる。
<!--/-->

```agda
             , hn , inner₆-out F v n z p q hi ) }) h
      at₂ : (n : S) → Σ[ v ∈ S ] Inner n v → FinWit p z
      at₂ n (v , h) = at₃ n v h
      at₁ : Σ[ n ∈ S ] ∥ Σ[ v ∈ S ] Inner n v ∥₁ → FinWit p z
      at₁ (n , h) = rec₁ squash₁ (at₂ n) h
```

<!--en-->
The final relation is obtained by separation inside the Cartesian product of `prodL κ` and `hullL`. Its defining formula is `nv₃`, whose three existential witnesses are an internal natural `n`, a value `v`, and a table entry `F`. The relation connects `p` to `z` exactly when `p = (n,v)`, `n ∈ ω`, the table records `F` at `n`, and `F` records `v` at `z`.
<!--zh-->
最终关系由分离从 `prodL κ` 与 `hullL` 的笛卡尔积中取得。定义它的公式是 `nv₃`，其三个存在见证分别为内部自然数 `n`、值 `v` 与表项 `F`。当且仅当 `p = (n,v)`、`n ∈ ω`、表在 `n` 处记录 `F`，且 `F` 在 `z` 处记录 `v` 时，该关系才把 `p` 与 `z` 联系起来。
<!--ja-->
最終の関係は、`prodL κ` と `hullL` の直積から分出によって得られる。これを定める論理式は `nv₃` であり、その三つの存在証人は、内部自然数 `n`、値 `v`、表の項目 `F` である。`p = (n,v)`、`n ∈ ω`、表が `n` で `F` を記録し、`F` が `z` で `v` を記録するとき、かつそのときに限り、この関係は `p` と `z` を結ぶ。
<!--/-->

```agda

  private
    module FinalGraph = Relation (prodL κ) hullL nv₃ (λ p z → FinWit p z , squash₁)
      (λ p z q → nv₃-out z p q)
      (λ p z q → rec₁ (snd ((z ∷ p ∷ q ∷ []) ⊨ nv₃))
        (λ { (n , v , F , qp , hn , ht , hv) → nv₃-in z p q n v F qp hn ht hv }))
```

<!--en-->
The separated set is named `Gf` and is the constructible carrier of the final graph.
<!--zh-->
分离所得的集合命名为 `Gf`，即最终图的可构造载体。
<!--ja-->
分離された集合は `Gf` と名付けられ、最終のグラフの構成可能な台になる。
<!--/-->

```agda

  Gf : S
  Gf = FinalGraph.rel

```

<!--en-->
To introduce membership in `Gf`, take `p ∈ prodL κ`, `z ∈ hullL`, an internal natural `n ∈ ω`, a value `v`, and a table entry `F`. An equation `p = (n,v)`, together with the graph memberships saying that `Te` records `F` at `n` and `F` records `v` at `z`, supplies exactly the witness required by the defining relation.
<!--zh-->
要引入 `Gf` 中的隶属，取 `p ∈ prodL κ`、`z ∈ hullL`、内部自然数 `n ∈ ω`、值 `v` 与表项 `F`。等式 `p = (n,v)`，连同表示 `Te` 在 `n` 处记录 `F`、`F` 在 `z` 处记录 `v` 的两条图隶属，恰好给出定义关系所需的见证。
<!--ja-->
`Gf` への所属を導入するには、`p ∈ prodL κ`、`z ∈ hullL`、内部自然数 `n ∈ ω`、値 `v`、表の項目 `F` を取る。等式 `p = (n,v)` と、`Te` が `n` で `F` を記録し、`F` が `z` で `v` を記録するという二つのグラフ所属が、定義関係に必要な証人をちょうど与える。
<!--/-->

```agda
  Gf-in : (p z n v F : S) → ⟨ fst p ∈ fst (prodL κ) ⟩ → ⟨ fst z ∈ fst hullL ⟩
        → fst p ≡ pr (fst n) (fst v) → ⟨ fst n ∈ fst ωʟ ⟩ → Holds Te n F → Holds F z v
        → Holds Gf p z
  Gf-in p z n v F hp hz qp hn ht hv = FinalGraph.into p z hp hz ∣ n , v , F , qp , hn , ht , hv ∣₁

```

<!--en-->
Conversely, `Gf-out` turns a graph membership into the propositionally truncated record `FinWit p z`. This record may be eliminated when proving proposition-valued consequences, such as membership in a set or equality of sets.
<!--zh-->
反过来，`Gf-out` 把一条图隶属化为命题截断的记录 `FinWit p z`。在证明集合隶属或集合相等等命题值结论时，可以消去这份记录的截断。
<!--ja-->
逆に、`Gf-out` はグラフへの所属を、命題的に切り詰められた記録 `FinWit p z` に変える。この記録の切り詰めは、集合への所属や集合の等しさのような命題値の結論を示すときに消去できる。
<!--/-->

```agda
  Gf-out : (p z : S) → Holds Gf p z → FinWit p z
  Gf-out = FinalGraph.pair-out
```

<!--en-->
Every value recorded by a table entry lies in `κ`. From `Te(n,F)`, the table reading identifies `F` with the selected entry at `n`; `e-wit` supplies an iterate `Zn` and an injection code from `Zn` into `κ` for that selected entry. Transporting `F(z)=v` across the table identification lets the range clause of this code prove `v ∈ κ`.
<!--zh-->
每个表项所记录的值都属于 `κ`。由 `Te(n,F)`，表的读法把 `F` 与 `n` 处选出的表项同一视；`e-wit` 为该选定表项给出一个迭代 `Zn` 及从 `Zn` 到 `κ` 的单射码。把 `F(z)=v` 沿表项的同一视搬运后，该码的值域条款便证明 `v ∈ κ`。
<!--ja-->
表の項目が記録する値はすべて `κ` に属する。`Te(n,F)` から、表の読みは `F` を `n` で選ばれた項目と同一視する。`e-wit` は、その選ばれた項目について、ある反復 `Zn` と `Zn` から `κ` への単射符号を与える。`F(z)=v` を表の項目の同一視に沿って移せば、その符号の値域条件から `v ∈ κ` が従う。
<!--/-->

```agda
  entry-ran : (n F z v : S) → Holds Te n F → Holds F z v → ⟨ fst v ∈ fst κ ⟩
  entry-ran n F z v ht hv = rec₁ (snd (fst v ∈ fst κ))
    (λ { (Zn , _ , code) → snd (snd (snd code)) z v
          (subst (λ w → ⟨ pr (fst z) (fst v) ∈ w ⟩) (Te-out n F ht .snd) hv) })
    (e-wit n (Te-out n F ht .fst))
```

<!--en-->
Every first component related by `Gf` belongs to `prodL κ`. A record for such a component writes it as `(n,v)` with `n ∈ ω` and `v ∈ κ`. Since the non-finite ordinal `κ` contains `ω`, also `n ∈ κ`; hence both coordinates lie in `κ`, so `(n,v) ∈ prodL κ`.
<!--zh-->
凡被 `Gf` 关联的第一分量都属于 `prodL κ`。相应记录把它写成 `(n,v)`，其中 `n ∈ ω` 且 `v ∈ κ`。由于非有限序数 `κ` 包含 `ω`，还有 `n ∈ κ`；故两个坐标都属于 `κ`，从而 `(n,v) ∈ prodL κ`。
<!--ja-->
`Gf` によって関係付けられる第一成分はすべて `prodL κ` に属する。その記録は第一成分を `(n,v)` と表し、`n ∈ ω` かつ `v ∈ κ` を与える。有限でない順序数 `κ` は `ω` を含むので `n ∈ κ` でもあり、両方の座標が `κ` に属する。したがって `(n,v) ∈ prodL κ` である。
<!--/-->

```agda

  inPκ : (p z : S) → Holds Gf p z → ⟨ fst p ∈ fst (prodL κ) ⟩
  inPκ p z h = rec₁ (snd (fst p ∈ fst (prodL κ)))
    (λ { (n , v , F , (qp , hn , ht , hv)) →
       subst (λ w → ⟨ w ∈ fst (prodL κ) ⟩) (sym qp)
         (prodL-in κ n v (ω⊆ (fst κ) oκ κ∉ω (fst n) hn) (entry-ran n F z v ht hv)) })
```

<!--en-->
Applying this argument to the truncated record returned by `Gf-out` proves `inPκ`: whenever `Gf(p,z)` holds, its first component `p` belongs to `prodL κ`.
<!--zh-->
把上述论证施于 `Gf-out` 返回的截断记录，便得到 `inPκ`：只要 `Gf(p,z)` 成立，其第一分量 `p` 就属于 `prodL κ`。
<!--ja-->
この議論を `Gf-out` が返す切り詰められた記録に適用すると、`inPκ` が得られる。すなわち、`Gf(p,z)` が成り立つなら、その第一成分 `p` は `prodL κ` に属する。
<!--/-->

```agda
    (Gf-out p z h)

```

<!--en-->
Every hull member merely has a related code. The characterization of the iterate union places `z` in some finite stage `hullStep n`. For the selected graph `F = eS (# n)`, the exact code `e-code n` has domain `hullStep n`; its totality clause therefore gives, merely, a value `v` with `F(z)=v`.
<!--zh-->
每个壳成员都纯粹地存在一个与之相关的码。迭代并的刻画把 `z` 放入某个有限阶段 `hullStep n`。对选定的图 `F = eS (# n)`，精确陈述 `e-code n` 以 `hullStep n` 为定义域；因此其全域性条款纯粹地给出一个满足 `F(z)=v` 的值 `v`。
<!--ja-->
包の各要素には、それと関係する符号が単に存在する。反復の合併の特徴づけにより、`z` はある有限段階 `hullStep n` に属する。選ばれたグラフ `F = eS (# n)` について、`e-code n` はその定義域が `hullStep n` であることを正確に述べる。したがって、その全域性条件から、`F(z)=v` を満たす値 `v` が単に得られる。
<!--/-->

```agda
  have-fin : (z : S) → ⟨ fst z ∈ fst hullL ⟩ → ∥ Σ[ p ∈ S ] Holds Gf p z ∥₁
  have-fin z hz = rec₁ squash₁ at (It.iterUnion-out z hz)
    where
    at : Σ[ n ∈ ℕ ] ⟨ fst z ∈ fst (hullStep n) ⟩ → ∥ Σ[ p ∈ S ] Holds Gf p z ∥₁
    at (n , hn) = map₁ val (domAt-in zero (suc zero) (F ∷ hullStep n ∷ []) (fst (snd (e-code n))) z hn)
```

<!--en-->
The totality clause of `e-code n` supplies the value `v` together with the graph membership `F(z)=v`. Pairing the canonical numeral `# n` with this value produces the candidate code `p = (# n,v)`.
<!--zh-->
`e-code n` 的全域性条款给出值 `v`，以及图隶属 `F(z)=v`。把标准数码 `# n` 与该值配对，便得到候选码 `p = (# n,v)`。
<!--ja-->
`e-code n` の全域性条件は、値 `v` とグラフ所属 `F(z)=v` を与える。標準数項 `# n` とこの値を対にすると、候補となる符号 `p = (# n,v)` が得られる。
<!--/-->

```agda
      where
      F : S
      F = eS (nn n) (#∈ω n)
      val : Σ[ v ∈ S ] Holds F z v → Σ[ p ∈ S ] Holds Gf p z
      val (v , hv) = prʟ (nn n) v
```

<!--en-->
The introduction assembles the whole record: the pair lies in the product by the numeral membership and the code's range clause, and the graph relates it to `z` by the table's own membership.
<!--zh-->
引入规则组装整个记录：该对因数码隶属与码的值域条款而属于乘积，而图凭表自身的隶属把它与 `z` 关联。
<!--ja-->
導入は記録の全体を組み立てる。対は、数項の所属とコードの値域の条項によって積の中にあり、表自身の所属によって `z` と関係付けられる。
<!--/-->

```agda
        , Gf-in (prʟ (nn n) v) z (nn n) v F
            (subst (λ w → ⟨ w ∈ fst (prodL κ) ⟩) (sym (prʟ-fst (nn n) v))
              (prodL-in κ (nn n) v (num∈κ n) (snd (snd (snd (e-code n))) z v hv)))
            hz (prʟ-fst (nn n) v) (#∈ω n) (Te-in (nn n) (#∈ω n)) hv

```

<!--en-->
The functionality needed for least-preimage selection runs from a candidate code back to the hull: if the same `p` is related to both `z` and `z'`, then `z = z'`. This property makes the selected map from hull members to their least codes injective. Both relation witnesses are truncated records, and they can be eliminated here because equality of sets is a proposition.
<!--zh-->
最小原像选取所需的函数性从候选码指回壳：若同一个 `p` 同时关联 `z` 与 `z'`，则 `z = z'`。这一性质使从壳成员到其最小码的选取映射成为单射。两份关系见证都是截断记录，而此处的目标是集合相等这一命题，故可消去它们的截断。
<!--ja-->
最小逆像の選択に必要な関数性は、候補となる符号から包へ向かう。同じ `p` が `z` と `z'` の両方に関係するなら、`z = z'` である。この性質により、包の要素をその最小符号へ送る選択写像は単射になる。二つの関係の証人はいずれも切り詰められた記録であるが、ここでの目標は集合の等しさという命題なので、その切り詰めを消去できる。
<!--/-->

```agda
  funct-fin : (p z z' : S) → Holds Gf p z → Holds Gf p z' → fst z ≡ fst z'
  funct-fin p z z' h h' = rec2 (setIsSet (fst z) (fst z')) read (Gf-out p z h) (Gf-out p z' h')
    where
    read : Σ[ n ∈ S ] Σ[ v ∈ S ] Σ[ F ∈ S ]
             ((fst p ≡ pr (fst n) (fst v)) × ⟨ fst n ∈ fst ωʟ ⟩ × Holds Te n F × Holds F z v)
```

<!--en-->
Unpacking the two records gives `n,v,F` and `n',v',F'`. Each record contains one pair equation, respectively `p=(n,v)` and `p=(n',v')`, together with three facts: its index belongs to `ω`, the table records its entry at that index, and the entry records the displayed value at the corresponding hull member.
<!--zh-->
展开两份记录，分别得到 `n,v,F` 与 `n',v',F'`。每份记录都含一条配对等式，即 `p=(n,v)` 或 `p=(n',v')`，并含三项事实：索引属于 `ω`、表在该索引处记录相应表项，以及该表项在对应壳成员处记录所示的值。
<!--ja-->
二つの記録を展開すると、`n,v,F` と `n',v',F'` がそれぞれ得られる。各記録は一つの対の等式、すなわち `p=(n,v)` または `p=(n',v')` と、三つの事実を含む。その添字が `ω` に属すること、表がその添字で対応する項目を記録すること、そしてその項目が対応する包の要素で表示された値を記録することである。
<!--/-->

```agda
         → Σ[ n' ∈ S ] Σ[ v' ∈ S ] Σ[ F' ∈ S ]
             ((fst p ≡ pr (fst n') (fst v')) × ⟨ fst n' ∈ fst ωʟ ⟩ × Holds Te n' F' × Holds F' z' v')
         → fst z ≡ fst z'
    read (n , v , F , (qp , hn , ht , hv)) (n' , v' , F' , (qp' , hn' , ht' , hv')) =
      rec₁ (setIsSet (fst z) (fst z'))
```

<!--en-->
The two pair equations first give `n=n'` and `v=v'`. The table readings then align `F` and `F'` with the same selected entry `eS n m`. The witness `e-wit n m` supplies an iterate `Zn` and an injection code for this entry. After transporting both graph memberships to that common entry, and the second value along `v'=v`, the injectivity clause yields `z=z'`.
<!--zh-->
两条配对等式先给出 `n=n'` 与 `v=v'`。随后，表的读法把 `F`、`F'` 与同一个选定表项 `eS n m` 对齐。见证 `e-wit n m` 为该表项给出一个迭代 `Zn` 及相应的单射码。把两条图隶属都搬运到这一共同表项，并把第二个值沿 `v'=v` 搬运后，单射性条款便给出 `z=z'`。
<!--ja-->
二つの対の等式から、まず `n=n'` と `v=v'` が得られる。次に、表の読みが `F` と `F'` を同じ選択項目 `eS n m` にそろえる。証人 `e-wit n m` は、この項目について、ある反復 `Zn` とその単射符号を与える。二つのグラフ所属をこの共通の項目へ移し、さらに第二の値を `v'=v` に沿って移すと、単射性条件から `z=z'` が従う。
<!--/-->

```agda
        (λ { (Zn , _ , code) →
           injAt-out zero (eS n m ∷ Zn ∷ []) (fst (snd (snd code))) v z z'
             (subst (λ w → ⟨ pr (fst z) (fst v) ∈ w ⟩) (Te-out n F ht .snd) hv)
             (subst2 (λ u w → ⟨ pr (fst z') u ∈ w ⟩) (sym (snd ee)) qF hv') })
        (e-wit n m)
```

<!--en-->
Injectivity of the ordered pair splits the identification into the numeral and the value component, and the table reading certifies that the numeral lies in `ω`.
<!--zh-->
有序对的单射性把该同一视拆分为数码分量与值分量，而表读取证明数码属于 `ω`。
<!--ja-->
順序対の単射性が、同一視を数項の成分と値の成分に分解する。そして表の読みが、数項が `ω` の中にあることを証明する。
<!--/-->

```agda
      where
      ee : (fst n ≡ fst n') × (fst v ≡ fst v')
      ee = pr-inj (sym qp ∙ qp')
      m : ⟨ fst n ∈ fst ωʟ ⟩
      m = Te-out n F ht .fst
```

<!--en-->
The two pairs, numeral together with ω-membership, are equal because ω-membership is propositional and the numeral equation is an equality of underlying sets.
<!--zh-->
两对「数码连同 `ω` 隶属」相等，因为 `ω` 隶属是命题，而数码等式是底层集合的等式。
<!--ja-->
数項と `ω` への所属の二つの対は等しくなる。`ω` への所属が命題であり、数項の等式が底の集合の等式だからである。
<!--/-->

```agda
      pth : _≡_ {A = Σ[ c ∈ S ] ⟨ fst c ∈ fst ωʟ ⟩} (n' , Te-out n' F' ht' .fst) (n , m)
      pth = Σ≡Prop (λ c → snd (fst c ∈ fst ωʟ)) (S≡ {x = n'} {y = n} (sym (fst ee)))

```

<!--en-->
Transporting the table reading for `F'` along the equality of the two internal-natural indices identifies `F'` with the selected entry `eS n m`. Together with the corresponding reading for `F`, this puts both graph memberships in the same injection graph.
<!--zh-->
把 `F'` 的表读法沿两个内部自然数索引的相等搬运，便把 `F'` 与选定表项 `eS n m` 同一视。再结合 `F` 的相应读法，两条图隶属就落在同一个单射图中。
<!--ja-->
`F'` に対する表の読みを二つの内部自然数の添字の等しさに沿って移すと、`F'` は選択項目 `eS n m` と同一視される。`F` に対する対応する読みと合わせると、二つのグラフ所属は同じ単射グラフの中に置かれる。
<!--/-->

```agda
      qF : fst F' ≡ fst (eS n m)
      qF = Te-out n' F' ht' .snd ∙ (λ i → fst (eS (fst (pth i)) (snd (pth i))))

```

<!--en-->
Let `γf` be the ordinal stage assigned to the constructible set `prodL κ`. It provides a common stage `Lset γf` containing every candidate code, so the canonical stage order can compare their preimages.
<!--zh-->
令 `γf` 为可构造集合 `prodL κ` 所对应的序数阶段。它给出包含所有候选码的共同层 `Lset γf`，从而可用典范阶段序比较这些原像。
<!--ja-->
`γf` を、構成可能集合 `prodL κ` に対応する順序数段階とする。これにより、すべての候補符号を含む共通の段階 `Lset γf` が得られ、標準的な段階順序でそれらの逆像を比較できる。
<!--/-->

```agda
  γf : V ℓ
  γf = stage (fst (prodL κ)) (snd (prodL κ))

```

<!--en-->
That stage is an ordinal, as every stage is.
<!--zh-->
该层是序数，正如所有层一样。
<!--ja-->
その段階は、すべての段階と同じく順序数である。
<!--/-->

```agda
  oγf : IsOrd γf
  oγf = stage-ord (fst (prodL κ)) (snd (prodL κ))

```

<!--en-->
The set `prodL κ` belongs to `Lset γf` by the defining property of its stage. Since `Lset γf` is transitive, every member of `prodL κ` also belongs to `Lset γf`; hence `prodL κ ⊆ Lset γf`.
<!--zh-->
由其阶段的定义性质，集合 `prodL κ` 属于 `Lset γf`。由于 `Lset γf` 是传递集，`prodL κ` 的每个成员也都属于 `Lset γf`；故 `prodL κ ⊆ Lset γf`。
<!--ja-->
段階の定義的性質により、集合 `prodL κ` は `Lset γf` に属する。`Lset γf` は推移的なので、`prodL κ` の各要素も `Lset γf` に属する。したがって `prodL κ ⊆ Lset γf` である。
<!--/-->

```agda
  prodκ⊆Lγ : (p : S) → ⟨ fst p ∈ fst (prodL κ) ⟩ → ⟨ fst p ∈ Lset γf ⟩
  prodκ⊆Lγ p hp =
    layer-trans (Lset-layer γf) {x = fst (prodL κ)} {y = fst p} hp (stage-mem (fst (prodL κ)) (snd (prodL κ)))

```

<!--en-->
For each `z ∈ hullL`, choose the stage-order-least `p ∈ prodL κ` with `Gf(p,z)`. The three required facts are exactly those proved above: every related `p` lies in `prodL κ`, this carrier is contained in `Lset γf`, and every hull member merely has a related `p`. Since `funct-fin` says that one `p` cannot be related to two different hull members, the resulting least-preimage map is an internal coded injection `hullL ↪ prodL κ`.
<!--zh-->
对每个 `z ∈ hullL`，选取满足 `Gf(p,z)` 的阶段序最小元 `p ∈ prodL κ`。所需的三项事实恰为上文所得：每个相关的 `p` 都属于 `prodL κ`，该载体包含于 `Lset γf`，且每个壳成员都纯粹地存在一个相关的 `p`。由于 `funct-fin` 说明同一个 `p` 不会关联两个不同的壳成员，所得最小原像映射便是内部编码单射 `hullL ↪ prodL κ`。
<!--ja-->
各 `z ∈ hullL` に対し、`Gf(p,z)` を満たす `p ∈ prodL κ` のうち、段階順序で最小のものを選ぶ。必要な三つの事実は、上で示したものである。関係する各 `p` は `prodL κ` に属し、この台は `Lset γf` に含まれ、各包の要素には関係する `p` が単に存在する。`funct-fin` により、一つの `p` が異なる二つの包の要素に関係することはないので、得られる最小逆像写像は内部で符号化された単射 `hullL ↪ prodL κ` になる。
<!--/-->

```agda
  module LF = LeastPre γf oγf Gf hullL (prodL κ) inPκ prodκ⊆Lγ have-fin using ( module Functional )
```

<!--en-->
The least-preimage construction gives a coded injection from the hull into `prodL κ`, and the square law gives a coded injection from `prodL κ` into `κ`. Their composition proves the propositionally truncated statement `InjL hullL κ`. This is an internal coded injection; it asserts neither surjectivity nor equality of cardinals, and it makes no claim about a collapse image. Thus the constructible hull has distinct internal `κ`-codes for all of its members.
<!--zh-->
最小原像构造给出从壳到 `prodL κ` 的编码单射，平方法则给出从 `prodL κ` 到 `κ` 的编码单射。二者复合便证明命题截断的陈述 `InjL hullL κ`。这是内部编码单射；它既不断言满射或基数相等，也不涉及任何塌缩像。因此，构造壳的所有成员在内部都有彼此不同的 `κ`-码。
<!--ja-->
最小逆像の構成は包から `prodL κ` への符号化された単射を与え、平方則は `prodL κ` から `κ` への符号化された単射を与える。両者を合成すると、命題的に切り詰められた主張 `InjL hullL κ` が得られる。これは内部で符号化された単射であり、全射も基数の等しさも主張せず、崩壊像についても何も述べない。したがって、構成可能包のすべての要素には、内部で互いに異なる `κ` の符号がある。
<!--/-->

```agda
  hull↪κ : InjL hullL κ
  hull↪κ = injl-trans hullL (prodL κ) κ (LF.Functional.injL funct-fin) pairκ
```
