<!--en-->
# The satisfaction graph formula
<!--zh-->
# 满足关系图公式
<!--ja-->
# 充足関係のグラフを表す論理式
<!--/-->

<!--en-->
The recursive construction `Sat` assigns a set of satisfying environments to each formula, but that metatheoretic assignment cannot simply be named inside a first-order definition over `L`. The task of this chapter is to give a binary object-language formula that can later serve as the relation for such queries. Its witnesses will describe enough local data to satisfy the recursion equations around the queried key, without assuming in advance that a canonical or single-valued table has already been obtained.
<!--zh-->
递归构造 `Sat` 为每条公式指定一个由满足环境组成的集合，但这项元理论赋值不能直接在 `L` 上的一阶定义中被点名。本章的任务是给出一条对象语言二元公式，使它随后能够充当这类查询所用的关系。公式的见证将描述足以在查询键周围满足递归方程的局部数据，而不预先假设已经得到一张典范或单值的表。
<!--ja-->
再帰的構成 `Sat` は各論理式に、それを満たす環境の集合を割り当てる。しかし、このメタ理論上の割当てを `L` 上の一階定義の内部でそのまま名指すことはできない。本章の課題は、後でそのような問い合わせの関係として使える対象言語の二項論理式を与えることである。論理式の証人は、問い合わせるキーの周囲で再帰方程式を満たすのに十分な局所データを記述するが、正準な表や一価な表がすでに得られているとは仮定しない。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}
```

<!--en-->
Excluded middle is available at the required universe level because the environment-tower interface used below carries that assumption. The formula assembled in this chapter does not itself decide propositions by cases; its quantifiers and connectives receive their meaning from the established first-order semantics.
<!--zh-->
下文使用的环境塔接口携带相应宇宙层级上的排中律假设，所以本章也取得这一假设。不过，本章组装公式时并不按命题作排中分类；公式中的量词与联结词都由已经建立的一阶语义解释。
<!--ja-->
以下で用いる環境の塔のインターフェースが、必要な宇宙レベルでの排中律を仮定するため、本章もその仮定を受け取る。ただし、ここで組み立てる論理式が命題を排中律で場合分けするわけではない。量化子と結合子の意味は、すでに構成された一階意味論から得られる。
<!--/-->

```agda
open import Base.Prelude
open import Base.Classical using ( LEM )
```

<!--en-->
Fix a universe level and this one classical parameter. The relation to be defined holds of a formula key `x` and a set `y` exactly when some locally qualified candidate satisfaction table over the carrier records `y` at `x`. At this stage it asserts only the existence of such local data; it neither selects a canonical table nor proves that every key has a unique value.
<!--zh-->
固定宇宙层级与这一项经典参数。要定义的关系在公式键 `x` 与集合 `y` 处成立，恰好表示某张载体上的局部合格候选满足关系表在 `x` 处记录了 `y`。此处只断言这样的局部数据存在，既不选定典范表，也不证明每个键都有唯一取值。
<!--ja-->
宇宙レベルとこの一つの古典的パラメータを固定する。これから定める関係が論理式キー `x` と集合 `y` について成り立つのは、台上の局所的な条件を満たす候補の充足関係表が `x` で `y` を記録するとき、かつそのときに限る。この段階で主張するのは、そのような局所データの存在だけである。正準な表を選ぶことも、すべてのキーで値が一意であることを証明することもない。
<!--/-->

```agda
module L.Coding.SatisfactionGraph {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where
```

<!--en-->
The formula language provides variables, constants, equality, conjunction, and existential quantification. Constants allow fixed constructible sets, such as the standard numerals used for tags, to occur directly in a formula, while `pr` encodes the ordered pairs used as graph entries. The ambient hierarchy supplies the semantics in which these formulas will be read.
<!--zh-->
公式语言提供变元、常元、相等、合取与存在量化。常元使标签所用的标准数码等固定可构造集合能够直接出现在公式中，`pr` 则编码作为图条目的有序对。周遭层级提供解释这些公式的语义。
<!--ja-->
論理式の言語には、変数、定数、等号、連言、存在量化がある。定数を使えば、タグに用いる標準の数項のような固定された構成可能集合を論理式に直接入れられる。また、`pr` はグラフ要素となる順序対を符号化する。これらの論理式を読む意味論は周囲の階層から得られる。
<!--/-->

```agda
open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula; var; con; _≐_; _∧̇_; ∃̇_ )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Coding {ℓ} using ( pr )
```

<!--en-->
Three descriptions organize the candidate data. `appAt` reads an encoded pair as a graph entry, `domAt T C` says that the key domain of the table `T` is exactly `C`, and `closedAt C` requires the keys in `C` to contain the direct subformula keys needed by compound formulas. The domain in `domAt` is the table's domain of keys; it is distinct from the environment sets that later occur as table values.
<!--zh-->
三种描述组织候选数据。`appAt` 把编码对读作图条目，`domAt T C` 说明表 `T` 的键定义域恰为 `C`，`closedAt C` 则要求 `C` 中的复合公式键所需的直接子公式键仍在 `C` 中。`domAt` 所说的是表的键定义域，与后来作为表值出现的环境集不同。
<!--ja-->
候補データは三つの記述によって組織される。`appAt` は符号化された対をグラフ要素として読み、`domAt T C` は表 `T` のキー領域がちょうど `C` であることを述べ、`closedAt C` は `C` 内の複合論理式キーが必要とする直下の部分式キーも `C` に属することを要求する。`domAt` が述べるのは表のキー領域であり、後に表の値として現れる環境集合とは異なる。
<!--/-->

```agda
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans )
open import L.Coding.Model {ℓ} using ( domAt; appAt; appAt-adequate )
open import L.Coding.Closure {ℓ} using ( closedAt )
open import L.Coding.Quantification {ℓ} using
  ( f0; f1; f2; f3; f4; f5; f6; f7; f8; f9; i0; i1; i2; i3; i4; i5; i6; i7; i8; i9; i10; i11; i12; i13; sh )
```

<!--en-->
The remaining descriptions prepare the local recursion equations. `towerAt` supplies candidate rows of encoded environments, `Tags` calibrates the ten constructor-tag slots, and `tableAt` combines propositional totality on the candidate key set, restriction of table entries to that set, and ten local extensional equations. These ingredients still describe only a candidate relation. `PinnedRecursion` proves the conditional uniqueness needed at a genuine formula key, while `SatisfactionBridge` independently interprets membership in the external value `Sat` as satisfaction in the restricted structure. `UniformSatisfaction` then combines existence with pinned uniqueness on `AllCodes B` to obtain a uniform table.
<!--zh-->
其余描述为局部递归方程作准备。`towerAt` 提供编码环境的候选各行，`Tags` 校准十个构造子标签槽，`tableAt` 则合并候选键集上的命题截断全定义性、表条目的键限于该集合这一条件，以及十条局部外延方程。这些材料仍然只描述一项候选关系。`PinnedRecursion` 证明真正公式键处所需的条件唯一性，`SatisfactionBridge` 则独立地把属于外部取值 `Sat` 解释为在限制结构中得到满足。随后，`UniformSatisfaction` 在 `AllCodes B` 上把存在性与钉扎所得的唯一性结合起来，得到一张一致的表。
<!--ja-->
残る記述は、局所的な再帰方程式を準備する。`towerAt` は符号化環境の候補となる各行を与え、`Tags` は十個の構成子タグのスロットを校正する。`tableAt` は、候補キー集合上の命題的に切り詰められた全域性、表項目のキーをその集合に限る条件、十個の局所的な外延方程式をまとめる。これらの材料が記述するのは、まだ候補関係だけである。`PinnedRecursion` は真正な論理式キーで必要となる条件付き一意性を証明し、`SatisfactionBridge` は独立に、外部の値 `Sat` への所属を制限構造での充足として解釈する。その後、`UniformSatisfaction` が `AllCodes B` 上で存在と固定された一意性を組み合わせ、一様な表を得る。
<!--/-->

```agda
open import L.Coding.EnvironmentTower {ℓ} lem using ( nn; towerAt )
open import L.Coding.CodeDomain {ℓ} using ( Tags )
open import L.Coding.SatisfactionClauses {ℓ} using ( tableAt )
```

<!--en-->
An interpretation environment for a formula with `n` free positions is a vector of `n` carrier elements. `lookup` reads the element assigned to a position, while cons extends an environment at its innermost end. This fixed convention will let fourteen auxiliary witnesses be placed in front of an arbitrary outer environment without losing the original query positions.
<!--zh-->
具有 `n` 个自由位置的公式，其解释环境是由 `n` 个载体元素组成的向量。`lookup` 读取某个位置所赋的元素，cons 则在环境最内端加入新元素。借助这一固定约定，可以在任意外围环境之前放入十四个辅助见证，同时仍保留原来的查询位置。
<!--ja-->
自由な位置を `n` 個もつ論理式の解釈環境は、`n` 個の台の要素からなるベクトルである。`lookup` はある位置に割り当てられた要素を読み、cons は環境の最も内側に新しい要素を加える。この規約により、任意の外側の環境の前に十四個の補助的な証人を置いても、元の問い合わせ位置を保てる。
<!--/-->



<!--en-->
Object-language existence is interpreted by propositional truncation. Thus a proof of an existential formula records that a witness exists while forgetting which witness was used. This is essential for the satisfaction graph: the public reading may establish that suitable tags, a tower, a key set, and a table exist, but it does not expose data from which a caller could choose one candidate table globally.
<!--zh-->
对象语言的存在由命题截断解释。因此，存在公式的证明只保留见证存在这一事实，而忘掉具体使用了哪个见证。这对满足关系图至关重要：公开读式可以确认合适的标签、塔、键集与表存在，却不会暴露能让使用者全局选定某张候选表的数据。
<!--ja-->
対象言語の存在は命題的切り詰めによって解釈される。そのため、存在論理式の証明は証人が存在するという事実だけを残し、どの証人を用いたかを忘れる。これは充足関係グラフにとって本質的である。公開される読みは、適切なタグ、塔、キー集合、表が存在することを示せるが、利用者が候補の表を大域的に一つ選べるようなデータは公開しない。
<!--/-->

```agda
open import Cubical.HITs.CumulativeHierarchy.Base using ( _∈_ )
```

<!--en-->
From now on `S` is the carrier of the constructible structure: an element consists of a hierarchy set together with evidence of constructibility. Relations in this structure have proposition-valued truth values, and brackets expose the underlying proposition whose inhabitants are proofs. Equality or membership of the underlying hierarchy sets must therefore remain distinct from an object-language formula that asserts equality or membership.
<!--zh-->
从现在起，`S` 表示可构造结构的载体：它的元素由一个层级集合及其可构造性证据组成。结构中的关系取命题值，尖括号取出其底层命题，而证明就是该命题的元素。因此，底层层级集合的相等或隶属必须与对象语言中断言相等或隶属的公式区别开来。
<!--ja-->
以下では、`S` を構成可能構造の台とする。その要素は階層の集合と、それが構成可能であることの証拠からなる。この構造の関係は命題値をとり、山括弧は証明が要素となる基礎の命題を取り出す。したがって、基礎となる階層集合の等しさや所属と、等号や所属を主張する対象言語の論理式とは区別しなければならない。
<!--/-->

```agda
open hPropStructure 𝒮ʟ
```

<!--en-->
The judgment `γ ⊨ φ` now means that the object-language formula `φ` holds under the constructible environment `γ`. It connects the finite vector of semantic values to the syntax of the formula. In particular, the outer environment used to ask about a key and a proposed value is a metatheoretic assignment; it is not one of the encoded environment sets arranged in the tower.
<!--zh-->
判断 `γ ⊨ φ` 表示对象语言公式 `φ` 在可构造环境 `γ` 下成立，它把语义值组成的有限向量与公式语法连接起来。尤其要注意，用来查询某个键及其候选值的外围环境是元理论赋值，并不是环境塔中排列的某个编码环境集。
<!--ja-->
判定 `γ ⊨ φ` は、対象言語の論理式 `φ` が構成可能な環境 `γ` のもとで成り立つことを意味する。これは意味論的な値の有限ベクトルを論理式の構文に結びつける。特に、キーとその候補値を問い合わせる外側の環境はメタ理論上の割当てであり、環境の塔に並ぶ符号化環境集合の一つではない。
<!--/-->

```agda
module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL renaming ( _⊨ᵐ_ to _⊨_ )
```

<!--en-->
## The guarded recursion frame
<!--zh-->
## 带守卫的递归框架
<!--ja-->
## 再帰条件を守る枠組み
<!--/-->

<!--en-->
The first four names describe the structural core of the fourteen new positions. From the innermost position outward they hold the carrier `b`, the candidate satisfaction table `T`, its candidate key set `C`, and the candidate environment tower `E`. Keeping these roles separate prevents two tempting confusions: elements of `C` are formula keys, whereas elements of `T` encode key-value pairs, and the rows represented through `E` organize encoded environments by arity.
<!--zh-->
前四个名称描述十四个新位置的结构核心。由最内向外，它们依次容纳载体 `b`、候选满足关系表 `T`、候选键集 `C` 与候选环境塔 `E`。区分这些角色可以避免两种常见混淆：`C` 的元素是公式键，`T` 的元素编码键值对，而由 `E` 表示的各行按元数组织编码环境。
<!--ja-->
最初の四つの名前は、十四個の新しい位置の構造的な中心を表す。最も内側から順に、台 `b`、候補となる充足関係表 `T`、その候補キー集合 `C`、候補となる環境の塔 `E` が入る。これらの役割を分けると、二つの混同を避けられる。`C` の要素は論理式キーであり、`T` の要素はキーと値の対を符号化する。また、`E` によって表される各行は、符号化環境をアリティごとに組織する。
<!--/-->

```agda
Bi Ti Ci Ei : ∀ {n} → Fin (14 + n)
Bi = i0
Ti = i1
Ci = i2
Ei = i3
```

<!--en-->
The next ten positions are constructor tags. `NN` begins their common address map by sending constructor indices zero through three to positions `i4` through `i7`. Before calibration these positions may contain arbitrary carrier elements, so the local clauses merely use them as parameters identifying code shapes.
<!--zh-->
接下来的十个位置是构造子标签。`NN` 给出统一的位置映射，先把零至三号构造子指标送到 `i4` 至 `i7`。在校准之前，这些位置可以含有任意载体元素，所以局部子句暂时只把它们当作辨认码形状的参数。
<!--ja-->
続く十個の位置は構成子タグである。`NN` は共通の位置対応を与え、まず構成子の添字ゼロから三までを `i4` から `i7` に送る。校正前の各位置には任意の台の要素が入りうるため、局所的な節はそれらを符号の形を識別するパラメータとして用いるだけである。
<!--/-->

```agda
NN : ∀ {n} → Fin 10 → Fin (14 + n)
NN zero = i4
NN (suc zero) = i5
NN (suc (suc zero)) = i6
NN (suc (suc (suc zero))) = i7
```

<!--en-->
The same map continues consecutively through constructor eight. This uniform indexing matters because closure and the ten table equations must agree on which numeral marks each formula constructor. Once that agreement is fixed, one family of clauses can cover atoms, the three binary connectives, falsity, the two unbounded quantifiers, and the two bounded quantifiers.
<!--zh-->
同一映射依次延伸到八号构造子。统一索引之所以重要，是因为封闭性条件与十条表方程必须就每种公式构造子由哪个数码标记达成一致。校准完成后，同一子句族便能涵盖原子式、三种二元联结词、假、两种无界量词与两种有界量词。
<!--ja-->
同じ対応は構成子八まで連続して続く。この一様な添字付けが必要なのは、閉性条件と十個の表方程式が、各論理式構成子をどの数項で示すかについて一致しなければならないからである。校正後は、一つの節の族で原子式、三つの二項結合子、偽、二つの非有界量化子、二つの有界量化子を扱える。
<!--/-->

```agda
NN (suc (suc (suc (suc zero)))) = i8
NN (suc (suc (suc (suc (suc zero))))) = i9
NN (suc (suc (suc (suc (suc (suc zero)))))) = i10
NN (suc (suc (suc (suc (suc (suc (suc zero))))))) = i11
NN (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) = i12
```

<!--en-->
The last equation places constructor nine at `i13`, completing the layout
`b, T, C, E, N0, ..., N9` from the innermost position outward. The environment tower occupies one position as the candidate set `E`; its arity-indexed rows are encoded entries described by `towerAt`, rather than ten further positions in this vector.
<!--zh-->
最后一条方程把九号构造子放在 `i13`，由最内向外的布局 `b, T, C, E, N0, ..., N9` 至此完整。环境塔只以候选集合 `E` 占据一个位置；它按元数索引的各行是由 `towerAt` 描述的编码条目，并不是这个向量中的另外十个位置。
<!--ja-->
最後の方程式は構成子九を `i13` に置き、最も内側から外へ並ぶ `b, T, C, E, N0, ..., N9` という配置を完成させる。環境の塔が占める位置は候補集合 `E` の一つだけである。アリティで添字付けられた各行は `towerAt` が記述する符号化要素であり、このベクトル内の別の十個の位置ではない。
<!--/-->

```agda
NN (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))) = i13
```

<!--en-->
The query key and proposed value remain in the caller's environment outside these fourteen positions. The shift `sh14` moves either original position across all fourteen binders, so a later occurrence such as `appAt Ti (sh14 x) (sh14 y)` still asks whether the original pair `(x,y)` is recorded in `T`.
<!--zh-->
查询键与候选值仍留在这十四个位置之外的调用方环境中。移位 `sh14` 把原位置越过全部十四个绑定，所以后来出现的 `appAt Ti (sh14 x) (sh14 y)` 仍是在询问原来的对 `(x,y)` 是否记录于 `T`。
<!--ja-->
問い合わせるキーと候補値は、この十四個の位置の外側にある呼び出し側の環境に残る。シフト `sh14` は元の位置を十四個すべての束縛の先へ移すので、後の `appAt Ti (sh14 x) (sh14 y)` も、元の対 `(x,y)` が `T` に記録されているかを問う。
<!--/-->

```agda
sh14 : ∀ {n} → Fin n → Fin (14 + n)
sh14 i = sh 14 i
```

<!--en-->
The function `ev` is the semantic realization of this position map. It places `b`, `T`, `C`, `E`, and the ten values supplied by `ν` in front of the outer environment `γ`. Consequently every named slot used by `Tags`, `towerAt`, `closedAt`, `domAt`, and `tableAt` refers to the same witness throughout the argument.
<!--zh-->
函数 `ev` 是这张位置映射的语义实现。它把 `b`、`T`、`C`、`E` 以及 `ν` 给出的十个值依次放在外围环境 `γ` 之前。因此，`Tags`、`towerAt`、`closedAt`、`domAt` 与 `tableAt` 所用的每个具名槽，在整个论证中始终指向同一个见证。
<!--ja-->
関数 `ev` は、この位置対応を意味論的に実現する。`b`、`T`、`C`、`E` と、`ν` が与える十個の値を外側の環境 `γ` の前に並べる。その結果、`Tags`、`towerAt`、`closedAt`、`domAt`、`tableAt` が用いる各スロットは、議論を通して同じ証人を指す。
<!--/-->

```agda
ev : ∀ {n} → (Fin 10 → S) → S → S → S → S → S ^ n → S ^ (14 + n)
ev ν E C T b γ =
  b ∷ T ∷ C ∷ E ∷ ν f0 ∷ ν f1 ∷ ν f2 ∷ ν f3 ∷ ν f4 ∷ ν f5
    ∷ ν f6 ∷ ν f7 ∷ ν f8 ∷ ν f9 ∷ γ
```

<!--en-->
For the canonical tag assignment, constructor index `k` is sent to the model numeral `nn (toℕ k)`. Its underlying hierarchy set is the finite ordinal representing `k`, while its second component certifies constructibility. Packaging the numeral as an element of `S` lets the object language name it by a constant.
<!--zh-->
在典范标签赋值中，构造子指标 `k` 被送到模型数码 `nn (toℕ k)`。其底层层级集合是表示 `k` 的有限序数，第二分量则证明它可构造。把数码包装成 `S` 的元素以后，对象语言便能用常元点名它。
<!--ja-->
正準なタグの割当てでは、構成子の添字 `k` をモデルの数項 `nn (toℕ k)` に送る。その基礎となる階層集合は `k` を表す有限順序数であり、第二成分は構成可能性を証明する。数項を `S` の要素としてまとめることで、対象言語から定数として名指せる。
<!--/-->

```agda
numν : Fin 10 → S
numν k = nn (toℕ k)
```

<!--en-->
`Tags γ NN` asks, for every constructor index `k`, whether the underlying set at position `NN k` is the numeral for `k`. In the environment built from `numν`, the first four cases hold by reflexivity because lookup and first projection compute to that numeral. The statement compares underlying sets, so it does not require the constructibility certificates themselves to be definitionally equal.
<!--zh-->
`Tags γ NN` 对每个构造子指标 `k` 询问：位置 `NN k` 上元素的底层集合是否为 `k` 的数码。在由 `numν` 构成的环境中，前四种情形都由自反性成立，因为查找与第一投影计算后正是该数码。该陈述比较底层集合，并不要求可构造性证书本身定义相等。
<!--ja-->
`Tags γ NN` は各構成子の添字 `k` について、位置 `NN k` にある要素の基礎集合が `k` の数項であるかを問う。`numν` から作った環境では、lookup と第一射影を計算するとその数項になるため、最初の四つの場合は反射律で成り立つ。この主張が比較するのは基礎集合であり、構成可能性の証明書そのものの定義的な等しさは要求しない。
<!--/-->

```agda
numTags : ∀ {n} (E C T b : S) (γ : S ^ n) → Tags (ev numν E C T b γ) NN
numTags E C T b γ zero = refl
numTags E C T b γ (suc zero) = refl
numTags E C T b γ (suc (suc zero)) = refl
numTags E C T b γ (suc (suc (suc zero))) = refl
```

<!--en-->
Reflexivity also proves the cases for indices four through eight. The longer successor patterns carry only the finite-index bookkeeping: `NN k` selects the slot occupied by `numν k`, whose first projection is the required numeral. Thus the proof remains pointwise and introduces no constructor-specific semantic assumption.
<!--zh-->
四至八号指标的情形同样由自反性证明。较长的后继形式只承担有限指标的记账：`NN k` 选中 `numν k` 所在的槽，而后者的第一投影就是所需数码。因此，这项证明始终是逐点计算，不会引入针对某个构造子的额外语义假设。
<!--ja-->
添字四から八の場合も反射律で証明できる。長い後続の形が担うのは有限添字の整理だけである。`NN k` は `numν k` が入るスロットを選び、その第一射影が必要な数項になる。したがって、この証明は各点での計算のままであり、特定の構成子に固有の意味論的仮定を加えない。
<!--/-->

```agda
numTags E C T b γ (suc (suc (suc (suc zero)))) = refl
numTags E C T b γ (suc (suc (suc (suc (suc zero))))) = refl
numTags E C T b γ (suc (suc (suc (suc (suc (suc zero)))))) = refl
numTags E C T b γ (suc (suc (suc (suc (suc (suc (suc zero))))))) = refl
numTags E C T b γ (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) = refl
```

<!--en-->
Index nine exhausts `Fin 10`, so the same reflexivity argument completes a total proof of `Tags` for the canonical assignment. Other assignments may still serve as candidate witnesses, but they must carry their own proof of this pointwise agreement before the ten constructor clauses acquire the intended tags.
<!--zh-->
九号指标穷尽 `Fin 10`，同一项自反性论证因而完成典范赋值满足 `Tags` 的全函数证明。其他赋值仍可充当候选见证，但必须自行携带这项逐点一致的证明，十条构造子子句才能取得预期标签。
<!--ja-->
添字九で `Fin 10` の全要素が尽くされるため、同じ反射律の議論によって、正準な割当てが `Tags` を満たすことの全域的な証明が完成する。別の割当ても候補の証人にはなれるが、十個の構成子の節を意図したタグで読むには、この各点での一致を自ら証明しなければならない。
<!--/-->

```agda
numTags E C T b γ (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))) = refl
```

<!--en-->
The object-language formula `numsAt` begins the same calibration as a right-associated conjunction of equations. Its first eight equations say that the values at positions `i4` through `i11` are the constants `nn 0` through `nn 7`. Thus the later variable-carrier form of the graph avoids naming the carrier as a constant, but the graph formula still names these fixed standard numerals.
<!--zh-->
对象语言公式 `numsAt` 以向右结合的等式合取表达同一校准。前八条等式说明位置 `i4` 至 `i11` 的值依次为常元 `nn 0` 至 `nn 7`。因此，后面的变元载体版本不会用常元点名载体，但图公式仍会点名这些固定的标准数码。
<!--ja-->
対象言語の論理式 `numsAt` は、同じ校正を右結合した等式の連言として始める。最初の八つの等式は、位置 `i4` から `i11` の値が順に定数 `nn 0` から `nn 7` であることを述べる。したがって、後の変数で台を与える形は台を定数として名指さないが、グラフの論理式はこれらの固定された標準の数項を名指す。
<!--/-->

```agda
numsAt : ∀ {n} → Formula S (14 + n)
numsAt =
  (var i4 ≐ con (nn 0)) ∧̇ ((var i5 ≐ con (nn 1)) ∧̇ ((var i6 ≐ con (nn 2)) ∧̇
  ((var i7 ≐ con (nn 3)) ∧̇ ((var i8 ≐ con (nn 4)) ∧̇ ((var i9 ≐ con (nn 5)) ∧̇
  ((var i10 ≐ con (nn 6)) ∧̇ ((var i11 ≐ con (nn 7)) ∧̇
```

<!--en-->
The equations for `i12` and `i13` finish the calibration with numerals eight and nine. Satisfaction of the complete conjunction therefore carries exactly the ten equations required by `Tags`; the following read lemma extracts those equations from the nested conjunction. This calibration identifies constructor tags only and adds no claim that the candidate key set is the complete set of well-formed formula codes.
<!--zh-->
关于 `i12` 与 `i13` 的等式以八、九两个数码完成校准。因此，满足整个合取恰好携带 `Tags` 所需的十条等式；接下来的读引理将从嵌套合取中取出它们。这项校准只认同构造子标签，并不宣称候选键集就是完整的良构公式码集。
<!--ja-->
`i12` と `i13` の等式が、数項八と九によって校正を完成させる。したがって、連言全体の充足は `Tags` が要求する十個の等式をちょうど含み、続く読みの補題が入れ子の連言からそれらを取り出す。この校正が同定するのは構成子タグだけであり、候補キー集合が整形式な論理式符号の完全な集合だという主張は加えない。
<!--/-->

```agda
  ((var i12 ≐ con (nn 8)) ∧̇ (var i13 ≐ con (nn 9))))))))))
```

<!--en-->
`nums-out` turns satisfaction of `numsAt` into the host-level family `Tags`. Since conjunction is interpreted as a pair, the case for tag zero takes the first projection, and the cases for tags one and two follow the second projection before taking the next first projection. The lemma works for an arbitrary tag assignment `ν`, so it can decode the calibration carried by any candidate graph witness.
<!--zh-->
`nums-out` 把 `numsAt` 的满足转成宿主层的 `Tags` 族。合取被解释为对，所以零号标签情形取第一投影，一号与二号情形则先沿第二投影进入，再取下一层的第一投影。该引理适用于任意标签赋值 `ν`，因而能读出任何候选图见证所携带的校准。
<!--ja-->
`nums-out` は `numsAt` の充足をホスト層の族 `Tags` に移す。連言は対として解釈されるので、タグゼロの場合は第一射影を取り、タグ一と二の場合は第二射影をたどってから次の第一射影を取る。この補題は任意のタグ割当て `ν` に使えるため、どの候補グラフの証人がもつ校正も読み出せる。
<!--/-->

```agda
nums-out : ∀ {n} (ν : Fin 10 → S) (E C T b : S) (γ : S ^ n)
         → ⟨ ev ν E C T b γ ⊨ numsAt ⟩ → Tags (ev ν E C T b γ) NN
nums-out ν E C T b γ h zero = h .fst
nums-out ν E C T b γ h (suc zero) = h .snd .fst
nums-out ν E C T b γ h (suc (suc zero)) = h .snd .snd .fst
```

<!--en-->
For every higher index, `nums-out` follows the second projection of the right-associated product until it reaches the corresponding equality. This is only elimination of conjunction: it neither chooses tag values nor proves them unique. When the fourteen existential witnesses are later eliminated under propositional truncation, these projections recover the tag certificate already present in the formula's satisfaction.
<!--zh-->
对每个更高指标，`nums-out` 都沿向右结合之积的第二投影深入，直到取得相应等式。这只是对合取的消去，既不选择标签值，也不证明其唯一。后续在命题截断下消去十四个存在见证时，这些投影会恢复公式满足中原已包含的标签证书。
<!--ja-->
より大きい各添字について、`nums-out` は右結合した積の第二射影をたどり、対応する等式に到達する。ここで行うのは連言の除去だけであり、タグの値を選ぶことも、その一意性を証明することもない。後に十四個の存在証人を命題的切り詰めのもとで除去するとき、これらの射影が、論理式の充足にすでに含まれているタグの証明を復元する。
<!--/-->

```agda
nums-out ν E C T b γ h (suc (suc (suc zero))) = h .snd .snd .snd .fst
nums-out ν E C T b γ h (suc (suc (suc (suc zero)))) = h .snd .snd .snd .snd .fst
nums-out ν E C T b γ h (suc (suc (suc (suc (suc zero))))) = h .snd .snd .snd .snd .snd .fst
nums-out ν E C T b γ h (suc (suc (suc (suc (suc (suc zero)))))) = h .snd .snd .snd .snd .snd .snd .fst
nums-out ν E C T b γ h (suc (suc (suc (suc (suc (suc (suc zero))))))) = h .snd .snd .snd .snd .snd .snd .snd .fst
```

<!--en-->
The deepest component of the right-associated conjunction is the pair of equations for tags eight and nine. Its two projections complete the pointwise family, so satisfaction of `numsAt` yields agreement at every index of `Fin 10` at once. This step only repackages the ten equations; it adds no condition on the candidate key set or table.
<!--zh-->
向右结合的合取最深处是关于八号与九号标签的一对等式。取出它的两个投影便补全逐点等式族，所以 `numsAt` 的满足会一次给出 `Fin 10` 每个指标处的一致。这一步只重新打包十条等式，不会给候选键集或候选表添加任何条件。
<!--ja-->
右結合した連言の最も深い成分は、タグ八と九に関する二つの等式の対である。その二つの射影によって各点の等式族が完成するため、`numsAt` の充足から `Fin 10` のすべての添字での一致が一度に得られる。この段階で行うのは十個の等式の組み直しだけであり、候補キー集合や候補表に新しい条件を加えることはない。
<!--/-->

```agda
nums-out ν E C T b γ h (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) = h .snd .snd .snd .snd .snd .snd .snd .snd .fst
nums-out ν E C T b γ h (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))) = h .snd .snd .snd .snd .snd .snd .snd .snd .snd
```

<!--en-->
The converse reading `nums-in`{.Agda} starts from `Tags`: for each constructor index, the chosen tag has the same underlying set as the corresponding standard numeral. Placing these ten equalities into the right-associated conjunction proves `numsAt`{.Agda}. Together, `nums-out`{.Agda} and `nums-in`{.Agda} let the rest of the chapter move in either direction between the object-language calibration and its host-level family of equalities.
<!--zh-->
反向读法 `nums-in`{.Agda} 从 `Tags` 出发：对每个构造子指标，所选标签与相应标准数码具有相同底集。按右结合的次序把这十条等式组成合取，便得到 `numsAt`{.Agda} 的满足。`nums-out`{.Agda} 与 `nums-in`{.Agda} 合在一起，使后文可以在对象语言的校准公式与宿主层的等式族之间双向转换。
<!--ja-->
逆向きの読み `nums-in`{.Agda} は `Tags` から出発する。各構成子の添字について、選ばれたタグと対応する標準数項の基底集合が等しいというデータである。これら十個の等式を右結合の連言に並べると、`numsAt`{.Agda} の充足が得られる。`nums-out`{.Agda} と `nums-in`{.Agda} により、以下では対象言語の校正論理式とホスト層の等式族との間を双方向に移れる。
<!--/-->

```agda
nums-in : ∀ {n} (ν : Fin 10 → S) (E C T b : S) (γ : S ^ n)
        → Tags (ev ν E C T b γ) NN → ⟨ ev ν E C T b γ ⊨ numsAt ⟩
nums-in ν E C T b γ tg =
    tg f0 , (tg f1 , (tg f2 , (tg f3 , (tg f4 , (tg f5
  , (tg f6 , (tg f7 , (tg f8 , tg f9))))))))
```

<!--en-->
The auxiliary family `satGraphOn` now assembles the complete frame. Its parameter `pin` is a formula over the extended environment and specifies only how the newly bound carrier is related to an outer reference; the query positions `x` and `y` remain in the outer environment. Fourteen nested existentials bind the ten tags, the tower, the key set, the table, and finally the innermost carrier. Their first conjunct is `pin`, so changing the carrier policy leaves every other condition of the candidate graph unchanged.
<!--zh-->
辅助公式族 `satGraphOn` 现在把完整框架组装起来。参数 `pin` 是扩张环境上的一条公式，只规定新绑定的载体如何与外围参照相关；查询位置 `x` 与 `y` 仍留在外围环境中。十四层嵌套存在量词依次绑定十个标签、塔、键集、表，最后在最内层绑定载体。它们的第一个合取项就是 `pin`，所以改变载体的固定方式不会改变候选图的其他任何条件。
<!--ja-->
補助的な論理式の族 `satGraphOn` が、ここで枠組み全体を組み立てる。パラメータ `pin` は拡張された環境上の論理式であり、新たに束縛される台と外側の参照との関係だけを指定する。問い合わせ位置 `x` と `y` は外側の環境に残る。十四重の存在量化が十個のタグ、塔、キー集合、表を束縛し、最後に最も内側で台を束縛する。最初の連言項が `pin` なので、台の固定方法を変えても候補グラフのほかの条件は変わらない。
<!--/-->

```agda

private
  satGraphOn : ∀ {n} → Formula S (14 + n)
             → Fin n → Fin n → Formula S n
  satGraphOn pin x y =
    ∃̇ (∃̇ (∃̇ (∃̇ (∃̇ (∃̇ (∃̇ (∃̇ (∃̇ (∃̇ (∃̇ (∃̇ (∃̇ (∃̇ (( pin
```

<!--en-->
After the pin, the conjunction records the conditions needed to interpret one table entry. The calibration `numsAt`{.Agda} identifies the ten tag slots with the standard numerals. The clause `towerAt Ei Bi (NN f0)` requires the candidate tower to have the row structure used by the recursive clauses over the bound carrier; it does not assert that the tower is canonical. The clause `closedAt Ci` closes the candidate key set under the seven possible immediate subformula keys. Next, `domAt Ti Ci` says that the key domain of the table is exactly `C`, while `appAt Ti (sh14 x) (sh14 y)` says that the original query pair is an entry after `x` and `y` have been shifted past all fourteen binders.
<!--zh-->
pin 之后的合取列出解释一个表项所需的条件。校准公式 `numsAt`{.Agda} 把十个标签槽认同为标准数码。子句 `towerAt Ei Bi (NN f0)` 要求候选塔在被绑定载体上具备递归子句所需的各行结构，但不声称该塔是典范的。`closedAt Ci` 要求候选键集对七种可能的直接子公式键封闭。随后，`domAt Ti Ci` 断言表的键定义域恰为 `C`，而 `appAt Ti (sh14 x) (sh14 y)` 断言原查询对在 `x` 与 `y` 越过全部十四个绑定后仍是表的一项。
<!--ja-->
pin に続く連言は、一つの表項目を解釈するための条件を並べる。校正論理式 `numsAt`{.Agda} は、十個のタグのスロットを標準数項と同一視する。`towerAt Ei Bi (NN f0)` は、候補の塔が、束縛された台上で再帰の節に必要な行の構造をもつことを要求するが、その塔が正準であるとは主張しない。`closedAt Ci` は候補キー集合を、七通りの直接の部分式のキーについて閉じる。`domAt Ti Ci` は表のキー領域がちょうど `C` であることを述べ、`appAt Ti (sh14 x) (sh14 y)` は、`x` と `y` を十四の束縛の先へ移した後も、もとの問い合わせの対が表項目であることを述べる。
<!--/-->

```agda
      ∧̇ ( numsAt
      ∧̇ ( towerAt Ei Bi (NN f0)
      ∧̇ ( closedAt Ci
      ∧̇ ( domAt Ti Ci
      ∧̇ ( appAt Ti (sh14 x) (sh14 y)
```

<!--en-->
The final conjunct `tableAt Ti Bi Ci Ei NN` supplies the local recursion specification. Its first domain condition gives, under propositional truncation, some value for every key in `C`; its second says that every member of `T` can be decomposed, again under truncation, as a key from `C` paired with a value. The remaining ten clauses characterize matching entries by extensional equations, one for each formula constructor. These conditions describe a candidate relation locally. They neither make `T` single-valued nor choose a value for each key. Uniqueness at a genuine formula key is proved later by structural induction in `PinnedRecursion`{.Agda}.
<!--zh-->
最后的合取项 `tableAt Ti Bi Ci Ei NN` 给出局部递归规格。它的第一项域条件说，`C` 中每个键都在命题截断下有某个取值；第二项说，`T` 的每个成员都能再次在命题截断下分解为 `C` 中的键与一个取值之对。余下十条子句分别对应一个公式构造子，用外延方程刻画所有匹配的表项。这些条件只在局部描述一张候选关系，既不使 `T` 成为单值关系，也不为每个键选出一个取值。真实公式键处的唯一性要到后面的 `PinnedRecursion`{.Agda} 中通过结构归纳证明。
<!--ja-->
最後の連言項 `tableAt Ti Bi Ci Ei NN` は、局所的な再帰の仕様を与える。第一の領域条件は、`C` の各キーに対して、命題的切り詰めのもとで何らかの値があることを述べる。第二の条件は、`T` の各要素が、やはり命題的切り詰めのもとで、`C` のキーと値との対に分解できることを述べる。残る十個の節は論理式の構成子に一つずつ対応し、該当する表の項目を外延的な等式で特徴づける。これらは候補関係を局所的に記述するだけで、`T` を一価にせず、各キーの値を選びもしない。真正な論理式のキーにおける一意性は、後の `PinnedRecursion`{.Agda} で構造帰納法により示される。
<!--/-->

```agda
      ∧̇ tableAt Ti Bi Ci Ei NN ))))))))))))))))))))
```

<!--en-->
## Witnesses for the satisfaction graph
<!--zh-->
## 满足关系图的见证
<!--ja-->
## 充足関係グラフの証人
<!--/-->

<!--en-->
The host-level type `GraphWitOn`{.Agda} flattens the same information into five pieces of data, `ν`, `E`, `C`, `T`, and `b`, followed by seven certificates. They assert equality of the underlying sets of `b` and the reference `W`, agreement of all ten tags, satisfaction of the tower, closure, and exact-domain clauses at the assembled environment, membership of the query pair in the underlying table, and satisfaction of `tableAt`{.Agda}. The two domain certificates have different later uses: `domAt`{.Agda} lets a consumer infer that a queried key lies in `C`, whereas the totality component inside `tableAt`{.Agda} supplies values for subkeys during structural induction. Public readings expose this concrete record only through propositional truncation, so they establish existence without selecting a particular candidate table.
<!--zh-->
宿主层类型 `GraphWitOn`{.Agda} 把同一份信息摊平成五项数据 `ν`、`E`、`C`、`T`、`b`，再接七份证书。它们依次断言 `b` 与参照 `W` 的底集相等、十个标签全部一致、塔子句、闭包子句与精确键定义域子句在组装环境中得到满足、查询对属于表的底集，以及 `tableAt`{.Agda} 得到满足。两份域证书在后文用途不同：`domAt`{.Agda} 让使用者从查询条目推出查询键属于 `C`，而 `tableAt`{.Agda} 内的全定义性在结构归纳中为子键提供取值。公开读法只在命题截断下暴露这份具体记录，因而只确立候选表存在，不选定其中一张。
<!--ja-->
ホスト層の型 `GraphWitOn`{.Agda} は、同じ情報を五つのデータ `ν`、`E`、`C`、`T`、`b` と、それに続く七つの証明書へ平らにする。証明書は、`b` と参照 `W` の基底集合の等しさ、十個すべてのタグの一致、組み立てた環境での塔、閉性、正確なキー領域の各節の充足、問い合わせの対が表の基底集合に属すること、そして `tableAt`{.Agda} の充足を述べる。二つの領域に関する証明書は後で異なる役割をもつ。`domAt`{.Agda} は問い合わせのキーが `C` に属することを導き、`tableAt`{.Agda} に含まれる全域性は構造帰納法で部分式のキーに値を供給する。公開される読みは、この具体的な記録を命題的切り詰めを通してのみ示すため、候補の表の存在を確立しても、特定の一つを選ばない。
<!--/-->

```agda
private
  GraphWitOn : ∀ {n} → S → Fin n → Fin n → S ^ n → Type (ℓ-suc ℓ)
  GraphWitOn W x y γ =
    Σ[ ν ∈ (Fin 10 → S) ] (Σ[ E ∈ S ] (Σ[ C ∈ S ] (Σ[ T ∈ S ] (Σ[ b ∈ S ] ((fst b ≡ fst W) × (Tags (ev ν E C T b γ) NN × (⟨ (ev ν E C T b γ) ⊨ towerAt Ei Bi (NN f0) ⟩ × (⟨ (ev ν E C T b γ) ⊨ closedAt Ci ⟩ × (⟨ (ev ν E C T b γ) ⊨ domAt Ti Ci ⟩ × (⟨ pr (fst (lookup x γ)) (fst (lookup y γ)) ∈ fst T ⟩ × ⟨ (ev ν E C T b γ) ⊨ tableAt Ti Bi Ci Ei NN ⟩))))))))))
```

<!--en-->
To compare satisfaction of `satGraphOn` with the flat record, fix the pin, its reference `W`, the query positions, and the outer environment. Every field of the record except the carrier equation already has a fixed interpretation among the frame's conjuncts. The only extra hypothesis is therefore a reading `rd` for the pin. The inward implication turns an equality `fst b ≡ fst W` into satisfaction of `pin`; the outward implication reads satisfaction of `pin` back as that equality.
<!--zh-->
为了比较 `satGraphOn` 的满足与平坦记录，先固定 pin、它所参照的 `W`、两个查询位置及外围环境。除载体等式外，记录中的每个字段都已经在框架的合取项中有固定解释。因此，唯一额外需要的假设是 pin 的读法 `rd`：内向蕴含把等式 `fst b ≡ fst W` 变成 `pin` 的满足，外向蕴含则把 `pin` 的满足读回该等式。
<!--ja-->
`satGraphOn` の充足と平坦な記録を比較するため、pin、その参照 `W`、二つの問い合わせ位置、外側の環境を固定する。台の等式を除けば、記録の各欄はすでに枠組みの連言項の中に定まった解釈をもっている。したがって、追加で必要な仮定は pin の読み `rd` だけである。内向きの含意では等式 `fst b ≡ fst W` を `pin` の充足へ移し、外向きの含意では `pin` の充足をその等式として読み戻す。
<!--/-->


<details open class="submodule-fold">
<summary class="submodule-fold-heading">
```agda
  module _ {n : ℕ} (pin : Formula S (14 + n)) (W : S)
           (x y : Fin n) (γ : S ^ n) where
```
</summary>
<div class="submodule-fold-content">



<!--en-->
The inward reading turns a truncated witness record into satisfaction of the
whole frame. Its hypothesis `rd`{.Agda} says how the pin is to be read: for
any choice of the ten tag values, the tower, the index set, the table and the
carrier, if the carrier agrees with the reference, then the pin is satisfied
at the assembled environment. The input is a truncation and the output is a
satisfaction, itself a truncation, so the whole proof is a map inside
truncations: it sends the flat record, matched component by component, to the
fourteen-level witness the formula demands. No witness is selected anywhere;
a map between truncations transports only the fact that witnesses exist.
<!--zh-->
内向读式把一份被截断的见证记录变成整条框架的满足。它的假设 `rd`{.Agda} 说 pin 应当如何理解：对十个标签值、塔、索引集、表与载体的任何选择，若载体与参照一致，则 pin 在装配出的环境处得到满足。输入是一个截断，输出是一次满足、本身也是截断，故整个证明是截断内部的一个映射：它把那份平坦记录逐分量匹配，送往公式所要求的十四层见证。全程没有任何见证被选取；截断之间的映射只运送「见证存在」这一事实。
<!--ja-->
内向きの読みは、切り詰められた証人の記録を、枠組み全体の充足へ変える。その仮定 `rd`{.Agda} は、pin をどう読むべきかを言う。十個のタグの値、塔、索引集合、表、台のどんな選択に対しても、台が参照と一致するなら、組み立てられた環境のもとで pin が充足される、というものである。入力は切り詰めであり、出力は充足、それ自体が切り詰めである。したがって証明全体は切り詰めの内部の一つの写しになる。平坦な記録を部品ごとに照らし合わせて、論理式が要求する十四重の証人へ送るのである。どこでも証人は選ばれない。切り詰めの間の写しは、証人が存在するという事実だけを運ぶ。
<!--/-->

```agda
    graphOn-in : ((ν : Fin 10 → S) (E C T b : S) → fst b ≡ fst W
                   → ⟨ ev ν E C T b γ ⊨ pin ⟩)
               → ∥ GraphWitOn W x y γ ∥₁ → ⟨ γ ⊨ satGraphOn pin x y ⟩
    graphOn-in rd = map₁
      (λ { (ν , (E , (C , (T , (b , (eb , (tg , (hE , (hc , (hd , (ha , h12))))))))))) →
```

<!--en-->
The flat record is re-nested in the reverse of the layout order. The outermost existential receives the tag of the ninth constructor, the next one the eighth, and so on, until the innermost existential receives the carrier; this is exactly the de Bruijn order of the layout, read from the outside in. The pin's satisfaction is supplied by `rd`{.Agda}, applied to the assembled witnesses and to the carrier equation the record carries. The calibration is converted by `nums-in`{.Agda} from the host-level agreement into satisfaction of the ten equations, so that every later conjunct meets standard numerals.
<!--zh-->
平坦记录按布局的逆序重新嵌套。最外层的存在量词收到第九号构造子的标签，下一个收到第八号，依此下去，直到最内层的存在量词收到载体；这恰是布局的 de Bruijn 次序，由外向内读。pin 的满足由 `rd`{.Agda} 供给：把它施于装配好的诸见证与记录所携带的载体等式。校准则由 `nums-in`{.Agda} 从宿主层的一致转换成十条等式的满足，使后文每个合取项遇到的都是标准数码。
<!--ja-->
平坦な記録は、配置の逆の順序で再び入れ子にされる。最も外側の存在量化が第九構成子のタグを受け取り、次が第八、という具合に、最も内側の存在量化が台を受け取るまで続く。これはまさに配置の de Bruijn の順序を、外から内へ読んだものである。pin の充足は `rd`{.Agda} が供給する。組み立てられた証人と、記録が運ぶ台の等式に適用するのである。校正は `nums-in`{.Agda} が、ホスト層の一致から十個の等式の充足へと変換し、後のどの連言項も標準数項を使うようにする。
<!--/-->

```agda
          ν f9
        , ∣ ν f8 , ∣ ν f7 , ∣ ν f6 , ∣ ν f5 , ∣ ν f4
        , ∣ ν f3 , ∣ ν f2 , ∣ ν f1 , ∣ ν f0 , ∣ E , ∣ C , ∣ T , ∣ b
        , ( rd ν E C T b eb
          , ( nums-in ν E C T b γ tg
```

<!--en-->
The three guard certificates pass through unchanged: they are satisfactions
of formulas read at the very environment the frame assembles, so they can
stand where the conjuncts stand. The query entry is the one component that
must change languages. On the host side it is an ordinary membership: the
ordered pair of the two query values belongs to the underlying set of the
table. The adequacy law of the application atom identifies satisfaction of
the atom with exactly this membership, and the proof transports along that
one path. This is the single substantial bridge of the inward direction;
everything else is re-packing.
<!--zh-->
三份守卫证书原样通过：它们是恰在框架装配的那个环境处读取的公式之满足，因此可以站在合取项所在的地方。查询条目是唯一必须换语言的分量。在宿主一侧它是寻常的隶属：两个查询值的有序对属于表的底层集合。应用原子的充分性律把该原子的满足认同为恰是这个隶属，证明沿那条唯一的路径作运输。这是内向方向唯一的实质性桥梁；其余一切只是重新打包。
<!--ja-->
三つの保護条件の証明書は、そのまま通り抜ける。それらは、枠組みが組み立てるその環境のもとで読んだ論理式の充足だからである。問い合わせの項目が、言語を変えねばならない唯一の部品である。ホスト側ではそれはありふれた所属、すなわち二つの問い合わせ値の順序対が表の基礎集合に属することである。適用の原子の妥当性の法則は、原子の充足をまさにこの所属と同一視し、証明はその一本の道に沿って運搬する。これが内向きの方向における唯一の実質的な橋であり、ほかのすべては組み直しにすぎない。
<!--/-->

```agda
          , ( hE
          , ( hc
          , ( hd
          , ( subst ⟨_⟩
                (sym (appAt-adequate Ti (sh14 x) (sh14 y) (ev ν E C T b γ))) ha
```

<!--en-->
After the clause-family certificate has been placed in the last conjunct, the only remaining work is to restore the nested truncations. The call to `map₁`{.Agda} supplies the outermost truncation: its mapping function returns the witness pair for the outermost existential. Inside that pair, the thirteen explicit insertions supply the remaining existential layers down to the carrier. Thus the construction turns the truncated flat record into satisfaction of all fourteen nested existentials without exposing any of its chosen data outside a truncation.
<!--zh-->
把子句族的证书放入最后一个合取项后，只需恢复各层嵌套的截断。`map₁`{.Agda} 的调用提供最外层截断，因为它的映射函数返回最外层存在量词所需的见证对；这对之内的十三次显式写入则依次提供余下各层，直到载体。于是，这个构造把被截断的平坦记录变为十四层存在量词的满足，同时没有让任何已选数据逸出命题截断。
<!--ja-->
節の族の証明書を最後の連言項に置いた後は、入れ子になった切り詰めを戻せば十分である。`map₁`{.Agda} の呼び出しが最も外側の切り詰めを与える。その写像が、最も外側の存在量化に必要な証人の対を返すからである。その対の内側にある十三回の明示的な挿入が、台に至るまでの残りの存在量化を順に与える。したがって、切り詰められた平坦な記録から十四重の存在量化の充足が得られるが、選ばれたデータが命題的切り詰めの外へ出ることはない。
<!--/-->

```agda
            , h12 ))))))
          ∣₁ ∣₁ ∣₁ ∣₁ ∣₁ ∣₁ ∣₁ ∣₁ ∣₁ ∣₁ ∣₁ ∣₁ ∣₁ })
```

<!--en-->
The outward reading reverses the journey, and its hypothesis `rd`{.Agda} now
runs the pin the other way: from a satisfaction of the pin at an assembled
environment, it recovers the carrier equation. The input is a satisfaction of
the whole frame, whose fourteen existentials are all truncated, and the
output is the truncated witness record. The proof eliminates the existentials
one level at a time, and every elimination targets the truncation of the
record, a proposition, so each one is legitimate: the lemma never claims to
produce the record itself, only the fact that one exists.
<!--zh-->
向外读式反走这段旅程，其假设 `rd`{.Agda} 这次反向运转 pin：从装配环境中 pin 的一次满足，恢复出载体等式。输入是整条框架的一次满足，其十四层存在量词全被截断；输出是被截断的见证记录。证明逐层消去那些存在量词，而每次消去都以记录的截断、一个命题为目标，故每一次都合法：这条引理从不声称产出记录本身，只声称产出一个记录存在这一事实。
<!--ja-->
外向きの読みはこの旅を逆向きにたどる。仮定 `rd`{.Agda} は、今度は pin を逆方向に回する。組み立てられた環境のもとでの pin の充足から、台の等式を回復するのである。入力は枠組み全体の充足であり、その十四重の存在量化はどれも切り詰められている。出力は切り詰められた証人の記録である。証明は存在量化を一段ずつ除去し、そのどれもが、記録の切り詰めという命題を目指す。したがってそれぞれが正当である。この補題は記録そのものを産み出すとは決して主張せず、一つが存在するという事実だけを主張する。
<!--/-->

```agda
    graphOn-out : ((ν : Fin 10 → S) (E C T b : S)
                    → ⟨ ev ν E C T b γ ⊨ pin ⟩ → fst b ≡ fst W)
                → ⟨ γ ⊨ satGraphOn pin x y ⟩ → ∥ GraphWitOn W x y γ ∥₁
    graphOn-out rd h = rec₁ squash₁ (λ { (n9 , h9) →
      rec₁ squash₁ (λ { (n8 , h8) →
```

<!--en-->
Each application of `rec₁` removes one truncated tag witness while keeping the same propositional target `∥ GraphWitOn W x y γ ∥₁`. The values recovered for slots nine through three may therefore be passed to the next continuation, but none can escape into untruncated data. Repeating this one legitimate elimination is what makes the nested object-language existentials compatible with one flat truncated record.
<!--zh-->
每次应用 `rec₁` 都消去一个被截断的标签见证，同时保持同一个命题目标 `∥ GraphWitOn W x y γ ∥₁`。因此，从九号至三号槽读出的取值可以传给下一层续体，却不能逸出为未截断的数据。正是对这项合法消去的重复使用，使对象语言的嵌套存在量词能够与一份平坦的截断记录对应。
<!--ja-->
`rec₁` を一回適用するたびに、切り詰められたタグの証人を一つ除去し、命題である同じ目標 `∥ GraphWitOn W x y γ ∥₁` を保つ。こうしてスロット九から三までの値を次の継続へ渡せるが、切り詰められていないデータとして外へ出すことはできない。この正当な除去を繰り返すことで、対象言語の入れ子の存在量化を一つの平坦な切り詰められた記録に対応させられる。
<!--/-->

```agda
      rec₁ squash₁ (λ { (n7 , h7) →
      rec₁ squash₁ (λ { (n6 , h6) →
      rec₁ squash₁ (λ { (n5 , h5) →
      rec₁ squash₁ (λ { (n4 , h4) →
      rec₁ squash₁ (λ { (n3 , h3) →
```

<!--en-->
Once all ten tag values have been recovered, the same propositional elimination reaches the candidate tower `E` and key set `C`. The names `hE'` and `hC'` denote the truncated tails that still contain the table, carrier, and certificates; they are not proofs of the tower or closure conditions. Those proofs remain inside the final conjunction and will enter the record only after `T` and `b` have also been exposed within the truncation.
<!--zh-->
读出全部十个标签值以后，同一种命题性消去继续取得候选塔 `E` 与键集 `C`。名字 `hE'` 与 `hC'` 表示仍含有表、载体及各项证书的截断尾部，并不是塔条件或闭包条件的证明。那些证明仍留在最内层合取中，要等 `T` 与 `b` 也在截断内部显露后才会进入记录。
<!--ja-->
十個すべてのタグの値を復元すると、同じ命題への除去によって候補の塔 `E` とキー集合 `C` に到達する。`hE'` と `hC'` は、表、台、各証明をまだ含んでいる切り詰められた残りを表す名前であり、塔や閉性の条件の証明ではない。それらの証明は最後の連言の中に残り、`T` と `b` も切り詰めの内部で現れた後に初めて記録へ入る。
<!--/-->

```agda
      rec₁ squash₁ (λ { (n2 , h2) →
      rec₁ squash₁ (λ { (n1 , h1) →
      rec₁ squash₁ (λ { (n0 , h0) →
      rec₁ squash₁ (λ { (E , hE') →
      rec₁ squash₁ (λ { (C , hC') →
```

<!--en-->
At the innermost level the proof maps rather than eliminates further. What
remains is a truncation whose content is the carrier record, and a map sends
it, component by component, into the truncated flat witness. The tag function
is rebuilt from the ten named slots by a small function defined below the
readings, and `rd`{.Agda}, applied to the rebuilt function, the three
structural witnesses, the carrier and the pin's satisfaction, delivers the
carrier equation that heads the record. Every operation here stays inside
truncations: the map transports the fact that a record exists, and constructs
the corresponding fact on the other side.
<!--zh-->
在最内层，证明作映射而不再继续消去。剩下的是一个以载体记录为内容的截断，一个映射把它逐分量送往被截断的平坦见证。标签函数由十个已命名的位置经一个小函数重建，该函数定义在读式之下；而 `rd`{.Agda} 施于重建的函数、三个结构见证、载体与 pin 的满足，交出领衔记录的载体等式。此处的每个运算都留在截断之内：映射运送「一份记录存在」的事实，并在另一侧构造出对应的事实。
<!--ja-->
最も内側の段で、証明はそれ以上除去するのではなく、写しを行う。残っているのは、台の記録を内容とする切り詰めであり、一つの写しがそれを部品ごとに、切り詰められた平坦な証人へ送る。タグの関数は、名前のついた十の位置から、読みの下で定義された小さな関数によって組み立て直される。そして `rd`{.Agda} を、組み立て直した関数、三つの構造的な証人、台、pin の充足に施せば、記録の冒頭に立つ台の等式が届く。ここでのどの操作も切り詰めの内部にとどまる。写しは、記録が存在するという事実を運び、向こう側で対応する事実を組み立てるのである。
<!--/-->

```agda
      rec₁ squash₁ (λ { (T , hT') →
      map₁ (λ { (b , (hpin , (hnum , (hE , (hc , (hd , (ha , h12))))))) →
        let ν : Fin 10 → S
            ν = ν' n0 n1 n2 n3 n4 n5 n6 n7 n8 n9
        in ν , (E , (C , (T , (b , (rd ν E C T b hpin
```

<!--en-->
The remaining fields are recovered in the directions required by the flat record. The calibration conjunct is read by `nums-out`{.Agda} as the host-level `Tags` family. The tower, closure, and exact-domain satisfactions already have the required types and are retained unchanged. Satisfaction of the query atom is the one field that crosses back to an ordinary membership: transport along `appAt-adequate`{.Agda} turns it into membership of the ordered query pair in the underlying set of `T`.
<!--zh-->
余下字段按平坦记录所需的方向恢复。校准合取项由 `nums-out`{.Agda} 读成宿主层的 `Tags` 等式族；塔、闭包与精确键定义域的满足已经具有所需类型，因而原样保留。查询原子的满足是唯一需要换回寻常隶属关系的字段：沿 `appAt-adequate`{.Agda} 搬运后，便得到查询有序对属于 `T` 的底集。
<!--ja-->
残る欄は、平坦な記録が要求する向きに復元される。校正の連言項は `nums-out`{.Agda} によってホスト層の `Tags` の等式族として読まれる。塔、閉性、正確なキー領域の充足はすでに必要な型をもつので、そのまま保たれる。問い合わせの原子の充足だけは通常の所属へ戻す必要がある。`appAt-adequate`{.Agda} に沿って移送すると、問い合わせの順序対が `T` の基礎集合に属することが得られる。
<!--/-->

```agda
           , ( nums-out ν E C T b γ hnum
           , ( hE
           , ( hc
           , ( hd
           , ( subst ⟨_⟩
```

<!--en-->
Satisfaction of `tableAt`{.Agda} supplies the last certificate of the record. Applying the accumulated continuations then discharges the nested eliminations and yields an element of `∥ GraphWitOn W x y γ ∥₁`. Together, the two readings show that frame satisfaction and the truncated existence of a qualified flat record imply one another. This is a pair of implications between propositions, not a procedure for choosing a canonical table, and it contains no uniqueness claim for table values.
<!--zh-->
`tableAt`{.Agda} 的满足给出记录的最后一份证书。随后依次施用已经积累的续体，便完成各层嵌套消去，并得到 `∥ GraphWitOn W x y γ ∥₁` 的一个元素。两条读法合起来表明，框架的满足与一份合格平坦记录在命题截断下的存在互相蕴含。这只是两个命题之间的一对蕴含，并不是选取典范表的过程，也没有断言表值唯一。
<!--ja-->
`tableAt`{.Agda} の充足が、記録の最後の証明書を与える。蓄積した継続を順に適用すると、入れ子の除去がすべて完了し、`∥ GraphWitOn W x y γ ∥₁` の要素が得られる。二つの読みにより、枠組みの充足と、条件を満たす平坦な記録の命題的に切り詰められた存在とは、互いを含意する。これは二つの命題の間の一対の含意であって、標準的な表を選ぶ手続きではなく、表の値の一意性も主張しない。
<!--/-->

```agda
                 (appAt-adequate Ti (sh14 x) (sh14 y) (ev ν E C T b γ)) ha
             , h12 )))))))))) })
        hT' }) hC' }) hE' }) h0 }) h1 }) h2 }) h3 }) h4 }) h5 }) h6 })
        h7 }) h8 }) h9 }) h
      where
```

<!--en-->
The existential formula presents the ten tags as ten separate bound values, whereas `GraphWitOn`{.Agda} expects one function `Fin 10 → S`. The local function `ν'`{.Agda} reconciles these presentations by case analysis on the constructor index. Its first four branches return `a0` through `a3`; no semantic fact is used here, only the fixed correspondence between indices and the slots already recovered from the formula.
<!--zh-->
存在公式把十个标签呈现为十个彼此分开的绑定值，而 `GraphWitOn`{.Agda} 需要一项函数 `Fin 10 → S`。局部函数 `ν'`{.Agda} 按构造子指标分类，把这两种呈现对齐。前四个分支依次返回 `a0` 至 `a3`；此处不使用任何语义事实，只使用构造子指标与刚从公式中读出的槽之间已经固定的对应。
<!--ja-->
存在論理式では十個のタグが別々の束縛値として現れるが、`GraphWitOn`{.Agda} は一つの関数 `Fin 10 → S` を要求する。局所関数 `ν'`{.Agda} は構成子の添字について場合分けし、この二つの表示を一致させる。最初の四つの分岐は `a0` から `a3` を順に返す。ここで意味論的な事実は使わず、構成子の添字と、論理式から取り出したスロットとの固定された対応だけを用いる。
<!--/-->

```agda
      ν' : S → S → S → S → S → S → S → S → S → S → Fin 10 → S
      ν' a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 zero = a0
      ν' a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 (suc zero) = a1
      ν' a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 (suc (suc zero)) = a2
      ν' a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 (suc (suc (suc zero))) = a3
```

<!--en-->
For constructor indices four through eight, the same case analysis returns the correspondingly named values `a4` through `a8`. Because these branches follow the indexing map `NN`, the equalities extracted by `nums-out` apply to the reconstructed function at precisely the slots where the table and closure clauses expect those tags.
<!--zh-->
对四号至八号构造子指标，同一分类依次返回相应命名的取值 `a4` 至 `a8`。这些分支遵循索引映射 `NN`，所以 `nums-out` 取出的等式恰能在表子句与闭包子句所期待的槽位上应用于重建后的函数。
<!--ja-->
構成子の添字四から八についても、同じ場合分けが対応する値 `a4` から `a8` を返す。これらの分岐は添字写像 `NN` に従うため、`nums-out` が取り出した等式を、表と閉性の節がタグを要求するちょうどそのスロットで、再構成した関数に適用できる。
<!--/-->

```agda
      ν' a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 (suc (suc (suc (suc zero)))) = a4
      ν' a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 (suc (suc (suc (suc (suc zero))))) = a5
      ν' a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 (suc (suc (suc (suc (suc (suc zero)))))) = a6
      ν' a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 (suc (suc (suc (suc (suc (suc (suc zero))))))) = a7
      ν' a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) = a8
```

<!--en-->
The case at index nine exhausts `Fin 10` and makes `ν'`{.Agda} a total function. Thus the fourteen separate object-language witnesses are represented in the host record by exactly one ten-entry tag function together with `E`, `C`, `T`, and `b`. This is only a change of presentation: it creates no new tag and discards none of the existential data.
<!--zh-->
九号指标的情形穷尽 `Fin 10`，使 `ν'`{.Agda} 成为全函数。于是，十四份彼此分开的对象语言见证在宿主记录中恰被表示为一个十项标签函数连同 `E`、`C`、`T` 与 `b`。这只是呈现方式的改变，既不产生新标签，也不丢弃任何存在数据。
<!--ja-->
添字九の場合で `Fin 10` が尽くされ、`ν'`{.Agda} は全域関数になる。したがって、十四個の別々の対象言語の証人は、ホスト側の記録では、一つの十項目のタグ関数と `E`、`C`、`T`、`b` によって正確に表される。これは表示の変更にすぎず、新しいタグを作ることも、存在データを捨てることもない。
<!--/-->

```agda
      ν' a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))) = a9
```
</div>
</details>


<!--en-->
## The carrier supplied by a variable
<!--zh-->
## 由变元提供载体
<!--ja-->
## 変数で与える台
<!--/-->

<!--en-->
The variable-carrier witness type chooses its reference from the ambient environment. In `GraphWitAt B x y γ`, the internal carrier `b` is required to have the same underlying set as `lookup B γ`; the proof does not identify the packaged elements themselves. Because the reference is obtained by lookup, the same witness type remains meaningful when later formulas add binders around the graph and shift the carrier slot accordingly.
<!--zh-->
变元载体的见证类型从周遭环境中取得参照。在 `GraphWitAt B x y γ` 中，内部载体 `b` 只需与 `lookup B γ` 具有相同底集，并不要求两个带证明包装的元素本身相等。由于参照来自环境查找，后续公式即使在图的外面增添绑定并相应平移载体槽，仍可使用同一个见证类型。
<!--ja-->
変数で台を与える証人型は、周囲の環境から参照を選ぶ。`GraphWitAt B x y γ` では、内部の台 `b` の基底集合が `lookup B γ` の基底集合と等しければよく、証明を伴って包装された要素そのものを同一視する必要はない。参照を環境から読み取るため、後の論理式がグラフの外側に束縛を加え、それに応じて台のスロットを移しても、同じ証人型を使える。
<!--/-->

```agda
GraphWitAt : ∀ {n} → Fin n → Fin n → Fin n → S ^ n → Type (ℓ-suc ℓ)
GraphWitAt B x y γ = GraphWitOn (lookup B γ) x y γ
```

<!--en-->
The formula `satGraphAt B x y`{.Agda} implements this reference by using the pin `var Bi ≐ var (sh14 B)`: the newly bound carrier slot is equated with the original carrier slot after that slot has been shifted past all fourteen internal binders. This instance therefore does not insert the carrier as a constant, although the ten standard numeral constants in `numsAt`{.Agda} remain. The formula is opaque so that larger descriptions can use it as one relation; its witness readings provide the public way to establish or consume its satisfaction.
<!--zh-->
公式 `satGraphAt B x y`{.Agda} 用 pin `var Bi ≐ var (sh14 B)` 实现这一参照：新绑定的载体槽与越过全部十四个内部绑定后的原载体槽相等。因此，这个实例不把载体嵌入为常元，不过 `numsAt`{.Agda} 中的十个标准数码常元仍然存在。公式保持不透明，使更大的描述可以把它作为一项完整关系使用；其见证读法则提供公开接口，用来建立或使用该公式的满足。
<!--ja-->
論理式 `satGraphAt B x y`{.Agda} は、pin `var Bi ≐ var (sh14 B)` によってこの参照を実現する。新しく束縛された台のスロットを、十四の内部束縛の先へ移した元の台のスロットと等置するのである。したがって、この版は台を定数として埋め込まないが、`numsAt`{.Agda} にある十個の標準数項の定数は残る。論理式を不透明にすることで、より大きな記述はこれを一つの関係として利用できる。その充足を組み立て、また読み出すための公開インターフェースは、証人についての二つの読みが与える。
<!--/-->

```agda
opaque
  satGraphAt : ∀ {n} → Fin n → Fin n → Fin n → Formula S n
  satGraphAt B x y = satGraphOn (var Bi ≐ var (sh14 B)) x y
```

<!--en-->
The body of `satGraphAt`{.Agda} is unfolded only while its two witness implications are established. Inside this scope the proof may compare the large formula with `GraphWitAt` field by field. Outside it, later mathematics uses the exact statements of `graphAt-in`{.Agda} and `graphAt-out`{.Agda}, so the fourteen binders remain an internal presentation of the same relation.
<!--zh-->
`satGraphAt`{.Agda} 的主体只在建立两条见证蕴含时展开。在这个作用域内，证明可以逐字段比较大型公式与 `GraphWitAt`；离开该作用域后，后续数学只使用 `graphAt-in`{.Agda} 与 `graphAt-out`{.Agda} 的精确陈述，因此十四个绑定始终只是同一关系的内部呈现。
<!--ja-->
`satGraphAt`{.Agda} の本体を展開するのは、証人に関する二つの含意を確立する間だけである。この範囲では、大きな論理式と `GraphWitAt` を欄ごとに比較できる。その外では、後の議論は `graphAt-in`{.Agda} と `graphAt-out`{.Agda} の正確な主張だけを使うため、十四個の束縛は同じ関係の内部的な表示にとどまる。
<!--/-->

```agda
opaque
  unfolding satGraphAt
```

<!--en-->
For the inward reading, the pin hypothesis is the identity: satisfaction of the variable equality is exactly the underlying-set equality already stored in `GraphWitAt`{.Agda}. Hence a truncated witness record at any ambient environment gives satisfaction of `satGraphAt`{.Agda} there. This flexibility is used concretely in `DefAt`{.Agda}, where `DefBody`{.Agda} places the graph below the element slot and two adjacent existentials, and in `DenoteBody`{.Agda}, where the graph reaches the same carrier through five added slots. In both cases the carrier stays in the caller's environment rather than being substituted into the graph as a constant.
<!--zh-->
对内向读法而言，pin 的读法假设就是恒等函数：变元等式的满足，恰是 `GraphWitAt`{.Agda} 中已经保存的底集等式。因此，在任意周遭环境中，一份命题截断下的见证记录都能给出 `satGraphAt`{.Agda} 的满足。`DefAt`{.Agda} 中的 `DefBody`{.Agda} 把图放在元素槽与两个相邻存在量词之下，`DenoteBody`{.Agda} 则让图越过五个新增槽取得同一个载体，这两处都具体使用了这种灵活性。在两种情形中，载体始终留在调用方的环境里，没有作为常元代入图公式。
<!--ja-->
内向きの読みでは、pin の読みの仮定は恒等関数である。変項の等式の充足は、`GraphWitAt`{.Agda} にすでに記録された基底集合の等式そのものだからである。したがって、任意の周囲の環境における命題的に切り詰められた証人の記録から、その環境での `satGraphAt`{.Agda} の充足が得られる。この柔軟性は、`DefAt`{.Agda} の中で `DefBody`{.Agda} が要素のスロットと隣接する二つの存在量化の下にグラフを置く場面と、`DenoteBody`{.Agda} の中でグラフが新たな五つのスロットの先に同じ台を参照する場面で具体的に使われる。どちらでも、台は呼び出し側の環境に残り、定数としてグラフの論理式へ代入されない。
<!--/-->

```agda
  graphAt-in : ∀ {n} (B x y : Fin n) (γ : S ^ n)
             → ∥ GraphWitAt B x y γ ∥₁ → ⟨ γ ⊨ satGraphAt B x y ⟩
  graphAt-in B x y γ =
    graphOn-in (var Bi ≐ var (sh14 B)) (lookup B γ) x y γ (λ _ _ _ _ _ e → e)
```

<!--en-->
The outward reading completes the variable-carrier interface. From a proof of
`satGraphAt B x y`{.Agda}, it recovers, under propositional truncation, the
same candidate data and certificates recorded by `GraphWitAt B x y γ`{.Agda}.
In particular, the internally bound carrier agrees on underlying sets with
the value of the outer slot `B`{.Agda}, while the queried key and value are
still read from the outer slots `x`{.Agda} and `y`{.Agda}. The identity passed
to `graphOn-out`{.Agda} reflects exactly this variable-to-variable pin. A
consumer may eliminate the resulting truncation when proving a proposition,
as the later uniqueness arguments do, but it cannot retain a chosen tower,
closed key set, or table.
<!--zh-->
外向读式补全了变元载体接口。从 `satGraphAt B x y`{.Agda} 的满足证明出发，它在命题截断之下恢复 `GraphWitAt B x y γ`{.Agda} 所记录的同一组候选数据与证书。尤其是，内部绑定的载体在底层集合上与外围槽 `B`{.Agda} 的取值一致，而所查询的键和值仍分别从外围槽 `x`{.Agda} 与 `y`{.Agda} 读取。传给 `graphOn-out`{.Agda} 的恒等函数恰好反映这项变元与变元之间的固定条件。使用者在证明命题时可以消去所得截断，后文的唯一性论证正是如此，但不能从中保留一座选定的塔、一个对子码封闭的键集或一张选定的表。
<!--ja-->
外向きの読みは、変数で与える台のインターフェースを完成させる。`satGraphAt B x y`{.Agda} の充足証明から、`GraphWitAt B x y γ`{.Agda} が記録するのと同じ候補データと証明を、命題的切り詰めのもとで取り出す。特に、内部で束縛された台の基礎集合は外側のスロット `B`{.Agda} の値と一致し、問い合わせるキーと値は引き続き外側のスロット `x`{.Agda} と `y`{.Agda} から読み取られる。`graphOn-out`{.Agda} に渡される恒等関数は、この変数同士を固定する条件をそのまま表している。後の一意性の議論のように、命題を証明するためなら得られた切り詰めを除去できるが、特定の塔、部分符号について閉じたキー集合、あるいは特定の表を選んで保持することはできない。
<!--/-->

```agda
  graphAt-out : ∀ {n} (B x y : Fin n) (γ : S ^ n)
              → ⟨ γ ⊨ satGraphAt B x y ⟩ → ∥ GraphWitAt B x y γ ∥₁
  graphAt-out B x y γ =
    graphOn-out (var Bi ≐ var (sh14 B)) (lookup B γ) x y γ (λ _ _ _ _ _ h → h)
```

<!--en-->
## The carrier fixed as a constant
<!--zh-->
## 把载体固定为常元
<!--ja-->
## 台を定数に固定する
<!--/-->

<!--en-->
When the carrier is already available as an element `B`{.Agda}, the second
instance uses the constant `B`{.Agda} instead of referring to an outer carrier
slot. It has exactly two free positions: `suc zero`{.Agda} is the input key and
`zero`{.Agda} is the proposed output value. The rest of the frame is unchanged,
so the formula still says merely that some locally suitable candidate package
records this query. In particular, `SatisfactionClauses` supplies totality and
domain restriction for the candidate table together with its ten local
equations; neither those clauses nor this instance by itself makes the graph
single-valued.
<!--zh-->
当载体已经作为元素 `B`{.Agda} 给出时，第二个实例不再引用外围载体槽，而是使用常元 `B`{.Agda}。它恰有两个自由位置：`suc zero`{.Agda} 是输入键，`zero`{.Agda} 是候选输出值。框架的其余部分保持不变，所以这条公式仍只表示某组局部合格的候选数据记录了这次查询。具体而言，`SatisfactionClauses` 提供候选表的全定义性、键域限制以及十条局部方程；无论这些子句还是这个实例本身，都没有使该图成为单值关系。
<!--ja-->
台が要素 `B`{.Agda} としてすでに与えられている場合、第二の具体化では外側の台のスロットを参照せず、定数 `B`{.Agda} を用いる。自由な位置はちょうど二つで、`suc zero`{.Agda} が入力のキー、`zero`{.Agda} が候補となる出力値である。枠組みの残りは変わらないため、この論理式が述べるのは、局所的な条件を満たす何らかの候補データがこの問い合わせを記録することだけである。具体的には、`SatisfactionClauses` が候補表の全域性、キー領域の制限、十個の局所方程式を与えるが、それらの節にも、この具体化そのものにも、グラフを一価にする条件はない。
<!--/-->

```agda
opaque
  satGraph : S → Formula S 2
  satGraph B = satGraphOn (var Bi ≐ con B) (suc zero) zero
```

<!--en-->
The witness type makes the direction of this binary relation explicit. In the
environment `y ∷ x ∷ []`{.Agda}, the innermost position contains `y`{.Agda}
and the next contains `x`{.Agda}; hence `GraphWit B x y`{.Agda} says that the
candidate table contains the encoded pair with key `x`{.Agda} and value
`y`{.Agda}. Its reference carrier is the fixed element `B`{.Agda}. The record
also contains calibrated tags, a candidate environment tower, a subcode-closed
candidate key set, a table whose key domain is exactly that set, and the
certificates required by `tableAt`{.Agda}. The key set is only locally closed;
this definition does not identify it with the set of all genuine formula keys.
<!--zh-->
见证类型把这个二元关系的方向写得明确。在环境 `y ∷ x ∷ []`{.Agda} 中，最内层位置容纳 `y`{.Agda}，其次容纳 `x`{.Agda}；因此 `GraphWit B x y`{.Agda} 表示候选表含有以 `x`{.Agda} 为键、以 `y`{.Agda} 为值的编码对。它所参照的载体是固定元素 `B`{.Agda}。记录还包含经过校准的标签、候选环境塔、对子码封闭的候选键集、键定义域恰为该集合的表，以及 `tableAt`{.Agda} 所要求的证书。这里的键集只有局部封闭性；此定义并未把它认同为全部真正公式键组成的集合。
<!--ja-->
証人型は、この二項関係の向きを明示する。環境 `y ∷ x ∷ []`{.Agda} では、最も内側の位置に `y`{.Agda}、その次に `x`{.Agda} が入る。したがって `GraphWit B x y`{.Agda} は、候補表が `x`{.Agda} をキー、`y`{.Agda} を値とする符号化された対を含むことを表す。参照する台は固定された要素 `B`{.Agda} である。この記録にはさらに、校正されたタグ、候補となる環境の塔、部分符号について閉じた候補キー集合、キー領域がちょうどその集合である表、そして `tableAt`{.Agda} が要求する証明が入る。キー集合に仮定されるのは局所的な閉性だけであり、この定義はそれを実際の論理式キーすべてからなる集合と同一視しない。
<!--/-->

```agda
GraphWit : (B x y : S) → Type (ℓ-suc ℓ)
GraphWit B x y = GraphWitOn B (suc zero) zero (y ∷ x ∷ [])
```

<!--en-->
The constant pin admits the same two witness implications, proved by unfolding `satGraph`{.Agda} only in this scope. They turn the large existential formula into a stable binary relation: `graph-in`{.Agda} establishes the relation from a propositionally truncated candidate record, and `graph-out`{.Agda} recovers exactly such a truncation from the relation. This is the form in which `UniformSatisfaction` can use `satGraph B` as the graph parameter of abstract recursion.
<!--zh-->
常元固定条件同样具有两条见证蕴含，只在这个作用域内展开 `satGraph`{.Agda} 来证明。它们把大型存在公式化为一条稳定的二元关系：`graph-in`{.Agda} 从一份经过命题截断的候选记录建立该关系，`graph-out`{.Agda} 则从该关系恢复恰好这样的截断。`UniformSatisfaction` 正以这种形式把 `satGraph B` 用作抽象递归的图参数。
<!--ja-->
定数による固定条件についても、証人に関する同じ二つの含意が成り立ち、この範囲でだけ `satGraph`{.Agda} を展開して証明する。これらの含意は、大きな存在論理式を安定した二項関係として扱えるようにする。`graph-in`{.Agda} は命題的に切り詰められた候補記録から関係を確立し、`graph-out`{.Agda} は関係からまさにその切り詰めを復元する。`UniformSatisfaction` はこの形の `satGraph B` を抽象的再帰のグラフパラメータとして使う。
<!--/-->

```agda
opaque
  unfolding satGraph
```

<!--en-->
The inward reading applies the general conversion with the constant pin. A
record begins with an equality between the underlying sets of its bound
carrier and `B`{.Agda}; satisfaction of the object-language equation
`var Bi ≐ con B`{.Agda} has exactly that content, so the pin reader is the
identity. The remaining fields already certify the tag calibration, tower and
closure conditions, exact key domain, queried table entry, and packaged table
conditions. Mapping this record through `graphOn-in`{.Agda} preserves its
propositional truncation: it proves that a suitable package exists, without
choosing one for later use.
<!--zh-->
内向读式把通用转换用于常元固定条件。一份记录首先给出其中被绑定载体与 `B`{.Agda} 的底层集合相等；对象语言等式 `var Bi ≐ con B`{.Agda} 的满足恰好具有这一内容，所以固定条件的读式就是恒等函数。其余字段已经证明标签校准、塔与封闭条件、恰好的键定义域、所查询的表条目，以及打包后的表条件。通过 `graphOn-in`{.Agda} 映射这份记录时，命题截断始终保留：结论只证明合适的数据存在，并不选定一份供以后使用。
<!--ja-->
内向きの読みは、定数による固定条件に一般の変換を適用する。記録の先頭には、内部で束縛された台と `B`{.Agda} の基礎集合が等しいという証明がある。対象言語の等式 `var Bi ≐ con B`{.Agda} の充足はまさにこの内容をもつので、固定条件を読む関数は恒等関数である。残りの成分はすでに、タグの校正、塔と閉性の条件、正確なキー領域、問い合わせた表要素、そしてまとめられた表の条件を証明している。この記録を `graphOn-in`{.Agda} で写しても命題的切り詰めは保たれる。得られるのは適切なデータが存在するという証明であって、後で使う一組を選ぶことではない。
<!--/-->

```agda
  graph-in : (B x y : S) → ∥ GraphWit B x y ∥₁ → ⟨ (y ∷ x ∷ []) ⊨ satGraph B ⟩
  graph-in B x y =
    graphOn-in (var Bi ≐ con B) B (suc zero) zero (y ∷ x ∷ []) (λ _ _ _ _ _ e → e)
```

<!--en-->
The outward reading reverses this conversion and completes the chapter: a
satisfaction of the binary formula yields only the propositional truncation of
a candidate record with the queried entry. This is the exact limit of the
satisfaction graph formula. `PinnedRecursion` subsequently proves, by
structural recursion on a genuine formula, that if its key lies in the
candidate key set and the candidate table records a value there, then that
value has the same underlying set as the externally defined value
`Sat`{.Agda}. `SatisfactionBridge` separately gives that value its semantics
by relating membership in it to satisfaction in the restricted structure.
Finally, `UniformSatisfaction` uses `satGraph B`{.Agda} on the genuine domain
`AllCodes B`{.Agda}; existence together with the pinned uniqueness there
allows the abstract recursion theorem to assemble one uniform table. The
present two readings supply the represented relation on which those later
arguments operate, but do not themselves choose, prove unique, or semantically
interpret a table.
<!--zh-->
外向读式反转这项转换，并为本章收尾：二元公式的一次满足只给出一份含有所查询条目的候选记录之命题截断。这正是满足关系图公式在本章中的边界。随后，`PinnedRecursion` 对一条真正的公式作结构递归，证明只要它的键属于候选键集，而且候选表在该键处记录了一个值，该值就与外部定义的 `Sat`{.Agda} 取值具有相同底层集合。`SatisfactionBridge` 另行赋予该取值以语义，把其中的隶属关系与限制结构中的满足联系起来。最后，`UniformSatisfaction` 在真正的定义域 `AllCodes B`{.Agda} 上使用 `satGraph B`{.Agda}；该域上的存在性与钉扎所得的唯一性共同满足抽象递归定理的条件，从而组装出一张一致的表。本章的两条读式提供后续论证所使用的表示关系，但自身既不选取表，也不证明表唯一，更不解释表的语义。
<!--ja-->
外向きの読みはこの変換を逆にたどり、本章を締めくくる。二項の論理式の充足から得られるのは、問い合わせた要素を含む候補の記録を命題的に切り詰めたものだけである。これが、この章における充足関係グラフの正確な限界である。続く `PinnedRecursion` は、実際の論理式について構造的再帰を行い、そのキーが候補キー集合に属し、候補表がそこで値を記録しているならば、その値が外部で定義された値 `Sat`{.Agda} と同じ基礎集合をもつことを証明する。`SatisfactionBridge` は別に、その値への所属を制限構造での充足と結びつけ、値に意味論的な内容を与える。最後に `UniformSatisfaction` は、実際の領域 `AllCodes B`{.Agda} 上で `satGraph B`{.Agda} を用いる。その領域での存在と、固定性から得られる一意性を合わせて抽象的再帰定理の仮定を満たし、一つの一様な表を組み立てる。本章の二つの読みは、これらの後続の議論が扱う表現された関係を与えるが、それ自体が表を選んだり、一意性を証明したり、その意味論を説明したりするわけではない。
<!--/-->

```agda
  graph-out : (B x y : S) → ⟨ (y ∷ x ∷ []) ⊨ satGraph B ⟩ → ∥ GraphWit B x y ∥₁
  graph-out B x y =
    graphOn-out (var Bi ≐ con B) B (suc zero) zero (y ∷ x ∷ []) (λ _ _ _ _ _ h → h)
```
