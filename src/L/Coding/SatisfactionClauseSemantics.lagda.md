<!--en-->
The specification `tableAt` combines two domain conditions, `total` and `onC`, with ten constructor clauses. How does one constructor clause become a step in the semantic recursion? This chapter first reads each clause as an exact extensional condition on a candidate value set, then proves the same condition for the recursively constructed set `SatW`. Extensionality can identify the two values once the surrounding argument also supplies the matching code, its subvalues, and a table entry. The local bridges alone do not prove that a whole table is functional or uniquely determined.
<!--zh-->
规格 `tableAt` 把两个定义域条件 `total`、`onC` 与十条构造子子句合在一起。一条构造子子句如何成为语义递归的一步？本章先把每条子句读成候选值集合的精确外延条件，再证明递归构造的集合 `SatW` 满足同一条件。当外围论证另外给出匹配的码、子值与表条目后，外延性便可把两个值同一视。这些局部桥接本身并不证明整张表单值或唯一确定。
<!--ja-->
仕様 `tableAt` は、二つの定義域条件 `total`、`onC` と十個の構成子の節を組み合わせます。一つの構成子の節は、どのように意味論的再帰の一段階になるのでしょうか。本章はまず各節を候補となる値集合の正確な外延条件として読み、次に再帰的に構成した集合 `SatW` も同じ条件を満たすことを示します。周囲の議論からさらに、一致するコード、その部分値、表要素が与えられれば、外延性によって二つの値を同一視できます。局所的な橋渡しだけでは、表全体の単値性や一意性は証明されません。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

```

<!--en-->
The argument takes excluded middle at level `ℓ-suc ℓ` as an explicit parameter. Decoding witnesses will nevertheless remain merely existent when their type has been propositionally truncated; the classical hypothesis does not turn those witnesses into chosen data.
<!--zh-->
论证把层级 `ℓ-suc ℓ` 上的排中律作为显式参数。解码见证的类型经过命题截断后，结论仍只保留其存在性；这个经典假设并不会把见证变成选定的数据。
<!--ja-->
議論はレベル `ℓ-suc ℓ` の排中律を明示的な引数として受け取ります。それでも、復号の証人の型が命題的に切り詰められているとき、結論が述べるのは単なる存在だけです。この古典的仮定が証人を選択済みのデータに変えることはありません。
<!--/-->

```agda
open import Base.Prelude
open import Cubical.Data.Nat using ( znots; snotz )
open import Base.Classical using ( LEM )

```

<!--en-->
All subsequent constructions are relative to the fixed hypothesis `lem`. This keeps the logical cost visible when the local clause readers are later imported into the global soundness and completeness proofs.
<!--zh-->
下文所有构造都相对于固定的假设 `lem` 陈述。这样，局部子句读式随后被用于整体可靠性与完备性证明时，其逻辑代价仍然清楚可见。
<!--ja-->
以下の構成はすべて、固定した仮定 `lem` に相対して述べられます。これにより、局所的な節の読み補題が後で全体の健全性と完全性の証明に使われても、その論理的な費用が明示されたままになります。
<!--/-->

```agda
module L.Coding.SatisfactionClauseSemantics {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

```

<!--en-->
Two languages meet in this proof. The internal formulas describe coded tables inside `L`; the external formulas are interpreted recursively in the structure presented by `W`. The bridge must respect each formula constructor, including bounded quantifiers whose bounds are term values in the current environment.
<!--zh-->
这个证明连接两种语言。内部公式在 `L` 中描述被编码的表，外部公式则在 `W` 所呈现的结构中递归解释。桥接必须逐个保持公式构造子，其中有界量词的界由当前环境中的词项值给出。
<!--ja-->
この証明では二つの言語が出会います。内部の論理式は `L` の中で符号化された表を記述し、外部の論理式は `W` が表示する構造で再帰的に解釈されます。橋渡しはすべての論理式構成子を保たなければならず、有界量化子の境界は現在の環境における項の値によって与えられます。
<!--/-->

```agda
open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using
  ( Formula; Term; var; con; _∈̇_; _∧̇_; _∨̇_; _⇒̇_; ⊤̇; ⊥̇; ∃̇_; ∀̇_; ∃̇∈; ∀̇∈ )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
```

<!--en-->
A finite environment is represented internally by its graph of ordered pairs `(i,v)`. Pair injectivity recovers an index and its value, while `lookup-spec` states that the canonical graph contains exactly the pair belonging to each host-level slot. Membership in `envSet W n` later says, merely, that a set is the graph of some length-`n` assignment into `W`.
<!--zh-->
有限环境在内部由有序对 `(i,v)` 构成的图表示。有序对的单射性可恢复索引及其值，而 `lookup-spec` 说明典范图恰好含有每个宿主层槽位对应的配对。随后，属于 `envSet W n` 只表示某集合是某个长度为 `n`、取值于 `W` 的赋值图。
<!--ja-->
有限環境は内部では順序対 `(i,v)` のグラフとして表されます。順序対の単射性から添字と値を復元でき、`lookup-spec` は正準なグラフが各ホストレベルのスロットに対応する対をちょうど含むことを述べます。後で `envSet W n` に属するという主張から得られるのは、その集合が長さ `n` で `W` に値を取る何らかの割り当てのグラフだという単なる存在です。
<!--/-->

```agda
open import V.Coding {ℓ} using ( pr; pr-inj; #-inj′ )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans )
open import L.Coding.Environment {ℓ} using ( env; lookup-spec )
open import L.Coding.EnvironmentSet {ℓ} lem using ( envSet )
open import L.Coding.Model {ℓ} using ( prAtL; container )
```

<!--en-->
The internal clauses can inspect pair components only through bounded formulas. A `container` supplies one constructible set containing both components, so the pair readers can bind them without an unbounded search. The analogous `consAtL` reader connects the graph of `x ∷ δ` with the graph of `δ`, which is the semantic step needed for quantifiers.
<!--zh-->
内部子句只能借助有界公式检查有序对的分量。`container` 给出一个同时包含两个分量的可构造集合，使配对读式无需无界搜索便能绑定它们。类似地，`consAtL` 读式把 `x ∷ δ` 的图与 `δ` 的图联系起来，这正是处理量词所需的语义步骤。
<!--ja-->
内部の節が順序対の成分を調べるときは、有界論理式だけを使います。`container` は二つの成分をともに含む一つの構成可能集合を与えるので、対の読み補題は非有界な探索なしに成分を束縛できます。同様に `consAtL` の読み補題は `x ∷ δ` のグラフを `δ` のグラフと結び付け、量化子に必要な意味論的な一歩を与えます。
<!--/-->

```agda
open import L.Coding.Expressions {ℓ} using ( sucAtL; consAtL )
import L.Coding.Expressions {ℓ} as CodingExpressions
module E = CodingExpressions.PairExpression
open import L.Axioms.Basic {ℓ} using ( extensionalL )
open import L.Coding.Quantification {ℓ} using
```

<!--en-->
Three kinds of finite index must remain distinct. A natural `n` is a formula arity, `# n` is its set-theoretic numeral inside a code, and `Fin m` selects a slot of a host-level vector of length `m`. The names `i0` through `i19` and the shift `sh` only manage the last of these: when a binder adds a value at the head, every older slot is shifted past it.
<!--zh-->
这里必须区分三种有限索引。自然数 `n` 是公式的元数，`# n` 是码中表示该元数的集合论数码，而 `Fin m` 选择宿主层长度为 `m` 的向量槽位。名称 `i0` 至 `i19` 与移位 `sh` 只管理第三种索引：约束子在向量前端加入一个值时，所有旧槽位都要越过这个新槽位。
<!--ja-->
ここでは三種類の有限添字を区別しなければなりません。自然数 `n` は論理式のアリティ、`# n` はコード内でそのアリティを表す集合論的な数項、`Fin m` は長さ `m` のホストレベルのベクトルのスロットを選びます。`i0` から `i19` までの名前とシフト `sh` が扱うのは最後の種類だけです。束縛子がベクトルの先頭に値を加えるたびに、以前のスロットはその分だけずらされます。
<!--/-->

```agda
  ( i0; i1; i2; i3; i4; i5; i6; i8; i9; i11; i12; i14; i16; i17; i19; sh
  ; pr-out; pr-in; down; sndS; suc-out; suc-in
  ; sndEx; sndAll; bothEx
  ; sndEx-out; sndAll-in; bothEx-out; bothAll-in
  ; fillSnd; fillBoth; useSnd; useBoth )
```

<!--en-->
The common table frame has a fixed nested shape. An environment-tower entry codes `(ar,F)`, a formula key codes `(ar,p)`, its payload codes `(tag,r)`, and a table entry codes `(c,yc)`. The readers below repeatedly peel these pairs so that a constructor relation can speak about the candidate value `yc` over the environment set `F`.
<!--zh-->
共同表框架具有固定的嵌套形状。环境塔条目编码 `(ar,F)`，公式键编码 `(ar,p)`，其载荷又编码 `(tag,r)`，而表条目编码 `(c,yc)`。下文的读式反复拆开这些配对，使构造子关系能够陈述候选值 `yc` 在环境集 `F` 上的外延。
<!--ja-->
共通の表の枠組みには、固定された入れ子の形があります。環境塔の要素は `(ar,F)`、論理式キーは `(ar,p)`、そのペイロードは `(tag,r)`、表の要素は `(c,yc)` を符号化します。以下の読み補題はこれらの対を順にほどき、構成子の関係が環境集合 `F` 上の候補値 `yc` の外延を述べられるようにします。
<!--/-->

```agda
open import L.Coding.CodeDomain {ℓ} using ( Tags )
open import L.Coding.CodeAlphabet {ℓ} using ( module Alphabet )
open import L.Coding.SatisfactionClauses {ℓ}
  using ( extB; fstAll; subAt; subSucAt; tmIs; module Rel; module Clause )

```

<!--en-->
The external environment is a finite vector, but the table stores a set-theoretic graph. Moving between them requires both host-level finite lookup and object-level pair membership. Products and coproducts then record the alternatives exposed by formula and term constructors without conflating those alternatives with the coded sets themselves.
<!--zh-->
外部环境是有限向量，表中保存的却是集合论的图。因此二者之间的转换同时需要宿主层的有限查找与对象层的配对隶属。积与余积记录公式构造子和词项构造子产生的不同情形，但不会把这些情形与被编码的集合混为一谈。
<!--ja-->
外部の環境は有限ベクトルですが、表に保存されるのは集合論的なグラフです。両者を行き来するには、ホストレベルの有限参照と対象レベルの対の所属の双方が必要です。積と直和は論理式や項の構成子から生じる場合を記録しますが、それらの場合を符号化された集合そのものと混同しません。
<!--/-->

```agda
```

<!--en-->
Most semantic comparisons are paths between propositions, obtained from implications in both directions. Propositional truncation is equally essential: pair decompositions and decoded environments may be used inside a proposition, while no global choice of their witnesses is produced.
<!--zh-->
多数语义比较都是命题之间的路径，由两个方向的蕴涵得到。命题截断同样关键：配对分解与解码环境的见证可以在命题内部使用，但证明不会由此产生对这些见证的全局选择。
<!--ja-->
意味論的な比較の多くは、二方向の含意から得られる命題間のパスです。命題的切り詰めも同じく本質的です。対の分解や復号された環境の証人は命題の内部では利用できますが、それらの証人の大域的な選択は得られません。
<!--/-->

```agda
```

<!--en-->
All codes live in the cumulative hierarchy. Ordered-pair codes and the numerals `# n` are therefore actual sets, and their injectivity lets later proofs recover arities, tags, and payloads from equations between codes. The h-set structure of the hierarchy ensures that these recovered equalities are proposition-valued.
<!--zh-->
所有码都生活在累积层级中。因此，有序对码与数码 `# n` 都是真正的集合，而它们的单射性使后文能从码的等式恢复元数、标签与载荷。累积层级的 h-集合结构保证这些恢复出的等式都是命题值。
<!--ja-->
すべてのコードは累積階層の中にあります。したがって順序対のコードと数項 `# n` は実際の集合であり、それらの単射性によって、後の証明はコード間の等式からアリティ、タグ、ペイロードを復元できます。累積階層の h-集合構造により、こうして得られる等式は命題値になります。
<!--/-->

```agda
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_; setIsSet )
open import Cubical.HITs.CumulativeHierarchy.Constructions using ( module InfinitySet )
open InfinitySet {ℓ} using ( #_; sucV )

```

<!--en-->
The internal assignments range over the constructible carrier `S`, but their equations and memberships concern the underlying sets selected by `fst`. Bounded absoluteness supplies the interpretation of internal formulas in this carrier. Every reader therefore ends with a concrete statement about projected sets, ready to be compared with the external recursion.
<!--zh-->
内部赋值取值于可构造载体 `S`，但其中的等式与隶属都是关于 `fst` 投影出的底层集合陈述的。有界绝对性给出内部公式在该载体中的解释。因此，每个读式最终都得到关于投影后集合的具体陈述，可以继续与外部递归比较。
<!--ja-->
内部の割り当ては構成可能な台 `S` に値を取りますが、そこで現れる等式と所属は `fst` で射影した底集合について述べられます。有界絶対性が、この台における内部論理式の解釈を与えます。したがって各読み補題は最後に射影された集合についての具体的な主張を返し、外部の再帰と比較できる形になります。
<!--/-->

```agda
open hPropStructure 𝒮ʟ using ( S )
module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans using ( _^_; _⊨ᵐ_ )
open AbsL using ( _^_ ) renaming ( _⊨ᵐ_ to _⊨_ )
```

<!--en-->
## Reading the shared frame
<!--zh-->
## 读取共同框架
<!--ja-->
## 共通の枠組みを読む
<!--/-->

<!--en-->
The central type records an extensional fact about a set `y`: every member of `y` belongs to `F` and satisfies the property, and conversely every member of `F` satisfying the property belongs to `y`. A value set is described by such a fact rather than by a chosen enumeration.
<!--zh-->
中心类型记录关于集合 `y` 的外延事实：`y` 的每个成员都属于 `F` 且满足该性质；反之，`F` 中满足该性质的每个元素都属于 `y`。值集合由这样的事实描述，而非由选定的枚举描述。
<!--ja-->
中心となる型は、集合 `y` についての外延的な事実を記録します。`y` のすべての要素が `F` に属し性質を満たすこと、また逆に、`F` の中で性質を満たすすべての要素が `y` に属することです。値の集合は、選ばれた列挙ではなく、このような事実によって記述されます。
<!--/-->

```agda
ExtFact : (y F : V ℓ) (P : S → Type (ℓ-suc ℓ)) → Type (ℓ-suc ℓ)
ExtFact y F P = ((z : S) → ⟨ fst z ∈ y ⟩ → ⟨ fst z ∈ F ⟩ × P z)
              × ((z : S) → ⟨ fst z ∈ F ⟩ → P z → ⟨ fst z ∈ y ⟩)

```

<!--en-->
The extensional set builder is read definitionally: satisfaction of the builder is literally the pair of the two membership directions, with the property evaluated in the environment extended by the bound variable.
<!--zh-->
外延集合构造子的读取是定义性的：构造子的满足字面上就是两个隶属方向的二元组，其中性质在由约束变元延拓后的环境中求值。
<!--ja-->
外延的な集合の構成子の読みは定義的です。構成子の充足は文字どおり、二つの所属の方向の対であり、性質は束縛変数で延長された環境のもとで評価されます。
<!--/-->

```agda
module _ {j : ℕ} (y F : Fin j) (φ : Formula S (1 + j)) (δ : S ^ j) where
  extB-out : ⟨ δ ⊨ extB y F φ ⟩ → ExtFact (fst (lookup y δ)) (fst (lookup F δ)) (λ z → ⟨ (z ∷ δ) ⊨ φ ⟩)
  extB-out h = h

```

<!--en-->
Filling is likewise definitional: an extensional fact is exactly satisfaction of the builder.
<!--zh-->
填充同样是定义性的：外延事实恰是构造子的满足。
<!--ja-->
埋めも同じく定義的です。外延的な事実は、構成子の充足にほかなりません。
<!--/-->

```agda
  extB-in : ExtFact (fst (lookup y δ)) (fst (lookup F δ)) (λ z → ⟨ (z ∷ δ) ⊨ φ ⟩) → ⟨ δ ⊨ extB y F φ ⟩
  extB-in h = h
```

<!--en-->
Suppose `y` and `y'` satisfy the same extension condition over `F`: among the elements of `F`, membership in either set is characterized by the property `P`. Extensionality reduces equality of their underlying sets to two membership conversions. In the first direction, a member of `y` passes through the outward half of its extension fact and then through the inward half for `y'`.
<!--zh-->
假定 `y` 与 `y'` 在 `F` 上满足同一个外延条件：对 `F` 中的元素而言，属于任一集合都由性质 `P` 刻画。外延性把二者底层集合的相等化为两个隶属转换。正向转换先用 `y` 的外延事实向外读出成员满足的条件，再用 `y'` 的外延事实向内得到该成员属于 `y'`。
<!--ja-->
`y` と `y'` が `F` 上で同じ外延条件を満たすと仮定します。すなわち、`F` の要素については、どちらの集合への所属も性質 `P` によって特徴付けられます。外延性により、底集合の等しさは二方向の所属の変換へ帰着します。順方向では、`y` の要素をその外延条件の外向きの半分で読み、続いて `y'` の外延条件の内向きの半分を適用します。
<!--/-->

```agda
ext-unique : (y y' F : S) (P : S → Type (ℓ-suc ℓ))
           → ExtFact (fst y) (fst F) P → ExtFact (fst y') (fst F) P → fst y ≡ fst y'
ext-unique y y' F P (o1 , i1') (o2 , i2') =
  cong fst (extensionalL {a = y} {b = y'} (λ z → ⇔toPath
    (λ hz → i2' z (o1 z hz .fst) (o1 z hz .snd))
```

<!--en-->
The backward conversion closes the biconditional: a member of the right-hand side is first recognized as a member of `F` satisfying the property, and the second half of the extensional fact then returns its membership in `y`. Composing the two conversions gives the equality of the underlying sets of `y` and `y'`; what is identified is the underlying set, not any chosen coding evidence.
<!--zh-->
反向转换补全该双条件：右侧的成员先被认作 `F` 中满足该性质的元素，外延事实的另一半随即返回它在 `y` 中的隶属。两个转换复合起来，就得到 `y` 与 `y'` 的底层集合相等；被同一视的是底层集合，而不是任何选定的编码证据。
<!--ja-->
逆方向の変換が同値を閉じます。右側の要素は、まず `F` に属し性質を満たす要素として認められ、外延的な事実のもう半分が、`y` の中での所属を返します。二つの変換を合成すれば、`y` と `y'` の底の集合の等しさが得られます。同一視されるのは底の集合であり、選ばれた符号化の証拠ではありません。
<!--/-->

```agda
    (λ hz → i1' z (o2 z hz .fst) (o2 z hz .snd))))
```

<!--en-->
To use a subformula value, fix a table slot `T`, an arity slot `ar`, a payload slot `a`, and a body that expects four new entries. The reader will expose a matching table pair `(c₁,ya)` and place, in front of the old environment, the value `ya`, its key `c₁`, a container for the pair components, and a constructible representative of the table entry itself.
<!--zh-->
要使用子公式的值，先固定表槽 `T`、元数槽 `ar`、载荷槽 `a`，以及需要四个新条目的主体。读式会揭示一条匹配的表对 `(c₁,ya)`，并在旧环境前依次放入值 `ya`、键 `c₁`、容纳配对分量的集合，以及表条目本身的可构造代表。
<!--ja-->
部分論理式の値を使うため、表のスロット `T`、アリティのスロット `ar`、ペイロードのスロット `a`、そして四つの新しい要素を期待する本体を固定します。読み補題は一致する表の対 `(c₁,ya)` を取り出し、古い環境の前に、値 `ya`、キー `c₁`、対の成分を収める集合、表の要素そのものの構成可能な表示をこの順に置きます。
<!--/-->

```agda
module _ {j : ℕ} (T ar a : Fin j) (body : Formula S (4 + j)) (δ : S ^ j) where
  private
    Tv = fst (lookup T δ)
    TS = lookup T δ
    A = fst (lookup ar δ)
```

<!--en-->
Write `A` for the projected arity and `Av` for the projected payload. The matching condition for the subkey is then the single equation `fst c₁ ≡ pr A Av`, which keeps the coded key separate from the host-level slots that supplied its two components.
<!--zh-->
记投影后的元数为 `A`，投影后的载荷为 `Av`。子键的匹配条件便是等式 `fst c₁ ≡ pr A Av`；这个写法清楚地区分了集合论编码的键与提供其两个分量的宿主层槽位。
<!--ja-->
射影されたアリティを `A`、射影されたペイロードを `Av` と書きます。部分キーの一致条件は一つの等式 `fst c₁ ≡ pr A Av` となり、集合論的に符号化されたキーと、その二成分を与えたホストレベルのスロットとが区別されます。
<!--/-->

```agda
    Av = fst (lookup a δ)

```

<!--en-->
If `subAt` holds, every table entry whose underlying pair is `(c₁,ya)` and whose key satisfies `c₁=(A,Av)` yields the body. The body is evaluated at `ya ∷ c₁ ∷ s ∷ e' ∷ δ`, where `e'` represents that table entry and `s` is only a container exposing the two pair components. Neither auxiliary object is an additional semantic value.
<!--zh-->
若 `subAt` 成立，则每条底层配对为 `(c₁,ya)` 且键满足 `c₁=(A,Av)` 的表条目都会推出主体。主体在 `ya ∷ c₁ ∷ s ∷ e' ∷ δ` 处求值，其中 `e'` 表示该表条目，`s` 只是用于暴露两个配对分量的容纳集合。二者都不是额外的语义值。
<!--ja-->
`subAt` が成り立つなら、底の対が `(c₁,ya)` であり、キーが `c₁=(A,Av)` を満たすすべての表要素から本体が従います。本体は `ya ∷ c₁ ∷ s ∷ e' ∷ δ` で評価されます。ここで `e'` はその表要素を表し、`s` は対の二成分を取り出すためだけの容器です。どちらも追加の意味論的な値ではありません。
<!--/-->

```agda
  subAt-out : ⟨ δ ⊨ subAt T ar a body ⟩ → (c₁ ya : S) (m : ⟨ pr (fst c₁) (fst ya) ∈ Tv ⟩)
            → fst c₁ ≡ pr A Av
            → ⟨ (ya ∷ c₁ ∷ container (down TS (pr (fst c₁) (fst ya)) m) c₁ ya refl .fst
                 ∷ down TS (pr (fst c₁) (fst ya)) m ∷ δ) ⊨ body ⟩
  subAt-out h c₁ ya m e =
```

<!--en-->
The proof first applies the table-bounded universal to the concrete representative `e'` of `(c₁,ya)`. The pair reader then supplies the two components `c₁` and `ya`; finally `pr-in` turns the equation `c₁=(A,Av)` into the antecedent required by the internal implication. What remains is exactly the requested body at the four-slot extension.
<!--zh-->
证明先把表上的有界全称用于 `(c₁,ya)` 的具体代表 `e'`。随后，配对读式给出两个分量 `c₁` 与 `ya`；最后，`pr-in` 把等式 `c₁=(A,Av)` 转成内部蕴涵所需的前件。余下的正是四槽扩展环境处的主体。
<!--ja-->
証明はまず、表上の有界全称を `(c₁,ya)` の具体的な表示 `e'` に適用します。次に対の読み補題が二成分 `c₁` と `ya` を与え、最後に `pr-in` が等式 `c₁=(A,Av)` を内部の含意が要求する前件へ変換します。残るのは四スロット拡張での本体そのものです。
<!--/-->

```agda
    useBoth i0 (down TS (pr (fst c₁) (fst ya)) m ∷ δ) c₁ ya refl (prAtL i1 (sh 4 ar) (sh 4 a) ⇒̇ body)
      (h (down TS (pr (fst c₁) (fst ya)) m) m)
      (pr-in i1 (sh 4 ar) (sh 4 a)
        (ya ∷ c₁ ∷ container (down TS (pr (fst c₁) (fst ya)) m) c₁ ya refl .fst
           ∷ down TS (pr (fst c₁) (fst ya)) m ∷ δ) e)
```

<!--en-->
Filling is the converse: given a proof of the body for every matching table entry with its own container, the bounded universal over table entries holds. Note what this reader does not do: it does not select one entry, and it does not assert that the value `ya` is unique; it quantifies over all matching entries.
<!--zh-->
填充是其反向：若对每个匹配的表条目连同其容器都能证明主体，则表条目上的有界全称成立。注意该读取器不做的事：它不选定某个条目，也不断言值 `ya` 唯一；它是对所有匹配条目量化。
<!--ja-->
埋めはその逆です。一致するすべての表の項目とその容器について本体が証明できれば、表の項目の上の有界全称が成立します。この読み手がしないことに注意してください。項目を一つ選ぶことも、値 `ya` が一意だと主張することもなく、一致するすべての項目の上で量化するだけです。
<!--/-->

```agda

  subAt-in : ((c₁ ya s e' : S) → ⟨ fst e' ∈ Tv ⟩ → fst e' ≡ pr (fst c₁) (fst ya) → fst c₁ ≡ pr A Av
              → ⟨ (ya ∷ c₁ ∷ s ∷ e' ∷ δ) ⊨ body ⟩)
           → ⟨ δ ⊨ subAt T ar a body ⟩
  subAt-in g e' e'∈ = bothAll-in i0 (prAtL i1 (sh 4 ar) (sh 4 a) ⇒̇ body) (e' ∷ δ)
    (λ c₁ ya s s∈ c₁∈ ya∈ e hp → g c₁ ya s e' e'∈ e (pr-out i1 (sh 4 ar) (sh 4 a) (ya ∷ c₁ ∷ s ∷ e' ∷ δ) hp))
```

<!--en-->
The second subclause reader is stated for the raised-arity shape: its body is extended by six slots, because the subformula of a quantified formula is read at the raised arity.
<!--zh-->
第二条子子句读取针对抬升元数的形状陈述：其主体延拓六个槽位，因为量化公式的子公式要在抬升后的元数处读取。
<!--ja-->
第二の部分節の読みは、アリティが上がった形に対して述べられます。その本体は六つの枠を延長します。量化された論理式の部分論理式は、上げられたアリティで読まれるからです。
<!--/-->

```agda

module _ {j : ℕ} (T ar a : Fin j) (body : Formula S (6 + j)) (δ : S ^ j) where
  private
    Tv = fst (lookup T δ)
    TS = lookup T δ
    A = fst (lookup ar δ)
```

<!--en-->
The arity value of the outer formula is named, and the raised one is recovered separately inside the proof.
<!--zh-->
外层公式的元数值被命名，抬升后的元数则在证明内部单独恢复。
<!--ja-->
外側の論理式のアリティの値が名付けられ、上げられたアリティは証明の内部で別に復元されます。
<!--/-->

```agda
    Av = fst (lookup a δ)

```

<!--en-->
The raised reader uses a table entry at a key `(ar',Av)` together with the equation `fst ar' ≡ sucV A`. Its body is evaluated at `ar' ∷ s' ∷ ya ∷ c₁ ∷ s ∷ e' ∷ δ`: the two containers `s'` and `s` merely make the components of the raised key and the table entry available to bounded formulas.
<!--zh-->
抬升读式使用键为 `(ar',Av)` 的表条目，并要求等式 `fst ar' ≡ sucV A`。主体在 `ar' ∷ s' ∷ ya ∷ c₁ ∷ s ∷ e' ∷ δ` 处求值；两个容纳集合 `s'` 与 `s` 只是让有界公式能够取得抬升键和表条目的分量。
<!--ja-->
持ち上げられた読み補題は、キーが `(ar',Av)` である表要素と、等式 `fst ar' ≡ sucV A` を使います。本体は `ar' ∷ s' ∷ ya ∷ c₁ ∷ s ∷ e' ∷ δ` で評価されます。二つの容器 `s'` と `s` は、有界論理式から持ち上げられたキーと表要素の成分を利用できるようにするだけです。
<!--/-->

```agda
  subSucAt-out : ⟨ δ ⊨ subSucAt T ar a body ⟩ → (c₁ ya ar' : S) (m : ⟨ pr (fst c₁) (fst ya) ∈ Tv ⟩)
               → (e : fst c₁ ≡ pr (fst ar') Av) → fst ar' ≡ sucV A
               → ⟨ (ar' ∷ container c₁ ar' (lookup a δ) e .fst ∷ ya ∷ c₁
                    ∷ container (down TS (pr (fst c₁) (fst ya)) m) c₁ ya refl .fst
                    ∷ down TS (pr (fst c₁) (fst ya)) m ∷ δ) ⊨ body ⟩
```

<!--en-->
Starting from the given table entry, the proof first obtains the four-slot statement `h4` by decomposing `(c₁,ya)`. It then supplies the candidate first component `ar'` to `fstAll`, proves `c₁=(ar',Av)` with `pr-in`, and proves `ar'=suc A` with `suc-in`. These two equations are precisely the guards needed before the body may be used.
<!--zh-->
证明从给定表条目出发，先分解 `(c₁,ya)` 得到四槽陈述 `h4`。随后向 `fstAll` 提供候选第一分量 `ar'`，用 `pr-in` 证明 `c₁=(ar',Av)`，再用 `suc-in` 证明 `ar'=suc A`。主体可用之前所需的守卫恰好就是这两个等式。
<!--ja-->
証明は与えられた表要素から出発し、まず `(c₁,ya)` を分解して四スロットの主張 `h4` を得ます。次に `fstAll` へ第一成分の候補 `ar'` を与え、`pr-in` で `c₁=(ar',Av)` を、`suc-in` で `ar'=suc A` を証明します。本体を使う前に必要な条件は、まさにこの二つの等式です。
<!--/-->

```agda
  subSucAt-out h c₁ ya ar' m e es =
    (h4 (container c₁ ar' (lookup a δ) e .fst) (container c₁ ar' (lookup a δ) e .snd .fst)
        ar' (container c₁ ar' (lookup a δ) e .snd .snd .fst)
        (pr-in (sh 2 i1) i0 (sh 2 (sh 4 a)) δ6 e))
      (suc-in (sh 6 ar) i0 δ6 es)
```

<!--en-->
The local name `e'S` is a constructible representative of the particular table entry `(c₁,ya)`, obtained from its membership in `T`. The environment `δ4` then places `ya`, `c₁`, a container for their pair, and `e'S` before `δ`; it does not contain a presentation of the whole table.
<!--zh-->
局部名称 `e'S` 是特定表条目 `(c₁,ya)` 的可构造代表，由该配对属于 `T` 得到。环境 `δ4` 随后在 `δ` 前依次放入 `ya`、`c₁`、容纳其配对分量的集合与 `e'S`；其中并没有整张表的呈现。
<!--ja-->
局所名 `e'S` は、特定の表要素 `(c₁,ya)` の構成可能な表示であり、その対が `T` に属することから得られます。環境 `δ4` は `δ` の前に `ya`、`c₁`、その対の成分を収める容器、`e'S` をこの順に置きます。表全体の表示が入っているわけではありません。
<!--/-->

```agda
    where
    e'S = down TS (pr (fst c₁) (fst ya)) m
    δ4 : S ^ (4 + j)
    δ4 = ya ∷ c₁ ∷ container e'S c₁ ya refl .fst ∷ e'S ∷ δ
    δ6 : S ^ (6 + j)
```

<!--en-->
Applying `useBoth` to the chosen table entry removes the outer table quantifier and the pair decomposition in one step. The result `h4` is the remaining `fstAll` statement at `δ4`; it still requires a candidate first component of `c₁` and the equations identifying that component with the successor arity.
<!--zh-->
把 `useBoth` 用于选定的表条目，会一步消去表上的外层量化与配对分解。所得 `h4` 是 `δ4` 处余下的 `fstAll` 陈述；它仍需取得 `c₁` 的候选第一分量，并验证该分量就是后继元数。
<!--ja-->
選んだ表要素に `useBoth` を適用すると、表上の外側の量化と対の分解が一度に除かれます。得られる `h4` は `δ4` における残りの `fstAll` の主張です。そこではなお `c₁` の第一成分の候補を与え、その成分が後続アリティであることを示す必要があります。
<!--/-->

```agda
    δ6 = ar' ∷ container c₁ ar' (lookup a δ) e .fst ∷ δ4
    h4 : ⟨ δ4 ⊨ fstAll i1 (sh 4 a) (sucAtL (sh 6 ar) i0 ⇒̇ body) ⟩
    h4 = useBoth i0 (e'S ∷ δ) c₁ ya refl (fstAll i1 (sh 4 a) (sucAtL (sh 6 ar) i0 ⇒̇ body)) (h e'S m)

```

<!--en-->
For the converse direction, it is enough to prove the body uniformly for every possible table-entry decomposition and every possible first-component decomposition of its key. The two equations in the hypothesis ensure that only entries at `(suc A,Av)` matter; no particular entry or raised arity is selected globally.
<!--zh-->
反向证明只需对每一种可能的表条目分解以及其键的每一种可能第一分量分解，一致地证明主体。前提中的两个等式保证只有键为 `(suc A,Av)` 的条目相关；证明不会全局选定某个表条目或抬升元数。
<!--ja-->
逆方向では、表要素のあらゆる分解と、そのキーの第一成分のあらゆる分解について、一様に本体を証明すれば十分です。仮定中の二つの等式により、キーが `(suc A,Av)` である要素だけが関係します。特定の表要素や持ち上げられたアリティを大域的に選ぶことはありません。
<!--/-->

```agda
  subSucAt-in : ((c₁ ya ar' s s' e' : S) → ⟨ fst e' ∈ Tv ⟩ → fst e' ≡ pr (fst c₁) (fst ya)
                 → fst c₁ ≡ pr (fst ar') Av → fst ar' ≡ sucV A
                 → ⟨ (ar' ∷ s' ∷ ya ∷ c₁ ∷ s ∷ e' ∷ δ) ⊨ body ⟩)
              → ⟨ δ ⊨ subSucAt T ar a body ⟩
  subSucAt-in g e' e'∈ = bothAll-in i0 (fstAll i1 (sh 4 a) (sucAtL (sh 6 ar) i0 ⇒̇ body)) (e' ∷ δ)
```

<!--en-->
The introduction proof receives the components exposed by the two universal pair readers. It uses `pr-out` to recover the equation `c₁=(ar',Av)` and `suc-out` to recover `ar'=suc A`, then passes those equations, the table memberships, and the six-slot environment to the uniform hypothesis `g`.
<!--zh-->
引入证明接收两层全称配对读式暴露出的分量。它用 `pr-out` 恢复等式 `c₁=(ar',Av)`，用 `suc-out` 恢复 `ar'=suc A`，再把这些等式、表隶属事实与六槽环境交给一致前提 `g`。
<!--ja-->
導入の証明は、二段の全称的な対の読みから現れる成分を受け取ります。`pr-out` で等式 `c₁=(ar',Av)` を、`suc-out` で `ar'=suc A` を復元し、それらの等式、表への所属、六スロットの環境を一様な仮定 `g` に渡します。
<!--/-->

```agda
    (λ c₁ ya s s∈ c₁∈ ya∈ e s' s'∈ ar' ar'∈ hp hs →
      g c₁ ya ar' s s' e' e'∈ e
        (pr-out (sh 2 i1) i0 (sh 2 (sh 4 a)) (ar' ∷ s' ∷ ya ∷ c₁ ∷ s ∷ e' ∷ δ) hp)
        (suc-out (sh 6 ar) i0 (ar' ∷ s' ∷ ya ∷ c₁ ∷ s ∷ e' ∷ δ) hs))
```

<!--en-->
`TmIsV t z v` records the two possible term-code shapes, under propositional truncation. Either `t=(#0,v)`, the constant case, or there merely exists an index `i` with `t=(#1,i)` and the graph entry `(i,v)` belonging to `z`, the variable case. For an arbitrary relation `z`, this statement contains no functionality or uniqueness claim.
<!--zh-->
`TmIsV t z v` 在命题截断下记录词项码的两种可能形状。常元情形为 `t=(#0,v)`；变元情形则只说存在索引 `i`，使 `t=(#1,i)` 且图条目 `(i,v)` 属于 `z`。对于任意关系 `z`，这个陈述不包含单值性或唯一性结论。
<!--ja-->
`TmIsV t z v` は、命題的切り詰めの下で項コードの二つの形を記録します。定数の場合は `t=(#0,v)` です。変数の場合は、`t=(#1,i)` かつグラフ要素 `(i,v)` が `z` に属する添字 `i` が単に存在します。任意の関係 `z` に対するこの主張には、単値性も一意性も含まれません。
<!--/-->

```agda
TmIsV : V ℓ → V ℓ → V ℓ → Type (ℓ-suc ℓ)
TmIsV t z v = ∥ (t ≡ pr (# 0) v) ⊎ (Σ[ i ∈ V ℓ ] ((t ≡ pr (# 1) i) × ⟨ pr i v ∈ z ⟩)) ∥₁

```

<!--en-->
The local reader is parameterized by five host-level slots: the term code, the environment graph, its proposed value, and the two tag numerals. The hypotheses `q0` and `q1` identify the last two slots with `#0` and `#1`; the local names `Tv` and `Z` project the term code and graph to the hierarchy where the coding equations live.
<!--zh-->
局部读式由五个宿主层槽位参数化：词项码、环境图、候选值以及两个标签数码。前提 `q0` 与 `q1` 把最后两个槽分别认同为 `#0` 与 `#1`；局部名称 `Tv` 与 `Z` 则把词项码和图投影到编码等式所在的累积层级。
<!--ja-->
局所的な読み補題は、項コード、環境グラフ、候補値、二つのタグ数項という五つのホストレベルのスロットでパラメータ化されます。仮定 `q0` と `q1` は最後の二スロットを `#0` と `#1` に同一視し、局所名 `Tv` と `Z` は項コードとグラフを、符号化の等式が置かれる累積階層へ射影します。
<!--/-->

```agda
module _ {j : ℕ} (t z v N0 N1 : Fin j) (δ : S ^ j)
  (q0 : fst (lookup N0 δ) ≡ # 0) (q1 : fst (lookup N1 δ) ≡ # 1) where
  private
    Tv = fst (lookup t δ)
    Z = fst (lookup z δ)
```

<!--en-->
The remaining projections name the proposed value `Vv` and the actual set stored in the tag-one slot, `N1v`. The proof must carry equations through `q1` because the internal formula refers to `N1v`, whereas `TmIsV` states its variable branch with the canonical numeral `#1`.
<!--zh-->
其余两个投影分别命名候选值 `Vv` 与标签一槽中实际存放的集合 `N1v`。内部公式引用的是 `N1v`，而 `TmIsV` 的变元分支使用典范数码 `#1`，所以证明必须沿 `q1` 搬运等式。
<!--ja-->
残る二つの射影は、候補値 `Vv` とタグ一のスロットに実際に入っている集合 `N1v` を名付けます。内部論理式は `N1v` を参照しますが、`TmIsV` の変数の場合は正準な数項 `#1` を使うため、証明は `q1` に沿って等式を輸送しなければなりません。
<!--/-->

```agda
    Vv = fst (lookup v δ)
    N1v = fst (lookup N1 δ)

```

<!--en-->
The inner bounded existential ranges over entries `q` of the graph `z`, not over indices themselves. Its pair atom asserts `q=(i,v)`, where the index `i` was already recovered as the second component of the term code. Thus the internal formula says that the graph contains the entry pairing that fixed index with the proposed value.
<!--zh-->
内层有界存在遍历的是图 `z` 的条目 `q`，并非索引本身。其配对原子断言 `q=(i,v)`，其中索引 `i` 已经作为词项码的第二分量被恢复。因此，内部公式表示图中含有把这个固定索引与候选值配对的条目。
<!--ja-->
内側の有界存在が動くのはグラフ `z` の要素 `q` であり、添字そのものではありません。その対のアトムは `q=(i,v)` を主張し、添字 `i` はすでに項コードの第二成分として復元されています。したがって内部論理式は、その固定した添字と候補値を組にした要素がグラフに含まれることを述べます。
<!--/-->

```agda
    inner : Formula S (2 + j)
    inner = ∃̇∈ (var (sh 2 z)) (prAtL i0 i1 (sh 3 v))

```

<!--en-->
`Inner i s` repackages the semantics of that bounded existential. It merely supplies a graph entry `q`, a proof that `q∈Z`, and satisfaction of the atom saying `q=(i,Vv)` at `q ∷ i ∷ s ∷ δ`. The slot `s` is the container used to expose the components of the term code.
<!--zh-->
`Inner i s` 重新包装这个有界存在的语义。它只给出一个图条目 `q`、证明 `q∈Z`，以及配对原子 `q=(i,Vv)` 在 `q ∷ i ∷ s ∷ δ` 处成立的证据。槽位 `s` 是用于暴露词项码分量的容纳集合。
<!--ja-->
`Inner i s` は、この有界存在の意味を詰め直します。そこから得られるのは、グラフ要素 `q`、`q∈Z` の証明、そして `q ∷ i ∷ s ∷ δ` において対のアトム `q=(i,Vv)` が成り立つ証明だけです。スロット `s` は項コードの成分を取り出すための容器です。
<!--/-->

```agda
    Inner : (i s : S) → Type (ℓ-suc ℓ)
    Inner i s = ∥ Σ[ q ∈ S ] (⟨ fst q ∈ Z ⟩ × ⟨ (q ∷ i ∷ s ∷ δ) ⊨ prAtL i0 i1 (sh 3 v) ⟩) ∥₁

```

<!--en-->
`Outer` packages the whole variable branch read from `sndEx`: there merely exist a payload representative `i` and a container `s` such that `Tv=pr N1v (fst i)` and the inner bounded existential holds at `i ∷ s ∷ δ`. The equation identifies the term code with the tag-one pair; it does not identify `i` with the tag.
<!--zh-->
`Outer` 包装从 `sndEx` 读出的整个变元分支：只存在一个载荷代表 `i` 与一个容纳集合 `s`，使 `Tv=pr N1v (fst i)`，并且内层有界存在在 `i ∷ s ∷ δ` 处成立。这个等式把词项码认同为标签一配对，并没有把 `i` 与标签本身同一视。
<!--ja-->
`Outer` は `sndEx` から読み出した変数の場合の全体をまとめます。ペイロードの表示 `i` と容器 `s` が単に存在し、`Tv=pr N1v (fst i)` が成り立ち、内側の有界存在が `i ∷ s ∷ δ` で成り立ちます。この等式が項コードと同一視するのはタグ一の対であり、`i` とタグそのものではありません。
<!--/-->

```agda
    Outer : Type (ℓ-suc ℓ)
    Outer = ∥ Σ[ i ∈ S ] Σ[ s ∈ S ] ((Tv ≡ pr N1v (fst i)) × ⟨ (i ∷ s ∷ δ) ⊨ inner ⟩) ∥₁

```

<!--en-->
From an inner witness `q`, `pr-out` gives `fst q=pr (fst i) Vv`; transporting the known membership `q∈Z` along this equation yields the required graph membership of `(i,Vv)`. In parallel, `q1` changes the outer equation from the actual tag slot `N1v` to `#1`. These are exactly the two fields of the variable branch of `TmIsV`.
<!--zh-->
从内层见证 `q` 出发，`pr-out` 给出 `fst q=pr (fst i) Vv`；沿该等式搬运已知的隶属 `q∈Z`，便得到所需的图条目 `(i,Vv)` 属于 `Z`。与此同时，`q1` 把外层等式中的实际标签槽 `N1v` 改写为 `#1`。这两部分恰好组成 `TmIsV` 的变元分支。
<!--ja-->
内側の証人 `q` から `pr-out` により `fst q=pr (fst i) Vv` が得られ、既知の所属 `q∈Z` をこの等式に沿って輸送すると、必要なグラフ要素 `(i,Vv)` の所属が得られます。同時に `q1` は、外側の等式に現れる実際のタグスロット `N1v` を `#1` に書き換えます。この二つが `TmIsV` の変数の場合の二つの成分そのものです。
<!--/-->

```agda
    viaQ : (i s : S) → Tv ≡ pr N1v (fst i) → Inner i s → TmIsV Tv Z Vv
    viaQ i s e = map₁
      (λ { (q , (q∈ , hp)) → inr (fst i , ( e ∙ cong (λ a → pr a (fst i)) q1
         , subst (λ u → ⟨ u ∈ Z ⟩) (pr-out i0 i1 (sh 3 v) (q ∷ i ∷ s ∷ δ) hp) q∈ )) })

```

<!--en-->
`viaI` eliminates the merely existing outer decomposition into `TmIsV`. This elimination is allowed because `TmIsV` is itself propositionally truncated, so the construction transforms each local pair decomposition without choosing one decomposition for later use.
<!--zh-->
`viaI` 把只保留存在性的外层分解消去到 `TmIsV`。由于 `TmIsV` 本身也经过命题截断，这种消去只会逐个转换局部配对分解，不会选出一个分解供后文使用。
<!--ja-->
`viaI` は、単に存在する外側の分解を `TmIsV` へ消去します。`TmIsV` 自身も命題的に切り詰められているため、この消去は各局所的な対の分解を変換するだけで、後で使う一つの分解を選び出すことはありません。
<!--/-->

```agda
    viaI : Outer → TmIsV Tv Z Vv
    viaI = rec₁ squash₁ (λ { (i , s , (e , hq)) → viaQ i s e hq })

```

<!--en-->
The object formula `tmIs` is a disjunction of two code shapes. In the constant branch, `pr-out` reads `Tv=pr(q0,Vv)` and the equation `q0=#0` converts it to the first branch of `TmIsV`. In the variable branch, `sndEx-out` produces `Outer`, which `viaI` converts to the graph-membership branch.
<!--zh-->
对象公式 `tmIs` 是两种码形状的析取。在常元分支中，`pr-out` 读出 `Tv=pr(q0,Vv)`，再由 `q0=#0` 把它化为 `TmIsV` 的第一分支。在变元分支中，`sndEx-out` 产生 `Outer`，随后由 `viaI` 转成图隶属分支。
<!--ja-->
対象論理式 `tmIs` は二つのコード形の選言です。定数の場合、`pr-out` が `Tv=pr(q0,Vv)` を読み出し、`q0=#0` によってそれを `TmIsV` の第一の場合へ変換します。変数の場合、`sndEx-out` が `Outer` を生成し、`viaI` がそれをグラフ所属の場合へ変換します。
<!--/-->

```agda
    cases : ⟨ δ ⊨ prAtL t N0 v ⟩ ⊎ ⟨ δ ⊨ sndEx t N1 inner ⟩ → TmIsV Tv Z Vv
    cases (inl h) = ∣ inl (pr-out t N0 v δ h ∙ cong (λ a → pr a Vv) q0) ∣₁
    cases (inr h) = viaI (sndEx-out t N1 inner δ h)

```

<!--en-->
The public elimination `tmIs-out` performs that case analysis under the outer disjunction's propositional truncation. Its conclusion concerns one proposed value `Vv`; it does not show that two proposed values agree. If `Z` is an arbitrary multivalued relation, the same variable code may satisfy `tmIs` at more than one value.
<!--zh-->
公开消去式 `tmIs-out` 在外层析取的命题截断之下完成上述情形分析。其结论只涉及一个给定候选值 `Vv`，并不证明两个候选值相等。若 `Z` 是任意多值关系，同一个变元码可以在多个值处满足 `tmIs`。
<!--ja-->
公開された消去補題 `tmIs-out` は、外側の選言の命題的切り詰めの下でこの場合分けを行います。結論は一つの候補値 `Vv` について述べるだけで、二つの候補値が等しいことは示しません。`Z` が任意の多値関係なら、同じ変数コードが複数の値で `tmIs` を満たしえます。
<!--/-->

```agda
  tmIs-out : ⟨ δ ⊨ tmIs t z v N0 N1 ⟩ → TmIsV Tv Z Vv
  tmIs-out h = rec₁ squash₁ cases h

```

<!--en-->
For the converse, `build` turns either concrete code shape back into satisfaction of `tmIs`. The constant equation is converted by `pr-in`. In the variable case, the proof must represent the payload index and the graph entry as elements of `S`, then rebuild the nested bounded existentials of `sndEx`.
<!--zh-->
在反向证明中，`build` 把任一具体码形状重新构造成 `tmIs` 的满足。常元等式由 `pr-in` 转换；在变元情形中，证明先把载荷索引与图条目表示成 `S` 的元素，再重建 `sndEx` 的嵌套有界存在。
<!--ja-->
逆方向では、`build` が二つの具体的なコード形のどちらからでも `tmIs` の充足を再構成します。定数の等式は `pr-in` で変換します。変数の場合は、ペイロードの添字とグラフ要素を `S` の要素として表示し、その後 `sndEx` の入れ子になった有界存在を組み立て直します。
<!--/-->

```agda
  private
    build : (Tv ≡ pr (# 0) Vv) ⊎ (Σ[ i ∈ V ℓ ] ((Tv ≡ pr (# 1) i) × ⟨ pr i Vv ∈ Z ⟩))
          → ⟨ δ ⊨ tmIs t z v N0 N1 ⟩
    build (inl e) = ∣ inl (pr-in t N0 v δ (e ∙ cong (λ a → pr a Vv) (sym q0))) ∣₁
    build (inr (i , (e , hp))) = ∣ inr (fillSnd t δ (lookup N1 δ) iS e' inner hq N1 refl) ∣₁
```

<!--en-->
`iS` is the constructible representative of the payload `i`, recovered as the second component of the pair equation `Tv=(#1,i)`. The term `qS` is the constructible representative of the graph entry `(i,Vv)`, obtained from its membership in `Z`. These are witnesses inside `S`, not new semantic indices or values.
<!--zh-->
`iS` 是载荷 `i` 的可构造代表，由配对等式 `Tv=(#1,i)` 的第二分量恢复。`qS` 是图条目 `(i,Vv)` 的可构造代表，由该配对属于 `Z` 得到。它们都是 `S` 内的见证，并非新的语义索引或语义值。
<!--ja-->
`iS` はペイロード `i` の構成可能な表示であり、対の等式 `Tv=(#1,i)` の第二成分として復元されます。`qS` はグラフ要素 `(i,Vv)` の構成可能な表示であり、その対が `Z` に属することから得られます。これらは `S` 内の証人であって、新しい意味論的な添字や値ではありません。
<!--/-->

```agda
      where
      iS : S
      iS = sndS (lookup t δ) (# 1) i e
      qS : S
      qS = down (lookup z δ) (pr i Vv) hp
```

<!--en-->
The equation `e'` rewrites the canonical tag equation into the actual tag-one slot required by `sndEx`. The auxiliary environment `δ3` places the graph entry `qS`, the payload representative `iS`, and the container for the outer term-code pair before `δ`. The remaining goal `hq` is exactly the inner bounded existential at `iS ∷ container ∷ δ`.
<!--zh-->
等式 `e'` 把典范标签等式改写成 `sndEx` 所需的实际标签一槽。辅助环境 `δ3` 在 `δ` 前依次放入图条目 `qS`、载荷代表 `iS` 与外层词项码配对的容纳集合。余下的目标 `hq` 正是 `iS ∷ container ∷ δ` 处的内层有界存在。
<!--ja-->
等式 `e'` は正準なタグの等式を、`sndEx` が要求する実際のタグ一スロットに書き換えます。補助環境 `δ3` は `δ` の前に、グラフ要素 `qS`、ペイロードの表示 `iS`、外側の項コードの対を収める容器をこの順に置きます。残る目標 `hq` は、`iS ∷ container ∷ δ` における内側の有界存在そのものです。
<!--/-->

```agda
      e' : Tv ≡ pr N1v (fst iS)
      e' = e ∙ cong (λ a → pr a i) (sym q1)
      δ3 : S ^ (3 + j)
      δ3 = qS ∷ iS ∷ container (lookup t δ) (lookup N1 δ) iS e' .fst ∷ δ
      hq : ⟨ (iS ∷ container (lookup t δ) (lookup N1 δ) iS e' .fst ∷ δ) ⊨ inner ⟩
```

<!--en-->
To prove `hq`, choose `qS` from the graph. Its membership is the given fact `hp`, and `pr-in` proves by reflexivity that its underlying set is the pair of `iS` and `Vv`. This supplies exactly the graph entry demanded by the variable branch.
<!--zh-->
为证明 `hq`，从图中选择 `qS`。其隶属事实就是给定的 `hp`，而 `pr-in` 以自反性证明其底层集合是 `iS` 与 `Vv` 的配对。这恰好给出变元分支所需的图条目。
<!--ja-->
`hq` を証明するには、グラフから `qS` を選びます。その所属は与えられた事実 `hp` であり、`pr-in` は反射性によって、その底集合が `iS` と `Vv` の対であることを示します。これで変数の場合に必要なグラフ要素がちょうど得られます。
<!--/-->

```agda
      hq = ∣ qS , (hp , pr-in i0 i1 (sh 3 v) δ3 refl) ∣₁

```

<!--en-->
Finally, `tmIs-in` eliminates the propositional truncation in `TmIsV` into the proposition expressing satisfaction of `tmIs`, applying `build` to either branch. Together with `tmIs-out`, this gives both semantic directions while preserving the absence of any global choice or uniqueness claim.
<!--zh-->
最后，`tmIs-in` 把 `TmIsV` 中的命题截断消去到表示 `tmIs` 满足的命题，并对任一分支应用 `build`。它与 `tmIs-out` 合在一起给出两个语义方向，同时仍不引入全局选择或唯一性结论。
<!--ja-->
最後に `tmIs-in` は、`TmIsV` の命題的切り詰めを `tmIs` の充足を表す命題へ消去し、どちらの場合にも `build` を適用します。`tmIs-out` と合わせて意味論の二方向が得られますが、大域的な選択や一意性の主張は導入されません。
<!--/-->

```agda
  tmIs-in : TmIsV Tv Z Vv → ⟨ δ ⊨ tmIs t z v N0 N1 ⟩
  tmIs-in = rec₁ (snd (δ ⊨ tmIs t z v N0 N1)) build
```

<!--en-->
`Frame` fixes the host-level slots for the table `T`, carrier `w`, code domain `C`, and environment tower `E`, together with the ten tag slots `N` and the surrounding assignment `γ`. The hypothesis `Tags γ N` identifies each tag slot with its numeral, allowing a clause selected by `k : Fin 10` to be read as the relation `relN (toℕ k)`.
<!--zh-->
`Frame` 固定表 `T`、载体 `w`、码定义域 `C` 与环境塔 `E` 的宿主层槽位，并固定十个标签槽 `N` 和外围赋值 `γ`。前提 `Tags γ N` 把每个标签槽与相应数码同一视，使由 `k : Fin 10` 选出的子句能够读成关系 `relN (toℕ k)`。
<!--ja-->
`Frame` は、表 `T`、台 `w`、コード領域 `C`、環境塔 `E` のホストレベルのスロットに加え、十個のタグスロット `N` と周囲の割り当て `γ` を固定します。仮定 `Tags γ N` は各タグスロットを対応する数項と同一視し、`k : Fin 10` で選ばれた節を関係 `relN (toℕ k)` として読めるようにします。
<!--/-->

```agda
module Frame {m : ℕ} (T w C E : Fin m) (N : Fin 10 → Fin m) (γ : S ^ m) (tg : Tags γ N) where
  private
    Tv = fst (lookup T γ)
    Cv = fst (lookup C γ)
    Ev = fst (lookup E γ)
```

<!--en-->
The frame is peeled by a sequence of bounded universals. At the innermost stage, `inner9 k` ranges over every table entry and uses `sndAll` to expose a value `yc` whenever that entry has first component `c`; the resulting twelve-slot environment is where `relN (toℕ k)` must hold. This is a universal condition on matching entries, not an existential search for one value.
<!--zh-->
框架通过一系列有界全称逐层拆开。在最内层，`inner9 k` 遍历每个表条目，并在该条目的第一分量为 `c` 时用 `sndAll` 暴露值 `yc`；所得十二槽环境正是 `relN (toℕ k)` 必须成立之处。这是对所有匹配条目的全称条件，并非寻找某个值的存在式。
<!--ja-->
枠組みは有界全称の列によって順にほどかれます。最も内側では `inner9 k` がすべての表要素を動き、その第一成分が `c` であるとき `sndAll` によって値 `yc` を取り出します。得られた十二スロットの環境で `relN (toℕ k)` が成り立たなければなりません。これは一致するすべての要素についての全称条件であり、一つの値を探す存在条件ではありません。
<!--/-->

```agda
    module Cl = Clause T w C E N
    module R = Rel T w N
    inner9 : Fin 10 → Formula S (9 + m)
    inner9 k = ∀̇∈ (var (sh 9 T)) (sndAll i0 i5 (R.relN (toℕ k)))
    inner7 : Fin 10 → Formula S (7 + m)
```

<!--en-->
The preceding stages expose the nested key. `inner4 k` ranges over every `c∈C` whose first component is the current arity `ar`, obtaining its payload `p`; `inner7 k` then requires `p` to have the tag stored at `N k` and exposes its residual data `r`. Each pair decomposition adds its components and a container at the head, so the shifts preserve access to the older frame slots.
<!--zh-->
前两层负责暴露嵌套的键。`inner4 k` 遍历每个第一分量为当前元数 `ar` 的 `c∈C`，取得其载荷 `p`；`inner7 k` 随后要求 `p` 的标签等于 `N k` 槽中的数码，并暴露余下数据 `r`。每次配对分解都会在前端加入分量与容纳集合，因此必须用移位保持对旧框架槽位的访问。
<!--ja-->
その前の段階では入れ子になったキーを取り出します。`inner4 k` は、第一成分が現在のアリティ `ar` であるすべての `c∈C` を動き、そのペイロード `p` を得ます。続いて `inner7 k` は `p` のタグが `N k` のスロットにある数項であることを要求し、残りのデータ `r` を取り出します。対を分解するたびに成分と容器が先頭へ加わるため、以前の枠組みのスロットへの参照はシフトによって保たれます。
<!--/-->

```agda
    inner7 k = sndAll i0 (sh 7 (N k)) (inner9 k)
    inner4 : Fin 10 → Formula S (4 + m)
    inner4 k = ∀̇∈ (var (sh 4 C)) (sndAll i0 i2 (inner7 k))
```

<!--en-->
For one clause instance, `At` fixes a tower pair `(ar,F)`, a formula key `c=(ar,p)`, a tagged payload `p=(N k,r)`, and a table pair `(c,yc)`. The memberships `q∈` and `e∈` concern the projected pairs in `E` and `T`; the module does not itself prove that `c∈C`, decode `r`, or show that the table value is unique.
<!--zh-->
对于一条子句实例，`At` 固定塔配对 `(ar,F)`、公式键 `c=(ar,p)`、带标签载荷 `p=(N k,r)` 与表配对 `(c,yc)`。隶属 `q∈` 和 `e∈` 分别涉及 `E` 与 `T` 中投影后的配对；该模块本身不证明 `c∈C`，不解码 `r`，也不证明表值唯一。
<!--ja-->
一つの節の実例について、`At` は塔の対 `(ar,F)`、論理式キー `c=(ar,p)`、タグ付きペイロード `p=(N k,r)`、表の対 `(c,yc)` を固定します。所属 `q∈` と `e∈` はそれぞれ `E` と `T` における射影された対について述べます。このモジュール自身は `c∈C` を証明せず、`r` を復号せず、表の値の一意性も示しません。
<!--/-->

```agda
  module At (ar F c p r yc : S) (q∈ : ⟨ pr (fst ar) (fst F) ∈ Ev ⟩)
            (ec : fst c ≡ pr (fst ar) (fst p)) (k : Fin 10)
            (ep : fst p ≡ pr (fst (lookup (N k) γ)) (fst r))
            (e∈ : ⟨ pr (fst c) (fst yc) ∈ Tv ⟩) where
    qS eS : S
```

<!--en-->
`qS` and `eS` lift the two projected pair memberships back to elements of the constructible carrier. Their underlying sets are definitionally `pr (fst ar) (fst F)` and `pr (fst c) (fst yc)`, respectively. They serve only as representatives to which the bounded pair readers can be applied when the twelve-slot environment is assembled.
<!--zh-->
`qS` 与 `eS` 把两个投影后的配对隶属提升回可构造载体中的元素。它们的底层集合分别按定义为 `pr (fst ar) (fst F)` 与 `pr (fst c) (fst yc)`。二者只充当代表，使组装十二槽环境时能够应用有界配对读式。
<!--ja-->
`qS` と `eS` は、二つの射影された対の所属を構成可能な台の要素へ持ち上げます。それらの底集合はそれぞれ定義により `pr (fst ar) (fst F)` と `pr (fst c) (fst yc)` です。十二スロットの環境を組み立てるとき、有界な対の読み補題を適用するための表示としてだけ使われます。
<!--/-->

```agda
    qS = down (lookup E γ) (pr (fst ar) (fst F)) q∈
    eS = down (lookup T γ) (pr (fst c) (fst yc)) e∈

```

<!--en-->
The frame begins with an actual tower member `qS` whose underlying pair is `(ar,F)`. The four new slots record `F`, `ar`, a witness for the pair decomposition, and `qS`; the next three record the payload `p`, a witness that `c=(ar,p)`, and the code `c`. Thus the successive environments retain both the mathematical data and the bounded witnesses by which the object-language clause obtained them.
<!--zh-->
框架从实际的塔成员 `qS` 开始，其底层配对是 `(ar,F)`。新增的四个槽位记录 `F`、`ar`、配对分解的见证与 `qS`；随后的三个槽位记录载荷 `p`、`c=(ar,p)` 的见证与代码 `c`。因此，逐层扩展的环境既保留数学数据，也保留对象语言子句取得这些数据时所用的有界见证。
<!--ja-->
枠は、基礎の対が `(ar,F)` である塔の実際の要素 `qS` から始まります。新しい四つの枠には `F`、`ar`、対への分解の証人、`qS` が入り、続く三つにはペイロード `p`、`c=(ar,p)` の証人、符号 `c` が入ります。このように、順次拡張される環境は、数学的データと、対象言語の節がそのデータを得るために用いた有界な証人の両方を保持します。
<!--/-->

```agda
    δ4 : S ^ (4 + m)
    δ4 = F ∷ ar ∷ container qS ar F refl .fst ∷ qS ∷ γ
    δ7 : S ^ (7 + m)
    δ7 = p ∷ container c ar p ec .fst ∷ c ∷ δ4
    δ9 : S ^ (9 + m)
```

<!--en-->
The twelve-slot environment completes the nesting. At the front is the candidate value `yc`, followed by a container exposing the components of the table pair `(c,yc)` and the actual table member `eS` whose underlying set is that pair; the nine earlier objects follow. This is the environment at which the relation body is read.
<!--zh-->
十二槽环境完成这层嵌套。候选取值 `yc` 居首，随后是暴露表配对 `(c,yc)` 两个分量的容纳集合，以及底层集合正是该配对的实际表成员 `eS`；再后是先前九个对象。关系体就在这个环境中读取。
<!--ja-->
十二の枠の環境がこの入れ子を完成させます。先頭には候補値 `yc` があり、表の対 `(c,yc)` の二成分を取り出すコンテナと、底集合がその対である実際の表要素 `eS` が続き、その後に先の九つの対象が並びます。関係の本体はこの環境で読み取られます。
<!--/-->

```agda
    δ9 = r ∷ container p (lookup (N k) γ) r ep .fst ∷ δ7
    δ12 : S ^ (12 + m)
    δ12 = yc ∷ container eS c yc refl .fst ∷ eS ∷ δ9

```

<!--en-->
The outward reading starts from satisfaction of clause `k` and fixes all data matching one instance of its frame: `ar` and `F` from a tower pair, a code `c=(ar,p)` in `C`, a tagged payload `p=(#k,r)`, and a candidate value `yc` with `(c,yc)` in `T`. It then returns satisfaction of `relN (toℕ k)` at the corresponding twelve-slot environment. The table hypothesis here is membership of the pair `(c,yc)`; the representative table member and its container are constructed locally.
<!--zh-->
向外读式从第 `k` 条子句的满足出发，并固定该子句一个框架实例的全部匹配数据：来自塔配对的 `ar` 与 `F`、`C` 中的代码 `c=(ar,p)`、带标签的载荷 `p=(#k,r)`，以及满足 `(c,yc)` 属于 `T` 的候选取值 `yc`。随后，它返回相应十二槽环境处 `relN (toℕ k)` 的满足。这里的表前提是配对 `(c,yc)` 的隶属；实际表成员及其容纳集合都在局部构造。
<!--ja-->
外向きの読み取りは第 `k` 節の充足から出発し、その枠の一つの実例に対応するデータをすべて固定します。塔の対から得られる `ar` と `F`、`C` に属するコード `c=(ar,p)`、タグ付きペイロード `p=(#k,r)`、そして `(c,yc)` が `T` に属する候補値 `yc` です。そのうえで、対応する十二の枠の環境における `relN (toℕ k)` の充足を返します。ここで表について仮定するのは対 `(c,yc)` の所属であり、実際の表要素とそのコンテナは局所的に構成されます。
<!--/-->

```agda
  clause-out : (k : Fin 10) → ⟨ γ ⊨ Cl.clause k ⟩
             → (ar F c p r yc : S) (q∈ : ⟨ pr (fst ar) (fst F) ∈ Ev ⟩) → ⟨ fst c ∈ Cv ⟩
             → (ec : fst c ≡ pr (fst ar) (fst p)) → (ep : fst p ≡ pr (# (toℕ k)) (fst r))
             → (e∈ : ⟨ pr (fst c) (fst yc) ∈ Tv ⟩)
             → ⟨ At.δ12 ar F c p r yc q∈ ec k (ep ∙ cong (λ a → pr a (fst r)) (sym (tg k))) e∈ ⊨ R.relN (toℕ k) ⟩
```

<!--en-->
With the matching data fixed, the module `A` gives one coherent realization of all twelve frame slots. The first elimination opens the tower pair, and the final `useSnd` opens the actual table member as `(c,yc)`. Between them, the proof must still pass through the code and tag layers; naming `h4` before those steps makes explicit that the conclusion follows by successively specializing the single outer clause, rather than by assuming the constructor relation separately.
<!--zh-->
匹配数据固定后，模块 `A` 为全部十二个框架槽给出一个彼此相容的实现。第一次消去打开塔配对，最后的 `useSnd` 把实际表成员打开为 `(c,yc)`；二者之间还必须经过代码层与标签层。先命名 `h4`，正是为了表明结论来自对同一条外层子句的逐次特化，而不是另行假定构造子关系。
<!--ja-->
対応するデータを固定すると、モジュール `A` は十二の枠すべてに対して整合した一つの実現を与えます。最初の除去が塔の対を開き、最後の `useSnd` が実際の表の要素を `(c,yc)` として開きます。その間には符号とタグの層を通る必要があります。そこで先に `h4` を名づけることで、結論が構成子の関係を別に仮定したものではなく、一つの外側の節を順次特殊化して得られることが明示されます。
<!--/-->

```agda
  clause-out k h ar F c p r yc q∈ c∈ ec ep e∈ =
    useSnd i0 (A.eS ∷ A.δ9) c yc refl (R.relN (toℕ k)) i5 refl (h9 A.eS e∈)
    where
    module A = At ar F c p r yc q∈ ec k (ep ∙ cong (λ a → pr a (fst r)) (sym (tg k))) e∈
    h4 : ⟨ A.δ4 ⊨ inner4 k ⟩
```

<!--en-->
The three intermediate judgments mark the three semantic layers of the common frame. At `δ4`, `h4` has opened the tower entry `(ar,F)` and is ready to range over codes in `C`; at `δ7`, `h7` has also decomposed `c=(ar,p)`; at `δ9`, `h9` has identified `p` as the tag-`k` payload `r` and is ready to inspect entries of `T`. The final elimination then decomposes the chosen table member as `(c,yc)` and reaches the constructor relation.
<!--zh-->
三条中间判断标出共同框架的三个语义层次。在 `δ4` 处，`h4` 已打开塔条目 `(ar,F)`，可以开始考察 `C` 中的代码；在 `δ7` 处，`h7` 还分解了 `c=(ar,p)`；在 `δ9` 处，`h9` 已把 `p` 识别为标签 `k` 的载荷 `r`，可以考察 `T` 中的条目。最后一次消去把所选表成员分解为 `(c,yc)`，由此抵达构造子关系。
<!--ja-->
三つの中間判断は、共通の枠の三つの意味論的な層を示します。`δ4` では `h4` が塔の項目 `(ar,F)` を開き、`C` の符号を調べられる状態にあります。`δ7` では `h7` がさらに `c=(ar,p)` を分解しています。`δ9` では `h9` が `p` をタグ `k` のペイロード `r` と同定し、`T` の項目を調べられる状態にあります。最後の除去で、選んだ表の要素を `(c,yc)` と分解し、構成子の関係に到達します。
<!--/-->

```agda
    h4 = useBoth i0 (A.qS ∷ γ) ar F refl (inner4 k) (h A.qS q∈)
    h7 : ⟨ A.δ7 ⊨ inner7 k ⟩
    h7 = useSnd i0 (c ∷ A.δ4) ar p ec (inner7 k) i2 refl (h4 c c∈)
    h9 : ⟨ A.δ9 ⊨ inner9 k ⟩
    h9 = useSnd i0 A.δ7 (lookup (N k) γ) r (ep ∙ cong (λ a → pr a (fst r)) (sym (tg k))) (inner9 k) (sh 7 (N k)) refl h7
```

<!--en-->
For the converse direction, suppose the constructor relation can be proved from every complete matching frame. Such a frame consists of a tower member `q=(ar,F)`, a code `c=(ar,p)` in `C`, a tag decomposition `p=(#k,r)`, and a table member `e=(c,yc)`, together with the four pair witnesses `s`, `s1`, `s2`, and `s3`. Proving the relation in the displayed environment for all this data is exactly the premise needed to reconstruct clause `k`.
<!--zh-->
反向构造假定：每个完整匹配的框架都能证明构造子关系。这样的框架包含塔成员 `q=(ar,F)`、`C` 中的代码 `c=(ar,p)`、标签分解 `p=(#k,r)`、表成员 `e=(c,yc)`，以及四个配对见证 `s`、`s1`、`s2` 与 `s3`。若对所有这些数据都能在所示环境中证明该关系，便恰好具备重建第 `k` 条子句所需的前提。
<!--ja-->
逆向きの構成では、完全に対応するすべての枠から構成子の関係を証明できると仮定します。そのような枠は、塔の要素 `q=(ar,F)`、`C` に属する符号 `c=(ar,p)`、タグの分解 `p=(#k,r)`、表の要素 `e=(c,yc)`、および四つの対の証人 `s`、`s1`、`s2`、`s3` からなります。これらすべてのデータについて表示された環境で関係を証明できることが、第 `k` 節を再構成するために必要な前提そのものです。
<!--/-->

```agda

  clause-in : (k : Fin 10)
            → ((q ar F s c p s1 r s2 e yc s3 : S) → ⟨ fst q ∈ Ev ⟩ → fst q ≡ pr (fst ar) (fst F)
               → ⟨ fst c ∈ Cv ⟩ → fst c ≡ pr (fst ar) (fst p) → fst p ≡ pr (# (toℕ k)) (fst r)
               → ⟨ fst e ∈ Tv ⟩ → fst e ≡ pr (fst c) (fst yc)
               → ⟨ (yc ∷ s3 ∷ e ∷ r ∷ s2 ∷ p ∷ s1 ∷ c ∷ F ∷ ar ∷ s ∷ q ∷ γ) ⊨ R.relN (toℕ k) ⟩)
```

<!--en-->
The proof rebuilds the universally quantified frame in its logical order. It handles an arbitrary `q` in `E` together with every exposed decomposition `q=(ar,F)`, then an arbitrary `c` in `C` together with every matching decomposition `c=(ar,p)`. It next identifies the tag and payload of `p`, and finally handles an arbitrary `e` in `T` together with every decomposition `e=(c,yc)`. Each bounded introduction places its new value at the head of the environment, while the accompanying `s`-variables retain the pair-decomposition witnesses required by the formulas.
<!--zh-->
证明按逻辑次序重建这个全称量化的框架。它先处理 `E` 中任意的 `q` 以及每个被暴露出的分解 `q=(ar,F)`，再处理 `C` 中任意的 `c` 以及每个匹配的分解 `c=(ar,p)`；继而识别 `p` 的标签与载荷，最后处理 `T` 中任意的 `e` 以及每个分解 `e=(c,yc)`。每次有界引入都把新值放在环境头部，而相伴的 `s` 变量保留公式所需的配对分解见证。
<!--ja-->
証明は全称量化された枠を論理的な順序で組み直します。まず `E` の任意の `q` と、そこから取り出される各分解 `q=(ar,F)` を扱い、次に `C` の任意の `c` と、それに一致する各分解 `c=(ar,p)` を扱います。続いて `p` のタグとペイロードを同定し、最後に `T` の任意の `e` と各分解 `e=(c,yc)` を扱います。有界な導入のたびに新しい値が環境の先頭に置かれ、対応する `s` 変数が論理式に必要な対分解の証人を保持します。
<!--/-->

```agda
            → ⟨ γ ⊨ Cl.clause k ⟩
  clause-in k g q q∈ = bothAll-in i0 (inner4 k) (q ∷ γ) (λ ar F s s∈ ar∈ F∈ eq c c∈ →
    sndAll-in i0 i2 (inner7 k) (c ∷ F ∷ ar ∷ s ∷ q ∷ γ) (λ p s1 s1∈ p∈ ec →
      sndAll-in i0 (sh 7 (N k)) (inner9 k) (p ∷ s1 ∷ c ∷ F ∷ ar ∷ s ∷ q ∷ γ) (λ r s2 s2∈ r∈ ep e e∈ →
        sndAll-in i0 i5 (R.relN (toℕ k)) (e ∷ r ∷ s2 ∷ p ∷ s1 ∷ c ∷ F ∷ ar ∷ s ∷ q ∷ γ) (λ yc s3 s3∈ yc∈ ee →
```

<!--en-->
Before the host-level rule `g` is applied, the payload equation is composed with `tg k`, replacing the set stored in the tag slot by the canonical numeral `#k`. The rule therefore receives exactly the equation `p=(#k,r)` appearing in the outward reading. Thus `clause-in` and `clause-out` give the two directions between clause `k` and its relation at every matching frame.
<!--zh-->
调用宿主层规则 `g` 之前，证明把载荷等式与 `tg k` 复合，将标签槽中存放的集合改写为典范数码 `#k`。因此，规则收到的恰是向外读式中出现的等式 `p=(#k,r)`。这样，`clause-in` 与 `clause-out` 就在每个匹配框架上给出第 `k` 条子句与其关系之间的两个方向。
<!--ja-->
ホスト側の規則 `g` を適用する前に、ペイロードの等式を `tg k` と合成し、タグの枠に格納された集合を正準な数項 `#k` に書き換えます。したがって規則が受け取るのは、外向きの読み取りに現れる等式 `p=(#k,r)` そのものです。こうして `clause-in` と `clause-out` は、一致する各枠において、第 `k` 節とその関係の間の二方向を与えます。
<!--/-->

```agda
          g q ar F s c p s1 r s2 e yc s3 q∈ eq c∈ ec (ep ∙ cong (λ a → pr a (fst r)) (tg k)) e∈ ee))))
```

<!--en-->
Totality is read outward as truncated existence: for each member of the code domain, the totality clause guarantees that some table entry with that first component exists, and the truncated decomposition of the table entry recovers the value `yc`.
<!--zh-->
全定义性向外读取为经过命题截断的存在陈述：对码定义域的每个成员，全定义性子句保证存在以该成员为第一分量的表条目，而表条目经过命题截断的分解会恢复取值 `yc`。
<!--ja-->
全域性は、切り詰められた存在として外向きに読まれます。符号領域の各要素に対して、全域性の条項が、その第一成分をもつ表の項目の存在を保証し、表の項目の切り詰められた分解が値 `yc` を復元します。
<!--/-->

```agda
  total-out : ⟨ γ ⊨ Cl.total ⟩ → (c : S) → ⟨ fst c ∈ Cv ⟩ → ∥ Σ[ yc ∈ S ] ⟨ pr (fst c) (fst yc) ∈ Tv ⟩ ∥₁
  total-out h c c∈ = rec₁ squash₁
    (λ { (e , (e∈ , hs)) → map₁
      (λ { (yc , s , (ee , _)) → yc , subst (λ u → ⟨ u ∈ Tv ⟩) ee e∈ })
      (sndEx-out i0 i1 ⊤̇ (e ∷ c ∷ γ) hs) })
```

<!--en-->
For a fixed `c∈C`, applying the standing hypothesis `h` yields, under propositional truncation, a table member `e` together with its membership in `T` and a decomposition statement. The reader `sndEx-out` decomposes `e` as `(c,yc)`, and transporting the membership of `e` along that equation proves `(c,yc)∈T`. Both decompositions remain hidden by the truncation, so the result supplies existence without selecting a canonical value.
<!--zh-->
固定 `c∈C` 后，把既有假设 `h` 用于 `c`，便在命题截断下得到一个表成员 `e`、它属于 `T` 的证明以及一条分解陈述。读式 `sndEx-out` 再把 `e` 分解为 `(c,yc)`，并沿该等式搬运 `e` 的隶属证明，从而得到 `(c,yc)∈T`。两层分解都由命题截断隐藏，因此结论只给出存在性，并不选取典范取值。
<!--ja-->
`c∈C` を固定して仮定 `h` を `c` に適用すると、命題的切り詰めの下で、表要素 `e`、その `T` への所属、および分解を述べる証明が得られます。読み補題 `sndEx-out` がさらに `e` を `(c,yc)` に分解し、その等式に沿って `e` の所属を運ぶことで `(c,yc)∈T` を示します。二段の分解はいずれも切り詰めの内部にとどまるので、結論は存在を与えるだけで、正準な値を選びません。
<!--/-->

```agda
    (h c c∈)

```

<!--en-->
Conversely, assume that every `c` in `C` has, propositionally truncated, a value `yc` with `(c,yc)` in `T`. The membership proof is turned by `down` into an element `e : S` of `T` whose underlying set is that pair; `fillSnd` supplies the bounded witnesses that decompose `e` back into `c` and `yc`. The remaining body is truth, so this data constructs the totality clause without choosing a value globally and without asserting uniqueness.
<!--zh-->
反过来，假定对 `C` 中每个 `c`，都有一个经过命题截断的存在陈述，断言某个 `yc` 满足 `(c,yc)` 属于 `T`。`down` 把这条隶属证明实现为 `T` 的一个元素 `e : S`，其底层集合正是该配对；`fillSnd` 再给出把 `e` 分解回 `c` 与 `yc` 的有界见证。余下的主体为真，故这些数据足以构造全定义性子句，同时既不全局选择取值，也不主张唯一性。
<!--ja-->
逆に、`C` の各 `c` について、`(c,yc)` が `T` に属するような値 `yc` が命題的に切り詰められて存在すると仮定します。`down` はその所属の証明を、基礎の集合がその対である `T` の要素 `e : S` に実現し、`fillSnd` は `e` を `c` と `yc` に分解する有界な証人を与えます。残る本体は真なので、このデータから全域性の節を構成できます。値の大域的な選択も一意性の主張も含まれません。
<!--/-->

```agda
  total-in : ((c : S) → ⟨ fst c ∈ Cv ⟩ → ∥ Σ[ yc ∈ S ] ⟨ pr (fst c) (fst yc) ∈ Tv ⟩ ∥₁) → ⟨ γ ⊨ Cl.total ⟩
  total-in g c c∈ = map₁
    (λ { (yc , m) → down (lookup T γ) (pr (fst c) (fst yc)) m
       , ( m , fillSnd i0 (down (lookup T γ) (pr (fst c) (fst yc)) m ∷ c ∷ γ) c yc refl ⊤̇ (λ b → b) i1 refl ) })
    (g c c∈)
```

<!--en-->
The on-domain condition starts with an arbitrary element `e` of `T`, rather than with a pair already chosen in advance. Its outward reading recovers, under propositional truncation, objects `c` and `yc` such that `e=(c,yc)` and `c` belongs to `C`. Thus every member of the table has a code from the stated domain as its first component, but the result says neither that the decomposition is selected canonically nor that a code has only one value.
<!--zh-->
定义域约束从 `T` 的任意元素 `e` 出发，而不是预先给定一个配对。其向外读法在命题截断下恢复 `c` 与 `yc`，满足 `e=(c,yc)` 且 `c` 属于 `C`。因此，表的每个成员都以给定定义域中的代码为第一分量；这个结论既不典范地选定分解，也不说明一个代码只有一个取值。
<!--ja-->
領域条件は、あらかじめ選ばれた対ではなく、`T` の任意の要素 `e` から出発します。その外向きの読み取りは、`e=(c,yc)` かつ `c` が `C` に属するような `c` と `yc` を、命題的切り詰めの下で復元します。したがって表の各要素の第一成分は指定された領域の符号ですが、分解の正準な選択も、一つの符号が値を一つしか持たないことも述べていません。
<!--/-->

```agda

  onC-out : ⟨ γ ⊨ Cl.onC ⟩ → (e : S) → ⟨ fst e ∈ Tv ⟩
          → ∥ Σ[ c ∈ S ] Σ[ yc ∈ S ] ((fst e ≡ pr (fst c) (fst yc)) × ⟨ fst c ∈ Cv ⟩) ∥₁
  onC-out h e e∈ = map₁ (λ { (c , yc , s , (ee , c∈)) → c , yc , (ee , c∈) })
    (bothEx-out i0 (var i1 ∈̇ var (sh 4 C)) (e ∷ γ) (h e e∈))

```

<!--en-->
The converse asks for precisely that truncated decomposition of every member of `T` and inserts it into the two bounded existentials of `onC`. Together the two readings identify `onC` with the claim that the first projection of every table member lies in `C`. Combined with totality this fixes the table's domain projection, but it still does not make the table single-valued.
<!--zh-->
反向读法恰好要求 `T` 的每个成员都具有上述经过命题截断的分解，再把该分解注入 `onC` 的两层有界存在量词。两条读法合起来把 `onC` 精确解释为「每个表成员的第一投影属于 `C`」。它与全定义性结合后确定表的定义域投影，但仍不使这张表成为单值关系。
<!--ja-->
逆向きの読み取りは、`T` の各要素についてまさにこの切り詰められた分解を要求し、それを `onC` の二つの有界存在量化へ入れます。二方向の読み取りを合わせると、`onC` は「表の各要素の第一射影が `C` に属する」という主張に正確に対応します。全域性と組み合わせれば表の領域射影は定まりますが、表が一価の関係になるわけではありません。
<!--/-->

```agda
  onC-in : ((e : S) → ⟨ fst e ∈ Tv ⟩ → ∥ Σ[ c ∈ S ] Σ[ yc ∈ S ] ((fst e ≡ pr (fst c) (fst yc)) × ⟨ fst c ∈ Cv ⟩) ∥₁)
         → ⟨ γ ⊨ Cl.onC ⟩
  onC-in g e e∈ = rec₁ (snd ((e ∷ γ) ⊨ bothEx i0 (var i1 ∈̇ var (sh 4 C))))
    (λ { (c , yc , (ee , c∈)) → fillBoth i0 (e ∷ γ) c yc ee (var i1 ∈̇ var (sh 4 C)) c∈ })
    (g e e∈)
```

<!--en-->
## Reading the constructor relations
<!--zh-->
## 读取构造子关系
<!--ja-->
## 構成子の関係を読む
<!--/-->

<!--en-->
The constructor readers work over a frame `δ` with twelve slots added in front of the original `m`-environment. The original slots `T` and `w`, and the ten numeral slots `N`, therefore live beyond this prefix, while the frame itself places the candidate value `yc` at `i0` and the constructor payload `r` at `i3`. Fixing these positions lets every relation reader use the same outer frame, regardless of the constructor being read.
<!--zh-->
构造子读式在一个框架 `δ` 上工作，它在原来的 `m` 槽环境前增加了十二个槽位。因此，原环境中的 `T`、`w` 与十个数码槽 `N` 都位于这段前缀之后；框架自身则把候选取值 `yc` 放在 `i0`，把构造子载荷 `r` 放在 `i3`。固定这些位置后，无论读取哪一种构造子，每条关系读式都能共用同一个外层框架。
<!--ja-->
構成子の読み取りは、元の `m` 枠の環境の前に十二の枠を加えた環境 `δ` 上で行われます。したがって元の枠 `T` と `w`、および十個の数項の枠 `N` はこの接頭部の先にあり、枠そのものでは候補値 `yc` が `i0`、構成子のペイロード `r` が `i3` に置かれます。この位置を固定することで、どの構成子を読む場合にも同じ外側の枠を使えます。
<!--/-->

```agda
module RelRead {m : ℕ} (T w : Fin m) (N : Fin 10 → Fin m) (δ : S ^ (12 + m)) where
  private
    module R = Rel T w N
    yc = lookup i0 δ
    r = lookup i3 δ
```

<!--en-->
The remaining local names identify the environment-set slot `F` and the arity slot `ar`. They project the underlying table set `Tv`, the arity value `A`, and the constructor payload `Rv` once, so the relation readers can state their hypotheses directly in the cumulative hierarchy.
<!--zh-->
其余局部名称标出环境集槽 `F` 与元数槽 `ar`，并一次性投影出表的底层集合 `Tv`、元数值 `A` 与构造子载荷 `Rv`。这样，后续关系读式就能直接在累积层级中陈述前提。
<!--ja-->
残る局所名は、環境集合の枠 `F` とアリティの枠 `ar` を示します。さらに表の底集合 `Tv`、アリティの値 `A`、構成子のペイロード `Rv` を一度だけ射影しておくことで、後の関係の読み補題が累積階層の中で仮定を直接述べられるようにします。
<!--/-->

```agda
    F = lookup i8 δ
    ar = lookup i9 δ
    Tv = fst (lookup (sh 12 T) δ)
    A = fst ar
    Rv = fst r
```

<!--en-->
For any further local environment `env`, `Ext env φ` states the exact extension property for the outer table value `yc`. An element `z` belongs to `yc` exactly when it belongs to the arity-appropriate environment set `F` and the formula `φ` holds after `z` is placed in the new head slot of `env`. The old slots of `env` are consequently read one position later inside `φ`.
<!--zh-->
对任意进一步扩展的局部环境 `env`，`Ext env φ` 都陈述外层表取值 `yc` 的精确外延性质。元素 `z` 属于 `yc`，当且仅当它属于元数相应的环境集 `F`，并且把 `z` 放入 `env` 的新头槽后公式 `φ` 成立。因此，`env` 的原有槽位在 `φ` 内都向后移动一个位置读取。
<!--ja-->
さらに拡張された任意の局所環境 `env` に対して、`Ext env φ` は外側の表の値 `yc` の正確な外延条件を述べます。要素 `z` が `yc` に属するのは、`z` がアリティに対応する環境集合 `F` に属し、かつ `z` を `env` の新しい先頭枠に置いたときに論理式 `φ` が成り立つ場合にちょうど限ります。そのため、`env` の元の枠は `φ` の内部では一つ後ろの位置から読まれます。
<!--/-->

```agda
  Ext : ∀ {k} (env : S ^ k) (φ : Formula S (1 + k)) → Type (ℓ-suc ℓ)
  Ext env φ = ExtFact (fst yc) (fst F) (λ z → ⟨ (z ∷ env) ⊨ φ ⟩)
```

<!--en-->
For a binary connective, the payload `r` must decompose as the two child codes `a` and `b`. The keys `c₁=(A,a)` and `c₂=(A,b)` must have table values `ya` and `yb`. From these hypotheses, `bin-out` returns five auxiliary witnesses under propositional truncation: one container for `r=(a,b)`, and for each child both an actual member of `T` and a container witnessing its decomposition. The mathematical conclusion is an `Ext` fact for the outer value `yc`, whose body tests membership in `ya` and `yb` using the connective `op`.
<!--zh-->
对于二元联结词，载荷 `r` 必须分解为两个子公式码 `a` 与 `b`，而键 `c₁=(A,a)`、`c₂=(A,b)` 必须分别在表中具有取值 `ya`、`yb`。由这些假设，`bin-out` 在命题截断下返回五个辅助见证：一个见证 `r=(a,b)` 的容纳集合，以及每个子公式对应的一个 `T` 的实际成员和一个分解容纳集合。数学结论是关于外层取值 `yc` 的 `Ext` 事实，其主体以联结词 `op` 组合对 `ya` 与 `yb` 的隶属判断。
<!--ja-->
二項結合子では、ペイロード `r` が二つの子論理式の符号 `a` と `b` に分解されなければなりません。また、鍵 `c₁=(A,a)` と `c₂=(A,b)` は、それぞれ表の値 `ya` と `yb` を持つ必要があります。これらの仮定から `bin-out` は、命題的切り詰めの下で五つの補助的な証人を返します。一つは `r=(a,b)` のコンテナで、各子論理式については `T` の実際の要素とその分解を示すコンテナです。数学的な結論は外側の値 `yc` に関する `Ext` であり、その本体は `ya` と `yb` への所属を結合子 `op` で組み合わせます。
<!--/-->

```agda
  bin-out : (op : ∀ {j} → Formula S j → Formula S j → Formula S j) → ⟨ δ ⊨ R.binRel op ⟩
          → (a b c₁ ya c₂ yb : S) → Rv ≡ pr (fst a) (fst b)
          → ⟨ pr (fst c₁) (fst ya) ∈ Tv ⟩ → fst c₁ ≡ pr A (fst a)
          → ⟨ pr (fst c₂) (fst yb) ∈ Tv ⟩ → fst c₂ ≡ pr A (fst b)
          → ∥ Σ[ s ∈ S ] Σ[ s₁ ∈ S ] Σ[ e₁ ∈ S ] Σ[ s₂ ∈ S ] Σ[ e₂ ∈ S ]
```

<!--en-->
The five witnesses are packaged only because the object-language bounded quantifiers hide the pair decompositions. After the payload has been opened, the first `subAt-out` reads the value at the left child key and the second reads the value at the right child key. The innermost `extB` then yields the exact extension of `yc`; it does not assert that either child value was uniquely selected by the table.
<!--zh-->
之所以打包这五个见证，只是因为对象语言的有界量词隐藏了各次配对分解。打开载荷后，第一次 `subAt-out` 读取左子公式键处的取值，第二次读取右子公式键处的取值；最内层的 `extB` 随即给出 `yc` 的精确外延。这个结论并不说明表为任一子公式键唯一选定了取值。
<!--ja-->
五つの証人をまとめるのは、対象言語の有界量化が各対分解を隠しているためです。ペイロードを開いた後、最初の `subAt-out` が左の子論理式の鍵における値を読み、二つ目が右の子論理式の鍵における値を読みます。最も内側の `extB` がそこで `yc` の正確な外延を与えますが、表がどちらかの子の値を一意に選んだとは述べていません。
<!--/-->

```agda
              Ext (yb ∷ c₂ ∷ s₂ ∷ e₂ ∷ ya ∷ c₁ ∷ s₁ ∷ e₁ ∷ b ∷ a ∷ s ∷ δ) (R.binBody op) ∥₁
  bin-out op h a b c₁ ya c₂ yb er m₁ e₁ m₂ e₂ =
    ∣ container r a b er .fst , container e₁S c₁ ya refl .fst , e₁S , container e₂S c₂ yb refl .fst , e₂S ,
      subAt-out (sh 19 T) i16 i4 (extB i11 i19 (R.binBody op)) δ19
        (subAt-out (sh 15 T) i12 i1 (subAt (sh 19 T) i16 i4 (extB i11 i19 (R.binBody op))) δ15
```

<!--en-->
The first step is to open the payload equation `r=(a,b)` inside the twelve-slot frame. This contributes the pair container and produces `δ15`, the old frame prefixed by `b`, `a`, and that container. The two nested subvalue readings then proceed from left to right, so their hidden table witnesses remain inside the outer propositional truncation.
<!--zh-->
第一步是在十二槽框架内打开载荷等式 `r=(a,b)`。这一步加入配对容纳集合，并产生 `δ15`，即在旧框架前依次加入 `b`、`a` 与该容纳集合。随后两层嵌套的子值读式从左到右进行，因而其中隐藏的表见证仍留在外层命题截断之内。
<!--ja-->
最初の段階では、十二枠の環境内でペイロードの等式 `r=(a,b)` を開きます。これにより対のコンテナが加わり、古い枠の前に `b`、`a`、そのコンテナを置いた `δ15` が得られます。その後、入れ子になった二つの子の値の読み取りが左から右へ進むため、そこで隠される表の証人は外側の命題的切り詰めの内部に保たれます。
<!--/-->

```agda
          (useBoth i3 δ a b er (subAt (sh 15 T) i12 i1 (subAt (sh 19 T) i16 i4 (extB i11 i19 (R.binBody op)))) h)
          c₁ ya m₁ e₁)
        c₂ yb m₂ e₂ ∣₁
    where
    δ15 : S ^ (15 + m)
```

<!--en-->
The membership proof for `(c₁,ya)` does not itself supply an element of the structure `S`; `down` realizes it as `e₁S : S`, an actual member of `T` with that underlying pair. The environment `δ19` then prefixes `ya`, `c₁`, their pair container, and `e₁S` to `δ15`. These four slots are exactly the frame expected by the first `subAt` reading.
<!--zh-->
关于 `(c₁,ya)` 的隶属证明本身并不直接给出结构 `S` 的元素；`down` 把它实现为 `e₁S : S`，即 `T` 中底层配对为 `(c₁,ya)` 的一个实际成员。环境 `δ19` 再把 `ya`、`c₁`、二者的配对容器与 `e₁S` 加到 `δ15` 前面。这四个槽位恰是第一次 `subAt` 读取所需的框架。
<!--ja-->
`(c₁,ya)` の所属証明そのものは、構造 `S` の要素を直接与えません。`down` はそれを、基礎の対が `(c₁,ya)` である `T` の実際の要素 `e₁S : S` として実現します。環境 `δ19` はさらに `ya`、`c₁`、両者の対のコンテナ、`e₁S` を `δ15` の前に置きます。この四つの枠が、最初の `subAt` の読み取りが要求する枠に正確に一致します。
<!--/-->

```agda
    δ15 = b ∷ a ∷ container r a b er .fst ∷ δ
    e₁S : S
    e₁S = down (lookup (sh 15 T) δ15) (pr (fst c₁) (fst ya)) m₁
    δ19 : S ^ (19 + m)
    δ19 = ya ∷ c₁ ∷ container e₁S c₁ ya refl .fst ∷ e₁S ∷ δ15
```

<!--en-->
The same construction realizes the second membership proof as `e₂S : S`, an actual table member with underlying pair `(c₂,yb)`. The second `subAt-out` supplies its accompanying pair container when it extends `δ19`. Hence both child values are available to `binBody`, while neither membership proof has been turned into a global choice from the table.
<!--zh-->
同一构造把第二条隶属证明实现为 `e₂S : S`，即底层配对为 `(c₂,yb)` 的实际表成员。第二次 `subAt-out` 在扩展 `δ19` 时会补上相应的配对容器。因此，`binBody` 可以同时读取两个子公式取值，而两条隶属证明都没有被提升为从表中进行的全局选择。
<!--ja-->
同じ構成により、二つ目の所属証明は、基礎の対が `(c₂,yb)` である実際の表の要素 `e₂S : S` として実現されます。二つ目の `subAt-out` は `δ19` を拡張するときに対応する対のコンテナも与えます。こうして `binBody` は二つの子の値をともに読めますが、どちらの所属証明も表からの大域的な選択には変えられていません。
<!--/-->

```agda
    e₂S : S
    e₂S = down (lookup (sh 19 T) δ19) (pr (fst c₂) (fst yb)) m₂

```

<!--en-->
The converse begins with a rule for every possible decomposition of the binary frame. Besides the child codes and values, the rule receives the payload container, the two actual table members, their pair containers, and the equations proving that their keys are `(A,a)` and `(A,b)`. Its conclusion must be the `Ext` fact for the outer value `yc` in the environment obtained by adding these eleven objects to the original twelve-slot frame.
<!--zh-->
反向构造从一条适用于二元框架所有可能分解的规则开始。除子公式码与取值外，该规则还接收载荷容器、两个实际表成员、它们的配对容器，以及证明相应键分别为 `(A,a)`、`(A,b)` 的等式。它必须在原十二槽框架前加入这十一个对象所得的环境中，给出外层取值 `yc` 的 `Ext` 事实。
<!--ja-->
逆向きの構成は、二項の枠のあらゆる分解に対する規則から始まります。規則は子論理式の符号と値に加えて、ペイロードのコンテナ、二つの実際の表の要素、それぞれの対のコンテナ、および鍵が `(A,a)` と `(A,b)` であることを示す等式を受け取ります。その結論は、元の十二枠の前にこれら十一の対象を加えた環境における、外側の値 `yc` の `Ext` でなければなりません。
<!--/-->

```agda
  bin-in : (op : ∀ {j} → Formula S j → Formula S j → Formula S j)
         → ((a b s c₁ ya s₁ e₁ c₂ yb s₂ e₂ : S) → Rv ≡ pr (fst a) (fst b)
            → ⟨ fst e₁ ∈ Tv ⟩ → fst e₁ ≡ pr (fst c₁) (fst ya) → fst c₁ ≡ pr A (fst a)
            → ⟨ fst e₂ ∈ Tv ⟩ → fst e₂ ≡ pr (fst c₂) (fst yb) → fst c₂ ≡ pr A (fst b)
            → Ext (yb ∷ c₂ ∷ s₂ ∷ e₂ ∷ ya ∷ c₁ ∷ s₁ ∷ e₁ ∷ b ∷ a ∷ s ∷ δ) (R.binBody op))
```

<!--en-->
The proof introduces the two argument quantifiers and the relation container, then opens the two nested subAt clauses for the left and right table entries, each introducing its code, value, and pair equation.
<!--zh-->
证明引入两个实参量词与关系容器，然后为左右两条表条目打开两层嵌套的 subAt 子句，各自引入其码、取值与对等式。
<!--ja-->
証明は、二つの引数の量化子と関係のコンテナを導入し、左右の表の項目のために、入れ子になった二つの subAt の条項を開いて、それぞれの符号、値、対の等式を導入します。
<!--/-->

```agda
         → ⟨ δ ⊨ R.binRel op ⟩
  bin-in op g = bothAll-in i3 (subAt (sh 15 T) i12 i1 (subAt (sh 19 T) i16 i4 (extB i11 i19 (R.binBody op)))) δ
    (λ a b s s∈ a∈ b∈ er →
      subAt-in (sh 15 T) i12 i1 (subAt (sh 19 T) i16 i4 (extB i11 i19 (R.binBody op))) (b ∷ a ∷ s ∷ δ)
        (λ c₁ ya s₁ e₁ e₁∈ ee₁ e₁' →
```

<!--en-->
At the innermost level, the host-side rule receives all eleven objects and produces the extension fact, which is transported into the innermost subAt clause. The nesting of introductions mirrors the nesting of the quantified clause.
<!--zh-->
在最内层，宿主侧规则接收全部十一个对象并产出外延事实，该事实被运入最内层的 subAt 子句。引入的嵌套与量化子句的嵌套互为镜像。
<!--ja-->
最も内側の水準で、ホスト側の規則が十一の対象をすべて受け取り、外延の事実を作ります。それは、最も内側の subAt の条項の中へ運ばれます。導入の入れ子は、量化された節の入れ子と鏡の関係です。
<!--/-->

```agda
          subAt-in (sh 19 T) i16 i4 (extB i11 i19 (R.binBody op)) (ya ∷ c₁ ∷ s₁ ∷ e₁ ∷ b ∷ a ∷ s ∷ δ)
            (λ c₂ yb s₂ e₂ e₂∈ ee₂ e₂' →
              g a b s c₁ ya s₁ e₁ c₂ yb s₂ e₂ er e₁∈ ee₁ e₁' e₂∈ ee₂ e₂')))
```

<!--en-->
For an unbounded quantifier, the payload `r` is the child formula code. A matching child key has the form `c₁=(ar',r)`, where `ar'` is the successor of the outer arity `A`, and `(c₁,ya)` belongs to the table. From these data, `qu-out` returns three hidden witnesses and an `Ext` fact for the outer value `yc`. In that extension fact, `ya` supplies the child satisfaction set used by the quantified body; `ya` itself is not the set being characterized.
<!--zh-->
对无界量词而言，载荷 `r` 就是子公式码。匹配的子公式键形如 `c₁=(ar',r)`，其中 `ar'` 是外层元数 `A` 的后继，并且 `(c₁,ya)` 属于表。由这些数据，`qu-out` 返回三个隐藏见证，以及关于外层取值 `yc` 的 `Ext` 事实。在该外延事实中，`ya` 提供量化体所读取的子公式满足集；被刻画的集合并不是 `ya` 本身。
<!--ja-->
非有界量化子では、ペイロード `r` が子論理式の符号です。対応する子の鍵は `c₁=(ar',r)` という形で、`ar'` は外側のアリティ `A` の後続であり、`(c₁,ya)` は表に属します。このデータから `qu-out` は三つの隠れた証人と、外側の値 `yc` に関する `Ext` を返します。その外延条件では `ya` が量化された本体の読む子論理式の充足集合を与えますが、特徴付けられる集合そのものは `ya` ではありません。
<!--/-->

```agda
  qu-out : (q : ∀ {j} → Term S j → Formula S (suc j) → Formula S j) → ⟨ δ ⊨ R.quRel q ⟩
         → (c₁ ya ar' : S) → ⟨ pr (fst c₁) (fst ya) ∈ Tv ⟩ → fst c₁ ≡ pr (fst ar') Rv → fst ar' ≡ sucV A
         → ∥ Σ[ s ∈ S ] Σ[ s' ∈ S ] Σ[ e' ∈ S ] Ext (ar' ∷ s' ∷ ya ∷ c₁ ∷ s ∷ e' ∷ δ) (R.quBody q) ∥₁
  qu-out q h c₁ ya ar' mem e es =
    ∣ container e'S c₁ ya refl .fst , container c₁ ar' r e .fst , e'S
```

<!--en-->
The three witnesses have distinct roles. `e'S` is an actual member of `T` realizing the pair `(c₁,ya)`; one container witnesses that pair, and the other witnesses `c₁=(ar',r)`. The general successor-arity reader already knows how to combine these witnesses with `ar'=suc A` and then expose the innermost extension fact.
<!--zh-->
三个见证各有不同作用。`e'S` 是 `T` 中实现配对 `(c₁,ya)` 的实际成员；一个容器见证该配对，另一个容器见证 `c₁=(ar',r)`。通用的后继元数读式已经能够把这些见证与 `ar'=suc A` 结合，再揭示最内层的外延事实。
<!--ja-->
三つの証人にはそれぞれ異なる役割があります。`e'S` は対 `(c₁,ya)` を実現する `T` の実際の要素で、一方のコンテナはその対を、もう一方は `c₁=(ar',r)` を証明します。後続アリティに対する一般の読み取りは、これらの証人を `ar'=suc A` と組み合わせて、最も内側の外延条件を取り出します。
<!--/-->

```agda
    , subSucAt-out (sh 12 T) i9 i3 (extB i6 i14 (R.quBody q)) δ h c₁ ya ar' mem e es ∣₁
    where
    e'S : S
    e'S = down (lookup (sh 12 T) δ) (pr (fst c₁) (fst ya)) mem

```

<!--en-->
Conversely, suppose every actual table member `e'=(c₁,ya)` whose key satisfies `c₁=(ar',r)` and `ar'=suc A` yields the required `Ext` fact, for every choice of the two pair containers. This universal premise is strong enough to rebuild the bounded structure of `quRel`. It concerns all matching entries and does not presume that the child value `ya` is unique.
<!--zh-->
反过来，假定每个实际表成员 `e'=(c₁,ya)`，只要其键满足 `c₁=(ar',r)` 与 `ar'=suc A`，就在任意两个配对容器下给出所需的 `Ext` 事实。这条全称前提足以重建 `quRel` 的有界结构；它考察所有匹配条目，并不预设子公式取值 `ya` 唯一。
<!--ja-->
逆に、鍵が `c₁=(ar',r)` と `ar'=suc A` を満たす実際の表の要素 `e'=(c₁,ya)` が、二つの対のコンテナのどの選び方に対しても必要な `Ext` を与えると仮定します。この全称的な前提から `quRel` の有界な構造を組み直せます。これは対応するすべての項目を扱うもので、子の値 `ya` の一意性を仮定しません。
<!--/-->

```agda
  qu-in : (q : ∀ {j} → Term S j → Formula S (suc j) → Formula S j)
        → ((c₁ ya ar' s s' e' : S) → ⟨ fst e' ∈ Tv ⟩ → fst e' ≡ pr (fst c₁) (fst ya)
           → fst c₁ ≡ pr (fst ar') Rv → fst ar' ≡ sucV A
           → Ext (ar' ∷ s' ∷ ya ∷ c₁ ∷ s ∷ e' ∷ δ) (R.quBody q))
        → ⟨ δ ⊨ R.quRel q ⟩
```

<!--en-->
No additional payload decomposition is needed for an unbounded quantifier: its payload `r` already is the child formula code. Consequently the general converse for a successor-arity subvalue has exactly the premise and conclusion required by `quRel`. Applying it once reconstructs the whole relation while preserving the universal reading over all matching table entries.
<!--zh-->
无界量词不需要额外分解载荷，因为其载荷 `r` 本身就是子公式码。因此，后继元数子值的一般反向读式具有 `quRel` 恰好所需的前提与结论；应用一次便能重建整个关系，同时保留对所有匹配表条目的全称读取。
<!--ja-->
非有界量化子では、ペイロード `r` 自体が子論理式の符号なので、追加のペイロード分解は要りません。したがって、後続アリティの子の値に対する一般の逆向きの読み取りは、`quRel` が必要とする前提と結論をそのまま持ちます。それを一度適用すれば、対応するすべての表の項目についての全称的な読みを保ったまま、関係全体が再構成されます。
<!--/-->

```agda
  qu-in q g = subSucAt-in (sh 12 T) i9 i3 (extB i6 i14 (R.quBody q)) δ g
```

<!--en-->
The bounded-quantifier payload has two syntactic components: the bound term code `t` and the child formula code `a`, so `r=(t,a)`. The child key is `c₁=(ar',a)` at successor arity, and its table value is `ya`. The four truncated witnesses record the payload pair, the child table member, and the two relevant pair decompositions. The resulting `Ext` fact characterizes the outer value `yc`; inside its body, the term code is evaluated and its value bounds the quantification.
<!--zh-->
有界量词的载荷有两个句法分量：界词项码 `t` 与子公式码 `a`，故 `r=(t,a)`。子公式键是在后继元数处的 `c₁=(ar',a)`，其表取值为 `ya`。四个见证在命题截断下打包在一起，记录载荷配对、子公式表成员与两个相关的配对分解。所得 `Ext` 事实刻画外层取值 `yc`；在其主体内部，词项码被求值，而所得词项值限制量化范围。
<!--ja-->
有界量化子のペイロードには、境界を与える項の符号 `t` と子論理式の符号 `a` という二つの構文的成分があり、`r=(t,a)` です。子の鍵は後続アリティにおける `c₁=(ar',a)` で、その表の値が `ya` です。切り詰められた四つの証人は、ペイロードの対、子の表の要素、および関係する二つの対分解を記録します。得られる `Ext` は外側の値 `yc` を特徴付け、その本体の中で項の符号が評価され、その値が量化の範囲を制限します。
<!--/-->

```agda
  bq-out : (q : ∀ {j} → Term S j → Formula S (suc j) → Formula S j)
         → (c : ∀ {j} → Formula S j → Formula S j → Formula S j) → ⟨ δ ⊨ R.bqRel q c ⟩
         → (t a c₁ ya ar' : S) → Rv ≡ pr (fst t) (fst a)
         → ⟨ pr (fst c₁) (fst ya) ∈ Tv ⟩ → fst c₁ ≡ pr (fst ar') (fst a) → fst ar' ≡ sucV A
         → ∥ Σ[ s ∈ S ] Σ[ s₁ ∈ S ] Σ[ s' ∈ S ] Σ[ e' ∈ S ]
```

<!--en-->
The proof packages exactly four witnesses: a container for `r=(t,a)`, a container and an actual table member for `(c₁,ya)`, and a container for `c₁=(ar',a)`. After `useBoth` opens the payload, `subSucAt-out` reads the child value at successor arity. The environment supplied to `Ext` adds nine local slots to the twelve-slot frame, and `Ext` itself places the candidate encoded environment `z` in one further head slot, matching the arity of `bqBody`.
<!--zh-->
证明恰好打包四个见证：`r=(t,a)` 的容器、配对 `(c₁,ya)` 的容器与实际表成员，以及 `c₁=(ar',a)` 的容器。`useBoth` 打开载荷后，`subSucAt-out` 在后继元数处读取子公式取值。传给 `Ext` 的环境在十二槽框架前增加九个局部槽位，而 `Ext` 自身再把候选编码环境 `z` 放入一个新的头槽，恰与 `bqBody` 的元数吻合。
<!--ja-->
証明がまとめる証人は正確に四つです。`r=(t,a)` のコンテナ、対 `(c₁,ya)` のコンテナと実際の表の要素、そして `c₁=(ar',a)` のコンテナです。`useBoth` がペイロードを開いた後、`subSucAt-out` が後続アリティにおける子の値を読みます。`Ext` に渡す環境は十二枠の前に九つの局所的な枠を加え、`Ext` 自身が候補となる符号化環境 `z` をさらに一つの先頭枠へ置くので、`bqBody` のアリティと一致します。
<!--/-->

```agda
             Ext (ar' ∷ s' ∷ ya ∷ c₁ ∷ s₁ ∷ e' ∷ a ∷ t ∷ s ∷ δ) (R.bqBody q c) ∥₁
  bq-out q c h t a c₁ ya ar' er mem e es =
    ∣ container r t a er .fst , container e'S c₁ ya refl .fst , container c₁ ar' a e .fst , e'S ,
      subSucAt-out (sh 15 T) i12 i0 (extB i9 i17 (R.bqBody q c)) δ15
        (useBoth i3 δ t a er (subSucAt (sh 15 T) i12 i0 (extB i9 i17 (R.bqBody q c))) h)
```

<!--en-->
Opening the payload extends the original frame by three slots: the child formula code `a`, the bound term code `t`, and a container witnessing `r=(t,a)`. This is the environment `δ15`. The notation records a fifteen-slot prefix over the original `m`-environment because `δ` already contained the twelve common frame slots.
<!--zh-->
打开载荷会在原框架前增加三个槽位：子公式码 `a`、界词项码 `t`，以及见证 `r=(t,a)` 的容器。这便是环境 `δ15`。该记号表示原 `m` 槽环境前共有十五个槽位，因为 `δ` 已经包含十二个共同框架槽。
<!--ja-->
ペイロードを開くと、元の枠の前に三つの枠が加わります。子論理式の符号 `a`、境界を与える項の符号 `t`、および `r=(t,a)` を証明するコンテナです。これが環境 `δ15` です。`δ` がすでに十二の共通枠を含むため、この記法は元の `m` 枠の環境の前に合計十五の枠があることを表します。
<!--/-->

```agda
        c₁ ya ar' mem e es ∣₁
    where
    δ15 : S ^ (15 + m)
    δ15 = a ∷ t ∷ container r t a er .fst ∷ δ
    e'S : S
```

<!--en-->
The hypothesis `mem` is membership of the underlying pair `(c₁,ya)` in the table set. Applying `down` at the shifted table slot realizes that proof as `e'S : S`, an actual table element with the required underlying set. This realization is local to the proof; it does not choose a child value from totality.
<!--zh-->
假设 `mem` 表示底层配对 `(c₁,ya)` 属于表集合。在移位后的表槽处应用 `down`，便把这条证明实现为 `e'S : S`，即具有所需底层集合的实际表元素。这个实现仅用于当前证明，并不是从全定义性中选择一个子公式取值。
<!--ja-->
仮定 `mem` は、基礎の対 `(c₁,ya)` が表の集合に属することを表します。移動後の表の枠で `down` を適用すると、この証明は必要な基礎の集合を持つ実際の表の要素 `e'S : S` として実現されます。この実現は証明の局所的なものであり、全域性から子の値を選ぶ操作ではありません。
<!--/-->

```agda
    e'S = down (lookup (sh 15 T) δ15) (pr (fst c₁) (fst ya)) mem

```

<!--en-->
The converse premise ranges over nine objects because it must accept every realization of the payload and child-table decompositions. Here `s₁` is a pair container for the table member, while `s'` is a container for the successor-arity child key; neither is the semantic witness bound by the quantified formula. Given the membership and pair equations, the premise supplies the `Ext` fact for `yc` and thereby determines the bounded relation locally.
<!--zh-->
反向前提量化九个对象，因为它必须接受载荷分解与子公式表分解的每一种实现。这里 `s₁` 是表成员的配对容器，`s'` 是后继元数子公式键的容器；二者都不是量化公式所约束的语义见证。在给定隶属证明与配对等式后，该前提提供关于 `yc` 的 `Ext` 事实，从而局部确定有界量词关系。
<!--ja-->
逆向きの前提が九つの対象を量化するのは、ペイロードと子の表の分解のあらゆる実現を受け取る必要があるためです。ここで `s₁` は表の要素の対コンテナ、`s'` は後続アリティの子の鍵のコンテナであり、どちらも量化された論理式が束縛する意味論的な証人ではありません。所属の証明と対の等式が与えられると、この前提は `yc` に関する `Ext` を与え、有界量化子の関係を局所的に定めます。
<!--/-->

```agda
  bq-in : (q : ∀ {j} → Term S j → Formula S (suc j) → Formula S j)
        → (c : ∀ {j} → Formula S j → Formula S j → Formula S j)
        → ((t a s c₁ ya ar' s₁ s' e' : S) → Rv ≡ pr (fst t) (fst a)
           → ⟨ fst e' ∈ Tv ⟩ → fst e' ≡ pr (fst c₁) (fst ya)
           → fst c₁ ≡ pr (fst ar') (fst a) → fst ar' ≡ sucV A
```

<!--en-->
To rebuild `bqRel`, `bothAll-in` first handles every decomposition `r=(t,a)` of the constructor payload. At that extended environment, `subSucAt-in` handles every table entry for the child key `(suc A,a)`. The supplied rule then proves the exact extension condition for `yc`; the semantic bound value itself is quantified later inside `bqBody`, where `tmIs` relates it to the term code `t`.
<!--zh-->
为重建 `bqRel`，`bothAll-in` 先处理构造子载荷的每个分解 `r=(t,a)`。在扩展后的环境中，`subSucAt-in` 再处理子公式键 `(suc A,a)` 的每个表条目。给定规则随后证明 `yc` 的精确外延条件；语义上的界值是在 `bqBody` 内部才被量化，并由 `tmIs` 把它与词项码 `t` 联系起来。
<!--ja-->
`bqRel` を組み直すため、`bothAll-in` はまず構成子のペイロードの各分解 `r=(t,a)` を扱います。その拡張環境で `subSucAt-in` が子の鍵 `(suc A,a)` に対するすべての表の項目を扱います。与えられた規則はそこで `yc` の正確な外延条件を証明します。意味論的な境界値そのものは、後で `bqBody` の内部で量化され、`tmIs` によって項の符号 `t` と結び付けられます。
<!--/-->

```agda
           → Ext (ar' ∷ s' ∷ ya ∷ c₁ ∷ s₁ ∷ e' ∷ a ∷ t ∷ s ∷ δ) (R.bqBody q c))
        → ⟨ δ ⊨ R.bqRel q c ⟩
  bq-in q c g = bothAll-in i3 (subSucAt (sh 15 T) i12 i0 (extB i9 i17 (R.bqBody q c))) δ
    (λ t a s s∈ t∈ a∈ er →
      subSucAt-in (sh 15 T) i12 i0 (extB i9 i17 (R.bqBody q c)) (a ∷ t ∷ s ∷ δ)
```

<!--en-->
At the innermost stage all structural obligations have become explicit: the payload is `(t,a)`, the child table member is `(c₁,ya)`, its key is `(ar',a)`, and `ar'` is the successor of `A`. These are exactly the hypotheses of the assumed rule `g`, so its extension fact closes the successor-arity subvalue clause. No assertion about the uniqueness of `ya` is used in this reconstruction.
<!--zh-->
到最内层时，所有结构义务都已显式给出：载荷为 `(t,a)`，子公式表成员为 `(c₁,ya)`，其键为 `(ar',a)`，且 `ar'` 是 `A` 的后继。这些恰是规则 `g` 的假设，故它给出的外延事实可以闭合后继元数子值子句。此处的重建不使用任何关于 `ya` 唯一性的断言。
<!--ja-->
最も内側の段階では、構造上の義務がすべて明示されています。ペイロードは `(t,a)`、子の表の要素は `(c₁,ya)`、その鍵は `(ar',a)` であり、`ar'` は `A` の後続です。これらは仮定した規則 `g` の前提と正確に一致するため、`g` の与える外延条件が後続アリティの子の値の節を閉じます。この再構成では `ya` の一意性をまったく用いません。
<!--/-->

```agda
        (λ c₁ ya ar' s₁ s' e' e'∈ ee e es → g t a s c₁ ya ar' s₁ s' e' er e'∈ ee e es))
```

<!--en-->
For an atomic formula, `t` and `u` are the two term codes stored in the payload, not their semantic values. Opening `r=(t,u)` contributes one pair container and leaves an `Ext` fact for the outer table value `yc`. The formula `atomBody` evaluated there will separately quantify candidate values of the two terms, verify them with `tmIs`, and apply the chosen atomic relation.
<!--zh-->
对原子公式而言，`t` 与 `u` 是载荷中存放的两个词项码，而不是它们的语义取值。打开 `r=(t,u)` 会加入一个配对容器，并留下关于外层表取值 `yc` 的 `Ext` 事实。在该环境中求值的 `atomBody` 会另行量化两个词项的候选取值，用 `tmIs` 验证它们，再应用选定的原子关系。
<!--ja-->
原子論理式では、`t` と `u` はペイロードに格納された二つの項の符号であり、それらの意味論的な値ではありません。`r=(t,u)` を開くと一つの対コンテナが加わり、外側の表の値 `yc` に関する `Ext` が残ります。その環境で評価される `atomBody` は、二つの項の候補値を別に量化し、`tmIs` で検証してから、選ばれた原子関係を適用します。
<!--/-->

```agda
  atom-out : (rel : Formula S (18 + m)) → ⟨ δ ⊨ R.atomRel rel ⟩
           → (t u : S) → Rv ≡ pr (fst t) (fst u)
           → ∥ Σ[ s ∈ S ] Ext (u ∷ t ∷ s ∷ δ) (R.atomBody rel) ∥₁
  atom-out rel h t u er = ∣ container r t u er .fst , useBoth i3 δ t u er (extB i3 i11 (R.atomBody rel)) h ∣₁

```

<!--en-->
Conversely, assume the extension condition can be proved for every decomposition of the payload into term codes `t` and `u` and every accompanying pair container. The bounded-universal introduction reconstructs that payload decomposition and hence the atomic relation. The later existential choices of actual term values remain inside `atomBody`; they are not parameters of `atom-in`.
<!--zh-->
反过来，假定对载荷分解为词项码 `t`、`u` 的每一种方式及每个相伴配对容器，都能证明所需的外延条件。有界全称引入据此重建载荷分解，从而构造原子关系。词项实际取值的存在选择仍位于 `atomBody` 内部，并不是 `atom-in` 的参数。
<!--ja-->
逆に、ペイロードを項の符号 `t` と `u` に分解するすべての場合と、それに伴うすべての対コンテナについて、必要な外延条件を証明できると仮定します。有界全称の導入がこのペイロード分解を組み直し、原子関係を構成します。項の実際の値に対する存在的な選択は `atomBody` の内部に残り、`atom-in` の引数ではありません。
<!--/-->

```agda
  atom-in : (rel : Formula S (18 + m))
          → ((t u s : S) → Rv ≡ pr (fst t) (fst u) → Ext (u ∷ t ∷ s ∷ δ) (R.atomBody rel))
          → ⟨ δ ⊨ R.atomRel rel ⟩
  atom-in rel g = bothAll-in i3 (extB i3 i11 (R.atomBody rel)) δ (λ t u s s∈ t∈ u∈ er → g t u s er)
```

<!--en-->
## Bridging clauses to semantic satisfaction
<!--zh-->
## 从子句桥接到语义满足关系
<!--ja-->
## 節から意味論的充足へ橋渡しする
<!--/-->

<!--en-->
The relation readings are complete: each constructor's clause has been converted into its extension fact, and each extension fact into its clause. The chapter now turns to the bridge that connects these object-language relations to the meta-level satisfaction semantics.
<!--zh-->
关系读法完毕：每个构造子的子句已被转换为外延事实，每个外延事实也被转换为子句。本章随即转向把这些对象语言关系与元层满足语义相连接的桥。
<!--ja-->
関係の読み出しは完成です。それぞれの構成子の節が外延の事実へ変換され、それぞれの外延の事実が節へ変換されました。本章はここから、これらの対象言語の関係を、メタレベルの充足の意味論へ結ぶ橋に移ります。
<!--/-->

```agda
open import FOL.Manipulation.ConstantMapping using ( mapFo; mapTm )
open import L.Coding.Satisfaction {ℓ} lem using ( Sat; Sat-mem; cond )
open import L.Coding.SatisfactionBridge {ℓ} lem using ( asConst )
import L.Coding.SatisfactionBridge {ℓ} lem as Semantic
```

<!--en-->
The bridge module is parameterized by a set `W` of the hierarchy whose members form the constant alphabet of the internal language. The definability and semantic modules are opened at `W`, so that formulas over the alphabet `Ab` can be interpreted in the small model carried by `W`.
<!--zh-->
桥模块以层级的一个集合 `W` 为参数，其成员构成内部语言的常元字母表。可定义性与语义模块在 `W` 处打开，使字母表 `Ab` 上的公式能在 `W` 携带的小模型中解释。
<!--ja-->
橋のモジュールは、階層の集合 `W` をパラメータとします。その要素が内部言語の定数のアルファベットをなします。定義可能性と意味論のモジュールが `W` で開かれ、アルファベット `Ab` の上の論理式が、`W` が担う小さなモデルの中で解釈できるようにします。
<!--/-->

```agda

module Bridge (W : S) where
  open Alphabet W
  private
    module DB = Semantic.DB W
    module Sem = Semantic.SemB W
```

<!--en-->
The small model's satisfaction judgment is renamed to `⊨ᴮ` and its term valuation to `⟦_⟧ᴮ`, so the bridge can distinguish them from the ambient-hierarchy satisfaction `⊨` used earlier in the chapter.
<!--zh-->
小模型的满足判断被改名为 `⊨ᴮ`，其词项赋值被改名为 `⟦_⟧ᴮ`，使桥接论证能够把二者与本章先前使用的外围层级满足 `⊨` 区分开来。
<!--ja-->
小モデルの充足判断を `⊨ᴮ`、項の値づけを `⟦_⟧ᴮ` と改名します。これにより、橋渡しの議論では、この二つを章の前半で使った周囲の階層の充足 `⊨` と区別できます。
<!--/-->

```agda
    open Sem.At DB.SM id using () renaming ( _⊨_ to _⊨ᴮ_ ; ⟦_⟧ to ⟦_⟧ᴮ )

```

<!--en-->
The meta-level meaning of a formula `ψ` at a meta-level environment `δ` is the satisfaction of the constant-relabeled formula in the small model carried by `W`. This is the target semantics that the bridges will relate to the object-language table entries.
<!--zh-->
公式 `ψ` 在元层环境 `δ` 处的元层意义，是该公式经常元改名后在 `W` 携带的小模型中的满足。这正是各桥要将对象语言表条目与之关联的目标语义。
<!--ja-->
論理式 `ψ` のメタレベルの環境 `δ` での意味論的な意味は、定数を付け替えた論理式が、`W` が担う小さなモデルの中で充足されることです。これが、橋が対象言語の表の項目を結びつける目標の意味論です。
<!--/-->

```agda
    Meaning : ∀ {n} → Formula Ab n → DB.SM ^ n → hProp (ℓ-suc ℓ)
    Meaning ψ δ = δ ⊨ᴮ mapFo DB.ι ψ

```

<!--en-->
The underlying set `Wv` is the carrier over which the small-model quantifiers range. Keeping it separate from the presentation `W : S` matters in the later bridges: object-language membership uses the set `Wv`, while constructibility evidence remains in the second component of `W`. Thus the bridges quantify over members of the fixed model, not over every constructible set.
<!--zh-->
底层集合 `Wv` 是小模型量词的取值载体。把它与呈现 `W : S` 区分开来，对后续桥接很重要：对象语言的隶属使用集合 `Wv`，而可构造性证据保留在 `W` 的第二分量中。因此，各桥只对固定模型的成员量化，而不是对所有可构造集合量化。
<!--ja-->
基礎の集合 `Wv` は、小モデルの量化子が走る台です。これを表示 `W : S` と区別しておくことは、後の橋にとって重要です。対象言語の所属は集合 `Wv` を使い、構成可能性の証拠は `W` の第二成分に残ります。したがって橋が量化するのは固定されたモデルの要素であり、すべての構成可能集合ではありません。
<!--/-->

```agda
  private
    Wv = fst W

```

<!--en-->
The map `toS` relabels every constant of a formula over the alphabet `Ab` into the corresponding constant of the structure `S`, producing a formula over `S` that can be judged by the ambient satisfaction.
<!--zh-->
映射 `toS` 把字母表 `Ab` 上公式的每个常元改名为结构 `S` 的相应常元，产出的 `S` 上公式可由环境满足判断。
<!--ja-->
対応 `toS` は、アルファベット `Ab` の上の論理式のすべての定数を、構造 `S` の対応する定数へ付け替え、周囲の充足で判定できる `S` の上の論理式を作ります。
<!--/-->

```agda
  toS : ∀ {n} → Formula Ab n → Formula S n
  toS = mapFo (asConst W)

```

<!--en-->
The constructible satisfaction set `SatW ψ` collects the coded environments that satisfy the relabeled formula. It is an element of `L`, being the output of the internal recursion that defines satisfaction.
<!--zh-->
可构造满足集 `SatW ψ` 收集满足改名后公式的编码环境。它是 `L` 的元素，因为它是定义满足的内部递归的输出。
<!--ja-->
構成可能な充足集合 `SatW ψ` は、付け替えられた論理式を満たす符号化された環境を集めます。それは充足を定義する内部の再帰の出力なので、`L` の要素です。
<!--/-->

```agda
  SatW : ∀ {n} → Formula Ab n → S
  SatW ψ = Sat W (toS ψ)
```

<!--en-->
The outward reading of membership in `SatW ψ` follows from the membership specification of the internal satisfaction: a member of `SatW ψ` is a coded environment that lies in the environment set at the correct arity and satisfies the relabeled formula's condition.
<!--zh-->
`SatW ψ` 中隶属的向外读法来自内部满足的隶属规格：`SatW ψ` 的成员是一个编码环境，它属于正确元数的环境集，并满足改名后公式的条件。
<!--ja-->
`SatW ψ` への所属の外向きの読み出しは、内部の充足の所属の仕様から従います。`SatW ψ` の要素は、正しいアリティの環境の集合に属し、付け替えられた論理式の条件を満たす、符号化された環境です。
<!--/-->

```agda
  Sat-out : ∀ {n} (ψ : Formula Ab n) (z : S) → ⟨ fst z ∈ fst (SatW ψ) ⟩
          → ⟨ fst z ∈ fst (envSet W n) ⟩ × ⟨ (z ∷ []) ⊨ cond W (toS ψ) ⟩
  Sat-out ψ z h = subst ⟨_⟩ (Sat-mem W (toS ψ) z) h

```

<!--en-->
The inward direction starts from membership in the correct environment set together with the recursive condition, transports that pair backward along `Sat-mem`, and obtains membership in `SatW ψ`. Thus `Sat-out` and `Sat-in` are exactly the two transports supplied by the membership specification; they require no additional semantic hypothesis.
<!--zh-->
向内方向从「属于正确的环境集」与「满足递归条件」这两个事实出发，把它们沿 `Sat-mem` 反向搬运，从而得到属于 `SatW ψ`。因此，`Sat-out` 与 `Sat-in` 恰是隶属规格所给路径的两个搬运方向，不需要额外的语义假设。
<!--ja-->
内向きの方向は、正しい環境集合への所属と再帰条件という二つの事実から出発し、その対を `Sat-mem` に沿って逆向きに輸送することで `SatW ψ` への所属を得ます。したがって `Sat-out` と `Sat-in` は、所属の仕様が与えるパスに沿う二方向の輸送そのものであり、追加の意味論的仮定を必要としません。
<!--/-->

```agda
  Sat-in : ∀ {n} (ψ : Formula Ab n) (z : S) → ⟨ fst z ∈ fst (envSet W n) ⟩
         → ⟨ (z ∷ []) ⊨ cond W (toS ψ) ⟩ → ⟨ fst z ∈ fst (SatW ψ) ⟩
  Sat-in ψ z hz hc = subst ⟨_⟩ (sym (Sat-mem W (toS ψ) z)) (hz , hc)
```

<!--en-->
The lemma `extension-path` turns a pointwise path of truth values into an exact extension theorem for `SatW ψ`. For each encoded environment `z`, its premise identifies the recursive condition `cond W (toS ψ)` with the target proposition `P z`. Using the two directions of `Sat-mem`, the conclusion says that the members of `SatW ψ` are exactly the members of `envSet W n` satisfying `P`; it neither decodes `z` nor chooses a representative environment vector.
<!--zh-->
引理 `extension-path` 把逐点的真值路径转化为关于 `SatW ψ` 的精确外延定理。对每个编码环境 `z`，其前提把递归条件 `cond W (toS ψ)` 与目标命题 `P z` 识别起来。借助 `Sat-mem` 的两个方向，结论说明 `SatW ψ` 的成员恰是 `envSet W n` 中满足 `P` 的成员；这里既不解码 `z`，也不选择环境向量的代表。
<!--ja-->
補題 `extension-path` は、各点における真理値のパスを `SatW ψ` の正確な外延定理へ変えます。符号化された各環境 `z` について、その前提は再帰条件 `cond W (toS ψ)` を目標命題 `P z` と同定します。`Sat-mem` の二方向を用いると、結論は `SatW ψ` の要素が、`P` を満たす `envSet W n` の要素にちょうど一致すると述べます。ここでは `z` を復号せず、環境ベクトルの代表も選びません。
<!--/-->

```agda
  private
    extension-path : ∀ {n} (ψ : Formula Ab n) (P : S → hProp (ℓ-suc ℓ))
                   → ((z : S) → ((z ∷ []) ⊨ cond W (toS ψ)) ≡ P z)
                   → ExtFact (fst (SatW ψ)) (fst (envSet W n)) (λ z → ⟨ P z ⟩)
    extension-path ψ P e =
```

<!--en-->
The outward direction reads the two components of membership in `SatW ψ` through `Sat-out` and transports the condition along the pointwise equality. The inward direction transports the property back and applies `Sat-in`. Both directions use only the pointwise equality, not any choice of representatives.
<!--zh-->
向外方向经 `Sat-out` 读取 `SatW ψ` 中隶属的两个分量，并沿逐点等式运输条件。向内方向把性质运回并应用 `Sat-in`。两个方向都只使用逐点等式，不选取任何代表。
<!--ja-->
外向きの方向は、`Sat-out` を通して `SatW ψ` への所属の二つの成分を読み、各点の等式に沿って条件を運びます。内向きの方向は、性質を運び戻して `Sat-in` を適用します。どちらの方向も、代表を選ぶことなく、各点の等式だけを使います。
<!--/-->

```agda
        (λ z hz → Sat-out ψ z hz .fst , subst ⟨_⟩ (e z) (Sat-out ψ z hz .snd))
      , (λ z hz hp → Sat-in ψ z hz (subst ⟨_⟩ (sym (e z)) hp))
```

<!--en-->
For falsity, the target property has no inhabitants for any `z`. If `z` belonged to `SatW ⊥̇`, `Sat-out` would expose the impossible satisfaction of falsity; conversely, an assumed proof of that impossible property eliminates the candidate immediately. The remaining component merely records that every hypothetical member would have the correct arity, so `botBridge` gives the empty extension inside `envSet W n`.
<!--zh-->
对假式而言，目标性质对任何 `z` 都没有元素。若 `z` 属于 `SatW ⊥̇`，`Sat-out` 会给出不可能成立的假式满足；反过来，假定有这项不可能的性质，便可立即消去候选。剩余分量只记录每个假想成员都会具有正确元数，因此 `botBridge` 给出 `envSet W n` 内的空外延。
<!--ja-->
偽の場合、目標の性質はどの `z` に対しても要素を持ちません。もし `z` が `SatW ⊥̇` に属すれば、`Sat-out` は不可能な偽の充足を取り出します。逆に、その不可能な性質の証明を仮定すれば、候補は直ちに除去できます。残る成分は、仮に要素があれば正しいアリティを持つことを記録するだけなので、`botBridge` は `envSet W n` の内部で空の外延を与えます。
<!--/-->

```agda
  botBridge : (n : ℕ) {k : ℕ} (env : S ^ k)
            → ExtFact (fst (SatW (⊥̇ {n = n}))) (fst (envSet W n)) (λ z → ⟨ (z ∷ env) ⊨ ⊥̇ ⟩)
  botBridge n env = (λ z hz → Sat-out ⊥̇ z hz .fst , Sat-out ⊥̇ z hz .snd) , (λ z hz b → ⊥*-rec b)
```

<!--en-->
Assume slots `ya` and `yb` of `env` contain the underlying satisfaction sets of `a` and `b`. The conjunction bridge then characterizes `SatW (a ∧̇ b)` as the encoded environments `z` belonging to both child sets. Since `z` is prepended before the body is evaluated, the old slots are addressed as `suc ya` and `suc yb`, while `i0` names `z`; this shift is exactly the host `Fin` boundary recorded in the displayed formula.
<!--zh-->
假定 `env` 的槽位 `ya` 与 `yb` 分别承载 `a`、`b` 的满足集之底层集合。合取桥于是把 `SatW (a ∧̇ b)` 刻画为同时属于两个子公式满足集的编码环境 `z`。由于求值主体前先把 `z` 加到环境头部，原槽位改由 `suc ya`、`suc yb` 读取，而 `i0` 指向 `z`；这次移位正是所示公式记录的宿主 `Fin` 边界。
<!--ja-->
`env` の枠 `ya` と `yb` が、それぞれ `a` と `b` の充足集合の基礎の集合を持つと仮定します。連言の橋は `SatW (a ∧̇ b)` を、二つの子の充足集合の両方に属する符号化環境 `z` として特徴付けます。本体を評価する前に `z` が環境の先頭へ加えられるため、元の枠は `suc ya` と `suc yb` で参照され、`i0` が `z` を指します。この移動が、表示された論理式に記録されたホスト側の `Fin` 境界です。
<!--/-->

```agda
  andBridge : ∀ {n} (a b : Formula Ab n) {k : ℕ} (env : S ^ k) (ya yb : Fin k)
            → fst (lookup ya env) ≡ fst (SatW a) → fst (lookup yb env) ≡ fst (SatW b)
            → ExtFact (fst (SatW (a ∧̇ b))) (fst (envSet W n))
                (λ z → ⟨ (z ∷ env) ⊨ (var i0 ∈̇ var (suc ya)) ∧̇ (var i0 ∈̇ var (suc yb)) ⟩)
  andBridge a b env ya yb qa qb = extension-path (a ∧̇ b)
```

<!--en-->
For conjunction, the pointwise path compares two descriptions of the same candidate environment `z`. The recursive condition says that `z` belongs to both `SatW a` and `SatW b`; transporting those two memberships along `qa` and `qb` gives exactly the two object-language membership atoms in the clause body. No child environment is decoded at this step.
<!--zh-->
对合取而言，这条逐点路径比较同一个候选环境 `z` 的两种描述。递归条件说 `z` 同时属于 `SatW a` 与 `SatW b`；沿 `qa` 和 `qb` 传输这两份隶属，恰好得到子句主体中的两条对象语言隶属原子。这一步不解码任何子环境。
<!--ja-->
連言では、点ごとのパスが同じ候補環境 `z` の二つの記述を比較します。再帰条件は `z` が `SatW a` と `SatW b` の両方に属すことを述べ、二つの所属を `qa` と `qb` に沿って輸送すると、節の本体にある二つの対象言語の所属原子がちょうど得られます。この段階では子環境を復号しません。
<!--/-->

```agda
    (λ z → (z ∷ env) ⊨ (var i0 ∈̇ var (suc ya)) ∧̇ (var i0 ∈̇ var (suc yb)))
    (λ z i → (fst z ∈ sym qa i) ⊓ (fst z ∈ sym qb i))

```

<!--en-->
The disjunction bridge gives an exact extension description. An environment belongs to `SatW (a ∨̇ b)` exactly when it lies in `envSet W n` and, after being placed at the head of the clause environment, satisfies the object-language disjunction saying that it belongs to the value of `a` or to the value of `b`.
<!--zh-->
析取桥接给出一条精确的外延描述。一个环境属于 `SatW (a ∨̇ b)`，当且仅当它属于 `envSet W n`，并且把它放在子句环境首部后，满足对象语言析取：它属于 `a` 的值或属于 `b` 的值。
<!--ja-->
選言の橋渡しは正確な外延記述を与えます。ある環境が `SatW (a ∨̇ b)` に属すのは、それが `envSet W n` に属し、さらに節の環境の先頭に置いたとき、`a` の値または `b` の値に属すという対象言語の選言を満たすとき、そのときに限ります。
<!--/-->

```agda
  orBridge : ∀ {n} (a b : Formula Ab n) {k : ℕ} (env : S ^ k) (ya yb : Fin k)
           → fst (lookup ya env) ≡ fst (SatW a) → fst (lookup yb env) ≡ fst (SatW b)
           → ExtFact (fst (SatW (a ∨̇ b))) (fst (envSet W n))
               (λ z → ⟨ (z ∷ env) ⊨ (var i0 ∈̇ var (suc ya)) ∨̇ (var i0 ∈̇ var (suc yb)) ⟩)
  orBridge a b env ya yb qa qb = extension-path (a ∨̇ b)
```

<!--en-->
The pointwise comparison for disjunction transports membership of the same `z` along the two slot equations. Its two alternatives are membership in `SatW a` and membership in `SatW b`; the object-language disjunction records precisely that alternative, without producing an additional environment witness.
<!--zh-->
析取的逐点比较沿两条槽位等式传输同一个 `z` 的隶属。两种可能分别是 `z` 属于 `SatW a` 与 `z` 属于 `SatW b`；对象语言析取准确记录这一选择，并不产生额外的环境见证。
<!--ja-->
選言の点ごとの比較は、同じ `z` の所属を二つのスロット等式に沿って輸送します。二つの選択肢は `z` の `SatW a` への所属と `SatW b` への所属であり、対象言語の選言はこの選択を正確に記録します。ここで別の環境の証人が作られることはありません。
<!--/-->

```agda
    (λ z → (z ∷ env) ⊨ (var i0 ∈̇ var (suc ya)) ∨̇ (var i0 ∈̇ var (suc yb)))
    (λ z i → (fst z ∈ sym qa i) ⊔ (fst z ∈ sym qb i))

```

<!--en-->
The implication bridge likewise characterizes `SatW (a ⇒̇ b)` inside the environment set. At a candidate environment `z`, its clause body says that membership of `z` in the value of the antecedent entails membership of that same `z` in the value of the consequent.
<!--zh-->
蕴涵桥接同样在环境集合之内刻画 `SatW (a ⇒̇ b)`。对候选环境 `z`，子句主体说：若 `z` 属于前件的值，则同一个 `z` 属于后件的值。
<!--ja-->
含意の橋渡しも、環境集合の内部で `SatW (a ⇒̇ b)` を特徴づけます。候補環境 `z` における節の本体は、`z` が前件の値に属すならば、同じ `z` が後件の値に属すと述べます。
<!--/-->

```agda
  impBridge : ∀ {n} (a b : Formula Ab n) {k : ℕ} (env : S ^ k) (ya yb : Fin k)
            → fst (lookup ya env) ≡ fst (SatW a) → fst (lookup yb env) ≡ fst (SatW b)
            → ExtFact (fst (SatW (a ⇒̇ b))) (fst (envSet W n))
                (λ z → ⟨ (z ∷ env) ⊨ (var i0 ∈̇ var (suc ya)) ⇒̇ (var i0 ∈̇ var (suc yb)) ⟩)
  impBridge a b env ya yb qa qb = extension-path (a ⇒̇ b)
```

<!--en-->
The required path is pointwise: `qa` and `qb` rename the antecedent and consequent value slots as `SatW a` and `SatW b`. Transporting along those equations turns the object-language implication into the recursive condition for implication, with no change of environment.
<!--zh-->
这里所需的是逐点路径：`qa` 与 `qb` 分别把前件和后件的值槽指认为 `SatW a` 与 `SatW b`。沿这两条等式传输后，对象语言蕴涵就成为蕴涵的递归条件，环境本身没有改变。
<!--ja-->
ここで必要なのは点ごとのパスです。`qa` と `qb` は前件と後件の値のスロットをそれぞれ `SatW a` と `SatW b` と同定します。これらの等式に沿って輸送すると、対象言語の含意は含意の再帰条件となり、環境そのものは変わりません。
<!--/-->

```agda
    (λ z → (z ∷ env) ⊨ (var i0 ∈̇ var (suc ya)) ⇒̇ (var i0 ∈̇ var (suc yb)))
    (λ z i → (fst z ∈ sym qa i) ⇒ (fst z ∈ sym qb i))

```

<!--en-->
Both unbounded quantifier bodies range first over the carrier named by `wi`. The existential body asks for some carrier member `x`, while the universal body treats every such `x`; in either case an inner bounded existential chooses an entry of the child value and requires it to be the graph obtained by consing `x` onto the old environment.
<!--zh-->
两种无界量词主体都先在 `wi` 指名的载体上量化。存在主体要求某个载体成员 `x`，全称主体则处理每个这样的 `x`；两者的内层都有一个有界存在，它从子公式的值中取一个条目，并要求该条目是把 `x` 添加到旧环境前端所得的图。
<!--ja-->
二つの非有界量化子の本体は、まず `wi` が名指す台の上で量化します。存在の本体は台のある要素 `x` を求め、全称の本体はそのようなすべての `x` を扱います。どちらの場合も内側の有界存在が子論理式の値から項目を取り、それが `x` を古い環境の先頭に加えて得られるグラフであることを要求します。
<!--/-->

```agda
  quEx quAll : ∀ {k} → Fin k → Fin k → Formula S (1 + k)
  quEx wi yai = ∃̇∈ (var (suc wi)) (∃̇∈ (var (suc (suc yai))) (consAtL i0 i1 i2))
  quAll wi yai = ∀̇∈ (var (suc wi)) (∃̇∈ (var (suc (suc yai))) (consAtL i0 i1 i2))
```

<!--en-->
The lemma `direct-extension` isolates the argument shared by the quantifier and atom bridges. Once `z` is identified with the graph of a vector `δ`, it asks for maps in both directions between `Meaning ψ δ` and the proposed clause property `P z`; from them it proves that `SatW ψ` is exactly the part of `envSet W n` satisfying `P`. Recovery of `δ` remains truncated throughout.
<!--zh-->
引理 `direct-extension` 抽出量词桥接与原子桥接共有的论证。一旦 `z` 被认作某个向量 `δ` 的图，它要求在 `Meaning ψ δ` 与拟议的子句性质 `P z` 之间给出两个方向的映射；由此证明 `SatW ψ` 恰是 `envSet W n` 中满足 `P` 的部分。对 `δ` 的恢复始终留在截断之内。
<!--ja-->
補題 `direct-extension` は、量化子と原子の橋渡しに共通する議論を取り出します。`z` がベクトル `δ` のグラフと同定されたなら、`Meaning ψ δ` と節が表す性質 `P z` の間の両方向の写像を仮定し、`SatW ψ` が `envSet W n` のうち `P` を満たす部分にちょうど等しいことを示します。`δ` の復元は終始切り詰めの内側に保たれます。
<!--/-->

```agda
  private
    direct-extension : ∀ {n} (ψ : Formula Ab n) (P : S → hProp (ℓ-suc ℓ))
      → ((δ : DB.SM ^ n) (z : S) → fst z ≡ Semantic.graph W δ → ⟨ Meaning ψ δ ⟩ → ⟨ P z ⟩)
      → ((δ : DB.SM ^ n) (z : S) → fst z ≡ Semantic.graph W δ → ⟨ P z ⟩ → ⟨ Meaning ψ δ ⟩)
      → ExtFact (fst (SatW ψ)) (fst (envSet W n)) (λ z → ⟨ P z ⟩)
```

<!--en-->
For the outward half, `Sat-out` first supplies membership of `z` in the environment set. The truncated recovery theorem then gives a vector `δ` and an equation identifying `z` with its graph; inside the proposition `P z`, `Sat-small-spec` changes the original membership in `SatW ψ` into `Meaning ψ δ`, and the forward hypothesis finishes the argument.
<!--zh-->
在向外的一半中，`Sat-out` 先给出 `z` 属于环境集合。随后，截断的恢复定理给出向量 `δ` 以及把 `z` 认作其图的等式；在命题 `P z` 内，`Sat-small-spec` 把原来的 `z ∈ SatW ψ` 转成 `Meaning ψ δ`，再由前向假设完成论证。
<!--ja-->
外向きの半分では、まず `Sat-out` が `z` の環境集合への所属を与えます。次に切り詰められた復元定理から、ベクトル `δ` と `z` をそのグラフに同定する等式を得ます。命題 `P z` の内部で `Sat-small-spec` が元の `z ∈ SatW ψ` を `Meaning ψ δ` に移し、前向きの仮定が議論を終えます。
<!--/-->

```agda
    direct-extension {n} ψ P f b = out , inn
      where
      out : (z : S) → ⟨ fst z ∈ fst (SatW ψ) ⟩ → ⟨ fst z ∈ fst (envSet W n) ⟩ × ⟨ P z ⟩
      out z hz = Sat-out ψ z hz .fst , rec₁ (snd (P z))
        (λ { (δ , q) → f δ z q (subst ⟨_⟩ (Semantic.Sat-small-spec W ψ δ z q) hz) })
```

<!--en-->
For the inward half, membership in the environment set again yields only a truncated pair `δ , q`. The backward hypothesis sends `P z` to `Meaning ψ δ`, and the inverse direction of `Sat-small-spec` returns membership in `SatW ψ`. This elimination is valid because the membership goal is a proposition, so no global choice of a decoding vector is made.
<!--zh-->
在向内的一半中，属于环境集合仍只给出截断的 `δ , q`。反向假设把 `P z` 送到 `Meaning ψ δ`，再沿 `Sat-small-spec` 的逆向得到 `z ∈ SatW ψ`。由于目标隶属是命题，这次截断消去是合法的，也没有全局选取解码向量。
<!--ja-->
内向きの半分でも、環境集合への所属から得られるのは切り詰められた組 `δ , q` だけです。逆向きの仮定が `P z` を `Meaning ψ δ` に送り、`Sat-small-spec` の逆向きが `z ∈ SatW ψ` を返します。目標の所属は命題なので、この切り詰めの消去は正当であり、復号ベクトルを大域的に選ぶことはありません。
<!--/-->

```agda
        (Semantic.envSet-vectors W z (Sat-out ψ z hz .fst))
      inn : (z : S) → ⟨ fst z ∈ fst (envSet W n) ⟩ → ⟨ P z ⟩ → ⟨ fst z ∈ fst (SatW ψ) ⟩
      inn z hz hp = rec₁ (snd (fst z ∈ fst (SatW ψ)))
        (λ { (δ , q) → subst ⟨_⟩ (sym (Semantic.Sat-small-spec W ψ δ z q)) (b δ z q hp) })
        (Semantic.envSet-vectors W z hz)
```

<!--en-->
The lemma `child` aligns the encoded and semantic views of one bound variable. If the old coded environment is the graph of `δ` and the named child value is `SatW a`, then saying that some member of that child value is the graph obtained by consing `x` onto the old environment is propositionally equal to `Meaning a (x ∷ δ)`.
<!--zh-->
引理 `child` 对齐一个约束变元的编码读法与语义读法。若旧编码环境是 `δ` 的图，且被指名的子公式值为 `SatW a`，那么「子公式值的某个成员是把 `x` 添加到旧环境前端所得的图」与 `Meaning a (x ∷ δ)` 命题相等。
<!--ja-->
補題 `child` は、一つの束縛変数について符号化された見方と意味論的な見方をそろえます。古い符号化環境が `δ` のグラフであり、名指された子論理式の値が `SatW a` なら、その値のある要素が `x` を古い環境の先頭に加えて得られるグラフであるという主張は、`Meaning a (x ∷ δ)` と命題として等しくなります。
<!--/-->

```agda

    child : ∀ {n k} (a : Formula Ab (suc n)) (δ : DB.SM ^ n) (x : DB.SM)
      (γ : S ^ k) (zi yai : Fin k) → fst (lookup zi γ) ≡ Semantic.graph W δ
      → fst (lookup yai γ) ≡ fst (SatW a)
      → ((Semantic.intoL W x ∷ γ) ⊨ ∃̇∈ (var (suc yai)) (consAtL i0 i1 (sh 2 zi)))
        ≡ Meaning a (x ∷ δ)
```

<!--en-->
The proof is a pair of implications joined by `⇔toPath`. The outward direction consumes the truncated witness of the bounded existential: an entry of the child value together with evidence from `consAtL` that this entry is the graph obtained by consing `x` onto the old environment.
<!--zh-->
证明是由 `⇔toPath` 连接的一对蕴涵。向外方向消去有界存在的截断见证：子公式值中的一个条目，以及 `consAtL` 给出的证据，说明该条目正是把 `x` 添加到旧环境前端所得的图。
<!--ja-->
証明は `⇔toPath` で結ばれた一対の含意です。外向きの方向では、有界存在の切り詰められた証人を消去します。その証人は、子論理式の値に属する一つの項目と、その項目が `x` を古い環境の先頭に加えて得られるグラフであることを示す `consAtL` の証拠です。
<!--/-->

```agda
    child a δ x γ zi yai qz qa = ⇔toPath out inn
      where
      out : ⟨ (Semantic.intoL W x ∷ γ) ⊨ ∃̇∈ (var (suc yai)) (consAtL i0 i1 (sh 2 zi)) ⟩
          → ⟨ Meaning a (x ∷ δ) ⟩
      out = rec₁ (snd (Meaning a (x ∷ δ))) (λ { (e , he , hc) →
```

<!--en-->
In the outward direction, the bounded existential is eliminated into the proposition `Meaning a (x ∷ δ)`. The cons clause and the equation for the old graph identify its witness `e` with the graph of `x ∷ δ`; after `qa` turns `e`'s membership into membership in `SatW a`, `Sat-small-spec` yields the desired semantic satisfaction.
<!--zh-->
在向外方向，有界存在被消去到命题 `Meaning a (x ∷ δ)` 中。序接子句连同旧图的等式，把见证 `e` 认作 `x ∷ δ` 的图；再由 `qa` 把 `e` 的隶属改写为属于 `SatW a`，`Sat-small-spec` 随即给出所需的语义满足。
<!--ja-->
外向きには、有界存在を命題 `Meaning a (x ∷ δ)` の中へ消去します。先頭追加の節と古いグラフの等式によって、証人 `e` は `x ∷ δ` のグラフと同定されます。さらに `qa` が `e` の所属を `SatW a` への所属に書き換え、`Sat-small-spec` が求める意味論的充足を与えます。
<!--/-->

```agda
        subst ⟨_⟩ (Semantic.Sat-small-spec W a (x ∷ δ) e
          (Semantic.consAtL-out W δ x (e ∷ Semantic.intoL W x ∷ γ) i0 i1 (sh 2 zi) qz refl hc))
          (subst (λ X → ⟨ fst e ∈ X ⟩) qa he) })
      inn : ⟨ Meaning a (x ∷ δ) ⟩
          → ⟨ (Semantic.intoL W x ∷ γ) ⊨ ∃̇∈ (var (suc yai)) (consAtL i0 i1 (sh 2 zi)) ⟩
```

<!--en-->
The inward direction builds the canonical extension environment `envFor W (x ∷ δ)`. Reading the small-spec path backward turns the semantic satisfaction into membership of this environment in `SatW a`; `consAtL-in` then proves that the same environment has the required graph-extension relation to the old one.
<!--zh-->
向内方向构造典范扩展环境 `envFor W (x ∷ δ)`。反向读取 small-spec 路径，把语义满足转成该环境属于 `SatW a` 的证明；随后，`consAtL-in` 证明同一环境与旧环境之间满足所需的图扩展关系。
<!--ja-->
内向きの方向では、正準な拡張環境 `envFor W (x ∷ δ)` を構成します。small-spec のパスを逆向きに読むと、意味論的充足はこの環境が `SatW a` に属することへ移ります。続いて `consAtL-in` が、同じ環境と古い環境の間に必要なグラフ拡張の関係が成り立つことを示します。
<!--/-->

```agda
      inn h = ∣ Semantic.envFor W (x ∷ δ)
        , subst (λ X → ⟨ fst (Semantic.envFor W (x ∷ δ)) ∈ X ⟩) (sym qa)
          (subst ⟨_⟩ (sym (Semantic.Sat-small-spec W a (x ∷ δ) (Semantic.envFor W (x ∷ δ))
            (Semantic.envFor-graph W (x ∷ δ)))) h)
        , Semantic.consAtL-in W δ x (Semantic.envFor W (x ∷ δ) ∷ Semantic.intoL W x ∷ γ)
```

<!--en-->
The remaining arguments to `consAtL-in` supply the old graph equation `qz`, the reflexive identification of the new head `x`, and `envFor-graph` for the extended vector. These data close the inward witness and complete the equivalence.
<!--zh-->
`consAtL-in` 的余下参数依次给出旧图等式 `qz`、新首项 `x` 的自反同一视，以及扩展向量的 `envFor-graph`。这些数据闭合向内见证，从而完成等价。
<!--ja-->
`consAtL-in` の残りの引数は、古いグラフの等式 `qz`、新しい先頭要素 `x` の反射的な同定、そして拡張ベクトルに対する `envFor-graph` を与えます。これらのデータが内向きの証人を閉じ、同値を完成させます。
<!--/-->

```agda
            i0 i1 (sh 2 zi) qz refl (Semantic.envFor-graph W (x ∷ δ)) ∣₁

```

<!--en-->
The existential bridge is the first quantifier result: membership in the internal value of `∃̇ a` over the environment set is the same as satisfying the bounded-existential shape `quEx` over the carrier, with the two slot equations naming the carrier and the child value.
<!--zh-->
存在桥接是量词的第一个结果：`∃̇ a` 的内部值在环境集上的隶属，与在载体上满足有界存在形状 `quEx` 是同一回事，其中两条槽位等式分别点名载体与子值。
<!--ja-->
存在の橋渡しは、量化子に関する最初の結果です。環境の集合の上での `∃̇ a` の内部の値への所属は、台の上で有界存在の形 `quEx` を充足することと同じであり、二つのスロットの等式が台と子の値を名指します。
<!--/-->

```agda
  exBridge : ∀ {n} (a : Formula Ab (suc n)) {k : ℕ} (γ : S ^ k) (wi yai : Fin k)
           → fst (lookup wi γ) ≡ Wv → fst (lookup yai γ) ≡ fst (SatW a)
           → ExtFact (fst (SatW (∃̇ a))) (fst (envSet W n)) (λ z → ⟨ (z ∷ γ) ⊨ quEx wi yai ⟩)
  exBridge a γ wi yai qw qa = direct-extension (∃̇ a) (λ z → (z ∷ γ) ⊨ quEx wi yai)
    (λ δ z qz → map₁ (λ { (x , h) → Semantic.intoL W x
```

<!--en-->
For the existential bridge, `direct-extension` leaves only the two translations supplied by `child`. From semantic satisfaction, a truncated model element `x` is embedded into `L` and becomes the outer bounded witness; conversely, an object-language witness in the named carrier is turned into an element of the restricted model and then read through `child`. Both transformations stay under propositional truncation.
<!--zh-->
对存在桥接，`direct-extension` 之后只剩由 `child` 提供的两次转换。从语义满足出发，截断中的模型元素 `x` 被嵌入 `L`，成为外层有界见证；反过来，对象语言中属于被指名载体的见证被视为限制模型的元素，再经 `child` 读取。两次转换都始终处在命题截断之内。
<!--ja-->
存在の橋渡しでは、`direct-extension` の後に残るのは `child` が与える二つの変換だけです。意味論的充足からは、切り詰めの中の模型要素 `x` を `L` に埋め込み、外側の有界な証人とします。逆に、対象言語で名指された台に属す証人を制限模型の要素として受け取り、`child` を通して読みます。どちらの変換も命題的切り詰めの内側で行われます。
<!--/-->

```agda
      , subst (λ X → ⟨ fst x ∈ X ⟩) (sym qw) (snd x)
      , subst ⟨_⟩ (sym (child a δ x (z ∷ γ) i0 (suc yai) qz qa)) h }))
    (λ δ z qz → map₁ (λ { (x , hx , h) → (fst x , subst (λ X → ⟨ fst x ∈ X ⟩) qw hx)
      , subst ⟨_⟩ (child a δ (fst x , subst (λ X → ⟨ fst x ∈ X ⟩) qw hx)
        (z ∷ γ) i0 (suc yai) qz qa) h }))
```

<!--en-->
The universal bridge states the same extensional fact for `∀̇ a`: the internal value contains an environment exactly when every carrier member, consed onto the environment, satisfies the child formula.
<!--zh-->
全称桥接为 `∀̇ a` 陈述同样的外延事实：内部值包含一个环境，当且仅当载体的每个成员添加到该环境之后都满足子公式。
<!--ja-->
全称の橋渡しは `∀̇ a` に対して同じ外延的事実を述べます。内部の値が環境を含むのは、台のすべての要素をその環境の先頭に加えたときに子論理式が充足される場合であり、またその場合に限られます。
<!--/-->

```agda

  allBridge : ∀ {n} (a : Formula Ab (suc n)) {k : ℕ} (γ : S ^ k) (wi yai : Fin k)
            → fst (lookup wi γ) ≡ Wv → fst (lookup yai γ) ≡ fst (SatW a)
            → ExtFact (fst (SatW (∀̇ a))) (fst (envSet W n)) (λ z → ⟨ (z ∷ γ) ⊨ quAll wi yai ⟩)
  allBridge a γ wi yai qw qa = direct-extension (∀̇ a) (λ z → (z ∷ γ) ⊨ quAll wi yai)
    (λ δ z qz h x hx → subst ⟨_⟩
```

<!--en-->
In the forward map required by `direct-extension`, an arbitrary object-level member of the named carrier is converted to a restricted-model element, the semantic universal hypothesis is applied to it, and `child` is read from semantic satisfaction back to the encoded extension clause. In the reverse map, a restricted-model element is embedded into the carrier, the encoded universal is applied, and `child` is read outward to recover semantic satisfaction.
<!--zh-->
在 `direct-extension` 所需的前向映射中，先把被指名载体的任意对象层成员变成限制模型的元素，对它施用语义全称假设，再从语义满足向编码扩展子句反向读取 `child`。在反向映射中，先把限制模型元素嵌入载体，施用编码全称，再向外读取 `child` 以恢复语义满足。
<!--ja-->
`direct-extension` が要求する前向きの写像では、名指された台の任意の対象レベルの要素を制限模型の要素に変え、意味論的な全称の仮定を適用し、`child` を意味論的充足から符号化された拡張の節へ逆向きに読みます。逆向きの写像では、制限模型の要素を台へ埋め込み、符号化された全称を適用してから、`child` を外向きに読んで意味論的充足を復元します。
<!--/-->

```agda
      (sym (child a δ (fst x , subst (λ X → ⟨ fst x ∈ X ⟩) qw hx) (z ∷ γ) i0 (suc yai) qz qa))
      (h (fst x , subst (λ X → ⟨ fst x ∈ X ⟩) qw hx)))
    (λ δ z qz h x → subst ⟨_⟩ (child a δ x (z ∷ γ) i0 (suc yai) qz qa)
      (h (Semantic.intoL W x) (subst (λ X → ⟨ fst x ∈ X ⟩) (sym qw) (snd x))))
```

<!--en-->
The bounded quantifiers are stated in the object language with three nested bounded layers: the value of the bounding term, a member of the carrier inside it, and the extension entry, in the same order for both quantifiers.
<!--zh-->
有界量词的对象语言形状有三层嵌套的有界量化：界项的取值、其内落在载体中的成员、以及扩展条目，两个量词的次序相同。
<!--ja-->
有界の量化子は、対象言語で三重に入れ子になった有界の層として述べられます。境界の項の値、その内側で台に属する要素、そして拡張の項目であり、順序は両方の量化子で同じです。
<!--/-->

```agda
  bqAll bqEx : ∀ {k} → Fin k → Fin k → Fin k → Fin k → Fin k → Formula S (1 + k)
  bqAll wi ti yai N0i N1i =
    ∀̇∈ (var (suc wi)) (tmIs (suc (suc ti)) i1 i0 (suc (suc N0i)) (suc (suc N1i))
      ⇒̇ ∀̇∈ (var (suc (suc wi))) ((var i0 ∈̇ var i1) ⇒̇ ∃̇∈ (var (suc (suc (suc yai)))) (consAtL i0 i1 i3)))
  bqEx wi ti yai N0i N1i =
```

<!--en-->
The existential form conjoins the three layers; the universal form nests them as implications. The bounding term's value is read by its own term clause, and the innermost clause uses the same graph-extension equation as in the unbounded case.
<!--zh-->
存在形式把三层合取；全称形式以蕴涵嵌套它们。界项的取值由其自身的词项子句读取，而最内层子句使用与无界情形相同的图扩展等式。
<!--ja-->
存在の形は三つの層を連言し、全称の形はそれらを含意として入れ子にします。境界項の値はその項の節によって読み取られ、最も内側の節は非有界の場合と同じグラフ拡張の等式を使います。
<!--/-->

```agda
    ∃̇∈ (var (suc wi)) (tmIs (suc (suc ti)) i1 i0 (suc (suc N0i)) (suc (suc N1i))
      ∧̇ ∃̇∈ (var (suc (suc wi))) ((var i0 ∈̇ var i1) ∧̇ ∃̇∈ (var (suc (suc (suc yai)))) (consAtL i0 i1 i3)))
```

<!--en-->
The semantic value of a term is obtained by mapping each constant from the alphabet of members of `W` into the restricted model and then evaluating the resulting term at `δ`. Constants are interpreted by the embedding `DB.ι`, while variables are read directly from the corresponding positions of `δ`; set-coded numerals belong to the later representation of variable indices, not to this evaluation function.
<!--zh-->
词项的语义值这样得到：先把字母表中来自 `W` 的每个常元映入限制模型，再在 `δ` 处求值。常元由嵌入 `DB.ι` 解释，变元则直接从 `δ` 的相应位置读取；集合编码的数码用于随后表示变元索引，并不属于这里的求值函数。
<!--ja-->
項の意味論的な値は、`W` の要素からなるアルファベットの各定数を制限模型へ写し、得られた項を `δ` で評価することで定まります。定数は埋め込み `DB.ι` で解釈され、変数は `δ` の対応する位置から直接読まれます。集合として符号化された数項は後で変数の添字を表すためのものであり、この評価関数の一部ではありません。
<!--/-->

```agda
  private
    value : ∀ {n} → Term Ab n → DB.SM ^ n → DB.SM
    value t δ = ⟦ mapTm DB.ι t ⟧ᴮ δ

```

<!--en-->
For a constant term, `term-out` eliminates the truncated `TmIsV` evidence into an equality of sets. In the constant branch, injectivity of the pair code compares the second components and identifies the proposed value with the constant; the variable-shaped branch would equate the distinct tags `# 0` and `# 1` and is therefore impossible.
<!--zh-->
对常元词项，`term-out` 把截断的 `TmIsV` 证据消去到集合等式中。在常元分支，对编码的单射性比较第二分量，从而把候选值认作该常元；变元形状的分支会迫使不同标签 `# 0` 与 `# 1` 相等，因而不可能。
<!--ja-->
定数項について、`term-out` は切り詰められた `TmIsV` の証拠を集合の等式へ消去します。定数の分枝では、対の符号化の単射性が第二成分を比較し、候補の値をその定数と同定します。変数の形をした分枝は異なるタグ `# 0` と `# 1` を等しくしてしまうため、不可能です。
<!--/-->

```agda
    term-out : ∀ {n} (t : Term Ab n) (δ : DB.SM ^ n) (z v : S)
      → fst z ≡ Semantic.graph W δ → TmIsV (ct t) (fst z) (fst v)
      → fst v ≡ fst (value t δ)
    term-out (con q) δ z v qz = rec₁ (setIsSet _ _)
      (λ { (inl e) → sym (pr-inj e .snd)
```

<!--en-->
For a variable term, the constant-shaped branch is ruled out by the same tag distinction. In the variable-shaped branch, pair injectivity identifies the stored index with the numeral of `i`; the equation `qz` moves its membership into the canonical graph, and `lookup-spec` then says that the proposed value is exactly the `i`th entry of `δ`. The truncation is eliminated only into this propositional equality.
<!--zh-->
对变元词项，常元形状的分支同样由标签互异而排除。在变元形状的分支，对编码的单射性把所存索引认作 `i` 的数码；等式 `qz` 把相应隶属移入典范图，`lookup-spec` 随即说明候选值恰是 `δ` 的第 `i` 个条目。截断只被消去到这条命题性等式中。
<!--ja-->
変数項では、定数の形をした分枝が同じタグの相違によって排除されます。変数の形をした分枝では、対の符号化の単射性が格納された添字を `i` の数項と同定し、等式 `qz` がその所属を正準なグラフへ移します。そこで `lookup-spec` により、候補の値が `δ` の第 `i` 成分にちょうど等しいと分かります。切り詰めはこの命題的な等式の中へのみ消去されます。
<!--/-->

```agda
         ; (inr (i , e , _)) → ⊥₀-rec (znots (#-inj′ {0} {1} (pr-inj e .fst))) })
    term-out (var i) δ z v qz = rec₁ (setIsSet _ _)
      (λ { (inl e) → ⊥₀-rec (snotz (#-inj′ {1} {0} (pr-inj e .fst)))
         ; (inr (j , e , hp)) → subst ⟨_⟩ (lookup-spec (Semantic.values W δ) i (fst v))
             (subst2 (λ a E → ⟨ pr a (fst v) ∈ E ⟩) (sym (pr-inj e .snd)) qz hp) })
```

<!--en-->
The converse lemma reconstructs `TmIsV` from the actual semantic value. For a constant, the supplied equality is reversed and transported through the pair constructor with tag `# 0`, producing the constant-shaped alternative under propositional truncation.
<!--zh-->
反向引理从真实语义值重建 `TmIsV`。对常元，把给定等式反向，并通过标签为 `# 0` 的对构造传输，就得到命题截断中的常元形状分支。
<!--ja-->
逆向きの補題は、実際の意味論的な値から `TmIsV` を組み立て直します。定数の場合、与えられた等式を逆向きにし、タグ `# 0` を持つ対の構成子を通して輸送すると、命題的切り詰めの中に定数の形をした選択肢が得られます。
<!--/-->

```agda

    term-in : ∀ {n} (t : Term Ab n) (δ : DB.SM ^ n) (z v : S)
      → fst z ≡ Semantic.graph W δ → fst v ≡ fst (value t δ)
      → TmIsV (ct t) (fst z) (fst v)
    term-in (con q) δ z v qz e = ∣ inl (cong (pr (# 0)) (sym e)) ∣₁
    term-in (var i) δ z v qz e = ∣ inr (# (toℕ i) , refl
```

<!--en-->
For a variable, the witness uses the numeral `# (toℕ i)` as its stored index. The supplied equality identifies the proposed value with the `i`th semantic entry; `lookup-spec` turns that equality into membership of the corresponding pair in the canonical graph, and transport backward along `qz` places the pair in the given coded environment.
<!--zh-->
对变元，见证以数码 `# (toℕ i)` 作为所存索引。给定等式把候选值认作第 `i` 个语义条目；`lookup-spec` 将这条等式转成相应的配对属于典范图的证明，再沿 `qz` 反向传输，把该配对放回给定的编码环境中。
<!--ja-->
変数の場合、証人は数項 `# (toℕ i)` を格納された添字として使います。与えられた等式は候補値を第 `i` 番目の意味論的成分と同定し、`lookup-spec` はその等式を、対応する対が正準なグラフに属することへ変えます。最後に `qz` に沿って逆向きに輸送し、その対を与えられた符号化環境へ戻します。
<!--/-->

```agda
      , subst (λ E → ⟨ pr (# (toℕ i)) (fst v) ∈ E ⟩) (sym qz)
          (subst ⟨_⟩ (sym (lookup-spec (Semantic.values W δ) i (fst v))) e)) ∣₁

```

<!--en-->
The bounded-quantifier module fixes the bounding term, the subformula, five slots, and five equations: the carrier, the term's coding, the subformula's value, and the two numeral slots, all read at a shared context.
<!--zh-->
有界量词模块固定界限词项、子公式、五个槽位与五条等式：载体、词项的编码、子公式的值，以及两个数码槽位，全部在同一语境上读取。
<!--ja-->
有界量化子のモジュールは、境界の項、部分式、五つのスロット、そして五つの等式を固定します。台、項の符号化、部分式の値、そして二つの数項のスロットで、すべて共有された文脈の上で読まれます。
<!--/-->

```agda
  module BqBridge {n : ℕ} (t : Term Ab n) (a : Formula Ab (suc n)) {k : ℕ} (Γ : S ^ k)
    (wi ti yai N0i N1i : Fin k)
    (qw : fst (lookup wi Γ) ≡ Wv) (qt : fst (lookup ti Γ) ≡ ct t) (qa : fst (lookup yai Γ) ≡ fst (SatW a))
    (q0 : fst (lookup N0i Γ) ≡ # 0) (q1 : fst (lookup N1i Γ) ≡ # 1) where

```

<!--en-->
The remaining proof must connect the object-language term clause used by the bounded quantifier with the semantic term value just established. The local lemmas keep that connection at the fixed slots and equations of `BqBridge`, so every later quantifier argument uses the same carrier, term code, child value, and numeral tags.
<!--zh-->
余下的证明要把有界量词所用的对象语言词项子句，与刚刚确立的语义词项值连接起来。以下局部引理把这条联系固定在 `BqBridge` 的槽位与等式上，使后续每个量词论证都使用同一个载体、词项码、子公式值和数码标签。
<!--ja-->
残る証明では、有界量化子が使う対象言語の項の節を、直前に確立した意味論的な項の値へ結び付ける必要があります。以下の局所補題はこの対応を `BqBridge` の固定されたスロットと等式の上に保ち、後続の量化子の議論が同じ台、項の符号、子論理式の値、数項のタグを使うようにします。
<!--/-->

```agda
    private
```

<!--en-->
If the object-language term clause holds at `v ∷ z ∷ Γ`, `tmIs-out` first reads it as `TmIsV` for the code occupying the term slot. Transport along `qt` then replaces that slot value by the actual code `ct t`, yielding the representation-level statement needed by `term-out`.
<!--zh-->
若对象语言词项子句在 `v ∷ z ∷ Γ` 处成立，`tmIs-out` 先把它读成关于词项槽中代码的 `TmIsV`。再沿 `qt` 传输，把该槽值替换为真实代码 `ct t`，得到 `term-out` 所需的表示层陈述。
<!--ja-->
対象言語の項の節が `v ∷ z ∷ Γ` で成り立つなら、`tmIs-out` はまずそれを項のスロットにある符号についての `TmIsV` として読みます。次に `qt` に沿って輸送し、そのスロットの値を実際の符号 `ct t` に置き換えると、`term-out` が必要とする表現レベルの主張が得られます。
<!--/-->

```agda
      tmOut : (z v : S) → ⟨ (v ∷ z ∷ Γ) ⊨ tmIs (suc (suc ti)) i1 i0 (suc (suc N0i)) (suc (suc N1i)) ⟩
            → TmIsV (ct t) (fst z) (fst v)
      tmOut z v h = subst (λ u → TmIsV u (fst z) (fst v)) qt
        (tmIs-out (suc (suc ti)) i1 i0 (suc (suc N0i)) (suc (suc N1i)) (v ∷ z ∷ Γ) q0 q1 h)

```

<!--en-->
Conversely, a `TmIsV` statement for `ct t` is transported backward along `qt` and passed to `tmIs-in`. The result is precisely the object-language term clause at `v ∷ z ∷ Γ`, so the bridge can move between the coded clause and semantic term evaluation in either direction.
<!--zh-->
反过来，关于 `ct t` 的 `TmIsV` 陈述沿 `qt` 反向传输，再交给 `tmIs-in`。所得正是在 `v ∷ z ∷ Γ` 处的对象语言词项子句，因此桥接可在编码子句与语义词项求值之间双向移动。
<!--ja-->
逆に、`ct t` についての `TmIsV` の主張を `qt` に沿って逆向きに輸送し、`tmIs-in` に渡します。結果は `v ∷ z ∷ Γ` における対象言語の項の節そのものであり、橋渡しは符号化された節と意味論的な項の評価との間を両方向に移動できます。
<!--/-->

```agda
      tmIn' : (z v : S) → TmIsV (ct t) (fst z) (fst v)
            → ⟨ (v ∷ z ∷ Γ) ⊨ tmIs (suc (suc ti)) i1 i0 (suc (suc N0i)) (suc (suc N1i)) ⟩
      tmIn' z v h = tmIs-in (suc (suc ti)) i1 i0 (suc (suc N0i)) (suc (suc N1i)) (v ∷ z ∷ Γ) q0 q1
        (subst (λ u → TmIsV u (fst z) (fst v)) (sym qt) h)

```

<!--en-->
For a semantic environment `δ`, `bound δ` is the value of the bounding term embedded back into `L`. It serves as the canonical witness for the outer value slot of the coded bounded quantifier, and its members are the elements over which the bounded formula ranges.
<!--zh-->
对语义环境 `δ`，`bound δ` 是界项取值重新嵌入 `L` 后所得的集合。它充当编码有界量词最外层取值槽的典范见证，而有界公式所量化的对象正是它的成员。
<!--ja-->
意味論的環境 `δ` に対し、`bound δ` は境界項の値を `L` へ埋め戻した集合です。これは符号化された有界量化子の最外側の値スロットに対する正準な証人となり、有界論理式はその要素の上を動きます。
<!--/-->

```agda
      bound : DB.SM ^ n → S
      bound δ = Semantic.intoL W (value t δ)

```

<!--en-->
The bound belongs to the carrier: the value's second component is its membership in the carrier, transported along the carrier's naming equation.
<!--zh-->
界属于载体：取值的第二分量是它在载体中的隶属，沿载体的命名等式传输。
<!--ja-->
境界は台に属します。値の第二成分が台への所属であり、台の名指しの等式に沿って輸送されます。
<!--/-->

```agda
      bound∈W : (δ : DB.SM ^ n) → ⟨ fst (bound δ) ∈ fst (lookup wi Γ) ⟩
      bound∈W δ = subst (λ X → ⟨ fst (value t δ) ∈ X ⟩)
        (sym qw) (snd (value t δ))

```

<!--en-->
When `z` is the graph of `δ`, the underlying set of `bound δ` is definitionally the underlying set of the semantic value of `t`, so reflexivity supplies the equality required by `term-in`. The result is `TmIsV (ct t) (fst z) (fst (bound δ))`, certifying that the chosen bound represents the coded term's value at the encoded environment.
<!--zh-->
当 `z` 是 `δ` 的图时，`bound δ` 的底层集合按定义就是 `t` 的语义值之底层集合，因此自反性给出 `term-in` 所需的等式。所得 `TmIsV (ct t) (fst z) (fst (bound δ))` 认证所选的界表示编码词项在该编码环境处的取值。
<!--ja-->
`z` が `δ` のグラフであるとき、`bound δ` の基礎の集合は定義上 `t` の意味論的な値の基礎の集合そのものなので、反射律が `term-in` に必要な等式を与えます。得られる `TmIsV (ct t) (fst z) (fst (bound δ))` は、選んだ境界が符号化環境における符号化項の値を表すことを証明します。
<!--/-->

```agda
      bound-term : (δ : DB.SM ^ n) (z : S) → fst z ≡ Semantic.graph W δ
                 → TmIsV (ct t) (fst z) (fst (bound δ))
      bound-term δ z qz = term-in t δ z (bound δ) qz refl

```

<!--en-->
The representation-level certificate from `bound-term` is then converted by `tmIn'` into the object-language `tmIs` formula at the exact shifted slots used by the bounded-quantifier body. Thus the canonical semantic bound can be inserted into that body's outer quantified layer.
<!--zh-->
随后，`bound-term` 给出的表示层证书由 `tmIn'` 转成对象语言的 `tmIs` 公式，并落在有界量词主体所用的精确移位槽位上。于是，典范语义界可以填入该主体的最外层量化。
<!--ja-->
次に、`bound-term` が与えた表現レベルの証明を `tmIn'` によって対象言語の `tmIs` へ変換し、有界量化子の本体が使う正確にずらされたスロットへ置きます。これにより、正準な意味論的境界を本体の最外側の量化層へ挿入できます。
<!--/-->

```agda
      bound-read : (δ : DB.SM ^ n) (z : S) → fst z ≡ Semantic.graph W δ
                 → ⟨ (bound δ ∷ z ∷ Γ)
                     ⊨ tmIs (suc (suc ti)) i1 i0
                         (suc (suc N0i)) (suc (suc N1i)) ⟩
      bound-read δ z qz = tmIn' z (bound δ) (bound-term δ z qz)
```

<!--en-->
For the forward half of the bounded universal bridge, consider an arbitrary candidate value `v` satisfying the term clause and an arbitrary carrier member `x` lying in `v`. The lemma `term-out` identifies the underlying set of `v` with the underlying set of the actual semantic value of `t`, so membership of `x` transports to the semantic bound. The universal semantic hypothesis gives the child's truth, and `child` converts it back to the encoded extension clause.
<!--zh-->
在有界全称桥接的前向一半中，任取满足词项子句的候选值 `v`，再任取既属于载体又属于 `v` 的成员 `x`。引理 `term-out` 把 `v` 的底层集合认同为 `t` 的真实语义值之底层集合，因此 `x` 的隶属可传输到语义界中。语义全称假设给出子公式的真值，再由 `child` 把它转回编码扩展子句。
<!--ja-->
有界な全称の橋渡しの前向きの半分では、項の節を満たす任意の候補値 `v` と、台に属しかつ `v` に属す任意の要素 `x` を考えます。補題 `term-out` は `v` の基礎の集合を `t` の実際の意味論的な値の基礎の集合と同定するので、`x` の所属を意味論的な境界への所属へ輸送できます。全称の意味論的仮定が子論理式の真理を与え、`child` がそれを符号化された拡張の節へ戻します。
<!--/-->

```agda
    allInBridge : ExtFact (fst (SatW (∀̇∈ t a))) (fst (envSet W n)) (λ z → ⟨ (z ∷ Γ) ⊨ bqAll wi ti yai N0i N1i ⟩)
    allInBridge = direct-extension (∀̇∈ t a) (λ z → (z ∷ Γ) ⊨ bqAll wi ti yai N0i N1i)
      (λ δ z qz h v hv ht x hx hxv → subst ⟨_⟩
        (sym (child a δ (fst x , subst (λ X → ⟨ fst x ∈ X ⟩) qw hx)
          (v ∷ z ∷ Γ) i1 (sh 2 yai) qz qa))
```

<!--en-->
For the reverse half, an arbitrary restricted-model element `x` lying in the semantic bound must satisfy the child. The coded universal is instantiated with the canonical value `bound δ`, using `bound∈W` and `bound-read`, and with the embedded element `intoL W x`, using its carrier membership and the assumed bound membership. Reading `child` outward then gives `Meaning a (x ∷ δ)`.
<!--zh-->
在反向一半中，要证明语义界内任意限制模型元素 `x` 满足子公式。把编码全称实例化于典范值 `bound δ`，所需条件由 `bound∈W` 与 `bound-read` 提供；再实例化于嵌入后的元素 `intoL W x`，使用它的载体隶属与假定的界内隶属。最后向外读取 `child`，得到 `Meaning a (x ∷ δ)`。
<!--ja-->
逆向きの半分では、意味論的境界に属す任意の制限模型の要素 `x` が子論理式を満たすことを示します。符号化された全称を正準な値 `bound δ` に適用し、必要な条件を `bound∈W` と `bound-read` から得ます。さらに埋め込まれた要素 `intoL W x` に適用し、その台への所属と仮定された境界への所属を使います。最後に `child` を外向きに読むと `Meaning a (x ∷ δ)` が得られます。
<!--/-->

```agda
        (h (fst x , subst (λ X → ⟨ fst x ∈ X ⟩) qw hx)
          (subst (λ V → ⟨ fst x ∈ V ⟩) (term-out t δ z v qz (tmOut z v ht)) hxv)))
      (λ δ z qz h x hx → subst ⟨_⟩
        (child a δ x (bound δ ∷ z ∷ Γ) i1 (sh 2 yai) qz qa)
        (h (bound δ) (bound∈W δ) (bound-read δ z qz)
```

<!--en-->
The last argument is exactly the hypothesis that `x` lies in the semantic value of the bounding term. Supplying it completes the universal verifier for every such `x`, and hence completes the reverse implication required by `direct-extension`.
<!--zh-->
最后一个参数恰是假设 `x` 属于界项的语义值。供给这份隶属后，便为每个这样的 `x` 完成全称验证者，也就完成了 `direct-extension` 所需的反向蕴涵。
<!--ja-->
最後の引数は、`x` が境界項の意味論的な値に属すという仮定そのものです。この所属を与えると、そのようなすべての `x` に対する全称の検証者が完成し、`direct-extension` が要求する逆向きの含意も完成します。
<!--/-->

```agda
          (Semantic.intoL W x) (subst (λ X → ⟨ fst x ∈ X ⟩) (sym qw) (snd x)) hx))

```

<!--en-->
The bounded existential bridge states the same extensional fact for `∃̇∈ t a`: membership in the internal value is equivalent, within the environment set, to satisfaction of the three-layer bounded-existential formula over the carrier.
<!--zh-->
有界存在桥接为 `∃̇∈ t a` 陈述同样的外延事实：在环境集合内，属于内部值等价于满足载体上的三层有界存在公式。
<!--ja-->
有界な存在量化の橋渡しは、`∃̇∈ t a` に対して同じ外延的事実を述べます。環境集合の内部では、内部の値への所属は、台の上の三層の有界存在論理式を充足することと同値です。
<!--/-->

```agda
    exInBridge : ExtFact (fst (SatW (∃̇∈ t a))) (fst (envSet W n)) (λ z → ⟨ (z ∷ Γ) ⊨ bqEx wi ti yai N0i N1i ⟩)
    exInBridge = direct-extension (∃̇∈ t a) (λ z → (z ∷ Γ) ⊨ bqEx wi ti yai N0i N1i)
      (λ δ z qz → map₁ (λ { (x , hx , h) → bound δ
        , bound∈W δ
        , bound-read δ z qz
```

<!--en-->
From a semantic witness `x` for the bounded existential, the forward map chooses the canonical outer value `bound δ`, supplies its carrier membership and term certificate, and embeds `x` as the inner carrier witness. Its membership in the semantic bound is retained, while `child` read backward produces the required encoded extension witness. Every existential witness remains under propositional truncation.
<!--zh-->
从有界存在的语义见证 `x` 出发，前向映射选取典范外层值 `bound δ`，供给其载体隶属与词项证书，并把 `x` 嵌入为内层载体见证。`x` 属于语义界的证据得到保留，而反向读取 `child` 产生所需的编码扩展见证。所有存在见证始终留在命题截断之内。
<!--ja-->
有界な存在の意味論的証人 `x` から、前向きの写像は正準な外側の値 `bound δ` を選び、その台への所属と項の証明を与え、`x` を内側の台の証人として埋め込みます。`x` の意味論的境界への所属は保たれ、`child` を逆向きに読むことで必要な符号化された拡張の証人が得られます。存在の証人はすべて命題的切り詰めの内側に保たれます。
<!--/-->

```agda
        , ∣ Semantic.intoL W x , subst (λ X → ⟨ fst x ∈ X ⟩) (sym qw) (snd x) , hx
            , subst ⟨_⟩ (sym (child a δ x (bound δ ∷ z ∷ Γ) i1 (sh 2 yai) qz qa)) h ∣₁ }))
      (λ δ z qz → rec₁ squash₁ (λ { (v , hv , ht , h) → map₁
        (λ { (x , hx , hxv , hc) → (fst x , subst (λ X → ⟨ fst x ∈ X ⟩) qw hx)
          , subst (λ V → ⟨ fst x ∈ V ⟩) (term-out t δ z v qz (tmOut z v ht)) hxv
```

<!--en-->
In the reverse map, the outer truncated witness supplies a candidate term value `v`, and the inner one supplies a carrier member `x` lying in `v` together with an encoded child extension. Reading the term clause outward identifies the underlying set of `v` with the underlying set of the actual semantic bound. That equality transports `x`'s membership to the true bound, and `child` transports the encoded child evidence to semantic satisfaction.
<!--zh-->
在反向映射中，外层截断见证给出候选词项值 `v`，内层见证给出既属于载体又属于 `v` 的成员 `x`，以及编码的子公式扩展。向外读取词项子句，把 `v` 的底层集合认同为真实语义界的底层集合；沿该等式把 `x` 的隶属传输到真实界，再由 `child` 把编码的子公式证据转成语义满足。
<!--ja-->
逆向きの写像では、外側の切り詰められた証人が項の候補値 `v` を与え、内側の証人が台に属しかつ `v` に属す要素 `x` と、符号化された子論理式の拡張を与えます。項の節を外向きに読むと、`v` の基礎の集合が実際の意味論的な境界の基礎の集合と同定されます。その等式に沿って `x` の所属を真の境界へ輸送し、さらに `child` が符号化された子の証拠を意味論的充足へ移します。
<!--/-->

```agda
          , subst ⟨_⟩ (child a δ (fst x , subst (λ X → ⟨ fst x ∈ X ⟩) qw hx)
              (v ∷ z ∷ Γ) i1 (sh 2 yai) qz qa) hc }) h }))
```

<!--en-->
The atomic body binds two values, not three: a carrier element `v` proposed as the value of `t`, and a carrier element `x` proposed as the value of `u`. It then conjoins the two `tmIs` clauses with the given relation formula `rel`, evaluated in the context `x ∷ v ∷ z ∷ Γ`; the coded environment `z` is already free, and `rel` is a formula rather than a bound entry.
<!--zh-->
原子主体只绑定两个值，而不是三个：载体元素 `v` 作为 `t` 的候选值，载体元素 `x` 作为 `u` 的候选值。随后，它把两条 `tmIs` 子句与给定关系公式 `rel` 合取，并在语境 `x ∷ v ∷ z ∷ Γ` 中求值；编码环境 `z` 原本就是自由参数，`rel` 是公式而非被绑定的条目。
<!--ja-->
原子の本体が束縛する値は三つではなく二つです。台の要素 `v` を `t` の候補値とし、台の要素 `x` を `u` の候補値とします。その後、二つの `tmIs` の節と与えられた関係式 `rel` を連言し、文脈 `x ∷ v ∷ z ∷ Γ` で評価します。符号化環境 `z` はもとから自由な引数であり、`rel` は束縛される項目ではなく論理式です。
<!--/-->

```agda
  atomEx : ∀ {k} → Fin k → Fin k → Fin k → Fin k → Fin k → Formula S (3 + k) → Formula S (1 + k)
  atomEx wi ti ui N0i N1i rel =
    ∃̇∈ (var (suc wi)) (∃̇∈ (var (suc (suc wi)))
      (tmIs (suc (suc (suc ti))) i2 i1 (sh 3 N0i) (sh 3 N1i)
        ∧̇ (tmIs (suc (suc (suc ui))) i2 i0 (sh 3 N0i) (sh 3 N1i) ∧̇ rel)))
```

<!--en-->
`AtomBridge` abstracts the common proof for membership and equality atoms. The terms `t` and `u` and the five slot equations determine how their codes and the tags `# 0`, `# 1` are read; the parameters `op`, `R`, and `rel` then specify the meta-level atom, its ambient binary relation, and the object-language formula that represents that relation.
<!--zh-->
`AtomBridge` 抽出隶属原子与相等原子共有的证明。词项 `t`、`u` 及五条槽位等式决定如何读取它们的代码与标签 `# 0`、`# 1`；参数 `op`、`R`、`rel` 则分别指定元层原子、对应的外围二元关系，以及表示该关系的对象语言公式。
<!--ja-->
`AtomBridge` は所属原子と等号原子に共通する証明を抽象化します。項 `t`、`u` と五つのスロット等式が、それらの符号とタグ `# 0`、`# 1` の読み方を定めます。さらに引数 `op`、`R`、`rel` がそれぞれメタレベルの原子、対応する周囲の二項関係、その関係を表す対象言語の論理式を指定します。
<!--/-->

```agda

  module AtomBridge {n : ℕ} (t u : Term Ab n) {k : ℕ} (Γ : S ^ k)
    (wi ti ui N0i N1i : Fin k)
    (qw : fst (lookup wi Γ) ≡ Wv) (qt : fst (lookup ti Γ) ≡ ct t) (qu : fst (lookup ui Γ) ≡ ct u)
    (q0 : fst (lookup N0i Γ) ≡ # 0) (q1 : fst (lookup N1i Γ) ≡ # 1)
    (op : ∀ {j} → Term Ab j → Term Ab j → Formula Ab j)
```

<!--en-->
The agreement hypothesis states the exact interface between `rel` and `R` at the three newly prepended entries. Satisfaction of `rel` in `x ∷ v ∷ z ∷ Γ` yields `R (fst v) (fst x)`, and a proof of that relation reconstructs satisfaction of `rel`. Thus the bridge may use an arbitrary representing formula only when both directions are supplied.
<!--zh-->
相符假设给出 `rel` 与 `R` 在新加入的三个条目处的精确接口。在 `x ∷ v ∷ z ∷ Γ` 中满足 `rel` 会得到 `R (fst v) (fst x)`，而该关系的一份证明又能重建 `rel` 的满足。因此，只有在两个方向均已给出时，桥接才可使用任意表示公式。
<!--ja-->
一致の仮定は、新たに先頭へ加えられた三つの項目における `rel` と `R` の正確な接続を述べます。`x ∷ v ∷ z ∷ Γ` での `rel` の充足から `R (fst v) (fst x)` が得られ、その関係の証明から `rel` の充足を組み立て直せます。したがって、橋渡しが任意の表現式を使えるのは、両方向が与えられている場合に限られます。
<!--/-->

```agda
    (R : V ℓ → V ℓ → Type (ℓ-suc ℓ))
    (rel : Formula S (3 + k))
    (agree : (z v x : S) → (⟨ (x ∷ v ∷ z ∷ Γ) ⊨ rel ⟩ → R (fst v) (fst x))
                           × (R (fst v) (fst x) → ⟨ (x ∷ v ∷ z ∷ Γ) ⊨ rel ⟩))
    (cnd-out : (δ : DB.SM ^ n) → ⟨ Meaning (op t u) δ ⟩ → R (fst (value t δ)) (fst (value u δ)))
```

<!--en-->
Two further hypotheses connect the chosen relation to the intended atomic semantics. The first sends `Meaning (op t u) δ` to `R` of the two evaluated term values, while the second reconstructs that meaning from the same relation. These hypotheses keep the generic bridge neutral between membership and equality.
<!--zh-->
另外两条假设把所选关系连接到目标原子语义。第一条把 `Meaning (op t u) δ` 送到两个词项求值之间的 `R`，第二条则从同一关系重建该语义。正因如此，这条一般桥接可同时适用于隶属与相等。
<!--ja-->
さらに二つの仮定が、選んだ関係を意図した原子の意味論へ結び付けます。第一の仮定は `Meaning (op t u) δ` を二つの項の評価値の間の `R` へ送り、第二の仮定は同じ関係からその意味を組み立て直します。このため、一般的な橋渡しは所属と等号のどちらにも同じ形で使えます。
<!--/-->

```agda
    (cnd-in : (δ : DB.SM ^ n) → R (fst (value t δ)) (fst (value u δ)) → ⟨ Meaning (op t u) δ ⟩) where

```

<!--en-->
The context `δ3 z v x = x ∷ v ∷ z ∷ Γ` places the proposed value of `u` at slot `i0`, the proposed value of `t` at `i1`, and the coded environment at `i2`. These are the three newly exposed entries used by the two term clauses and the relation interface; the inherited entries of `Γ` remain available to the generic formula `rel`. Only `x` and `v` are newly bound by `atomEx`, while `z` is already the free environment argument.
<!--zh-->
语境 `δ3 z v x = x ∷ v ∷ z ∷ Γ` 把 `u` 的候选值放在槽位 `i0`，把 `t` 的候选值放在 `i1`，并把编码环境放在 `i2`。它们是两条词项子句与关系接口使用的三个新条目；一般公式 `rel` 仍可使用从 `Γ` 继承的条目。`atomEx` 只新绑定 `x` 与 `v`，而 `z` 原本就是自由的环境参数。
<!--ja-->
文脈 `δ3 z v x = x ∷ v ∷ z ∷ Γ` は、`u` の候補値をスロット `i0`、`t` の候補値を `i1`、符号化環境を `i2` に置きます。これらは二つの項の節と関係の接続が使う、新たに現れた三つの項目です。一方、一般の論理式 `rel` は、引き継いだ `Γ` の項目も利用できます。`atomEx` が新たに束縛するのは `x` と `v` だけで、`z` はもとから自由な環境引数です。
<!--/-->

```agda
    private
      δ3 : (z v x : S) → S ^ (3 + k)
      δ3 z v x = x ∷ v ∷ z ∷ Γ

```

<!--en-->
The two outward readers turn the object-language term clauses in `δ3 z v x` into `TmIsV` statements. Transport along `qt` makes the first statement concern the actual code `ct t` and proposed value `v`; transport along `qu` does the same for `ct u` and proposed value `x`. The coded environment remains the common argument `z`.
<!--zh-->
两条向外读式把 `δ3 z v x` 中的对象语言词项子句转成 `TmIsV` 陈述。沿 `qt` 传输后，第一条陈述涉及真实代码 `ct t` 与候选值 `v`；沿 `qu` 传输后，第二条同样涉及 `ct u` 与候选值 `x`。两者共享的编码环境始终是 `z`。
<!--ja-->
二つの外向きの読みは、`δ3 z v x` における対象言語の項の節を `TmIsV` の主張へ変えます。`qt` に沿った輸送により、第一の主張は実際の符号 `ct t` と候補値 `v` に関するものとなり、`qu` に沿った輸送により、第二の主張は `ct u` と候補値 `x` に関するものとなります。符号化環境 `z` は両者に共通です。
<!--/-->

```agda
      tOut : (z v x : S) → ⟨ δ3 z v x ⊨ tmIs (suc (suc (suc ti))) i2 i1 (sh 3 N0i) (sh 3 N1i) ⟩ → TmIsV (ct t) (fst z) (fst v)
      tOut z v x h = subst (λ w → TmIsV w (fst z) (fst v)) qt
        (tmIs-out (suc (suc (suc ti))) i2 i1 (sh 3 N0i) (sh 3 N1i) (δ3 z v x) q0 q1 h)
      uOut : (z v x : S) → ⟨ δ3 z v x ⊨ tmIs (suc (suc (suc ui))) i2 i0 (sh 3 N0i) (sh 3 N1i) ⟩ → TmIsV (ct u) (fst z) (fst x)
      uOut z v x h = subst (λ w → TmIsV w (fst z) (fst x)) qu
```

<!--en-->
The converse readers rebuild the two object-language term clauses from `TmIsV`. For `t`, the code is first transported backward along `qt` and then passed to `tmIs-in`; the declaration for `uIn` sets up the identical construction for `u` at its own value slot.
<!--zh-->
反向读式从 `TmIsV` 重建两条对象语言词项子句。对 `t`，先沿 `qt` 反向传输代码，再把结果交给 `tmIs-in`；`uIn` 的声明则为 `u` 在自身取值槽处安排同样的构造。
<!--ja-->
逆向きの読みは、`TmIsV` から二つの対象言語の項の節を組み立て直します。`t` については、まず符号を `qt` に沿って逆向きに輸送し、その結果を `tmIs-in` に渡します。`uIn` の宣言は、`u` の値のスロットにおける同じ構成を用意します。
<!--/-->

```agda
        (tmIs-out (suc (suc (suc ui))) i2 i0 (sh 3 N0i) (sh 3 N1i) (δ3 z v x) q0 q1 h)
      tIn : (z v x : S) → TmIsV (ct t) (fst z) (fst v) → ⟨ δ3 z v x ⊨ tmIs (suc (suc (suc ti))) i2 i1 (sh 3 N0i) (sh 3 N1i) ⟩
      tIn z v x h = tmIs-in (suc (suc (suc ti))) i2 i1 (sh 3 N0i) (sh 3 N1i) (δ3 z v x) q0 q1
        (subst (λ w → TmIsV w (fst z) (fst v)) (sym qt) h)
      uIn : (z v x : S) → TmIsV (ct u) (fst z) (fst x) → ⟨ δ3 z v x ⊨ tmIs (suc (suc (suc ui))) i2 i0 (sh 3 N0i) (sh 3 N1i) ⟩
```

<!--en-->
For `u`, backward transport along `qu` changes `TmIsV (ct u) (fst z) (fst x)` into the code named by the caller's slot, and `tmIs-in` rebuilds the second object-language term clause. The bridge now has both read and write directions for each proposed term value.
<!--zh-->
对 `u`，沿 `qu` 反向传输，把 `TmIsV (ct u) (fst z) (fst x)` 改写成关于调用者槽位所指代码的陈述，再由 `tmIs-in` 重建第二条对象语言词项子句。至此，桥接对两个候选词项值都具备读取与写入两个方向。
<!--ja-->
`u` については、`qu` に沿った逆向きの輸送が `TmIsV (ct u) (fst z) (fst x)` を呼出し側のスロットが名指す符号についての主張に変え、`tmIs-in` が第二の対象言語の項の節を組み立て直します。これで橋渡しは、二つの候補値のそれぞれについて読み書きの両方向を備えます。
<!--/-->

```agda
      uIn z v x h = tmIs-in (suc (suc (suc ui))) i2 i0 (sh 3 N0i) (sh 3 N1i) (δ3 z v x) q0 q1
        (subst (λ w → TmIsV w (fst z) (fst x)) (sym qu) h)

```

<!--en-->
The theorem `atomBridge` now asks `direct-extension` to compare the atomic semantic value with `atomEx` on every encoded environment. Its outward map must start from `Meaning (op t u) δ` and construct the two bounded value witnesses, their term clauses, and the relation formula in `x ∷ v ∷ z ∷ Γ`; the inward map will reverse the same data.
<!--zh-->
定理 `atomBridge` 现在让 `direct-extension` 在每个编码环境上比较原子的语义值与 `atomEx`。其前向映射必须从 `Meaning (op t u) δ` 出发，构造两个有界取值见证、相应词项子句，以及 `x ∷ v ∷ z ∷ Γ` 中的关系公式；反向映射则沿同一批数据返回。
<!--ja-->
定理 `atomBridge` はここで、各符号化環境について原子の意味論的な値と `atomEx` を比較するよう `direct-extension` に求めます。その前向きの写像は `Meaning (op t u) δ` から出発し、二つの有界な値の証人、それぞれの項の節、そして `x ∷ v ∷ z ∷ Γ` における関係式を構成しなければなりません。逆向きの写像は同じデータを逆にたどります。
<!--/-->

```agda
    atomBridge : ExtFact (fst (SatW (op t u))) (fst (envSet W n)) (λ z → ⟨ (z ∷ Γ) ⊨ atomEx wi ti ui N0i N1i rel ⟩)
    atomBridge = direct-extension (op t u) (λ z → (z ∷ Γ) ⊨ atomEx wi ti ui N0i N1i rel) out inn
      where
      out : (δ : DB.SM ^ n) (z : S) → fst z ≡ Semantic.graph W δ → ⟨ Meaning (op t u) δ ⟩
          → ⟨ (z ∷ Γ) ⊨ atomEx wi ti ui N0i N1i rel ⟩
```

<!--en-->
The outward construction chooses the actual semantic values of `t` and `u`, embedded into `L`, as the two bounded witnesses. The second components of the restricted-model values prove their membership in the carrier; `term-in` followed by `tIn` and `uIn` supplies the two term clauses, and `cnd-out` followed by the reverse half of `agree` supplies the object-language relation. The nested witnesses are introduced under the two propositional truncations.
<!--zh-->
前向构造选取 `t` 与 `u` 的真实语义值嵌入 `L` 后的结果，作为两个有界见证。限制模型取值的第二分量证明它们属于载体；`term-in` 再接 `tIn` 与 `uIn`，给出两条词项子句；`cnd-out` 再接 `agree` 的反向一半，给出对象语言关系。两层见证分别被引入到两层命题截断之中。
<!--ja-->
外向きの構成では、`t` と `u` の実際の意味論的な値を `L` へ埋め込んだものを、二つの有界な証人として選びます。制限模型での値の第二成分が、それらの台への所属を示します。`term-in` に続く `tIn` と `uIn` が二つの項の節を与え、さらに `cnd-out` に続いて `agree` の逆向きの半分を使うと、対象言語の関係が得られます。二つの証人は、入れ子になった二つの命題的切り詰めの中へ導入されます。
<!--/-->

```agda
      out δ z qz h = ∣ v , subst (λ X → ⟨ fst v ∈ X ⟩) (sym qw) (snd (value t δ))
        , ∣ x , subst (λ X → ⟨ fst x ∈ X ⟩) (sym qw) (snd (value u δ))
          , tIn z v x (term-in t δ z v qz refl)
          , uIn z v x (term-in u δ z x qz refl)
          , agree z v x .snd (cnd-out δ h) ∣₁ ∣₁
```

<!--en-->
The local names `v` and `x` are the embeddings into `L` of the evaluated terms `t` and `u`. They are canonical witnesses for the two value quantifiers of `atomEx`; the atomic code itself names the two term codes, while these witnesses supply their values at the particular environment `δ`.
<!--zh-->
局部名称 `v` 与 `x` 分别是词项 `t`、`u` 的求值嵌入 `L` 后所得的元素。它们是 `atomEx` 两个取值量词的典范见证；原子码本身指名的是两个词项码，而这里的见证给出它们在特定环境 `δ` 处的取值。
<!--ja-->
局所名 `v` と `x` は、評価された項 `t` と `u` をそれぞれ `L` へ埋め込んだ要素です。これらは `atomEx` の二つの値量化に対する正準な証人です。原子の符号そのものが名指すのは二つの項の符号であり、ここでの証人は特定の環境 `δ` におけるそれらの値を与えます。
<!--/-->

```agda
        where
        v x : S
        v = Semantic.intoL W (value t δ)
        x = Semantic.intoL W (value u δ)

```

<!--en-->
The reverse implication of `atomBridge` starts with a meta-level environment `δ`, a coded environment `z`, and an identification of `z` with the canonical graph of `δ`. Its remaining hypothesis says that `atomEx` holds at `z`. The outer propositionally truncated bounded existential supplies a candidate `v`, a proof `hv` that it lies in `W`, and an inner existential proof `h`. Since `Meaning (op t u) δ` is a proposition, `rec₁` may eliminate this truncation, and then the inner one, into that target. At this point `v` is only a candidate for the value of `t`; the term-value record extracted from the inner witness will identify it with the actual semantic value.
<!--zh-->
`atomBridge` 的反向蕴含从元层环境 `δ`、编码环境 `z` 以及 `z` 与 `δ` 的典范图之间的同一视出发。余下的假设断言 `atomEx` 在 `z` 处成立。外层命题截断的有界存在式给出候选值 `v`、它属于 `W` 的证明 `hv`，以及内层存在式的证明 `h`。由于 `Meaning (op t u) δ` 是命题，`rec₁` 可以把这层命题截断消去到该目标中，随后也可如此消去内层命题截断。此时 `v` 还只是 `t` 的候选值；从内层见证取得的词项取值记录才会把它认同为真正的语义值。
<!--ja-->
`atomBridge` の逆向きの含意は、メタレベルの環境 `δ`、符号化された環境 `z`、および `z` を `δ` の正準なグラフと同一視する等式から始まります。残る仮定は、`atomEx` が `z` で成り立つことです。外側の命題的に切り詰められた有界存在は、候補 `v`、それが `W` に属することの証明 `hv`、および内側の存在の証明 `h` を与えます。`Meaning (op t u) δ` は命題なので、`rec₁` によってこの切り詰めをその目標へ消去し、続いて内側の切り詰めも同様に消去できます。この時点の `v` はまだ `t` の値の候補にすぎません。内側の証人から得る項の値の記録によって、初めて実際の意味論的な値と同一視されます。
<!--/-->

```agda
      inn : (δ : DB.SM ^ n) (z : S) → fst z ≡ Semantic.graph W δ
          → ⟨ (z ∷ Γ) ⊨ atomEx wi ti ui N0i N1i rel ⟩ → ⟨ Meaning (op t u) δ ⟩
      inn δ z qz = rec₁ (snd (Meaning (op t u) δ)) (λ { (v , hv , h) →
        rec₁ (snd (Meaning (op t u) δ)) (λ { (x , hx , ht , hu , hr) →
          cnd-in δ (subst2 R (term-out t δ z v qz (tOut z v x ht))
```

<!--en-->
The inner witness supplies a second candidate `x`, its membership proof `hx : x ∈ W`, proofs `ht` and `hu` of the two term clauses, and a proof `hr` of the object-language relation. The proofs `hv` and `hx` record the bounds of the two existential quantifiers, but no further use of them is needed here. First, `agree z v x .fst` reads `hr` as `R (fst v) (fst x)`. Because `z` is the canonical graph of `δ`, `tOut` and `uOut` feed the two term-clause proofs to `term-out`, which identifies the underlying sets of `v` and `x` with those of the semantic values of `t` and `u`. Then `subst2` transports `R` along those identifications, and `cnd-in` turns the transported relation into `Meaning (op t u) δ`. This completes the atomic bridge. Downstream it is instantiated for membership and equality. In `SatSoundC`, subcode closure and structural recursion pin table entries to `SatW` by comparing extension facts; in `SatHoldsC`, decoding, prescribed table values, totality, and the stated domain let the same bridges fill all ten clauses. `SatisfactionDescription` supplies the code-domain and environment-tower facts, proves that the canonical graph `SatGraph.pairs W` satisfies `tableAt`, and packages `towerAt`, `codesAt`, and `tableAt` as `satAt`. Its `SatRead` module exposes two-way membership readers for the resulting table graph, code set, and environment tower.
<!--zh-->
内层见证给出第二个候选值 `x`、其成员证明 `hx : x ∈ W`、两条词项子句的证明 `ht` 与 `hu`，以及对象语言关系的证明 `hr`。`hv` 与 `hx` 记录两个存在量词的界，但这里无需再使用它们。首先，`agree z v x .fst` 把 `hr` 读成 `R (fst v) (fst x)`。由于 `z` 是 `δ` 的典范图，`tOut` 与 `uOut` 把两条词项子句证明交给 `term-out`；所得等式分别把 `v`、`x` 的底层集合认同为 `t`、`u` 的语义值之底层集合。随后，`subst2` 沿这两条同一视搬运 `R`，最后 `cnd-in` 把搬运后的关系化为 `Meaning (op t u) δ`。原子桥至此完成。下游分别为隶属关系与相等关系实例化该桥。在 `SatSoundC` 中，对子码封闭与公式结构递归通过比较外延事实，把表项固定为 `SatW`；在 `SatHoldsC` 中，码的解码、给定的表值、全定义性与指定定义域使同一组桥能够填入全部十条子句。`SatisfactionDescription` 提供码域与环境塔的事实，证明典范图 `SatGraph.pairs W` 满足 `tableAt`，并把 `towerAt`、`codesAt` 与 `tableAt` 封装为 `satAt`。其中的 `SatRead` 模块为所得满足图、码集与环境塔给出双向隶属读式。
<!--ja-->
内側の証人は、第二の候補 `x`、その所属証明 `hx : x ∈ W`、二つの項の節の証明 `ht` と `hu`、および対象言語の関係の証明 `hr` を与えます。`hv` と `hx` は二つの存在量化子の境界を記録しますが、ここではそれ以上使う必要はありません。まず `agree z v x .fst` が `hr` を `R (fst v) (fst x)` として読み取ります。`z` は `δ` の正準なグラフなので、`tOut` と `uOut` は二つの項の節の証明を `term-out` に渡します。得られる等式は、`v` と `x` の基礎の集合を、それぞれ `t` と `u` の意味論的な値の基礎の集合と同定します。次に `subst2` がその二つの同定に沿って `R` を運び、最後に `cnd-in` が運ばれた関係を `Meaning (op t u) δ` に変えます。これで原子の橋が完成します。下流では所属と等号の場合にそれぞれ具体化されます。`SatSoundC` では、部分符号に関する閉性と論理式の構造再帰により、外延事実を比較して表要素を `SatW` に固定します。`SatHoldsC` では、コードの復号、あらかじめ与えられた表の値、全域性、および指定された領域を使い、同じ橋によって十個の節をすべて満たします。`SatisfactionDescription` はコード領域と環境の塔に関する事実を与え、正準なグラフ `SatGraph.pairs W` が `tableAt` を満たすことを証明し、`towerAt`、`codesAt`、`tableAt` を `satAt` としてまとめます。その `SatRead` モジュールは、得られた充足関係グラフ、コード集合、環境の塔について、所属を両方向に読む補題を公開します。
<!--/-->

```agda
            (term-out u δ z x qz (uOut z v x hu)) (agree z v x .fst hr)) }) h })
```

<!--en-->
## Recap
<!--zh-->
## 回顾
<!--ja-->
## まとめ
<!--/-->

<!--en-->
The clause semantics is now tied to ordinary satisfaction in both directions. Environment graphs interpret variables, the recursive bridges handle the logical constructors, and the atomic bridge transports membership and equality through the values of their terms. The proof uses only the existence and extensional facts stated by the coded table; it does not assume that an arbitrary table relation is already functional.
<!--zh-->
各条子句的内部语义至此与通常的满足关系双向对应。环境图解释变元，递归桥接处理逻辑构造子，原子桥接则沿词项取值搬运隶属关系与相等关系。证明只使用编码表所陈述的存在事实与外延事实，并未假定任意表关系本身已经是函数。
<!--ja-->
各節の内部意味論は、通常の充足関係と双方向に結びつきました。環境グラフが変数を解釈し、再帰的な橋渡しが論理構成子を扱い、原子式の橋渡しが項の値に沿って所属と等号を運びます。証明が用いるのは、符号化された表が述べる存在と外延性の事実だけであり、任意の表関係がすでに関数的であるとは仮定していません。
<!--/-->
