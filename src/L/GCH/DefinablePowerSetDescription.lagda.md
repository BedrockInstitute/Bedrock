<!--en-->
The problem of this chapter is to recognize, by a bounded formula, the collection of subsets of a constructible carrier that are first-order definable over that carrier with parameters from it. This collection is the definable power set `𝒟ₒ`, not the full internal power set. Its internal description is correct only when the numeral tags, code domain, and satisfaction table have their intended meanings.
<!--zh-->
本章要解决的问题是：怎样用有界公式识别一个可构造载体的所有一阶可定义子集，其中允许使用该载体中的参数。这个集合是可定义幂集 `𝒟ₒ`，不是完整的内部幂集。只有当数码标签、码域与满足关系表都具有预期含义时，内部描述才是正确的。
<!--ja-->
この章の課題は、構成可能な台の要素をパラメータとして許した一階定義可能部分集合の集まりを、有界論理式で認識することです。この集まりは定義可能冪集合 `𝒟ₒ` であり、完全な内部冪集合ではありません。内部の記述が正しくなるには、数項のタグ、符号領域、充足関係表がそれぞれ意図した意味をもつ必要があります。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

```

<!--en-->
The construction uses excluded middle as the book's single explicit classical hypothesis. Propositional truncation will nevertheless remain visible throughout: an existence proof may establish that a formula or table value exists without selecting one globally.
<!--zh-->
这个构造把排中律作为全书唯一的显式经典假设。即便如此，命题截断仍会贯穿本章：存在性证明可以表明某个公式或表值存在，却不从中作出全局选择。
<!--ja-->
この構成では、排中律を本書で唯一の明示的な古典的仮定として用います。それでも命題的切り詰めは全体に残ります。存在証明は、ある論理式や表の値が存在することを示しても、それを大域的に選び出しません。
<!--/-->

```agda
open import Base.Prelude
open import Base.Classical using ( LEM )

```

<!--en-->
Fix a universe level `ℓ` and an instance `lem : LEM (ℓ-suc ℓ)`. Every result in the module, including the final soundness and completeness statements, is understood under precisely this hypothesis.
<!--zh-->
固定宇宙层级 `ℓ` 及实例 `lem : LEM (ℓ-suc ℓ)`。本模块的每项结果，包括最后的可靠性与完备性定理，都恰在这一假设下成立。
<!--ja-->
宇宙レベル `ℓ` と実例 `lem : LEM (ℓ-suc ℓ)` を固定します。このモジュールのすべての結果は、最後の健全性と完全性を含め、ちょうどこの仮定のもとで成り立ちます。
<!--/-->

```agda
module L.GCH.DefinablePowerSetDescription {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

```

<!--en-->
The object-language description is deliberately bounded. It is assembled from membership atoms, conjunction, implication, and bounded existential and universal quantifiers; `checkΔ₀` will later verify this syntactic shape. Constant mapping is needed when an externally given formula is compared with its interpretation in the coded satisfaction construction.
<!--zh-->
对象语言中的描述刻意保持有界。它只由隶属原子式、合取、蕴涵、有界存在量词与有界全称量词组成；稍后 `checkΔ₀` 将核验这一句法形状。把外部给定的公式与编码满足构造中的解释相比较时，还需要常元映射。
<!--ja-->
対象言語での記述は、意図的に有界に保ちます。所属原子式、連言、含意、有界存在量化子、有界全称量化子だけから組み立て、後で `checkΔ₀` がこの構文上の形を検査します。外から与えた論理式を、符号化された充足構成での解釈と比較する際には、定数の写像も用います。
<!--/-->

```agda
open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula; var; _∈̇_; _∧̇_; _⇒̇_; ∃̇∈; ∀̇∈ )
open import FOL.LevyHierarchy using ( Δ₀; checkΔ₀ )
open import FOL.Manipulation.ConstantMapping using ( mapFo )
import FOL.Absoluteness
```

<!--en-->
The intended output is `𝒟ₒ W`: the set of subsets of `W` definable in the restricted structure over `W`, with parameters from `W`. Extensionality will identify a candidate output with this set once both membership directions have been proved, while ordered-pair codes represent environments, formula keys, and table entries.
<!--zh-->
预期输出是 `𝒟ₒ W`：在 `W` 上的受限结构中、允许使用 `W` 中参数而可定义的子集所成的集合。证明两个隶属方向后，外延性将候选输出与这个集合等同；有序对编码则用来表示环境、公式键与表条目。
<!--ja-->
意図する出力は `𝒟ₒ W`、すなわち `W` 上の制限構造で `W` の要素をパラメータとして定義できる部分集合の集まりです。二つの所属方向を証明すれば、外延性によって候補の出力をこの集合と同一視できます。順序対の符号は、環境、論理式の鍵、表の項目を表します。
<!--/-->

```agda
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ; extensionalV )
open import V.Coding {ℓ} using ( pr )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans; 𝒟ₒ; 𝒟ₒ-intro; 𝒟ₒ-inv )
open import L.Definability {ℓ} using ( module DefOf )
open import L.Coding.Model {ℓ} using ( prAtL; container )
```

<!--en-->
For a formula `ψ`, the satisfaction construction records which one-entry environments satisfy `ψ`. The bridge theorem identifies the resulting slice of `W` with the subset defined by `ψ`. The genuine code set contains the key built from `ψ`, and functionality of the genuine satisfaction table fixes the value at that key. These facts become available only after `satAt` has certified the proposed code set and table; they do not make decoding unique or select a defining formula for a subset.
<!--zh-->
对公式 `ψ`，满足构造记录哪些单条目环境满足 `ψ`。桥接定理把由此从 `W` 中切出的部分认同为 `ψ` 所定义的子集。真正的码集包含由 `ψ` 构造的键，而真正满足关系表的函数性固定该键处的取值。只有在 `satAt` 已校准候选码集与表之后，才能使用这些事实；它们既不使解码唯一，也不为某个子集选取定义公式。
<!--ja-->
論理式 `ψ` に対し、充足構成はどの一項環境が `ψ` を満たすかを記録します。橋渡し定理は、そこから `W` の中で切り出される部分を、`ψ` が定義する部分集合と同一視します。実際の符号集合は `ψ` から作られる鍵を含み、実際の充足関係表の関数性がその鍵での値を定めます。これらを使えるのは、候補の符号集合と表を `satAt` が保証した後だけです。復号が一意になるわけでも、部分集合の定義論理式が選ばれるわけでもありません。
<!--/-->

```agda
open import L.Coding.SatisfactionBridge {ℓ} lem using ( asConst; defSet-Sat )
open import L.Coding.DefinablePowerSet {ℓ} lem using ( envOne )
open import L.Coding.CodeSet {ℓ} lem using ( keyS; key∈AllCodes )
open import L.Coding.UniformSatisfaction {ℓ} lem using ( module Table; val-at )
open import L.Coding.Satisfaction {ℓ} lem using ( Sat )
```

<!--en-->
Every quantifier in the description must remain bounded by a set already present in the environment. The auxiliary quantifiers below express the two components of an ordered-pair code within those bounds, and their two directions let us pass between object-language satisfaction and the corresponding semantic witnesses.
<!--zh-->
描述中的每个量词都必须受环境中已有集合约束。下文的辅助量词在这些界限内表达有序对编码的两个分量；它们的两个方向使我们能在对象语言的满足与相应语义见证之间来回转换。
<!--ja-->
記述に現れる量化子はすべて、環境にすでにある集合によって有界でなければなりません。以下の補助量化子は、その範囲内で順序対の符号の二成分を表します。二方向の補題によって、対象言語での充足と対応する意味論的な証人との間を行き来できます。
<!--/-->

```agda
open import L.Coding.Quantification {ℓ} using
  ( sh; i0; i1; i3; i6; f0; f1; down
  ; sndEx; sndAll; sndEx-out; sndAll-in; fillSnd; useSnd
  ; pr-out; pr-in; sndS )
open import L.Coding.CodeDomain {ℓ} using ( Tags )
```

<!--en-->
The ten distinguished slots are interpreted as the numerals zero through nine by `Tags`. In particular, the clauses below use the tags zero and one to recognize a one-entry environment and a key of arity one. The separate predicate `satAt` supplies the stronger semantic fact that the proposed code domain and table implement the alphabet and recursive satisfaction construction over the carrier.
<!--zh-->
`Tags` 把十个指定槽位解释为数码零至九。特别地，下文的子句用标签零识别单条目环境，并用标签一识别元数一的键。另一个谓词 `satAt` 提供更强的语义事实：候选码域与表确实实现了该载体上的字母表和递归满足构造。
<!--ja-->
`Tags` は、指定された十個の枠を数項 0 から 9 と解釈します。特に以下の節では、タグ 0 で一項環境を、タグ 1 でアリティ 1 の鍵を認識します。別の述語 `satAt` はさらに強く、候補のコード領域と表が、その台上のアルファベットと再帰的な充足構成を実現していることを保証します。
<!--/-->

```agda
open import L.Coding.CodeAlphabet {ℓ} using ( module Alphabet )
open import L.GCH.SatisfactionDescription {ℓ} lem using ( satAt; module SatRead; module Match )

```

<!--en-->
An environment is represented by a finite vector of constructible sets. Products combine the two membership conditions that define a slice, and their propositionhood ensures that truncated witnesses may be eliminated into these conditions without introducing a choice.
<!--zh-->
环境由可构造集合组成的有限向量表示。积类型合并定义切出关系的两个隶属条件，而这些条件的命题性保证可以把截断见证消去到其中，而不引入选择。
<!--ja-->
環境は構成可能集合からなる有限ベクトルで表します。積は切り出し関係を定める二つの所属条件を組み合わせます。それらが命題であるため、選択を導入することなく、切り詰められた証人をその条件へ消去できます。
<!--/-->

```agda
open import Cubical.Data.Nat using ( _+_ )
open import Cubical.Data.Unit using ( tt )
open import Cubical.Data.Vec using ( _∷_; lookup )
open import Cubical.Data.Sigma using ( _×_ )
open import Cubical.Foundations.HLevels using ( isProp× )
```

<!--en-->
The proofs repeatedly turn pointwise equivalences of membership into equalities of sets. Membership is proposition-valued, so a merely existing code, formula, or presentation can be eliminated while proving either membership direction; `∈-asFiber` then recovers a presentation index when an ambient member must be read as an element of a carrier.
<!--zh-->
证明会反复把逐点的隶属等价转成集合相等。隶属是命题值的，因此在证明任一隶属方向时，可以消去仅仅存在的码、公式或表示；当外围成员需要作为载体元素读取时，`∈-asFiber` 再恢复其呈现索引。
<!--ja-->
証明では、点ごとの所属の同値を集合の等しさへ繰り返し変換します。所属は命題値なので、どちらの所属方向を示すときにも、単に存在する符号・論理式・表示を消去できます。周囲の集合の要素を台の要素として読む必要があるときは、`∈-asFiber` が表示の添字を復元します。
<!--/-->

```agda
open import Cubical.Functions.Logic using ( ⇔toPath )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁; ∣_∣₁; squash₁ )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_; setIsSet )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ∈-asFiber )
```

<!--en-->
The von Neumann numerals used as tags live in the cumulative hierarchy. In particular, zero marks the only entry of a one-variable environment, while one marks the arity of the formulas considered here.
<!--zh-->
用作标签的冯·诺伊曼数码位于累积层级中。特别地，零标记单变元环境的唯一条目，一标记本章所考虑公式的元数。
<!--ja-->
タグとして使うフォン・ノイマン数項は累積階層の中にあります。特に 0 は一変数環境の唯一の項目を示し、1 はここで扱う論理式のアリティを示します。
<!--/-->

```agda
open import Cubical.HITs.CumulativeHierarchy.Constructions using ( module InfinitySet )
open InfinitySet {ℓ} using ( #_ )

```

<!--en-->
Write `S` for the carrier of constructible sets. An element of `S` consists of an underlying set together with its constructibility certificate, so bounded witnesses in the formulas remain inside the intended model.
<!--zh-->
记可构造集合的载体为 `S`。`S` 的元素由底层集合及其可构造性证书组成，因此公式中的有界见证始终留在预期模型内。
<!--ja-->
構成可能集合の台を `S` と書きます。`S` の要素は基礎の集合とその構成可能性の証明書からなるので、論理式の有界な証人は意図したモデルの内部にとどまります。
<!--/-->

```agda
open hPropStructure 𝒮ʟ using ( S )

```

<!--en-->
We write `γ ⊨ φ` for satisfaction of an object-language formula at a finite environment of constructible sets. The absoluteness result behind this notation lets the later semantic argument compare that internal reading with ordinary membership in the surrounding cumulative hierarchy.
<!--zh-->
以 `γ ⊨ φ` 表示对象语言公式在一个可构造集合有限环境处的满足。该记号背后的绝对性结果使后面的语义论证能把这种内部读法与周遭累积层级中的通常隶属相比较。
<!--ja-->
構成可能集合の有限環境で対象言語の論理式が充足されることを `γ ⊨ φ` と書きます。この記法の背後にある絶対性によって、後の意味論的な議論では、この内部の読みを周囲の累積階層における通常の所属と比較できます。
<!--/-->

```agda
module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans using ( _^_; _⊨ᵐ_ )
open AbsL using ( _^_ ) renaming ( _⊨ᵐ_ to _⊨_ )
```

<!--en-->
A singleton environment is described by two bounded clauses over one slot: every member of the coded set `e` is the ordered pair of the tag zero and the value `z`, and some member of `e` is that pair. The universal clause excludes all other members, and the existential clause excludes the empty set.
<!--zh-->
单点环境由一个槽位上的两条有界子句描述：编码集合 `e` 的每个成员都是「标签零与值 `z` 的有序对」，且 `e` 中存在一个成员等于该对。全称子句排除所有其他成员，存在子句排除空集。
<!--ja-->
単項環境は、一つの枠の上の二つの有界の節で記述されます。符号化された集合 `e` のすべての要素が、タグ 0 と値 `z` の順序対であり、`e` の中にその対に等しい要素が存在する、というものです。全称の節がほかのすべての要素を排除し、存在の節が空集合を排除します。
<!--/-->

```agda
singleOf : ∀ {j} → Fin j → Fin j → Fin j → Formula S j
singleOf e N0 z = ∀̇∈ (var e) (prAtL i0 (sh 1 N0) (sh 1 z)) ∧̇ ∃̇∈ (var e) (prAtL i0 (sh 1 N0) (sh 1 z))

```

<!--en-->
The definable-subset clause has two conjuncts. The first says every member of the coded set `x` lies in `w` and has its one-entry environment inside the value `y`. The second says every member `z` of `w` whose one-entry environment lies in `y` belongs to `x`. Together they say exactly that `x` is cut out of `w` by the value `y`.
<!--zh-->
可定义子集子句有两个合取支。第一支说编码集合 `x` 的每个成员都属于 `w`，且其单条目环境落在值 `y` 中。第二支说 `w` 的每个成员 `z`，只要其单条目环境落在 `y` 中，就属于 `x`。两者合起来恰好说明 `x` 是由值 `y` 从 `w` 中切出的。
<!--ja-->
定義可能部分集合の節には二つの連言肢があります。第一は、符号化された集合 `x` のすべての要素が `w` に属し、その一項環境が値 `y` に属することを述べます。第二は、`w` の要素 `z` のうち、その一項環境が `y` に属するものはすべて `x` に属することを述べます。合わせると、`x` が値 `y` によって `w` から切り出されることが分かります。
<!--/-->

```agda
definesB : ∀ {j} → Fin j → Fin j → Fin j → Fin j → Formula S j
definesB x w y N0 =
    ∀̇∈ (var x) ((var i0 ∈̇ var (sh 1 w)) ∧̇ ∃̇∈ (var (sh 1 y)) (singleOf i0 (sh 2 N0) i1))
  ∧̇ ∀̇∈ (var w) (∃̇∈ (var (sh 1 y)) (singleOf i0 (sh 2 N0) i1) ⇒̇ (var i0 ∈̇ var (sh 1 x)))

```

<!--en-->
The membership clause ranges over members of the proposed value. For each member it merely asks for an element `c` of the proposed domain `C` shaped as a pair with tag one, together with a table entry pairing `c` with a value `y` that cuts the member out of `w`. At this stage `c` is only key-shaped: only the later hypothesis `satAt` permits it to be decoded as the key of an actual formula.
<!--zh-->
隶属子句遍历候选值的成员。对每个成员，它只要求候选域 `C` 中有一个形如「标签一与某个第二分量之对」的元素 `c`，并有一个表条目把 `c` 与值 `y` 配对，而 `y` 从 `w` 中切出该成员。此时 `c` 仅具有键的形状；只有稍后加入 `satAt` 假设，才能把它解码为真实公式的键。
<!--ja-->
所属の節は候補の値の要素を走ります。各要素について要求するのは、候補領域 `C` にタグ 1 との対の形をした要素 `c` があり、表の項目が `c` と値 `y` を対にし、その `y` が当の要素を `w` から切り出すことだけです。この段階の `c` は鍵の形をしているにすぎません。後で `satAt` を仮定して初めて、実際の論理式の鍵として復号できます。
<!--/-->

```agda
memAt : ∀ {m} → Fin m → Fin m → Fin m → Fin m → (Fin 10 → Fin m) → Formula S m
memAt v w T C N =
  ∀̇∈ (var v) (∃̇∈ (var (sh 1 C)) (sndEx i0 (sh 2 (N f1))
    (∃̇∈ (var (sh 4 T)) (sndEx i0 i3 (definesB i6 (sh 7 w) i0 (sh 7 (N f0)))))))
```

<!--en-->
The covering clause runs in the converse direction. Whenever an element `c` of `C` has the shape of a tag-one key, it requires merely a table value `y` at `c` and a member `x` of the proposed output cut out by `y`. Thus it covers every key-shaped element of the proposed domain; identifying these with all actual arity-one formula keys again depends on `satAt`.
<!--zh-->
覆盖子句给出反向条件。只要 `C` 的元素 `c` 具有标签一之键的形状，它便仅仅要求 `c` 处有表值 `y`，并且候选输出中有一个由 `y` 切出的成员 `x`。因此它覆盖候选域中每个具有这种形状的元素；要把这些元素认同为全部真实的元数一公式键，仍须依赖 `satAt`。
<!--ja-->
被覆の節は逆向きの条件を与えます。`C` の要素 `c` がタグ 1 の鍵の形をもつなら、`c` での表の値 `y` と、`y` によって切り出される候補出力の要素 `x` が単に存在することを要求します。したがって候補領域の鍵形の要素をすべて覆いますが、それらを実際のアリティ 1 の論理式の鍵すべてと同一視するには、やはり `satAt` が必要です。
<!--/-->

```agda
allAt : ∀ {m} → Fin m → Fin m → Fin m → Fin m → (Fin 10 → Fin m) → Formula S m
allAt v w T C N =
  ∀̇∈ (var C) (sndAll i0 (sh 1 (N f1))
    (∃̇∈ (var (sh 3 T)) (sndEx i0 i3 (∃̇∈ (var (sh 6 v)) (definesB i0 (sh 7 w) i1 (sh 7 (N f0)))))))

```

<!--en-->
The formula `defAt` conjoins the membership and covering clauses. By itself it only relates the proposed output to the proposed code domain and table; combined with correct `Tags` and `satAt` data, the two clauses become the two inclusions proving that the output is `𝒟ₒ W`.
<!--zh-->
公式 `defAt` 合取隶属子句与覆盖子句。它单独只把候选输出同候选码域及表联系起来；与正确的 `Tags` 和 `satAt` 数据结合后，两条子句才成为证明输出等于 `𝒟ₒ W` 的两个包含方向。
<!--ja-->
論理式 `defAt` は、所属の節と被覆の節を連言で結びます。それだけでは候補出力を候補のコード領域と表に関係づけるにすぎません。正しい `Tags` と `satAt` のデータを合わせると、二つの節が、出力は `𝒟ₒ W` であることを示す二つの包含になります。
<!--/-->

```agda


opaque
  defAt : ∀ {m} → Fin m → Fin m → Fin m → Fin m → (Fin 10 → Fin m) → Formula S m
  defAt v w T C N = memAt v w T C N ∧̇ allAt v w T C N

```

<!--en-->
The definition remains opaque in ordinary reasoning so that later arguments use its mathematical interface, the two inclusions, rather than its long syntactic expansion. It is unfolded locally only to verify boundedness and to prove the two reading directions.
<!--zh-->
在通常论证中，这一定义保持不透明，使后续证明通过两个包含方向这一数学接口使用它，而不依赖冗长的句法展开。只有在核验有界性和证明两个读取方向时，才在局部展开它。
<!--ja-->
通常の議論ではこの定義を不透明に保ち、後の証明が長い構文展開ではなく、二つの包含という数学的なインターフェースを使うようにします。展開するのは、有界性の確認と二方向の読みの証明に必要な局所的な範囲だけです。
<!--/-->

```agda
opaque
  unfolding defAt

```

<!--en-->
The Δ₀ certificate is produced by the structural checker: the formula uses only variables, membership, conjunction, implication, and bounded quantifiers. It certifies the shape of the formula, not the correctness of the description.
<!--zh-->
Δ₀ 证书由结构性检查器产出：该公式只用变元、隶属、合取、蕴涵与有界量词。它证明的是公式的形状，而非描述的正确性。
<!--ja-->
Δ₀ の証拠は、構造的な検査によって産み出されます。論理式が使うのは、変数・所属・連言・含意・有界の量化子だけです。証明されるのは論理式の形であって、記述の正しさではありません。
<!--/-->

```agda
  Δ₀-defAt : ∀ {m} (v w T C : Fin m) (N : Fin 10 → Fin m) → Δ₀ (defAt v w T C N)
  Δ₀-defAt v w T C N = checkΔ₀ (defAt v w T C N) tt

```

<!--en-->
Reading the description splits it into its two conjuncts.
<!--zh-->
读取描述即把它拆成两个合取支。
<!--ja-->
記述の読みは、それを二つの連言支に分解します。
<!--/-->

```agda
  defAt-out : ∀ {m} (v w T C : Fin m) (N : Fin 10 → Fin m) (γ : S ^ m)
            → ⟨ γ ⊨ defAt v w T C N ⟩ → ⟨ γ ⊨ memAt v w T C N ⟩ × ⟨ γ ⊨ allAt v w T C N ⟩
  defAt-out v w T C N γ h = h

```

<!--en-->
Filling the description pairs the two conjuncts back together.
<!--zh-->
填充描述把两个合取支重新配对。
<!--ja-->
記述の埋めは、二つの連言支を再び対にします。
<!--/-->

```agda
  defAt-in : ∀ {m} (v w T C : Fin m) (N : Fin 10 → Fin m) (γ : S ^ m)
           → ⟨ γ ⊨ memAt v w T C N ⟩ → ⟨ γ ⊨ allAt v w T C N ⟩ → ⟨ γ ⊨ defAt v w T C N ⟩
  defAt-in v w T C N γ h1 h2 = h1 , h2
```

<!--en-->
The first semantic calculation concerns `singleOf`. Fix the coded set `E` and value `Z`, and assume that the distinguished tag really denotes zero. Under this assumption the two bounded clauses will be shown equivalent to the set equality `E = envOne Z`.
<!--zh-->
第一个语义计算处理 `singleOf`。固定编码集合 `E` 与值 `Z`，并假定指定标签确实指称零。在此前提下，将证明两条有界子句等价于集合等式 `E = envOne Z`。
<!--ja-->
最初の意味論的な計算では `singleOf` を扱います。符号化された集合 `E` と値 `Z` を固定し、指定されたタグが実際に 0 を表すと仮定します。この仮定の下で、二つの有界な節が集合の等式 `E = envOne Z` と同値であることを示します。
<!--/-->

```agda
module _ {j : ℕ} (e N0 z : Fin j) (δ : S ^ j) (q0 : fst (lookup N0 δ) ≡ # 0) where
  private
    E = fst (lookup e δ)
    Z = fst (lookup z δ)

```

<!--en-->
Reading the singleton clause yields the equality of the coded set with the standard singleton environment of the value. Forward: every member of the coded set is the ordered pair of the numeral zero and the value, transported through the adequacy of the pairing atom.
<!--zh-->
读取单点子句得到「编码集合等于值的标准单点环境」。正向：编码集合的每个成员都是「数码零与值」的有序对，经配对原子的充分性搬运。
<!--ja-->
単項の節の読みから、符号化された集合が値の正準な単項環境と等しいことが得られます。順方向では、符号化された集合のすべての要素が、数項ゼロと値の順序対であり、対のアトムの妥当性に沿って運ばれます。
<!--/-->

```agda
  singleOf-out : ⟨ δ ⊨ singleOf e N0 z ⟩ → E ≡ envOne Z
  singleOf-out (hall , hex) = extensionalV (λ y → ⇔toPath (fwd y) (bwd y))
    where
    fwd : (y : V ℓ) → ⟨ y ∈ E ⟩ → ⟨ y ∈ envOne Z ⟩
    fwd y hy = ∣ lift zero , sym (pr-out i0 (sh 1 N0) (sh 1 z) (down (lookup e δ) y hy ∷ δ) (hall (down (lookup e δ) y hy) hy)
```

<!--en-->
For the reverse inclusion, begin with a member of the standard one-entry environment. The existential conjunct supplies some member of the coded set, and its pairing equation, together with the known zero tag, identifies that member with the one already given. Transporting its membership along this equality puts the original member in the coded set.
<!--zh-->
证明反向包含时，从标准单条目环境的一个成员出发。存在合取支给出编码集合的某个成员；它的配对等式与已知的零标签一起，把这个成员认同为起初给定的成员。沿此等式搬运隶属证明，便得到原成员属于编码集合。
<!--ja-->
逆向きの包含では、正準な一項環境の要素から始めます。存在側の連言肢が符号化された集合のある要素を与え、その対の等式と既知のタグ 0 によって、その要素を最初に与えた要素と同一視できます。この等式に沿って所属を移送すれば、元の要素が符号化された集合に属することが得られます。
<!--/-->

```agda
                                 ∙ cong (λ a → pr a Z) q0) ∣₁
    bwd : (y : V ℓ) → ⟨ y ∈ envOne Z ⟩ → ⟨ y ∈ E ⟩
    bwd y = PT.rec (snd (y ∈ E))
      (λ { (lift zero , qy) → PT.rec (snd (y ∈ E))
        (λ { (y' , (y'∈ , hy')) →
```

<!--en-->
A member of `envOne Z` is the ordered pair `pr (# 0) Z`. Rewriting the tag slot as the numeral zero therefore identifies this member with the ordered pair required by `singleOf`; it does not identify the member with `Z` itself.
<!--zh-->
`envOne Z` 的成员是有序对 `pr (# 0) Z`。因此，把标签槽改写为数码零后，这个成员便与 `singleOf` 所要求的有序对认同；它并不与 `Z` 本身认同。
<!--ja-->
`envOne Z` の要素は順序対 `pr (# 0) Z` です。したがってタグの枠を数項 0 に書き換えると、この要素は `singleOf` が要求する順序対と同一視されます。要素そのものが `Z` と同一視されるわけではありません。
<!--/-->

```agda
          subst (λ u → ⟨ u ∈ E ⟩)
            (pr-out i0 (sh 1 N0) (sh 1 z) (y' ∷ δ) hy' ∙ cong (λ a → pr a Z) q0 ∙ qy) y'∈ })
        hex
         ; (lift (suc ()) , _) })

```

<!--en-->
Conversely, assume the coded set equals the standard one-entry environment. Its unique index is zero, so every member has the required ordered-pair form; impossible successor indices close the remaining cases. The canonical zero entry supplies the bounded existential witness, and transport along the assumed equality supplies its membership.
<!--zh-->
反过来，假设编码集合等于标准单条目环境。该环境唯一的索引是零，所以每个成员都具有所需的有序对形式；其余后继索引情形由不可能性排除。典范的零号条目提供有界存在见证，沿所给等式搬运则提供它的隶属证明。
<!--ja-->
逆に、符号化された集合が正準な一項環境に等しいと仮定します。その環境の唯一の添字は 0 なので、各要素は必要な順序対の形をもち、残る後者添字の場合は不可能性で閉じます。正準な 0 番の項目が有界存在の証人を与え、仮定した等式に沿う移送がその所属を与えます。
<!--/-->

```agda
  singleOf-in : E ≡ envOne Z → ⟨ δ ⊨ singleOf e N0 z ⟩
  singleOf-in q =
      (λ y hy → pr-in i0 (sh 1 N0) (sh 1 z) (y ∷ δ)
         (PT.rec (setIsSet (fst y) (pr (fst (lookup N0 δ)) Z))
           (λ { (lift zero , qy) → sym qy ∙ cong (λ a → pr a Z) (sym q0) ; (lift (suc ()) , _) })
```

<!--en-->
The member is named, its membership is transported, and the existential witness pairs the zero numeral with the value, transported against the tag equation.
<!--zh-->
该成员被命名，其隶属被搬运，而存在见证把零数码与值配对，并逆着标签等式搬运。
<!--ja-->
要素に名前が与えられ、その所属が運ばれます。そして存在の証人は、ゼロの数項と値の対を、タグの等式に逆らってまとめます。
<!--/-->

```agda
           (subst (λ u → ⟨ fst y ∈ u ⟩) q hy)))
    , ∣ yS , ( subst (λ u → ⟨ pr (# 0) Z ∈ u ⟩) (sym q) ∣ lift zero , refl ∣₁
             , pr-in i0 (sh 1 N0) (sh 1 z) (yS ∷ δ) (cong (λ a → pr a Z) (sym q0)) ) ∣₁
    where
    yS : S
```

<!--en-->
The named member is the presentation, inside the coded set, of the pair of the zero numeral and the value.
<!--zh-->
被命名的成员是「零数码与值的对」在编码集合内的呈现。
<!--ja-->
名前のついた要素は、数項ゼロと値の対の、符号化された集合の中での提示です。
<!--/-->

```agda
    yS = down (lookup e δ) (pr (# 0) Z) (subst (λ u → ⟨ pr (# 0) Z ∈ u ⟩) (sym q) ∣ lift zero , refl ∣₁)
```

<!--en-->
The cut relation between a set `X`, a carrier `Wv`, and a value `Y` is a pair of pointwise directions: every member of `X` lies in `Wv` with its singleton environment in `Y`, and every member of `Wv` whose singleton environment lies in `Y` belongs to `X`. The quantification is over constructible sets, so the relation is stated on the constructible carrier.
<!--zh-->
集合 `X`、载体 `Wv` 与值 `Y` 之间的切割关系是逐点双向的：`X` 的每个成员都属于 `Wv` 且其单点环境在 `Y` 中；而 `Wv` 中单点环境落在 `Y` 的每个成员都属于 `X`。量化遍历可构造集合，因此该关系在可构造载体上陈述。
<!--ja-->
集合 `X`・台 `Wv`・値 `Y` の間の切り出しの関係は、各点での双方向です。`X` のすべての要素は `Wv` に属しその単項環境が `Y` の中にあり、`Wv` の要素のうちその単項環境が `Y` の中にあるものはすべて `X` に属します。量化は構成可能な集合の上を行われるので、この関係は構成可能な台の上で述べられます。
<!--/-->

```agda
Cuts : (X Wv Y : V ℓ) → Type (ℓ-suc ℓ)
Cuts X Wv Y = ((z : S) → ⟨ fst z ∈ X ⟩ → ⟨ fst z ∈ Wv ⟩ × ⟨ envOne (fst z) ∈ Y ⟩)
            × ((z : S) → ⟨ fst z ∈ Wv ⟩ → ⟨ envOne (fst z) ∈ Y ⟩ → ⟨ fst z ∈ X ⟩)

```

<!--en-->
To compare the object-language clause with the mathematical cut relation, fix the slots for `x`, `w`, `y`, and the zero tag. Their interpretations are named `X`, `Wv`, and `Y`; the tag equation is exactly what lets `singleOf` denote the standard one-entry environment.
<!--zh-->
为了把对象语言子句与数学上的切割关系比较，固定 `x`、`w`、`y` 与零标签的槽位。将它们的解释分别记作 `X`、`Wv` 与 `Y`；标签等式恰好使 `singleOf` 能表示标准单条目环境。
<!--ja-->
対象言語の節を数学的な切り出し関係と比較するため、`x`、`w`、`y`、タグ 0 の枠を固定します。それぞれの解釈を `X`、`Wv`、`Y` と名付けます。タグの等式があるからこそ、`singleOf` は正準な一項環境を表せます。
<!--/-->

```agda
module _ {j : ℕ} (x w y N0 : Fin j) (δ : S ^ j) (q0 : fst (lookup N0 δ) ≡ # 0) where
  private
    X = fst (lookup x δ)
    Wv = fst (lookup w δ)
    Y = fst (lookup y δ)
```

<!--en-->
Because `Y` is a constructible set, any proof that a one-entry environment belongs to `Y` can be converted into a carrier representative of that environment. This presentation is what permits the bounded existential in `definesB` to range over an actual member of `Y`.
<!--zh-->
由于 `Y` 是可构造集合，单条目环境属于 `Y` 的任何证明都能转换为该环境的一个载体表示。正是这个呈现使 `definesB` 中的有界存在量词能够在 `Y` 的实际成员上取值。
<!--ja-->
`Y` は構成可能集合なので、一項環境が `Y` に属するという証明から、その環境を表す台の要素を得られます。この表示があるため、`definesB` の有界存在量化子は `Y` の実際の要素を証人にできます。
<!--/-->

```agda
    YS = lookup y δ

```

<!--en-->
Reading the existential of the singleton clause converts it into membership of the standard singleton environment in the value: the witness is a member of the value, and the singleton clause identifies the coded entry with the standard environment of the index.
<!--zh-->
读取单点子句的存在量化，将其转换为标准单点环境在值中的隶属：见证是值的成员，而单点子句把编码条目认同为该索引的标准环境。
<!--ja-->
単項の節の存在量化を読むと、それが、正準な単項環境の値の中での所属に変換されます。証人は値の要素であり、単項の節が、符号化された項目をその索引の正準な環境と同一視します。
<!--/-->

```agda
    one-out : (z : S) → ⟨ (z ∷ δ) ⊨ ∃̇∈ (var (sh 1 y)) (singleOf i0 (sh 2 N0) i1) ⟩ → ⟨ envOne (fst z) ∈ Y ⟩
    one-out z = PT.rec (snd (envOne (fst z) ∈ Y))
      (λ { (e , (e∈ , he)) → subst (λ u → ⟨ u ∈ Y ⟩) (singleOf-out i0 (sh 2 N0) i1 (e ∷ z ∷ δ) q0 he) e∈ })

```

<!--en-->
Filling the existential is the converse: the standard singleton environment is presented inside the value, and the singleton clause is filled at the extended environment.
<!--zh-->
填充存在量化是反向：标准单点环境在值内被呈现，而单点子句在延拓环境处填充。
<!--ja-->
存在量化の埋めは逆です。正準な単項環境は値の中で提示され、単項の節は延長された環境のもとで埋められます。
<!--/-->

```agda
    one-in : (z : S) → ⟨ envOne (fst z) ∈ Y ⟩ → ⟨ (z ∷ δ) ⊨ ∃̇∈ (var (sh 1 y)) (singleOf i0 (sh 2 N0) i1) ⟩
    one-in z h = ∣ down YS (envOne (fst z)) h , (h , singleOf-in i0 (sh 2 N0) i1 (down YS (envOne (fst z)) h ∷ z ∷ δ) q0 refl) ∣₁

```

<!--en-->
Reading the definable-subset clause produces the two directions of the cut relation. The first conjunct gives, for each member of `X`, its membership in `Wv` and membership of its one-entry environment in `Y`; the second converts these two facts back into membership in `X`.
<!--zh-->
读取可定义子集子句便得到切割关系的两个方向。第一个合取支对 `X` 的每个成员给出它属于 `Wv`，以及其单条目环境属于 `Y`；第二个合取支把这两个事实转换回该成员属于 `X`。
<!--ja-->
定義可能部分集合の節を読むと、切り出し関係の二つの方向が得られます。第一の連言肢は、`X` の各要素が `Wv` に属し、その一項環境が `Y` に属することを与えます。第二の連言肢は、この二つの事実から `X` への所属を戻します。
<!--/-->

```agda
  definesB-out : ⟨ δ ⊨ definesB x w y N0 ⟩ → Cuts X Wv Y
  definesB-out (h1 , h2) = (λ z hz → h1 z hz .fst , one-out z (h1 z hz .snd)) , (λ z hw he → h2 z hw (one-in z he))

```

<!--en-->
Conversely, the two pointwise directions in `Cuts X Wv Y` fill the two conjuncts of the object-language definable-subset clause. The private conversions above translate precisely between the bounded singleton witness and membership of the standard one-entry environment in `Y`.
<!--zh-->
反过来，`Cuts X Wv Y` 的两个逐点方向填充对象语言中可定义子集子句的两个合取支。上面的私有转换恰在「有界的单条目见证」与「标准单条目环境属于 `Y`」之间往返。
<!--ja-->
逆に、`Cuts X Wv Y` の二つの各点的な方向から、対象言語における定義可能部分集合の節の二つの連言肢を満たせます。上の内部変換は、有界な一項環境の証人と、正準な一項環境が `Y` に属することとの間を正確に行き来します。
<!--/-->

```agda
  definesB-in : Cuts X Wv Y → ⟨ δ ⊨ definesB x w y N0 ⟩
  definesB-in (o , i) = (λ z hz → o z hz .fst , one-in z (o z hz .snd)) , (λ z hw he → i z hw (one-out z he))
```

<!--en-->
## Reading the bounded subset clauses
<!--zh-->
## 读取有界子集的诸子句
<!--ja-->
## 有界部分集合の各節を読む
<!--/-->

<!--en-->
The full reading module names the four sets: the proposed value, the carrier, the table, and the code domain.
<!--zh-->
完整读取模块命名四个集合：拟议值、载体、表与码域。
<!--ja-->
完全な読みのモジュールは、四つの集合、すなわち提案された値・台・表・コードの定義域に名前を与えます。
<!--/-->

```agda
module Read {m : ℕ} (v w T C : Fin m) (N : Fin 10 → Fin m) (γ : S ^ m) (tg : Tags γ N) where
  private
    Vv = fst (lookup v γ)
    Wv = fst (lookup w γ)
    Tv = fst (lookup T γ)
```

<!--en-->
The code domain's underlying set and the numeral behind the tag one are named, since the membership clause selects codes shaped as the pair of the tag one and a second component.
<!--zh-->
码域的底层集与标签一背后的数码被命名，因为隶属子句选取的码形如「标签一与第二分量」之对。
<!--ja-->
コードの定義域の底の集合と、タグ一の背後にある数項が名付けられます。所属の節が選ぶのは、タグ一と第二成分の対の形のコードだからです。
<!--/-->

```agda
    Cv = fst (lookup C γ)
    N1v = fst (lookup (N f1) γ)
```

<!--en-->
Reading the membership clause yields, for each member of the proposed value, a truncated record: a code in the domain, split as the pair of the tag one and a component, a table entry pairing that code with a value, and the cut relation between the member and that value. The record exists under truncation; no code or value is chosen.
<!--zh-->
读取隶属子句对拟议值的每个成员给出截断记录：码域中的一个码 (拆为标签一与某分量之对)、把该码与某值配对的表条目，以及该成员与该值之间的切割关系。记录在截断下存在；不选定任何码或值。
<!--ja-->
所属の節の読みは、提案された値の各要素に対して、切り詰められた記録を与えます。定義域の中の、タグ一とある成分の対として分解される符号、その符号をある値と対にする表の項目、そしてその要素と値の間の切り出しの関係です。記録は切り詰めのもとで存在し、符号や値は選ばれません。
<!--/-->

```agda
  mem-out : ⟨ γ ⊨ memAt v w T C N ⟩ → (x : S) → ⟨ fst x ∈ Vv ⟩
          → ∥ Σ[ c ∈ S ] Σ[ p ∈ S ] Σ[ y ∈ S ]
              (⟨ fst c ∈ Cv ⟩ × ((fst c ≡ pr (# 1) (fst p)) × (⟨ pr (fst c) (fst y) ∈ Tv ⟩ × Cuts (fst x) Wv (fst y)))) ∥₁
  mem-out h x x∈ = PT.rec squash₁
    (λ { (c , (c∈ , hc)) → PT.rec squash₁
```

<!--en-->
To read the membership clause, first expose the key-shaped member `c` of the proposed code domain and then the table entry pairing `c` with a value `y`. The pairing specifications turn the encoded second components into the semantic equations displayed in the result, while the tag equation changes the formal tag into the actual numeral one.
<!--zh-->
读取隶属子句时，先取得候选码域中具有键形状的成员 `c`，再取得把 `c` 与值 `y` 配对的表条目。配对规格把编码的第二分量转成结果中所示的语义等式，而标签等式把形式标签改写为真正的数码一。
<!--ja-->
所属の節を読むには、まず候補の符号領域から鍵の形をした要素 `c` を取り出し、次に `c` と値 `y` を対にする表の項目を取り出します。対の仕様が符号化された第二成分を結果に現れる意味論的な等式へ変え、タグの等式が形式的なタグを実際の数項 1 へ書き換えます。
<!--/-->

```agda
      (λ { (p , s , (ec , he)) → PT.rec squash₁
        (λ { (e , (e∈ , hy)) → PT.map
          (λ { (y , s' , (ee , hd)) →
            c , p , y , ( c∈ , ( ec ∙ cong (λ a → pr a (fst p)) (tg f1)
                        , ( subst (λ u → ⟨ u ∈ Tv ⟩) ee e∈
```

<!--en-->
The innermost existential is read through `definesB-out`, which produces the cut relation between the member and the value `y` of the table entry.
<!--zh-->
最内层存在经 `definesB-out` 读取，产出该成员与表条目之值 `y` 之间的切割关系。
<!--ja-->
最も内側の存在は、`definesB-out` を通して読まれ、要素と表の項目の値 `y` の間の切り出しの関係を産み出します。
<!--/-->

```agda
                          , definesB-out i6 (sh 7 w) i0 (sh 7 (N f0)) (y ∷ s' ∷ e ∷ p ∷ s ∷ c ∷ x ∷ γ) (tg f0) hd ) ) ) })
          (sndEx-out i0 i3 (definesB i6 (sh 7 w) i0 (sh 7 (N f0))) (e ∷ p ∷ s ∷ c ∷ x ∷ γ) hy) })
        he })
      (sndEx-out i0 (sh 2 (N f1)) (∃̇∈ (var (sh 4 T)) (sndEx i0 i3 (definesB i6 (sh 7 w) i0 (sh 7 (N f0))))) (c ∷ x ∷ γ) hc) })
    (h x x∈)
```

<!--en-->
Filling the membership clause is the converse construction: it takes the function producing truncated records for each member and assembles the satisfaction of the clause.
<!--zh-->
填充隶属子句是反向构造：它收取为每个成员产出截断记录的函数，并组装子句的满足。
<!--ja-->
所属の節の埋めは逆の構成です。各要素に対して切り詰められた記録を産み出す関数を受け取り、節の充足を組み立てます。
<!--/-->

```agda

  mem-in : ((x : S) → ⟨ fst x ∈ Vv ⟩
            → ∥ Σ[ c ∈ S ] Σ[ p ∈ S ] Σ[ y ∈ S ]
                (⟨ fst c ∈ Cv ⟩ × ((fst c ≡ pr (# 1) (fst p)) × (⟨ pr (fst c) (fst y) ∈ Tv ⟩ × Cuts (fst x) Wv (fst y)))) ∥₁)
         → ⟨ γ ⊨ memAt v w T C N ⟩
  mem-in g x x∈ = PT.map
```

<!--en-->
Conversely, suppose such a truncated semantic record is given for each member of the proposed output. The equation `c = pr (# 1) p` supplies the arity-one shape required by the bounded formula, and membership of `pr(c,y)` in the table supplies a bounded representative for the table entry.
<!--zh-->
反过来，设候选输出的每个成员都带有这样一个截断的语义记录。等式 `c = pr (# 1) p` 给出有界公式所需的元数一形状，而 `pr(c,y)` 属于表的证明为表条目提供一个有界表示。
<!--ja-->
逆に、候補出力の各要素に対して、このような切り詰められた意味論的記録が与えられているとします。等式 `c = pr (# 1) p` は有界論理式が要求するアリティ一の形を与え、`pr(c,y)` の表への所属は表の項目の有界な表示を与えます。
<!--/-->

```agda
    (λ { (c , p , y , (c∈ , (ec , (e∈ , cuts)))) →
      let ec' : fst c ≡ pr N1v (fst p)
          ec' = ec ∙ cong (λ a → pr a (fst p)) (sym (tg f1))
          δ4 = p ∷ container c (lookup (N f1) γ) p ec' .fst ∷ c ∷ x ∷ γ
          eS = down (lookup T γ) (pr (fst c) (fst y)) e∈
```

<!--en-->
The seven-slot environment is then assembled, and the cut relation is translated back into the definable-subset clause by `definesB-in`.
<!--zh-->
随后组装七槽环境，并由 `definesB-in` 把切割关系转换回可定义子集子句。
<!--ja-->
続いて七つの枠からなる環境を組み立て、`definesB-in` によって切り出し関係を定義可能部分集合の節へ戻します。
<!--/-->

```agda
          δ7 = y ∷ container eS c y refl .fst ∷ eS ∷ δ4
      in c , ( c∈ , fillSnd i0 (c ∷ x ∷ γ) (lookup (N f1) γ) p ec'
                 (∃̇∈ (var (sh 4 T)) (sndEx i0 i3 (definesB i6 (sh 7 w) i0 (sh 7 (N f0)))))
                 ∣ eS , ( e∈ , fillSnd i0 (eS ∷ δ4) c y refl (definesB i6 (sh 7 w) i0 (sh 7 (N f0)))
                              (definesB-in i6 (sh 7 w) i0 (sh 7 (N f0)) δ7 (tg f0) cuts) i3 refl ) ∣₁
```

<!--en-->
After the key shape, table entry, and cut condition have been encoded, the outer bounded quantifier applies this truncated package to the original member of the proposed output. Hence the semantic record is sufficient to reconstruct satisfaction of the whole membership clause.
<!--zh-->
键的形状、表条目与切出条件编码完毕后，外层有界量词把这个截断整体用于候选输出的原成员。因此，这个语义记录足以重建整个隶属子句的满足。
<!--ja-->
鍵の形、表の項目、切り出し条件を符号化した後、外側の有界量化子が、この切り詰められたまとまりを候補出力の元の要素に適用します。したがって、この意味論的記録から所属の節全体の充足を再構成できます。
<!--/-->

```agda
                 (sh 2 (N f1)) refl ) })
    (g x x∈)
```

<!--en-->
Reading the covering clause takes a code `c` that splits as the pair of the tag one and `p`, and yields, merely, a table value `y` at `c` together with a set `x` cut by `y`.
<!--zh-->
读取覆盖子句：取一个可拆成「标签一与 `p` 之对」的码 `c`，则仅仅地给出 `c` 处的表值 `y` 以及被 `y` 切出的集合 `x`。
<!--ja-->
覆いの節の読みは、タグ一と `p` の対として分解される符号 `c` を取り、単に、`c` における表の値 `y` と、`y` によって切り出される集合 `x` を与えます。
<!--/-->

```agda
  all-out : ⟨ γ ⊨ allAt v w T C N ⟩ → (c p : S) → ⟨ fst c ∈ Cv ⟩ → fst c ≡ pr (# 1) (fst p)
          → ∥ Σ[ y ∈ S ] Σ[ x ∈ S ] (⟨ pr (fst c) (fst y) ∈ Tv ⟩ × (⟨ fst x ∈ Vv ⟩ × Cuts (fst x) Wv (fst y))) ∥₁
  all-out h c p c∈ ec = PT.rec squash₁
    (λ { (e , (e∈ , hy)) → PT.rec squash₁
      (λ { (y , s' , (ee , hx)) → PT.map
```

<!--en-->
The proof eliminates the table entry and the three-slot existential, and the definable-subset reading produces the cut relation between the member and the table value.
<!--zh-->
证明消去表条目与三槽存在量化，而可定义子句读取产出成员与表值之间的切割关系。
<!--ja-->
証明は、表の項目と三つの枠の存在量化を消去します。そして定義可能な部分集合の節の読みが、要素と表の値の間の切り出しの関係を産み出します。
<!--/-->

```agda
        (λ { (x , (x∈ , hd)) →
          y , x , ( subst (λ u → ⟨ u ∈ Tv ⟩) ee e∈
                  , ( x∈ , definesB-out i0 (sh 7 w) i1 (sh 7 (N f0)) (x ∷ y ∷ s' ∷ e ∷ δ3) (tg f0) hd ) ) })
        hx })
      (sndEx-out i0 i3 (∃̇∈ (var (sh 6 v)) (definesB i0 (sh 7 w) i1 (sh 7 (N f0)))) (e ∷ δ3) hy) })
```

<!--en-->
For the converse construction, fix a member `c` of the code domain and inspect any presentation of it as `pr (# 1) p`. The semantic coverage hypothesis then provides, under propositional truncation, a table value and the subset that this value cuts out; these witnesses fill the bounded conclusion for that presentation.
<!--zh-->
为作反向构造，固定码域的成员 `c`，并考察它作为 `pr (# 1) p` 的任一呈现。语义覆盖假设随后在命题截断下给出一个表取值及由该取值切出的子集；这些见证填入该呈现所需的有界结论。
<!--ja-->
逆向きの構成では、符号領域の要素 `c` を固定し、それが `pr (# 1) p` として表される場合を調べます。意味論的な覆いの仮定は、命題的切り詰めの下で表の値と、その値が切り出す部分集合を与えます。これらの証人が、その表示に対する有界な結論を満たします。
<!--/-->

```agda
    (useSnd i0 (c ∷ γ) (lookup (N f1) γ) p ec'
      (∃̇∈ (var (sh 3 T)) (sndEx i0 i3 (∃̇∈ (var (sh 6 v)) (definesB i0 (sh 7 w) i1 (sh 7 (N f0))))))
      (sh 1 (N f1)) refl (h c c∈))
    where
    ec' : fst c ≡ pr N1v (fst p)
```

<!--en-->
The equation using the formal tag is converted to the required arity-one equation by `Tags`. The auxiliary containers merely keep the component and code within bounded quantifiers; they add no mathematical choice or uniqueness to the semantic witness.
<!--zh-->
借助 `Tags`，使用形式标签的等式被转换为所需的元数一等式。辅助容器只负责让分量与码始终处于有界量词内；它们不会给语义见证增加任何选择或唯一性。
<!--ja-->
形式的なタグを使う等式は、`Tags` によって必要なアリティ一の等式へ変換されます。補助的な容器は、成分と符号を有界量化子の範囲内に保つだけであり、意味論的な証人に選択や一意性を加えるものではありません。
<!--/-->

```agda
    ec' = ec ∙ cong (λ a → pr a (fst p)) (sym (tg f1))
    δ3 : S ^ (3 + m)
    δ3 = p ∷ container c (lookup (N f1) γ) p ec' .fst ∷ c ∷ γ

```

<!--en-->
Filling the coverage clause therefore ranges over every member of the proposed code domain that is presented with arity-one key shape. For each such presentation, the semantic hypothesis supplies a table value, a cut-out member of the proposed output, and their memberships, all under propositional truncation. No claim that these are genuine formula keys is made until `satAt` is added later.
<!--zh-->
因此，填充覆盖子句时遍历候选码域中每个被呈现为元数一键形状的成员。对每个这样的呈现，语义假设在命题截断下给出表取值、候选输出中由它切出的成员及二者的隶属。直到后文加入 `satAt`，这里都不声称这些成员是真正的公式键。
<!--ja-->
したがって覆いの節を満たす際には、候補の符号領域の要素のうち、アリティ一の鍵の形で表示されたものをすべて扱います。その各表示に対し、意味論的な仮定が命題的切り詰めの下で、表の値、それが切り出す候補出力の要素、および両者の所属を与えます。後で `satAt` を加えるまでは、これらが実際の論理式の鍵であるとは主張しません。
<!--/-->

```agda
  all-in : ((c p : S) → ⟨ fst c ∈ Cv ⟩ → fst c ≡ pr (# 1) (fst p)
            → ∥ Σ[ y ∈ S ] Σ[ x ∈ S ] (⟨ pr (fst c) (fst y) ∈ Tv ⟩ × (⟨ fst x ∈ Vv ⟩ × Cuts (fst x) Wv (fst y))) ∥₁)
         → ⟨ γ ⊨ allAt v w T C N ⟩
  all-in g c c∈ = sndAll-in' (λ p s s∈ p∈ ec →
    PT.map (λ { (y , x , (e∈ , (x∈ , cuts))) →
```

<!--en-->
The innermost bounded existential now receives the sliced set `x` together with its membership in the value set and the `Cuts` evidence just encoded by `definesB`. This completes the converse translation: semantic witnesses for a table entry and its slice yield satisfaction of the membership clause, while all existential data remain propositionally truncated.
<!--zh-->
最内层的有界存在量词现在以切出的集合 `x` 为见证，并同时接收 `x` 属于取值集合的证明以及刚由 `definesB` 编码的 `Cuts` 证据。这便完成反向翻译：表条目及其所切子集的语义见证给出隶属子句的满足，而所有存在数据仍保留在命题截断中。
<!--ja-->
最も内側の有界存在量化子には、切り出された集合 `x` と、`x` が値の集合に属する証明、さらに `definesB` で符号化したばかりの `Cuts` の証拠が渡されます。これで逆向きの翻訳が完成します。表の項目とそれが切り出す部分集合についての意味論的な証人から所属の条項の充足が得られ、存在データはすべて命題的切り詰めの中に保たれます。
<!--/-->

```agda
      let eS = down (lookup T γ) (pr (fst c) (fst y)) e∈
          δ6 = y ∷ container eS c y refl .fst ∷ eS ∷ p ∷ s ∷ c ∷ γ
      in eS , ( e∈ , fillSnd i0 (eS ∷ p ∷ s ∷ c ∷ γ) c y refl (∃̇∈ (var (sh 6 v)) (definesB i0 (sh 7 w) i1 (sh 7 (N f0))))
                       ∣ x , (x∈ , definesB-in i0 (sh 7 w) i1 (sh 7 (N f0)) (x ∷ δ6) (tg f0) cuts) ∣₁ i3 refl ) })
      (g c p c∈ (ec ∙ cong (λ a → pr a (fst p)) (tg f1))))
```

<!--en-->
The coverage clause contains the same two nested existential choices: a value of the satisfaction table and the subset that this value cuts out of the working set. Naming their combined outward reading lets the next argument treat this pair of merely existing witnesses as one proposition-valued package.
<!--zh-->
覆盖子句含有同样两层存在选择：满足关系表的一个取值，以及该取值从工作集中切出的子集。为二者合成后的向外读法命名，使下一个论证能把这对仅仅存在的见证作为一个命题值整体处理。
<!--ja-->
覆いの条項にも同じ二段の存在選択があります。充足関係表の値と、その値が作業集合から切り出す部分集合です。両者を合わせた外向きの読み出しに名前を付けることで、次の議論では、この単に存在する一対の証人を一つの命題値のまとまりとして扱えます。
<!--/-->

```agda
    where
    sndAll-in' = sndAll-in i0 (sh 1 (N f1))
      (∃̇∈ (var (sh 3 T)) (sndEx i0 i3 (∃̇∈ (var (sh 6 v)) (definesB i0 (sh 7 w) i1 (sh 7 (N f0)))))) (c ∷ γ)
```

<!--en-->
## Correctness of the bounded description
<!--zh-->
## 有界描述的正确性
<!--ja-->
## 有界な記述の正しさ
<!--/-->

<!--en-->
We can now compare the bounded description with the actual definability operation. This comparison requires more than satisfaction of `defAt`: the numeral tags must have their intended values, the working-set slot must denote `W`, and `satAt` must certify that the code set and table have their genuine satisfaction semantics.
<!--zh-->
现在可以把有界描述与真正的可定义性算子比较。这个比较不只需要 `defAt` 成立：数码标签必须取预期值，工作集槽必须指称 `W`，而 `satAt` 必须保证码集与满足关系表具有其真正的满足语义。
<!--ja-->
ここから、有界な記述を実際の定義可能性の演算と比較します。この比較には `defAt` の充足だけでは足りません。数を表すタグが意図した値をもち、作業集合の枠が `W` を表し、さらに `satAt` が符号集合と充足関係表に本来の充足意味論を保証していなければなりません。
<!--/-->

```agda
module DefRead {m : ℕ} (v w T C E : Fin m) (N : Fin 10 → Fin m) (γ : S ^ m) (W : S)
  (qw : fst (lookup w γ) ≡ fst W) (tg : Tags γ N) (hs : ⟨ γ ⊨ satAt T w C E N ⟩) where
  open Alphabet W
  open Match W
  private
```

<!--en-->
Two earlier readers supply the needed bridge. `SatRead` identifies the advertised code domain and table with the real codes and satisfaction values over `W`; `Read` turns `defAt` into its two semantic slice conditions. `DefOf (fst W)` then interprets each decoded arity-one formula as one subset of `W`.
<!--zh-->
前面的两个读取器提供所需桥梁。`SatRead` 把描述中的码域和表与 `W` 上真正的码及满足取值对齐；`Read` 把 `defAt` 读成两个语义切出条件。随后 `DefOf (fst W)` 把每条解码得到的元数一公式解释为 `W` 的一个子集。
<!--ja-->
先に得た二つの読み出しが必要な橋を与えます。`SatRead` は、記述された符号領域と表を、`W` 上の実際の符号と充足値に対応させます。`Read` は `defAt` を二つの意味論的な切り出し条件として読みます。その上で `DefOf (fst W)` が、復号されたアリティ一の各論理式を `W` の一つの部分集合として解釈します。
<!--/-->

```agda
    module SR = SatRead T w C E N γ W qw tg hs
    module RD = Read v w T C N γ tg
    module DA = DefOf (fst W)
    Vv = fst (lookup v γ)
    Wv = fst (lookup w γ)
```

<!--en-->
Write `Tv` and `Cv` for the underlying sets occupying the table and code slots. The point of `satAt` is precisely that membership in these advertised sets can now be converted to, and reconstructed from, membership in the genuine satisfaction table and code domain.
<!--zh-->
记表槽与码槽所指称的底层集合为 `Tv` 与 `Cv`。`satAt` 的作用正在于：如今可以在这些描述集合中的隶属与真正满足关系表、码域中的隶属之间来回转换。
<!--ja-->
表の枠と符号の枠が表す基礎の集合を、それぞれ `Tv` と `Cv` と書きます。`satAt` の役割はまさに、これら記述された集合への所属と、実際の充足関係表および符号領域への所属とを相互に変換できるようにすることです。
<!--/-->

```agda
    Tv = fst (lookup T γ)
    Cv = fst (lookup C γ)

```

<!--en-->
The map `toS` relabels every constant of a formula over the alphabet into the corresponding constant of `S`, producing a formula that the ambient satisfaction judges.
<!--zh-->
映射 `toS` 把字母表上公式的每个常元改名为 `S` 的相应常元，产出可由环境满足判断的公式。
<!--ja-->
対応 `toS` は、アルファベットの上の論理式のすべての定数を、`S` の対応する定数へ付け替え、周囲の充足で判定できる論理式を作ります。
<!--/-->

```agda
    toS : Formula Ab 1 → Formula S 1
    toS = mapFo (asConst W)
```

<!--en-->
The table-value lemma says that the value recorded at the key of a formula equals the explicit satisfaction set of the relabeled formula. The proof composes the table's outward projection with the uniform satisfaction's value identification.
<!--zh-->
表取值引理说：在公式键处记录的取值等于改名后公式的显式满足集合。证明复合表的外向投影与一致满足的取值认同。
<!--ja-->
表の値の補題は、論理式のキーで記録された値が、付け替えられた論理式の明示的な充足集合に等しいと言います。証明は、表の外向きの射影と、一様な充足の値の同定とを合成します。
<!--/-->

```agda
    valOf : (ψ : Formula Ab 1) (c y : S) → fst c ≡ fst (keyS W ψ) → ⟨ pr (fst c) (fst y) ∈ Tv ⟩
          → fst y ≡ fst (Sat W (toS ψ))
    valOf ψ c y qc h = SR.T-out c y h .snd ∙ cong fst (val-at W W ψ c (SR.T-out c y h .fst) qc)
```

<!--en-->
The central bridge concerns one formula at a time. If `Cuts` says that `x` consists exactly of those members of `W` whose one-variable environments lie in the satisfaction set of `ψ`, then `x` is equal to the particular definable subset `DA.defSet ψ`. Extensionality proves this equality in both membership directions.
<!--zh-->
核心桥梁逐条处理公式。若 `Cuts` 说明 `x` 恰由 `W` 中那些其单变元环境属于 `ψ` 的满足集合的元素组成，那么 `x` 就等于这个特定的可定义子集 `DA.defSet ψ`。外延性通过两个隶属方向证明此等式。
<!--ja-->
中心となる橋は論理式を一つずつ扱います。`Cuts` が、`x` は `W` の要素のうち、その一変数環境が `ψ` の充足集合に属するものからちょうど成ると述べるなら、`x` は特定の定義可能部分集合 `DA.defSet ψ` に等しくなります。この等式は、所属の両方向を示して外延性から得られます。
<!--/-->

```agda
    cut≡ : (ψ : Formula Ab 1) (x : S) → Cuts (fst x) Wv (fst (Sat W (toS ψ))) → DA.defSet ψ ≡ fst x
    cut≡ ψ x (o , i) = extensionalV (λ z → ⇔toPath (fwd z) (bwd z))
      where
      fwd : (z : V ℓ) → ⟨ z ∈ DA.defSet ψ ⟩ → ⟨ z ∈ fst x ⟩
      fwd z = PT.rec (snd (z ∈ fst x))
```

<!--en-->
For the first direction, membership in `DA.defSet ψ` supplies, under propositional truncation, a representative of an element of `W`. The satisfaction bridge places that representative's one-variable environment in the satisfaction set of `ψ`, so the inward half of `Cuts` places the represented set in `x`.
<!--zh-->
第一个方向中，属于 `DA.defSet ψ` 的证明在命题截断下给出 `W` 中元素的一个表示。满足桥梁把该表示的单变元环境放入 `ψ` 的满足集合，于是 `Cuts` 的向内一半把所表示的集合放入 `x`。
<!--ja-->
第一の方向では、`DA.defSet ψ` への所属から、命題的切り詰めの下で `W` の要素の表示が得られます。充足の橋によって、その表示の一変数環境は `ψ` の充足集合に入り、`Cuts` の内向きの半分が、表示された集合を `x` に入れます。
<!--/-->

```agda
        (λ { ((q , hq) , e) →
          i (down W z (subst (λ u → ⟨ u ∈ fst W ⟩) e (ι∈ q)))
            (subst (λ u → ⟨ z ∈ u ⟩) (sym qw) (subst (λ u → ⟨ u ∈ fst W ⟩) e (ι∈ q)))
            (subst (λ u → ⟨ envOne u ∈ fst (Sat W (toS ψ)) ⟩) e
              (subst ⟨_⟩ (defSet-Sat W ψ q) ∣ (q , hq) , refl ∣₁)) })
```

<!--en-->
For the other direction, begin with `z ∈ x`. The outward half of `Cuts` gives both `z ∈ W` and membership of its one-variable environment in the satisfaction set. The first fact is converted by `∈-asFiber` into an actual index of the presentation of `W`, together with a path back to `z`.
<!--zh-->
另一个方向从 `z ∈ x` 出发。`Cuts` 的向外一半同时给出 `z ∈ W` 以及其单变元环境属于满足集合。`∈-asFiber` 把第一项转换为 `W` 的呈现中的一个实际索引，并给出回到 `z` 的路径。
<!--ja-->
もう一方の方向では `z ∈ x` から始めます。`Cuts` の外向きの半分は、`z ∈ W` と、その一変数環境が充足集合に属することの両方を与えます。第一の事実は `∈-asFiber` によって、`W` の表示の実際の添字と、そこから `z` へ戻るパスに変換されます。
<!--/-->

```agda
      bwd : (z : V ℓ) → ⟨ z ∈ fst x ⟩ → ⟨ z ∈ DA.defSet ψ ⟩
      bwd z hz =
        let zS = down x z hz
            zW = subst (λ u → ⟨ z ∈ u ⟩) qw (o zS hz .fst)
            fib = ∈-asFiber {a = z} {b = fst W} zW
```

<!--en-->
Transport the environment membership along that presentation path and apply `defSet-Sat` in reverse. This proves that the representative belongs to `DA.defSet ψ`; transporting back along the same path proves `z ∈ DA.defSet ψ` and completes the extensional equality.
<!--zh-->
沿该呈现路径运输环境隶属，再反向应用 `defSet-Sat`，便证明对应表示属于 `DA.defSet ψ`；沿同一路径运回后得到 `z ∈ DA.defSet ψ`，从而完成外延等式。
<!--ja-->
その表示のパスに沿って環境の所属を移し、`defSet-Sat` を逆向きに適用します。これにより表示が `DA.defSet ψ` に属することが分かり、同じパスに沿って戻せば `z ∈ DA.defSet ψ` が得られて、外延的な等式が完成します。
<!--/-->

```agda
        in subst (λ u → ⟨ u ∈ DA.defSet ψ ⟩) (fib .snd)
             (subst ⟨_⟩ (sym (defSet-Sat W ψ (fib .fst)))
               (subst (λ u → ⟨ envOne u ∈ fst (Sat W (toS ψ)) ⟩) (sym (fib .snd)) (o zS hz .snd)))

```

<!--en-->
Conversely, suppose `DA.defSet ψ` is already known to equal `x`. To reconstruct `Cuts`, take a member of `x`, rewrite it as a member of `DA.defSet ψ`, and unpack definable-set membership. This yields both its presentation as an element of `W` and the corresponding one-variable environment's membership in the satisfaction set.
<!--zh-->
反过来，设已知 `DA.defSet ψ` 等于 `x`。为重建 `Cuts`，先取 `x` 的一个成员，把它改写为 `DA.defSet ψ` 的成员，再展开可定义子集的隶属。由此同时得到它作为 `W` 中元素的表示，以及相应单变元环境属于满足集合的证明。
<!--ja-->
逆に、`DA.defSet ψ` がすでに `x` に等しいとします。`Cuts` を再構成するには、`x` の要素を `DA.defSet ψ` の要素へ書き換え、定義可能部分集合への所属を展開します。すると、その集合を `W` の要素として表すデータと、対応する一変数環境が充足集合に属する証明が同時に得られます。
<!--/-->

```agda
    cuts-of : (ψ : Formula Ab 1) (x : S) → DA.defSet ψ ≡ fst x → Cuts (fst x) Wv (fst (Sat W (toS ψ)))
    cuts-of ψ x e = o , i
      where
      o : (z : S) → ⟨ fst z ∈ fst x ⟩ → ⟨ fst z ∈ Wv ⟩ × ⟨ envOne (fst z) ∈ fst (Sat W (toS ψ)) ⟩
      o z hz = PT.rec (isProp× (snd (fst z ∈ Wv)) (snd (envOne (fst z) ∈ fst (Sat W (toS ψ)))))
```

<!--en-->
Unpacking that membership gives a representative in `W` and, through `defSet-Sat`, the required satisfaction-set membership of its one-variable environment. The equality between the representative and the original member transports both conclusions back to the member of `x`.
<!--zh-->
展开这一隶属，得到 `W` 中的一个表示，并经 `defSet-Sat` 得到其单变元环境属于所需满足集合。表示与原成员之间的等式把这两个结论都运输回 `x` 的该成员。
<!--ja-->
この所属を展開すると、`W` の中の表示と、`defSet-Sat` を通じて、その一変数環境が必要な充足集合に属することが得られます。表示と元の要素との等式に沿って、二つの結論をどちらも `x` のその要素へ戻します。
<!--/-->

```agda
        (λ { ((q , hq) , eq) →
            subst (λ u → ⟨ fst z ∈ u ⟩) (sym qw) (subst (λ u → ⟨ u ∈ fst W ⟩) eq (ι∈ q))
          , subst (λ u → ⟨ envOne u ∈ fst (Sat W (toS ψ)) ⟩) eq (subst ⟨_⟩ (defSet-Sat W ψ q) ∣ (q , hq) , refl ∣₁) })
        (subst (λ u → ⟨ fst z ∈ u ⟩) (sym e) hz)
      i : (z : S) → ⟨ fst z ∈ Wv ⟩ → ⟨ envOne (fst z) ∈ fst (Sat W (toS ψ)) ⟩ → ⟨ fst z ∈ fst x ⟩
```

<!--en-->
For the inward half of `Cuts`, start with a presented member of `W` whose one-variable environment satisfies `ψ`. The satisfaction bridge turns this into membership in `DA.defSet ψ`; the assumed equality `DA.defSet ψ = fst x` then places the member in `x`.
<!--zh-->
为证明 `Cuts` 的向内一半，从 `W` 中一个已呈现的成员出发，并假定其单变元环境满足 `ψ`。满足桥梁把它转成属于 `DA.defSet ψ`，再由假定的等式 `DA.defSet ψ = fst x` 把该成员放入 `x`。
<!--ja-->
`Cuts` の内向きの半分では、`W` の表示された要素から始め、その一変数環境が `ψ` を満たすと仮定します。充足の橋がこれを `DA.defSet ψ` への所属に変え、仮定した等式 `DA.defSet ψ = fst x` がその要素を `x` に入れます。
<!--/-->

```agda
      i z hw he =
        let fib = ∈-asFiber {a = fst z} {b = fst W} (subst (λ u → ⟨ fst z ∈ u ⟩) qw hw)
        in subst (λ u → ⟨ fst z ∈ u ⟩) e
             (subst (λ u → ⟨ u ∈ DA.defSet ψ ⟩) (fib .snd)
               (subst ⟨_⟩ (sym (defSet-Sat W ψ (fib .fst)))
```

<!--en-->
The final transports only reconcile the chosen presentation of the member with its underlying set. Thus `cut≡` and `cuts-of` together identify the `Cuts` predicate for `ψ` with equality to the single definable subset `DA.defSet ψ`; neither direction asserts uniqueness of a defining formula.
<!--zh-->
最后的运输只是在所选成员表示与其底层集合之间作对齐。因此，`cut≡` 与 `cuts-of` 合起来把 `ψ` 的 `Cuts` 谓词同「等于单个可定义子集 `DA.defSet ψ`」对应起来；两个方向都没有断言定义公式唯一。
<!--ja-->
最後の輸送は、選んだ要素の表示とその基礎の集合を揃えるだけです。したがって `cut≡` と `cuts-of` を合わせると、`ψ` に対する `Cuts` 述語は、一つの定義可能部分集合 `DA.defSet ψ` との等しさに対応します。どちらの向きも定義論理式の一意性を主張しません。
<!--/-->

```agda
                 (subst (λ u → ⟨ envOne u ∈ fst (Sat W (toS ψ)) ⟩) (sym (fib .snd)) he)))

```

<!--en-->
Soundness can now be stated accurately. Under the standing identification of the working-set slot with `W`, the correct numeral tags, and the `satAt` certification of the code set and satisfaction table, satisfaction of `defAt` forces the value slot to be exactly `𝒟ₒ (fst W)`. Here `𝒟ₒ` collects the subsets of `W` definable by first-order formulas with parameters from `W`; it is not the full internal power set.
<!--zh-->
现在可以准确陈述可靠性。在工作集槽与 `W` 已对齐、数码标签正确且 `satAt` 已校准码集和满足关系表的背景下，`defAt` 的满足迫使取值槽恰等于 `𝒟ₒ (fst W)`。这里的 `𝒟ₒ` 收集由允许取 `W` 中参数的一阶公式定义出的 `W` 的子集，并非完整的内部幂集。
<!--ja-->
これで健全性を正確に述べられます。作業集合の枠が `W` と同一視され、数を表すタグが正しく、`satAt` が符号集合と充足関係表を正しく保証しているという前提の下で、`defAt` の充足は値の枠をちょうど `𝒟ₒ (fst W)` に定めます。ここで `𝒟ₒ` が集めるのは、`W` の要素をパラメータに使える一階論理式で定義される `W` の部分集合であり、完全な内部冪集合ではありません。
<!--/-->

```agda
  def-sound : ⟨ γ ⊨ defAt v w T C N ⟩ → Vv ≡ 𝒟ₒ (fst W)
  def-sound hd = extensionalV (λ x → ⇔toPath (fwd x) (bwd x))
    where
    hm = defAt-out v w T C N γ hd .fst
    ha = defAt-out v w T C N γ hd .snd
```

<!--en-->
For the forward inclusion, the membership clause supplies, under propositional truncation, a key-shaped code, a satisfaction-table entry, and the condition describing the subset cut out by that entry. After `satAt` identifies the proposed code domain with the genuine one, `decodeAll` yields merely an arity-one formula whose code has the required second component. The table-value lemma then identifies the entry's value with that formula's satisfaction set.
<!--zh-->
对正向包含，隶属子句在命题截断下给出一个具有键形状的码、一个满足关系表条目，以及描述该条目所切子集的条件。`satAt` 把候选码域同真正码域对齐后，`decodeAll` 仅仅给出一条元数一公式，其编码具有所需的第二分量。表取值引理再把该条目的取值认同为这条公式的满足集合。
<!--ja-->
順方向の包含では、所属の節が命題的切り詰めの下で、鍵の形をした符号、充足関係表の項目、その項目が切り出す部分集合を記述する条件を与えます。`satAt` が候補の符号領域を実際のものと対応させた後、`decodeAll` は、符号が必要な第二成分をもつアリティ一の論理式が単に存在することだけを与えます。続いて表の値の補題が、その項目の値をこの論理式の充足集合と同一視します。
<!--/-->

```agda

    fwd : (x : V ℓ) → ⟨ x ∈ Vv ⟩ → ⟨ x ∈ 𝒟ₒ (fst W) ⟩
    fwd x hx = PT.rec (snd (x ∈ 𝒟ₒ (fst W)))
      (λ { (c , p , y , (c∈ , (ec , (e∈ , cuts)))) → PT.rec (snd (x ∈ 𝒟ₒ (fst W)))
        (λ { (ψ , qp) →
          𝒟ₒ-intro (fst W) x ∣ ψ , cut≡ ψ xS
```

<!--en-->
The `Cuts` fact is transported along the table-value identification to the satisfaction set of the decoded formula, and the definable-power-set introduction places the sliced set inside `𝒟ₒ`. The truncated formula decoding is consumed into the proposition-valued introduction.
<!--zh-->
`Cuts` 事实沿表取值认同被运至解码公式的满足集，而可定义幂集引入把切片集合放进 `𝒟ₒ`。截断的公式解码被消耗到命题值的引入中。
<!--ja-->
`Cuts` の事実が、表の値の同定に沿って、復号された論理式の充足集合の中へ運ばれ、定義可能冪集合の導入が、切り出された集合を `𝒟ₒ` の中に置きます。切り詰められた論理式の復号は、命題値の導入の中で消費されます。
<!--/-->

```agda
            (subst (λ u → Cuts x Wv u) (valOf ψ c y (ec ∙ cong (pr (# 1)) qp) e∈) cuts) ∣₁ })
        (decodeAll c (SR.C-out c c∈) 1 (fst p) ec) })
      (RD.mem-out hm xS hx)
      where
      xS : S
```

<!--en-->
The value slot is presented as a carrier element for reading the outward direction of the membership clause.
<!--zh-->
取值槽被呈现为载体元素，以供隶属子句向外方向读取。
<!--ja-->
値の枠は、所属の条項の外向きの読み出しのために、台の要素として提示されます。
<!--/-->

```agda
      xS = down (lookup v γ) x hx

```

<!--en-->
For the reverse inclusion, membership in `𝒟ₒ (fst W)` yields only a propositionally truncated formula `ψ` together with an equality `DA.defSet ψ = x`. Inside elimination into the membership proposition, the coverage half of `defAt` provides a table value and a set `x'` in the value slot for the key built from this temporary witness `ψ`.
<!--zh-->
对反向包含，属于 `𝒟ₒ (fst W)` 只给出命题截断下的一条公式 `ψ` 及等式 `DA.defSet ψ = x`。在消去到隶属命题的过程中，`defAt` 的覆盖部分针对由这个临时见证 `ψ` 构造的键，给出一个表取值以及取值槽中的集合 `x'`。
<!--ja-->
逆向きの包含では、`𝒟ₒ (fst W)` への所属から得られるのは、命題的に切り詰められた論理式 `ψ` と等式 `DA.defSet ψ = x` だけです。所属命題への消去の内部で、`defAt` の覆いの側が、この一時的な証人 `ψ` から作った鍵に対し、表の値と、値の枠に属する集合 `x'` を与えます。
<!--/-->

```agda
    bwd : (x : V ℓ) → ⟨ x ∈ 𝒟ₒ (fst W) ⟩ → ⟨ x ∈ Vv ⟩
    bwd x hx = PT.rec (snd (x ∈ Vv))
      (λ { (ψ , e) → PT.rec (snd (x ∈ Vv))
        (λ { (y , x' , (e∈ , (x'∈ , cuts))) →
          subst (λ u → ⟨ u ∈ Vv ⟩)
```

<!--en-->
The slice equality is transported along the table-value identification to recover the underlying set of the sliced set, and the transport places it inside the value slot.
<!--zh-->
切片等式沿表取值认同运输以恢复切片集的底层集合，运输把它放进取值槽。
<!--ja-->
切り出しの等式が、表の値の同定に沿って運ばれて、切り出された集合の基礎の集合を復元し、輸送がそれを値の枠の中へ置きます。
<!--/-->

```agda
            (sym (cut≡ ψ x' (subst (λ u → Cuts (fst x') Wv u) (valOf ψ (keyS W ψ) y refl e∈) cuts)) ∙ e)
            x'∈ })
        (RD.all-out ha (keyS W ψ) (sndS (keyS W ψ) (# 1) (cd ψ) refl) (SR.C-in (keyS W ψ) (key∈AllCodes W ψ)) refl) })
      (𝒟ₒ-inv (fst W) x hx)

```

<!--en-->
Completeness runs the same equivalence backwards. Still assuming the working-set identification, correct tags, and `satAt`, an equality between the value slot and `𝒟ₒ (fst W)` suffices to satisfy `defAt`. The two conjuncts respectively show that every listed set has a defining formula and that every arity-one formula contributes its definable subset.
<!--zh-->
完备性把同一等价关系反向使用。在仍假定工作集已对齐、标签正确且 `satAt` 成立时，取值槽与 `𝒟ₒ (fst W)` 的相等足以构造 `defAt` 的满足。两个合取项分别说明：列出的每个集合都有定义公式，而每条元数一公式所定义的子集都会出现。
<!--ja-->
完全性は同じ同値関係を逆向きにたどります。作業集合の同一視、正しいタグ、`satAt` を引き続き仮定すると、値の枠と `𝒟ₒ (fst W)` との等式から `defAt` の充足を構成できます。二つの連言項はそれぞれ、列挙された各集合に定義論理式があることと、アリティ一の各論理式が定める部分集合が必ず現れることを示します。
<!--/-->

```agda
  def-complete : Vv ≡ 𝒟ₒ (fst W) → ⟨ γ ⊨ defAt v w T C N ⟩
  def-complete qv = defAt-in v w T C N γ mem all
    where
```

<!--en-->
Each formula's table entry is selected from the already-defined recursion table, which guarantees both the membership in the table and the identification with the explicit satisfaction set.
<!--zh-->
每条公式的表条目从已定义的递归表中选取，后者同时保证表中的隶属与显式满足集的认同。
<!--ja-->
それぞれの論理式の表の項目は、すでに定義された再帰の表から選ばれます。その表は、表の中での所属と、明示的な充足集合との同定の両方を保証します。
<!--/-->

```agda
    entry : (ψ : Formula Ab 1) → Σ[ y ∈ S ] (⟨ pr (fst (keyS W ψ)) (fst y) ∈ Tv ⟩ × (fst y ≡ fst (Sat W (toS ψ))))
    entry ψ = Table.val W W (keyS W ψ) (key∈AllCodes W ψ)
            , ( SR.T-in (keyS W ψ) (key∈AllCodes W ψ)
              , cong fst (val-at W W ψ (keyS W ψ) (key∈AllCodes W ψ) refl) )

```

<!--en-->
For the membership conjunct, a member of the value slot is transported into `𝒟ₒ (fst W)` and then unpacked by `𝒟ₒ-inv`. The defining formula exists only under propositional truncation. Within that truncation, its formula key, the corresponding table entry, and the required `Cuts` evidence are assembled; no defining formula is selected globally or retained as canonical data.
<!--zh-->
对隶属合取项，先把取值槽的成员运输到 `𝒟ₒ (fst W)`，再由 `𝒟ₒ-inv` 展开。定义公式只在命题截断下存在。在该截断内部，证明组装它的公式键、相应表条目和所需的 `Cuts` 证据；整个过程没有全局选取定义公式，也没有把某条公式保留为规范数据。
<!--ja-->
所属の連言項では、値の枠の要素を `𝒟ₒ (fst W)` へ移し、`𝒟ₒ-inv` で展開します。定義論理式は命題的切り詰めの下でのみ存在します。その内部で論理式の鍵、対応する表の項目、必要な `Cuts` の証拠を組み立てますが、定義論理式を大域的に選んだり、標準的なデータとして保持したりはしません。
<!--/-->

```agda
    mem : ⟨ γ ⊨ memAt v w T C N ⟩
    mem = RD.mem-in (λ x x∈ → PT.map
      (λ { (ψ , e) →
        keyS W ψ , sndS (keyS W ψ) (# 1) (cd ψ) refl , entry ψ .fst
        , ( SR.C-in (keyS W ψ) (key∈AllCodes W ψ)
```

<!--en-->
The chosen table value is the value already determined by the recursive satisfaction table for this formula key. Transporting `cuts-of` along its equality with the explicit satisfaction set supplies the slice evidence. This use of a temporary formula witness stays inside `PT.map`, so the resulting membership witness remains propositionally truncated.
<!--zh-->
所用表取值是递归满足关系表已为该公式键确定的取值。沿它与显式满足集合的等式运输 `cuts-of`，便得到切出证据。这个临时公式见证始终留在 `PT.map` 内，因此所得隶属见证仍受命题截断。
<!--ja-->
ここで用いる表の値は、再帰的な充足関係表がこの論理式の鍵に対してすでに定めた値です。その値と明示的な充足集合との等式に沿って `cuts-of` を移せば、切り出しの証拠が得られます。この一時的な論理式の証人は終始 `PT.map` の内部にあり、得られる所属の証人も命題的に切り詰められたままです。
<!--/-->

```agda
          , ( refl
            , ( entry ψ .snd .fst
              , subst (λ u → Cuts (fst x) Wv u) (sym (entry ψ .snd .snd)) (cuts-of ψ x e) ) ) ) })
      (𝒟ₒ-inv (fst W) (fst x) (subst (λ u → ⟨ fst x ∈ u ⟩) qv x∈)))

```

<!--en-->
The coverage conjunct is proved for every arity-one key in the code domain, with the pair decomposition named explicitly.
<!--zh-->
覆盖合取项对码域中每个元数一的键证明，对分解被显式名指。
<!--ja-->
覆いの連言項は、符号の領域の中の、アリティ一のキーそれぞれに対して証明されます。対の分解が明示的に名指されます。
<!--/-->

```agda
    all : ⟨ γ ⊨ allAt v w T C N ⟩
    all = RD.all-in (λ c p c∈ ec → PT.map
      (λ { (ψ , qp) →
        let qc : fst c ≡ fst (keyS W ψ)
            qc = ec ∙ cong (pr (# 1)) qp
```

<!--en-->
For a given arity-one key, decoding supplies merely a formula `ψ` whose code is the key's second component. Its definable subset `DA.defSet ψ` belongs to `𝒟ₒ (fst W)` by introduction, and the assumed equality transports this membership into the value slot. Decoding does not choose a unique or canonical formula.
<!--zh-->
对给定的元数一键，解码仅仅给出一条公式 `ψ`，其编码是该键的第二分量。由引入规则，可定义子集 `DA.defSet ψ` 属于 `𝒟ₒ (fst W)`；再沿假定的等式运输，便得到它属于取值槽。解码并未选出唯一或规范的公式。
<!--ja-->
与えられたアリティ一の鍵に対し、復号は、その第二成分を符号にもつ論理式 `ψ` が単に存在することだけを与えます。定義可能部分集合 `DA.defSet ψ` は導入によって `𝒟ₒ (fst W)` に属し、仮定した等式に沿う輸送で値の枠に入ります。復号は一意な論理式や標準的な論理式を選びません。
<!--/-->

```agda
            xS : S
            xS = down (lookup v γ) (DA.defSet ψ)
                   (subst (λ u → ⟨ DA.defSet ψ ∈ u ⟩) (sym qv) (𝒟ₒ-intro (fst W) (DA.defSet ψ) ∣ ψ , refl ∣₁))
        in entry ψ .fst , xS
         , ( subst (λ u → ⟨ pr u (fst (entry ψ .fst)) ∈ Tv ⟩) (sym qc) (entry ψ .snd .fst)
```

<!--en-->
The satisfaction table supplies the value attached to the decoded formula key, while `cuts-of` proves that this value cuts out exactly `DA.defSet ψ`. Together with the membership just obtained, these data satisfy the coverage clause. Because `decodeAll` is propositionally truncated and is eliminated only into that proposition-valued clause, the construction records existence without retaining a decoded formula.
<!--zh-->
满足关系表给出解码公式键所对应的取值，而 `cuts-of` 证明该取值从工作集中切出的恰是 `DA.defSet ψ`。连同刚得到的隶属，这些数据满足覆盖子句。由于 `decodeAll` 的结果受命题截断，且只被消去到这个命题值子句中，构造只记录存在性，并不保留解码所得的公式。
<!--ja-->
充足関係表は、復号された論理式の鍵に対応する値を与え、`cuts-of` は、その値が作業集合からちょうど `DA.defSet ψ` を切り出すことを示します。先ほど得た所属と合わせれば、これらのデータは覆いの条項を満たします。`decodeAll` の結果は命題的に切り詰められ、この命題値の条項にだけ消去されるので、構成は存在だけを記録し、復号された論理式を保持しません。
<!--/-->

```agda
           , ( subst (λ u → ⟨ DA.defSet ψ ∈ u ⟩) (sym qv) (𝒟ₒ-intro (fst W) (DA.defSet ψ) ∣ ψ , refl ∣₁)
             , subst (λ u → Cuts (DA.defSet ψ) Wv u) (sym (entry ψ .snd .snd)) (cuts-of ψ xS refl) ) ) })
      (decodeAll c (SR.C-out c c∈) 1 (fst p) ec))
```

<!--en-->
The exported soundness direction exposes the exact interface used later: once the working-set slot denotes `W`, `Tags` fixes the numeral slots, and `satAt` validates the code and satisfaction data, `defAt` implies equality with `𝒟ₒ (fst W)`. Thus the bounded formula receives its intended meaning only in this calibrated background.
<!--zh-->
导出的可靠性方向给出后文实际使用的精确接口：一旦工作集槽指称 `W`、`Tags` 固定数码槽且 `satAt` 校准码与满足数据，`defAt` 就推出与 `𝒟ₒ (fst W)` 相等。因此，这条有界公式只有在这一已校准背景中才具有预期语义。
<!--ja-->
公開される健全性の向きは、後で実際に使う正確なインターフェースを示します。作業集合の枠が `W` を表し、`Tags` が数の枠を固定し、`satAt` が符号と充足のデータを保証すれば、`defAt` から `𝒟ₒ (fst W)` との等しさが従います。したがって、この有界論理式が意図した意味をもつのは、このように整えられた背景の中です。
<!--/-->

```agda
def-sound : ∀ {m} (v w T C E : Fin m) (N : Fin 10 → Fin m) (γ : S ^ m) (W : S)
          → fst (lookup w γ) ≡ fst W → Tags γ N → ⟨ γ ⊨ satAt T w C E N ⟩
          → ⟨ γ ⊨ defAt v w T C N ⟩ → fst (lookup v γ) ≡ 𝒟ₒ (fst W)
def-sound v w T C E N γ W qw tg hs = DefRead.def-sound v w T C E N γ W qw tg hs

```

<!--en-->
The exported completeness direction has the same hypotheses and reverses the implication: equality with `𝒟ₒ (fst W)` reconstructs satisfaction of `defAt`. Together the two theorems characterize the definable-subset collection without choosing a representative formula for each member and without identifying it with the full internal power set.
<!--zh-->
导出的完备性方向具有相同前提，并反转上述蕴含：与 `𝒟ₒ (fst W)` 的相等可重建 `defAt` 的满足。两条定理合起来刻画可定义子集的集合，既不为每个成员选取代表公式，也不把它等同于完整的内部幂集。
<!--ja-->
公開される完全性の向きは同じ仮定をもち、含意を逆にします。`𝒟ₒ (fst W)` との等しさから `defAt` の充足が再構成されます。二つの定理を合わせると、各要素の代表論理式を選ぶことも、完全な内部冪集合と同一視することもなく、定義可能部分集合の集まりが特徴づけられます。
<!--/-->

```agda
def-complete : ∀ {m} (v w T C E : Fin m) (N : Fin 10 → Fin m) (γ : S ^ m) (W : S)
             → fst (lookup w γ) ≡ fst W → Tags γ N → ⟨ γ ⊨ satAt T w C E N ⟩
             → fst (lookup v γ) ≡ 𝒟ₒ (fst W) → ⟨ γ ⊨ defAt v w T C N ⟩
def-complete v w T C E N γ W qw tg hs = DefRead.def-complete v w T C E N γ W qw tg hs
```
