```agda
{-# OPTIONS --cubical --safe --guardedness #-}
```

<!--en-->
# A Δ₀ description of the constructible hierarchy
<!--zh-->
# 可构造层级的 Δ₀ 描述
<!--ja-->
# 構成可能階層の Δ₀ 記述
<!--/-->

```agda
open import Base.Prelude
open import Base.Classical using ( LEM )
```

<!--en-->
Fix a universe level `ℓ` and excluded middle for propositions at level `ℓ-suc ℓ`. Every formula, reader, and final correctness theorem in the chapter is relative to this one explicit classical hypothesis.
<!--zh-->
固定宇宙层级 `ℓ`，并假设层级 `ℓ-suc ℓ` 上命题的排中律。本章的每条公式、读引理与最终正确性定理都相对于这一个显式经典假设陈述。
<!--ja-->
宇宙レベル `ℓ` と、レベル `ℓ-suc ℓ` の命題に対する排中律を固定する。本章の論理式、読み補題、そして最終的な正しさの定理は、すべてこの一つの明示的な古典的仮定に相対して述べられる。
<!--/-->

```agda
module L.GCH.HierarchyDescription {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where
```

```agda
open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula; var; _∈̇_; _∧̇_; ⊤̇; ⊥̇; ∃̇∈; ∀̇∈ )
open import FOL.LevyHierarchy using ( Δ₀; checkΔ₀; δ-∧; δ-∃∈ )
open import FOL.Manipulation.ConstantOccurrences using ( countFo )
open import FOL.Manipulation.ConstantMapping using ( embed )
open import FOL.Manipulation.Relabelling using ( embed-⊨; mapΔ₀ )
import FOL.Absoluteness
import FOL.Semantics
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ; ∈-induction; extensionalV )
open import V.Coding {ℓ} using ( pr )
open import L.Constructible {ℓ} using
  ( 𝒮ʟ; isL; isL-trans; IsOrd; Lset; Lset-in; Lset-out; Lset-mono; 𝒟ₒ )
open import L.Ordinal {ℓ} using ( mem-ord; suc-ord; #∈ω )
open import L.Axioms.Basic {ℓ} using ( LsetS; Lset-suc )
open import L.Axioms.Numerals {ℓ} using ( numeralL-fst )
open import L.Coding.Expressions {ℓ} using ( sucAtL )
open import L.Coding.NumeralBound {ℓ} lem using ( module Bound )
open import L.Coding.CodeSet {ℓ} lem using ( AllCodes )
open import L.Coding.Model {ℓ} using ( container )
open import L.Coding.Quantification {ℓ} using
  ( sh; i0; i1; i2; i3; i8; f0; f1; f2; f3; f4; f5; f6; f7; f8; f9
  ; down; suc-out; suc-in; sndEx; sndAll; bothAll
  ; sndEx-out; sndAll-in; bothAll-in; fillSnd; useSnd; useBoth; sndS )
open import L.Coding.CodeDomain {ℓ} using ( Tags; shN )
open import L.Coding.EnvironmentTower {ℓ} lem using ( nn; module Tower )
open import L.Hierarchy {ℓ} lem using ( hierL-spec; IsHier; hier-out; hier-in; Values; Entries )
open import L.GCH.SkolemHull {ℓ} lem using ( module Cnt; erase-Δ₀; isOrd-at-p; Δ₀-isOrd-at-p; _⊨ₚ_ )
open import L.Coding.SatisfactionGraphSet {ℓ} lem using ( module SatGraph )
open import L.GCH.SatisfactionDescription {ℓ} lem using ( satAt; sat-complete )
open import L.GCH.DefinablePowerSetDescription {ℓ} lem using ( defAt; def-sound; def-complete )
open import L.GCH.AdequateStages {ℓ} lem using ( Adequate; module Adequate; module At; Lset∈suc )
```

<!--en-->
The later condensation argument must transport the assertion that a set is the constructible stage at a given ordinal. Since elementarity transports formulas rather than the external operation `Lset`, this chapter builds a bounded object-language formula that recognizes the same stage relation, using a third set as a common bound for all auxiliary witnesses.
<!--zh-->
后续的凝聚论证需要搬运「某集合是给定序数处的可构造层」这一断言。初等性搬运的是公式，而不是外围定义的运算 `Lset`，所以本章构造一条有界的对象语言公式来识别同一个层关系，并以第三个集合作为全部辅助见证的公共界。
<!--ja-->
後の凝縮の議論では、ある集合が与えられた順序数における構成可能段階である、という主張を移す必要がある。初等性が移すのは論理式であって、外部で定義された演算 `Lset` ではない。そこで本章は、同じ段階関係を認識する有界な対象言語の論理式を作り、第三の集合をすべての補助的な証人に共通する上界として用いる。
<!--/-->

<!--en-->
The construction is classical only through one fixed instance of excluded middle. Bounded existential formulas are nevertheless read as propositionally truncated existence, so classical background does not turn the hidden tables into chosen global data.
<!--zh-->
这一构造的经典性只来自一个固定的排中律实例。不过，有界存在公式仍被读作命题截断的存在，因此经典背景并不会把隐藏的诸表变成全局选定的数据。
<!--ja-->
この構成で用いる古典性は、固定された一つの排中律の実例だけに由来する。それでも有界存在の論理式は命題的に切り詰められた存在として読まれるため、古典的な背景から、隠れた表を大域的に選んだデータが得られるわけではない。
<!--/-->

```agda
open import Cubical.Data.FinData using ( weakenFin )
```



<!--en-->
The object language needs only membership, conjunction, truth, falsity, and bounded quantifiers. These constructors admit structural Δ₀ witnesses. Later, proving that no constants occur allows the constant domain to be changed to the empty alphabet, making the final three-variable formula parameter-free without removing its free variables.
<!--zh-->
这里的对象语言只需要隶属、合取、真、假与有界量词；这些构造子都具有结构性的 Δ₀ 见证。稍后证明公式不含常元，便可把常元域改为空字母表，使最终的三变元公式成为无参公式，同时保留其自由变元。
<!--ja-->
ここで対象言語に必要なのは、所属、連言、真、偽、有界量化子だけである。これらの構成子には構造に沿った Δ₀ の証人がある。後で定数が現れないことを示せば、定数域を空のアルファベットへ変えられる。こうして自由変数を残したまま、最終的な三変数の論理式をパラメータなしにする。
<!--/-->

<!--en-->
A bounded formula can be read both inside the constructible carrier and in the ambient cumulative hierarchy. Δ₀ absoluteness identifies those readings. Membership induction will validate table rows from lower rows, while extensionality will turn the two resulting membership implications into equality of stages.
<!--zh-->
同一条有界公式既可在可构造载体内部读取，也可在外围累积层级中读取；Δ₀ 绝对性认同这两种读法。隶属归纳将由更低的表行验证当前表行，外延性则把由此得到的两个隶属蕴含化为层的相等。
<!--ja-->
同じ有界論理式は、構成可能な台の内部でも、周囲の累積階層でも読める。Δ₀ 絶対性がこの二つの読みを同定する。所属帰納法は、より下の行から現在の表の行を検証し、外延性は、そこから得られる二つの所属の含意を段階の等しさへ変える。
<!--/-->

<!--en-->
The stage `Lset b` is assembled from the definable power sets of earlier stages: its members come from some `𝒟ₒ (Lset c)` with `c ∈ b`, and each such contribution lies in `Lset b`. The inward and outward membership rules express these two directions; ordinal facts ensure that the indices used later really are stage indices.
<!--zh-->
层 `Lset b` 由此前各层的可定义幂集组装而成：它的每个成员都来自某个满足 `c ∈ b` 的 `𝒟ₒ (Lset c)`，而每一份这样的贡献都属于 `Lset b`。向内与向外的隶属规则表达这两个方向；序数事实则保证后文使用的索引确实是层索引。
<!--ja-->
段階 `Lset b` は、それ以前の段階の定義可能冪集合から組み立てられる。その各要素は、ある `c ∈ b` に対する `𝒟ₒ (Lset c)` から来ており、そのような寄与はすべて `Lset b` に属する。所属についての内向きと外向きの規則がこの二方向を表し、順序数の事実が、後で使う添字が実際に段階の添字であることを保証する。
<!--/-->

<!--en-->
Recognizing one definable power set internally requires formula codes, a satisfaction table, and an environment tower. Ordered-pair encodings then join each stage index to its recorded value. These auxiliary sets will all be bounded by the same witness set `z`, keeping the complete description within Δ₀.
<!--zh-->
在模型内部识别一个可定义幂集，需要公式码、满足关系表与环境塔；有序对编码再把每个层索引同其记录值连接起来。这些辅助集合都将由同一个见证集 `z` 界住，从而使完整描述保持在 Δ₀ 中。
<!--ja-->
一つの定義可能冪集合を内部で認識するには、論理式の符号、充足関係表、環境の塔が必要である。順序対の符号化は、各段階の添字をその記録された値と結びつける。これらの補助集合はすべて同じ証人集合 `z` で有界化されるため、記述全体が Δ₀ にとどまる。
<!--/-->

<!--en-->
The components of a set-coded pair cannot be projected by an unbounded operation inside the object language. Instead, bounded component formulas range through a small container and read or fill the pair there. Ten named slots hold the numeral tags used by the coding descriptions, and shifting those names keeps them aligned when new witnesses extend the environment.
<!--zh-->
在对象语言内部，不能用无界运算投影集合编码的有序对分量。这里改用有界的分量公式，在一个小容器中遍历并读取或填入该有序对。十个具名槽位保存编码描述所用的数码标签；每次新见证扩展环境时，对这些名称作移位便能保持槽位对齐。
<!--ja-->
対象言語の内部では、集合として符号化された順序対の成分を非有界な演算で射影することはできない。代わりに、有界な成分論理式が小さな容器の中を動き、そこで対を読んだり埋めたりする。十個の名前付きスロットには符号化の記述で使う数項タグが入り、新しい証人で環境を拡張するときには、その名前をずらして位置を保つ。
<!--/-->

<!--en-->
Three semantic specifications meet here. A hierarchy table records pairs `(c,Lset c)` below a bound; the satisfaction description recognizes the genuine code, environment, and satisfaction data over a stage; and the definable-power-set description recognizes the set `𝒟ₒ (Lset c)`. Soundness will recover only the table properties `Values` and `Entries`, whereas completeness begins with the exact specification `IsHier`.
<!--zh-->
这里汇合了三类语义规格。层级表在一个界以下记录形如 `(c,Lset c)` 的有序对；满足描述识别一层上的真实码、环境与满足关系数据；可定义幂集描述则识别集合 `𝒟ₒ (Lset c)`。可靠性只会恢复表性质 `Values` 与 `Entries`，完备性则从精确规格 `IsHier` 出发。
<!--ja-->
ここでは三つの意味論的な仕様が合流する。階層表は上界より下の対 `(c,Lset c)` を記録し、充足の記述は一つの段階上の真正な符号、環境、充足関係のデータを認識し、定義可能冪集合の記述は集合 `𝒟ₒ (Lset c)` を認識する。健全性が復元する表の性質は `Values` と `Entries` だけであり、完全性は正確な仕様 `IsHier` から始まる。
<!--/-->

<!--en-->
Completeness needs one common stage containing every auxiliary witness. If `γ` is adequate and `c ∈ γ`, then `Lset γ` contains the hierarchy table, code set, satisfaction table, and environment tower required at `c`; successor closure also places the next stage there, while `ω ∈ γ` supplies all ten finite numeral tags.
<!--zh-->
完备性需要一个包含全部辅助见证的公共层。若 `γ` 充分且 `c ∈ γ`，则 `Lset γ` 含有在 `c` 处所需的层级表、码集、满足关系表与环境塔；后继封闭还把下一层放入其中，而 `ω ∈ γ` 则供给全部十个有限数码标签。
<!--ja-->
完全性には、すべての補助的な証人を含む一つの共通段階が必要である。`γ` が十分で `c ∈ γ` なら、`Lset γ` は `c` で必要な階層表、符号集合、充足関係表、環境の塔を含む。後続に関する閉性は次の段階もそこへ入れ、`ω ∈ γ` は十個の有限な数項タグをすべて与える。
<!--/-->

<!--en-->
An environment is a finite vector of constructible sets. Introducing a bounded witness places it at the front and shifts every older slot by one; finite indices make those shifts explicit. This bookkeeping is what lets the same stage, table, and bound names survive through several nested quantifiers.
<!--zh-->
环境是可构造集合组成的有限向量。引入一个有界见证时，它被放到向量前端，原有每个槽位都后移一位；有限索引把这些移位显式记录下来。正因如此，同一组层、表与界的名称才能穿过多层嵌套量词而保持不变。
<!--ja-->
環境は構成可能集合からなる有限ベクトルである。有界な証人を導入すると、それは先頭に置かれ、以前の各スロットは一つずつ後ろへずれる。有限添字がこのずれを明示する。この管理によって、同じ段階、表、上界の名前を、入れ子になった複数の量化子の中でも保つことができる。
<!--/-->

<!--en-->
Existential satisfaction retains only propositional truncation: it records that suitable data exist and forgets which data were used. Every later elimination therefore targets a proposition. In particular, membership is proposition-valued and equality of cumulative-hierarchy sets is a proposition, so the two conclusions needed in the proof are legitimate targets.
<!--zh-->
存在公式的满足只保留命题截断：它记录合适的数据存在，却忘去具体用了哪一份数据。因此后文每次消去都以命题为目标。这里隶属取命题值，而累积层级中集合的相等也是命题，所以证明所需的这两类结论都可作为合法目标。
<!--ja-->
存在論理式の充足が保つのは命題的切り詰めだけである。適切なデータが存在することを記録し、どのデータを使ったかは忘れる。したがって、後で切り詰めを除去するときの行き先は常に命題である。ここでは所属が命題値であり、累積階層の集合の等しさも命題なので、証明で必要な二種類の結論はいずれも正当な行き先になる。
<!--/-->

```agda
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_; setIsSet )
```

<!--en-->
The ten finite tags are represented by the von Neumann numerals inside the hierarchy. Zero is the empty set, each following tag is obtained by set-theoretic successor, and all ten lie in `ω`. Membership readers connect these ambient sets with their presentations as elements of the constructible carrier.
<!--zh-->
十个有限标签由层级内部的 von Neumann 数码表示。零是空集，之后每个标签由集合论后继得到，而且十个数码都属于 `ω`。隶属读式把这些外围集合与它们作为可构造载体元素的呈现连接起来。
<!--ja-->
十個の有限なタグは、階層内部の von Neumann 数項で表される。零は空集合であり、後の各タグは集合論的な後続によって得られ、十個すべてが `ω` に属する。所属の読みは、これらの周囲の集合を、構成可能な台の要素としての表示と結びつける。
<!--/-->

```agda
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ∈∈ₛ )
open import Cubical.HITs.CumulativeHierarchy.Constructions using ( ∅; ∅-empty; module InfinitySet )
open InfinitySet {ℓ} using ( #_; sucV; ω )
```

<!--en-->
Write `S` for the carrier of the constructible model. Its elements present ambient sets together with proofs of constructibility. All hidden tables and witnesses are quantified over this carrier, and the final visible slots will likewise present the value `a`, its stage index `p`, and the common bound `z`.
<!--zh-->
以 `S` 表示可构造模型的载体。它的元素由外围集合及其可构造性证明组成。所有隐藏的表与见证都在这一载体上量化；最终保留的可见槽位也分别呈现取值 `a`、层索引 `p` 与公共界 `z`。
<!--ja-->
構成可能モデルの台を `S` と書く。その要素は、周囲の集合とその構成可能性の証明を組にして提示する。隠れた表と証人はすべてこの台の上で量化され、最後に見えるスロットも、値 `a`、その段階の添字 `p`、共通の上界 `z` をそれぞれ提示する。
<!--/-->

```agda
open hPropStructure 𝒮ʟ using ( S )
```

<!--en-->
Satisfaction inside `L` and satisfaction in the ambient hierarchy use different structures but agree on Δ₀ formulas whose parameters come from `L`. The lemma `abs₀` is the bridge between them. This bridge will let completeness build the formula internally and soundness read the transported formula back as an ambient equality of stages.
<!--zh-->
`L` 内部的满足关系与外围层级中的满足关系使用不同结构，但当 Δ₀ 公式的参数来自 `L` 时，两种读法一致。引理 `abs₀` 正是二者之间的桥。借助它，完备性可以在内部构造公式的满足，而可靠性可以把搬运后的公式读回外围的层相等。
<!--ja-->
`L` の内部での充足と周囲の階層での充足は異なる構造を使うが、パラメータが `L` から来る Δ₀ 論理式については一致する。補題 `abs₀` が両者の橋である。この橋により、完全性は内部で論理式の充足を組み立て、健全性は移された論理式を周囲での段階の等しさとして読み戻せる。
<!--/-->

```agda
module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans using ( _^_; _⊨ᵐ_; abs₀ )
open AbsL using ( _^_ ) renaming ( _⊨ᵐ_ to _⊨_ )
module SemVᵃ = FOL.Semantics 𝒮ᵥ
```

<!--en-->
The formula `defIn w z N body` uses four nested bounded existentials to place a satisfaction table `T`, a code set `C`, an environment tower `E`, and a value `d` inside `z`. The satisfaction description validates `T`, `C`, and `E` over the value at `w`; the power-set description identifies `d` with its definable power set; and `body` states what is required of that `d`. Satisfaction retains only the propositional truncation of these witnesses, and the formula does not characterize `z` uniquely.
<!--zh-->
公式 `defIn w z N body` 用四层嵌套的有界存在量词，把满足关系表 `T`、码集 `C`、环境塔 `E` 与取值 `d` 放入 `z`。满足描述验证 `w` 处取值上的 `T`、`C`、`E`，可定义幂集描述把 `d` 认同为该取值的可定义幂集，而 `body` 则陈述对 `d` 的进一步要求。满足关系只保留这些见证的命题截断，并且该公式并不唯一刻画 `z`。
<!--ja-->
論理式 `defIn w z N body` は、四重の有界存在量化子を使って、充足関係表 `T`、符号集合 `C`、環境の塔 `E`、値 `d` を `z` の中に置く。充足の記述は `w` の値上の `T`、`C`、`E` を検証し、定義可能冪集合の記述は `d` をその値の定義可能冪集合と同定し、`body` はその `d` に対する追加の条件を述べる。充足が保つのはこれらの証人の命題的切り詰めだけであり、この論理式は `z` を一意には特徴づけない。
<!--/-->

```agda
defIn : ∀ {k} → Fin k → Fin k → (Fin 10 → Fin k) → Formula S (4 + k) → Formula S k
defIn w z N body =
  ∃̇∈ (var z) (∃̇∈ (var (sh 1 z)) (∃̇∈ (var (sh 2 z)) (∃̇∈ (var (sh 3 z))
    (satAt i3 (sh 4 w) i2 i1 (shN 4 N) ∧̇ (defAt i0 (sh 4 w) i3 i2 (shN 4 N) ∧̇ body)))))
```

<!--en-->
The inward inclusion `intoAt` says that each `x ∈ v` is accounted for by an earlier stage index `c ∈ b`: some pair-shaped member of `f` records a value `w` at `c`, and `x` belongs to the definable power set of `w`. In bounded notation its outer shape is `∀[ x ∈ v ] ∃[ c ∈ b ] ...`; the remaining bounded witnesses expose the row and the data used to recognize that power set.
<!--zh-->
内向包含式 `intoAt` 说，每个 `x ∈ v` 都由某个更早的层索引 `c ∈ b` 说明：`f` 中有一个有序对形的成员在 `c` 处记录取值 `w`，而 `x` 属于 `w` 的可定义幂集。其外层有界形状是 `∀[ x ∈ v ] ∃[ c ∈ b ] ...`；余下的有界见证展开该表行以及识别这个幂集所需的数据。
<!--ja-->
内向きの包含を表す `intoAt` は、各 `x ∈ v` が、それ以前の段階の添字 `c ∈ b` によって説明されることを述べる。すなわち、`f` の順序対の形をしたある要素が `c` で値 `w` を記録し、`x` は `w` の定義可能冪集合に属する。外側の有界な形は `∀[ x ∈ v ] ∃[ c ∈ b ] ...` であり、残りの有界な証人が、その行と冪集合を認識するためのデータを展開する。
<!--/-->

```agda
intoAt : ∀ {m} → Fin m → Fin m → Fin m → Fin m → (Fin 10 → Fin m) → Formula S m
intoAt v b f z N =
  ∀̇∈ (var v) (∃̇∈ (var (sh 1 b)) (∃̇∈ (var (sh 2 f))
    (sndEx i0 i1 (defIn i0 (sh 5 z) (shN 5 N) (var i8 ∈̇ var i0)))))
```

<!--en-->
The reverse inclusion `overAt` ranges over `c ∈ b` and over members of `f` that are presented as pairs `(c,w)`. For each such presentation, every element of the definable power set of `w` must belong to `v`. The clause says nothing about a member of `f` that has no such pair presentation, so it must not be read as excluding arbitrary junk from the whole candidate table.
<!--zh-->
反向包含式 `overAt` 遍历 `c ∈ b`，并遍历 `f` 中可呈现为有序对 `(c,w)` 的成员。对每个这样的呈现，`w` 的可定义幂集的每个成员都必须属于 `v`。该子句不讨论 `f` 中无法如此呈现的成员，因此不能把它读成从整个候选表中排除了任意垃圾成员。
<!--ja-->
逆向きの包含を表す `overAt` は、`c ∈ b` と、対 `(c,w)` として提示される `f` の要素を動く。そのような提示ごとに、`w` の定義可能冪集合のすべての要素が `v` に属することを要求する。この節は、そのような対として提示されない `f` の要素については何も述べないため、候補表全体から任意の余分な要素を排除するものとは読めない。
<!--/-->

```agda
overAt : ∀ {m} → Fin m → Fin m → Fin m → Fin m → (Fin 10 → Fin m) → Formula S m
overAt v b f z N =
  ∀̇∈ (var b) (∀̇∈ (var (sh 1 f))
    (sndAll i0 i1 (defIn i0 (sh 4 z) (shN 4 N) (∀̇∈ (var i0) (var i0 ∈̇ var (sh 9 v))))))
```

<!--en-->
The conjunction `stepAt` combines the two inclusions. Relative to the pair rows recorded below `b`, `intoAt` says that `v` has no additional members, while `overAt` says that none of the definable-power-set contributions is missing. Correct table values are a separate hypothesis of the later read lemma.
<!--zh-->
合取式 `stepAt` 合并这两个包含。相对于 `b` 以下记录的有序对表行，`intoAt` 说明 `v` 没有额外成员，`overAt` 则说明可定义幂集的贡献一项不缺。表中取值的正确性是后续读引理另行要求的假设。
<!--ja-->
連言 `stepAt` は二つの包含をまとめる。`b` より下に記録された対の行に相対して、`intoAt` は `v` に余分な要素がないことを述べ、`overAt` は定義可能冪集合からの寄与が一つも欠けないことを述べる。表の値が正しいことは、後の読み補題が別に要求する仮定である。
<!--/-->

```agda
stepAt : ∀ {m} → Fin m → Fin m → Fin m → Fin m → (Fin 10 → Fin m) → Formula S m
stepAt v b f z N = intoAt v b f z N ∧̇ overAt v b f z N
```

<!--en-->
The first half of `approxAt` gives coverage: every `c ∈ b` has some pair-shaped entry in `f`. The second half tests `stepAt w c f z N` whenever a member of `f` is presented as a pair `(c,w)`. It does not say that every member of `f` is a pair or that every recorded first component lies below `b`. Accordingly, `approx-out` will recover exactly `Values f b × Entries f b`, not equality with the entire hierarchy graph and not a global no-junk property.
<!--zh-->
`approxAt` 的前半给出覆盖性：每个 `c ∈ b` 在 `f` 中都有某个有序对形的表项。后半则在 `f` 的一个成员被呈现为 `(c,w)` 时检验 `stepAt w c f z N`。它并未断言 `f` 的每个成员都是有序对，也未断言每个被记录的第一分量都低于 `b`。因此，`approx-out` 恰好恢复 `Values f b × Entries f b`，既不恢复与整个层级图的相等，也不恢复全局的无垃圾性质。
<!--ja-->
`approxAt` の前半は被覆を与える。すべての `c ∈ b` について、`f` に順序対の形をした何らかの項目がある。後半は、`f` の要素が対 `(c,w)` として提示されたときに `stepAt w c f z N` を検査する。`f` の各要素が対であることも、記録された各第一成分が `b` より下にあることも述べない。したがって `approx-out` が復元するのは正確に `Values f b × Entries f b` であり、表全体と階層グラフとの等しさでも、大域的に余分な要素がないという性質でもない。
<!--/-->

```agda
approxAt : ∀ {m} → Fin m → Fin m → Fin m → (Fin 10 → Fin m) → Formula S m
approxAt f b z N =
    ∀̇∈ (var b) (∃̇∈ (var (sh 1 f)) (sndEx i0 i1 ⊤̇))
  ∧̇ ∀̇∈ (var f) (bothAll i0 (stepAt i0 i1 (sh 4 f) (sh 4 z) (shN 4 N)))
```

<!--en-->
The clause `hierAt a p f z N` joins an approximation below `p` to one final step at `p`. If the approximation supplies `Values` and `Entries`, the final step identifies `a` with `Lset p`; conversely, an exact hierarchy table `IsHier p f` and adequate supplies fill both conjuncts. This is the local stage relation that the final three-variable formula will hide behind bounded witnesses.
<!--zh-->
子句 `hierAt a p f z N` 把 `p` 以下的逼近与 `p` 处的最后一步连接起来。若逼近给出 `Values` 与 `Entries`，最后一步便把 `a` 认同为 `Lset p`；反过来，精确的层级表 `IsHier p f` 与充分的见证供应可以填入两个合取支。这就是最终三变元公式将在有界见证之后隐藏的局部层关系。
<!--ja-->
節 `hierAt a p f z N` は、`p` より下の近似と、`p` における最後の一段階を結びつける。近似から `Values` と `Entries` が得られれば、最後の一段階は `a` を `Lset p` と同定する。逆に、正確な階層表 `IsHier p f` と十分な証人の供給があれば、二つの連言を埋められる。これは、最終的な三変数の論理式が有界な証人の背後に隠す、局所的な段階関係である。
<!--/-->

```agda
hierAt : ∀ {m} → Fin m → Fin m → Fin m → Fin m → (Fin 10 → Fin m) → Formula S m
hierAt a p f z N = approxAt f p z N ∧̇ stepAt a p f z N
```

<!--en-->
The tag clause pins the ten slots to the numerals: the first slot has no members, so it is the empty set.
<!--zh-->
标签子句把十个槽位钉在数码上：第一个槽位没有成员，故它是空集。
<!--ja-->
タグの節は、十の枠を数項に固定する。最初の枠には要素がないので、それは空集合である。
<!--/-->

```agda
pins : ∀ {m} → (Fin 10 → Fin m) → Formula S m
pins N =
    ∀̇∈ (var (N f0)) ⊥̇
  ∧̇ ( sucAtL (N f0) (N f1) ∧̇ ( sucAtL (N f1) (N f2) ∧̇ ( sucAtL (N f2) (N f3)
  ∧̇ ( sucAtL (N f3) (N f4) ∧̇ ( sucAtL (N f4) (N f5) ∧̇ ( sucAtL (N f5) (N f6)
```

<!--en-->
The remaining nine slots are linked by nine successor assertions, so the ten slots are exactly the numerals zero through nine.
<!--zh-->
其余九个槽位由九条后继断言串联，于是十个槽位恰是数码零至九。
<!--ja-->
残りの九つの枠は九つの後続の主張でつながれ、こうして十の枠は、数項の 0 から 9 にちょうどなる。
<!--/-->

```agda
  ∧̇ ( sucAtL (N f6) (N f7) ∧̇ ( sucAtL (N f7) (N f8) ∧̇ sucAtL (N f8) (N f9) ))))))))
```

<!--en-->
## The bounded clauses of the hierarchy table
<!--zh-->
## 层级表的有界子句
<!--ja-->
## 階層表を表す有界な節
<!--/-->

<!--en-->
To use the ten tags in later descriptions, their object-language pinning must agree with the semantic record `Tags γ N`. The next two lemmas prove both directions: one reads numeral equalities from `pins`, and the other reconstructs `pins` from those equalities.
<!--zh-->
为了在后续描述中使用这十个标签，对象语言中的固定条件必须与语义记录 `Tags γ N` 一致。接下来的两个引理证明两个方向：一个从 `pins` 读出数码等式，另一个由这些等式重建 `pins`。
<!--ja-->
後の記述で十個のタグを使うには、対象言語での固定条件が意味論的な記録 `Tags γ N` と一致しなければならない。次の二つの補題が両方向を示す。一方は `pins` から数項の等式を読み、もう一方はその等式から `pins` を再構成する。
<!--/-->

<details open class="submodule-fold">
<summary class="submodule-fold-heading">
```agda
module PinsRead {m : ℕ} (N : Fin 10 → Fin m) (γ : S ^ m) where
```
</summary>
<div class="submodule-fold-content">

<!--en-->
Reading the tag clause first shows that the first slot is empty: it has no members.
<!--zh-->
读取标签子句先证第一个槽位为空：它没有成员。
<!--ja-->
タグの節の読みは、まず最初の枠が空であることを示す。要素をもたないのである。
<!--/-->

```agda
  pins-out : ⟨ γ ⊨ pins N ⟩ → Tags γ N
  pins-out (h0 , hs) = go
    where
    q0 : fst (lookup (N f0) γ) ≡ # 0
    q0 = extensionalV (λ y → ⇔toPath
```

<!--en-->
Emptiness is an extensionality argument in both directions: any member of the first slot would contradict the falsity clause, and the empty set has no members to begin with.
<!--zh-->
空性是双向的外延性论证：第一个槽位的任何成员都会与假值子句矛盾，而空集本无成员。
<!--ja-->
空であることは、両方向の外延性の議論である。最初の枠のどんな要素も偽の節と矛盾し、そもそも空集合には要素がない。
<!--/-->

```agda
      (λ y∈ → ⊥*-rec (h0 (down (lookup (N f0) γ) y y∈) y∈))
      (λ y∈ → ⊥₀-rec (∅-empty y (∈∈ₛ {a = y} {b = ∅} .fst y∈))))
```

<!--en-->
The auxiliary lemma `up` advances one link of the numeral chain. If slot `i` denotes `# k` and `sucAtL i j` holds, its sound reading identifies slot `j` with `sucV (# k)`, hence with the numeral `# (suc k)`.
<!--zh-->
辅助引理 `up` 沿数码链前进一步。若槽位 `i` 表示 `# k` 且 `sucAtL i j` 成立，则其可靠读法把槽位 `j` 认同为 `sucV (# k)`，因而认同为数码 `# (suc k)`。
<!--ja-->
補助補題 `up` は数項の鎖を一つ進める。スロット `i` が `# k` を表し、`sucAtL i j` が成り立つなら、その健全な読みはスロット `j` を `sucV (# k)`、したがって数項 `# (suc k)` と同定する。
<!--/-->

```agda
    up : (i j : Fin m) (k : ℕ) → ⟨ γ ⊨ sucAtL i j ⟩ → fst (lookup i γ) ≡ # k
       → fst (lookup j γ) ≡ # (suc k)
    up i j k h q = suc-out i j γ h ∙ cong sucV q
```

<!--en-->
Starting from the equality for zero, the first five successor clauses yield `q1` through `q5`. Thus the slots named by `f1` through `f5` are identified successively with the numerals one through five.
<!--zh-->
从零的等式出发，前五条后继子句依次给出 `q1` 至 `q5`。因此，由 `f1` 至 `f5` 命名的槽位分别被认同为数码一至五。
<!--ja-->
零についての等式から始め、最初の五つの後続の節によって `q1` から `q5` が順に得られる。したがって `f1` から `f5` が名付けるスロットは、それぞれ数項一から五と同定される。
<!--/-->

```agda
    q1 = up (N f0) (N f1) 0 (hs .fst) q0
    q2 = up (N f1) (N f2) 1 (hs .snd .fst) q1
    q3 = up (N f2) (N f3) 2 (hs .snd .snd .fst) q2
    q4 = up (N f3) (N f4) 3 (hs .snd .snd .snd .fst) q3
    q5 = up (N f4) (N f5) 4 (hs .snd .snd .snd .snd .fst) q4
```

<!--en-->
The remaining four successor clauses continue the same chain, producing `q6` through `q9`. This identifies the slots `f6` through `f9` with the numerals six through nine and completes the numerical part of the reading.
<!--zh-->
余下四条后继子句延续同一条链，给出 `q6` 至 `q9`。由此，槽位 `f6` 至 `f9` 分别被认同为数码六至九，数码读取也随之完成。
<!--ja-->
残り四つの後続の節が同じ鎖を続け、`q6` から `q9` を与える。これにより、スロット `f6` から `f9` は数項六から九と同定され、数項についての読みが完成する。
<!--/-->

```agda
    q6 = up (N f5) (N f6) 5 (hs .snd .snd .snd .snd .snd .fst) q5
    q7 = up (N f6) (N f7) 6 (hs .snd .snd .snd .snd .snd .snd .fst) q6
    q8 = up (N f7) (N f8) 7 (hs .snd .snd .snd .snd .snd .snd .snd .fst) q7
    q9 = up (N f8) (N f9) 8 (hs .snd .snd .snd .snd .snd .snd .snd .snd) q8
```

<!--en-->
The record `Tags γ N` asks for the corresponding numeral equality at each element of `Fin 10`. The first four cases return `q0`, `q1`, `q2`, and `q3`, matching the tags zero through three.
<!--zh-->
记录 `Tags γ N` 要求对 `Fin 10` 的每个元素给出相应的数码等式。前四个情形返回 `q0`、`q1`、`q2` 与 `q3`，分别对应标签零至三。
<!--ja-->
記録 `Tags γ N` は、`Fin 10` の各要素について対応する数項の等式を要求する。最初の四つの場合は `q0`、`q1`、`q2`、`q3` を返し、零から三までのタグに対応する。
<!--/-->

```agda
    go : Tags γ N
    go zero = q0
    go (suc zero) = q1
    go (suc (suc zero)) = q2
    go (suc (suc (suc zero))) = q3
```

<!--en-->
The next five cases of `go` return `q4` through `q8`. Written as nested successors, these patterns exhaust the tags four through eight without introducing any additional arithmetic argument.
<!--zh-->
`go` 接下来的五个情形返回 `q4` 至 `q8`。这些模式写成嵌套后继，直接穷尽标签四至八，无须再引入算术论证。
<!--ja-->
`go` の次の五つの場合は `q4` から `q8` を返す。入れ子の後続として書かれたこれらのパターンは、追加の算術的な議論なしに、タグ四から八を尽くす。
<!--/-->

```agda
    go (suc (suc (suc (suc zero)))) = q4
    go (suc (suc (suc (suc (suc zero))))) = q5
    go (suc (suc (suc (suc (suc (suc zero)))))) = q6
    go (suc (suc (suc (suc (suc (suc (suc zero))))))) = q7
    go (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) = q8
```

<!--en-->
The sole remaining case of `Fin 10` is the ninth successor of zero, and it returns `q9`. The case analysis now supplies all ten numeral equalities required by `Tags γ N`.
<!--zh-->
`Fin 10` 唯一剩余的情形是零的第九次后继，它返回 `q9`。至此，分类讨论供给了 `Tags γ N` 所需的全部十条数码等式。
<!--ja-->
`Fin 10` に残る唯一の場合は、零の九回目の後続であり、`q9` を返す。これで場合分けは、`Tags γ N` が要求する十個すべての数項の等式を与える。
<!--/-->

```agda
    go (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))) = q9
```

<!--en-->
For the converse direction, suppose the slots already satisfy `Tags γ N`. A purported member of the zero slot transports along its tag equality to a member of the empty set and is therefore impossible. The same tag equalities then provide the data from which the nine successor clauses are filled.
<!--zh-->
反过来，设这些槽位已经满足 `Tags γ N`。零槽位的任意假定成员都可沿标签等式搬运为空集的成员，因而不可能存在；同一组标签等式随后供给填入九条后继子句所需的数据。
<!--ja-->
逆向きには、スロットがすでに `Tags γ N` を満たすとする。零のスロットの要素と仮定されたものは、タグの等式に沿って空集合の要素へ移されるため、存在できない。同じタグの等式が、九つの後続の節を埋めるためのデータも与える。
<!--/-->

```agda
  pins-in : Tags γ N → ⟨ γ ⊨ pins N ⟩
  pins-in tg =
      (λ x x∈ → ⊥₀-rec (∅-empty (fst x) (∈∈ₛ {a = fst x} {b = ∅} .fst
                  (subst (λ u → ⟨ fst x ∈ u ⟩) (tg f0) x∈))))
    , ( st f0 f1 refl , ( st f1 f2 refl , ( st f2 f3 refl , ( st f3 f4 refl , ( st f4 f5 refl , ( st f5 f6 refl
```

<!--en-->
Each successor clause is reconstructed by applying the inward successor reader after transporting both tag slots along their numeral equalities.
<!--zh-->
每条后继子句都先沿相应的数码等式改写两个标签槽，再应用后继公式的向内读法来重建。
<!--ja-->
各後続の節は、二つのタグのスロットを対応する数項の等式に沿って書き換えた後、後続論理式の内向きの読みを適用して再構成する。
<!--/-->

```agda
    , ( st f6 f7 refl , ( st f7 f8 refl , st f8 f9 refl ))))))))
    where
    st : (j k : Fin 10) → # (toℕ k) ≡ sucV (# (toℕ j)) → ⟨ γ ⊨ sucAtL (N j) (N k) ⟩
    st j k e = suc-in (N j) (N k) γ (tg k ∙ e ∙ cong sucV (sym (tg j)))
```
</div>
</details>

<!--en-->
Fix an environment `δ` whose ten named slots have the required numeral values. Let `Wv` be the underlying set at `w` and `Zv` the underlying set at `z`. The first is the stage over which definability is interpreted, and the second is the common bound in which the four witnesses must lie.
<!--zh-->
固定一个环境 `δ`，其中十个具名槽位都具有所要求的数码值。以 `Wv` 表示 `w` 处的底层集合，以 `Zv` 表示 `z` 处的底层集合。前者是解释可定义性的层，后者则是必须容纳四个见证的公共界。
<!--ja-->
十個の名前付きスロットが必要な数項の値をもつ環境 `δ` を固定する。`w` にある底集合を `Wv`、`z` にある底集合を `Zv` とする。前者は定義可能性を解釈する段階であり、後者は四つの証人を含まなければならない共通の上界である。
<!--/-->

<details open class="submodule-fold">
<summary class="submodule-fold-heading">
```agda
module DefInRead {k : ℕ} (w z : Fin k) (N : Fin 10 → Fin k) (body : Formula S (4 + k))
  (δ : S ^ k) (tg : Tags δ N) where
```
</summary>
<div class="submodule-fold-content">

```agda
  private
    Wv = fst (lookup w δ)
    Zv = fst (lookup z δ)
```

<!--en-->
The four witnesses are bound successively as `T`, `C`, `E`, and `d`. Since each new binder extends the front of the environment, the body is evaluated at `d ∷ E ∷ C ∷ T ∷ δ`. Thus its first four slots refer, in order, to the definable-power-set value, the environment tower, the code set, and the satisfaction table.
<!--zh-->
四个见证依次绑定为 `T`、`C`、`E` 与 `d`。由于每个新约束子都从环境前端扩展，主体在 `d ∷ E ∷ C ∷ T ∷ δ` 上求值。因此，其前四个槽位依次指向可定义幂集的取值、环境塔、码集与满足关系表。
<!--ja-->
四つの証人は `T`、`C`、`E`、`d` の順に束縛される。新しい束縛子は環境の先頭を拡張するため、本体は `d ∷ E ∷ C ∷ T ∷ δ` で評価される。したがって先頭の四つのスロットは、定義可能冪集合の値、環境の塔、符号集合、充足関係表をこの順に指す。
<!--/-->

```agda
  δ4 : (T C E d : S) → S ^ (4 + k)
  δ4 T C E d = d ∷ E ∷ C ∷ T ∷ δ
```

<!--en-->
Reading `defIn` preserves the propositional truncation around four witnesses `T`, `C`, `E`, and `d`. Its conclusion deliberately retains only that `d ∈ z`, that `d = 𝒟ₒ Wv`, and that the body holds in the extended environment. Membership of `T`, `C`, and `E` in `z`, together with the internal satisfaction and power-set proofs, is consumed while deriving this weaker statement.
<!--zh-->
读取 `defIn` 时，四个见证 `T`、`C`、`E`、`d` 外面的命题截断保持不变。其结论有意只保留 `d ∈ z`、`d = 𝒟ₒ Wv`，以及主体在扩展环境中成立。`T`、`C`、`E` 属于 `z` 的证明，以及内部的满足描述与幂集描述证明，都在导出这条较弱陈述时被消耗。
<!--ja-->
`defIn` を読むとき、四つの証人 `T`、`C`、`E`、`d` を囲む命題的切り詰めは保たれる。その結論が意図的に残すのは、`d ∈ z`、`d = 𝒟ₒ Wv`、そして拡張された環境で本体が成り立つことだけである。`T`、`C`、`E` が `z` に属する証明と、内部の充足および冪集合の記述の証明は、この弱い主張を導く途中で消費される。
<!--/-->

```agda
  defIn-out : ⟨ δ ⊨ defIn w z N body ⟩
            → ∥ Σ[ T ∈ S ] Σ[ C ∈ S ] Σ[ E ∈ S ] Σ[ d ∈ S ]
                (⟨ fst d ∈ Zv ⟩ × ((fst d ≡ 𝒟ₒ Wv) × ⟨ δ4 T C E d ⊨ body ⟩)) ∥₁
  defIn-out = rec₁ squash₁ (λ { (T , (T∈ , h1)) → rec₁ squash₁ (λ { (C , (C∈ , h2)) →
    rec₁ squash₁ (λ { (E , (E∈ , h3)) → map₁ (λ { (d , (d∈ , (hs , (hd , hb)))) →
```

<!--en-->
After the four nested truncations have exposed the witnesses, `def-sound` combines the satisfaction description `hs` with the definable-power-set description `hd`. Its conclusion is the one equality retained here, namely `d = 𝒟ₒ Wv`; the body proof is passed through unchanged.
<!--zh-->
四层嵌套截断暴露见证之后，`def-sound` 把满足描述 `hs` 与可定义幂集描述 `hd` 合并起来。这里保留的唯一等式正是其结论 `d = 𝒟ₒ Wv`；主体的证明则原样继续传递。
<!--ja-->
四重の切り詰めから証人を取り出した後、`def-sound` は充足の記述 `hs` と定義可能冪集合の記述 `hd` を組み合わせる。ここに残される唯一の等式は、その結論 `d = 𝒟ₒ Wv` であり、本体の証明はそのまま先へ渡される。
<!--/-->

```agda
      T , C , E , d , ( d∈ , ( def-sound i0 (sh 4 w) i3 i2 i1 (shN 4 N) (δ4 T C E d) (lookup w δ) refl tg hs hd
                             , hb )) })
      h3 }) h2 }) h1 })
```

<!--en-->
Conversely, proving `defIn` from semantic data requires explicit genuine witnesses. One supplies a constructible carrier `W` represented at `w`, the four sets and their memberships in `z`, their identifications with the genuine satisfaction table, code set, environment tower, and definable power set, and a proof of the body. This direction therefore assumes data that the outward reading intentionally forgets.
<!--zh-->
反过来，要从语义数据证明 `defIn`，就必须显式给出真实见证：由 `w` 表示的可构造载体 `W`、四个集合及其属于 `z` 的证明、它们分别与真实满足关系表、码集、环境塔和可定义幂集的同一视，以及主体的证明。因此，这个方向所假设的数据多于向外读取有意保留的数据。
<!--ja-->
逆に、意味論的なデータから `defIn` を示すには、真正な証人を明示的に与える必要がある。`w` で表される構成可能な台 `W`、四つの集合とそれらが `z` に属する証明、真正な充足関係表、符号集合、環境の塔、定義可能冪集合とのそれぞれの同定、そして本体の証明を与える。したがってこの向きでは、外向きの読みが意図的に忘れるデータを仮定する。
<!--/-->

```agda
  defIn-in : (W : S) → Wv ≡ fst W → (T C E d : S)
           → ⟨ fst T ∈ Zv ⟩ → ⟨ fst C ∈ Zv ⟩ → ⟨ fst E ∈ Zv ⟩ → ⟨ fst d ∈ Zv ⟩
           → fst T ≡ fst (SatGraph.pairs W) → fst C ≡ fst (AllCodes W) → fst E ≡ fst (Tower.tower W)
           → fst d ≡ 𝒟ₒ (fst W) → ⟨ δ4 T C E d ⊨ body ⟩ → ⟨ δ ⊨ defIn w z N body ⟩
  defIn-in W qw T C E d T∈ C∈ E∈ d∈ qT qC qE qd hb =
```

<!--en-->
For the inward reading, `sat-complete` first proves that the genuine satisfaction table, code set, and environment tower satisfy `satAt`. Using that proof and the supplied equality for `d`, `def-complete` proves the definable-power-set clause. The given body proof completes the conjunction, after which the four witnesses and their memberships are introduced under the nested propositional truncations.
<!--zh-->
在向内读法中，`sat-complete` 先证明真实的满足关系表、码集与环境塔满足 `satAt`。`def-complete` 再使用这一证明和给定的 `d` 的等式，证明可定义幂集子句。给定的主体证明补全合取，随后四个见证及其隶属证明被依次引入嵌套的命题截断中。
<!--ja-->
内向きの読みでは、まず `sat-complete` が、真正な充足関係表、符号集合、環境の塔が `satAt` を満たすことを示す。次に `def-complete` が、その証明と与えられた `d` の等式を使って、定義可能冪集合の節を示す。与えられた本体の証明で連言が完成し、その後、四つの証人とそれぞれの所属証明が、入れ子の命題的切り詰めの中へ順に導入される。
<!--/-->

```agda
    ∣ T , ( T∈ , ∣ C , ( C∈ , ∣ E , ( E∈ , ∣ d , ( d∈ , ( hs
      , ( def-complete i0 (sh 4 w) i3 i2 i1 (shN 4 N) (δ4 T C E d) W qw tg hs qd , hb ))) ∣₁ ) ∣₁ ) ∣₁ ) ∣₁
    where
    hs : ⟨ δ4 T C E d ⊨ satAt i3 (sh 4 w) i2 i1 (shN 4 N) ⟩
    hs = sat-complete i3 (sh 4 w) i2 i1 (shN 4 N) (δ4 T C E d) W qw qT qC qE tg
```
</div>
</details>

<!--en-->
The predicate `Supply` says that, for an ordinal `c`, all four witnesses needed by `defIn` already lie inside the common bound: the satisfaction graph, code set, and environment tower of the stage `Lset c`, together with the next stage `Lset (sucV c)`.
<!--zh-->
谓词 `Supply` 说：对序数 `c`，`defIn` 所需的四个见证都已在公共界之内，即层 `Lset c` 的满足图、码集与环境塔，以及下一层 `Lset (sucV c)`。
<!--ja-->
述語 `Supply` は、`c` が順序数なら、`defIn` が必要とする四つの証人がすでに共通の上界の中にあることを述べる。その四つとは、段階 `Lset c` の充足グラフ、符号集合、環境の塔、および次の段階 `Lset (sucV c)` である。
<!--/-->

```agda
Supply : (Zv : V ℓ) (c : V ℓ) → IsOrd c → Type (ℓ-suc ℓ)
Supply Zv c oc =
    ⟨ fst (SatGraph.pairs (LsetS c oc)) ∈ Zv ⟩
  × ( ⟨ fst (AllCodes (LsetS c oc)) ∈ Zv ⟩
  × ( ⟨ fst (Tower.tower (LsetS c oc)) ∈ Zv ⟩
```

<!--en-->
The fourth component is the next stage, which is what the successor step of the approximation needs.
<!--zh-->
第四分量是下一层，正是逼近的后继一步所需的。
<!--ja-->
第四の成分が次の段階であり、近似の後続の一歩に必要なものである。
<!--/-->

```agda
  × ⟨ Lset (sucV c) ∈ Zv ⟩ ))
```

<!--en-->
Now fix one proposed hierarchy step in an environment `γ`. Write `Vv` for the proposed result, `Bv` for the set of earlier indices, and `Fv` for the underlying candidate table. The question is whether the two bounded inclusions force `Vv` to equal `Lset Bv` once the relevant rows of `Fv` are known to be correct and present.
<!--zh-->
现固定环境 `γ` 中一个拟议的层级步骤。以 `Vv` 表示拟议结果，以 `Bv` 表示此前索引组成的集合，以 `Fv` 表示候选表的底层集合。要问的是：一旦知道 `Fv` 中相关表行取值正确且确实存在，这两个有界包含是否迫使 `Vv` 等于 `Lset Bv`。
<!--ja-->
環境 `γ` における一つの候補となる階層の段階を固定する。候補の結果を `Vv`、それ以前の添字の集合を `Bv`、候補表の底集合を `Fv` と書く。問うのは、`Fv` の関係する行が正しく、かつ存在すると分かったとき、二つの有界な包含から `Vv = Lset Bv` が強制されるかどうかである。
<!--/-->

<details open class="submodule-fold">
<summary class="submodule-fold-heading">
```agda
module StepRead {m : ℕ} (v b f z : Fin m) (N : Fin 10 → Fin m) (γ : S ^ m) (tg : Tags γ N) where
```
</summary>
<div class="submodule-fold-content">

```agda
  private
    Vv = fst (lookup v γ)
    Bv = fst (lookup b γ)
    Fv = fst (lookup f γ)
```

<!--en-->
Let `Zv` denote the underlying common bound. It controls where the auxiliary satisfaction, code, tower, and definable-power-set witnesses may be found. The equality sought from the step does not mention `Zv`; the bound enables the description without becoming part of the resulting stage value.
<!--zh-->
以 `Zv` 表示公共界的底层集合。它控制可在何处找到辅助的满足关系、码、环境塔与可定义幂集见证。单步所求的等式本身不提及 `Zv`；这个界使描述能够成立，却不成为所得层取值的一部分。
<!--ja-->
共通の上界の底集合を `Zv` と書く。これは、補助的な充足関係、符号、環境の塔、定義可能冪集合の証人をどこで見つけられるかを制御する。一段階から得たい等式には `Zv` は現れない。この上界は記述を可能にするが、得られる段階の値の一部にはならない。
<!--/-->

```agda
    Zv = fst (lookup z γ)
```

<!--en-->
In the inward body, `d` is the definable power set recognized by `defIn`, and `x` is the member introduced by the outer bounded universal over `v`. The atomic body says `x ∈ d`. Once the recorded value `w` is identified with `Lset c`, this becomes membership in `𝒟ₒ (Lset c)` for some `c ∈ b`.
<!--zh-->
在内向主体中，`d` 是由 `defIn` 识别的可定义幂集，而 `x` 是外层对 `v` 的有界全称量词引入的成员。原子主体陈述 `x ∈ d`。一旦把记录值 `w` 认同为 `Lset c`，这就成为对某个 `c ∈ b` 的 `𝒟ₒ (Lset c)` 的隶属。
<!--ja-->
内向きの本体では、`d` は `defIn` が認識する定義可能冪集合であり、`x` は外側の `v` 上の有界全称量化子が導入した要素である。原子論理式の本体は `x ∈ d` を述べる。記録された値 `w` を `Lset c` と同定すれば、これはある `c ∈ b` に対する `𝒟ₒ (Lset c)` への所属になる。
<!--/-->

```agda
    intoBody : Formula S (5 + m)
    intoBody = defIn i0 (sh 5 z) (shN 5 N) (var i8 ∈̇ var i0)
```

<!--en-->
The `over` body is a definable-power-set description whose inner formula says that every member of the described set belongs to the proposed next value. This gives the reverse inclusion needed for the union equality.
<!--zh-->
`over` 主体是一条可定义幂集描述，其内层公式断言，被描述集合的每个成员都属于拟议的下一取值。这给出并集等式所需的反向包含。
<!--ja-->
`over` の本体は定義可能冪集合の記述であり、その内側の論理式は、記述された集合のすべての要素が候補となる次の値に属することを述べる。これは合併の等式に必要な逆向きの包含を与える。
<!--/-->

```agda
    overBody : Formula S (4 + m)
    overBody = defIn i0 (sh 4 z) (shN 4 N) (∀̇∈ (var i0) (var i0 ∈̇ var (sh 9 v)))
```

<!--en-->
The read lemma for one step assumes separately that every pair row below `Bv` has the correct value (`Values`) and that every index below `Bv` has its canonical row (`Entries`). Under precisely these two hypotheses, the two halves of `stepAt` give opposite membership implications, and extensionality yields `Vv = Lset Bv`. These assumptions control the relevant pair rows only; they do not exclude unrelated members of the candidate table.
<!--zh-->
单步读引理另行假设：`Bv` 以下每条有序对表行都具有正确取值 (`Values`)，并且 `Bv` 以下每个索引都有其正準表行 (`Entries`)。恰在这两个假设下，`stepAt` 的两半给出相反方向的隶属蕴含，外延性遂得到 `Vv = Lset Bv`。这些假设只约束相关的有序对表行，并不排除候选表中无关的成员。
<!--ja-->
一段階の読み補題は、`Bv` より下の各対の行が正しい値をもつこと (`Values`) と、`Bv` より下の各添字に正準な行があること (`Entries`) を別々に仮定する。ちょうどこの二つの仮定のもとで、`stepAt` の二つの部分が反対向きの所属の含意を与え、外延性から `Vv = Lset Bv` が得られる。これらの仮定が制約するのは関係する対の行だけであり、候補表の無関係な要素を排除するものではない。
<!--/-->

```agda
  step-out : ⟨ γ ⊨ stepAt v b f z N ⟩ → Values (lookup f γ) Bv → Entries (lookup f γ) Bv → Vv ≡ Lset Bv
  step-out (hi , ho) vals ents = extensionalV (λ x → ⇔toPath (fwd x) (bwd x))
    where
    fwd : (x : V ℓ) → ⟨ x ∈ Vv ⟩ → ⟨ x ∈ Lset Bv ⟩
    fwd x x∈ = rec₁ (snd (x ∈ Lset Bv)) (λ { (c , (c∈ , h1)) → rec₁ (snd (x ∈ Lset Bv))
```

<!--en-->
For the forward inclusion, `intoAt` supplies a stage index `c ∈ Bv`, a pair row `(c,w)` in the table, and a definable-power-set value `d` containing `x`. The `Values` hypothesis identifies `w` with `Lset c`, so `d = 𝒟ₒ (Lset c)`. The inward stage rule `Lset-in` then carries `x` from that contribution into `Lset Bv`.
<!--zh-->
对正向包含，`intoAt` 给出层索引 `c ∈ Bv`、表中的有序对表行 `(c,w)`，以及包含 `x` 的可定义幂集值 `d`。假设 `Values` 把 `w` 认同为 `Lset c`，故 `d = 𝒟ₒ (Lset c)`；层的向内规则 `Lset-in` 随即把 `x` 从这一份贡献送入 `Lset Bv`。
<!--ja-->
前向きの包含では、`intoAt` が段階の添字 `c ∈ Bv`、表の対の行 `(c,w)`、そして `x` を含む定義可能冪集合の値 `d` を与える。仮定 `Values` は `w` を `Lset c` と同定するので、`d = 𝒟ₒ (Lset c)` である。段階への内向きの規則 `Lset-in` が、この寄与から `x` を `Lset Bv` へ運ぶ。
<!--/-->

```agda
      (λ { (q , (q∈ , h2)) → rec₁ (snd (x ∈ Lset Bv)) (λ { (w , s , (eq , h3)) →
        rec₁ (snd (x ∈ Lset Bv)) (λ { (T , C , E , d , (d∈ , (qd , hx))) →
          Lset-in Bv (fst c) x c∈
            (subst (λ u → ⟨ x ∈ u ⟩)
              (qd ∙ cong 𝒟ₒ (vals c w c∈ (subst (λ u → ⟨ u ∈ Fv ⟩) eq q∈))) hx) })
```

<!--en-->
The nested existential readers preserve truncation at every stage. First `sndEx-out` recovers merely a second component `w` from the pair-shaped table entry; then `defIn-out` recovers merely the auxiliary data and the equality identifying `d` with the definable power set of `w`. Each truncation is eliminated directly into the membership proposition `x ∈ Lset Bv`.
<!--zh-->
嵌套存在式的各层读取都保持命题截断。`sndEx-out` 先从有序对形的表项中仅仅恢复第二分量 `w`，`defIn-out` 再仅仅恢复辅助数据，以及把 `d` 认同为 `w` 的可定义幂集的等式。每一层截断都直接消去到隶属命题 `x ∈ Lset Bv`。
<!--ja-->
入れ子の存在形を読む各段階で、命題的切り詰めは保たれる。まず `sndEx-out` が、対の形をした表の項目から第二成分 `w` が単に存在することを復元し、次に `defIn-out` が、補助データと、`d` を `w` の定義可能冪集合と同定する等式が単に存在することを復元する。各切り詰めは、所属命題 `x ∈ Lset Bv` へ直接除去される。
<!--/-->

```agda
        (DefInRead.defIn-out i0 (sh 5 z) (shN 5 N) (var i8 ∈̇ var i0) (w ∷ s ∷ q ∷ c ∷ xS ∷ γ) tg h3) })
        (sndEx-out i0 i1 intoBody (q ∷ c ∷ xS ∷ γ) h2) })
      h1 })
      (hi xS x∈)
      where
```

<!--en-->
The proof begins with an ambient member `x ∈ Vv`, but the formula is interpreted over the constructible carrier `S`. The operation `down` uses that membership to present `x` as a carrier element `xS`; placing `xS` at the front of the environment makes the newly bound slot denote the same underlying set `x`.
<!--zh-->
证明从外围成员 `x ∈ Vv` 出发，但公式是在可构造载体 `S` 上解释的。运算 `down` 利用这一隶属证明把 `x` 呈现为载体元素 `xS`；再把 `xS` 放到环境前端，便使新约束的槽位表示同一个底层集合 `x`。
<!--ja-->
証明は周囲の要素 `x ∈ Vv` から始まるが、論理式は構成可能な台 `S` の上で解釈される。演算 `down` はこの所属証明を使って `x` を台の要素 `xS` として提示する。`xS` を環境の先頭に置くと、新しく束縛されたスロットは同じ底集合 `x` を表す。
<!--/-->

```agda
      xS : S
      xS = down (lookup v γ) x x∈
```

<!--en-->
The backward direction of `step-out` sends a member of the genuine stage `Lset Bv` into the proposed value `Vv`. It eliminates the truncated stage decomposition of `Lset Bv`, reducing the claim to an earlier stage `δ` whose definable power set contains `x`.
<!--zh-->
`step-out` 的反向包含把真实层 `Lset Bv` 的成员送入拟议取值 `Vv`。它消去 `Lset Bv` 的截断层分解，把目标化归为更早层 `δ`，其中 `x` 属于该层的可定义幂集。
<!--ja-->
`step-out` の逆向きの包含は、実際の段階 `Lset Bv` の要素を候補の値 `Vv` に入れる。これは `Lset Bv` の切り詰められた段階分解を消去し、`x` がその定義可能冪集合に属するような、より前の段階 `δ` についての主張へ帰着させる。
<!--/-->

```agda
    bwd : (x : V ℓ) → ⟨ x ∈ Lset Bv ⟩ → ⟨ x ∈ Vv ⟩
    bwd x x∈ = rec₁ (snd (x ∈ Vv)) put (Lset-out Bv x x∈)
      where
      put : Σ[ δ ∈ V ℓ ] (⟨ δ ∈ Bv ⟩ × ⟨ x ∈ 𝒟ₒ (Lset δ) ⟩) → ⟨ x ∈ Vv ⟩
      put (δ , (δ∈ , xD)) = rec₁ (snd (x ∈ Vv))
```

<!--en-->
Once `Lset-out` has exhibited an earlier index `δ`, completeness supplies the canonical table entry `(δ, Lset δ)`. The `over` clause applies to this entry, and `defIn-out` identifies its bounded set `d` with `𝒟ₒ (Lset δ)`. Its universal body therefore sends the given `x` into the proposed value `Vv`. This direction uses the canonical entry supplied by `Entries`; it does not need a separate appeal to `Values`.
<!--zh-->
`Lset-out` 给出更早的索引 `δ` 后，完备性提供典范表条目 `(δ, Lset δ)`。`over` 子句施用于这条目，`defIn-out` 再把其中的有界集合 `d` 同认于 `𝒟ₒ (Lset δ)`。因此，其全称体把给定的 `x` 放入拟议取值 `Vv`。这个方向使用 `Entries` 提供的典范条目，无须另行诉诸 `Values`。
<!--ja-->
`Lset-out` がより前の添字 `δ` を示すと、完全性が正準な表の項目 `(δ, Lset δ)` を与える。`over` の節をこの項目に適用し、さらに `defIn-out` がそこで有界化された集合 `d` を `𝒟ₒ (Lset δ)` と同一視する。したがって、その全称な本体は与えられた `x` を候補の値 `Vv` に入れる。この向きで使うのは `Entries` が与える正準な項目であり、`Values` への別の訴えは要らない。
<!--/-->

```agda
        (λ { (T , C , E , d , (d∈ , (qd , hsub))) →
          hsub (down d x (subst (λ u → ⟨ x ∈ u ⟩) (sym qd) xD)) (subst (λ u → ⟨ x ∈ u ⟩) (sym qd) xD) })
        (DefInRead.defIn-out i0 (sh 4 z) (shN 4 N) (∀̇∈ (var i0) (var i0 ∈̇ var (sh 9 v)))
          (w ∷ container q c w refl .fst ∷ q ∷ c ∷ γ) tg
          (useSnd i0 (q ∷ c ∷ γ) c w refl overBody i1 refl (ho c δ∈ q (ents c δ∈))))
```

<!--en-->
The two named objects are the coded argument and the coded pair: both are presented by descending along their membership proofs into carrier elements.
<!--zh-->
两个被命名的对象是编码实参与编码对：二者都沿其隶属证明下降而呈现为载体元素。
<!--ja-->
名づけられる二つの対象は、符号化された引数と符号化された対である。どちらも、所属の証明を下降して台の要素として提示される。
<!--/-->

```agda
        where
        c : S
        c = down (lookup b γ) δ δ∈
        q : S
        q = down (lookup f γ) (pr δ (Lset δ)) (ents c δ∈)
```

<!--en-->
The value `w` of the row is read from the pair presentation, and is the component consumed by the satisfaction of the body.
<!--zh-->
该行的取值 `w` 从对呈现中读取，正是体的满足所消耗的分量。
<!--ja-->
行の値 `w` は、対の提示から読まれ、本体の充足が消費する成分である。
<!--/-->

```agda
        w : S
        w = sndS q δ (Lset δ) refl
```

<!--en-->
The inward direction of the step clause requires five hypotheses: ordinality of the bound, the identification of the proposed value with the stage at the bound, correctness and completeness of the table at the bound, and a supply function placing every auxiliary witness for each member of the bound inside the witness bound. The proof splits into the two conjuncts.
<!--zh-->
步进子句的向内方向需要五条假设：界的序数性、拟议取值与界处层的等同、表在界处的正确性与完备性，以及把界的每个成员所需的辅助见证放进见证界的供给函数。证明分为两个合取项。
<!--ja-->
ステップの条項の内向きの方向には、五つの仮定が要る。界の順序数性、提案された値と界での段階の同定、界での表の正しさと完備さ、そして界の各要素のための補助の証人を証人の界の中に置く供給関数である。証明は二つの連言項に分かれる。
<!--/-->

```agda
  step-in : (ob : IsOrd Bv) → Vv ≡ Lset Bv → Values (lookup f γ) Bv → Entries (lookup f γ) Bv
          → ((c : V ℓ) (oc : IsOrd c) → ⟨ c ∈ Bv ⟩ → Supply Zv c oc)
          → ⟨ γ ⊨ stepAt v b f z N ⟩
  step-in ob vq vals ents sup = into , over
    where
```

<!--en-->
The `into` conjunct reads outward from a member `x` of the proposed value: the truncated decomposition of the stage at the bound names an earlier ordinal and a definable-power-set membership, which the existence introduction fills into the two bounded quantifiers.
<!--zh-->
`into` 合取项从拟议取值的成员 `x` 向外读取：界处层的截断分解名指更早序数与可定义幂集隶属，存在引入把它们填入两个有界量词。
<!--ja-->
`into` の連言項は、提案された値の要素 `x` から外向きに読まれる。界での段階の切り詰められた分解が、より前の順序数と定義可能冪集合への所属を名指し、存在の導入がそれを二つの有界量化子に満たす。
<!--/-->

```agda
    into : ⟨ γ ⊨ intoAt v b f z N ⟩
    into x x∈ = rec₁ squash₁ put (Lset-out Bv (fst x) (subst (λ u → ⟨ fst x ∈ u ⟩) vq x∈))
      where
      put : Σ[ δ ∈ V ℓ ] (⟨ δ ∈ Bv ⟩ × ⟨ fst x ∈ 𝒟ₒ (Lset δ) ⟩)
          → ⟨ (x ∷ γ) ⊨ ∃̇∈ (var (sh 1 b)) (∃̇∈ (var (sh 2 f)) (sndEx i0 i1 intoBody)) ⟩
```

<!--en-->
The nested bounded existentials are filled without extracting data from propositional truncation. The proof presents `δ` as the carrier element `c`, uses `Entries` to present the canonical pair as `q`, and supplies the pair decomposition through `fillSnd`; the remaining body is `hb`. Each constructor retains the truncation built into `∃[]-syntax`, which is appropriate because satisfaction is a proposition.
<!--zh-->
这些嵌套有界存在量词的填充并不从命题截断中取出数据。证明把 `δ` 呈现为载体元素 `c`，用 `Entries` 把典范对呈现为 `q`，再由 `fillSnd` 提供有序对分解；余下的公式体就是 `hb`。每次构造都保留 `∃[]-syntax` 内含的命题截断，因为满足关系本身是命题。
<!--ja-->
入れ子になった有界存在量化子は、命題的切り詰めからデータを取り出すことなく満たされる。証明は `δ` を台の要素 `c` として提示し、`Entries` によって正準な対を `q` として提示し、`fillSnd` で対の分解を与える。残る本体が `hb` である。充足は命題なので、各構成子は `∃[]-syntax` に組み込まれた命題的切り詰めを保つ。
<!--/-->

```agda
      put (δ , (δ∈ , xD)) =
        ∣ c , ( δ∈ , ∣ q , ( ents c δ∈ , fillSnd i0 (q ∷ c ∷ x ∷ γ) c w refl intoBody hb i1 refl ) ∣₁ ) ∣₁
        where
        oδ : IsOrd δ
        oδ = mem-ord {A = Bv} ob δ δ∈
```

<!--en-->
The three carrier elements have different sources. The membership `δ ∈ Bv` presents the earlier index as `c`; membership of the canonical pair in the table presents that pair as `q`; and ordinality of `δ` lets `LsetS` present the stage `Lset δ` as `w`. Keeping these sources distinct matters when the bounded witnesses are assembled.
<!--zh-->
三个载体元素有不同的来源。隶属 `δ ∈ Bv` 把更早的索引呈现为 `c`；典范对属于表的证明把该对呈现为 `q`；而 `δ` 的序数性使 `LsetS` 能把层 `Lset δ` 呈现为 `w`。组装有界见证时，必须区分这三种来源。
<!--ja-->
三つの台の要素は、それぞれ異なる根拠から得られる。所属 `δ ∈ Bv` はより前の添字を `c` として提示し、正準な対が表に属するという証明はその対を `q` として提示し、`δ` の順序数性によって `LsetS` は段階 `Lset δ` を `w` として提示できる。有界な証人を組み立てる際には、これらの由来を区別することが大切である。
<!--/-->

```agda
        c : S
        c = down (lookup b γ) δ δ∈
        q : S
        q = down (lookup f γ) (pr δ (Lset δ)) (ents c δ∈)
        w : S
```

<!--en-->
Here `w` is the genuine stage `Lset δ` in the constructible carrier. Applying the supply hypothesis at `δ` gives membership evidence in `Zv` for its satisfaction table, code set, environment tower, and successor stage. With those four bounds and their defining equalities, `defIn-in` reduces the remaining obligation to the mathematical fact that `x ∈ 𝒟ₒ (Lset δ)`.
<!--zh-->
这里的 `w` 是可构造载体中的真实层 `Lset δ`。在 `δ` 处应用供给假设，得到满足关系表、码集、环境塔与后继层都属于 `Zv` 的证明。有了这四个界及其定义等式，`defIn-in` 把余下义务归结为数学事实 `x ∈ 𝒟ₒ (Lset δ)`。
<!--ja-->
ここで `w` は構成可能な台における実際の段階 `Lset δ` である。供給の仮定を `δ` に適用すると、その充足関係表、符号集合、環境の塔、後継段階がいずれも `Zv` に属するという証明が得られる。この四つの界とそれらを同定する等式により、`defIn-in` は残る課題を数学的事実 `x ∈ 𝒟ₒ (Lset δ)` に帰着させる。
<!--/-->

```agda
        w = LsetS δ oδ
        s = sup δ oδ δ∈
        hb : ⟨ (w ∷ container q c w refl .fst ∷ q ∷ c ∷ x ∷ γ) ⊨ intoBody ⟩
        hb = DefInRead.defIn-in i0 (sh 5 z) (shN 5 N) (var i8 ∈̇ var i0)
               (w ∷ container q c w refl .fst ∷ q ∷ c ∷ x ∷ γ) tg w refl
```

<!--en-->
The four bounded objects are the genuine satisfaction table, code set, environment tower, and `Lset (sucV δ)`. The supply hypothesis proves that each lies in `Zv`, while reflexivity identifies the first three with the structures expected by the descriptions. Finally `Lset-suc δ` identifies the fourth with `𝒟ₒ (Lset δ)`, so the original membership of `x` can be transported into the formula body.
<!--zh-->
四个有界对象分别是真实的满足关系表、码集、环境塔与 `Lset (sucV δ)`。供给假设证明它们都属于 `Zv`，前三个对象则由自反等式同描述所要求的结构对齐。最后，`Lset-suc δ` 把第四个对象同认于 `𝒟ₒ (Lset δ)`，于是 `x` 原有的隶属可被运输到公式体中。
<!--ja-->
四つの有界な対象は、実際の充足関係表、符号集合、環境の塔、そして `Lset (sucV δ)` である。供給の仮定はそれぞれが `Zv` に属することを証明し、最初の三つは反射律によって記述が要求する構造と一致する。最後に `Lset-suc δ` が四つ目を `𝒟ₒ (Lset δ)` と同一視するので、もとの `x` の所属を論理式の本体へ移せる。
<!--/-->

```agda
               (SatGraph.pairs w) (AllCodes w) (Tower.tower w) (LsetS (sucV δ) (suc-ord oδ))
               (s .fst) (s .snd .fst) (s .snd .snd .fst) (s .snd .snd .snd) refl refl refl (Lset-suc δ)
               (subst (λ u → ⟨ fst x ∈ u ⟩) (sym (Lset-suc δ)) xD)
```

<!--en-->
For the `over` conjunct, fix `c ∈ Bv`, a member `q` of the table, and a presentation of `q` as the pair `(c,w)`. Correctness then identifies `w` with `Lset c`. The remaining task is uniform in `y`: every `y ∈ 𝒟ₒ w` must belong to the proposed value `Vv`. This is the second inclusion needed to identify the proposed value with the stage at `Bv`.
<!--zh-->
证明 `over` 合取项时，固定 `c ∈ Bv`、表的成员 `q`，以及把 `q` 呈现为有序对 `(c,w)` 的方式。正确性随即把 `w` 同认于 `Lset c`。余下目标对 `y` 一致：每个 `y ∈ 𝒟ₒ w` 都必须属于拟议取值 `Vv`。这正是把拟议取值同认于 `Bv` 处层所需的第二个包含关系。
<!--ja-->
`over` の連言を示すため、`c ∈ Bv`、表の要素 `q`、そして `q` を対 `(c,w)` として提示する仕方を固定する。すると正しさにより `w` は `Lset c` と同一視される。残る目標は `y` について一様である。すべての `y ∈ 𝒟ₒ w` が候補の値 `Vv` に属さなければならない。これは候補の値を `Bv` における段階と同一視するために必要な第二の包含である。
<!--/-->

```agda
    over : ⟨ γ ⊨ overAt v b f z N ⟩
    over c c∈ q q∈ = sndAll-in i0 i1 overBody (q ∷ c ∷ γ) (λ w s s∈ w∈ e →
      let wq : fst w ≡ Lset (fst c)
          wq = vals c w c∈ (subst (λ u → ⟨ u ∈ Fv ⟩) e q∈)
          oc : IsOrd (fst c)
```

<!--en-->
Ordinality of `c` is inherited from the bound; the stage is presented as a carrier element; and the supply function produces the four witnesses at `c`.
<!--zh-->
`c` 的序数性承继自界；层被呈现为载体元素；供给函数在 `c` 处产出四个见证。
<!--ja-->
`c` の順序数性は界から受け継がれ、段階は台の要素として提示され、供給の関数が `c` で四つの証人を作る。
<!--/-->

```agda
          oc = mem-ord {A = Bv} ob (fst c) c∈
          W : S
          W = LsetS (fst c) oc
          s' = sup (fst c) oc c∈
      in DefInRead.defIn-in i0 (sh 4 z) (shN 4 N) (∀̇∈ (var i0) (var i0 ∈̇ var (sh 9 v)))
```

<!--en-->
The supply at `c` bounds the genuine satisfaction table, code set, environment tower, and successor stage, so `defIn-in` can establish the definable-power-set description. If `y` belongs to the set described there, `Lset-suc c` turns this into membership in `𝒟ₒ (Lset c)`, and `Lset-in` uses `c ∈ Bv` to place `y` in `Lset Bv`. Transport along `Vv ≡ Lset Bv` then yields the required membership in the proposed value.
<!--zh-->
`c` 处的供给把真实的满足关系表、码集、环境塔与后继层都界定在 `Zv` 内，因此 `defIn-in` 可以建立可定义幂集描述。若 `y` 属于那里描述的集合，`Lset-suc c` 先把它化为 `y ∈ 𝒟ₒ (Lset c)`，再由 `c ∈ Bv` 通过 `Lset-in` 得到 `y ∈ Lset Bv`。最后沿 `Vv ≡ Lset Bv` 运输，便得到 `y` 属于拟议取值。
<!--ja-->
`c` における供給は、実際の充足関係表、符号集合、環境の塔、後継段階をすべて `Zv` の中に有界化するので、`defIn-in` は定義可能冪集合の記述を示せる。`y` がそこで記述された集合に属するとき、`Lset-suc c` によりこれは `y ∈ 𝒟ₒ (Lset c)` となり、さらに `c ∈ Bv` と `Lset-in` によって `y ∈ Lset Bv` が得られる。最後に `Vv ≡ Lset Bv` に沿って移せば、候補の値への所属が従う。
<!--/-->

```agda
           (w ∷ s ∷ q ∷ c ∷ γ) tg W wq
           (SatGraph.pairs W) (AllCodes W) (Tower.tower W) (LsetS (sucV (fst c)) (suc-ord oc))
           (s' .fst) (s' .snd .fst) (s' .snd .snd .fst) (s' .snd .snd .snd) refl refl refl (Lset-suc (fst c))
           (λ y y∈d → subst (λ u → ⟨ fst y ∈ u ⟩) (sym vq)
             (Lset-in Bv (fst c) (fst y) c∈ (subst (λ u → ⟨ fst y ∈ u ⟩) (Lset-suc (fst c)) y∈d))))
```
</div>
</details>

<!--en-->
The approximation reader is parameterized by the table, the bound, the witness bound, the tag map and the environment. The three underlying sets are named once.
<!--zh-->
逼近读取器以表、界、见证界、标签映射与环境为参数。三个底层集合一次性命名。
<!--ja-->
近似の読み手は、表・界・証人の界・タグの対応・環境をパラメータとする。三つの基礎の集合が一度だけ名づけられる。
<!--/-->

<details open class="submodule-fold">
<summary class="submodule-fold-heading">
```agda
module ApproxRead {m : ℕ} (f b z : Fin m) (N : Fin 10 → Fin m) (γ : S ^ m) (tg : Tags γ N) where
```
</summary>
<div class="submodule-fold-content">

```agda
  private
    Fv = fst (lookup f γ)
    Bv = fst (lookup b γ)
    Zv = fst (lookup z γ)
```

<!--en-->
The step body is the step clause at the four shifted slots.
<!--zh-->
步进体是在四个平移槽位处的步进子句。
<!--ja-->
ステップの本体は、四つずらした枠でのステップの条項である。
<!--/-->

```agda
    stepBody : Formula S (4 + m)
    stepBody = stepAt i0 i1 (sh 4 f) (sh 4 z) (shN 4 N)
```

<!--en-->
The outward reading of the approximation clause produces correctness and completeness of the table at the bound. The predicate `P` records what must be proved about each argument: that its recorded value is the stage at the argument. Note carefully what is and is not claimed: the result is exactly `Values` and `Entries`; it does not say that the table contains no non-pair members or no entries whose first component lies outside the bound.
<!--zh-->
逼近子句的向外读法产出表在界处的正确性与完备性。谓词 `P` 记录对每个实参须证之事：其被记录取值是该实参处的层。请仔细注意所证与所未证：结果恰为 `Values` 与 `Entries`；它不说表中没有非对成员、也没有第一分量落在界外的条目。
<!--ja-->
近似の条項の外向きの読み出しは、界での表の正しさと完備さを作る。述語 `P` は、それぞれの入力について証明すべきことを記録する。記録された値がその入力での段階であること。結果が正確に `Values` と `Entries` であることに注意してほしい。表が対でない要素や、界の外を第一成分とする項目を含まないとは述べていない。
<!--/-->

```agda
  approx-out : ⟨ γ ⊨ approxAt f b z N ⟩ → IsOrd Bv → Values (lookup f γ) Bv × Entries (lookup f γ) Bv
  approx-out (hd , hs) ob = vals , ents
    where
    P : V ℓ → Type (ℓ-suc ℓ)
    P c = ⟨ c ∈ Bv ⟩ → (w : S) → ⟨ pr c (fst w) ∈ Fv ⟩ → fst w ≡ Lset c
```

<!--en-->
Coverage says that for each `c ∈ Bv` there merely exists a table member that presents a pair with first component `c`. Reading that pair exposes a value `w` and maps the original membership proof to the canonical pair notation `pr c w`. The result remains propositionally truncated, so `entryOf` supplies existence for later propositional reasoning without choosing a value globally.
<!--zh-->
覆盖子句说：对每个 `c ∈ Bv`，仅命题截断地存在一个表成员，它呈现为第一分量是 `c` 的有序对。读取这个对会显出取值 `w`，并把原隶属证明运输到典范记号 `pr c w` 上。结果仍受命题截断，因此 `entryOf` 只为后续命题推理提供存在性，并不在全局选出一个取值。
<!--ja-->
被覆の節は、各 `c ∈ Bv` に対して、第一成分が `c` である対を提示する表の要素が命題的に切り詰められた意味で存在すると述べる。その対を読むと値 `w` が現れ、もとの所属の証明は正準な記法 `pr c w` へ移される。結果は命題的に切り詰められたままなので、`entryOf` は後の命題的推論に存在を与えるが、値を大域的に選ぶことはない。
<!--/-->

```agda
    entryOf : (c : S) → ⟨ fst c ∈ Bv ⟩ → ∥ Σ[ w ∈ S ] ⟨ pr (fst c) (fst w) ∈ Fv ⟩ ∥₁
    entryOf c c∈ = rec₁ squash₁
      (λ { (q , (q∈ , h)) → map₁ (λ { (w , s , (e , _)) → w , subst (λ u → ⟨ u ∈ Fv ⟩) e q∈ })
                              (sndEx-out i0 i1 ⊤̇ (q ∷ c ∷ γ) h) })
      (hd c c∈)
```

<!--en-->
The induction step validates an arbitrary recorded pair `(c,w)` with `c ∈ Bv`. Its membership proof lets the second approximation clause supply `stepAt w c`; the induction hypothesis gives correctness at every argument below `c`, and coverage will give the matching canonical entries there. `StepRead.step-out` can then conclude that the recorded value is exactly `Lset c`.
<!--zh-->
归纳步验证任意一条满足 `c ∈ Bv` 的被记录对 `(c,w)`。它的隶属证明使逼近的第二子句给出 `stepAt w c`；归纳假设提供 `c` 以下每个实参处的正确性，覆盖子句则将在这些位置提供相应的典范条目。于是 `StepRead.step-out` 可断定，被记录取值恰为 `Lset c`。
<!--ja-->
帰納段階では、`c ∈ Bv` を満たす任意の記録された対 `(c,w)` を検証する。その所属の証明から近似の第二の節が `stepAt w c` を与え、帰納の仮定が `c` より下の各入力での正しさを与える。さらに被覆の節がそこで対応する正準な項目を与える。したがって `StepRead.step-out` は、記録された値がちょうど `Lset c` であると結論できる。
<!--/-->

```agda
    step : (c : V ℓ) → ((y : V ℓ) → ⟨ y ∈ c ⟩ → P y) → P c
    step c IH c∈ w rec =
      StepRead.step-out i0 i1 (sh 4 f) (sh 4 z) (shN 4 N) env tg
        (useBoth i0 (q ∷ γ) cS w refl stepBody (hs q rec)) vals' ents'
      where
```

<!--en-->
The proof now presents the relevant sets inside the constructible carrier. The membership `c ∈ Bv` yields the carrier element `cS`, and the assumed membership of `pr c (fst w)` in the table yields `q`. The value `w` is already a carrier element supplied to the induction predicate; the next environment places these three presentations in the slots expected by the step formula.
<!--zh-->
证明现在把有关集合呈现在可构造载体中。隶属 `c ∈ Bv` 给出载体元素 `cS`，而 `pr c (fst w)` 属于表的假设给出 `q`。取值 `w` 已经是归纳谓词所接收的载体元素；接下来的环境把这三个呈现放入步进公式所要求的槽位。
<!--ja-->
ここで関係する集合を構成可能な台の中に提示する。所属 `c ∈ Bv` から台の要素 `cS` が得られ、`pr c (fst w)` が表に属するという仮定から `q` が得られる。値 `w` はすでに帰納述語へ渡された台の要素である。次の環境は、この三つの提示をステップの論理式が要求する枠に置く。
<!--/-->

```agda
      cS : S
      cS = down (lookup b γ) c c∈
      q : S
      q = down (lookup f γ) (pr c (fst w)) rec
      env : S ^ (4 + m)
```

<!--en-->
The extended environment assembles the four slots for the step reading. Ordinality of the bound restricts smaller arguments to below the bound, and the correctness reading at smaller arguments is the restriction of the induction hypothesis.
<!--zh-->
扩展环境为步进读法装配四个槽位。界的序数性把更小的实参限制到界以下，而更小实参处的正确性读取即归纳假设的限制。
<!--ja-->
拡張された環境は、ステップの読み出しのための四つの枠を組み立てる。界の順序数性がより小さい入力を界の下に制限し、より小さい入力での正しさの読み出しは、帰納の仮定の制限である。
<!--/-->

```agda
      env = w ∷ cS ∷ container q cS w refl .fst ∷ q ∷ γ
      in' : (y : S) → ⟨ fst y ∈ c ⟩ → ⟨ fst y ∈ Bv ⟩
      in' y y∈ = ob .fst {x = c} {y = fst y} y∈ c∈
      vals' : Values (lookup f γ) c
      vals' y w' y∈ rec' = IH (fst y) y∈ (in' y y∈) w' rec'
```

<!--en-->
Completeness at smaller arguments is recovered by the same restriction: for each smaller argument, the truncated entry is consumed, and the value equation from the induction hypothesis transports the canonical entry into place.
<!--zh-->
更小实参处的完备性以同一限制恢复：对每个更小实参，消耗其截断条目，而归纳假设的取值等式把典范条目运到位。
<!--ja-->
より小さい入力での完備さも同じ制限で復元される。より小さい入力ごとに、切り詰められた項目が消費され、帰納の仮定の値の等式が、正準な項目を所定の位置へ運ぶ。
<!--/-->

```agda
      ents' : Entries (lookup f γ) c
      ents' y y∈ = rec₁ (snd (pr (fst y) (Lset (fst y)) ∈ Fv))
        (λ { (w' , rec') → subst (λ u → ⟨ pr (fst y) u ∈ Fv ⟩) (IH (fst y) y∈ (in' y y∈) w' rec') rec' })
        (entryOf y (in' y y∈))
```

<!--en-->
Correctness below `Bv` is obtained by ambient membership induction on the underlying argument `c`. The predicate `P c` is conditional on `c ∈ Bv`; this membership both restricts the theorem to the required bound and, through ordinality of `Bv`, makes every smaller argument eligible for the induction hypothesis. Applying the induction result to an arbitrary recorded value gives `Values`.
<!--zh-->
`Bv` 以下的正确性通过在外围累积层级中对底层实参 `c` 作隶属归纳而得。谓词 `P c` 以 `c ∈ Bv` 为条件；这项隶属既把定理限制在所需界内，又借助 `Bv` 的序数性，使每个更小实参都可使用归纳假设。把归纳结论施于任意被记录取值，便得到 `Values`。
<!--ja-->
`Bv` より下での正しさは、基礎にある入力 `c` に対する周囲の所属帰納によって得られる。述語 `P c` は `c ∈ Bv` を条件とする。この所属は定理を必要な界に制限すると同時に、`Bv` の順序数性を通じて、より小さい各入力に帰納の仮定を適用できるようにする。帰納の結論を任意の記録された値に適用すると `Values` が得られる。
<!--/-->

```agda
    vals : Values (lookup f γ) Bv
    vals c w c∈ rec = ∈-induction {P = P} step (fst c) c∈ w rec
```

<!--en-->
Completeness at the bound composes the truncated entry with the correctness just proved: the value equation transports the recorded entry to the canonical one.
<!--zh-->
界处的完备性复合截断条目与刚证的正确性：取值等式把被记录条目运成典范条目。
<!--ja-->
界での完備さは、切り詰められた項目と、今証明した正しさを合成する。値の等式が、記録された項目を正準な項目へ運ぶ。
<!--/-->

```agda
    ents : Entries (lookup f γ) Bv
    ents c c∈ = rec₁ (snd (pr (fst c) (Lset (fst c)) ∈ Fv))
      (λ { (w , rec) → subst (λ u → ⟨ pr (fst c) u ∈ Fv ⟩) (vals c w c∈ rec) rec })
      (entryOf c c∈)
```

<!--en-->
The inward direction of the approximation clause starts from the stronger semantic hypothesis that the table realizes the hierarchy at the bound. This asymmetry is intentional: the outward direction proves only the two table conditions, while the inward direction consumes the full hierarchy specification.
<!--zh-->
逼近子句的向内方向从更强的语义假设出发：表在界处实现层级。这一不对称是有意的：向外方向只证两条表条件，而向内方向消耗完整的层级规格。
<!--ja-->
近似の条項の内向きの方向は、より強い意味論的な仮定からはじまる。表が界で階層を実現することである。この非対称は意図的なものである。外向きの方向が証明するのは二つの表の条件だけで、内向きの方向が消費するのは、階層の完全な仕様である。
<!--/-->

```agda
  approx-in : (ob : IsOrd Bv) → IsHier Bv (lookup f γ)
            → ((c : V ℓ) (oc : IsOrd c) → ⟨ c ∈ Bv ⟩ → Supply Zv c oc)
            → ⟨ γ ⊨ approxAt f b z N ⟩
  approx-in ob sp sup = dom , steps
    where
```

<!--en-->
The outward reading of the hierarchy specification says that every recorded pair has its argument below the bound and its value equal to the stage there.
<!--zh-->
层级规格的向外读法说：每条被记录对的实参低于界，其取值等于该处的层。
<!--ja-->
階層の仕様の外向きの読み出しは、記録されたそれぞれの対について、入力が界の下にあり、値がそこの段階に等しいと言う。
<!--/-->

```agda
    hout : (c w : S) → ⟨ pr (fst c) (fst w) ∈ Fv ⟩ → ⟨ fst c ∈ Bv ⟩ × (fst w ≡ Lset (fst c))
    hout = hier-out Bv ob (lookup f γ) sp
```

<!--en-->
The inward reading says that every canonical pair below the bound is recorded.
<!--zh-->
向内读法说：界以下每条典范对都被记录。
<!--ja-->
内向きの読み出しは、界の下のすべての正準な対が記録されていると言う。
<!--/-->

```agda
    hin : (c : S) → ⟨ fst c ∈ Bv ⟩ → ⟨ pr (fst c) (Lset (fst c)) ∈ Fv ⟩
    hin = hier-in Bv ob (lookup f γ) sp
```

<!--en-->
The domain conjunct is proved by presenting the stage at each argument below the bound and injecting the canonical pair into the table.
<!--zh-->
定义域合取项的证明：对界以下每个实参呈现其层，并把典范对注入表。
<!--ja-->
定義域の連言項は、界の下のそれぞれの入力で段階を提示し、正準な対を表の中へ注入することで証明される。
<!--/-->

```agda
    dom : ⟨ γ ⊨ ∀̇∈ (var b) (∃̇∈ (var (sh 1 f)) (sndEx i0 i1 ⊤̇)) ⟩
    dom c c∈ = ∣ q , ( hin c c∈ , fillSnd i0 (q ∷ c ∷ γ) c w refl ⊤̇ (λ z → z) i1 refl ) ∣₁
      where
      w : S
      w = LsetS (fst c) (mem-ord {A = Bv} ob (fst c) c∈)
```

<!--en-->
The canonical pair is presented by descending along its membership proof into the carrier.
<!--zh-->
正準对沿其隶属证明下降而呈现为载体元素。
<!--ja-->
正準な対は、所属の証明を下降して台の要素として提示される。
<!--/-->

```agda
      q : S
      q = down (lookup f γ) (pr (fst c) (Lset (fst c))) (hin c c∈)
```

<!--en-->
The second approximation conjunct must be proved for every member `q` of the table and every presentation of `q` as a pair `(c,w)`. Under such a presentation, the exact hierarchy specification yields both `c ∈ Bv` and `w ≡ Lset c`. These facts prepare a proof of the step formula at `c`. No claim is made here that an arbitrary member of the candidate table has such a pair presentation.
<!--zh-->
逼近的第二合取项须对表的每个成员 `q`，以及把 `q` 呈现为有序对 `(c,w)` 的每种方式成立。在这样的呈现下，精确的层级规格同时给出 `c ∈ Bv` 与 `w ≡ Lset c`，从而可在 `c` 处证明步进公式。这里并未断言候选表的任意成员都具有这种有序对呈现。
<!--ja-->
近似の第二の連言は、表の各要素 `q` と、`q` を対 `(c,w)` として提示する各方法について示す必要がある。そのような提示のもとでは、階層の厳密な仕様から `c ∈ Bv` と `w ≡ Lset c` の両方が得られ、`c` におけるステップの論理式を証明する準備が整う。ここでは、候補の表の任意の要素がそのような対の提示をもつとは主張していない。
<!--/-->

```agda
    steps : ⟨ γ ⊨ ∀̇∈ (var f) (bothAll i0 stepBody) ⟩
    steps q q∈ = bothAll-in i0 stepBody (q ∷ γ) (λ c w s s∈ c∈s w∈s e →
      let rec : ⟨ pr (fst c) (fst w) ∈ Fv ⟩
          rec = subst (λ u → ⟨ u ∈ Fv ⟩) e q∈
          c∈ : ⟨ fst c ∈ Bv ⟩
```

<!--en-->
The argument is below the bound by the outward hierarchy reading; ordinality is inherited; and `StepRead.step-in` receives all five hypotheses, including the restricted correctness and completeness and the supply at each smaller argument.
<!--zh-->
实参由层级向外读法低于界；序数性被承继；`StepRead.step-in` 接收全部五条假设，包括限制后的正确性与完备性及每个更小实参处的供给。
<!--ja-->
入力は、階層の外向きの読み出しによって界の下にあり、順序数性は受け継がれる。そして `StepRead.step-in` が、制限された正しさと完備さと、より小さい入力ごとの供給を含む、五つの仮定をすべて受け取る。
<!--/-->

```agda
          c∈ = hout c w rec .fst
          oc : IsOrd (fst c)
          oc = mem-ord {A = Bv} ob (fst c) c∈
      in StepRead.step-in i0 i1 (sh 4 f) (sh 4 z) (shN 4 N) (w ∷ c ∷ s ∷ q ∷ γ) tg oc (hout c w rec .snd)
           (λ d w' d∈ rec' → hout d w' rec' .snd)
```

<!--en-->
Below the current argument `c`, completeness comes from `hier-in`: transitivity of the ordinal bound turns `d ∈ c ∈ Bv` into `d ∈ Bv`, where the canonical entry is known to occur. The auxiliary bounds have a different source. They come from the given supply function `sup`, restricted along the same transitivity argument. Thus the hierarchy specification supplies table entries, while `sup` supplies the four bounded coding objects.
<!--zh-->
在当前实参 `c` 以下，完备性来自 `hier-in`：序数界的传递性把 `d ∈ c ∈ Bv` 化为 `d ∈ Bv`，于是典范条目确实存在。辅助界有不同的来源：它们来自给定的供给函数 `sup`，并沿同一传递性论证限制到 `c` 以下。因此，层级规格提供表条目，而 `sup` 提供四个有界编码对象。
<!--ja-->
現在の入力 `c` より下での完全性は `hier-in` から得られる。順序数である界の推移性が `d ∈ c ∈ Bv` を `d ∈ Bv` に変え、そこで正準な項目の存在が分かる。補助的な界は別の根拠から来る。与えられた供給関数 `sup` を同じ推移性に沿って制限したものである。したがって、階層の仕様が表の項目を与え、`sup` が四つの有界な符号化対象を与える。
<!--/-->

```agda
           (λ d d∈ → hin d (ob .fst {x = fst c} {y = fst d} d∈ c∈))
           (λ d od d∈ → sup d od (ob .fst {x = fst c} {y = d} d∈ c∈)))
```
</div>
</details>

<!--en-->
The hierarchy reading has four distinguished slots: the proposed stage `a`, its stage index `p`, the approximation table `f`, and the common witness bound `z`. The tag map interprets the ten numeral positions used by the coding formulas, and the environment supplies carrier elements for all these slots.
<!--zh-->
层级读法有四个特殊槽位：拟议层 `a`、它的层索引 `p`、逼近表 `f` 与公共见证界 `z`。标签映射解释编码公式所用的十个数码位置，环境则为所有这些槽位提供载体元素。
<!--ja-->
階層の読みには四つの特別な枠がある。候補の段階 `a`、その段階の添字 `p`、近似表 `f`、そして共通の証人の界 `z` である。タグの写像は符号化の論理式が使う十個の数項の位置を解釈し、環境はこれらすべての枠に台の要素を与える。
<!--/-->

<details open class="submodule-fold">
<summary class="submodule-fold-heading">
```agda
module HierRead {m : ℕ} (a p f z : Fin m) (N : Fin 10 → Fin m) (γ : S ^ m) (tg : Tags γ N) where
```
</summary>
<div class="submodule-fold-content">

```agda
  private
    Av = fst (lookup a γ)
    Pv = fst (lookup p γ)
    Zv = fst (lookup z γ)
```

<!--en-->
The soundness theorem for the hierarchy formula says: if the formula holds and the ordinal slot is an ordinal, then the level slot equals the stage at the ordinal slot. The proof reads the approximation and the final step separately.
<!--zh-->
层级公式的可靠性定理说：若公式成立且序数槽是序数，则层槽等于序数槽处的层。证明分别读取逼近与最后一步。
<!--ja-->
階層の論理式の健全性の定理はこう言う。論理式が成立し、順序数の枠が順序数であれば、層の枠は順序数の枠での段階に等しい、と。証明は、近似と最後のステップを別々に読む。
<!--/-->

```agda
  hier-sound : ⟨ γ ⊨ hierAt a p f z N ⟩ → IsOrd Pv → Av ≡ Lset Pv
  hier-sound (ha , hs) op = StepRead.step-out a p f z N γ tg hs (ve .fst) (ve .snd)
    where
    ve = ApproxRead.approx-out f p z N γ tg ha op
```

<!--en-->
The completeness theorem for the hierarchy formula takes ordinality of the index slot, the identification of the level slot with the stage, an actual hierarchy table at the index, and the supply function, and constructs the satisfaction.
<!--zh-->
层级公式的完备性定理取索引槽的序数性、层槽与层的等同、索引处的真实层级表与供给函数，构造满足。
<!--ja-->
階層の論理式の完備性の定理は、添字の枠の順序数性、層の枠と段階の同定、添字での実際の階層の表、そして供給の関数を受け取り、充足を作る。
<!--/-->

```agda
  hier-complete : (op : IsOrd Pv) → Av ≡ Lset Pv → IsHier Pv (lookup f γ)
                → ((c : V ℓ) (oc : IsOrd c) → ⟨ c ∈ Pv ⟩ → Supply Zv c oc)
                → ⟨ γ ⊨ hierAt a p f z N ⟩
  hier-complete op aq sp sup =
      ApproxRead.approx-in f p z N γ tg op sp sup
```

<!--en-->
The proof composes the inward approximation from the hierarchy specification with the final step, whose correctness and completeness clauses are read outward from the hierarchy specification at each smaller argument.
<!--zh-->
证明把层级规格的向内逼近与最后一步复合，后者的正确性与完备性子句在每个更小实参处由层级规格向外读取。
<!--ja-->
証明は、階層の仕様からの内向きの近似と、最後のステップを合成する。後者の正しさと完備さの条項は、より小さい入力ごとに、階層の仕様から外向きに読まれる。
<!--/-->

```agda
    , StepRead.step-in a p f z N γ tg op aq
        (λ c w c∈ rec → hier-out Pv op (lookup f γ) sp c w rec .snd)
        (hier-in Pv op (lookup f γ) sp) sup
```
</div>
</details>

<!--en-->
## Reading approximations and the completed hierarchy
<!--zh-->
## 读取逼近与完整层级
<!--ja-->
## 近似と完成した階層を読む
<!--/-->

<!--en-->
The inner module seals the formula that will ultimately express the constructible hierarchy inside the object language.
<!--zh-->
内部模块封存最终将在对象语言内表达可构造层级的公式。
<!--ja-->
内部のモジュールは、対象言語の中で構成可能階層を最終的に表す論理式を封印する。
<!--/-->

<details open class="submodule-fold">
<summary class="submodule-fold-heading">
```agda
module Inner where
```
</summary>
<div class="submodule-fold-content">

<!--en-->
The fourteen-slot environment begins with the ten numeral tags. Repeated `weakenFin` embeds each of their indices into `Fin 14` without changing its numerical position, so `N14` occupies slots zero through nine. This agrees with the concrete environment used later, whose first ten entries are the von Neumann numerals.
<!--zh-->
十四槽环境以前十个数码标签开头。反复使用 `weakenFin` 会把各索引嵌入 `Fin 14` 而不改变其数值位置，因此 `N14` 占据零至九号槽。这与后文使用的具体环境一致，其中前十项正是冯·诺伊曼数码。
<!--ja-->
十四枠の環境は十個の数項タグから始まる。`weakenFin` を繰り返すと、各添字は数値上の位置を変えずに `Fin 14` へ埋め込まれるので、`N14` は零番から九番までの枠を占める。これは、先頭の十項がフォン・ノイマン数項である、後に用いる具体的な環境と一致する。
<!--/-->

```agda
  N14 : Fin 10 → Fin 14
  N14 k = weakenFin (weakenFin (weakenFin (weakenFin k)))
```

<!--en-->
The four trailing slots complete the mathematical data of the inner formula. Slot ten holds the table `ff`, slot eleven the proposed stage `aa`, slot twelve its stage index `pp`, and slot thirteen the common bound `zz`. Thus the full environment is ordered as ten tags, followed by `f`, `a`, `p`, and `z`.
<!--zh-->
末尾四个槽位补全内部公式的数学数据：十号槽存放表 `ff`，十一号槽存放拟议层 `aa`，十二号槽存放其层索引 `pp`，十三号槽存放公共界 `zz`。因此，完整环境的顺序是十个标签，随后依次为 `f`、`a`、`p` 与 `z`。
<!--ja-->
末尾の四つの枠が内側の論理式の数学的データを完成させる。十番の枠は表 `ff`、十一番は候補の段階 `aa`、十二番はその段階の添字 `pp`、十三番は共通の界 `zz` を保持する。したがって環境全体の順序は、十個のタグに続いて `f`、`a`、`p`、`z` となる。
<!--/-->

```agda
  ff aa pp zz : Fin 14
  ff = sh 10 (i0 {3})
  aa = sh 11 (i0 {2})
  pp = sh 12 (i0 {1})
  zz = sh 13 (i0 {0})
```

<!--en-->
The inner formula conjoins two mathematical requirements. `pins N14` fixes the first ten slots as the numeral tags needed by the coding descriptions, while `hierAt aa pp ff zz N14` says that `ff` approximates the hierarchy below `pp` and that `aa` is its next value at `pp`, with all auxiliary data bounded by `zz`. Opacity keeps this large formula behind its proved readings.
<!--zh-->
内部公式合取两项数学要求。`pins N14` 把前十个槽位固定为编码描述所需的数码标签；`hierAt aa pp ff zz N14` 则说 `ff` 逼近 `pp` 以下的层级，而 `aa` 是它在 `pp` 处的下一取值，所有辅助数据均由 `zz` 界定。不透明性把这条大型公式保留在已经证明的读引理之后。
<!--ja-->
内側の論理式は二つの数学的要件を連言する。`pins N14` は最初の十枠を符号化の記述に必要な数項タグとして固定し、`hierAt aa pp ff zz N14` は `ff` が `pp` より下の階層を近似し、`aa` が `pp` におけるその次の値であり、補助データがすべて `zz` で有界化されることを述べる。不透明性により、この大きな論理式は証明済みの読み補題の背後に保たれる。
<!--/-->

```agda
  opaque
    inner : Formula S 14
    inner = pins N14 ∧̇ hierAt aa pp ff zz N14
```

<!--en-->
To prove boundedness, the checker may unfold `inner` together with the sealed descriptions `satAt` and `defAt`. This scoped unfolding reveals that the large conjunction is built entirely from atoms, connectives, and bounded quantifiers. Outside this proof boundary, the mathematical content is recovered through the read lemmas rather than by normalizing the expanded formula.
<!--zh-->
为证明有界性，检查器可以在此局部展开 `inner`，连同封存的描述 `satAt` 与 `defAt`。这一受限展开表明，大型合取只由原子式、联结词与有界量词构成。在这道证明边界之外，公式的数学内容通过读引理恢复，而不靠归约展开后的公式。
<!--ja-->
有界性を証明するため、検査器はこの局所的な範囲で `inner` と、封印された記述 `satAt`、`defAt` を展開できる。この限定された展開により、大きな連言が原子論理式、結合子、有界量化子だけから作られていることが分かる。この証明境界の外では、展開された論理式を正規化するのではなく、読み補題によって数学的内容を取り出す。
<!--/-->

```agda
  opaque
    unfolding inner satAt defAt
```

<!--en-->
After the scoped unfolding, `checkΔ₀ inner _` supplies the structural `Δ₀` witness: every quantifier occurring in `inner` is bounded. This is a syntactic verification of this particular formula, not a claim that `checkΔ₀` decides boundedness in both directions. The surrounding module and its exported results remain parameterized by `lem : LEM (ℓ-suc ℓ)`.
<!--zh-->
经过局部展开，`checkΔ₀ inner _` 给出结构性的 `Δ₀` 见证：`inner` 中出现的每个量词都有界。这是对这条特定公式的句法核验，并不声称 `checkΔ₀` 在两个方向上判定有界性。外围模块及其导出结果仍以 `lem : LEM (ℓ-suc ℓ)` 为参数。
<!--ja-->
局所的な展開の後、`checkΔ₀ inner _` は構造的な `Δ₀` の証人を与える。`inner` に現れる量化子はすべて有界である。これはこの特定の論理式に対する構文的な検証であり、`checkΔ₀` が有界性を双方向に決定するという主張ではない。外側のモジュールとそこから公開される結果は、引き続き `lem : LEM (ℓ-suc ℓ)` をパラメータとする。
<!--/-->

```agda
    Δ₀-inner : Δ₀ inner
    Δ₀-inner = checkΔ₀ inner tt
```

<!--en-->
The readings of the sealed formula are exposed through the same unfolding boundary.
<!--zh-->
封存公式的读法经由同一边界暴露。
<!--ja-->
封印された論理式の読み出しも、同じ展開の境界を通して公開される。
<!--/-->

```agda
  opaque
    unfolding inner
```

<!--en-->
The outward reading of the conjunction is the pair of its two conjuncts, since conjunction is a pair of propositions.
<!--zh-->
合取的向外读法是其两个合取项组成的对，因为合取就是一对命题。
<!--ja-->
連言の外向きの読み出しは、その二つの連言項の対である。連言とは命題の対だからである。
<!--/-->

```agda
    inner-out : (γ : S ^ 14) → ⟨ γ ⊨ inner ⟩ → ⟨ γ ⊨ pins N14 ⟩ × ⟨ γ ⊨ hierAt aa pp ff zz N14 ⟩
    inner-out γ h = h
```

<!--en-->
Conversely, proofs of the pin clauses and of the hierarchy clause form the two components required to satisfy their conjunction. Together with `inner-out`, this gives the two exact directions needed later: one can reason from the large formula through its two mathematical parts, and reconstruct it once both parts have been proved.
<!--zh-->
反过来，pin 子句与层级子句的证明正好构成满足其合取所需的两个分量。它与 `inner-out` 合在一起，给出后文所需的两个精确方向：既可从大型公式推出两个数学部分，也可在两部分均已证明时重新构造该公式。
<!--ja-->
逆に、pin の節と階層の節の証明は、それらの連言を満たすために必要な二つの成分をなす。`inner-out` と合わせると、後で必要となる正確な二方向が得られる。大きな論理式から二つの数学的部分を取り出すことも、両方を証明した後で論理式を再構成することもできる。
<!--/-->

```agda
    inner-in : (γ : S ^ 14) → ⟨ γ ⊨ pins N14 ⟩ → ⟨ γ ⊨ hierAt aa pp ff zz N14 ⟩ → ⟨ γ ⊨ inner ⟩
    inner-in γ h1 h2 = h1 , h2
```

<!--en-->
For an outer environment with `suc n` positions, `lastFin` denotes its last position. In every application below, that position contains the common bounding set that supplies the bound for the new existential. The witness introduced by the bounded quantifier occupies the new front position of the body; it is not the position denoted by `lastFin`.
<!--zh-->
对具有 `suc n` 个位置的外层环境，`lastFin` 表示其最后一个位置。在下文每次应用中，该位置都存放为新存在量词提供界的公共界集。有界量词引入的见证占据公式体中新添的最前位置，并不是 `lastFin` 所指的位置。
<!--ja-->
`suc n` 個の位置をもつ外側の環境に対して、`lastFin` はその最後の位置を表す。以下の各適用では、その位置に新しい存在量化子の界となる共通の集合が置かれている。有界量化子が導入する証人は本体の新しい先頭位置を占め、`lastFin` が指す位置ではない。
<!--/-->

```agda
  lastFin : {n : ℕ} → Fin (suc n)
  lastFin {zero} = zero
  lastFin {suc n} = suc (lastFin {n})
```

<!--en-->
The operation `wrap` existentially binds the front witness position of its body and requires that witness to belong to the set named by the last outer position. Consequently the arity drops by one while boundedness is preserved. Repeating this operation will quantify the ten numeral tags and the table, each as an element of the common bound `z`.
<!--zh-->
操作 `wrap` 以存在量词约束公式体最前的见证位置，并要求该见证属于外层最后位置所命名的集合。因此，公式的元数减少一，而有界性保持。反复施用这一操作，会把十个数码标签与表逐个量化，并要求它们都属于公共界 `z`。
<!--ja-->
演算 `wrap` は、本体の先頭にある証人の位置を存在量化し、その証人が外側の最後の位置で名づけられた集合に属することを要求する。そのため、有界性を保ったまま項数が一つ減る。この演算を繰り返すことで、十個の数項タグと表がそれぞれ量化され、いずれも共通の界 `z` の要素であることが要求される。
<!--/-->

```agda
  wrap : {n : ℕ} → Formula S (suc (suc n)) → Formula S (suc n)
  wrap {n} φ = ∃̇∈ (var (lastFin {n})) φ
```

<!--en-->
The Δ₀ witness is preserved under wrapping, because bounded existential quantification is itself a bounded construction.
<!--zh-->
Δ₀ 见证在包裹下保持，因为有界存在量化本身就是有界构造。
<!--ja-->
Δ₀ の証人は、包む操作の下でも保たれる。有界の存在量化は、それ自体が有界の構成だからである。
<!--/-->

```agda
  δ-wrap : {n : ℕ} {φ : Formula S (suc (suc n))} → Δ₀ φ → Δ₀ (wrap {n} φ)
  δ-wrap d = δ-∃∈ d
```

<!--en-->
Five wrapping steps consume five of the ten numeral slots, reducing the free positions one at a time from fourteen to nine.
<!--zh-->
五步包裹消耗十个数码槽中的五个，把自由位置从十四逐次减到九。
<!--ja-->
五回の包む操作が、十の数項の枠のうち五つを消費し、自由な位置を十四から九へと一つずつ減らす。
<!--/-->

```agda
  s13 = wrap {12} inner
  s12 = wrap {11} s13
  s11 = wrap {10} s12
  s10 = wrap {9}  s11
  s9  = wrap {8}  s10
```

<!--en-->
Five more wrapping steps reduce the free positions from nine to four, leaving only the level, the ordinal index, the table and the witness bound.
<!--zh-->
再五步包裹把自由位置从九减到四，只余层、序数索引、表与见证界。
<!--ja-->
さらに五回の包む操作が、自由な位置を九から四へ減らし、層・順序数の添字・表・証人の界だけを残す。
<!--/-->

```agda
  s8  = wrap {7}  s9
  s7  = wrap {6}  s8
  s6  = wrap {5}  s7
  s5  = wrap {4}  s6
  s4  = wrap {3}  s5
```

<!--en-->
The eleventh wrap existentially binds the remaining auxiliary slot, the hierarchy table `f`, again with bound `z`. Exactly three free positions remain, in the order `(a,p,z)`: the proposed stage, its stage index, and the common witness bound. Thus `three` has arity three and is not a sentence; the later erasure step will remove its unused constant domain without removing these free variables.
<!--zh-->
第十一次包裹再次以 `z` 为界，用存在量词约束最后的辅助槽，即层级表 `f`。此时恰余三个自由位置，顺序为 `(a,p,z)`：拟议层、它的层索引与公共见证界。因此，`three` 是三元公式而不是句子；后续擦除步骤会移除其未使用的常元域，但不会移除这三个自由变元。
<!--ja-->
十一回目の包みは、再び `z` を界として、残る補助的な枠である階層の表 `f` を存在量化する。自由な位置はちょうど三つ、順に `(a,p,z)`、すなわち候補の段階、その段階の添字、共通の証人の界だけになる。したがって `three` は三項論理式であって文ではない。後の消去は使われていない定数領域を取り除くが、この三つの自由変数は取り除かない。
<!--/-->

```agda
  three : Formula S 3
  three = wrap {2} s4
```

<!--en-->
The witness formula is wrapped eleven times, once per bounded existential introduced inside the common bound. Each wrap adds one layer of the Δ₀ certificate, so the wrapped formula is bounded throughout.
<!--zh-->
见证公式被包裹十一次，对应公共界内部引入的十一个有界存在量词。每次包裹增加一层 Δ₀ 见证，因此包裹后的公式始终有界。
<!--ja-->
証人の論理式は十一回包まれる。共通の界の内側で導入された有界の存在量化子の一つひとつに対応する。各包みが Δ₀ の証拠の一層を加えるため、包まれた論理式は全体を通して有界のままである。
<!--/-->

```agda
  Δ₀-three : Δ₀ three
  Δ₀-three =
    δ-wrap (δ-wrap (δ-wrap (δ-wrap (δ-wrap (δ-wrap (δ-wrap
      (δ-wrap (δ-wrap (δ-wrap (δ-wrap Δ₀-inner))))))))))
```

<!--en-->
To verify that the wrapped formula contains no constants, the calculation may look through the sealed definitions of `inner`, `satAt`, and `defAt`. This local unfolding exposes enough of their syntax for the occurrence count to reduce, while the large formulas themselves remain hidden behind their read and write lemmas in the surrounding argument.
<!--zh-->
为了验证包裹后的公式不含常元，这项计算可以查看已密封的 `inner`、`satAt` 与 `defAt` 的定义。这样的局部展开只暴露化简出现次数所需的语法；在外围论证中，这些大型公式本身仍由各自的读引理与写引理来使用。
<!--ja-->
包まれた論理式に定数が含まれないことを確かめるため、この計算では密封された `inner`、`satAt`、`defAt` の定義を参照できる。この局所的な展開が明らかにするのは出現回数の簡約に必要な構文だけであり、周囲の議論では大きな論理式そのものを読み補題と書き補題を通して扱う。
<!--/-->

```agda
  opaque
    unfolding inner satAt defAt
```

<!--en-->
The constant-occurrence count of `three` is zero. Its three remaining positions are free variables for `a`, `p`, and `z`; they are not constants. Once the sealed components are unfolded for this calculation, the equality reduces definitionally because every term in the formula was built from variables.
<!--zh-->
`three` 的常元出现次数为零。它留下的三个位置是供 `a`、`p` 与 `z` 使用的自由变元，并非常元。为这项计算展开密封成分后，该等式按定义化简，因为公式中的每个词项都由变元构成。
<!--ja-->
`three` における定数の出現回数は零である。残る三つの位置は `a`、`p`、`z` のための自由変数であり、定数ではない。この計算のために密封された部分を展開すると、論理式のすべての項が変数から作られているため、等式は定義的に簡約される。
<!--/-->

```agda
    count-three : countFo three ≡ 0
    count-three = refl
```

<!--en-->
Since `three` contains no constants, erasure changes its constant domain from the constructible carrier to the empty type and leaves its variables and quantifier structure intact. The resulting `erased` is therefore parameter-free but still has arity three; embedding it back into the old constant domain recovers `three`.
<!--zh-->
由于 `three` 不含常元，擦除把它的常元域从可构造载体改为空类型，同时保持其变元与量词结构。所得 `erased` 因而是无参公式，但元数仍为三；把它嵌回原常元域便恢复 `three`。
<!--ja-->
`three` は定数を含まないので、消去は定数域を構成可能な台から空の型へ変えつつ、変数と量化子の構造を保つ。したがって得られる `erased` は無パラメータであるが、アリティは三のままである。これを元の定数域へ埋め込むと `three` が復元される。
<!--/-->

```agda
  erased : Formula (⊥* {ℓ-suc ℓ}) 3
  erased = Cnt.erase three count-three
```

<!--en-->
Erasure also preserves the Δ₀ witness. It changes only the unavailable constant symbols, so every bounded quantifier in `three` remains bounded and the same structural argument proves `erased` to be Δ₀.
<!--zh-->
擦除也保持 Δ₀ 见证。它只改变已经不出现的常元符号，所以 `three` 中的每个有界量词仍然有界；同一项结构论证由此证明 `erased` 是 Δ₀ 公式。
<!--ja-->
消去は Δ₀ の証拠も保つ。変更されるのは、もともと出現しない定数記号だけである。そのため `three` の各有界量化子は有界なままであり、同じ構造的な議論によって `erased` が Δ₀ であることが示される。
<!--/-->

```agda
  Δ₀-erased : Δ₀ erased
  Δ₀-erased = erase-Δ₀ three count-three Δ₀-three
```

<!--en-->
Semantically, one wrapped layer is a propositionally truncated bounded witness. If every member `x` of the bound that satisfies the body yields `P`, then `unwrap` eliminates that truncated existence into `P`. The declaration `P : hProp` supplies precisely the proposition condition required by this elimination.
<!--zh-->
在语义上，一层包裹是一份受命题截断的有界见证。若界中的每个成员 `x` 只要满足主体就能推出 `P`，则 `unwrap` 可把这项受截断的存在消去到 `P` 中。声明 `P : hProp` 恰好提供这种消去所要求的命题条件。
<!--ja-->
意味論的には、一層の包みは命題的に切り詰められた有界の証人である。境界の要素 `x` が本体を満たすたびに `P` が得られるなら、`unwrap` はその切り詰められた存在を `P` へ除去する。`P : hProp` という宣言が、この除去に必要な命題性をちょうど与える。
<!--/-->

```agda
  unwrap : {n : ℕ} (φ : Formula S (suc (suc n))) (γ : S ^ (suc n)) {P : hProp (ℓ-suc ℓ)}
         → ((x : S) → ⟨ fst x ∈ fst (lookup (lastFin {n}) γ) ⟩ → ⟨ (x ∷ γ) ⊨ φ ⟩ → ⟨ P ⟩)
         → ⟨ γ ⊨ wrap {n} φ ⟩ → ⟨ P ⟩
  unwrap φ γ {P} k h = rec₁ (snd P) (λ { (x , xz , hx) → k x xz hx }) h
```

<!--en-->
`wrap-in` builds the bounded existential from a named member and the body's satisfaction at its extension, the introduction rule of the bounded existential quantifier.
<!--zh-->
`wrap-in` 由一个被点名的成员及其扩展处的主体满足构造有界存在，即有界存在量词的引入规则。
<!--ja-->
`wrap-in` は、名指された要素とその拡張での本体の充足から、有界の存在量化を組み立てる。有界の存在量化子の導入規則である。
<!--/-->

```agda
  wrap-in : {n : ℕ} (φ : Formula S (suc (suc n))) (γ : S ^ (suc n)) (x : S)
          → ⟨ fst x ∈ fst (lookup (lastFin {n}) γ) ⟩ → ⟨ (x ∷ γ) ⊨ φ ⟩ → ⟨ γ ⊨ wrap {n} φ ⟩
  wrap-in φ γ x m h = ∣ x , (m , h) ∣₁
```
</div>
</details>

<!--en-->
## A parameter-free formula for constructible levels
<!--zh-->
## 描述可构造层的无参公式
<!--ja-->
## 構成可能な階層を表すパラメータなし論理式
<!--/-->

<!--en-->
The visible formula `levelFo` has three free positions `(a,p,z)`. It conjoins the assertion that `p` is an ordinal with the erased hierarchy description bounded by `z`. Thus `z` remains a free input even though the soundness conclusion will mention only `a` and `p`.
<!--zh-->
可见公式 `levelFo` 有三个自由位置 `(a,p,z)`。它把「`p` 是序数」与「由 `z` 限界的已擦除层级描述」合取起来。因此，尽管可靠性的结论只提及 `a` 与 `p`，`z` 仍是一个自由输入。
<!--ja-->
表に現れる論理式 `levelFo` には、三つの自由な位置 `(a,p,z)` がある。これは `p` が順序数であるという主張と、`z` で有界化された消去後の階層記述との連言である。したがって健全性の結論が `a` と `p` だけに言及しても、`z` は論理式の入力として残る。
<!--/-->

```agda
levelFo : Formula (⊥* {ℓ-suc ℓ}) 3
levelFo = isOrd-at-p ∧̇ Inner.erased
```

<!--en-->
Both conjuncts of `levelFo` are Δ₀, and the Δ₀ class is closed under conjunction. The conjunction constructor therefore combines their two boundedness witnesses into the witness `Δ₀-levelFo` without introducing an unbounded quantifier.
<!--zh-->
`levelFo` 的两个合取项都是 Δ₀ 公式，而 Δ₀ 类对合取封闭。因此，合取构造子把两份 Δ₀ 见证合成 `Δ₀-levelFo`，并未引入无界量词。
<!--ja-->
`levelFo` の二つの連言項はいずれも Δ₀ であり、Δ₀ のクラスは連言について閉じている。したがって連言の構成子は、非有界量化子を導入することなく、二つの有界性の証拠を `Δ₀-levelFo` の証拠へまとめる。
<!--/-->

```agda
Δ₀-levelFo : Δ₀ levelFo
Δ₀-levelFo = δ-∧ Δ₀-isOrd-at-p Inner.Δ₀-erased
```

<!--en-->
The reading lemma composes three paths for any constant-free Δ₀ formula: Δ₀ absoluteness from the restricted carrier to the ambient hierarchy, the invariance of satisfaction under embedding the empty constant domain, and the uniqueness of the empty interpretation. The result is an equality of satisfaction propositions.
<!--zh-->
读取引理对任何无常元 Δ₀ 公式复合三条路径：从限制载体到外围层级的 Δ₀ 绝对性、空常元域嵌入下满足的不变性、以及空解释的唯一性。结果是两个满足命题的等式。
<!--ja-->
読みの補題は、定数のない任意の Δ₀ 論理式に対して三つのパスを合成する。制限された台から周囲の階層への Δ₀ 絶対性、空の定数域の埋め込みによる充足の不変性、そして空の解釈の一意性である。結果は二つの充足の命題の等式である。
<!--/-->

```agda
read : {n : ℕ} {φ : Formula (⊥* {ℓ-suc ℓ}) n} → Δ₀ φ → (δ : S ^ n)
     → (δ ⊨ embed φ) ≡ (map fst δ ⊨ₚ φ)
read {n} {φ} dφ δ =
    AbsL.abs₀ (mapΔ₀ ⊥*-rec dφ) δ
  ∙ embed-⊨ 𝒮ᵥ {K = S} fst φ (map fst δ)
```

<!--en-->
The final equality in this path concerns the interpretation of constants. Because the constant domain is empty, any such interpretation agrees pointwise with empty elimination. Function extensionality identifies it with the canonical empty interpretation, so the preceding embedding comparison ends at the ambient reading of the same parameter-free formula.
<!--zh-->
这条路径的最后一项等式处理常元解释。由于常元域为空，任何这类解释都逐点等于空类型消去给出的解释。函数外延性把它认同于典范的空解释，于是前一步的嵌入比较最终到达同一无参公式的外围读法。
<!--ja-->
このパスの最後の等式が扱うのは定数の解釈である。定数域が空なので、どの解釈も各点で空型の除去から得られる解釈と一致する。関数外延性がそれを正準な空の解釈と同一視し、その結果、直前の埋め込みの比較は同じ無パラメータ論理式の外側での読みへ到達する。
<!--/-->

```agda
  ∙ cong (λ ι → SemVᵃ.At._⊨_ (⊥* {ℓ-suc ℓ}) ι (map fst δ) φ)
         (funExt (λ b → ⊥*-rec b))
```

<!--en-->
The outward ordinal reader unpacks the two clauses of the ordinality atom into the transitivity of the underlying set of `p` and the transitivity of each of its members, with every entry lowered through the presentation of `p`.
<!--zh-->
向外序数读取把序数性原子的两个子句展开为：`p` 的底层集合的传递性，以及其每个成员的传递性；所有条目都经 `p` 的呈现降下。
<!--ja-->
外向きの順序数の読みは、順序数性の原子の二つの節を、`p` の基底集合の推移性とその各要素の推移性へと展開する。すべての項目は `p` の提示を通して降ろされる。
<!--/-->

```agda
ord-out : (a p z : S) → ⟨ (a ∷ p ∷ z ∷ []) ⊨ embed isOrd-at-p ⟩ → IsOrd (fst p)
ord-out a p z h =
    ( λ {x} {y} y∈x x∈p → h .fst (down p x x∈p) x∈p (down (down p x x∈p) y y∈x) y∈x )
  , ( λ x x∈p {y} {u} u∈y y∈x →
        h .snd (down p x x∈p) x∈p (down (down p x x∈p) y y∈x) y∈x
```

<!--en-->
For the second ordinality clause, take `x ∈ p`, `y ∈ x`, and `u ∈ y`. Lowering all three memberships into the constructible carrier lets the formula's second conjunct conclude `u ∈ x`. This is exactly the transitivity of each member `x` of `p`, and together with the first clause it yields `IsOrd p`.
<!--zh-->
对序数性的第二个子句，取 `x ∈ p`、`y ∈ x` 与 `u ∈ y`。把这三层隶属都降入可构造载体后，公式的第二个合取项推出 `u ∈ x`。这恰是 `p` 的每个成员 `x` 的传递性；连同第一个子句便得到 `IsOrd p`。
<!--ja-->
順序数性の第二の条項では、`x ∈ p`、`y ∈ x`、`u ∈ y` を取る。この三段の所属を構成可能な台へ降ろすと、論理式の第二の連言項から `u ∈ x` が得られる。これは `p` の各要素 `x` の推移性そのものであり、第一の条項と合わせて `IsOrd p` が得られる。
<!--/-->

```agda
          (down (down (down p x x∈p) y y∈x) u u∈y) u∈y )
```

<!--en-->
The inward ordinal reader builds the two clauses from the ordinality certificate, with every entry packaged as an element of `L`.
<!--zh-->
向内序数读取由序数性证明构造两个子句，所有条目都打包为 `L` 的元素。
<!--ja-->
内向きの順序数の読みは、順序数性の証明から二つの節を組み立てる。すべての項目は `L` の要素としてまとめられる。
<!--/-->

```agda
ord-in : (a p z : S) → IsOrd (fst p) → ⟨ (a ∷ p ∷ z ∷ []) ⊨ embed isOrd-at-p ⟩
ord-in a p z op =
    (λ x x∈p y y∈x → op .fst {x = fst x} {y = fst y} y∈x x∈p)
  , (λ x x∈p y y∈x u u∈y → op .snd (fst x) x∈p {x = fst y} {y = fst u} u∈y y∈x)
```

<!--en-->
The soundness argument now works inside the fourteen-slot reading of the hidden formula. Its task is to discard the bounded auxiliary witnesses while retaining their mathematical consequence: the value in slot `a` is the constructible stage indexed by slot `p`.
<!--zh-->
可靠性论证现在转入隐藏公式的十四槽位读法。它要丢弃受限界的辅助见证，同时保留这些见证的数学后果：槽位 `a` 中的值就是由槽位 `p` 索引的可构造层。
<!--ja-->
健全性の議論はここから、隠された論理式を十四のスロットで読む形に移る。目的は、有界な補助証人を捨てつつ、その数学的帰結、すなわちスロット `a` の値がスロット `p` を添字とする構成可能な段階であることを残すことである。
<!--/-->



<details open class="submodule-fold">
<summary class="submodule-fold-heading">
```agda
private module Sound where
```
</summary>
<div class="submodule-fold-content">

```agda
  open Inner
```

<!--en-->
The finish lemma separates the two conjuncts of `inner`. The pins reader turns the first into the ten numeral equalities required by the hierarchy reader. From the approximation in the second conjunct, `hier-sound` recovers only `Values × Entries`, which is enough to read the final step as `a = Lset p` once the ordinality of `p` is supplied. This does not assert that the hidden table has no malformed members or entries outside `p`.
<!--zh-->
`finish` 引理分开读取 `inner` 的两个合取项。pins 读引理把第一项化为层级读引理所需的十条数码等式。对于第二项中的逼近，`hier-sound` 只恢复 `Values × Entries`；再给出 `p` 的序数性后，这已足以把最后一步读成 `a = Lset p`。这里并未断言隐藏表不含畸形成员，也未断言其中没有基点落在 `p` 之外的条目。
<!--ja-->
`finish` 補題は `inner` の二つの連言項を分けて読む。pins の読み補題は第一項を、階層の読み補題が必要とする十個の数項の等式へ変える。第二項の近似から `hier-sound` が復元するのは `Values × Entries` だけであるが、`p` の順序数性が与えられれば、それで最後のステップを `a = Lset p` と読むには十分である。ここでは、隠れた表に不正な形の要素がないことも、`p` の外を第一成分とする項目がないことも主張していない。
<!--/-->

```agda
  finish : (γ : S ^ 14) → ⟨ γ ⊨ inner ⟩ → IsOrd (fst (lookup pp γ))
         → fst (lookup aa γ) ≡ Lset (fst (lookup pp γ))
  finish γ h op = HierRead.hier-sound aa pp ff zz N14 γ tg (inner-out γ h .snd) op
    where
    tg : Tags γ N14
```

<!--en-->
The pinned numerals are read outward by the pins reader, which derives the ten numeral equations from the object-language clauses.
<!--zh-->
被固定的数码由 pins 读式向外读取，从对象语言子句推导出十条数码等式。
<!--ja-->
固定された数項は pins の読みによって外向きに読まれ、対象言語の節から十の数項の等式が導かれる。
<!--/-->

```agda
    tg = PinsRead.pins-out N14 γ (inner-out γ h .fst)
```

<!--en-->
The internal soundness lemma begins with three elements `a`, `p`, and `z` of the constructible carrier and assumes that `embed levelFo` holds there. It first uses the erasure inverse to recover satisfaction of the eleven-times-wrapped formula. The desired conclusion compares the underlying set of `a` with `Lset` at the underlying index `p`.
<!--zh-->
内部可靠性引理从可构造载体的三个元素 `a`、`p` 与 `z` 出发，并假设 `embed levelFo` 在其上成立。它先用擦除逆等式恢复十一重包裹公式的满足。所求结论把 `a` 的底层集合与 `p` 的底层索引处的 `Lset` 相比较。
<!--ja-->
内部の健全性補題は、構成可能な台の三要素 `a`、`p`、`z` から始め、そこで `embed levelFo` が成り立つと仮定する。まず消去の逆等式を用いて、十一回包まれた論理式の充足を復元する。求める結論は、`a` の基礎集合と、`p` の基礎集合を添字とする `Lset` とを比較するものである。
<!--/-->

```agda
  sound-L : (a p z : S) → ⟨ (a ∷ p ∷ z ∷ []) ⊨ embed levelFo ⟩ → fst a ≡ Lset (fst p)
  sound-L a p z (ho , hφ) =
    go (subst (λ ψ → ⟨ (a ∷ p ∷ z ∷ []) ⊨ ψ ⟩) (Cnt.erase-inv three count-three) hφ)
    where
    ordp : IsOrd (fst p)
```

<!--en-->
The ordinality conjunct produces the ordinality certificate of `p` through the outward ordinal reader, which is the remaining input that the hierarchy reader requires.
<!--zh-->
序数性合取项经向外序数读取产生 `p` 的序数性证明，这是层级读式所需的剩余输入。
<!--ja-->
順序数性の連言項は、外向きの順序数の読みを通して `p` の順序数性の証明を生み出す。これが階層の読みの残りの入力である。
<!--/-->

```agda
    ordp = ord-out a p z ho
```

<!--en-->
The equality to be retained is made into the proposition `G`. Sets in the cumulative hierarchy form an h-set, so `setIsSet` proves that this equality type is an `hProp`. Consequently each propositionally truncated bounded witness may be eliminated into `G` without exposing a chosen witness.
<!--zh-->
需要保留的等式被组成命题 `G`。累积层级中的集合构成 h-集合，因此 `setIsSet` 证明该等式类型是 `hProp`。由此，每份受命题截断的有界见证都可被消去到 `G` 中，而不会暴露一个选定见证。
<!--ja-->
最後まで残す等式を命題 `G` としてまとめる。累積階層の集合は h-集合をなすので、`setIsSet` によりこの等式型が `hProp` であることが分かる。したがって、命題的に切り詰められた各有界証人を、特定の証人を外へ取り出すことなく `G` へ除去できる。
<!--/-->

```agda
    G : hProp (ℓ-suc ℓ)
    G = (fst a ≡ Lset (fst p)) , setIsSet (fst a) (Lset (fst p))
```

<!--en-->
Soundness unwraps the eleven bounded existentials one at a time, consuming the truncated witnesses into the propositional equality. The unwrapping order mirrors the binding order of the formula.
<!--zh-->
可靠性逐一消去十一个有界存在，把截断的见证消耗为命题等式。消去的顺序镜像公式的绑定顺序。
<!--ja-->
健全性は十一の有界の存在量化を一つずつ展開し、切り詰められた証人を命題の等式の中で消費する。展開の順序は論理式の束縛の順序を反映する。
<!--/-->

```agda
    go : ⟨ (a ∷ p ∷ z ∷ []) ⊨ three ⟩ → ⟨ G ⟩
    go =
      unwrap s4 (a ∷ p ∷ z ∷ []) {G} λ F mF →
      unwrap s5 (F ∷ a ∷ p ∷ z ∷ []) {G} λ x9 m9 →
      unwrap s6 (x9 ∷ F ∷ a ∷ p ∷ z ∷ []) {G} λ x8 m8 →
```

<!--en-->
The next five eliminations recover the numeral witnesses `x7` through `x3`. At every stage the environment grows at the front, while its last slot remains `z`, the common bound from which all eleven witnesses came.
<!--zh-->
接下来的五次消去恢复数码见证 `x7` 至 `x3`。每一步都在环境前端加入一个元素，而最后一个槽位始终是 `z`，也就是十一份见证共同来自的界。
<!--ja-->
続く五回の除去で、数項の証人 `x7` から `x3` までを復元する。各段階で環境は先頭側へ伸ぶが、最後のスロットは常に `z` のままである。十一個の証人はすべてこの共通の境界から得られる。
<!--/-->

```agda
      unwrap s7 (x8 ∷ x9 ∷ F ∷ a ∷ p ∷ z ∷ []) {G} λ x7 m7 →
      unwrap s8 (x7 ∷ x8 ∷ x9 ∷ F ∷ a ∷ p ∷ z ∷ []) {G} λ x6 m6 →
      unwrap s9 (x6 ∷ x7 ∷ x8 ∷ x9 ∷ F ∷ a ∷ p ∷ z ∷ []) {G} λ x5 m5 →
      unwrap s10 (x5 ∷ x6 ∷ x7 ∷ x8 ∷ x9 ∷ F ∷ a ∷ p ∷ z ∷ []) {G} λ x4 m4 →
      unwrap s11 (x4 ∷ x5 ∷ x6 ∷ x7 ∷ x8 ∷ x9 ∷ F ∷ a ∷ p ∷ z ∷ []) {G} λ x3 m3 →
```

<!--en-->
The innermost witness completes the unwrapping: the fourteen-slot environment is passed to the finish lemma together with the ordinality certificate, producing the equality of the two underlying sets.
<!--zh-->
最内层见证完成消去：十四槽位环境连同序数性证明一起交给 finish 引理，产出两个底层集合的等式。
<!--ja-->
最も内側の証人が展開を完成させる。十四スロットの環境と順序数性の証明が finish の補題に渡され、二つの基底集合の等式が生まれる。
<!--/-->

```agda
      unwrap s12 (x3 ∷ x4 ∷ x5 ∷ x6 ∷ x7 ∷ x8 ∷ x9 ∷ F ∷ a ∷ p ∷ z ∷ []) {G} λ x2 m2 →
      unwrap s13 (x2 ∷ x3 ∷ x4 ∷ x5 ∷ x6 ∷ x7 ∷ x8 ∷ x9 ∷ F ∷ a ∷ p ∷ z ∷ []) {G} λ x1 m1 →
      unwrap inner (x1 ∷ x2 ∷ x3 ∷ x4 ∷ x5 ∷ x6 ∷ x7 ∷ x8 ∷ x9 ∷ F ∷ a ∷ p ∷ z ∷ []) {G}
        λ x0 m0 hm →
          finish (x0 ∷ x1 ∷ x2 ∷ x3 ∷ x4 ∷ x5 ∷ x6 ∷ x7 ∷ x8 ∷ x9 ∷ F ∷ a ∷ p ∷ z ∷ []) hm ordp
```
</div>
</details>

<!--en-->
For ambient sets `a`, `p`, and `z` known to be constructible, their constructibility proofs present them as elements of the constructible carrier. Reading Δ₀ absoluteness backwards transfers ambient satisfaction of `levelFo` to satisfaction by those presentations, where the internal soundness argument applies. Projecting back gives `a = Lset p`. Thus constructibility of all three inputs is an explicit hypothesis, not a consequence of the formula.
<!--zh-->
对于已知可构造的周遭集合 `a`、`p` 与 `z`，各自的可构造性证明把它们呈现为可构造载体的元素。反向读取 Δ₀ 绝对性，便把 `levelFo` 的周遭满足搬到这些呈现上的满足，从而可应用内部可靠性论证。投影回去后得到 `a = Lset p`。因此，三个输入全都可构造是显式假设，并非公式自身的结论。
<!--ja-->
周囲の集合 `a`、`p`、`z` が構成可能であるとき、それぞれの構成可能性の証拠によって、これらを構成可能な台の要素として提示できる。Δ₀ 絶対性を逆向きに読むと、`levelFo` の周囲での充足がそれらの提示による充足へ移り、内部の健全性の議論を適用できる。基礎集合へ戻せば `a = Lset p` が得られる。したがって、三つの入力がすべて構成可能であることは明示的な仮定であり、論理式から導かれる結論ではない。
<!--/-->

```agda
level-sound : (a p z : V ℓ) → ⟨ isL a ⟩ → ⟨ isL p ⟩ → ⟨ isL z ⟩
            → ⟨ (a ∷ p ∷ z ∷ []) ⊨ₚ levelFo ⟩ → a ≡ Lset p
level-sound a p z la lp lz h =
  Sound.sound-L (a , la) (p , lp) (z , lz)
    (subst ⟨_⟩ (sym (read Δ₀-levelFo ((a , la) ∷ (p , lp) ∷ (z , lz) ∷ []))) h)
```

<!--en-->
For completeness, fix `lam` with adequacy data and an ordinal `p ∈ lam`. The ordinality field makes `lam` a stage index, whose corresponding stage is `Lset lam`; the other fields give successor closure, membership of `ω`, and the required coding witnesses below `lam`. The proof will use these facts to show that the particular bound `Lset lam` contains every witness needed to describe the stage `Lset p`.
<!--zh-->
为证明完备性，固定带有充分性数据的 `lam` 以及序数 `p ∈ lam`。序数性字段使 `lam` 成为层索引，其对应的层是 `Lset lam`；其余字段给出后继封闭、包含 `ω`，以及 `lam` 以下各处所需的编码见证。证明将用这些性质说明，特定的界 `Lset lam` 包含描述层 `Lset p` 所需的每份见证。
<!--ja-->
完全性のため、妥当性のデータをもつ `lam` と順序数 `p ∈ lam` を固定する。順序数性のフィールドにより `lam` は段階の添字となり、対応する段階は `Lset lam` である。残るフィールドは後者閉包、`ω` の所属、および `lam` の下で必要となる符号化の証人を与える。これらを用いて、特定の境界 `Lset lam` が段階 `Lset p` の記述に必要なすべての証人を含むことを示す。
<!--/-->



<details open class="submodule-fold">
<summary class="submodule-fold-heading">
```agda
private module Complete (lam : V ℓ) (ad : Adequate lam) (p : V ℓ) (op : IsOrd p) (p∈λ : ⟨ p ∈ lam ⟩) where
```
</summary>
<div class="submodule-fold-content">

```agda
  open Inner
  open Adequate lam ad using ( ord; succ; ω∈; wit )
```

<!--en-->
Transitivity of the adequate stage `lam` is extracted from its ordinality: two nested memberships compose into one.
<!--zh-->
充分层 `lam` 的传递性由其序数性提取：两个嵌套的隶属复合为一个。
<!--ja-->
十分な段階 `lam` の推移性は、その順序数性から取り出される。入れ子になった二つの所属が一つに合成される。
<!--/-->

```agda
  private
    tr : (x y : V ℓ) → ⟨ x ∈ lam ⟩ → ⟨ y ∈ x ⟩ → ⟨ y ∈ lam ⟩
    tr x y x∈ y∈ = ord .fst {x = x} {y = y} y∈ x∈
```

<!--en-->
The empty set belongs to the adequate stage, by transitivity applied to the chain `∅ ∈ ω ∈ lam`.
<!--zh-->
空集属于充分层，依据是对链 `∅ ∈ ω ∈ lam` 施用的传递性。
<!--ja-->
空集合は十分な段階に属する。`∅ ∈ ω ∈ lam` の連鎖に推移性を適用した結果である。
<!--/-->

```agda
    ∅∈λ : ⟨ ∅ ∈ lam ⟩
    ∅∈λ = tr ω ∅ ω∈ (#∈ω zero)
```

<!--en-->
The numeral-bound argument specializes to the constructible hierarchy at `lam`. Ordinality, successor closure, and the membership `∅ ∈ lam` imply that the underlying set of every model numeral belongs to `Lset lam`. This supplies the uniform bound later needed for all ten tag numerals.
<!--zh-->
数码限界论证在 `lam` 处特化到可构造层级。由序数性、后继封闭与 `∅ ∈ lam` 可得，每个模型数码的底层集合都属于 `Lset lam`。这给出稍后十个标签数码共同需要的界。
<!--ja-->
数項の有界性の議論を、`lam` における構成可能階層へ特殊化する。順序数性、後者閉包、`∅ ∈ lam` から、各模型数項の基礎集合が `Lset lam` に属することが従う。これが、後で十個のタグ数項すべてに必要となる共通の境界を与える。
<!--/-->

```agda
    module B = Bound lam ord succ ∅∈λ using ( num∈λ )
```

<!--en-->
Set `K = Lset lam`. This is the common bounding set represented by the third free input `zS`; the hierarchy table, the ten numerals, and every auxiliary set used to justify a row must all be shown to belong to `K`.
<!--zh-->
令 `K = Lset lam`。这是第三个自由输入 `zS` 所呈现的公共界集；层级表、十个数码，以及论证每一行所用的全部辅助集合，都必须证明属于 `K`。
<!--ja-->
`K = Lset lam` と置く。これは第三の自由入力 `zS` が表す共通の境界集合である。階層表、十個の数項、そして各行を正当化するすべての補助集合が `K` に属することを示す必要がある。
<!--/-->

```agda
    K : V ℓ
    K = Lset lam
```

<!--en-->
If `c ∈ lam`, successor closure gives `sucV c ∈ lam`. The standard successor-stage fact places `Lset c` in `Lset (sucV c)`, and monotonicity along `sucV c ∈ lam` then lifts this membership to `Lset c ∈ K`. Later the same lemma is applied to `sucV c`, using successor closure once more, to put `Lset (sucV c)` in `K`; that is the definable-power-set witness needed for the row at `c`.
<!--zh-->
若 `c ∈ lam`，后继封闭给出 `sucV c ∈ lam`。标准的后继层事实把 `Lset c` 放入 `Lset (sucV c)`，再沿 `sucV c ∈ lam` 使用单调性，便把这条隶属提升为 `Lset c ∈ K`。稍后把同一引理应用于 `sucV c`，并再用一次后继封闭，即可得到 `Lset (sucV c) ∈ K`；这才是在 `c` 行所需的可定义幂集见证。
<!--ja-->
`c ∈ lam` なら、後者閉包から `sucV c ∈ lam` が得られる。後者段階についての標準的な事実により `Lset c ∈ Lset (sucV c)` となり、さらに `sucV c ∈ lam` に沿う単調性によって、この所属を `Lset c ∈ K` へ持ち上げられる。後では同じ補題を `sucV c` に適用し、後者閉包をもう一度用いて `Lset (sucV c) ∈ K` を得る。これが `c` の行に必要な定義可能冪集合の証人である。
<!--/-->

```agda
    Lset∈K : (c : V ℓ) → ⟨ c ∈ lam ⟩ → ⟨ Lset c ∈ K ⟩
    Lset∈K c c∈ = Lset-mono {α = lam} {β = sucV c} (succ c c∈) (Lset∈suc c)
```

<!--en-->
The numeral-bound theorem first places the underlying set of the model numeral in `K`. The projection equation `numeralL-fst` identifies that set with the ambient von Neumann numeral `# k`, and transport yields `# k ∈ K`. Hence all ten numeral witnesses satisfy the same bound as the hierarchy table.
<!--zh-->
数码限界定理先把模型数码的底层集合放入 `K`。投影等式 `numeralL-fst` 把该集合认同于周遭的 von Neumann 数码 `# k`，沿此搬运便得 `# k ∈ K`。因此，十个数码见证与层级表满足同一个界。
<!--ja-->
数項の有界性定理は、まず模型の数項の基礎集合を `K` に入れる。射影等式 `numeralL-fst` がその集合を周囲のフォン・ノイマン数項 `# k` と同一視し、それに沿う輸送から `# k ∈ K` が得られる。したがって十個の数項の証人は、階層表と同じ境界を満たす。
<!--/-->

```agda
    num∈K : (k : ℕ) → ⟨ # k ∈ K ⟩
    num∈K k = subst (λ u → ⟨ u ∈ K ⟩) (numeralL-fst k) (B.num∈λ k)
```

<!--en-->
Four sets are named: the level `Lset p`, the ordinal `p`, the stage `Lset lam`, and the hierarchy table at `p`, each in the appropriate carrier.
<!--zh-->
四个集合被命名：层 `Lset p`、序数 `p`、层 `Lset lam`、以及 `p` 处的层级表，各处于相应的载体中。
<!--ja-->
四つの集合に名前が与えられる。段階 `Lset p`、順序数 `p`、段階 `Lset lam`、そして `p` における階層の表で、それぞれ適切な台の中にある。
<!--/-->

```agda
  aS pS zS F : S
  aS = LsetS p op
  pS = p , At.cL p op
  zS = LsetS lam ord
  F = At.hier p op
```

<!--en-->
The environment `E` now records the complete fourteen-slot assignment. From front to back it contains the numerals `0` through `9`, the genuine hierarchy table at `p`, the intended value `Lset p`, the index `p`, and the common bound `Lset lam`. This is exactly the slot order in which `inner` reads its data.
<!--zh-->
环境 `E` 现在记录完整的十四槽位赋值。从前到后依次是数码 `0` 至 `9`、`p` 处的真实层级表、预定值 `Lset p`、索引 `p`，以及公共界 `Lset lam`。这恰是 `inner` 读取数据的槽位次序。
<!--ja-->
環境 `E` はここで、十四のスロットへの完全な割り当てを記録する。先頭から順に、数項 `0` から `9`、`p` における実際の階層表、意図した値 `Lset p`、添字 `p`、そして共通の境界 `Lset lam` が並ぶ。これは `inner` がデータを読むスロットの順序とちょうど一致する。
<!--/-->

```agda
  E : S ^ 14
  E = nn 0 ∷ nn 1 ∷ nn 2 ∷ nn 3 ∷ nn 4 ∷ nn 5 ∷ nn 6 ∷ nn 7 ∷ nn 8 ∷ nn 9
    ∷ F ∷ aS ∷ pS ∷ zS ∷ []
```

<!--en-->
The tag hypothesis identifies each of the first four tag slots with its own numeral, definitionally.
<!--zh-->
标签假设定义性地把前四个标签槽位各自等同于自己的数码。
<!--ja-->
タグの仮定は、最初の四つのタグのスロットを、それぞれみずからの数項と定義的に同一視する。
<!--/-->

```agda
  tg : Tags E N14
  tg zero = refl
  tg (suc zero) = refl
  tg (suc (suc zero)) = refl
  tg (suc (suc (suc zero))) = refl
```

<!--en-->
The next five cases verify the tag slots at indices four through eight. Each lookup reduces to the corresponding entry of `E`, so these slots are definitionally the numerals `4` through `8`.
<!--zh-->
接下来的五个情形验证索引四至八处的标签槽位。每次查找都化简为 `E` 中相应的条目，因此这些槽位按定义分别是数码 `4` 至 `8`。
<!--ja-->
続く五つの場合は、添字 4 から 8 までのタグのスロットを検証する。各参照は `E` の対応する項目へ簡約されるので、これらのスロットは定義上それぞれ数項 `4` から `8` である。
<!--/-->

```agda
  tg (suc (suc (suc (suc zero)))) = refl
  tg (suc (suc (suc (suc (suc zero))))) = refl
  tg (suc (suc (suc (suc (suc (suc zero)))))) = refl
  tg (suc (suc (suc (suc (suc (suc (suc zero))))))) = refl
  tg (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) = refl
```

<!--en-->
The final case verifies the tenth tag slot, at index nine, as the numeral `9`. All ten equations required by `Tags E N14` are therefore established by computation on the explicit environment.
<!--zh-->
最后一个情形验证第十个标签槽位，也就是索引九处的槽位，为数码 `9`。由此，`Tags E N14` 要求的十条等式全都由显式环境上的计算得到。
<!--ja-->
最後の場合は、添字 9 にある十番目のタグのスロットが数項 `9` であることを確かめる。これで `Tags E N14` が要求する十個の等式が、明示された環境上の計算によってすべて得られた。
<!--/-->

```agda
  tg (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))) = refl
```

<!--en-->
For each member `c` of the ordinal `p`, the supply lemma places four objects in `K`: the satisfaction graph, the code set, the environment tower, and the next level `Lset (sucV c)`. The chain `c ∈ p ∈ lam` and the transitivity of `lam` first place `c` in `lam`, making the adequacy witnesses available.
<!--zh-->
对序数 `p` 的每个成员 `c`，供给引理把四个对象放入 `K`：满足图、码集、环境塔与下一层 `Lset (sucV c)`。链 `c ∈ p ∈ lam` 与 `lam` 的传递性先把 `c` 放入 `lam`，从而使充分性见证可用。
<!--ja-->
順序数 `p` の各要素 `c` に対して、供給の補題は四つの対象、すなわち充足のグラフ、コードの集合、環境の塔、次の段階 `Lset (sucV c)` を `K` に入れる。連鎖 `c ∈ p ∈ lam` と `lam` の推移性によって、まず `c` が `lam` に属することが分かり、妥当性の証人を使えるようになる。
<!--/-->

```agda
  sup : (c : V ℓ) (oc : IsOrd c) → ⟨ c ∈ p ⟩ → Supply K c oc
  sup c oc c∈ = w .snd .snd .fst , ( w .snd .fst , ( w .snd .snd .snd , Lset∈K (sucV c) (succ c c∈λ) ))
    where
    c∈λ : ⟨ c ∈ lam ⟩
    c∈λ = tr p c p∈λ c∈
```

<!--en-->
The witness for each `c` is read from the adequacy data, closing the supply for every member of the ordinal.
<!--zh-->
每个 `c` 的见证从充分性数据读取，为该序数的每个成员完成供给。
<!--ja-->
それぞれの `c` の証人は妥当性のデータから読まれ、順序数のすべての要素のための供給が閉じられる。
<!--/-->

```agda
    w = wit c c∈λ oc
```

<!--en-->
The inner formula now holds at `E`. The pins writer supplies its numeral conjunct. For the hierarchy conjunct, `hier-complete` uses the ordinality of `p`, the reflexive identification of the proposed value with `Lset p`, the exact hierarchy table supplied by `hierL-spec`, and the row-by-row supply derived above from adequacy. No strengthened stage hypothesis is used here.
<!--zh-->
内层公式现在在 `E` 处成立。pins 写引理给出其中的数码合取项。对于层级合取项，`hier-complete` 使用 `p` 的序数性、候选值与 `Lset p` 的自反等同、`hierL-spec` 给出的精确层级表，以及上文从充分性逐行导出的供给。这里没有使用任何加强的层假设。
<!--ja-->
内側の論理式はここで `E` において成り立つ。pins の書き補題が数項の連言項を与える。階層の連言項については、`hier-complete` が `p` の順序数性、候補となる値と `Lset p` の反射的な同一視、`hierL-spec` が与える正確な階層表、そして妥当性から上で各行について導いた供給を用いる。ここでは強化された段階仮定を使わない。
<!--/-->

```agda
  hm : ⟨ E ⊨ inner ⟩
  hm = inner-in E (PinsRead.pins-in N14 E tg)
         (HierRead.hier-complete aa pp ff zz N14 E tg op refl (hierL-spec p (At.cL p op) op) sup)
```

<!--en-->
The adequacy witness at `p` places the underlying set of the genuine hierarchy table `F` in the common bound `K`. This supplies the membership proof needed to introduce `F` as the outermost bounded witness.
<!--zh-->
`p` 处的充分性见证把真实层级表 `F` 的底层集合放入公共界集 `K`。这给出把 `F` 引入为最外层有界见证所需的隶属证明。
<!--ja-->
`p` における妥当性の証人は、実際の階層表 `F` の基礎集合を共通の境界集合 `K` に入れる。これにより、`F` を最も外側の有界な証人として導入するために必要な所属の証拠が得られる。
<!--/-->

```agda
  FK : ⟨ fst F ∈ K ⟩
  FK = wit p p∈λ op .fst
```

<!--en-->
It remains to hide the table and numeral data behind the eleven bounded existentials. The outermost introduction uses the genuine hierarchy table `F`, whose membership in `K` was just proved. The next two introductions use the numerals `9` and `8`, each with its membership in the same common bound.
<!--zh-->
还需把层级表与数码数据隐藏在十一个有界存在量词之后。最外层的引入使用真实层级表 `F`，其属于 `K` 已在上一步证明。接下来的两次引入使用数码 `9` 与 `8`，并各自附上属于同一公共界的证明。
<!--ja-->
残る仕事は、階層表と数項のデータを十一個の有界存在量化子の内側へ隠すことである。最も外側の導入には実際の階層表 `F` を用い、その `K` への所属は直前に示した。続く二回の導入には数項 `9` と `8` を用い、それぞれが同じ共通の境界に属するという証拠を添える。
<!--/-->

```agda
  h3 : ⟨ (aS ∷ pS ∷ zS ∷ []) ⊨ three ⟩
  h3 =
    wrap-in s4 (aS ∷ pS ∷ zS ∷ []) F FK (
    wrap-in s5 (F ∷ aS ∷ pS ∷ zS ∷ []) (nn 9) (num∈K 9) (
    wrap-in s6 (nn 9 ∷ F ∷ aS ∷ pS ∷ zS ∷ []) (nn 8) (num∈K 8) (
```

<!--en-->
The same introduction rule inserts the numerals `7` through `3`. Their membership proofs all come from `num∈K`, so every quantifier is witnessed inside `K = Lset lam`; no witness is taken from an unbounded ambient search.
<!--zh-->
同一条引入规则继续插入数码 `7` 至 `3`。它们的隶属证明全都来自 `num∈K`，所以每个量词的见证都位于 `K = Lset lam` 内；这里没有从无界的周遭搜索中取得见证。
<!--ja-->
同じ導入規則によって数項 `7` から `3` までを挿入する。それらの所属証明はすべて `num∈K` から得られるので、各量化子の証人は `K = Lset lam` の内部にある。周囲で非有界な探索を行って証人を得ているわけではない。
<!--/-->

```agda
    wrap-in s7 (nn 8 ∷ nn 9 ∷ F ∷ aS ∷ pS ∷ zS ∷ []) (nn 7) (num∈K 7) (
    wrap-in s8 (nn 7 ∷ nn 8 ∷ nn 9 ∷ F ∷ aS ∷ pS ∷ zS ∷ []) (nn 6) (num∈K 6) (
    wrap-in s9 (nn 6 ∷ nn 7 ∷ nn 8 ∷ nn 9 ∷ F ∷ aS ∷ pS ∷ zS ∷ []) (nn 5) (num∈K 5) (
    wrap-in s10 (nn 5 ∷ nn 6 ∷ nn 7 ∷ nn 8 ∷ nn 9 ∷ F ∷ aS ∷ pS ∷ zS ∷ []) (nn 4) (num∈K 4) (
    wrap-in s11 (nn 4 ∷ nn 5 ∷ nn 6 ∷ nn 7 ∷ nn 8 ∷ nn 9 ∷ F ∷ aS ∷ pS ∷ zS ∷ []) (nn 3) (num∈K 3) (
```

<!--en-->
Finally the numerals `2`, `1`, and `0` are inserted. After the last introduction, the extended environment is exactly `E`, where `hm` already proves `inner`. The nested introductions therefore establish satisfaction of the eleven-times-wrapped formula at the visible triple `(Lset p,p,Lset lam)`.
<!--zh-->
最后插入数码 `2`、`1` 与 `0`。末次引入后的扩展环境恰好是 `E`，而 `hm` 已证明 `inner` 在该环境中成立。因此，这串嵌套引入证明十一重包裹公式在可见三元组 `(Lset p,p,Lset lam)` 处得到满足。
<!--ja-->
最後に数項 `2`、`1`、`0` を挿入する。最後の導入後に得られる拡張環境はちょうど `E` であり、そこで `hm` がすでに `inner` を証明している。したがって、入れ子になった導入によって、十一回包まれた論理式が表に残る三つ組 `(Lset p,p,Lset lam)` で満たされることが示される。
<!--/-->

```agda
    wrap-in s12 (nn 3 ∷ nn 4 ∷ nn 5 ∷ nn 6 ∷ nn 7 ∷ nn 8 ∷ nn 9 ∷ F ∷ aS ∷ pS ∷ zS ∷ []) (nn 2) (num∈K 2) (
    wrap-in s13 (nn 2 ∷ nn 3 ∷ nn 4 ∷ nn 5 ∷ nn 6 ∷ nn 7 ∷ nn 8 ∷ nn 9 ∷ F ∷ aS ∷ pS ∷ zS ∷ []) (nn 1) (num∈K 1) (
    wrap-in inner (nn 1 ∷ nn 2 ∷ nn 3 ∷ nn 4 ∷ nn 5 ∷ nn 6 ∷ nn 7 ∷ nn 8 ∷ nn 9 ∷ F ∷ aS ∷ pS ∷ zS ∷ []) (nn 0) (num∈K 0)
      hm))))))))))
```

<!--en-->
The erasure inverse says that embedding `erased` into the constructible constant domain recovers `three`. Transporting `h3` along the inverse direction therefore yields satisfaction of `embed erased` at the same three-slot environment. Only the constant domain has changed; the eleven bounded witnesses and their common bound remain the ones already constructed.
<!--zh-->
擦除逆等式说明，把 `erased` 嵌入可构造常元域便恢复 `three`。因此，沿该等式的反向搬运 `h3`，可得 `embed erased` 在同一三槽位环境中的满足。改变的只有常元域；十一个有界见证及其公共界仍是刚才构造的那些。
<!--ja-->
消去の逆等式は、`erased` を構成可能な定数域へ埋め込むと `three` が復元されることを述べる。したがって、その等式の逆向きに `h3` を輸送すれば、同じ三スロットの環境における `embed erased` の充足が得られる。変わるのは定数域だけであり、十一個の有界証人とその共通の境界は、すでに構成したもののままである。
<!--/-->

```agda
  hφ : ⟨ (aS ∷ pS ∷ zS ∷ []) ⊨ embed erased ⟩
  hφ = subst (λ ψ → ⟨ (aS ∷ pS ∷ zS ∷ []) ⊨ ψ ⟩) (sym (Cnt.erase-inv three count-three)) h3
```

<!--en-->
Completeness is assembled from the two conjuncts: the ordinality atom holds by `ord-in`, and the erased witness formula holds by the transport just proved. The reading lemma transfers both to the ambient satisfaction.
<!--zh-->
完备性由两个合取项组装：序数性原子由 `ord-in` 成立，擦除后的见证公式由刚才的传输成立。读取引理把二者传入外围满足。
<!--ja-->
完全性は二つの連言項から組み立てられる。順序数性の原子は `ord-in` によって成り立ち、消去後の証人の論理式は証明されたばかりの輸送によって成り立つ。読みの補題が両方を周囲の充足の中へ移す。
<!--/-->

```agda
  complete : ⟨ (Lset p ∷ p ∷ Lset lam ∷ []) ⊨ₚ levelFo ⟩
  complete = subst ⟨_⟩ (read Δ₀-levelFo (aS ∷ pS ∷ zS ∷ [])) (ord-in aS pS zS op , hφ)
```
</div>
</details>

<!--en-->
The completeness theorem states the precise existence direction available here. If `γ` is adequate and contains the ordinal `p`, then the triple `(Lset p,p,Lset γ)` satisfies `levelFo`. Later, `CondensationTransfer` places unbounded existential quantifiers around this Δ₀ core, carries all three coordinates through elementarity, and uses soundness to recognize the transported first coordinate as the corresponding constructible stage. The theorem makes no claim that an arbitrary third coordinate works or is uniquely determined.
<!--zh-->
完备性定理给出这里能够证明的精确存在方向。若 `γ` 充分并含有序数 `p`，则三元组 `(Lset p,p,Lset γ)` 满足 `levelFo`。后续的 `CondensationTransfer` 在这个 Δ₀ 核心之外加入无界存在量词，经初等性搬运三个坐标，再用可靠性把搬运后的第一坐标识别为相应的可构造层。该定理并未断言任意第三坐标都可使用，也未断言第三坐标由公式唯一确定。
<!--ja-->
完全性定理は、ここで得られる存在方向を正確に述べる。`γ` が十分で順序数 `p` を含むなら、三つ組 `(Lset p,p,Lset γ)` は `levelFo` を満たす。後の `CondensationTransfer` では、この Δ₀ の核の外側に非有界存在量化子を加え、三つの座標すべてを初等性によって移し、健全性を用いて移された第一座標を対応する構成可能な段階として認識する。この定理は、任意の第三座標が使えるとも、第三座標が論理式によって一意に定まるとも主張しない。
<!--/-->

```agda
level-complete : (γ : V ℓ) → Adequate γ → (p : V ℓ) → IsOrd p → ⟨ p ∈ γ ⟩
               → ⟨ (Lset p ∷ p ∷ Lset γ ∷ []) ⊨ₚ levelFo ⟩
level-complete γ ad p op p∈ = Complete.complete γ ad p op p∈
```
