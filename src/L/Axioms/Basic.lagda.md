<!--en-->
# The basic axioms

How does a set-producing operation lift into the constructible universe? A set belongs to `L` when it can be presented as a definable subset of an ordinal stage `Lset σ`. The chapter repeatedly finds one ordinal stage containing the needed inputs, writes a formula over that stage whose extension is the desired set, and proves the extensional equation in the surrounding hierarchy.

The closure lemma `defSet→isL` completes this pattern. Given an ordinal `σ` and the mere existence of a unary formula whose extension is `x`, `𝒟ₒ-intro` recognizes `x` as a definable subset of `Lset σ`, and `𝒟ₒ→isL` places it in `L`. The identity `Lset (sucV σ) ≡ 𝒟ₒ (Lset σ)` explains the stage calculation: the next stage consists exactly of the definable subsets of the present one. The packaged sets `LsetS` and `𝒟ₒS` provide these two sets as elements of the carrier `S`.

This method constructs the empty set, unordered pairs, and unions inside `L`. Extensionality follows by using transitivity to extend agreement from constructible members to all surrounding members; regularity instead restricts the hierarchy's accessibility proof recursively. When two inputs need a common stage, `bound2` supplies a common strict upper bound without comparing their original stages.
<!--zh-->
# 基本公理

造集合运算怎样提升到可构造宇宙中？一个集合属于 `L`，当且仅当它能呈现为某个序数层 `Lset σ` 的可定义子集。本章反复使用同一思路：找出一个容纳所需输入的序数层，在该层上写出外延为目标集合的公式，再在周遭集合层级中证明相应的外延等式。

闭包引理 `defSet→isL` 完成这一过程。给定序数 `σ`，若仅仅存在一条外延为 `x` 的一元公式，`𝒟ₒ-intro` 便认出 `x` 是 `Lset σ` 的可定义子集，`𝒟ₒ→isL` 再把它放入 `L`。恒等式 `Lset (sucV σ) ≡ 𝒟ₒ (Lset σ)` 说明了层计算：下一层恰由当前层的可定义子集组成。打包后的集合 `LsetS` 与 `𝒟ₒS` 把这两个集合给成载体 `S` 的元素。

本章以此在 `L` 中构造空集、无序对与并。外延性利用传递性，把关于可构造成员的一致性推广到所有周遭成员；正则性则递归限制层级的可及性证明。若两个输入需要公共层，`bound2` 会给出共同的严格上界，而无须比较原来的两层。
<!--ja-->
# 基本公理

集合を作る演算を構成可能宇宙へ移すには、どうすればよいでしょうか。集合が `L` に属するとは、ある順序数段階 `Lset σ` の定義可能部分集合として表示できることです。本章では、必要な入力を含む一つの順序数段階を見つけ、その段階上で目的の集合を外延にもつ論理式を書き、周囲の階層で外延的な等式を証明する、という方法を繰り返します。

閉包補題 `defSet→isL` がこの方法を完成させます。順序数 `σ` と、外延が `x` である一変数論理式の単なる存在が与えられると、`𝒟ₒ-intro` は `x` を `Lset σ` の定義可能部分集合として認識し、`𝒟ₒ→isL` はそれを `L` に入れます。恒等式 `Lset (sucV σ) ≡ 𝒟ₒ (Lset σ)` は段階の計算を説明します。次の段階は、現在の段階の定義可能部分集合全体にちょうど一致します。`LsetS` と `𝒟ₒS` はこの二つの集合を台 `S` の要素としてまとめます。

この方法で空集合、非順序対、和集合を `L` の中に構成します。外延性では推移性により構成可能な要素についての一致を周囲のすべての要素へ広げますが、正則性では階層の可到達性の証明を再帰的に制限します。二つの入力に共通段階が必要なとき、`bound2` は元の段階を比較せずに共通の厳密上界を与えます。
<!--/-->

<!--en-->
The setting fixes one universe level `ℓ` and works in the cumulative hierarchy `V` at that level. Everything in this chapter is constructive: no excluded middle, no resizing, no choice. The carrier on which the axioms will be proved is the type of sets of `V` together with a constructibility certificate `isL`, and every claim below is established from the ambient hierarchy alone.
<!--zh-->
设定固定一个宇宙层级 `ℓ`，并在该层级的累积层级 `V` 中工作。本章一切都是构造性的：不假设排中律、resize 或选择。公理将据以证明的载体，是 `V` 的集合连同可构造性证书 `isL` 组成的类型，而下文每条主张都仅凭周遭集合层级建立。
<!--ja-->
設定は宇宙レベル `ℓ` を一つ固定し、そのレベルの累積階層 `V` の中で作業します。本章はすべて構成的であり、排中律もサイズ変更も選択公理も仮定しません。公理が証明される台は、`V` の集合と構成可能性の証明書 `isL` の対からなる型であり、以下の主張はすべて周囲の階層だけから立証されます。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude

module L.Axioms.Basic {ℓ : Level} where

open import FOL.Syntax using ( Formula; var; con; _≐_; _∈̇_; _∨̇_; ⊤̇; ⊥̇; ∃̇∈ )
```

<!--en-->
The defining step of the closure pattern is expressed in a first-order language. Its formulas sit over a structure's small index type, with equality and membership as the atomic predicates, and with disjunction and bounded existential quantification available; these are the operations used to form definable subsets. Two ambient facts about passing from a structure to a substructure will matter: a path between two elements of a restriction is already a path between their underlying sets, and that is the direction the inherited axioms will exploit.
<!--zh-->
闭包模式的刻出步骤在一阶语言中进行。它的公式以某结构的小索引类型为载体，原子谓词是相等与隶属，并备有析取与有界存在量词；这正是可定义性算子所用的构造。关于从结构过渡到子结构，有两条周遭集合层级的事实将发挥作用：限制中两个元素之间的路径已经是其底层集合之间的路径，而继承来的公理要利用的正是这一方向。
<!--ja-->
閉包パターンの切り出しのステップは一階の言語の中で行われます。その論理式は構造の小さな添字型の上にあり、等式と所属が原子的な述語で、選言と有界存在量化が使えます。これがまさに定義可能性の演算子が消費するものです。構造から部分構造への移行について、後で効いてくる周囲の事実が二つあります。制限の中の二つの要素の間のパスは、すでに基底の集合の間のパスであり、継承される公理が利用するのはこの向きです。
<!--/-->

```agda
open import FOL.ZFStructure using ( ↾-reflects; module hPropStructure )
import FOL.ZFModel
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ; extensionalV; regularityV )
open import V.Model {ℓ}
  using ( empty-spec; pair-spec; union-spec; self∈sucV; ∈sucV-elim
```

<!--en-->
Each construction to be lifted already satisfies its membership law in the ambient hierarchy: the empty set has no members, every member of an unordered pair is one of its two entries, and union has its exact two-way classification. These ambient laws, proved once in the hierarchy, serve as the standards against which the formulas carved below are checked by extensionality; they are inherited, not re-derived. Two further ambient facts enter the computations: membership in the successor `sucV σ` splits into members of `σ` and `σ` itself, and the singleton is identified with the pair `⁅ x , x ⁆`. The Kuratowski code `pr` of an ordered pair will have its stage placement computed from unordered pairs.
<!--zh-->
待提升的每个构造在周遭集合层级中已满足其成员律：空集没有成员，无序对的每个成员是两个条目之一，并集有精确的双向刻画。这些周遭定律在层级中证明一次，便充当下文公式以外延性接受检验的标准；它们被继承，而非重证。计算中还要用到两条周遭集合层级的事实：属于后继 `sucV σ` 可分成「属于 `σ`」与「就是 `σ`」两种情形，而单点集与对 `⁅ x , x ⁆` 被指认等同。有序对的 Kuratowski 码 `pr` 落在哪个层，将由无序对计算得出。
<!--ja-->
持ち上げる対象となる各構成は、周囲の階層ですでに所属の法則を満たしています。空集合は元をひとつももたず、非順序対のすべての元は二つの項のいずれかであり、和集合は正確な双方向の特徴づけをもちます。これらの周囲の法則は階層で一度証明され、後で切り出される論理式を外延性で検査するときの基準となります。再証明されるのではなく、継承されるのです。計算にはさらに二つの周囲の事実が入ります。後者 `sucV σ` への所属は「`σ` の要素である」場合と「`σ` そのものである」場合に分かれること、そして一元集合が対 `⁅ x , x ⁆` と同一視されることです。順序対のクラトフスキー符号 `pr` がどの段階に置かれるかは、非順序対から計算されます。
<!--/-->

```agda
        ; pair-singleton )
open import V.Coding {ℓ} using ( pr )
open import L.Definability {ℓ} using ( module DefOf )
open import L.Constructible {ℓ}
  using ( 𝒮ʟ; isL; isL-trans; IsOrd; Lset; Lset-layer
```

<!--en-->
On the constructible side, `Lset` indexes stages by sets, `IsOrd` records which indices are ordinals, and `isL` is the class of constructible sets, transitive by `isL-trans`. The definable powerset of a stage is `𝒟ₒ`; `𝒟ₒ-intro` recognizes a definable subset from a formula and an extensional equation, and `Lset-in`, `Lset-out`, `Lset⊆𝒟ₒ`, `Lset-mono` and `Lset→isL` let membership in a stage be converted, carried upward along a larger stage, and read as a constructibility certificate. Stage transitivity is `layer-trans`.
<!--zh-->
可构造一侧提供层体系。`Lset` 以集合为索引给出各层，`IsOrd` 是序数性证书，`isL` 是可构造集的类，`isL-trans` 使其传递。层的可定义幂集是 `𝒟ₒ`；`𝒟ₒ-intro` 从一条公式加一条外延等式识别出可定义子集，而 `Lset-in`、`Lset-out`、`Lset⊆𝒟ₒ`、`Lset-mono` 与 `Lset→isL` 让层中的隶属得以转换、沿更大的层向上搬运、并被读成可构造性证书。层的传递性是 `layer-trans`。
<!--ja-->
構成可能な側は、塔とその簿記を供給します。`Lset` は集合を添字として段階を与え、`IsOrd` は順序数性の証明書、`isL` は構成可能集合のクラスで、`isL-trans` により推移的です。段階の定義可能冪集合は `𝒟ₒ` です。`𝒟ₒ-intro` が論理式と外延的な等式から定義可能部分集合を認識し、`Lset-in`、`Lset-out`、`Lset⊆𝒟ₒ`、`Lset-mono`、`Lset→isL` は段階への所属の変換、より大きな段階に沿った持ち上げ、構成可能性の証明書としての読み替えを可能にします。段階の推移性は `layer-trans` です。
<!--/-->

```agda
        ; layer-trans; 𝒟ₒ; 𝒟ₒ-intro; Lset-in; Lset-out; Lset⊆𝒟ₒ
        ; Lset-mono; Lset→isL )
open import L.Ordinal {ℓ} using ( ∅-ord; suc-ord; bound2 )

open import Cubical.Data.FinData using ( zero; suc )
open import Cubical.Data.Sum using ( inl; inr )
```

<!--en-->
Three ordinal facts control the stages: the empty set is an ordinal, the successor of an ordinal is an ordinal, and `bound2` returns an ordinal strictly containing each of two given ordinals. Pairing uses the last result to place two constructible arguments in one common stage without comparing their original stages or choosing a maximum. Finite index types then describe finite images inside that stage, while binary sums express the disjunctions that define them.
<!--zh-->
三个序数事实控制层：空集是序数，序数的后继仍是序数，而 `bound2` 对两个给定序数返回一个严格包含二者的序数。配对用最后一条把两个可构造实参放进同一层，无须比较原层或选取最大者。有穷索引类型随后描述该层中的有穷像，二元和则表达定义这些像所用的析取。
<!--ja-->
段階を制御する順序数の事実は三つです。空集合は順序数であり、順序数の後者も順序数であり、`bound2` は二つの順序数をそれぞれ真に含む順序数を返します。対の構成では最後の結果により、もとの段階を比較したり最大のものを選んだりせず、二つの構成可能な実引数を一つの共通段階へ置きます。有限添字型はその段階内の有限像を記述し、二つの型の和はそれらを定義する論理和を表します。
<!--/-->

```agda
open import Cubical.Functions.Logic using ( ⇔toPath )
open import Cubical.Foundations.Prelude using ( isPropIsContr )
open import Cubical.Induction.WellFounded using ( Acc; acc; WellFounded )
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
```

<!--en-->
Membership in the ambient hierarchy is proposition-valued, but the presentation embedding has propositional fibers. Consequently `∈-asFiber` converts a given membership proof into an actual index of the small presentation together with a path back to the member. Thus from `⟨ x ∈ Lset σ ⟩` one obtains `m : ⟪ Lset σ ⟫` with `⟪ Lset σ ⟫↪ m ≡ x`, allowing the formula to name that member by a constant. The output is data because the corresponding fiber is itself a proposition; there is no additional outer truncation to eliminate at this step.
<!--zh-->
周遭集合层级中的隶属取值于命题，而呈现嵌入的纤维也是命题。因此，`∈-asFiber` 能把给定的隶属证明转换成小呈现中的实际索引，连同回到该成员的路径。具体地，从 `⟨ x ∈ Lset σ ⟩` 得到 `m : ⟪ Lset σ ⟫` 与 `⟪ Lset σ ⟫↪ m ≡ x`，公式因而能用常元指名该成员。这里直接得到数据，是因为相应纤维自身为命题；这一步没有另一个外层截断需要消去。
<!--ja-->
周囲の階層の所属は命題値であり、提示の埋め込みのファイバーも命題です。そのため `∈-asFiber` は、与えられた所属の証明を小さな提示の実際の添字と、その要素へ戻るパスに変換します。すなわち `⟨ x ∈ Lset σ ⟩` から `m : ⟪ Lset σ ⟫` と `⟪ Lset σ ⟫↪ m ≡ x` が得られ、論理式はこの要素を定数で名指せます。対応するファイバー自体が命題なのでデータを直接得られるのであり、この段階で消去すべき別の外側の切り詰めはありません。
<!--/-->

```agda
open PT using ( ∣_∣₁; ∥_∥₁; squash₁ )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_; sett )
open import Cubical.HITs.CumulativeHierarchy.Properties
  using ( _∈ₛ_; ∈∈ₛ; ∈-asFiber; extensionality; _⊆_; ⟪_⟫; ⟪_⟫↪ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
```

<!--en-->
The ambient sets this chapter needs come with their exact membership characterizations: `∅-empty` for the empty set, `pairing-ax` for the unordered pair `⁅_,_⁆` and its singleton variant, and `union-ax` and `⋃_` for the union. These are the hierarchy's own classification results, and they supply both directions of each membership law, so the definable subsets carved below can be checked against them by extensionality. The successor operation `sucV` supplies the next stage's index.
<!--zh-->
本章所需的周遭集合都带有精确的隶属刻画：空集配 `∅-empty`，无序对 `⁅_,_⁆` 及其单点变体配 `pairing-ax`，并配 `union-ax` 与 `⋃_`。这些是层级自己的分类结果，给出每条成员律的两个方向，故下文刻出的可定义子集可以对照它们以外延性检验。后继运算 `sucV` 给出下一层的索引。
<!--ja-->
本章で必要な周囲の集合は、それぞれ正確な所属の特徴づけを伴います。空集合には `∅-empty`、非順序対 `⁅_,_⁆` とその一元の変種には `pairing-ax`、和集合には `union-ax` と `⋃_` です。これらは階層そのものの分類結果であり、所属の法則の両方向を与えるので、後で切り出される定義可能部分集合は、これらと突き合わせて外延性で検査できます。後者演算 `sucV` が次の段階の添字を供給します。
<!--/-->

```agda
  using ( ∅; ∅-empty; ⁅_,_⁆; ⁅_⁆s; pairing-ax; ⋃_; union-ax
        ; module InfinitySet )
open InfinitySet using ( sucV )

open hPropStructure 𝒮ʟ
```

<!--en-->
The semantic side is fixed once. Truth values are the propositions at level `ℓ-suc ℓ`, so a formula's interpretation lands in an ordinary type former, and reading the restricted structure through the proposition-valued semantics gives the structural membership `∈ˢ` and the bracket notation `⟨_⟩` for the type underlying a proposition. A realizing set is then an element of the carrier `S`, a set with its constructibility certificate, together with the equation stating which specification its membership realizes; this is the type `SetOf Q`. The principle `setOf-unique`, which turns one realizing set into contractibility data, is what reduces every remaining axiom field in this chapter to a bare existence problem.
<!--zh-->
语义一侧一次性确定。真值取层级 `ℓ-suc ℓ` 上的命题，故公式的解释落在普通的类型构造中；把限制结构经命题值语义读取，便得到结构成员关系 `∈ˢ`，以及取命题底层类型的括号记法 `⟨_⟩`。一个实现集合于是是载体 `S` 的元素，即带可构造性证书的集合，连同说明其成员关系实现哪条规格的等式；这就是类型 `SetOf Q`。原理 `setOf-unique` 把一个实现集合变成收缩性数据，正是它把本章余下每条公理字段化归为纯粹的存在问题。
<!--ja-->
意味論の側は一度だけ確定します。真理値はレベル `ℓ-suc ℓ` の命題なので、論理式の解釈は通常の型構成に落ちます。制限された構造を命題値の意味論を通して読むと、構造的な所属 `∈ˢ` と、命題の基礎型を取る括弧の記法 `⟨_⟩` が得られます。実現する集合とは、台 `S` の要素、すなわち構成可能性の証明書を添えた集合に、その所属がどの仕様を実現するかを言う等式を添えたものです。これが型 `SetOf Q` です。一つの実現集合を可縮性のデータへ変える原理 `setOf-unique` が、本章の残りの各公理フィールドを純粋な存在の問題へ帰着させます。
<!--/-->

```agda

module ModelL = FOL.ZFModel 𝒮ʟ
open ModelL using ( SetOf; setOf-unique )
```

<!--en-->
## Definable subsets are constructible

The stage `Lset (sucV σ)` is a union indexed by `δ ∈ sucV σ`. Since `σ ∈ sucV σ`, the set `𝒟ₒ (Lset σ)` is one of the sets being unioned. Therefore every element of `𝒟ₒ (Lset σ)` belongs to `Lset (sucV σ)`. When `σ` is ordinal, so is its successor, and this stage membership yields an `isL` certificate.
<!--zh-->
## 可定义子集是可构造的

层 `Lset (sucV σ)` 是以 `δ ∈ sucV σ` 为指标的一族集合的并。由于 `σ ∈ sucV σ`，集合 `𝒟ₒ (Lset σ)` 是其中一个被并集合，所以它的每个元素都属于 `Lset (sucV σ)`。若 `σ` 是序数，其后继也是序数，这条层隶属便给出 `isL` 证书。
<!--ja-->
## 定義可能部分集合は構成可能である

段階 `Lset (sucV σ)` は `δ ∈ sucV σ` で添字づけられた集合族の和です。`σ ∈ sucV σ` なので、集合 `𝒟ₒ (Lset σ)` は和を取られる集合の一つです。したがって、そのすべての要素は `Lset (sucV σ)` に属します。`σ` が順序数ならその後者も順序数であり、この段階への所属から `isL` の証明書が得られます。
<!--/-->

<!--en-->
The lemma `𝒟ₒ→isL` takes an ordinal `σ` with its ordinality certificate `oσ`, a set `x`, and a proof that `x` belongs to the definable power set of the stage at `σ`; it concludes that `x` is constructible. The proof places `x` one level up. Because `σ` is a member of its own successor `sucV σ`, the inclusion `Lset-in` carries membership in `𝒟ₒ (Lset σ)` into membership in the stage `Lset (sucV σ)`, whose index is an ordinal by `suc-ord oσ`. One application of `Lset→isL` then converts that stage membership into the certificate `isL x`. The truncated hypothesis is used as given: it is passed straight into `Lset-in`, whose conclusion is truncated in the same way, so no witness of constructibility is ever extracted or chosen.
<!--zh-->
引理 `𝒟ₒ→isL` 接收一个序数 `σ` 及其序数性证书 `oσ`、一个集合 `x`、以及「`x` 属于 `σ` 处层的可定义幂集」的证明，结论是 `x` 可构造。证明把 `x` 抬高一级。由于 `σ` 属于自身的后继 `sucV σ`，包含关系 `Lset-in` 把「属于 `𝒟ₒ (Lset σ)`」变成「属于层 `Lset (sucV σ)`」，而该层的索引经 `suc-ord oσ` 是序数。再用一次 `Lset→isL`，就把这条层隶属转成证书 `isL x`。那条截断的假设按原样使用：它被直接送入 `Lset-in`，而后者的结论以同样方式截断，因此全程没有提取或选定任何可构造性见证。
<!--ja-->
補題 `𝒟ₒ→isL` は、順序数 `σ` とその順序数性の証明書 `oσ`、集合 `x`、そして「`x` が `σ` での段階の定義可能冪集合に属する」証明を受け取り、`x` が構成可能であると結論します。証明は `x` を一段引き上げます。`σ` は自身の後者 `sucV σ` の要素でもあるので、包含 `Lset-in` は「`𝒟ₒ (Lset σ)` への所属」を「段階 `Lset (sucV σ)` への所属」へ変えます。この段階の添字は `suc-ord oσ` により順序数です。そのうえで `Lset→isL` を一度適用すれば、この段階への所属が証明書 `isL x` に変わります。切り詰められた仮定はそのまま使われます。仮定は `Lset-in` に直接渡され、その結論も同じ形で切り詰められているため、構成可能性の証人が取り出されたり選ばれたりすることはありません。
<!--/-->

```agda
𝒟ₒ→isL : (σ : V ℓ) → IsOrd σ → (x : V ℓ) → ⟨ x ∈ 𝒟ₒ (Lset σ) ⟩ → ⟨ isL x ⟩
𝒟ₒ→isL σ oσ x x∈𝒟ₒσ = Lset→isL (sucV σ) (suc-ord oσ) x
  (Lset-in (sucV σ) σ x (self∈sucV σ) x∈𝒟ₒσ)
```

<!--en-->
Composing the closure lemma with the recognition principle for the operator gives the form every construction in this chapter uses: to put a set in `L`, exhibit an ordinal stage, a formula, and an extensional equation saying that the formula defines exactly that set. The exhibit is merely existential, a truncated pair of a formula and an equation, and that is already enough. The empty set, pairing, and union below are its first three instances.
<!--zh-->
把闭包引理与算子的识别原则复合，就得到本章每个构造所用的形式：要把一个集合放进 `L`，出示一个序数层、一条公式、以及一条说明该公式恰定义该集合的外延等式。这份出示只是存在层面的，即一条公式与一条等式组成的截断对，而这就已经足够。下文的空集、配对与并正是它的头三个实例。
<!--ja-->
閉包の補題を演算子の認識の原理と合成すると、本章のどの構成も使う形が得られます。集合を `L` の中に置くには、順序数の段階、論理式、そしてその論理式がちょうどその集合を定義すると言う外延的な等式を示せばよいのです。この出示は存在の water準にすぎません。すなわち論理式と等式の組の切り詰められた対であり、それで十分です。以下の空集合、対、和集合はその最初の三つの実例です。
<!--/-->

<!--en-->
The hypothesis of `defSet→isL` is a truncated existential: merely some formula `φ` of arity one over the stage's members satisfies `defSet (Lset σ) φ ≡ x`. The recognition principle `𝒟ₒ-intro` turns exactly such data into membership of `x` in `𝒟ₒ (Lset σ)`. That membership is a proposition, so eliminating the truncation into it is legitimate and no formula is ever chosen; the one-line composition with `𝒟ₒ→isL` then delivers `isL x`. The shape of the displayed certificate, an ordinal stage, a defining formula, and an extensional equation, is the pattern the rest of the chapter instantiates.
<!--zh-->
`defSet→isL` 的假设是一个截断的存在式：仅仅是存在一条以该层成员为载体、元数为 1 的公式 `φ`，满足 `defSet (Lset σ) φ ≡ x`。识别原则 `𝒟ₒ-intro` 恰好把这样的数据转换成 `x` 属于 `𝒟ₒ (Lset σ)` 的成员关系。该隶属是命题，故向它消去截断是合法的，任何公式都从未被选定；与 `𝒟ₒ→isL` 的一行复合随即给出 `isL x`。这份证书的形状，序数层、定义公式、外延等式，正是本章余下部分反复实例化的模式。
<!--ja-->
`defSet→isL` の仮定は切り詰められた存在式です。すなわち、段階の要素の上のアリティ 1 の論理式 `φ` で `defSet (Lset σ) φ ≡ x` を満たすものが、単に存在するということです。認識の原理 `𝒟ₒ-intro` はまさにこのようなデータを「`x` が `𝒟ₒ (Lset σ)` に属する」という所属へ変えます。この所属は命題なので、そこへの切り詰めの除去は正当であり、論理式が選ばれることはありません。`𝒟ₒ→isL` との一行の合成がただちに `isL x` を与えます。順序数の段階、定義する論理式、外延的な等式、というこの証明書の形こそ、本章の残りが実例化するパターンです。
<!--/-->

```agda
defSet→isL : (σ : V ℓ) → IsOrd σ → (x : V ℓ)
           → ∥ Σ[ φ ∈ Formula ⟪ Lset σ ⟫ 1 ] (DefOf.defSet (Lset σ) φ ≡ x) ∥₁
           → ⟨ isL x ⟩
defSet→isL σ oσ x p = 𝒟ₒ→isL σ oσ x (𝒟ₒ-intro (Lset σ) x p)
```

<!--en-->
The zeroth instance of the pattern is the stage itself. The formula "true" defines the whole of a set, so every stage is a definable subset of itself, and therefore constructible one stage later. This is what lets a stage be *named* by a formula, the fact on which any construction that bounds a quantifier by a stage rests. Together with the packaging `LsetS`{.Agda}, which pairs a stage with its constructibility certificate, it makes the stage itself an element of the carrier of `L`.
<!--zh-->
这个模式的第零个实例是层自身。公式「真」定义出一个集合的全体，故每层都是它自身的可定义子集，从而在下一层可构造。正是这一点使层可以被一条公式**点名**，凡用层界住量词的构造都立足于此。再加上把层与其可构造性证书配对的打包 `LsetS`{.Agda}，层本身就成为 `L` 载体的一个元素。
<!--ja-->
このパターンの第零の実例は段階そのものです。「真」の論理式は集合の全体を定義するので、どの段階もそれ自身の定義可能部分集合であり、したがって一段上で構成可能です。これこそが、段階を一つの論理式で**名指す**ことを可能にする事実であり、段階で量化子を有界にする構成はすべてこれに依拠します。さらに、段階とその構成可能性の証明書を対にする包み `LsetS`{.Agda} と合わせて、段階そのものが `L` の台の要素になります。
<!--/-->

<!--en-->
The proof of `isL-Lset` is a direct instance of `𝒟ₒ→isL` at `x = Lset β`. The witness formula is the constant-true formula `⊤̇`, and `defSet⊤≡A` identifies its extension with the whole of the carrier set, here the stage `Lset β` itself. Wrapping the pair of formula and equation in a single truncation gives a member of `𝒟ₒ (Lset β)`, and the closure lemma lifts it to `⟨ isL (Lset β) ⟩`. Nothing about the stage's internal structure is inspected; only the ordinality of `β` enters, through `suc-ord`.
<!--zh-->
`isL-Lset` 的证明是在 `x = Lset β` 处对 `𝒟ₒ→isL` 的直接实例化。见证公式是常真公式 `⊤̇`，而 `defSet⊤≡A` 把它的外延等同于载体集合的全体，在这里就是层 `Lset β` 自身。把公式与等式组成的对包进一次截断，便得到 `𝒟ₒ (Lset β)` 的一个成员；闭包引理再把它提升为 `⟨ isL (Lset β) ⟩`。证明没有检视层的任何内部结构；唯一进入论证的是 `β` 的序数性，经由 `suc-ord`。
<!--ja-->
`isL-Lset` の証明は `x = Lset β` における `𝒟ₒ→isL` の直接の実例です。証人となる論理式は定数真の論理式 `⊤̇` であり、`defSet⊤≡A` がその外延を台の集合の全体、ここでは段階 `Lset β` 自身と同一視します。論理式と等式の組を一度の切り詰めに包めば `𝒟ₒ (Lset β)` の要素が得られ、閉包の補題がそれを `⟨ isL (Lset β) ⟩` へ引き上げます。証明は段階の内部構造を一切調べず、論に入るのは `suc-ord` を通しての `β` の順序数性だけです。
<!--/-->

```agda
opaque
  isL-Lset : (β : V ℓ) → IsOrd β → ⟨ isL (Lset β) ⟩
  isL-Lset β oβ = 𝒟ₒ→isL β oβ (Lset β)
    (𝒟ₒ-intro (Lset β) (Lset β) ∣ ⊤̇ , DefOf.defSet⊤≡A (Lset β) ∣₁)

LsetS : (β : V ℓ) → IsOrd β → S
```

<!--en-->
The carrier `S` of the restricted structure consists of a set together with a proof that it lies in the class; `LsetS` supplies exactly that pairing for an ordinal stage: the underlying set `Lset β` with the certificate just built. Through this element the stage enters the constructible structure as an ordinary carrier point.
<!--zh-->
限制结构的载体 `S` 由一个集合连同「它落在该类中」的证明组成；`LsetS` 恰好为序数层给出这个配对：底层集合 `Lset β` 加上刚构造的证书。经由这个元素，层作为一个普通的载体点进入可构造结构。
<!--ja-->
制限された構造の台 `S` は、集合と「それがクラスに属する」ことの証明の対からなります。`LsetS` は順序数の段階に対してまさにこの対を与えます。すなわち基礎の集合 `Lset β` と、今作った証明書です。この要素を通して、段階は普通の台の点として構成可能な構造に入ります。
<!--/-->

```agda
LsetS β oβ = Lset β , isL-Lset β oβ
```

<!--en-->
## The successor stage

The tower's step is the definable power set, and at a successor index the step is all there is: `Lset (sucV σ)` is `𝒟ₒ (Lset σ)` exactly. The identity is proved as two inclusions. For one direction, `σ` is a member of its own successor, so every element of `𝒟ₒ (Lset σ)`, one of the sets being unioned, lies in the next stage. For the other, a member of `Lset (sucV σ)` lies in `𝒟ₒ (Lset δ)` for some `δ` in `sucV σ`; either `δ` is a member of `σ`, and then the set is already in `Lset σ` and so among its definable subsets, or `δ` is `σ` and the inclusion is immediate. Neither half relativizes anything, and neither needs the operator to be monotone; no ordinality hypothesis on `σ` is used.

With the identity in hand, constructibility of the definable power set follows at once: a stage is constructible one stage later, and the definable power set of a stage is that very next stage.
<!--zh-->
## 后继层

塔的步进是可定义幂集；在后继索引处，步进就是全部：`Lset (sucV σ)` 恰是 `𝒟ₒ (Lset σ)`。这条恒等式作为两个包含来证明。其一，`σ` 属于自身的后继，所以 `𝒟ₒ (Lset σ)` 是被并集合之一，其每个元素都属于下一层。其二，`Lset (sucV σ)` 的成员属于某个 `δ ∈ sucV σ` 对应的 `𝒟ₒ (Lset δ)`；若 `δ` 是 `σ` 的成员，该集合已在 `Lset σ` 中，因而是它的可定义子集；若 `δ` 就是 `σ`，结论直接成立。两个方向都不使用相对化，也不需要算子的单调性；这里没有 `σ` 的序数性假设。

有了这条恒等式，可定义幂集的可构造性随之立得：层在下一层可构造，而层的可定义幂集正是那下一层。
<!--ja-->
## 後者段階

塔のステップは定義可能冪集合であり、後者の添字ではステップがすべてです。`Lset (sucV σ)` は `𝒟ₒ (Lset σ)` にちょうど一致します。この恒等式は二つの包含として証明されます。一つの向きには、`σ` は自身の後者の要素なので、`𝒟ₒ (Lset σ)` は和を取られる集合の一つなので、その各要素が次の段階に入ります。もう一つの向きでは、`Lset (sucV σ)` の要素は `sucV σ` のある `δ` に対する `𝒟ₒ (Lset δ)` に属します。`δ` が `σ` の要素ならその集合はすでに `Lset σ` にあり、したがってその定義可能部分集合の一つです。`δ` が `σ` そのものなら包含は直ちに成ります。どちらの向きも相対化を使わず、演算子の単調性も要りません。ここには `σ` の順序数性の仮定もありません。

この恒等式があれば、定義可能冪集合の構成可能性はただちに従います。段階は一段上で構成可能であり、段階の定義可能冪集合はまさにその次の段階だからです。
<!--/-->

<!--en-->
The two sets are compared by ambient extensionality, which reduces the path to a pair of inclusions. The harder inclusion needs a bridge lemma: from a member `x` of the next stage, merely some earlier stage's definable power set contains `x`, with the witness `δ` a member of `sucV σ`. Since the members of `sucV σ` are, by its construction, either members of `σ` or `σ` itself, the witness is exactly the information the argument can case on.
<!--zh-->
两个集合用周遭集合层级的外延性比较，路径化归为一对包含关系。较难的方向需要一条桥引理：从下一层的成员 `x` 出发，仅仅是存在某个更早层的可定义幂集包含 `x`，其见证 `δ` 是 `sucV σ` 的成员。按 `sucV σ` 的构造，其成员要么是 `σ` 的成员，要么是 `σ` 自身，故这个见证正是论证可以分情况处理的信息。
<!--ja-->
二つの集合は周囲の外延性によって比較され、パスは一対の包含へ帰着します。より難しい包含には橋渡しの補題が要ります。次の段階の要素 `x` から、ある前の段階の定義可能冪集合が `x` を含むことが単に成り立ち、その証人 `δ` は `sucV σ` の要素です。`sucV σ` の構成により、その要素は `σ` の要素か `σ` 自身のどちらかなので、この証人はまさに議論が場合分けできる情報です。
<!--/-->

```agda
Lset-suc : (σ : V ℓ) → Lset (sucV σ) ≡ 𝒟ₒ (Lset σ)
Lset-suc σ = extensionality (Lset (sucV σ)) (𝒟ₒ (Lset σ)) (sub₁ , sub₂)
  where
  fromEarlier : (x : V ℓ)
              → Σ[ δ ∈ V ℓ ] (⟨ δ ∈ sucV σ ⟩ × ⟨ x ∈ 𝒟ₒ (Lset δ) ⟩)
```

<!--en-->
The elimination of the witness uses exactly that dichotomy. `∈sucV-elim` takes the proof that `δ` lies in `sucV σ` and two branches. In the first branch `δ` is a member of `σ`, so `Lset-in` places `x` inside `Lset σ`, and the lemma `Lset⊆𝒟ₒ` says that every member of a stage is one of its definable subsets, lifting `x` into `𝒟ₒ (Lset σ)`. In the second branch `δ` is `σ` itself, and `subst` transports the given membership across the path `δ ≡ σ`, changing the index of the stage. The whole target `x ∈ 𝒟ₒ (Lset σ)` is a proposition, which is what allows the truncated witness to be eliminated here at all.
<!--zh-->
对见证的消去恰好使用这条二分法。`∈sucV-elim` 取「`δ` 落在 `sucV σ` 中」的证明与两个分支。第一个分支里 `δ` 是 `σ` 的成员，于是 `Lset-in` 把 `x` 放进 `Lset σ`，而引理 `Lset⊆𝒟ₒ` 说层的每个成员都是它的可定义子集之一，把 `x` 抬进 `𝒟ₒ (Lset σ)`。第二个分支里 `δ` 就是 `σ` 自身，`subst` 沿路径 `δ ≡ σ` 搬运已有的隶属，改换层的索引。整个目标 `x ∈ 𝒟ₒ (Lset σ)` 是命题，这正是截断的见证在此得以消去的前提。
<!--ja-->
証人の消去は、まさにこの二分法を使います。`∈sucV-elim` は「`δ` が `sucV σ` に属する」証明と二つの分岐を受け取ります。第一の分岐では `δ` は `σ` の要素なので、`Lset-in` が `x` を `Lset σ` の内側に置き、補題 `Lset⊆𝒟ₒ` は段階のすべての要素がその定義可能部分集合の一つであると言うので、`x` は `𝒟ₒ (Lset σ)` へ引き上げられます。第二の分岐では `δ` は `σ` 自身であり、`subst` が与えられた所属をパス `δ ≡ σ` に沿って輸送し、段階の添字を付け替えます。目標全体 `x ∈ 𝒟ₒ (Lset σ)` が命題であることこそ、切り詰められた証人をここで除去できる前提です。
<!--/-->

```agda
              → ⟨ x ∈ 𝒟ₒ (Lset σ) ⟩
  fromEarlier x (δ , (δ∈suc , x∈𝒟ₒδ)) =
    ∈sucV-elim {A = σ} {x = δ} (snd (x ∈ 𝒟ₒ (Lset σ))) δ∈suc
      (λ δ∈σ → Lset⊆𝒟ₒ σ x (Lset-in σ δ x δ∈σ x∈𝒟ₒδ))
      (λ δ≡σ → subst (λ w → ⟨ x ∈ 𝒟ₒ (Lset w) ⟩) δ≡σ x∈𝒟ₒδ)
```

<!--en-->
The first inclusion applies the bridge in its forward direction. A structural member of `Lset (sucV σ)` is converted by `∈∈ₛ` into membership in the surrounding hierarchy, the stage characterization `Lset-out` returns the truncated earlier-stage witness, and `fromEarlier` maps it into `𝒟ₒ (Lset σ)`; the elimination lands in the proposition `x ∈ 𝒟ₒ (Lset σ)`, which is what licenses discarding the choice of `δ`. The reverse inclusion needs only that `σ` belongs to its own successor: after `∈∈ₛ` converts the structural membership into the ambient form, `Lset-in` with the witness `self∈sucV σ` places any member of `𝒟ₒ (Lset σ)` directly into the stage at `sucV σ`. The two inclusions assemble into the identity as a path.
<!--zh-->
第一个包含正向使用这条桥。`Lset (sucV σ)` 的结构成员经 `∈∈ₛ` 转成周遭成员关系，层刻画 `Lset-out` 返回截断的更早层见证，`fromEarlier` 再把它映入 `𝒟ₒ (Lset σ)`；消去的目标是命题 `x ∈ 𝒟ₒ (Lset σ)`，这正是丢弃 `δ` 的选择得以合法的依据。反向包含只需 `σ` 属于自身的后继：经 `∈∈ₛ` 把结构成员关系转成周遭形式后，带见证 `self∈sucV σ` 的 `Lset-in` 把 `𝒟ₒ (Lset σ)` 的任何成员直接放进 `sucV σ` 处的层。两个包含合起来，便得到作为路径的恒等式。
<!--ja-->
第一の包含はこの橋を順向きに使います。`Lset (sucV σ)` の構造的な要素は `∈∈ₛ` によって周囲の所属へ変換され、段階の特徴づけ `Lset-out` が切り詰められた前段階の証人を返し、`fromEarlier` がそれを `𝒟ₒ (Lset σ)` へ写します。消去の着地点は命題 `x ∈ 𝒟ₒ (Lset σ)` であり、`δ` の選択を捨ててよい根拠はこれです。逆向きの包含には、`σ` が自身の後者に属することだけが要ります。`∈∈ₛ` で構造的な所属を周囲の形へ変換したのち、証人 `self∈sucV σ` とともに `Lset-in` を適用すれば、`𝒟ₒ (Lset σ)` の任意の要素が `sucV σ` での段階に直接入ります。二つの包含を合わせれば、パスとしての恒等式が得られます。
<!--/-->

```agda

  sub₁ : ⟨ Lset (sucV σ) ⊆ 𝒟ₒ (Lset σ) ⟩
  sub₁ x x∈ₛ = ∈∈ₛ {a = x} {b = 𝒟ₒ (Lset σ)} .fst
    (PT.rec (snd (x ∈ 𝒟ₒ (Lset σ))) (fromEarlier x)
      (Lset-out (sucV σ) x (∈∈ₛ {a = x} {b = Lset (sucV σ)} .snd x∈ₛ)))

  sub₂ : ⟨ 𝒟ₒ (Lset σ) ⊆ Lset (sucV σ) ⟩
```

<!--en-->
For the other inclusion, `self∈sucV σ` selects `𝒟ₒ (Lset σ)` as one of the sets being unioned in the definition of `Lset (sucV σ)`. Thus `Lset-in` sends each element of that definable power set into the successor stage. Together with the first inclusion, surrounding extensionality gives the path `Lset (sucV σ) ≡ 𝒟ₒ (Lset σ)`; no ordinality hypothesis on `σ` occurs in this identity.
<!--zh-->
另一个包含用 `self∈sucV σ` 指出：在 `Lset (sucV σ)` 的定义中，`𝒟ₒ (Lset σ)` 是被并集合之一。因此，`Lset-in` 把这个可定义幂集的每个元素送入后继层。结合第一个包含，周遭集合层级的外延性给出路径 `Lset (sucV σ) ≡ 𝒟ₒ (Lset σ)`；这条恒等式不含 `σ` 的序数性假设。
<!--ja-->
もう一方の包含では、`self∈sucV σ` により、`𝒟ₒ (Lset σ)` が `Lset (sucV σ)` の定義で和を取られる集合の一つだと分かります。したがって `Lset-in` は、その定義可能冪集合の各要素を後者段階へ送ります。第一の包含と合わせ、周囲の外延性からパス `Lset (sucV σ) ≡ 𝒟ₒ (Lset σ)` が得られます。この恒等式には `σ` の順序数性の仮定はありません。
<!--/-->

```agda
  sub₂ x x∈ₛ = ∈∈ₛ {a = x} {b = Lset (sucV σ)} .fst
    (Lset-in (sucV σ) σ x (self∈sucV σ)
      (∈∈ₛ {a = x} {b = 𝒟ₒ (Lset σ)} .snd x∈ₛ))
```

<!--en-->
The successor identity converts the statement that a stage is constructible one stage later into a statement about the definable power set itself: since `Lset (sucV σ)` is exactly `𝒟ₒ (Lset σ)`, and `Lset (sucV σ)` is constructible by the earlier lemma, the definable power set of any ordinal stage is constructible. It can then be packaged as an element of the carrier, a set of `L` with its constructibility certificate attached.
<!--zh-->
后继恒等式把「层在下一层可构造」转成关于可定义幂集自身的陈述：既然 `Lset (sucV σ)` 恰是 `𝒟ₒ (Lset σ)`，而前者由前文引理可构造，故任何序数层的可定义幂集都可构造。于是可以把它打包成载体的一个元素：一个 `L` 的集合，附上其可构造性证书。
<!--ja-->
後者の恒等式は、段階が一段上で構成可能という主張を、定義可能冪集合そのものについての主張へ変えます。`Lset (sucV σ)` はちょうど `𝒟ₒ (Lset σ)` であり、前者は前の補題によって構成可能なので、任意の順序数の段階の定義可能冪集合は構成可能です。したがってそれを、構成可能性の証明書を添えた `L` の集合として台の要素にまとめ直せます。
<!--/-->

<!--en-->
The proof is a transport along the successor identity. `isL-Lset` at the successor, whose ordinality is `suc-ord oσ`, proves `⟨ isL (Lset (sucV σ)) ⟩`; rewriting the target along the path `Lset-suc σ` turns that into `⟨ isL (𝒟ₒ (Lset σ)) ⟩`. No property of the operator beyond the identity is used.
<!--zh-->
证明是沿后继恒等式的一次传输。在后继处应用 `isL-Lset` (其序数性为 `suc-ord oσ`)，得到 `⟨ isL (Lset (sucV σ)) ⟩`；再沿路径 `Lset-suc σ` 改写目标，便得到 `⟨ isL (𝒟ₒ (Lset σ)) ⟩`。除这条恒等式外，没有使用算子的任何其他性质。
<!--ja-->
証明は後者の恒等式に沿った輸送です。後者における (その順序数性は `suc-ord oσ` です) `isL-Lset` の適用が `⟨ isL (Lset (sucV σ)) ⟩` を与え、パス `Lset-suc σ` に沿って目標を書き換えれば `⟨ isL (𝒟ₒ (Lset σ)) ⟩` になります。この恒等式のほかに演算子の性質は何も使っていません。
<!--/-->

```agda
opaque
  isL-𝒟ₒ : (σ : V ℓ) → IsOrd σ → ⟨ isL (𝒟ₒ (Lset σ)) ⟩
  isL-𝒟ₒ σ oσ = subst (λ w → ⟨ isL w ⟩) (Lset-suc σ)
    (isL-Lset (sucV σ) (suc-ord oσ))

𝒟ₒS : (σ : V ℓ) → IsOrd σ → S
```

<!--en-->
The packaging `𝒟ₒS` pairs the definable power set of the stage with its constructibility certificate, giving a carrier element that denotes exactly `𝒟ₒ (Lset σ)`. Where the previous section packaged a stage itself, this one packages the totality of definable subsets of a stage.
<!--zh-->
打包 `𝒟ₒS` 把该层的可定义幂集与其可构造性证书配成对，得到一个恰指称 `𝒟ₒ (Lset σ)` 的载体元素。上一节打包的是层自身，这一节打包的是「一层的可定义子集的全体」。
<!--ja-->
包み `𝒟ₒS` は段階の定義可能冪集合とその構成可能性の証明書を対にし、ちょうど `𝒟ₒ (Lset σ)` を指す台の要素を与えます。前の節が段階そのものをまとめたのに対し、こちらは段階の定義可能部分集合の全体をまとめます。
<!--/-->

```agda
𝒟ₒS σ oσ = 𝒟ₒ (Lset σ) , isL-𝒟ₒ σ oσ
```

<!--en-->
## Finite families

The closure pattern is easiest to see on a finite family. Fix a stage `Lset σ` and a family of `n` members of it. Their image is the set `finSet n h`, and the finite disjunction of "equals this one" carves exactly that image out of the stage: at length zero the formula is falsity, and at each later length one more constant is compared against the free variable. The family may repeat a member; distinct positions may name the same set.

The whole content is one induction identifying satisfaction of the disjunction with being hit by the family, each direction stated for the embedded representatives of the named members. With both directions in hand, an ambient extensionality proves `defSet≡`, the equation saying the definable subset is exactly the image; `finSet∈𝒟ₒ` records the image as a member of `𝒟ₒ (Lset σ)`, and `finSetL` passes from the hypothesis that every family member lies in the stage to the certificate `isL (finSet n h)`, via the closure lemma `defSet→isL`.
<!--zh-->
## 有穷族

闭包模式在有穷族上最容易看清。固定一层 `Lset σ` 与它的 `n` 个成员组成的族。它们的像是集合 `finSet n h`，而「等于这一个」的有穷析取恰好从该层中刻出这个像：长度为零时公式取假，此后每个长度多比较一个常元与自由变元。族中的成员可以重复，不同位置可以指名同一个集合。

全部内容是一次归纳，它把析取的满足与被该族命中等同起来，两个方向都对着被指名成员的嵌入代表陈述。两个方向就位后，一次周遭集合层级的外延性证出 `defSet≡`，即「可定义子集恰是该像」的等式；`finSet∈𝒟ₒ` 把该像记录为 `𝒟ₒ (Lset σ)` 的成员，而 `finSetL` 从「族中每个成员都落在该层」的假设出发，经闭包引理 `defSet→isL`，给出证书 `isL (finSet n h)`。
<!--ja-->
## 有限族

閉包のパターンは有限族の上でいちばんよく見えます。段階 `Lset σ` と、その要素 `n` 個からなる族を固定します。それらの像は集合 `finSet n h` であり、「これと等しい」の有限論理和がちょうどその像を段階から切り出します。長さ零では論理式は偽となり、その後は長さが一つ増えるごとに定数と自由変数の比較が一つ増えます。族の要素は繰り返してよく、異なる位置が同じ集合を名指してもかまいません。

内容のすべては一つの帰納です。論理和の充足と族への命中とを同一視するもので、両方向とも名指された要素の埋め込まれた代表に対して述べられます。両方向が揃えば、周囲の外延性によって `defSet≡`、すなわち定義可能部分集合が像にちょうど一致するという等式が証明されます。`finSet∈𝒟ₒ` は像を `𝒟ₒ (Lset σ)` の要素として記録し、`finSetL` は「族の各要素が段階に属する」という仮定から、閉包の補題 `defSet→isL` を経て証明書 `isL (finSet n h)` を与えます。
<!--/-->

<!--en-->
The image set is defined directly: `finSet n h` is the set presented by the index type `Fin n` lifted into the hierarchy's universe and the indexing map that applies `h` after lowering. Membership is characterized in the truncated form appropriate to the hierarchy: `y` belongs to `finSet n h` precisely when some index `i` merely satisfies `h i ≡ y`. Each direction of `finSet-in` and `finSet-out` is a single map inside the truncation, since membership in a presented set is by construction the truncated existence of an index.
<!--zh-->
像集合被直接定义：`finSet n h` 是由提升到层级所在宇宙的索引类型 `Fin n` 与「先降层再作用 `h`」的索引映射所呈现的集合。成员关系按层级截断的形式刻画：`y` 属于 `finSet n h`，恰当仅仅是存在索引 `i` 满足 `h i ≡ y`。`finSet-in` 与 `finSet-out` 的每个方向都是截断内部的一次映射，因为呈现场合中的成员关系按构造就是索引的截断存在。
<!--ja-->
像の集合は直接定義されます。`finSet n h` は、階層の宇宙へ持ち上げた添字型 `Fin n` と、`lower` をほどこしてから `h` を適用する添字写像によって表現された集合です。所属は階層に適した切り詰めの形で特徴づけられます。`y` が `finSet n h` に属するのは、ある添字 `i` が `h i ≡ y` を満たすことが単に成り立つとき、そのときに限ります。`finSet-in` と `finSet-out` の各方向は切り詰めの内部での一つの写像です。表現された集合への所属は、構成上、添字の切り詰められた存在だからです。
<!--/-->

```agda
finSet : (n : ℕ) → (Fin n → V ℓ) → V ℓ
finSet n h = sett (Lift {ℓ-zero} {ℓ} (Fin n)) (λ i → h (lower i))

finSet-in : (n : ℕ) (h : Fin n → V ℓ) (y : V ℓ)
          → ∥ Σ[ i ∈ Fin n ] (h i ≡ y) ∥₁ → ⟨ y ∈ finSet n h ⟩
finSet-in n h y = PT.map (λ { (i , q) → lift i , q })
```

<!--en-->
The reverse membership lemma `finSet-out` is the same map read backwards, from a lifted index back down to `Fin n`. The definability work then happens at an ordinal stage `σ`: working inside `DefOf (Lset σ)` fixes the alphabet of constants to be the small index type `⟪ Lset σ ⟫` of that stage, so a member of the stage can be named by a constant, and the definable subsets at issue are those carved from `Lset σ`.
<!--zh-->
反向成员引理 `finSet-out` 是同一映射倒过来读，从提升后的索引降回 `Fin n`。随后可定义性的工作在序数层 `σ` 上进行：在 `DefOf (Lset σ)` 内部工作，把常元的字母表定为该层的小索引类型 `⟪ Lset σ ⟫`，于是层的成员可用常元命名，而所论的可定义子集就是从 `Lset σ` 中刻出的那些。
<!--ja-->
逆向きの所属の補題 `finSet-out` は、同じ写像を逆に読んだもので、持ち上げられた添字から `Fin n` へ降ります。つづいて定義可能性の作業は順序数の段階 `σ` で行われます。`DefOf (Lset σ)` の内側で作業すると、定数のアルファベットはその段階の小さな添字型 `⟪ Lset σ ⟫` に確定し、段階の要素は定数で名指せます。問題になる定義可能部分集合は、`Lset σ` から切り出されるものです。
<!--/-->

```agda

finSet-out : (n : ℕ) (h : Fin n → V ℓ) (y : V ℓ)
           → ⟨ y ∈ finSet n h ⟩ → ∥ Σ[ i ∈ Fin n ] (h i ≡ y) ∥₁
finSet-out n h y = PT.map (λ { (i , q) → lower i , q })

module FinOf (σ : V ℓ) (oσ : IsOrd σ) where
  module DefC = DefOf (Lset σ)
```

<!--en-->
The formula is the finite disjunction of equalities. At length zero there is nothing to be equal to, so the formula is falsity; at the successor of a length, the free variable is compared against the constant naming the first family member, and the remaining members are handled by the recursive call with the family shifted. The arity is one throughout: a single free-variable slot serves the whole disjunction, and the function `g` need not be injective, distinct positions may name the same member.
<!--zh-->
公式是等式的有穷析取。长度为零时无可等同之物，故公式取假；长度为后继时，自由变元与指名族首成员的常元比较，其余成员由族平移后的递归调用处理。元数始终为一：整个析取共用一个自由变元槽，而函数 `g` 无须单射，不同位置可以指名同一个成员。
<!--ja-->
論理式は等式の有限論理和です。長さ零では等しい相手がいないので論理式は偽となり、長さが後者のときは自由変数を族の最初の要素を名指す定数と比較し、残りの要素は族をずらした再帰呼び出しに委ねます。アリティは全体を通して一です。一つの自由変数のスロットが論理和全体に使われ、関数 `g` は単射である必要はなく、異なる位置が同じ要素を名指してもかまいません。
<!--/-->

```agda

  finDisj : (n : ℕ) → (Fin n → ⟪ Lset σ ⟫) → Formula ⟪ Lset σ ⟫ 1
  finDisj zero    g = ⊥̇
  finDisj (suc n) g =
    (var zero ≐ con (g zero)) ∨̇ finDisj n (λ i → g (suc i))

  private
```

<!--en-->
The bridge statement `Hits` says that the member named by the environment is merely hit by the family, with the path written against the embedded representative `⟪ Lset σ ⟫↪ (g i)` of the named member. The two directions connect satisfaction of the disjunction, which is what the definable subset sees, with being hit by the family, which is what the image set sees.
<!--zh-->
桥陈述 `Hits` 说：赋值所指名的成员仅仅被该族命中，其中路径是对照被指名成员的嵌入代表 `⟪ Lset σ ⟫↪ (g i)` 书写的。两个方向连接的是：可定义子集所看见的「析取被满足」，与像集合所看见的「被族命中」。
<!--ja-->
橋渡しの主張 `Hits` は、環境で名指された要素が族に単に命中することを言います。パスは名指された要素の埋め込まれた代表 `⟪ Lset σ ⟫↪ (g i)` に対して書かれます。二つの方向は、定義可能部分集合が見る「論理和の充足」と、像の集合が見る「族への命中」とを結びます。
<!--/-->

```agda
    Hits : (n : ℕ) (g : Fin n → ⟪ Lset σ ⟫) (y : V ℓ) → Type (ℓ-suc ℓ)
    Hits n g y = ∥ Σ[ i ∈ Fin n ] (⟪ Lset σ ⟫↪ (g i) ≡ y) ∥₁

    sat→hits : (n : ℕ) (g : Fin n → ⟪ Lset σ ⟫) (m : ⟪ Lset σ ⟫)
             → ⟨ (DefC.ι m ∷ []) DefC.⊨ᵐ finDisj n g ⟩
             → Hits n g (⟪ Lset σ ⟫↪ m)
```

<!--en-->
From satisfaction to hits proceeds by recursion on the length. At zero the formula is falsity, and a proof of it is absurd. At a successor, satisfaction is a truncated disjunction: in the left branch the environment equals the first constant, giving the index `zero`; in the right branch the recursive call returns a hit for the shifted family, whose index is promoted by one. Each branch returns its witness inside a truncation, and the outer elimination is legitimate because the target `Hits` is proposition-valued.
<!--zh-->
从满足到命中沿长度递归。长度为零时公式是假，其证明导致荒谬。长度为后继时，满足是截断的析取：左支中赋值等于第一个常元，给出索引 `zero`；右支中递归调用对平移后的族返回一个命中，其索引加一提升。每个分支都在截断内返回其见证，而外层消去合法，因为目标 `Hits` 取命题值。
<!--ja-->
充足から命中へは、長さについての再帰で進みます。零では論理式は偽であり、その証明は荒謬です。後者では充足は切り詰められた論理和です。左の分岐では環境が最初の定数と等しく、添字 `zero` が得られます。右の分岐では再帰呼び出しがずらした族への命中を返し、その添字が一つ上げられます。各分岐は証人を切り詰めの内部で返し、目標の `Hits` が命題値であるため、外側の消去は正当です。
<!--/-->

```agda
    sat→hits zero    g m bot = Empty.rec* bot
    sat→hits (suc n) g m = PT.rec squash₁
      (λ { (inl e)  → ∣ zero , sym e ∣₁
         ; (inr sat) → PT.map (λ { (i , q) → suc i , q })
                         (sat→hits n (λ i → g (suc i)) m sat) })
```

<!--en-->
The reverse direction turns a hit into satisfaction, again by recursion on the length. At length zero there is no index of type `Fin 0`, so a hit there can be refuted by matching against the empty index type; this matches the formula being falsity at zero. Since the statement of `hits→sat` is quantified over all lengths at once, the recursive call in the successor case is available without any hypothesis being carried along.
<!--zh-->
反方向把命中转为满足，同样沿长度递归。长度为零时索引类型 `Fin 0` 没有任何元素，故通过对照空索引类型做匹配即可反驳那里的命中；这正与公式在零处取假相配。由于 `hits→sat` 是同时对所有长度陈述的，后继情形中的递归调用无须携带任何额外假设即可使用。
<!--ja-->
逆方向は命中を充足に変えるもので、これも長さについての再帰で進みます。長さ零では型 `Fin 0` の添字が存在しないので、そこの命中は空の添字型とのマッチングで反証できます。これは論理式が零で偽であることと対応します。`hits→sat` はすべての長さに対して一度に述べられているため、後者の場合の再帰呼び出しは仮定を何も引き回さずに使えます。
<!--/-->

```agda

    hits→sat : (n : ℕ) (g : Fin n → ⟪ Lset σ ⟫) (m : ⟪ Lset σ ⟫)
             → Hits n g (⟪ Lset σ ⟫↪ m)
             → ⟨ (DefC.ι m ∷ []) DefC.⊨ᵐ finDisj n g ⟩
    hits→sat zero g m =
      PT.rec (snd ((DefC.ι m ∷ []) DefC.⊨ᵐ finDisj zero g)) (λ { (() , _) })
```

<!--en-->
At a successor length, the hit is a truncated pair whose index is either `zero` or a successor `suc i`. In the first case the path identifies the member with the first constant, and the left disjunct of the formula is satisfied. In the second, the recursive call applied to the shifted family produces satisfaction of the tail disjunction, which becomes the right disjunct. Both cases return their answer inside a truncation, so the proof never depends on which index a hit happened to carry.
<!--zh-->
长度为后继时，命中是截断的对，其索引要么是 `zero`，要么是后继 `suc i`。第一种情形中，路径把成员与第一个常元等同，公式的左析取支得到满足。第二种情形中，对平移后族施用递归调用得到尾部析取的满足，它成为右析取支。两种情形都在截断内返回答案，故证明从不依赖于命中恰好携带的是哪个索引。
<!--ja-->
長さが後者のとき、命中は添字が `zero` であるか後者 `suc i` であるかのいずれかである切り詰められた対です。最初の場合、パスが要素を最初の定数と同一視し、論理式の左の選言肢が充足されます。第二の場合、ずらした族に対する再帰呼び出しが尾部の論理和の充足を生み、それが右の選言肢になります。どちらの場合も答えは切り詰めの内部で返されるので、証明が命中のもつ添字に依存することはありません。
<!--/-->

```agda
    hits→sat (suc n) g m =
      PT.rec (snd ((DefC.ι m ∷ []) DefC.⊨ᵐ finDisj (suc n) g))
        (λ { (zero  , q) → ∣ inl (sym q) ∣₁
           ; (suc i , q) →
             ∣ inr (hits→sat n (λ j → g (suc j)) m ∣ i , q ∣₁) ∣₁ })
```

<!--en-->
The two directions of the bridge are exactly the two inclusions that the identity `defSet≡` needs. It is proved by ambient extensionality, which reduces the path of sets to a pair of inclusions, and the image set is abbreviated `F`. It remains to translate between membership in the structured presentation and membership in the surrounding hierarchy.
<!--zh-->
桥的两个方向恰好是恒等式 `defSet≡` 所需的两条包含。证明用的是周遭集合层级的外延性：集合的路径化归为一对包含，而像集合以缩写 `F` 记之。剩下的工作只是在结构成员记号与周遭成员记号之间做簿记。
<!--ja-->
橋の二つの方向は、恒等式 `defSet≡` が必要とする二つの包含にちょうど一致します。証明は周囲の外延性によるもので、集合のパスは一対の包含へ帰着し、像の集合には略称 `F` が使われます。残りの作業は、構造的な所属の記法と周囲の所属の記法のあいだの簿記です。
<!--/-->

```agda

  defSet≡ : (n : ℕ) (g : Fin n → ⟪ Lset σ ⟫)
          → DefC.defSet (finDisj n g) ≡ finSet n (λ i → ⟪ Lset σ ⟫↪ (g i))
  defSet≡ n g = extensionality _ _ (sub₁ , sub₂)
    where
    F = finSet n (λ i → ⟪ Lset σ ⟫↪ (g i))
```

<!--en-->
The first inclusion starts from a structural member `y` of the definable subset. The conversion `∈∈ₛ` turns it into ambient membership, whose reading lemma supplies the truncated defining data: an environment `m` with a satisfaction certificate, together with a path `q` identifying `y` with the member named by `m`. The goal being proved at that point is the proposition `⟨ y ∈ F ⟩`, which is what licenses eliminating the truncation.
<!--zh-->
第一个包含从可定义子集的结构成员 `y` 出发。转换 `∈∈ₛ` 把它变成周遭成员关系，其读法引理给出截断的定义数据：赋值 `m` 连同满足证书，以及强迫 `y` 等于 `m` 所指名成员的路径 `q`。此处要证的目标是命题 `⟨ y ∈ F ⟩`，这正是消去截断得以合法的依据。
<!--ja-->
第一の包含は、定義可能部分集合の構造的な要素 `y` から始まります。変換 `∈∈ₛ` がそれを周囲の所属へ変え、その読み取り補題が切り詰められた定義データを与えます。すなわち充足の証明書を伴う環境 `m` と、`y` を `m` の名指す要素と同一視するパス `q` です。この時点で証明すべき目標は命題 `⟨ y ∈ F ⟩` であり、これが切り詰めの除去を正当化します。
<!--/-->

```agda
    sub₁ : ⟨ DefC.defSet (finDisj n g) ⊆ F ⟩
    sub₁ y y∈ₛ = ∈∈ₛ {a = y} {b = F} .fst (PT.rec (snd (y ∈ F))
      (λ { ((m , h) , q) →
        subst (λ v → ⟨ v ∈ F ⟩) q
          (finSet-in n (λ i → ⟪ Lset σ ⟫↪ (g i)) (⟪ Lset σ ⟫↪ m)
```

<!--en-->
The satisfaction certificate is converted, by the computation rule `defSet-mem` for membership in a definable subset, into a satisfaction of the disjunction at the environment `m`. The bridge lemma `sat→hits` then produces a hit, and `finSet-in` reads the hit as membership of the embedded element in the image. The transport along `q` finally relocates that membership from the named member to `y` itself.
<!--zh-->
满足证书经可定义子集成员关系的计算规则 `defSet-mem` 转换，得到析取在赋值 `m` 处的一次满足。桥引理 `sat→hits` 随之产出一次命中，`finSet-in` 把命中读成嵌入元素在像中的成员关系。最后沿 `q` 的搬移把这条成员关系从被指名的成员移到 `y` 自身。
<!--ja-->
充足の証明書は、定義可能部分集合への所属の計算規則 `defSet-mem` によって、環境 `m` での論理和の充足へ変換されます。橋渡しの補題 `sat→hits` が命中を生み、`finSet-in` がその命中を、埋め込まれた要素の像への所属として読みます。最後に `q` に沿った輸送が、その所属を名指された要素から `y` 自身へ移します。
<!--/-->

```agda
            (sat→hits n g m
              (subst ⟨_⟩ (DefC.defSet-mem (finDisj n g) m)
                ∣ (m , h) , refl ∣₁))) })
      (∈∈ₛ {a = y} {b = DefC.defSet (finDisj n g)} .snd y∈ₛ))
    sub₂ : ⟨ F ⊆ DefC.defSet (finDisj n g) ⟩
```

<!--en-->
The reverse inclusion starts from `y ∈ F`. The elimination rule `finSet-out` merely supplies an index `i : Fin n` and a path `q : ⟪ Lset σ ⟫↪ (g i) ≡ y`. At the representative `g i`, the truncated witness `∣ i , refl ∣₁` proves `Hits n g (⟪ Lset σ ⟫↪ (g i))`; `hits→sat` converts it into satisfaction of the finite disjunction there. The following transport along `q` then yields membership of `y` in the definable subset.
<!--zh-->
反向包含从 `y ∈ F` 出发。消去规则 `finSet-out` 仅仅给出索引 `i : Fin n` 与路径 `q : ⟪ Lset σ ⟫↪ (g i) ≡ y`。在代表元 `g i` 处，截断见证 `∣ i , refl ∣₁` 证明 `Hits n g (⟪ Lset σ ⟫↪ (g i))`；`hits→sat` 把它转换成有限析取在该代表元处的满足。随后沿 `q` 搬移，便得到 `y` 属于可定义子集。
<!--ja-->
逆の包含は `y ∈ F` から始まります。除去規則 `finSet-out` は、添字 `i : Fin n` とパス `q : ⟪ Lset σ ⟫↪ (g i) ≡ y` を単に与えます。代表元 `g i` では、切り詰められた証人 `∣ i , refl ∣₁` が `Hits n g (⟪ Lset σ ⟫↪ (g i))` を示し、`hits→sat` がそれを有限論理和の充足へ変換します。その後 `q` に沿って輸送すれば、`y` の定義可能部分集合への所属が得られます。
<!--/-->

```agda
    sub₂ y y∈ₛ = PT.rec (snd (y ∈ₛ DefC.defSet (finDisj n g)))
      (λ { (i , q) →
        subst (λ v → ⟨ v ∈ₛ DefC.defSet (finDisj n g) ⟩) q
          (∈∈ₛ {a = ⟪ Lset σ ⟫↪ (g i)} {b = DefC.defSet (finDisj n g)} .fst
            (subst ⟨_⟩ (sym (DefC.defSet-mem (finDisj n g) (g i)))
```

<!--en-->
The satisfaction is read, through the membership reading of `defSet` used in reverse, as structural membership of the embedded `g i` in the definable subset, and the transport along the hit's path moves it onto `y`. With both inclusions assembled, `defSet≡` states the equality as a path of sets: the subset carved by the finite disjunction is the image of the family, repetitions in the family included, since equal members are named by several constants without affecting the image.
<!--zh-->
满足经反向使用 `defSet` 的隶属读法，被读成嵌入的 `g i` 在可定义子集中的结构成员关系，再沿命中路径的搬移把它落到 `y` 上。两条包含合起来，`defSet≡` 便作为集合的路径陈述这一相等：由有穷析取刻出的子集就是该族的像，族中的重复也在其内，因为相同的成员由多个常元名指，并不影响像。
<!--ja-->
充足は `defSet` の所属の読みを逆向きに用いて、埋め込まれた `g i` の定義可能部分集合への構造的な所属として読まれ、命中のパスに沿った輸送がそれを `y` へ移します。二つの包含を組み合わせれば、`defSet≡` は集合としてのパスでこの等式を述べます。有限論理和が切り出す部分集合は族の像であり、族に繰り返しがあっても同様です。同じ要素が複数の定数で名指されても像は変わらないからです。
<!--/-->

```agda
              (hits→sat n g (g i) ∣ i , refl ∣₁))) })
      (finSet-out n (λ i → ⟪ Lset σ ⟫↪ (g i)) y
        (∈∈ₛ {a = y} {b = F} .snd y∈ₛ))

  finSet∈𝒟ₒ : (n : ℕ) (g : Fin n → ⟪ Lset σ ⟫)
            → ⟨ finSet n (λ i → ⟪ Lset σ ⟫↪ (g i)) ∈ 𝒟ₒ (Lset σ) ⟩
```

<!--en-->
Two packaging steps finish the section. First, `finSet∈𝒟ₒ` supplies the disjunction and the identity just proved to `𝒟ₒ-intro`, recording the image set as a member of the definable power set of the stage; the certificate is truncated, so the particular formula is not part of the data retained. Second, `finSetL` starts from a family of arbitrary sets, each of which is given as lying in the stage by a membership proof. For each member, `∈-asFiber` converts that membership proof into an index of the stage's presentation together with a path back to the member; collecting these paths and rewriting the image set along them by `cong (finSet n) (funExt qg)` identifies it with the embedded family that `defSet≡` speaks about. The closure lemma `defSet→isL` then delivers the constructibility of `finSet n h`.
<!--zh-->
本节以两步收尾。第一步，`finSet∈𝒟ₒ` 把刚才证明的析取与等式交给 `𝒟ₒ-intro`，把像集合记录为该层可定义幂集的一个成员；这一可定义性证书是截断的，故被保留的数据中不含特定公式。第二步，`finSetL` 从一个由任意集合组成的族出发，并给定每个成员属于该层的证明。对每个成员，`∈-asFiber` 给出层呈现的索引以及回到该成员的路径；用 `cong (finSet n) (funExt qg)` 沿这些路径改写像集合，便把它与 `defSet≡` 所谈论的嵌入族等同起来。闭包引理 `defSet→isL` 随即给出 `finSet n h` 的可构造性。
<!--ja-->
この節は二段階で結ばれます。第一に、`finSet∈𝒟ₒ` は今証明した論理式と等式を `𝒟ₒ-intro` に渡し、像の集合を段階の定義可能冪集合の要素として記録します。この定義可能性の証明書は切り詰められているため、保持されるデータに特定の論理式は含まれません。第二に、`finSetL` は任意の集合の族と、各要素がこの段階に属する証明から出発します。各要素に対して `∈-asFiber` が段階の提示の添字と要素へのパスを与え、`cong (finSet n) (funExt qg)` でそれらのパスに沿って像の集合を書き換えると、`defSet≡` が扱う埋め込まれた族と同一視できます。閉包の補題 `defSet→isL` が `finSet n h` の構成可能性を与えます。
<!--/-->

```agda
  finSet∈𝒟ₒ n g = 𝒟ₒ-intro (Lset σ) _ ∣ finDisj n g , defSet≡ n g ∣₁

  finSetL : (n : ℕ) (h : Fin n → V ℓ) → ((i : Fin n) → ⟨ h i ∈ Lset σ ⟩)
          → ⟨ isL (finSet n h) ⟩
  finSetL n h hσ = defSet→isL σ oσ (finSet n h)
    ∣ finDisj n g , (defSet≡ n g ∙ cong (finSet n) (funExt qg)) ∣₁
```

<!--en-->
The hypothesis `hσ i` states merely that `h i` lies in the stage. Membership in a hierarchy set is a truncated fiber of the embedding `⟪ Lset σ ⟫↪`, and because that map is an embedding its fiber types are propositions, so eliminating the truncation into a fiber type is legitimate and `∈-asFiber` performs exactly that conversion. Thus `g i` is a chosen index whose embedded element has the path `qg i` back to `h i`. The certificate handed to `defSet→isL` pairs the finite disjunction in the representatives `g` with `defSet≡ n g` followed by the rewriting `funExt qg`, carrying the identification from the embedded family `finSet n (λ i → ⟪ Lset σ ⟫↪ (g i))` to the original family `finSet n h`.
<!--zh-->
假设 `hσ i` 只是陈述 `h i` 属于该层。对一个层级集合的隶属是嵌入映射 `⟪ Lset σ ⟫↪` 的纤维的截断，而该映射是嵌入，其纤维类型是命题，故向纤维类型消去截断是合法的，`∈-asFiber` 做的正是这一转换。于是 `g i` 是被选出的索引，其嵌入后的元素有路径 `qg i` 回到 `h i`。交给 `defSet→isL` 的证书把关于代表元 `g` 的有穷析取与 `defSet≡ n g` 配对，再接上改写 `funExt qg`，把这条等同从嵌入后的族 `finSet n (λ i → ⟪ Lset σ ⟫↪ (g i))` 搬到原先的族 `finSet n h` 上。
<!--ja-->
仮定 `hσ i` は、`h i` がこの段階に属することを切り詰められた形で述べるにすぎません。階層の集合への所属は埋め込み `⟪ Lset σ ⟫↪` のファイバーの切り詰めであり、この写像は埋め込みなのでファイバーの型は命題です。したがってファイバーの型への切り詰めの除去は正当であり、`∈-asFiber` がまさにその変換を行います。ゆえに `g i` は選ばれた添字であり、その埋め込まれた元から `h i` へのパスが `qg i` です。`defSet→isL` に渡す証明書は、代表元 `g` に対する有限論理和と `defSet≡ n g` を組にし、さらに書き換え `funExt qg` を続けることで、埋め込まれた族 `finSet n (λ i → ⟪ Lset σ ⟫↪ (g i))` についての同一視を元の族 `finSet n h` へと運びます。
<!--/-->

```agda
    where
    g : Fin n → ⟪ Lset σ ⟫
    g i = ∈-asFiber {a = h i} {b = Lset σ} (hσ i) .fst
    qg : (i : Fin n) → ⟪ Lset σ ⟫↪ (g i) ≡ h i
    qg i = ∈-asFiber {a = h i} {b = Lset σ} (hσ i) .snd
```

<!--en-->
## Two sets, one stage

`isL-directed`{.Agda} places any two constructible sets in one common ordinal stage.

Each constructible set has a stage of its own, given merely by its truncated certificate of constructibility. The conclusion combines the two: merely, there is an ordinal `σ` whose stage contains both sets. The ordinal `bound2` produces one that contains both given ordinals, and monotonicity of stages carries each set from its own stage up into the stage at the bound. The result is stated truncated, so no stage is ever exhibited to the outside; locally the two certificates are opened far enough to read off the two stages they name.
<!--zh-->
## 两个集合，一层

`isL-directed`{.Agda} 把任意两个可构造集合放进一个公共的序数层。

每个可构造集合都有自己的层，由其截断的可构造性证书「仅仅地」给出。结论把二者合并：仅仅是存在一个序数 `σ`，其层同时装下这两个集合。`bound2` 产出一个同时包含两个给定序数的序数，而层的单调性把每个集合从各自的层抬进上界处的层。结论以截断形式陈述，故从不向外界出示任何层；在局部，两份证书只被打开到足以读出它们各自名指的层为止。
<!--ja-->
## 二つの集合を一つの段階へ

`isL-directed`{.Agda} は、任意の二つの構成可能集合を一つの共通の順序数段階へ置きます。

構成可能集合はそれぞれ固有の段階をもち、それは構成可能性の切り詰められた証明書によって単に与えられます。結論はこの二つを組み合わせます。すなわち、両方の集合を含む段階をもつ順序数 `σ` が単に存在するということです。`bound2` は与えられた二つの順序数をともに含む順序数を作り、段階の単調性が各集合をその固有の段階から上界の段階へ引き上げます。結論は切り詰められた形で述べられるので、外部に段階が示されることはありません。局所的には、二つの証明書がそれぞれの名指す段階を読み取れるところまで開かれるだけです。
<!--/-->

<!--en-->
The statement takes two constructible sets as truncated certificates: `⟨ isL x ⟩` and `⟨ isL y ⟩` say merely that each lies in `L`, without naming a stage. The conclusion is likewise truncated, so the two certificates are eliminated only into a truncated existence statement, and no stage is ever chosen for the outside world. Locally the target content is packaged as `Bound`: an ordinal `σ`, its ordinality, and the two memberships in `Lset σ`.
<!--zh-->
这条陈述把两个可构造集合当作截断的证书接收：`⟨ isL x ⟩` 与 `⟨ isL y ⟩` 只是说各自落在 `L` 中，并不点名某一层。结论同样是截断的，因此那两份证书只被消去到一条截断的存在陈述中，从未向外部世界选出任何层。局部的目标内容被打包为 `Bound`：一个序数 `σ`、它的序数性，以及 `Lset σ` 中的两条隶属。
<!--ja-->
この定理は二つの構成可能集合を切り詰められた証明書として受け取ります。`⟨ isL x ⟩` と `⟨ isL y ⟩` は、それぞれが `L` に属することを述べるだけで、段階を名指ししません。結論も同様に切り詰められているため、この二つの証明書は切り詰められた存在の主張の中へしか除去されず、外部に向かって段階が選ばれることはありません。局所的には、目標の内容は `Bound` にまとめられています。すなわち順序数 `σ`、その順序数性、そして `Lset σ` への二つの所属です。
<!--/-->

```agda
isL-directed : (x y : V ℓ) → ⟨ isL x ⟩ → ⟨ isL y ⟩
             → ∥ Σ[ σ ∈ V ℓ ] (IsOrd σ × (⟨ x ∈ Lset σ ⟩ × ⟨ y ∈ Lset σ ⟩)) ∥₁
isL-directed x y px py = PT.rec2 squash₁ go px py
  where
  Bound : Type (ℓ-suc ℓ)
```

<!--en-->
The two truncations are eliminated at once by `PT.rec2`, whose target is the truncation `∥ Bound ∥₁`. Its working part `go` receives the explicit data that the certificates conceal: a stage `α`, ordinal, with `x` in `Lset α`, and a stage `β`, ordinal, with `y` in `Lset β`. Merging them is not a comparison of sizes; `bound2 α β oα oβ` returns a single ordinal bound that contains both `α` and `β`, together with its ordinality and the two memberships.
<!--zh-->
两条截断由 `PT.rec2` 一次消去，其目标是截断 `∥ Bound ∥₁`。干活的分支 `go` 接收证书所隐藏的显式数据：序数层 `α` 且 `x` 属于 `Lset α`，以及序数层 `β` 且 `y` 属于 `Lset β`。合并它们并不是在比较大小；`bound2 α β oα oβ` 返回一个同时包含 `α` 与 `β` 的序数上界，连同它的序数性和两条隶属。
<!--ja-->
二つの切り詰めは `PT.rec2` によって一度に除去されます。その目標は切り詰め `∥ Bound ∥₁` です。実際に働く部分 `go` が受け取るのは、証明書が隠している明示的なデータ、すなわち順序数である段階 `α` と `x ∈ Lset α`、および順序数である段階 `β` と `y ∈ Lset β` です。両者を併合することは大きさの比較ではありません。`bound2 α β oα oβ` は `α` と `β` の両方を含む単一の順序数上界を、その順序数性と二つの所属とともに返します。
<!--/-->

```agda
  Bound = Σ[ σ ∈ V ℓ ] (IsOrd σ × (⟨ x ∈ Lset σ ⟩ × ⟨ y ∈ Lset σ ⟩))
  go : Σ[ α ∈ V ℓ ] (IsOrd α × ⟨ x ∈ Lset α ⟩)
     → Σ[ β ∈ V ℓ ] (IsOrd β × ⟨ y ∈ Lset β ⟩) → ∥ Bound ∥₁
  go (α , (oα , x∈Lα)) (β , (oβ , y∈Lβ)) =
    ∣ bnd .fst , (bnd .snd .fst , ( Lset-mono (bnd .snd .snd .fst) x∈Lα
```

<!--en-->
The bound comes with memberships `α ∈ σ₀` and `β ∈ σ₀`, so monotonicity `Lset-mono` lifts `x ∈ Lset α` into the stage `Lset σ₀` at the bound, and likewise for `y` from `β`. Wrapping the assembled triple in `∣_∣₁` completes `go`, and with it the whole statement: any two constructible sets merely have a common ordinal stage. This is what the pairing field will consume, since it needs both arguments visible at one stage.
<!--zh-->
上界自带 `α ∈ σ₀` 与 `β ∈ σ₀` 两条隶属，于是单调性 `Lset-mono` 把 `x ∈ Lset α` 抬进上界处的层 `Lset σ₀`；对来自 `β` 的 `y` 同理。把拼好的三元组用 `∣_∣₁` 包起来便完成 `go`，也随之完成整条陈述：任意两个可构造集合「仅仅存在」一个公共的序数层。配对字段要消费的正是它，因为配对需要两个实参在同一层上可见。
<!--ja-->
上界には `α ∈ σ₀` と `β ∈ σ₀` という所属が付いてくるので、単調性 `Lset-mono` は `x ∈ Lset α` を上界の段階 `Lset σ₀` へ引き上げます。`β` からの `y` についても同様です。組み立てた三つ組を `∣_∣₁` で包めば `go` が完成し、それとともに定理全体、すなわち任意の二つの構成可能集合が共通の順序数段階を「単に存在する」という形でもつことが示されます。対のフィールドは、二つの実引数が同じ段階で見えることを必要とするので、消費するのはまさにこれです。
<!--/-->

```agda
                                  , Lset-mono (bnd .snd .snd .snd) y∈Lβ )) ∣₁
    where bnd = bound2 α β oα oβ
```

<!--en-->
## The two inherited axioms

Extensionality and regularity both restrict from the ambient hierarchy, but by different arguments. For extensionality, `isL-trans` turns an ambient member of either constructible set into a carrier element, so the assumed agreement on carrier members applies; ambient extensionality then equates the underlying sets and restriction reflection gives a carrier path. Regularity does not use `isL-trans`: ambient accessibility is restricted recursively to pairs already carrying their constructibility certificates.
<!--zh-->
## 继承来的两条公理

外延性与正则性都从周遭集合层级限制而来，但论证不同。对外延性，`isL-trans` 把任一可构造集合的周遭成员变成载体元素，从而可以应用关于载体成员的一致性假设；周遭集合层级的外延性随后等同底层集合，限制反射再给出载体路径。正则性不使用 `isL-trans`：只需把周遭可及性递归地限制到已经自带可构造性证书的对子上。
<!--ja-->
## 継承される二つの公理

外延性と正則性はいずれも周囲の階層から制限されますが、議論は異なります。外延性では `isL-trans` により、どちらかの構成可能集合の周囲での要素を台の要素にし、台の要素について仮定した一致を適用します。周囲の外延性が基底の集合を同一視し、制限の反射が台のパスを与えます。正則性は `isL-trans` を使いません。周囲の可到達性を、すでに構成可能性の証明書を持つ対へ再帰的に制限します。
<!--/-->

<!--en-->
Extensionality inside `L` has the shape: if two carrier elements agree on membership at every carrier element, they are equal as paths. The proof reduces to the underlying hierarchy. The carrier consists of pairs of a set with a constructibility certificate, and `↾-reflects` is the principle that such pairs are determined by their first projections: a path between the underlying sets `fst a` and `fst b` already gives a path `a ≡ b`. Everything therefore rests on producing that underlying path, which `extensionalV` supplies given `vwise`.
<!--zh-->
`L` 内部的外延性形状是：若载体的两个元素在每个载体元素处的隶属一致，它们就作为路径相等。证明被化归到底层层级。载体由「集合加可构造性证书」的对组成，而 `↾-reflects` 是一条原理：这样的对由其第一投影决定，底层集合 `fst a` 与 `fst b` 之间的路径已经给出路径 `a ≡ b`。于是全部工作归结为制造那条底层路径，它在 `vwise` 的前提下由 `extensionalV` 提供。
<!--ja-->
`L` の内部での外延性の形はこうです。台の二つの元がすべての台の元について所属が一致するなら、それらはパスとして等しい。証明は基底の階層へ帰着します。台は集合と構成可能性の証明書の対からなり、`↾-reflects` はそのような対が第一射影で決まるという原理です。基底の集合 `fst a` と `fst b` の間のパスがあれば、すでにパス `a ≡ b` が得られます。したがって仕事のすべてはその基底のパスを作ることにあり、`vwise` を前提に `extensionalV` がそれを供給します。
<!--/-->

```agda
extensionalL : {a b : S} → ((x : S) → (x ∈ˢ a) ≡ (x ∈ˢ b)) → a ≡ b
extensionalL {a} {b} h =
  ↾-reflects {𝒮 = 𝒮ᵥ} {M = isL} (extensionalV {a = fst a} {b = fst b} vwise)
  where
  vwise : (v : V ℓ) → (v ∈ fst a) ≡ (v ∈ fst b)
```

<!--en-->
The hypothesis `h` only speaks about carrier elements, that is, about constructible pairs. To extend it to an arbitrary `v` of the hierarchy, transitivity does the work: from `v ∈ fst a` and the certificate carried by `a`, `isL-trans` yields that `v` is itself constructible; pairing that certificate with `v` presents it as a carrier element, and `h` at that element gives a path of restricted memberships. Transporting `v∈a` along that path lands in `⟨ v ∈ fst b ⟩`, so `fwd` is a plain implication. Joining the two implications with `⇔toPath` yields the pointwise path of ambient membership that `extensionalV` demands.
<!--zh-->
假设 `h` 只谈及载体元素，即可构造的对。要把它扩展到层级中任意的 `v`，出力的是传递性：由 `v ∈ fst a` 与 `a` 所携带的证书，`isL-trans` 得出 `v` 自身可构造；把该证书与 `v` 配成对，就把 `v` 呈现为载体元素，`h` 在该元素处给出限制成员关系的路径。沿这条路径搬移 `v∈a` 便落在 `⟨ v ∈ fst b ⟩`，故 `fwd` 是一个普通的蕴涵。用 `⇔toPath` 把两个方向的蕴涵合成路径，便得到 `extensionalV` 所要求的周遭隶属的逐点路径。
<!--ja-->
仮定 `h` が語るのは台の元、つまり構成可能な対についてだけです。これを階層の任意の `v` に拡張するために働くのが推移性です。`v ∈ fst a` と `a` の携える証明書から、`isL-trans` が `v` 自身の構成可能性を導きます。その証明書を `v` と対にすれば `v` が台の元として提示され、その元での `h` が制限された所属のパスを与えます。このパスに沿って `v∈a` を輸送すれば `⟨ v ∈ fst b ⟩` に着くので、`fwd` は普通の含意です。二つの含意を `⇔toPath` でパスにまとめれば、`extensionalV` が要求する周囲の所属の各点パスが得られます。
<!--/-->

```agda
  vwise v = ⇔toPath fwd bwd
    where
    fwd : ⟨ v ∈ fst a ⟩ → ⟨ v ∈ fst b ⟩
    fwd v∈a = subst ⟨_⟩ (h (v , isL-trans v∈a (a .snd))) v∈a
    bwd : ⟨ v ∈ fst b ⟩ → ⟨ v ∈ fst a ⟩
```

<!--en-->
The backward direction is the same argument read from `b`, with `sym` because `h` points from `a` to `b`. This closes `extensionalL`. Regularity asks for something else: well-foundedness of the carrier's membership relation, as explicit accessibility data. For a pair `(v , p)`, meaning the set `v` together with its constructibility certificate, the ambient hierarchy already provides `Acc` for `v`; the task is to lift that data through the certificate.
<!--zh-->
反向是从 `b` 出发读同一个论证，因 `h` 的方向是从 `a` 指向 `b` 而加 `sym`。至此 `extensionalL` 完成。正则性要的是另一件事：把载体的成员关系的良基性作为显式的可及性数据。对对子 `(v , p)`，即集合 `v` 连同它的可构造性证书，周遭集合层级已经为 `v` 提供了 `Acc`；任务是把这份数据沿着证书抬上去。
<!--ja-->
逆向きは同じ議論を `b` から読んだもので、`h` の向きが `a` から `b` へ向くことに応じて `sym` が付きます。これで `extensionalL` が閉じます。正則性が求めるのは別のもの、すなわち台の所属関係の整礎性を明示的な可到達性データとして得ることです。対 `(v , p)`、つまり集合 `v` とその構成可能性の証明書に対しては、周囲の階層がすでに `v` の `Acc` を提供しています。課題はそのデータを証明書を通して持ち上げることです。
<!--/-->

```agda
    bwd v∈b = subst ⟨_⟩ (sym (h (v , isL-trans v∈b (b .snd)))) v∈b

regularityL : WellFounded _∈ᵗ_
regularityL (v , p) = accL v (regularityV v) p
  where
  module Vmem = hPropStructure 𝒮ᵥ
```

<!--en-->
The lifting is a recursion on the ambient accessibility data. If `u` is accessible, then by definition every ambient member `y` of `u` is accessible, and the clause `rec` packages exactly that. A member `(y , r)` of the restricted element `(u , q)` projects to an ambient member `y` of `u`, so `accL` may recurse on `rec y y∈` and attach the certificate `r` to the result. The restricted membership `y ∈ᵗ (u , q)` is inherited solely from the underlying relation `y ∈ u`; the certificate `r` belongs to the predecessor carrier element `(y , r)`, rather than to the membership proof. Thus accessibility transfers member by member along the underlying set.
<!--zh-->
这次抬升是对周遭可及性数据的一次递归。若 `u` 可及，则依定义 `u` 的每个周遭成员 `y` 都可及，子句 `rec` 打包的正是这一点。限制元素 `(u , q)` 的成员 `(y , r)` 投影为 `u` 的周遭成员 `y`，故 `accL` 可以对 `rec y y∈` 递归，并把证书 `r` 附到结果上。限制的成员关系 `y ∈ᵗ (u , q)` 只沿用底层关系 `y ∈ u`；证书 `r` 属于前驱载体元素 `(y , r)`，并不是成员证明的一部分。因此，可及性沿底层集合逐成员转移。
<!--ja-->
この持ち上げは、周囲の可到達性データに対する再帰です。`u` が可到達なら、定義により `u` のすべての周囲の元 `y` も可到達であり、句 `rec` はまさにそれをまとめています。制限された元 `(u , q)` の元 `(y , r)` は `u` の周囲の元 `y` へ射影されるので、`accL` は `rec y y∈` について再帰し、結果に証明書 `r` を付けて返せます。制限された所属 `y ∈ᵗ (u , q)` は基底の関係 `y ∈ u` だけを継承します。証明書 `r` は前駆の台の要素 `(y , r)` に属し、所属証明の一部ではありません。したがって、可到達性は基底の集合に沿って元ごとに移ります。
<!--/-->

```agda
  accL : (u : V ℓ) → Acc Vmem._∈ᵗ_ u → (q : u ∈ᶜ isL) → Acc _∈ᵗ_ (u , q)
  accL u (acc rec) q = acc (λ { (y , r) y∈ → accL y (rec y y∈) r })
```

<!--en-->
## Uniqueness from extensionality

`uniqueL`{.Agda} derives uniqueness from extensionality: any set realizing a fixed membership specification is unique, so the axiom fields still ahead need only a witness that merely exists.

The argument is the extensionality of the carrier applied to realizers. Two sets realizing the same predicate `Q` agree, at every carrier element, on the same truth value, namely `Q x`, so `extensionalL` equates them. Uniqueness in the form needed here is contractibility, and contractibility is a proposition, which is exactly what lets a merely existing realizer be turned into the contractibility data itself.
<!--zh-->
## 由外延性得到唯一性

`uniqueL`{.Agda} 从外延性导出唯一性：实现固定成员规格的集合是唯一的，因此后文尚未完成的公理字段只须给出一个「仅仅存在」的见证。

论证是把载体的外延性用在实现者上。实现同一谓词 `Q` 的两个集合，在每个载体元素处取同一真值，即 `Q x`，故 `extensionalL` 把它们等同。此处所需的唯一性形式是收缩性，而收缩性是命题；这恰好使「仅仅存在的实现者」能够被转换为收缩性数据本身。
<!--ja-->
## 外延性から得られる一意性

`uniqueL`{.Agda} は外延性から一意性を導きます。固定された所属の仕様を実現する集合は一意であり、したがって、このあと残っている公理のフィールドには「単に存在する」証人だけで足ります。

議論は、実現者に台の外延性を適用するものです。同じ述語 `Q` を実現する二つの集合は、すべての台の元で同じ真理値、すなわち `Q x` を取るので、`extensionalL` が両者を同一視します。ここで必要な一意性の形は収縮性であり、収縮性は命題です。まさにこのことにより、単に存在する実現者を収縮性のデータそのものへ変えられるのです。
<!--/-->

<!--en-->
Uniqueness of a realizer is contractibility data: a center, namely any realizing set, together with a path from the center to every realizing set. The path-producing part is `extensionalL`, since two realizing sets carry the same membership specification and hence coincide; the assembly of center and paths is `setOf-unique` applied to `extensionalL`. The second statement passes from mere existence: `PT.rec` may eliminate the truncated hypothesis because its target `isContr (SetOf Q)` is a proposition, and returns the same contractibility data. From here on, each remaining axiom field is proved by exhibiting one witness, supplied truncated.
<!--zh-->
实现者的唯一性是收缩性数据：一个中心，即任一实现该规格的集合，以及从中心到任一实现集合的路径。给出路径的部分是 `extensionalL`，因为两个实现集合携带同一成员规格，因而重合；中心与路径的组装则是对 `extensionalL` 应用 `setOf-unique`。第二条陈述从仅仅存在出发：`PT.rec` 之所以能消去截断的假设，是因为其目标 `isContr (SetOf Q)` 是命题，并返回同样的收缩性数据。从这里起，余下每条公理字段都通过展示一个见证、且以截断形式给出，来完成证明。
<!--ja-->
実現者の一意性は収縮性のデータです。すなわち中心、これは仕様を実現する任意の集合であり、および中心から任意の実現集合へのパスです。パスを生む部分は `extensionalL` です。実現する二つの集合は同じ所属の仕様を携えるので一致します。中心とパスの組み立ては、`extensionalL` に対する `setOf-unique` の適用です。第二の定理は単なる存在から出発します。仮定の切り詰めを `PT.rec` で除去できるのは、その目標 `isContr (SetOf Q)` が命題だからで、返るのは同じ収縮性のデータです。以後、残りの各公理フィールドは、証人を一つ、切り詰められた形で提示するだけで証明されます。
<!--/-->

```agda
uniqueL : (Q : S → hProp (ℓ-suc ℓ)) → SetOf Q → isContr (SetOf Q)
uniqueL = setOf-unique extensionalL

mere→uniqueL : (Q : S → hProp (ℓ-suc ℓ)) → ∥ SetOf Q ∥₁ → isContr (SetOf Q)
mere→uniqueL Q = PT.rec isPropIsContr (uniqueL Q)
```

<!--en-->
## The empty set

The false object-language formula carves the ambient empty set as a definable subset, and `hasEmptyL`{.Agda} packages its constructibility and empty-membership specification.

The falsehood of the object language carves nothing out of any stage: a member of `defSet ⊥̇` would carry a proof of falsehood at its index. So `defSet ⊥̇` is the empty set, one extensionality apart, and the empty set is therefore constructible. Its specification comes from the hierarchy, since membership in `L` is membership in the hierarchy, and the uniqueness principle of the previous section turns the witness into the contractibility the model demands.
<!--zh-->
## 空集

对象语言中的假公式把周遭空集定义为可定义子集，而 `hasEmptyL`{.Agda} 封装其可构造性与空成员规格。

对象语言的假在任何层中都定义不出元素：`defSet ⊥̇` 的成员会在其索引处包含一个假的证明。因此，`defSet ⊥̇` 经外延性等于空集，从而空集可构造。它的规格来自层级，因为 `L` 中的隶属就是层级中的隶属；而上一节的唯一性原理把这个见证变成模型所要求的收缩性数据。
<!--ja-->
## 空集合

対象言語の偽な論理式が周囲の空集合を定義可能部分集合として切り出し、`hasEmptyL`{.Agda} がその構成可能性と所属をもたないという仕様をまとめます。

対象言語の偽はどの段階からも何も切り出しません。`defSet ⊥̇` の元はその添字のところで偽の証明を伴うことになるからです。したがって `defSet ⊥̇` は外延性を一つ隔てただけで空集合であり、空集合は構成可能です。その仕様は階層から来ます。`L` における所属は階層における所属だからです。そして前節の一意性原理が、この証人をモデルが要求する収縮性のデータへ変えます。
<!--/-->

<!--en-->
The empty set is the first constructed set, and it needs no bounding at all: the argument `σ` ranges over arbitrary stages, with no ordinality hypothesis, because a formula defining the empty set can be read at any stage whatsoever. The certificate is the pairing of the object-language falsity `⊥̇` with the equation `defSet⊥≡∅`, and it is supplied truncated, as `𝒟ₒ-intro` expects.
<!--zh-->
空集是第一个被构造的集合，而且它完全不需要上界：实参 `σ` 跑遍任意层，没有序数性假设，因为定义空集的公式在任何层都可以解读。证书是对象语言的假 `⊥̇` 与等式 `defSet⊥≡∅` 组成的对，并按 `𝒟ₒ-intro` 的要求以截断形式给出。
<!--ja-->
空集合は最初に構成される集合であり、しかも上界をまったく必要としません。実引数 `σ` は任意の段階を渡り、順序数性の仮定もありません。空集合を定義する論理式はどの段階ででも読めるからです。証明書は、対象言語の偽 `⊥̇` と等式 `defSet⊥≡∅` の対であり、`𝒟ₒ-intro` が要求する切り詰められた形で与えられます。
<!--/-->

```agda
∅∈𝒟ₒ : (σ : V ℓ) → ⟨ ∅ ∈ 𝒟ₒ (Lset σ) ⟩
∅∈𝒟ₒ σ = 𝒟ₒ-intro (Lset σ) ∅ ∣ ⊥̇ , defSet⊥≡∅ ∣₁
  where
  module DefC = DefOf (Lset σ)
  defSet⊥≡∅ : DefC.defSet ⊥̇ ≡ ∅
```

<!--en-->
The equation is one extensionality against the ambient empty set, in two inclusions. The first is the substantive direction: a member `y` of the definable subset comes, by the reading lemma for `defSet`, as a truncated pair of an index `m` and a satisfaction proof `h` for `⊥̇`. Satisfaction of falsity is an empty host type, so `Empty.rec* h` refutes any such member. Since inclusion is stated as a proposition-valued statement, eliminating the truncation into it is legitimate.
<!--zh-->
这条等式是对照周遭空集的一次外延，分两个包含方向。第一向是有实质内容的方向：可定义子集的成员 `y`，经 `defSet` 的读法引理，呈现为索引 `m` 与 `⊥̇` 的满足证明 `h` 组成的截断对。假在对象语言中的满足是空的宿主类型，故 `Empty.rec* h` 反驳任何这样的成员。由于包含关系以命题值陈述，向它消去截断是合法的。
<!--ja-->
この等式は、周囲の空集合に対する一回の外延性で、二つの包含からなります。最初の向きが実質のある方向です。定義可能部分集合の元 `y` は、`defSet` の読み取り補題により、添字 `m` と `⊥̇` の充足の証明 `h` からなる切り詰められた対として現れます。偽の充足は空のホスト型なので、`Empty.rec* h` がそのような元を一切否定します。包含が命題値の主張として述べられているため、そこへの切り詰めの除去は正当です。
<!--/-->

```agda
  defSet⊥≡∅ = extensionality (DefC.defSet ⊥̇) ∅ (sub₁ , sub₂)
    where
    sub₁ : ⟨ DefC.defSet ⊥̇ ⊆ ∅ ⟩
    sub₁ y y∈ₛ = PT.rec (snd (y ∈ₛ ∅))
      (λ { ((m , h) , q) → Empty.rec* h })
```

<!--en-->
The second inclusion is vacuous: `∅-empty` turns any would-be member of the ambient empty set directly into a refutation. With both directions in hand, `defSet ⊥̇` and `∅` are equal as sets, and `∅∈𝒟ₒ` records that the empty set is a definable subset of an arbitrary stage. The closure lemma then applies one last time, at the stage `∅` itself, whose ordinality is the lemma `∅-ord`: the empty set is constructible, one successor above itself.
<!--zh-->
第二向是空洞的：`∅-empty` 把周遭空集的任何候选成员直接变成反驳。两个方向齐备后，`defSet ⊥̇` 与 `∅` 作为集合相等，`∅∈𝒟ₒ` 于是记录下空集是任意层的可定义子集。闭包引理随后最后再施展一次，就在层 `∅` 自身处，其序数性由引理 `∅-ord` 提供：空集可构造，位于其自身之上一个后继。
<!--ja-->
第二の包含は空虚です。`∅-empty` は周囲の空集合の候補となる元を直接的に反証へ変えます。両方向が揃えば、`defSet ⊥̇` と `∅` は集合として等しく、`∅∈𝒟ₒ` は空集合が任意の段階の定義可能部分集合であることを記録します。そこから閉包の補題が最後にもう一度だけ働き、今度は段階 `∅` そのもので、その順序数性は補題 `∅-ord` が供給します。空集合は、それ自身の一段上で構成可能なのです。
<!--/-->

```agda
      (∈∈ₛ {a = y} {b = DefC.defSet ⊥̇} .snd y∈ₛ)
    sub₂ : ⟨ ∅ ⊆ DefC.defSet ⊥̇ ⟩
    sub₂ y y∈ₛ = Empty.rec (∅-empty y y∈ₛ)

∅∈L : ⟨ isL ∅ ⟩
∅∈L = 𝒟ₒ→isL ∅ ∅-ord ∅ (∅∈𝒟ₒ ∅)
```

<!--en-->
Packaging mirrors the underlying set: `∅ʟ` is the pair of `∅` with its constructibility certificate, an element of the carrier `S`. The model's existence statement requires a unique set with no members. The witness offered is `∅ʟ` together with the specification taken from the hierarchy, `empty-spec` read at the underlying set of any candidate; uniqueness then follows by `uniqueL`. This is the first field, and the pattern of the next two is already visible in it: bound, carve, close.
<!--zh-->
打包方式照应底层集合：`∅ʟ` 是 `∅` 连同其可构造性证书组成的对，是载体 `S` 的一个元素。模型的存在性要求「没有成员的集合唯一存在」。所给出的见证是 `∅ʟ`，连同从层级取来的规格，即对任何候选集合的底层集合读取 `empty-spec`；唯一性则由 `uniqueL` 得到。这是第一条字段，而下两条构造的模式在它身上已经可见：找界、刻出、收尾。
<!--ja-->
パッケージ化は基底の集合に対応しています。`∅ʟ` は `∅` とその構成可能性の証明書の対であり、台 `S` の元です。モデルの存在主張は、元をひとつももたない集合が一意に存在することを要求します。提示される証人は `∅ʟ` であり、仕様は階層から取られたもので、候補となる集合の基底の集合で `empty-spec` を読んだものです。一意性は `uniqueL` によって従います。これが最初のフィールドであり、次の二つの構成の型がすでにここに見えています。すなわち、上界を定め、切り出し、締めくくる、という型です。
<!--/-->

```agda

∅ʟ : S
∅ʟ = ∅ , ∅∈L

hasEmptyL : isContr (SetOf (λ _ → ⊥))
hasEmptyL = uniqueL _ (∅ʟ , (λ x → empty-spec (fst x)))
```

<!--en-->
## Pairing, bounded by a stage

For two members of one stage, a two-constant disjunction carves their unordered pair as a definable subset, and the derived statements place the singleton one stage up and the Kuratowski ordered-pair code two stages up.

The unordered pair of two members of a stage is a definable subset of that stage: each of them is `⟪ Lset σ ⟫↪` of some index, and the formula naming those two indices carves out exactly the pair. Checking that takes one extensionality against the hierarchy's own pairing axiom, in both directions: a member of the definable subset satisfies the disjunction, hence is one of the two; and each of the two satisfies it, hence is a member.

Nothing in the argument concerns the model. What it says is a fact about the tower, and it is stated as one: an ordered pair in Kuratowski's encoding is two unordered pairs deep, so it sits two stages above its entries.

Ordinality is not asked for, exactly as the successor identity does not ask for it, and for the same reason: carving is not comparison. The singleton is the degenerate pair, and the ordered pair is the pair of a singleton with a pair.
<!--zh-->
## 受层界住的配对

对同一层的两个成员，一条含两个常元的析取公式把其无序对定义为该可定义子集；派生的结果把单点集安置在高一层处，把 Kuratowski 有序对码安置在高两层处。

一层的两个成员，其无序对是该层的可定义子集：二者各是某个索引的 `⟪ Lset σ ⟫↪`，而点名那两个索引的公式恰好定义出这个对。验证它要对照层级自己的配对公理做一次双向外延：可定义子集的成员满足那个析取，故是二者之一；而二者各自满足它，故是成员。

论证里没有一处关乎模型，说的是塔本身的一条事实，故照这样陈述：Kuratowski 编码下的有序对嵌套了两层无序对，因此落在其条目之上两层处。

此处不涉及序数性，后继恒等式也不涉及，理由相同：这里做的是构造，而非比较。单点集是退化的对，而有序对是单点集与对所成的对。
<!--ja-->
## 一つの段階内で対を作る

一つの段階の二要素について、二定数の論理和がその非順序対を定義可能部分集合として切り出します。派生する結果は、一元集合を一段階上へ、Kuratowski の順序対の符号を二段階上へ置きます。

一つの段階の二つの要素の非順序対は、その段階の定義可能部分集合です。それぞれの要素はある添字の `⟪ Lset σ ⟫↪` であり、その二つの添字を名指す論理式がちょうどこの対を切り出します。確認には、階層そのものの対の公理と突き合わせて一方向ずつの外延性が要ります。定義可能部分集合の元は論理和を充足するので二者のいずれかであり、逆に二者のそれぞれは論理和を充足するので元です。

この議論のどこにもモデルは現れません。述べられているのは塔そのものについての事実であり、そのように述べられます。Kuratowski 符号の順序対は非順序対を二段重ねたものなので、その項目より二段階上の段階にあります。

順序数性は要求されません。後者の恒等式が要求しないのと同じ理由で、切り出しは比較ではないからです。一元集合は退化した対であり、順序対は一元集合と対の対です。
<!--/-->

<!--en-->
The statement assumes only that `x` and `y` lie in the stage `Lset σ`; no ordinality of `σ` is required, because carving a subset needs no comparison of stages. The certificate is assembled by `𝒟ₒ-intro`: a formula `φ` together with the equation `defSet≡` saying that φ's extension inside the stage is exactly `⁅ x , y ⁆`, supplied merely, as the definability operator's interface expects.
<!--zh-->
这条陈述只假设 `x` 与 `y` 落在层 `Lset σ` 中；不要求 `σ` 的序数性，因为刻出一个子集不需要比较层。证书由 `𝒟ₒ-intro` 组装：一条公式 `φ`，连同说明 φ 在该层中的外延恰为 `⁅ x , y ⁆` 的等式 `defSet≡`，并按可定义性算子的接口要求以截断形式给出。
<!--ja-->
この主張は、`x` と `y` が段階 `Lset σ` に属することだけを仮定します。`σ` の順序数性は要求されません。部分集合を切り出すのに段階の比較は要らないからです。証明書は `𝒟ₒ-intro` で組み立てます。すなわち論理式 `φ` と、φ のこの段階での外延がちょうど `⁅ x , y ⁆` であることを言う等式 `defSet≡` を、定義可能性の演算子のインターフェースが期待する切り詰められた形で対にするのです。
<!--/-->

```agda
pair∈𝒟ₒ : (σ x y : V ℓ) → ⟨ x ∈ Lset σ ⟩ → ⟨ y ∈ Lset σ ⟩
        → ⟨ ⁅ x , y ⁆ ∈ 𝒟ₒ (Lset σ) ⟩
pair∈𝒟ₒ σ x y x∈ y∈ = 𝒟ₒ-intro (Lset σ) ⁅ x , y ⁆ ∣ φ , defSet≡ ∣₁
  where
  module DefC = DefOf (Lset σ)
```

<!--en-->
The formula must name constants drawn from the small presentation `⟪ Lset σ ⟫` of the stage. Applying `∈-asFiber` to the two membership proofs gives actual indices `mₓ` and `mᵧ`, together with paths `qₓ : ⟪ Lset σ ⟫↪ mₓ ≡ x` and `qᵧ : ⟪ Lset σ ⟫↪ mᵧ ≡ y`. This direct recovery is available because the presentation embedding has propositional fibers; the membership hypotheses are not treated as an outer truncation here.
<!--zh-->
公式必须以层的小呈现 `⟪ Lset σ ⟫` 中的元素为常元。对两条隶属证明应用 `∈-asFiber`，得到实际索引 `mₓ`、`mᵧ`，以及路径 `qₓ : ⟪ Lset σ ⟫↪ mₓ ≡ x` 与 `qᵧ : ⟪ Lset σ ⟫↪ mᵧ ≡ y`。呈现嵌入的纤维是命题，所以这里可以直接恢复这些数据；论证没有把隶属假设当作另一个外层截断。
<!--ja-->
論理式は段階の小さな提示 `⟪ Lset σ ⟫` から定数を取る必要があります。二つの所属の証明に `∈-asFiber` を適用すると、実際の添字 `mₓ`、`mᵧ` と、パス `qₓ : ⟪ Lset σ ⟫↪ mₓ ≡ x`、`qᵧ : ⟪ Lset σ ⟫↪ mᵧ ≡ y` が得られます。提示の埋め込みのファイバーが命題なので、このデータを直接復元できます。ここでは所属の仮定を別の外側の切り詰めとして扱いません。
<!--/-->

```agda
  mₓ = ∈-asFiber {a = x} {b = Lset σ} x∈ .fst
  qₓ : ⟪ Lset σ ⟫↪ mₓ ≡ x
  qₓ = ∈-asFiber {a = x} {b = Lset σ} x∈ .snd
  mᵧ = ∈-asFiber {a = y} {b = Lset σ} y∈ .fst
  qᵧ : ⟪ Lset σ ⟫↪ mᵧ ≡ y
```

<!--en-->
The formula has one free-variable slot and reads: the variable equals the constant `mₓ`, or it equals the constant `mᵧ`. Its claimed extension is the unordered pair of `x` and `y`. The proof does not identify the extension with that pair directly; it first identifies it with the pair of the embedded representatives, where the constants actually live, and then transports the whole equation along `qₓ` and `qᵧ` by congruence under `⁅_,_⁆`.
<!--zh-->
公式有一个自由变元槽，读作：变元等于常元 `mₓ`，或等于常元 `mᵧ`。它被断言的外延是 `x` 与 `y` 的无序对。证明并不直接把外延与这个对等同；它先把外延与嵌入代表元组成的对等同，常元实际上就在那里，再对构造子 `⁅_,_⁆` 应用 `cong₂`沿 `qₓ` 与 `qᵧ` 搬移整条等式。
<!--ja-->
論理式は自由変数のスロットをひとつもち、「変数は定数 `mₓ` に等しい、または定数 `mᵧ` に等しい」と読みます。その外延として主張されるのは `x` と `y` の非順序対です。証明は外延をこの対に直接同一視するのではありません。まず外延を埋め込まれた代表元の対、つまり定数が実際に住んでいる対と同一視し、それから構成子 `⁅_,_⁆` への `cong₂` の適用によって等式全体を `qₓ` と `qᵧ` に沿って輸送します。
<!--/-->

```agda
  qᵧ = ∈-asFiber {a = y} {b = Lset σ} y∈ .snd

  φ : Formula ⟪ Lset σ ⟫ 1
  φ = (var zero ≐ con mₓ) ∨̇ (var zero ≐ con mᵧ)

  defSet≡ : DefC.defSet φ ≡ ⁅ x , y ⁆
  defSet≡ =
```

<!--en-->
The first half of the identification is one extensionality, from the definable subset to the pair of embedded representatives, split into two inclusions. The direction shown here says: whatever satisfies φ is one of the two named elements.
<!--zh-->
等同的前一半是一次外延性，从可定义子集到嵌入代表元的对，分为两个包含。此处展示的方向说的是：凡满足 φ 者，都是那两个被点名元素之一。
<!--ja-->
同一視の前半は一回の外延性で、定義可能部分集合から埋め込まれた代表元の対への向きであり、二つの包含に分かれます。ここで示す向きが言うのは、φ を充足するものはすべて名指された二つの要素のいずれかである、ということです。
<!--/-->

```agda
      extensionality (DefC.defSet φ) ⁅ ⟪ Lset σ ⟫↪ mₓ , ⟪ Lset σ ⟫↪ mᵧ ⁆
        (sub₁ , sub₂)
    ∙ cong₂ ⁅_,_⁆ qₓ qᵧ
    where
    sub₁ : ⟨ DefC.defSet φ ⊆ ⁅ ⟪ Lset σ ⟫↪ mₓ , ⟪ Lset σ ⟫↪ mᵧ ⁆ ⟩
```

<!--en-->
A member `w` of the definable subset is presented, by the reading lemma, as a truncated pair of an index `m` and a satisfaction proof for φ at the environment naming `m`. The satisfaction of a disjunction of equalities records, merely, that the element named by `m` equals one of the two constants. That truncated disjunction is exactly the hypothesis the hierarchy's pairing characterization requires in its right-to-left direction, so `pairing-ax` places the embedded element `⟪ Lset σ ⟫↪ m` inside the pair of embedded representatives. The transport along the path `q` identifying `w` with the embedded index then finishes the inclusion.
<!--zh-->
可定义子集的成员 `w`，经读法引理，呈现为索引 `m` 与「在点名 `m` 的赋值下 φ 的满足证明」组成的截断对。等式析取的满足只是记录：`m` 所名指的元素等于两个常元之一。而这条截断析取恰好是层级的配对刻画在从右到左方向所需的假设，于是 `pairing-ax` 把嵌入元素 `⟪ Lset σ ⟫↪ m` 放进嵌入代表元组成的对中。再沿把 `w` 与嵌入索引等同的路径 `q` 做搬移，包含即告完成。
<!--ja-->
定義可能部分集合の元 `w` は、読み取り補題によって、添字 `m` と「`m` を名指す環境での φ の充足の証明」からなる切り詰められた対として現れます。等式の論理和の充足が記録するのは、`m` の名指す要素が二つの定数のいずれかに等しいこと、単にそれだけです。この切り詰められた論理和は、階層の対の特徴づけが右から左の向きで必要とする仮定にちょうど一致するので、`pairing-ax` は埋め込まれた要素 `⟪ Lset σ ⟫↪ m` を埋め込まれた代表元の対の中に置きます。そのうえで、`w` を埋め込まれた添字と同一視するパス `q` に沿った輸送が包含を仕上げます。
<!--/-->

```agda
    sub₁ w w∈ₛ = PT.rec (snd (w ∈ₛ ⁅ ⟪ Lset σ ⟫↪ mₓ , ⟪ Lset σ ⟫↪ mᵧ ⁆))
      (λ { ((m , h) , q) →
        subst (λ v → ⟨ v ∈ₛ ⁅ ⟪ Lset σ ⟫↪ mₓ , ⟪ Lset σ ⟫↪ mᵧ ⁆ ⟩) q
          (pairing-ax (⟪ Lset σ ⟫↪ mₓ) (⟪ Lset σ ⟫↪ mᵧ) (⟪ Lset σ ⟫↪ m) .snd
            (subst ⟨_⟩ (DefC.defSet-mem φ m) ∣ (m , h) , refl ∣₁)) })
```

<!--en-->
The reverse inclusion reads the hierarchy's pairing characterization in its other direction. A member `w` of the pair of embedded representatives is, merely, equal to one of the two entries. Each of the two branches supplies the same helper with the corresponding representative: knowing which representative `w` equals, one shows `w` satisfies φ at that representative's constant, and is therefore a member of the definable subset.
<!--zh-->
反向包含把层级的配对刻画按另一方向读取。嵌入代表元之对的成员 `w`，仅仅是等于两个条目之一。两个分支各自把相应的代表元交给同一个辅助引理：既然知道 `w` 等于哪个代表元，就能证明 `w` 在该代表元的常元处满足 φ，因而是可定义子集的成员。
<!--ja-->
逆の包含は、階層の対の特徴づけをもう一方の向きで読みます。埋め込まれた代表元の対の元 `w` は、二つの項のいずれかに単に等しいことが分かります。二つの分岐はそれぞれ、対応する代表元を同じ補助補題に渡します。`w` がどちらの代表元に等しいかが分かれば、`w` がその代表元の定数のところで φ を充足し、したがって定義可能部分集合の元であることを示せます。
<!--/-->

```agda
      (∈∈ₛ {a = w} {b = DefC.defSet φ} .snd w∈ₛ)
    sub₂ : ⟨ ⁅ ⟪ Lset σ ⟫↪ mₓ , ⟪ Lset σ ⟫↪ mᵧ ⁆ ⊆ DefC.defSet φ ⟩
    sub₂ w w∈ₛ = PT.rec (snd (w ∈ₛ DefC.defSet φ))
      (λ { (inl p) → memOf mₓ ∣ inl refl ∣₁ p
         ; (inr p) → memOf mᵧ ∣ inr refl ∣₁ p })
```

<!--en-->
The helper `memOf` takes a representative `mᵢ`, a satisfaction proof for φ at the constant naming `mᵢ`, and a path identifying `w` with the embedded element of `mᵢ`. The membership reading of `defSet` turns satisfaction at the constant into membership of the embedded element in the definable subset; transporting along the path, in the direction `sym p`, moves that membership to `w`. With both inclusions proved, the extensionality yields the equation with the pair of embedded representatives, and the congruence step under `⁅_,_⁆` rewrites that pair into `⁅ x , y ⁆` along the paths `qₓ` and `qᵧ`.
<!--zh-->
辅助引理 `memOf` 接收一个代表元 `mᵢ`、φ 在名指 `mᵢ` 的常元处的满足证明，以及把 `w` 与 `mᵢ` 的嵌入元素等同的路径。`defSet` 的隶属读法把在常元处的满足转成嵌入元素在可定义子集中的隶属；沿路径 (方向为 `sym p`) 搬移，就把这条隶属搬到 `w` 上。两个包含证毕后，外延性给出与嵌入代表元之对的等式，再对构造子 `⁅_,_⁆` 应用 `cong₂`，沿路径 `qₓ` 与 `qᵧ` 把那个对改写成 `⁅ x , y ⁆`。
<!--ja-->
補助補題 `memOf` は、代表元 `mᵢ`、`mᵢ` を名指す定数のところでの φ の充足の証明、そして `w` を `mᵢ` の埋め込まれた要素と同一視するパスを受け取ります。`defSet` の所属の読みは、定数のところでの充足を、埋め込まれた要素の定義可能部分集合への所属に変えます。パスに沿った輸送 (向きは `sym p`) がその所属を `w` へ移します。両方の包含が証明されれば、外延性が埋め込まれた代表元の対との等式を与え、つづく構成子 `⁅_,_⁆` への `cong₂` の適用の一歩が、パス `qₓ` と `qᵧ` に沿ってその対を `⁅ x , y ⁆` へ書き換えます。
<!--/-->

```agda
      (pairing-ax (⟪ Lset σ ⟫↪ mₓ) (⟪ Lset σ ⟫↪ mᵧ) w .fst w∈ₛ)
      where
      memOf : (mᵢ : ⟪ Lset σ ⟫) → ⟨ (DefC.ι mᵢ ∷ []) DefC.⊨ᵐ φ ⟩
            → w ≡ ⟪ Lset σ ⟫↪ mᵢ → ⟨ w ∈ₛ DefC.defSet φ ⟩
      memOf mᵢ sat p = subst (λ v → ⟨ v ∈ₛ DefC.defSet φ ⟩) (sym p)
```

<!--en-->
The first derived result converts the definability statement into membership in a stage. The successor identity proved earlier in this chapter says that `Lset (sucV σ)` is exactly `𝒟ₒ (Lset σ)`, so transporting the conclusion of `pair∈𝒟ₒ` along that identity, in the direction `sym`, yields `⟨ ⁅ x , y ⁆ ∈ Lset (sucV σ) ⟩`: the unordered pair of two members of a stage is contained in the displayed next-stage bound.
<!--zh-->
第一条派生结果把可定义性陈述转成对某一层的隶属。本章前文证明的后继恒等式说 `Lset (sucV σ)` 恰是 `𝒟ₒ (Lset σ)`，故沿该恒等式 (方向取 `sym`) 搬移 `pair∈𝒟ₒ` 的结论，便得 `⟨ ⁅ x , y ⁆ ∈ Lset (sucV σ) ⟩`：一层两个成员的无序对由此得到的上界是下一层。
<!--ja-->
最初の派生結果は、定義可能性の主張を段階への所属に変えるものです。この章の前の方で証明した後者の恒等式によれば `Lset (sucV σ)` はちょうど `𝒟ₒ (Lset σ)` なので、その恒等式に沿って (向きは `sym`)`pair∈𝒟ₒ` の結論を輸送すれば `⟨ ⁅ x , y ⁆ ∈ Lset (sucV σ) ⟩` が得られます。すなわち、一つの段階の二つの要素の非順序対は、ここで示された次段階を上界としてもちます。
<!--/-->

```agda
        (∈∈ₛ {a = ⟪ Lset σ ⟫↪ mᵢ} {b = DefC.defSet φ} .fst
          (subst ⟨_⟩ (sym (DefC.defSet-mem φ mᵢ)) sat))

pair∈Lset-suc : (σ x y : V ℓ) → ⟨ x ∈ Lset σ ⟩ → ⟨ y ∈ Lset σ ⟩
              → ⟨ ⁅ x , y ⁆ ∈ Lset (sucV σ) ⟩
pair∈Lset-suc σ x y x∈ y∈ =
```

<!--en-->
The singleton is the degenerate case. Applying the pair placement to `x` twice gives the pair `⁅ x , x ⁆` in the next stage, and the hierarchy's identification `pair-singleton` of `⁅ x , x ⁆` with `⁅ x ⁆s` transports that membership onto the singleton `⁅ x ⁆s`.
<!--zh-->
单点集是退化情形。把配对安置对 `x` 施用两次，得到下一层中的 `⁅ x , x ⁆`；层级把 `⁅ x , x ⁆` 等同于 `⁅ x ⁆s` 的 `pair-singleton` 再把这条隶属搬到单点集 `⁅ x ⁆s` 上。
<!--ja-->
一元集合は退化した場合です。対の配置を `x` に二度適用すれば、次の段階に対 `⁅ x , x ⁆` が得られ、`⁅ x , x ⁆` を `⁅ x ⁆s` と同一視する階層の `pair-singleton` がその所属を一元集合 `⁅ x ⁆s` へ輸送します。
<!--/-->

```agda
  subst (λ w → ⟨ ⁅ x , y ⁆ ∈ w ⟩) (sym (Lset-suc σ)) (pair∈𝒟ₒ σ x y x∈ y∈)

sgl∈Lset-suc : (σ x : V ℓ) → ⟨ x ∈ Lset σ ⟩ → ⟨ ⁅ x ⁆s ∈ Lset (sucV σ) ⟩
sgl∈Lset-suc σ x x∈ = subst (λ w → ⟨ w ∈ Lset (sucV σ) ⟩) (pair-singleton x)
  (pair∈Lset-suc σ x x x∈ x∈)

pr∈Lset-suc : (σ x y : V ℓ) → ⟨ x ∈ Lset σ ⟩ → ⟨ y ∈ Lset σ ⟩
```

<!--en-->
The ordered pair code `pr x y` is the pair whose two entries are the singleton `⁅ x ⁆s` and the unordered pair `⁅ x , y ⁆`. Both entries lie in `Lset (sucV σ)`, the first by the singleton result and the second by the pair result, so the outer unordered pair can be placed at the stage one further up: `pr x y` lies in `Lset (sucV (sucV σ))`. Because the Kuratowski code nests one unordered pair inside another, two applications of pair closure give the displayed two-successor upper bound for the ordered-pair code; this does not assert that the code first appears there.
<!--zh-->
有序对码 `pr x y` 是以单点集 `⁅ x ⁆s` 与无序对 `⁅ x , y ⁆` 为两个条目的对。两个条目都落在 `Lset (sucV σ)` 中，第一个由单点集结果、第二个由配对结果给出，于是外层无序对可以安置在再高一个的层处：`pr x y` 落在 `Lset (sucV (sucV σ))` 中。由于 Kuratowski 码把一个无序对嵌套在另一个之内，两次使用配对闭包给出有序对码的这个双后继上界，但并不声称它最早恰在此处出现。
<!--ja-->
順序対の符号 `pr x y` は、一元集合 `⁅ x ⁆s` と非順序対 `⁅ x , y ⁆` を二つの項にもつ対です。二つの項はいずれも `Lset (sucV σ)` にあり、第一は一元集合の結果から、第二は対の結果から従うので、外側の非順序対はさらに一段階上の段階に置けます。すなわち `pr x y` は `Lset (sucV (sucV σ))` にあります。Kuratowski 符号は一つの非順序対を別の非順序対の内側に入れ子にするので、対の閉包を二回使うことで順序対符号の二後者段階という上界が得られますが、そこで初めて現れるとは主張していません。
<!--/-->

```agda
            → ⟨ pr x y ∈ Lset (sucV (sucV σ)) ⟩
pr∈Lset-suc σ x y x∈ y∈ = pair∈Lset-suc (sucV σ) ⁅ x ⁆s ⁅ x , y ⁆
  (sgl∈Lset-suc σ x x∈) (pair∈Lset-suc σ x y x∈ y∈)
```

<!--en-->
## Pairing

`hasPairL`{.Agda} first places two arbitrary constructible sets in a common stage, then applies the bounded pair construction and the uniqueness principle.

The witness for the axiom is the unordered pair of the two arguments at a common ordinal stage, proved constructible by the lemma of the previous section; the specification is the hierarchy's own classification of the unordered pair, read at the underlying sets. Uniqueness then comes from extensionality.
<!--zh-->
## 配对

`hasPairL`{.Agda} 先把任意两个可构造集合放进公共层，再施用有界配对构造与唯一性原理。

这条公理的见证是两个实参在公共序数层处的无序对，其可构造性由上一节的引理证明；规格是层级自己对无序对的分类，在底层集合处读取。唯一性则来自外延性。
<!--ja-->
## 対の公理

`hasPairL`{.Agda} はまず任意の二つの構成可能集合を共通段階へ入れ、次に有界な対の構成と一意性原理を適用します。

この公理の証人は、二つの実引数の共通の順序数段階における非順序対であり、その構成可能性は前節の補題が示します。仕様は、非順序対に対する階層そのものの分類を基底の集合で読んだものです。一意性はその後、外延性から来ます。
<!--/-->

<!--en-->
The pairing field is stated over two arguments. Its predicate `Q x` says that an element `x` is equal to `a` or to `b`, with the disjunction interpreted in the model's truth values. A set realizes the field when its elements are exactly those satisfying `Q`. The construction `mkPair` assumes a common ordinal stage containing the underlying sets of both arguments, which is precisely what the bounding step supplies.
<!--zh-->
配对字段以两个实参为参数。谓词 `Q x` 说元素 `x` 等于 `a` 或等于 `b`，其中析取在模型的真值中解释。一个集合实现该字段，是指它的元素恰为满足 `Q` 的元素。构造 `mkPair` 假设已有一个公共序数层包含两个实参的底层集合，而这正是上界步骤所供给的。
<!--ja-->
対のフィールドは二つの実引数について述べられます。述語 `Q x` は、要素 `x` が `a` または `b` に等しいことを、モデルの真理値で解釈した論理和として表します。集合がこのフィールドを実現するとは、その要素がちょうど `Q` を満たすことです。構成 `mkPair` は、両方の実引数の基底集合を含む共通の順序数段階を仮定し、上界の段階がまさにそれを供給します。
<!--/-->

```agda
module PairOf (a b : S) where
  Q : S → hProp (ℓ-suc ℓ)
  Q x = (x ≈ˢ a) ⊔ (x ≈ˢ b)

  mkPair : (σ : V ℓ) → IsOrd σ → ⟨ fst a ∈ Lset σ ⟩ → ⟨ fst b ∈ Lset σ ⟩
         → SetOf Q
```

<!--en-->
The witness is the ambient unordered pair of the underlying sets, packaged with its constructibility certificate. That certificate comes from the bounded construction: the pair of two members of `Lset σ` is a definable subset there, and the lemma `𝒟ₒ→isL` lifts a definable subset of an ordinal stage into `L`. The specification is the hierarchy's own classification of the unordered pair, `pair-spec`, read at the underlying sets; restricted membership is ambient membership on carriers, so the model's reading of the field coincides with the hierarchy's classification.
<!--zh-->
见证是底层集合的周遭无序对，连同其可构造性证书打包。该证书来自有界构造：`Lset σ` 两个成员的对是那里的可定义子集，而引理 `𝒟ₒ→isL` 把序数层的可定义子集抬进 `L`。规格是层级自己对无序对的分类 `pair-spec`，在底层集合处读取；限制载体上的隶属就是周遭隶属，故模型对该字段的解读与层级的分类一致。
<!--ja-->
証人は基底の集合の周囲の非順序対であり、その構成可能性の証明書とともにまとめられます。証明書は有界な構成から来ます。`Lset σ` の二つの要素の対はそこの定義可能部分集合であり、補題 `𝒟ₒ→isL` が順序数段階の定義可能部分集合を `L` へ引き上げます。仕様は、非順序対に対する階層そのものの分類 `pair-spec` を基底の集合で読んだものです。制限された台での所属は周囲の所属ですから、モデルによるこのフィールドの読みは階層の分類と一致します。
<!--/-->

```agda
  mkPair σ oσ fa∈ fb∈ = pairElt , (λ z → pair-spec (fst a) (fst b) (fst z))
    where
    pairElt : S
    pairElt = ⁅ fst a , fst b ⁆
            , 𝒟ₒ→isL σ oσ ⁅ fst a , fst b ⁆ (pair∈𝒟ₒ σ (fst a) (fst b) fa∈ fb∈)
```

<!--en-->
The construction is not yet the field: it needs a stage, and only its mere existence is available. `build` eliminates the truncation from `isL-directed` with `PT.rec`, whose target `∥ SetOf Q ∥₁` is itself truncated, so the two certificates of constructibility for `a` and `b` may be opened just far enough to read off the common stage and the two memberships, and `mkPair` runs there. No stage is chosen for the outside world.
<!--zh-->
这个构造还不是那条字段：它需要一层，而手头只有其「仅仅存在」。`build` 用 `PT.rec` 消去 `isL-directed` 的截断，其目标 `∥ SetOf Q ∥₁` 本身就是截断的，因此可以把 `a` 与 `b` 的两份可构造性证书打开到恰好读出公共层与两条隶属的程度，然后在该处运行 `mkPair`。全程没有向外部世界选定任何层。
<!--ja-->
この構成はまだフィールドではありません。段階が必要ですが、手もとにあるのはその単なる存在だけです。`build` は `PT.rec` で `isL-directed` の切り詰めを除去します。その目標 `∥ SetOf Q ∥₁` 自身が切り詰められているので、`a` と `b` の二つの構成可能性の証明書を、共通段階と二つの所属が読み取れるところまで開けばよく、そこで `mkPair` が対を構成します。外部に向かって段階が選ばれることはありません。
<!--/-->

```agda

  build : ∥ SetOf Q ∥₁
  build = PT.rec squash₁
    (λ { (σ , (oσ , (fa∈ , fb∈))) → ∣ mkPair σ oσ fa∈ fb∈ ∣₁ })
    (isL-directed (fst a) (fst b) (a .snd) (b .snd))

hasPairL : (a b : S) → isContr (SetOf (λ x → (x ≈ˢ a) ⊔ (x ≈ˢ b)))
```

<!--en-->
The field `hasPairL` asks for contractibility of the type of realizers: a canonical realizer together with a path from it to every other realizer. The truncated common-stage bound is eliminated only into the truncated existence `∥ SetOf Q ∥₁`; within that elimination, `mkPair` constructs a realizer from the stage and its two membership proofs. Then `mere→uniqueL`, using `uniqueL` and extensionality, turns mere existence plus uniqueness into an explicit center of contraction. Thus the proof makes no arbitrary choice of a common stage, while its final result does contain the definite canonical realizer required by `isContr`.
<!--zh-->
字段 `hasPairL` 要求实现者类型具有收缩性：给出一个典范实现者，以及从中心到任一实现者的路径。公共层的截断上界只被消去到截断存在 `∥ SetOf Q ∥₁` 中；在该消去内部，`mkPair` 由层及两条隶属证明构造实现者。随后 `mere→uniqueL` 借助 `uniqueL` 与外延性，把仅仅存在与唯一性合成为明确的收缩中心。因此，证明不任意选择公共层，而最终结果确实含有 `isContr` 所要求的明确典范实现者。
<!--ja-->
フィールド `hasPairL` が要求するのは、実現者の型の可縮性、すなわち標準的な実現者と、中心から任意の実現者へのパスです。切り詰められた共通段階の上界は、切り詰められた存在 `∥ SetOf Q ∥₁` の中へだけ除去され、その内部で `mkPair` が段階と二つの所属証明から実現者を構成します。つぎに `mere→uniqueL` は `uniqueL` と外延性を用い、単なる存在と一意性から明示的な可縮中心を得ます。したがって共通段階を恣意的に選ぶ必要はありませんが、最終結果には `isContr` が要求する明確な標準的実現者が含まれます。
<!--/-->

```agda
hasPairL a b = mere→uniqueL (PairOf.Q a b) (PairOf.build a b)
```

<!--en-->
## Union

Union needs no bounding search: a single stage containing the argument already suffices. Because the stage `Lset σ` is transitive, every member of a member of `fst a` is again in the stage, so a bounded existential formula, "some member of the argument has me as a member", carves out exactly the ambient union `⋃ (fst a)`.

The extensional equation is proved by two inclusions. One direction reads the formula's satisfaction: a witness `v` with `y` a member of `v` is exactly what the hierarchy's union classification asks for. The other direction starts from the union classification and must first pull the intermediate member `v` into the stage, which is precisely what stage transitivity does, applied twice. The final specification compares two quantifiers: the constructible condition quantifies over carrier witnesses only, while the hierarchy's union law quantifies over all of `V`, and `isL-trans` identifies the two ranges in both directions. With union in place, this chapter has proved five axioms: extensionality, regularity, the empty set, pairing, and union.
<!--zh-->
## 并

并不需要寻找上界：一个装着实参的层就足够了。由于层 `Lset σ` 是传递的，`fst a` 的成员的每个成员也仍在该层中，于是有界存在公式「实参的某个成员以我为成员」恰好刻出周遭并 `⋃ (fst a)`。

外延等式由两个包含方向证明。一个方向读出公式的满足：一个见证 `v` 使 `y` 属于 `v`，恰好是层级的并刻画所要求的输入。另一个方向从并刻画出发，必须先把中间成员 `v` 拉进层，而这正是层传递性所做的，施用两次。最后的规格比较两个量词：可构造条件只对载体见证量化，而层级的并律对全部 `V` 量化，`isL-trans` 在两个方向上把这两个范围等同起来。并就位之后，本章已证明五条公理：外延、正则、空集、配对与并。
<!--ja-->
## 和集合の公理

和集合には上界の探索が要りません。実引数を含む一つの段階で足ります。段階 `Lset σ` は推移的なので、`fst a` の要素の各要素もやはり段階にあるからです。そこで有界存在の論理式、「実引数のある要素が自分を要素にもつ」が、周囲の和集合 `⋃ (fst a)` をちょうど切り出します。

外延的な等式は二つの包含で証明されます。一つの向きは論理式の充足を読みます。`y` を要素にもつ証人 `v` は、階層の和集合の分類が求める入力にちょうど一致します。もう一つの向きは和集合の分類から始まり、途中の要素 `v` をまず段階へ引き込まねばなりません。これこそ段階の推移性が二度適用されて果たす役目です。最後の仕様は二つの量化子を比べます。構成可能な条件は台の証人の上だけで量化し、階層の和集合の法則はすべての `V` の上で量化しますが、`isL-trans` が両方向でこの二つの範囲を同一視します。和集合が整ったとき、本章は五つの公理、すなわち外延性、正則性、空集合、対、和集合を証明し終えています。
<!--/-->

<!--en-->
The membership condition `Q` is an indexed disjunction inside the model's truth values: `x` realizes the union when, for some `y` that is a member of `a`, `x` is a member of `y`. The construction `mkUnion` carries a single hypothesis, that one ordinal stage `σ` contains the underlying set of `a`. There is no second argument to house, so unlike pairing no bounding ordinal is needed; the stage that `a` itself already has is enough.
<!--zh-->
成员条件 `Q` 是模型真值内部的一条带索引析取：若存在属于 `a` 的某个 `y` 使 `x` 属于 `y`，则 `x` 实现这个并。构造 `mkUnion` 只带一条假设：某个序数层 `σ` 装下 `a` 的底层集合。这里没有第二个实参需要安置，因此与配对不同，无须任何上界序数；`a` 本已有的那一层便够了。
<!--ja-->
所属の条件 `Q` は、モデルの真理値の内部での添字つき論理和です。`a` の要素であるある `y` について `x` が `y` の要素であるとき、`x` はこの和集合を実現します。構成 `mkUnion` が仮定するのは一つだけ、ある順序数段階 `σ` が `a` の基底の集合を含むことです。収容すべき第二の引数はないので、対の場合と違って上界順序数は不要であり、`a` がすでにもつ段階そのもので足ります。
<!--/-->

```agda
module UnionOf (a : S) where
  Q : S → hProp (ℓ-suc ℓ)
  Q x = ⋁ S (λ y → (y ∈ˢ a) ⊓ (x ∈ˢ y))

  mkUnion : (σ : V ℓ) → IsOrd σ → ⟨ fst a ∈ Lset σ ⟩ → SetOf Q
  mkUnion σ oσ fa∈ = unionElt , spec
```

<!--en-->
At the stage `Lset σ`, formulas range over its small presentation. Its transitivity, obtained from `Lset-layer σ` and `layer-trans`, says that a member of a member of the stage lies in the stage again. Applying `∈-asFiber` to the given membership of `fst a` produces the representative `mₐ` and path `qₐ : ⟪ Lset σ ⟫↪ mₐ ≡ fst a`; as above, this is direct fiber data rather than elimination of an outer truncation.
<!--zh-->
在层 `Lset σ` 上，公式跑遍该层的小呈现。由 `Lset-layer σ` 与 `layer-trans` 得到的传递性说明：层成员的成员仍属于该层。对给定的 `fst a` 层隶属应用 `∈-asFiber`，得到代表元 `mₐ` 与路径 `qₐ : ⟪ Lset σ ⟫↪ mₐ ≡ fst a`；与上文相同，这是直接取得的纤维数据，并非对外层截断作消去。
<!--ja-->
段階 `Lset σ` では、論理式はその小さな提示の上を動きます。`Lset-layer σ` と `layer-trans` から得られる推移性は、段階の要素の要素が再びその段階に属することを述べます。与えられた `fst a` の段階への所属に `∈-asFiber` を適用すると、代表元 `mₐ` とパス `qₐ : ⟪ Lset σ ⟫↪ mₐ ≡ fst a` が得られます。上と同様、これは外側の切り詰めを消去した結果ではなく、直接得られるファイバーのデータです。
<!--/-->

```agda
    where
    module DefA = DefOf (Lset σ)
    Atrans = layer-trans (Lset-layer σ)
    mₐ = ∈-asFiber {a = fst a} {b = Lset σ} fa∈ .fst
    qₐ : ⟪ Lset σ ⟫↪ mₐ ≡ fst a
```

<!--en-->
The formula has one free-variable slot and is a bounded existential: the variable ranges over the members of the constant `mₐ`, that is, over the members of `a` as presented inside the stage, and the matrix says that the bound variable has the outer variable as a member. Since the bound variable occupies the first slot inside the quantifier body, the outer variable sits in the successor slot. The claimed extension is the ambient union `⋃ (fst a)`, and the equation `defSet≡` is one extensionality, split into two inclusions.
<!--zh-->
公式有一个自由变元槽，是一个有界存在：变元跑遍常元 `mₐ` 的成员，也就是在层内呈现的 `a` 的成员；母式说，约束变元以外部变元为成员。由于约束变元在量词母式中占据第一个槽，外部变元落在后继槽上。被断言的外延是周遭并 `⋃ (fst a)`，等式 `defSet≡` 是一次外延性，分为两个包含。
<!--ja-->
論理式は自由変数のスロットを一つもつ有界存在です。変数は定数 `mₐ` の要素、すなわち段階の内部で提示された `a` の要素の上を渡り、母式は束縛変数が外側の変数を要素にもつと述べます。束縛変数が量化子の本体の中で第一のスロットを占めるため、外側の変数は後者のスロットに置かれます。外延として主張されるのは周囲の和集合 `⋃ (fst a)` であり、等式 `defSet≡` は一回の外延性で、二つの包含に分かれます。
<!--/-->

```agda
    qₐ = ∈-asFiber {a = fst a} {b = Lset σ} fa∈ .snd

    φ : Formula ⟪ Lset σ ⟫ 1
    φ = ∃̇∈ (con mₐ) (var (suc zero) ∈̇ var zero)

    defSet≡ : DefA.defSet φ ≡ ⋃ (fst a)
    defSet≡ = extensionality (DefA.defSet φ) (⋃ (fst a)) (sub₁ , sub₂)
```

<!--en-->
The first inclusion says: everything satisfying the formula lies in the ambient union. A member `y` of the definable subset arrives, by the reading lemma for `defSet`, as a truncated pair of an index `m` and a satisfaction proof, together with a path `q` identifying `y` with the embedded element `⟪ Lset σ ⟫↪ m`. The satisfaction hypothesis names members by their indices, so it can only be consumed for the embedded element; transporting along `q` moves the goal from `y` to that element, and the elimination into the proposition `y ∈ₛ ⋃ (fst a)` is what keeps the whole step legitimate.
<!--zh-->
第一个包含说：凡满足公式者，都在周遭并中。可定义子集的成员 `y`，经 `defSet` 的读法引理，呈现为索引 `m` 与满足证明组成的截断对，连同把 `y` 与嵌入元素 `⟪ Lset σ ⟫↪ m` 等同的路径 `q`。满足假设是按索引来名指成员的，所以它只能用于嵌入元素；沿 `q` 的搬移把目标从 `y` 移到那个元素，而向命题 `y ∈ₛ ⋃ (fst a)` 的消去保证整步合法。
<!--ja-->
最初の包含は、論理式を充足するものはすべて周囲の和集合にある、と言います。定義可能部分集合の元 `y` は、`defSet` の読み取り補題によって、添字 `m` と充足の証明からなる切り詰められた対として、`y` を埋め込まれた要素 `⟪ Lset σ ⟫↪ m` と同一視するパス `q` とともに届きます。充足の仮定は要素を添字で名指すので、それを消費できるのは埋め込まれた要素に対してだけです。`q` に沿った輸送が目標を `y` からその要素へ移し、命題 `y ∈ₛ ⋃ (fst a)` への消去がこの一歩全体を正当に保ちます。
<!--/-->

```agda
      where
      sub₁ : ⟨ DefA.defSet φ ⊆ ⋃ (fst a) ⟩
      sub₁ y y∈ₛ = PT.rec (snd (y ∈ₛ ⋃ (fst a)))
        (λ { ((m , h) , q) →
          subst (λ w → ⟨ w ∈ₛ ⋃ (fst a) ⟩) q
```

<!--en-->
The satisfaction proof for the bounded existential yields, merely, a witness `v` from the range together with the two matrix memberships: `fst v` is a member of the embedded `mₐ`, and the embedded `m` is a member of `fst v`. These are exactly the two memberships the hierarchy's union classification requires in its introduction direction: to place `⟪ Lset σ ⟫↪ m` inside `⋃ (fst a)` it suffices to exhibit some member of `fst a` having it as a member.
<!--zh-->
有界存在的满足证明仅仅给出一个来自范围的见证 `v`，连同母式的两条隶属：`fst v` 属于嵌入的 `mₐ`，而嵌入的 `m` 属于 `fst v`。这两条恰好是层级的并刻画在进入方向所需的输入：要把 `⟪ Lset σ ⟫↪ m` 放进 `⋃ (fst a)`，只须出示 `fst a` 的某个成员以它为成员。
<!--ja-->
有界存在の充足の証明は、範囲からの証人 `v` を、母式の二つの所属とともに単に与えます。すなわち `fst v` が埋め込まれた `mₐ` の要素であり、埋め込まれた `m` が `fst v` の要素であることです。この二つこそ、階層の和集合の分類が導入の向きで消費する入力です。`⟪ Lset σ ⟫↪ m` を `⋃ (fst a)` の中に置くには、それを要素にもつ `fst a` の要素を一つ示せば足ります。
<!--/-->

```agda
            (PT.rec (snd (⟪ Lset σ ⟫↪ m ∈ₛ ⋃ (fst a)))
              (λ { (v , (fstv∈mₐ , m∈fstv)) →
                union-ax (fst a) (⟪ Lset σ ⟫↪ m) .snd
                  ∣ fst v
                  , ( ∈∈ₛ {a = fst v} {b = fst a} .fst
```

<!--en-->
The two matrix memberships, however, speak the restricted presentation's language and must become ambient ones. `∈∈ₛ` performs the conversion, and the path `qₐ` already in hand rewrites the range from the embedded `mₐ` to `fst a`, so the witness `fst v` is presented as a member of `fst a`; the second conjunct is used as it stands, since it is already a membership of the embedded `m` in `fst v`. With both memberships in ambient form, the union classification applies and the first inclusion closes.
<!--zh-->
但母式的两条隶属说的是限制呈现的语言，必须变成周遭隶属。`∈∈ₛ` 执行转换，而已有的路径 `qₐ` 把范围从嵌入的 `mₐ` 改写为 `fst a`，于是见证 `fst v` 被呈现为 `fst a` 的成员；第二个合取肢按原样使用，因为它本来就是嵌入的 `m` 对 `fst v` 的隶属。两条隶属都成为周遭形式后，并刻画随即适用，第一个包含合拢。
<!--ja-->
しかし母式の二つの所属は制限された提示の言葉で語っており、周囲の所属へ変えねばなりません。変換は `∈∈ₛ` が行い、すでに手もとのパス `qₐ` が範囲を埋め込まれた `mₐ` から `fst a` へ書き換えるので、証人 `fst v` は `fst a` の要素として提示されます。第二の項はそのまま使えます。それは埋め込まれた `m` の `fst v` への所属としてすでに成っているからです。両方の所属が周囲の形になれば和集合の分類が適用され、最初の包含が閉じます。
<!--/-->

```agda
                        (subst (λ w → ⟨ fst v ∈ w ⟩) qₐ fstv∈mₐ)
                    , ∈∈ₛ {a = ⟪ Lset σ ⟫↪ m} {b = fst v} .fst m∈fstv ) ∣₁ })
              (subst ⟨_⟩ (DefA.defSet-mem φ m) ∣ (m , h) , refl ∣₁)) })
        (∈∈ₛ {a = y} {b = DefA.defSet φ} .snd y∈ₛ)
      sub₂ : ⟨ ⋃ (fst a) ⊆ DefA.defSet φ ⟩
```

<!--en-->
The reverse inclusion reads the same classification in its other direction: membership of `y` in the ambient union is, merely, a member `v` of `fst a` with `y` a member of `v`. The helper `member` must then exhibit `y` inside the definable subset for this particular `v`. This is the half where the stage hypothesis does the work, because nothing so far guarantees that the intermediate `v` is visible in the stage at all.
<!--zh-->
反向包含把同一条刻画按另一方向读取：`y` 在周遭并中的隶属，仅仅是 `fst a` 的某个成员 `v` 以 `y` 为成员。辅助引理 `member` 随后必须对这个特定的 `v` 把 `y` 展示在可定义子集中。这一半正是层假设出力的地方，因为到此为止，没有任何东西保证那个中间的 `v` 在层中可见。
<!--ja-->
逆の包含は、同じ分類のもう一方の向きを読みます。周囲の和集合への `y` の所属とは、単に、`fst a` のある要素 `v` が `y` を要素にもつことです。補助補題 `member` は、この特定の `v` に対して `y` を定義可能部分集合の中に示さねばなりません。ここで段階の仮定が働きます。これまでのところ、途中の `v` が段階で見えることを保証するものは何もないからです。
<!--/-->

```agda
      sub₂ y y∈ₛ = PT.rec (snd (y ∈ₛ DefA.defSet φ))
        (λ { (v , (v∈ₛfa , y∈ₛv)) → member v v∈ₛfa y∈ₛv })
        (union-ax (fst a) y .fst y∈ₛ)
        where
        member : (v : V ℓ) → ⟨ v ∈ₛ fst a ⟩ → ⟨ y ∈ₛ v ⟩
```

<!--en-->
The helper first converts `y` into a representative `m'` of the stage with its identifying path `q'`, and uses the membership reading of `defSet` backward: satisfaction of φ at the constant naming `m'` becomes membership of the embedded `m'`, and the transport along `q'` moves that membership to `y`. All that remains is the satisfaction proof `sat`, which is assembled from the two memberships `v ∈ₛ fst a` and `y ∈ₛ v`: transitivity of the stage, applied through `Atrans`, certifies first that `v` lies in `Lset σ` and then that `y` does as well, and the two conjuncts are transported to the embedded presentation along the paths `sym qₐ` and `sym q'`.
<!--zh-->
辅助引理先把 `y` 转成层的一个代表元 `m'`，连同其等同路径 `q'`，并把 `defSet` 的隶属读法反着用：在名指 `m'` 的常元处的 φ 满足变成嵌入 `m'` 的隶属，沿 `q'` 的搬移再把这条隶属搬到 `y` 上。剩下的只是满足证明 `sat`，它由两条隶属 `v ∈ₛ fst a` 与 `y ∈ₛ v` 组装：经由 `Atrans` 施用层传递性，先证 `v` 落在 `Lset σ` 中，再证 `y` 也如此，两个合取肢则沿路径 `sym qₐ` 与 `sym q'` 被搬到嵌入呈现上。
<!--ja-->
補助補題はまず `y` を段階の代表元 `m'` と、その同一視のパス `q'` に変換し、`defSet` の所属の読みを逆向きに用います。`m'` を名指す定数のところでの φ の充足は埋め込まれた `m'` の所属となり、`q'` に沿った輸送がその所属を `y` へ移します。残るは充足の証明 `sat` で、これは二つの所属 `v ∈ₛ fst a` と `y ∈ₛ v` から組み立てられます。`Atrans` を通して段階の推移性を適用すれば、まず `v` が `Lset σ` にあり、ついで `y` もそうであることが証明され、二つの項はパス `sym qₐ` と `sym q'` に沿って埋め込まれた提示へ輸送されます。
<!--/-->

```agda
               → ⟨ y ∈ₛ DefA.defSet φ ⟩
        member v v∈ₛfa y∈ₛv =
          subst (λ w → ⟨ w ∈ₛ DefA.defSet φ ⟩) q'
            (∈∈ₛ {a = ⟪ Lset σ ⟫↪ m'} {b = DefA.defSet φ} .fst
              (subst ⟨_⟩ (sym (DefA.defSet-mem φ m')) sat))
```

<!--en-->
This block is where the stage hypothesis earns its keep, and it is the one step pairing did not need. The two ambient memberships are first read back out of their structural form by `∈∈ₛ`: `v` is a member of the underlying set of `a`, and `y` is a member of `v`. Transitivity of the stage is then applied twice. Since `fst a` lies in `Lset σ` and the stage is transitive, its member `v` lies in `Lset σ` too; applying the same reasoning to the membership of `y` in `v` certifies `y` itself as a member of the stage. So a member of a member of `a` is pulled into the stage, which is precisely what lets the formula's quantifier see it.
<!--zh-->
这一块正是层假设出力之处，也是配对所不需要的一步。先用 `∈∈ₛ` 把两条周遭隶属从结构形式读出：`v` 是 `a` 底层集合的成员，`y` 是 `v` 的成员。然后对层的传递性施用两次：既然 `fst a` 落在 `Lset σ` 中而层传递，其成员 `v` 也落在 `Lset σ` 中；对 `y` 属于 `v` 这条隶属再施同一推理，便证得 `y` 自身是层的成员。于是 `a` 的成员的成员被拉进层，这恰好让公式的量词能够看到它。
<!--ja-->
ここが段階の仮定が働く場所であり、対の構成には要らなかった一手です。まず `∈∈ₛ` によって二つの周囲の所属を構造的な形から読み出します。`v` は `a` の基底の集合の要素、`y` は `v` の要素です。次に段階の推移性を二度適用します。`fst a` が `Lset σ` にあり段階が推移的である以上、その要素 `v` も `Lset σ` にあり、`v` への `y` の所属に同じ推論を適用すれば、`y` 自身も段階の要素であると証明されます。こうして `a` の要素の要素が段階へ引き込まれ、論理式の量化子がそれを見えるようにするのはまさにこのためです。
<!--/-->

```agda
          where
          v∈fa = ∈∈ₛ {a = v} {b = fst a} .snd v∈ₛfa
          y∈v = ∈∈ₛ {a = y} {b = v} .snd y∈ₛv
          v∈A = Atrans {x = fst a} {y = v} v∈fa fa∈
          y∈A = Atrans {x = v} {y = y} y∈v v∈A
```

<!--en-->
With `y` certified to lie in the stage, the fiber conversion `∈-asFiber` supplies the representative `m'` and its identifying path `q'` from the embedded element back to `y`. The satisfaction proof for φ at that representative is then assembled inside the truncation: the witness is the pair of `v` together with its own membership `v∈A` in the stage, and the two matrix conjuncts are transported to the embedded presentation, `v` into the embedded `mₐ` along `sym qₐ` and the embedded `m'` into `v` along `sym q'`. This is exactly the data the bounded existential asks for.
<!--zh-->
`y` 落在层的证书到手后，纤维转换 `∈-asFiber` 给出代表元 `m'` 及其从嵌入元素回到 `y` 的等同路径 `q'`。随后在截断内组装 φ 在该代表元处的满足证明：见证是 `v` 连同它自身在层中的隶属 `v∈A` 组成的对，而两条母式合取肢被搬到嵌入呈现处，`v` 沿 `sym qₐ` 进入嵌入的 `mₐ`，嵌入的 `m'` 沿 `sym q'` 进入 `v`。这恰好就是有界存在所要求的数据。
<!--ja-->
`y` が段階にあるという証明書が手に入れば、ファイバー変換 `∈-asFiber` が代表元 `m'` と、埋め込まれた要素から `y` への同一視のパス `q'` を供給します。次に、この代表元のところでの φ の充足の証明を切り詰めの内部で組み立てます。証人は段階への所属 `v∈A` を伴う `v` の対であり、母式の二つの項は埋め込まれた提示へ輸送されます。`v` は `sym qₐ` に沿って埋め込まれた `mₐ` へ、埋め込まれた `m'` は `sym q'` に沿って `v` へ入ります。これが有界存在が要求するデータにちょうど一致します。
<!--/-->

```agda
          fib = ∈-asFiber {a = y} {b = Lset σ} y∈A
          m' = fib .fst
          q' = fib .snd
          sat : ⟨ (DefA.ι m' ∷ []) DefA.⊨ᵐ φ ⟩
          sat = ∣ (v , v∈A)
```

<!--en-->
The two inclusions assemble into the equation `defSet≡`, and the recognition principle `𝒟ₒ-intro` turns formula and equation into membership of `⋃ (fst a)` in `𝒟ₒ (Lset σ)`. One application of the closure lemma `𝒟ₒ→isL` finishes the construction: since `σ` is an ordinal, a definable subset of `Lset σ` is constructible, so `⋃ (fst a)` enters `L` packaged as a carrier element together with its certificate. This packaging is what the next block classifies.
<!--zh-->
两个包含组装成等式 `defSet≡`，识别原则 `𝒟ₒ-intro` 把公式与等式转换为 `⋃ (fst a)` 在 `𝒟ₒ (Lset σ)` 中的隶属。再对闭包引理 `𝒟ₒ→isL` 施用一次便完成构造：既然 `σ` 是序数，`Lset σ` 的可定义子集就可构造，于是 `⋃ (fst a)` 连同其证书被打包成载体元素进入 `L`。下一块将对该打包给出刻画。
<!--ja-->
二つの包含は等式 `defSet≡` に組み上げられ、認識の原理 `𝒟ₒ-intro` が論理式と等式を `⋃ (fst a)` の `𝒟ₒ (Lset σ)` への所属に変えます。閉包の補題 `𝒟ₒ→isL` を一度適用すれば構成は完成です。`σ` が順序数である以上、`Lset σ` の定義可能部分集合は構成可能であり、`⋃ (fst a)` は証明書とともに台の要素として `L` に入ります。次のブロックはこの包みを分類します。
<!--/-->

```agda
                , ( subst (λ w → ⟨ v ∈ w ⟩) (sym qₐ) v∈fa
                  , subst (λ w → ⟨ w ∈ v ⟩) (sym q') y∈v ) ∣₁

    union∈𝒟ₒ : ⟨ ⋃ (fst a) ∈ 𝒟ₒ (Lset σ) ⟩
    union∈𝒟ₒ = 𝒟ₒ-intro (Lset σ) (⋃ (fst a)) ∣ φ , defSet≡ ∣₁

    unionElt : S
```

<!--en-->
The specification is a path of truth values, and it is composed from two pieces. The hierarchy's own union law `union-spec` classifies membership of `fst z` in the ambient union as an indexed disjunction over all of the hierarchy: some `y` in `fst a` with `fst z` in `y`. What remains is to turn that ambient indexed disjunction into `Q z`, which quantifies over the carrier `S`, that is, over constructible witnesses only. The two quantifier ranges differ, and the bridge of the next block identifies the two truncated disjunctions.
<!--zh-->
规格是一条真值路径，由两块复合而成。层级自己的并律 `union-spec` 把 `fst z` 在周遭并中的隶属分类为跑遍整个层级的带索引析取：存在 `fst a` 中的 `y` 使 `fst z` 属于 `y`。剩下要做的是把这条周遭的带索引析取转成 `Q z`，后者对载体 `S` 量化，也就是只对可构造的见证量化。两个量化范围不同，下一块的桥将把这两条截断的析取等同起来。
<!--ja-->
仕様は真理値のパスであり、二つの部品の合成です。階層そのものの和集合の法則 `union-spec` は、周囲の和集合への `fst z` の所属を、階層全体を渡る添字つき論理和として分類します。すなわち `fst a` のある `y` が `fst z` を要素にもつ、というものです。残る仕事は、この周囲の添字つき論理和を `Q z` に変えることです。`Q z` は台 `S` の上、つまり構成可能な証人だけの上で量化します。二つの量化の範囲は異なっており、次のブロックの橋渡しがこの二つの切り詰められた論理和を同一視します。
<!--/-->

```agda
    unionElt = ⋃ (fst a) , 𝒟ₒ→isL σ oσ (⋃ (fst a)) union∈𝒟ₒ

    spec : (z : S) → (z ∈ˢ unionElt) ≡ Q z
    spec z = union-spec (fst a) (fst z) ∙ bridge
      where
      bridge : ⋁ (V ℓ) (λ y → (y ∈ fst a) ⊓ (fst z ∈ y)) ≡ Q z
```

<!--en-->
The bridge is a pair of maps between the two truncated disjunctions, joined into a path by `⇔toPath`. Forward: an ambient witness `y` with its two memberships gains a constructibility certificate, precisely because `y` is a member of `fst a`, whose own certificate `a .snd` is in hand; transitivity of the class, here `isL-trans` applied to the membership of `y` and the certificate of `a`, certifies `y` itself, so the witness may be presented as a carrier element while keeping the memberships. Backward: a carrier witness is projected down to its underlying set, discarding the certificate but keeping the memberships. Neither direction inspects how the truth values are built; both act on abstract Ω values. With the bridge in place, `spec` is the composite path, and the union field of the model is thereby supplied.
<!--zh-->
桥是这两条截断析取之间的一对映射，由 `⇔toPath` 接成路径。正向：带两条隶属的周遭见证 `y` 获得一份可构造性证书，依据恰恰是 `y` 属于 `fst a`，而 `a` 自身的证书 `a .snd` 就在手边；类的传递性在此处即 `isL-trans` 施于「`y` 的隶属」与「`a` 的证书」，证得 `y` 自身可构造，于是该见证可以被呈现为载体元素而不丢失隶属。反向：载体见证被投影回其底层集合，丢掉证书但保留隶属。两个方向都不检视真值是如何构造的，都作用于抽象的 Ω 值。桥就位后，`spec` 便是复合路径，模型的并字段由此得证。
<!--ja-->
橋渡しは、二つの切り詰められた論理和の間の一対の写像であり、`⇔toPath` によってパスに結ばれます。前向きには、二つの所属を伴う周囲の証人 `y` が構成可能性の証明書を得ます。根拠はまさに `y` が `fst a` の要素であることで、`a` 自身の証明書 `a .snd` が手もとにあります。クラスの推移性、ここでは「`y` の所属」と「`a` の証明書」に適用される `isL-trans` が `y` 自身を証明するので、証人は所属を保ったまま台の要素として提示できます。後向きには、台の証人はその基底の集合へ射影され、証明書は捨てられますが所属は保たれます。どちらの向きも真理値の作られ方を覗かず、抽象的な Ω の値に作用します。橋が整えば `spec` は合成パスとなり、モデルの和集合のフィールドがここに供給されます。
<!--/-->

```agda
      bridge = ⇔toPath
        (PT.map (λ { (y , py) →
          (y , isL-trans {x = fst a} {y = y} (py .fst) (a .snd)) , py }))
        (PT.map (λ { (y , py) → fst y , py }))

  build : ∥ SetOf Q ∥₁
```

<!--en-->
The assembly mirrors the pairing field. The argument's own certificate `a .snd` is truncated, and `build` eliminates it with `PT.rec` into the truncated existence of a realizing set: at the stage the certificate names, `mkUnion` runs and produces a witness. The field itself is then one application of the uniqueness principle, `mere→uniqueL`, which turns a merely existing witness into contractibility data, the form every existence field of the model record takes.
<!--zh-->
组装方式照应配对字段。实参自身的证书 `a .snd` 是截断的，`build` 用 `PT.rec` 把它消去，得到实现集合的截断存在：在证书所名指的层处运行 `mkUnion`，产出见证。字段本身于是是一次唯一性原理的应用，`mere→uniqueL` 把仅仅存在的见证变成收缩性数据，这正是模型 record 每个存在字段所采取的形式。
<!--ja-->
組み立ては対のフィールドを写したものです。実引数自身の証明書 `a .snd` は切り詰められており、`build` はそれを `PT.rec` で除去して、実現する集合の単なる存在へします。証明書の名指す段階で `mkUnion` が走り、証人が生まれます。フィールドそのものは、その後の一意性原理の一度の適用、`mere→uniqueL` です。単に存在する証人が収縮性のデータへ変わり、これはモデルの record のすべての存在フィールドが取る形です。
<!--/-->

```agda
  build = PT.rec squash₁ (λ { (σ , (oσ , fa∈)) → ∣ mkUnion σ oσ fa∈ ∣₁ }) (a .snd)

hasUnionL : (a : S) → isContr (SetOf (λ x → ⋁ S (λ y → (y ∈ˢ a) ⊓ (x ∈ˢ y))))
hasUnionL a = mere→uniqueL (UnionOf.Q a) (UnionOf.build a)
```

<!--en-->
## Recap

This chapter supplies five axioms for the constructible universe. Extensionality and regularity are inherited: extensionality uses transitivity to reach ambient members, whereas regularity directly restricts ambient accessibility, and once extensionality is available inside the carrier, each remaining axiom reduces to exhibiting a witness, because a set realizing a fixed membership condition is unique. The empty set, pairing, and union are constructed: each is carved from a single stage by a single formula, with the bounding ordinal supplying that stage where two arguments had to meet. The union specification also shows transitivity at work a second time: an ambient witness for membership in the union gains its constructibility certificate exactly by `isL-trans`, which identifies the restricted witnesses of the model with all witnesses of the ambient union. Alongside the axioms, the chapter records the corresponding placement facts about the tower itself: `pair∈Lset-suc`{.Agda} puts the unordered pair of two members of a stage in the next stage, `sgl∈Lset-suc`{.Agda} the singleton, and `pr∈Lset-suc`{.Agda} the ordered pair two stages up, which is what places anything written with ordered pairs at a stage at all.
<!--zh-->
## 小结

本章为可构造宇宙供给五条公理。外延公理与正则公理是继承来的：外延性用传递性处理周遭成员，而正则性直接限制周遭可及性；而一旦载体内部有了外延性，余下每条公理都化归为出示一个见证，因为实现固定隶属条件的集合是唯一的。空集、配对与并是构造出来的：各由一条公式从单一层中刻出；两个实参须会合时，所需的层由上界序数提供。并的规格还第二次展示了传递性的作用：周遭并中的隶属见证，其可构造性证书恰由 `isL-trans` 给出，正是它把模型的限制见证与周遭并的全部见证等同起来。与公理并行，本章还记录了关于塔自身的相应安置事实：`pair∈Lset-suc`{.Agda} 把一层的两个成员的无序对放进下一层，`sgl∈Lset-suc`{.Agda} 放单点集，`pr∈Lset-suc`{.Agda} 把有序对放到高两层处；这正是以有序对写成的任何东西得以安置在某一层上的原因。
<!--ja-->
## まとめ

本章は構成可能宇宙のために五つの公理を供給します。外延性公理と正則性公理は継承されたものです。外延性は推移性を用いて周囲の要素を扱い、正則性は周囲の可到達性を直接制限します。そして台の内部で外延性が手に入れば、残りの各公理は証人を一つ提示するだけに帰着します。固定された所属条件を実現する集合は一意だからです。空集合、対、和集合は構成されたものです。いずれも一つの論理式で単一の段階から切り出され、二つの実引数が合流しなければならないところでは、必要な段階を上界順序数が供給します。和集合の仕様は、推移性がもう一度働く場面も示しています。周囲の和集合への所属の証人が構成可能性の証明書を得るのはまさに `isL-trans` によってであり、これがモデルの制限された証人と周囲の和集合のすべての証人を同一視するのです。公理と並んで、本章は塔そのものについての配置の事実も記録します。`pair∈Lset-suc`{.Agda} は一つの段階の二つの要素の非順序対を次の段階へ入れ、`sgl∈Lset-suc`{.Agda} は一元集合を、`pr∈Lset-suc`{.Agda} は順序対を二段階上へ置きます。順序対で書かれたものが段階に配置できるのは、まさにこのためです。
<!--/-->
