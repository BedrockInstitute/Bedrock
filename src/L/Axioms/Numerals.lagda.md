<!--en-->
# The numeral chain

This chapter constructs the natural-number chain inside `L` from the model's empty-set, pairing, and union operations, and proves that it projects to the ambient von Neumann numerals.

The mathematical question is this. The von Neumann successor of a set `a` is `a ∪ {a}`, and the model of `L` supplies its own empty set, unordered pair, and union as canonical realizers: each is the centre of a contractible type of sets satisfying its membership specification, read out by the description operator `℩`. Such a centre is an operation with a specification, not a computation: nothing about its definition says that, on its underlying set, it is the set the ambient hierarchy constructs from its own pairing and union. So before the chain can be compared with the hierarchy's chain of numerals, a family of **projection equations** is needed, each saying that one model operation, read through the underlying set, is the corresponding hierarchy operation.

The argument for each projection equation has a fixed shape. The centre of a contractible type is compared with an explicitly built realizer: for pairing, the bounded pair construction applied at a merely existing common stage for the two underlying sets, supplied by `isL-directed`. Contractibility then gives a path from the centre to that realizer, and congruence of the underlying-set projection turns it into an equality of sets. Each elimination of truncated data is legitimate only because its target, an equation between hierarchy sets, is a proposition, which holds because the hierarchy's carrier is an h-set. With the projection equations in hand, the internal chain and the hierarchy's chain coincide step by step, and the two pinning equations the model record demands of a numeral chain follow by transporting the hierarchy's own facts along them.

The whole chapter is constructive: no excluded middle, no resizing, and no choice beyond what the contractibility of the realizer types already provides. What it does not do is collect the numerals into a set; that collection is the content of the infinity axiom itself.
<!--zh-->
# 数码链

本章从模型自身的空集、配对与并运算出发，在 `L` 内构造自然数链，并证明它投影到周遭集合层级中的冯·诺伊曼数码。

数学问题如下。集合 `a` 的冯·诺伊曼后继是 `a ∪ {a}`，而 `L` 的模型把自身的空集、无序对与并供给为典范实现者：每一个都是满足其成员规格的集合之可缩类型的中心，由摹状词算子 `℩` 读出。这样的中心是一个带规格的运算，而不是一条计算规则：其定义本身并未说明，它的底层集合就是周遭集合层级用自身配对与并造出的那个集合。因此，在把这条链与层级的数码链比较之前，需要一族**投影等式**，每一条说：模型的某个运算沿底层集合读出来，就是层级中对应的运算。

每条投影等式的论证有固定的形状。可缩类型的中心与一个显式构造的实现者比较：对配对而言，是把有界配对构造施于两个底层集的一个仅仅存在的公共层，该层由 `isL-directed` 供给。可缩性随后给出从中心到该实现者的路径，而把底层集合投影这个函数作用于该路径，便得到底层集合之间的等式。每一次对截断数据的消去之所以合法，只因目标是层级集合之间的等式，是命题；这又因层级的载体是 h-集合。有了投影等式，内部链与层级链逐步重合，而模型 record 向数码链要求的两条成员方程，也就沿着它们由层级自己的事实推得。

全章都是构造性的：不用排中律，不用 resize，也不需要实现者类型的可缩性之外的选择。本章不做的是把诸数码收集成一个集合；那一步收集正是无穷公理本身的内容。
<!--ja-->
# 数項列

本章ではモデル自身の空集合、対、和集合の演算から `L` 内部の自然数列を構成し、それが周囲のフォン・ノイマン数項へ射影されることを証明する。

数学的な問いはこうです。集合 `a` のフォン・ノイマン後者は `a ∪ {a}` ですが、`L` のモデルは自前の空集合、非順序対、和集合を標準的な実現者として供給します。それぞれ、所属の仕様を満たす集合の可縮な型の中心であり、確定記述の演算子 `℩` によって読み出されます。そのような中心は仕様をもつ演算であって計算規則ではありません。その定義自身は、基底の集合が周囲の階層が自前の対と和集合から作る集合と同じであるとは言っていません。したがって、この列を階層の数項列と比較する前に、**射影方程式**の族が必要です。各方程式は、モデルの演算が基底の集合を通して読めば階層の対応する演算である、と述べます。

各射影方程式の議論には固定した形があります。可縮な型の中心を、明示的に作った実現者と比較します。対の場合、その実現者は、二つの基底の集合の単に存在する共通段階 (`isL-directed` が供給する) に有界な対の構成を適用したものです。可縮性は中心からその実現者へのパスを与え、基底集合への射影関数をそのパスに適用すると、集合の間の等式が得られます。切り詰められたデータの消去が正当なのは、目標が階層の集合の間の等式、すなわち命題だからであり、これは階層の台が h-集合であることに依ります。射影方程式が手に入れば、内部の列と階層の列は一歩ずつ一致し、モデルの record が数項列に要求する二つの指定方程式も、階層自身の事実をそれらに沿って輸送して従います。

章全体が構成的です。排中律もサイズ変更も、実現者の型の可縮性を超える選択も用いません。本章が行わないのは、数項を一つの集合へ収集することです。その収集こそ無限公理自身の内容です。
<!--/-->

<!--en-->
The key notion is unique realization. For pairing, the specification is `λ x → (x ≈ˢ a) ⊔ (x ≈ˢ b)`, and `hasPairL a b` certifies that the type `SetOf` of constructible sets realizing it is contractible: there is a canonical realizer, the centre, together with a path from the centre to every other realizer. Union is specified and certified analogously by `hasUnionL`. A contractibility proof is explicit data, not a bare existence statement: it includes both the centre and the contraction, and it is the centre that the operations below select. This is the only form of choice the chapter uses, and it is supplied by the contractibility itself.
<!--zh-->
关键概念是唯一实现。配对的规格是 `λ x → (x ≈ˢ a) ⊔ (x ≈ˢ b)`，而 `hasPairL a b` 证明实现它的可构造集的类型 `SetOf` 是可缩的：有一个典范实现者，即中心，并有从中心到每个其他实现者的路径。并由 `hasUnionL` 类似地规格化与证明。可缩性证明是显式数据，不是单纯的存在陈述：它同时包含中心与收缩，而下面要选的正是这个中心。这是本章用到的唯一形式的选择，且它由可缩性本身供给。
<!--ja-->
鍵となる概念は一意な実現です。対の仕様は `λ x → (x ≈ˢ a) ⊔ (x ≈ˢ b)` であり、`hasPairL a b` は、それを実現する構成可能集合の型 `SetOf` が可縮であることを証明します。すなわち、標準的な実現者である中心と、中心から他のすべての実現者へのパスがあるのです。和集合も同様に `hasUnionL` によって仕様が与えられ証明されます。可縮性の証明は明示的なデータであって、単なる存在主張ではありません。中心と収縮の両方を含み、以下で選ばれるのはこの中心です。これが本章で用いる唯一の形の選択であり、それは可縮性そのものによって供給されます。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
module L.Axioms.Numerals {ℓ : Level} where

open import FOL.ZFStructure using ( module hPropStructure )
```

<!--en-->
Two sides meet in the projection equations. On the model side stand `hasPairL` and `hasUnionL` with their realizing constructions `PairOf` and `UnionOf`, and the internal empty set `∅ʟ`. On the ambient side stand the hierarchy's unordered pair `⁅ _, _ ⁆` and union `⋃_`, its successor `sucV`, and its numerals `#_`. The input that binds the two sides is `isL-directed`, which supplies, merely, a common ordinal stage containing the underlying sets of two constructible sets; the bounded pair construction needs exactly such a stage to build its realizer. The two internal operations must first be defined before they can be compared.
<!--zh-->
投影等式让两侧相遇。模型一侧是 `hasPairL` 与 `hasUnionL` 及其实现构造 `PairOf` 与 `UnionOf`，以及内部空集 `∅ʟ`。周遭集合一侧是层级的无序对 `⁅ _, _ ⁆` 与并 `⋃_`、后继 `sucV`、数码 `#_`。把两侧绑在一起的输入是 `isL-directed`：它仅仅存在地给出一个容纳两个可构造集底层集合的公共序数层，而有界配对构造恰需这样一层才能造出实现者。这两个内部运算必须先被定义，然后才能比较。
<!--ja-->
射影方程式は両側を出会わせます。モデルの側には、`hasPairL` と `hasUnionL` とその実現の構成 `PairOf` と `UnionOf`、そして内部の空集合 `∅ʟ` があります。周囲の側には、階層の非順序対 `⁅ _, _ ⁆` と和集合 `⋃_`、後者 `sucV`、数項 `#_` があります。両側を結ぶ入力は `isL-directed` です。これは、二つの構成可能集合の基底の集合を含む共通の順序数段階を、単に存在するものとして供給します。有界な対の構成が実現者を作るには、まさにそのような段階が必要です。二つの内部の演算は、まず定義されて初めて比較できます。
<!--/-->

```agda
import FOL.ZFModel
open import V.Model {ℓ} using ( pair-singleton; module NumPin )
open import L.Constructible {ℓ} using ( 𝒮ʟ )
open import L.Axioms.Basic {ℓ}
  using ( hasPairL; hasUnionL; module PairOf; module UnionOf; isL-directed; ∅ʟ )
```

<!--en-->
A projection equation is an equality between sets of the ambient hierarchy, for example `fst (pairʟ a b) ≡ ⁅ fst a , fst b ⁆`. This particular equality type is a proposition because the hierarchy's carrier is an h-set, which is what `setIsSet` certifies. That propositionhood is what permits eliminating the truncated stage data into it; no propositionhood is claimed about arbitrary equality types.
<!--zh-->
投影等式是周遭集合层级集合之间的等式，例如 `fst (pairʟ a b) ≡ ⁅ fst a , fst b ⁆`。这个特定的等值类型之所以是命题，是因为层级的载体是 h-集合，`setIsSet` 证实的正是这一点。正是这个命题性使得把截断的层数据消去进去成为可能；这里并没有对任意等值类型主张命题性。
<!--ja-->
射影方程式は、周囲の階層の集合の間の等式です。たとえば `fst (pairʟ a b) ≡ ⁅ fst a , fst b ⁆`。この特定の等式の型が命題なのは、階層の台が h-集合だからであり、`setIsSet` が保証するのはまさにそれです。この命題性ゆえに、切り詰められた段階のデータをそこへ消去できます。任意の等式の型について命題性を主張しているのではありません。
<!--/-->

```agda

import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.HITs.CumulativeHierarchy.Base using ( setIsSet )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ⁅_,_⁆; ⋃_; module InfinitySet )
```

<!--en-->
Two conventions make the code readable. The structure `𝒮ʟ` is the constructible universe presented as a model of set theory, and opening its model package exposes `SetOf`, the type of a carrier element together with its realizing specification, and `℩`, the operator returning the first component of the centre of a contractible `SetOf` type. Throughout, `fst` on an element of the carrier `S` extracts the underlying set of the ambient hierarchy, and the projection equations compare exactly those underlying sets.
<!--zh-->
两条约定使代码可读。结构 `𝒮ʟ` 是呈现为集合论模型的可构造宇宙；打开其模型包即暴露 `SetOf`，即载体元素连同其实现规格的类型，以及 `℩`，即返回可缩 `SetOf` 类型中心第一分量的算子。全文中，对载体 `S` 元素取 `fst` 得到周遭集合层级的底层集合，投影等式比较的恰是这些底层集合。
<!--ja-->
コードを読みやすくする約束が二つあります。構造 `𝒮ʟ` は集合論のモデルとして提示された構成可能宇宙であり、そのモデルのパッケージを開くと、`SetOf`、すなわち台の要素とその実現の仕様の対の型、そして `℩`、すなわち可縮な `SetOf` の型の中心の第一成分を返す演算子が使えます。全体を通して、台 `S` の要素への `fst` は周囲の階層の基底の集合を取り出します。射影方程式が比較するのはまさにこの基底の集合です。
<!--/-->

```agda
open InfinitySet using ( sucV; #_ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ

module ModelL = FOL.ZFModel 𝒮ʟ
open ModelL using ( SetOf; ℩ )
```

<!--en-->
## The model's own operations

The description operator turns the contractibility of the realizer types into operations: `pairʟ` and `unionʟ` select the centres of `hasPairL` and `hasUnionL`, and the successor composes them.

One distinction governs what follows. A centre selected from a contractible type is an operation with a specification, not a computation rule. The contractibility proof does not make `pairʟ a b` reduce, on its underlying set, to the hierarchy's pair `⁅ fst a , fst b ⁆`; what it does provide is a path from the centre to every realizer, and the projection equations of the next section are obtained by comparing the centre with an explicitly built realizer along that path. All three operations are declared `opaque`, so every later use reads them through their specifications and through the projection equations rather than through their construction.
<!--zh-->
## 模型自己的运算

摹状词算子把实现者类型的可缩性变成运算：`pairʟ` 与 `unionʟ` 选出 `hasPairL` 与 `hasUnionL` 的中心，后继则把它们复合起来。

有一条区分主宰下文。从可缩类型选出的中心是带规格的运算，而不是计算规则。可缩性证明并未使 `pairʟ a b` 的底层集合化归为层级的对 `⁅ fst a , fst b ⁆`；它提供的是从中心到每个实现者的路径，而下一节的投影等式正是沿这条路径把中心与显式构造的实现者比较得到的。三个运算都声明为 `opaque`，此后每一处使用都经它们的规格与投影等式读它们，而非经它们的构造。
<!--ja-->
## モデル自身の演算

確定記述の演算子は、実現者の型の可縮性を演算に変えます。`pairʟ` と `unionʟ` は `hasPairL` と `hasUnionL` の中心を選び、後者はそれらを合成します。

以下を支配する区別が一つあります。可縮な型から選んだ中心は、仕様をもつ演算であって計算規則ではありません。可縮性の証明は、`pairʟ a b` の基底の集合を階層の対 `⁅ fst a , fst b ⁆` へ簡約するものではありません。実際に与えるのは、中心からすべての実現者へのパスであり、次節の射影方程式は、そのパスに沿って中心を明示的に作った実現者と比較することで得られます。三つの演算はすべて `opaque` と宣言され、以後の使用はその構成ではなく、仕様と射影方程式を通して読まれます。
<!--/-->

<!--en-->
The operator `℩` takes a contractibility proof and returns the centre's first component, an element of the carrier `S`. Applying it to `hasPairL a b` and `hasUnionL a` gives two functions on constructible sets. Their inputs are carrier elements, that is, sets packaged with constructibility certificates, so each operation needs no further argument beyond what its inputs already carry.
<!--zh-->
算子 `℩` 接受一份可缩性证明，返回中心的第一个分量，即载体 `S` 的一个元素。把它用于 `hasPairL a b` 与 `hasUnionL a`，便得到可构造集上的两个函数。它们的输入是载体元素，即连同可构造性证书打包的集合，因此每个运算除输入已带的内容外无须再取实参。
<!--ja-->
演算子 `℩` は可縮性の証明を受け取り、その中心の第一成分、すなわち台 `S` の要素を返します。これを `hasPairL a b` と `hasUnionL a` に適用すれば、構成可能集合の上の二つの関数が得られます。入力は台の要素、つまり構成可能性の証明書とともにまとめられた集合なので、各演算は入力がすでに持つもののほかに引数を必要としません。
<!--/-->

```agda
opaque
  pairʟ : S → S → S
  pairʟ a b = ℩ (hasPairL a b)

  unionʟ : S → S
  unionʟ a = ℩ (hasUnionL a)
```

<!--en-->
The internal successor composes the two: `sucʟ a = unionʟ (pairʟ a (pairʟ a a))`. The inner pair is the unordered pair of `a` with itself; the singleton law, applied to underlying sets later, identifies this inner pair with `{a}`, while the outer pair has entries `a` and that singleton, which is how the expression collapses to `a ∪ {a}`. It is the outer unordered pair and its two entries here, not an ordered pair or one of its components.
<!--zh-->
内部后继把两者复合：`sucʟ a = unionʟ (pairʟ a (pairʟ a a))`。内层的对是 `a` 与自身的无序对；稍后对底层集合施加的单点集律会把这个内层对认同为 `{a}`，而外层对的两个条目是 `a` 与该单点集，这正是该表达式坍缩为 `a ∪ {a}` 的方式。这里是外层的无序对及其两个条目，不是有序对，也不是它的某个分量。
<!--ja-->
内部の後者は両者を合成します。`sucʟ a = unionʟ (pairʟ a (pairʟ a a))`。内側の対は `a` とそれ自身の非順序対です。後で基底の集合に適用される一元集合の法則がこの内側の対を `{a}` と同一視し、外側の対の二つの項は `a` とその一元集合になります。したがって、式が `a ∪ {a}` へ崩れるのはそのためです。ここで扱うのは外側の非順序対とその二つの項であって、順序対やその成分ではありません。
<!--/-->

```agda

  sucʟ : S → S
  sucʟ a = unionʟ (pairʟ a (pairʟ a a))
```

<!--en-->
## Projection equations

Contractibility identifies the extracted operations with the ambient hierarchy's unordered pair and union, yielding projection equations for the internal successor.

The centre of a contractible type is not, on the face of it, the set the hierarchy would have built: the operations are opaque here, so this chapter compares them with the hierarchy through projection equations rather than by unfolding them. But contractibility says more than existence: every realizer *is* the centre. So the proof builds an explicit realizer from whatever stage data is at hand and applies the contraction to it, obtaining a path from the centre to it. Each such contraction is applied inside an elimination of truncated data whose target is an equality between hierarchy sets; that target is a proposition because the hierarchy's carrier is an h-set, which is what makes the elimination legal.
<!--zh-->
## 投影等式

可缩性把抽取出的运算与周遭集合层级中的无序对及并对应起来，从而给出内部后继的投影等式。

可缩类型的中心，表面上并不是层级会造出的那个集合：这里的运算是 opaque 的，因此本章用投影等式把它们与层级运算比较，而不展开其定义。但可缩性说的比存在更多：**每个**实现者都等于中心。因此证明用手头已有的层数据显式构造一个实现者，对它施加收缩，得到从中心到该实现者的路径。每次收缩都在一次对截断数据的消去内部施加，其目标是层级集合之间的等式；这个目标是命题，因为层级的载体是 h-集合，这正使消去合法。
<!--ja-->
## 射影方程式

可縮性により取り出した演算を周囲の階層の非順序対および和集合と同一視し、内部の後者について射影方程式を得る。

可縮な型の中心は、一見すると階層が作るであろう集合ではありません。ここで演算は opaque なので、本章では定義を展開せず、射影方程式を通して階層の演算と比較するからです。しかし可縮性が語るのは存在にとどまらず、すべての実現者が**まさに**中心である、ということです。そこで証明は、手元にある段階のデータから明示的な実現者を作り、それに収縮を適用して中心からその実現者へのパスを得ます。各収縮は、目標が階層の集合の間の等式であるような切り詰められたデータの消去の内部で適用されます。その目標が命題なのは階層の台が h-集合だからであり、これが消去を正当化します。
<!--/-->

<!--en-->
The statement fixes the target: the underlying set of the extracted pair must equal the hierarchy's unordered pair of the underlying sets. The elimination `PT.rec` opens the merely existing common-stage data `isL-directed` supplies, and it is legal precisely because the goal is the equality `fst (pairʟ a b) ≡ ⁅ fst a , fst b ⁆`, and `setIsSet (fst (pairʟ a b)) ⁅ fst a , fst b ⁆` proves that this equality type is a proposition. Inside, the incoming data `σ , oσ , fa∈ , fb∈` is exactly what `PairOf.mkPair` consumes, so `mkPair` builds a realizer from it. The path the certificate provides goes from the centre to that realizer, not the other way.
<!--zh-->
陈述先固定目标：抽出的对的底层集合必须等于层级对底层集合所作的无序对。消去 `PT.rec` 打开 `isL-directed` 仅仅存在的公共层数据，而这一步合法，恰因目标是等式 `fst (pairʟ a b) ≡ ⁅ fst a , fst b ⁆`，而 `setIsSet (fst (pairʟ a b)) ⁅ fst a , fst b ⁆` 证明这个等式类型是命题。在内部，送入的数据 `σ , oσ , fa∈ , fb∈` 恰是 `PairOf.mkPair` 所消耗的，于是 `mkPair` 由它构造出一个实现者。证书提供的路径从中心指向那个实现者，方向不可颠倒。
<!--ja-->
主張はまず目標を固定します。取り出した対の基底の集合が、階層が基底の集合たちに作る非順序対と等しいこと。消去 `PT.rec` が `isL-directed` の単に存在する共通段階のデータを開きますが、これが正当なのは、目標は等式 `fst (pairʟ a b) ≡ ⁅ fst a , fst b ⁆` であり、`setIsSet (fst (pairʟ a b)) ⁅ fst a , fst b ⁆` がこの等式の型を命題だと証明することだからです。内部では、届くデータ `σ , oσ , fa∈ , fb∈` がちょうど `PairOf.mkPair` が消費するものであり、`mkPair` はそこから実現者を構成します。証明書が供給するパスは中心からその実現者へ向かうものであり、逆向きではありません。
<!--/-->

```agda
  pairʟ-fst : (a b : S) → fst (pairʟ a b) ≡ ⁅ fst a , fst b ⁆
  pairʟ-fst a b = PT.rec (setIsSet (fst (pairʟ a b)) ⁅ fst a , fst b ⁆)
    (λ { (σ , (oσ , (fa∈ , fb∈))) →
         cong (λ (e : SetOf (PairOf.Q a b)) → fst (fst e))
           (hasPairL a b .snd (PairOf.mkPair a b σ oσ fa∈ fb∈)) })
```

<!--en-->
The last step identifies the center with the explicitly built realizer. The contraction `hasPairL a b .snd` sends any realizer to a path starting at the center and ending at that realizer; applied to `mkPair a b σ oσ fa∈ fb∈`, it yields a path in the type `SetOf (PairOf.Q a b)`, which packages a carrier element with its realizing specification. Congruence of the projection `λ e → fst (fst e)`, which reads out the carrier element and then its underlying set, turns that path into an equation between underlying sets, closing the goal. Note that the truncated common-stage data is eliminated only into this set equality, whose propositionhood `setIsSet` supplies. The union case is the same argument one input short: `UnionOf.mkUnion` needs a single stage containing `fst a`, and the certificate `a .snd` is exactly such merely existing stage data, so the elimination consumes it directly.
<!--zh-->
最后一步把中心与显式构造的实现者等同。收缩 `hasPairL a b .snd` 对任意实现者给出一条从中心出发、终于该实现者的路径；把它用于 `mkPair a b σ oσ fa∈ fb∈`，得到类型 `SetOf (PairOf.Q a b)` 中的路径，该类型把载体元素连同其实现规格打包。把投影函数 `λ e → fst (fst e)` 作用于这条路径，先读出载体元素再读出其底层集合，把这条路径变成底层集合之间的等式，目标合拢。注意，截断的公共层数据只被消去到这条集合等式中，其命题性由 `setIsSet` 供给。并的情形是少一个输入的同一论证：`UnionOf.mkUnion` 只需一个容纳 `fst a` 的层，而证书 `a .snd` 正是那样的仅存层数据，消去直接消耗它。
<!--ja-->
最後の一歩は、中心と明示的に構成した実現者を同一視します。収縮 `hasPairL a b .snd` は任意の実現者に対して、中心からその実現者へ向かうパスを与えます。これを `mkPair a b σ oσ fa∈ fb∈` に適用すると、型 `SetOf (PairOf.Q a b)` の中のパスが得られます。この型は台の要素をその実現の仕様とともにまとめたものです。射影関数 `λ e → fst (fst e)` をこのパスに適用することで、台の要素を読み取りつぎにその基底の集合を読み取りる射影が、このパスを基底の集合の間の等式に変え、目標が閉じます。切り詰められた共通段階のデータが消去される先はこの集合の等式だけであり、その命題性は `setIsSet` が供給します。和集合の場合は、入力が一つ少ないだけの同じ議論です。`UnionOf.mkUnion` は `fst a` を含む一つの段階を必要とするだけで、証明書 `a .snd` はまさにそのような、単に存在する段階のデータなので、消去はそれを直接消費します。
<!--/-->

```agda
    (isL-directed (fst a) (fst b) (a .snd) (b .snd))

  unionʟ-fst : (a : S) → fst (unionʟ a) ≡ ⋃ (fst a)
  unionʟ-fst a = PT.rec (setIsSet (fst (unionʟ a)) (⋃ (fst a)))
    (λ { (σ , (oσ , fa∈)) →
         cong (λ (e : SetOf (UnionOf.Q a)) → fst (fst e))
```

<!--en-->
Read the result: `fst (unionʟ a) ≡ ⋃ (fst a)`, the underlying set of the model's union operation is the hierarchy's union of the underlying set. Together with the pairing equation, every set assembled from the model's pairing and union reads, through its underlying set, as the same set assembled from the hierarchy's operations. This is what the projection equations are for: comparing the two successor operations, and with them the two numeral chains, one step at a time.
<!--zh-->
读这个结果：`fst (unionʟ a) ≡ ⋃ (fst a)`，模型并运算的底层集合就是层级对底层集合取的并。与配对等式合在一起，凡由模型的配对与并组装出的集合，沿底层集合读出来，就是由层级运算组装出的同一个集合。投影等式的用途正在于此：一步步比较两个后继运算，进而比较两条数码链。
<!--ja-->
結果を読めば `fst (unionʟ a) ≡ ⋃ (fst a)`、モデルの和集合の演算の基底の集合は、階層が基底の集合に作る和集合です。対の方程式と合わせて、モデルの対と和集合から組み立てた集合は、基底の集合を通して読めば、階層の演算から組み立てた同じ集合になります。射影方程式の用途はまさにここにあります。二つの後者の演算を、ひいては二つの数項列を、一歩ずつ比較することです。
<!--/-->

```agda
           (hasUnionL a .snd (UnionOf.mkUnion a σ oσ fa∈)) })
    (a .snd)
```

<!--en-->
The successor equation is the projection equations composed, plus the hierarchy's own identification of `{a, a}` with `{a}`. Unfold the outer union, then the outer pair, then the inner pair, then collapse the doubled singleton, and what is left is the hierarchy's successor.

Each congruence rewrites one nested position at a time, so the composition runs from the outside in. The direction of each factor matters. The pair equation points from the extracted center to the hierarchy's pair, so congruence over the surrounding union-of-pair shape carries the whole term toward the hierarchy's form, and `pair-singleton` is used at the end in exactly its stated direction.
<!--zh-->
后继等式就是那几条投影等式的复合，再加上层级自己对 `{a, a}` 与 `{a}` 的认同。先展开外层的并，再展开外层的对，再展开内层的对，最后消去重复的单点集，剩下的就是层级的后继。

每一步都把某个函数作用于已有等式，一次改写一个嵌套位置，所以复合从外向内进行。每个因子的方向都重要：配对等式从抽出的中心指向层级的对，于是把周遭「对取并」的函数作用于该等式，就把整个词项朝层级的形式搬运；而 `pair-singleton` 在最后按它陈述的方向使用。
<!--ja-->
後者の方程式は、射影方程式を合成したものであり、そこに階層自身の `{a, a}` と `{a}` の同一視が加わります。外側の和集合を展開し、つぎに外側の対、つぎに内側の対を展開し、最後に重複した一元集合を潰せば、残るのは階層の後者です。

各段階では一つの関数を既存の等式に適用し、入れ子の位置を一つずつ書き換えるだけなので、合成は外から内へ進みます。各因子の向きが重要です。対の方程式は取り出した中心から階層の対へ向かうので、周囲の「対の和集合」という関数をその等式に適用することが項全体を階層の形へ運び、`pair-singleton` は最後に、宣言どおりの向きで使われます。
<!--/-->

<!--en-->
The first three factors rewrite the outer layers. The union projection at `pairʟ a (pairʟ a a)` gives `fst (unionʟ ...) ≡ ⋃ (fst (pairʟ a (pairʟ a a)))`. Applying the function `⋃_` to the outer equation `pairʟ-fst a (pairʟ a a)` rewrites its argument to `⋃ ⁅ fst a , fst (pairʟ a a) ⁆`. Applying `λ w → ⋃ ⁅ fst a , w ⁆` to the inner equation `pairʟ-fst a a` then gives `⋃ ⁅ fst a , ⁅ fst a , fst a ⁆ ⁆`. The inner doubled pair is equal to the singleton by `pair-singleton`; the final factor applies that equality inside the same surrounding function.
<!--zh-->
前三个因子依次改写外层。并的投影等式在 `pairʟ a (pairʟ a a)` 处给出 `fst (unionʟ ...) ≡ ⋃ (fst (pairʟ a (pairʟ a a)))`。把函数 `⋃_` 作用于外层等式 `pairʟ-fst a (pairʟ a a)`，其实参改写为 `⋃ ⁅ fst a , fst (pairʟ a a) ⁆`。再把函数 `λ w → ⋃ ⁅ fst a , w ⁆` 作用于内层等式 `pairʟ-fst a a`，得到 `⋃ ⁅ fst a , ⁅ fst a , fst a ⁆ ⁆`。内层重复对由 `pair-singleton` 等同于单点集；最后一个因子把这条等式置于同一个周遭函数内。
<!--ja-->
最初の三つの因子は外側から順に書き換えます。`pairʟ a (pairʟ a a)` における和集合の射影方程式は `fst (unionʟ ...) ≡ ⋃ (fst (pairʟ a (pairʟ a a)))` を与えます。外側の方程式 `pairʟ-fst a (pairʟ a a)` に関数 `⋃_` を適用すると、引数は `⋃ ⁅ fst a , fst (pairʟ a a) ⁆` へ書き換わります。つぎに内側の方程式 `pairʟ-fst a a` に関数 `λ w → ⋃ ⁅ fst a , w ⁆` を適用すると、`⋃ ⁅ fst a , ⁅ fst a , fst a ⁆ ⁆` が得られます。内側の重複した対は `pair-singleton` によって一元集合と等しく、最後の因子は同じ周囲の関数の中でこの等式を用います。
<!--/-->

```agda
  sucʟ-fst : (a : S) → fst (sucʟ a) ≡ sucV (fst a)
  sucʟ-fst a =
      unionʟ-fst (pairʟ a (pairʟ a a))
    ∙ cong ⋃_ (pairʟ-fst a (pairʟ a a))
    ∙ cong (λ w → ⋃ ⁅ fst a , w ⁆) (pairʟ-fst a a)
```

<!--en-->
The last factor is where the hierarchy's own law enters: `pair-singleton (fst a)` is the path identifying the doubled pair `⁅ fst a , fst a ⁆` with the singleton `⁅ fst a ⁆`. Composed under the same congruence shape, it turns the term into `⋃ ⁅ fst a , ⁅ fst a ⁆ ⁆`, which is exactly `sucV (fst a)`. The chain of factors thus verifies the statement: the internal successor, read through its underlying set, is the hierarchy's successor.
<!--zh-->
最后一个因子是层级自己的定律进入之处：`pair-singleton (fst a)` 是把重复的对 `⁅ fst a , fst a ⁆` 认同为单点集 `⁅ fst a ⁆` 的路径。把同一个函数作用于这条路径，它把词项变为 `⋃ ⁅ fst a , ⁅ fst a ⁆ ⁆`，而后者恰是 `sucV (fst a)`。这串因子因此验证了那个陈述：内部后继沿底层集合读出来就是层级的后继。
<!--ja-->
最後の因子は、階層自身の法則が入る場所です。`pair-singleton (fst a)` は、重複した対 `⁅ fst a , fst a ⁆` を一元集合 `⁅ fst a ⁆` と同一視するパスです。同じ関数をこのパスに適用すれば、項は `⋃ ⁅ fst a , ⁅ fst a ⁆ ⁆` となり、これはまさに `sucV (fst a)` です。したがってこの因子の連なりは主張を検証します。内部の後者は、基底の集合を通して読めば階層の後者なのです。
<!--/-->

```agda
    ∙ cong (λ w → ⋃ ⁅ fst a , w ⁆) (pair-singleton (fst a))
```

<!--en-->
## The chain

Primitive recursion defines `numeralL`{.Agda} from the internal zero and successor, and induction proves `numeralL-fst`{.Agda}, its equality with the ambient numeral.

With the successor equation in hand, the chain is written by ordinary recursion on a natural number, and one induction says it projects onto the hierarchy's numerals. The zero stage is the internal empty set, whose underlying set is the empty set on the nose.

What this section provides is each individual numeral as an element of the carrier, together with its membership behavior. It does not collect all numerals into a set, and it does not prove Infinity; the chain is simply the successor equation iterated, so the induction has one interesting step and the zero case is a computation.
<!--zh-->
## 链

原始递归从内部零与后继定义 `numeralL`{.Agda}，归纳则证明 `numeralL-fst`{.Agda}，即它与周遭数码相等。

有了后继等式，链就可以沿自然数用普通递归写出，而一次归纳即说明它投影到层级的数码上。第零阶段是内部空集，其底层集合严格就是空集。

本节提供的是每个数码作为载体的元素，连同它的成员行为。它不把所有数码收集成一个集合，也不证明无穷公理；链只是后继等式的迭代，因此归纳只有一步有内容，零的情形是一次计算。
<!--ja-->
## 数項列の構成

原始再帰により内部の零と後者から `numeralL`{.Agda} を定義し、帰納法で周囲の数項との等しさ `numeralL-fst`{.Agda} を証明します。

後者の方程式が手に入れば、列は自然数上の通常の再帰で書け、一度の帰納法で階層の数項へ射影されることが示されます。第 0 の段階は内部の空集合であり、その基底の集合は文字どおり空集合です。

この節が供給するのは、各数項を台の要素として、その所属の振る舞いとともに得ることです。すべての数項を一つの集合に収集するのではなく、無限公理を証明するのでもありません。列は後者の方程式の繰り返しにすぎないので、帰納法で内容のあるのは一歩だけで、零の場合は計算です。
<!--/-->

<!--en-->
The definition has two clauses. The zeroth stage is `∅ʟ`, the internal empty set, and each later stage is the internal successor applied to the previous one. Because the recursion is on the natural number index, the chain is an explicit function `ℕ → S`: every stage is an element of the carrier, since `∅ʟ`, `pairʟ` and `unionʟ` all return such elements, and the internal successor preserves this at every iteration. Each stage thus arrives packaged with its constructibility certificate.
<!--zh-->
定义有两条子句。第零阶段是 `∅ʟ`，即内部空集；其后每个阶段是把内部后继用于前一阶段。由于递归在自然数索引上进行，链是一个显式函数 `ℕ → S`：每个阶段都是载体的元素，因为 `∅ʟ`、`pairʟ` 与 `unionʟ` 都返回这样的元素，而内部后继在每次迭代中都保持这一点。于是每个阶段都连同其可构造性证书一起到手。
<!--ja-->
定義は二つの節からなります。第 0 の段階は `∅ʟ`、すなわち内部の空集合であり、その後の各段階は内部の後者を直前のものに適用したものです。再帰が自然数の添字の上で行われるので、列は明示的な関数 `ℕ → S` です。`∅ʟ`、`pairʟ`、`unionʟ` はいずれもそのような要素を返し、内部の後者は繰り返しのたびにこれを保つので、各段階は台の要素になっています。したがって各段階は構成可能性の証明書とともにまとめて手に入ります。
<!--/-->

```agda
  numeralL : ℕ → S
  numeralL zero    = ∅ʟ
  numeralL (suc n) = sucʟ (numeralL n)

  numeralL-fst : (n : ℕ) → fst (numeralL n) ≡ # n
  numeralL-fst zero    = refl
```

<!--en-->
The alignment with the ambient numerals is proved by induction on `n`. At zero, both sides compute to the empty set, so the path is `refl`. At the successor, the equation `sucʟ-fst` applied at `numeralL n` identifies `fst (numeralL (suc n))` with `sucV (fst (numeralL n))`, and congruence of `sucV` over the induction hypothesis `fst (numeralL n) ≡ # n` moves the induction step inside the successor. The composite has exactly the shape of the defining recursion of `# (suc n)`, so the two chains agree at every stage.
<!--zh-->
与周遭数码的对齐按 `n` 归纳证明。在零处，两边都计算为空集，路径是 `refl`。在后继处，把 `sucʟ-fst` 施于 `numeralL n`，把 `fst (numeralL (suc n))` 认同为 `sucV (fst (numeralL n))`；再对归纳假设 `fst (numeralL n) ≡ # n` 把函数 `sucV` 作用于，把归纳步搬进后继内部。复合恰有 `# (suc n)` 的定义递归的形状，于是两条链在每个阶段都一致。
<!--ja-->
周囲の数項との整列は `n` 上の帰納法で証明します。零では両辺とも空集合に計算されるので、パスは `refl` です。後続では、`sucʟ-fst` を `numeralL n` に適用して `fst (numeralL (suc n))` を `sucV (fst (numeralL n))` と同一視し、帰納法の仮定 `fst (numeralL n) ≡ # n` の上の関数 `sucV` を帰納の一歩を後者の内部へ運びます。合成は `# (suc n)` を定義する再帰と同じ形をしているので、二つの列はすべての段階で一致します。
<!--/-->

```agda
  numeralL-fst (suc n) = sucʟ-fst (numeralL n) ∙ cong sucV (numeralL-fst n)
```

<!--en-->
## The two pinning equations

`numeralL-zero`{.Agda} proves that internal zero has no members, while `numeralL-suc`{.Agda} characterizes the next numeral as the preceding members together with its predecessor.

The model record demands these two laws of a numeral chain: zero must be empty, and each successor must have exactly the members of its predecessor together with the predecessor itself, both stated through membership rather than through the derived operations. That phrasing is what keeps the proofs short: each is a fact about the hierarchy's numerals, transported along the projection family `numeralL-fst`. Nothing here unfolds a description operator.

The vehicle is the module `NumPin`, which takes a hierarchy-valued chain `a : ℕ → V ℓ` together with an alignment `q : (n : ℕ) → a n ≡ # n` and returns the two pinning equations for that chain. Our chain supplies the underlying-set family `λ k → fst (numeralL k)` and the alignment `numeralL-fst`.
<!--zh-->
## 两条成员方程

`numeralL-zero`{.Agda} 证明内部零没有成员，而 `numeralL-suc`{.Agda} 刻画下一数码的成员恰为前一数码的成员及前一数码自身。

模型 record 向数码链索取这两条律：零必须为空，且每个后继的成员恰是前者的成员连同前者自身，两条都经隶属陈述，而非经派生运算。正是这个措辞使证明很短：每一条都是关于层级数码的事实，沿投影族 `numeralL-fst` 搬运过来。全程从不展开摹状词算子。

`NumPin` 统一给出这一论证：它接受取值于周遭集合层级的链 `a : ℕ → V ℓ` 连同对齐 `q : (n : ℕ) → a n ≡ # n`，返回该链的两条成员方程。我们的链供给底层集族 `λ k → fst (numeralL k)` 与对齐 `numeralL-fst`。
<!--ja-->
## 二つの指定方程式

`numeralL-zero`{.Agda} は内部の零に要素がないことを示し、`numeralL-suc`{.Agda} は次の数項の要素が直前の数項の要素とその数項自身からなることを特徴づけます。

モデルの record は数項列にこの二つの法則を要求します。零が空であること、そして各後者の要素が前者の要素に前者自身を加えたものにちょうど等しいこと。どちらも派生した演算ではなく所属を通して述べられています。この言い回しゆえに証明は短くなります。どちらも階層の数項についての事実であり、射影の族 `numeralL-fst` に沿って輸送されるからです。ここで確定記述の演算子が展開されることは一切ありません。

運び役はモジュール `NumPin` です。これは周囲の階層に値をとる列 `a : ℕ → V ℓ` と整列 `q : (n : ℕ) → a n ≡ # n` を受け取り、その列に対する二つの指定方程式を返します。こちらの列は基底の集合の族 `λ k → fst (numeralL k)` と整列 `numeralL-fst` を供給します。
<!--/-->

<!--en-->
The zero equation has the shape of a refutation: a member `z` of the chain's zeroth stage yields an inhabitant of the empty host type. The resulting function type is itself a proposition in the hProp setting. `pinZero` transports the assumed membership along the alignment at stage zero, turning membership in `fst (numeralL zero)` into membership in `# zero`, and the hierarchy's own fact that nothing is a member of `∅` then closes the proof. The transport runs one way only: from the chain to the library numeral.
<!--zh-->
零方程式取反驳的形状：链第零阶段的一个成员 `z` 导出空宿主类型的一个元素，所得函数类型在 hProp 设定下自身也是命题。`pinZero` 把假设的隶属沿第零处的对齐传输，把「属于 `fst (numeralL zero)`」变成「属于 `# zero`」，然后层级自己关于 `∅` 无成员的事实合拢证明。传输只走一个方向：从链到库数码。
<!--ja-->
第 0 の方程式は反駁の形をしています。列の第 0 段階の要素 `z` から空のホスト型の要素が得られるので、得られる関数型は hProp の設定ではそれ自身が命題です。`pinZero` は仮定された所属を段階 0 での整列に沿って輸送し、`fst (numeralL zero)` への所属を `# zero` への所属に変え、その後、階層自身の「`∅` には要素がない」という事実が証明を閉じます。輸送は一方向にだけ進みます。列からライブラリの数項へ、です。
<!--/-->

```agda
numeralL-zero : (z : S) → ⟨ z ∈ˢ numeralL zero ⟩ → Empty.⊥
numeralL-zero z = NumPin.pinZero (λ k → fst (numeralL k)) numeralL-fst (fst z)

numeralL-suc : (n : ℕ) (z : S)
             → (⟨ z ∈ˢ numeralL (suc n) ⟩
                  → ⟨ (z ∈ˢ numeralL n) ⊔ (z ≈ˢ numeralL n) ⟩)
```

<!--en-->
The successor equation is a pair of implications, and its second component speaks of the structure equality `≈ˢ`; for this restriction structure, that relation is the underlying path `fst z ≡ fst (numeralL n)`. Forward, a member of `numeralL (suc n)` is transported along the alignment at stage `suc n` into membership in `# (suc n)`, where the hierarchy's own analysis of membership in `sucV` splits it, merely, between a member of `# n` and the case of `# n` itself; each branch is then transported back along the reverse alignment at stage `n`. Backward, a member of `numeralL n` is transported to `# n` and placed into `# (suc n)` by `∈sucV-inl`, and an element equal to `numeralL n` transports its path to `# n` and uses the hierarchy's fact that a set belongs to its own successor. Both directions are `pinSuc`'s output for the chain `λ k → fst (numeralL k)` and the alignment `numeralL-fst`, instantiated at `fst z`.
<!--zh-->
后继方程是一对蕴涵，其第二个分句使用结构关系 `≈ˢ`；对当前限制结构，它的底层正是路径 `fst z ≡ fst (numeralL n)`。正向：`numeralL (suc n)` 的成员沿 `suc n` 处的对齐被传输为 `# (suc n)` 的成员，在那里层级自己对 `sucV` 成员的分析把它，仅仅存在地，分为「`# n` 的成员」与「就是 `# n`」两种情形；每个分支再沿 `n` 处的逆向对齐传回链上。反向：`numeralL n` 的成员被传输为 `# n` 后经 `∈sucV-inl` 放进 `# (suc n)`，而与 `numeralL n` 相等的元素则把路径传到 `# n`，再使用层级自己「集合属于自己的后继」的事实。两个方向就是 `pinSuc` 对链 `λ k → fst (numeralL k)` 与对齐 `numeralL-fst` 的输出，实例化在 `fst z` 上。
<!--ja-->
後者の方程式は一対の含意であり、その第二の成分が語るのは構造の関係 `≈ˢ` です。この制限構造では、その基底はパス `fst z ≡ fst (numeralL n)` です。順方向では、`numeralL (suc n)` の要素が段階 `suc n` での整列に沿って `# (suc n)` への所属へ輸送され、そこで階層自身の `sucV` の所属の分析が、単に存在するものとして、それを `# n` の要素である場合と `# n` そのものである場合に分けます。各枝はさらに段階 `n` での逆向きの整列に沿って列へ輸送し戻されます。逆方向では、`numeralL n` の要素は `# n` へ輸送されたうえで `∈sucV-inl` によって `# (suc n)` へ置かれ、`numeralL n` と等しい要素はパスを `# n` へ運び、階層自身の「集合は自分自身の後続に属する」という事実を使います。どちらの向きも、列 `λ k → fst (numeralL k)` と整列 `numeralL-fst` に対する `pinSuc` の出力を `fst z` に実例化したものです。
<!--/-->

```agda
             × (⟨ (z ∈ˢ numeralL n) ⊔ (z ≈ˢ numeralL n) ⟩
                  → ⟨ z ∈ˢ numeralL (suc n) ⟩)
numeralL-suc n z = NumPin.pinSuc (λ k → fst (numeralL k)) numeralL-fst n (fst z)
```

<!--en-->
## Recap

`numeralL`{.Agda} is an internal copy of the von Neumann numerals inside `L`, with the exact zero and successor membership laws the model record requires.

The chapter's argument has three layers. The internal successor is built from the operations that unique existence hands over as contractibility centres, and the projection equations identify, propositionally, the underlying sets of those operations with the hierarchy's unordered pair, union, and successor. Recursion on a natural number then iterates the internal successor from the internal empty set, and induction proves `numeralL-fst`{.Agda}, the family of paths aligning each stage's underlying set with the ambient numeral `# n`. Finally `numeralL-zero`{.Agda} and `numeralL-suc`{.Agda} follow by applying `NumPin` to that alignment, so the two membership laws hold for the internal chain while all the case analysis happens at the hierarchy's numerals.

What has been established concerns individual numerals: each `numeralL n` exists inside `L` and has the right membership behavior. No statement here collects the stages into a set, and infinity is not proved in this chapter. Beyond the numerals, the projection equations say that anything assembled from the model's pairing and union reads, through its underlying set, as the same thing assembled from the hierarchy's operations.
<!--zh-->
## 小结

`numeralL`{.Agda} 是 `L` 内部的冯·诺伊曼数码副本，满足模型 record 所要求的精确零与后继成员律。

本章的论证有三层。内部后继由唯一存在交出的、作为可缩中心的运算组装而成，投影等式在命题层面把这些运算的底层集合与层级的无序对、并及后继认同起来。然后沿自然数递归，从内部空集出发迭代内部后继，归纳证明 `numeralL-fst`{.Agda}，即把每个阶段的底层集合与周遭数码 `# n` 对齐的路径族。最后，把 `NumPin` 应用于这条对齐便得 `numeralL-zero`{.Agda} 与 `numeralL-suc`{.Agda}，两条成员律对内部链成立，而全部分情形分析都发生在层级的数码上。

这里确立的只是逐个数码的事实：每个 `numeralL n` 存在于 `L` 内并有正确的成员行为。本章没有把各阶段收集成一个集合的陈述，也没有证明无穷。投影等式的用途不止于数码：凡由模型的配对与并组装出的东西，沿底层集合读出来，就是用层级运算组装出的同一个东西。
<!--ja-->
## まとめ

`numeralL`{.Agda} は `L` の内部におけるフォン・ノイマン数項のコピーであり、モデルの record が要求する零と後者の正確な所属法則を満たします。

本章の議論には三つの層があります。内部の後者は、一意存在が可縮中心として手渡す演算から組み立てられ、射影方程式がそれらの演算の基底の集合を、命題の水準で、階層の非順序対・和集合・後者と同一視します。つぎに自然数上の再帰が内部の空集合から内部の後者を繰り返し、帰納法により `numeralL-fst`{.Agda}、すなわち各段階の基底の集合を周囲の数項 `# n` と整列させるパスの族が証明されます。最後に、この整列へ `NumPin` を適用して `numeralL-zero`{.Agda} と `numeralL-suc`{.Agda} が従い、二つの所属法則が内部の列に対して成り立ちます。場合分けの分析はすべて階層の数項の上で行われます。

ここで確立されるのは個々の数項についての事実です。各 `numeralL n` が `L` の内部に存在し、正しい所属の振る舞いをもつこと。本章には段階たちを一つの集合へ収集する主張はなく、無限は証明されません。射影方程式の用途は数項にとどまらず、モデルの対と和集合から組み立てられたものは、基底の集合を通して読めば、階層の演算から組み立てた同じものです。
<!--/-->
