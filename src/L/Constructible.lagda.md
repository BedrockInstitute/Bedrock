<!--en-->
# The constructible hierarchy and universe

The constructible hierarchy starts from the empty set and repeatedly applies definable power set, taking unions at limit points. The resulting stages are transitive, and the tower is monotone along membership of its indices; the sets that appear in some stage form the class `L`{.Agda}, together with the set-theoretic structure obtained by restricting the ambient one to it.

One design choice does most of the work. The tower is indexed not by a separate type of ordinals but by **sets themselves**, through the recursion on membership that regularity licensed: `Lset α = ⋃ { Def (Lset β) ∣ β ∈ α }`. This single equation covers zero, successors, and limits at once, and on von Neumann ordinals it is exactly Gödel's tower; the definition itself accepts arbitrary sets as indices, and the requirement that the index be an ordinal is imposed later, only where the class `L` is defined. Alongside the tower runs an inductive predicate `isLayer`{.Agda}, "being a stage", whose constructors are the tower's closure principles; the two views cooperate throughout.
<!--zh-->
# 可构造层级与可构造宇宙

可构造层级从空集开始，反复施加可定义幂集，并在极限点处取并。所得阶段都是传递集，而塔沿指标之间的隶属关系保持单调；出现在某个阶段中的集合构成类 `L`{.Agda}，连同把环境结构限制到其上所得的集合论结构。

一个设计选择承担了大部分工作。塔的索引不是另立的序数类型，而是**集合自身**，凭借正则性所授权的沿成员关系的递归：`Lset α = ⋃ { Def (Lset β) ∣ β ∈ α }`。这一条方程同时覆盖零、后继与极限，而在冯·诺伊曼序数上它恰是哥德尔的塔；定义本身接受任意集合作为索引，索引须为序数的要求留到定义类 `L` 时才施加。与之并行的是归纳谓词 `isLayer`{.Agda}，「是一个层」，其构造子就是塔的闭包原则；两个视角在全章配合使用。
<!--ja-->
# 構成可能階層と構成可能宇宙

構成可能階層は空集合から始まり、定義可能冪集合を繰り返し施し、極限点では和集合を取ります。できあがる各段階は推移的で、塔は添字の所属に沿って単調です。いくつかの段階に現れる集合の全体がクラス `L`{.Agda} を与え、周囲の構造をそこへ制限した集合論的構造が伴います。

この章の仕事の大部分は、ひとつの設計判断が担います。塔の添字には独立した順序数の型ではなく**集合そのもの**を使い、正則性公理が許す所属に沿った再帰で進めます。つまり `Lset α = ⋃ { Def (Lset β) ∣ β ∈ α }` です。このただ一本の等式が零・後者・極限を同時にカバーし、フォン・ノイマン順序数の上ではまさにゲーデルの塔になります。定義そのものは任意の集合を添字として受け入れ、添字が順序数であるという要求は、クラス `L` を定義する場所で初めて課されます。これと並行して帰納的述語 `isLayer`{.Agda}、すなわち「段階であること」が走ります。その構成子こそ塔の閉包原理であり、二つの見方は章全体で協調します。
<!--/-->

<!--en-->
The chapter works at a fixed universe level `ℓ` inside the cumulative hierarchy V. Its carrier `S` consists of sets with extensional, well-founded membership. The associated structure reads equality and membership as proposition-valued relations, so expressions such as `⟨ x ∈ˢ A ⟩` denote ordinary types of membership proofs. This is the ambient setting for the constructions below.
<!--zh-->
本章在固定的宇宙层级 `ℓ` 上、累积层级 V 内工作。其载体 `S` 由带有外延且良基隶属关系的集合组成。相应结构把相等与隶属读作命题值关系，因此 `⟨ x ∈ˢ A ⟩` 这样的表达式表示通常的隶属证明类型。下文的构造都在这个环境中进行。
<!--ja-->
本章は固定した宇宙レベル `ℓ` で累積階層 V の内部を扱います。その台 `S` は、外延的で整礎的な所属関係をもつ集合からなります。対応する構造では等式と所属を命題値の関係として読み、`⟨ x ∈ˢ A ⟩` のような式は通常の所属証明の型を表します。以下の構成はこの環境で行います。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth

module L.Constructible {ℓ : Level} where

open import FOL.ZFStructure using ( ZFStructure; _↾_; module hPropStructure; Transitive )
```

<!--en-->
Three mathematical ingredients drive the construction. First, well-founded recursion on membership: the hierarchy chapter's principle `∈-induction` lets a function on sets be defined by recursion along `∈ˢ`, which is what the tower itself will be. Second, unions of indexed families, with the two model lemmas that read membership in such a union in each direction. Third, the definability chapter's operator `Def A`, which collects the subsets of `A` definable in the inner world `(A, ∈)` with parameters from `A`; applied stage by stage, it is what pushes the hierarchy upward. The syntax of first-order formulas, in particular the type `Formula`, is carried over from the syntax chapter for exactly this operator.
<!--zh-->
推动构造的数学素材有三。其一是沿成员关系的良基递归：层级章的原理 `∈-induction` 允许沿 `∈ˢ` 递归地定义集合上的函数，塔本身正是这样定义的。其二是索引族的并，以及从两个方向读取这种并中隶属关系的两条模型引理。其三是可定义性章的算子 `Def A`，它收集在内层世界 `(A, ∈)` 中、由 `A` 中参数定义出的 `A` 的子集；逐阶段施加它，正是层级向上生长的动力。一阶公式的语法，尤其是类型 `Formula`，正是为这个算子而从语法章沿用的。
<!--ja-->
構成を進める数学的な材料は三つあります。第一に、所属に沿った整礎再帰です。階層の章の原理 `∈-induction` は、`∈ˢ` に沿った再帰で集合上の関数を定義することを可能にし、塔そのものがまさにこれで定義されます。第二に、添字族の和集合と、その和への所属を両方向に読む二つのモデル補題です。第三に、定義可能性の章の演算子 `Def A` であり、内側の世界 `(A, ∈)` で `A` のパラメータによって定義される `A` の部分集合を集めるもので、これを段階ごとに施すことが階層を上へ伸ばす原動力になります。一階述語論理式の構文、とりわけ型 `Formula` は、まさにこの演算子のために構文の章から引き継がれます。
<!--/-->

```agda
open import FOL.Syntax using ( Formula )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ; ∈-induction; ∈-induction-compute )
open import V.Model {ℓ} using ( union-family-in; union-family-out )
open import L.Definability {ℓ} using ( module DefOf )

open import Cubical.Foundations.HLevels using ( isProp× )
```

<!--en-->
A set of the hierarchy is presented by a small family, and this chapter reads its members through that presentation: for a set `α`, `⟪ α ⟫` is the small index type of its members, `⟪ α ⟫↪` embeds an index back into a set, and `∈ₛ⟪ α ⟫↪ m` certifies that the member named by `m` belongs to `α`. The bridge `∈∈ₛ` connects the hierarchy's native membership `∈` with the structural membership `∈ˢ` in both directions, and `sett X f` forms the set whose members are the values of `f` over `X`. Alongside these, propositional truncation `∥ _ ∥₁` with its introduction `∣ _ ∣₁` gives mere existence: an inhabitant of a truncated statement asserts that a witness exists, without naming one.
<!--zh-->
层级中的集合由一个小族来表现，本章正是通过这种表现读取成员：对集合 `α`，`⟪ α ⟫` 是其成员的小索引类型，`⟪ α ⟫↪` 把索引嵌回集合，`∈ₛ⟪ α ⟫↪ m` 证明 `m` 所指名的成员属于 `α`。桥梁 `∈∈ₛ` 在两个方向上连接层级自身的成员关系 `∈` 与结构成员关系 `∈ˢ`；`sett X f` 构造以 `f` 在 `X` 上取值为成员的集合。与之相伴，命题截断 `∥ _ ∥₁` 及其引入 `∣ _ ∣₁` 给出「仅仅存在」：截断陈述的一个证明断言存在某个见证，而不指名它。
<!--ja-->
階層の集合は小さな族によって表現され、本章はその表現を通して要素を読みます。集合 `α` に対して `⟪ α ⟫` はその要素の小さな添字型であり、`⟪ α ⟫↪` は添字をふたたび集合へ埋め込み、`∈ₛ⟪ α ⟫↪ m` は `m` の指す要素が `α` に属することを証明します。橋渡し `∈∈ₛ` は階層固有の所属 `∈` と構造的な所属 `∈ˢ` を双方向に結び、`sett X f` は `X` 上の `f` の値を要素とする集合を作ります。これらと並んで、命題的切り詰め `∥ _ ∥₁` とその導入 `∣ _ ∣₁` が「単に存在する」を与えます。切り詰められた主張の要素は、証人が存在すると主張するのであって、それを名指しはしません。
<!--/-->

```agda
import Cubical.Data.Empty as Empty
import Cubical.Data.Sum as Sum
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁ )
open import Cubical.HITs.CumulativeHierarchy.Base using ( sett )
```

<!--en-->
The basic constructions are available with membership characterizations: the empty set with `∅-empty`, unordered pairing with `pairing-ax`, and binary and indexed unions with `union-ax`. The truth algebra is then fixed once and for all: propositions at level `ℓ-suc ℓ` form a `TruthAlgebra` via `hPropAlgebra`, and reading the ambient structure `𝒮ᵥ` through `hPropStructure` yields the notations `⟨ _ ⟩` for the type underlying a proposition and `∈ˢ` for structural membership. Every statement of this chapter is phrased in this proposition-valued setting.
<!--zh-->
基本构造连同隶属刻画一并可用：空集配 `∅-empty`，无序配对配 `pairing-ax`，二元并与索引族并配 `union-ax`。真值代数随之一次性选定：层级 `ℓ-suc ℓ` 上的命题经 `hPropAlgebra` 组成 `TruthAlgebra`，而把环境结构 `𝒮ᵥ` 经 `hPropStructure` 展开，便得到记号 `⟨ _ ⟩` 取命题的底层类型、`∈ˢ` 表示结构成员关系。本章的每个陈述都在这个命题值设定中表述。
<!--ja-->
基本の構成は所属の特徴づけとともに使えます。空集合には `∅-empty`、非順序対には `pairing-ax`、二項和と添字族の和には `union-ax` が対応します。真理値代数はここで一度に選ばれます。レベル `ℓ-suc ℓ` の命題は `hPropAlgebra` によって `TruthAlgebra` をなし、周囲の構造 `𝒮ᵥ` を `hPropStructure` を通じて読むことで、命題の基礎型を取る記法 `⟨ _ ⟩` と構造的な所属を表す `∈ˢ` が使えるようになります。本章のすべての主張はこの命題値の設定のなかで述べられます。
<!--/-->

```agda
open import Cubical.HITs.CumulativeHierarchy.Properties
  using ( ∈∈ₛ; ∈-asFiber; ⟪_⟫; ⟪_⟫↪; ∈ₛ⟪_⟫↪_ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ∅; ∅-empty; ⁅_,_⁆; pairing-ax; ⋃_; union-ax; _∪_ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
```

<!--en-->
With the setting in place, the definable power set operator receives its working name: `𝒟 A` is exactly the `Def A` of the definability chapter, the set of subsets of `A` definable over the restricted structure with finitely many parameters from `A`. The mathematical content of that operator, including that its members are subsets of `A` and that a transitive `A` satisfies `A ⊆ 𝒟 A`, was already established there; here it only takes on the short glyph used throughout.
<!--zh-->
设定就位后，可定义幂集算子得到它的工作名：`𝒟 A` 恰是可定义性章中的 `Def A`，即在限制结构上、由 `A` 中有限多个参数定义的 `A` 的子集之集。该算子的数学内容，包括其成员都是 `A` 的子集、以及传递集满足 `A ⊆ 𝒟 A`，均已在彼处建立；这里只是赋予全书通用的短记号。
<!--ja-->
設定が整ったところで、定義可能冪集合の演算子に作業用の名前が与えられます。`𝒟 A` は定義可能性の章の `Def A` そのものであり、制限構造の上で `A` の有限個のパラメータによって定義される `A` の部分集合を集めたものです。この演算子の数学的内容、すなわちその要素がすべて `A` の部分集合であることや、推移的な `A` に対して `A ⊆ 𝒟 A` が成り立つことは、すでにそこで確立済みであり、ここでは本書を通して使われる短い記号を与えるだけです。
<!--/-->

```agda
open hPropStructure 𝒮ᵥ

𝒟 : S → S
𝒟 A = DefOf.Def A
```

<!--en-->
## Transitive sets

Every stage of the hierarchy is transitive: the empty set is transitive, definable power set preserves transitivity, and unions of transitive sets remain transitive. These closure facts match the constructors used to build layers.

(`𝒟` is the book's short glyph for the previous chapter's `Def`, matching the usual script letter for the operator.)
<!--zh-->
## 传递集

层级的每个阶段都是传递的：空集传递，可定义幂集保持传递性，传递集之并仍然传递。这些封闭性事实与构造层所用的构造子逐一对应。

(`𝒟` 是上一章 `Def` 在本书中的短记号，沿用这个算子惯用的花体字母。)
<!--ja-->
## 推移的集合

階層の各段階は推移的です。空集合は推移的であり、定義可能冪集合は推移性を保存し、推移的集合の和も推移的です。これらの閉性は、後で層を作る構成子に一つずつ対応します。

(`𝒟` は前の章の `Def` に対する本書の短い記号で、この演算子に慣用される花文字に合わせたものです。)
<!--/-->

<!--en-->
A set `A` is transitive when every member of a member of `A` is again a member of `A`. The definition `isTransV` instantiates the structure-level closure condition `Transitive 𝒮ᵥ` at the class of sets equal to `A`, so a proof of `isTransV A` is literally a function taking `y ∈ˢ x` and `x ∈ˢ A` to `y ∈ˢ A`. Note the universe: the statement lives at `ℓ-suc ℓ`, since it quantifies over the carrier. Transitivity is a proposition, and `isPropIsTransV` shows this directly: given two proofs `p` and `q`, the conclusions `y ∈ˢ A` are propositions by construction, so they agree pointwise, and cubical function extensionality assembles the pointwise agreement into a path between `p` and `q`. The last line announces the first closure fact, for the empty set.
<!--zh-->
集合 `A` 传递，指 `A` 的成员的成员仍是 `A` 的成员。定义 `isTransV` 把结构层面的闭合条件 `Transitive 𝒮ᵥ` 实例化到「等于 `A` 的集合」这个类上，故 `isTransV A` 的证明字面上就是一个函数：从 `y ∈ˢ x` 与 `x ∈ˢ A` 给出 `y ∈ˢ A`。注意宇宙层级：该陈述对载体做了量化，故位于 `ℓ-suc ℓ`。传递性是一个命题，`isPropIsTransV` 直接证明这一点：给定两个证明 `p` 与 `q`，其结论 `y ∈ˢ A` 按构造是命题，故逐点相等，而立方版的函数外延性把逐点一致组装成 `p` 与 `q` 之间的路径。最后一行宣布第一条封闭性事实，关于空集。
<!--ja-->
集合 `A` が推移的であるとは、`A` の要素の要素が再び `A` の要素になることです。定義 `isTransV` は構造レベルの閉性条件 `Transitive 𝒮ᵥ` を「`A` と等しい集合のクラス」に具体化したものであり、したがって `isTransV A` の証明は文字どおり、`y ∈ˢ x` と `x ∈ˢ A` から `y ∈ˢ A` を与える関数です。宇宙に注意してください。この主張は台を量化するので `ℓ-suc ℓ` に存在します。推移性は命題であり、`isPropIsTransV` がこれを直接示します。二つの証明 `p` と `q` が与えられれば、その結論 `y ∈ˢ A` は構成により命題なので各点で一致し、立方の関数外延性がこの各点一致を `p` と `q` の間のパスへ組み立てます。最後の行は、空集合についての最初の閉性事実を宣言しています。
<!--/-->

```agda
isTransV : S → Type (ℓ-suc ℓ)
isTransV A = Transitive 𝒮ᵥ (λ x → x ∈ˢ A)

isPropIsTransV : (A : S) → isProp (isTransV A)
isPropIsTransV A p q i {x} {y} y∈x x∈A = (y ∈ˢ A) .snd (p y∈x x∈A) (q y∈x x∈A) i

∅-trans : isTransV ∅
```

<!--en-->
The empty set case is vacuous: from `x ∈ˢ ∅` one extracts a native member of `∅` via `∈∈ₛ`, and `∅-empty` derives absurdity from it, so any implication into `y ∈ˢ A` holds. For the definable power set, two lemmas from the previous chapter combine. A member `x` of `𝒟 A` is a definable subset, hence `y ∈ x` forces `y ∈ A` (`Def∋⊆A`); that is exactly the hypothesis `Atr` applied to a transitive `A`, under which `A ⊆ 𝒟 A` (`A⊆Def`) puts `y` into `𝒟 A`. Finally `⋃-trans` states the union principle: if every member of `x` is transitive, then so is `⋃ x`, the set of all members of members of `x`.
<!--zh-->
空集情形是空洞的：从 `x ∈ˢ ∅` 经 `∈∈ₛ` 提取 `∅` 的原生成员，`∅-empty` 由此导出荒谬，故任何到达 `y ∈ˢ A` 的蕴涵都成立。对可定义幂集，前一章的两条引理合用。`𝒟 A` 的成员 `x` 是可定义子集，故 `y ∈ x` 迫使 `y ∈ A` (`Def∋⊆A`)；把传递性假设 `Atr` 用于此，传递集满足 `A ⊆ 𝒟 A` (`A⊆Def`)，从而 `y` 进入 `𝒟 A`。最后 `⋃-trans` 陈述并原理：若 `x` 的每个成员都传递，则 `⋃ x`，即 `x` 的成员之成员的全体，也传递。
<!--ja-->
空集合の場合は空虚に成り立ちます。`x ∈ˢ ∅` から `∈∈ₛ` を経て `∅` の本来の要素が取り出せ、`∅-empty` がそこから矛盾を導くので、`y ∈ˢ A` へ至る任意の含意が成り立ちます。定義可能冪集合については、前の章の二つの補題を組み合わせます。`𝒟 A` の要素 `x` は定義可能な部分集合なので、`y ∈ x` なら `y ∈ A` が強制され (`Def∋⊆A`)、これに推移性の仮定 `Atr` を適用すれば、推移的な `A` に対する `A ⊆ 𝒟 A` (`A⊆Def`) によって `y` は `𝒟 A` に入ります。最後に `⋃-trans` が和の原理を述べます。`x` の各要素が推移的ならば、`x` の要素の要素全体の集合 `⋃ x` も推移的です。
<!--/-->

```agda
∅-trans {x} y∈x x∈∅ = Empty.rec (∅-empty x (∈∈ₛ {a = x} {b = ∅} .fst x∈∅))

𝒟-trans : ∀ {A} → isTransV A → isTransV (𝒟 A)
𝒟-trans {A} Atr {x} {y} y∈x x∈𝒟A =
  DefOf.Refine.A⊆Def A Atr y (DefOf.Def∋⊆A A x x∈𝒟A y y∈x)

⋃-trans : (x : S) → ((y : S) → ⟨ y ∈ˢ x ⟩ → isTransV y) → isTransV (⋃ x)
```

<!--en-->
To see a member of the union, one must first see that it is a member at all. The hypothesis `u∈⋃x` is membership in the ambient hierarchy; `∈∈ₛ` in its second direction converts it into the truncated fiber form, and `union-ax` characterizes such membership: `u ∈ ⋃ x` holds merely if some `w ∈ x` has `u ∈ w`. The truncation is essential: the axiom does not name the intermediate `w`, it merely asserts that one exists. The proof therefore maps inside the truncation, and in the branch where a pair `w , (w∈ₛx , u∈ₛw)` is given, the two coercions `∈∈ₛ` recover usable hypotheses `w∈x` and `u∈w` from the fiber data.
<!--zh-->
要看并的一个成员，必须先看它究竟是不是成员。假设 `u∈⋃x` 是环境层级中的成员关系；`∈∈ₛ` 的第二方向把它转换成截断的纤维形式，而 `union-ax` 刻画这种隶属：`u ∈ ⋃ x` 仅仅当某个 `w ∈ x` 满足 `u ∈ w`。截断不可省略：公理并不指名中间的 `w`，只断言其存在。故证明在截断内部做映射，而在给出对 `w , (w∈ₛx , u∈ₛw)` 的分支里，两次 `∈∈ₛ` 从纤维数据恢复出可用的假设 `w∈x` 与 `u∈w`。
<!--ja-->
和の要素を見るには、まずそれが実際に要素であることを見なければなりません。仮定 `u∈⋃x` は周囲の階層における所属であり、`∈∈ₛ` の第二の向きがそれを切り詰められたファイバー形式へ変換します。そして `union-ax` がその所属を特徴づけます。すなわち `u ∈ ⋃ x` となるのは、`u ∈ w` なる `w ∈ x` が単に存在するとき、そしてそのときに限ります。命題的切り詰めは本質的です。公理は途中の `w` を名指しせず、その存在を主張するだけだからです。したがって証明は切り詰めの内部で写像を行い、対 `w , (w∈ₛx , u∈ₛw)` が与えられる分岐では、二度の `∈∈ₛ` がファイバーのデータから使える仮定 `w∈x` と `u∈w` を復元します。
<!--/-->

```agda
⋃-trans x mem {u} {v} v∈u u∈⋃x =
  ∈∈ₛ {a = v} {b = ⋃ x} .snd (union-ax x v .snd
    (PT.map
      (λ { (w , (w∈ₛx , u∈ₛw)) →
        let w∈x = ∈∈ₛ {a = w} {b = x} .snd w∈ₛx
```

<!--en-->
In that branch the hypothesis `mem w w∈x` says `w` is transitive, so `v ∈ u` and `u ∈ w` give `v ∈ w`; coercing back with `∈∈ₛ` in the first direction repackages the data as a valid fiber for `union-ax`, and the elimination of the truncation is legitimate because the target, membership of `v` in `⋃ x`, is a proposition. The binary union follows: `A ∪ B` is defined as `⋃ ⁅ A , B ⁆`, so `∪-trans` applies `⋃-trans` to the pair, and the remaining obligation is that every member of the pair is transitive, which the local statement `prem` must supply.
<!--zh-->
在该分支中，假设 `mem w w∈x` 说 `w` 传递，故 `v ∈ u` 与 `u ∈ w` 给出 `v ∈ w`；再用第一方向的 `∈∈ₛ` 转换，这些数据成为 `union-ax` 合法的纤维，而截断消去合法，因为目标，即 `v` 属于 `⋃ x`，是命题。二元并随之得到：`A ∪ B` 定义为 `⋃ ⁅ A , B ⁆`，故 `∪-trans` 就是把 `⋃-trans` 用于这个配对，剩余的义务是配对的每个成员都传递，而这正是局部陈述 `prem` 要供给的。
<!--ja-->
この分岐では、仮定 `mem w w∈x` が `w` の推移性を言うので、`v ∈ u` と `u ∈ w` から `v ∈ w` が得られます。第一の向きの `∈∈ₛ` で改めて変換すると、このデータは `union-ax` の正当なファイバーになり、命題的切り詰めの消去も、目標である「`v` の `⋃ x` への所属」が命題であるため正当です。二項和はこれに続きます。`A ∪ B` は `⋃ ⁅ A , B ⁆` と定義されるので、`∪-trans` はこの対への `⋃-trans` の適用であり、残る義務は対の各要素が推移的であることで、これを供給するのが局所的な主張 `prem` です。
<!--/-->

```agda
            u∈w = ∈∈ₛ {a = u} {b = w} .snd u∈ₛw
        in w , (w∈ₛx , ∈∈ₛ {a = v} {b = w} .fst (mem w w∈x v∈u u∈w)) })
      (union-ax x u .fst (∈∈ₛ {a = u} {b = ⋃ x} .fst u∈⋃x))))

∪-trans : ∀ {A B} → isTransV A → isTransV B → isTransV (A ∪ B)
∪-trans {A} {B} tA tB = ⋃-trans ⁅ A , B ⁆ prem
```

<!--en-->
The obligation `prem` asks: for each `y` in the pair, is `y` transitive? Pairing characterizes membership merely: `y ∈ ⁅ A , B ⁆` holds merely if `y` is `A` or `y` is `B`, given by propositional truncation rather than a chosen disjunct. The elimination runs into the proposition `isTransV y`, and each branch carries an equation `p` identifying `y` with `A` or with `B`; since transitivity is invariant under equality of sets, `subst isTransV (sym p)` transports the already-known proof `tA` or `tB` along that equation to type `isTransV y`.
<!--zh-->
义务 `prem` 问的是：配对中的每个 `y` 是否传递？配对的隶属刻画是「仅仅」式的：`y ∈ ⁅ A , B ⁆` 仅仅当 `y` 是 `A` 或 `y` 是 `B`，由命题截断给出，而非选定的析取支。消去的目标是命题 `isTransV y`，每个分支携带一条等式 `p` 把 `y` 与 `A` 或 `B` 等同；由于传递性在集合相等下不变，`subst isTransV (sym p)` 沿这条等式把已知的 `tA` 或 `tB` 传送到类型 `isTransV y`。
<!--ja-->
義務 `prem` が問うのは、対の各 `y` が推移的かどうかです。対の所属は「単に」の形で特徴づけられます。すなわち `y ∈ ⁅ A , B ⁆` となるのは、`y` が `A` であるか `y` が `B` であることが単に成り立つときであり、選ばれた選言肢ではなく命題的切り詰めによって与えられます。消去の目標は命題 `isTransV y` であり、各分岐は `y` を `A` ないし `B` と同一視する等式 `p` を伴います。推移性は集合の等しさで不変なので、`subst isTransV (sym p)` が既知の証明 `tA` ないし `tB` をその等式に沿って型 `isTransV y` へ輸送します。
<!--/-->

```agda
  where
  prem : (y : S) → ⟨ y ∈ˢ ⁅ A , B ⁆ ⟩ → isTransV y
  prem y y∈ = PT.rec (isPropIsTransV y)
    (λ { (Sum.inl p) → subst isTransV (sym p) tA
       ; (Sum.inr p) → subst isTransV (sym p) tB })
```

<!--en-->
The last line of `prem` feeds the truncated membership through `pairing-ax`, the case analysis is complete, and with it the binary case. The family form `setUnion-trans` handles a small indexed family at once: given a type `X : Type ℓ` and a function `f : X → S`, the set `sett X f` has as members the values `f x`, and each `f x` is transitive by hypothesis. Here too membership in the index set is truncated: the proof receives a pair `x , fx≡y`, an index together with a path identifying the value with `y`.
<!--zh-->
`prem` 的末行把截断的隶属经 `pairing-ax` 送入上述情形分析，情形分析完成，二元情形随之完成。族形式 `setUnion-trans` 一次处理小的索引族：给定类型 `X : Type ℓ` 与函数 `f : X → S`，集合 `sett X f` 的成员是取值 `f x`，而每个 `f x` 由假设传递。这里对索引集合的成员同样是截断的：证明收到的是对 `x , fx≡y`，即一个索引连同把取值与 `y` 等同的路径。
<!--ja-->
`prem` の最後の行が命題的切り詰めされた所属を `pairing-ax` に通して場合分けを完成させ、二項の場合が終わります。族の形式 `setUnion-trans` は小さな添字族を一度に扱います。型 `X : Type ℓ` と関数 `f : X → S` が与えられれば、集合 `sett X f` の要素は値 `f x` であり、各 `f x` は仮定により推移的です。ここでも添字集合への所属は命題的切り詰めされており、証明が受け取るのは対 `x , fx≡y`、すなわち添字と、その値を `y` と同一視するパスです。
<!--/-->

```agda
    (pairing-ax A B y .fst (∈∈ₛ {a = y} {b = ⁅ A , B ⁆} .fst y∈))

setUnion-trans : (X : Type ℓ) (f : X → S) → ((x : X) → isTransV (f x))
               → isTransV (⋃ (sett X f))
setUnion-trans X f hf = ⋃-trans (sett X f)
  (λ y → PT.rec (isPropIsTransV y)
```

<!--en-->
Transport again does the bookkeeping: `subst isTransV fx≡y (hf x)` moves the transitivity proof of `f x` along the identification to a proof for `y`, and eliminating the truncation is allowed because `isTransV y` is a proposition. With these closure principles in place, the empty set, the definable power set, and unions in general, binary, and indexed form, the proof below that every layer is transitive becomes a one-line dispatch: each constructor is matched with the corresponding lemma proved here.
<!--zh-->
传输再次承担簿记：`subst isTransV fx≡y (hf x)` 沿等同把 `f x` 的传递性证明移到 `y` 上，而截断消去合法，因为 `isTransV y` 是命题。有了这些封闭性原则，空集、可定义幂集、以及一般、二元、索引三种形式的并，下文证明每个层都传递的归纳就成了一行分发：每个构造子对应这里证明的相应引理。
<!--ja-->
ここでも輸送が帳簿づけを担います。`subst isTransV fx≡y (hf x)` は `f x` の推移性の証明を同一視に沿って `y` へ移し、`isTransV y` が命題であるため命題的切り詰めの消去が許されます。これで閉包原理、空集合、定義可能冪集合、そして一般・二項・添字付きの三形態の和、がそろいました。以下で証明する、すべての層が推移的であることの帰納は一行の振り分けとなり、各構成子がここで証明した対応する補題と結びます。
<!--/-->

```agda
    (λ { (x , fx≡y) → subst isTransV fx≡y (hf x) }))
```

<!--en-->
## Ordinals, just the predicate

The indices that matter for the constructible hierarchy are the von Neumann ordinals, and inside a well-founded, extensional universe the classical definition reduces to very little: an **ordinal** is a transitive set of transitive sets. Well-foundedness and extensionality need not be written into the definition, since the hierarchy guarantees them everywhere; linearity is a classical theorem deferred to later chapters, not part of the notion itself. This chapter records the predicate and its propositionality; the theory of ordinals gets its own chapters when needed.
<!--zh-->
## 序数，仅取谓词

对可构造层级真正起作用的索引是冯·诺伊曼序数，而在良基、外延的宇宙里，经典定义所剩无几：**序数**就是由传递集组成的传递集。良基与外延无须写进定义，层级处处保证它们成立；线序则是留待后文的经典定理，不属于概念本身。本章记录这个谓词及其命题性；序数的理论待需要时另章展开。
<!--ja-->
## 順序数の述語

構成可能階層の添字として働くのはフォン・ノイマン順序数であり、整礎で外延的な宇宙の内部では、古典的な定義はわずかなものに縮みます。すなわち**順序数**とは、推移的な集合からなる推移的な集合です。整礎性と外延性は定義に書き込む必要がありません。階層が至る所でそれらを保証するからです。線形性は後の章で証明される古典的な定理であって、概念そのものの一部ではありません。この章ではこの述語とその命題性を記録し、順序数の理論は必要になったときに専用の章で展開されます。
<!--/-->

<!--en-->
Thus `IsOrd A` is the conjunction of two propositions: `A` is transitive, and every member of `A` is transitive. The proof `isPropIsOrd A` combines the propositionality of these two components using closure under products and dependent functions. This certificate is used explicitly in the definition of `isL`, where `(IsOrd α , isPropIsOrd α)` supplies the truth value asserting that the stage index is an ordinal.
<!--zh-->
因此，`IsOrd A` 是两个命题的合取：`A` 是传递集，而且 `A` 的每个成员都是传递集。证明 `isPropIsOrd A` 利用命题在积与依值函数下的封闭性，把两个分量的命题性合并起来。`isL` 的定义会显式使用这份证书，其中 `(IsOrd α , isPropIsOrd α)` 给出「阶段指标是序数」这一真值。
<!--ja-->
したがって `IsOrd A` は二つの命題の積です。`A` が推移的であり、かつ `A` の各要素が推移的である、という二つです。`isPropIsOrd A` は、命題が積と依存関数に関して閉じていることを使い、両成分の命題性を合わせます。この証明書は `isL` の定義で明示的に使われ、`(IsOrd α , isPropIsOrd α)` が「段階の添字は順序数である」という真理値を与えます。
<!--/-->

```agda
IsOrd : S → Type (ℓ-suc ℓ)
IsOrd A = isTransV A × ((x : S) → ⟨ x ∈ˢ A ⟩ → isTransV x)

isPropIsOrd : (A : S) → isProp (IsOrd A)
isPropIsOrd A = isProp× (isPropIsTransV A)
                  (isPropΠ λ x → isPropΠ λ _ → isPropIsTransV x)
```

<!--en-->
## Layers

`isLayer A` records closure of the tower by five constructors. The empty set is a layer; applying `𝒟` to a layer gives a layer; and unions are admitted in three forms, from a set all of whose members are layers, from two layers, or from a small indexed family of layers. These are the induction cases available when proving a property of every layer. In particular, each case matches one of the transitivity lemmas from the preceding section.
<!--zh-->
## 层

`isLayer A` 用五个构造子记录塔的封闭性：空集是层；对一层应用 `𝒟` 仍得到层；并集则有三种形式，分别来自成员全是层的集合、两个层以及层的小指标族。要证明每个层都具有某性质时，可用的归纳情形正是这五种。特别地，每个情形都对应上一节的一条传递性引理。
<!--ja-->
## 層

`isLayer A` は塔の閉包性を五つの構成子で記録します。空集合は層であり、層に `𝒟` を適用したものも層です。和集合については、要素がすべて層である集合、二つの層、小さく添字付けられた層の族、という三つの形を受け入れます。すべての層について性質を証明するときの帰納法の場合分けは、この五つです。特に各場合は、前節で証明した推移性の補題の一つに対応します。
<!--/-->

<!--en-->
The predicate is an inductive family indexed by the carrier, and the constructors are read as generation rules for stages. The base case says the empty set is a stage. Closure under `𝒟` says that if `A` is a stage then so is its definable power set, mirroring the successor step. The general union constructor mirrors the limit step: if `x` is a set whose members are all, untruncatedly, stages, then `⋃ x` is a stage. The binary union constructor covers `A ∪ B` directly from stage witnesses for `A` and `B`. Each constructor mirrors one of the transitivity lemmas of the previous section, with `isTransV` replaced by `isLayer`; this parallelism is what makes the next proof immediate.
<!--zh-->
这个谓词是以载体为索引的归纳族，其构造子被读作阶段的生成规则。基底说空集是阶段。对 `𝒟` 的闭包说：若 `A` 是阶段，则其可定义幂集也是阶段，对应后继步骤。一般并构造子对应极限步骤：若 `x` 的成员全部、以不加截断的方式是阶段，则 `⋃ x` 是阶段。二元并构造子直接从 `A` 与 `B` 的阶段见证覆盖 `A ∪ B`。每个构造子对应上一节的一条传递性引理，只是把 `isTransV` 换成 `isLayer`；正是这种平行性使下一条证明变得直接。
<!--ja-->
この述語は台を添字とする帰納的な族であり、構成子は段階の生成規則として読めます。基底の場合は、空集合が段階であること。`𝒟` による閉包は、`A` が段階ならその定義可能冪集合も段階であることで、後者ステップに対応します。一般の和の構成子は極限ステップに対応します。`x` の要素がすべて、切り詰めなしに層であるなら、`⋃ x` も層です。二項和の構成子は、`A` と `B` の層の証明から直接 `A ∪ B` を扱います。各構成子は、前節の推移性の補題の一つを `isTransV` を `isLayer` に置き換えた形に対応し、この平行性こそが次の証明を即座にします。
<!--/-->

```agda
data isLayer : S → Type (ℓ-suc ℓ) where
  ∅-layer        : isLayer ∅
  𝒟-layer        : ∀ {A} → isLayer A → isLayer (𝒟 A)
  union-layer    : (x : S) → ((y : S) → ⟨ y ∈ˢ x ⟩ → isLayer y) → isLayer (⋃ x)
  union₂-layer   : ∀ {A B} → isLayer A → isLayer B → isLayer (A ∪ B)
```

<!--en-->
The small-indexed family constructor completes the picture: for a type `X : Type ℓ` and a family `f : X → S` all of whose values are stages, the union `⋃ (sett X f)` is a stage. This is the constructor through which a limit stage can be assembled from the family of earlier stages. Now the induction: to prove `layer-trans`, that every layer is transitive, one receives the layer as an inductive argument, so the case is determined by its constructor. The empty case is `∅-trans` verbatim. The `𝒟` case applies `𝒟-trans`, whose premise is the induction hypothesis `layer-trans lA` for the sublayer.
<!--zh-->
小索引族构造子补全全图：对类型 `X : Type ℓ` 与族 `f : X → S`，若所有取值都是阶段，则并 `⋃ (sett X f)` 是阶段。极限阶段正是经由这个构造子从更早阶段的族组装出来。接下来是归纳：要证 `layer-trans`，即每个层都传递，层以归纳参数的形式给出，情形由其构造子决定。空集情形逐字就是 `∅-trans`。`𝒟` 情形应用 `𝒟-trans`，其前提正是对子层的归纳假设 `layer-trans lA`。
<!--ja-->
小さな添字族の構成子が全体を完成させます。型 `X : Type ℓ` と族 `f : X → S` に対し、すべての値が層なら、和 `⋃ (sett X f)` も層です。極限段階は、まさにこの構成子を通して前段階の族から組み立てられます。次に帰納です。`layer-trans`、すなわちすべての層が推移的であることを示すには、層を帰納的な引数として受け取るので、場合はその構成子で定まります。空集合の場合はそのまま `∅-trans` です。`𝒟` の場合は `𝒟-trans` を適用し、その前提は下の層に対する帰納仮定 `layer-trans lA` です。
<!--/-->

```agda
  setUnion-layer : (X : Type ℓ) (f : X → S)
                 → ((x : X) → isLayer (f x)) → isLayer (⋃ (sett X f))

layer-trans : ∀ {A} → isLayer A → isTransV A
layer-trans ∅-layer = ∅-trans
layer-trans (𝒟-layer {A} lA) = 𝒟-trans {A} (layer-trans lA)
```

<!--en-->
The three union cases dispatch just as directly. The general union case hands the memberwise induction hypothesis to `⋃-trans`: the lemma wants, for each member `y` of `x`, a transitivity proof for `y`, and the constructor premise `mem` supplies exactly that, untruncated, so no elimination of truncation is needed. The binary case is `∪-trans` on the two induction hypotheses. The family case is `setUnion-trans` with the pointwise induction hypothesis. The section thus establishes, by structural recursion alone, that every stage of the tower is a transitive set, the fact used by the transitivity of the class `L` later in this chapter.
<!--zh-->
三种并的情形同样直接分发。一般并情形把逐成员的归纳假设交给 `⋃-trans`：该引理要求对 `x` 的每个成员 `y` 给出 `y` 的传递性证明，而构造子前提 `mem` 恰好不加截断地供给，故无需消去截断。二元情形是对两个归纳假设应用 `∪-trans`。族情形是带逐点归纳假设的 `setUnion-trans`。于是本节仅凭结构递归就确立了塔的每个阶段都是传递集，本章稍后证明类 `L` 的传递性时正要用到这一事实。
<!--ja-->
三つの和の場合も同じように直接に振り分けられます。一般の和の場合は、要素ごとの帰納仮定を `⋃-trans` に渡します。この補題は `x` の各要素 `y` に対する `y` の推移性の証明を要求しますが、構成子の前提 `mem` がまさにそれを切り詰めなしで供給するため、命題的切り詰めの消去は必要ありません。二項の場合は二つの帰納仮定に対する `∪-trans` です。族の場合は各点の帰納仮定を伴う `setUnion-trans` です。こうしてこの節は、構造的再帰だけで塔のすべての段階が推移的集合であることを確立します。本章の後半でクラス `L` の推移性を示す際に用いられる事実です。
<!--/-->

```agda
layer-trans (union-layer x mem) = ⋃-trans x (λ y y∈x → layer-trans (mem y y∈x))
layer-trans (union₂-layer lA lB) = ∪-trans (layer-trans lA) (layer-trans lB)
layer-trans (setUnion-layer X f hf) = setUnion-trans X f (λ x → layer-trans (hf x))
```

<!--en-->
## The tower

Now the tower itself, defined by recursion on membership. Two technical measures come first. `𝒟` unfolds to a sizable `sett` over formulas, and the recursion machinery itself unfolds to the accessibility eliminator, so if left exposed both would enter the conversions that follow; `opaque`{.Agda} makes `𝒟ₒ` and the tower opaque, opened only inside blocks that explicitly unfold them, and `Lset-compute`{.Agda} serves as the tower's declared unfolding. The step takes the union, over the members `β` of the index `α`, of `𝒟ₒ` applied to the recursive values; the computation rule holds as a propositional path.
<!--zh-->
## 塔

现在构造塔本身，沿成员关系递归。先做两项技术处理：`𝒟` 的展开是公式上较大的 `sett`，递归机制自身又会展开成可及性消去子，若不加遮蔽，二者都会进入后续的转换；`opaque`{.Agda} 让 `𝒟ₒ` 与塔成为黑箱，只在显式展开它们的块内打开，`Lset-compute`{.Agda} 则作为塔的被声明展开式。步进取索引 `α` 的成员 `β`，`𝒟ₒ` 作用于递归值再取并；计算规则作为命题路径成立。
<!--ja-->
## 階層

いよいよ塔そのものを、所属に沿った再帰で構成します。まず二つの技術的な措置を施します。`𝒟` を展開すると論理式上の大きな `sett` になり、再帰の仕組みそのものも到達可能性の消去子へ展開されます。露出したままだと両者がその後の変換に割り込むため、`opaque`{.Agda} によって `𝒟ₒ` と塔を不透明にし、明示的に展開するブロックの内側でのみ開き、`Lset-compute`{.Agda} を塔の宣言された展開式とします。ステップは、添字 `α` の要素 `β` にわたって再帰値に `𝒟ₒ` を施したものの和集合を取り、計算規則は命題としてのパスとして成り立ちます。
<!--/-->

<!--en-->
The operator is first repackaged as `𝒟ₒ` inside an `opaque` block, so that the elaborate definition of `Def` stays hidden unless a lemma explicitly asks to unfold it. The step function `LsetStep` receives an index set `α` and, for each member `β` of `α`, the recursive value `rec β`; membership here appears through `∈ᵗ`, the type-valued reading of the structural membership proposition. The body forms the family that sends a small index `m : ⟪ α ⟫` to `𝒟ₒ` applied to the recursive value at the member `⟪ α ⟫↪ m` named by `m`, and takes its union. Unfolding the union over the index type, the intended reading is exactly `⋃ { 𝒟ₒ (Lset β) ∣ β ∈ α }`, one equation serving zero, successors, and limits alike: for `α` empty the union is empty, for a successor it repeats the classical next step, and for a limit it collects all earlier stages at once.
<!--zh-->
算子先在 `opaque` 块内被重新包装为 `𝒟ₒ`，使 `Def` 精细的定义保持隐藏，除非某条引理显式要求展开。步进函数 `LsetStep` 接收索引集 `α`，以及对 `α` 的每个成员 `β` 的递归值 `rec β`；这里的成员关系经由 `∈ᵗ`，即结构成员命题的取类型读法出现。函数体构造一个族：把小索引 `m : ⟪ α ⟫` 映到 `𝒟ₒ` 作用于 `m` 所指名成员 `⟪ α ⟫↪ m` 处递归值的结果，再取其并。沿索引类型展开这个并，其意读恰好是 `⋃ { 𝒟ₒ (Lset β) ∣ β ∈ α }`，一条方程同时服务零、后继与极限：`α` 为空时并为空，后继时重复经典的下一步，极限时一次收齐所有更早阶段。
<!--ja-->
まず演算子を `opaque` ブロックの内側で `𝒟ₒ` として包み直し、`Def` の込み入った定義が、補題が明示的に展開を求めない限り姿を現さないようにします。ステップ関数 `LsetStep` は添字集合 `α` と、`α` の各要素 `β` に対する再帰値 `rec β` を受け取ります。ここでの所属は、構造的な所属の命題を型として読む `∈ᵗ` を通して現れます。本体は、小さな添字 `m : ⟪ α ⟫` を、`m` の指す要素 `⟪ α ⟫↪ m` での再帰値に `𝒟ₒ` を施したものへ写す族を作り、その和集合を取ります。この和を添字型にわたって展開すれば、意図された読みはまさに `⋃ { 𝒟ₒ (Lset β) ∣ β ∈ α }` であり、一本の等式が零・後者・極限を等しく扱います。`α` が空なら和は空、後者なら古典的な次のステップを繰り返し、極限ならすべての前段階を一度に集めます。
<!--/-->

```agda
opaque
  𝒟ₒ : S → S
  𝒟ₒ A = 𝒟 A

LsetStep : (α : S) → (∀ β → β ∈ᵗ α → S) → S
LsetStep α rec = ⋃ (sett ⟪ α ⟫ (λ m → 𝒟ₒ (rec (⟪ α ⟫↪ m) (mem m))))
```

<!--en-->
The helper `mem` supplies the conversion the body needs: the member of `α` named by an index `m` is `⟪ α ⟫↪ m`, and `∈ₛ⟪ α ⟫↪ m` certifies that this set belongs to `α` in the small presentation; `∈∈ₛ` converts that into the type-valued membership `∈ᵗ` that `rec` expects. The tower itself is then a single call: `Lset` is defined as `∈-induction` applied to the step. This is well-founded recursion on membership, justified once and for all by the regularity theorem of the hierarchy chapter; the recursion index is the set `α` itself, and ordinalhood of the index is not required by the raw definition, it will be imposed where the hierarchy is used.
<!--zh-->
辅助引理 `mem` 提供函数体所需的转换：索引 `m` 指名的 `α` 的成员是 `⟪ α ⟫↪ m`，`∈ₛ⟪ α ⟫↪ m` 证明这个集合在小表示中属于 `α`；`∈∈ₛ` 再把它转换为 `rec` 所期望的取类型成员关系 `∈ᵗ`。塔本身随之只是一次调用：`Lset` 定义为 `∈-induction` 作用于步进函数。这是沿成员关系的良基递归，其正当性由层级章的正则性定理一次性给出；递归索引就是集合 `α` 自身，原始定义不要求索引是序数，序数性只在使用层级之处施加。
<!--ja-->
補助関数 `mem` が本体に必要な変換を供給します。添字 `m` の指す `α` の要素は `⟪ α ⟫↪ m` であり、`∈ₛ⟪ α ⟫↪ m` がこの集合が小さな表現で `α` に属することを証明します。そして `∈∈ₛ` がそれを、`rec` が期待する型としての所属 `∈ᵗ` へ変換します。塔そのものはただ一度の呼び出しです。`Lset` はステップ関数に `∈-induction` を適用したものとして定義されます。これは所属に沿った整礎再帰であり、その正当性は階層の章の正則性の定理が一度に与えます。再帰の添字は集合 `α` そのものであり、素の定義は添字の順序数性を要求しません。順序数性が課されるのは、この階層を使う場所においてです。
<!--/-->

```agda
  where
  mem : (m : ⟪ α ⟫) → ⟪ α ⟫↪ m ∈ᵗ α
  mem m = ∈∈ₛ {a = ⟪ α ⟫↪ m} {b = α} .snd (∈ₛ⟪ α ⟫↪ m)

opaque
  Lset : S → S
```

<!--en-->
Both `𝒟ₒ` and `Lset` are wrapped in their own `opaque` blocks, so the Agda term for either stays abstract during type checking; whatever unfolds inside the recursion machinery, an accessibility eliminator, cannot leak into later conversions. What replaces blind unfolding is a declared computation rule: `Lset-compute` states, as a propositional path, that `Lset α` equals the step applied to `α` with the recursive values `λ β _ → Lset β`. This is exactly the shape of `∈-induction-compute` from the hierarchy chapter instantiated at the step; the equation need not hold definitionally, and stating it explicitly lets later proofs rewrite `Lset α` by this one controlled equation instead of opening the recursion machinery.
<!--zh-->
`𝒟ₒ` 与 `Lset` 各自被包在 `opaque` 块中，二者的 Agda 项在类型检查期间保持抽象；递归机制内部，即某个可及性消去子，展开出的一切都不会泄漏到后续的转换中。取代盲目展开的是一条被声明的计算规则：`Lset-compute` 以命题路径陈述 `Lset α` 等于把步进函数作用于 `α` 与递归值 `λ β _ → Lset β` 的结果。这正是层级章的 `∈-induction-compute` 在该步进上的实例化；该等式未必定义性成立，而显式陈述它，使后续证明得以按这一条受控的等式改写 `Lset α`，而不必打开递归机制。
<!--ja-->
`𝒟ₒ` と `Lset` はそれぞれ固有の `opaque` ブロックで包まれるため、両者の Agda の項は型検査のあいだ抽象的なままです。再帰の仕組みの内側、つまりある到達可能性の消去子で何が展開されようと、それが後の変換に漏れ出すことはありません。盲目的な展開の代わりとなるのが、宣言された計算規則です。`Lset-compute` は、`Lset α` が `α` と再帰値 `λ β _ → Lset β` にステップを適用したものに等しいことを、命題としてのパスとして述べます。これは階層の章の `∈-induction-compute` をこのステップで実例化した恰好であり、この等式は定義的に成り立つとは限りません。明示的に述べておくことで、以後の証明は再帰の仕組みを開く代わりに、この一本の制御された等式で `Lset α` を書き換えられます。
<!--/-->

```agda
  Lset = ∈-induction LsetStep

opaque
  unfolding Lset
  Lset-compute : (α : S) → Lset α ≡ LsetStep α (λ β _ → Lset β)
  Lset-compute = ∈-induction-compute LsetStep
```

<!--en-->
Every value of the tower is a layer: unfold once with `Lset-compute`{.Agda}, apply the inductive hypothesis to each member, raise by `𝒟ₒ-layer`{.Agda} (the opaque definition unfolds exactly here), and conclude with `setUnion-layer`{.Agda} that the union of the family is again a layer.
<!--zh-->
塔的每个值都是层：先用 `Lset-compute`{.Agda} 展开一次，对每个成员应用归纳假设，再经 `𝒟ₒ-layer`{.Agda} 升一层 (不透明定义只在此处展开)，最后用 `setUnion-layer`{.Agda} 证明族的并仍是层。
<!--ja-->
塔のすべての値は層です。まず `Lset-compute`{.Agda} で一度展開し、各要素に帰納仮定を適用し、`𝒟ₒ-layer`{.Agda} で一段上げ (不透明な定義が展開されるのはまさにここだけです)、最後に `setUnion-layer`{.Agda} によって族の和が再び層であると結論します。
<!--/-->

<!--en-->
The bridge from the operator to the predicate costs one line. Inside a block that unfolds `𝒟ₒ`, the statement `𝒟ₒ-layer` is literally the constructor `𝒟-layer`, since `𝒟ₒ A` computes to `𝒟 A`; this is the only place in the chapter that needs to look inside the opaque wrapper, and afterwards every use of the operator can stay abstract. The goal `Lset-layer` then says that the tower lands entirely inside the inductive predicate: every stage `Lset α` is a layer. Its proof is itself an application of membership induction, the same principle that defined the tower.
<!--zh-->
从算子到谓词的桥只花一行。在展开 `𝒟ₒ` 的块内，陈述 `𝒟ₒ-layer` 字面上就是构造子 `𝒟-layer`，因为 `𝒟ₒ A` 化归为 `𝒟 A`；这是全章唯一需要查看不透明包装内部之处，此后对算子的每个使用都可保持抽象。目标 `Lset-layer` 随之说塔完全落在归纳谓词之内：每个阶段 `Lset α` 都是层。其证明本身又是一次成员归纳的应用，即定义塔的那条同一原理。
<!--ja-->
演算子から述語への橋渡しは一行で済みます。`𝒟ₒ` を展開するブロックの内側では、`𝒟ₒ-layer` という主張は文字どおり構成子 `𝒟-layer` です。`𝒟ₒ A` は `𝒟 A` へ簡約されるからです。本章で不透明な包みの内側を見る必要があるのはここだけで、これ以後は演算子のすべての使用が抽象的なままで済みます。目標 `Lset-layer` は、塔がまるごと帰納的述語の内側に落ちること、すなわちすべての段階 `Lset α` が層であることを言います。その証明自体が、塔を定義したのと同じ原理である所属帰納の適用です。
<!--/-->

```agda
opaque
  unfolding 𝒟ₒ
  𝒟ₒ-layer : ∀ {A} → isLayer A → isLayer (𝒟ₒ A)
  𝒟ₒ-layer = 𝒟-layer

Lset-layer : (α : S) → isLayer (Lset α)
```

<!--en-->
The step function of this induction receives `α` and the inductive hypothesis `IH` giving a layer proof for `Lset β` at each member `β` of `α`. Since `Lset` is opaque, the goal `isLayer (Lset α)` is not directly matchable against a constructor; it must first be transported. The equation `Lset-compute α` identifies `Lset α` with the step's union, and `subst isLayer (sym (Lset-compute α))` moves the target along that path in the right direction, so the goal becomes `isLayer (⋃ (sett ⟪ α ⟫ (λ m → 𝒟ₒ (Lset (⟪ α ⟫↪ m)))))`, precisely the family the step function of the tower built.
<!--zh-->
这次归纳的步进函数接收 `α` 与归纳假设 `IH`，后者对 `α` 的每个成员 `β` 给出 `Lset β` 是层的证明。由于 `Lset` 不透明，目标 `isLayer (Lset α)` 无法直接与构造子匹配；必须先做传输。等式 `Lset-compute α` 把 `Lset α` 与步进的并等同，`subst isLayer (sym (Lset-compute α))` 沿该路径把目标移到正确方向，于是目标变为 `isLayer (⋃ (sett ⟪ α ⟫ (λ m → 𝒟ₒ (Lset (⟪ α ⟫↪ m)))))`，恰好是塔的步进函数所构造的那个族。
<!--ja-->
この帰納のステップ関数は `α` と、`α` の各要素 `β` に対して `Lset β` が層であることを与える帰納仮定 `IH` を受け取ります。`Lset` は不透明なので、目標 `isLayer (Lset α)` は構成子と直接照合できず、まず輸送されなければなりません。等式 `Lset-compute α` が `Lset α` をステップの和集合と同一視し、`subst isLayer (sym (Lset-compute α))` がそのパスに沿って目標を正しい向きへ移すので、目標は `isLayer (⋃ (sett ⟪ α ⟫ (λ m → 𝒟ₒ (Lset (⟪ α ⟫↪ m)))))` になります。これはまさに塔のステップ関数が作った族です。
<!--/-->

```agda
Lset-layer = ∈-induction step
  where
  step : (α : S) → (∀ β → β ∈ᵗ α → isLayer (Lset β)) → isLayer (Lset α)
  step α IH = subst isLayer (sym (Lset-compute α))
    (setUnion-layer ⟪ α ⟫ (λ m → 𝒟ₒ (Lset (⟪ α ⟫↪ m)))
```

<!--en-->
The remaining obligation fits the family constructor exactly: `setUnion-layer` wants the family and a layer proof for each of its values. For an index `m`, the value is `𝒟ₒ` at `Lset (⟪ α ⟫↪ m)`, and the induction hypothesis `IH` applied at that member, converted to type-valued membership by the local `mem` helper, gives `isLayer (Lset (⟪ α ⟫↪ m))`; `𝒟ₒ-layer` raises it one definable-power-set step. The opaque wrapper of `Lset` opens only through the declared equation, and the opaque wrapper of `𝒟ₒ` only inside `𝒟ₒ-layer`, so the whole induction runs at the level of the intended reading of the tower. Combining this with the previous section, every stage is a transitive layer.
<!--zh-->
剩余义务与族构造子严丝合缝：`setUnion-layer` 要求族以及每个取值的层证明。对索引 `m`，取值是 `𝒟ₒ` 作用于 `Lset (⟪ α ⟫↪ m)` 的结果，而归纳假设 `IH` 在该成员处应用、经局部辅助 `mem` 转换为取类型成员关系后，给出 `isLayer (Lset (⟪ α ⟫↪ m))`；`𝒟ₒ-layer` 再把它提升一个可定义幂集步。`Lset` 的不透明包装只经由被声明的等式打开，`𝒟ₒ` 的不透明包装只在 `𝒟ₒ-layer` 内部打开，故整个归纳都在塔的意读层面运行。结合上一节，每个阶段都是传递的层。
<!--ja-->
残りの義務は族の構成子に正確にはまります。`setUnion-layer` は族と、その各値に対する層の証明を要求します。添字 `m` に対する値は `Lset (⟪ α ⟫↪ m)` での `𝒟ₒ` であり、局所的な補助 `mem` によって型としての所属へ変換されたうえでその要素に適用した帰納仮定 `IH` が `isLayer (Lset (⟪ α ⟫↪ m))` を与え、`𝒟ₒ-layer` がそれを定義可能冪集合の一段へ引き上げます。`Lset` の不透明な包みは宣言された等式を通してのみ開かれ、`𝒟ₒ` の包みは `𝒟ₒ-layer` の内側でのみ開かれるので、帰納全体が塔の意図された読みのレベルで進みます。前節と合わせれば、すべての段階は推移的な層です。
<!--/-->

```agda
      (λ m → 𝒟ₒ-layer (IH (⟪ α ⟫↪ m) (mem m))))
    where
    mem : (m : ⟪ α ⟫) → ⟪ α ⟫↪ m ∈ᵗ α
    mem m = ∈∈ₛ {a = ⟪ α ⟫↪ m} {b = α} .snd (∈ₛ⟪ α ⟫↪ m)
```

<!--en-->
## Stages compared

Two more facts about the tower. The first names the operator's membership: `𝒟ₒ A` is the set of definable subsets of `A`, so belonging to it is, by construction, "merely, is some `defSet φ`", and exhibiting a formula together with an extensional equation is exactly what it takes to place a set inside the operator. The second unfolds the tower once and reads the union both ways: a stage is the union, over the members of its index, of `𝒟ₒ` of the earlier stages, so belonging to a stage is exactly belonging to `𝒟ₒ` of some earlier stage, stated as two independent directions. Monotonicity then follows as a corollary rather than a separate construction.
<!--zh-->
## 阶段之间的比较

关于塔还有两个事实。第一条给算子的隶属命名：`𝒟ₒ A` 就是 `A` 的可定义子集之集，故属于它按构造即「仅仅是某个 `defSet φ`」；要把一个集合放进算子里，拿出一条公式连同一个外延等式恰好就够。第二条把塔展开一次，从两个方向读那个并：一个阶段是其索引的成员对更早诸阶段的 `𝒟ₒ` 取的并，故属于一个阶段恰是属于某个更早阶段的 `𝒟ₒ`；这条刻画按两个独立方向给出。单调性随之作为推论得到，而非另行构造。
<!--ja-->
## 段階の比較

塔についてさらに二つの事実があります。第一は演算子の所属に名前を与えます。`𝒟ₒ A` は `A` の定義可能部分集合の集合なので、それに属することは構成上「ある `defSet φ` である、と単に」であり、論理式を一つ、外延的な等式とともに示せば、集合を演算子の中へ置くのにちょうど十分です。第二は塔を一度展開し、和集合を両方向から読みます。段階とは、添字の要素にわたる前段階の `𝒟ₒ` の和集合であり、したがって段階に属することは、ある前段階の `𝒟ₒ` に属することに他なりません。これは二つの独立な方向として述べられます。単調性はその後、別個の構成ではなく帰結として従います。
<!--/-->

<!--en-->
Inside a block that unfolds `𝒟ₒ`, membership in `𝒟ₒ A` reduces to the defining property of `Def`: a member of `𝒟ₒ A` is a subset of `A` picked out by a formula `φ` of arity one over the small members of `A`, with the actual set identified by a path `DefOf.defSet A φ ≡ x`. Since membership in the ambient hierarchy is truncated, the statement is prefixed by propositional truncation: the claim is merely that such a formula exists, not that one is chosen. The two lemmas below state this equivalence in each direction; here the introduction direction is declared, taking the truncated defining data to membership.
<!--zh-->
在展开 `𝒟ₒ` 的块内，属于 `𝒟ₒ A` 化归为 `Def` 的定义性质：`𝒟ₒ A` 的成员是由一条元数为 1 的公式、在 `A` 的小成员上选出的 `A` 的子集，而实际的集合由路径 `DefOf.defSet A φ ≡ x` 指认。由于环境层级中的成员关系是截断的，陈述冠以命题截断：所断言的只是这样的公式存在，而非选定了某条。下面两条引理把这条等价各按一个方向陈述；这里宣告的是进入方向，把截断的定义数据变成隶属。
<!--ja-->
`𝒟ₒ` を展開するブロックの内側では、`𝒟ₒ A` への所属は `Def` の定義的性質に帰着します。`𝒟ₒ A` の要素とは、`A` の小さな要素の上でのアリティ 1 の論理式 `φ` が選び出す `A` の部分集合であり、実際の集合はパス `DefOf.defSet A φ ≡ x` によって特定されます。周囲の階層での所属は命題的に切り詰められているため、主張には命題的切り詰めが冠されます。断言されるのはそのような論理式が単に存在することであって、一つが選ばれていることではありません。以下の二つの補題は、この同値をそれぞれ一方向ずつ述べるものです。ここでは導入の方向が宣言され、切り詰められた定義データを所属へ取ります。
<!--/-->

```agda
opaque
  unfolding 𝒟ₒ
  𝒟ₒ-intro : (A x : S)
           → ∥ Σ[ φ ∈ Formula ⟪ A ⟫ 1 ] (DefOf.defSet A φ ≡ x) ∥₁
           → ⟨ x ∈ˢ 𝒟ₒ A ⟩
```

<!--en-->
The proof body is the identity in both directions: once `𝒟ₒ` is unfolded, an element of the truncated defining data already is a member, and conversely the inversion lemma `𝒟ₒ-inv` returns a membership as the same truncated data. So the pair `𝒟ₒ-intro` and `𝒟ₒ-inv` is exactly the interface described just above: reading `DefOf.defSet` at a stage as a map from formulas, and recovering a member's defining formula by inversion. Both work at the level of mere existence, so no canonical formula is ever chosen; a member of `𝒟ₒ A` merely *is* some definable subset, and that is all these two directions say.
<!--zh-->
证明在两个方向上都是恒等：`𝒟ₒ` 一旦展开，截断定义数据的一个元素本来就是成员，反之，反演引理 `𝒟ₒ-inv` 把一个隶属作为同样的截断数据返回。于是 `𝒟ₒ-intro` 与 `𝒟ₒ-inv` 这一对恰是上文描述的接口：把一个阶段处的 `DefOf.defSet` 读作从公式出发的映射，用反演恢复成员的定义公式。二者都在「仅仅存在」的层面工作，因此从不选定任何典范公式；`𝒟ₒ A` 的成员仅仅是某个可定义子集，这两条方向所说的也仅止于此。
<!--ja-->
証明の本体は両方向とも恒等写像です。`𝒟ₒ` を展開すれば、命題的に切り詰められた定義データの要素はもともと要素であり、逆に反転の補題 `𝒟ₒ-inv` は所属を同じ切り詰められたデータとして返します。したがって `𝒟ₒ-intro` と `𝒟ₒ-inv` の対は、直前述べたインターフェイスそのものです。段階における `DefOf.defSet` を論理式からの写像として読み、反転によって要素の定義論理式を取り戻します。どちらも「単に存在する」のレベルで働くため、標準的な論理式が選ばれることはありません。`𝒟ₒ A` の要素は単に何らかの定義可能部分集合であるだけであり、この二方向が言うのはそれだけです。
<!--/-->

```agda
  𝒟ₒ-intro A x p = p

  𝒟ₒ-inv : (A x : S) → ⟨ x ∈ˢ 𝒟ₒ A ⟩
         → ∥ Σ[ φ ∈ Formula ⟪ A ⟫ 1 ] (DefOf.defSet A φ ≡ x) ∥₁
  𝒟ₒ-inv A x p = p
```

<!--en-->
Two further facts make the tower usable in later arguments. The first names the operator's membership: `𝒟ₒ A` is the set of definable subsets of `A`, so belonging to it is, by construction, "merely, is some `defSet φ`", and exhibiting a formula together with an extensional equation is exactly what it takes to place a set inside the operator. The second unfolds the tower once and reads the union both ways: a stage is the union, over the members of its index, of `𝒟ₒ` of the earlier stages, so belonging to a stage is exactly belonging to `𝒟ₒ` of some earlier stage, stated as two independent directions since that is how proofs consume it. Monotonicity then follows as a corollary rather than a separate construction.
<!--zh-->
关于塔还有两个事实，承载着后续诸章的每一个闭包论证，而只要在对的地方开封，二者都很廉价。第一条给算子的隶属命名：`𝒟ₒ A` 就是 `A` 的可定义子集之集，故属于它按构造即「仅仅是某个 `defSet φ`」；要把一个集合放进算子里，拿出一条公式连同一个外延等式恰好就够。第二条把塔展开一次，从两个方向读那个并：一个阶段是其索引的成员对更早诸阶段的 `𝒟ₒ` 取的并，故属于一个阶段恰是属于某个更早阶段的 `𝒟ₒ`；这条刻画按两个独立方向给出，因为证明正是这样使用它。单调性随之作为推论得到，而非另行构造。
<!--ja-->
塔を後の議論で使うために、さらに二つの事実を示します。第一は演算子の所属に名前を与えます。`𝒟ₒ A` は `A` の定義可能部分集合の集合なので、それに属することは構成上「ある `defSet φ` である、と単に」であり、論理式を一つ、外延的な等式とともに示せば、集合を演算子の中へ置くのにちょうど十分です。第二は塔を一度展開し、和集合を両方向から読みます。段階とは、添字の要素にわたる前段階の `𝒟ₒ` の和集合であり、したがって段階に属することは、ある前段階の `𝒟ₒ` に属することに他なりません。これは、証明がそう使うために、二つの独立な方向として述べられます。単調性はその後、別個の構成ではなく帰結として従います。
<!--/-->

<!--en-->
The first lemma is the inclusion of a stage in its own definable power set: since `Lset-layer β` says the stage `Lset β` is a layer and `layer-trans` makes it transitive, the refinement bound `A⊆Def` of the definability chapter applies verbatim, giving `x ∈ Lset β ⟹ x ∈ 𝒟ₒ (Lset β)`. Its dual `𝒟ₒ∋⊆` restates that the operator only refines: every member of `𝒟ₒ A` is a subset of `A`, so a member of a member is still in `A`. Finally `stageFam` names the family underlying the tower's step: for an index `m` in the small presentation of `α`, the corresponding stage is `𝒟ₒ` at `Lset` of the member named by `m`.
<!--zh-->
第一条引理是阶段包含于其自身的可定义幂集：由于 `Lset-layer β` 说阶段 `Lset β` 是层，而 `layer-trans` 使其传递，可定义性章的精化界 `A⊆Def` 逐字适用，给出 `x ∈ Lset β ⟹ x ∈ 𝒟ₒ (Lset β)`。其对偶 `𝒟ₒ∋⊆` 重申算子只精化不扩缩：`𝒟ₒ A` 的每个成员都是 `A` 的子集，故成员的成员仍在 `A` 中。最后 `stageFam` 为塔的步进下的族命名：对 `α` 的小表示中的索引 `m`，对应的阶段是 `𝒟ₒ` 作用于 `m` 所指名成员处的 `Lset`。
<!--ja-->
最初の補題は、段階がその固有の定義可能冪集合に含まれるという包含です。`Lset-layer β` が段階 `Lset β` が層であることを言い、`layer-trans` がそれを推移的にするので、定義可能性の章の細分の評価 `A⊆Def` がそのまま適用され、`x ∈ Lset β ⟹ x ∈ 𝒟ₒ (Lset β)` が得られます。双対の `𝒟ₒ∋⊆` は、演算子が細分するだけで要素を失わないことを再確認します。`𝒟ₒ A` の各要素は `A` の部分集合なので、その要素の要素も依然 `A` にあります。最後に `stageFam` が、塔のステップの下にある族に名前を与えます。`α` の小さな表現の添字 `m` に対して、対応する段階は `m` の指す要素での `Lset` に `𝒟ₒ` を施したものです。
<!--/-->

```agda
  Lset⊆𝒟ₒ : (β x : S) → ⟨ x ∈ˢ Lset β ⟩ → ⟨ x ∈ˢ 𝒟ₒ (Lset β) ⟩
  Lset⊆𝒟ₒ β x = DefOf.Refine.A⊆Def (Lset β) (layer-trans (Lset-layer β)) x

  𝒟ₒ∋⊆ : (A x : S) → ⟨ x ∈ˢ 𝒟ₒ A ⟩ → (y : S) → ⟨ y ∈ˢ x ⟩ → ⟨ y ∈ˢ A ⟩
  𝒟ₒ∋⊆ A = DefOf.Def∋⊆A A

stageFam : (α : S) → ⟪ α ⟫ → S
```

<!--en-->
Now the characterization of stage membership from above. `Lset-in` says: if `δ` is a member of `α` and `x` lies in `𝒟ₒ (Lset δ)`, then `x` already lies in `Lset α`. The proof rewrites `Lset α` once by its computation rule, so the goal becomes membership in the union `⋃ (sett ⟪ α ⟫ (stageFam α))`, and then invokes `union-family-in`, the model lemma which takes an index `i` and a member `x` of `f i` and returns a member of the indexed union. The index supplied is `fib .fst`, an element of `⟪ α ⟫` naming the member `δ`.
<!--zh-->
现在从上方刻画阶段隶属。`Lset-in` 说：若 `δ` 是 `α` 的成员且 `x` 落在 `𝒟ₒ (Lset δ)` 中，则 `x` 已经落在 `Lset α` 中。证明先用计算规则改写 `Lset α` 一次，使目标变为并 `⋃ (sett ⟪ α ⟫ (stageFam α))` 的隶属，然后调用 `union-family-in`，即模型章的引理：它接收索引 `i` 与 `f i` 的成员 `x`，返回索引并的成员。所供索引是 `fib .fst`，即 `⟪ α ⟫` 中指名成员 `δ` 的元素。
<!--ja-->
次に、段階への所属を上から特徴づけます。`Lset-in` の主張は、`δ` が `α` の要素であり `x` が `𝒟ₒ (Lset δ)` に属するなら、`x` はすでに `Lset α` に属する、ということです。証明はまず計算規則で `Lset α` を一度書き換え、目標を和集合 `⋃ (sett ⟪ α ⟫ (stageFam α))` への所属に変えます。そして `union-family-in` を呼びます。これはモデル章の補題で、添字 `i` と `f i` の要素 `x` を受け取り、添字付きの和の要素を返します。供給される添字は `fib .fst`、すなわち `⟪ α ⟫` のうち要素 `δ` を名指す元です。
<!--/-->

```agda
stageFam α m = 𝒟ₒ (Lset (⟪ α ⟫↪ m))

Lset-in : (α δ x : S) → ⟨ δ ∈ˢ α ⟩ → ⟨ x ∈ˢ 𝒟ₒ (Lset δ) ⟩ → ⟨ x ∈ˢ Lset α ⟩
Lset-in α δ x δ∈α x∈𝒟ₒδ =
  subst (λ w → ⟨ x ∈ˢ w ⟩) (sym (Lset-compute α))
    (union-family-in ⟪ α ⟫ (stageFam α) (fib .fst) x
```

<!--en-->
The name `fib` abbreviates a fiber computation: the structural membership `δ∈α` is truncated, and `∈-asFiber` converts it into a fiber of the embedding `⟪ α ⟫↪`, that is, a pair of an index `i` with `⟪ α ⟫↪ i ≡ δ`. Inside the proof this identification is transported along: `x∈𝒟ₒδ` speaks of `Lset δ`, but `union-family-in` needs a member of `stageFam α (fib .fst)`, which equals `𝒟ₒ (Lset (⟪ α ⟫↪ (fib .fst)))`, so `subst` moves the hypothesis across the path `sym (fib .snd)`. The truncated origin of `δ∈α` never matters here, because a fiber representation was actually constructed from it by `∈-asFiber`.
<!--zh-->
名字 `fib` 缩写一次纤维计算：结构成员 `δ∈α` 是截断的，`∈-asFiber` 把它转换为嵌入 `⟪ α ⟫↪` 的纤维，即索引 `i` 与路径 `⟪ α ⟫↪ i ≡ δ` 组成的对。证明内部沿这条等同做传输：`x∈𝒟ₒδ` 谈的是 `Lset δ`，而 `union-family-in` 需要的是 `stageFam α (fib .fst)` 的成员，后者等于 `𝒟ₒ (Lset (⟪ α ⟫↪ (fib .fst)))`，故 `subst` 沿路径 `sym (fib .snd)` 把假设移过去。`δ∈α` 的截断来源在此无关紧要，因为 `∈-asFiber` 确实从它构造出了纤维表示。
<!--ja-->
名前 `fib` はファイバーの計算の略記です。構造的な所属 `δ∈α` は命題的に切り詰められていますが、`∈-asFiber` がそれを埋め込み `⟪ α ⟫↪` のファイバーへ変換します。つまり添字 `i` と `⟪ α ⟫↪ i ≡ δ` というパスの対です。証明の内側ではこの同一視に沿って輸送が行われます。`x∈𝒟ₒδ` は `Lset δ` について述べていますが、`union-family-in` が必要とするのは `stageFam α (fib .fst)` の要素であり、これは `𝒟ₒ (Lset (⟪ α ⟫↪ (fib .fst)))` に等しいので、`subst` がパス `sym (fib .snd)` を横断して仮定を移します。`δ∈α` が切り詰められたものであることはここでは問題になりません。`∈-asFiber` が実際にそこからファイバー表現を構成したからです。
<!--/-->

```agda
      (subst (λ δ → ⟨ x ∈ˢ 𝒟ₒ (Lset δ) ⟩) (sym (fib .snd)) x∈𝒟ₒδ))
  where
  fib = ∈-asFiber {a = δ} {b = α} δ∈α

Lset-out : (α x : S) → ⟨ x ∈ˢ Lset α ⟩
         → ∥ Σ[ δ ∈ S ] (⟨ δ ∈ˢ α ⟩ × ⟨ x ∈ˢ 𝒟ₒ (Lset δ) ⟩) ∥₁
```

<!--en-->
The downward direction `Lset-out` cannot avoid truncation, and states it honestly: a member `x` of `Lset α` merely comes from some predecessor, that is, merely there is a `δ` with `δ ∈ α` and `x ∈ 𝒟ₒ (Lset δ)`. The proof again rewrites `Lset α` by the computation rule, applies `union-family-out` to get merely an index `m` of `⟪ α ⟫` with `x` in the family value at `m`, and maps inside the truncation: the pair `(m , hx)` becomes the stage `⟪ α ⟫↪ m`, its structural membership in `α` via `∈∈ₛ`, and `hx`. The result is a truncated witness precisely because the union axiom names no canonical predecessor; the construction of one inside the branch is local data, not a chosen function.
<!--zh-->
向下的方向 `Lset-out` 无法避开截断，并如实陈述：`Lset α` 的成员 `x` 仅仅来自某个前驱，即仅仅存在 `δ` 满足 `δ ∈ α` 与 `x ∈ 𝒟ₒ (Lset δ)`。证明同样先用计算规则改写 `Lset α`，对 `union-family-out` 的应用得到「仅仅」有 `⟪ α ⟫` 的索引 `m` 使 `x` 落在该索引处的族值中，再在截断内部做映射：对 `(m , hx)` 变为阶段 `⟪ α ⟫↪ m`、经 `∈∈ₛ` 的它在 `α` 中的结构隶属、以及 `hx`。结果是截断的见证，正是因为并公理不指名任何典范前驱；分支内构造出的那一个只是局部数据，而非选定的函数。
<!--ja-->
下向きの方向 `Lset-out` は命題的切り詰めを避けられず、それを率直に述べます。`Lset α` の要素 `x` は、ある前駆から単に来ています。すなわち `δ ∈ α` かつ `x ∈ 𝒟ₒ (Lset δ)` なる `δ` が単に存在するということです。証明はここでも計算規則で `Lset α` を書き換え、`union-family-out` を適用して、`⟪ α ⟫` の添字 `m` でその位置の族の値に `x` が属することが単に成り立つことを得ます。そして切り詰めの内部で写像を行います。対 `(m , hx)` は、段階 `⟪ α ⟫↪ m`、`∈∈ₛ` による `α` への構造的な所属、そして `hx` になります。結果が切り詰められた証人になるのは、和集合の公理が標準的な前駆を名指さないからにほかなりません。分岐の内側で構成した一つは局所的なデータであって、選ばれた関数ではありません。
<!--/-->

```agda
Lset-out α x x∈Lα = PT.map
  (λ { (m , hx) → ⟪ α ⟫↪ m
    , (∈∈ₛ {a = ⟪ α ⟫↪ m} {b = α} .snd (∈ₛ⟪ α ⟫↪ m) , hx) })
  (union-family-out ⟪ α ⟫ (stageFam α) x
    (subst (λ w → ⟨ x ∈ˢ w ⟩) (Lset-compute α) x∈Lα))
```

<!--en-->
Monotonicity is now a two-line corollary of the characterization rather than a separate construction. If `β ∈ α` and `x ∈ Lset β`, then `Lset⊆𝒟ₒ` first lifts `x` into `𝒟ₒ (Lset β)`, using that stages are transitive, and `Lset-in` with the inclusion `β ∈ α` carries it into `Lset α`. Note the strict form: what monotonicity requires is that `β` is a member of `α`, not merely a subset, matching how the tower grows by taking the union over members.
<!--zh-->
单调性由此成为刻画的不到三行的推论，而非另行构造。若 `β ∈ α` 且 `x ∈ Lset β`，先用 `Lset⊆𝒟ₒ` 把 `x` 提升到 `𝒟ₒ (Lset β)`，用到阶段传递；再以包含 `β ∈ α` 应用 `Lset-in`，把 `x` 送入 `Lset α`。注意其严格形式：单调性要求 `β` 是 `α` 的成员，而不仅是子集，这与塔沿成员取并的生长方式一致。
<!--ja-->
単調性はこれで、別個の構成ではなく特徴づけの短い帰結になります。`β ∈ α` かつ `x ∈ Lset β` なら、まず `Lset⊆𝒟ₒ` が `x` を `𝒟ₒ (Lset β)` へ引き上げます。段階が推移的であることを使います。次に包含 `β ∈ α` とともに `Lset-in` を適用して、`x` を `Lset α` へ運びます。厳密な形に注意してください。単調性が要求するのは `β` が `α` の部分集合であることではなく要素であることであり、これは塔が要素にわたる和集合を取って伸びる仕方と一致します。
<!--/-->

```agda

Lset-mono : {α β : S} → ⟨ β ∈ˢ α ⟩ → {x : S} → ⟨ x ∈ˢ Lset β ⟩ → ⟨ x ∈ˢ Lset α ⟩
Lset-mono {α} {β} β∈α {x} x∈Lβ = Lset-in α β x β∈α (Lset⊆𝒟ₒ β x x∈Lβ)
```

<!--en-->
## The class L, and its structure

A set is **constructible** when some ordinal stage of the tower contains it. The ordinal bound is part of the definition on purpose: the later theory extracts stage ordinals, and this shape yields them by construction. Note that ordinality is imposed here, at the point of definition; the tower `Lset` itself accepts arbitrary sets as indices. `L` is a transitive class: stages are transitive, and the witnessing ordinal does not move.
<!--zh-->
## 类 L，及其结构

一个集合是**可构造的**，指塔的某个序数阶段包含它。序数界故意写进定义：后文的理论要提取阶段序数，这个形状按构造直接给出。注意序数性正是在定义之处施加的；塔 `Lset` 本身接受任意集合作为索引。`L` 是传递类：阶段传递，见证序数不动。
<!--ja-->
## クラス L とその構造

集合が**構成可能**であるとは、塔のある順序数段階がそれを含むことです。順序数の上限を定義に意図的に書き込むのは、後の理論が段階の順序数を取り出す必要があるためであり、この形はそれを構成によって直接与えます。順序数性が課されるのはまさにこの定義の箇所であることに注意してください。塔 `Lset` そのものは任意の集合を添字として受け付けます。`L` は推移的クラスです。段階は推移的であり、証人となる順序数は動きません。
<!--/-->

<!--en-->
The class is a truth value, not a subtype: `isL x` is defined in the chosen truth algebra as the indexed disjunction `⋁` over all sets `α` of the conjunction of `IsOrd α` with `x ∈ˢ Lset α`. So an element of `isL x` is, by the algebra's meaning of the quantifier, merely a pair of an ordinal `α` and a membership of `x` in stage `α`; no canonical stage is attached to a constructible set. The quantifier ranges over the whole carrier, so a witness is available only in this merely-exists form; treating the class as a proposition-valued predicate is what allows it to be restricted into a structure shortly.
<!--zh-->
这个类是一个真值，而非子类型：`isL x` 在所选真值代数中定义为对全体集合 `α` 的索引析取 `⋁`，其各项是 `IsOrd α` 与 `x ∈ˢ Lset α` 的合取。故按该代数量词的含义，`isL x` 的一个元素仅仅是一个对：序数 `α` 与 `x` 属于阶段 `α` 的证据；可构造集并不附带一个典范阶段。量词遍历整个载体，故见证只以「仅仅存在」的形式可得；把类当作命题值谓词，正是稍后能把它限制成结构的原因。
<!--ja-->
このクラスは部分型ではなく真理値です。`isL x` は、選ばれた真理値代数において、すべての集合 `α` にわたる索引付きの選言 `⋁` として定義され、その各項は `IsOrd α` と `x ∈ˢ Lset α` の連言です。したがって代数の量詞の意味により、`isL x` の要素は単に、順序数 `α` と段階 `α` への `x` の所属の対です。構成可能集合に標準的な段階が付属することはありません。量詞は台全体にわたるため、証人はこの「単に存在する」の形でしか得られません。クラスを命題値の述語として扱うことが、まもなくそれを構造へ制限できる理由です。
<!--/-->

```agda
isL : S → Ω
isL x = ⋁ S (λ α → ((IsOrd α , isPropIsOrd α) ⊓ (x ∈ˢ Lset α)))

isL-trans : Transitive 𝒮ᵥ isL
isL-trans {x} {y} y∈x x∈L = PT.rec (snd (isL y))
  (λ { (α , (ordα , x∈Lα)) →
```

<!--en-->
Transitivity of the class is now immediate from the closure of the stages. Given `y ∈ x` and an element of `isL x`, eliminate the truncation into the proposition `isL y`: the witness is a pair `(α , ordα , x∈Lα)`, and since the stage `Lset α` is a transitive set by `layer-trans (Lset-layer α)`, the two hypotheses `y∈x` and `x∈Lα` yield `y ∈ Lset α`. The same ordinal `α` re-certifies the conclusion, so the class is closed under members of members. The conclusion is re-truncated with `∣ _ ∣₁` because the target `isL y` is itself a truncated existential, not because any choice had to be undone.
<!--zh-->
类的传递性现在由阶段的闭包立即可得。给定 `y ∈ x` 与 `isL x` 的一个元素，向命题 `isL y` 消去截断：见证是对 `(α , ordα , x∈Lα)`，而阶段 `Lset α` 经 `layer-trans (Lset-layer α)` 是传递集，故两条假设 `y∈x` 与 `x∈Lα` 给出 `y ∈ Lset α`。同一个序数 `α` 重新为结论作证，故类对成员的成员封闭。结论再用 `∣ _ ∣₁` 重新截断，是因为目标 `isL y` 本身就是截断的存在式，而不是因为任何选择需要撤销。
<!--ja-->
クラスの推移性は、段階の閉性からただちに従います。`y ∈ x` と `isL x` の要素が与えられ、命題的に切り詰められたものを命題 `isL y` へ消去します。証人は対 `(α , ordα , x∈Lα)` であり、段階 `Lset α` は `layer-trans (Lset-layer α)` により推移的集合なので、二つの仮定 `y∈x` と `x∈Lα` から `y ∈ Lset α` が得られます。同じ順序数 `α` が結論を改めて証明するので、クラスは要素の要素について閉じています。結論を `∣ _ ∣₁` で改めて切り詰めるのは、目標 `isL y` それ自体が切り詰められた存在式だからであって、どの選択を取り消す必要があったからではありません。
<!--/-->

```agda
    ∣ α , (ordα , layer-trans (Lset-layer α) y∈x x∈Lα) ∣₁ })
  x∈L
```

<!--en-->
Sitting in an ordinal stage *is* the definition, so the bridge in that direction is the constructor itself. Giving the bridge a name simply makes it convenient to cite.
<!--zh-->
落在某个序数阶段中**就是**定义，故这个方向的桥就是构造子本身。给它一个名字，只是便于日后引用。
<!--ja-->
ある順序数段階に属すること**こそ**定義そのものなので、この方向の橋は構成子そのものです。この橋に名前を与えるのは、引用しやすくするためです。
<!--/-->

<!--en-->
Given an ordinal witness `oα` for the stage `α` and a membership `x∈Lα`, the proof packages the three components, the ordinal, its ordinality, and the membership, into a single propositionally truncated pair. Nothing is computed; the content of the lemma is that the existential in the definition of `isL x` is witnessed by exactly the data at hand. Note the direction of trust: the lemma takes the ordinality of `α` as a hypothesis, since `Lset` as defined accepts arbitrary sets as indices and it is the caller who must know that the chosen index really is an ordinal.
<!--zh-->
给定阶段 `α` 的序数见证 `oα` 与隶属 `x∈Lα`，证明把三个分量，序数、其序数性、隶属，打包成单个经命题截断的对。没有任何计算；该引理的内容在于：`isL x` 定义中的存在式恰好由手头的数据见证。注意信任的方向：引理把 `α` 的序数性作为假设接收，因为按定义 `Lset` 接受任意集合作为索引，所选索引确实是序数这一点必须由调用方知道。
<!--ja-->
段階 `α` の順序数の証人 `oα` と所属 `x∈Lα` が与えられれば、証明は三つの成分、順序数、その順序数性、所属、を一つの命題的に切り詰められた対へまとめます。計算されるものは何もありません。この補題の内容は、`isL x` の定義にある存在式が、まさに手元のデータによって証明されるということです。信頼の向きに注意してください。この補題は `α` の順序数性を仮定として受け取ります。定義上の `Lset` は任意の集合を添字として受け付けるため、選んだ添字が本当に順序数であることは呼び出し側が知っていなければならないからです。
<!--/-->

```agda
Lset→isL : (α : S) → IsOrd α → (x : S) → ⟨ x ∈ˢ Lset α ⟩ → ⟨ isL x ⟩
Lset→isL α oα x x∈Lα = ∣ α , (oα , x∈Lα) ∣₁
```

<!--en-->
The final construction views the constructible class as a structure. Restricting `𝒮ᵥ` to the proposition-valued class `isL` gives `𝒮ʟ`: its elements are sets equipped with constructibility proofs, and equality and membership are inherited through the restriction. This supplies the structure in which later formulas about L are interpreted; proving that it is a model of ZFC requires the separate axiom arguments that follow.
<!--zh-->
最后把可构造类看成一个结构。把 `𝒮ᵥ` 限制到命题值类 `isL` 上得到 `𝒮ʟ`：其元素是配有可构造性证明的集合，相等与隶属则从限制结构继承。这给出了后文解释关于 L 的公式所用的结构；要证明它是 ZFC 的模型，还需要随后各章分别给出的公理论证。
<!--ja-->
最後に、構成可能クラスを一つの構造として捉えます。`𝒮ᵥ` を命題値のクラス `isL` に制限して得られるのが `𝒮ʟ` です。その元は構成可能性の証明を伴う集合であり、等式と所属は制限を通して受け継がれます。これが後に L についての論理式を解釈する構造になります。これを ZFC のモデルと示すには、続く各章の公理ごとの議論が別に必要です。
<!--/-->

<!--en-->
One line suffices. The restriction `_↾_` takes the ambient structure and the class `isL`, and forms the structure whose elements are pairs of a set with a proof that it satisfies `isL`; equality and membership are read along the first projection, so they agree with the ambient ones. Since `isL` is a truth value in the same algebra and the class was proved transitive, the restricted structure is well-defined in the same framework. What remains open, and is the subject of the following chapters, is whether this structure satisfies the ZF and ZFC axioms; the restriction itself asserts nothing about that.
<!--zh-->
一行足矣。限制 `_↾_` 接收环境结构与类 `isL`，构成这样的结构：其元素是集合配上其满足 `isL` 的证明的对；等词与隶属沿第一投影读取，故与环境一致。由于 `isL` 是同一代数中的真值、且该类已被证明传递，限制结构在同一框架中良定义。尚待解决、也是后续各章主题的，是这个结构是否满足 ZF 与 ZFC 公理；限制本身对此不作任何断言。
<!--ja-->
一行で十分です。制限 `_↾_` は周囲の構造とクラス `isL` を受け取り、`isL` を満たす証拠と対になった集合を要素とする構造を作ります。等号と所属は第一射影に沿って読まれるため、周囲のものと一致します。`isL` は同じ代数における真理値であり、クラスは推移的であると証明済みなので、制限された構造は同じ枠組みのなかで問題なく定義されます。まだ開いている問題、すなわち後の章の主題は、この構造が ZF と ZFC の公理を満たすかどうかです。制限そのものはそれについて何も主張しません。
<!--/-->

```agda
𝒮ʟ : ZFStructure (hPropAlgebra (ℓ-suc ℓ))
𝒮ʟ = 𝒮ᵥ ↾ isL
```

<!--en-->
## Recap

The tower `Lset`{.Agda} is defined by membership recursion, and `isLayer`{.Agda} records closure under the definability operation and the three union constructions. Structural recursion with the corresponding lemmas proves `layer-trans`{.Agda}. A set is in `isL`{.Agda} when it merely belongs to `Lset α` for some ordinal `α`; this class is transitive, and restricting the ambient structure to it gives `𝒮ʟ`{.Agda}. The remaining task is to prove, axiom by axiom, that this structure satisfies ZFC.
<!--zh-->
## 小结

塔 `Lset`{.Agda} 由成员递归定义，`isLayer`{.Agda} 记录它对可定义性运算和三种并集构造的封闭性。对层见证作结构递归，并使用相应引理，便得到 `layer-trans`{.Agda}。一个集合属于 `isL`{.Agda}，是指它仅仅地属于某个序数 `α` 的阶段 `Lset α`；这个类是传递的，把环境结构限制到该类上便得到 `𝒮ʟ`{.Agda}。余下任务是逐条公理证明这个结构满足 ZFC。
<!--ja-->
## まとめ

塔 `Lset`{.Agda} は所属再帰で定義され、`isLayer`{.Agda} は定義可能性の演算と三種類の和集合構成に関する閉包性を記録します。層の証拠に対する構造的再帰と対応する補題から `layer-trans`{.Agda} が得られます。集合が `isL`{.Agda} に属するとは、ある順序数 `α` に対して `Lset α` に単に属することです。このクラスは推移的であり、周囲の構造をそこへ制限すると `𝒮ʟ`{.Agda} が得られます。残る課題は、この構造が ZFC を満たすことを公理ごとに証明することです。
<!--/-->
