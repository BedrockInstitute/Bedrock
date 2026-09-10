<!--en-->
# Formulas for singletons and pairs

The goal of this chapter is to let the object language recognize that one assigned set is the Kuratowski ordered pair of two others, and, along the way, to recognize singletons and unordered pairs, of which the Kuratowski pair is built. A first-order formula can speak only of membership and equality, so recognition must be extensional: a set is recognized as `pr U W` by saying, through membership alone, exactly which members it has. Three bounded formulas are constructed: `sglAt`{.Agda} says "this set is the singleton of that one", `pairAt`{.Agda} says "this is the unordered pair of those two", and `prAt`{.Agda} combines these into "this is the Kuratowski pair of those two".

The adequacy theorem at the end is an exact identification. For any environment, satisfaction of `prAt q u v` is a path of truth values to the proposition that the value at position `q` equals `pr` applied to the values at `u` and `v`. Nothing weaker, such as a one-way implication, is claimed.

Because the quantifiers of each formula are bounded by an assigned set and its free-variable positions are de Bruijn indices given as arguments, the same formula works at any depth of nesting. Every clause is an atom or a bounded quantifier, so each reader is Δ₀ in the Lévy hierarchy.
<!--zh-->
# 单点集与有序对的公式

本章的目标是让对象语言识别出某个被指派的集合恰是另外两个集合的 Kuratowski 有序对，顺带识别出 Kuratowski 对由之构成的单点集与无序对。一阶公式只能谈论隶属与相等，故识别必须是外延的：识别 `pr U W`，就是仅凭隶属说出它恰有哪些成员。本章构造三条有界公式：`sglAt`{.Agda} 说「这个集合是那个集合的单点集」，`pairAt`{.Agda} 说「这是那两个集合的无序对」，`prAt`{.Agda} 把这些组合成「这是那两个集合的 Kuratowski 对」。

结尾的充分性定理是一条精确的等同。对任意赋值，`prAt q u v` 的满足关系是一条真值路径，通向「`q` 处的值等于 `pr` 作用在 `u`、`v` 处之值上的结果」这一命题。这里不断言任何更弱的陈述，例如单向蕴含。

由于每条公式的量词都以某个被指派的集合为界，其自由变元位置取作参数给出的 de Bruijn 下标，同一条公式在任何嵌套深度都能使用。每条子句都是原子或有界量词，故每条读式都是 Lévy 层级中的 Δ₀。
<!--ja-->
# 単集合と対を表す論理式

この章の目標は、対象言語に、割り当てられたある集合が他の二つの集合の Kuratowski 順序対であると認識させること、そして道すがら、Kuratowski 対を構成する単集合と非順序対も認識させることです。一階の論理式が語れるのは所属と等号だけなので、認識は外延的でなければなりません。`pr U W` を認識するとは、所属だけを通して、どの要素をちょうど持つのかを言うことです。本章では有界な論理式を三つ構成します。`sglAt`{.Agda} は「この集合はあれの単集合である」、`pairAt`{.Agda} は「これはあの二つの非順序対である」、`prAt`{.Agda} はこれらを組み合わせて「これはあの二つの Kuratowski 対である」と読み取る式です。

最後の妥当性定理は正確な同一視です。任意の割当てに対して、`prAt q u v` の充足は真理値のパスであり、その先にあるのは「`q` の位置の値が、`u` と `v` の位置の値に `pr` を施した結果と等しい」という命題です。一方向の含意のようなより弱い主張はここでは行いません。

各論理式の量化子は指定された集合で限られ、自由変数の位置は引数として与えられる de Bruijn 添字なので、同じ式を任意の入れ子の深さで使えます。すべての節が原子か有界量化子であるため、各読解式は Lévy 階層の Δ₀ です。
<!--/-->

<!--en-->
The external target has a specific membership shape: `pr U W = ⁅ ⁅ U ⁆s , ⁅ U , W ⁆ ⁆`. Its outer set is an unordered pair whose first member is the singleton of `U` and whose second member is the unordered pair of `U` and `W`. Recognizing the ordered pair therefore reduces to three conditions: the two required members occur, and every member is one of them. The last condition is propositionally truncated, matching the classification of unordered-pair membership; it records the alternative without choosing a side.
<!--zh-->
外部目标有明确的成员形状：`pr U W = ⁅ ⁅ U ⁆s , ⁅ U , W ⁆ ⁆`。其外层集合是一个无序对，第一个成员是 `U` 的单点集，第二个成员是 `U` 与 `W` 的无序对。因此，识别这个有序对可归结为三项条件：两个指定成员都出现，并且每个成员都是二者之一。最后一项采用命题截断，正好对应无序对隶属的分类；它记录这项选择，却不指定是哪一侧。
<!--ja-->
外側の目標は明確な所属の形を持ちます。`pr U W = ⁅ ⁅ U ⁆s , ⁅ U , W ⁆ ⁆` です。外側の集合は非順序対で、第 1 の要素は `U` の単集合、第 2 の要素は `U` と `W` の非順序対です。したがって順序対の認識は、指定された二要素がともに存在し、すべての要素がそのどちらかであるという三条件に帰着します。最後の条件は命題的に切り詰められており、非順序対の所属の分類と一致します。これは選択肢の存在を記録しますが、どちら側かは選びません。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth

module L.Coding.PairFormulas {ℓ : Level} where

open import FOL.Syntax
```

<!--en-->
The tool for expressing the descriptions is the bounded fragment of the first-order language. Its atoms `_∈̇_` and `_≐_` and its connectives `_∧̇_` and `_∨̇_` state membership and equality between the sets assigned to positions; its quantifiers `∀̇∈` and `∃̇∈` are always bounded by an assigned set. Formulas built from these alone form the class `Δ₀` of the Lévy hierarchy, checked syntactically by `checkΔ₀`.

The target of recognition is the Kuratowski coding `pr`, defined by `pr U W = ⁅ ⁅ U ⁆s , ⁅ U , W ⁆ ⁆`: an ordered pair is presented as an unordered pair of two sets, the singleton of `U` and the pair of `U` and `W`. The recognition problem thus reduces to saying, with bounded formulas, that a set has a member which is the singleton of `U`, a member which is the unordered pair of `U` and `W`, and no other members. Singleton and unordered-pair membership have their own classifications, and extensionality will convert complete membership conditions into equalities of sets.
<!--zh-->
表达这些描述的工具是一阶语言的有界片段。其原子 `_∈̇_` 与 `_≐_` 及联结词 `_∧̇_` 与 `_∨̇_` 陈述各位置上被指派集合之间的隶属与相等；其量词 `∀̇∈` 与 `∃̇∈` 总以某个被指派的集合为界。仅由这些构造的公式组成 Lévy 层级中的有界类 `Δ₀`，并由 `checkΔ₀` 作语法检查。

识别的对象是 Kuratowski 编码 `pr`，定义为 `pr U W = ⁅ ⁅ U ⁆s , ⁅ U , W ⁆ ⁆`：有序对被呈现为两个集合的无序对，即 `U` 的单点集与 `U` 和 `W` 的对。于是识别问题归结为：用有界公式说一个集合有一个成员是 `U` 的单点集、有一个成员是 `U` 与 `W` 的无序对、且没有别的成员。单点集与无序对的隶属各有自己的分类，而外延性将把完备的隶属条件转换为集合间的等式。
<!--ja-->
これらの記述を表す道具は、一階言語の有界フラグメントです。原子 `_∈̇_` と `_≐_`、結合子 `_∧̇_` と `_∨̇_` は、各位置に割り当てられた集合の間の所属と等号を述べます。量化子 `∀̇∈` と `∃̇∈` は常に割り当てられた集合で限られます。これらだけから作られる論理式は Lévy 階層の有界クラス `Δ₀` をなし、`checkΔ₀` が構文的に検査します。

認識の対象は Kuratowski 符号化 `pr` で、`pr U W = ⁅ ⁅ U ⁆s , ⁅ U , W ⁆ ⁆` と定義されます。順序対は、`U` の単集合と `U` と `W` の対という二つの集合の非順序対として提示されるのです。したがって認識の問題は、有界論理式で、ある集合が `U` の単集合である要素をひとつ、`U` と `W` の非順序対である要素をひとつ持ち、それ以外の要素を持たない、と言うことに帰着します。単集合と非順序対への所属にはそれぞれ分類があり、外延性が完全な所属の条件を集合の間の等号に変換します。
<!--/-->

```agda
  using ( var; Formula; _∈̇_; _≐_; _∧̇_; _∨̇_; ∀̇∈; ∃̇∈ )
open import FOL.LevyHierarchy using ( Δ₀; checkΔ₀ )
import FOL.Semantics
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ; extensionalV )
open import V.Coding {ℓ} using ( pr )
```

<!--en-->
Singleton and unordered-pair membership are supplied in two equivalent forms: hierarchy membership `⟨ y ∈ b ⟩` and the small classified membership used by their constructions. The equivalence `∈∈ₛ` passes between them. For a singleton, the classification yields the path `y ≡ u`; for an unordered pair, it yields the truncated alternative `∥ (y ≡ u) ⊎ (y ≡ v) ∥₁`. Once these membership descriptions are proved in both directions, `⇔toPath` turns each equivalence of membership propositions into the path required by extensionality.
<!--zh-->
单点集与无序对的隶属各有两种等价形式：层级隶属 `⟨ y ∈ b ⟩`，以及相应构造所使用的小隶属分类；`∈∈ₛ` 在两者之间转换。对单点集，分类给出路径 `y ≡ u`；对无序对，分类给出截断的两种可能 `∥ (y ≡ u) ⊎ (y ≡ v) ∥₁`。分别证明这些隶属描述的两个方向后，`⇔toPath` 把每一对隶属命题的等价转成外延性所需的路径。
<!--ja-->
単集合と非順序対の所属には、階層での所属 `⟨ y ∈ b ⟩` と、それぞれの構成が用いる小さな所属の分類という同値な二つの形があります。`∈∈ₛ` が両者を結びます。単集合の分類はパス `y ≡ u` を与え、非順序対の分類は切り詰められた選択肢 `∥ (y ≡ u) ⊎ (y ≡ v) ∥₁` を与えます。各所属の記述を両方向に証明すれば、`⇔toPath` が所属命題の同値を外延性に必要なパスへ変えます。
<!--/-->

```agda

open import Cubical.Data.Unit using ( tt )
import Cubical.Data.Sum as Sum
open Sum using ( _⊎_; inl; inr )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁; ∣_∣₁ )
```

<!--en-->
The semantics takes its truth values in `hProp` at level `ℓ-suc ℓ`. A formula does not evaluate to a bare boolean: its value is a proposition, and satisfaction of a formula under an environment is itself a proposition rather than a decision. The truth algebra supplies conjunction and disjunction of these truth values for reading compound formulas. This propositional setting matters for the goal: it allows satisfaction of a bounded formula to be identified, path-for-path, with an external condition such as equality of a set with its coded pair.
<!--zh-->
语义以层级 `ℓ-suc ℓ` 上的 `hProp` 为真值。公式不取值为一个裸的布尔值：其值是一个命题，而一个赋值下公式的满足关系本身就是一个命题，而非一个判定。真值代数供给这些真值的合取与析取，用以解读复合公式。这一命题化设定对目标至关重要：它使一条有界公式的满足关系能够逐路径地等同于一个外部条件，例如某集合与其编码对相等。
<!--ja-->
意味論は、レベル `ℓ-suc ℓ` の `hProp` を真理値として取ります。論理式は裸のブール値に評価されるのではなく、その値は命題であり、環境のもとでの論理式の充足それ自体が判定ではなく命題です。真理値代数は、複合した論理式を読むために、これらの真理値の連言と選言を供給します。この命題的な設定が目標にとって重要です。有界論理式の充足を、集合とその符号化された対の等号のような外側の条件と、パスとして同一視できるからです。
<!--/-->

```agda
open import Cubical.Functions.Logic using ( ⇔toPath )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_; setIsSet )
open import Cubical.HITs.CumulativeHierarchy.Properties
  using ( ∈∈ₛ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
```

<!--en-->
Within this semantics, the constant interpretation is fixed to be the identity on `V ℓ`: a constant of the language is simply a set, denoting itself. Consequently `⟦ var k ⟧ γ` is the value that the environment `γ` assigns to position `k`, and a formula may speak directly about the assigned sets.
<!--zh-->
在此语义中，常元解释被固定为 `V ℓ` 上的恒等：语言中的一个常元就是一个集合，指称它自身。于是 `⟦ var k ⟧ γ` 是环境 `γ` 分派给位置 `k` 的值，公式从而可以直接谈论被指派的集合。
<!--ja-->
この意味論の中で、定数解釈は `V ℓ` 上の恒等写像に固定されます。言語の定数はただの集合であり、自分自身を表示するのです。したがって `⟦ var k ⟧ γ` は環境 `γ` が位置 `k` に割り当てる値であり、論理式は割り当てられた集合を直接語ることができます。
<!--/-->

```agda
  using ( ⁅_,_⁆; pairing-ax; ⁅_⁆s; SingletonPackage; module InfinitySet )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( SetPackage )  -- lint-agda: keep (used qualified: SetPackage.classification)
open InfinitySet using ( #_ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
```

<!--en-->
This is what makes the adequacy statement below meaningful: satisfaction of the reader `prAt` at positions `q`, `u`, `v` will be compared, as truth values, with the equality of `⟦ var q ⟧ γ` and `pr (⟦ var u ⟧ γ) (⟦ var v ⟧ γ)`.
<!--zh-->
这正是下面充分性陈述有意义的原因：读式 `prAt` 在位置 `q`、`u`、`v` 上的满足关系将作为真值，与 `⟦ var q ⟧ γ` 和 `pr (⟦ var u ⟧ γ) (⟦ var v ⟧ γ)` 的相等相比较。
<!--ja-->
これが次の妥当性の主張を意味あるものにします。読解式 `prAt` の位置 `q`、`u`、`v` での充足が、真理値として、`⟦ var q ⟧ γ` と `pr (⟦ var u ⟧ γ) (⟦ var v ⟧ γ)` の等号と比較されるのです。
<!--/-->

```agda
module Sem = FOL.Semantics (hPropAlgebra (ℓ-suc ℓ)) 𝒮ᵥ
open Sem using ( _^_ )
open Sem.At (V ℓ) id using ( _⊨_; ⟦_⟧ )
```

<!--en-->
## Singletons and pairs, characterized

A set whose only member is `u` is the singleton of `u`, and a set whose members are exactly `u` and `v` is their unordered pair. These are the external meanings that the object-language readers will express, so they are proved here once, at the meta level. Both characterizations rest on the same move: if two sets admit the same members, extensionality `extensionalV` turns the pointwise membership equivalence into a path of sets.

The two directions differ in strength. That a member of `⁅ u ⁆s` equals `u` is a path without an outer truncation; that a member of `⁅ u , v ⁆` is one of `u` and `v` is merely so, a propositionally truncated disjunction. The proofs keep this distinction exact.
<!--zh-->
## 单点集与无序对的特征刻画

唯一成员为 `u` 的集合就是 `u` 的单点集，而成员恰为 `u` 与 `v` 的集合就是它们的无序对。这些正是对象语言读式将要表达的外部含义，故在元层于此一次性证明。两条特征刻画依赖同一个手法：若两个集合允许相同的成员，外延性 `extensionalV` 便把逐点的隶属等价变成集合间的路径。

两个方向的强度不同。`⁅ u ⁆s` 的成员等于 `u` 是一条没有外层截断的路径；`⁅ u , v ⁆` 的成员是 `u` 或 `v` 则仅仅是如此，是一个命题截断的析取。证明严格保持了这一区分。
<!--ja-->
## 単集合と非順序対を特徴付ける

唯一の要素が `u` である集合は `u` の単集合であり、要素がちょうど `u` と `v` である集合はそれらの非順序対です。これらは対象言語の読解式が表すことになる外側の意味なので、メタレベルでここに一度証明します。どちらの特徴付けも同じ手法に依ります。二つの集合が同じ要素を許すなら、外延性 `extensionalV` が点ごとの所属の同値を集合間のパスに変えるのです。

二つの方向は強さが異なります。`⁅ u ⁆s` の要素が `u` と等しいことは外側の切り詰めを伴わないパスですが、`⁅ u , v ⁆` の要素が `u` か `v` のどちらかであることは命題的に切り詰められた形でしか、つまり命題として丸められた選言でしか言えません。証明はこの区別を正確に保ちます。
<!--/-->

<!--en-->
Membership in a singleton is completely described by the classification of `SingletonPackage`: `y` belongs to `⁅ u ⁆s` precisely when `y` equals `u`. The bridge `∈∈ₛ` moves between the ambient membership of the hierarchy and this small membership, so `∈sgl-elim` chains the bridge's forward leg with the classification to extract an actual path `y ≡ u` from a mere membership proof, and `∈sgl-intro` runs the same two steps backwards. No truncation is involved: the equality path is available directly and, since `V ℓ` is a set, remains a proposition.
<!--zh-->
对单点集的隶属被 `SingletonPackage` 的分类完全刻画：`y` 属于 `⁅ u ⁆s`，恰好当 `y` 等于 `u`。桥 `∈∈ₛ` 在层级的原生隶属与这一小隶属之间转换，于是 `∈sgl-elim` 把桥的前半段与分类串联起来，从仅仅一条隶属证明中提取出直接的路径 `y ≡ u`；`∈sgl-intro` 把同样的两步反向执行。这里没有任何截断：相等路径可直接使用；由于 `V ℓ` 是集合，这仍是命题。
<!--ja-->
単集合への所属は `SingletonPackage` の分類によって完全に記述されます。`y` が `⁅ u ⁆s` に属するのは、`y` が `u` と等しいとき、かつそのときに限ります。橋 `∈∈ₛ` が階層本来の所属とこの小さい所属の間を行き来するので、`∈sgl-elim` は橋の前半と分類をつなげ、単なる所属の証明から実際のパス `y ≡ u` を取り出します。`∈sgl-intro` は同じ二段階を逆向きに進めます。ここに丸めは一切なく、等号は明示的なデータです。
<!--/-->

```agda
∈sgl-elim : {u y : V ℓ} → ⟨ y ∈ ⁅ u ⁆s ⟩ → y ≡ u
∈sgl-elim {u} {y} h =
    SetPackage.classification (SingletonPackage u) y .fst (∈∈ₛ {a = y} {b = ⁅ u ⁆s} .fst h)

∈sgl-intro : {u y : V ℓ} → y ≡ u → ⟨ y ∈ ⁅ u ⁆s ⟩
∈sgl-intro {u} {y} e = ∈∈ₛ {a = y} {b = ⁅ u ⁆s} .snd
```

<!--en-->
For the unordered pair, the classification `pairing-ax` describes membership by a disjunction: a member equals `u` or it equals `v`. Here the truncation appears. `∈pair-elim` converts a membership proof into a merely-disjunct statement `∥ (y ≡ u) ⊎ (y ≡ v) ∥₁`, because the underlying classification returns a propositionally truncated choice of side, and eliminating it into the untruncated sum is not allowed. Conversely, `∈pair-introL` and `∈pair-introR` each take an explicit path on one side and seal it as merely one side or the other, obtaining membership.
<!--zh-->
对无序对，分类 `pairing-ax` 用析取刻画隶属：成员等于 `u` 或等于 `v`。截断正是在此出现。`∈pair-elim` 把隶属证明转换为仅仅成立的析取 `∥ (y ≡ u) ⊎ (y ≡ v) ∥₁`，因为底层的分类返回的是命题截断的两种可能，而不允许把它消去到未截断的和类型。反过来，`∈pair-introL` 与 `∈pair-introR` 各取一侧的直接给出的路径，把它封为「仅仅这一侧或那一侧」，从而得到隶属。
<!--ja-->
非順序対については、分類 `pairing-ax` が所属を選言で記述します。要素は `u` と等しいか、`v` と等しいかです。ここに丸めが現れます。`∈pair-elim` は所属の証明を、命題的に切り詰められた形でしか成り立たない選言 `∥ (y ≡ u) ⊎ (y ≡ v) ∥₁` に変えます。下の分類が側の選択を命題として丸めて返すためで、それを丸めなしの直和型へ消去することはできません。逆に `∈pair-introL` と `∈pair-introR` はそれぞれ片側の明示的なパスを受け取り、それを「どちらか一方が成り立つという切り詰められた形」として封入して所属を得ます。
<!--/-->

```agda
    (SetPackage.classification (SingletonPackage u) y .snd e)

∈pair-elim : {u v y : V ℓ} → ⟨ y ∈ ⁅ u , v ⁆ ⟩ → ∥ (y ≡ u) ⊎ (y ≡ v) ∥₁
∈pair-elim {u} {v} {y} h = pairing-ax u v y .fst (∈∈ₛ {a = y} {b = ⁅ u , v ⁆} .fst h)

∈pair-introL : {u v y : V ℓ} → y ≡ u → ⟨ y ∈ ⁅ u , v ⁆ ⟩
∈pair-introL {u} {v} {y} e = ∈∈ₛ {a = y} {b = ⁅ u , v ⁆} .snd
```

<!--en-->
The second introduction is symmetric to the first. With membership into and out of both constructions available, the external characterizations can be stated. `sgl-char` says: if `u` belongs to `x` and every member of `x` equals `u`, then `x` is the singleton of `u`. `pair-char` says the analogous thing for two components, with the every-member clause now merely disjunctive. Both conclusions are paths of sets, and both will later supply exactly the clauses that the reader `prAt` expresses.
<!--zh-->
第二条引入与第一条对称。进入与离开这两个构造的隶属都齐备后，外部特征刻画便可陈述。`sgl-char` 说：若 `u` 属于 `x` 且 `x` 的每个成员都等于 `u`，则 `x` 是 `u` 的单点集。`pair-char` 对两个分量说类似的话，只是「每个成员」条款此刻是仅仅成立的析取。两条结论都是集合间的路径，而且之后都将恰好供给读式 `prAt` 所表达的那些子句。
<!--ja-->
二つ目の導入は一つ目と対称です。両方の構成への出入りの所属が揃ったので、外側の特徴付けを述べられます。`sgl-char` はこう言います。`u` が `x` に属し、`x` のすべての要素が `u` と等しいなら、`x` は `u` の単集合である、と。`pair-char` は二つの成分について同様のことを言い、「すべての要素」の節が命題的に切り詰められた選言になるだけです。どちらの結論も集合間のパスであり、後でどちらも読解式 `prAt` が表す節をちょうど供給します。
<!--/-->

```agda
    (pairing-ax u v y .snd ∣ inl e ∣₁)

∈pair-introR : {u v y : V ℓ} → y ≡ v → ⟨ y ∈ ⁅ u , v ⁆ ⟩
∈pair-introR {u} {v} {y} e = ∈∈ₛ {a = y} {b = ⁅ u , v ⁆} .snd
    (pairing-ax u v y .snd ∣ inr e ∣₁)

sgl-char : (x u : V ℓ) → ⟨ u ∈ x ⟩ → ((y : V ℓ) → ⟨ y ∈ x ⟩ → y ≡ u) → x ≡ ⁅ u ⁆s
```

<!--en-->
To prove `x ≡ ⁅ u ⁆s` from the two membership hypotheses, extensionality is applied pointwise: for each `y`, the proposition `⟨ y ∈ x ⟩` must be connected to `⟨ y ∈ ⁅ u ⁆s ⟩` by a path, and `⇔toPath` builds exactly such a path from an iff. The forward direction uses the hypothesis that all members of `x` equal `u` and then reintroduces membership in the singleton; this is `sub₁`.
<!--zh-->
要从两条隶属假设证明 `x ≡ ⁅ u ⁆s`，需逐点使用外延性：对每个 `y`，命题 `⟨ y ∈ x ⟩` 必须经一条路径与 `⟨ y ∈ ⁅ u ⁆s ⟩` 相连，而 `⇔toPath` 恰好从当且仅当构造出这样的路径。前进方向使用「`x` 的所有成员都等于 `u`」这一假设，再重新引入对单点集的隶属；这就是 `sub₁`。
<!--ja-->
二つの所属の仮定から `x ≡ ⁅ u ⁆s` を証明するには、外延性を点ごとに適用します。各 `y` について、命題 `⟨ y ∈ x ⟩` を `⟨ y ∈ ⁅ u ⁆s ⟩` と結ぶパスが必要であり、`⇔toPath` は同値からまさにそのようなパスを作ります。順方向は「`x` のすべての要素は `u` に等しい」という仮定を使い、その後で単集合への所属を再導入します。これが `sub₁` です。
<!--/-->

```agda
sgl-char x u hu hall = extensionalV (λ y → ⇔toPath (sub₁ y) (sub₂ y))
  where
  sub₁ : (y : V ℓ) → ⟨ y ∈ x ⟩ → ⟨ y ∈ ⁅ u ⁆s ⟩
  sub₁ y hy = ∈sgl-intro (hall y hy)
  sub₂ : (y : V ℓ) → ⟨ y ∈ ⁅ u ⁆s ⟩ → ⟨ y ∈ x ⟩
```

<!--en-->
The backward direction `sub₂` starts from membership in the singleton and must produce membership in `x`. Elimination gives the path `y ≡ u`, and membership is then transported along its reversal: if `u` belongs to `x` and `y` is a path away from `u`, `y` belongs to `x` as well. This transport-along-a-path pattern is the standard substitute for comparing constructions directly, and it recurs in every remaining proof of the chapter. With both directions in place, `⇔toPath` assembles the pointwise equivalence and `extensionalV` returns the path `x ≡ ⁅ u ⁆s`.
<!--zh-->
反向的 `sub₂` 从对单点集的隶属出发，须产出对 `x` 的隶属。消去给出路径 `y ≡ u`，再沿其逆把隶属传输过去：若 `u` 属于 `x` 而 `y` 与 `u` 相差一条路径，则 `y` 也属于 `x`。这种「沿路径传输」的模式是直接比较各构造的标准替代品，在本章其余每个证明中都会重现。两个方向就位后，`⇔toPath` 组装出逐点等价，`extensionalV` 返回路径 `x ≡ ⁅ u ⁆s`。
<!--ja-->
逆向きの `sub₂` は単集合への所属から出発し、`x` への所属を作らねばなりません。消去がパス `y ≡ u` を与え、その逆方向に所属が輸送されます。`u` が `x` に属し、`y` が `u` とパス一本分しか違わないなら、`y` も `x` に属する、というわけです。この「パスに沿った輸送」の型は、構成を直接比較する代わりの標準的な手段であり、本章の残りのすべての証明で繰り返し現れます。両方向が揃えば、`⇔toPath` が点ごとの同値を組み立て、`extensionalV` がパス `x ≡ ⁅ u ⁆s` を返します。
<!--/-->

```agda
  sub₂ y hy = subst (λ z → ⟨ z ∈ x ⟩) (sym (∈sgl-elim hy)) hu


pair-char : (x u v : V ℓ) → ⟨ u ∈ x ⟩ → ⟨ v ∈ x ⟩
          → ((y : V ℓ) → ⟨ y ∈ x ⟩ → ∥ (y ≡ u) ⊎ (y ≡ v) ∥₁)
          → x ≡ ⁅ u , v ⁆
pair-char x u v hu hv hall = extensionalV (λ y → ⇔toPath (sub₁ y) (sub₂ y))
```

<!--en-->
The proof of `pair-char` follows the same plan, with one new feature: the every-member hypothesis is truncated, so the forward direction `sub₁` cannot pattern-match on which side `y` is on. Instead it eliminates the truncation `PT.rec` into the membership proposition `⟨ y ∈ ⁅ u , v ⁆ ⟩`, which is indeed proposition-valued, and dispatches on the two sides of the sum: a member equal to `u` enters the pair from the left, one equal to `v` from the right. This is the sanctioned way to use a merely-disjunct fact.
<!--zh-->
`pair-char` 的证明遵循同一计划，但有一个新特点：「每个成员」假设是截断的，故前进方向 `sub₁` 不能对 `y` 在哪一侧做模式匹配。它改为用 `PT.rec` 把截断消去到确为命题值的隶属命题 `⟨ y ∈ ⁅ u , v ⁆ ⟩` 中，再在和类型的两侧上分派：等于 `u` 的成员从左边进入那个对，等于 `v` 的成员从右边进入。这是使用仅仅成立的析取事实的正当方式。
<!--ja-->
`pair-char` の証明は同じ計画に従いますが、新しい特徴が一つあります。「すべての要素」の仮定は丸められているので、順方向の `sub₁` は `y` がどちらの側かでパターンマッチできません。代わりに、`PT.rec` で丸めを、実際に命題値である所属の命題 `⟨ y ∈ ⁅ u , v ⁆ ⟩` へ消去し、直和の二つの側で場合分けします。`u` に等しい要素は対に左から、`v` に等しい要素は右から入ります。これが命題的に切り詰められた選言の事実を用いる正しいやり方です。
<!--/-->

```agda
  where
  sub₁ : (y : V ℓ) → ⟨ y ∈ x ⟩ → ⟨ y ∈ ⁅ u , v ⁆ ⟩
  sub₁ y hy = PT.rec ((y ∈ ⁅ u , v ⁆) .snd)
    (Sum.rec (∈pair-introL {u = u} {v = v}) (∈pair-introR {u = u} {v = v})) (hall y hy)
  sub₂ : (y : V ℓ) → ⟨ y ∈ ⁅ u , v ⁆ ⟩ → ⟨ y ∈ x ⟩
```

<!--en-->
The backward direction `sub₂` mirrors this: from membership in `⁅ u , v ⁆` it obtains the truncated disjunction via `∈pair-elim`, eliminates it into the membership proposition `⟨ y ∈ x ⟩`, and in each branch transports the corresponding hypothesis `hu` or `hv` backward along the recovered path. Both `sub₁` and `sub₂` thus manufacture membership in `x` out of nothing more than the classification of the pair construction, and `extensionalV` upgrades the pointwise result to `x ≡ ⁅ u , v ⁆`.
<!--zh-->
反向的 `sub₂` 与之镜像：从对 `⁅ u , v ⁆` 的隶属经 `∈pair-elim` 得到截断析取，把它消去到隶属命题 `⟨ y ∈ x ⟩` 中，并在每个分支里沿还原出的路径把相应的假设 `hu` 或 `hv` 反向传输。于是 `sub₁` 与 `sub₂` 都只凭对构造的分类就制造出对 `x` 的隶属，`extensionalV` 再把逐点的结果升级为 `x ≡ ⁅ u , v ⁆`。
<!--ja-->
逆向きの `sub₂` はこれを鏡写しにします。`⁅ u , v ⁆` への所属から `∈pair-elim` で丸められた選言を得て、それを所属の命題 `⟨ y ∈ x ⟩` へ消去し、各分岐で取り戻したパスに沿って対応する仮定 `hu` か `hv` を逆方向へ輸送します。こうして `sub₁` と `sub₂` は、対の構成の分類だけを材料に `x` への所属を作り出し、`extensionalV` が点ごとの結果を `x ≡ ⁅ u , v ⁆` へ引き上げます。
<!--/-->

```agda
  sub₂ y hy = PT.rec ((y ∈ x) .snd)
    (Sum.rec (λ e → subst (λ z → ⟨ z ∈ x ⟩) (sym e) hu)
             (λ e → subst (λ z → ⟨ z ∈ x ⟩) (sym e) hv)) (∈pair-elim hy)
```

<!--en-->
## The Kuratowski pair, at the meta level

The reader `prAt`{.Agda} will say of a set `Q` that it contains a member which is the singleton of `U`, a member which is the unordered pair of `U` and `W`, and that every member is one of these two. This section proves that exactly these three conditions force `Q` to equal the Kuratowski pair `pr U W = ⁅ ⁅ U ⁆s , ⁅ U , W ⁆ ⁆`, and conversely. The two auxiliary predicates below record the conditions one clause at a time, in precisely the shape that the satisfaction of a bounded formula will unfold to; the semantic lemmas of the adequacy section can then hand their hypotheses straight to the metalevel lemmas proved here, instead of proving anything a second time.
<!--zh-->
## 元层的 Kuratowski 对

读式 `prAt`{.Agda} 将对一个集合 `Q` 说：它有一个成员是 `U` 的单点集，有一个成员是 `U` 与 `W` 的无序对，且每个成员都是这两者之一。本节证明恰好这三条条件迫使 `Q` 等于 Kuratowski 对 `pr U W = ⁅ ⁅ U ⁆s , ⁅ U , W ⁆ ⁆`，并证明其逆。下面的两个辅助谓词逐条记录这些条件，其形状恰好是 bounded 公式的满足关系将要展开成的形状；于是充分性一节的语义引理可以直接把假设交给这里证明的元层引理，而不必再证一遍。
<!--ja-->
## メタレベルの Kuratowski 対

読解式 `prAt`{.Agda} は、集合 `Q` について、`U` の単集合である要素をひとつ持ち、`U` と `W` の非順序対である要素をひとつ持ち、しかもすべての要素がこのどちらかである、と言います。この節は、まさにこの三つの条件が `Q` を Kuratowski 対 `pr U W = ⁅ ⁅ U ⁆s , ⁅ U , W ⁆ ⁆` と等しくすること、およびその逆を証明します。下の二つの補助述語は条件を節ごとに記録し、その形は有界論理式の充足が展開されていく形とちょうど同じです。そのため、妥当性の節の意味論的補題は、仮定をここで証明したメタレベルの補題にそのまま渡すことができ、同じことを二度証明する必要がありません。
<!--/-->

<!--en-->
The first predicate `SglOf U w` states that `w` is the singleton of `U` in purely membership terms: `U` belongs to `w`, and any `z` belonging to `w` equals `U` outright. The second, `PairOf U W w`, states that `w` is the unordered pair: both `U` and `W` belong to `w`, and every member is merely one of the two, a propositionally truncated disjunction. Both live at the level `ℓ-suc ℓ` because quantifying over all sets of `V ℓ` costs one level, the same level at which the semantics takes its truth values.
<!--zh-->
第一个谓词 `SglOf U w` 用纯粹的隶属语言说 `w` 是 `U` 的单点集：`U` 属于 `w`，且任何属于 `w` 的 `z` 都实实在在地等于 `U`。第二个谓词 `PairOf U W w` 说 `w` 是无序对：`U` 与 `W` 都属于 `w`，且每个成员仅仅是二者之一，即一个命题截断的析取。二者都居于层级 `ℓ-suc ℓ`，因为对所有 `V ℓ` 中的集合量化要花掉一个层级，与语义取真值的层级相同。
<!--ja-->
最初の述語 `SglOf U w` は、`w` が `U` の単集合であることを所属の言葉だけで述べます。`U` が `w` に属し、`w` に属する任意の `z` は打ち切りなしに `U` と等しい、ということです。二つ目の `PairOf U W w` は、`w` が非順序対であることを述べます。`U` と `W` がともに `w` に属し、すべての要素が命題的に切り詰められた形でこのどちらかである、つまり命題として丸められた選言です。両方がレベル `ℓ-suc ℓ` に住むのは、`V ℓ` のすべての集合を量化するのに一レベル必要で、それが意味論が真理値を取るレベルと同じだからです。
<!--/-->

```agda
private
  SglOf : V ℓ → V ℓ → Type (ℓ-suc ℓ)
  SglOf U w = ⟨ U ∈ w ⟩ × ((z : V ℓ) → ⟨ z ∈ w ⟩ → z ≡ U)

  PairOf : V ℓ → V ℓ → V ℓ → Type (ℓ-suc ℓ)
  PairOf U W w =
```

<!--en-->
The packages connect to equality through the characterizations of the previous section. If `w` carries `SglOf U`, its two components are exactly the hypotheses of `sgl-char`, which returns the path `w ≡ ⁅ U ⁆s`; similarly `pair-char` turns a `PairOf` package into `w ≡ ⁅ U , W ⁆`. Thus a package is a certificate of equality with the corresponding construction, and it is obtained without inspecting how `w` was built.
<!--zh-->
这些包装经由上一节的特征刻画与等式相连。若 `w` 携带 `SglOf U`，其两个分量恰是 `sgl-char` 的假设，后者返回路径 `w ≡ ⁅ U ⁆s`；类似地，`pair-char` 把 `PairOf` 包装变成 `w ≡ ⁅ U , W ⁆`。于是包装就是与相应构造相等的证书，而且取得它无需检查 `w` 是如何构造的。
<!--ja-->
パッケージは、前節の特徴付けを通して等号と結び付きます。`w` が `SglOf U` を持てば、その二つの成分はちょうど `sgl-char` の仮定であり、`sgl-char` はパス `w ≡ ⁅ U ⁆s` を返します。同様に `pair-char` は `PairOf` のパッケージを `w ≡ ⁅ U , W ⁆` に変えます。つまりパッケージは対応する構成との等号の証明書であり、`w` がどう作られたかを検査することなしに得られます。
<!--/-->

```agda
    ⟨ U ∈ w ⟩ × (⟨ W ∈ w ⟩ × ((z : V ℓ) → ⟨ z ∈ w ⟩ → ∥ (z ≡ U) ⊎ (z ≡ W) ∥₁))

  sglOf→≡ : {U w : V ℓ} → SglOf U w → w ≡ ⁅ U ⁆s
  sglOf→≡ {U} {w} (hu , hall) = sgl-char w U hu hall

  pairOf→≡ : {U W w : V ℓ} → PairOf U W w → w ≡ ⁅ U , W ⁆
  pairOf→≡ {U} {W} {w} (hu , hv , hall) = pair-char w U W hu hv hall
```

<!--en-->
The converse data also exists: the constructions themselves carry their own packages. For `⁅ U ⁆s`, membership of `U` follows from `∈sgl-intro` at the reflexive path, and every member equals `U` by `∈sgl-elim`; the unordered pair is packaged the same way using both introductions and `∈pair-elim`. Finally, since a package is a proposition-valued type in the set `w`, it can be transported along a path between sets: from `w ≡ ⁅ U ⁆s` one obtains `SglOf U w` by transporting the package of `⁅ U ⁆s` backward along the path.
<!--zh-->
反向的数据也存在：这些构造本身就携带自己的包装。对 `⁅ U ⁆s` 而言，`U` 的隶属由在自反路径上使用 `∈sgl-intro` 得到，而每个成员等于 `U` 由 `∈sgl-elim` 得到；无序对用两条引入与 `∈pair-elim` 以同样方式包装。最后，由于包装是关于集合 `w` 的取命题值的类型，它可以沿集合间的路径传输：从 `w ≡ ⁅ U ⁆s` 出发，把 `⁅ U ⁆s` 的包装沿路径反向传输，便得到 `SglOf U w`。
<!--ja-->
逆向きのデータも存在します。構成そのものが自分のパッケージを持つのです。`⁅ U ⁆s` については、`U` の所属は反射パスでの `∈sgl-intro` から、すべての要素が `U` と等しいことは `∈sgl-elim` から従います。非順序対も、二つの導入と `∈pair-elim` を使って同様にパッケージされます。最後に、パッケージは集合 `w` についての命題値の型なので、集合間のパスに沿って輸送できます。`w ≡ ⁅ U ⁆s` からは、`⁅ U ⁆s` のパッケージをパスに沿って逆方向へ輸送して `SglOf U w` が得られます。
<!--/-->

```agda

  sglOf⁅⁆ : (U : V ℓ) → SglOf U ⁅ U ⁆s
  sglOf⁅⁆ U = ∈sgl-intro refl , (λ z z∈ → ∈sgl-elim z∈)

  pairOf⁅⁆ : (U W : V ℓ) → PairOf U W ⁅ U , W ⁆
  pairOf⁅⁆ U W = ∈pair-introL refl , ∈pair-introR refl , (λ z z∈ → ∈pair-elim z∈)

  sglOf-subst : {U w : V ℓ} → w ≡ ⁅ U ⁆s → SglOf U w
```

<!--en-->
With the packages in place, the metalevel characterization can be stated. `prChar-fwd` takes three hypotheses and concludes the path `Q ≡ pr U W`. The first two are truncated existential statements: merely some member `w` of `Q` carries `SglOf U`, and merely some member `w` of `Q` carries `PairOf U W`. The third is the universal clause: every member `y` of `Q` merely is a singleton of `U` or a pair of `U` and `W`. Note that the outer set of `pr U W` is an unordered pair whose two members encode the ordered components; `Q` will be shown equal to that outer pair via `pair-char`.
<!--zh-->
包装就位后，元层特征刻画便可陈述。`prChar-fwd` 取三条假设，得出路径 `Q ≡ pr U W`。前两条是截断的存在陈述：仅仅存在 `Q` 的某个成员 `w` 携带 `SglOf U`，仅仅存在 `Q` 的某个成员 `w` 携带 `PairOf U W`。第三条是全称条款：`Q` 的每个成员 `y` 仅仅是 `U` 的单点集或 `U` 与 `W` 的对。注意 `pr U W` 的外层集合是一个无序对，其两个成员编码了有序的分量；下面将通过 `pair-char` 证明 `Q` 等于这个外层对。
<!--ja-->
パッケージが揃ったので、メタレベルの特徴付けを述べられます。`prChar-fwd` は三つの仮定を受け取り、パス `Q ≡ pr U W` という結論を出します。最初の二つは丸められた存在の主張です。`Q` のある要素 `w` が `SglOf U` を持つこと、`Q` のある要素 `w` が `PairOf U W` を持つことが、いずれも命題的に切り詰められた形で主張されます。三つ目は全称の節です。`Q` のすべての要素 `y` は、`U` の単集合か、`U` と `W` の対かのどちらかに命題的に切り詰められたります。`pr U W` の外側の集合は、順序づけられた成分を符号化する二つの要素を持つ非順序対であり、`Q` がその外側の対と等しいことを `pair-char` で示すことに注意してください。
<!--/-->

```agda
  sglOf-subst {U} e = subst (SglOf U) (sym e) (sglOf⁅⁆ U)

  pairOf-subst : {U W w : V ℓ} → w ≡ ⁅ U , W ⁆ → PairOf U W w
  pairOf-subst {U} {W} e = subst (PairOf U W) (sym e) (pairOf⁅⁆ U W)

prChar-fwd : (Q U W : V ℓ)
  → ∥ Σ[ w ∈ V ℓ ] (⟨ w ∈ Q ⟩ × SglOf U w) ∥₁
```

<!--en-->
The first two hypotheses each provide, merely, a member of `Q` together with a package proving that member equal to the corresponding construction. The truncation is eliminated into the membership proposition `⟨ ⁅ U ⁆s ∈ Q ⟩` or `⟨ ⁅ U , W ⁆ ∈ Q ⟩`, both of which are proposition-valued, so no choice of witness needs to be made uniform. Inside each branch, the package is converted to the path `w ≡ ⁅ U ⁆s` or `w ≡ ⁅ U , W ⁆` and the membership of `w` is transported along it, yielding membership of the construction in `Q`. These are exactly the first two arguments `pair-char` requires with `⁅ U ⁆s` and `⁅ U , W ⁆` in place of `u` and `v`.
<!--zh-->
前两条假设各自仅仅给出 `Q` 的一个成员以及证明该成员等于相应构造的包装。截断被消去到隶属命题 `⟨ ⁅ U ⁆s ∈ Q ⟩` 或 `⟨ ⁅ U , W ⁆ ∈ Q ⟩` 中，二者都取命题值，故无需让见证的选取保持一致。在每个分支内，包装被转换为路径 `w ≡ ⁅ U ⁆s` 或 `w ≡ ⁅ U , W ⁆`，并把 `w` 的隶属沿它传输，得到该构造对 `Q` 的隶属。这正是 `pair-char` 所需的前两个参数，只是 `u` 与 `v` 的位置换成了 `⁅ U ⁆s` 与 `⁅ U , W ⁆`。
<!--ja-->
最初の二つの仮定は、それぞれ命題的に切り詰められた形で、`Q` の要素と、その要素が対応する構成と等しいことを証明するパッケージを与えます。丸めは、命題値である所属の命題 `⟨ ⁅ U ⁆s ∈ Q ⟩` か `⟨ ⁅ U , W ⁆ ∈ Q ⟩` へ消去されるので、witness の選び方を揃える必要はありません。各分岐の中で、パッケージはパス `w ≡ ⁅ U ⁆s` か `w ≡ ⁅ U , W ⁆` に変えられ、`w` の所属がそれに沿って輸送され、その構成の `Q` への所属が得られます。これは、`u` と `v` の場所に `⁅ U ⁆s` と `⁅ U , W ⁆` を置いた `pair-char` が要求する最初の二つの引数にちょうど相当します。
<!--/-->

```agda
  → ∥ Σ[ w ∈ V ℓ ] (⟨ w ∈ Q ⟩ × PairOf U W w) ∥₁
  → ((y : V ℓ) → ⟨ y ∈ Q ⟩ → ∥ SglOf U y ⊎ PairOf U W y ∥₁)
  → Q ≡ pr U W
prChar-fwd Q U W h₁ h₂ h₃ = pair-char Q ⁅ U ⁆s ⁅ U , W ⁆
  (PT.rec ((⁅ U ⁆s ∈ Q) .snd)
```

<!--en-->
The universal clause needs no elimination at all: for each member `y` of `Q`, the truncated disjunction of packages is mapped through the conversions `sglOf→≡` and `pairOf→≡`, producing the truncated statement that `y` merely equals `⁅ U ⁆s` or `⁅ U , W ⁆`. That is the third argument of `pair-char`. Its conclusion is then `Q ≡ ⁅ ⁅ U ⁆s , ⁅ U , W ⁆ ⁆`, which is by definition `Q ≡ pr U W`. The converse `prChar-bwd` is a matter of exhibiting the three hypotheses for the Kuratowski pair itself.
<!--zh-->
全称条款根本不需要消去：对 `Q` 的每个成员 `y`，把包装的截断析取经转换 `sglOf→≡` 与 `pairOf→≡` 映过去，得到「`y` 仅仅等于 `⁅ U ⁆s` 或 `⁅ U , W ⁆`」的截断陈述。这便是 `pair-char` 的第三个参数。其结论即 `Q ≡ ⁅ ⁅ U ⁆s , ⁅ U , W ⁆ ⁆`，按定义就是 `Q ≡ pr U W`。逆向的 `prChar-bwd` 则只需为 Kuratowski 对本身展示这三条假设。
<!--ja-->
全称の節には消去はまったく要りません。`Q` の各要素 `y` について、パッケージの丸められた選言を変換 `sglOf→≡` と `pairOf→≡` を通して写せば、`y` が命題的に切り詰められた形で `⁅ U ⁆s` か `⁅ U , W ⁆` に等しいという丸められた主張が得られます。これが `pair-char` の三つ目の引数です。その結論は `Q ≡ ⁅ ⁅ U ⁆s , ⁅ U , W ⁆ ⁆` であり、これは定義により `Q ≡ pr U W` です。逆向きの `prChar-bwd` は、Kuratowski 対そのものについて三つの仮定を提示するだけの作業です。
<!--/-->

```agda
    (λ { (w , hw , h) → subst (λ z → ⟨ z ∈ Q ⟩) (sglOf→≡ h) hw }) h₁)
  (PT.rec ((⁅ U , W ⁆ ∈ Q) .snd)
    (λ { (w , hw , h) → subst (λ z → ⟨ z ∈ Q ⟩) (pairOf→≡ h) hw }) h₂)
  (λ y hy → PT.map (Sum.map sglOf→≡ pairOf→≡) (h₃ y hy))


prChar-bwd : (Q U W : V ℓ) → Q ≡ pr U W
```

<!--en-->
Given a path `Q ≡ pr U W`, the three hypotheses are produced in order. The helper `inQ` moves a membership in `pr U W` to a membership in `Q` by transporting along the reversal of the path, and it will feed all three components.
<!--zh-->
给定路径 `Q ≡ pr U W` 后，三条假设依次产出。辅助工具 `inQ` 沿路径的逆把对 `pr U W` 的隶属传输为对 `Q` 的隶属，三条分量都将用到它。
<!--ja-->
パス `Q ≡ pr U W` が与えられれば、三つの仮定が順に作られます。補助の `inQ` は、パスの逆方向に沿って輸送することで、`pr U W` への所属を `Q` への所属に移し、三つの成分すべてがこれを使います。
<!--/-->

```agda
  → (∥ Σ[ w ∈ V ℓ ] (⟨ w ∈ Q ⟩ × SglOf U w) ∥₁)
  × ((∥ Σ[ w ∈ V ℓ ] (⟨ w ∈ Q ⟩ × PairOf U W w) ∥₁)
  × ((y : V ℓ) → ⟨ y ∈ Q ⟩ → ∥ SglOf U y ⊎ PairOf U W y ∥₁))
prChar-bwd Q U W e = h₁ , h₂ , h₃
  where
```

<!--en-->
The first existential is witnessed by `⁅ U ⁆s` itself: it belongs to `pr U W` because the outer pair contains its first component, an instance of `∈pair-introL` at the reflexive path, and after transport through `inQ` this membership holds in `Q`; it carries `SglOf U` by the package `sglOf⁅⁆`. The second is the same with `⁅ U , W ⁆`, `∈pair-introR`, and `pairOf⁅⁆`. Both are sealed with the truncation, as their types demand; the chosen witnesses are enough because the target is merely an existence statement.
<!--zh-->
第一条存在陈述由 `⁅ U ⁆s` 自己作见证：它属于 `pr U W`，因为外层对含有其第一个分量，即在自反路径上的 `∈pair-introL` 的实例；经 `inQ` 传输后这条隶属在 `Q` 中成立；而它携带 `SglOf U` 则由包装 `sglOf⁅⁆` 给出。第二条同样，换用 `⁅ U , W ⁆`、`∈pair-introR` 与 `pairOf⁅⁆`。二者按其类型的要求都以截断封口；由于目标只是存在陈述，所选的见证便已足够。
<!--ja-->
一つ目の存在の主張は、`⁅ U ⁆s` そのものが証人になります。外側の対が第一成分を含むこと、つまり反射パスでの `∈pair-introL` の実例によって、それは `pr U W` に属し、`inQ` を通した輸送の後、この所属は `Q` の中で成り立ちます。`SglOf U` を持つことはパッケージ `sglOf⁅⁆` によります。二つ目は、`⁅ U , W ⁆`、`∈pair-introR`、`pairOf⁅⁆` に置き換えた同じ議論です。どちらも型が求めるとおり丸めで封入されます。対象が単なる存在の主張である以上、選んだ証人で十分です。
<!--/-->

```agda
  inQ : {z : V ℓ} → ⟨ z ∈ pr U W ⟩ → ⟨ z ∈ Q ⟩
  inQ {z} h = subst (λ w → ⟨ z ∈ w ⟩) (sym e) h
  h₁ : ∥ Σ[ w ∈ V ℓ ] (⟨ w ∈ Q ⟩ × SglOf U w) ∥₁
  h₁ = ∣ ⁅ U ⁆s , (inQ (∈pair-introL refl) , sglOf⁅⁆ U) ∣₁
  h₂ : ∥ Σ[ w ∈ V ℓ ] (⟨ w ∈ Q ⟩ × PairOf U W w) ∥₁
```

<!--en-->
The universal clause reduces to the classification of the pair construction. For a member `y` of `Q`, transport along the path gives membership of `y` in `pr U W`, and `∈pair-elim` converts that into the truncated disjunction `y ≡ ⁅ U ⁆s` or `y ≡ ⁅ U , W ⁆`. Each side is upgraded to the corresponding package by the transport lemmas `sglOf-subst` and `pairOf-subst`, so the map sends the disjunction of paths to the disjunction of packages, without ever unfolding either construction.
<!--zh-->
全称条款归结为对构造的分类。对 `Q` 的成员 `y`，沿路径传输给出 `y` 对 `pr U W` 的隶属，`∈pair-elim` 把它转换为截断析取：`y ≡ ⁅ U ⁆s` 或 `y ≡ ⁅ U , W ⁆`。每一侧经传输引理 `sglOf-subst` 与 `pairOf-subst` 升级为相应的包装，于是该映射把路径的析取变为包装的析取，而自始至终不展开任何一个构造。
<!--ja-->
全称の節は、対の構成の分類に帰着します。`Q` の要素 `y` について、パスに沿った輸送により `y` の `pr U W` への所属が得られ、`∈pair-elim` がそれを丸められた選言 `y ≡ ⁅ U ⁆s` か `y ≡ ⁅ U , W ⁆` に変えます。各側は輸送の補題 `sglOf-subst` と `pairOf-subst` によって対応するパッケージに引き上げられ、この対応はパスの選言をパッケージの選言へ写します。どちらの構成も展開されることは一度もありません。
<!--/-->

```agda
  h₂ = ∣ ⁅ U , W ⁆ , (inQ (∈pair-introR refl) , pairOf⁅⁆ U W) ∣₁
  h₃ : (y : V ℓ) → ⟨ y ∈ Q ⟩ → ∥ SglOf U y ⊎ PairOf U W y ∥₁
  h₃ y y∈Q = PT.map (Sum.rec (λ q → inl (sglOf-subst q)) (λ q → inr (pairOf-subst q)))
    (∈pair-elim (subst (λ w → ⟨ y ∈ w ⟩) e y∈Q))
```

<!--en-->
## The readers

The external characterizations now become object-language formulas. Each reader takes the de Bruijn positions it speaks about as arguments, so the same definition serves at any depth of nesting. The bookkeeping is the standard one for bounded quantification: a bounded quantifier binds a fresh variable at position zero and pushes the existing positions one step outward, so a position mentioned under one binder appears as its successor. Because every clause is an atom, a conjunction or disjunction, or a quantifier bounded by a variable of the environment, every reader is Δ₀ and its bounding sets are visible directly in its shape.
<!--zh-->
## 对象语言中的读式

现在把外部的特征刻画写成对象语言的公式。每条读式把它所谈论的 de Bruijn 位置取作参数，故同一条定义在任何嵌套深度都能使用。有界量化的记账是标准做法：有界量词在位置零绑定一个新变元，并把原有位置向外推一步，故在约束下提到的位置以其后继出现。由于每条子句都是原子、合取或析取、或以环境中变元为界的量词，每条读式都是 Δ₀，且其界定集合直接从形状可见。
<!--ja-->
## 対象言語の読解式

外側の特徴付けを、対象言語の論理式にします。各読解式は、それが語る de Bruijn 位置を引数として取るので、同じ定義を任意の入れ子の深さで使えます。有界量化の簿記は標準的なものです。有界量化子は位置ゼロに新しい変数を束縛し、既存の位置を一つ外へずらします。束縛の下で言及される位置はその後者として現れるわけです。すべての節が原子、連言か選言、あるいは環境の変数で限られた量化子であるため、各読解式は Δ₀ であり、その界定集合は形から直接読めます。
<!--/-->

<!--en-->
The singleton reader `sglAt k i` says of the sets assigned to positions `k` and `i` that the one at `i` is the singleton of the one at `k`. Its first conjunct is the atom `var i ∈̇ var k`; the second bounds a quantifier over the members of `var k` and, inside it, compares the freshly bound variable at position zero with `var (suc i)`, which is the position `i` after the one-step shift under the binder. A set satisfies this reading exactly when it has a member equal to `k`'s value and no other members, the content of `SglOf`.
<!--zh-->
单点集读式 `sglAt k i` 对位置 `k` 与 `i` 上指派的集合说：`i` 处的是 `k` 处的单点集。第一个合取支是原子 `var i ∈̇ var k`；第二个合取支以 `var k` 的成员为界量化，并在其内把位置零上新绑定的变元与 `var (suc i)` 比较，后者是 `i` 在约束下经一步移位后的位置。一个集合满足这条读式，恰好当它有一个等于 `k` 值的成员且没有别的成员，即 `SglOf` 的内容。
<!--ja-->
単集合の読解式 `sglAt k i` は、位置 `k` と `i` に割り当てられた集合について、`i` のものが `k` のものの単集合であると言います。第一の連言支は原子 `var i ∈̇ var k` です。第二の支は `var k` の要素の上で有界に量化し、その内側で、位置ゼロに新しく束縛された変数を `var (suc i)` と比較します。後者は、束縛の下で一段ずらされた後の位置 `i` です。ある集合がこの読解を充足するのは、`k` の値と等しい要素をひとつ持ち、ほかに要素を持たないとき、かつそのときに限ります。これが `SglOf` の内容です。
<!--/-->

```agda
sglAt : ∀ {n} → Fin n → Fin n → Formula (V ℓ) n
sglAt k i = (var i ∈̇ var k) ∧̇ (∀̇∈ (var k) (var zero ≐ var (suc i)))
```

<!--en-->
The unordered-pair reader `pairAt k i j` adds the second component and weakens the universal clause to a disjunction. Under the bounded quantifier, the fresh variable at position zero is compared with both `var (suc i)` and `var (suc j)`, the two shifted argument positions. Read externally, a set satisfies it when the values at `i` and `j` both belong to it and every member merely equals one of the two, which is exactly the package `PairOf`. Note the fixity of `_∧̇_` and `_∨̇_` governs only how these expressions parse; no associativity of the connectives is being asserted.
<!--zh-->
无序对读式 `pairAt k i j` 添加第二个分量，并把全称条款弱化为析取。在有界量词之下，位置零上的新变元与两个移位后的参数位置 `var (suc i)` 与 `var (suc j)` 都作比较。从外部读，一个集合满足它，当 `i` 与 `j` 处的值都属于它且每个成员仅仅等于二者之一，这恰是包装 `PairOf`。注意 `_∧̇_` 与 `_∨̇_` 的结合性声明只控制这些表达式如何解析；这里不断言任何联结词的结合律。
<!--ja-->
非順序対の読解式 `pairAt k i j` は第二の成分を加え、全称の節を選言に弱めます。有界量化子の下では、位置ゼロの新しい変数が、ずらされた二つの引数位置 `var (suc i)` と `var (suc j)` のどちらとも比較されます。外側から読めば、`i` と `j` の値がともに属し、すべての要素が命題的に切り詰められた形でそのどちらかと等しいときに充足されます。これはパッケージ `PairOf` そのものです。`_∧̇_` と `_∨̇_` の結合の宣言はこれらの式の構文解析だけを制御するもので、結合子の結合律を主張するものではないことに注意してください。
<!--/-->

```agda

pairAt : ∀ {n} → Fin n → Fin n → Fin n → Formula (V ℓ) n
pairAt k i j = (var i ∈̇ var k) ∧̇ ((var j ∈̇ var k)
            ∧̇ (∀̇∈ (var k) ((var zero ≐ var (suc i)) ∨̇ (var zero ≐ var (suc j)))))

```

<!--en-->
The assembled pair reader puts the two smaller readers together with the three clauses of the metalevel characterization: some member is the singleton, some member is the pair, and every member is one of the two. Each bounded quantifier is over the members of the value at `q`, and the two argument positions are shifted by one beneath each binder, so the inner readers again address the fresh variable as position zero.
<!--zh-->
组装好的对读式把两条较小的读式与元层特征刻画的三条子句合在一起：某个成员是那个单点集，某个成员是那个对，且每个成员二者居其一。每条有界量词都以 `q` 处的值的成员为界，两个参数位置在每条约束下各移一位，故内层读式照旧把新变元当作位置零来称呼。
<!--ja-->
組み立てられた対の読解式は、二つの小さな読解式を、メタレベルの特徴付けの三つの節とともにまとめます。ある要素が単集合であること、ある要素が対であること、そしてすべての要素がそのどちらかであることです。各有界量化子は `q` の値の要素の上で限られ、二つの引数位置は束縛の下で一つずつずれるので、内側の読解式はやはり新しい変数を位置ゼロとして参照します。
<!--/-->

<!--en-->
The first clause bounds an existential over the members of `var q` with body `sglAt zero (suc u)`: the fresh variable at position zero is the candidate member, and `suc u` is the position of `u` after the shift. The second clause is the same with `pairAt`, now mentioning the shifted positions of both `u` and `v`. The third bounds a universal quantifier whose body is the disjunction of the two readers: every member of the value at `q` is merely a singleton or a pair. The existential witnesses and the either-or classification remain propositionally truncated, exactly as in `SglOf` and `PairOf`; the object language does not select a member, it only says that one merely exists.
<!--zh-->
第一条子句以 `var q` 的成员为界作存在量化，体为 `sglAt zero (suc u)`：位置零上的新变元是候选成员，而 `suc u` 是 `u` 经移位后的位置。第二条子句用 `pairAt` 同理，此刻同时提到 `u` 与 `v` 移位后的位置。第三条子句以全称量词为界，其体是两条读式的析取：`q` 处之值的每个成员仅仅是单点集或对。存在见证与「二者居其一」的分类保持命题截断，与 `SglOf` 和 `PairOf` 中完全一致；对象语言不选取成员，只说仅仅存在一个。
<!--ja-->
第一の節は、`var q` の要素の上に存在量化を限り、その本体を `sglAt zero (suc u)` とします。位置ゼロの新しい変数が候補の要素であり、`suc u` は一段ずれた後の `u` の位置です。第二の節は `pairAt` で同じことを行い、今度はずれた後の `u` と `v` 両方の位置に言及します。第三の節は全称量化子を限り、その本体が二つの読解式の選言です。`q` の値のすべての要素は、命題的に切り詰められた形で単集合か対のどちらかです。存在の証人も「どちらか一方」という分類も、`SglOf` と `PairOf` とまったく同じく命題として丸められたままです。対象言語は要素を選ばず、ひとつ命題的に切り詰められた形で存在することしか言いません。
<!--/-->

```agda
prAt : ∀ {n} → Fin n → Fin n → Fin n → Formula (V ℓ) n
prAt q u v = (∃̇∈ (var q) (sglAt zero (suc u)))
          ∧̇ ((∃̇∈ (var q) (pairAt zero (suc u) (suc v)))
          ∧̇ (∀̇∈ (var q) (sglAt zero (suc u) ∨̇ pairAt zero (suc u) (suc v))))

Δ₀-prAt : ∀ {n} (q u v : Fin n) → Δ₀ (prAt q u v)
```

<!--en-->
Boundedness is certified syntactically. The checker `checkΔ₀` traverses the assembled formula, and since every node is an atom, a connective, or a quantifier bounded by a variable, it accepts with the trivial certificate `tt`, yielding `Δ₀-prAt`. This places the reader in the bounded class whose satisfaction is absolute between transitive models, a fact the later chapters on absoluteness rely on.
<!--zh-->
有界性由语法给出证书。检查器 `checkΔ₀` 遍历组装后的公式，由于每个节点都是原子、联结词或以变元为界的量词，它以平凡的证书 `tt` 接受，得到 `Δ₀-prAt`。这把该读式放入那个有界类，其满足关系在传递模型之间是绝对的，后续关于绝对性的各章正依赖这一点。
<!--ja-->
有界性は構文的に証明書を与えられます。検査器 `checkΔ₀` が組み立てられた論理式をたどり、すべての節点が原子、結合子、あるいは変数で限られた量化子であるため、自明な証明書 `tt` とともに受理され、`Δ₀-prAt` が得られます。これでこの読解式は有界なクラスに属し、その充足は推移的モデルの間で絶対的です。後の絶対性に関する章が依拠するのはこの事実です。
<!--/-->

```agda
Δ₀-prAt q u v = checkΔ₀ (prAt q u v) tt

```

<!--en-->
## Adequacy

The final theorem connects the object-language reader with its external meaning. Since satisfaction takes values in `hProp`, the statement is itself a path of truth values: the proposition `γ ⊨ prAt q u v` is identified with the proposition that the value at `q` equals the Kuratowski pair of the values at `u` and `v`, packaged with the proof that this equality type is a proposition because `V ℓ` is an h-set. Unfolding the satisfaction of the three connectives and the bounded quantifiers turns the left side into exactly the three hypotheses that `prChar-fwd` and `prChar-bwd` consume, so the adequacy proof composes two existing arguments rather than proving anything new.
<!--zh-->
## 充分性

最后的定理把对象语言的读式与其外部含义连接起来。由于满足关系取值于 `hProp`，这条陈述本身就是真值之间的一条路径：命题 `γ ⊨ prAt q u v` 被等同于「`q` 处的值等于 `u` 与 `v` 处之值的 Kuratowski 对」这一命题，并附上该相等类型为命题的证明，因为 `V ℓ` 是 h-集。展开三条联结词与有界量词的满足关系后，左边恰好变成 `prChar-fwd` 与 `prChar-bwd` 所消耗的三条假设，于是充分性证明只是把两个已有论证组合起来，而不需证明任何新东西。
<!--ja-->
## 妥当性

最後の定理が、対象言語の読解式とその外側の意味を結び付けます。充足は `hProp` に値を持つので、この主張そのものが真理値の間のパスです。命題 `γ ⊨ prAt q u v` は、「`q` の値が `u` と `v` の値の Kuratowski 対と等しい」という命題と同一視されます。等号の型が命題であることの証明は、`V ℓ` が h-集合であることから付きます。三つの結合子と有界量化子の充足を展開すると、左辺はちょうど `prChar-fwd` と `prChar-bwd` が受け取る三つの仮定になります。したがって妥当性の証明は、既にある二つの議論を組み合わせるだけで、新しいことを証明するのではありません。
<!--/-->

<!--en-->
Both sides of the displayed path are truth values. On the right, the equality type `⟦ var q ⟧ γ ≡ pr (⟦ var u ⟧ γ) (⟦ var v ⟧ γ)` is paired with `setIsSet _ _`, the witness that equality of two h-set elements is a proposition; this pairing is exactly how an `hProp` is built. The proof then supplies the two directions of the underlying iff, and `⇔toPath` promotes them to the path of propositions.
<!--zh-->
所展示的路径两侧都是真值。右边把相等类型 `⟦ var q ⟧ γ ≡ pr (⟦ var u ⟧ γ) (⟦ var v ⟧ γ)` 与 `setIsSet _ _` 配对，后者是「两个 h-集元素的相等是命题」的证明；这种配对正是构造 `hProp` 的方式。证明随后给出底层当且仅当的两个方向，`⇔toPath` 把它们提升为命题间的路径。
<!--ja-->
示されたパスの両辺はともに真理値です。右辺では、等号の型 `⟦ var q ⟧ γ ≡ pr (⟦ var u ⟧ γ) (⟦ var v ⟧ γ)` に `setIsSet _ _` が組にされます。後者は、h-集合の二つの要素の等号が命題であることの証明です。この組がまさに `hProp` の作り方です。証明はその後、根底にある同値の二方向を与え、`⇔toPath` がそれらを命題の間のパスへ引き上げます。
<!--/-->

```agda
prAt-adequate : ∀ {n} (q u v : Fin n) (γ : (V ℓ) ^ n)
              → (γ ⊨ prAt q u v) ≡ ((⟦ var q ⟧ γ ≡ pr (⟦ var u ⟧ γ) (⟦ var v ⟧ γ))
                                   , setIsSet _ _)
prAt-adequate q u v γ = ⇔toPath
  (λ { (h₁ , h₂ , h₃) → prChar-fwd _ _ _ h₁ h₂ h₃ })
```

<!--en-->
The forward direction receives the satisfaction of `prAt q u v`, which by the semantics of `_∧̇_` and the bounded `∃̇∈` and `∀̇∈` is a triple: the truncated existence of a member satisfying the singleton reader, the truncated existence of one satisfying the pair reader, and the universal clause. These are precisely the three arguments of `prChar-fwd`, and they return the path to `pr U W`. The backward direction takes the equality path and hands it to `prChar-bwd`, which packages it into the three clauses that the semantics reassembles into satisfaction. Nothing in either direction inspects how any set was constructed.
<!--zh-->
前进方向接收 `prAt q u v` 的满足关系，按 `_∧̇_` 与有界的 `∃̇∈`、`∀̇∈` 的语义，它是一个三元组：满足单点集读式的成员的截断存在、满足对读式的成员的截断存在，以及全称条款。这恰是 `prChar-fwd` 的三个参数，它们返回到 `pr U W` 的路径。反向取这条相等路径交给 `prChar-bwd`，后者把它包装成语义重新组装为满足关系的三条子句。两个方向都没有检查任何集合是如何构造的。
<!--ja-->
順方向は `prAt q u v` の充足を受け取ります。`_∧̇_` と有界な `∃̇∈`、`∀̇∈` の意味論により、それは三つ組です。単集合の読解を満たす要素の丸められた存在、対の読解を満たす要素の丸められた存在、そして全称の節です。これらはちょうど `prChar-fwd` の三つの引数であり、`pr U W` へのパスを返します。逆向きは等号のパスを受け取り、`prChar-bwd` に渡します。後者はそれを、意味論が充足へと組み立て直す三つの節にパッケージします。どちらの方向でも、集合がどう構成されたかを検査することは一切ありません。
<!--/-->

```agda
  (λ e → prChar-bwd _ _ _ e)

```

<!--en-->
## Recap

`prAt`{.Agda} reads a Kuratowski pair from inside the object language; it is Δ₀ and adequate, its satisfaction being a path to equality with `pr` of the assigned values. Everything a certificate needs in order to destructure a code is now available in bounded form, with no recursion and no comparison of code values. The chapters that follow build certificates on top of these readers.
<!--zh-->
## 小结

`prAt`{.Agda} 从对象语言内部读出 Kuratowski 对，它是 Δ₀ 的且是充分的，其满足关系是一条通往「与指派值之 `pr` 相等」的路径。解构一个码所需的全部证书信息，如今都已具有有界形式，既不使用递归，也不比较码值。随后诸章在这些读式的基础上构造证书。
<!--ja-->
## まとめ

`prAt`{.Agda} は対象言語の内部から Kuratowski 対を読み取ります。それは Δ₀ であり、かつ妥当です。その充足は、割り当てられた値の `pr` との等号へのパスになっています。コードを分解するために証明書が必要とする情報は、いまやすべて有界な形で利用でき、再帰もコード値の比較も使いません。続く章は、これらの読解式の上に証明書を構築していきます。
<!--/-->
