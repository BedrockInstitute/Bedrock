<!--en-->
# Impredicativity

A predicative foundation does not allow a definition to range over a totality that already contains what is being defined. Cubical Agda has such a foundation, whereas the set theory formalized in this book contains impredicative constructions. This chapter therefore states the extra conditions needed for those constructions as explicit assumptions, without changing the foundation of the host.

A predicative foundation can accommodate impredicative assumptions just as intuitionistic logic can explicitly assume classical principles. The converse does not hold: once the stronger principles are built into the foundation, later results no longer reveal which of them they actually require. We therefore retain Cubical Agda's predicative foundation and name every impredicative condition at the point where it is used.

The issue appears in the universe levels. The propositions whose [underlying types]{.term-ref #underlying-type} lie in `Type ℓ`{.Agda} form `hProp ℓ`{.Agda}, but this proposition universe as a whole belongs to `Type (ℓ-suc ℓ)`{.Agda}. A proposition obtained by quantifying over all of `hProp ℓ`{.Agda} need not fit at level `ℓ`. This chapter asks how the truth content of such a higher proposition can nevertheless be represented by an object at the lower level.
<!--zh-->
# 非直谓性

直谓式基础不允许一个定义量化某个已经包含待定义对象的总体。Cubical Agda 建立在这样的基础之上，而本书所要形式化的集合论包含非直谓的构造。为了在直谓式的宿主中准确说明这些构造需要什么，本章专门提出一组接口：它们不改变宿主本身，而是把开展非直谓数学所需的额外条件明确列为假设。

直谓式基础可以容纳这样的非直谓假设，正如直觉主义逻辑可以明确加入经典逻辑原理；反过来却不成立，因为一旦基础本身预先采用了更强的原则，就无法再分辨后续结果究竟依赖哪些额外假设。因此，本书保留 Cubical Agda 的直谓式基础，并在需要非直谓性时，通过本章的接口逐项说明所用的条件。

这里的困难来自宇宙层级。[底层类型]{.term-ref #underlying-type}位于 `Type ℓ`{.Agda} 的命题组成 `hProp ℓ`{.Agda}，而这个命题宇宙整体属于 `Type (ℓ-suc ℓ)`{.Agda}。因此，对 `hProp ℓ`{.Agda} 中所有命题量化所得的命题，不一定仍能放在层级 `ℓ`。本章要解决的问题，就是如何让高层命题的真值内容仍能由低层对象表示。
<!--ja-->
# 非可述性

直謂的な基礎では、定義される対象をすでに含む全体にわたって、その定義自身が量化することを認めません。Cubical Agda はこのような基礎の上にありますが、本書で形式化する集合論には非可述的な構成が含まれます。そこで本章では、ホストの基礎そのものを変えずに、それらの構成に必要な追加条件を明示的な仮定として述べます。

直謂的な基礎が非可述的な仮定を受け入れられることは、直観主義論理が古典論理の原理を明示的に仮定できることに似ています。逆は成り立ちません。強い原理を初めから基礎に組み込めば、後の結果がそのどれに依存するかを区別できなくなるからです。本書は Cubical Agda の直謂的な基礎を保ち、非可述性が必要な箇所で条件を一つずつ明記します。

問題は宇宙レベルに現れます。[基礎型]{.term-ref #underlying-type}が `Type ℓ`{.Agda} に属する命題は `hProp ℓ`{.Agda} をなしますが、この命題の宇宙全体は `Type (ℓ-suc ℓ)`{.Agda} に属します。したがって、`hProp ℓ`{.Agda} のすべての命題にわたる量化から得た命題が、再びレベル `ℓ` に収まるとは限りません。本章では、そのような上位の命題の真理内容を、どのように下位レベルの対象で表せるかを問います。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

module Base.Impredicativity where

open import Base.Prelude
```

<!--en-->
## Comparing across universe levels

To represent a higher proposition is not to place it unchanged in a lower universe. It is to find a lower proposition with the same content. Before making that statement precise, we must decide what relation should compare the two.
<!--zh-->
## 跨越宇宙层级的比较

所谓「表示」，并不是把高层命题原封不动地放进低层宇宙，而是为它寻找一个低层命题，使二者表达相同的内容。要把这句话写成精确的数学条件，我们首先需要确定应当用什么关系比较它们。
<!--ja-->
## 宇宙レベルを越えた比較

上位の命題を「表す」とは、その命題をそのまま下位の宇宙へ入れることではありません。同じ内容を表す下位の命題を見つけることです。この主張を正確に書くには、まず両者をどの関係で比較するかを定める必要があります。
<!--/-->

<!--en-->
A path cannot yet do this job directly, because its endpoints must belong to a common ambient type, while the higher and lower propositions inhabit different universes. [Logical equivalence]{.term-intro #logical-equivalence} can express mutual implication between propositions, but the small classifier used later is not itself a proposition. We therefore need a comparison that applies to arbitrary types: **[type equivalence]{.term-intro #type-equivalence}**.

For types `A` and `B`, a type equivalence `A ≃ B`{.Agda} begins with a map `f : A → B`{.Agda}. To determine whether this map preserves all information, consider in turn how each `b : B`{.Agda} can arise from `A`.
<!--zh-->
路径暂时不能直接承担这项工作，因为路径的两端必须属于同一个环境类型，而高层命题与低层命题位于不同的宇宙。[逻辑等价]{.term-intro #logical-equivalence}可以说明两个命题互相蕴含，却只适用于命题；后面使用的小分类器本身并不是命题。因此，我们需要一种对任意类型都适用的比较方式，这就是**[类型等价]{.term-intro #type-equivalence}**。

对类型 `A` 与 `B`，类型等价 `A ≃ B`{.Agda} 首先包含一个映射 `f : A → B`{.Agda}。为了判断这个映射能否完整地保存信息，我们逐个考察 `b : B`{.Agda} 可以怎样从 `A` 映到。
<!--ja-->
パスはこの役割を直接には担えません。パスの両端は共通の型に属する必要がありますが、上位と下位の命題は異なる宇宙に属するからです。[論理的同値]{.term-intro #logical-equivalence}は命題間の両方向の含意を表せますが、後で用いる小分類子それ自体は命題ではありません。そこで、任意の型に使える比較として**[型同値]{.term-intro #type-equivalence}**を用います。

型 `A` と `B` の型同値 `A ≃ B`{.Agda} は、まず写像 `f : A → B`{.Agda} を含みます。この写像がすべての情報を保つかを調べるため、各 `b : B`{.Agda} が `A` からどのように写ってくるかを一つずつ考えます。
<!--/-->

```agda
open import Cubical.Foundations.Equiv using ( _≃_ )
```

<!--en-->
The **[fibre]{.term-intro #fiber}** of `f` over `b` is the following dependent pair type:

<div class="single-line-code"><code>Σ (a : A) (f a ≡ b)</code></div>

An element of the fibre has two components. The first is a candidate preimage `a : A`{.Agda}; the second is a path `f a ≡ b`{.Agda} witnessing that this candidate really maps to `b`. An empty fibre means that `b` has no preimage. Elements of a fibre that cannot be identified by a path represent substantively different ways to return from `b` to `A`.

When the fibre over every `b : B`{.Agda} is [contractible]{.term-ref #contractible}, each fibre has a centre and all its other elements are path-equal to that centre. Every `b` can therefore be recovered from `A`, and the recovery has no ambiguity up to paths. A map with this property is an equivalence. The inverse map and its two round-trip paths can be derived from the centres of the fibres.

This notion should be distinguished from an [isomorphism]{.term-intro #type-isomorphism}. An isomorphism presents a forward map, a chosen inverse map and the two inverse laws explicitly. It can be converted into an equivalence, and an equivalence can in turn be presented as an isomorphism; the difference is how the same mathematical information is organised. Explicit maps often make an isomorphism convenient when constructing an example. The cubical library uses equivalence as the common interface for transporting type structure, so this chapter records its size principles with `_≃_`{.Agda}.

Nor does `_≃_`{.Agda} merely mean [logical equivalence]{.term-ref #logical-equivalence}. Logical equivalence between propositions supplies implications in both directions. If the underlying types of `P` and `Q` both satisfy `isProp`{.Agda}, those implications do determine an equivalence: propositionhood makes all proofs indistinguishable, so the two composites satisfy the inverse laws automatically. For general types, maps in both directions need not be inverse and are therefore insufficient. This distinction separates the two uses below. In `isSmall`{.Agda}, both sides are propositions, so a logical equivalence can be promoted to a type equivalence. In `HPropSmallness`{.Agda}, the small classifier and `hProp ℓ`{.Agda} are not themselves propositions, so the full type equivalence is essential.

The three notions thus serve different parts of an argument in this book. We often construct an isomorphism to prove an equivalence, use equivalences to preserve and transport structure, and state the final comparison as a path once both objects lie in the same ambient type.
<!--zh-->
`f` 在 `b` 上的**[纤维]{.term-intro #fiber}**，是下面这个依值对类型：

<div class="single-line-code"><code>Σ (a : A) (f a ≡ b)</code></div>

纤维的一个元素由两部分组成：第一分量是一个候选原像 `a : A`{.Agda}，第二分量是一条路径 `f a ≡ b`{.Agda}，证明这个 `a` 的确映到 `b`。纤维为空，表示 `b` 没有原像；纤维中若有彼此不能通过路径等同的元素，则表示从 `b` 返回 `A` 时存在实质不同的选择。

当每个 `b : B`{.Agda} 上的纤维都[可缩]{.term-ref #contractible}时，每条纤维都有一个中心，纤维中的其他元素都通过路径与它等同。因此，每个 `b` 都可以从 `A` 中恢复，而且恢复结果在路径意义下没有歧义。满足这个条件的映射称为等价；逆向映射与两条往返路径都可以由这些纤维的中心导出。

这里的[类型等价]{.term-ref #type-equivalence}需要与[同构]{.term-intro #type-isomorphism}区分。同构显式给出正向映射、选定的逆向映射和两条逆律。同构可以转换为等价，等价也可以表示为同构；区别在于怎样组织同一份数学信息。构造具体例子时，显式列出映射往往使同构更为方便；立方库则以等价作为搬运类型结构的统一接口，因此本章用 `_≃_`{.Agda} 表述两项小性原理。

`_≃_`{.Agda} 也不只是[逻辑等价]{.term-ref #logical-equivalence}。两个命题逻辑等价，指的是它们之间具有两个方向的蕴含。若 `P` 与 `Q` 的底层类型都满足 `isProp`{.Agda}，这两个方向便足以确定一个类型等价：命题性使所有证明都不可区分，两个复合因而自动满足逆律。对一般类型，两个方向各有一个映射并不能保证它们互逆，所以逻辑等价并不足够。下面的两种用法体现了这个区别：在 `isSmall`{.Agda} 中，两端都是命题，逻辑等价可以提升为类型等价；在 `HPropSmallness`{.Agda} 中，小分类器和 `hProp ℓ`{.Agda} 本身都不是命题，完整的类型等价不可省略。

这样便可以看清三个概念在本书论证中的分工：证明类型等价时常先构造同构，保存和搬运结构时统一使用类型等价，而当两个对象已经位于同一个环境类型中时，最终的比较往往表述为路径。
<!--ja-->
`b` 上の `f` の**[ファイバー]{.term-intro #fiber}**は、次の依存対型です。

<div class="single-line-code"><code>Σ (a : A) (f a ≡ b)</code></div>

ファイバーの要素は二つの成分を持ちます。第一成分は原像の候補 `a : A`{.Agda}、第二成分はその候補が実際に `b` へ写ることを示すパス `f a ≡ b`{.Agda} です。ファイバーが空なら `b` に原像はありません。ファイバーにパスで同一視できない要素があれば、`b` から `A` へ戻る方法に本質的な違いが残っています。

各 `b : B`{.Agda} 上のファイバーが[可縮]{.term-ref #contractible}なら、各ファイバーには中心があり、他のすべての要素はパスによってその中心と等しくなります。したがって、すべての `b` を `A` から復元でき、その復元はパスの意味で曖昧さを残しません。この条件を満たす写像を同値と呼びます。逆写像と二つの往復パスは、各ファイバーの中心から導けます。

この[型同値]{.term-ref #type-equivalence}は[同型]{.term-intro #type-isomorphism}と区別する必要があります。同型は順写像、選ばれた逆写像、二つの逆法則を明示的に与えます。同型は同値へ変換でき、同値も同型として表示できます。違いは、同じ数学的情報をどのように編成するかにあります。具体例を構成するときには、写像を明示する同型が便利なことがあります。一方、Cubical ライブラリは型の構造を運ぶ共通のインターフェースとして同値を用いるため、本章も二つの小ささの原理を `_≃_`{.Agda} で記述します。

`_≃_`{.Agda} は単なる[論理的同値]{.term-ref #logical-equivalence}でもありません。二つの命題の論理的同値が与えるのは、両方向の含意です。`P` と `Q` の基礎型がともに `isProp`{.Agda} を満たすなら、この二つの含意から型同値を構成できます。命題性によってすべての証明が区別できなくなり、二つの合成が自動的に逆法則を満たすからです。一般の型では、両方向の写像があっても互いに逆とは限らないので、それだけでは不十分です。以下の二つの用法は、この違いを表します。`isSmall`{.Agda} では両辺が命題なので、論理的同値を型同値へ高められます。`HPropSmallness`{.Agda} では、小分類子も `hProp ℓ`{.Agda} もそれ自体は命題ではないため、完全な型同値が必要です。

以上の三つの概念は、本書の議論で異なる役割を担います。型同値を証明するときにはまず同型を構成することが多く、構造を保存して運ぶときには型同値を共通の形として用い、二つの対象が同じ型に属するところまで来れば、最後の比較をパスとして述べます。
<!--/-->

<!--en-->
## Being small

Let `P : hProp (ℓ-suc ℓ)`{.Agda}. Its truth content has a representation at level `ℓ` when there is a `Q : hProp ℓ`{.Agda} whose underlying type is equivalent to that of `P`. This pair of data is what it means for `P` to **be small**: the first component chooses `Q`, and the second converts certificates in both directions.

The witness `isSmall P`{.Agda} still belongs to `Type (ℓ-suc ℓ)`{.Agda}. Smallness does not move `P` itself into the lower universe; it supplies a lower representative, and different witnesses may choose different representatives.
<!--zh-->
## 何谓小

设 `P : hProp (ℓ-suc ℓ)`{.Agda}。若存在 `Q : hProp ℓ`{.Agda}，且它的底层类型与 `P` 的底层类型等价，那么 `P` 的真值内容就在层级 `ℓ` 有了表示。这一对数据就是 `P` **是小的**含义：第一分量选出 `Q`，第二分量使两边的证书可以双向转换。

完整见证 `isSmall P`{.Agda} 仍属于 `Type (ℓ-suc ℓ)`{.Agda}。小性并不把 `P` 本身降入低层宇宙，而是为它给出一个低层代表；不同见证也可能选出不同的代表。
<!--ja-->
## 小さいということ

`P : hProp (ℓ-suc ℓ)`{.Agda} とします。基礎型が `P` の基礎型と同値な `Q : hProp ℓ`{.Agda} があれば、`P` の真理内容はレベル `ℓ` に表現を持ちます。この一対のデータを持つことが、`P` が**小さい**という意味です。第一成分は `Q` を選び、第二成分は両側の証明を双方向に変換します。

証拠全体である `isSmall P`{.Agda} は依然として `Type (ℓ-suc ℓ)`{.Agda} に属します。小ささは `P` 自身を低い宇宙へ移すのではなく、低いレベルの代表を与えます。異なる証拠が異なる代表を選んでもかまいません。
<!--/-->

```agda
isSmall : ∀ {ℓ} → hProp (ℓ-suc ℓ) → Type (ℓ-suc ℓ)
isSmall {ℓ} P = Σ[ Q ∈ hProp ℓ ] (⟨ P ⟩ ≃ ⟨ Q ⟩)
```

<!--en-->
## The two interfaces

Smallness concerns one proposition. **Propositional resizing** makes it available uniformly: for every proposition one universe above `ℓ`, it returns a witness that this proposition is small. Thus `Resizing ℓ`{.Agda} is a dependent function type whose input is `P : hProp (ℓ-suc ℓ)`{.Agda} and whose output is `isSmall P`{.Agda}.

Because the input ranges over `hProp (ℓ-suc ℓ)`{.Agda}, resizing itself lies in `Type (ℓ-suc (ℓ-suc ℓ))`{.Agda}. An inhabitant supplies one representative for each `P`, without requiring uniqueness or any further relation among the choices.
<!--zh-->
## 两个接口

小性只涉及一个命题。**命题降级**把它一致地用于任意命题：对高于 `ℓ` 一个宇宙的每个命题，它都返回该命题是小的见证。因此，`Resizing ℓ`{.Agda} 是一个依值函数类型，输入为 `P : hProp (ℓ-suc ℓ)`{.Agda}，输出为 `isSmall P`{.Agda}。

由于输入遍历 `hProp (ℓ-suc ℓ)`{.Agda}，命题降级本身位于 `Type (ℓ-suc (ℓ-suc ℓ))`{.Agda}。它的元素为每个 `P` 给出一个代表，但不要求代表唯一，也不要求这些选择之间另有关系。
<!--ja-->
## 二つのインターフェース

小ささは一つの命題についての性質です。**命題リサイズ**はこれを任意の命題に一様に与えます。レベル `ℓ` より一つ上の宇宙にある命題を受け取るたびに、その命題が小さいことの証拠を返します。したがって `Resizing ℓ`{.Agda} は、入力を `P : hProp (ℓ-suc ℓ)`{.Agda}、出力を `isSmall P`{.Agda} とする依存関数型です。

入力が `hProp (ℓ-suc ℓ)`{.Agda} 全体を動くため、命題リサイズ自身は `Type (ℓ-suc (ℓ-suc ℓ))`{.Agda} に属します。その元は各 `P` に代表を一つ与えますが、代表の一意性も、選択された代表の間の追加の関係も要求しません。
<!--/-->

```agda
Resizing : ∀ ℓ → Type (ℓ-suc (ℓ-suc ℓ))
Resizing ℓ = (P : hProp (ℓ-suc ℓ)) → isSmall P
```

<!--en-->
The second principle concerns the whole proposition universe. A witness of `HPropSmallness ℓ`{.Agda} chooses one type `Ω' : Type ℓ`{.Agda} and an equivalence `Ω' ≃ hProp ℓ`{.Agda}. Thus one small classifier presents all level-`ℓ` propositions at once.

The classifier need not itself be a proposition. Its elements classify propositions through the equivalence. This statement lies in `Type (ℓ-suc ℓ)`{.Agda}, one universe below resizing. The two principles therefore have different shapes, and neither definition claims that one implies the other.
<!--zh-->
第二条原理针对整个命题宇宙。`HPropSmallness ℓ`{.Agda} 的见证选取一个类型 `Ω' : Type ℓ`{.Agda}，并给出等价 `Ω' ≃ hProp ℓ`{.Agda}。于是，一个小分类器便一次呈现了层级 `ℓ` 的所有命题。

分类器本身不必是命题，它的元素通过上述等价分类命题。这条陈述位于 `Type (ℓ-suc ℓ)`{.Agda}，比命题降级低一个宇宙。因此两项原理具有不同的形状，两项定义也都没有声称其中一项蕴含另一项。
<!--ja-->
第二の原理は命題の宇宙全体を扱います。`HPropSmallness ℓ`{.Agda} の証拠は、一つの型 `Ω' : Type ℓ`{.Agda} と同値 `Ω' ≃ hProp ℓ`{.Agda} を与えます。こうして、一つの小分類子がレベル `ℓ` のすべての命題を一度に提示します。

分類子自身が命題である必要はなく、その要素が同値を通して命題を分類します。この主張は `Type (ℓ-suc ℓ)`{.Agda} に属し、命題リサイズより一つ低い宇宙にあります。したがって二つの原理は形が異なり、どちらの定義も一方が他方を含意するとは主張しません。
<!--/-->

```agda
HPropSmallness : ∀ ℓ → Type (ℓ-suc ℓ)
HPropSmallness ℓ = Σ[ Ω' ∈ Type ℓ ] (Ω' ≃ hProp ℓ)
```

<!--en-->
## Combining the two principles

The cumulative hierarchy uses the principles for different axioms: resizing supplies each proposition defining a separated subset with an equivalent representative in the lower universe, while the classifier supplies the size control needed for power set. `Impredicativity ℓ`{.Agda} therefore records both assumptions together. Its two fields contain a `Resizing ℓ`{.Agda} and an `HPropSmallness ℓ`{.Agda}, with no compatibility condition.

The record lies in `Type (ℓ-suc (ℓ-suc ℓ))`{.Agda}, the larger of the levels occupied by its components. Projection recovers either principle independently. The record adds no mathematical strength; it expresses their conjunction as data.
<!--zh-->
## 合并两项原理

累积层级在不同公理中使用这两项原理：命题降级为定义分离子集的每个命题给出低一宇宙中的等价代表，小分类器则为幂集提供所需的尺寸控制。`Impredicativity ℓ`{.Agda} 因而同时记录两项假设；它的两个字段分别包含 `Resizing ℓ`{.Agda} 和 `HPropSmallness ℓ`{.Agda}，二者之间没有相容性条件。

这个 record 位于 `Type (ℓ-suc (ℓ-suc ℓ))`{.Agda}，即两个分量所在层级中较高的一层。投影可以分别取回任一项原理。record 不增加数学强度，只是把二者的合取表示为数据。
<!--ja-->
## 二つの原理をまとめる

累積階層では二つの原理を異なる公理に用います。命題リサイズは、分出する部分集合を定める各命題に、下の宇宙にある同値な代表を与えます。小分類子は冪集合に必要な大きさの制御を与えます。そこで `Impredicativity ℓ`{.Agda} は二つの仮定を同時に記録します。二つのフィールドは `Resizing ℓ`{.Agda} と `HPropSmallness ℓ`{.Agda} をそれぞれ持ち、両者の間に整合条件はありません。

この record は、二つの成分が属するレベルのうち高い方である `Type (ℓ-suc (ℓ-suc ℓ))`{.Agda} に属します。射影すれば、どちらの原理も独立に取り出せます。record は数学的な強さを加えず、二つの原理の連言をデータとして表すだけです。
<!--/-->

```agda
record Impredicativity (ℓ : Level) : Type (ℓ-suc (ℓ-suc ℓ)) where
  field
    resizing       : Resizing ℓ
    hPropSmallness : HPropSmallness ℓ
```

<!--en-->
## Recap

These definitions isolate the size information that predicative universe levels do not provide automatically. Equivalence gives a higher proposition a lower representative with the same truth content; resizing supplies such representatives pointwise, while small classification presents a proposition universe all at once. No inhabitant has been constructed here. The classical chapter derives both principles from excluded middle, after which separation and power set can use them for their distinct purposes.
<!--zh-->
## 小结

这些定义分离出了直谓式宇宙层级不会自动提供的尺寸信息。借助等价，高层命题获得具有相同真值内容的低层代表；命题降级逐点给出这类代表，小分类则一次呈现整个命题宇宙。本章尚未构造这些原理的见证。「经典逻辑的边界」将从排中律导出二者，随后分离与幂集便可分别使用它们。
<!--ja-->
## まとめ

これらの定義は、直謂的な宇宙レベルからは自動的に得られない大きさの情報を切り分けます。同値によって上位の命題は同じ真理内容をもつ低いレベルの代表を得ます。命題リサイズはその代表を各命題に与え、小分類は命題の宇宙全体を一度に提示します。本章では、これらの原理の証拠をまだ構成していません。「古典論理との境界」の章で排中律から両者を導けば、分出と冪集合はそれぞれの目的に応じて用いることができます。
<!--/-->
