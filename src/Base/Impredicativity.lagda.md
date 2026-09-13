<!--en-->
# Impredicativity

In a predicative foundation, propositions form a hierarchy: for each universe level ℓ the type `hProp ℓ` of level-ℓ propositions sits in the next universe up, so the range of **[truth values]{.term-intro #truth-value}** grows as the universes grow. In this book a truth value is a proposition in `hProp`: it records whether a statement is inhabited, rather than supplying a separate Boolean datatype. Nontrivial propositions may therefore be stranded at higher levels with no equivalent among the low ones. This chapter studies two precise ways to control this growth: representing each higher-level proposition by a lower one, and presenting the whole type of level-ℓ propositions by one small classifier.

This chapter develops the vocabulary for that principle precisely. First, a single proposition of level `ℓ-suc ℓ` **is small** when its underlying type is equivalent to the underlying type of some proposition `Q : hProp ℓ`; the equivalence, not a path or a rewrite, is what certifies that `Q` represents the same truth content. Second, two uniform interfaces assert smallness across all propositions at once: **propositional resizing** chooses, proposition by proposition, a lower-level representative for each higher-level proposition, while a small classifier presents the entire type `hProp ℓ` by a single small carrier. Finally a record packages the two interfaces. Nothing here is assumed, and this chapter does not yet construct either interface: the chapter "The classical boundary" constructs both from excluded middle, and the cumulative-hierarchy chapters use them as concrete model fields.
<!--zh-->
# 非直谓性

在直谓式的基础中，命题构成一个层级：对每个宇宙层级 ℓ，`hProp ℓ` 中的层级 ℓ 命题都位于其上一层的宇宙，于是**[真值]{.term-intro #truth-value}**的范围随宇宙一起增长。本书的真值就是 `hProp` 中的命题：它记录一个陈述是否有元，而不是另设一个布尔数据类型。不平凡的命题可能被搁置在高层，在低层没有等价的对应物。本章研究控制这种增长的两种精确方式：逐个用低层命题表示高层命题，以及用一个小分类器呈现整个 ℓ 层命题类型。

本章把这条原理的词汇表述得精确。首先，一个层级为 `ℓ-suc ℓ` 的命题**是小的**，当且仅当其底层类型等价于某个命题 `Q : hProp ℓ` 的底层类型；正是等价 (而非路径或重写) 证明 `Q` 代表相同的真值内容。其次，两个接口一齐对所有命题一致地断言小性：**命题降层**逐命题为每个高层命题选取低层代表；而小分类器则用单个小的载体呈现整个类型 `hProp ℓ`。最后用一个 record 把两个接口打包。这里不作任何假设，本章尚未给出这两个接口的构造：「经典逻辑的边界」一章将从排中律构造二者，累积层级诸章把它们用作具体的模型字段。
<!--ja-->
# 非可述性

直謂的な基礎では命題は階層をなします。宇宙レベル ℓ ごとに、レベル ℓ の命題の型 `hProp ℓ` はその一つ上の宇宙に住むため、**[真理値]{.term-intro #truth-value}**の範囲は宇宙とともに増えます。本書の真理値は `hProp` の命題そのものです。これは文に要素があるかどうかを記録するもので、別のブール型を設けるものではありません。自明でない命題が高いレベルに取り残され、低いレベルに同値な対応物を持たない可能性が生じます。本章では、この増大を制御する二つの正確な方法を扱います。上位の命題を一つずつ下位の命題で表すことと、レベル ℓ の命題の型全体を一つの小分類子で提示することです。

本章ではこの原理の語彙を正確に整えます。まず、レベル `ℓ-suc ℓ` の一つの命題が**小さい**とは、その基礎型が何らかの命題 `Q : hProp ℓ` の基礎型と同値であることです。`Q` が同じ真理内容を代表することを証するのは、パスでも書き換えでもなく、この同値です。次に、小ささをすべての命題に一様に主張する二つのインターフェースを示します。**命題リサイズ**は命題ごとに上位命題の下位レベル代表を選ぶ原理であり、小分類子は型 `hProp ℓ` 全体を一つの小さな台で提示する原理です。最後に、両者を一つの record にまとめます。ここでは何も仮定せず、本章ではまだ、どちらのインターフェースの構成も与えません。次の章が排中律から両者を構成し、累積階層の諸章が具体的なモデルの構成要素として利用します。
<!--/-->

<!--en-->
Every smallness statement in this chapter compares two propositions through an equivalence of underlying types. An equivalence `A ≃ B` gives an invertible correspondence between the two types. For propositions, such a correspondence preserves whether they are inhabited, so the large and small propositions have the same truth content; the definition claims this equivalence of underlying types, not literal identity of their elements.
<!--zh-->
本章中每一条小性陈述都通过底层类型之间的等价来比较两个命题。等价 `A ≃ B` 给出两个类型之间可逆的对应。对命题而言，这样的对应保持其是否有元素，因而大命题与小命题具有相同的真值内容；定义断言的是底层类型等价，而不是二者元素逐字相同。
<!--ja-->
本章の小ささの主張は、すべて基礎型の間の同値を通して二つの命題を比較します。同値 `A ≃ B` は二つの型の間に可逆な対応を与えます。命題については、この対応が要素をもつかどうかを保存するので、大きな命題と小さな命題は同じ真理内容をもちます。定義が主張するのは基礎型の同値であり、両者の要素が文字どおり同一だということではありません。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

module Base.Impredicativity where

open import Base.Prelude
open import Cubical.Foundations.Equiv using ( _≃_ )
```

<!--en-->
## Being small

A proposition `P : hProp (ℓ-suc ℓ)` may be too large to speak about at level ℓ, yet its truth content could still be carried by a proposition that fits in `hProp ℓ`. We call `P` **small** exactly when this happens: there is a `Q : hProp ℓ` whose underlying type is equivalent to `⟨ P ⟩`. The witness is explicit data. An inhabitant of `isSmall P` is a pair: the first component is the small stand-in `Q`, the second is an equivalence of underlying types `⟨ P ⟩ ≃ ⟨ Q ⟩`.

The level bookkeeping is worth reading off the type. Since `P` lives at level `ℓ-suc ℓ`, the pair recording its smallness also lives there: `isSmall P` is a type in `Type (ℓ-suc ℓ)`. So asserting that a level-`ℓ-suc ℓ` proposition is small is itself a statement at level `ℓ-suc ℓ`; smallness of `P` does not collapse to level ℓ.
<!--zh-->
## 何谓小

命题 `P : hProp (ℓ-suc ℓ)` 也许大到无法在层级 ℓ 上讨论，但它的真值内容仍可能由一个装进 `hProp ℓ` 的命题承担。我们恰在这种情形发生时称 `P` **是小的**：存在 `Q : hProp ℓ`，其底层类型与 `⟨ P ⟩` 等价。这个见证是显式的数据。`isSmall P` 的元素是一个对子：第一分量是小替身 `Q`，第二分量是底层类型间的等价 `⟨ P ⟩ ≃ ⟨ Q ⟩`。

层级记账值得从类型上直接读出。由于 `P` 住在层级 `ℓ-suc ℓ`，记录其小性的对子也住在那里：`isSmall P` 是 `Type (ℓ-suc ℓ)` 中的类型。因此断言一个 `ℓ-suc ℓ` 层级命题是小的，本身就是 `ℓ-suc ℓ` 层级的陈述；`P` 的小性并不会塌缩到层级 ℓ。
<!--ja-->
## 小さいということ

命題 `P : hProp (ℓ-suc ℓ)` はレベル ℓ で扱うには大きすぎるかもしれませんが、その真理内容は `hProp ℓ` に収まる命題が担えるかもしれません。まさにこれが起きるとき、`P` は**小さい**といいます。つまり、基礎型が `⟨ P ⟩` と同値であるような `Q : hProp ℓ` が存在するのです。証拠は明示的なデータです。`isSmall P` の元は対であり、第一成分が小さな代替物 `Q`、第二成分が基礎型の間の同値 `⟨ P ⟩ ≃ ⟨ Q ⟩` です。

レベルの帳簿は型からそのまま読み取れます。`P` はレベル `ℓ-suc ℓ` に住むので、その小ささを記録する対もそこに住みます。つまり `isSmall P` は `Type (ℓ-suc ℓ)` の型です。したがって、レベル `ℓ-suc ℓ` の命題が小さいと主張すること自体が、レベル `ℓ-suc ℓ` の文です。`P` の小ささがレベル ℓ に落ちることはありません。
<!--/-->

<!--en-->
The definition quantifies over the level `ℓ` implicitly, so `isSmall` applies to a proposition at any level `ℓ-suc ℓ` without naming the level. For a fixed `P`, an inhabitant of `isSmall P` chooses the lower-level proposition `Q` and supplies the equivalence of underlying types. Only this existence of data is asserted: the definition does not exhibit a path between `P` and `Q` as propositions, and it does not transport `P` itself into the lower universe. Different inhabitants of `isSmall P` may pick different `Q`, and nothing here says the choice is in any way forced.
<!--zh-->
定义对层级 `ℓ` 作隐式量化，因此 `isSmall` 适用于任意层级 `ℓ-suc ℓ` 的命题而不必指名层级。对固定的 `P`，`isSmall P` 的元素选取低层命题 `Q`，并给出底层类型间的等价。这里只断言这样的数据存在：定义既不给出作为命题的 `P` 与 `Q` 之间的路径，也不把 `P` 本身传输到较低宇宙。`isSmall P` 的不同元素可能选取不同的 `Q`，这里没有任何内容说明该选择以任何方式被强制。
<!--ja-->
定義はレベル `ℓ` を暗黙に量化するので、`isSmall` はレベルを指名せずとも任意のレベル `ℓ-suc ℓ` の命題に適用できます。固定した `P` に対する `isSmall P` の元は、低レベルの命題 `Q` を選び、基礎型の間の同値を与えます。断言されるのはこのデータの存在だけです。命題としての `P` と `Q` の間のパスを示すことも、`P` 自身を低い宇宙へ輸送することもありません。`isSmall P` の異なる元は異なる `Q` を選ぶかもしれません。その選択が何らかの形で強制されることを、ここでは述べません。
<!--/-->

```agda
isSmall : ∀ {ℓ} → hProp (ℓ-suc ℓ) → Type (ℓ-suc ℓ)
isSmall {ℓ} P = Σ[ Q ∈ hProp ℓ ] (⟨ P ⟩ ≃ ⟨ Q ⟩)
```

<!--en-->
## The two interfaces

`isSmall` speaks about one proposition at a time. Two uniform principles extend it over all propositions at a level, and they differ in what they quantify over. **Propositional resizing** `Resizing ℓ` is the pointwise principle: it says that every proposition one universe up is small, each with its own equivalent representative in `hProp ℓ`. The next section's `HPropSmallness ℓ` is the global principle: instead of choosing representatives one by one, it asks for one small type that classifies all level-ℓ propositions at once. The two shapes of claim are sharply different and are kept apart throughout this development.
<!--zh-->
## 两个接口

`isSmall` 一次只谈论一个命题。两条统一原理把它扩展到某个层级上的所有命题，而二者的量化对象不同。**命题降层** `Resizing ℓ` 是逐点的原理：它说高一层的每个命题都是小的，各自在 `hProp ℓ` 中有自己的等价代表。下一节的 `HPropSmallness ℓ` 是全局的原理：它不逐个挑选代表，而是要求一个能同时分类所有 ℓ 层级命题的小类型。这两种断言形状截然不同，在本开发中始终分开对待。
<!--ja-->
## 二つのインターフェース

`isSmall` は一度に一つの命題について語ります。これをあるレベルのすべての命題にわたって一様に拡げる原理が二つあり、量化の対象が異なります。**命題リサイズ** `Resizing ℓ` は点ごとの原理です。一つ上の宇宙のすべての命題は小さく、それぞれが `hProp ℓ` の中に自分専用の同値な代表を持つ、という主張です。次節の `HPropSmallness ℓ` は大域的な原理です。代表を一つずつ選ぶのではなく、レベル ℓ の命題すべてを一度に分類する一つの小さな型を要求します。この二つの主張の形はまったく異なり、本開発を通じて区別して扱われます。
<!--/-->

<!--en-->
Read `Resizing ℓ` as a function type. An inhabitant takes any `P : hProp (ℓ-suc ℓ)` and returns an element of `isSmall P`, that is, a lower-level representative plus its equivalence. Because it quantifies over `hProp (ℓ-suc ℓ)`, which lives in `Type (ℓ-suc (ℓ-suc ℓ))`, the statement itself has type `Type (ℓ-suc (ℓ-suc ℓ))` and is asserted one level at a time, exactly like `LEM ℓ`. The inhabitant is data: one witness per proposition, with no claim that a witness is unique or that representatives chosen for different propositions satisfy additional coherence laws.
<!--zh-->
把 `Resizing ℓ` 读作函数类型。它的元素取任意 `P : hProp (ℓ-suc ℓ)`，返回 `isSmall P` 的一个元素，即一个低层代表连同其等价。由于它对住在 `Type (ℓ-suc (ℓ-suc ℓ))` 的 `hProp (ℓ-suc ℓ)` 量化，该陈述自身的类型就是 `Type (ℓ-suc (ℓ-suc ℓ))`，并且与 `LEM ℓ` 一样逐层级陈述。其元素是数据：每个命题一份见证，不声称见证唯一，也不要求为不同命题选取的代表满足额外的相容律。
<!--ja-->
`Resizing ℓ` は関数型として読みます。その元は任意の `P : hProp (ℓ-suc ℓ)` を受け取り、`isSmall P` の元、すなわち低レベルの代表とその同値を返します。`Type (ℓ-suc (ℓ-suc ℓ))` に住む `hProp (ℓ-suc ℓ)` 上で量化するため、この主張自身の型は `Type (ℓ-suc (ℓ-suc ℓ))` になり、`LEM ℓ` と同じく一レベルずつ述べられます。その元はデータであり、命題ごとに一つの証拠を与えます。証拠の一意性も、異なる命題に選んだ代表が追加の整合条件を満たすことも主張しません。
<!--/-->

```agda
Resizing : ∀ ℓ → Type (ℓ-suc (ℓ-suc ℓ))
Resizing ℓ = (P : hProp (ℓ-suc ℓ)) → isSmall P
```

<!--en-->
The second interface speaks not of each proposition but of their totality. The type of level-ℓ truth values, `hProp ℓ`, lives one universe up in `Type (ℓ-suc ℓ)`. `HPropSmallness ℓ` is the request for exactly such an object: a **small** type in `Type ℓ` equivalent to all of `hProp ℓ` at once, a small classifier of propositions.
<!--zh-->
第二个接口针对的不是单个命题，而是它们的总体。ℓ 层级真值的类型 `hProp ℓ` 住在上一层宇宙 `Type (ℓ-suc ℓ)` 中。`HPropSmallness ℓ` 恰是对这种对象的要求：一个 `Type ℓ` 中的**小**类型，与整个 `hProp ℓ` 同时等价，即命题的小分类器。
<!--ja-->
第二のインターフェースは個々の命題ではなくその全体について語ります。レベル ℓ の真理値の型 `hProp ℓ` は一つ上の宇宙 `Type (ℓ-suc ℓ)` に住む。`HPropSmallness ℓ` はまさにそのような対象への要求です。`Type ℓ` の**小さな**型であって、`hProp ℓ` 全体と一度に同値なもの、命題の小分類子です。
<!--/-->

<!--en-->
The pair structure makes the claim precise: the first component `Ω'` is an arbitrary type in `Type ℓ`, and the second is an equivalence `Ω' ≃ hProp ℓ` onto the whole type of level-ℓ propositions. Since the statement quantifies over a single `Type ℓ` together with an equivalence, `HPropSmallness ℓ` lives in `Type (ℓ-suc ℓ)`, one level lower than `Resizing ℓ`. The shapes differ: resizing assigns a lower representative to each higher proposition separately, while here one small carrier presents the entire totality. Nothing in this definition relates the two principles; whether one implies the other is a separate question, and this module does not address it.
<!--zh-->
对子结构使断言精确：第一分量 `Ω'` 是 `Type ℓ` 中的任意类型，第二分量是到整个 ℓ 层级命题类型上的等价 `Ω' ≃ hProp ℓ`。由于这里只对单个 `Type ℓ` 连同一个等价量化，`HPropSmallness ℓ` 处于 `Type (ℓ-suc ℓ)`，比 `Resizing ℓ` 低一层。二者的形状不同：命题降层为每个高层命题各自指派低层代表，而这里用一个小载体呈现整个总体。本定义没有把两项原理联系起来；一项是否蕴含另一项是另一个问题，本模块不予讨论。
<!--ja-->
対の構造が主張を正確にします。第一成分 `Ω'` は `Type ℓ` の任意の型であり、第二成分はレベル ℓ の命題の型全体への同値 `Ω' ≃ hProp ℓ` です。単一の `Type ℓ` と一つの同値について量化するだけなので、`HPropSmallness ℓ` は `Type (ℓ-suc ℓ)` に住み、`Resizing ℓ` より一つ低いレベルです。形も異なります。リサイズは上位の各命題に個別の低レベル代表を割り当てますが、こちらは一つの小さな台で全体を提示します。この定義は二つの原理を結びつけません。一方が他方を含意するかは別の問題であり、このモジュールでは扱いません。
<!--/-->

```agda
HPropSmallness : ∀ ℓ → Type (ℓ-suc ℓ)
HPropSmallness ℓ = Σ[ Ω' ∈ Type ℓ ] (Ω' ≃ hProp ℓ)
```

<!--en-->
## Combining the two principles

Downstream chapters that build models want both uniform principles available at once, so this chapter packages them. `Impredicativity ℓ`{.Agda} is a record whose two fields are the two principles at the same level ℓ. Holding a value of this record type is exactly holding a `Resizing ℓ` and an `HPropSmallness ℓ` together; the record itself asserts no implication between its fields and constructs neither one. Its universe is `Type (ℓ-suc (ℓ-suc ℓ))`, which is what the `Resizing ℓ` field requires.
<!--zh-->
## 合并两项原理

后续构造模型的章节希望两条统一原理同时可用，因此本章把它们打包。`Impredicativity ℓ`{.Agda} 是一个 record，其两个字段就是同一层级 ℓ 上的两条原理。持有这个 record 类型的一个值，恰好等价于同时持有一个 `Resizing ℓ` 和一个 `HPropSmallness ℓ`；record 本身不断言两字段之间存在蕴含关系，也不构造其中任何一项。它的宇宙是 `Type (ℓ-suc (ℓ-suc ℓ))`，这正是字段 `Resizing ℓ` 所需要的。
<!--ja-->
## 二つの原理をまとめる

後の章でモデルを構成するときには、二つの大域的原理を同時に使えることが望まれます。そこで本章は両者をまとめます。`Impredicativity ℓ`{.Agda} は record であり、その二つのフィールドが同じレベル ℓ の二つの原理です。この record 型の値を持つことは、`Resizing ℓ` と `HPropSmallness ℓ` を同時に持つことに他なりません。record 自身はフィールド間の含意を主張せず、いずれの原理も構成しません。その宇宙は `Type (ℓ-suc (ℓ-suc ℓ))` であり、これは `Resizing ℓ` フィールドが要求するものです。
<!--/-->

<!--en-->
The record has exactly two fields, matching the two definitions above: `resizing` of type `Resizing ℓ` and `hPropSmallness` of type `HPropSmallness ℓ`. Projecting a value of `Impredicativity ℓ` therefore recovers either principle independently, at the same level ℓ. No other content is packaged: the record is pure conjunction of the two interfaces.
<!--zh-->
这个 record 恰有两个字段，与上面的两个定义对应：类型为 `Resizing ℓ` 的 `resizing`，以及类型为 `HPropSmallness ℓ` 的 `hPropSmallness`。因此，从 `Impredicativity ℓ` 的一个值可以在同一层级 ℓ 上分别投影出任一项原理。record 不打包其他内容：它就是两个接口的纯粹合取。
<!--ja-->
この record には上の二つの定義に対応するフィールドがちょうど二つあります。型 `Resizing ℓ` の `resizing` と、型 `HPropSmallness ℓ` の `hPropSmallness` です。したがって、`Impredicativity ℓ` の値から各原理を同じレベル ℓ で別々に射影できます。それ以外の内容は包装されていません。record は二つのインターフェースの純粋な連言です。
<!--/-->

```agda
record Impredicativity (ℓ : Level) : Type (ℓ-suc (ℓ-suc ℓ)) where
  field
    resizing       : Resizing ℓ
    hPropSmallness : HPropSmallness ℓ
```

<!--en-->
## Recap

The chapter's vocabulary reduces impredicativity to equivalences of underlying types. A proposition `P : hProp (ℓ-suc ℓ)` **is small** (`isSmall`) when `⟨ P ⟩` is equivalent to `⟨ Q ⟩` for some `Q : hProp ℓ`, with the equivalence supplied as data. **Propositional resizing** `Resizing ℓ` chooses such data separately for every proposition one universe up, so it lives in `Type (ℓ-suc (ℓ-suc ℓ))`. **`HPropSmallness ℓ`** presents the entire type `hProp ℓ` by one small classifier `Ω' : Type ℓ` with `Ω' ≃ hProp ℓ`, so it lives one level lower, in `Type (ℓ-suc ℓ)`. `Impredicativity` records the two principles as independent fields and adds nothing beyond them. This module defines these statements but supplies no inhabitant of any of them; the chapter "The classical boundary" derives inhabitants from excluded middle.
<!--zh-->
## 小结

本章的词汇把非直谓性化归为底层类型之间的等价。命题 `P : hProp (ℓ-suc ℓ)` **是小的** (`isSmall`)，指对某个 `Q : hProp ℓ` 有 `⟨ P ⟩ ≃ ⟨ Q ⟩`，且等价作为数据给出。**命题降层** `Resizing ℓ` 为高一层宇宙中的每个命题分别选取这类数据，因此它处于 `Type (ℓ-suc (ℓ-suc ℓ))`。**`HPropSmallness ℓ`** 用一个小分类器 `Ω' : Type ℓ` 连同 `Ω' ≃ hProp ℓ` 呈现整个类型 `hProp ℓ`，因此它低一层，处于 `Type (ℓ-suc ℓ)`。`Impredicativity` 把两项原理记为独立字段，除此之外不添加任何内容。本模块定义这些陈述，但不提供其中任何一项的元素；「经典逻辑的边界」一章将从排中律导出相应的元素。
<!--ja-->
## まとめ

本章の語彙は、非可述性を基礎型の間の同値へ帰着させます。命題 `P : hProp (ℓ-suc ℓ)` が**小さい** (`isSmall`) とは、ある `Q : hProp ℓ` に対して `⟨ P ⟩ ≃ ⟨ Q ⟩` が成り立つことで、同値はデータとして与えられます。**命題リサイズ** `Resizing ℓ` は一つ上の宇宙の各命題にこのデータを個別に選ばせるものなので、`Type (ℓ-suc (ℓ-suc ℓ))` に住みます。**`HPropSmallness ℓ`** は小分類子 `Ω' : Type ℓ` と `Ω' ≃ hProp ℓ` によって型 `hProp ℓ` 全体を提示するものなので、一段低い `Type (ℓ-suc ℓ)` に住みます。`Impredicativity` は二つの原理を独立なフィールドとして記録し、それ以上のものは加えません。このモジュールはこれらの主張を定義しますが、いずれの元も与えません。「古典論理との境界」の章では排中律から元を導きます。
<!--/-->
