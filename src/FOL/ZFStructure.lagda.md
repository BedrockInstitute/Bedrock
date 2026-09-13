<!--en-->
# Structures

A first-order language about sets has two primitive predicates: equality and membership. To interpret it, we must choose what its variables range over and what those two predicates mean there. A `ZFStructure`{.Agda} packages exactly this data: a carrier of "sets", together with proposition-valued interpretations of equality and membership. The record demands that the carrier be an h-set and nothing more; no ZF axiom is built in.

Because both relations take values in `hProp`{.Agda}, each atomic statement has an underlying type whose inhabitants are its proofs. A class over the carrier can therefore be used to cut out a smaller structure: `Transitive`{.Agda} expresses that members of members of a class stay in the class, and the restriction `𝒮 ↾ M` turns the class into the carrier of a new structure of dependent pairs. Since the membership fibers are propositions, that pair carrier is again an h-set, and equality of first projections already determines equality of the pairs.

Three membership notations must be kept apart throughout: the host-level class membership `∈ᶜ`{.Agda}, which tests whether a carrier element satisfies a predicate `M`; the proposition-valued structure membership `∈ˢ`{.Agda}; and the object-language membership symbol `∈̇`{.Agda} introduced in "The object language", which is only given meaning once a structure interprets it.
<!--zh-->
# 结构

关于集合的一阶语言有两个初始谓词：等词与隶属。要解释它，就必须选定变量的取值范围，以及这两个谓词在那里分别指什么。`ZFStructure`{.Agda} 正是打包这些数据：一个由「集合」组成的载体，加上等词与隶属的命题值解释。这个 record 只要求载体是 h-集合，别无其他；其中不内置任何 ZF 公理。

两个关系都取值于 `hProp`{.Agda}，因此每条原子陈述都有一个底层类型，其元素就是该陈述的证明。载体上的类也因而可以用来裁出较小的结构：`Transitive`{.Agda} 表达类的元素之元素仍留在类中，限制 `𝒮 ↾ M` 则把类变成一个由依值对组成的新结构的载体。由于各隶属纤维都是命题，这个对载体仍是 h-集合，且第一投影的相等已经决定整个对的相等。

全章要区分三种隶属记号：宿主层的类隶属 `∈ᶜ`{.Agda}，检验载体元素是否满足谓词 `M`；取命题值的结构隶属 `∈ˢ`{.Agda}；以及「对象语言」一章语法中的隶属符号 `∈̇`{.Agda}，只有在结构给出解释之后它才有意义。
<!--ja-->
# 構造

集合についての一階言語には、等号と所属という二つの原始述語があります。これを解釈するには、変数が何を渡り歩くかを定め、その二つの述語がそこで何を意味するかを指定しなければなりません。`ZFStructure`{.Agda} はまさにこのデータをまとめます。すなわち「集合」からなる台と、等号と所属の命題値の解釈です。レコードが要求するのは台が h-集合であることだけで、ZF の公理は組み込まれていません。

二つの関係はどちらも `hProp`{.Agda} に値を取るので、各原子文には証明を要素とする基礎型があります。台の上のクラスは、それによってより小さな構造を切り出すのに使えます。`Transitive`{.Agda} はクラスの要素の要素が再びそのクラスに属することを表し、制限 `𝒮 ↾ M` はクラスを依存対からなる新しい構造の台に変えます。所属の各ファイバーが命題であるため、この対の台は再び h-集合であり、第一射影の等しさだけで対全体の等しさが定まります。

全章を通して三つの所属の記法を区別しなければなりません。ホストレベルのクラス所属 `∈ᶜ`{.Agda} は、台の要素が述語 `M` を満たすかを調べます。構造の所属 `∈ˢ`{.Agda} は命題に値を持つフィールドです。そして「対象言語」の章の構文にある対象言語の所属記号 `∈̇`{.Agda} は、構造が解釈を与えて初めて意味を持ちます。
<!--/-->

<!--en-->
Membership appears on three distinct levels, and the notation keeps them apart. At the host level, a class is a predicate `M` valued in `hProp`{.Agda}, and `x ∈ᶜ M` is the underlying proposition `⟨ M x ⟩`{.Agda}: a type witnessing that `x` satisfies the predicate. This is a relation between a carrier element and a predicate, not between two sets. At the structure level, `x ∈ˢ y` is a proposition about two carrier elements. The object level belongs to the syntax introduced in "The object language", where `∈̇` is a mere symbol awaiting interpretation.
<!--zh-->
隶属出现在三个不同的层面上，记法把它们彼此分开。在宿主层，类是取值于 `hProp`{.Agda} 的谓词 `M`，`x ∈ᶜ M` 就是底层命题 `⟨ M x ⟩`{.Agda}：一个见证 `x` 满足该谓词的类型。这是载体元素与谓词之间的关系，不是两个集合之间的关系。在结构层，`x ∈ˢ y` 是关于两个载体元素的命题。对象层属于「对象语言」一章的语法，那里的 `∈̇` 只是一个等待解释的符号。
<!--ja-->
所属は三つの異なる層に現れ、記法がそれらを区別します。ホストレベルでは、クラスは `hProp`{.Agda} 値の述語 `M` であり、`x ∈ᶜ M` は基底の命題 `⟨ M x ⟩`{.Agda}、つまり `x` が述語を満たすことを証拠立てる型です。これは台の要素と述語の間の関係であって、二つの集合の間の関係ではありません。構造レベルでは、`x ∈ˢ y` が二つの台の要素についての命題です。対象レベルは「対象言語」の章の構文に属し、そこの `∈̇` は解釈を待つ単なる記号です。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

module FOL.ZFStructure where

open import Base.Prelude
```

<!--en-->
The relations of a structure are propositions, so their underlying types may be inhabited by proofs. Gathering the carrier elements that satisfy a class forms a dependent pair type. The carrier `S` being an h-set does not automatically make such a pair type an h-set; what saves it is that each fiber, the membership evidence at a fixed element, is a proposition, so no two distinct proofs can separate otherwise equal pairs.
<!--zh-->
结构中的关系是命题，因此可以用证明占据其底层类型。把满足一个类的载体元素汇集起来，便得到依值对类型。载体 `S` 是 h-集合并不自动保证这样的对类型也是 h-集合；关键在于每个纤维，也就是固定元素处的隶属证据，都是命题，因此不会有两组不同的证明把本应相等的对拆开。
<!--ja-->
構造の関係は命題なので、その基礎型を証明によって満たせます。クラスを満たす台の要素を集めると、依存対の型が得られます。台 `S` が h-集合でも、そのような対の型が h-集合になるとは限りません。これを保証するのは、各ファイバー、すなわち固定した要素での所属の証拠が命題であることで、異なる二組の証拠が本来等しいはずの対を引き裂くことはありません。
<!--/-->

```agda
open import Cubical.Foundations.HLevels using ( isSetΣSndProp )
```

<!--en-->
Restricting a structure to a class therefore rests on a general principle about dependent pairs. A pair consists of a first projection together with a second component whose type depends on the first. When that second component is proposition-valued, the pair carries no information beyond its first projection up to equality: if `fst a ≡ fst b`, then already `a ≡ b`. The chapter closes with a lemma, `↾-reflects`{.Agda}, recording this direction for the restricted carrier.
<!--zh-->
因此，把结构限制到一个类，依赖的是关于依值对的一个一般原理。对由第一投影和类型依赖于第一投影的第二分量组成。当第二分量取命题值时，就相等而言，对所携带的信息不超出第一投影：若 `fst a ≡ fst b`，则已经有 `a ≡ b`。本章以引理 `↾-reflects`{.Agda} 收尾，为限制载体记录这个方向。
<!--ja-->
したがって、構造をクラスへ制限することは、依存対に関する一般的な原理に依拠します。対は第一射影と、その型が第一射影に依存する第二成分からなります。第二成分が命題値であれば、等しさに関して対が第一射影を超える情報を持つことはありません。つまり `fst a ≡ fst b` なら、すでに `a ≡ b` です。本章は最後に補題 `↾-reflects`{.Agda} で、制限された台についてのこの向きを記録します。
<!--/-->

```agda
open import Cubical.Data.Sigma using ( Σ≡Prop )
```

<!--en-->
## The record

Why should equality of sets be a field rather than the host's fixed path equality? Because the language of set theory treats `=` and `∈` as primitive symbols, and a structure is precisely a choice of meaning for them. Two carrier elements may be equal according to the structure even when they are distinct as inhabitants of the host type. Making `≈ˢ` and `∈ˢ` proposition-valued fields states exactly what the structure supplies; the record imposes no compatibility laws between the two relations.

The conventions are book-wide: script `𝒮` stands for a structure, `S` for its carrier, and `x`, `y`, `z` for carrier elements, the "sets" the language speaks of. The superscript `ˢ` marks a symbol as a **field of the structure at hand**, and the membership family on the page now has one glyph per layer: the library's `∈` for the host, `∈ˢ` for the structure, and the object-language symbol `∈̇` for the syntax.

The record is deliberately bare model-theoretic data. It requires the carrier to be an h-set and gives the two truth-valued relations; it asserts no extensionality, well-foundedness, or any other ZF axiom. Those belong to the later model chapters, where they appear as further fields.
<!--zh-->
## 结构的 record

为什么集合的等词应当是字段，而不是直接采用宿主中的路径相等？因为集合论语言把 `=` 与 `∈` 当作初始符号，而结构正是对它们意义的一次选定。两个载体元素即使作为宿主类型的元素并不相同，也可能被结构判为相等。把 `≈ˢ` 与 `∈ˢ` 做成取命题值的字段，准确写出了结构所提供的数据；这个 record 不对两种关系施加任何相容性定律。

约定全书通用：花体 `𝒮` 代表结构，`S` 代表其载体，`x`、`y`、`z` 代表载体元素，即这门语言所谈的「集合」。上标 `ˢ` 标示一个符号是**当前结构的字段**，纸面上的隶属记号一族已一字一层：库的 `∈` 表示宿主，`∈ˢ` 表示结构，对象语言中的 `∈̇` 表示语法。

这个 record 刻意只记录裸的模型论数据：要求载体是 h-集合，并给出两个命题值关系；不主张外延性、良基性或任何其他 ZF 公理。那些属于后文的模型诸章，在那里成为模型的进一步字段。
<!--ja-->
## 構造の record

集合の等号は、ホストのパス等式をそのまま使わず、なぜフィールドとして与えるのでしょうか。集合論の言語は `=` と `∈` を原始記号として扱い、構造とはそれらの意味の選択にほかなりません。二つの台の要素は、ホスト型の要素としては異なっていても、構造には等しいとされることがあります。`≈ˢ` と `∈ˢ` を命題値のフィールドにすることで、構造が実際に与えるデータを正確に表します。このレコードは二つの関係の間にいかなる整合性の法則も課しません。

約束は本書全体で共通です。筆記体の `𝒮` は構造を、`S` はその台を、`x`、`y`、`z` は台の要素、すなわちこの言語が語る「集合」を表します。上付きの `ˢ` は、その記号が**当該構造のフィールド**であることの印で、紙面上の所属記号の族はすでに一字一層に分かれています。ライブラリの `∈` がホストを、`∈ˢ` が構造を、対象言語の `∈̇` が構文を表します。

このレコードは、あえて素のモデル論的データだけを記録します。台が h-集合であることを要求し、二つの真理値関係を与えますが、外延性や正則性、その他の ZF 公理は一切主張しません。それらは後のモデル諸章に属し、そこでモデルのさらなるフィールドとして現れます。
<!--/-->

<!--en-->
The carrier `S` is an ordinary type at level `ℓ`, and the field `isSetS` asks that it be an h-set: its equality types are propositions. This is the only constraint on what the language's "sets" may be. The two relation fields take values in `hProp ℓ`{.Agda}. Since both `S : Type ℓ`{.Agda} and `hProp ℓ`{.Agda} live one universe up, the whole record has type `Type (ℓ-suc ℓ)`{.Agda}.
<!--zh-->
载体 `S` 是层级 `ℓ` 上的普通类型，字段 `isSetS` 要求它是 h-集合：其相等类型都是命题。这是对语言中「集合」可以是什么的唯一约束。两个关系字段取值于 `hProp ℓ`{.Agda}。由于 `S : Type ℓ`{.Agda} 与 `hProp ℓ`{.Agda} 都位于高一层宇宙，整个 record 的类型是 `Type (ℓ-suc ℓ)`{.Agda}。
<!--ja-->
台 `S` はレベル `ℓ` の通常の型で、フィールド `isSetS` はそれが h-集合であること、つまり等式の型がすべて命題であることを要求します。これが、この言語の「集合」となりうるものに対する唯一の制約です。二つの関係フィールドは `hProp ℓ`{.Agda} に値を取ります。`S : Type ℓ`{.Agda} と `hProp ℓ`{.Agda} はどちらも一つ上の宇宙に住むため、レコード全体の型は `Type (ℓ-suc ℓ)`{.Agda} です。
<!--/-->

```agda
record ZFStructure (ℓ : Level) : Type (ℓ-suc ℓ) where
  field
    S         : Type ℓ
    isSetS    : isSet S
```

<!--en-->
The two relation fields give the structure's equality `≈ˢ` and membership `∈ˢ`, each a function `S → S → hProp ℓ`{.Agda}. Thus `x ∈ˢ y` is a proposition about two carrier elements. The record ends here: the carrier and two relations are data, the h-set condition is a constraint, and no set-theoretic axiom is imposed.
<!--zh-->
两个关系字段给出结构的等词 `≈ˢ` 与隶属 `∈ˢ`，都是 `S → S → hProp ℓ`{.Agda} 型的函数。因此，`x ∈ˢ y` 是关于两个载体元素的命题。record 到此为止：载体与两个关系是数据，h-集合性是约束，并未施加集合论公理。
<!--ja-->
二つの関係フィールドは構造の等号 `≈ˢ` と所属 `∈ˢ` を与え、いずれも `S → S → hProp ℓ`{.Agda} 型の関数です。したがって `x ∈ˢ y` は二つの台の要素についての命題です。レコードはここで終わり、台と二つの関係がデータ、h-集合性が制約であり、集合論の公理は課されません。
<!--/-->

```agda
    _≈ˢ_ _∈ˢ_ : S → S → hProp ℓ

  infix 20 _≈ˢ_ _∈ˢ_
```

<!--en-->
The structure equality `≈ˢ` is a field rather than the host's path equality, so an arbitrary structure supplies its own proposition-valued interpretations of equality and membership, with no compatibility laws imposed by the record.

## The propositional side

Every structural membership proposition has an underlying type. The notation `x ∈ᵗ y` names exactly `⟨ x ∈ˢ y ⟩`{.Agda}. This Type-valued reading is what lets later definitions use a proof of membership and collect class members into a dependent pair. The module `hPropStructure`{.Agda} adds this notation on top of the structure's fields.
<!--zh-->
结构等词 `≈ˢ` 是字段，而不是宿主的路径相等，因此任意结构都分别提供自己的真值等词解释与成员解释，record 不施加任何相容性定律。

## 命题侧

每个结构隶属命题都有底层类型。记号 `x ∈ᵗ y` 所指的恰是 `⟨ x ∈ˢ y ⟩`{.Agda}。正是这个 Type 值读法，让后续定义能够使用隶属的证明，并把类的成员收集成依值对。模块 `hPropStructure`{.Agda} 在结构字段之上加入这个记号。
<!--ja-->
構造の等号 `≈ˢ` は、ホスト言語のパス等式ではなくフィールドです。したがって、任意の構造は等号と所属についてそれぞれ真理値を返す解釈を与えますが、レコードは整合性の法則を課しません。

## 命題として読む

構造の所属を表す各命題には基礎型があります。記法 `x ∈ᵗ y` は、ちょうど `⟨ x ∈ˢ y ⟩`{.Agda} を表します。この Type 値の読み方により、後続の定義は所属の証明を使い、クラスの要素を依存対に集められます。モジュール `hPropStructure`{.Agda} は構造のフィールドの上にこの記法を追加します。
<!--/-->

<!--en-->
`x ∈ᵗ y` is defined as the underlying type `⟨ x ∈ˢ y ⟩`{.Agda}, and therefore lies in `Type ℓ`. This is not a new relation but a Type-valued reading of the existing membership proposition. Note the direction of the arguments, matching the earlier notations: `x ∈ᵗ y` reads "x is a member of y".
<!--zh-->
`x ∈ᵗ y` 定义为底层类型 `⟨ x ∈ˢ y ⟩`{.Agda}，因此落在 `Type ℓ` 中。这不是新关系，而是既有隶属命题的 Type 值读法。注意实参方向与前面的记号一致：`x ∈ᵗ y` 读作「x 是 y 的成员」。
<!--ja-->
`x ∈ᵗ y` は基礎型 `⟨ x ∈ˢ y ⟩`{.Agda} と定義され、`Type ℓ` に属します。これは新しい関係ではなく、既存の所属命題を Type として読むものです。引数の向きはこれまでの記法と一致し、`x ∈ᵗ y` は「x は y の要素である」と読みます。
<!--/-->

```agda
module hPropStructure {ℓ} (𝒮 : ZFStructure ℓ) where
  open ZFStructure 𝒮 public

  _∈ᵗ_ : S → S → Type ℓ
  x ∈ᵗ y = ⟨ x ∈ˢ y ⟩
```

<!--en-->
So `y ∈ᵗ x` states that y is a member of x, as a proposition of the proposition-valued structure; an inhabitant of this type is evidence that the membership truth value holds.
<!--zh-->
于是 `y ∈ᵗ x` 陈述的是：在命题值结构中 y 是 x 的成员；这个类型的元素，就是成员真值成立的证据。
<!--ja-->
つまり `y ∈ᵗ x` は、命題値の構造において y が x の要素であることを述べます。この型の要素は、所属の真理値が成り立つことの証拠です。
<!--/-->

```agda

  infix 20 _∈ᵗ_
```

<!--en-->
## Transitive classes

With membership available as a Type-valued proposition, a class over the carrier becomes something whose elements we can reason about element by element. A class `M` is **transitive** when every member of an element of `M` is itself in `M`. This is the set-theoretic notion of transitivity, phrased with the two available membership relations: the structure's `∈ᵗ` on the left of the implication, and the host-level `∈ᶜ` for membership in the class itself.
<!--zh-->
## 传递类

隶属以 Type 值命题的形式可用之后，载体上的类就成为可以逐个元素推理的对象。类 `M` 若使 `M` 中元素的每个成员仍属于 `M`，就称为**传递**。这是集合论中的传递性概念，用现有的两种隶属关系来表述：蕴涵左侧用结构的 `∈ᵗ`，类本身的隶属用宿主层的 `∈ᶜ`。
<!--ja-->
## 推移的クラス

所属が Type 値の命題として使えるようになると、台の上のクラスは要素を一つずつ論じられる対象になります。クラス `M` は、`M` の要素のすべての要素が再び `M` に属するとき、**推移的**であるといいます。これは集合論の推移性の概念を、利用できる二つの所属関係で述べたものです。含意の左には構造の `∈ᵗ` を、クラスそのものへの所属にはホストレベルの `∈ᶜ` を用います。
<!--/-->

<!--en-->
`Transitive`{.Agda} takes a proposition-valued structure `𝒮` and a class `M : S → hProp ℓ`, and states the implication `y ∈ᵗ x → x ∈ᶜ M → y ∈ᶜ M`: assuming y is a member of x in the structure, and x belongs to the class M, y belongs to M as well. The direction is closure under members of members, not closure under subsets; the definition quantifies over carrier elements `x` and `y` implicitly and asserts nothing beyond this implication.
<!--zh-->
`Transitive`{.Agda} 接受命题值结构 `𝒮` 与类 `M : S → hProp ℓ`，陈述蕴涵 `y ∈ᵗ x → x ∈ᶜ M → y ∈ᶜ M`：若在结构中 y 是 x 的成员，且 x 属于类 `M`，则 y 也属于 `M`。这里的方向是对元素之元素的闭合，而不是对子集的闭合；定义隐含地量化载体元素 `x`、`y`，此外不断言任何内容。
<!--ja-->
`Transitive`{.Agda} は命題値の構造 `𝒮` とクラス `M : S → hProp ℓ` を受け取り、含意 `y ∈ᵗ x → x ∈ᶜ M → y ∈ᶜ M` を述べます。構造において y が x の要素であり、x がクラス `M` に属するなら、y も `M` に属する、というものです。向きとしては要素の要素についての閉性であって、部分集合についての閉性ではありません。定義は台の要素 `x`、`y` を暗黙に量化し、この含意以外は何も主張しません。
<!--/-->

```agda
Transitive : ∀ {ℓ} (𝒮 : ZFStructure ℓ)
           → (ZFStructure.S 𝒮 → hProp ℓ) → Type ℓ
Transitive 𝒮 M = ∀ {x y} → y ∈ᵗ x → x ∈ᶜ M → y ∈ᶜ M
  where open hPropStructure 𝒮
```

<!--en-->
## Substructures

Given a proposition-valued class `M`, we can now cut a structure down to the part of its carrier that satisfies `M`. The restriction `𝒮 ↾ M` is again a `ZFStructure`{.Agda}, and its carrier is the type of dependent pairs `(x , proof)` with `x : S` and `proof : x ∈ᶜ M`. Equality and membership on the restricted elements are inherited from `𝒮`: both relations look only at the first projections and apply the original relations there. This changes what counts as an element of the structure; it does not construct a set representing `M`, nor does it by itself fix a syntax or a constant domain.
<!--zh-->
## 子结构

给定命题值类 `M`，现在可以把结构裁剪到载体中满足 `M` 的那一部分。限制 `𝒮 ↾ M` 仍是一个 `ZFStructure`{.Agda}，其载体是依值对 `(x , proof)` 的类型，其中 `x : S` 且 `proof : x ∈ᶜ M`。限制元素上的等词与隶属从 `𝒮` 继承：两种关系都只看第一投影，并在其上应用原关系。这改变的是结构中什么算作元素；它不构造表示 `M` 的集合，也不自行确定语法或常元域。
<!--ja-->
## 部分構造

命題値のクラス `M` が与えられれば、台のうち `M` を満たす部分へ構造を切り詰められます。制限 `𝒮 ↾ M` は再び `ZFStructure`{.Agda} であり、その台は依存対 `(x , proof)` の型です。ここで `x : S` かつ `proof : x ∈ᶜ M` です。制限された要素に対する等号と所属は `𝒮` から受け継がれます。どちらの関係も第一射影だけを見て、そこに元の関係を適用します。変わるのは構造の要素の範囲であって、`M` を表す集合を構成するのでも、構文や定数域をそれ自体で固定するのでもありません。
<!--/-->

<!--en-->
The new carrier is the Σ-type `Σ[ x ∈ S ] (x ∈ᶜ M)`: an inhabitant is a pair of an underlying carrier element and membership evidence in `M`, so restricting does not collect `M` into a set, it only changes which pairs count as elements. The record's `isSetS` field still must be filled, and here the fiber-wise fact from the chapter opening does the work: since each `M x` is a proposition by its second component, `isSetΣSndProp`{.Agda} applied to `isSetS` proves that this pair type is again an h-set.
<!--zh-->
新载体是 Σ 类型 `Σ[ x ∈ S ] (x ∈ᶜ M)`：其元素是「底层载体元素配上 `M` 的成员证据」的对，因此限制并不把 `M` 收集成一个集合，只是改变哪些对算作元素。record 的 `isSetS` 字段仍须填写，这里正是章首那条逐纤维的事实起作用：由于每个 `M x` 凭第二分量是命题，把 `isSetΣSndProp`{.Agda} 作用于 `isSetS` 便证明这个对类型仍是 h-集合。
<!--ja-->
新しい台は Σ 型 `Σ[ x ∈ S ] (x ∈ᶜ M)` です。その要素は「元となる台の要素と `M` への所属の証拠」の対であり、したがって制限は `M` を集合に集めるのではなく、どの対を要素とみなすかを変えるだけです。レコードの `isSetS` フィールドは依然として埋める必要があり、ここで章の冒頭のファイバーごとの事実が働きます。各 `M x` は第二成分によって命題なので、`isSetS` に `isSetΣSndProp`{.Agda} を適用すれば、この対の型が再び h-集合であることが示されます。
<!--/-->

```agda
_↾_ : ∀ {ℓ} (𝒮 : ZFStructure ℓ)
    → (ZFStructure.S 𝒮 → hProp ℓ) → ZFStructure ℓ
_↾_ {ℓ} 𝒮 M = record
  { S      = Σ[ x ∈ S ] (x ∈ᶜ M)
  ; isSetS = isSetΣSndProp isSetS (λ x → (M x) .snd)
```

<!--en-->
Both relation fields pull the original relations back along the first projection: for restricted elements `a` and `b`, the structure evaluates `fst a ≈ˢ fst b` and `fst a ∈ˢ fst b`. So membership and equality between restricted elements are evaluated entirely on their underlying carrier elements; whatever evidence the pairs carry in their second components plays no role in the relations.
<!--zh-->
两个关系字段都沿第一投影拉回原关系：对限制元素 `a`、`b`，结构求值 `fst a ≈ˢ fst b` 与 `fst a ∈ˢ fst b`。因此限制元素之间的隶属与相等完全在其底层载体元素上求值；对在第二分量携带的证据对这两种关系不起任何作用。
<!--ja-->
どちらの関係フィールドも、元の関係を第一射影に沿って引き戻します。制限された要素 `a`、`b` に対して、構造は `fst a ≈ˢ fst b` と `fst a ∈ˢ fst b` を評価します。したがって、制限された要素の間の所属も等号も、もっぱら基底の台の要素の上で評価され、対が第二成分に持つ証拠はこの二つの関係に何の役割も果たしません。
<!--/-->

```agda
  ; _≈ˢ_   = λ a b → fst a ≈ˢ fst b
  ; _∈ˢ_   = λ a b → fst a ∈ˢ fst b }
  where open ZFStructure 𝒮

infixl 21 _↾_
```

<!--en-->
The relations of `𝒮 ↾ M` ignore the second components, so one might ask whether the restricted carrier distinguishes pairs at all beyond their first projections. It does not: because each membership type `M x` is a proposition, a path between the first projections determines a path between the whole pairs. The following lemma records this direction.
<!--zh-->
`𝒮 ↾ M` 的关系忽略第二分量，于是可以问：限制载体除了第一投影之外，是否还能区分不同的对？不能：因为每个隶属类型 `M x` 都是命题，第一投影之间的路径决定整个对之间的路径。下面的引理记录这个方向。
<!--ja-->
`𝒮 ↾ M` の関係は第二成分を無視します。そこで、制限された台は第一射影を超えて対を区別できるのか、と問えるでしょう。できません。各所属の型 `M x` が命題であるため、第一射影の間のパスが依存対全体の間のパスを定めます。次の補題はこの向きを記録します。
<!--/-->

<!--en-->
`↾-reflects`{.Agda} has type `fst a ≡ fst b → a ≡ b`{.Agda}. It applies `Σ≡Prop`{.Agda} with the family `λ x → (M x) .snd`, whose value proves pointwise that the membership evidence at `x` is proposition-valued; the resulting path between pairs is then built from the path between first projections alone. The lemma states this one direction only: it reflects equality of the underlying elements up to equality of the restricted elements, and says nothing about a converse.
<!--zh-->
`↾-reflects`{.Agda} 的类型是 `fst a ≡ fst b → a ≡ b`{.Agda}。它把 `Σ≡Prop`{.Agda} 用于族 `λ x → (M x) .snd`，该族逐点证明 `x` 处的成员证据是命题；于是对之间的路径仅由第一投影之间的路径构成。该引理只陈述这一个方向：底层元素的相等被反映为限制元素的相等，不另行陈述逆向命题。
<!--ja-->
`↾-reflects`{.Agda} の型は `fst a ≡ fst b → a ≡ b`{.Agda} です。族 `λ x → (M x) .snd` とともに `Σ≡Prop`{.Agda} を適用します。この族は各点で、`x` での所属の証拠が命題値であることを示すものであり、対の間のパスは第一射影の間のパスだけから組み立てられます。補題が述べるのはこの一方向だけです。基底の要素の等しさが制限された要素の等しさとして反映されることであり、逆については何も主張しません。
<!--/-->

```agda
↾-reflects : ∀ {ℓ} {𝒮 : ZFStructure ℓ} {M : ZFStructure.S 𝒮 → hProp ℓ}
             {a b : ZFStructure.S (𝒮 ↾ M)}
           → fst a ≡ fst b → a ≡ b
↾-reflects {M = M} = Σ≡Prop (λ x → (M x) .snd)
```

<!--en-->
## Recap

A `ZFStructure`{.Agda} records four fields: a carrier, its h-set proof, and proposition-valued interpretations of equality and membership. It includes no ZF axioms. For proposition-valued structures, `∈ᵗ` exposes the underlying membership type, `Transitive` states closure under members of members, and `𝒮 ↾ M` restricts the carrier to a class of dependent pairs. The lemma `↾-reflects`{.Agda} lifts equality of first projections to equality in that restricted carrier. The next step is to interpret the object-language formulas themselves inside such a structure.
<!--zh-->
## 小结

`ZFStructure`{.Agda} 记录四个字段：载体、载体的 h-集合性证明，以及等词与成员关系的真值解释；其中不包含 ZF 公理。对命题值结构，`∈ᵗ` 给出成员真值的底层类型，`Transitive` 陈述对元素之元素的闭合，`𝒮 ↾ M` 把载体限制到一个由依值对组成的类。引理 `↾-reflects`{.Agda} 把第一投影的相等提升为限制载体中的相等。下一步是在这样的结构中解释对象语言的公式本身。
<!--ja-->
## まとめ

`ZFStructure`{.Agda} は、台、その h-集合性の証明、等号と所属の真理値による解釈という四つのフィールドを記録し、ZF の公理は含みません。命題値の構造では、`∈ᵗ` が所属の基礎型を与え、`Transitive` が要素の要素についての閉性を述べ、`𝒮 ↾ M` が台を依存対からなるクラスへ制限します。`↾-reflects`{.Agda} は、第一射影の等しさを制限された台の等しさへ持ち上げます。次の段階は、このような構造の中で対象言語の論理式そのものを解釈することです。
<!--/-->
