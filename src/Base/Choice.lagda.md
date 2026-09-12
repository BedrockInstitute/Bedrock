<!--en-->
# Choice

Choice asserts that a simultaneous choice function merely exists for every family of merely inhabited fibers indexed by a set. This chapter states that principle level by level, proves that it descends to smaller universes, and derives excluded middle from it by Diaconescu's theorem.

The classical boundary has a second interface. Alongside the excluded middle, classical mathematics runs on choice, and this chapter states the book's form of it, one level at a time, in the same interface style as `LEM`{.Agda}. **Set-level choice** says that over an h-set of indices, truncation commutes with the product: if every fiber is merely inhabited, then merely, every fiber is inhabited at once. This is the type-theoretic reading of "a family of nonempty sets has a choice function". The h-set restriction on the index is part of the principle's statement, and the proof below will use it where the theory demands it. Like the excluded middle, choice is never assumed globally: a chapter that needs it takes it as a parameter, as the cumulative-hierarchy model chapter does.

The two interfaces are not peers, and this chapter proves it on the spot by Diaconescu's theorem: **choice proves the excluded middle**. At each level, the choice interface already implies the whole classical boundary.
<!--zh-->
# 选择原理

选择原理断言：对一个以集合为指标、每根纤维都仅仅有元的族，也仅仅存在一个同时从所有纤维中取值的选择函数。本章逐宇宙层级陈述这条原理，证明它能下降到较低层级，并用 Diaconescu 定理由此推出排中律。

经典边界还有第二个接口。经典数学除排中律外还依靠选择运转，本章陈述本书采用的形式，即逐层级、与 `LEM`{.Agda} 同款的接口风格。**集合层选择**说：在 h-集合索引之上，截断与乘积交换：若每根纤维都仅仅有元，则仅仅地，全体纤维一齐有元。这是「非空集族有选择函数」的类型论读法。索引上的 h-集合限制是原理陈述的一部分，下文的证明将在理论需要之处用到它。与排中律一样，选择从不全局假设：需要它的章节以参数领取，累积层级的模型章正是如此。

两个接口并非平级，本章当场用 Diaconescu 定理证明这一点：**选择证明排中律**。在每个层级上，选择接口都能推出整条经典边界。
<!--ja-->
# 選択原理

選択原理は、集合で添字付けられ、各ファイバーが単に要素を持つ族に対して、同時選択関数が単に存在すると主張します。本章ではこの原理を宇宙レベルごとに述べ、低いレベルへ移せることを示し、ディアコネスクの定理によって排中律を導きます。

古典的な境界には第二のインターフェースがあります。排中律と並んで、古典数学は選択原理の上でも動いており、本章では本書の形の選択原理を、`LEM`{.Agda} と同じインターフェース様式で一つずつのレベルについて述べます。**集合レベルの選択**とは、h-集合の添字の上で命題的切り詰めが積と可換になること、すなわち各ファイバーが単に要素を持てば、単に、すべてのファイバーが同時に要素を持つ、という主張です。これは「空でない集合の族には選択関数がある」という命題の型理論的な読みです。添字に対する h-集合という制限は原理の述べ方の一部であり、後の証明は理論が要求する場所でこれを用います。排中律と同様、選択は大域的に仮定されることはなく、必要とする章はパラメータとして受け取ります。累積階層のモデルの章がまさにそうしています。

二つのインターフェースは対等ではありません。本章はその場でディアコネスクの定理によってこれを証明します。**選択原理は排中律を証明する**のです。各レベルで、選択のインターフェースはすでに古典的な境界の全体を含意します。
<!--/-->

<!--en-->
This chapter compares two classical interfaces, and the first, `LEM`{.Agda} from `Base.Classical`{.Agda}, is available here only through its statement: it takes every proposition of a level to a decision, and since it quantifies over all of `Type ℓ`, it has the shape `∀ ℓ → Type (ℓ-suc ℓ)`. Choice will be stated in exactly the same shape, so that the two can be compared honestly at the same level. Nothing about excluded middle is assumed in this chapter; its statement is what the final theorem will produce from choice.
<!--zh-->
本章比较两个经典接口，而第一个，`Base.Classical`{.Agda} 中的 `LEM`{.Agda}，在这里只有其陈述可用：它把某层级的每个命题变为一个判定；由于它量化了整个 `Type ℓ`，其形状为 `∀ ℓ → Type (ℓ-suc ℓ)`。选择原理将以完全相同的形状陈述，使两个接口能在同一层级上被诚实地比较。本章不假设任何排中律；它的陈述正是章末定理要从选择推出的东西。
<!--ja-->
本章は二つの古典的インターフェースを比較します。その第一である `Base.Classical`{.Agda} の `LEM`{.Agda} は、ここではその記述だけが使われます。それはあるレベルの各命題を判定に写すもので、`Type ℓ` 全体を量化するため `∀ ℓ → Type (ℓ-suc ℓ)` という形を持ちます。選択原理はまったく同じ形で述べられるため、二つを同じレベルで公正に比較できます。本章で排中律は何も仮定されず、その記述こそ章末の定理が選択原理から導き出すものです。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

module Base.Choice where

open import Base.Prelude
open import Base.Classical using ( LEM )

open import Cubical.Foundations.Prelude using ( Path )
```

<!--en-->
The Diaconescu argument later in the chapter will need three concrete ingredients from the library. The first is a two-point type with a decidable equality: the case split at the end of the proof will run on that comparison, which unlike an arbitrary proposition can actually be inspected. The second is a trivially inhabited proposition, which supplies the unconditionally provable entries of a relation table. The third is the `Dec`{.Agda} datatype, whose `yes`{.Agda} and `no`{.Agda} record the two possible outcomes of such a comparison.
<!--zh-->
本章稍后的 Diaconescu 论证需要库中的三个具体材料。其一是一个带可判定相等的两点类型：证明末尾的分情形将在这份比较上进行，它与任意命题不同，是可以实际检视的。其二是一个平凡有元的命题，为关系表提供无条件可证的表项。其三是 `Dec`{.Agda} 数据类型，其 `yes`{.Agda} 与 `no`{.Agda} 记录这类比较的两种可能结果。
<!--ja-->
章の後半の Diaconescu の議論には、ライブラリから三つの具体的な材料が必要です。第一は判定可能な等式を持つ二点の型です。証明の最後の場合分けはこの比較の上で行われ、任意の命題と違って実際に検査できます。第二は自明に要素を持つ命題で、関係の表の無条件に証明できる項を供給します。第三は `Dec`{.Agda} 型で、その `yes`{.Agda} と `no`{.Agda} が比較の二つの帰結を記録します。
<!--/-->

```agda
open import Cubical.Foundations.HLevels using ( isOfHLevelLift )
open import Cubical.Data.Bool using ( Bool; true; false; _≟_ )
open import Cubical.Data.Unit using ( Unit*; tt*; isPropUnit* )
open import Cubical.Relation.Nullary using ( Dec; yes; no )
import Cubical.Data.Sum as Sum
```

<!--en-->
Two further tools carry the Diaconescu argument. One is propositional truncation `∥_∥₁`{.Agda}: it turns a statement into the weaker claim that the statement merely holds, so from it one obtains mere existence, never a chosen witness. The other is the set quotient construction: from a type and a relation it builds the type of classes `[ b ]`{.Agda}, adds a path `[ b ] ≡ [ b' ]`{.Agda} whenever `eq/`{.Agda} is given a certificate that the relation relates `b` and `b'`, and truncates the result to an h-set by `squash/`{.Agda}. Two theorems about quotients do the argument's decisive work: `[]surjective`{.Agda} says every point of a quotient merely arises as the class of some representative, and `effective`{.Agda} says a path in the quotient can be read backwards as a proof that the relation related the endpoints.
<!--zh-->
还有两件工具承担 Diaconescu 论证的关键。其一是命题截断 `∥_∥₁`{.Agda}：它把一个陈述变为「该陈述仅仅成立」的较弱主张，因此从它得到的是仅仅存在，绝非选定的见证。其二是集合商构造：从类型与关系出发，它构造出类 `[ b ]`{.Agda} 所成的类型；只要给 `eq/`{.Agda} 一份「关系关联 `b` 与 `b'`」的证书，就添加一条 `[ b ] ≡ [ b' ]`{.Agda} 的路径，并由 `squash/`{.Agda} 把结果截断为 h-集合。关于商的两条定理完成论证的决定性工作：`[]surjective`{.Agda} 说商的每个点都仅仅来自某个代表元的类，`effective`{.Agda} 说商中的路径可以倒读为「关系确实关联两端」的证明。
<!--ja-->
Diaconescu の議論の要を担う道具がさらに二つあります。一つは命題的切り詰め `∥_∥₁`{.Agda} です。これは主張を「その主張が単に成り立つ」というより弱い主張に変えるので、そこから得られるのは単なる存在であって、選ばれた証拠では決してありません。もう一つは集合商の構成です。型と関係から、類 `[ b ]`{.Agda} からなる型を作り、`eq/`{.Agda} に関係が `b` と `b'` を結ぶことの証拠が与えられれば道 `[ b ] ≡ [ b' ]`{.Agda} を加え、`squash/`{.Agda} によって結果を h-集合へ切り詰めます。商についての二つの定理が議論の決定的な仕事をします。`[]surjective`{.Agda} は商の各点が単に何らかの代表元の類として現れると述べ、`effective`{.Agda} は商の中の道を「関係が実際に両端を結んでいた」ことの証明として逆読みできると述べます。
<!--/-->

```agda
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁ )
open import Cubical.HITs.SetQuotients
  using ( _/_; [_]; eq/; squash/; []surjective; effective )
```

<!--en-->
The effectivity theorem just cited applies only to relations that are proposition-valued and equivalence relations, so the library also supplies the two corresponding predicates, packaged as records. The gluing relation built below will be proved to have exactly these two properties, which is what licenses reading its quotient's paths backwards.
<!--zh-->
刚才引用的有效性定理只适用于取值于命题且为等价关系的关系，因此库还提供了对应的两个谓词，以记录打包。下文构造的粘合关系将被证明恰好具备这两个性质，这正是倒读其商中路径的依据。
<!--ja-->
先に引用した有効性定理は、命題値であり同値関係であるような関係にしか適用できません。そこでライブラリは、対応する二つの述語をレコードとしてまとめて供給します。後で作る貼り合わせの関係は、まさにこの二つの性質を持つことが示されます。それが商の道を逆読みする根拠になります。
<!--/-->

```agda
open import Cubical.Relation.Binary.Base using ( module BinaryRelation )
```

<!--en-->
## The principle

Like the excluded middle, choice passes **downward** through the levels: lift the index set and the fibers one universe up, choose there, lower the choice function. A single higher instance therefore covers the levels below.
<!--zh-->
## 原理

与排中律一样，选择沿层级**向下**通行：把索引集与纤维抬升到高一层的宇宙，在那里做选择，再把选择函数降回来。于是较高层级上的单个实例覆盖其下诸层。
<!--ja-->
## 原理

排中律と同様に、選択原理は宇宙レベルを下向きに移せます。添字集合と各ファイバーを一つ上の宇宙へ持ち上げ、そこで選択し、その選択関数を元のレベルへ戻すため、高いレベルの一つの仮定がそれより低いレベルをすべて覆います。
<!--/-->

<!--en-->
The definition takes a level `ℓ` and packages four inputs. First an index type `X` in `Type ℓ`, together with the proof that it is an h-set: the principle is stated for set-indexed families. Then a family `B` of fibers over `X`, all in the same universe. The hypothesis is that each fiber is merely inhabited, and the conclusion is that merely, there is a single function choosing an inhabitant in every fiber at once. The word merely appears on both sides, and that is the honest strength: choice produces no actual function, only the truncated statement that one exists. Since the statement quantifies over all of `Type ℓ`, it lives one level up, at `Type (ℓ-suc ℓ)`, exactly like `LEM`{.Agda}.
<!--zh-->
定义取层级 `ℓ`，打包四个输入。第一是 `Type ℓ` 中的指标类型 `X`，并附其是 h-集合的证明：原理是对以集合为指标的族陈述的。其次是以 `X` 为指标、同在 `Type ℓ` 中的纤维族 `B`。假设是每根纤维都仅仅有元；结论是仅仅地，存在一个同时在每根纤维中取元的函数。「仅仅」出现在两侧，这正是诚实的强度：选择给出的不是真实的函数，只是「存在其一」的截断陈述。由于该陈述量化了整个 `Type ℓ`，它居于高一层级的 `Type (ℓ-suc ℓ)`，与 `LEM`{.Agda} 一致。
<!--ja-->
定義はレベル `ℓ` を受け、四つの入力をまとめます。第一に `Type ℓ` の添字型 `X` と、それが h-集合であることの証明です。原理は集合で添字付けられた族に対して述べられます。次に `X` の上のファイバーの族 `B` で、これも同じ `Type ℓ` に住みます。仮定は各ファイバーが単に要素を持つことであり、結論は、単に、すべてのファイバーから同時に要素を選ぶ一つの関数が存在する、というものです。「単に」が両側に現れるのが誠実な強さで、選択が実際の関数ではなく「存在する」という命題的切り詰められた主張だけを与えることを示しています。この主張は `Type ℓ` 全体を量化するため、`LEM`{.Agda} と同じく一つ上の `Type (ℓ-suc ℓ)` に住みます。
<!--/-->

```agda
SetChoice : ∀ ℓ → Type (ℓ-suc ℓ)
SetChoice ℓ = (X : Type ℓ) → isSet X → (B : X → Type ℓ)
            → ((x : X) → ∥ B x ∥₁) → ∥ ((x : X) → B x) ∥₁
```

<!--en-->
Downward transfer mirrors `lowerLEM`{.Agda} from `Base.Classical`{.Agda}: assume choice one universe up, recover it at the given level. The transport is by `Lift`{.Agda}, whose source and target universe parameters let data from `Type ℓ` be seen inside `Type (ℓ-suc ℓ)` and lowered back afterwards.
<!--zh-->
向下传递与 `Base.Classical`{.Agda} 的 `lowerLEM`{.Agda} 同构：假设高一层级的选择，恢复给定层级的选择。搬运借助 `Lift`{.Agda}：它的源与目标宇宙参数使 `Type ℓ` 的数据可以被放进 `Type (ℓ-suc ℓ)` 中使用，事后再降回来。
<!--ja-->
下向きの移行は `Base.Classical`{.Agda} の `lowerLEM`{.Agda} と同じ構図です。一つ上のレベルの選択を仮定して、与えられたレベルの選択を取り戻します。輸送には `Lift`{.Agda} を用います。そのソースとターゲットの宇宙パラメータにより、`Type ℓ` のデータを `Type (ℓ-suc ℓ)` の中で使うことができ、後で `lower` で元に戻せます。
<!--/-->

<!--en-->
Given data at level `ℓ`, the proof rehouses it at level `ℓ-suc ℓ` where the stronger hypothesis `sc` applies. The index `X` becomes `Lift X`, whose h-set condition follows from `X`'s by `isOfHLevelLift`{.Agda}. The family `B x` becomes `λ x → Lift (B (lower x))`: a fiber over the lifted index is the lifted fiber over the original index underneath, so the lifted family carries exactly the same information as the original.
<!--zh-->
给定 `ℓ` 层级的数据，证明把它安置到 `ℓ-suc ℓ` 层级，使更强的假设 `sc` 得以适用。指标 `X` 变为 `Lift X`，其 h-集合性经 `isOfHLevelLift`{.Agda} 从 `X` 的 h-集合性得到。纤维族 `B x` 变为 `λ x → Lift (B (lower x))`：抬升指标上的纤维就是底下原指标上纤维的抬升，因此抬升后的族与原来的族携带完全相同的信息。
<!--ja-->
レベル `ℓ` のデータが与えられると、証明はそれを `ℓ-suc ℓ` のレベルに置き直し、より強い仮定 `sc` を適用できるようにします。添字 `X` は `Lift X` となり、その h-集合性は `isOfHLevelLift`{.Agda} によって `X` のものから従います。ファイバーの族 `B x` は `λ x → Lift (B (lower x))` となります。持ち上げた添字の上のファイバーは、その下にある元の添字の上のファイバーを持ち上げたものであり、持ち上げられた族は元の族とまったく同じ情報を運びます。
<!--/-->

```agda
lowerSetChoice : ∀ {ℓ} → SetChoice (ℓ-suc ℓ) → SetChoice ℓ
lowerSetChoice sc X setX B inh =
  PT.map (λ f x → lower (f (lift x)))
         (sc (Lift X) (isOfHLevelLift 2 setX)
             (λ x → Lift (B (lower x)))
```

<!--en-->
The remaining inputs are transferred in step. The hypothesis that each lifted fiber is merely inhabited is met by lowering the index and lifting the resulting truncation, using that `PT.map`{.Agda} acts inside the truncation. Once `sc` returns the mere existence of a lifted choice function, `PT.map` again converts it into the mere existence of the lowered one, whose value at `x` is `lower (f (lift x))`. The conclusion is a truncated statement, so this final step is legitimate: nothing actual about `f` was ever claimed.
<!--zh-->
其余输入逐项传递。每个抬升纤维仅仅有元的假设，通过把指标降下、把所得截断抬升来满足，其中用到 `PT.map`{.Agda} 在截断内部的作用。一旦 `sc` 交出抬升选择函数的仅仅存在，`PT.map` 再次把它转化为降低后函数的仅仅存在，其在 `x` 处的值为 `lower (f (lift x))`。结论本身是截断陈述，所以最后这步是合法的：对 `f` 我们从未主张任何真实的存在。
<!--ja-->
残りの入力も一つずつ移されます。持ち上げた各ファイバーが単に要素を持つという仮定は、添字を降ろし、得られた命題的切り詰めを持ち上げることで満たされます。ここで `PT.map`{.Agda} が切り詰めの内部で働くことを使います。`sc` が持ち上げた選択関数の単なる存在を返したら、再び `PT.map` によって降ろした関数の単なる存在へと変換し、その `x` での値は `lower (f (lift x))` です。結論は切り詰められた主張なので、この最後の一段は正当です。`f` について実際の存在が主張されることは一度もありません。
<!--/-->

```agda
             (λ x → PT.map lift (inh (lower x))))
```

<!--en-->
## Diaconescu's theorem

The theorem: given set-level choice, **any** proposition `P` can be decided, proved or refuted. On its face this is absurd, since a decision procedure has nothing to act on: an arbitrary `P` offers no case to split on. The proof instead proceeds *geometrically*. Build a little space whose very shape depends on `P`: the two classes of `true` and `false` in it coincide exactly when `P` holds. Put one question about that space to the choice principle; the answer necessarily reveals the shape, and the shape is `P`.

Concretely, fix `P`; everything below lives in a module dedicated to the theorem. Take the two booleans and glue them together exactly when `P` holds. "Gluing" is a **set quotient**: the points are still `true` and `false`, but a path is added between them whenever the gluing relation says so, and the result is made into an h-set. The relation is best given as a four-entry table: trivially satisfied on the diagonal, and **literally `P` itself** in the two mixed squares, so that "the two points are related" and "`P` holds" are the same proposition by definition. This last clause is the key to the whole argument, and it will be used twice below.
<!--zh-->
## Diaconescu 定理

定理说：给定集合层选择，**任何**命题 `P` 都可判定，即或证明或反驳。乍看这很荒谬，因为判定程序无从下手：任意的 `P` 没有可供分情况处理的切入口。证明的想法是改从**几何**入手。造一个形状依赖于 `P` 的小空间：其中的两个类，即 `true` 的类与 `false` 的类，恰在 `P` 成立时重合。然后用选择原理回答一个关于这个空间的问题；答案必然透露出形状，而形状就是 `P`。

具体地，固定 `P`；以下一切都设在一个专属于该定理的模块里。取两个布尔值，恰在 `P` 成立时把它们粘起来。「粘合」指**集合商**：点仍是 `true` 与 `false`，但凡粘合关系在两点之间成立，就添一条路径，最后把结果做成 h-集合。粘合关系最好用一张四格表给出：对角线上平凡成立，混色的两格**就是 `P` 本身**，于是「这两点相关」与「`P` 成立」按定义是同一个命题。最后这一条是全部论证的关键，下文将用到两次。
<!--ja-->
## ディアコネスクの定理

定理はこう述べます。集合レベルの選択原理が与えられれば、**任意の**命題 `P` が判定できる、つまり証明か反証のいずれかが得られる、とします。一見これは不条理です。判定手続きは `P` について場合分けする入り口を何も持たないからです。証明は代わりに**幾何的**に進みます。`P` に応じて形そのものが変わる小さな空間を作ります。その空間における `true` の類と `false` の類は、`P` が成り立つとき、そしてそのときに限って一致します。その空間についてのただ一つの質問を選択原理に投げると、答えは必然的に形を明かし、その形こそが `P` なのです。

具体的には `P` を固定し、以下すべてをこの定理専用のモジュールの中で行います。二つのブール値を、`P` が成り立つときちょうど貼り合わせます。「貼り合わせ」とは**集合商**のことです。点は `true` と `false` のままですが、貼り合わせの関係が成り立つ二点の間には道が加えられ、結果は h-集合にされます。関係は四項の表として与えるのが最も分かりやすいでしょう。対角線上では自明に成り立ち、混色の二項は**文字どおり `P` そのもの**です。したがって「二点が関係で結ばれる」と「`P` が成り立つ」は定義により同じ命題になります。この最後の条項が議論全体の鍵であり、後で二度使われます。
<!--/-->

<!--en-->
The gluing relation `_~_` is defined by pattern matching on the two booleans, so its four squares are visible at once. When the two inputs agree, the relation holds with the trivial certificate `tt*`{.Agda} in the one-point type `Unit*`{.Agda}. When they differ, the relation holds exactly with a proof of the underlying type `⟨ P ⟩` of the proposition `P`. There is no machinery here: reading the mixed squares off the table *is* the proof that being related across the two points is the same statement as `P`.
<!--zh-->
粘合关系 `_~_` 通过对两个布尔值做模式匹配定义，四个表项一眼可见。当两个输入一致时，关系以单点类型 `Unit*`{.Agda} 中的平凡证书 `tt*`{.Agda} 成立。当二者相异时，关系恰好以命题 `P` 的底类型 `⟨ P ⟩` 的证明成立。这里没有任何机关：从表中读出混色两项，**就是**「跨两点相关」与 `P` 同为一个陈述的证明。
<!--ja-->
貼り合わせの関係 `_~_` は二つのブール値に対するパターンマッチで定義されるため、四つの項が一目で分かります。入力が一致するとき、関係は一点型 `Unit*`{.Agda} の自明な証拠 `tt*`{.Agda} とともに成り立ちます。一致しないとき、関係は命題 `P` の底の型 `⟨ P ⟩` の証拠によってちょうど成り立ちます。ここに仕掛けはありません。表の混色の項を読み取ることが、二点をまたぐ関係が `P` と同じ主張であることの証明そのものです。
<!--/-->

```agda
module Diaconescu {ℓ} (P : hProp ℓ) where

  _~_ : Bool → Bool → Type ℓ
  true  ~ true  = Unit*
  false ~ false = Unit*
  _     ~ _     = ⟨ P ⟩
```

<!--en-->
The space itself, `Glued`, is the set quotient `Bool / _~_`: the type of classes `[ b ]`{.Agda} of booleans under the relation, with `eq/`{.Agda} adding a path `[ true ] ≡ [ false ]` whenever a certificate of `true ~ false` is supplied, and `squash/`{.Agda} making the result an h-set. Its two distinguished points are the classes of `true` and `false`. When `P` holds, the quotient supplies the path between them; when `P` fails, effectivity will show that the two distinguished classes are distinct.
<!--zh-->
空间本身 `Glued` 是集合商 `Bool / _~_`：即布尔值在此关系下的类 `[ b ]`{.Agda} 所成的类型；只要给出 `true ~ false` 的证书，`eq/`{.Agda} 就添加一条 `[ true ] ≡ [ false ]` 的路径，而 `squash/`{.Agda} 把结果做成 h-集合。它的两个特殊点是 `true` 的类与 `false` 的类。`P` 成立时，商在两点之间提供路径；`P` 不成立时，有效性将表明这两个特殊类相异。
<!--ja-->
空間そのものである `Glued` は集合商 `Bool / _~_` です。すなわち、この関係に関するブール値の類 `[ b ]`{.Agda} からなる型であり、`true ~ false` の証拠が与えられると `eq/`{.Agda} が道 `[ true ] ≡ [ false ]` を加え、`squash/`{.Agda} が結果を h-集合にします。二つの注目すべき点は `true` の類と `false` の類です。`P` が成り立てば商が両者の間の道を供給し、`P` が成り立たなければ、有効性がこの二つの類の相異を示します。
<!--/-->

```agda

  Glued : Type ℓ
  Glued = Bool / _~_
```

<!--en-->
Because the relation is a table, its certificates are tables too: propositional in every square, reflexive on the diagonal, symmetric since the table is, and transitive by reading off whichever mixed square remains. The certificates are not bookkeeping: they are what lets us apply the library's **effectivity** theorem, which says that a quotient by a propositional equivalence relation glues *honestly*: two points end up connected only if the relation actually related them, never by accident. In other words, a path in the quotient can be read backwards, recovering the relation that caused it.
<!--zh-->
关系及其证书都由这张表给出：每个表项都是命题，对角线给出自反性，表的对称性给出关系的对称性，传递性则由剩余的混合表项证明。这些证书用于应用库的**有效性**定理。该定理说明，按命题值等价关系取商时，两点在商中相等必然来自原关系对它们的关联；因此，可以从商中的路径恢复对应的关系证明。
<!--ja-->
関係は表として与えられているので、その証拠もまた表になります。どの項でも命題値であり、対角線からは反射性が、表の対称性からは対称性が、残った混色の項を読み取ることで推移性が従います。これらの証拠は事務作業ではありません。ライブラリの**有効性**定理を適用するための条件です。この定理によれば、命題値の同値関係による商は正直に貼り合わせを行います。すなわち、二点が商の中で結ばれるのは、関係が実際にその二点を結んだときに限られ、偶然には決して起こりません。言い換えれば、商の中の道を逆に読んで、それを生んだ関係を取り戻せるのです。
<!--/-->

<!--en-->
The first certificate says that the relation is proposition-valued: for each pair of inputs, the type of certificates is a proposition. On the diagonal the certificate type is `Unit*`{.Agda}, which `isPropUnit*`{.Agda} shows is a proposition. In the two mixed squares the certificate type is `⟨ P ⟩` itself, and propositionhood is exactly the second component `P .snd` of the `hProp`{.Agda} package. The effectivity theorem requires this: if certificates could differ from each other, a path in the quotient would not determine a well-defined statement to read back.
<!--zh-->
第一份证书说明关系取值于命题：对每对输入，证书类型都是命题。对角线上证书类型是 `Unit*`{.Agda}，`isPropUnit*`{.Agda} 表明它是命题。混色的两格中，证书类型正是 `⟨ P ⟩`，其命题性恰是 `hProp`{.Agda} 打包的第二个分量 `P .snd`。有效性定理要求这一点：若证书可以彼此不同，商中的路径就无法确定一个良定义的陈述供倒读。
<!--ja-->
最初の証拠は、関係が命題値であることを述べます。すなわち入力の各組に対して、証拠の型が命題になるということです。対角線上では証拠の型は `Unit*`{.Agda} であり、`isPropUnit*`{.Agda} がそれが命題であることを示します。混色の二項では証拠の型は `⟨ P ⟩` そのものであり、その命題性は `hProp`{.Agda} パッケージの第二成分 `P .snd` にほかなりません。有効性定理はこれを要求します。証拠が互いに異なり得るなら、商の中の道は逆読みのための well-defined な主張を決定できません。
<!--/-->

```agda
  ~-prop : BinaryRelation.isPropValued _~_
  ~-prop true  true  = isPropUnit*
  ~-prop false false = isPropUnit*
  ~-prop true  false = P .snd
  ~-prop false true  = P .snd
```

<!--en-->
Reflexivity is immediate: every element is related to itself, since the two diagonal squares of the table hold unconditionally. The certificates are again `tt*`{.Agda}, one per boolean, so the proof is a two-case pattern match with nothing to construct. This is the first of the three equivalence axioms, and the next two follow the same read-the-table style.
<!--zh-->
自反性直接可得：表的两条对角格无条件成立，所以每个元素都与自身相关。证书仍是 `tt*`{.Agda}，每个布尔值一条，于是证明是两分支的模式匹配，无需构造任何东西。这是三条等价公理中的第一条，后两条沿用同样的「读表」风格。
<!--ja-->
反射性は直ちに得られます。表の対角の二項は条件なしで成り立つため、すべての元は自分自身と関係を持ちます。証拠は再び `tt*`{.Agda} で、ブール値ごとに一つ。したがって証明は場合分け二つだけのパターンマッチで、構成すべきものは何もありません。これは同値関係の三公理の最初のもので、続く二つも同じ「表を読む」様式に従います。
<!--/-->

```agda

  ~-refl : (a : Bool) → a ~ a
  ~-refl true  = tt*
  ~-refl false = tt*

  ~-sym : (a b : Bool) → a ~ b → b ~ a
  ~-sym true  true  _ = tt*
```

<!--en-->
Symmetry holds because the table itself is symmetric: swapping the two inputs maps each square to itself, so a certificate of `a ~ b` becomes a certificate of `b ~ a`. On the diagonal the certificate is `tt*`{.Agda} either way, and in the mixed squares the certificate is a proof of `P`, which is the same thing in both directions. The four pattern cases are therefore either a `tt*`{.Agda} or the identity on the given proof.
<!--zh-->
对称性成立，因为表本身对称：交换两个输入把每个表项映到自身，于是 `a ~ b` 的证书变成 `b ~ a` 的证书。对角线上无论方向证书都是 `tt*`{.Agda}；混色两格中证书是 `P` 的证明，两个方向说的是同一件事。四个分支因此要么是 `tt*`{.Agda}，要么就是对给定证明的恒等。
<!--ja-->
対称性は、表そのものが対称であることから成り立ちます。入力を入れ替えても各項は自分自身に写るので、`a ~ b` の証拠は `b ~ a` の証拠になります。対角線上では証拠はどちら向きでも `tt*`{.Agda} であり、混色の項では証拠は `P` の証明であり、両方向で同じものです。したがって四つのパターンは `tt*`{.Agda} か、与えられた証明に対する恒等写像のいずれかです。
<!--/-->

```agda
  ~-sym false false _ = tt*
  ~-sym true  false p = p
  ~-sym false true  p = p

  ~-trans : (a b c : Bool) → a ~ b → b ~ c → a ~ c
  ~-trans true  _     true  _ _ = tt*
```

<!--en-->
Transitivity needs a little thought, because two certificates could in principle combine to demand a certificate the table does not contain. Reading the cases shows this cannot happen: whenever the endpoints agree, some diagonal square makes the result trivial; whenever they differ, one of the two given certificates must come from a mixed square, and since the other certificate then involves only equal booleans, that same `P`-proof serves as the result. Six cases cover the possibilities, each reusing one of the inputs.
<!--zh-->
传递性需要稍作思考：两个证书的组合原则上可能要求表中不存在的证书。逐情形读表可知这不会发生：若两端一致，某条对角格使结论平凡成立；若两端相异，则给定的两个证书中必有一个来自混色格，而此时另一个证书只涉及相等的布尔值，于是同一个 `P` 证明就充当结论。六个分支覆盖所有情形，每个都复用某个输入。
<!--ja-->
推移性には少し考えが必要です。二つの証拠の組み合わせが、表に存在しない証拠を要求する可能性が原理的にはあるからです。場合を読むと、それは起こりえないことが分かります。両端が一致していれば、どこかの対角の項が結論を自明にします。両端が異なっていれば、与えられた二つの証拠のどちらかは混色の項から来ており、このときもう一方の証拠は等しいブール値しか含まないので、同じ `P` の証明がそのまま結論になります。六つの場合分けがすべての可能性を覆い、それぞれが入力の一つを再利用します。
<!--/-->

```agda
  ~-trans false _     false _ _ = tt*
  ~-trans true  false false p _ = p
  ~-trans false true  true  p _ = p
  ~-trans true  true  false _ p = p
  ~-trans false false true  _ p = p
```

<!--en-->
The three pieces are assembled into the record `isEquivRel _~_` by the library constructor `BinaryRelation.equivRel`{.Agda}. With proposition-valuedness and the equivalence axioms in hand, the quotient `Glued` satisfies exactly the hypotheses of effectivity, so the honest reading of its paths is now available for the lemmas below.
<!--zh-->
三份材料由库构造子 `BinaryRelation.equivRel`{.Agda} 组装为记录 `isEquivRel _~_`。有了命题值性与等价公理，商 `Glued` 便恰好满足有效性的全部假设，于是对它的路径的诚实读法在下面的引理中即可取用。
<!--ja-->
三つの材料は、ライブラリの構成子 `BinaryRelation.equivRel`{.Agda} によってレコード `isEquivRel _~_` へと組み立てられます。命題値性と同値関係の公理が揃ったので、商 `Glued` は有効性定理の仮定をちょうど満たし、その道の正直な読み方が以下の補題で使えるようになります。
<!--/-->

```agda

  ~-equivRel : BinaryRelation.isEquivRel _~_
  ~-equivRel = BinaryRelation.equivRel ~-refl ~-sym ~-trans
```

<!--en-->
The core of the construction is a two-line statement: **the two distinguished classes of the quotient coincide exactly when `P` holds**. One direction: if `P` holds, the table relates `true` to `false`, so the quotient identifies their classes. The other direction: if the two classes coincide, effectivity of the gluing says the relation must have related `true` to `false`, and by the table that relation *is* `P`, so `P` holds. The mixed square is used in both directions: a `P`-witness feeds the path constructor directly, and the effectivity theorem's output is already a proof of `P`, with no decoding and no impossible case to dismiss.
<!--zh-->
构造的核心是一个两行论断：**商的两个特殊类重合，当且仅当 `P` 成立**。一个方向是：若 `P` 成立，表格判定 `true` 与 `false` 相关，商便把两个类等同。另一个方向是：若两个类重合，粘合的有效性说明关系必定关联 `true` 与 `false`，而表中的这项关系**就是** `P`，所以 `P` 成立。混色格在这里用于两个方向：`P` 的见证直接传给路径构造子，有效性定理的输出本身就是 `P` 的证明，无需解码或排除其他情形。
<!--ja-->
構成の核心は二行で述べられます。**商の二つの注目すべき類が一致するのは、`P` が成り立つとき、かつそのときに限る**のです。一つの向きはこうです。`P` が成り立てば、表は `true` と `false` を関係で結ぶので、商は両者の類を同一視します。他の向きはこうです。二つの類が一致すれば、貼り合わせの有効性により、関係が実際に `true` と `false` を結んだはずであり、表によればその関係こそ `P` なので、`P` が成り立ちます。混色の項は両方の向きで使われます。`P` の証拠はそのまま道の構成子に渡り、有効性定理の出力もそのまま `P` の証明であり、復号も不可能な場合の除去も要りません。
<!--/-->

<!--en-->
The two directions are packaged as named functions. Forward, `glue`{.Agda} turns a proof of `P` into the path constructor applied to it: since the mixed square of the table holds with certificate `p`, the classes of `true` and `false` are equal by definition of the quotient. Backward, `unglue`{.Agda} is the effectivity theorem instantiated at `true` and `false`: given any path between the two classes, it returns a certificate of `true ~ false`, which by the table is a proof of `⟨ P ⟩`. No case analysis on the path is needed; the theorem's output already has the required type. Together they give the biconditional as plain data: `glue`{.Agda} and `unglue`{.Agda} are the two halves of the dictionary between `P` and the equality of the two distinguished classes.
<!--zh-->
两个方向被打包为命名的函数。正向的 `glue`{.Agda} 把 `P` 的证明送入路径构造子：表的混色格以证书 `p` 成立，按商的定义两个类便相等。反向的 `unglue`{.Agda} 是在 `true` 与 `false` 处例示的有效性定理：给定两类之间的任意路径，它返回 `true ~ false` 的证书，而按表这就是 `⟨ P ⟩` 的证明。无需对路径做任何分情形；定理输出的类型恰好就是所需。两者合起来，把双条件作为普通数据给出：`glue`{.Agda} 与 `unglue`{.Agda} 是 `P` 与两个特殊类的相等之间词典的两半。
<!--ja-->
二つの向きは名前付きの関数としてまとめられます。順方向の `glue`{.Agda} は `P` の証明を道の構成子に渡すだけです。表の混色の項は証拠 `p` とともに成り立つので、商の定義により二つの類は等しくなります。逆方向の `unglue`{.Agda} は `true` と `false` で具体化した有効性定理です。二つの類の間の任意の道が与えられれば、`true ~ false` の証拠を返し、表によればそれは `⟨ P ⟩` の証明です。道に対する場合分けは一切不要で、定理の出力の型はそのまま要求に合致します。両者を合わせれば、双条件がそのままデータとして得られます。`glue`{.Agda} と `unglue`{.Agda} は、`P` と二つの注目すべき類の一致とを結ぶ辞書の二半分です。
<!--/-->

```agda
  glue : ⟨ P ⟩ → Path Glued [ true ] [ false ]
  glue p = eq/ true false p

  unglue : Path Glued [ true ] [ false ] → ⟨ P ⟩
  unglue = effective ~-prop ~-equivRel true false
```

<!--en-->
Now the choice principle enters, and here is the single question we ask it: *hand every point of the glued space a boolean representative.* A **pick** at a point is a boolean together with the guarantee that its class is that point. Each point separately is sure to have one, but only *merely* so: a quotient remembers that its points came from somewhere without remembering from where. Turning "each point merely has a representative" into the mere existence of one **function** choosing representatives everywhere at once is what set-level choice states, and it applies here because the glued space is an h-set by construction. The chooser supplies representatives uniformly over `Glued`; the later argument extracts a decision by comparing only its values at the two distinguished classes.
<!--zh-->
现在应用选择原理，要求为粘合空间的每个点选出一个布尔代表元。某点处的一次**选取**由一个布尔值及其等价类等于该点的证明组成。每个点单独地都必有一次选取，但只能证明其**仅仅**存在：商保留每个点来自某个代表元，却不指定该代表元。把「每个点都仅仅有代表元」转化为一个同时处处选代表元的函数的**仅仅**存在，正是集合层选择所陈述的内容；它在此处适用，因为粘合空间按构造是 h-集合。这个选择函数在整个 `Glued` 上一致地给出代表元；后面的论证只比较它在两个特殊等价类上的取值，由此提取判定。
<!--ja-->
ここで選択原理が登場し、これに問う質問はただ一つです。*貼り合わせの空間のすべての点に、ブール値の代表元を一つずつ渡せ*、というものです。ある点での**選択 (pick)**とは、一つのブール値と、その類がその点に等しいという保証の組です。点ごとには必ず選択が存在しますが、それは**単に**存在するだけです。商は、自分の点がどこかから来たことを覚えていても、どこから来たかは覚えていないからです。「各点が単に代表元を持つ」ことを、あらゆる点で一度に代表元を選ぶ一つの**関数**の単なる存在へ変える、これが集合レベルの選択原理の述べるところであり、貼り合わせの空間が構成上 h-集合であるためここに適用できます。選択関数は `Glued` 全体で一様に代表元を与えます。後の議論は二つの特別な同値類での値だけを比較し、そこから判定を取り出します。
<!--/-->

<!--en-->
The family to choose from is `Pick x`, a dependent pair: a boolean `b` together with a path witnessing that the class `[ b ]` equals the point `x`. That each point merely has a pick is not an extra assumption but a library fact: `[]surjective`{.Agda} says every element of a quotient merely arises as the class of some representative, and `pickable`{.Agda} is exactly that statement read with `x` ranging over `Glued`. Note the direction of the information: the certificate of a pick records which representative was used, and it is this certificate, not the boolean alone, that lets the argument later reconstruct paths between classes.
<!--zh-->
被选取的族是 `Pick x`，一个依赖对：布尔值 `b` 加上见证类 `[ b ]` 等于点 `x` 的路径。「每个点都仅仅有一次选取」不是额外假设而是库定理：`[]surjective`{.Agda} 说商的每个元素都仅仅来自某个代表元的类，`pickable`{.Agda} 正是把这句话按 `x` 取遍 `Glued` 读出的形式。注意信息的方向：一次选取的证书记录了用的是哪个代表元，后面论证要重构类与类之间的路径，靠的是这份证书而非单独的布尔值。
<!--ja-->
選択の対象となる族は `Pick x` という依存ペアです。ブール値 `b` と、類 `[ b ]` が点 `x` に等しいことを見届ける道の組です。「各点が単に選択を持つ」ことは追加の仮定ではなくライブラリの事実です。`[]surjective`{.Agda} は商の任意の元が単に何らかの代表元の類として現れると述べ、`pickable`{.Agda} はそれを `x` が `Glued` を走る形で読んだものにほかなりません。情報の向きに注意してください。選択の証拠はどの代表元が使われたかを記録しており、後に類と類の間の道を再構成するのは、ブール値そのものではなくこの証拠なのです。
<!--/-->

```agda
  Pick : Glued → Type ℓ
  Pick x = Σ[ b ∈ Bool ] ([ b ] ≡ x)

  pickable : (x : Glued) → ∥ Pick x ∥₁
  pickable = []surjective
```

<!--en-->
The question deserves to be a lemma of its own, so that its type displays exactly what choice delivers: the mere existence of a picking function defined on the whole space.
<!--zh-->
这个问题值得单独立为引理，好让类型原样展示选择所给出之物：**仅仅地**存在的一整个选取函数。
<!--ja-->
この問いは独立した補題にする価値があります。型そのものが、選択原理が与えるもの、すなわち空間全体で定義された選択関数の**単なる**存在を示すからです。
<!--/-->

<!--en-->
The lemma takes `SetChoice ℓ` as an explicit hypothesis and instantiates it with the data assembled above: index `Glued`, its h-set certificate from `squash/`{.Agda}, the fiber family `Pick`, and the pointwise mere inhabitation `pickable`{.Agda}. The hypothesis `sc` is itself a function; what is truncated is its output. The conclusion is the propositionally truncated existence of a function defined on all of `Glued` at once: choice never produces the function itself, only the statement that one merely exists, and this limitation will shape the final step of the theorem.
<!--zh-->
引理把 `SetChoice ℓ` 取为显式假设，并用上文备好的数据例示它：指标 `Glued`、来自 `squash/`{.Agda} 的 h-集合性、纤维族 `Pick`、逐点的仅仅有元 `pickable`{.Agda}。假设 `sc` 本身是一个函数；被命题截断的是它的输出。结论是定义在整个 `Glued` 上的函数的命题截断存在：选择从不给出函数本身，只给出「有一个函数」的截断陈述，这一限制将塑造定理的最后一步。
<!--ja-->
補題は `SetChoice ℓ` を明示的な仮定として受け、上で揃えたデータで具体化します。添字 `Glued`、`squash/`{.Agda} による h-集合性、ファイバーの族 `Pick`、各点での単なる非空性 `pickable`{.Agda} です。仮定 `sc` はそれ自身関数であり、命題的切り詰めが施されるのはその出力の側です。結論は `Glued` 全体で定義された関数の命題的切り詰めされた存在です。選択原理は関数そのものではなく「関数が単に存在する」という主張しか与えず、この制限が定理の最終段階の形を決めます。
<!--/-->

```agda
  merePicker : SetChoice ℓ → ∥ ((x : Glued) → Pick x) ∥₁
  merePicker sc = sc Glued squash/ Pick pickable
```

<!--en-->
Suppose, then, that a picking function `g` is given. Apply it to the two distinguished points, the class of `true` and the class of `false`, and name the two boolean representatives it selects, `b₀` and `b₁`. Two lemmas, one per direction, relate these values to `P`. **If the representatives agree**, their guarantees give a path from the class of `true` to the class of `b₀`, then to the class of `b₁`, and finally to the class of `false`; effectivity turns the equality of the endpoints into a proof of `P`. **If `P` holds**, the two distinguished points are equal, and the picking function respects that equality, so `b₀` and `b₁` are equal. (Formally, it suffices to project `g` along the gluing path; both endpoints are plain booleans, so no transport is needed.)
<!--zh-->
设选取函数为 `g`。将它分别作用于两个特殊点，即 `true` 的类和 `false` 的类，并把所得布尔代表元记作 `b₀` 与 `b₁`。两个方向的引理把这两个值与 `P` 联系起来。**若代表元一致**，它们各自的保证给出从 `true` 的类到 `b₀` 的类、再到 `b₁` 的类、最后到 `false` 的类的路径；有效性定理把两端相等转化为 `P` 的证明。**若 `P` 成立**，两个特殊点相等，选取函数尊重这条相等，因此 `b₀` 与 `b₁` 相等。(形式化地，只需把 `g` 沿粘合路径投影；两端都是普通布尔值，无需搬运。)
<!--ja-->
そこで、選択関数 `g` が与えられたとします。これを二つの注目点、すなわち `true` の類と `false` の類に適用し、選ばれた二つのブール値の代表元を `b₀` と `b₁` と名付けます。二つの補題が、方向ごとに一つずつ、これらの値を `P` と結びます。**代表元が一致するなら**、それぞれの保証が `true` の類から `b₀` の類へ、`b₁` の類へ、そして `false` の類への道を与え、有効性が両端の一致を `P` の証明へ変えます。**`P` が成り立つなら**、二つの注目点は等しく、選択関数はその等しさを尊重するので、`b₀` と `b₁` は等しくなります。(形式的には、`g` を貼り合わせの道に沿って射影すれば足ります。両端は生のブール値なので輸送は不要です。)
<!--/-->

<!--en-->
A genuine function `g` of type `(x : Glued) → Pick x` is now assumed as a module parameter, suspending the fact that only its mere existence is known. Evaluating `g` at the two distinguished points yields two picks, and their first components are the booleans `b₀` and `b₁`: the representatives chosen at the class of `true` and at the class of `false`. All the reasoning that follows is about these two ordinary booleans, which is what will eventually make `P` mechanically decidable.
<!--zh-->
现在把一个真函数 `g : (x : Glued) → Pick x` 设为模块参数，暂且悬置「只知道它仅仅存在」这一事实。在两个特殊点处求值 `g` 得到两次选取，其第一分量即布尔值 `b₀` 与 `b₁`：分别在 `true` 的类与 `false` 的类处选出的代表元。随后的全部推理只关乎这两个普通布尔值，这最终使 `P` 得以机械判定。
<!--ja-->
ここで、真の関数 `g : (x : Glued) → Pick x` をモジュールパラメータとして仮定し、「その単なる存在しか知らない」という事実はひとまず据え置きます。二つの注目点で `g` を評価すると二つの選択が得られ、その第一成分がブール値 `b₀` と `b₁`、すなわち `true` の類と `false` の類で選ばれた代表元です。以降の推論はすべてこの二つの生のブール値に関するものであり、それが最終的に `P` を機械的に判定可能にします。
<!--/-->

```agda
  module _ (g : (x : Glued) → Pick x) where

    b₀ : Bool
    b₀ = g [ true ] .fst

    b₁ : Bool
    b₁ = g [ false ] .fst
```

<!--en-->
The first lemma reads a claimed equality `q : b₀ ≡ b₁` backwards into `P`. Compose three paths in `Glued`: from `[ true ]` to `[ b₀ ]` (the guarantee recorded by `g [ true ]`), then from `[ b₀ ]` to `[ b₁ ]` (the equality of classes induced by `q` via `cong [_]`), then from `[ b₁ ]` to `[ false ]` (the guarantee of `g [ false ]`). The composite runs from `[ true ]` to `[ false ]`, and `unglue`{.Agda} converts it into a proof of `⟨ P ⟩`. The second lemma is the forward direction: given a proof `p` of `P`, the gluing path `glue p` identifies the two distinguished points, and applying the picking function pointwise along that path gives `b₀ ≡ b₁`. Because both endpoints are plain booleans, this is a direct congruence projection of `g`, with no transport of the fiber family required.
<!--zh-->
第一条引理把所宣称的相等 `q : b₀ ≡ b₁` 倒读为 `P`。在 `Glued` 中复合三条路径：从 `[ true ]` 到 `[ b₀ ]` (`g [ true ]` 记录的保证)，再从 `[ b₀ ]` 到 `[ b₁ ]` (`q` 经 `cong [_]` 诱导的类相等)，再从 `[ b₁ ]` 到 `[ false ]` (`g [ false ]` 的保证)。复合路径从 `[ true ]` 走到 `[ false ]`，`unglue`{.Agda} 把它转为 `⟨ P ⟩` 的证明。第二条引理是正向：给定 `P` 的证明 `p`，粘合路径 `glue p` 等同两个特殊点，沿这条路径逐点应用选取函数便得 `b₀ ≡ b₁`。两端都是普通布尔值，所以这只是 `g` 的直接同余投影，无需对纤维族做任何搬运。
<!--ja-->
最初の補題は、主張された等式 `q : b₀ ≡ b₁` を逆方向に読んで `P` へ結びます。`Glued` の中で三つの道を合成します。`[ true ]` から `[ b₀ ]` へ (`g [ true ]` が記録した保証)、`[ b₀ ]` から `[ b₁ ]` へ (`q` が `cong [_]` を通して誘導する類の一致)、`[ b₁ ]` から `[ false ]` へ (`g [ false ]` の保証)。合成した道は `[ true ]` から `[ false ]` へ走り、`unglue`{.Agda} がそれを `⟨ P ⟩` の証明に変えます。二番目の補題は順方向です。`P` の証明 `p` が与えられれば、貼り合わせの道 `glue p` が二つの注目点を同一視し、その道に沿って選択関数を点ごとに適用すれば `b₀ ≡ b₁` が得られます。両端は生のブール値なので、これは `g` の直接の合同による射影であり、ファイバーの族の輸送は一切要りません。
<!--/-->

```agda

    agree→P : b₀ ≡ b₁ → ⟨ P ⟩
    agree→P q = unglue (sym (g [ true ] .snd) ∙ cong [_] q ∙ g [ false ] .snd)

    P→agree : ⟨ P ⟩ → b₀ ≡ b₁
    P→agree p i = g (glue p i) .fst
```

<!--en-->
Now decide `P` by looking at the two booleans, which, unlike `P`, **can** be inspected: two booleans are equal or they are not, mechanically. If `b₀` and `b₁` agree, the first lemma proves `P`. If they differ, `P` must fail, for had it held, the second lemma would force them to agree. Either way `P` is decided, and note what carries the decision: the case split happened on the two chosen booleans, not on `P` itself.
<!--zh-->
现在改由那两个布尔值来判定 `P`。与 `P` 不同，它们**可以**被检视：两个布尔值要么相等要么不等，机械可判。若 `b₀` 与 `b₁` 一致，第一条引理证出 `P`。若二者相异，`P` 必不成立，因为它若成立，第二条引理将迫使二者一致。无论哪边 `P` 都被判定；注意承载判定的是什么：分情形发生在选出的两个布尔值上，从头到尾不触及 `P` 自身。
<!--ja-->
いまや二つのブール値を見て `P` を判定できます。`P` とは違って、ブール値は**検査できる**からです。二つのブール値は機械的に、等しいか等しくないかのどちらかです。`b₀` と `b₁` が一致すれば、最初の補題が `P` を証明します。異なっていれば `P` は成り立たないはずです。もし成り立てば、二番目の補題が両者の一致を強いるからです。いずれにせよ `P` は判定されます。判定を担うものに注目してください。場合分けは選ばれた二つのブール値の上で行われたのであり、`P` 自身には一切触れていません。
<!--/-->

<!--en-->
The decidable equality `_≟_` on booleans compares `b₀` with `b₁` and returns a value of `Dec (b₀ ≡ b₁)`: either a `yes`{.Agda} carrying the equality proof, or a `no`{.Agda} carrying a refutation. The helper `fromDec` converts each outcome through the dictionary. In the `yes`{.Agda} case, the equality `q` feeds `agree→P`, producing the left summand, the proof of `⟨ P ⟩`.
<!--zh-->
布尔值上的可判定相等 `_≟_` 比较 `b₀` 与 `b₁`，返回 `Dec (b₀ ≡ b₁)` 的值：要么是携带相等证明的 `yes`{.Agda}，要么是携带反驳的 `no`{.Agda}。辅助函数 `fromDec` 经词典转换每种结果。在 `yes`{.Agda} 情形，相等 `q` 送入 `agree→P`，产出左侧和项，即 `⟨ P ⟩` 的证明。
<!--ja-->
ブール値上の判定可能な等式 `_≟_` が `b₀` と `b₁` を比較し、`Dec (b₀ ≡ b₁)` の値を返します。等式の証明を伴う `yes`{.Agda} か、反証を伴う `no`{.Agda} のどちらかです。補助関数 `fromDec` が辞書を通してそれぞれの結果を変換します。`yes`{.Agda} の場合は等式 `q` が `agree→P` に渡り、左の和成分、すなわち `⟨ P ⟩` の証明が生まれます。
<!--/-->

```agda
    decide : ⟨ P ⟩ Sum.⊎ (⟨ P ⟩ → Empty.⊥)
    decide = fromDec (b₀ ≟ b₁)
      where
      fromDec : Dec (b₀ ≡ b₁) → ⟨ P ⟩ Sum.⊎ (⟨ P ⟩ → Empty.⊥)
      fromDec (yes q) = Sum.inl (agree→P q)
```

<!--en-->
In the `no`{.Agda} case, `ne` is a proof that `b₀` and `b₁` cannot be equal. If `P` held, `P→agree` would exhibit them as equal, contradicting `ne`; so the right summand is the function that takes any proof of `⟨ P ⟩`, applies the forward lemma to obtain `b₀ ≡ b₁`, and hands it to `ne`. Together with the previous case this decides `P`, with the case split performed only on boolean data.
<!--zh-->
在 `no`{.Agda} 情形，`ne` 是 `b₀` 与 `b₁` 不可能相等的证明。若 `P` 成立，`P→agree` 会给出二者相等，与 `ne` 矛盾；于是右侧和项是这样的函数：取任一 `⟨ P ⟩` 的证明，经正向引理得到 `b₀ ≡ b₁`，再交给 `ne`。与上一情形合起来，`P` 被判定，而分情形只在布尔数据上进行。
<!--ja-->
`no`{.Agda} の場合、`ne` は `b₀` と `b₁` が等しくありえないことの証明です。もし `P` が成り立てば `P→agree` が両者の等しさを示し、`ne` と衝突します。そこで右の和成分は、`⟨ P ⟩` の任意の証明を受け取り、順方向の補題で `b₀ ≡ b₁` を得て、それを `ne` に渡す関数です。前の場合と合わせて `P` は判定され、場合分けはブール値のデータの上だけで行われています。
<!--/-->

```agda
      fromDec (no ne) = Sum.inr (λ p → ne (P→agree p))
```

<!--en-->
One last gap and the theorem assembles. Choice never hands over an actual picking function, only its *mere* existence. But the goal "`P` or not `P`" is itself a proposition: the two sides exclude each other, so between any two decisions there is nothing to distinguish. Into such a goal, mere existence eliminates as if it were actual, and the proof closes.
<!--zh-->
补上最后一步，定理即告完成。选择并未真正交出选取函数，只交出它的**仅仅**存在。但目标「`P` 或非 `P`」自身是命题：两侧互斥，任何两个判定之间无可区分。对这样的目标，仅仅存在可以当作真实存在来消去，证明就此闭合。
<!--ja-->
最後の一段を埋めれば定理が組み上がります。選択原理が渡すのは実際の選択関数ではなく、その**単なる**存在にすぎません。しかし目標「`P` または `P` でない」はそれ自身が命題です。両側は互いに排反し、二つの判定の間に区別できるものが何もないからです。そのような目標への消去では、単なる存在は実際の存在であるかのように扱えて、証明が閉じます。
<!--/-->

<!--en-->
The certification that the goal is a proposition is explicit: `Sum.isProp⊎`{.Agda} needs the propositionhood of each side and a proof that no element can inhabit both. The first side is `⟨ P ⟩`, propositional by `P .snd`; the second is a function type into the empty type, propositional because any two such functions agree on every input, where the exclusion proof `λ p np → np p` shows the type of such inhabitants is empty. The final theorem `choice→lem`{.Agda} then has type `SetChoice ℓ → LEM ℓ`: given `sc` and an `hProp`{.Agda} `P`, it works inside the Diaconescu module at `P`, obtains the mere picker by `merePicker sc`, and eliminates the truncation with `PT.rec`{.Agda} into the now-certified propositional goal, returning `decide`. The order of ideas matters: the case split inside `decide` is genuine data, and the truncation is discharged only because the target cannot distinguish its answers.
<!--zh-->
「目标是命题」需要显式证明：`Sum.isProp⊎`{.Agda} 要求两侧各自的命题性，以及两侧不能同时有元的证明。第一侧是 `⟨ P ⟩`，由 `P .snd` 给出命题性；第二侧是到空类型的函数类型，它之所以是命题，是因为任何两个这样的函数在每个输入处一致，而互斥证明 `λ p np → np p` 表明该类型的元是空的。最终定理 `choice→lem`{.Agda} 的类型是 `SetChoice ℓ → LEM ℓ`：给定 `sc` 与 `hProp`{.Agda} 值的 `P`，它在 `P` 处进入 Diaconescu 模块，用 `merePicker sc` 得到仅仅的选取函数，再以 `PT.rec`{.Agda} 把命题截断消去到已证为命题的目标中，返回 `decide`。想法的次序重要：`decide` 内部的分情形是真实数据，截断之所以能消去，只因目标无法区分其答案。
<!--ja-->
目標が命題であることの証明は明示的に与えられます。`Sum.isProp⊎`{.Agda} は両側それぞれの命題性と、両方の元が同時に存在しないことの証明を要求します。第一側は `⟨ P ⟩` であり、`P .snd` によって命題です。第二側は空型への関数型であり、そのような関数はどの入力でも一致するため命題であり、排反の証明 `λ p np → np p` がこの型の元が存在しないことを示します。最終定理 `choice→lem`{.Agda} の型は `SetChoice ℓ → LEM ℓ` です。`sc` と `hProp`{.Agda} の `P` が与えられると、`P` について Diaconescu モジュールの中で働き、`merePicker sc` で単なる選択関数の存在を得て、`PT.rec`{.Agda} によって証明済みの命題である目標へ命題的切り詰めを消去し、`decide` を返します。考えの順序が重要です。`decide` の中の場合分けは本物のデータであり、切り詰めが消去できるのは、目標がその答えたちを区別できないからにすぎません。
<!--/-->

```agda
  decideIsProp : isProp (⟨ P ⟩ Sum.⊎ (⟨ P ⟩ → Empty.⊥))
  decideIsProp = Sum.isProp⊎ (P .snd) (isPropΠ (λ _ → Empty.isProp⊥)) (λ p np → np p)

choice→lem : ∀ {ℓ} → SetChoice ℓ → LEM ℓ
choice→lem sc P = PT.rec decideIsProp decide (merePicker sc)
  where open Diaconescu P
```

<!--en-->
## Recap

`SetChoice`{.Agda} is the book's choice interface, one level at a time, in the same shape as `LEM`{.Agda}; and by `choice→lem`{.Agda} it is the stronger of the two in one direction: choice decides every proposition of its level, through the glued booleans, the `glue`{.Agda}/`unglue`{.Agda} dictionary, and one comparison of chosen representatives. The two interfaces therefore remain distinct as displayed implications: this chapter proves `SetChoice ℓ → LEM ℓ`, and no converse is proved here. The model chapter applies choice to obtain its choice set, and closes by using this chapter's theorem: one instance of choice, one universe up, suffices for all the classical reasoning that follows.
<!--zh-->
## 小结

`SetChoice`{.Agda} 是本书的选择接口，逐层级陈述，形状与 `LEM`{.Agda} 相同；而经 `choice→lem`{.Agda}，在一个方向上它是两者中更强的一个：经由粘合布尔值、`glue`{.Agda}/`unglue`{.Agda} 词典与一次代表元比较，选择判定其层级的每个命题。因此，作为已证的蕴含，两个接口仍然分立：本章证明的是 `SetChoice ℓ → LEM ℓ`，而其逆并未在此证明。模型章将把选择用于选择集，并在收尾处应用本章定理：高一层宇宙上的一份选择，即可支持后文所需的全部经典推理。
<!--ja-->
## まとめ

`SetChoice`{.Agda} は本書の選択のインターフェースであり、`LEM`{.Agda} と同じ形でレベルごとに述べられます。そして `choice→lem`{.Agda} により、一つの向きについては両者のうち強い方です。貼り合わせたブール値、`glue`{.Agda}/`unglue`{.Agda} の辞書、選ばれた代表元の一度の比較を通して、選択原理はそのレベルのすべての命題を判定します。したがって、証明された含意としては二つのインターフェースは区別されたままです。本章が示すのは `SetChoice ℓ → LEM ℓ` であり、逆はここでは証明されません。モデルの章は選択原理を選択集合の構成に用い、締めくくりに本章の定理を使います。一つ上の宇宙における選択原理の仮定一つで、その後に続くすべての古典的推論が賄えるのです。
<!--/-->
