<!--en-->
# Choice

Classical mathematics does not rest on excluded middle alone. Given a family of nonempty sets, one may pick one element from each set simultaneously; for a finite or explicitly described family this is routine, but for a family indexed by an arbitrary set it is a genuine principle, the axiom of choice. Type theory sharpens what "nonempty" can mean here. In the base theory, the elements of a fiber `B x` hide behind its propositional truncation `∥ B x ∥₁`, which records that the fiber has an element and forgets which one. A truncation eliminates only into propositions, so no actual element can be extracted from a hypothesis of this shape. The Prelude noted that extracting a genuine function from a truncated existential requires a choice principle. The hypothesis of the principle is therefore that every fiber is *merely* inhabited. The conclusion keeps the truncation as well: it claims the mere existence of one function choosing in every fiber at once, never the function itself. The statement includes one restriction from the start: the index type must be an h-set, and the proof of Diaconescu's theorem will need exactly this.

Set-level choice and `LEM`{.Agda} are both stated one level at a time, so their families have the same outer type `∀ ℓ → Type (ℓ-suc ℓ)`. Their internal quantifiers are different: excluded middle ranges over propositions, while choice ranges over an h-set `X`, a family `B` over it, and proofs that its fibers are merely inhabited. Neither principle is assumed globally; a chapter that needs one takes the instance at the required level as an explicit parameter.

Three questions organize the chapter. What does choice assert here, and at which levels? Does one assumption at a higher universe cover the levels below? And how strong is the principle? Diaconescu's theorem answers the last one: `SetChoice ℓ` implies `LEM ℓ`, proved as `choice→lem`{.Agda}, so at each level the choice interface already yields excluded middle, and the two interfaces are not peers. The model chapter draws on this twice: `choice→lem`{.Agda} obtains from a single `SetChoice (ℓ-suc ℓ)` the excluded middle that drives its ZF axioms, and `lowerSetChoice`{.Agda} lowers the same instance for the choice-set axiom.
<!--zh-->
# 选择原理

经典数学并不只有排中律。给定一族非空集合，可以同时从每个集合中各取一个元素；对有限或显式描述的族，这是例行手续，而对以任意集合为指标的族，它是一条真正的原理，即选择公理。类型论把这里的「非空」严格化了。在基础理论中，纤维 `B x` 的元素藏在它的命题截断 `∥ B x ∥₁` 之后：截断记录纤维有元素，却忘去是哪个元素。截断只能向命题消去，所以从这种形状的假设取不出真实的元素。《基础词汇》指出过：要从截断的存在陈述取出一个真正的函数，需要一条选择原理。因此这条原理的假设只能是每根纤维都仅仅有元。结论同样保留截断：它断言的是一个同时在每根纤维中取值的函数的仅仅存在，而不是函数本身。陈述从一开始就含有一项限制：指标类型必须是 h-集合；Diaconescu 定理的证明正需要这一点。

集合层选择与 `LEM`{.Agda} 都逐层级陈述，因此两族具有相同的外层类型 `∀ ℓ → Type (ℓ-suc ℓ)`。二者内部量化的对象不同：排中律遍历命题，选择则遍历 h-集合 `X`、其上的族 `B`，以及各纤维仅仅有元的证明。两项原理都不被全局假设；需要其中一项时，章节会把所需层级的实例作为显式参数。

本章围绕三个问题展开。选择原理在这里断言什么，在哪些层级上断言？高一层宇宙的一个假设能否覆盖其下的层级？这条原理又有多强？最后一个问题由 Diaconescu 定理回答：`SetChoice ℓ` 蕴含 `LEM ℓ`，即 `choice→lem`{.Agda}。因此在每个层级上，选择接口都已给出排中律，两个接口并不平级。模型章两度依赖这一点：`choice→lem`{.Agda} 从一个 `SetChoice (ℓ-suc ℓ)` 实例取得驱动 ZF 公理的排中律，`lowerSetChoice`{.Agda} 把同一实例降到所需层级，供选择集公理使用。
<!--ja-->
# 選択原理

古典数学で用いられる原理は、排中律だけではありません。空でない集合の族が与えられれば、各集合から同時に一つずつ要素を選べます。有限の族や明示的に記述された族なら日常的な手続きですが、任意の集合で添字付けられた族に対しては、これは選択公理という固有の原理です。型理論は、ここでいう「空でない」をいっそう正確にします。基礎理論では、ファイバー `B x` の元は命題的切り詰め `∥ B x ∥₁` の後ろに隠れています。切り詰めはファイバーに元があることを記録しますが、どの元かは忘れます。切り詰めは命題へしか消去できないので、この形の仮定から実際の元を取り出すことはできません。「基礎語彙」は、切り詰められた存在から本物の関数を取り出すには選択原理が要ると述べました。したがってこの原理の仮定は、各ファイバーが単に要素を持つ、という形をしか取れません。結論にも切り詰めが残ります。主張されるのは、すべてのファイバーで同時に値を選ぶ一つの関数の単なる存在であり、関数そのものではありません。この主張には最初から一つの制限が含まれます。添字の型は h-集合でなければならず、ディアコネスクの定理の証明はまさにこれを用います。

集合レベルの選択と `LEM`{.Agda} は、どちらもレベルごとに述べられるので、その族の外側の型は同じ `∀ ℓ → Type (ℓ-suc ℓ)` です。ただし、内側で量化する対象は異なります。排中律は命題全体にわたり、選択は h-集合 `X`、その上の族 `B`、そして各ファイバーが単に要素を持つことの証明にわたります。どちらの原理も大域的には仮定されず、必要とする章は所定のレベルの実例を明示的なパラメータとして受け取ります。

本章は三つの問いを中心に進みます。選択原理はここで何を主張し、どのレベルで主張するのか。一つ上の宇宙の仮定一つで、それより下のレベルを覆えるのか。そしてこの原理はどれほど強いのか。最後の問いにディアコネスクの定理が答えます。`SetChoice ℓ` は `LEM ℓ` を含意します (`choice→lem`{.Agda})。したがって各レベルで選択のインターフェースはすでに排中律を与え、二つのインターフェースは対等ではありません。モデルの章はこのことを二度頼ります。`choice→lem`{.Agda} が一つの `SetChoice (ℓ-suc ℓ)` の実例から ZF の公理を支える排中律を得て、`lowerSetChoice`{.Agda} が同じ実例を下げて選択集合の公理に用います。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

module Base.Choice where

open import Base.Prelude
open import Cubical.Foundations.Prelude using ( Path )
open import Cubical.Foundations.HLevels using ( isOfHLevelLift )
open import Cubical.Data.Sum using ( isProp⊎ )
open import Base.Classical using ( LEM )
```

<!--en-->
The proof of Diaconescu's theorem is a finite argument, and it uses three concrete pieces. The booleans `Bool`{.Agda} with `true`{.Agda} and `false`{.Agda} form a two-point type whose equality `_≟_`{.Agda} decides. The unit type `⊤*`{.Agda} holds the single element `tt*`{.Agda}, and `isProp⊤*`{.Agda} records it as a proposition, so the argument has a trivially true statement available wherever one is needed. A comparison of two booleans returns an element of `Dec`{.Agda}: either `yes`{.Agda} with the equality, or `no`{.Agda} with its refutation.
<!--zh-->
Diaconescu 定理的证明是一个有限论证，用到三份具体材料。布尔类型 `Bool`{.Agda} 连同 `true`{.Agda} 与 `false`{.Agda} 构成两点类型，其相等由 `_≟_`{.Agda} 判定。单元类型 `⊤*`{.Agda} 有唯一元素 `tt*`{.Agda}，`isProp⊤*`{.Agda} 记录它为命题，论证由此随处可得一条平凡成立的陈述。两个布尔值的比较返回 `Dec`{.Agda} 的元素：要么 `yes`{.Agda} 连同相等，要么 `no`{.Agda} 连同反驳。
<!--ja-->
ディアコネスクの定理の証明は有限の議論であり、三つの具体的な材料を用います。ブール型 `Bool`{.Agda} と `true`{.Agda}、`false`{.Agda} は二点の型をなし、その等しさは `_≟_`{.Agda} が判定します。単元型 `⊤*`{.Agda} は唯一の元 `tt*`{.Agda} を持ち、`isProp⊤*`{.Agda} がこれを命題として記録するので、議論には自明に成り立つ主張がいつでも用意できます。二つのブール値の比較は `Dec`{.Agda} の元を返します。`yes`{.Agda} に等式が伴うか、`no`{.Agda} に反証が伴うかです。
<!--/-->

```agda
open import Cubical.Data.Bool using ( Bool; true; false; _≟_ )
open import Cubical.Relation.Nullary using ( Dec; yes; no )
```

<!--en-->
Beyond these, the proof needs two constructions. The first is propositional truncation `∥_∥₁`{.Agda}, introduced in the Prelude: it keeps exactly the inhabitedness of a type and forgets which element was there, so from `∥ A ∥₁` one never extracts an inhabitant of `A` itself. The second is the set quotient, which appears in this book for the first time here; from a type and a relation it builds the type of classes, and the Diaconescu construction is carried out inside one.
<!--zh-->
除此之外，证明还需要两个构造。第一个是命题截断 `∥_∥₁`{.Agda}，《基础词汇》已经介绍：它恰好保留一个类型的有元性，忘去元素是哪一个，所以从 `∥ A ∥₁` 取不出 `A` 自身的元素。第二个是集合商，本书在此首次用到；它从类型与关系构造类所成的类型，Diaconescu 构造就将在一个集合商内部进行。
<!--ja-->
このほか、証明には二つの構成が要ります。第一は命題的切り詰め `∥_∥₁`{.Agda} で、「基礎語彙」で紹介しました。型の有元性だけを保ち、それがどの元であったかを忘れるので、`∥ A ∥₁` から `A` 自身の元を取り出すことはできません。第二は集合商で、本書で初めて登場します。型と関係から類からなる型を作るもので、ディアコネスクの構成はその内部で行われます。
<!--/-->

```agda
open import Cubical.HITs.SetQuotients
  using ( _/_; [_]; eq/; squash/; []surjective; effective )
```

<!--en-->
A set quotient can be formed from any relation. The stronger effectivity theorem used here, which reads equality of quotient classes back as the original relation, requires that relation to be proposition-valued and to satisfy the equivalence laws. The library expresses these two requirements as records, and the gluing relation will be proved to meet both.
<!--zh-->
任意关系都可以生成集合商。本章还要使用更强的 effectivity 定理，把商类的相等反向读成原关系；这条定理要求关系取值于命题并满足等价律。库以 record 表述这两项条件，粘合关系将分别证明它们。
<!--ja-->
集合商そのものは任意の関係から作れます。ここで用いるより強い effectivity 定理は、商類の等しさを元の関係へ逆向きに読むものであり、関係が命題値で同値律を満たすことを要求します。ライブラリはこの二つの条件をレコードで表し、貼り合わせの関係が両方を満たすことをそれぞれ証明します。
<!--/-->

```agda
open import Cubical.Relation.Binary.Base using ( module BinaryRelation )
```

<!--en-->
## The principle

The principle compares, at one fixed level `ℓ`, a hypothesis about each fiber with a conclusion about all fibers at once. The data are an index type `X` in `Type ℓ`, the proof that `X` is an h-set, a family `B` of fibers over `X`, and the hypothesis `∥ B x ∥₁` for every `x`. The conclusion `∥ ((x : X) → B x) ∥₁` says that merely, one function chooses an inhabitant in every fiber simultaneously. The truncation appears on both sides, and this is the principle's exact strength. The hypothesis gives nothing beyond mere inhabitation, so the conclusion claims no more than the same; an actual choice function is exactly what is missing, and supplying it is the whole content of the assumption. Since the statement quantifies over all of `Type ℓ`, it lives one level up, at `Type (ℓ-suc ℓ)`, for the same reason as `LEM`{.Agda}.
<!--zh-->
## 原理

原理在固定的层级 `ℓ` 上比较一个关于每根纤维的假设与一个关于全体纤维的结论。数据是 `Type ℓ` 中的指标类型 `X`、`X` 是 h-集合的证明、`X` 上的纤维族 `B`，以及对每个 `x` 的假设 `∥ B x ∥₁`。结论 `∥ ((x : X) → B x) ∥₁` 说的是，仅仅存在一个同时在每根纤维中取元的函数。截断出现在两侧，这正是原理的准确强度。假设给出的不超过仅仅有元，结论断言的也不超过仅仅存在；真实的选择函数恰是缺失的东西，把它造出来正是这条假设的全部内容。由于陈述量化了整个 `Type ℓ`，它居于高一层的 `Type (ℓ-suc ℓ)`，理由与 `LEM`{.Agda} 相同。
<!--ja-->
## 原理

原理は、固定したレベル `ℓ` の上で、各ファイバーについての仮定と、すべてのファイバーを一度に扱う結論とを比べます。データは、`Type ℓ` の添字型 `X`、`X` が h-集合であることの証明、`X` の上のファイバーの族 `B`、そして各 `x` に対する仮定 `∥ B x ∥₁` です。結論 `∥ ((x : X) → B x) ∥₁` が言うのは、すべてのファイバーで同時に要素を選ぶ一つの関数が単に存在することです。切り詰めが両側に現れるのが、この原理の正確な強さです。仮定が与えるのは単なる要素の存在までであり、結論もそれ以上を主張しません。実際の選択関数こそ欠けているものであり、それを供給することがこの仮定の内容のすべてです。主張が `Type ℓ` 全体を量化するため、`LEM`{.Agda} と同じ理由で、それは一つ上の `Type (ℓ-suc ℓ)` に住みます。
<!--/-->

```agda
SetChoice : ∀ ℓ → Type (ℓ-suc ℓ)
SetChoice ℓ = (X : Type ℓ) → isSet X → (B : X → Type ℓ)
            → ((x : X) → ∥ B x ∥₁) → ∥ ((x : X) → B x) ∥₁
```

<!--en-->
Like excluded middle, choice in an application is often handed only one higher-level instance, and a descent lemma brings it to the level at hand. `lowerSetChoice` has type `SetChoice (ℓ-suc ℓ) → SetChoice ℓ`: assume choice one universe up, recover it at level `ℓ`. As in `lowerLEM`{.Agda}, the tool is `Lift`, the Prelude's operation for presenting a type of `Type ℓ` inside `Type (ℓ-suc ℓ)` and taking it back.

Given data at level `ℓ`, the proof first moves it one level up, where the hypothesis `sc` applies. The index type `X` becomes `Lift X`, and its h-set condition follows from `setX` by `isOfHLevelLift`, which records that lifting does not disturb homotopy level. The family becomes `λ x → Lift (B (lower x))`: a fiber over a lifted index is the lifted fiber over the index beneath it, so the moved family contains exactly the information of the original.
<!--zh-->
与排中律一样，应用中的选择往往只拿到一个高层实例，再由一条下降引理把它换到所需的层级。`lowerSetChoice` 的类型是 `SetChoice (ℓ-suc ℓ) → SetChoice ℓ`：假设高一层宇宙的选择，恢复层级 `ℓ` 的选择。与 `lowerLEM`{.Agda} 一样，这里使用的工具是 `Lift`，即《基础词汇》中把 `Type ℓ` 的类型放进 `Type (ℓ-suc ℓ)` 中呈现、再取回来的运算。

给定层级 `ℓ` 的数据，证明先把它搬到高一层，使假设 `sc` 得以适用。指标类型 `X` 变为 `Lift X`，其 h-集合性由 `setX` 经 `isOfHLevelLift` 得到，库中这条定理说明抬升不扰动同伦层级。纤维族变为 `λ x → Lift (B (lower x))`：抬升指标上的纤维就是底下原指标上纤维的抬升，所以移动后的族与原族包含完全相同的信息。
<!--ja-->
排中律と同様、応用で使う選択にはしばしば一つの高いレベルの実例だけが渡され、下降の補題がそれを必要なレベルへ移します。`lowerSetChoice` の型は `SetChoice (ℓ-suc ℓ) → SetChoice ℓ` です。一つ上の宇宙の選択を仮定して、レベル `ℓ` の選択を取り戻します。`lowerLEM`{.Agda} と同じく、ここで用いる道具は `Lift` です。「基礎語彙」にある、`Type ℓ` の型を `Type (ℓ-suc ℓ)` の中で提示し、また取り戻す演算です。

レベル `ℓ` のデータが与えられると、証明はまずそれを一つ上のレベルへ移し、仮定 `sc` を適用できるようにします。添字型 `X` は `Lift X` となり、その h-集合性は `setX` から `isOfHLevelLift` によって従います。これは、持ち上げがホモトピーレベルを乱さないことを記録するライブラリの定理です。ファイバーの族は `λ x → Lift (B (lower x))` となります。持ち上げられた添字の上のファイバーは、その下の元の添字の上のファイバーを持ち上げたものであり、移した族は元の族とまったく同じ情報を含みます。
<!--/-->

```agda
lowerSetChoice : ∀ {ℓ} → SetChoice (ℓ-suc ℓ) → SetChoice ℓ
lowerSetChoice sc X setX B inh =
  map₁ (λ f x → lower (f (lift x)))
         (sc (Lift X) (isOfHLevelLift 2 setX)
             (λ x → Lift (B (lower x)))
```

<!--en-->
The remaining inputs are transferred in the same way. Each lifted fiber is merely inhabited, because lowering its index and mapping `lift` over the resulting truncation exhibits the required element; `map₁`{.Agda} acts inside the truncation, so the hypothesis holds in exactly the form the principle demands. When `sc` returns the mere existence of a lifted choice function `f`, one further `map₁`{.Agda} produces the mere existence of the lowered function, whose value at `x` is `lower (f (lift x))`. The final step is legitimate because the goal is a statement inside a truncation: about the particular `f`, nothing is ever claimed outside it.
<!--zh-->
其余输入以同样的方式移动。每个抬升纤维都仅仅有元，因为把指标降下、再对所得截断映射 `lift`，就给出所需的元素；`map₁`{.Agda} 在截断内部作用，所以假设恰以原理所要求的形式成立。当 `sc` 返回抬升选择函数 `f` 的仅仅存在时，再一次 `map₁`{.Agda} 给出降低后函数的仅仅存在，其在 `x` 处的值为 `lower (f (lift x))`。最后一步之所以合法，是因为目标是截断内部的陈述：至于这个具体的 `f`，截断之外没有任何主张。
<!--ja-->
残りの入力も同じ方法で移します。持ち上げられた各ファイバーが単に要素を持つのは、添字を降ろし、得られた切り詰めに `lift` を写像すれば必要な元が示されるからです。`map₁`{.Agda} は切り詰めの内部で働くので、仮定は原理が求める通りの形で満たされます。`sc` が持ち上げられた選択関数 `f` の単なる存在を返したら、もう一度の `map₁`{.Agda} が降ろした関数の単なる存在を与え、その `x` での値は `lower (f (lift x))` です。最後の一段が正当なのは、目標が切り詰めの内部の主張だからです。この具体的な `f` について、切り詰めの外で主張されることは何もありません。
<!--/-->

```agda
             (λ x → map₁ lift (inh (lower x))))
```

<!--en-->
## Diaconescu's theorem

The theorem reads: given set-level choice, every proposition `P` can be decided, proved or refuted. From a constructive viewpoint this conclusion is far from evident, since an arbitrary `P` offers no case to split on; a decision procedure has nothing to inspect directly. The proof approaches the question geometrically instead. It builds a small space whose shape depends on `P`: in it, the classes of `true` and `false` coincide exactly when `P` holds. One question about this space, put to choice, forces the shape into the open, and the shape is `P`.

Concretely, fix a proposition `P : hProp ℓ` and work in a module dedicated to the theorem. Take the two booleans and glue them together exactly when `P` holds. Gluing is a set quotient: the points are still `true` and `false`, a path is added between them whenever the gluing relation says so, and the result is made into an h-set. The relation is a table with four entries: trivially true on the diagonal, and literally `P` itself in the two mixed squares. By that last clause, being related across the two points is the same statement as `P`, and the argument uses it twice.
<!--zh-->
## Diaconescu 定理

定理说的是：给定集合层选择，任何命题 `P` 都可判定，即或证明或反驳。从构造性的观点看，这个结论远非显然：任意的 `P` 不提供可供分情况处理的切入口，判定程序也没有可以直接检视的内容。证明转而从几何入手。它构造一个形状依赖于 `P` 的小空间：其中 `true` 的类与 `false` 的类恰在 `P` 成立时重合。把这个空间上的一个问题交给选择原理，形状便暴露出来，而形状就是 `P`。

具体地，固定命题 `P : hProp ℓ`，在一个专属于该定理的模块中工作。取两个布尔值，恰在 `P` 成立时把它们粘起来。粘合即集合商：点仍是 `true` 与 `false`，但凡粘合关系如此断言，就添一条路径，结果做成 h-集合。关系是一张四格表：对角格平凡成立，混色的两格就是 `P` 本身。由最后这一条，「跨两点相关」与 `P` 是同一个陈述，论证将两次用到它。
<!--ja-->
## ディアコネスクの定理

定理はこう述べます。集合レベルの選択が与えられれば、任意の命題 `P` は判定できる、すなわち証明か反証のいずれかが得られます。構成的な立場から見れば、この結論は決して明らかではありません。任意の `P` は場合分けの入口を与えず、判定手続きが直接調べられるものもないからです。そこで証明は幾何的に進みます。形が `P` に応じて変わる小さな空間を作ります。その空間で `true` の類と `false` の類は、`P` が成り立つとき、そしてそのときに限って一致します。この空間についてのただ一つの質問を選択原理に投げれば、形は白日の下にさらされ、その形こそが `P` です。

具体的には、命題 `P : hProp ℓ` を固定し、この定理専用のモジュールの中で作業します。二つのブール値を、`P` が成り立つときちょうど貼り合わせます。貼り合わせとは集合商のことです。点は `true` と `false` のまま保たれ、貼り合わせの関係がそう述べるときには道が加えられ、結果は h-集合にされます。関係は四項の表です。対角では自明に成り立ち、混色の二項は文字どおり `P` そのものです。この最後の条項により、二点をまたぐ関係が成り立つことは `P` と同じ主張であり、議論はこれを二度使います。
<!--/-->

<!--en-->
The gluing relation `_~_` is defined by pattern matching on the two booleans, so the four entries of the table are visible at once. When the two inputs agree, the relation holds with the one element `tt*`{.Agda} of the unit type `⊤*`{.Agda}. When they differ, it holds with a proof of `⟨ P ⟩`, the statement underlying `P`. Nothing else is used: reading the mixed squares off the table is already the proof that being related across the two points says exactly `P`.
<!--zh-->
粘合关系 `_~_` 由对两个布尔值的模式匹配定义，表中四格一目了然。两个输入一致时，关系以单元类型 `⊤*`{.Agda} 的唯一元素 `tt*`{.Agda} 成立。二者相异时，关系以 `⟨ P ⟩` 的一个证明成立，即 `P` 的底层陈述。此外别无他用：从表中读出混色两格，就已经证明了跨两点相关所说的恰是 `P`。
<!--ja-->
貼り合わせの関係 `_~_` は二つのブール値へのパターンマッチで定義され、表の四項が一目で分かります。入力が一致するとき、関係は単元型 `⊤*`{.Agda} の唯一の元 `tt*`{.Agda} とともに成り立ちます。異なるときは、`⟨ P ⟩`、すなわち `P` の基礎となる主張の証明とともに成り立ちます。ほかに使うものは何もありません。表の混色の項を読み取ることが、二点をまたぐ関係がまさに `P` を述べていることの証明になっています。
<!--/-->

```agda
module Diaconescu {ℓ} (P : hProp ℓ) where

  _~_ : Bool → Bool → Type ℓ
  true  ~ true  = ⊤*
  false ~ false = ⊤*
  _     ~ _     = ⟨ P ⟩
```

<!--en-->
The space itself, `Glued`, is the set quotient `Bool / _~_`. A set quotient of a type by a relation keeps the points and adds a path `[ b ] ≡ [ b' ]`{.Agda} whenever the relation is proved to relate them, by the constructor `eq/`{.Agda}; the further constructor `squash/`{.Agda} makes the result an h-set. Its two distinguished points are the classes `[ true ]`{.Agda} and `[ false ]`{.Agda}. When `P` holds, the quotient supplies the path between them; when `P` fails, the backward reading below shows the two classes apart.
<!--zh-->
空间本身 `Glued` 是集合商 `Bool / _~_`。类型按关系取商时，点被保留，而只要给出关系关联二者的证明，构造子 `eq/`{.Agda} 就添加路径 `[ b ] ≡ [ b' ]`{.Agda}；构造子 `squash/`{.Agda} 再把结果做成 h-集合。它的两个特殊点是类 `[ true ]`{.Agda} 与 `[ false ]`{.Agda}。`P` 成立时，商在两点间提供路径；`P` 不成立时，下面的倒读会把两类分开。
<!--ja-->
空間そのものである `Glued` は集合商 `Bool / _~_` です。型を関係で割ると、点は保たれ、関係が二者を結ぶ証明が与えられるたびに、構成子 `eq/`{.Agda} が道 `[ b ] ≡ [ b' ]`{.Agda} を加えます。構成子 `squash/`{.Agda} はさらに結果を h-集合にします。注目する二点は類 `[ true ]`{.Agda} と `[ false ]`{.Agda} です。`P` が成り立てば商が両者の間の道を供給し、成り立たなければ、後の逆読みが二つの類を引き離します。
<!--/-->

```agda

  Glued : Type ℓ
  Glued = Bool / _~_
```

<!--en-->
Everything now rests on one theorem about set quotients, the library's effectivity: for a relation that is proposition-valued and satisfies the equivalence laws, a path between classes exists only because the relation related the representatives. A path in the quotient can therefore be read backwards, into a proof of the relation. The table provides each condition the theorem asks for, and the next paragraphs verify them entry by entry.
<!--zh-->
此后的一切都系于集合商的一条定理，即库的有效性：对取值于命题且满足等价律的关系，类与类之间的路径之所以存在，只是因为关系确实关联了代表元。因此商中的路径可以倒读为关系成立的证明。表格逐格供应该定理所要求的各个条件，下面几段逐一验证。
<!--ja-->
この先のすべては、集合商についての一条の定理、ライブラリの有効性にかかっています。命題値で同値律を満たす関係に対して、類の間の道が存在するのは、関係が実際に代表元を結んだとき、そのときに限ります。したがって商の中の道は、関係が成り立ったことの証明として逆読みできます。表はこの定理の要求する条件を項ごとに供給し、続く段落が一つずつ検証します。
<!--/-->

<!--en-->
The first condition is proposition-valuedness: for each pair of inputs, the type of proofs of `a ~ b` must be a proposition. On the diagonal that type is `⊤*`{.Agda}, a proposition by `isProp⊤*`{.Agda}; in the mixed squares it is `⟨ P ⟩` itself, and its propositionhood is exactly the certificate `⟨ P ⟩isProp`{.Agda}. Were proofs allowed to differ, a path in the quotient would not determine a well-defined statement to read back.
<!--zh-->
第一个条件是命题值性：对每对输入，`a ~ b` 的证明类型必须是命题。对角线上该类型是 `⊤*`{.Agda}，由 `isProp⊤*`{.Agda} 知其为命题；混色两格中它就是 `⟨ P ⟩` 自身，其命题性恰是 `P` 的证书 `⟨ P ⟩isProp`{.Agda}。若证明可以彼此不同，商中的路径就无法确定一个良定义的陈述供倒读。
<!--ja-->
第一の条件は命題値性です。入力の各組に対して、`a ~ b` の証明の型が命題でなければなりません。対角ではこの型は `⊤*`{.Agda} であり、`isProp⊤*`{.Agda} が命題であることを示します。混色の項では `⟨ P ⟩` そのものであり、その命題性は `P` の証明書 `⟨ P ⟩isProp`{.Agda} にほかなりません。証明が異なり得るなら、商の道は逆読みのための well-defined な主張を定められません。
<!--/-->

```agda
  ~-prop : BinaryRelation.isPropValued _~_
  ~-prop true  true  = isProp⊤*
  ~-prop false false = isProp⊤*
  ~-prop true  false = ⟨ P ⟩isProp
  ~-prop false true  = ⟨ P ⟩isProp
```

<!--en-->
Reflexivity is immediate: the two diagonal entries hold unconditionally, so every boolean is related to itself, with `_`{.Agda} as the proof in each case.
<!--zh-->
自反性是直接的：两条对角格无条件成立，于是每个布尔值都与自身相关，各情形的证明都是 `_`{.Agda}。
<!--ja-->
反射性は直ちに得られます。対角の二項は条件なしで成り立つので、すべてのブール値は自分自身と関係を持ち、その場合の証明はいずれも `_`{.Agda} です。
<!--/-->

```agda

  ~-refl : (a : Bool) → a ~ a
  ~-refl true  = tt*
  ~-refl false = tt*

  ~-sym : (a b : Bool) → a ~ b → b ~ a
  ~-sym true  true  _ = tt*
```

<!--en-->
Symmetry holds because the table itself is symmetric: swapping the inputs carries each entry to itself, so a proof of `a ~ b` serves as a proof of `b ~ a`. On the diagonal the proof is `_`{.Agda} either way, and in the mixed squares it is a proof of `P`, the same thing in both directions.
<!--zh-->
对称性成立，因为表本身对称：交换输入把每格映到自身，`a ~ b` 的证明即可充当 `b ~ a` 的证明。对角线上两个方向的证明都是 `_`{.Agda}；混色两格中它是 `P` 的证明，两个方向说的是同一件事。
<!--ja-->
対称性は、表そのものが対称なことから成り立ちます。入力を入れ替えても各項は自分自身に写るので、`a ~ b` の証明は `b ~ a` の証明として働きます。対角ではどちら向きでも証明は `_`{.Agda} であり、混色の項では `P` の証明であり、両方向で同じものです。
<!--/-->

```agda
  ~-sym false false _ = tt*
  ~-sym true  false p = p
  ~-sym false true  p = p

  ~-trans : (a b c : Bool) → a ~ b → b ~ c → a ~ c
  ~-trans true  _     true  _ _ = tt*
```

<!--en-->
Transitivity asks for a little more care, since two proofs could in principle demand an entry the table does not contain. The cases show this cannot happen. Whenever the endpoints agree, a diagonal entry settles the result trivially; whenever they differ, one of the two given proofs comes from a mixed square, and the other then involves only equal booleans, so the same proof of `P` serves as the result. Six cases cover the possibilities, each reusing one of the inputs.
<!--zh-->
传递性要多想一步，因为两个证明的组合原则上可能要求表中不存在的格。逐情形检查可知这不会发生：两端一致时，某条对角格使结论平凡成立；两端相异时，给定的两个证明中必有一个来自混色格，而另一个此时只涉及相等的布尔值，于是同一个 `P` 的证明就充当结论。六个分支覆盖所有情形，每个都复用某个输入。
<!--ja-->
推移性にはもう少しの注意が要ります。二つの証明の組が、表に存在しない項を要求する可能性が原理的にはあるからです。場合を調べれば、それは起こりえないと分かります。両端が一致していれば、どこかの対角の項が結論を自明にします。異なっていれば、与えられた二つの証明のどちらかは混色の項から来ており、もう一方はこのとき等しいブール値しか含まないので、同じ `P` の証明がそのまま結論になります。六つの場合がすべての可能性を覆い、それぞれが入力の一つを再利用します。
<!--/-->

```agda
  ~-trans false _     false _ _ = tt*
  ~-trans true  false false p _ = p
  ~-trans false true  true  p _ = p
  ~-trans true  true  false _ p = p
  ~-trans false false true  _ p = p
```

<!--en-->
The three laws assemble into the record `isEquivRel _~_` by the constructor `BinaryRelation.equivRel`{.Agda}. With proposition-valuedness and the equivalence laws in place, `Glued` meets exactly the hypotheses of effectivity, and the backward reading of its paths is available to the lemmas below.
<!--zh-->
三条定律由构造子 `BinaryRelation.equivRel`{.Agda} 组装为记录 `isEquivRel _~_`。有了命题值性与等价律，`Glued` 便恰好满足有效性的全部假设，其路径的倒读对下面的引理可用。
<!--ja-->
三つの法則は、構成子 `BinaryRelation.equivRel`{.Agda} によってレコード `isEquivRel _~_` に組み立てられます。命題値性と同値律が揃うと、`Glued` は有効性の仮定をちょうど満たし、道の逆読みが以下の補題で使えるようになります。
<!--/-->

```agda

  ~-equivRel : BinaryRelation.isEquivRel _~_
  ~-equivRel = BinaryRelation.equivRel ~-refl ~-sym ~-trans
```

<!--en-->
The core of the construction is a two-line statement: the two distinguished classes coincide exactly when `P` holds. If `P` holds, the table relates `true` to `false`, and the quotient identifies their classes. If the classes coincide, effectivity reports that the relation related `true` to `false`, and by the table that relation is `P`. The mixed squares do the work in both directions: a proof of `P` feeds the path constructor directly, and the output of effectivity is already a proof of `⟨ P ⟩`, with no decoding and no impossible case to dismiss.
<!--zh-->
构造的核心是一个两行论断：两个特殊类重合，当且仅当 `P` 成立。若 `P` 成立，表关联 `true` 与 `false`，商便等同两个类。若两类重合，有效性报告说关系关联了 `true` 与 `false`，而按表，该关系就是 `P`。混色格在两个方向上工作：`P` 的证明直接交给路径构造子，有效性的输出本身已是 `⟨ P ⟩` 的证明，无需解码，也没有需要排除的不可能情形。
<!--ja-->
構成の核心は二行の主張です。二つの注目すべき類が一致するのは、`P` が成り立つとき、そのときに限ります。`P` が成り立てば、表は `true` と `false` を結び、商は両者の類を同一視します。二つの類が一致すれば、有効性は関係が `true` と `false` を結んだと報告し、表によればその関係こそ `P` です。混色の項は両方向で働きます。`P` の証明はそのまま道の構成子に渡り、有効性の出力はすでに `⟨ P ⟩` の証明であり、復号も不可能な場合の除去も要りません。
<!--/-->

<!--en-->
The two directions become named functions. Forward, `glue`{.Agda} hands a proof of `P` to the path constructor: since the mixed entry holds with proof `p`, the two classes are equal by the definition of the quotient. Backward, `unglue`{.Agda} is effectivity instantiated at `true` and `false`: any path between the two classes returns a proof of `true ~ false`, and by the table that is a proof of `⟨ P ⟩`. No case analysis on the path is needed. Together they form a dictionary between `P` and the equality of the two classes.
<!--zh-->
两个方向成为具名函数。正向的 `glue`{.Agda} 把 `P` 的证明交给路径构造子：混色格以证明 `p` 成立，按商的定义两个类相等。反向的 `unglue`{.Agda} 是在 `true` 与 `false` 处例示的有效性：两类之间的任何路径返回 `true ~ false` 的证明，按表即 `⟨ P ⟩` 的证明。无需对路径作任何分情形。二者合起来，构成 `P` 与两类相等之间的词典。
<!--ja-->
二つの向きは名前付きの関数になります。順方向の `glue`{.Agda} は `P` の証明を道の構成子に渡します。混色の項は証明 `p` とともに成り立つので、商の定義により二つの類は等しくなります。逆方向の `unglue`{.Agda} は `true` と `false` で具体化した有効性です。二つの類の間の任意の道が `true ~ false` の証明を返し、表によればそれは `⟨ P ⟩` の証明です。道に対する場合分けは不要です。両者合わせて、`P` と二つの類の一致とを結ぶ辞書になります。
<!--/-->

```agda
  glue : ⟨ P ⟩ → Path Glued [ true ] [ false ]
  glue p = eq/ true false p

  unglue : Path Glued [ true ] [ false ] → ⟨ P ⟩
  unglue = effective ~-prop ~-equivRel true false
```

<!--en-->
Now the choice principle is put to use, with a single question: hand every point of `Glued` a boolean representative. A pick at a point is a boolean together with the guarantee that its class equals that point. Each point on its own is sure to have one, but only merely so: a quotient remembers that its points come from representatives without remembering which. Converting this pointwise mere inhabitation into the mere existence of one function choosing everywhere at once is exactly what set-level choice states, and it applies here because `Glued` is an h-set by construction. The chooser acts uniformly over the whole space; the final comparison will read it at the two distinguished classes only.
<!--zh-->
现在用上选择原理，问题只有一个：为 `Glued` 的每个点选出一个布尔代表元。一点处的选取是一个布尔值连同「其类等于该点」的保证。每个点单独地必有一次选取，但只能证明其仅仅存在：商记得自己的点来自代表元，却不记得来自哪一个。把这种逐点的仅仅有元转化为一个处处同时选取的函数的仅仅存在，正是集合层选择所述的内容；它在此适用，因为 `Glued` 按构造是 h-集合。选取函数在整个空间上一致地起作用；最后的比较只在两个特殊类处读取它。
<!--ja-->
いま選択原理を用います。問いはただ一つ、`Glued` の各点にブール値の代表元を一つずつ渡せ、というものです。ある点での選択 (pick) とは、一つのブール値と、その類がその点に等しいという保証の組です。点ごとには必ず選択がありますが、それは単に存在するだけです。商は自分の点が代表元から来たことを覚えていても、どの代表元かは覚えていません。この点ごとの単なる非空性を、あらゆる点で一度に選ぶ一つの関数の単なる存在へ変えるのが、まさに集合レベルの選択の述べるところであり、`Glued` が構成上 h-集合であるためここに適用できます。選択関数は空間全体で一様に働き、最後の比較は二つの注目すべき類でのみ読み取ります。
<!--/-->

<!--en-->
The family to choose from is `Pick x`, a dependent pair: a boolean `b` together with the path witnessing that the class `[ b ]` equals the point `x`. That every point merely has a pick is not an extra assumption but a theorem about quotients: `[]surjective`{.Agda} says each element of a quotient arises, merely, as the class of some representative, and `pickable`{.Agda} is that statement with `x` ranging over `Glued`. Note what the second component is for: it records which representative was chosen, and it is this certificate, not the boolean alone, that lets the argument rebuild paths between classes.
<!--zh-->
被选取的族是 `Pick x`，一个依赖对：布尔值 `b` 连同见证类 `[ b ]` 等于点 `x` 的路径。每个点都仅仅有选取，这不是额外假设而是关于商的定理：`[]surjective`{.Agda} 说商的每个元素都仅仅作为某个代表元的类出现，`pickable`{.Agda} 就是把这句话按 `x` 取遍 `Glued` 读出的形式。注意第二分量的用处：它记录选的是哪个代表元；后面论证要重建类与类之间的路径，靠的正是这份证书，而非单独的布尔值。
<!--ja-->
選択の対象となる族は `Pick x` という依存対です。ブール値 `b` と、類 `[ b ]` が点 `x` に等しいことを見届ける道の組です。各点が単に選択を持つことは追加の仮定ではなく、商についての定理です。`[]surjective`{.Agda} は商の任意の元が、単に、何らかの代表元の類として現れると述べ、`pickable`{.Agda} はそれを `x` が `Glued` を走る形で読んだものです。第二成分の役割に注目してください。これはどの代表元が選ばれたかを記録する証明書であり、後に類と類の間の道を組み立てるのは、ブール値そのものではなくこの証明書です。
<!--/-->

```agda
  Pick : Glued → Type ℓ
  Pick x = Σ[ b ∈ Bool ] ([ b ] ≡ x)

  pickable : (x : Glued) → ∥ Pick x ∥₁
  pickable = []surjective
```

<!--en-->
The question deserves a lemma of its own, so that its type displays what choice delivers: the mere existence of a function picking on the whole of `Glued`. Given `sc : SetChoice ℓ`{.Agda}, the lemma instantiates it with the data assembled so far, the index `Glued`, its h-set proof `squash/`{.Agda}, the family `Pick`, and the pointwise inhabitation `pickable`{.Agda}. The hypothesis `sc` is itself a function; what is truncated is only its output. Choice thus returns no function, only the statement that one exists, and this limit shapes the final step of the theorem.
<!--zh-->
这个问题值得单独立为引理，好让类型原样展示选择所给出之物：在整个 `Glued` 上定义的选取函数的仅仅存在。给定 `sc : SetChoice ℓ`{.Agda}，引理用至今备好的数据例示它：指标 `Glued`、其 h-集合证明 `squash/`{.Agda}、族 `Pick`、逐点的有元性 `pickable`{.Agda}。假设 `sc` 本身是函数；被截断的只是它的输出。于是选择给出的不是函数，只是「有一个」的陈述，这一限制将塑造定理的最后一步。
<!--ja-->
この問いは独立した補題にする価値があります。型そのものが、選択原理が与えるもの、すなわち `Glued` 全体で定義された選択関数の単なる存在を示すからです。`sc : SetChoice ℓ`{.Agda} が与えられると、補題はこれまでに揃えたデータでこれを具体化します。添字 `Glued`、その h-集合の証明 `squash/`{.Agda}、族 `Pick`、点ごとの非空性 `pickable`{.Agda} です。仮定 `sc` はそれ自体が関数であり、切り詰められるのはその出力だけです。したがって選択が与えるのは関数ではなく、それがあるという主張であり、この制限が定理の最終段階の形を決めます。
<!--/-->

```agda
  merePicker : SetChoice ℓ → ∥ ((x : Glued) → Pick x) ∥₁
  merePicker sc = sc Glued squash/ Pick pickable
```

<!--en-->
Suppose, then, that a picking function `g` of type `(x : Glued) → Pick x` is at hand. Evaluating it at the two distinguished points yields two picks, and their first components are the booleans `b₀` and `b₁`, chosen at the class of `true` and at the class of `false`. All further reasoning concerns these two ordinary booleans, which is what makes `P` mechanically decidable. Two lemmas connect the values to `P`, one for each direction: if the representatives agree, their guarantees give a path from the class of `true` to the class of `false`, and effectivity reads it into `P`; if `P` holds, the two distinguished points are equal, and `g` respects the equality, so `b₀` and `b₁` agree.
<!--zh-->
设 picking 函数 `g : (x : Glued) → Pick x` 已经在手。在两个特殊点处求值得到两次选取，其第一分量是布尔值 `b₀` 与 `b₁`，分别在 `true` 的类与 `false` 的类处选出。此后的推理只关乎这两个普通布尔值，正是这一点使 `P` 得以机械判定。两条引理按方向把这两个值与 `P` 相连：若代表元一致，它们的保证给出从 `true` 的类到 `false` 的类的路径，有效性把它读成 `P`；若 `P` 成立，两个特殊点相等，`g` 尊重这条相等，于是 `b₀` 与 `b₁` 一致。
<!--ja-->
いま picking 関数 `g : (x : Glued) → Pick x` が手もとにあるとします。二つの注目点で評価すれば二つの選択が得られ、その第一成分がブール値 `b₀` と `b₁`、`true` の類と `false` の類でそれぞれ選ばれたものです。以降の推論はこの二つの生のブール値だけに関するものであり、`P` が機械的に判定できるのはこのためです。二つの補題が、向きごとに一つずつ、この値を `P` と結びます。代表元が一致すれば、両者の保証が `true` の類から `false` の類への道を与え、有効性がそれを `P` と読みます。`P` が成り立てば二つの注目点は等しく、`g` はその等しさを尊重するので、`b₀` と `b₁` は一致します。
<!--/-->

```agda
  module _ (g : (x : Glued) → Pick x) where

    b₀ : Bool
    b₀ = g [ true ] .fst

    b₁ : Bool
    b₁ = g [ false ] .fst
```

<!--en-->
The first lemma reads an equality `q : b₀ ≡ b₁` backwards into `P`. Three paths compose in `Glued`: from the class of `true` to the class of `b₀` (the guarantee of `g [ true ]`), from there to the class of `b₁` (the equality of classes induced by `q` through `cong [_]`), and from there to the class of `false` (the guarantee of `g [ false ]`). The composite runs from one distinguished class to the other, and `unglue`{.Agda} turns it into a proof of `⟨ P ⟩`. The second lemma goes forward: given a proof `p` of `P`, the path `glue p` identifies the two points, and applying `g` along it gives `b₀ ≡ b₁`; since both endpoints are plain booleans, this is a direct projection of `g`, with no transport of the family.
<!--zh-->
第一条引理把相等 `q : b₀ ≡ b₁` 倒读为 `P`。三条路径在 `Glued` 中复合：从 `true` 的类到 `b₀` 的类 (`g [ true ]` 的保证)，再到 `b₁` 的类 (`q` 经 `cong [_]` 诱导的类相等)，再到 `false` 的类 (`g [ false ]` 的保证)。复合路径从一个特殊类走到另一个，`unglue`{.Agda} 把它变成 `⟨ P ⟩` 的证明。第二条引理正向而行：给定 `P` 的证明 `p`，路径 `glue p` 等同两点，沿它应用 `g` 便得 `b₀ ≡ b₁`；两端都是普通布尔值，所以这只是 `g` 的直接投影，无需对族作任何搬运。
<!--ja-->
最初の補題は、等式 `q : b₀ ≡ b₁` を逆方向に読んで `P` と結びます。三つの道が `Glued` の中で合成されます。`true` の類から `b₀` の類へ (`g [ true ]` の保証)、そこから `b₁` の類へ (`q` が `cong [_]` を通して誘導する類の一致)、さらに `false` の類へ (`g [ false ]` の保証)。合成した道は一つの注目すべき類からもう一つへと走り、`unglue`{.Agda} がそれを `⟨ P ⟩` の証明に変えます。二番目の補題は順方向です。`P` の証明 `p` が与えられれば、道 `glue p` が二点を同一視し、それに沿って `g` を適用すれば `b₀ ≡ b₁` が得られます。両端は生のブール値なので、これは `g` の直接の射影であり、族の輸送は一切要りません。
<!--/-->

```agda

    agree→P : b₀ ≡ b₁ → ⟨ P ⟩
    agree→P q = unglue (sym (g [ true ] .snd) ∙ cong [_] q ∙ g [ false ] .snd)

    P→agree : ⟨ P ⟩ → b₀ ≡ b₁
    P→agree p i = g (glue p i) .fst
```

<!--en-->
Now decide `P` by inspecting the two booleans, which, unlike `P`, can be inspected: two booleans are equal or not, mechanically. If they agree, the first lemma proves `P`. If they differ, `P` must fail, for otherwise the second lemma would force them to agree. Either way `P` is decided, and the case split ran on the two chosen booleans, never on `P` itself.
<!--zh-->
现在改由两个布尔值判定 `P`。与 `P` 不同，它们可以被检视：两个布尔值相等或不相等，机械可判。若二者一致，第一条引理证出 `P`。若二者相异，`P` 必不成立，因为它若成立，第二条引理将迫使二者一致。无论哪边 `P` 都被判定；分情形发生在选出的两个布尔值上，从未触及 `P` 自身。
<!--ja-->
いまや二つのブール値で `P` を判定します。`P` とは違って、ブール値は検査できます。二つのブール値は等しいか等しくないか、機械的に決まります。一致すれば最初の補題が `P` を証明します。異なれば `P` は成り立たないはずです。成り立てば二番目の補題が両者の一致を強めるからです。どちらにしても `P` は判定されます。場合分けは選ばれた二つのブール値の上で行われ、`P` 自身には触れていません。
<!--/-->

<!--en-->
The decidable equality `_≟_` compares `b₀` with `b₁` and returns an element of `Dec (b₀ ≡ b₁)`: either `yes`{.Agda} with the equality proof, or `no`{.Agda} with its refutation. The helper `fromDec` converts each outcome through the dictionary. In the `yes`{.Agda} case the equality `q` feeds `agree→P` and yields the left summand, a proof of `⟨ P ⟩`.
<!--zh-->
可判定相等 `_≟_` 比较 `b₀` 与 `b₁`，返回 `Dec (b₀ ≡ b₁)` 的元素：要么是携带相等证明的 `yes`{.Agda}，要么是携带反驳的 `no`{.Agda}。辅助函数 `fromDec` 经词典转换每种结果。`yes`{.Agda} 情形中，相等 `q` 送入 `agree→P`，产出左侧和项，即 `⟨ P ⟩` 的证明。
<!--ja-->
判定可能な等式 `_≟_` が `b₀` と `b₁` を比較し、`Dec (b₀ ≡ b₁)` の元を返します。等式の証明を伴う `yes`{.Agda} か、反証を伴う `no`{.Agda} かです。補助関数 `fromDec` が辞書を通してそれぞれの結果を変換します。`yes`{.Agda} の場合、等式 `q` が `agree→P` に渡り、左の和成分、すなわち `⟨ P ⟩` の証明が得られます。
<!--/-->

```agda
    decide : ⟨ P ⟩ ⊎ (⟨ P ⟩ → ⊥₀)
    decide = fromDec (b₀ ≟ b₁)
      where
      fromDec : Dec (b₀ ≡ b₁) → ⟨ P ⟩ ⊎ (⟨ P ⟩ → ⊥₀)
      fromDec (yes q) = inl (agree→P q)
```

<!--en-->
In the `no`{.Agda} case, `ne` proves that the two booleans cannot be equal. Were `P` to hold, `P→agree` would exhibit them as equal, against `ne`; the right summand is therefore the function that takes any proof of `⟨ P ⟩`, obtains `b₀ ≡ b₁` by the forward lemma, and hands it to `ne`. Together the two cases decide `P`, with the case split on boolean data alone.
<!--zh-->
`no`{.Agda} 情形中，`ne` 证明两个布尔值不可能相等。若 `P` 成立，`P→agree` 会给出二者相等，与 `ne` 相抵；右侧和项因此是这样的函数：取任一 `⟨ P ⟩` 的证明，经正向引理得到 `b₀ ≡ b₁`，再交给 `ne`。两种情形合起来判定 `P`，分情形只在布尔数据上进行。
<!--ja-->
`no`{.Agda} の場合、`ne` は二つのブール値が等しくありえないことの証明です。`P` が成り立てば `P→agree` が両者の等しさを示し、`ne` と衝突します。そこで右の和成分は、`⟨ P ⟩` の任意の証明を受け取り、順方向の補題で `b₀ ≡ b₁` を得て、それを `ne` に渡す関数です。二つの場合合わせて `P` は判定され、場合分けはブール値のデータの上だけで行われています。
<!--/-->

```agda
      fromDec (no ne) = inr (λ p → ne (P→agree p))
```

<!--en-->
One gap remains before the theorem assembles. Choice delivers no picking function, only its mere existence. But the goal, `P` or not `P`, is itself a proposition: the two sides exclude each other, so between any two decisions there is nothing to distinguish. Into such a goal, mere existence eliminates as if it were actual, and the proof closes.
<!--zh-->
定理组装前还差一步。选择并未交出选取函数，只交出它的仅仅存在。但目标「`P` 或非 `P`」自身是命题：两侧互斥，任何两个判定之间无可区分。对这样的目标，仅仅存在可以当作真实存在来消去，证明就此闭合。
<!--ja-->
定理を組み上げるまでに、まだ一段残っています。選択が渡すのは選択関数ではなく、その単なる存在です。しかし目標「`P` または `P` でない」はそれ自身が命題です。両側は互いに排反し、二つの判定の間に区別できるものが何もないからです。そのような目標への消去では、単なる存在は実際の存在であるかのように扱えて、証明が閉じます。
<!--/-->

<!--en-->
That the goal is a proposition is proved explicitly: `isProp⊎`{.Agda} asks for the propositionhood of each side and for the impossibility of inhabiting both. The first side is `⟨ P ⟩`, propositional by `⟨ P ⟩isProp`. The second is the function type `⟨ P ⟩ → ⊥₀`, whose propositionhood follows pointwise from `isProp⊥` by `isPropΠ`. Finally, `λ p np → np p` proves that the two sides cannot be inhabited at once. The theorem `choice→lem`{.Agda} then has type `SetChoice ℓ → LEM ℓ`. Given `sc` and a proposition `P`, it works inside the Diaconescu module at `P`, obtains the mere picker by `merePicker sc`, and eliminates the truncation with `rec₁`{.Agda} into the now-certified propositional goal, returning `decide`. The order of ideas matters: the case split inside `decide` is genuine data, and the truncation is discharged only because the target cannot distinguish its answers.
<!--zh-->
「目标是命题」这一点被显式证明：`isProp⊎`{.Agda} 要求两侧各自的命题性，以及两侧不能同时有元的证明。第一侧是 `⟨ P ⟩`，由 `⟨ P ⟩isProp` 得其命题性。第二侧是函数类型 `⟨ P ⟩ → ⊥₀`，`isPropΠ` 利用 `isProp⊥` 逐点证明它是命题。最后，`λ p np → np p` 证明两侧不能同时有元。定理 `choice→lem`{.Agda} 的类型随之是 `SetChoice ℓ → LEM ℓ`。给定 `sc` 与命题 `P`，它在 `P` 处进入 Diaconescu 模块，用 `merePicker sc` 得到仅仅的选取函数，再以 `rec₁`{.Agda} 把截断消去到已证为命题的目标中，返回 `decide`。想法的次序重要：`decide` 内部的分情形是真实数据，截断之所以能消去，只因目标无法区分其答案。
<!--ja-->
目標が命題であることは明示的に証明されます。`isProp⊎`{.Agda} は両側それぞれの命題性と、両方の元が同時に存在しないことの証明を要求します。第一側は `⟨ P ⟩` で、`⟨ P ⟩isProp` により命題です。第二側は関数型 `⟨ P ⟩ → ⊥₀` であり、`isPropΠ` が `isProp⊥` を各点で用いて、その命題性を証明します。最後に `λ p np → np p` が、両側に同時に要素が存在しないことを証明します。定理 `choice→lem`{.Agda} の型はしたがって `SetChoice ℓ → LEM ℓ` です。`sc` と命題 `P` が与えられると、`P` について Diaconescu モジュールの中で働き、`merePicker sc` で単なる選択関数の存在を得て、`rec₁`{.Agda} によって証明済みの命題である目標へ切り詰めを消去し、`decide` を返します。考えの順序が重要です。`decide` の中の場合分けは本物のデータであり、切り詰めが消去できるのは、目標がその答えたちを区別できないからです。
<!--/-->

```agda
  decideIsProp : isProp (⟨ P ⟩ ⊎ (⟨ P ⟩ → ⊥₀))
  decideIsProp = isProp⊎ ⟨ P ⟩isProp (isPropΠ (λ _ → isProp⊥)) (λ p np → np p)

choice→lem : ∀ {ℓ} → SetChoice ℓ → LEM ℓ
choice→lem sc P = rec₁ decideIsProp decide (merePicker sc)
  where open Diaconescu P
```

<!--en-->
## Recap

At one fixed level, `SetChoice` says that over an h-set of indices, the mere inhabitation of every fiber yields the mere existence of one function choosing everywhere at once. One higher-level instance therefore covers the level below, and by Diaconescu's theorem it decides every proposition of its level. In the direction this chapter proves, choice is the stronger classical interface: `SetChoice ℓ → LEM ℓ`, and no converse is established here. The model chapter uses one `SetChoice (ℓ-suc ℓ)` instance in two ways: `choice→lem`{.Agda} supplies excluded middle for the ZF axioms, while `lowerSetChoice`{.Agda} supplies the choice-set axiom at the lower level.
<!--zh-->
## 小结

在一个固定的层级上，`SetChoice` 说的是：在 h-集合指标之上，每根纤维的仅仅有元给出一个同时处处选取的函数的仅仅存在。于是高一层的一个实例覆盖其下的层级；而由 Diaconescu 定理，它还能判定其层级的每个命题。在本章所证的方向上，选择是更强的经典接口：`SetChoice ℓ → LEM ℓ`；其逆在此并未建立。模型章以两种方式使用同一个 `SetChoice (ℓ-suc ℓ)` 实例：`choice→lem`{.Agda} 为 ZF 公理给出排中律，`lowerSetChoice`{.Agda} 则在较低层级给出选择集公理。
<!--ja-->
## まとめ

一つの固定したレベルの上で、`SetChoice` が述べるのは次のことです。h-集合の添字の上では、各ファイバーの単なる非空性から、あらゆる点で一度に選ぶ一つの関数の単なる存在が従う。したがって一つ上のレベルの実例がその下のレベルを覆い、ディアコネスクの定理により、そのレベルのすべての命題を判定できます。本章が証明した方向では、選択はより強い古典的インターフェースです。すなわち `SetChoice ℓ → LEM ℓ` であり、逆はここでは確立されません。モデルの章は、一つの `SetChoice (ℓ-suc ℓ)` の実例を二通りに使います。`choice→lem`{.Agda} は ZF の公理に排中律を与え、`lowerSetChoice`{.Agda} は低いレベルで選択集合の公理を与えます。
<!--/-->
