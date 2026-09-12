<!--en-->
# Truth values

To interpret first-order formulas we must first say what a formula evaluates to. In classical textbook semantics the answer is a two-element set of truth values, and connectives are given by truth tables. Here the evaluation target is left open: the semantics of a formula is stated relative to an arbitrary choice of carrier type together with operations for connectives and quantifiers. This chapter records that parametrized data as the record `TruthAlgebra`{.Agda}, and then builds the instance that the rest of the development actually uses.

The chapter therefore makes one conceptual distinction over and over. Specifying operations is not the same as proving laws about them. `TruthAlgebra`{.Agda} is only an operation signature: it fixes a carrier, requires that carrier to be an h-set, and gives fields for conjunction, disjunction, implication, negation, truth, falsity and the two quantifiers. It assumes no associativity, distributivity or Boolean laws, so any theorem proved about an arbitrary `TruthAlgebra`{.Agda} holds even without them.
<!--zh-->
# 真值

要解释一阶公式，首先要回答公式求值得到什么。经典的教科书语义把答案取为二元素的真值集，并用真值表解释联结词。这里不固定求值目标：公式语义相对于任选的载体类型以及解释联结词与量词的运算来陈述。本章把这些参数化数据记录为 record `TruthAlgebra`{.Agda}，然后构造后续发展真正使用的实例。

于是本章反复出现一个概念区分：指定运算与证明运算满足的定律是两回事。`TruthAlgebra`{.Agda} 只是运算签名：它确定载体、要求载体是 h-集合，并给出合取、析取、蕴涵、否定、真、假以及两个量词的字段。它不假设结合律、分配律或布尔律，因此关于任意 `TruthAlgebra`{.Agda} 证明的定理在这些定律缺失时依然成立。
<!--ja-->
# 真理値

一階論理の論理式を解釈するには、まず論理式の評価結果が何であるかを決めなければなりません。古典的な教科書の意味論では、答えは二元の真理値集合であり、結合子は真理値表で与えられます。ここでは評価の対象を固定しません。論理式の意味論は、任意に選んだ台の型と、結合子および量化子を解釈する演算とを相対的に述べます。本章ではこのパラメータ化されたデータをレコード `TruthAlgebra`{.Agda} として記録し、続いてこの後の展開で実際に使う実例を構成します。

そこで本章を通して一つの概念的な区別が繰り返し現れます。演算を指定することと、その演算が満たす法則を証明することは別の作業です。`TruthAlgebra`{.Agda} は演算だけのシグネチャです。台を定め、その台が h-集合であることを要求し、連言・選言・含意・否定・真・偽と二つの量化子のフィールドを与えます。結合律も分配律もブール法則も仮定しないので、任意の `TruthAlgebra`{.Agda} について証明された定理は、それらの法則がなくても成り立ちます。
<!--/-->

<!--en-->
The chapter proceeds in two stages. It first isolates the carrier and operations that a truth-value interpretation supplies. It then specializes this interface to propositions, where the corresponding logical operations give a concrete instance.
<!--zh-->
本章分两步进行。首先抽取真值解释所提供的载体与运算，然后把这一接口具体化为命题，并以相应的逻辑运算给出一个具体实例。
<!--ja-->
この章は二段階で進みます。まず、真理値解釈が与える台と演算を取り出します。次に、このインターフェースを命題に特殊化し、対応する論理演算によって具体的な実例を与えます。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

module Base.Truth where
```

<!--en-->
The abstract interface leaves the operations unspecified. In the proposition-valued instance, conjunction, disjunction, implication, negation, truth, and quantification become the corresponding operations on propositions. Falsity illustrates the change of viewpoint: the host-language empty type `⊥*`{.Agda}, together with its propositionhood proof, forms an element of the truth-value carrier `hProp`{.Agda}.
<!--zh-->
抽象接口不具体指定这些运算。在命题值实例中，合取、析取、蕴涵、否定、真与量化分别取命题上的相应运算。假展示了这里的视角转换：宿主语言的空类型 `⊥*`{.Agda} 连同其命题性证明，组成真值载体 `hProp`{.Agda} 的一个元素。
<!--ja-->
抽象的なインターフェースでは、これらの演算を具体的に定めません。命題値の実例では、連言、選言、含意、否定、真、量化に、命題上の対応する演算を用います。偽はここでの見方の違いを示します。ホスト言語の空型 `⊥*`{.Agda} にその命題性の証明を添えることで、真理値の台 `hProp`{.Agda} の要素になります。
<!--/-->

```agda

open import Base.Prelude
import Cubical.Functions.Logic as Logic
  using ( _⊓_; _⊔_; _⇒_; ¬_; ⊤; ∃[]-syntax; ∀[]-syntax )
```

<!--en-->
## The interface

What data is needed before formulas can be assigned truth values? `TruthAlgebra`{.Agda} answers with a carrier, a proof that it is an h-set, and operations for the connectives and quantifiers. It deliberately includes no associativity, distributivity, lattice, or Boolean laws. Thus the record specifies how expressions may be interpreted without assuming equations among their interpretations.
<!--zh-->
## 接口

要为公式赋予真值，首先需要哪些数据？`TruthAlgebra`{.Agda} 给出的答案是：一个载体、该载体是 h-集合的证明，以及解释联结词与量词的运算。它有意不包含结合律、分配律、格律或布尔律。因此，这个 record 规定表达式可以如何解释，却不预设这些解释之间的等式。
<!--ja-->
## インターフェース

論理式に真理値を与えるには、まずどのようなデータが必要でしょうか。`TruthAlgebra`{.Agda} は、台、それが h-集合であることの証明、そして結合子と量化子を解釈する演算を挙げます。結合律、分配律、束やブール代数の法則は含めません。したがってこのレコードは、式の解釈方法を定めますが、解釈の間の等式までは仮定しません。
<!--/-->

<!--en-->
The record takes two independent universe levels. The carrier `Ω` is a type in `Type ℓ'`{.Agda}, so `ℓ'` measures how large the truth values themselves are. The level `ℓ` is reserved for the index types of the infinitary operations, which appear in the next chunk; nothing forces any size relation between the two. The record type itself lives in `ℓ-suc (ℓ-max ℓ ℓ')`, the level above both. The three fields after the h-set requirement present conjunction, disjunction and implication as plain functions `Ω → Ω → Ω`: each takes two truth values and returns one, with no assumption yet about what the result computes to.
<!--zh-->
record 取两个独立的宇宙层级。载体 `Ω` 是 `Type ℓ'`{.Agda} 中的类型，因此 `ℓ'` 度量真值本身的大小；层级 `ℓ` 留给下一部分出现的无穷运算的索引类型，两者之间没有任何大小关系的约束。record 类型本身落在比两者都高的 `ℓ-suc (ℓ-max ℓ ℓ')`。h-集合性要求之后的三个字段把合取、析取与蕴涵表现为普通的函数 `Ω → Ω → Ω`：各自取两个真值并返回一个，对结果的性质暂无任何假设。
<!--ja-->
レコードは独立な二つの宇宙レベルを取ります。台 `Ω` は `Type ℓ'`{.Agda} の型なので、`ℓ'` は真理値そのものの大きさを測ります。レベル `ℓ` は次の部分に現れる無限演算の添字の型のために確保されており、両者の間に大きさの関係を課すものは何もありません。レコード型自身は、その両方より上の `ℓ-suc (ℓ-max ℓ ℓ')` に属します。h-集合性の要求に続く三つのフィールドは、連言・選言・含意を普通の関数 `Ω → Ω → Ω` として示します。それぞれ二つの真理値を取り一つを返しますが、結果がどのような性質をもつかについてはまだ何も仮定していません。
<!--/-->

```agda
record TruthAlgebra (ℓ ℓ' : Level) : Type (ℓ-suc (ℓ-max ℓ ℓ')) where
  field
    Ω      : Type ℓ'
    isSetΩ : isSet Ω
    _⊓_ _⊔_ _⇒_ : Ω → Ω → Ω
```

<!--en-->
Negation and the constants `⊤` and `⊥` account for the remaining finitary forms. Quantifiers require a different shape: given an index type `A : Type ℓ` and a family `P : A → Ω`, each of `⋀ A P` and `⋁ A P` combines the whole family into one truth value. If `P x` is read as the truth value of a formula with `x` ranging over `A`, these two operations provide the interpretations of universal and existential quantification.
<!--zh-->
否定以及常量 `⊤`、`⊥` 对应其余有限运算。量词需要另一种形状：给定索引类型 `A : Type ℓ` 和族 `P : A → Ω`，`⋀ A P` 与 `⋁ A P` 分别把整个族汇集成一个真值。若把 `P x` 读作变元 `x` 取遍 `A` 时公式的真值，这两个运算便分别提供全称量化与存在量化的解释。
<!--ja-->
否定と定数 `⊤`、`⊥` は、残りの有限演算に対応します。量化子には別の形が必要です。添字の型 `A : Type ℓ` と族 `P : A → Ω` が与えられると、`⋀ A P` と `⋁ A P` はそれぞれ族全体を一つの真理値にまとめます。`P x` を、`x` が `A` を動くときの論理式の真理値と読めば、この二つの演算が全称量化と存在量化の解釈を与えます。
<!--/-->

```agda
    ¬_     : Ω → Ω
    ⊤ ⊥    : Ω
    ⋀ ⋁    : (A : Type ℓ) → (A → Ω) → Ω

  infixr 12 _⊓_ _⊔_
  infixr 10 _⇒_
```

<!--en-->
For reading formulas, negation binds tighter than the binary connectives, so `¬ p ⊓ q` means `(¬ p) ⊓ q`: the negation applies to `p` alone, as usual mathematical convention would suggest.
<!--zh-->
为了阅读公式，否定的结合力强于各二元联结词，因此 `¬ p ⊓ q` 读作 `(¬ p) ⊓ q`：否定只作用于 `p`，与通常的数学约定一致。
<!--ja-->
論理式を読むにあたり、否定は二項結合子より強く結びます。したがって `¬ p ⊓ q` は `(¬ p) ⊓ q` の意味で、否定は `p` だけに働きます。これは通常の数学の流儀に沿ったものです。
<!--/-->

```agda
  infix  13 ¬_
```

<!--en-->
## The canonical instance: hProp

The abstract carrier now becomes `hProp ℓ`{.Agda}. An element of this type packages a type with a proof that the type is a proposition, so a formula is assigned a proposition as its truth value. Satisfaction can then be read proof-theoretically: to establish the formula is to inhabit its assigned proposition. Universal quantification uses dependent functions, whereas existential quantification uses propositionally truncated dependent pairs and therefore records existence without exposing a chosen witness.
<!--zh-->
## 典范实例：hProp

现在把抽象载体具体取为 `hProp ℓ`{.Agda}。这个类型的元素由一个类型及其命题性证明组成，因此公式的真值是一个命题。于是满足关系可以按证明来理解：证明公式成立，就是给出其真值命题的元素。全称量化使用依值函数，存在量化使用命题截断的依值对，因而只记录存在性而不暴露选定的见证。
<!--ja-->
## 正準な実例：hProp

ここで抽象的な台を `hProp ℓ`{.Agda} に具体化します。この型の要素は、型とその命題性の証明を組にしたものなので、論理式には命題が真理値として割り当てられます。充足は証明論的に読むことができ、論理式を示すとは、その真理値である命題の要素を与えることです。全称量化には依存関数を、存在量化には命題的切り詰めを施した依存対を用いるため、後者は特定の証人を公開せずに存在を記録します。
<!--/-->

<!--en-->
At level `ℓ`, propositions whose underlying types lie in `Type ℓ`{.Agda} form the carrier `hProp ℓ`{.Agda}, which itself lies in the successor universe. Hence the instance has type `TruthAlgebra ℓ (ℓ-suc ℓ)`. The lemma `isSetHProp`{.Agda} supplies exactly the h-set proof this carrier requires, and conjunction is interpreted by `Logic._⊓_`{.Agda}.
<!--zh-->
在层级 `ℓ`，底层类型属于 `Type ℓ`{.Agda} 的命题组成载体 `hProp ℓ`{.Agda}，而该载体本身位于后继宇宙。因此实例的类型是 `TruthAlgebra ℓ (ℓ-suc ℓ)`。引理 `isSetHProp`{.Agda} 恰好给出载体所需的 h-集合性，合取则解释为 `Logic._⊓_`{.Agda}。
<!--ja-->
レベル `ℓ` では、基底の型が `Type ℓ`{.Agda} に属する命題が台 `hProp ℓ`{.Agda} をなし、この台自身は後続宇宙に属します。したがって実例の型は `TruthAlgebra ℓ (ℓ-suc ℓ)` です。補題 `isSetHProp`{.Agda} が台に必要な h-集合性を与え、連言は `Logic._⊓_`{.Agda} で解釈されます。
<!--/-->

```agda
hPropAlgebra : ∀ ℓ → TruthAlgebra ℓ (ℓ-suc ℓ)
hPropAlgebra ℓ = record
  { Ω      = hProp ℓ
  ; isSetΩ = isSetHProp
  ; _⊓_    = Logic._⊓_
```

<!--en-->
Disjunction, implication, negation, and truth use the corresponding proposition operations. The disjunction is propositionally truncated: `p ⊔ q` records that one side holds without retaining which side as data. Falsity is written explicitly as `(⊥* , isProp⊥*)`, pairing the host-language empty type with its propositionhood proof. Thus `⊥` is an element of the truth-value carrier, while `⊥*`{.Agda} is the underlying empty type in this instance.
<!--zh-->
析取、蕴涵、否定与真使用命题上的相应运算。析取经过命题截断：`p ⊔ q` 记录某一侧成立，却不把是哪一侧保留为数据。假显式写成 `(⊥* , isProp⊥*)`，即把宿主语言的空类型与其命题性证明配成一对。因此，`⊥` 是真值载体的元素，`⊥*`{.Agda} 则是该实例中底层的空类型。
<!--ja-->
選言、含意、否定、真には、命題上の対応する演算を用います。選言は命題的に切り詰められており、`p ⊔ q` は一方が成り立つことを記録しますが、どちらであるかをデータとして残しません。偽は `(⊥* , isProp⊥*)` と明示され、ホスト言語の空型とその命題性の証明を組にします。したがって `⊥` は真理値の台の要素であり、`⊥*`{.Agda} はこの実例でその基礎となる空型です。
<!--/-->

```agda
  ; _⊔_    = Logic._⊔_
  ; _⇒_    = Logic._⇒_
  ; ¬_     = Logic.¬_
  ; ⊤      = Logic.⊤
  ; ⊥      = ⊥* , isProp⊥*
```

<!--en-->
For a family `P : A → hProp ℓ`, universal quantification is the dependent function type `∀ x → ⟨ P x ⟩`, packaged as a proposition. Its elements give a proof of `P x` for every `x`. Existential quantification is the propositionally truncated dependent pair: it asserts that some `x` satisfies `P` while forgetting the choice of witness. These constructions have exactly the family-indexed types required by `⋀` and `⋁`.
<!--zh-->
对于族 `P : A → hProp ℓ`，全称量化是依值函数类型 `∀ x → ⟨ P x ⟩`，并被打包为命题；它的元素对每个 `x` 都给出 `P x` 的证明。存在量化是命题截断的依值对：它断言某个 `x` 满足 `P`，同时忘去见证的选择。这两个构造恰好具有 `⋀` 与 `⋁` 所要求的族索引类型。
<!--ja-->
族 `P : A → hProp ℓ` に対し、全称量化は依存関数型 `∀ x → ⟨ P x ⟩` を命題としてまとめたものです。その要素は各 `x` に `P x` の証明を与えます。存在量化は命題的切り詰めを施した依存対で、ある `x` が `P` を満たすことを主張しつつ、証人の選択を忘れます。これらの構成は `⋀` と `⋁` が要求する族添字付きの型をちょうど備えています。
<!--/-->

```agda
  ; ⋀      = λ A P → Logic.∀[]-syntax P
  ; ⋁      = λ A P → Logic.∃[]-syntax P }
```

<!--en-->
## Other truth-value instances

The definition of `TruthAlgebra`{.Agda} does not require its carrier to consist of propositions. Any other instance would still have to provide an h-set carrier and every operation in the signature, including the two operations over arbitrary `Type ℓ`{.Agda}-indexed families. This chapter constructs only `hPropAlgebra`{.Agda}.

## Recap

`TruthAlgebra`{.Agda} separates the data for interpreting logical syntax from any laws those operations might satisfy. Its proposition-valued instance packages host-language propositions as truth values: the connectives use proposition operations, falsity packages the empty type, universal quantification is a dependent function type, and existential quantification is a propositionally truncated dependent pair.
<!--zh-->
## 其他真值实例

`TruthAlgebra`{.Agda} 的定义不要求载体由命题组成。任何其他实例仍须给出具有 h-集合性的载体与签名中的全部运算，其中包括对任意 `Type ℓ`{.Agda} 索引族进行操作的两个量词。本章只构造 `hPropAlgebra`{.Agda}。

## 小结

`TruthAlgebra`{.Agda} 把解释逻辑语法所需的数据与这些运算可能满足的定律分开。它的命题值实例把宿主语言命题打包为真值：联结词采用命题运算，假由空类型打包而成，全称量化是依值函数类型，存在量化是命题截断的依值对。
<!--ja-->
## 他の真理値の実例

`TruthAlgebra`{.Agda} の定義は、台が命題からなることを要求しません。別の実例を与える場合にも、h-集合である台とシグネチャの全演算が必要であり、そこには任意の `Type ℓ`{.Agda} 添字付き族に対する二つの量化演算も含まれます。本章で構成するのは `hPropAlgebra`{.Agda} だけです。

## まとめ

`TruthAlgebra`{.Agda} は、論理構文を解釈するためのデータを、それらの演算が満たしうる法則から切り離します。命題値の実例では、ホスト言語の命題を真理値としてまとめ、結合子には命題上の演算を用い、偽は空型から作り、全称量化は依存関数型、存在量化は命題的切り詰めを施した依存対として解釈します。
<!--/-->
