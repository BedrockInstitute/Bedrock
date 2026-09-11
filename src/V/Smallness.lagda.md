<!--en-->
# Small truth values in the cumulative hierarchy

Work over the cumulative hierarchy `V ℓ` produces many statements of the form `x ∈ˢ a` or `a ≈ˢ b`: propositions packaged as elements of `hProp (ℓ-suc ℓ)`, one universe above the level `ℓ` at which the sets themselves are indexed. Such upper-universe propositions are inconvenient: constructions that expect data at level `ℓ`, among them the library's separation set, cannot accept them. A proposition `P : hProp (ℓ-suc ℓ)` is therefore called **small** when it is equivalent, as a type of proofs, to some proposition `Q : hProp ℓ` in the lower universe. Smallness is not a reduction of `P` itself; it is a certificate that another, lower proposition says exactly the same thing.

This chapter lowers large truth values to small ones in stages. The atomic membership and equality relations of `V`{.Agda} are small outright, because each set comes with a small index type presenting its members. Smallness then propagates through every connective and through bounded quantifiers, whose range is exactly such an index type. For unbounded quantifiers, this chapter proves preservation when the range itself is essentially small, that is, equivalent to a type at level `ℓ`. The two payoffs are separation for Δ₀ formulas with no propositional resizing, and smallness of every formula's truth value inside a restricted structure whose carrier is essentially small.
<!--zh-->
# 累积层级中的小真值

在累积层级 `V ℓ` 上工作会不断产生形如 `x ∈ˢ a` 或 `a ≈ˢ b` 的陈述：它们是打包成 `hProp (ℓ-suc ℓ)` 元素的命题，比集合自身所在的层级 `ℓ` 高一个宇宙。这样的上宇宙命题不便使用：期望 `ℓ` 层数据的构造，例如库中的分离集合，无法接受它们。于是，若命题 `P : hProp (ℓ-suc ℓ)` 作为证明的类型等价于某个低宇宙命题 `Q : hProp ℓ`，就称它是**小的**。小性不是把 `P` 本身化简，而是一份证书：另一个更低的命题说的恰是同一件事。

本章分阶段把大真值降到小真值。`V`{.Agda} 的原子隶属关系与相等关系直接是小，因为每个集合都配有呈现其成员的小索引类型。小性随后经一切联结词传播，也经有界量词传播，因为后者的量化范围恰是这种索引类型。对无界量词，本章证明了量化范围本身本质小，即等价于层级 `ℓ` 的某个类型时，小性仍然保持。两项成果是：无需命题降层的 Δ₀ 分离，以及载体本质小的限制结构上全体公式真值的小性。
<!--ja-->
# 累積階層における小さな真理値

累積階層 `V ℓ` の上で作業をすると、`x ∈ˢ a` や `a ≈ˢ b` のような主張が次々に現れます。これらは `hProp (ℓ-suc ℓ)` の要素としてまとめられた命題であり、集合そのものの添字レベル `ℓ` より一つ上の宇宙に住みます。上の宇宙の命題はそのままでは不便です。レベル `ℓ` のデータを要求する構成、たとえばライブラリの分出集合は、それを受け付けられません。そこで、命題 `P : hProp (ℓ-suc ℓ)` の証明の型がある低い宇宙の命題 `Q : hProp ℓ` と同値であるとき、`P` は**小さい**と呼びます。小ささは `P` を単純化するのではなく、別の低い命題がまったく同じことを述べているという証明書です。

本章は、大きな真理値を段階的に小さな真理値へ下げます。`V`{.Agda} の原子的な所属と等号はそのまま小さく、これは各集合が要素を提示する小さな添字の型をもつからです。小ささはすべての結合子を通して保存され、有界量化子も同様です。その量化の範囲はまさにその添字の型だからです。非有界量化子については、範囲そのものが本質的に小さい、つまりレベル `ℓ` の型と同値である場合に小ささが保たれることを本章で示します。成果は二つあります。命題リサイズなしの Δ₀ 分出と、台が本質的に小さい制限構造の上でのすべての論理式の評価の小ささです。
<!--/-->

<!--en-->
Everything in this chapter takes place at one fixed universe level `ℓ`, fixed once and for all by the module parameter. The ambient object is the cumulative hierarchy `V ℓ` from the chapter V.Hierarchy, whose sets are images of `Type ℓ`-indexed families. The one definition that organizes everything is `isSmall`{.Agda}: for `P : hProp (ℓ-suc ℓ)`, an inhabitant of `isSmall P` is a pair consisting of a lower-universe proposition `Q : hProp ℓ` and an equivalence of underlying types `⟨ P ⟩ ≃ ⟨ Q ⟩`. The chapter's task is to manufacture such pairs. Its setting is the `ZFStructure`{.Agda} record, which packages a carrier with truth-valued equality and membership relations; the restriction `_↾_`{.Agda} of such a record to a class is used in the final section.
<!--zh-->
本章的一切都在一个固定的宇宙层级 `ℓ` 上进行，它由模块参数一次性确定。环境对象是 V.Hierarchy 章引入的累积层级 `V ℓ`，其集合是 `Type ℓ` 索引族的像。统摄全章的定义是 `isSmall`{.Agda}：对 `P : hProp (ℓ-suc ℓ)`，`isSmall P` 的元素是一个对子，第一分量是低宇宙命题 `Q : hProp ℓ`，第二分量是底层类型间的等价 `⟨ P ⟩ ≃ ⟨ Q ⟩`。本章的任务就是制造这样的对子。工作环境是 `ZFStructure`{.Agda} record，它把载体与取真值的等词、隶属关系打包在一起；把这样的 record 限制到一个类上的运算 `_↾_`{.Agda} 将在最后一节用到。
<!--ja-->
本章のすべては、モジュール引数によって一度だけ固定される宇宙レベル `ℓ` のもとで行われます。対象となるのは V.Hierarchy 章の累積階層 `V ℓ` で、その集合は `Type ℓ` で添字付けられた族の像です。全体を貫く定義は `isSmall`{.Agda} です。`P : hProp (ℓ-suc ℓ)` に対し、`isSmall P` の要素は、低い宇宙の命題 `Q : hProp ℓ` と基礎型の間の同値 `⟨ P ⟩ ≃ ⟨ Q ⟩` からなる対です。本章の課題はこのような対を作ることです。舞台となるのは `ZFStructure`{.Agda} レコード、すなわち台と、真理値を返す等号と所属の関係をひとまとめにしたものです。このレコードをクラスに制限する演算 `_↾_`{.Agda} は最終節で使います。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth

module V.Smallness {ℓ : Level} where

open import Base.Impredicativity using ( isSmall )
```

<!--en-->
The statements to be lowered live in a formal first-order language. Its relation symbols are `_∈̇_` and `_≐_` for membership and equality; its connectives combine formulas; and it has both bounded quantifiers `∀̇∈` and `∃̇∈` and unbounded quantifiers `∀̇` and `∃̇_`. The `Δ₀`{.Agda} fragment classifies formulas within the Lévy hierarchy. `Δ₀` is not a predicate on formulas but an inductive witness that a formula is built from atoms using connectives and bounded quantifiers only. Crucially there is no constructor for unbounded quantification: a formula containing `∀̇` or `∃̇_` simply cannot carry a Δ₀ witness, and the Δ₀ theorem of this chapter relies on exactly that absence.
<!--zh-->
待压低的陈述生活在一阶形式语言中。其关系符号是表示隶属与相等的 `_∈̇_` 与 `_≐_`；联结词组合公式；语言同时具有有界量词 `∀̇∈`、`∃̇∈` 与无界量词 `∀̇`、`∃̇_`。`Δ₀`{.Agda} 片段在 Lévy 层级中给公式分类。`Δ₀` 不是公式上的谓词，而是一个归纳见证，证明该公式仅由原子经联结词与有界量词构成。关键在于，无界量化没有对应构造子：含有 `∀̇` 或 `∃̇_` 的公式根本无法携带 Δ₀ 见证，本章的 Δ₀ 定理正是依赖这一缺席。
<!--ja-->
下げるべき主張は、一階の形式言語の中にあります。関係記号は所属と等号の `_∈̇_` と `_≐_`、結合子は論理式を組み合わせ、さらに有界量化子 `∀̇∈` と `∃̇∈`、非有界量化子 `∀̇` と `∃̇_` があります。`Δ₀`{.Agda} のフラグメントは Lévy 階層による論理式の分類です。`Δ₀` は論理式上の述語ではなく、その論理式が原子から結合子と有界量化子だけで作られていることの帰納的な証人です。決定的なのは、非有界量化に対応する構成子が存在しないことです。`∀̇` や `∃̇_` を含む論理式はそもそも Δ₀ の証人をもてず、本章の Δ₀ 定理はまさにこの不在に依拠します。
<!--/-->

```agda
open import FOL.ZFStructure using ( ZFStructure; _↾_ )
open import FOL.Syntax
  using ( Formula; _∈̇_; _≐_; _∧̇_; _∨̇_; _⇒̇_; ⊥̇; ∃̇_; ∀̇_; ∀̇∈; ∃̇∈ )
open import FOL.LevyHierarchy
  using ( Δ₀; δ-∈; δ-≐; δ-∧; δ-∨; δ-⇒; δ-⊥; δ-∀∈; δ-∃∈ )
```

<!--en-->
A formula's meaning is given by the semantics module, instantiated here at the structure `𝒮ᵥ`{.Agda} from V.Hierarchy: the cumulative hierarchy equipped as a structure whose relations take values in `hProp (ℓ-suc ℓ)`. So the truth values this chapter studies are exactly propositions one universe up, the kind `isSmall` speaks about. The proofs all rest on a small toolkit for equivalences: the type `_≃_` with its evaluation `equivFun` and preimages `invEq`, `equivΠ` for lifting equivalences through function types, and `propBiimpl→Equiv`, which turns two proofs of propositionhood and a bi-implication into an equivalence. Since both sides of the equivalences below are propositions, this last constructor carries most of the weight.
<!--zh-->
公式的意义由语义模块给出，这里在 V.Hierarchy 的结构 `𝒮ᵥ`{.Agda} 上实例化：即装备成结构的累积层级，其关系取值于 `hProp (ℓ-suc ℓ)`。因此本章研究的真值恰是高一层的命题，正是 `isSmall` 所谈的那类。所有证明都建立在一套等价工具之上：等价类型 `_≃_` 及其求值 `equivFun` 与原像 `invEq`，穿越函数类型的 `equivΠ`，以及 `propBiimpl→Equiv`，它把两个命题性证明加一条双向蕴含变成等价。由于下面各等价的两端都是命题，最后这个构造子承担了大部分工作。
<!--ja-->
論理式の意味は意味論のモジュールが与え、ここでは V.Hierarchy の構造 `𝒮ᵥ`{.Agda} で具体化します。つまり、構造としての装備を施した累積階層で、その関係は `hProp (ℓ-suc ℓ)` に値をとります。したがって本章が扱う真理値は一段上の宇宙の命題であり、まさに `isSmall` が語る種類のものです。証明はすべて同値の小さな道具立てに依拠します。同値の型 `_≃_` とその適用 `equivFun`、原像 `invEq`、関数型を通して同値を運ぶ `equivΠ`、そして二つの命題性の証明と双条件から同値を作る `propBiimpl→Equiv`。以下の同値はどちらの側も命題なので、この構成子がほとんどの仕事を担います。
<!--/-->

```agda
import FOL.Semantics
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )

open import Cubical.Foundations.Equiv
  using ( _≃_; equivFun; invEq; invEquiv; equivΠ; propBiimpl→Equiv )
import Cubical.Functions.Logic as Logic
```

<!--en-->
Closing smallness under the connectives needs the library's proposition operations at the lower level `ℓ`, which is the target universe of every compression. These are kept under the qualified name `Logic`{.Agda}, so `Logic.⊓`{.Agda} and its siblings always denote operations on `hProp ℓ` and never collide with the truth-algebra operations on `hProp (ℓ-suc ℓ)` opened later. The remaining pieces support specific equivalence constructions: `Σ-cong-equiv` builds an equivalence of pair types from componentwise equivalences, `Sum.⊎-equiv` handles coproducts, `tt*` is the unit element, and the propositional truncation module `PT`{.Agda} provides a map operation that transports merely-exists statements along a function without ever choosing a witness.
<!--zh-->
要证联结词保小，需要库在低层 `ℓ`，即每次化归的目标宇宙，上的命题运算。它们以限定名 `Logic`{.Agda} 保存，因此 `Logic.⊓`{.Agda} 等名字总是 `hProp ℓ` 上的运算，不会与稍后打开的 `hProp (ℓ-suc ℓ)` 上的真值代数运算冲突。其余部分服务于具体的等价构造：`Σ-cong-equiv` 由逐分量的等价构造对子类型间的等价；`Sum.⊎-equiv` 处理余积；`tt*` 是单元元素；命题截断模块 `PT`{.Agda} 的 map 运算沿函数搬运「仅仅存在」式陈述，而不选取任何见证。
<!--ja-->
結合子による保存を示すには、低いレベル `ℓ`、すなわち圧縮の到達点となる宇宙における、ライブラリの命題演算が必要です。これらは限定名 `Logic`{.Agda} のもとに置かれ、`Logic.⊓`{.Agda} などの名前はつねに `hProp ℓ` 上の演算を指し、後で開く `hProp (ℓ-suc ℓ)` 上の真理値代数の演算と衝突しません。残りの部品は個々の同値の構成に役立ちます。`Σ-cong-equiv` は成分ごとの同値から対の型の間の同値を作り、`Sum.⊎-equiv` は直和を扱い、`tt*` は単一元であり、命題的切り詰めのモジュール `PT`{.Agda} は、証人を選ばずに関数に沿って「存在するだけ」の主張を運ぶ map を与えます。
<!--/-->

```agda
open import Cubical.Functions.Logic using ( ⇔toPath )
open import Cubical.Data.Sigma using ( Σ-cong-equiv )
import Cubical.Data.Sum as Sum
open import Cubical.Data.Unit using ( tt* )
import Cubical.HITs.PropositionalTruncation as PT
```

<!--en-->
The hierarchy itself supplies the atomic data. Each set `a` comes with a monic presentation: a small index type `⟪ a ⟫` with an embedding `⟪ a ⟫↪` into `V ℓ`. Membership in a set therefore has a small twin `_∈ₛ_`, defined as the type of pairs `(m : ⟪ b ⟫, ⟪ b ⟫↪ m ∼ a)`, which lives in `hProp ℓ`; the conversion `∈∈ₛ` links the two memberships in both directions, and `identityPrinciple`{.Agda} identifies bisimilarity `∼` with actual paths. The operation `∈-asFiber` turns an (untruncated) membership into an actual fiber of the embedding. `SeparationSet`{.Agda} is the library's separation construction, which only accepts predicates already valued in the lower universe. Finally the truth algebra `hPropAlgebra (ℓ-suc ℓ)` is opened, bringing the connectives `⊓ ⊔ ⇒ ¬ ⊤ ⊥` and the quantifiers `⋀ ⋁` on `hProp (ℓ-suc ℓ)` into scope.
<!--zh-->
层级本身提供原子数据。每个集合 `a` 都有一个单射呈现：小索引类型 `⟪ a ⟫` 与到 `V ℓ` 的嵌入 `⟪ a ⟫↪`。于是隶属有一个小的孪生 `_∈ₛ_`，定义为所有对 `(m : ⟪ b ⟫, ⟪ b ⟫↪ m ∼ a)` 的类型，落在 `hProp ℓ` 中；转换 `∈∈ₛ` 双向联结两种隶属，`identityPrinciple`{.Agda} 把双相似 `∼` 与真正的路径等同。运算 `∈-asFiber` 把 (不加截断的) 隶属变成嵌入的一个真正的纤维。`SeparationSet`{.Agda} 是库的分离构造，只接受已经在低宇宙取值的谓词。最后打开真值代数 `hPropAlgebra (ℓ-suc ℓ)`，把 `hProp (ℓ-suc ℓ)` 上的联结词 `⊓ ⊔ ⇒ ¬ ⊤ ⊥` 与量词 `⋀ ⋁` 带入作用域。
<!--ja-->
階層そのものが原子的なデータを供給します。各集合 `a` は単射表示をもち、小さな添字の型 `⟪ a ⟫` と `V ℓ` への埋め込み `⟪ a ⟫↪` です。すると所属には小さい双子 `_∈ₛ_` が伴います。これは対 `(m : ⟪ b ⟫, ⟪ b ⟫↪ m ∼ a)` 全体の型として定義され、`hProp ℓ` に住みます。変換 `∈∈ₛ` が二つの所属を双方向に結び、`identityPrinciple`{.Agda} は双相似 `∼` を実際のパスと同一視します。演算 `∈-asFiber` は (切り詰められていない) 所属を埋め込みの実際のファイバーに変えます。`SeparationSet`{.Agda} はライブラリの分出構成であり、すでに低い宇宙に値をもつ述語だけを受け付けます。最後に真理値代数 `hPropAlgebra (ℓ-suc ℓ)` を開き、`hProp (ℓ-suc ℓ)` 上の結合子 `⊓ ⊔ ⇒ ¬ ⊤ ⊥` と量化子 `⋀ ⋁` をスコープに入れます。
<!--/-->

```agda
open import Cubical.HITs.CumulativeHierarchy.Properties
  using ( _∼_; identityPrinciple; _∈ₛ_; ∈∈ₛ; ⟪_⟫; ⟪_⟫↪; ∈ₛ⟪_⟫↪_; ∈-asFiber )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module SeparationSet )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
```

<!--en-->
The structure record is instantiated at `𝒮ᵥ`{.Agda}, and from this point the names `S`, `_≈ˢ_` and `_∈ˢ_` refer to its carrier and relations. Concretely `S` is `V ℓ`. A statement about members of the structure is thus a proposition one universe up, which is precisely the kind of statement this chapter spends its effort on proving small.
<!--zh-->
结构 record 在 `𝒮ᵥ`{.Agda} 处实例化，此后名字 `S`、`_≈ˢ_` 与 `_∈ˢ_` 就指它的载体与关系。具体地，`S` 是 `V ℓ`。关于结构成员的陈述因此是高一层的命题，而这类陈述能否小，正是本章要用力的地方。
<!--ja-->
構造レコードは `𝒮ᵥ`{.Agda} で具体化され、以後 `S`、`_≈ˢ_`、`_∈ˢ_` という名前はその台と関係を指します。具体的には `S` は `V ℓ` です。したがって構造の要素についての主張は一段上の宇宙の命題であり、それが小さいと言えるかどうかこそ、本章が力を注ぐ点なのです。
<!--/-->

```agda
open ZFStructure 𝒮ᵥ
```

<!--en-->
## Being small

A proposition `P : hProp (ℓ-suc ℓ)` is small, written `isSmall P`, when it comes with a lower-universe proposition `Q : hProp ℓ` and an equivalence `⟨ P ⟩ ≃ ⟨ Q ⟩`. The definition was introduced in `Base.Impredicativity`, where the resizing interface asserts smallness of every proposition at once. This chapter assumes no such interface. It earns smallness for individual propositions, beginning with the two atomic relations of the structure, and the rest of the chapter passes these witnesses through connectives and quantifiers.

Why should the atoms be small at all? Because of how a set in `V ℓ` is built: as the image of a family indexed by some `⟪ a ⟫ : Type ℓ`. To say `x` is a member of `a` is to say some index presents a member equal to `x`, and that statement quantifies over a small type. Membership therefore has a small twin `a ∈ₛ b`, and `∈∈ₛ` converts between the two relations in both directions. Equality likewise compresses to bisimilarity `a ∼ b` via the identity principle.
<!--zh-->
## 何谓小

命题 `P : hProp (ℓ-suc ℓ)` 是小的 (记作 `isSmall P`)，指它配有低宇宙命题 `Q : hProp ℓ` 以及等价 `⟨ P ⟩ ≃ ⟨ Q ⟩`。该定义来自 `Base.Impredicativity`，那里的降层接口对每个命题一次性断言小性。本章不作这种假设，而是对个别的命题挣得小性，从结构的两个原子关系开始，再把这些见证经联结词与量词传递下去。

原子为何会是小的？因为 `V ℓ` 中集合的构造方式：它是某个 `⟪ a ⟫ : Type ℓ` 索引的族的像。「`x` 是 `a` 的成员」即是说某个索引呈现的成员等于 `x`，而这个陈述在小类型上量化。隶属因此有小孪生 `a ∈ₛ b`，`∈∈ₛ` 在两个方向上转换这两种关系。相等同样经恒等原理压缩为双相似 `a ∼ b`。
<!--ja-->
## 小さい命題

命題 `P : hProp (ℓ-suc ℓ)` が小さい、つまり `isSmall P` が成り立つとは、低い宇宙の命題 `Q : hProp ℓ` と同値 `⟨ P ⟩ ≃ ⟨ Q ⟩` を備えることです。この定義は `Base.Impredicativity` で導入され、そこではリサイズのインターフェースがすべての命題について小ささを一括して断言します。本章はそのような仮定を置きません。個々の命題について小ささを獲得し、まず構造の二つの原子関係から始めて、その証人を結合子と量化子を通して運んでいきます。

原子がなぜ小さいのでしょうか。`V ℓ` の集合は、ある `⟪ a ⟫ : Type ℓ` で添字付けられた族の像として作られているからです。「`x` は `a` の要素である」とは、ある添字が提示する要素が `x` と等しいことであり、その主張は小さな型の上で量化します。したがって所属には小さな双子 `a ∈ₛ b` が伴い、`∈∈ₛ` が双方向に変換します。等号も同様に、同一性原理を経て双相似 `a ∼ b` へ圧縮されます。
<!--/-->

<!--en-->
The first lemma packages the small membership relation as a smallness witness. To show `isSmall (a ∈ˢ b)` we must exhibit a lower-universe proposition with an equivalence to `⟨ a ∈ˢ b ⟩`; the witness is `a ∈ₛ b`, and since both underlying types are propositions, `propBiimpl→Equiv` builds the equivalence from the two directions of `∈∈ₛ` alone. No content about `a` or `b` is used: whatever the sets are, membership between them is small. Note what the lemma does not say: it does not identify the two relations by a path, and it does not make `∈ˢ` itself land in the lower universe; it supplies a compressed equivalent.
<!--zh-->
第一条引理把小的隶属关系打包成小性见证。要证 `isSmall (a ∈ˢ b)`，须给出一个低宇宙命题以及它与 `⟨ a ∈ˢ b ⟩` 的等价；见证取 `a ∈ₛ b`。由于两个底层类型都是命题，`propBiimpl→Equiv` 仅凭 `∈∈ₛ` 的两个方向即可造出等价。这里没有用到关于 `a`、`b` 的任何内容：无论这两个集合是什么，它们之间的隶属都是小的。注意引理没有说的内容：它不以路径等同两个关系，也不让 `∈ˢ` 本身落在低宇宙；它提供的是一个被压缩的等价物。
<!--ja-->
最初の補題は、小さな所属関係を小ささの証人としてまとめます。`isSmall (a ∈ˢ b)` を示すには、低い宇宙の命題と `⟨ a ∈ˢ b ⟩` との同値を示す必要があります。証人としては `a ∈ₛ b` をとります。両方の基礎型が命題なので、`propBiimpl→Equiv` によって `∈∈ₛ` の二つの方向だけで同値が得られます。`a` や `b` についての情報は一切使っていません。集合が何であれ、それらの間の所属は小さいのです。この補題が主張しないことも重要です。二つの関係をパスで同一視するのでも、`∈ˢ` 自身を低い宇宙に落とすのでもなく、圧縮された同値物を供給するだけです。
<!--/-->

```agda
small-∈ : (a b : S) → isSmall (a ∈ˢ b)
small-∈ a b = (a ∈ₛ b) ,
  propBiimpl→Equiv (snd (a ∈ˢ b)) (snd (a ∈ₛ b))
    (∈∈ₛ {a = a} {b = b} .fst) (∈∈ₛ {a = a} {b = b} .snd)

small-≡ : (a b : S) → isSmall (a ≈ˢ b)
```

<!--en-->
The equality atom follows the same pattern with a different small twin. The structure's equality `a ≈ˢ b` is compressed to bisimilarity `a ∼ b`, the statement that the two sets have the same members; the library's identity principle is an equivalence between `⟨ a ∼ b ⟩` and the path type `a ≡ b`, and `invEquiv` orients it in the direction required by `isSmall`, from the large equality type `⟨ a ≈ˢ b ⟩` to the lower-universe bisimilarity proposition. Together with `small-∈` this exhausts the atomic cases of the language.
<!--zh-->
相等原子遵循同一模式，但用不同的小孪生。结构的相等 `a ≈ˢ b` 压缩为双相似 `a ∼ b`，即两集合有相同成员的陈述；库的恒等原理是 `⟨ a ∼ b ⟩` 与路径类型 `a ≡ b` 之间的等价，`invEquiv` 把它转向 `isSmall` 所需的方向，即从大宇宙的相等类型 `⟨ a ≈ˢ b ⟩` 到低宇宙的双相似命题。与 `small-∈` 合起来，语言的原子情形就此穷尽。
<!--ja-->
等号の原子は同じ形をしつつ、別の小さな双子を用います。構造の等号 `a ≈ˢ b` は双相似 `a ∼ b`、すなわち二つの集合が同じ要素をもつという主張へ圧縮されます。ライブラリの同一性原理は `⟨ a ∼ b ⟩` とパスの型 `a ≡ b` との間の同値であり、`invEquiv` がそれを `isSmall` に必要な方向、すなわち大きな宇宙の等号型 `⟨ a ≈ˢ b ⟩` から低い宇宙の双相似の命題へ向け直します。`small-∈` と合わせて、言語の原子の場合はこれで尽くされます。
<!--/-->

```agda
small-≡ a b = (a ∼ b) , invEquiv identityPrinciple
```

<!--en-->
## The connectives preserve smallness

With the atoms in hand, the next question is whether smallness survives logical combination. It does: each of the four connectives and the two constants passes smallness witnesses through, and once this section is done, any truth value built from small atoms by connectives is small again. This is what later lets an induction over Δ₀ witnesses close off all the connective cases at once.

Each proof takes two smallness witnesses `(P' , eP)` and `(Q' , eQ)`, where `eP : ⟨ P ⟩ ≃ ⟨ P' ⟩` and `eQ : ⟨ Q ⟩ ≃ ⟨ Q' ⟩`, and returns a smallness witness for the compound. The lower-universe component is built from `P'` and `Q'` by the corresponding `Logic`{.Agda} operation at level `ℓ`, and the equivalence component transports proofs of the compound along `eP` and `eQ`.
<!--zh-->
## 联结词保小

有了原子之后，下一个问题是小性能否在逻辑组合下存活。答案是肯定的：四个联结词与两个常量逐一传递小性见证；本节完成后，凡由小原子经联结词构成的真值都是小的。这也为日后对 Δ₀ 见证的归纳一次性封闭所有联结词情形铺平了道路。

每个证明取两个小性见证 `(P' , eP)` 与 `(Q' , eQ)`，其中 `eP : ⟨ P ⟩ ≃ ⟨ P' ⟩`、`eQ : ⟨ Q ⟩ ≃ ⟨ Q' ⟩`，再返回复合命题的小性见证。低宇宙分量由 `P'`、`Q'` 经层级 `ℓ` 上对应的 `Logic`{.Agda} 运算构成；等价分量则沿 `eP`、`eQ` 传输复合命题的证明。
<!--ja-->
## 結合子による保存

原子が揃ったところで、次の問いは、小ささが論理的な組み合わせの下で保たれるかどうかです。答えは肯定です。四つの結合子と二つの定数のそれぞれが小ささの証人を通し、この節が終わった時点で、小さな原子から結合子で作られる真理値はすべて再び小さくなります。これが後で、Δ₀ の証人に関する帰納法が結合子の場合を一括して片付ける理由です。

各証明は二つの小ささの証人 `(P' , eP)` と `(Q' , eQ)`、ここでは `eP : ⟨ P ⟩ ≃ ⟨ P' ⟩`、`eQ : ⟨ Q ⟩ ≃ ⟨ Q' ⟩`、を受け取り、合成された命題に対する小ささの証人を返します。低い宇宙側の成分は `P'` と `Q'` をレベル `ℓ` の対応する `Logic`{.Agda} の演算で組み上げ、同値の成分は `eP` と `eQ` に沿って合成の証明を輸送します。
<!--/-->

<!--en-->
Conjunction is the simplest case because the underlying type of `P ⊓ Q` is a pair `⟨ P ⟩ × ⟨ Q ⟩`. Pairing the two compressed propositions with `Logic.⊓`, whose underlying type is likewise a product, the equivalence is obtained by `Σ-cong-equiv` applied to `eP` and `eQ`: map a pair of proofs to the pair of its compressions. Nothing about propositions is needed beyond that each factor compresses.
<!--zh-->
合取最简单，因为 `P ⊓ Q` 的底层类型是对子 `⟨ P ⟩ × ⟨ Q ⟩`。用 `Logic.⊓` 组合两个压缩命题，其底层类型同样是乘积；等价由 `Σ-cong-equiv` 作用于 `eP`、`eQ` 得到：把一对证明映到其压缩后的一对。除了每个因子可压缩之外，不需要任何关于命题的其他内容。
<!--ja-->
連言が最も単純です。`P ⊓ Q` の基礎の型は対 `⟨ P ⟩ × ⟨ Q ⟩` だからです。二つの圧縮された命題を、基礎の型がやはり積である `Logic.⊓` で組み合わせれば、同値は `eP` と `eQ` に `Σ-cong-equiv` を適用して得られます。証明の対を、圧縮された証明の対へ写すだけです。各因子が圧縮できること以外に、命題についての情報は要りません。
<!--/-->

```agda
small⊓ : {P Q : hProp (ℓ-suc ℓ)} → isSmall P → isSmall Q → isSmall (P ⊓ Q)
small⊓ {P} {Q} (P' , eP) (Q' , eQ) =
  (P' Logic.⊓ Q') , Σ-cong-equiv eP (λ _ → eQ)

small⊔ : {P Q : hProp (ℓ-suc ℓ)} → isSmall P → isSmall Q → isSmall (P ⊔ Q)
small⊔ {P} {Q} (P' , eP) (Q' , eQ) =
```

<!--en-->
Disjunction and implication need one idea each. For disjunction, `⟨ P ⊔ Q ⟩` is the propositional truncation of the coproduct, so the compressed proposition `P' Logic.⊔ Q'` is again a truncation, and `PT.propTrunc≃` lifts the coproduct equivalence `Sum.⊎-equiv eP eQ` to the truncations. This is where truncation discipline shows: the map merely relabels which side holds, never inspects which side was chosen, because truncation provides no chosen side. For implication, `⟨ P ⇒ Q ⟩` is the function type `⟨ P ⟩ → ⟨ Q ⟩`; the compressed proposition `P' Logic.⇒ Q'` has the same shape at level `ℓ`, and `equivΠ` transports the equivalence through the function space pointwise.
<!--zh-->
析取与蕴涵各需一个想法。对析取，`⟨ P ⊔ Q ⟩` 是余积的命题截断，因此压缩命题 `P' Logic.⊔ Q'` 也是截断，`PT.propTrunc≃` 把余积等价 `Sum.⊎-equiv eP eQ` 提升到截断上。截断纪律在此显现：该映射只是改记哪一侧成立，从不检视选定了哪一侧，因为截断根本不提供选定的侧。对蕴涵，`⟨ P ⇒ Q ⟩` 是函数类型 `⟨ P ⟩ → ⟨ Q ⟩`；压缩命题 `P' Logic.⇒ Q'` 在层级 `ℓ` 上形状相同，`equivΠ` 逐点地把等价穿过函数空间。
<!--ja-->
選言と含意には、それぞれ一つの考え方が要ります。選言では `⟨ P ⊔ Q ⟩` は直和の命題的切り詰めなので、圧縮された命題 `P' Logic.⊔ Q'` も切り詰めであり、`PT.propTrunc≃` が直和の同値 `Sum.⊎-equiv eP eQ` を切り詰めへ引き上げます。ここで切り詰めの規律が現れます。この写像はどちら側が成り立つかのラベルを付け替えるだけで、選ばれた側を検査しません。切り詰めは選ばれた側をそもそも提供しないからです。含意では `⟨ P ⇒ Q ⟩` は関数型 `⟨ P ⟩ → ⟨ Q ⟩` であり、圧縮された命題 `P' Logic.⇒ Q'` はレベル `ℓ` で同じ形をもち、`equivΠ` が関数空間を通して同値を各点で運びます。
<!--/-->

```agda
  (P' Logic.⊔ Q') , PT.propTrunc≃ (Sum.⊎-equiv eP eQ)

small⇒ : {P Q : hProp (ℓ-suc ℓ)} → isSmall P → isSmall Q → isSmall (P ⇒ Q)
small⇒ {P} {Q} (P' , eP) (Q' , eQ) =
  (P' Logic.⇒ Q') , equivΠ eP (λ _ → eQ)

small¬ : {P : hProp (ℓ-suc ℓ)} → isSmall P → isSmall (¬ P)
```

<!--en-->
Negation is the one case where the compressed proposition alone does not determine the equivalence, because negation is contravariant: a proof of `¬ P` consumes a proof of `P`. The compressed proposition is `Logic.¬ P'`, whose underlying type sends `⟨ P' ⟩` to the empty type. Both sides are propositions, so `propBiimpl→Equiv` applies, and the two directions use `eP` in opposite orientations: to contradict `np : ¬ P` from a compressed refutation `p'`, apply `np` to the preimage `invEq eP p'`; conversely, feed the image `equivFun eP p` of `p : ⟨ P ⟩` to `np'`. The evaluation and inverse of the equivalence appear with opposite variance exactly as the logic of negation demands.
<!--zh-->
否定是唯一一个压缩命题本身不能确定等价的情形，缘于否定的反变性：`¬ P` 的证明要消费 `P` 的证明。压缩命题取 `Logic.¬ P'`，其底层类型把 `⟨ P' ⟩` 映入空类型。两端都是命题，故 `propBiimpl→Equiv` 适用；两个方向沿相反方向使用 `eP`：要从压缩的反驳 `p'` 得到 `np : ¬ P` 的矛盾，把原像 `invEq eP p'` 喂给 `np`；反向则把 `p : ⟨ P ⟩` 的像 `equivFun eP p` 喂给 `np'`。等价的求值与逆恰好按否定的逻辑以相反的变差出现。
<!--ja-->
否定だけは、圧縮された命題だけでは同値が定まりません。否定は反変だからです。`¬ P` の証明は `P` の証明を消費します。圧縮された命題は `Logic.¬ P'` であり、その基礎の型は `⟨ P' ⟩` を空な型へ送ります。両側とも命題なので `propBiimpl→Equiv` が使え、二つの方向は `eP` を逆向きに使います。圧縮された反証 `p'` から `np : ¬ P` の矛盾を作るには、原像 `invEq eP p'` を `np` に適用し、逆に `p : ⟨ P ⟩` の像 `equivFun eP p` を `np'` に渡します。同値の適用と逆が、否定の論理の要求どおり、正反対の変動で現れます。
<!--/-->

```agda
small¬ {P} (P' , eP) = (Logic.¬ P') ,
  propBiimpl→Equiv (snd (¬ P)) (snd (Logic.¬ P'))
    (λ np p' → np (invEq eP p'))
    (λ np' p → np' (equivFun eP p))

small⊤ : isSmall ⊤
```

<!--en-->
The two constants close the section. Truth is small because both sides are inhabited propositions: the compressed proposition is `Logic.⊤`, and in each direction the function discards its argument and returns the unit element `tt*`. Falsity begins slightly differently: the truth value `⊥` of the algebra was defined as the hProp pair `(⊥* , isProp⊥*)`, so its underlying type is the empty type `⊥*` itself, and the compressed proposition is that same empty type packaged as an hProp. Both functions are then defined by absurdity: an argument of an empty type admits no cases.
<!--zh-->
两个常量收尾本节。真是小的，因为两端都是有元素的命题：压缩命题取 `Logic.⊤`，两个方向的函数都丢弃参数、返回单元元素 `tt*`。假的起点略有不同：代数的真值 `⊥` 本就定义为 hProp 对 `(⊥* , isProp⊥*)`，故其底层类型恰是空类型 `⊥*`，压缩命题也就是打包成 hProp 的同一个空类型。于是两个函数都用荒谬来定义：空类型的参数没有任何情形可分。
<!--ja-->
最後の二つの定数でこの節を閉じます。真が小さいのは、両側とも要素をもつ命題だからです。圧縮された命題は `Logic.⊤` であり、どちらの方向の関数も引数を捨てて単一元 `tt*` を返します。偽は少し違う始まり方をします。代数の真理値 `⊥` はもともと hProp の対 `(⊥* , isProp⊥*)` として定義されているので、その基礎の型は空な型 `⊥*` そのものであり、圧縮された命題も同じ空な型を hProp にまとめたものです。したがって両方の関数は背理で定義されます。空な型の引数には場合分けが存在しないのです。
<!--/-->

```agda
small⊤ = Logic.⊤ ,
  propBiimpl→Equiv (⊤ .snd) (snd (Logic.⊤ {ℓ}))
    (λ _ → tt*) (λ _ → tt*)

small⊥ : isSmall ⊥
small⊥ = (⊥* , isProp⊥*) ,
```

<!--en-->
The absurd case analysis `(λ ())` in each direction is the whole content of the falsity proof: `⊥*` has no constructors, so a function out of it requires no defining clauses. This is the first appearance of a theme that returns with force in the Δ₀ section: absence of constructors does real logical work.
<!--zh-->
两个方向中的荒谬情形分析 `(λ ())` 就是假性证明的全部内容：`⊥*` 没有构造子，因此从它出发的函数无需任何定义子句。这是「构造子缺席能做真正的逻辑工作」这一主题的首次登场，它将在 Δ₀ 一节强势回归。
<!--ja-->
両方向の背理的な場合分け `(λ ())` こそが、偽の証明の内容のすべてです。`⊥*` には構成子がないため、そこからの関数には定義のための節が一切要りません。これは、構成子の不在が実際の論理的仕事をする、というテーマの最初の登場であり、Δ₀ の節で強い形で再登場します。
<!--/-->

```agda
  propBiimpl→Equiv isProp⊥* isProp⊥* (λ ()) (λ ())
```

<!--en-->
## Bounded quantifiers preserve smallness

The connectives suffice only for quantifier-free truth values, and one bounded quantifier in a formula would already break the induction of the next section. This section removes that obstacle. A quantifier over all of `V ℓ` ranges over the large carrier `S : Type (ℓ-suc ℓ)`, so the constructions used here do not by themselves compress its truth value. A quantifier **bounded by a set `a`** ranges, semantically, only over the members of `a`, and those members are presented by a small index type: the monic presentation gives `a` as `sett ⟪ a ⟫ ⟪ a ⟫↪` with `⟪ a ⟫ : Type ℓ`. Quantifying over `⟪ a ⟫` instead therefore produces a truth value built from the small propositions `sm (⟪ a ⟫↪ m)` by a Π or a truncated Σ, and both compress.

The bridge between the two quantifications is `∈-asFiber`{.Agda}: from an inhabitant of `x ∈ᵗ a` it returns an actual fiber of `⟪ a ⟫↪` over `x`, a pair of an index `m` with a path `⟪ a ⟫↪ m ≡ x`. The fiber is **untruncated**, because `⟪ a ⟫↪` is an embedding, so passing from a member of `a` back to an index of `⟪ a ⟫` is a function, not a choice. This is what lets the backward directions of both lemmas proceed without any selection.
<!--zh-->
## 有界量词保小

联结词只够处理无量词的真值，而公式里出现一个有界量词就足以让下一节的归纳中断。本节移除这一障碍。以整个 `V ℓ` 为范围的量词在大载体 `S : Type (ℓ-suc ℓ)` 上量化，本章已有的构造本身不能压缩其真值；而**以集合 `a` 为界**的量词在语义上只在 `a` 的成员上量化，这些成员由一个小的索引类型呈现：单射呈现把 `a` 给作 `sett ⟪ a ⟫ ⟪ a ⟫↪`，其中 `⟪ a ⟫ : Type ℓ`。于是改在 `⟪ a ⟫` 上量化，得到的真值由小的命题 `sm (⟪ a ⟫↪ m)` 经 Π 或截断 Σ 构成，两者都能压缩。

两种量化之间的桥梁是 `∈-asFiber`{.Agda}：从 `x ∈ᵗ a` 的元素出发，它返回 `⟪ a ⟫↪` 在 `x` 上的一个真正的纤维，即索引 `m` 配路径 `⟪ a ⟫↪ m ≡ x` 的对。该纤维**不加截断**，因为 `⟪ a ⟫↪` 是嵌入，所以从 `a` 的成员回到 `⟪ a ⟫` 的索引是函数操作而非选择。两条引理的反向因此都无需任何选取。
<!--ja-->
## 有界量化子による保存

結合子だけでは量化子を含まない真理値しか扱えず、論理式に有界量化子が一つ現れただけで次節の帰納は途絶えます。この節はその障害を取り除きます。`V ℓ` 全体を範囲とする量化子は大きな台 `S : Type (ℓ-suc ℓ)` 上で量化するため、ここまでの構成だけではその真理値を圧縮できません。一方、**集合 `a` で有界な**量化子は、意味論の上では `a` の要素の上だけで量化します。その要素は小さな添字の型で提示されています。単射表示は `a` を `sett ⟪ a ⟫ ⟪ a ⟫↪` として与え、`⟪ a ⟫ : Type ℓ` です。そこで `⟪ a ⟫` 上で量化すれば、得られる真理値は小さな命題 `sm (⟪ a ⟫↪ m)` を Π または切り詰められた Σ で組み合わせたものになり、どちらも圧縮できます。

二つの量化を結ぶ橋が `∈-asFiber`{.Agda} です。`x ∈ᵗ a` の要素から、`⟪ a ⟫↪` の `x` 上の実際のファイバー、すなわち添字 `m` とパス `⟪ a ⟫↪ m ≡ x` の対を返します。このファイバーは**切り詰められていません**。`⟪ a ⟫↪` が埋め込みだからです。`a` の要素から `⟪ a ⟫` の添字を取り戻すのは関数であって、選択ではありません。だから二つの補題の逆方向は、いかなる選択もなしに進みます。
<!--/-->

<!--en-->
The universal bounded quantifier states: for every member `x` of `a`, the proposition `B x` holds. Its truth value is `⋀ S (λ x → (x ∈ˢ a) ⇒ B x)`, an implication indexed over the whole carrier, where the antecedent `x ∈ˢ a` restricts attention to members. The lemma assumes each `B x` small, with witness `sm x = (B' x , e x)`, and concludes the whole universal statement small. The compressed proposition replaces membership with its small twin and the carrier with `⟪ a ⟫`: it asserts that for every index `m : ⟪ a ⟫`, the proposition `B' (⟪ a ⟫↪ m)` holds. The bound `a` enters as an explicit parameter, while the family `B` stays implicit, fixed by the goal type.
<!--zh-->
全称有界量词陈述的是：对 `a` 的每个成员 `x`，命题 `B x` 成立。其真值是 `⋀ S (λ x → (x ∈ˢ a) ⇒ B x)`，即在整个载体上索引的蕴涵，前件 `x ∈ˢ a` 把注意限制到成员上。引理假设每个 `B x` 都小，见证为 `sm x = (B' x , e x)`，并断言整个全称陈述小。压缩命题用小孪生替换隶属、用 `⟪ a ⟫` 替换载体：它断言对每个索引 `m : ⟪ a ⟫`，命题 `B' (⟪ a ⟫↪ m)` 成立。界 `a` 作为显式参数进入，族 `B` 则保持隐式、由目标类型确定。
<!--ja-->
全称の有界量化子は、`a` のすべての要素 `x` に対して命題 `B x` が成り立つと述べます。その真理値は `⋀ S (λ x → (x ∈ˢ a) ⇒ B x)` で、台全体にわたって索引付けされた含意であり、前件 `x ∈ˢ a` が注意を要素に限定します。補題は各 `B x` が小さいこと、証人 `sm x = (B' x , e x)` を仮定し、全称の主張全体が小さいと結論します。圧縮された命題は、所属をその小さな双子で、台を `⟪ a ⟫` で置き換え、すべての添字 `m : ⟪ a ⟫` に対して命題 `B' (⟪ a ⟫↪ m)` が成り立つと述べます。限界 `a` は明示的な引数として現れ、族 `B` は暗黙のままで目標の型から決まります。
<!--/-->

```agda
small-∀∈ : (a : S) {B : S → hProp (ℓ-suc ℓ)}
         → (∀ x → isSmall (B x))
         → isSmall (⋀ S (λ x → (x ∈ˢ a) ⇒ B x))
small-∀∈ a {B} sm = Qsm , propBiimpl→Equiv (snd big) (snd Qsm) fwd bwd
  where
```

<!--en-->
The forward direction converts a proof of the original statement into a proof of the compressed one. Given `f` assigning to each `x` an implication from `x ∈ˢ a` to `B x`, we must produce, for each index `m`, a proof of `B' (⟪ a ⟫↪ m)`. First apply `f` at the member `⟪ a ⟫↪ m`; this needs the antecedent, namely a proof that `⟪ a ⟫↪ m` is a member of `a`, which the conversion `∈∈ₛ` produces from the canonical witness `∈ₛ⟪ a ⟫↪ m`, itself just the pair of the index with the reflexivity of `∼`. The resulting proof of `B (⟪ a ⟫↪ m)` is then pushed through the equivalence `e` to land in the compressed proposition.
<!--zh-->
正向方向把原陈述的证明转换为压缩命题的证明。给定 `f`，它对每个 `x` 给出从 `x ∈ˢ a` 到 `B x` 的蕴涵；我们要对每个索引 `m` 产出 `B' (⟪ a ⟫↪ m)` 的证明。先在成员 `⟪ a ⟫↪ m` 处应用 `f`，这需要前件，即 `⟪ a ⟫↪ m` 是 `a` 成员的证明；转换 `∈∈ₛ` 从典范见证 `∈ₛ⟪ a ⟫↪ m` 给出它，后者不过是索引配上 `∼` 的自反性。得到的 `B (⟪ a ⟫↪ m)` 的证明再穿过等价 `e`，落入压缩命题。
<!--ja-->
順方向は、もとの主張の証明を圧縮された命題の証明へ変換します。各 `x` に `x ∈ˢ a` から `B x` への含意を割り当てる `f` が与えられたとき、各添字 `m` に対して `B' (⟪ a ⟫↪ m)` の証明を作ります。まず要素 `⟪ a ⟫↪ m` で `f` を適用します。これには前件、つまり `⟪ a ⟫↪ m` が `a` の要素である証明が要りますが、変換 `∈∈ₛ` が正準な証人 `∈ₛ⟪ a ⟫↪ m`、すなわち添字と `∼` の反射性の対からこれを与えます。得られた `B (⟪ a ⟫↪ m)` の証明は、同値 `e` を通されて圧縮された命題に落ち着きます。
<!--/-->

```agda
  big = ⋀ S (λ x → (x ∈ˢ a) ⇒ B x)
  Qsm = Logic.∀[]-syntax (λ (m : ⟪ a ⟫) → sm (⟪ a ⟫↪ m) .fst)
  fwd : ⟨ big ⟩ → ⟨ Qsm ⟩
  fwd f m = equivFun (sm (⟪ a ⟫↪ m) .snd)
                     (f (⟪ a ⟫↪ m) (∈∈ₛ {a = ⟪ a ⟫↪ m} {b = a} .snd (∈ₛ⟪ a ⟫↪ m)))
```

<!--en-->
The backward direction is where the embedding earns its keep. Given `g`, a function assigning to each index `m` a proof of `B' (⟪ a ⟫↪ m)`, we must produce, for each `x` with `x∈a : x ∈ᵗ a`, a proof of `B x`. The fiber `mf = ∈-asFiber x∈a` supplies an index `mf .fst` with a path `mf .snd : ⟪ a ⟫↪ (mf .fst) ≡ x`. Applying `g` at that index yields a proof of `B' (⟪ a ⟫↪ (mf .fst))`, which the inverse equivalence sends to `B (⟪ a ⟫↪ (mf .fst))`; the `subst` then transports it along `mf .snd` to `B x`. Note that the path, not an arbitrary choice among members, does the adjusting: had the fiber been truncated, this transport would be unavailable and the lemma would fail without extra assumptions.
<!--zh-->
反向方向正是嵌入发挥价值之处。给定 `g`，它对每个索引 `m` 给出 `B' (⟪ a ⟫↪ m)` 的证明；我们要对每个满足 `x∈a : x ∈ᵗ a` 的 `x` 产出 `B x` 的证明。纤维 `mf = ∈-asFiber x∈a` 给出索引 `mf .fst` 与路径 `mf .snd : ⟪ a ⟫↪ (mf .fst) ≡ x`。在该索引处应用 `g` 得到 `B' (⟪ a ⟫↪ (mf .fst))` 的证明，逆等价把它送到 `B (⟪ a ⟫↪ (mf .fst))`；`subst` 再沿 `mf .snd` 把它传输到 `B x`。注意做调整的是路径，而非在成员间的任意选择：若纤维被截断，这一传输就无从谈起，引理在不加额外假设时将失败。
<!--ja-->
逆方向で埋め込みが真価を発揮します。各添字 `m` に `B' (⟪ a ⟫↪ m)` の証明を割り当てる `g` が与えられたとき、`x∈a : x ∈ᵗ a` を満たす各 `x` に対して `B x` の証明を作ります。ファイバー `mf = ∈-asFiber x∈a` は、添字 `mf .fst` とパス `mf .snd : ⟪ a ⟫↪ (mf .fst) ≡ x` を与えます。その添字で `g` を適用すれば `B' (⟪ a ⟫↪ (mf .fst))` の証明が得られ、逆の同値がそれを `B (⟪ a ⟫↪ (mf .fst))` へ送り、`subst` がパス `mf .snd` に沿って `B x` へ輸送します。調整を行うのは、要素の間の任意の選択ではなくパスです。ファイバーが切り詰められていればこの輸送は不可能で、追加の仮定なしには補題は成り立ちません。
<!--/-->

```agda
  bwd : ⟨ Qsm ⟩ → ⟨ big ⟩
  bwd g x x∈a =
    subst (λ v → ⟨ B v ⟩) (mf .snd)
          (invEq (sm (⟪ a ⟫↪ (mf .fst)) .snd) (g (mf .fst)))
    where mf = ∈-asFiber {a = x} {b = a} x∈a
```

<!--en-->
The existential bounded quantifier states: some member `x` of `a` has `B x`. Its truth value is `⋁ S (λ x → (x ∈ˢ a) ⊓ B x)`, a truncated pairing of membership with `B`, and the compressed proposition asserts, merely, some index `m : ⟪ a ⟫` with `B' (⟪ a ⟫↪ m)`. The hypothesis and conclusion mirror the universal case, but the proofs differ in kind: because both sides are truncated existentials, neither direction returns a function; each maps truncations to truncations.
<!--zh-->
存在有界量词陈述的是：`a` 的某个成员 `x` 满足 `B x`。其真值是 `⋁ S (λ x → (x ∈ˢ a) ⊓ B x)`，即隶属与 `B` 的截断配对；压缩命题仅仅断言存在索引 `m : ⟪ a ⟫` 使 `B' (⟪ a ⟫↪ m)`。假设与结论都镜像全称情形，但证明性质不同：由于两侧都是截断的存在陈述，两个方向都不返回函数，而是把截断映到截断。
<!--ja-->
存在の有界量化子は、`a` のある要素 `x` が `B x` を満たすと述べます。その真理値は `⋁ S (λ x → (x ∈ˢ a) ⊓ B x)`、すなわち所属と `B` の切り詰められた組み合わせであり、圧縮された命題は、`B' (⟪ a ⟫↪ m)` を満たす添字 `m : ⟪ a ⟫` が存在するとだけ主張します。仮定と結論は全称の場合と鏡像ですが、証明の性質は異なります。両側とも切り詰められた存在主張なので、どちらの方向も関数を返さず、切り詰めを切り詰めへ写します。
<!--/-->

```agda

small-∃∈ : (a : S) {B : S → hProp (ℓ-suc ℓ)}
         → (∀ x → isSmall (B x))
         → isSmall (⋁ S (λ x → (x ∈ˢ a) ⊓ B x))
small-∃∈ a {B} sm = Qsm , propBiimpl→Equiv (snd big) (snd Qsm) fwd bwd
  where
```

<!--en-->
Forward: `PT.map` applies a pointwise construction inside the truncation, which is permitted because the target, the compressed proposition, is again a proposition. The pointwise step unpacks a truncated triple `(x , x∈a , bx)` of a member, its membership evidence, and a proof of `B x`; this unpacking is legitimate only because it happens under the truncation, where the choice of `x` need never be exported. The fiber of `x∈a` then yields an index, and the proof `bx` is transported along the fiber's path, in the direction `sym (mf .snd)`, before the equivalence compresses it. Compare this with the universal forward direction: there a function was in hand outright, here one merely knows that such data exists.
<!--zh-->
正向：`PT.map` 在截断内部施加逐点构造，这是允许的，因为目标即压缩命题仍是命题。逐点步骤拆开截断的三元组 `(x , x∈a , bx)`：成员、其隶属证据、以及 `B x` 的证明。这一拆开之所以合法，只因它发生在截断之下，`x` 的选取永远不必导出。随后 `x∈a` 的纤维给出索引，证明 `bx` 沿纤维的路径、按 `sym (mf .snd)` 方向传输，再经等价压缩。可与全称的正向对照：那里函数是直接到手的，这里仅仅知道这样的数据存在。
<!--ja-->
順方向では、`PT.map` が切り詰めの内部で各点の構成を適用します。これは、目標である圧縮された命題が再び命題であるために許されます。各点の段階は、切り詰められた三つ組 `(x , x∈a , bx)`、すなわち要素、その所属の証拠、`B x` の証明をほどきます。これが正当なのは、切り詰めの内側で行われるからであり、`x` の選択を外へ取り出す必要は一度もありません。次に `x∈a` のファイバーが添字を与え、証明 `bx` はファイバーのパスに沿って `sym (mf .snd)` の向きに輸送され、それから同値で圧縮されます。全称の順方向と比べてください。あちらでは関数がはじめから手にあり、こちらではそのようなデータが存在するとしか知りません。
<!--/-->

```agda
  big = ⋁ S (λ x → (x ∈ˢ a) ⊓ B x)
  Qsm = Logic.∃[]-syntax (λ (m : ⟪ a ⟫) → sm (⟪ a ⟫↪ m) .fst)
  fwd : ⟨ big ⟩ → ⟨ Qsm ⟩
  fwd = PT.map λ where
    (x , x∈a , bx) →
```

<!--en-->
Backward: again under `PT.map`, a truncated pair `(m , q)` of an index and a proof of `B' (⟪ a ⟫↪ m)` is turned into a member of `a` with property `B`. The member is `⟪ a ⟫↪ m`, its membership evidence comes from `∈∈ₛ` applied to the canonical witness, and the property proof is the preimage `invEq (sm _ .snd) q`. Here no transport is needed at all: the index is given from the start, so nothing has to be recovered. The asymmetry between the two directions is exactly the asymmetry of data: one side holds an index outright, the other must manufacture one from a member, and only the embedding makes that manufacturing a function.
<!--zh-->
反向：同样在 `PT.map` 之下，截断的对 `(m , q)`，即索引与 `B' (⟪ a ⟫↪ m)` 的证明，被转换成一个具有性质 `B` 的 `a` 的成员。成员取 `⟪ a ⟫↪ m`，其隶属证据由 `∈∈ₛ` 作用于典范见证得到，性质证明是原像 `invEq (sm _ .snd) q`。这里完全不需要传输：索引一开始就给定，无须从成员恢复。两个方向之间的不对称正是数据的不对称：一侧直接握有索引，另一侧必须从成员制造索引，而只有嵌入使这一制造成为函数。
<!--ja-->
逆方向でも、やはり `PT.map` の下で、添字と `B' (⟪ a ⟫↪ m)` の証明の切り詰められた対 `(m , q)` が、性質 `B` をもつ `a` の要素へ変換されます。要素は `⟪ a ⟫↪ m` であり、その所属の証拠は正準な証人への `∈∈ₛ` の適用から、性質の証明は原像 `invEq (sm _ .snd) q` から得られます。ここでは輸送はまったく要りません。添字は最初から与えられており、要素から取り戻す必要がないからです。二つの方向の非対称性はそのままデータの非対称性です。一方は添字をはじめから持ち、他方は要素から添字を作り出さねばならず、埋め込みだけがその作り出しを関数にします。
<!--/-->

```agda
      let mf = ∈-asFiber {a = x} {b = a} x∈a
      in mf .fst ,
         equivFun (sm (⟪ a ⟫↪ (mf .fst)) .snd)
                  (subst (λ v → ⟨ B v ⟩) (sym (mf .snd)) bx)
  bwd : ⟨ Qsm ⟩ → ⟨ big ⟩
```

<!--en-->
With this pair of lemmas the bounded quantifier clauses of the semantics are covered, and the induction of the next section can pass through any formula whose quantifiers are all bounded. Worth noting is what was not used: no classical principle, no choice, and no resizing entered either proof. The only substantive facts were the monic presentation of membership and the property that `⟪ a ⟫↪` is an embedding.
<!--zh-->
有了这对引理，语义中的有界量词子句已被覆盖，下一节的归纳可以穿过任何量词皆有界的公式。值得注意的是没有用到什么：两条证明都没有使用任何经典原则、选择，也没有使用降层。唯一实质的事实是隶属的单射呈现，以及 `⟪ a ⟫↪` 是嵌入这一性质。
<!--ja-->
この一対の補題で、意味論の有界量化子の節はすべて賄われ、次節の帰納は量化子がすべて有界であるどんな論理式も通過できます。使わなかったものに注目してください。どちらの証明にも古典的な原理も選択もリサイズも現れません。実質的に使ったのは、所属の単射表示と、`⟪ a ⟫↪` が埋め込みであるという事実だけです。
<!--/-->

```agda
  bwd = PT.map λ where
    (m , q) → ⟪ a ⟫↪ m , ∈∈ₛ {a = ⟪ a ⟫↪ m} {b = a} .snd (∈ₛ⟪ a ⟫↪ m)
            , invEq (sm (⟪ a ⟫↪ m) .snd) q
```

<!--en-->
## From smallness to separation

This section is where smallness pays off. The library's separation construction `SeparationSet`{.Agda} builds, for a set `a` and a predicate `ϕ : V ℓ → hProp ℓ` valued in the **lower** universe, a set whose members are exactly the members of `a` satisfying `ϕ`. Such a construction is impossible for upper-universe predicates, since its internal index type would have to live at level `ℓ`. The lemma below is the adapter: given a predicate `P` on `S` with a smallness witness at every point, it produces a set `s` in the structure together with the membership specification `y ∈ˢ s` if and only if `y ∈ˢ a` and `P y`, stated as paths in the style of the model record's separation field.

This is also where the pieces assemble into a plan. Whatever first supplies smallness of a predicate, whether the bounded quantifiers of the last section or the essentially small worlds of the last, this lemma converts the small predicate into a set, once and in the same way.
<!--zh-->
## 从小性到分离

本节是小性兑现之处。库的分离构造 `SeparationSet`{.Agda} 对集合 `a` 与取值于**低**宇宙的谓词 `ϕ : V ℓ → hProp ℓ`，构造一个集合，其成员恰是 `a` 中满足 `ϕ` 的成员。对上宇宙谓词这种构造不可能：其内部索引类型必须落在层级 `ℓ`。下面的引理是适配器：给定 `S` 上逐点带小性见证的谓词 `P`，它产出结构中的集合 `s`，并附上成员规格「`y ∈ˢ s` 当且仅当 `y ∈ˢ a` 且 `P y`」，以模型 record 分离字段风格的路径表述。

这里也是各部件汇成计划之处。无论谓词的小性最先来自何处，是上一节的有界量词，还是最后的本质小世界，本引理都把小谓词一次性、以同一方式变成集合。
<!--ja-->
## 小ささから分出へ

この節は、小ささが実を結ぶ場所です。ライブラリの分出構成 `SeparationSet`{.Agda} は、集合 `a` と、**低い**宇宙に値をもつ述語 `ϕ : V ℓ → hProp ℓ` に対して、`a` の要素のうち `ϕ` を満たすもの全体を要素とする集合を作ります。上の宇宙に値をもつ述語では、内部の添字の型がレベル `ℓ` に属さねばならないため、このような構成は不可能です。下の補題はその適合装置です。各点で小ささの証人をもつ `S` 上の述語 `P` が与えられれば、構造の中の集合 `s` と、所属の仕様「`y ∈ˢ s` は `y ∈ˢ a` かつ `P y` とちょうど同じ」とを、モデルの record の分出フィールドと同じ形式のパスとして返します。

ここで部品が計画へ組み上がります。述語の小ささが最初にどこから供給されるかに関わりなく、前節の有界量化子であれ、最後の本質的に小さな世界であれ、この補題は小さな述語を一度だけ、同じ方法で集合へ変えます。
<!--/-->

<!--en-->
The statement deserves a close reading. The result is a dependent pair: a set `s` of the structure, and for every `y` a **path** `(y ∈ˢ s) ≡ ((y ∈ˢ a) ⊓ P y)` in the type `hProp (ℓ-suc ℓ)`, not merely a bi-implication between the underlying propositions. This matches the shape of the separation field in the model record, so the construction can be transplanted into any structure that must verify the separation axiom. The proof applies the library construction to `a` and to the compressed predicate, and assembles the required paths from the two directions of the resulting specification.
<!--zh-->
这条陈述值得细读。结果是一个依值对：结构中的集合 `s`，以及对每个 `y` 的**路径** `(y ∈ˢ s) ≡ ((y ∈ˢ a) ⊓ P y)`，落在类型 `hProp (ℓ-suc ℓ)` 中，而不只是底层命题间的双向蕴含。这与模型 record 分离字段的形状一致，因此该构造可以被移植进任何需要验证分离公理的结构。证明把库构造应用于 `a` 与压缩后的谓词，再由所得规格的两个方向拼装出所需的路径。
<!--ja-->
この主張は注意して読む価値があります。結果は依存対です。構造の集合 `s` と、各 `y` に対する `hProp (ℓ-suc ℓ)` における**パス** `(y ∈ˢ s) ≡ ((y ∈ˢ a) ⊓ P y)` であり、基礎の命題の間の双条件ではありません。これはモデルの record の分出フィールドの形と一致するため、この構成は分出公理を検証すべきどんな構造にも移植できます。証明は、ライブラリの構成を `a` と圧縮された述語に適用し、得られた仕様の二つの方向から必要なパスを組み上げます。
<!--/-->

```agda
separateFromSmall : (a : S) (P : S → hProp (ℓ-suc ℓ))
                  → (∀ y → isSmall (P y))
                  → Σ[ s ∈ S ] (∀ y → (y ∈ˢ s) ≡ ((y ∈ˢ a) ⊓ P y))
separateFromSmall a P sm = Sep.SEPAREE , λ y → ⇔toPath (fwd y) (bwd y)
  where
```

<!--en-->
The compressed predicate is assembled first: `ϕₛ y` is by definition the lower-universe stand-in `sm y .fst` extracted from the pointwise smallness witness. The library module `Sep` is then instantiated at `a` and `ϕₛ`, and its resulting set is named `Sep.SEPAREE`. This is the only place in the chapter where the library's separation runs; anything else this part separates goes through this lemma.
<!--zh-->
先组装压缩谓词：`ϕₛ y` 按定义就是从逐点小性见证中取出的低宇宙替身 `sm y .fst`。随后库模块 `Sep` 在 `a` 与 `ϕₛ` 处实例化，其结果集合名为 `Sep.SEPAREE`。这是本章唯一一处运行库分离的地方；本部分其余的分离都要经过这条引理。
<!--ja-->
まず圧縮された述語を組み立てます。`ϕₛ y` は定義により、各点の小ささの証人から取り出した低い宇宙の代替物 `sm y .fst` です。次にライブラリのモジュール `Sep` を `a` と `ϕₛ` で具体化し、その結果の集合を `Sep.SEPAREE` とします。本章でライブラリの分出が使われるのはここだけです。この部でほかに分出するものはすべてこの補題を通ります。
<!--/-->

```agda
  ϕₛ : S → hProp ℓ
  ϕₛ y = sm y .fst
  module Sep = SeparationSet a ϕₛ
  fwd : ∀ y → ⟨ y ∈ˢ Sep.SEPAREE ⟩ → ⟨ (y ∈ˢ a) ⊓ P y ⟩
  fwd y y∈s = ∈∈ₛ {a = y} {b = a} .snd (Sep.separation-ax y .fst y∈ₛs .fst)
```

<!--en-->
Both directions translate between the structure membership `y ∈ˢ Sep.SEPAREE` and the pair `y ∈ˢ a` plus `P y`. Forward: convert `y∈s` through `∈∈ₛ` into the small membership, feed it to the library's specification `separation-ax y` in its forward direction, and obtain the pair of `y ∈ₛ a` and the compressed property; the first component converts back to `y ∈ᵗ a` via `∈∈ₛ` in the other orientation, and the second is expanded through the inverse of the equivalence `e`. Backward is the mirror image: convert membership in `a` to its small form, compress the property proof with `equivFun`, and let `separation-ax y` in its backward direction produce membership in `Sep.SEPAREE`, converted once more through `∈∈ₛ`. The library specification does the set-theoretic work; the equivalences do the universe bookkeeping.
<!--zh-->
两个方向都在结构隶属 `y ∈ˢ Sep.SEPAREE` 与「`y ∈ˢ a` 加 `P y`」之间翻译。正向：经 `∈∈ₛ` 把 `y∈s` 转成小隶属，喂给库规格 `separation-ax y` 的正向，得到 `y ∈ₛ a` 与压缩性质的配对；第一分量再以另一朝向经 `∈∈ₛ` 转回 `y ∈ᵗ a`，第二分量经等价 `e` 的逆展开。反向是镜像：把 `a` 中隶属转成小形式，用 `equivFun` 压缩性质证明，让 `separation-ax y` 的反向产出 `Sep.SEPAREE` 中的隶属，再经 `∈∈ₛ` 转换一次。库规格承担集合论的工作，等价承担宇宙层面的记账。
<!--ja-->
両方向とも、構造の所属 `y ∈ˢ Sep.SEPAREE` と「`y ∈ˢ a` かつ `P y`」との間を翻訳します。順方向では、`∈∈ₛ` で `y∈s` を小さな所属へ変換し、ライブラリの仕様 `separation-ax y` の順方向へ渡して、`y ∈ₛ a` と圧縮された性質の対を得ます。第一成分は逆の向きの `∈∈ₛ` で `y ∈ᵗ a` へ戻し、第二成分は同値 `e` の逆で展開します。逆方向はその鏡像です。`a` での所属を小さな形へ変換し、`equivFun` で性質の証明を圧縮し、`separation-ax y` の逆方向に `Sep.SEPAREE` への所属を作らせ、もう一度 `∈∈ₛ` で変換します。集合論の仕事をするのはライブラリの仕様であり、宇宙レベルの帳簿づけをするのは同値です。
<!--/-->

```agda
            , invEq (sm y .snd) (Sep.separation-ax y .fst y∈ₛs .snd)
    where y∈ₛs = ∈∈ₛ {a = y} {b = Sep.SEPAREE} .fst y∈s
  bwd : ∀ y → ⟨ (y ∈ˢ a) ⊓ P y ⟩ → ⟨ y ∈ˢ Sep.SEPAREE ⟩
  bwd y yp = ∈∈ₛ {a = y} {b = Sep.SEPAREE} .snd (Sep.separation-ax y .snd
               (∈∈ₛ {a = y} {b = a} .fst (yp .fst) , equivFun (sm y .snd) (yp .snd)))
```

<!--en-->
## Δ₀ formulas evaluate small

The previous sections built a stock of smallness witnesses: two atoms, four connectives, two constants, and two bounded quantifiers. This section converts the stock into a theorem by induction over the `Δ₀` witness itself. Recall from the chapter on the Lévy hierarchy that `Δ₀`{.Agda} is an inductive witness, one per formula, whose constructors certify that the formula is built from atoms by connectives and bounded quantifiers only. The theorem states that any formula carrying such a witness has a small truth value at every environment. Since the witness is defined inductively, the proof is an induction with one case per constructor, and each case is exactly one of the stock lemmas.

The case analysis has an instructive omission: there are no cases for the unbounded quantifiers `∀̇` and `∃̇_`, because the witness type has no constructors for them. Absence of constructors is what makes the classification; a formula with an unbounded quantifier simply cannot carry a Δ₀ witness, so the induction never needs to face it. The Lévy hierarchy thus functions as an accounting of universe cost: Δ₀ is exactly the fragment whose truth values come without it.
<!--zh-->
## Δ₀ 公式求值小

前几节积累了小性见证的库存：两个原子、四个联结词、两个常量与两个有界量词。本节通过对 `Δ₀` 见证本身的归纳把库存变成定理。回顾 Lévy 层级一章，`Δ₀`{.Agda} 是归纳定义的见证，每个公式至多一个，其构造子证明该公式仅由原子经联结词与有界量词构成。定理陈述：凡带有这种见证的公式，在任何环境下的真值都小。由于见证是归纳定义的，证明就是每个构造子一个情形的归纳，而每个情形恰好就是库存中的一条引理。

情形分析有一个富有教益的省略：无界量词 `∀̇` 与 `∃̇_` 没有对应情形，因为见证类型本就没有它们的构造子。构造子的缺席正是分类的实现方式；带无界量词的公式根本无法携带 Δ₀ 见证，归纳也就永远不必面对它。Lévy 层级由此充任宇宙代价的核算：Δ₀ 恰是真值无需付出这一代价的片段。
<!--ja-->
## Δ₀ 論理式の評価は小さい

ここまでの節で、小ささの証人の備えができました。原子二つ、結合子四つ、定数二つ、有界量化子二つです。この節は、その備えを `Δ₀` の証人自身に関する帰納法で定理へ変えます。Lévy 階層の章で思い出されるように、`Δ₀`{.Agda} は帰納的な証人であり、論理式ごとに一つ、その構成子はその論理式が原子から結合子と有界量化子だけで作られていることを証明します。定理は、そのような証人をもつ論理式の真理値がどの環境でも小さいと述べます。証人は帰納的に定義されるので、証明は構成子ごとに一つの場合を持つ帰納法であり、それぞれの場合がまさに備えられた補題の一つです。

場合分けには示唆的な省略があります。非有界量化子 `∀̇` と `∃̇_` の場合は存在しません。証人の型にその構成子がないからです。構成子の不在こそが分類を実現しており、非有界量化子を含む論理式はそもそも Δ₀ の証人をもてないので、帰納法がそれに直面することは決してありません。こうして Lévy 階層は宇宙のコストの計算として機能します。Δ₀ は、そのコストなしに真理値が手に入る、まさにそのフラグメントなのです。
<!--/-->

<!--en-->
The setup instantiates the semantics once and for all: `SemanticsV` is the satisfaction relation over `𝒮ᵥ`{.Agda} with truth values in `hProp (ℓ-suc ℓ)`, so a formula's truth value is exactly a proposition of the kind the whole chapter has been compressing. The environment type `S ^ n` is the length-`n` vector notation. The module is parameterized by a constant interpretation `ι : K → S`, so the theorem holds for any choice of constants; the canonical case `ι` the identity is taken at the end of the chapter. Inside, `open SemanticsV.At K ι` brings the term evaluation `⟦_⟧` and satisfaction `_⊨_` into scope. The goal type deserves attention: `Δ₀-small` is a function from a Δ₀ witness to, for each environment `γ`, a smallness witness of `γ ⊨ φ`. The induction is over the witness, with the formula and environment universally quantified around it.
<!--zh-->
准备工作一次性实例化语义：`SemanticsV` 是 `𝒮ᵥ`{.Agda} 上、真值取于 `hProp (ℓ-suc ℓ)` 的满足关系，因此公式的真值恰是全章一直在压缩的那类命题。环境类型 `S ^ n` 是长度 `n` 的向量记法。模块由常元解释 `ι : K → S` 参数化，故定理对常元的任意选取成立；恒等函数这一典范情形在本章末取用。模块内 `open SemanticsV.At K ι` 把词项求值 `⟦_⟧` 与满足 `_⊨_` 带入作用域。目标类型值得注意：`Δ₀-small` 是从 Δ₀ 见证到「对每个环境 `γ`，`γ ⊨ φ` 的小性见证」的函数。归纳针对见证进行，公式与环境在其外围被全称量化。
<!--ja-->
準備として、意味論を一度だけ具体化します。`SemanticsV` は `𝒮ᵥ`{.Agda} 上の、真理値を `hProp (ℓ-suc ℓ)` にとる充足関係であり、したがって論理式の真理値は、この章がずっと圧縮してきた種類の命題そのものです。環境の型 `S ^ n` は長さ `n` のベクトルの記法です。モジュールは定数解釈 `ι : K → S` でパラメータ化されるので、定理は定数のどんな選び方に対しても成り立ちます。恒等写像という正準な場合は章の末尾で取られます。内部の `open SemanticsV.At K ι` は、項の評価 `⟦_⟧` と充足 `_⊨_` をスコープに入れます。目標の型に注意してください。`Δ₀-small` は、Δ₀ の証人から、各環境 `γ` に対する `γ ⊨ φ` の小ささの証人への関数です。帰納法は証人に対して行われ、論理式と環境はその周りで全称化されています。
<!--/-->

```agda
module SemanticsV = FOL.Semantics (hPropAlgebra (ℓ-suc ℓ)) 𝒮ᵥ
open SemanticsV using ( _^_ )

module Δ₀Small {ℓc} {K : Type ℓc} (ι : K → S) where

  open SemanticsV.At K ι

  Δ₀-small : ∀ {n} {φ : Formula K n} → Δ₀ φ → (γ : S ^ n) → isSmall (γ ⊨ φ)
```

<!--en-->
The atom cases invoke the first two stock lemmas directly, after evaluating the two terms in the environment `γ`: membership becomes `small-∈` applied to the values of `t` and `u`, equality becomes `small-≡`. The three binary connective cases are equally direct: the induction hypotheses `Δ₀-small c γ` and `Δ₀-small d γ` are smallness witnesses for the subformulas' truth values, and the closure lemma of the corresponding connective combines them. The explicit instantiation `{P = γ ⊨ φ}` merely records which propositions the witnesses compress; Agda could infer them, but writing them out documents the shape of the case.
<!--zh-->
原子情形在环境 `γ` 中求值两个词项后，直接调用前两条库存引理：隶属变为对 `t`、`u` 的值应用 `small-∈`，相等变为 `small-≡`。三个二元联结词情形同样直接：归纳假设 `Δ₀-small c γ` 与 `Δ₀-small d γ` 是子公式真值的小性见证，对应联结词的封闭引理把它们组合起来。显式实例化 `{P = γ ⊨ φ}` 只是记录见证所压缩的是哪些命题；Agda 本可推断，但写出来记录了该情形的形状。
<!--ja-->
原子の場合は、環境 `γ` で二つの項を評価したうえで、備えられた最初の二つの補題を直接呼びます。所属は `t` と `u` の値への `small-∈` の適用に、等号は `small-≡` になります。三つの二項結合子の場合も同じく直接です。帰納法の仮定 `Δ₀-small c γ` と `Δ₀-small d γ` が部分論理式の真理値の小ささの証人であり、対応する結合子の閉包補題がそれらを組み合わせます。明示的な具体化 `{P = γ ⊨ φ}` は、証人がどの命題を圧縮するかを記録するだけです。Agda は推論できますが、書き出すことで場合の形が文書化されます。
<!--/-->

```agda
  Δ₀-small (δ-∈ {t = t} {u}) γ = small-∈ (⟦ t ⟧ γ) (⟦ u ⟧ γ)
  Δ₀-small (δ-≐ {t = t} {u}) γ = small-≡ (⟦ t ⟧ γ) (⟦ u ⟧ γ)
  Δ₀-small (δ-∧ {φ = φ} {ψ} c d) γ =
    small⊓ {P = γ ⊨ φ} {Q = γ ⊨ ψ} (Δ₀-small c γ) (Δ₀-small d γ)
  Δ₀-small (δ-∨ {φ = φ} {ψ} c d) γ =
```

<!--en-->
The remaining connective-shaped case is falsity, and then the two bounded quantifiers. Falsity needs no environment at all: the witness `δ-⊥` carries no subformulas, and the case is just `small⊥`. The bounded quantifier cases are the interesting ones. For `δ-∀∈`, the formula is `∀̇∈ t φ`, whose truth value is `⋀ S (λ x → (x ∈ˢ ⟦ t ⟧ γ) ⇒ ((x ∷ γ) ⊨ φ))`; this is precisely the shape that `small-∀∈` consumes, with `a` the value of `t` and the family `B x` the truth value of the body at the extended environment `x ∷ γ`. The induction hypothesis is applied at the extended environment, which is legitimate because the witness `c` certifies the body `φ` itself.
<!--zh-->
其余联结词形状的情形是假，然后是两个有界量词。假完全不需要环境：见证 `δ-⊥` 不携带子公式，该情形就是 `small⊥`。有界量词情形才有意思。对 `δ-∀∈`，公式是 `∀̇∈ t φ`，其真值是 `⋀ S (λ x → (x ∈ˢ ⟦ t ⟧ γ) ⇒ ((x ∷ γ) ⊨ φ))`；这恰好是 `small-∀∈` 消费的形状，其中 `a` 取 `t` 的值，族 `B x` 取体公式在扩展环境 `x ∷ γ` 下的真值。归纳假设在扩展环境处应用；这是合法的，因为见证 `c` 证明的正是体公式 `φ` 本身。
<!--ja-->
残る結合子の形の場合は偽であり、次いで二つの有界量化子です。偽には環境がまったく要りません。証人 `δ-⊥` は部分論理式を運ばず、この場合はただ `small⊥` です。有界量化子の場合が興味の対象です。`δ-∀∈` では論理式は `∀̇∈ t φ` であり、その真理値は `⋀ S (λ x → (x ∈ˢ ⟦ t ⟧ γ) ⇒ ((x ∷ γ) ⊨ φ))` です。これは `small-∀∈` が消費する形状そのものであり、`a` は `t` の値、族 `B x` は拡張された環境 `x ∷ γ` での本体の真理値です。帰納法の仮定は拡張された環境で適用されます。証人 `c` が証明するのは本体 `φ` 自身なので、これは正当です。
<!--/-->

```agda
    small⊔ {P = γ ⊨ φ} {Q = γ ⊨ ψ} (Δ₀-small c γ) (Δ₀-small d γ)
  Δ₀-small (δ-⇒ {φ = φ} {ψ} c d) γ =
    small⇒ {P = γ ⊨ φ} {Q = γ ⊨ ψ} (Δ₀-small c γ) (Δ₀-small d γ)
  Δ₀-small δ-⊥ γ = small⊥
  Δ₀-small (δ-∀∈ {t = t} {φ = φ} c) γ =
```

<!--en-->
The existential bounded case mirrors the universal one exactly, with `small-∃∈` in place of `small-∀∈` and the conjunction-shaped truth value `⋁ S (λ x → (x ∈ˢ ⟦ t ⟧ γ) ⊓ ((x ∷ γ) ⊨ φ))` matched against `small-∃∈`'s conclusion. This closes the induction: every constructor of the witness type has a case, every case is one stock lemma, and no case remains for the unbounded quantifiers. The theorem `Δ₀-small` is thus the point where the earlier sections stop being isolated facts and become a statement about the formal language.
<!--zh-->
存在有界情形与全称完全镜像：用 `small-∃∈` 替换 `small-∀∈`，把合取形状的真值 `⋁ S (λ x → (x ∈ˢ ⟦ t ⟧ γ) ⊓ ((x ∷ γ) ⊨ φ))` 对上 `small-∃∈` 的结论。归纳就此闭合：见证类型的每个构造子都有情形，每个情形都是一条库存引理，而无界量词不再留下任何情形。定理 `Δ₀-small` 由此成为前几节从孤立事实转变为关于形式语言之陈述的转折点。
<!--ja-->
存在の有界量化の場合は全称の場合と正確に鏡像で、`small-∀∈` の代わりに `small-∃∈` を使い、連言の形の真理値 `⋁ S (λ x → (x ∈ˢ ⟦ t ⟧ γ) ⊓ ((x ∷ γ) ⊨ φ))` を `small-∃∈` の結論に合わせます。これで帰納法は閉じます。証人の型のすべての構成子に場合があり、すべての場合が備えられた補題の一つであり、非有界量化子に残る場合はありません。定理 `Δ₀-small` は、ここでこれまでの節が孤立した事実から、形式言語についての主張へと変わる地点なのです。
<!--/-->

```agda
    small-∀∈ (⟦ t ⟧ γ) {B = λ x → (x ∷ γ) ⊨ φ} (λ x → Δ₀-small c (x ∷ γ))
  Δ₀-small (δ-∃∈ {t = t} {φ = φ} c) γ =
    small-∃∈ (⟦ t ⟧ γ) {B = λ x → (x ∷ γ) ⊨ φ} (λ x → Δ₀-small c (x ∷ γ))
```

<!--en-->
## Δ₀ separation without resizing

Compose the induction of the last section with the adapter of the section before it, and the chapter's central theorem appears. Take the canonical constant interpretation, in which the constants of the language are the sets of the structure themselves and `ι` is the identity. Then a Δ₀ formula `φ` with one free variable defines a pointwise-small predicate on `S`, and `separateFromSmall` turns it into a set. The result is a full instance of the separation axiom schema restricted to Δ₀ formulas, proved with no resizing principle, no classical axiom, and no choice: the smallness is supplied by the induction, and the library construction does the rest. The model chapter still owes the unrestricted separation axiom; this theorem shows that the Δ₀ tier of the Lévy hierarchy needs nothing beyond the representation of `V`.
<!--zh-->
## 无需命题降层的 Δ₀ 分离

把上一节的归纳与之前的适配器复合，本章的核心定理便出现了。取典范常元解释：语言的常元就是结构中的集合本身，`ι` 为恒等函数。此时带一个自由变量的 Δ₀ 公式 `φ` 在 `S` 上定义一个逐点小的谓词，`separateFromSmall` 把它变成集合。结果是分离公理模式限制到 Δ₀ 公式的完整实例，证明中既无命题降层原则，也无任何经典公理或选择：小性由归纳供给，其余交给库构造。模型章仍欠无限制的分离公理；本定理说明，Lévy 层级中的 Δ₀ 档无需 `V` 的表示之外的任何东西。
<!--ja-->
## 命題リサイズを要しない Δ₀ 分出

前節の帰納法と、その前の節の適合装置を合成すれば、本章の中心定理が現れます。正準な定数解釈、すなわち言語の定数が構造の集合そのものであり `ι` が恒等写像である場合をとります。このとき自由変数を一つもつ Δ₀ 論理式 `φ` は `S` 上の各点で小さい述語を定義し、`separateFromSmall` がそれを集合へ変えます。結果は、Δ₀ 論理式に制限された分出公理図式の完全な実例であり、命題リサイズの原理も古典的公理も選択も一切使わずに証明されます。小ささは帰納法が供給し、残りはライブラリの構成が担います。モデルの章はまだ制限なしの分出公理を証明する必要がありますが、この定理は、Lévy 階層の Δ₀ の階層が `V` の表示以外に何も要しないことを示しています。
<!--/-->

<!--en-->
The two opening lines fix the canonical interpretation: `Δ₀Small id` instantiates the induction at the identity, and the satisfaction relation for one free variable is re-exported as `_⊨_`. The theorem's type is the separation specification with `φ` in place of an arbitrary predicate: a set `s` such that, for every `y`, membership in `s` is equal, as truth values, to membership in `a` conjoined with `y` satisfying `φ` at the one-point environment `y ∷ []`. The proof is a single application of `separateFromSmall`, passing the predicate `λ y → (y ∷ []) ⊨ φ` together with its pointwise smallness, which is `Δ₀-small c` applied at every one-point environment. Nothing else intervenes: the Δ₀ witness `c` is consumed exactly once, by the induction.
<!--zh-->
开头两行固定典范解释：`Δ₀Small id` 在恒等处实例化归纳，单自由变量的满足关系再导出为 `_⊨_`。定理的类型是以 `φ` 替换任意谓词的分离规格：一个集合 `s`，使得对每个 `y`，`s` 中的隶属作为真值等于 `a` 中的隶属与「`y` 在单元环境 `y ∷ []` 下满足 `φ`」的合取。证明是 `separateFromSmall` 的一次应用：传入谓词 `λ y → (y ∷ []) ⊨ φ` 及其逐点小性，后者是 `Δ₀-small c` 在每个单元环境处的应用。此外别无他物：Δ₀ 见证 `c` 恰好被归纳消费一次。
<!--ja-->
冒頭の二行は正準な解釈を固定します。`Δ₀Small id` が恒等写像で帰納法を具体化し、自由変数一つの充足関係が `_⊨_` として再エクスポートされます。定理の型は、任意の述語の代わりに `φ` を入れた分出の仕様です。すなわち集合 `s` で、各 `y` に対して `s` への所属が、真理値として、`a` への所属と「一点環境 `y ∷ []` で `y` が `φ` を満たす」との連言に等しいもの。証明は `separateFromSmall` の一度の適用であり、述語 `λ y → (y ∷ []) ⊨ φ` とその各点の小ささ、すなわちすべての一点環境での `Δ₀-small c` の適用を渡すだけです。ほかに何も介在しません。Δ₀ の証人 `c` は帰納法によってちょうど一度消費されるのです。
<!--/-->

```agda
open Δ₀Small id
open SemanticsV.At S id using ( _⊨_ )

separateΔ₀ : (a : S) (φ : Formula S 1) → Δ₀ φ
           → Σ[ s ∈ S ] (∀ y → (y ∈ˢ s) ≡ ((y ∈ˢ a) ⊓ ((y ∷ []) ⊨ φ)))
separateΔ₀ a φ c = separateFromSmall a (λ y → (y ∷ []) ⊨ φ) (λ y → Δ₀-small c (y ∷ []))
```

<!--en-->
## Essentially small worlds

The Δ₀ theorem prices every quantifier as if it ranged over all of `V ℓ`. This final register of smallness removes even that cost, by changing where the quantifier ranges. Suppose a type `A` at the upper level is equipped with an equivalence `e : X ≃ A` from a small type `X : Type ℓ`. Then quantification over `A` can be replaced, step by step, by quantification over `X`: each statement about an element `a` of `A` is read at its preimage `equivFun e m`. The bounded-quantifier lemmas are a related but distinct phenomenon: there the range was an index type presenting a set, with membership as the filter; here no boundedness hypothesis remains. Smallness is then carried not by the shape of the formula but by the shape of the world it is spoken in. Note the direction of the hypothesis: it asserts that the equivalence `e` from `X` onto `A` exists; `A` itself still lives at the upper level.
<!--zh-->
## 本质小的世界

Δ₀ 定理把每个量词都按「在全 `V ℓ` 上量化」计价。最后这一层小性通过改变量化的位置连这个代价也免除了。设上层类型 `A` 配有从小类型 `X : Type ℓ` 出发的等价 `e : X ≃ A`。那么对 `A` 的量化可以逐步替换为对 `X` 的量化：关于 `A` 中元素 `a` 的陈述，在其原像 `equivFun e m` 处读取。有界量词引理是相关但不同的现象：那里量化范围是呈现某个集合的索引类型，隶属充当过滤器；这里不再留下任何有界性假设。于是小性不是由公式的形状承载，而是由说出它的世界的形状承载。注意假设的方向：它断言的是从 `X` 到 `A` 的等价 `e` 存在；`A` 本身仍住在上层宇宙。
<!--ja-->
## 本質的に小さな世界

Δ₀ の定理は、すべての量化子をあたかも `V ℓ` 全体の上で量化するかのように評価しました。小ささの最後のこの層は、量化の位置を変えることで、そのコストさえも取り払います。上のレベルの型 `A` が、小さな型 `X : Type ℓ` からの同値 `e : X ≃ A` を備えているとします。すると `A` の上での量化は、段階的に `X` の上での量化へ置き換えられます。`A` の要素 `a` についての主張は、その原像 `equivFun e m` で読めばよいのです。有界量化子の補題は関連するが別の現象です。あそこでの範囲は集合を提示する添字の型であり、所属がふるいの役を果たしました。ここでは有界性の仮定がまったく残りません。小ささは論理式の形ではなく、それが語られる世界の形によって担われるのです。仮定の向きに注意してください。断言されているのは `X` から `A` への同値 `e` が存在することであり、`A` 自身は依然として上の宇宙に住みます。
<!--/-->

<!--en-->
The universal version first. The statement `⋀ A B` quantifies over all of `A`; the compressed proposition quantifies instead over `X`, asserting that for every `m : X` the compressed proposition `sm (equivFun e m) .fst` holds. Since `e` is an equivalence, quantifying over `X` or over `A` gives equivalent dependent function types. The equivalence component transports a family of proofs `f : ∀ m → ⟨ sm (e m) ⟩` to `∀ a → ⟨ B a ⟩` by `equivΠ`, composed with each pointwise equivalence, and `invEquiv` orients the composite from the small Π to the large one, as the goal type demands. Note the contrast with `small-∀∈`: there the antecedent `x ∈ˢ a` did the filtering; here no antecedent exists, and the equivalence alone carries the reduction.
<!--zh-->
先看全称版本。陈述 `⋀ A B` 对整个 `A` 量化；压缩命题改为对 `X` 量化，断言对每个 `m : X`，压缩命题 `sm (equivFun e m) .fst` 成立。由于 `e` 是等价，在 `X` 上量化与在 `A` 上量化给出等价的依值函数类型。等价分量把一族证明 `f : ∀ m → ⟨ sm (e m) ⟩` 传输为 `∀ a → ⟨ B a ⟩`，逐点再与各等价复合，`invEquiv` 按目标类型的要求把复合定向为从小 Π 到大 Π。注意与 `small-∀∈` 的对照：那里的前件 `x ∈ˢ a` 起了过滤作用；这里没有前件，仅凭等价完成化归。
<!--ja-->
まず全称の方です。主張 `⋀ A B` は `A` 全体の上で量化しますが、圧縮された命題は代わりに `X` の上で量化し、すべての `m : X` に対して圧縮された命題 `sm (equivFun e m) .fst` が成り立つと述べます。`e` が同値なので、`X` 上の量化と `A` 上の量化は同値な依存関数型を与えます。同値の成分は証明の族 `f : ∀ m → ⟨ sm (e m) ⟩` を `∀ a → ⟨ B a ⟩` へ運び、各点でさらに同値と合成し、`invEquiv` が目標の型の求めどおり、小さな Π から大きな Π へと向きを定めます。`small-∀∈` との対比に注意してください。あちらでは前件 `x ∈ˢ a` がふるいの役を果たしましたが、こちらには前件がなく、同値だけが化約の役を担います。
<!--/-->

```agda
small-⋀ : {A : Type (ℓ-suc ℓ)} {X : Type ℓ} (e : X ≃ A) {B : A → hProp (ℓ-suc ℓ)}
        → (∀ a → isSmall (B a))
        → isSmall (⋀ A B)
small-⋀ e sm = Logic.∀[]-syntax (λ m → sm (equivFun e m) .fst)
  , invEquiv (equivΠ e (λ m → invEquiv (sm (equivFun e m) .snd)))
```

<!--en-->
The existential version follows the same plan with truncations in place of function types. The compressed proposition is the truncated Σ over `X` of the small witnesses; the equivalence is obtained from the truncated Σ over `A` of the large witnesses by `Σ-cong-equiv`, which changes the base of the pair from `A` to `X` along `e` and each fiber along the inverse pointwise equivalence, and `PT.propTrunc≃` then lifts the pair equivalence to the truncations. Again `invEquiv` supplies the required orientation. Together the two lemmas say: quantification over any essentially small type preserves smallness, and essentially small means, in the next block, equivalent to a type at level `ℓ`.
<!--zh-->
存在版本沿用同一方案，只是以截断替换函数类型。压缩命题是对 `X` 的小性见证的截断 Σ；等价从对 `A` 的大见证的截断 Σ 出发：`Σ-cong-equiv` 沿 `e` 把对子的基底从 `A` 换成 `X`，各纤维沿逆的逐点等价变换，`PT.propTrunc≃` 再把对子等价提升到截断上。`invEquiv` 同样提供所需朝向。两条引理合起来说：对任何本质小类型的量化保持小性；而「本质小」在下一块代码中将指等价于层级 `ℓ` 的某个类型。
<!--ja-->
存在の方も同じ計画に従いますが、関数型の代わりに切り詰めが現れます。圧縮された命題は、`X` の上の小さな証人の切り詰められた Σ です。同値は、`A` の上の大きな証人の切り詰められた Σ から、`Σ-cong-equiv` によって得られます。これは対の基底を `e` に沿って `A` から `X` へ変え、各ファイバーを逆向きの各点の同値に沿って変え、`PT.propTrunc≃` がさらにその対の同値を切り詰めへ引き上げます。ここでも `invEquiv` が必要な向きを与えます。二つの補題を合わせると、本質的に小さな型の上での量化は小ささを保存する、ということになります。そして次のコード塊で、本質的に小さいとはレベル `ℓ` の型と同値であることを意味します。
<!--/-->

```agda

small-⋁ : {A : Type (ℓ-suc ℓ)} {X : Type ℓ} (e : X ≃ A) {B : A → hProp (ℓ-suc ℓ)}
        → (∀ a → isSmall (B a))
        → isSmall (⋁ A B)
small-⋁ e sm = Logic.∃[]-syntax (λ m → sm (equivFun e m) .fst)
  , invEquiv (PT.propTrunc≃ (Σ-cong-equiv e (λ m → invEquiv (sm (equivFun e m) .snd))))
```

<!--en-->
The consequence: over an essentially small restricted structure, **every** formula evaluates small, no Δ₀ witness required. Fix a class `M` on the structure and suppose its restricted carrier is essentially small, in the precise form of an equivalence `e : X ≃ (Σ[ x ∈ S ] (x ∈ᶜ M))` with `X : Type ℓ`. Inside the structure `𝒮ᵥ ↾ M`, the quantifiers range over that restricted carrier, so the two lemmas of the last block apply to every quantifier, bounded or not, and the atoms reduce to `V`'s atomic smallness through the first projection. Boundedness is a syntactic restriction on a formula, whereas essential smallness is a property of the quantifier range. Once that hypothesis is available, the structural induction covers unbounded as well as bounded quantifiers. This smallness of inner satisfaction is what lets a definability step, such as the one the constructible hierarchy takes at each stage, operate with predicates at the lower universe.
<!--zh-->
后果是：在本质小的限制结构上，**任何**公式求值皆小，无需 Δ₀ 见证。固定结构上的类 `M`，并设其限制载体本质小，精确形式是等价 `e : X ≃ (Σ[ x ∈ S ] (x ∈ᶜ M))`，其中 `X : Type ℓ`。在结构 `𝒮ᵥ ↾ M` 内，量词在该限制载体上量化，于是上一块代码的两条引理对每个量词都适用，无论有界与否；原子则经第一投影归结为 `V` 的原子小性。有界性是公式的句法限制，而本质小是量化范围的性质。有了后一项假设，结构归纳便同时覆盖无界与有界量词。内部满足的这一小性，正是让可定义性步骤 (例如可构造层级在每层所做的那一步) 能以低宇宙的谓词运作的原因。
<!--ja-->
帰結は次のとおりです。本質的に小さな制限された構造の上では、Δ₀ の証人がなくても、**すべての**論理式の評価が小さくなります。構造の上のクラス `M` を固定し、その制限された台が本質的に小さい、すなわち `X : Type ℓ` を用いた同値 `e : X ≃ (Σ[ x ∈ S ] (x ∈ᶜ M))` の形で仮定します。構造 `𝒮ᵥ ↾ M` の中では、量化子はその制限された台の上で量化するので、前のコード塊の二つの補題は、有界かどうかにかかわらず、すべての量化子に適用できます。原子は第一射影を通して `V` の原子的な小ささに帰着します。有界性は論理式に対する構文上の制限であり、本質的な小ささは量化範囲の性質です。後者の仮定があれば、構造帰納法は非有界量化子と有界量化子の両方を扱えます。この内部充足の小ささこそ、可定義性の段階、たとえば構成可能階層が各段階で踏む那段階が、低い宇宙の述語で動けるようにするものです。
<!--/-->

<!--en-->
The module's parameters assemble the small world. `M` is a class on the carrier `S`, possibly proper: nothing restricts its size. The hypothesis is the pair of a small type `X : Type ℓ` and an equivalence from `X` onto the restricted carrier `Σ[ x ∈ S ] (x ∈ᶜ M)`; this is the exact sense in which the world is essentially small, and note that the burden rests on the equivalence existing, not on `M` being in any way bounded internally. The constants are interpreted in the restricted carrier by `ι : K → Σ[ x ∈ S ] (x ∈ᶜ M)`, so every constant denotes a pair whose second component is evidence that its first component lies in `M`.
<!--zh-->
模块的参数装配出这个小世界。`M` 是载体 `S` 上的一个类，可以是真类：没有任何大小限制。假设是一对数据：小类型 `X : Type ℓ`，以及从 `X` 到限制载体 `Σ[ x ∈ S ] (x ∈ᶜ M)` 的等价；这正是「世界本质小」的精确含义。注意负担在于该等价存在，而不在于 `M` 在任何内部意义上有界。常元经 `ι : K → Σ[ x ∈ S ] (x ∈ᶜ M)` 在限制载体中解释，因此每个常元指称一个对子，其第二分量是「第一分量属于 `M`」的证据。
<!--ja-->
モジュールの引数が小さな世界を組み立てます。`M` は台 `S` 上のクラスで、真クラスであってもかまいません。大きさの制限は一切ありません。仮定は、小さな型 `X : Type ℓ` と、`X` から制限された台 `Σ[ x ∈ S ] (x ∈ᶜ M)` への同値との組であり、これが世界が本質的に小さいということの正確な意味です。負担はこの同値が存在することにあり、`M` が何らかの内部的な意味で有界であることにはありません。定数は `ι : K → Σ[ x ∈ S ] (x ∈ᶜ M)` によって制限された台の中で解釈され、したがって各定数は、第二成分が「第一成分が `M` に属する」ことの証拠であるような対を指します。
<!--/-->

```agda
module InnerSmall (M : S → hProp (ℓ-suc ℓ))
                  (X : Type ℓ) (e : X ≃ (Σ[ x ∈ S ] (x ∈ᶜ M)))
                  {ℓc} {K : Type ℓc}
                  (ι : K → Σ[ x ∈ S ] (x ∈ᶜ M)) where

  SM : Type (ℓ-suc ℓ)
```

<!--en-->
Two abbreviations fix notation. `SM` names the restricted carrier itself, and `𝒮M` is the structure restricted to `M`, built by `_↾_`: its carrier is `SM`, its sethood is inherited, and its two relations pull back along the first projection, so equality and membership inside the world are decided by the underlying sets of `V`. The semantics module is instantiated at `𝒮M`, and the satisfaction and term-evaluation notations are renamed with a superscript to mark that formulas are being read **inside** the world. The renaming is exported public, so other chapters can read restricted satisfaction under these names.
<!--zh-->
两个缩写固定记号。`SM` 命名限制载体本身；`𝒮M` 是限制到 `M` 的结构，由 `_↾_` 构造：其载体是 `SM`，集合性被继承，两个关系沿第一投影拉回，因此世界内部的相等与隶属由 `V` 的底层集合决定。语义模块在 `𝒮M` 处实例化，满足与词项求值记号以上标记号改名，标示公式是在世界**内部**读取的。该改名以 public 导出，其他章节可在这些名字下读取限制后的满足关系。
<!--ja-->
二つの略記が記法を固定します。`SM` は制限された台そのものの名前であり、`𝒮M` は `_↾_` によって `M` に制限された構造です。その台は `SM` であり、集合性は受け継がれ、二つの関係は第一射影に沿って引き戻されるので、世界の中の等号と所属は `V` の基礎となる集合で決まります。意味論のモジュールは `𝒮M` で具体化され、充足と項の評価の記法は上付き添え字に改名されて、論理式が世界の**内側**で読まれていることを示します。この改名は public にエクスポートされ、他の章ではこれらの名前で制限された充足を読めます。
<!--/-->

```agda
  SM = Σ[ x ∈ S ] (x ∈ᶜ M)

  𝒮M : ZFStructure (hPropAlgebra (ℓ-suc ℓ))
  𝒮M = 𝒮ᵥ ↾ M

  module SemanticsM = FOL.Semantics (hPropAlgebra (ℓ-suc ℓ)) 𝒮M
  open SemanticsM.At K ι renaming ( _⊨_ to _⊨ᵐ_ ; ⟦_⟧ to ⟦_⟧ᵐ ) public
```

<!--en-->
The theorem's statement is deliberately parallel to `Δ₀-small`: for every formula `φ` of any arity `n` and every environment `δ : SM ^ n` of restricted elements, the truth value `δ ⊨ᵐ φ` is small. There is no inductive witness in sight, because none is needed: the induction here is on the formula itself, and the essential smallness of the carrier replaces the Δ₀ restriction. The two atom cases evaluate the terms inside the world, obtaining restricted elements, and apply the atomic smallness lemmas to their first projections: the world's membership `(fst xm) ∈ˢ (fst ym)` is exactly a proposition of the ambient structure, already known small.
<!--zh-->
定理的陈述刻意与 `Δ₀-small` 平行：对任意元数 `n` 的公式 `φ` 与任意限制元素环境 `δ : SM ^ n`，真值 `δ ⊨ᵐ φ` 是小的。这里看不到任何归纳见证，因为不需要：此处的归纳直接针对公式，载体的本质小性取代了 Δ₀ 限制。两个原子情形在世界内求值词项，得到限制元素，再对其第一投影应用原子小性引理：世界内的隶属 `(fst xm) ∈ˢ (fst ym)` 恰是环境结构的命题，其小性已知。
<!--ja-->
定理の主張は、意図的に `Δ₀-small` と並行しています。任意のアリティ `n` の論理式 `φ` と、制限された要素の任意の環境 `δ : SM ^ n` に対して、真理値 `δ ⊨ᵐ φ` は小さい。ここに帰納的な証人は姿を見せません。必要ないからです。ここの帰納法は論理式そのものに対して行われ、台の本質的な小ささが Δ₀ の制限の代わりをします。原子の二つの場合は、世界の中で項を評価して制限された要素を得て、その第一射影に原子的な小ささの補題を適用します。世界の中の所属 `(fst xm) ∈ˢ (fst ym)` は、周囲の構造の命題そのものであり、その小ささはすでに知られています。
<!--/-->

```agda

  ⊨ᵐ-small : ∀ {n} (φ : Formula K n) (δ : SM ^ n) → isSmall (δ ⊨ᵐ φ)
  ⊨ᵐ-small (t ∈̇ u)  δ = small-∈ (fst (⟦ t ⟧ᵐ δ)) (fst (⟦ u ⟧ᵐ δ))
  ⊨ᵐ-small (t ≐ u)  δ = small-≡ (fst (⟦ t ⟧ᵐ δ)) (fst (⟦ u ⟧ᵐ δ))
  ⊨ᵐ-small (φ ∧̇ ψ)  δ =
    small⊓ {P = δ ⊨ᵐ φ} {Q = δ ⊨ᵐ ψ} (⊨ᵐ-small φ δ) (⊨ᵐ-small ψ δ)
```

<!--en-->
The three binary connectives and falsity pass through exactly as before: the closure lemmas `small⊓`, `small⊔`, `small⇒` and the constant `small⊥` are level-generic in the propositions they consume, so they apply unchanged to truth values read inside the world. This reuse is the point of having isolated them in the earlier section: nothing about those proofs mentioned `V` specifically, only `hProp (ℓ-suc ℓ)`.
<!--zh-->
三个二元联结词与假的处理与之前完全相同：封闭引理 `small⊓`、`small⊔`、`small⇒` 与常量 `small⊥` 对所消费的命题是层级泛型的，因此对在世界内读取的真值原样适用。这正是先前把它们单独隔离的意义：那些证明没有提及 `V` 的任何特殊性，只涉及 `hProp (ℓ-suc ℓ)`。
<!--ja-->
三つの二項結合子と偽は、まったく同じように通ります。閉包補題 `small⊓`、`small⊔`、`small⇒` と定数 `small⊥` は、消費する命題に関してレベルに対して汎用的なので、世界の中で読まれた真理値にもそのまま適用できます。これこそ、先の節でそれらを独立に切り出した意味です。あれらの証明は `V` 固有の何かには触れず、`hProp (ℓ-suc ℓ)` にだけ言及していたのです。
<!--/-->

```agda
  ⊨ᵐ-small (φ ∨̇ ψ)  δ =
    small⊔ {P = δ ⊨ᵐ φ} {Q = δ ⊨ᵐ ψ} (⊨ᵐ-small φ δ) (⊨ᵐ-small ψ δ)
  ⊨ᵐ-small (φ ⇒̇ ψ)  δ =
    small⇒ {P = δ ⊨ᵐ φ} {Q = δ ⊨ᵐ ψ} (⊨ᵐ-small φ δ) (⊨ᵐ-small ψ δ)
  ⊨ᵐ-small ⊥̇        δ = small⊥
```

<!--en-->
Now the quantifiers, where the two world lemmas enter. The unbounded existential `∃̇ φ` has truth value `⋁ SM (λ xm → (xm ∷ δ) ⊨ᵐ φ)` over the restricted carrier, and the induction hypothesis supplies smallness of each fiber `(xm ∷ δ) ⊨ᵐ φ`. This is precisely the shape of `small-⋁`, with `A` the restricted carrier and `e` its smallness equivalence, so the case closes by direct application. The universal case is the mirror image with `small-⋀`. Note how the quantification is genuinely over the restricted world: an element of `SM` is a pair, so the extended environment `xm ∷ δ` extends by whole restricted elements, and the body is read at them.
<!--zh-->
现在轮到量词，两个世界引理在此登场。无界存在量词 `∃̇ φ` 的真值是限制载体上的 `⋁ SM (λ xm → (xm ∷ δ) ⊨ᵐ φ)`，归纳假设给出每个纤维 `(xm ∷ δ) ⊨ᵐ φ` 的小性。这恰是 `small-⋁` 的形状，`A` 取限制载体、`e` 取其小性等价，该情形由直接应用闭合。全称情形是 `small-⋀` 的镜像。注意量化确实是对限制世界进行的：`SM` 的元素是对子，因此扩展环境 `xm ∷ δ` 是以完整的限制元素扩展，体公式在这些元素处读取。
<!--ja-->
次に量化子で、世界の二つの補題が登場します。非有界の存在量化子 `∃̇ φ` の真理値は、制限された台の上の `⋁ SM (λ xm → (xm ∷ δ) ⊨ᵐ φ)` であり、帰納法の仮定が各ファイバー `(xm ∷ δ) ⊨ᵐ φ` の小ささを与えます。これは `small-⋁` の形状そのものであり、`A` に制限された台を、`e` にその小ささの同値を入れれば、この場合は直接の適用で閉じます。全称の場合は `small-⋀` を用いた鏡像です。量化が本当に制限された世界の上で行われていることに注意してください。`SM` の要素は対なので、拡張された環境 `xm ∷ δ` は制限された要素全体による拡張であり、本体はそれらの上で読まれます。
<!--/-->

```agda
  ⊨ᵐ-small (∃̇ φ)    δ =
    small-⋁ e {B = λ xm → (xm ∷ δ) ⊨ᵐ φ} (λ xm → ⊨ᵐ-small φ (xm ∷ δ))
  ⊨ᵐ-small (∀̇ φ)    δ =
    small-⋀ e {B = λ xm → (xm ∷ δ) ⊨ᵐ φ} (λ xm → ⊨ᵐ-small φ (xm ∷ δ))
  ⊨ᵐ-small (∀̇∈ t φ) δ =
```

<!--en-->
The bounded quantifiers combine the two sources of smallness in one case each. For `∀̇∈ t φ`, the truth value is an implication, bounded over the restricted carrier: `⋀ SM (λ xm → (fst xm ∈ˢ ⟦ t ⟧ᵐ δ) ⇒ ((xm ∷ δ) ⊨ᵐ φ))`. Smallness of the antecedent comes from the atomic lemma, smallness of the consequent from the induction hypothesis, and `small⇒` assembles the implication; the whole statement is then small by `small-⋀` along `e`. The interesting detail is the first projection `fst xm`: boundedness is a statement about the underlying set of the restricted element, since the membership relation of the world is the pullback of `V`'s.
<!--zh-->
有界量词在每个情形中把两个小性来源合并。对 `∀̇∈ t φ`，真值是限制载体上有界的蕴涵：`⋀ SM (λ xm → (fst xm ∈ˢ ⟦ t ⟧ᵐ δ) ⇒ ((xm ∷ δ) ⊨ᵐ φ))`。前件的小性来自原子引理，后件的小性来自归纳假设，`small⇒` 组装蕴涵；整个陈述再经 `small-⋀` 沿 `e` 而小。有趣的细节是第一投影 `fst xm`：有界性是关于限制元素底层集合的陈述，因为世界的隶属关系本就是 `V` 的拉回。
<!--ja-->
有界量化子は、それぞれの場合で小ささの二つの源泉を結合します。`∀̇∈ t φ` の真理値は、制限された台の上で有界な含意 `⋀ SM (λ xm → (fst xm ∈ˢ ⟦ t ⟧ᵐ δ) ⇒ ((xm ∷ δ) ⊨ᵐ φ))` です。前件の小ささは原子的な補題から、後件の小ささは帰納法の仮定から得られ、`small⇒` が含意を組み立てます。主張全体は、さらに `e` に沿う `small-⋀` によって小さくなります。興味深い細部は第一射影 `fst xm` です。有界性は、制限された要素の基礎となる集合についての主張です。世界の所属関係は `V` のそれの引き戻しだからです。
<!--/-->

```agda
    small-⋀ e {B = λ xm → (fst xm ∈ˢ fst (⟦ t ⟧ᵐ δ)) ⇒ ((xm ∷ δ) ⊨ᵐ φ)} (λ xm →
      small⇒ {P = fst xm ∈ˢ fst (⟦ t ⟧ᵐ δ)} {Q = (xm ∷ δ) ⊨ᵐ φ}
        (small-∈ (fst xm) (fst (⟦ t ⟧ᵐ δ))) (⊨ᵐ-small φ (xm ∷ δ)))
  ⊨ᵐ-small (∃̇∈ t φ) δ =
    small-⋁ e {B = λ xm → (fst xm ∈ˢ fst (⟦ t ⟧ᵐ δ)) ⊓ ((xm ∷ δ) ⊨ᵐ φ)} (λ xm →
```

<!--en-->
The existential bounded case is the dual composition: the truth value pairs boundedness with the body under a truncated Σ, `small⊓` combines the two smallness witnesses, and `small-⋁` moves the whole statement to the small index type. With this case the induction is complete, and the chapter's second headline result stands: inside an essentially small world, every formula, unbounded quantifiers included, has a small truth value. Where Δ₀-smallness was carried by the shape of the formula, essential smallness is carried by the range of the quantifiers; either way, once a small predicate is in hand, the separation of the previous section applies.
<!--zh-->
存在有界情形是对偶的复合：真值是在截断 Σ 下把有界与体公式配对，`small⊓` 组合两个小性见证，`small-⋁` 把整个陈述搬到小索引类型上。此情形完成归纳，本章的第二项主结果就此成立：在本质小的世界内，包括无界量词在内的每个公式都有小的真值。Δ₀ 小性由公式的形状承载，本质小性由量词的范围承载；无论哪种方式，一旦拿到小谓词，前一节的分离都照常适用。
<!--ja-->
存在の有界量化の場合は双対の合成です。真理値は切り詰められた Σ の下で有界性と本体を対にし、`small⊓` が二つの小ささの証人を組み合わせ、`small-⋁` が主張全体を小さな添字の型の上へ移します。この場合で帰納法は完了し、本章のもう一つの主要な結果が立ちます。本質的に小さな世界の中では、非有界量化子を含むすべての論理式が小さな真理値をもつのです。Δ₀ の小ささは論理式の形が担い、本質的な小ささは量化子の範囲が担います。どちらであっても、小さな述語が手もとにあれば、前節の分出がそのまま適用されます。
<!--/-->

```agda
      small⊓ {P = fst xm ∈ˢ fst (⟦ t ⟧ᵐ δ)} {Q = (xm ∷ δ) ⊨ᵐ φ}
        (small-∈ (fst xm) (fst (⟦ t ⟧ᵐ δ))) (⊨ᵐ-small φ (xm ∷ δ)))
```

<!--en-->
## Recap

Smallness is equivalence to a proposition one universe down (`isSmall`{.Agda}). The atomic membership and equality of `V` compress through the library's monic presentation; the four connectives and two constants pass smallness witnesses through their corresponding lower-level operations; and the bounded quantifiers compress by quantifying over a set's small index type, using the untruncated fibers of the embedding. The adapter `separateFromSmall`{.Agda} converts any pointwise-small predicate into a set with the separation specification. The induction `Δ₀-small`{.Agda} then gives the Δ₀ tier of the Lévy hierarchy outright, and `separateΔ₀`{.Agda} turns it into Δ₀ separation with no propositional resizing, no classical axiom, and no choice. Formulas outside Δ₀ need more, and the model chapter supplies it under the name of propositional resizing. The final section added a second route: over a world whose carrier is essentially small, that is, equivalent to a type at level `ℓ`, every formula evaluates small, which is what lets a definability step work with lower-universe predicates.
<!--zh-->
## 小结

小性即与低一层命题的等价 (`isSmall`{.Agda})。`V` 的原子隶属与相等经库的单射呈现压缩；四个联结词与两个常量经对应的低层运算传递小性见证；有界量词通过在集合的小索引类型上量化而压缩，其间用到嵌入的非截断纤维。适配器 `separateFromSmall`{.Agda} 把任何逐点小的谓词变成带有分离规格的集合。归纳 `Δ₀-small`{.Agda} 直接给出 Lévy 层级的 Δ₀ 档，`separateΔ₀`{.Agda} 把它变成无需命题降层、无需任何经典公理或选择的 Δ₀ 分离。Δ₀ 之外的公式需要更多，模型章以命题降层的名义供给。最后一节引入了第二条路径：在载体本质小，即等价于 `ℓ` 层某类型的世界里，每个公式求值皆小，这正是让可定义性步骤能以低宇宙谓词运作的原因。
<!--ja-->
## まとめ

小ささとは、一段低い宇宙の命題との同値です (`isSmall`{.Agda})。`V` の原子的な所属と等号は、ライブラリの単射表示を通して圧縮されます。四つの結合子と二つの定数は、対応する低いレベルの演算を通して小ささの証人を運び、有界量化子は、集合の小さな添字の型の上での量化によって圧縮されます。その際に使われるのは、埋め込みの切り詰められていないファイバーです。適合装置 `separateFromSmall`{.Agda} は、各点で小さいどんな述語も、分出の仕様を備えた集合へ変えます。帰納法 `Δ₀-small`{.Agda} は Lévy 階層の Δ₀ の階層をそのまま与え、`separateΔ₀`{.Agda} は命題リサイズも古典的な公理も選択も要らない Δ₀ 分出へ変えます。Δ₀ の外の論理式にはさらに多くが要り、モデルの章が命題リサイズという名のもとでそれを供給します。最後の節は第二の道を加えました。台が本質的に小さい、つまりレベル `ℓ` の型と同値である世界の中ではすべての論理式の評価が小さく、これが可定義性の段階を低い宇宙の述語で動かせるようにする理由です。
<!--/-->
