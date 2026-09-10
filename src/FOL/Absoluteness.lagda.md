<!--en-->
# Absoluteness

A formula is absolute when interpreting it in a transitive substructure gives the same truth value as interpreting it in the ambient structure. Here the substructure has carrier `𝒮 ↾ M`, whose elements are pairs consisting of an ambient element and evidence that it belongs to the class `M`; the ambient interpretation uses the same syntax after projecting those pairs with `fst`. Transitivity supplies the key step: if a bound belongs to `M`, then every member of that bound belongs to `M` as well.

The chapter proves by induction that every Δ₀ formula has equal inner and outer truth values. Atomic formulas follow from agreement of term evaluation, connectives preserve the induction hypotheses, and transitivity is needed exactly when a bounded quantifier must turn an ambient member into an element of the substructure. The final results extend this equality to one-way laws: Σ₁ truth passes upward from the substructure, while Π₁ truth passes downward from the ambient structure.
<!--zh-->
# 绝对性

若一条公式在传递子结构中的解释与在外围结构中的解释具有相同真值，就称它是绝对的。这里子结构的载体是 `𝒮 ↾ M`，其元素由一个外围元素及其属于类 `M` 的证据组成；外围解释则在用 `fst` 投影这些序对后使用同一套语法。传递性提供关键一步：若某个界属于 `M`，那么该界的每个成员也属于 `M`。

本章通过归纳证明每条 Δ₀ 公式的内外真值相等。原子公式归结为词项求值的一致，联结词保持归纳假设，而有界量词必须把外围成员变成子结构元素时才需要传递性。最后再把这一等式推广为两个单向规律：Σ₁ 真值从子结构向上传递到外围结构，Π₁ 真值则从外围结构向下传递到子结构。
<!--ja-->
# 絶対性

推移的部分構造で論理式を解釈した真理値が、周囲の構造で解釈した真理値と等しいとき、その論理式は絶対的です。ここで部分構造の台 `𝒮 ↾ M` の元は、周囲の元と、それがクラス `M` に属する証拠との対です。周囲での解釈には、それらの対を `fst` で射影したうえで同じ構文を使います。推移性が与える要点は、ある範囲が `M` に属すれば、その範囲の各要素も `M` に属するということです。

本章では、すべての Δ₀ 論理式について内側と外側の真理値が等しいことを帰納法で証明します。原子論理式は項の評価の一致に帰着し、結合子は帰納法の仮定を保ちます。推移性が必要になるのは、有界量化子が周囲の元を部分構造の元に直す箇所だけです。最後にこの等式を一方向の法則へ拡張し、Σ₁ の真理は部分構造から周囲の構造へ上向きに、Π₁ の真理は周囲の構造から部分構造へ下向きに保存されることを示します。
<!--/-->

<!--en-->
Structures here are proposition-valued: a `ZFStructure`{.Agda} over the truth algebra `hPropAlgebra ℓ` has a carrier with equality and membership valued in `hProp ℓ`, so a satisfaction statement is a proposition with an underlying type, and two satisfaction statements can be compared by path equality. Two further notions carry the mathematics. `Transitive`{.Agda} is the closure condition `y ∈ᵗ x → x ∈ᶜ M → y ∈ᶜ M`: a member of an element of `M` is again in `M`. And `_↾_`{.Agda} restricts a structure to a class, taking as its new carrier the pairs of an element with evidence that it lies in the class; what changes is what counts as an element, while the relations are inherited along the first projection.
<!--zh-->
这里的结构是命题值的：真值代数 `hPropAlgebra ℓ` 上的 `ZFStructure`{.Agda} 带有一个载体，其等词与成员关系都取值于 `hProp ℓ`，因此一条满足陈述是带有底层类型的命题，两条满足陈述可以用路径相等来比较。另有两个概念承载数学内容。其一是 `Transitive`{.Agda}，即闭合条件 `y ∈ᵗ x → x ∈ᶜ M → y ∈ᶜ M`：`M` 中元素的成员仍属于 `M`。其二是 `_↾_`{.Agda}，它把结构限制到一个类，新载体由「元素配上其属于该类的证据」的对组成；改变的是什么算作元素，而各关系沿第一投影继承。
<!--ja-->
ここでの構造は命題値です。真理値代数 `hPropAlgebra ℓ` 上の `ZFStructure`{.Agda} は台をひとつ持ち、その等号と所属は `hProp ℓ` に値を取るので、充足の主張は基礎型をもつ命題になり、二つの充足の主張はパスとしての等しさで比較できます。数学的内容を担う概念がさらに二つあります。第一は `Transitive`{.Agda} で、閉性の条件 `y ∈ᵗ x → x ∈ᶜ M → y ∈ᶜ M`、すなわち `M` の要素の要素も `M` に属することを述べます。第二は `_↾_`{.Agda} で、構造をクラスへ制限し、「要素と、それがクラスに属する証拠」の対を新しい台とします。変わるのは何を要素とみなすかだけで、関係は第一射影に沿って引き継がれます。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

module FOL.Absoluteness where

open import Base.Prelude
open import Base.Truth
open import FOL.ZFStructure using ( ZFStructure; Transitive; _↾_ )
```

<!--en-->
On the syntactic side, formulas have constants `con` and variables `var` and the two bounded quantifiers `∀̇∈` and `∃̇∈`, whose range is the members of a term's value. The Lévy hierarchy enters through its inductive characterizations: `Δ₀`{.Agda} is the inductive class of formulas built from atomic membership and equality by the propositional connectives and the bounded quantifiers, with constructors named `δ-`. `Σ₁`{.Agda} and `Π₁`{.Agda} are built on top: either a Δ₀ formula, or an unbounded existential (respectively universal) whose matrix is again Σ₁ (respectively Π₁), witnessed by `σ-∃`{.Agda} and `π-∀`{.Agda}. These witnesses are exactly the induction data the absoluteness proof will consume.
<!--zh-->
句法方面，公式有常元 `con`、变量 `var`，以及两个有界量词 `∀̇∈` 与 `∃̇∈`，其范围是某词项取值的成员。Lévy 层谱以归纳刻画的方式进入：`Δ₀`{.Agda} 是由原子成员关系与等词出发、经命题联结词与有界量词生成的公式的归纳类，构造子名为 `δ-`。`Σ₁`{.Agda} 与 `Π₁`{.Agda} 建立其上：要么是一条 Δ₀ 公式，要么是一个无界存在 (相应地全称) 量词、其母式仍为 Σ₁ (相应地 Π₁)，由 `σ-∃`{.Agda} 与 `π-∀`{.Agda} 见证。这些见证正是绝对性证明将要消耗的归纳数据。
<!--ja-->
構文の側では、論理式には定数 `con` と変数 `var`、そして項の値の要素を範囲とする二つの有界量化子 `∀̇∈` と `∃̇∈` が現れます。Lévy 階層は帰納的特徴づけを通して登場します。`Δ₀`{.Agda} は、原始的な所属と等号から出発し、命題結合子と有界量化子で作られる論理式の帰納的な類であり、その構成子には `δ-` 系の名前が付いています。`Σ₁`{.Agda} と `Π₁`{.Agda} はその上に築かれます。Δ₀ 論理式であるか、無制限の存在 (それぞれ全称) 量化子を持ち母式が再び Σ₁ (それぞれ Π₁) であるかで、`σ-∃`{.Agda} と `π-∀`{.Agda} が証拠となります。これらの証拠こそ、絶対性の証明が消費する帰納のデータです。
<!--/-->

```agda
open import FOL.Syntax using ( Term; con; var; Formula; ∀̇∈; ∃̇∈ )
open import FOL.LevyHierarchy using
  ( Δ₀; δ-∈; δ-≐; δ-∧; δ-∨; δ-⇒; δ-⊥; δ-∀∈; δ-∃∈
  ; Σ₁; σ-Δ₀; σ-∃; Π₁; π-Δ₀; π-∀ )
import FOL.Semantics
```

<!--en-->
The semantics is generic, so the chapter will use it twice over the same syntax, once for each world. Three pieces of notation serve the proofs to come: `map`{.Agda} applies the first projection to a whole environment, `⇔toPath`{.Agda} turns two implications into a path of truth values, and the truncation machinery appears as `PT`{.Agda} because satisfaction of an unbounded existential is a merely-inhabited type, so transferring witnesses between the two worlds happens under truncation.
<!--zh-->
语义是泛型的，因此本章将在同一套语法上使用它两次，每个世界一次。三个记号服务于后续证明：`map`{.Agda} 把第一投影作用到整个环境，`⇔toPath`{.Agda} 把两个蕴涵合成真值的路径，而截断工具以 `PT`{.Agda} 出现：无界存在量词的满足是仅要求存在的类型，因此见证在两个世界之间的转移发生在截断之下。
<!--ja-->
意味論は汎用的なので、本章では同じ構文の上で世界ごとに二回使うことになります。これからの証明のために三つの記法があります。`map`{.Agda} は環境全体に第一射影を適用し、`⇔toPath`{.Agda} は二つの含意を真理値のパスに合成します。切断の機構が `PT`{.Agda} として現れるのは、無制限の存在量化子の充足が単に inhabited な型だからです。したがって証拠の二世界間の移動は切断の下で行われます。
<!--/-->

```agda
open import Cubical.Data.Vec using ( map )
open import Cubical.Functions.Logic using ( ⇔toPath )
import Cubical.HITs.PropositionalTruncation as PT
```

<!--en-->
## The setting: one syntax, two semantics

Fix an ambient structure `𝒮` and a transitive class `M`; the inner world is the restriction `𝒮 ↾ M`, whose carrier `SM` consists of the members of `M`. The syntax takes `K := SM`: a constant in a formula must be a member of `M`, so the parameter discipline is enforced by the type. The same formula family then receives **two semantics**: evaluated outside, in `𝒮`, with constants interpreted through `fst`{.Agda}; and evaluated inside, in `𝒮 ↾ M`, with constants standing for themselves. Relativization is thus not a syntactic operation but two readings of one generic semantics; the superscripts `ᵛ` and `ᵐ` on the satisfaction symbols read "evaluated where".
<!--zh-->
## 设置：一套语法，两套语义

固定环境结构 `𝒮` 与传递类 `M`；内层世界是限制结构 `𝒮 ↾ M`，其载体 `SM` 由 `M` 的成员组成。语法取 `K := SM`：公式中的常元必须是 `M` 的成员，参数须满足的规则由类型强制保证。同一族公式于是得到**两套语义**：在外层 `𝒮` 中求值，常元经 `fst`{.Agda} 解释；在内层 `𝒮 ↾ M` 中求值，常元即其自身。相对化因此不是句法操作，而是同一泛型语义的两种读法；满足符号上的上标 `ᵛ` 与 `ᵐ` 读作「在哪里求值」。
<!--ja-->
## 設定：一つの構文と二つの意味論

周囲の構造 `𝒮` と推移的クラス `M` を固定します。内側の世界は制限 `𝒮 ↾ M` であり、その台 `SM` は `M` の要素からなります。構文は `K := SM` を取ります。論理式に現れる定数は `M` の要素でなければならず、パラメータについての規律が型で強制されます。同じ論理式の族はこうして**二つの意味論**を受け取ります。外側では `𝒮` の中で、定数を `fst`{.Agda} で解釈して評価し、内側では `𝒮 ↾ M` の中で、定数がそれ自身を表すものとして評価します。相対化は構文操作ではなく、一つの汎用的な意味論の二つの読み方なのです。充足を表す記号の上付き `ᵛ` と `ᵐ` は「どこで評価したか」を読み取る目印です。
<!--/-->

<!--en-->
The section works under three fixed parameters: a structure `𝒮`, a class `M` valued in `hProp ℓ` on its carrier, and a proof `trans` of transitivity. The carrier `S` and the truth-valued relations `_∈ˢ_`, `_≈ˢ_` belong to `𝒮`; the truth-algebra operations `⊓`, `⊔`, `⇒` interpret the connectives. Nothing about `M` is used yet except that it is a class; transitivity enters the proof of the theorem, not the definitions that state it.
<!--zh-->
本节在三个固定参数下工作：结构 `𝒮`、其载体上取值于 `hProp ℓ` 的类 `M`、以及传递性的证明 `trans`。载体 `S` 与真值关系 `_∈ˢ_`、`_≈ˢ_` 属于 `𝒮`；真值代数运算 `⊓`、`⊔`、`⇒` 解释各联结词。目前只用到 `M` 是一个类这一事实；传递性进入的是定理的证明，而不是陈述定理的定义。
<!--ja-->
この節は三つの固定パラメータのもとで進みます。構造 `𝒮`、その台上で `hProp ℓ` に値を取るクラス `M`、そして推移性の証明 `trans` です。台 `S` と真理値の関係 `_∈ˢ_`、`_≈ˢ_` は `𝒮` に属し、真理値代数の演算 `⊓`、`⊔`、`⇒` が結合子を解釈します。現時点で `M` について使うのはそれがクラスであることだけです。推移性が現れるのは定理の証明であり、それを述べる定義ではありません。
<!--/-->

```agda
module Single {ℓ} (𝒮 : ZFStructure (hPropAlgebra ℓ))
              (M : ZFStructure.S 𝒮 → hProp ℓ)
              (trans : Transitive 𝒮 M) where

  open TruthAlgebra (hPropAlgebra ℓ)
  open ZFStructure 𝒮
```

<!--en-->
The carrier of the inner world is the Σ-type `SM`: a pair of an element of `S` with evidence that it lies in `M`. Since `𝒮 ↾ M` interprets its relations on first projections, an inner element and its `fst`{.Agda} image name the same inhabitant of `S` as far as `𝒮` is concerned. The generic semantics is then used twice over this carrier: once evaluating in the outer structure `𝒮`, once in the restriction `𝒮M`. The two readings share the syntax because both take constant domain `SM`; they differ only in the structure and in the constant interpretation.
<!--zh-->
内层世界的载体是 Σ 类型 `SM`：`S` 的一个元素配上它属于 `M` 的证据。由于 `𝒮 ↾ M` 的关系都在第一投影上解释，就 `𝒮` 而言，内层元素与其 `fst`{.Agda} 像指称 `S` 中同一个 inhabitant。泛型语义于是在这个载体上使用两次：一次在外层结构 `𝒮` 中求值，一次在限制结构 `𝒮M` 中求值。两种读法共享语法，因为常元域都取 `SM`；差别只在结构与常元解释。
<!--ja-->
内側の世界の台は Σ 型 `SM` です。`S` の要素に、それが `M` に属する証拠を対にしたものです。`𝒮 ↾ M` の関係は第一射影の上で解釈されるので、`𝒮` の目には、内側の要素とその `fst`{.Agda} による像は `S` の同じ inhabitant を指します。汎用の意味論はこの台の上で二回使われます。一度は外側の構造 `𝒮` で評価し、一度は制限 `𝒮M` で評価します。両者の読み方が構文を共有するのは、定数域をともに `SM` とするからで、違いは構造と定数解釈にだけあります。
<!--/-->

```agda

  SM : Type ℓ
  SM = Σ[ x ∈ S ] (x ∈ᶜ M)

  𝒮M : ZFStructure (hPropAlgebra ℓ)
  𝒮M = 𝒮 ↾ M

  module SemV = FOL.Semantics (hPropAlgebra ℓ) 𝒮
```

<!--en-->
The outer reading uses the constant interpretation `ι := fst`{.Agda}: a constant naming a member of `M` denotes that member itself in `𝒮`. The fixed notation is `_⊨ᵛ_` for satisfaction in `𝒮` and `⟦_⟧ᵛ` for term values, and the environment notation `_^_` is available throughout.
<!--zh-->
外层读法采用常元解释 `ι := fst`{.Agda}：命名某个 `M` 成员的常元在 `𝒮` 中就指那个成员本身。固定记号为：`𝒮` 中的满足写作 `_⊨ᵛ_`，词项取值写作 `⟦_⟧ᵛ`；环境记号 `_^_` 在全章可用。
<!--ja-->
外側の読み方は定数解釈 `ι := fst`{.Agda} を用います。`M` の要素を名指す定数は、`𝒮` の中ではその要素そのものを指します。記号は固定されます。`𝒮` での充足は `_⊨ᵛ_`、項の値は `⟦_⟧ᵛ` と書き、環境の記法 `_^_` は章全体で使えます。
<!--/-->

```agda
  module SemM = FOL.Semantics (hPropAlgebra ℓ) 𝒮M

  open SemV using ( _^_ ) public

  open module V = SemV.At SM fst public
    renaming ( _⊨_ to _⊨ᵛ_ ; ⟦_⟧ to ⟦_⟧ᵛ )
  open module Mse = SemM.At SM id public
```

<!--en-->
The inner reading uses `ι := id`{.Agda}: inside `𝒮 ↾ M`, a constant is the pair it names, and the relations of the restriction read off that pair's first projection. Hence an inner atomic statement `xm ∈ˢ ym` means exactly `fst xm ∈ˢ fst ym` in `𝒮`, which is why the two satisfaction relations can be compared at all. The notation is `_⊨ᵐ_` and `⟦_⟧ᵐ`, so each formula can be read both as `δ ⊨ᵐ φ` (inside) and as `(map fst δ) ⊨ᵛ φ` (outside).
<!--zh-->
内层读法采用 `ι := id`{.Agda}：在 `𝒮 ↾ M` 中，常元就是它所命名的对，而限制结构的关系读出该对的第一投影。于是内层的原子命题 `xm ∈ˢ ym` 恰好意味着 `𝒮` 中的 `fst xm ∈ˢ fst ym`，这正是两条满足关系能够比较的原因。记号为 `_⊨ᵐ_` 与 `⟦_⟧ᵐ`，因此每条公式既可读作内层的 `δ ⊨ᵐ φ`，也可读作外层的 `(map fst δ) ⊨ᵛ φ`。
<!--ja-->
内側の読み方は `ι := id`{.Agda} を用います。`𝒮 ↾ M` の中では定数はそれが名指す対そのものであり、制限の関係はその対の第一射影を読み取ります。したがって、内側の原子的な主張 `xm ∈ˢ ym` は、`𝒮` ではちょうど `fst xm ∈ˢ fst ym` を意味します。これが二つの充足関係を比較できる理由です。記号は `_⊨ᵐ_` と `⟦_⟧ᵐ` となり、各論理式は内側の `δ ⊨ᵐ φ` としても外側の `(map fst δ) ⊨ᵛ φ` としても読めます。
<!--/-->

```agda
    renaming ( _⊨_ to _⊨ᵐ_ ; ⟦_⟧ to ⟦_⟧ᵐ )
```

<!--en-->
The two worlds differ only in how environments are read: an inner environment `δ : SM ^ n` names outer values through `fst`{.Agda}, so `map fst δ` is the corresponding outer environment. Two lemmas connect the term evaluation on the two sides. A constant evaluates to its own first projection on both sides, and a variable is a lookup in both worlds, so the dictionary is settled at the atoms.
<!--zh-->
两个世界的差别只在环境的读法：内层环境 `δ : SM ^ n` 经 `fst`{.Agda} 给出外层的取值，`map fst δ` 就是相应的外层环境。两条引理连接两侧的词项求值。常元在两侧都取自己的第一投影为值，变量在两个世界都只是一次查表，因此词典问题在原子层面就已解决。
<!--ja-->
二つの世界の違いは環境の読み方にだけあります。内側の環境 `δ : SM ^ n` は `fst`{.Agda} を通して外側の値を名指すので、`map fst δ` が対応する外側の環境です。二つの補題が両側の項の評価を結びます。定数はどちらの側でも自分の第一射影を値とし、変数はどちらの世界でも一回の参照にすぎません。したがって辞書の問題は原子の段階で解決されます。
<!--/-->

<!--en-->
The first lemma commutes lookup with projection, pointwise along the vector: reading the `i`-th entry of the projected environment is the same as projecting the `i`-th entry. The proof is a case split on the index, `refl` at the head and recursion down the tail, since both `lookup` and `map` compute entry by entry.
<!--zh-->
第一条引理使查表与投影逐项交换：读取投影后环境的第 `i` 项，等于投影第 `i` 项。证明对下标分情形：表头处是 `refl`，尾部递归，因为 `lookup` 与 `map` 都是逐项计算的。
<!--ja-->
最初の補題は、参照と射影を項ごとに交換します。射影後の環境の第 `i` 項を読むことは、第 `i` 項を射影することと同じです。証明は添字で場合分けし、先頭では `refl`、尾では再帰します。`lookup` と `map` がどちらも項ごとに計算されるからです。
<!--/-->

```agda
  private
    lookup-fst : ∀ {n} (i : Fin n) (δ : SM ^ n)
               → lookup i (map fst δ) ≡ fst (lookup i δ)
    lookup-fst zero    (m ∷ δ) = refl
    lookup-fst (suc i) (m ∷ δ) = lookup-fst i δ
```

<!--en-->
The second lemma lifts this to terms: evaluating a term in the inner world and projecting gives its outer value under the projected environment. For a constant, both sides compute to `fst m` by the respective interpretations `id` and `fst`, so `refl` suffices. For a variable, the outer value is a lookup into `map fst δ`, which the first lemma rewrites into the projection of the inner lookup; `sym` places the equation in the required direction. Any term is built from these two cases, so the dictionary is complete.
<!--zh-->
第二条引理把这一点提升到词项：在内层求值再投影，等于在投影后的环境中求值。常元情形，两侧按各自的解释 `id` 与 `fst` 都计算到 `fst m`，`refl` 即可。变量情形，外层值是对 `map fst δ` 的查表，第一条引理把它改写为内层查表的投影；`sym` 把等式摆到所需方向。任何词项都由这两种情形生成，词典于是完备。
<!--ja-->
二つ目の補題はこれを項へ持ち上げます。内側で項を評価してから射影したものは、射影後の環境での外側の値に等しい。定数の場合は、それぞれの解釈 `id` と `fst` により両辺とも `fst m` に計算され、`refl` で足ります。変数の場合は、外側の値が `map fst δ` への参照であり、最初の補題がそれを内側の参照の射影へ書き換えます。`sym` は等式を必要な向きに置くためのものです。すべての項はこの二つの場合から作られるので、辞書はこれで完結です。
<!--/-->

```agda

    ⟦⟧-fst : ∀ {n} (t : Term SM n) (δ : SM ^ n)
           → fst (⟦ t ⟧ᵐ δ) ≡ ⟦ t ⟧ᵛ (map fst δ)
    ⟦⟧-fst (con m) δ = refl
    ⟦⟧-fst (var i) δ = sym (lookup-fst i δ)
```

<!--en-->
## The theorem

Absoluteness for Δ₀ is proved by structural induction on the Δ₀ witness. The atomic and connective cases are bookkeeping: atoms go through the term lemmas of the previous section, and each connective computes the whole truth value from the parts, so equality of the parts transports to equality of the whole. The bounded universal is the case where the mathematics happens. Outward, an outer member `x` of the bound must be repackaged for the inner semantics as a member of `M`; since the bound's value lies in `M`, `x ∈ ⟦ t ⟧` together with `⟦ t ⟧ ∈ᶜ M` yields exactly `x ∈ᶜ M` by transitivity. The reverse direction needs only the projection. The bounded existential is the dual argument, carried out under propositional truncation. Transitivity is used when the proof must turn a bare outer element into an inner element: in the inner-to-outer direction for the bounded universal, and in the outer-to-inner direction for the bounded existential.
<!--zh-->
## 定理

Δ₀ 的绝对性由对 Δ₀ 见证的结构归纳证明。原子与联结词情形只是记账：原子情形使用前节的词项引理，每个联结词由部分的真值算出整体的真值，因此部分相等会传递到整体相等。有界全称才是数学发生的地方。向外时，界的外层成员 `x` 必须重新包装成 `M` 的成员交给内层语义；由于界的取值属于 `M`，`x ∈ ⟦ t ⟧` 配上 `⟦ t ⟧ ∈ᶜ M` 经传递性正好给出 `x ∈ᶜ M`。反向只需投影。有界存在是对偶论证，在命题截断之下进行。当证明必须把裸的外层元素变成内层元素时才使用传递性：对有界全称是从内到外的方向，对有界存在则是从外到内的方向。
<!--ja-->
## Δ₀ 絶対性定理

Δ₀ の絶対性は、Δ₀ の証拠についての構造的帰納法で証明します。原子と結合子の場合は帳簿づけにすぎません。原子の場合は前節の項の補題を使い、各結合子は部分の真理値から全体の真理値を計算するので、部分の等しさが全体の等しさに伝わります。数学が起きるのは有界全称の場合です。外向きには、界の外側の要素 `x` を `M` の要素として内側の意味論に引き渡すための束ね直しが必要です。界の値が `M` に属するので、`x ∈ ⟦ t ⟧` と `⟦ t ⟧ ∈ᶜ M` から推移性によってちょうど `x ∈ᶜ M` が得られます。逆向きは射影だけで済みます。有界存在はその双対で、命題の切断のもとで行われます。推移性が使われるのは、外側の裸の要素を内側の要素に直す必要があるときです。有界全称では内側から外側への方向、有界存在では外側から内側への方向に当たります。
<!--/-->

<!--en-->
The statement is a path of truth values, not a mere implication: for every Δ₀ witness `d` certifying `φ` and every environment `δ` into `SM`, inner satisfaction `δ ⊨ᵐ φ` is equal, as a type, to outer satisfaction under the projected environment. In the atomic cases the term lemma evaluates both sides: `∈` reads the structure field `_∈ˢ_`, `≐` reads `_≈ˢ_`, and `cong₂` moves the equality of the two term values through the relation. On the connectives `∧`, `∨` and `⇒` the semantics is by `⊓`, `⊔` and `⇒`, so `abs₀` on the two subwitnesses, fed to `cong₂`, is the whole case: the algebra operations are functions, hence preserve equality.
<!--zh-->
定理陈述的是真值的路径，而不仅是蕴涵：对每条证明 `φ` 是 Δ₀ 的见证 `d` 及指向 `SM` 的每个环境 `δ`，内层满足 `δ ⊨ᵐ φ` 作为类型等于投影后环境下的外层满足。原子情形中，词项引理对两侧求值：`∈` 读结构字段 `_∈ˢ_`，`≐` 读 `_≈ˢ_`，`cong₂` 把两个词项值的相等沿关系搬运。联结词 `∧`、`∨`、`⇒` 的语义分别是 `⊓`、`⊔`、`⇒`，因此把 `abs₀` 作用于两个子见证、再交给 `cong₂`，即是整个情形：代数运算是函数，因而保持相等。
<!--ja-->
定理の主張は、単なる含意ではなく真理値のパスです。`φ` が Δ₀ であることを証明する証拠 `d` と `SM` への環境 `δ` のそれぞれに対して、内側の充足 `δ ⊨ᵐ φ` は、型として、射影後の環境での外側の充足と等しくなります。原子の場合、項の補題が両辺を評価します。`∈` は構造のフィールド `_∈ˢ_` を読み、`≐` は `_≈ˢ_` を読み、`cong₂` が二つの項の値の等しさを関係に沿って運びます。結合子 `∧`、`∨`、`⇒` の意味論は `⊓`、`⊔`、`⇒` なので、二つの部分証拠に `abs₀` を適用して `cong₂` に渡すことが場合全体になります。代数の演算は関数であり、等しさを保つからです。
<!--/-->

```agda
  abs₀ : ∀ {n} {φ : Formula SM n} → Δ₀ φ → (δ : SM ^ n)
       → (δ ⊨ᵐ φ) ≡ ((map fst δ) ⊨ᵛ φ)
  abs₀ (δ-∈ {t = t} {u}) δ = cong₂ _∈ˢ_ (⟦⟧-fst t δ) (⟦⟧-fst u δ)
  abs₀ (δ-≐ {t = t} {u}) δ = cong₂ _≈ˢ_ (⟦⟧-fst t δ) (⟦⟧-fst u δ)
  abs₀ (δ-∧ d e) δ = cong₂ _⊓_ (abs₀ d δ) (abs₀ e δ)
```

<!--en-->
Absurdity needs no work: `δ-⊥` gives `⊥` on both sides, so the required path is `refl`. What remains are the two bounded quantifiers, where the ranges `⟦ t ⟧` live in the outer world but the inner quantification runs over pairs of a value with its membership evidence in `M`. The next blocks unpack one direction at a time.
<!--zh-->
荒谬无需工作：`δ-⊥` 两侧都是 `⊥`，所需路径即 `refl`。剩下的是两个有界量词：其范围 `⟦ t ⟧` 生活在外层世界，而内层量化遍历的是「值配上其属于 `M` 的证据」的对。下面的分块逐个方向展开。
<!--ja-->
矛盾には仕事がありません。`δ-⊥` では両辺とも `⊥` であり、必要なパスは `refl` です。残るのは二つの有界量化子です。その範囲 `⟦ t ⟧` は外側の世界に住み、一方、内側の量化は「値と、その `M` への所属の証拠」の対を走査します。次のブロックで一方向ずつ展開します。
<!--/-->

```agda
  abs₀ (δ-∨ d e) δ = cong₂ _⊔_ (abs₀ d δ) (abs₀ e δ)
  abs₀ (δ-⇒ d e) δ = cong₂ _⇒_ (abs₀ d δ) (abs₀ e δ)
  abs₀ δ-⊥ δ = refl
  abs₀ (δ-∀∈ {t = t} {φ = φ} d) δ = ⇔toPath fwd bwd
    where
```

<!--en-->
For `∀̇∈`, both directions are packaged by `⇔toPath` into one path. Two abbreviations are set up first: `tm` is the inner value of the bounding term, and `p` is the term lemma `fst tm ≡ ⟦ t ⟧ᵛ (map fst δ)` specialized to it, the bridge between the inner range (a pair) and the outer range (its first projection).
<!--zh-->
对 `∀̇∈`，两个方向由 `⇔toPath` 打包成一条路径。先做两个缩写：`tm` 是界定词项的内层取值，`p` 是词项引理 `fst tm ≡ ⟦ t ⟧ᵛ (map fst δ)` 在其上的特化，即内层范围 (一个对) 与外层范围 (其第一投影) 之间的桥。
<!--ja-->
`∀̇∈` では、両方向が `⇔toPath` によって一つのパスにまとめられます。まず二つの略記を用意します。`tm` は範囲を定める項の内側での値で、`p` は項の補題 `fst tm ≡ ⟦ t ⟧ᵛ (map fst δ)` をそれに特化したものであり、内側の範囲 (対) と外側の範囲 (その第一射影) を結ぶ橋です。
<!--/-->

```agda
    tm : SM
    tm = ⟦ t ⟧ᵐ δ
    p : fst tm ≡ ⟦ t ⟧ᵛ (map fst δ)
    p = ⟦⟧-fst t δ
    fwd : ⟨ δ ⊨ᵐ (∀̇∈ t φ) ⟩ → ⟨ (map fst δ) ⊨ᵛ (∀̇∈ t φ) ⟩
```

<!--en-->
The forward direction takes an inner verifier `h` and must supply, for each outer `x` with `x ∈ˢ ⟦ t ⟧ᵛ (map fst δ)`, the body's outer truth. Here `x` is a bare element, not a member of `M`, so it must first be repackaged. The transport along `sym p` moves the membership evidence to the inner range `fst tm`, and then transitivity applies: `x ∈ fst tm` together with `fst tm ∈ᶜ M` gives `x ∈ᶜ M`, so `xm := x , trans hx' (snd tm)` is a legitimate inner element. Running `h` at `xm` gives the inner truth of the body, and the induction hypothesis `abs₀ d (xm ∷ δ)` transports it outward. This is the only step of the whole induction that consumes the hypothesis `trans`.
<!--zh-->
正向取内层的验证者 `h`，须对每个满足 `x ∈ˢ ⟦ t ⟧ᵛ (map fst δ)` 的外层 `x` 给出母式的外层真值。这里的 `x` 只是裸元素而非 `M` 的成员，必须先重新包装。沿 `sym p` 的传输把成员证据搬到内层范围 `fst tm`，随后传递性生效：`x ∈ fst tm` 配上 `fst tm ∈ᶜ M` 得到 `x ∈ᶜ M`，于是 `xm := x , trans hx' (snd tm)` 是合法的内层元素。在 `xm` 处运行 `h` 得到母式的内层真值，归纳假设 `abs₀ d (xm ∷ δ)` 再把它运到外层。整条归纳中唯有这一步使用前提 `trans`。
<!--ja-->
順方向は内側の検証者 `h` を受け取り、`x ∈ˢ ⟦ t ⟧ᵛ (map fst δ)` を満たす各外側の `x` に対して母式の外側の真理値を与えなければなりません。ここで `x` は `M` の要素ではなく素の要素なので、まず束ね直しが必要です。`sym p` に沿った輸送が所属の証拠を内側の範囲 `fst tm` へ移し、次いで推移性が働きます。`x ∈ fst tm` と `fst tm ∈ᶜ M` から `x ∈ᶜ M` が得られ、したがって `xm := x , trans hx' (snd tm)` は正当な内側の要素です。`xm` で `h` を実行すると母式の内側の真理値が得られ、帰納仮定 `abs₀ d (xm ∷ δ)` がそれを外側へ運びます。帰納全体を通して前提 `trans` を消費するのは、この一段階だけです。
<!--/-->

```agda
    fwd h x hx =
      let hx' = subst (λ s → ⟨ x ∈ˢ s ⟩) (sym p) hx
          xm  = x , trans hx' (snd tm)
      in subst ⟨_⟩ (abs₀ d (xm ∷ δ)) (h xm hx')
    bwd : ⟨ (map fst δ) ⊨ᵛ (∀̇∈ t φ) ⟩ → ⟨ δ ⊨ᵐ (∀̇∈ t φ) ⟩
```

<!--en-->
The backward direction runs the other way: an outer verifier `g` quantifies over bare elements, while the inner clause expects a pair `xm` with its membership evidence attached. The projection `fst xm` is the outer element, and the term lemma transports its membership from `fst tm` to `⟦ t ⟧ᵛ (map fst δ)`, exactly the form `g` expects. Calling `g` yields outer truth, and `abs₀ d (xm ∷ δ)` transported along `sym` brings it back inside. This direction needs no transitivity: the pair `xm` arrives with its evidence attached.
<!--zh-->
反向沿另一方向进行：外层验证者 `g` 遍历裸元素，而内层子句期待一个自带成员证据的对 `xm`。投影 `fst xm` 是外层元素，词项引理把其成员关系从 `fst tm` 运到 `⟦ t ⟧ᵛ (map fst δ)`，恰是 `g` 期待的形式。调用 `g` 得到外层真值，`abs₀ d (xm ∷ δ)` 再沿 `sym` 运回内层。这一方向不需要传递性：对 `xm` 是带着证据到达的。
<!--ja-->
逆方向は逆向きに進みます。外側の検証者 `g` は素の要素を走査し、内側の節は所属の証拠を伴う対 `xm` を期待します。射影 `fst xm` が外側の要素であり、項の補題がその所属を `fst tm` から `⟦ t ⟧ᵛ (map fst δ)` へ運びます。これはちょうど `g` が期待する形です。`g` を呼び出せば外側の真理値が得られ、`abs₀ d (xm ∷ δ)` を `sym` に沿って運ぶことで内側へ戻します。この方向に推移性は不要です。対 `xm` は証拠を伴って届くからです。
<!--/-->

```agda
    bwd g xm hxm =
      subst ⟨_⟩ (sym (abs₀ d (xm ∷ δ)))
            (g (fst xm) (subst (λ s → ⟨ fst xm ∈ˢ s ⟩) p hxm))
  abs₀ (δ-∃∈ {t = t} {φ = φ} d) δ = ⇔toPath fwd bwd
    where
```

<!--en-->
The existential case `∃̇∈` mirrors the universal one, with one structural difference: satisfaction of an existential is defined as a join over the carrier, the least truth value above all the per-element contributions, and a join of truncated statements lives under propositional truncation, so both directions operate via `PT.map`. The same abbreviations `tm` and `p` are in scope; the mathematics of repacking witnesses through the range is identical.
<!--zh-->
存在情形 `∃̇∈` 镜像全称情形，仅有一处结构差异：存在量词的满足定义为载体上的上确界，即盖过所有逐元素贡献的最小真值，而被截断命题的上确界生活在命题截断之下，因此两个方向都经 `PT.map` 运作。缩写 `tm` 与 `p` 同样在作用域内；把见证经范围重新包装的数学与全称情形完全相同。
<!--ja-->
存在の場合 `∃̇∈` は全称の場合を写し取りますが、構造上の違いが一つあります。存在量化子の充足は台の上の上限、すなわち要素ごとの寄与すべてを覆う最小の真理値として定義され、切断された命題の上限は命題的切り詰めの下に住むため、両方向とも `PT.map` を通して動きます。略記 `tm` と `p` は同じくスコープにあり、範囲を通して証拠を束ね直す数学は全称の場合と同一です。
<!--/-->

```agda
    tm : SM
    tm = ⟦ t ⟧ᵐ δ
    p : fst tm ≡ ⟦ t ⟧ᵛ (map fst δ)
    p = ⟦⟧-fst t δ
    fwd : ⟨ δ ⊨ᵐ (∃̇∈ t φ) ⟩ → ⟨ (map fst δ) ⊨ᵛ (∃̇∈ t φ) ⟩
```

<!--en-->
Forward, a truncated inner witness is a triple: an inner element `xm` in the range, its membership evidence, and the body's inner truth. The map sends it to `fst xm`, transports the membership outward along `p` into the shape `⟨ fst xm ∈ˢ ⟦ t ⟧ᵛ (map fst δ) ⟩`, and transports the body's truth outward through the induction hypothesis `abs₀ d (xm ∷ δ)`. The witness itself is used only inside the truncation, never extracted.
<!--zh-->
正向，截断下的内层见证是一个三元组：范围内的内层元素 `xm`、其成员证据、母式的内层真值。map 把它送到 `fst xm`，沿 `p` 把成员关系运到外层，成为 `⟨ fst xm ∈ˢ ⟦ t ⟧ᵛ (map fst δ) ⟩` 的形状，再经归纳假设 `abs₀ d (xm ∷ δ)` 把母式真值运到外层。见证本身只在截断之内使用，从不被提取。
<!--ja-->
順方向では、切断された内側の証拠は三つ組です。範囲内の内側の要素 `xm`、その所属の証拠、そして母式の内側の真理値です。map はこれを `fst xm` に送り、`p` に沿って所属を外側へ運んで `⟨ fst xm ∈ˢ ⟦ t ⟧ᵛ (map fst δ) ⟩` の形にし、さらに帰納仮定 `abs₀ d (xm ∷ δ)` を通して母式の真理値を外側へ運びます。証拠そのものが取り出されることはなく、切断の内側でだけ使われます。
<!--/-->

```agda
    fwd = PT.map λ { (xm , hxm , hφ) →
            fst xm
          , subst (λ s → ⟨ fst xm ∈ˢ s ⟩) p hxm
          , subst ⟨_⟩ (abs₀ d (xm ∷ δ)) hφ }
    bwd : ⟨ (map fst δ) ⊨ᵛ (∃̇∈ t φ) ⟩ → ⟨ δ ⊨ᵐ (∃̇∈ t φ) ⟩
```

<!--en-->
Backward, an outer witness is a triple of a bare element `x`, its membership in the outer range, and the body's outer truth. The transport along `sym p` pulls the membership to the inner range, transitivity then certifies `x ∈ᶜ M` so that `xm` is an inner element, and the body's truth is transported inward through `sym (abs₀ d (xm ∷ δ))`. The truncated output is again assembled by `PT.map`, so no choice principle is invoked anywhere: the two bounded-quantifier cases hold with merely-inhabited witnesses on both sides.
<!--zh-->
反向，外层见证是三元组：裸元素 `x`、其在外层范围中的成员关系、母式的外层真值。沿 `sym p` 的传输把成员关系拉回内层范围，传递性随后证明 `x ∈ᶜ M`，使 `xm` 成为内层元素，母式真值再经 `sym (abs₀ d (xm ∷ δ))` 运入内层。截断的输出同样由 `PT.map` 组装，因此全程未使用任何选择公理：两个有界量词情形在两侧都只以仅要求存在的见证成立。
<!--ja-->
逆方向では、外側の証拠は三つ組です。素の要素 `x`、外側の範囲での所属、そして母式の外側の真理値です。`sym p` に沿う輸送が所属を内側の範囲へ引き戻し、推移性が続いて `x ∈ᶜ M` を証明するので `xm` は内側の要素となり、母式の真理値は `sym (abs₀ d (xm ∷ δ))` を通して内側へ運ばれます。切断された出力はやはり `PT.map` で組み立てられるため、どこでも選択公理は使われません。二つの有界量化子の場合は、両側とも単に inhabited な証拠で成立します。
<!--/-->

```agda
    bwd = PT.map λ { (x , hx , hφ) →
            let hx' = subst (λ s → ⟨ x ∈ˢ s ⟩) (sym p) hx
                xm  = x , trans hx' (snd tm)
            in xm , hx' , subst ⟨_⟩ (sym (abs₀ d (xm ∷ δ))) hφ }
```

<!--en-->
## Σ₁ upward, Π₁ downward

Beyond Δ₀, absoluteness becomes one-directional, and the directions are dual: a Σ₁ formula true inside is true outside, while a Π₁ formula true outside is true inside. The asymmetry comes from quantifier variance. A Σ₁ witness may be built by any finite string of unbounded existentials over a Δ₀ core, and an inner existential witness travels outward through `fst`{.Agda}. A Π₁ witness may likewise be built by unbounded universals, and an outer verifier is specialized, at each step, to `fst`{.Agda} of an inner element. No additional appeal to transitivity occurs in these unbounded steps; the Δ₀ base of each induction still rests on the absoluteness theorem, and hence on the transitivity hypothesis.
<!--zh-->
## Σ₁ 向上，Π₁ 向下

越出 Δ₀ 之外，绝对性变成单向的，且两个方向对偶：内层为真的 Σ₁ 公式在外层为真，外层为真的 Π₁ 公式在内层为真。不对称源于量词的变异性。Σ₁ 见证可以在 Δ₀ 核之上由任意有限串的无界存在量词构造，内层的存在见证经 `fst`{.Agda} 送到外层。Π₁ 见证同样可由无界全称构造，外层验证者在每一步被特化到内层元素的 `fst`{.Agda} 上。这些无界步骤不再使用传递性；但每条归纳的 Δ₀ 基础仍依赖绝对性定理，因而依赖传递性前提。
<!--ja-->
## Σ₁ は上向き、Π₁ は下向き

Δ₀ の外に出ると、絶対性は一方向になりますが、その二方向は双対です。内側で真な Σ₁ 論理式は外側でも真であり、外側で真な Π₁ 論理式は内側でも真です。この非対称は量化子の変異から来ます。Σ₁ の証拠は Δ₀ の核の上に、任意の有限個の無制限存在量化子の連なりで作られ得て、内側の存在の証拠は `fst`{.Agda} を通して外側へ渡ります。Π₁ の証拠も同様に無制限の全称量化子で作られ得て、外側の検証者は各段階で内側の要素の `fst`{.Agda} に特殊化されます。これらの無制限の段階で推移性がさらに使われることはありません。ただし、それぞれの帰納の Δ₀ の基底は絶対性定理に、ひいては推移性の仮定に依存します。
<!--/-->

<!--en-->
In the Δ₀ base case, `abs₀ d δ` is a path between the inner and outer truth values, so `subst` carries a proof of the inner truth value along that path. No propositional truncation is introduced in this base case. The Σ₁ case `σ-∃` is an unbounded existential over the carrier, and its satisfaction is a truncated join, so `PT.map` acts on a truncated pair: an inner witness `xm` with the body's inner truth `h` is sent to the outer element `fst xm`, and the recursive call `σ₁-up s (xm ∷ δ) h` extends the environment with the full pair, keeping the witness inside until the base case discards the wrapper.
<!--zh-->
在 Δ₀ 基础情形中，`abs₀ d δ` 是内外真值之间的路径，`subst` 沿这条路径把内层真值的证明传输到外层。这个基础情形本身不引入命题截断。Σ₁ 情形 `σ-∃` 是载体上的无界存在，其满足是命题截断下的上确界，因此 `PT.map` 作用于截断的对：内层见证 `xm` 配上母式的内层真值 `h`，被送到外层元素 `fst xm`，而递归调用 `σ₁-up s (xm ∷ δ) h` 用完整的对扩展环境，让见证在内层保留到基础情形丢弃包装为止。
<!--ja-->
Δ₀ の基底の場合、`abs₀ d δ` は内側と外側の真理値を結ぶパスであり、`subst` は内側の真理値の証明をそのパスに沿って外側へ輸送します。この基底の場合そのものは命題的切り詰めを導入しません。Σ₁ の場合 `σ-∃` は台の上の無制限の存在量化であり、その充足は命題的切り詰めのもとでの上限なので、`PT.map` が切断された対に作用します。内側の証拠 `xm` と母式の内側の真理値 `h` の対は、外側の要素 `fst xm` に送られ、再帰呼び出し `σ₁-up s (xm ∷ δ) h` は対全体で環境を拡張して、基底の場合が包みを捨てるまで証拠を内側に保ちます。
<!--/-->

```agda
  σ₁-up : ∀ {n} {φ : Formula SM n} → Σ₁ φ → (δ : SM ^ n)
        → ⟨ δ ⊨ᵐ φ ⟩ → ⟨ (map fst δ) ⊨ᵛ φ ⟩
  σ₁-up (σ-Δ₀ d) δ = subst ⟨_⟩ (abs₀ d δ)
  σ₁-up (σ-∃ s)  δ = PT.map λ { (xm , h) → fst xm , σ₁-up s (xm ∷ δ) h }

  π₁-down : ∀ {n} {φ : Formula SM n} → Π₁ φ → (δ : SM ^ n)
```

<!--en-->
The downward law is its mirror. The Δ₀ case transports along `sym (abs₀ d δ)`, and the Π₁ case `π-∀` is an unbounded universal: given an outer verifier `h`, it is instantiated at `fst xm` for each inner element `xm`, and the recursive call proves the body at the extended environment. No truncation appears here, since satisfaction of a universal is a meet, the greatest truth value below all the per-element contributions, and it is verified explicitly by giving the verifier; and the unbounded steps use no transitivity, because unbounded quantifiers range over the whole carrier, where the pair construction and the projection are already available.
<!--zh-->
向下律是它的镜像。Δ₀ 情形沿 `sym (abs₀ d δ)` 传输；Π₁ 情形 `π-∀` 是无界全称：给定外层验证者 `h`，对每个内层元素 `xm` 在 `fst xm` 处实例化，递归调用在扩展后的环境中证明母式。这里不出现截断，因为全称的满足是一个下确界，即低于所有逐元素贡献的最大真值，直接给出验证者即可显式验证；无界步骤不使用传递性，因为无界量词遍历整个载体，在那里对构造与投影本就可用。
<!--ja-->
下向きの法則はその鏡像です。Δ₀ の場合は `sym (abs₀ d δ)` に沿って輸送し、Π₁ の場合 `π-∀` は無制限の全称量化です。外側の検証者 `h` が与えられると、各内側の要素 `xm` に対して `fst xm` でインスタンス化し、再帰呼び出しが拡張された環境で母式を証明します。ここに切断は現れません。全称の充足は下限、すなわち要素ごとの寄与すべての下にある最大の真理値であり、検証者を直接与えることで明示的に検証できるからです。そして無制限の段階に推移性は使われません。無制限の量化子は台全体を走査し、そこでは対の構成と射影がはじめから使えるからです。
<!--/-->

```agda
          → ⟨ (map fst δ) ⊨ᵛ φ ⟩ → ⟨ δ ⊨ᵐ φ ⟩
  π₁-down (π-Δ₀ d) δ = subst ⟨_⟩ (sym (abs₀ d δ))
  π₁-down (π-∀ s)  δ h xm = π₁-down s (xm ∷ δ) (h (fst xm))
```

<!--en-->
## Recap

The boundary is exact. Under transitivity, Δ₀ truth agrees between `𝒮 ↾ M` and `𝒮`: `abs₀`{.Agda} gives a path of truth values for every Δ₀ witness. The bounded universal uses transitivity when passing from an inner verifier to arbitrary outer members of the bound; the bounded existential uses it when an outer witness must be admitted to the inner carrier. From this base, `σ₁-up`{.Agda} preserves Σ₁ truth upward and `π₁-down`{.Agda} preserves Π₁ truth downward. The reverse directions are unavailable in general: an arbitrary outer existential witness need not lie in `M`, while an inner universal verifier says nothing about outer elements outside `M`.
<!--zh-->
## 小结

边界是精确的。在传递性之下，Δ₀ 真值在 `𝒮 ↾ M` 与 `𝒮` 之间一致：`abs₀`{.Agda} 为每条 Δ₀ 见证给出真值的路径。有界全称从内层验证者走向界的任意外层成员时使用传递性；有界存在则在外层见证必须进入内层载体时使用它。在此基础上，`σ₁-up`{.Agda} 向上保持 Σ₁ 真值，`π₁-down`{.Agda} 向下保持 Π₁ 真值。反方向一般不能成立：任意外层存在见证未必属于 `M`，而内层全称验证者也没有说明 `M` 之外的外层元素。
<!--ja-->
## まとめ

境界は明確です。推移性のもとで、Δ₀ の真理値は `𝒮 ↾ M` と `𝒮` の間で一致し、`abs₀`{.Agda} は各 Δ₀ の証拠に真理値のパスを与えます。有界全称では、内側の検証者を界の任意の外側の要素へ適用するときに推移性を使います。有界存在では、外側の証人を内側の台へ入れるときに使います。この基底から、`σ₁-up`{.Agda} は Σ₁ の真理を上向きに、`π₁-down`{.Agda} は Π₁ の真理を下向きに保存します。逆方向は一般には得られません。任意の外側の存在証人が `M` に属するとは限らず、内側の全称検証者は `M` の外側の要素について何も述べないからです。
<!--/-->
