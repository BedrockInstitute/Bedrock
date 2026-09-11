<!--en-->
# The cumulative hierarchy

The cumulative hierarchy `V`{.Agda} is a higher inductive type with a strikingly economical idea: a set is the image of a small family, and membership in it asks merely for an index that hits the element. Equality is extensional by construction, because the type's own path constructor identifies families with the same image. This chapter turns that carrier into the set-theoretic structure `𝒮ᵥ`{.Agda}, whose equality is the path type, proposition-valued because `V`{.Agda} is an h-set, and whose membership is the hierarchy's native `∈`. On this structure the chapter proves extensionality, shows that membership is well-founded by building an accessibility witness for every set, derives irreflexivity from well-foundedness, and ends with dependent recursion along membership together with its propositional computation law.
<!--zh-->
# 累积层级

累积层级 `V`{.Agda} 是一个高阶归纳类型，其想法极为经济：集合就是某个小族的像，而属于它只需纯粹地存在一个命中该元素的索引。相等性由构造直接外延，因为类型的路径构造子把像相同的族视为同一个集合。本章把这个载体变成集合论结构 `𝒮ᵥ`{.Agda}：等词取路径类型，由于 `V`{.Agda} 是 h-集而成为命题值；成员关系取层级原生的 `∈`。在该结构上，本章证明外延性，通过为每个集合构造可及性证据说明成员关系良基，从良基性导出不可反性，最后给出沿成员关系的依赖递归及其命题级计算法则。
<!--ja-->
# 累積階層

累積階層 `V`{.Agda} は高階帰納型であり、その発想はきわめて経済的です。集合とは小さな族の像であり、その要素に属するとは、その要素に命中するインデックスが純粋に存在することを言います。等しさは構成によって外延的です。像の一致する族をパス構成子が同一視するからです。本章はこの台を集合論的構造 `𝒮ᵥ`{.Agda} へと組み立てます。等号はパス型であり、`V`{.Agda} が h-集合であるため命題値になり、所属関係は階層本来の `∈` です。この構造の上で、本章は外延性を証明し、すべての集合に対する到達可能性の証拠を構成して所属関係の整礎性を示し、整礎性から非反射性を導き、最後に所属関係に沿う依存再帰とその命題としての計算法則を与えます。
<!--/-->

<!--en-->
A carrier alone does not interpret the first-order language; one needs a carrier together with equality and membership as proposition-valued relations. The chapter fixes a universe level `ℓ` once, and every construction below is stated at that level. For the hierarchy the chosen pairing is native rather than adapted: equality will be the path type, made proposition-valued by the fact that `V`{.Agda} is an h-set, and membership will be the hierarchy's own `∈`, which already lands in `hProp`{.Agda}.
<!--zh-->
仅有一个载体还不足以解释一阶语言；需要载体配上作为命题值关系的等词与成员关系。本章一次性固定宇宙层级 `ℓ`，下文所有构造都在该层级上陈述。对层级而言，所选的配对是原生的而非适配的：等词取路径类型，由于 `V`{.Agda} 是 h-集而成为命题值；成员关系取层级自身的 `∈`，它本就落在 `hProp`{.Agda} 中。
<!--ja-->
台だけでは一階の言語を解釈できません。台に、命題値の関係としての等号と所属関係を対にする必要があります。本章は宇宙レベル `ℓ` を一度固定し、以下の構成はすべてこのレベルで述べられます。階層にとって選ばれる対は、適合の作業ではなく本来の形です。等号はパス型であり、`V`{.Agda} が h-集合であることにより命題値になり、所属関係は階層自身の `∈` で、はじめから `hProp`{.Agda} に落ち着きます。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth

module V.Hierarchy {ℓ : Level} where

open import FOL.ZFStructure using ( ZFStructure; module hPropStructure )
```

<!--en-->
Two imported ideas carry the well-foundedness proof. The first is propositional truncation: the statement "some index does the job" is kept as a mere existence, with no chosen witness, and it may be eliminated only into propositions. The second is accessibility, the data `Acc` of a well-founded relation: `x` is accessible when every membership step down from `x` lands at an already accessible element. These combine precisely because of the truncation: membership in a `sett` gives only a merely existing index, while accessibility, being propositional, is exactly the kind of target into which that mere existence may be converted.
<!--zh-->
良基性证明依赖两个导入的观念。其一是命题截断：「某个索引可行」这类陈述只作为纯粹存在保留，不选取见证，且只能消去到命题。其二是可及性，即良基关系的数据 `Acc`：当从 `x` 出发的每一步成员下降都落在已可及的元素上时，`x` 是可及的。二者恰因截断而结合：`sett` 中的成员关系只给出纯粹存在的索引，而可及性作为命题，正是那种纯粹存在可以转入的目标。
<!--ja-->
整礎性の証明を支えるのは、二つの考えです。第一は命題的切り詰めです。「あるインデックスが条件を満たす」という主張は選ばれた証人なしの純粋な存在として保たれ、命題へしか消去できません。第二は整礎な関係のデータ `Acc` である到達可能性です。`x` からの各所属の下降がすでに到達可能な要素に着地するとき、`x` は到達可能です。この二つは切り詰めによってこそ組み合わさります。`sett` への所属は切り詰められた形でしかインデックスの存在を与えませんが、到達可能性は命題であり、まさにその純粋な存在を変換できる種類の行き先だからです。
<!--/-->

```agda

import Cubical.HITs.PropositionalTruncation as PT
import Cubical.Data.Empty as Empty
import Cubical.Induction.WellFounded as WellFoundedInduction
open import Cubical.Induction.WellFounded using ( Acc; acc; WellFounded; isPropAcc; wf→x≮x )
open import Cubical.HITs.CumulativeHierarchy.Base
```

<!--en-->
The higher inductive type is worth reading closely before it is used. Its constructor `sett`{.Agda} forms, from a small index type and a family into the hierarchy, the set that is the image of that family. Membership `y ∈ sett X ix` is a truncated preimage: it holds merely when some `i : X` has `ix i ≡ y`. A path constructor identifies any two `sett` presentations whose members agree, which is extensionality built into the type itself. This chapter does not define the HIT; it builds the structure `𝒮ᵥ`{.Agda} on top of it, and the next code block is that structure.
<!--zh-->
在使用这个高阶归纳类型之前，值得细读它。其构造子 `sett`{.Agda} 从小索引类型和指向层级的族造出作为该族之像的集合。成员关系 `y ∈ sett X ix` 是截断的原像：仅当某个 `i : X` 使 `ix i ≡ y` 时成立。路径构造子把成员一致的任意两个 `sett` 表示视为相等，这是内建于类型本身的外延性。本章不定义该高阶归纳类型，而是在其上构造结构 `𝒮ᵥ`{.Agda}；下一个代码块就是这个结构。
<!--ja-->
この高階帰納型は、使う前によく見る価値があります。その構成子 `sett`{.Agda} は、小さなインデックス型と階層への族から、その族の像である集合を形作ります。所属 `y ∈ sett X ix` は切り詰められた原像であり、`ix i ≡ y` となる `i : X` が切り詰められた形で存在するときに成り立ちます。パス構成子は、要素の一致する二つの `sett` 表示を同一視します。これは型そのものに組み込まれた外延性です。本章は HIT を定義するのではなく、その上に構造 `𝒮ᵥ`{.Agda} を組み立てます。次のコードブロックがその構造です。
<!--/-->

```agda
  using ( V; setIsSet; _∈_; elimProp )
open import Cubical.HITs.CumulativeHierarchy.Base
  using ( sett )  -- lint-agda: keep (prose references link through this import)
open import Cubical.HITs.CumulativeHierarchy.Properties
  using ( ∈∈ₛ; extensionality )
```

<!--en-->
## The higher inductive type

The generating idea is the oldest one in set theory: a set is no more than the collection of its members. The constructor `sett`{.Agda} takes a small index type `X : Type ℓ` and a family `ix : X → V ℓ`, and forms the set whose members are the image of `ix`. Membership accordingly asks for a preimage, merely: `y ∈ sett X ix` is the truncation of "some `i : X` with `ix i ≡ y`". Two families with the same image give the *same* set, because a path constructor identifies `sett` presentations with agreeing members, and the whole type is truncated to an h-set by `setIsSet`{.Agda}.

## The structure

The chosen packaging is deliberately minimal. Equality is the path type `x ≡ y`, paired with the certificate `setIsSet x y` that this type is a proposition; set-hood of `V`{.Agda} is what makes paths between its elements proposition-valued. Membership is the hierarchy's own `∈`, whose value at each pair already lives in `hProp`{.Agda}. These fields assemble into the structure `𝒮ᵥ`{.Agda} over the `hProp`{.Agda} truth-value algebra, the structure on which the first-order language is interpreted. The subscript is a plain `v`, for the hierarchy.
<!--zh-->
## 高阶归纳类型

其基本思想是集合论中最古老的表述：集合由其成员汇集而成。构造子 `sett`{.Agda} 接受小索引类型 `X : Type ℓ` 和族 `ix : X → V ℓ`，形成以 `ix` 的像为成员的集合。因此，`y ∈ sett X ix` 表示「存在 `i : X` 使 `ix i ≡ y`」的截断。像相同的两个族给出**同一个**集合，因为路径构造子把成员一致的 `sett` 表示视为相等，而整个类型又被 `setIsSet`{.Agda} 截断为 h-集。

## 结构

所选的打包刻意保持极简。等词是路径类型 `x ≡ y`，连同「该类型是命题」的证书 `setIsSet x y` 配成一对；正是 `V`{.Agda} 的 h-集性使其元素间的路径成为命题值。成员关系是层级自身的 `∈`，其在每一点上的值本就落在 `hProp`{.Agda} 中。这些字段组装成 `hProp`{.Agda} 真值代数上的结构 `𝒮ᵥ`{.Agda}，一阶语言就在这个结构上解释。下标就是普通的 `v`，指层级。
<!--ja-->
## 高階帰納型

基本となる考えは集合論で最も古いものです。集合とはその要素の集まりにほかなりません。構成子 `sett`{.Agda} は小さなインデックス型 `X : Type ℓ` と族 `ix : X → V ℓ` を受け取り、`ix` の像を要素とする集合を形作ります。したがって所属は原像を、切り詰められた形で求めます。`y ∈ sett X ix` は「`ix i ≡ y` となる `i : X` がある」ことの切り詰めです。同じ像を持つ二つの族は**同じ**集合を与えます。要素の一致する `sett` 表示をパス構成子が同一視し、型全体が `setIsSet`{.Agda} によって h-集合へと切り詰められるからです。

## 構造

選ばれる構成は意図的に最小限です。等号はパス型 `x ≡ y` であり、この型が命題であることの証明 `setIsSet x y` と対にされます。`V`{.Agda} の h-集合性こそが、その要素間のパスを命題値にするのです。所属関係は階層自身の `∈` で、各対での値ははじめから `hProp`{.Agda} に住みます。これらのフィールドが、`hProp`{.Agda} の真理値代数上の構造 `𝒮ᵥ`{.Agda} に組み上がります。一階の言語はこの構造の上で解釈されます。添字は階層を指す普通の `v` です。
<!--/-->

<!--en-->
The carrier field is `V ℓ`, and its set-hood certificate `setIsSet` is recorded as `isSetS`. The equality field makes the choice explicit: `_≈ˢ_` sends `x` and `y` to the pair of the path type `x ≡ y` and the proof `setIsSet x y` that this path type is a proposition. This is the one place where h-set-ness does real work in the packaging. It is not that paths need to be changed into something proposition-valued; for an h-set, the type `x ≡ y` of paths between two elements already is a proposition, and the field simply records that fact alongside the type it certifies.
<!--zh-->
载体字段是 `V ℓ`，其 h-集性证书 `setIsSet` 记录在 `isSetS` 中。等词字段把这个选择写得很明确：`_≈ˢ_` 把 `x` 与 `y` 送往由路径类型 `x ≡ y` 与「该路径类型是命题」的证明 `setIsSet x y` 组成的对。这是打包过程中 h-集性真正发挥作用的地方。并不是要把路径改造成某种命题值的东西；对 h-集而言，两个元素之间的路径类型 `x ≡ y` 本来就是命题，该字段只是把这一事实连同它所认证的类型一起记录下来。
<!--ja-->
台のフィールドは `V ℓ` であり、その h-集合性の証明 `setIsSet` が `isSetS` として記録されます。等号のフィールドはこの選択を明示します。`_≈ˢ_` は `x` と `y` を、パス型 `x ≡ y` と「このパス型が命題である」ことの証明 `setIsSet x y` の対へ送ります。h-集合性がこの構成で実際に働くのはここです。パスを命題値の何かに作り変える必要があるのではありません。h-集合に対しては、二つの要素の間のパス型 `x ≡ y` はもともと命題であり、フィールドはその事実を、証明の対象となる型とともに記録しているだけです。
<!--/-->

```agda
𝒮ᵥ : ZFStructure (hPropAlgebra (ℓ-suc ℓ))
𝒮ᵥ = record
  { S      = V ℓ
  ; isSetS = setIsSet
  ; _≈ˢ_   = λ x y → (x ≡ y) , setIsSet x y
```

<!--en-->
The membership field `_∈ˢ_` is simply the hierarchy's own `∈`, which already takes values in `hProp`. Since the structure's relations are proposition-valued, many later arguments need the underlying type of a truth value rather than the truth value itself. Opening `hPropStructure 𝒮ᵥ` provides that reading: `x ∈ᵗ y` names the type `⟨ x ∈ˢ y ⟩` of inhabitants of the membership proposition. So `∈ᵗ` is not a second membership relation; it is the same relation viewed as a type. It is this reading that well-foundedness and induction below are stated for.
<!--zh-->
成员关系字段 `_∈ˢ_` 就是层级自身的 `∈`，它本就取值于 `hProp`。由于结构的关系都是命题值，后文许多论证需要的是真值的底层类型而非真值本身。打开 `hPropStructure 𝒮ᵥ` 后即可获得这一读法：`x ∈ᵗ y` 指成员命题的元素构成的类型 `⟨ x ∈ˢ y ⟩`。所以 `∈ᵗ` 不是另一条成员关系，而是同一条关系按类型来看的样子。下文的良基性与归纳正是对这个 `∈ᵗ` 读法陈述的。
<!--ja-->
所属関係のフィールド `_∈ˢ_` は階層自身の `∈` そのものであり、はじめから `hProp` に値を取ります。構造の関係は命題値なので、以後の多くの議論では真理値そのものではなく、その基礎型が必要になります。`hPropStructure 𝒮ᵥ` を開くと、この読み方が `x ∈ᵗ y` として提供され、型 `⟨ x ∈ˢ y ⟩`、つまり所属命題の要素のなす型を表します。したがって `∈ᵗ` は第二の所属関係ではなく、同じ関係を型として見たものです。以下の整礎性と帰納は、この `∈ᵗ` の読みに対して述べられます。
<!--/-->

```agda
  ; _∈ˢ_   = _∈_ }

open hPropStructure 𝒮ᵥ
```

<!--en-->
One reading of the levels, worth fixing early: the carrier `V ℓ` lives in `Type (ℓ-suc ℓ)`, one universe above its index types, and truth values live in `hProp (ℓ-suc ℓ)` alongside it. The hierarchy is a *large* type built from *small* indexing data. The small membership `∈ₛ`, connected to the large one by `∈∈ₛ`{.Agda}, will reappear below.

## Extensionality and well-founded membership

Suppose two sets `a` and `b` agree at every point: for each `x`, there is a path between the propositions `x ∈ a` and `x ∈ b`. Then any member of `a` transports along that path to a member of `b`, and conversely, so `a` and `b` mutually include each other. The library's `extensionality`{.Agda} turns exactly this mutual inclusion into a path `a ≡ b`, and `subst`{.Agda} carries membership along the pointwise paths to produce it. Extensionality for the hierarchy is thus a consequence of its definition, not an additional assumption.
<!--zh-->
先确定层级的一种读法：载体 `V ℓ` 住在 `Type (ℓ-suc ℓ)`，比它的索引类型高一个宇宙，真值也随之住在 `hProp (ℓ-suc ℓ)`。层级是由**小**索引数据造出的**大**类型。经 `∈∈ₛ`{.Agda} 与大成员关系相连的小成员关系 `∈ₛ` 在下文会再次出现。

## 外延性与成员关系的良基性

假设两个集合 `a` 与 `b` 在每一点上一致：对每个 `x`，命题 `x ∈ a` 与 `x ∈ b` 之间有路径。那么 `a` 的任何成员沿该路径可搬运为 `b` 的成员，反之亦然，于是 `a` 与 `b` 互相包含。库的 `extensionality`{.Agda} 正是把这种双向包含转化为路径 `a ≡ b`，而 `subst`{.Agda} 沿逐点路径搬运成员资格来完成转化。层级的外延性因此是其定义的推论，而非额外假设。
<!--ja-->
レベルの読み方を先に確めておきます。台 `V ℓ` は `Type (ℓ-suc ℓ)` に住み、そのインデックス型より一つ上の宇宙にあり、真理値もそれに並んで `hProp (ℓ-suc ℓ)` に住みます。階層は**小さな**インデックスデータから作られた**大きな**型です。`∈∈ₛ`{.Agda} によって大きな所属関係と結ばれる小さな所属関係 `∈ₛ` は、この後も現れます。

## 外延性と所属関係の整礎性

二つの集合 `a` と `b` が各点で一致すると仮定します。つまり各 `x` に対して、命題 `x ∈ a` と `x ∈ b` の間にパスがあるとします。すると `a` の任意の要素はそのパスに沿って `b` の要素へ輸送でき、その逆もできるので、`a` と `b` は互いを包含します。ライブラリの `extensionality`{.Agda} はまさにこの相互包含をパス `a ≡ b` へ変換し、`subst`{.Agda} が各点のパスに沿って所属を輸送することでそれを作ります。階層の外延性はしたがって追加の仮定ではなく、その定義の帰結です。
<!--/-->

<!--en-->
The hypothesis `h` gives, for every `x`, a path between the propositions `x ∈ a` and `x ∈ b`; the goal is the path `a ≡ b`. The library's `extensionality` expects small membership, so the proof runs through the bridge `∈∈ₛ` in one direction. An input `x∈ₛa` is a small membership of `x` in `a`. Its conversion `∈∈ₛ .snd x∈ₛa` goes from small to large, producing an inhabitant of `x ∈ a`. Then `subst ⟨_⟩ (h x)` transports that inhabitant along the pointwise path, and since `h x` says the two membership propositions agree at `x`, the transported value inhabits `x ∈ b`. Finally `∈∈ₛ .fst` converts back from large to small, yielding a small membership of `x` in `b`. That is the forward component of the mutual inclusion `extensionality` consumes.
<!--zh-->
假设 `h` 对每个 `x` 给出命题 `x ∈ a` 与 `x ∈ b` 之间的路径；目标是路径 `a ≡ b`。库的 `extensionality` 期望小成员关系，因此证明经桥 `∈∈ₛ` 走一个方向。输入 `x∈ₛa` 是 `x` 属于 `a` 的小成员关系。其转换 `∈∈ₛ .snd x∈ₛa` 从小到大，产出 `x ∈ a` 的一个元素。然后 `subst ⟨_⟩ (h x)` 沿逐点路径搬运该元素；由于 `h x` 说两条成员命题在 `x` 处一致，搬运后的值落在 `x ∈ b` 中。最后 `∈∈ₛ .fst` 从大到小转回，得到 `x` 属于 `b` 的小成员关系。这正是 `extensionality` 所消耗的双向包含的向前分量。
<!--ja-->
仮定 `h` は、各 `x` に対して命題 `x ∈ a` と `x ∈ b` の間のパスを与えます。目標はパス `a ≡ b` です。ライブラリの `extensionality` は小さな所属関係を期待するので、証明は橋 `∈∈ₛ` を一方向に通ります。入力 `x∈ₛa` は `x` の `a` への小所属関係です。その変換 `∈∈ₛ .snd x∈ₛa` は小から大へ向かい、`x ∈ a` の要素を生成します。次に `subst ⟨_⟩ (h x)` がその要素を各点のパスに沿って輸送します。`h x` は二つの所属命題が `x` で一致することを言うので、輸送された値は `x ∈ b` に住みます。最後に `∈∈ₛ .fst` が大から小へ戻し、`x` の `b` への小所属関係が得られます。これが `extensionality` が受け取る相互包含の前方の成分です。
<!--/-->

```agda
extensionalV : {a b : V ℓ} → ((x : V ℓ) → (x ∈ a) ≡ (x ∈ b)) → a ≡ b
extensionalV {a} {b} h = extensionality a b
  ( (λ x x∈ₛa → ∈∈ₛ {a = x} {b = b} .fst
      (subst ⟨_⟩ (h x) (∈∈ₛ {a = x} {b = a} .snd x∈ₛa)))
  , (λ x x∈ₛb → ∈∈ₛ {a = x} {b = a} .fst
```

<!--en-->
The second component is the same run of the bridge in reverse: a small membership of `x` in `b` is converted to large, transported backward along `sym (h x)`, and converted back to a small membership of `x` in `a`. Together the two components form the mutual inclusion from which `extensionality` produces the path `a ≡ b`, which is the equality `extensionalV` returns.
<!--zh-->
第二个分量是把桥反向走一遍：`x` 属于 `b` 的小成员关系先转为大，再沿 `sym (h x)` 反向搬运，最后转回 `x` 属于 `a` 的小成员关系。两个分量合起来构成双向包含，`extensionality` 由此产出路径 `a ≡ b`，即 `extensionalV` 返回的等词。
<!--ja-->
第二の成分は、同じ橋を逆向きに通るものです。`x` の `b` への小所属関係を大へ変換し、`sym (h x)` に沿って逆方向へ輸送し、`x` の `a` への小所属関係へ戻します。二つの成分が合わさって相互包含が得られ、`extensionality` はそこからパス `a ≡ b` を作ります。これが `extensionalV` が返す等号です。
<!--/-->

```agda
      (subst ⟨_⟩ (sym (h x)) (∈∈ₛ {a = x} {b = b} .snd x∈ₛb))) )
```

<!--en-->
(The `∈ₛ` appearing through `∈∈ₛ`{.Agda} is the library's *small* membership; the chapter "Small presentations of sets" discusses it in detail. Here it serves only to connect the two.)

Regularity, in this development, is the statement that membership is well-founded: every element of the carrier is accessible under `∈ᵗ`, where accessibility is the inductive data `Acc` of a well-founded relation. The proof eliminates the higher inductive type into the proposition-valued family `λ s → Acc _∈ᵗ_ s`; the role of `isPropAcc s` is to certify that this target is indeed a proposition, which is what licenses the elimination. In the `sett` case, a member `y` merely comes from an index via `ix`, so the induction hypothesis gives accessibility at `ix i`, and the witnessed path `ix i ≡ y` transports that accessibility to `y` itself.
<!--zh-->
(经 `∈∈ₛ`{.Agda} 现身的 `∈ₛ` 是库的**小**成员关系，「集合的小呈现」一章将细说；此处它只起衔接作用。)

在本开发中，正则性即是「成员关系良基」这一陈述：载体的每个元素在 `∈ᵗ` 下都可及，其中可及性是良基关系的归纳数据 `Acc`。证明把该高阶归纳类型消去到取命题值的族 `λ s → Acc _∈ᵗ_ s`；`isPropAcc s` 的作用是认证这个目标确实是命题，正是这一点使消去合法。在 `sett` 情形中，成员 `y` 只经由 `ix` 以截断方式来自某个索引，于是归纳假设给出 `ix i` 处的可及性，而带见证的路径 `ix i ≡ y` 把这一可及性搬运到 `y` 自身。
<!--ja-->
(`∈∈ₛ`{.Agda} を通して現れる `∈ₛ` はライブラリの**小さな**所属関係であり、次の章で詳しく述べます。ここでは両者を結ぶ役割だけを果たします。)

この開発における正則性は、所属関係が整礎であるという主張です。すなわち、台のすべての要素が `∈ᵗ` の下で到達可能であり、到達可能性とは整礎な関係の帰納的データ `Acc` のことです。証明は、この高階帰納型を命題値の族 `λ s → Acc _∈ᵗ_ s` へ消去することによって進みます。`isPropAcc s` の役割は、この行き先が確かに命題であることを証明することであり、そのために消去が正当化されるのです。`sett` の場合、要素 `y` は `ix` を通して切り詰められた形でインデックスに由来するだけなので、帰納仮定が `ix i` での到達可能性を与え、証人つきのパス `ix i ≡ y` がその到達可能性を `y` 自身へ輸送します。
<!--/-->

<!--en-->
Accessibility of a set `s`, the type `Acc _∈ᵗ_ s`, says that every descending membership step from `s` to a member `y` of `s` lands at an element that is itself accessible; `WellFounded _∈ᵗ_` says this holds for every element of the carrier. In the call to `elimProp`, the function `λ s → isPropAcc s` certifies that each target `Acc _∈ᵗ_ s` is a proposition. The target family remains `λ s → Acc _∈ᵗ_ s`. In the `sett` case, the branch receives the family `ix` and an induction hypothesis `rec i : Acc _∈ᵗ_ (ix i)` for every index. It must assemble `Acc _∈ᵗ_ (sett X ix)`, so `acc` asks it to provide accessibility for an arbitrary member `y`.
<!--zh-->
集合 `s` 的可及性，即类型 `Acc _∈ᵗ_ s`，说从 `s` 到其成员 `y` 的每一步下降都落在本身可及的元素上；`WellFounded _∈ᵗ_` 则说载体的每个元素都如此。在 `elimProp` 的调用中，函数 `λ s → isPropAcc s` 证明各目标 `Acc _∈ᵗ_ s` 都是命题；目标族本身仍是 `λ s → Acc _∈ᵗ_ s`。在 `sett` 情形中，分支拿到族 `ix`，以及对每个索引给出 `rec i : Acc _∈ᵗ_ (ix i)` 的归纳假设。它要组装 `Acc _∈ᵗ_ (sett X ix)`，所以 `acc` 要求它为任意成员 `y` 给出可及性。
<!--ja-->
集合 `s` の到達可能性、すなわち型 `Acc _∈ᵗ_ s` は、`s` からその要素 `y` への各下降が、それ自体到達可能な要素に着地することを述べます。`WellFounded _∈ᵗ_` は、台のすべての要素についてこれが成り立つという主張です。`elimProp` の呼び出しでは、関数 `λ s → isPropAcc s` が各目標 `Acc _∈ᵗ_ s` の命題性を証明します。目標の族そのものは `λ s → Acc _∈ᵗ_ s` です。`sett` の場合、分岐は族 `ix` と、各インデックスについて `rec i : Acc _∈ᵗ_ (ix i)` を与える帰納仮定を受け取ります。ここで `Acc _∈ᵗ_ (sett X ix)` を組み立てるため、`acc` は任意の要素 `y` の到達可能性を要求します。
<!--/-->

```agda
regularityV : WellFounded _∈ᵗ_
regularityV = elimProp (λ s → isPropAcc s)
  (λ X ix rec → acc (λ y y∈ →
    PT.rec (isPropAcc y)
           (λ { (i , p) → subst (Acc _∈ᵗ_) p (rec i) })
```

<!--en-->
For such a member `y`, the witness `y∈` gives only the propositional truncation of a pair `(i , p)` with `p : ix i ≡ y`. The call `PT.rec (isPropAcc y)` may eliminate this truncated preimage because its actual target, `Acc _∈ᵗ_ y`, is a proposition, as certified by `isPropAcc y`. Inside the branch, `subst (Acc _∈ᵗ_) p (rec i)` transports the induction hypothesis from `ix i` to `y`. Thus the proof uses the index without choosing one globally.
<!--zh-->
对这样的成员 `y`，证据 `y∈` 只给出一对 `(i , p)` 的命题截断，其中 `p : ix i ≡ y`。调用 `PT.rec (isPropAcc y)` 可以消去这个截断原像，因为真正的目标 `Acc _∈ᵗ_ y` 是命题，而 `isPropAcc y` 正是它的命题性证书。在分支内部，`subst (Acc _∈ᵗ_) p (rec i)` 把归纳假设从 `ix i` 搬运到 `y`。因此证明可在局部分支中使用索引，却不需要在全局选定一个索引。
<!--ja-->
このような要素 `y` に対し、証拠 `y∈` が与えるのは、`p : ix i ≡ y` を持つ対 `(i , p)` の命題的切り詰めだけです。`PT.rec (isPropAcc y)` がこの切り詰められた原像を消去できるのは、実際の目標 `Acc _∈ᵗ_ y` が命題であり、`isPropAcc y` がその命題性を証明するからです。分岐の中では `subst (Acc _∈ᵗ_) p (rec i)` が帰納仮定を `ix i` から `y` へ輸送します。このため、証明は大域的にインデックスを選ぶことなく、局所的な分岐の中でそれを利用できます。
<!--/-->

```agda
           y∈))
```

<!--en-->
The first consequence of regularity is irreflexivity: no set belongs to itself. In terms of accessibility this is immediate: an element standing in a well-founded relation to itself would contradict the accessibility data, which requires every step down to land at an accessible element. This derivation uses the `Acc` statement proved above; it is not claimed here to capture every classical formulation of Foundation.
<!--zh-->
正则性的第一个推论是不可反性：没有集合属于自身。用可及性的语言看这是直接的：与自身处于良基关系中的元素会同可及性数据矛盾，因为可及性要求每一步下降都落在可及的元素上。这里的推导使用的是上文证明的 `Acc` 陈述；本章不宣称它涵盖 Foundation 的每一个经典表述。
<!--ja-->
正則性の最初の帰結は非反射性です。集合は自分自身に属しません。到達可能性の言葉で言えばこれは直接です。自分自身と整礎な関係に立つ要素は、到達可能性のデータと矛盾します。下降の各一歩が到達可能な要素に着地することを、到達可能性は要求するからです。ここでの導出は、上で証明した `Acc` の主張を使うものであり、Foundation のすべての古典的定式化を捉えると主張するものではありません。
<!--/-->

<!--en-->
The hypothesis `⟨ A ∈ˢ A ⟩` is an inhabitant of the underlying type of the membership truth value, which is precisely the relation `∈ᵗ` on which `regularityV` was proved. For any well-founded relation, no element can stand in the relation to itself: this is the library's irreflexivity theorem `wf→x≮x`, which applies here with `regularityV` as its well-foundedness input. The result is a contradiction, witnessed by the empty type `Empty.⊥`.
<!--zh-->
假设 `⟨ A ∈ˢ A ⟩` 是成员真值底层类型的一个元素，而这正是 `regularityV` 所针对的关系 `∈ᵗ`。对任何良基关系，元素都不能与自身处于该关系中：这就是库的不可反性定理 `wf→x≮x`，此处以 `regularityV` 作为其良基性输入来适用。结果是矛盾，以空类型 `Empty.⊥` 呈现。
<!--ja-->
仮定 `⟨ A ∈ˢ A ⟩` は、所属の真理値の基礎型の要素であり、これは `regularityV` が証明された関係 `∈ᵗ` そのものです。整礎な関係に対しては、どの要素も自分自身とその関係に立つことはできません。これがライブラリの非反射性の定理 `wf→x≮x` であり、ここでは `regularityV` を整礎性の入力として適用します。結果は矛盾であり、空の型 `Empty.⊥` がそれを示します。
<!--/-->

```agda
∈-irrefl : (A : S) → ⟨ A ∈ˢ A ⟩ → Empty.⊥
∈-irrefl A = wf→x≮x regularityV {x = A}
```

<!--en-->
## Recursion on membership

Well-foundedness has a computational payoff: a well-founded relation supports recursion. Concretely, a value at `x` may depend on the values at every member `y` of `x`, and this dependence terminates because membership is well-founded. The target may be an arbitrary dependent type family `P`, not merely a proposition, which is what makes this a recursion principle rather than a proof principle. This is the type-theoretic form of recursion along membership, stated without an ordinal-indexed hierarchy: instead of recursing along stage indices, one recurses directly along the membership relation. Its recursion equation also holds as a propositional equality, so later arguments can compute with it.
<!--zh-->
## 沿成员关系的递归

良基性有计算上的回报：良基关系支持递归。具体而言，`x` 处的值可以依赖于 `x` 的每个成员 `y` 处的值，而由于成员关系良基，这种依赖必然终止。落点可以是任意的依赖类型族 `P`，而不限于命题；这使它成为递归原理而非仅仅是证明原理。这是沿成员关系的递归在类型论中的形态，且不以序数索引的层级来陈述：不是沿层指标递归，而是直接沿成员关系本身递归。其递归方程还以命题等式成立，故后续论证可据以计算。
<!--ja-->
## 所属関係上の再帰

整礎性には計算上の見返りがあります。整礎な関係は再帰を支えるのです。具体的には、`x` での値は `x` の各要素 `y` での値に依存でき、所属関係が整礎であるためこの依存は必ず停止します。行き先は命題に限らず任意の依存型族 `P` でよく、これがこの原理を証明原理にとどまらない再帰原理にしています。これは所属関係に沿う再帰の型論的形態であり、序数で添字付けられた階層を介さずに述べられます。段階の添字に沿って再帰するのではなく、所属関係そのものに沿って再帰するのです。再帰方程式も命題としての等式で成り立つため、後の議論はそれを頼りに計算できます。
<!--/-->

<!--en-->
Read the type of `∈-induction` from the outside in. The family `P` assigns to each set a type in an arbitrary universe `Type ℓ'`, so the value being constructed may genuinely vary with the set. The step function `e` receives a set `x` together with recursive values `P y` for every member `y` of `x`, where membership appears through `∈ᵗ`, the Type-valued reading of the truth value, and returns `P x`. What justifies the definition is `regularityV`: the library's `WFI.induction`, instantiated at this well-founded relation, converts the step function into a total family. No fresh proof of well-foundedness is needed.
<!--zh-->
从外向内读 `∈-induction` 的类型。类型族 `P` 给每个集合指派任意宇宙 `Type ℓ'` 中的一个类型，因此被构造的值可以真正随集合变化。步进函数 `e` 接收集合 `x` 以及 `x` 的每个成员 `y` 处的递归值 `P y`，成员关系经由真值的 Type 值读法 `∈ᵗ` 出现，并返回 `P x`。为这一构造提供依据的是 `regularityV`：库的 `WFI.induction` 在这条良基关系上实例化，把步进函数变为全定义的族。此处无需重新证明良基性。
<!--ja-->
`∈-induction` の型は外から内へ読みます。型族 `P` は各集合に対して任意の宇宙 `Type ℓ'` の型を割り当てるので、構成される値は集合とともに実際に変わりえます。ステップ関数 `e` は集合 `x` と、`x` の各要素 `y` での再帰的な値 `P y` を受け取ります。所属関係は真理値の Type 値の読み `∈ᵗ` を通して現れます。そして `P x` を返します。この定義を正当化するのは `regularityV` です。ライブラリの `WFI.induction` をこの整礎な関係で実例化すれば、ステップ関数が全域の族へ変わります。ここで整礎性を改めて証明する必要はありません。
<!--/-->

```agda
∈-induction : ∀ {ℓ'} {P : V ℓ → Type ℓ'}
            → (∀ x → (∀ y → y ∈ᵗ x → P y) → P x)
            → ∀ x → P x
∈-induction = WellFoundedInduction.WFI.induction regularityV

∈-induction-compute : ∀ {ℓ'} {P : V ℓ → Type ℓ'}
```

<!--en-->
The computation law exposes the recursive call at each member as an equation rather than leaving it hidden in the definition: `∈-induction e x` equals the step applied to `x` and to `∈-induction e y` at every member `y`. The equation is stated as a propositional equality, so it may or may not hold definitionally; stating it explicitly lets later proofs rewrite a recursively defined value by this equation whenever reduction is not definitional. The law is `WFI.induction-compute` from the library, proved for any well-founded relation, instantiated here at membership.
<!--zh-->
计算法则把每个成员处的递归调用显式地作为等式呈现，而不是藏在定义之中：`∈-induction e x` 等于把步进函数作用于 `x` 与每个成员 `y` 处的 `∈-induction e y`。该等式以命题等式的形式陈述，因此未必定义性成立；显式陈述它，使得当化归不是定义性时，后续证明仍可按这条等式改写递归定义的值。该法则即库的 `WFI.induction-compute`，它对任意良基关系证明此等式，此处实例化于成员关系。
<!--ja-->
計算法則は、各要素での再帰呼び出しを定義の内側に隠さず、等式として露呈させます。すなわち `∈-induction e x` は、ステップ関数を `x` と各要素 `y` での `∈-induction e y` に適用したものに等しいということです。この等式は命題としての等式として述べられており、定義的に成り立つとは限りません。それを明示しておけば、簡約が定義的でない場合でも、後の証明はこの等式によって再帰的に定義された値を書き換えられます。この法則はライブラリの `WFI.induction-compute` であり、任意の整礎な関係に対して証明され、ここでは所属関係に実例化されています。
<!--/-->

```agda
  (e : ∀ x → (∀ y → y ∈ᵗ x → P y) → P x) (x : V ℓ)
  → ∈-induction e x ≡ e x (λ y _ → ∈-induction e y)
∈-induction-compute = WellFoundedInduction.WFI.induction-compute regularityV
```

<!--en-->
## Recap

The hierarchy `V`{.Agda}, received from the library as a higher inductive type in which sets are images of small families and the whole type is an h-set, has been packaged as the structure `𝒮ᵥ`{.Agda}: paths as equality, proposition-valued by set-hood, and the native membership. Extensionality (`extensionalV`{.Agda}) follows from the extensional path constructor via the small-membership bridge, and well-foundedness of membership (`regularityV`{.Agda}) follows by elimination into accessibility. Well-foundedness in turn yields irreflexivity and the recursion principle `∈-induction` with its computation law `∈-induction-compute`. The chapter "Small presentations of sets" takes up the small membership `∈ₛ` and its bridge to `∈`, which is the specific question it addresses.
<!--zh-->
## 小结

作为高阶归纳类型的层级 `V`{.Agda}，其中集合是小族的像、整个类型是 h-集，已被打包为结构 `𝒮ᵥ`{.Agda}：路径为等词，由 h-集性使其为命题值，成员关系取原生的 `∈`。外延 (`extensionalV`{.Agda}) 经小成员关系桥从外延路径构造子得到，成员关系的良基性 (`regularityV`{.Agda}) 由消去到可及性得到。良基性又给出不可反性以及递归原理 `∈-induction` 及其计算法则 `∈-induction-compute`。「集合的小呈现」一章讨论小成员关系 `∈ₛ` 及其与 `∈` 的桥接，这是它要处理的具体问题。
<!--ja-->
## まとめ

集合を小さな族の像とし、型全体が h-集合である高階帰納型としてライブラリから受け取った階層 `V`{.Agda} は、構造 `𝒮ᵥ`{.Agda} として構成されました。パスを等号とし、h-集合性により命題値とし、本来の所属関係を取ります。外延性 (`extensionalV`{.Agda}) は小所属関係の橋を経て外延的なパス構成子から、所属関係の整礎性 (`regularityV`{.Agda}) は到達可能性への消去から従います。整礎性はさらに非反射性と、再帰原理 `∈-induction` とその計算法則 `∈-induction-compute` をもたらします。次の章は小さな所属関係 `∈ₛ` とその `∈` への橋を取り上げます。これが次の章が扱う具体的な問題です。
<!--/-->
