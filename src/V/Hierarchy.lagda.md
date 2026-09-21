<!--en-->
# The cumulative hierarchy

Every model of the language of set theory needs a carrier of "sets" together with an equality and a membership, both valued in propositions. This chapter builds that carrier. It is the cumulative hierarchy `V`{.Agda}, a higher inductive type built on the oldest idea in set theory, that a set is nothing over and above its members. The type takes the idea literally. Every set is presented by a family of sets indexed by a small type, one member for each index, and to be a member of it is just to have an index of that family that hits the element. Two presentations with the same members present the same set, so extensionality is not an axiom this model has to demand but the way the type is constructed.

On this carrier the chapter then builds the structure `𝒮ᵥ`{.Agda} and proves the first set-theoretic properties, from extensionality to a recursion principle along membership. The hierarchy natively supplies what a structure asks for: equality between sets is the path type, proposition-valued because the hierarchy is an h-set, and membership is the hierarchy's own `∈`, already valued in `hProp`{.Agda}. One universe level `ℓ` is fixed once, and every construction in the chapter is stated at that level.
<!--zh-->
# 累积层级

集合论语言的每个模型都需要一个由「集合」组成的载体，连同取值于命题的等词与成员关系。本章构造这个载体。它就是累积层级 `V`{.Agda}，一个高阶归纳类型，体现的是集合论最古老的观念：集合不外乎其成员的汇集。这个类型把观念不折不扣地体现了出来。每个集合都由一个以小类型为索引的集合族呈现，每个索引对应一个成员；属于它，无非是拥有该族中一个命中此元素的索引。成员相同的两种呈现给出的是同一个集合，因此外延性不是这个模型有待要求的公理，而是类型构造的方式本身。

本章在这个载体上建立结构 `𝒮ᵥ`{.Agda}，并证明最早的一批集合论性质，从外延性直到沿成员关系的递归原理。层级原生地供给了结构所要求的一切：集合之间的等词就是路径类型，因层级是 h-集合而为命题值；成员关系取层级自身的 `∈`，本就取值于 `hProp`{.Agda}。本章固定一个宇宙层级 `ℓ`，全章所有构造都在该层级上陈述。
<!--ja-->
# 累積階層

集合論の言語のモデルにはどれも、「集合」からなる台と、命題に値を持つ等号と所属関係が要る。本章はその台を構成する。累積階層 `V`{.Agda} は高階帰納型であり、土台にあるのは集合論最古の考え、すなわち集合とはその要素の集まりにほかならないというものである。この型はこの考えをそのまま形にする。すべての集合は、小さな型をインデックスとする集合の族によって表示され、各インデックスが一つの要素に対応する。ある集合の要素であるとは、その族のどれかのインデックスがその要素に命中することにほかならない。同じ要素を持つ二つの表示は同じ集合を表示する。したがって外延性は、このモデルが要求すべき公理ではなく、型の構成のされ方そのものなのである。

本章はこの台の上に構造 `𝒮ᵥ`{.Agda} を組み立て、外延性から所属関係に沿う再帰原理まで、集合論の最初の性質を証明する。構造の求めるものは、階層が本来の形で供給する。集合の間の等号はパス型であり、階層が h-集合であるため命題値になる。所属関係は階層本来の `∈` で、はじめから `hProp`{.Agda} に値を取る。本章は宇宙レベル `ℓ` を一度だけ固定し、全章の構成をこのレベルで述べる。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude

module V.Hierarchy {ℓ : Level} where

open import FOL.ZFStructure using ( ZFStructure; module hPropStructure )
```

<!--en-->
Two ideas carry the hardest proof of the chapter. The first is propositional truncation. The statement "some index does the job" is kept as a mere existence, with no chosen witness, and a truncated statement may be eliminated only into propositions. The second is accessibility, the inductive data `Acc` that accompanies a well-founded relation: an element is accessible when every step down, from the element to one of its members, lands at an element that is itself accessible. The two fit because membership in the hierarchy is itself truncated. The proof of well-foundedness must turn a merely existing index into an accessibility proof; accessibility is a proposition, and only into propositions may a truncated statement be eliminated.
<!--zh-->
本章最难的证明依赖两个观念。其一是命题截断。「某个索引可行」这类陈述只作为纯粹存在保留，不选定任何见证，而截断后的陈述只能消去到命题。其二是可及性，即伴随良基关系的归纳数据 `Acc`：当一个元素向下的每一步、从该元素到它的某个成员，都落在本身可及的元素上时，这个元素是可及的。二者能配合，是因为层级的成员关系本身就是截断的。良基性的证明必须把一个纯粹存在的索引转换为可及性证明，而可及性正是命题。
<!--ja-->
本章で最も難しい証明を支えるのは、二つの考えである。第一は命題的切り詰めである。「あるインデックスが条件を満たす」という主張は、証人を選ばない純粋な存在として保たれ、切り詰められた主張は命題へしか消去できない。第二は到達可能性である。これは整礎な関係に伴う帰納的データ `Acc` であり、ある要素からその要素の下降の各一歩が、それ自体到達可能な要素に着地するとき、その要素は到達可能である。この二つが噛み合うのは、階層への所属そのものが切り詰められているからである。整礎性の証明は、切り詰められた形でしか存在しないインデックスを、到達可能性の証明へ変えなければならない。到達可能性はまさに命題である。
<!--/-->

```agda

import Cubical.Induction.WellFounded as WellFoundedInduction
open import Cubical.Induction.WellFounded using ( Acc; acc; WellFounded; isPropAcc; wf→x≮x )
open import Cubical.HITs.CumulativeHierarchy.Base
```

<!--en-->
The hierarchy itself deserves a close reading, for everything that follows rests on it. Its constructor `sett`{.Agda} forms, from a small index type and a family into the hierarchy, the set that is the image of that family. Membership `y ∈ sett X ix` is a truncated preimage: it holds when some `i : X` has `ix i ≡ y`, and only so. A path constructor identifies any two `sett` presentations whose members agree, which is extensionality built into the type itself. This type is not defined here; the chapter builds the structure `𝒮ᵥ`{.Agda} on top of it and proves the set-theoretic properties of that structure.
<!--zh-->
层级本身值得细读，此后的一切论证都建立在它之上。其构造子 `sett`{.Agda} 从小索引类型和指向层级的族造出作为该族之像的集合。成员关系 `y ∈ sett X ix` 是截断的原像：当某个 `i : X` 使 `ix i ≡ y` 时成立，而且只以此方式成立。路径构造子把成员一致的任意两个 `sett` 表示视为相等，这是内建于类型本身的外延性。这个类型并非在本章定义；本章在其上构造结构 `𝒮ᵥ`{.Agda}，并证明该结构的集合论性质。
<!--ja-->
まずは階層そのものをじっくり読もう。この後の議論はすべてそれの上に立つ。構成子 `sett`{.Agda} は、小さなインデックス型と階層への族から、その族の像である集合を形作る。所属 `y ∈ sett X ix` は切り詰められた原像であり、`ix i ≡ y` となる `i : X` があるとき、そしてそのときにしか成り立たない。パス構成子は、要素の一致する任意の二つの `sett` 表示を同一視する。これは型そのものに組み込まれた外延性である。この型がここで定義されるのではなく、本章はその上に構造 `𝒮ᵥ`{.Agda} を組み立て、その構造の集合論的性質を証明する。
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

The generating idea is the oldest one in set theory: a set is no more than the collection of its members. The type turns the idea into data with two restrictions worth noting. Index types must be small, of the form `X : Type ℓ`, so every set is assembled from `ℓ`-small data; and the whole type is an h-set by `setIsSet`{.Agda}, so that however presentations are identified, no distinguishable structure remains between the results.

## The structure

The packaging question is what the structure record asks for, and the answer here is that the hierarchy already has all of it. A carrier of sets: `V ℓ` supplies one, and its h-set condition is not an extra requirement but a fact the hierarchy proves of itself. An equality valued in propositions: paths between elements of an h-set form a proposition, so the path type qualifies. A membership valued in propositions: the hierarchy's own `∈` already lands in `hProp`{.Agda}. Nothing has to be manufactured; the fields assemble into the structure `𝒮ᵥ`{.Agda}, on which the first-order language is interpreted. The subscript is a plain `v`, for the hierarchy.
<!--zh-->
## 高阶归纳类型

其基本思想是集合论中最古老的表述：集合不外乎其成员的汇集。这个类型把思想落实为数据，并带有两点值得注意的约束。索引类型必须小，形如 `X : Type ℓ`，因此每个集合都由大小为 `ℓ` 的数据组装而成；整个类型经 `setIsSet`{.Agda} 而成为 h-集合，因此无论呈现如何被同一化，结果之间都不残留可区分的结构。

## 结构

要把层级视为一阶结构，需要给出 record 所列的各项数据；层级本身已经具备这些数据。要有一个由集合组成的载体：`V ℓ` 供给了它，而且 h-集合性不是额外要求，而是层级自证的事实。要有取命题值的等词：h-集合的元素之间的路径构成命题，路径类型即可充任。要有取命题值的成员关系：层级自身的 `∈` 本就落在 `hProp`{.Agda} 中。无须另造任何部分，这些字段组装成结构 `𝒮ᵥ`{.Agda}，一阶语言就在其上解释。下标就是普通的 `v`，指层级。
<!--ja-->
## 高階帰納型

基本となる考えは集合論で最も古いものである。集合とはその要素の集まりにほからない。この型はこの考えをデータとして実現し、注意すべき制約を二つ伴う。インデックス型は小さくなければならず、`X : Type ℓ` の形をする。したがって各集合は大きさ `ℓ` のデータから組み立てられる。また、型全体は `setIsSet`{.Agda} によって h-集合なので、表示がどう同一視されようと、結果のあいだにはそれ以上の区別できる構造は残らない。

## 構造

構成で問うのは、構造の record が何を要求するかである。ここでの答えは、階層がすでにそのすべてを備えている、というものである。集合からなる台としては `V ℓ` があり、h-集合性は追加の要件ではなく、階層がみずから証明する事実である。命題に値を持つ等号としては、h-集合の要素の間のパスが命題をなすので、パス型がそれになる。命題に値を持つ所属関係としては、階層本来の `∈` がはじめから `hProp`{.Agda} にある。新たに作るべきものは何もなく、これらのフィールドが構造 `𝒮ᵥ`{.Agda} に組み上がり、一階の言語はこの構造の上で解釈される。添字は階層を指す普通の `v` である。
<!--/-->

<!--en-->
The equality field makes the choice explicit: `_≈ˢ_` sends `x` and `y` to the pair of the path type `x ≡ y` and the proof `setIsSet x y` that this type is a proposition, which is exactly the shape of an element of `hProp (ℓ-suc ℓ)`. The same h-set theorem has two roles in the structure: `setIsSet` supplies the field `isSetS`, while `setIsSet x y` proves that the path type used for equality is a proposition. The paths themselves need no conversion: for an h-set, the type of paths between two elements already is a proposition, and the field simply records that type together with the certificate it comes with.
<!--zh-->
等词字段把这个选择写得很明确：`_≈ˢ_` 把 `x` 与 `y` 送到由路径类型 `x ≡ y` 与「该类型是命题」的证明 `setIsSet x y` 组成的对，而这正是 `hProp (ℓ-suc ℓ)` 中元素的形状。同一条 h-集合性定理在结构中承担两项作用：`setIsSet` 充任字段 `isSetS`，`setIsSet x y` 则证明用作等词的路径类型是命题。路径本身无须任何转换：对 h-集合而言，两个元素之间的路径类型本来就是命题，字段只是把这个类型连同它所附带的证书一起记录下来。
<!--ja-->
等号のフィールドはこの選択を明示する。`_≈ˢ_` は `x` と `y` を、パス型 `x ≡ y` と「この型が命題である」ことの証明 `setIsSet x y` の対へ送る。これは `hProp (ℓ-suc ℓ)` の要素の形そのものである。同じ h-集合性の定理は、構造の中で二つの役割を持つ。`setIsSet` はフィールド `isSetS` を与え、`setIsSet x y` は等号として用いるパス型が命題であることを証明する。パスそのものを変換する必要はない。h-集合に対しては、二つの要素の間のパス型はもともと命題であり、フィールドはその型を、それに伴う証明とともに記録しているだけである。
<!--/-->

```agda
𝒮ᵥ : ZFStructure (ℓ-suc ℓ)
𝒮ᵥ = record
  { S      = V ℓ
  ; isSetS = setIsSet
  ; _≈ˢ_   = λ x y → (x ≡ y) , setIsSet x y
```

<!--en-->
The membership field `_∈ˢ_` is simply the hierarchy's own `∈`, whose value at each pair is already an element of `hProp (ℓ-suc ℓ)`. Since the structure's relations are proposition-valued, many later arguments need the underlying type of a proposition rather than the proposition itself. Opening `hPropStructure 𝒮ᵥ` provides that reading: `x ∈ᵗ y` names the type `⟨ x ∈ˢ y ⟩` of inhabitants of the membership proposition. They are the same relation read two ways, `∈ˢ` giving the proposition and `∈ᵗ` its underlying type. Well-foundedness and induction will be stated for this reading.
<!--zh-->
成员关系字段 `_∈ˢ_` 就是层级自身的 `∈`，它在每一对上的取值本来就在 `hProp (ℓ-suc ℓ)` 之中。由于结构的关系都是命题值，后文许多论证需要的是命题的底层类型，而不是命题本身。打开 `hPropStructure 𝒮ᵥ` 即可得到这一读法：`x ∈ᵗ y` 指成员命题的元素所构成的类型 `⟨ x ∈ˢ y ⟩`。二者是同一条关系的两种读法，`∈ˢ` 给出命题，`∈ᵗ` 给出其底层类型。良基性与归纳就建立在这个读法之上。
<!--ja-->
所属関係のフィールド `_∈ˢ_` は階層本来の `∈` そのものであり、各対での値ははじめから `hProp (ℓ-suc ℓ)` の中にある。構造の関係は命題値なので、以後の多くの議論では、命題そのものではなくその基礎型が必要になる。`hPropStructure 𝒮ᵥ` を開くと、この読み方が `x ∈ᵗ y` として得られる。これは所属命題の要素のなす型 `⟨ x ∈ˢ y ⟩` を表す。両者は同じ関係の二つの読み方で、`∈ˢ` が命題を、`∈ᵗ` がその基礎型を与える。後の整礎性と帰納は、この読みの上に築かれる。
<!--/-->

```agda
  ; _∈ˢ_   = _∈_ }

open hPropStructure 𝒮ᵥ
```

<!--en-->
Before the proofs begin, one feature of the levels deserves comment. The carrier `V ℓ` lives in `Type (ℓ-suc ℓ)`, one universe above its index types, and the values of the relations live in `hProp (ℓ-suc ℓ)` alongside it: the hierarchy is a large type built from small indexing data. A small membership `∈ₛ`, connected to the large one by `∈∈ₛ`{.Agda}, will reappear in the proofs below.

## Extensionality and well-founded membership

Suppose two sets `a` and `b` agree at every point: for each `x`, there is a path between the propositions `x ∈ a` and `x ∈ b`. Then any member of `a` transports along that path to a member of `b`, and conversely, so `a` and `b` mutually include each other. The library's `extensionality`{.Agda} turns exactly this mutual inclusion into a path `a ≡ b`, and `subst`{.Agda} carries membership along the pointwise paths to produce it. Extensionality for the hierarchy is thus a consequence of its definition, not an additional assumption.
<!--zh-->
在证明开始之前，先看清层级的位置。载体 `V ℓ` 住在 `Type (ℓ-suc ℓ)`，比它的索引类型高一个宇宙，关系的取值也随之住在同层的 `hProp (ℓ-suc ℓ)` 中：层级是由小索引数据造出的大类型。经 `∈∈ₛ`{.Agda} 与大成员关系相连的小成员关系 `∈ₛ` 在下文的证明中会再次出现。

## 外延性与成员关系的良基性

假设两个集合 `a` 与 `b` 在每一点上一致：对每个 `x`，命题 `x ∈ a` 与 `x ∈ b` 之间有路径。那么 `a` 的任何成员沿该路径可搬运为 `b` 的成员，反之亦然，于是 `a` 与 `b` 互相包含。库的 `extensionality`{.Agda} 正是把这种双向包含转化为路径 `a ≡ b`，而 `subst`{.Agda} 沿逐点路径搬运成员资格来完成转化。层级的外延性因此是其定义的推论，而非额外假设。
<!--ja-->
証明を始める前に、階層の位置を一度見ておこう。台 `V ℓ` は `Type (ℓ-suc ℓ)` に住み、そのインデックス型より一つ上の宇宙にあり、関係の値もそれに並んで `hProp (ℓ-suc ℓ)` に住む。階層は小さなインデックスデータから作られた大きな型である。`∈∈ₛ`{.Agda} によって大きな所属関係と結ばれる小さな所属関係 `∈ₛ` は、この後の証明にも現れる。

## 外延性と所属関係の整礎性

二つの集合 `a` と `b` が各点で一致すると仮定する。つまり各 `x` に対して、命題 `x ∈ a` と `x ∈ b` の間のパスがあるとする。すると `a` の任意の要素はそのパスに沿って `b` の要素へ輸送でき、その逆もできるので、`a` と `b` は互いを包含する。ライブラリの `extensionality`{.Agda} はまさにこの相互包含をパス `a ≡ b` へ変換し、`subst`{.Agda} が各点のパスに沿って所属を輸送することでそれを作る。階層の外延性はしたがって追加の仮定ではなく、その定義の帰結である。
<!--/-->

```agda
extensionalV : {a b : V ℓ} → ((x : V ℓ) → (x ∈ a) ≡ (x ∈ b)) → a ≡ b
extensionalV {a} {b} h = extensionality a b
  ( (λ x x∈ₛa → ∈∈ₛ {a = x} {b = b} .fst
      (subst ⟨_⟩ (h x) (∈∈ₛ {a = x} {b = a} .snd x∈ₛa)))
  , (λ x x∈ₛb → ∈∈ₛ {a = x} {b = a} .fst
```

<!--en-->
The hypothesis `h` gives, for every `x`, a path between the propositions `x ∈ a` and `x ∈ b`; the goal is the path `a ≡ b`. The library's `extensionality` expects small membership, so the proof runs through the bridge `∈∈ₛ` in one direction. An input `x∈ₛa` is a small membership of `x` in `a`. Its conversion `∈∈ₛ .snd x∈ₛa` goes from small to large, producing an inhabitant of `x ∈ a`. Then `subst ⟨_⟩ (h x)` transports that inhabitant along the pointwise path, and since `h x` says the two membership propositions agree at `x`, the transported value inhabits `x ∈ b`. Finally `∈∈ₛ .fst` converts back from large to small, yielding a small membership of `x` in `b`. That is the forward component of the mutual inclusion that `extensionality` takes as input.
<!--zh-->
假设 `h` 对每个 `x` 给出命题 `x ∈ a` 与 `x ∈ b` 之间的路径；目标是路径 `a ≡ b`。库的 `extensionality` 期望小成员关系，因此证明经桥 `∈∈ₛ` 走一个方向。输入 `x∈ₛa` 是 `x` 属于 `a` 的小成员关系。其转换 `∈∈ₛ .snd x∈ₛa` 从小到大，产出 `x ∈ a` 的一个元素。然后 `subst ⟨_⟩ (h x)` 沿逐点路径搬运该元素；由于 `h x` 说两条成员命题在 `x` 处一致，搬运后的值落在 `x ∈ b` 中。最后 `∈∈ₛ .fst` 从大到小转回，得到 `x` 属于 `b` 的小成员关系。这正是 `extensionality` 所需双向包含的向前分量。
<!--ja-->
仮定 `h` は、各 `x` に対して命題 `x ∈ a` と `x ∈ b` の間のパスを与える。目標はパス `a ≡ b` である。ライブラリの `extensionality` は小さな所属関係を期待するので、証明は橋 `∈∈ₛ` を一方向に通る。入力 `x∈ₛa` は `x` の `a` への小所属関係である。その変換 `∈∈ₛ .snd x∈ₛa` は小から大へ向かい、`x ∈ a` の要素を生成する。次に `subst ⟨_⟩ (h x)` がその要素を各点のパスに沿って輸送する。`h x` は二つの所属命題が `x` で一致することを言うので、輸送された値は `x ∈ b` に住む。最後に `∈∈ₛ .fst` が大から小へ戻し、`x` の `b` への小所属関係が得られる。これが `extensionality` が入力として受け取る相互包含の前方の成分である。
<!--/-->

```agda
      (subst ⟨_⟩ (sym (h x)) (∈∈ₛ {a = x} {b = b} .snd x∈ₛb))) )
```

<!--en-->
The second component is the same run of the bridge in reverse: a small membership of `x` in `b` is converted to large, transported backward along `sym (h x)`, and converted back to a small membership of `x` in `a`. Together the two components form the mutual inclusion from which `extensionality` produces `a ≡ b`, the path `extensionalV` returns.

(The `∈ₛ` appearing through `∈∈ₛ`{.Agda} is the library's *small* membership; the chapter "Small presentations of sets" discusses it in detail. Here it serves only to connect the two.)

Regularity, in this development, is the statement that membership is well-founded: every element of the carrier is accessible under `∈ᵗ`, in the sense of the accessibility data `Acc` introduced above. The proof eliminates the higher inductive type into the family `λ s → Acc _∈ᵗ_ s`. Elimination into an arbitrary family is not always available; what makes it legitimate here is that each `Acc _∈ᵗ_ s` is a proposition, and `isPropAcc s` supplies precisely that certificate. In the `sett` case, the branch receives the family `ix` and an induction hypothesis `rec i : Acc _∈ᵗ_ (ix i)` for every index. It must assemble `Acc _∈ᵗ_ (sett X ix)`, which by the shape of `acc` amounts to providing accessibility for an arbitrary member `y` of the set.
<!--zh-->
第二个分量是把桥反向走一遍：`x` 属于 `b` 的小成员关系先转为大，再沿 `sym (h x)` 反向搬运，最后转回 `x` 属于 `a` 的小成员关系。两个分量合起来构成双向包含，`extensionality` 由此得到 `a ≡ b`，即 `extensionalV` 返回的路径。

(经 `∈∈ₛ`{.Agda} 现身的 `∈ₛ` 是库的**小**成员关系，「集合的小呈现」一章将细说；此处它只起衔接作用。)

在本书中，正则公理即是「成员关系良基」这一陈述：载体的每个元素在 `∈ᵗ` 下都可及，含义即上文引入的可及性数据 `Acc`。证明把该高阶归纳类型消去到族 `λ s → Acc _∈ᵗ_ s`。向任意族的消去并非总是可用；使这里合法的，是每个 `Acc _∈ᵗ_ s` 都是命题，而 `isPropAcc s` 恰好给出这份证书。在 `sett` 情形中，分支拿到族 `ix`，以及对每个索引给出 `rec i : Acc _∈ᵗ_ (ix i)` 的归纳假设。它要组装 `Acc _∈ᵗ_ (sett X ix)`；按 `acc` 的形状，这就是要对集合的任意成员 `y` 给出可及性。
<!--ja-->
第二の成分は、同じ橋を逆向きに通るものである。`x` の `b` への小所属関係を大へ変換し、`sym (h x)` に沿って逆方向へ輸送し、`x` の `a` への小所属関係へ戻す。二つの成分が合わさって相互包含が得られ、`extensionality` はそこから `a ≡ b` を作る。これが `extensionalV` が返すパスである。

(`∈∈ₛ`{.Agda} を通して現れる `∈ₛ` はライブラリの**小さな**所属関係であり、「集合の小さな提示」の章で詳しく述べる。ここでは両者を結ぶ役割だけを果たす。)

本書における正則性は、所属関係が整礎であるという主張である。すなわち、台のすべての要素が `∈ᵗ` の下で到達可能である、というものである。その意味は、上で導入した到達可能性のデータ `Acc` にある。証明は、この高階帰納型を族 `λ s → Acc _∈ᵗ_ s` へ消去することによって進む。任意の族への消去はいつでもできるわけではなく、ここでそれが許されるのは、各 `Acc _∈ᵗ_ s` が命題であり、`isPropAcc s` がまさにその証明を与えるからである。`sett` の場合、分岐は族 `ix` と、各インデックスについて `rec i : Acc _∈ᵗ_ (ix i)` を与える帰納仮定を受け取る。組み立てるべきは `Acc _∈ᵗ_ (sett X ix)` であり、`acc` の形から、これは集合の任意の要素 `y` に対する到達可能性を与えることにほかならない。
<!--/-->

```agda
regularityV : WellFounded _∈ᵗ_
regularityV = elimProp (λ s → isPropAcc s)
  (λ X ix rec → acc (λ y y∈ →
    rec₁ (isPropAcc y)
           (λ { (i , p) → subst (Acc _∈ᵗ_) p (rec i) })
```

<!--en-->
For such a member `y`, the witness `y∈` gives only the propositional truncation of a pair `(i , p)` with `p : ix i ≡ y`. The call `rec₁ (isPropAcc y)` may eliminate this truncated preimage because its actual target, `Acc _∈ᵗ_ y`, is a proposition, as certified by `isPropAcc y`. Inside the branch, `subst (Acc _∈ᵗ_) p (rec i)` transports the induction hypothesis from `ix i` to `y`. The proof thus uses the index without ever choosing one globally.
<!--zh-->
对这样的成员 `y`，证据 `y∈` 只给出一对 `(i , p)` 的命题截断，其中 `p : ix i ≡ y`。调用 `rec₁ (isPropAcc y)` 可以消去这个截断原像，因为真正的目标 `Acc _∈ᵗ_ y` 是命题，而 `isPropAcc y` 正是它的命题性证书。在分支内部，`subst (Acc _∈ᵗ_) p (rec i)` 把归纳假设从 `ix i` 搬运到 `y`。整个证明由此用到索引，却从未全局选定一个索引。
<!--ja-->
このような要素 `y` に対し、証拠 `y∈` が与えるのは、`p : ix i ≡ y` を持つ対 `(i , p)` の命題的切り詰めだけである。`rec₁ (isPropAcc y)` がこの切り詰められた原像を消去できるのは、実際の目標 `Acc _∈ᵗ_ y` が命題であり、`isPropAcc y` がその命題性を証明するからである。分岐の中では `subst (Acc _∈ᵗ_) p (rec i)` が帰納仮定を `ix i` から `y` へ輸送する。証明全体として、インデックスは使われるが、大域的に一つを選ぶことはない。
<!--/-->

```agda
           y∈))
```

<!--en-->
The first consequence of regularity is irreflexivity: no set belongs to itself. In terms of accessibility this is immediate. An element standing in a well-founded relation to itself would contradict the accessibility data, which requires every step down to land at an accessible element. The derivation uses the `Acc` statement proved above; it is not claimed here to capture every classical formulation of Foundation.

The hypothesis `⟨ A ∈ˢ A ⟩` is an inhabitant of the underlying type of the membership proposition, which is precisely the relation `∈ᵗ` on which `regularityV` was proved. For any well-founded relation, no element can stand in the relation to itself: this is the library's irreflexivity theorem `wf→x≮x`, applied here with `regularityV` as its well-foundedness input. The result is a contradiction, witnessed by the empty type `⊥₀`.
<!--zh-->
正则公理的第一个推论是不可反性：没有集合属于自身。用可及性的语言看，这是直接的。与自身处于良基关系中的元素会同可及性数据矛盾，因为可及性要求每一步下降都落在可及的元素上。这里的推导使用的是上文证明的 `Acc` 陈述；本章不宣称它涵盖 Foundation 的每一个经典表述。

假设 `⟨ A ∈ˢ A ⟩` 是成员命题底层类型的一个元素，而这正是 `regularityV` 所针对的关系 `∈ᵗ`。对任何良基关系，元素都不能与自身处于该关系中：这就是库的不可反性定理 `wf→x≮x`，此处以 `regularityV` 作为其良基性输入。结果是矛盾，以空类型 `⊥₀` 呈现。
<!--ja-->
正則性の最初の帰結は非反射性である。集合は自分自身に属しない。到達可能性の言葉で言えば、これはすぐに分かる。自分自身と整礎な関係に立つ要素は、到達可能性のデータと矛盾する。下降の各一歩が到達可能な要素に着地することを、到達可能性は要求するからである。ここでの導出は、上で証明した `Acc` の主張を使うものであり、Foundation のすべての古典的定式化を捉えると主張するものではない。

仮定 `⟨ A ∈ˢ A ⟩` は、所属命題の基礎型の要素であり、これは `regularityV` が証明された関係 `∈ᵗ` そのものである。整礎な関係に対しては、どの要素も自分自身とその関係に立つことはできない。これがライブラリの非反射性の定理 `wf→x≮x` であり、ここでは `regularityV` を整礎性の入力として適用する。結果は矛盾であり、空の型 `⊥₀` がそれを示す。
<!--/-->

```agda
∈-irrefl : (A : S) → ⟨ A ∈ˢ A ⟩ → ⊥₀
∈-irrefl A = wf→x≮x regularityV {x = A}
```

<!--en-->
## Recursion on membership

Well-foundedness has a computational payoff: a well-founded relation supports recursion. A value at `x` may depend on the values at every member `y` of `x`, and this dependence terminates because membership is well-founded. The target may be an arbitrary dependent type family `P`, not merely a proposition, which is what makes this a recursion principle rather than a proof principle. This is the type-theoretic form of recursion along membership, stated without an ordinal-indexed hierarchy: instead of recursing along stage indices, one recurses directly along the membership relation. Its recursion equation also holds as a propositional equality, so later arguments can compute with it.
<!--zh-->
## 沿成员关系的递归

良基性有计算上的回报：良基关系支持递归。`x` 处的值可以依赖于 `x` 的每个成员 `y` 处的值，而由于成员关系良基，这种依赖必然终止。目标可以是任意的依赖类型族 `P`，而不限于命题；这使它成为递归原理而非仅仅是证明原理。这是沿成员关系的递归在类型论中的形态，且不以序数索引的层级来陈述：不是沿层指标递归，而是直接沿成员关系本身递归。其递归方程还以命题等式成立，故后续论证可据以计算。
<!--ja-->
## 所属関係上の再帰

整礎性には計算上の見返りがある。整礎な関係は再帰を支えるのである。具体的には、`x` での値は `x` の各要素 `y` での値に依存でき、所属関係が整礎であるためこの依存は必ず停止する。対象は命題に限らず任意の依存型族 `P` でよく、これがこの原理を証明原理にとどまらない再帰原理にしている。これは所属関係に沿う再帰の型論的形態であり、序数で添字付けられた階層を介さずに述べられる。段階の添字に沿って再帰するのではなく、所属関係そのものに沿って再帰するのである。再帰方程式も命題としての等式で成り立つため、後の議論はそれを頼りに計算できる。
<!--/-->

<!--en-->
Read the type of `∈-induction` from the outside in. The family `P` assigns to each set a type in an arbitrary universe `Type ℓ'`, so the value being constructed may genuinely vary with the set. The step function `e` receives a set `x` together with recursive values `P y` for every member `y` of `x`, where membership appears through `∈ᵗ`, the Type-valued reading of the membership proposition, and returns `P x`. What justifies the definition is `regularityV`: the library's `WFI.induction`, instantiated at this well-founded relation, converts the step function into a total family. No fresh proof of well-foundedness is needed.
<!--zh-->
从外向内读 `∈-induction` 的类型。类型族 `P` 给每个集合指派任意宇宙 `Type ℓ'` 中的一个类型，因此被构造的值可以真正随集合变化。步进函数 `e` 接收集合 `x`，以及 `x` 的每个成员 `y` 处的递归值 `P y`，成员关系经由成员命题的 Type 值读法 `∈ᵗ` 出现，并返回 `P x`。为这一构造提供依据的是 `regularityV`：库的 `WFI.induction` 在这条良基关系上实例化，把步进函数变为全定义的族。此处无需重新证明良基性。
<!--ja-->
`∈-induction` の型は外から内へ読む。型族 `P` は各集合に対して任意の宇宙 `Type ℓ'` の型を割り当てるので、構成される値は集合とともに実際に変わりえる。ステップ関数 `e` は集合 `x` と、`x` の各要素 `y` での再帰的な値 `P y` を受け取る。所属関係は所属命題を Type として読む `∈ᵗ` を通して現れる。そして `P x` を返す。この定義を正当化するのは `regularityV` である。ライブラリの `WFI.induction` をこの整礎な関係で実例化すれば、ステップ関数が全域の族へ変わる。ここで整礎性を改めて証明する必要はない。
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
計算法則は、各要素での再帰呼び出しを定義の内側に隠さず、等式として示す。すなわち `∈-induction e x` は、ステップ関数を `x` と各要素 `y` での `∈-induction e y` に適用したものに等しい、ということである。この等式は命題としての等式として述べられており、定義的に成り立つとは限らない。それを明示しておけば、簡約が定義的でない場合でも、後の証明はこの等式によって再帰的に定義された値を書き換えられる。この法則はライブラリの `WFI.induction-compute` であり、任意の整礎な関係に対して証明され、ここでは所属関係に実例化されている。
<!--/-->

```agda
  (e : ∀ x → (∀ y → y ∈ᵗ x → P y) → P x) (x : V ℓ)
  → ∈-induction e x ≡ e x (λ y _ → ∈-induction e y)
∈-induction-compute = WellFoundedInduction.WFI.induction-compute regularityV
```

<!--en-->
## Recap

The hierarchy `V`{.Agda} is a higher inductive type in which sets are images of small families and the whole type is an h-set; packaged as the structure `𝒮ᵥ`{.Agda}, it carries the path type as equality and the native membership as membership, both proposition-valued. Extensionality (`extensionalV`{.Agda}) follows from the extensional path constructor via the small-membership bridge, and well-foundedness of membership (`regularityV`{.Agda}) follows by elimination into accessibility. Well-foundedness in turn yields irreflexivity and the recursion principle `∈-induction` with its computation law `∈-induction-compute`. The small membership `∈ₛ` and its bridge to `∈` are taken up in the chapter "Small presentations of sets".
<!--zh-->
## 小结

层级 `V`{.Agda} 是一个高阶归纳类型：集合是小族的像，整个类型是 h-集合。构成结构 `𝒮ᵥ`{.Agda} 后，它以路径类型为等词、以原生 `∈` 为成员关系，二者都是命题值。外延性 (`extensionalV`{.Agda}) 经小成员关系桥从外延路径构造子得到，成员关系的良基性 (`regularityV`{.Agda}) 由消去到可及性得到。良基性又给出不可反性，以及递归原理 `∈-induction` 及其计算法则 `∈-induction-compute`。小成员关系 `∈ₛ` 及其与 `∈` 的桥接，将在「集合的小呈现」一章处理。
<!--ja-->
## まとめ

階層 `V`{.Agda} は高階帰納型であり、集合は小さな族の像で、型全体は h-集合である。構造 `𝒮ᵥ`{.Agda} に組み上げると、等号にはパス型が、所属関係には本来の `∈` が入る。どちらも命題値である。外延性 (`extensionalV`{.Agda}) は小所属関係の橋を経て外延的なパス構成子から、所属関係の整礎性 (`regularityV`{.Agda}) は到達可能性への消去から従う。整礎性はさらに非反射性と、再帰原理 `∈-induction` とその計算法則 `∈-induction-compute` をもたらする。小さな所属関係 `∈ₛ` とその `∈` への橋は、「集合の小さな提示」の章で扱われる。
<!--/-->
