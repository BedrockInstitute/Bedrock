<!--en-->
# Ordinal closure and finite ordinals

Ordinals are transitive sets whose members are transitive. This chapter proves closure under zero, successor, and unions, constructs ordinal bounds for small families, and identifies membership among the finite numerals and `ω`.

The chapter develops these closure and bounding tools before turning to finite ordinals. Zero is an ordinal; successors of ordinals are ordinals; a union of ordinals is an ordinal; and, as the chapter's main result, every small family of ordinals lies below a single ordinal. That last statement turns "each member of a small family has *some* ordinal bound" into "the whole family shares *one* ordinal bound", a form used later in separation, power set, recursion, reflection, and GCH constructions.

This chapter does not give comparison of ordinals. Ordinals are indeed linearly ordered, but that fact is not constructive and it is not needed here: the axioms ask only for a common bound, so the book constructs a common bound directly. None of the closure or bounding proofs in this chapter assumes classical logic.
<!--zh-->
# 序数的封闭性与有限序数

序数是其成员也都传递的传递集。本章证明序数对零、后继与并封闭，为小族构造序数上界，并刻画有限数码之间及其与 `ω` 的隶属关系。

本章先建立这些封闭与取界工具，再转向有限序数。零是序数；序数的后继是序数；序数之并是序数；以及本章的主要结果：任一小族序数都落在单一序数之下。最后这条把「小族的每个成员**各有**序数上界」变成「整个小族共用**同一**序数上界」；后面的分离、幂集、递归、反射与 GCH 构造都会使用这种形式。

本章没有给出序数的比较。序数确实构成线序，但该事实不是构造性的，而且此处也不需要它：这些公理只要求公共上界，因此本书在这里直接构造公共上界。本章的封闭与取界证明都不假设经典逻辑。
<!--ja-->
# 順序数の閉性と有限順序数

順序数は、その要素も推移的である推移的集合です。本章では零、後続、和集合に関する閉性を示し、小さな族の順序数上界を構成し、有限数項の間および `ω` との所属関係を特徴付けます。

本章では、これらの閉性と上界構成を整えた後、有限順序数を扱います。零は順序数であり、順序数の後続は順序数であり、順序数の和集合は順序数であり、そして本章の主結果として、小さな順序数の族は必ず単一の順序数の下に収まります。最後の命題は、「小さな族の各要素が**それぞれ**順序数上界を持つ」ことを「族全体が**同一の**順序数上界を共有する」ことへ変えます。この形は後の分離、冪集合、再帰、反映、GCH の構成で使われます。

本章は順序数の比較を与えません。順序数が実際に線形に整列していることは事実ですが、その事実は構成的ではなく、ここでは必要でもありません。公理が求めるのは共通の上界だけなので、本書は共通の上界を直接構成します。本章の閉性と上界の証明には古典論理の仮定は現れません。
<!--/-->

<!--en-->
The ordinal predicate is defined in the constructible-universe chapter as `IsOrd A = isTransV A × ((x : S) → ⟨ x ∈ˢ A ⟩ → isTransV x)`: a pair of a transitivity proof and a proof that every member of `A` is itself transitive. Both components are propositions, and `isPropIsOrd` certifies this, so `IsOrd` is a genuine truth value rather than structure-bearing data. The module fixes an ambient universe level `ℓ` and works with the carrier `S` of the cumulative hierarchy over it.
<!--zh-->
序数谓词在可构造宇宙一章中定义为 `IsOrd A = isTransV A × ((x : S) → ⟨ x ∈ˢ A ⟩ → isTransV x)`：它是传递性证明与「`A` 的每个成员自身传递」之证明的序对。两个分量都是命题，`isPropIsOrd` 证明了这一点，因此 `IsOrd` 是真正的真值，而不是携带结构的数据。本模块固定周遭宇宙层级 `ℓ`，并在其上的累积层级载体 `S` 中工作。
<!--ja-->
順序数述語は構成可能宇宙の章で `IsOrd A = isTransV A × ((x : S) → ⟨ x ∈ˢ A ⟩ → isTransV x)` と定義されます。これは推移性の証明と「`A` の各要素がそれ自身推移的である」ことの証明との対です。両成分はともに命題であり、`isPropIsOrd` がそれを保証するので、`IsOrd` は構造を追加するデータではなく、命題値です。このモジュールは周囲の宇宙レベル `ℓ` を固定し、その上の累積階層の台 `S` の中で働きます。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth

module L.Ordinal {ℓ : Level} where

open import FOL.ZFStructure using ( module hPropStructure )
```

<!--en-->
Two families of tools meet here. From the side of the ambient hierarchy `V` come the successor `sucV`, its membership eliminator, and the union of a small family. From the side of the constructible universe `L` come the transitivity lemma for the empty set and for small unions, and the predicate `IsOrd` itself. Everything in this chapter is proved about the underlying sets; nothing yet refers to constructibility, so no excluded-middle assumption appears in any statement below.
<!--zh-->
这里会合了两套工具。来自周遭层级 `V` 一侧的有后继 `sucV`、其隶属消去子，以及小族之并；来自可构造宇宙 `L` 一侧的有空集与小并的传递性引理，以及谓词 `IsOrd` 本身。本章的全部结论都只涉及底层的集合，尚未触及可构造性，因此下面的任何陈述都不出现排中律假设。
<!--ja-->
ここで二組の道具が出会います。周囲の階層 `V` の側からは、後続 `sucV`、その所属の消去子、そして小さな族の和集合が来ます。構成可能宇宙 `L` の側からは、空集合と小さな和集合に対する推移性の補題、および述語 `IsOrd` そのものが来ます。本章の結果はすべて基礎となる集合についてであり、まだ構成可能性には触れないため、以下のどの主張にも排中律の仮定は現れません。
<!--/-->

```agda
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Model {ℓ} using ( union-family-in; union-family-out; ∈sucV-elim; ∈sucV-inl; self∈sucV )
open import V.Coding {ℓ} using ( #-inj′ )
open import L.Constructible {ℓ}
  using ( isTransV; isPropIsTransV; ∅-trans; setUnion-trans; IsOrd; isPropIsOrd )
```

<!--en-->
A recurring pattern in the proofs is elimination of a truncated witness. Membership in a union is only *merely* witnessed by some index and member, so a fact about all union members is extracted with `PT.rec` into a proposition-valued target. This is why each closure lemma names its target proposition, such as `isPropIsTransV z`, before consuming the truncation: elimination of `∥ A ∥₁` is permitted exactly into such propositions.
<!--zh-->
这些证明中反复出现的模式是截断见证的消去。属于一个并的成员只是**仅仅**由某个指标与某个成员见证，因此关于并之全体成员的事实要用 `PT.rec` 提取到一个命题值的目标中。正因如此，每条闭包引理在消耗截断之前先指明目标命题，例如 `isPropIsTransV z`：`∥ A ∥₁` 的消去恰好允许进入这类命题。
<!--ja-->
これらの証明で繰り返される型は、截断された証人の消去です。和集合への所属は、ある添字とある要素によって**単に (merely)** 証明されるだけなので、和のすべての要素に関する事実は `PT.rec` を用いて命題値の対象へと取り出します。そのため、各閉性補題は截断を消費する前に、`isPropIsTransV z` のような目標の命題を名指します。`∥ A ∥₁` の消去が許されるのは、まさにこのような命題へのときだけだからです。
<!--/-->

```agda

open import Cubical.Data.Nat.Order using ( _<_; ≤-suc; isProp≤ )
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁; squash₁ )
open import Cubical.Data.Bool using ( Bool; true; false )
```

<!--en-->
The numerals `# n` are the von Neumann naturals of the hierarchy: `# 0` is the empty set and `# (suc n)` is the successor of `# n`. Their limit `ω` and the facts that each numeral lies in `ω` come from the infinity construction. The final section of the chapter will read a natural index back out of a membership `z ∈ˢ (# n)`, using that the coding of numerals is injective.
<!--zh-->
数码 `# n` 是层级的冯·诺依曼自然数：`# 0` 是空集，`# (suc n)` 是 `# n` 的后继。它们的极限 `ω`，以及每个数码都属于 `ω`，来自无穷构造。本章最后一节将从隶属关系 `z ∈ˢ (# n)` 中读回一个自然数序号，所用的是数码编码的单射性。
<!--ja-->
数項 `# n` は階層のフォン・ノイマン自然数です。`# 0` は空集合、`# (suc n)` は `# n` の後続です。その極限 `ω` および各数項が `ω` に属することは、無限公理の構成から来ます。本章の最終節では、数項の符号化の単射性を用いて、所属 `z ∈ˢ (# n)` から自然数の添字を読み戻します。
<!--/-->

```agda
open import Cubical.HITs.CumulativeHierarchy.Base using ( sett )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ∈∈ₛ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ∅; ∅-empty; ⋃_; module InfinitySet )
open InfinitySet using ( sucV; #_; ω; #-in-ω )
```

<!--en-->
One last convention: the truth algebra is opened once and for all, so the notation `⟨ P ⟩` for the underlying type of a proposition `P` and the indexed connectives of the hProp algebra are available throughout. The propositions here, such as `isTransV A` and `IsOrd A`, live one level above `ℓ`, which is exactly the level at which the later axioms will quantify.
<!--zh-->
最后一个约定：真值代数在此一次性打开，于是「命题 `P` 的底类型」的记号 `⟨ P ⟩` 与 hProp 代数的索引连接词在全章可用。这里的命题，如 `isTransV A` 与 `IsOrd A`，位于 `ℓ` 之上一层，而这正是稍后公理进行量化的层级。
<!--ja-->
最後の約束として、真理値代数はここで一度だけ開かれ、命題 `P` の台の型を表す記法 `⟨ P ⟩` と hProp 代数の索引付き連結詞が全章を通して使えます。`isTransV A` や `IsOrd A` のようなここでの命題は `ℓ` の一つ上の階層に住み、それはのちの公理が量化を行う階層とちょうど一致します。
<!--/-->

```agda

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ
```

<!--en-->
## Zero and successors

Recall the predicate: an ordinal is a transitive set whose members are all transitive. Both halves are vacuous for the empty set, so zero is an ordinal with nothing to prove.
<!--zh-->
## 零与后继

回忆那个谓词：序数是成员皆传递的传递集。两半对空集都真空成立，于是零是序数，无须证明什么。
<!--ja-->
## 零と後続

述語を思い出しましょう。順序数とは、推移的集合であって、その要素がすべて推移的であるものです。空集合に対しては両方の条件が空虚に成立するので、零は順序数であり、証明すべきことは何もありません。次に、順序数 `A` から後続 `sucV A` が再び順序数であることを示します。
<!--/-->

<!--en-->
The certificate `∅-ord` packages the two vacuous halves. Transitivity of `∅` is the already-proved lemma `∅-trans`. For the second half, the function must accept any `x` with a claimed membership `x ∈ˢ ∅`, but the empty-set lemma converts that membership into an element of the empty host type, which `Empty.rec` eliminates to prove anything at all. A member that cannot exist imposes no obligation.
<!--zh-->
证书 `∅-ord` 把两个真空的半边打包起来。`∅` 的传递性用已证的引理 `∅-trans`；对第二半，函数必须接受任何声称有 `x ∈ˢ ∅` 的 `x`，但空集引理把这一隶属转化为空宿主类型中的一个元素，`Empty.rec` 由此证明任何命题。不可能存在的成员不施加任何义务。
<!--ja-->
証明書 `∅-ord` は空虚に成立する二つの半分をまとめたものです。`∅` の推移性には既証の補題 `∅-trans` を使い、第二の半分については、`x ∈ˢ ∅` を主張する任意の `x` を受け取る関数を与えますが、空集合の補題がその所属を空のホスト型の要素へと変換し、`Empty.rec` がそこから任意の命題を証明します。存在し得ない要素は何の義務も課しません。
<!--/-->

```agda
∅-ord : IsOrd ∅
∅-ord = ∅-trans
      , (λ x x∈∅ → Empty.rec (∅-empty x (∈∈ₛ {a = x} {b = ∅} .fst x∈∅)))
```

<!--en-->
The successor `sucV A` adds `A` itself as a member. A member of `sucV A` is either a member of `A` or `A` itself, and that case split is a proposition-level eliminator, `∈sucV-elim`, which requires its target to be a proposition and takes two branches. Both halves of the ordinal predicate follow this eliminator.
<!--zh-->
后继 `sucV A` 把 `A` 自身添作成员。`sucV A` 的成员要么是 `A` 的成员，要么就是 `A` 自身；这个分情形是命题级的消去子 `∈sucV-elim`，它要求目标是命题并接受两个分支。序数谓词的两半都照着这个消去子走。
<!--ja-->
後続 `sucV A` は `A` 自身を要素として加えます。`sucV A` の要素は `A` の要素であるか、`A` 自身であるかのいずれかであり、この場合分けは命題レベルの消去子 `∈sucV-elim` によって行えます。消去子は目標が命題であることを要求し、二つの分岐を受け取ります。順序数述語の両半分は、この消去子に従って証明されます。
<!--/-->

<!--en-->
Transitivity of `sucV A` must show `y ∈ˢ sucV A` from `y ∈ˢ x` and `x ∈ˢ sucV A`. The eliminator consumes `x∈suc`, and the proof obligation it hands to each branch is again a membership in `sucV A`, so the propositionality argument `snd (y ∈ˢ sucV A)` is supplied as the target.
<!--zh-->
`sucV A` 的传递性要从「`y ∈ˢ x` (就 `A` 内部的项而言) 与 `x ∈ˢ sucV A`」推出 `y ∈ˢ sucV A`。消去子消耗 `x∈suc`，它交给每个分支的证明义务又是一个对 `sucV A` 的隶属，因此以命题性论证 `snd (y ∈ˢ sucV A)` 作为目标。
<!--ja-->
`sucV A` の推移性は、`y ∈ˢ x` と `x ∈ˢ sucV A` から `y ∈ˢ sucV A` を出さねばなりません。消去子が `x∈suc` を消費し、各分岐に渡す証明義務は再び `sucV A` への所属であるため、命題性の証明 `snd (y ∈ˢ sucV A)` を目標として渡します。
<!--/-->

```agda
suc-ord : ∀ {A} → IsOrd A → IsOrd (sucV A)
suc-ord {A} (Atr , Amem) = trans-sucV , mem-sucV
  where
  trans-sucV : isTransV (sucV A)
  trans-sucV {x} {y} y∈x x∈suc = ∈sucV-elim (snd (y ∈ˢ sucV A)) x∈suc
```

<!--en-->
In the first branch, `x` is a member of `A`, so `A`'s transitivity applied to `y ∈ˢ x` and `x ∈ˢ A` gives `y ∈ˢ A`, hence `y ∈ˢ sucV A`. In the second branch, `x` is identified with `A` itself, so `y ∈ˢ x` transports along that path directly into `y ∈ˢ A`; no extra fact about `A` is needed there.
<!--zh-->
第一分支中 `x` 是 `A` 的成员，于是把 `A` 的传递性用于 `y ∈ˢ x` 与 `x ∈ˢ A` 得到 `y ∈ˢ A`，进而 `y ∈ˢ sucV A`。第二分支中 `x` 被等同于 `A` 自身，于是 `y ∈ˢ x` 沿这条路径直接传递为 `y ∈ˢ A`；这里无需关于 `A` 的任何额外事实。
<!--ja-->
第一分岐では `x` は `A` の要素なので、`A` の推移性を `y ∈ˢ x` と `x ∈ˢ A` に適用して `y ∈ˢ A`、したがって `y ∈ˢ sucV A` が得られます。第二分岐では `x` は `A` 自身と同一視されるので、`y ∈ˢ x` はそのパスに沿って直接 `y ∈ˢ A` へと輸送され、`A` に関する追加の事実は不要です。
<!--/-->

```agda
    (λ x∈A → ∈sucV-inl (Atr y∈x x∈A))
    (λ x≡A → ∈sucV-inl (subst (λ w → ⟨ y ∈ˢ w ⟩) x≡A y∈x))
  mem-sucV : (x : S) → ⟨ x ∈ˢ sucV A ⟩ → isTransV x
  mem-sucV x x∈suc = ∈sucV-elim (isPropIsTransV x) x∈suc
    (λ x∈A → Amem x x∈A)
```

<!--en-->
The second half, that every member of `sucV A` is transitive, is the same case split with a different target. Members of `A` are transitive by the hypothesis `Amem`; in the branch where `x` equals `A`, the transitivity `Atr` is transported back along the reversed path. The propositionality of `isTransV x` is what makes the eliminator applicable here.
<!--zh-->
第二半，即 `sucV A` 的每个成员都传递，是同一分情形配以不同目标。`A` 的成员由假设 `Amem` 得到传递性；在 `x` 等于 `A` 的分支中，把传递性 `Atr` 沿反向路径传递回去。`isTransV x` 的命题性正是消去子在此适用的原因。
<!--ja-->
第二の半分、すなわち `sucV A` の各要素が推移的であることは、同じ場合分けに異なる目標を合わせたものです。`A` の要素は仮定 `Amem` により推移的であり、`x` が `A` と等しい分岐では、推移性 `Atr` を逆向きのパスに沿って輸送して返します。ここで消去子が適用できるのは `isTransV x` の命題性によるものです。
<!--/-->

```agda
    (λ x≡A → subst isTransV (sym x≡A) Atr)
```

<!--en-->
## Unions and bounds

Ordinals are closed under small-indexed unions. Transitivity is the closure lemma already proved for transitive sets; for the second half, a member of the union sits inside some `f x`, and that family member is an ordinal by hypothesis, so its own members are transitive.
<!--zh-->
## 并与上界

序数对小索引并封闭。传递性就是传递集那边已证的闭包引理；第二半：并的成员落在某个 `f x` 里面，而依假设该族元是序数，故其成员传递。
<!--ja-->
## 和集合と上界

順序数は、小さな添字付けられた族の和集合について閉じています。推移性は、推移的集合に対してすでに証明した閉性補題そのものです。第二の半分については、和集合の要素はある `f x` の内側にあり、仮定によりその族の元は順序数なので、その要素もまた推移的です。
<!--/-->

<!--en-->
The family is given by a small type `X` of indices and a map `f : X → S`, so the union `⋃ (sett X f)` is a set built from an honest function rather than a truncated enumeration. Its transitivity is borrowed directly from `setUnion-trans`, feeding it the first component of each hypothesis `hf x`.
<!--zh-->
族由小的索引类型 `X` 与映射 `f : X → S` 给出，因此并 `⋃ (sett X f)` 是由真实的函数构造的集合，而非截断的枚举。其传递性直接取自 `setUnion-trans`，并喂入各假设 `hf x` 的第一个分量。
<!--ja-->
族は小さな型 `X` の添字と写像 `f : X → S` で与えられるので、和集合 `⋃ (sett X f)` は截断された列挙ではなく実際の関数から構成される集合です。その推移性は `setUnion-trans` から直接借り、仮定 `hf x` の第一成分を渡します。
<!--/-->

```agda
setUnion-ord : (X : Type ℓ) (f : X → S) → ((x : X) → IsOrd (f x))
             → IsOrd (⋃ (sett X f))
setUnion-ord X f hf = setUnion-trans X f (λ x → hf x .fst) , memTr
  where
  memTr : (z : S) → ⟨ z ∈ˢ (⋃ (sett X f)) ⟩ → isTransV z
```

<!--en-->
For the remaining obligation, `union-family-out` states that `z ∈ˢ ⋃ (sett X f)` means merely that `z` lies in some `f x`. Since the goal `isTransV z` is a proposition, `PT.rec` may eliminate that truncation, and in each branch `hf x .snd z hz` supplies exactly the needed certificate: a member of an ordinal family member is transitive.
<!--zh-->
剩下的义务是：`union-family-out` 表明 `z ∈ˢ ⋃ (sett X f)` 仅仅意味着 `z` 落在某个 `f x` 中。由于目标 `isTransV z` 是命题，`PT.rec` 可以消去该截断，而在每个分支中 `hf x .snd z hz` 恰好给出所需证书：序数族元的成员是传递的。
<!--ja-->
残りの義務については、`union-family-out` は `z ∈ˢ ⋃ (sett X f)` が、`z` がある `f x` に属することを**単に (merely)** 意味することを述べます。目標 `isTransV z` は命題なので `PT.rec` がこの截断を消去でき、各分岐では `hf x .snd z hz` がちょうど必要な証明書を与えます。すなわち、順序数である族の元の要素は推移的です。
<!--/-->

```agda
  memTr z z∈⋃ = PT.rec (isPropIsTransV z)
    (λ { (x , hz) → hf x .snd z hz }) (union-family-out X f z z∈⋃)
```

<!--en-->
And the chapter's deliverable. Given a small family of ordinals, a single ordinal contains every member of the family. The naive attempt, take the union of the family, gives only inclusion: a union absorbs its members' *elements*, not the members themselves, and no set contains itself. The repair is one step of successor: union the family of successors instead. The result is a genuine pair, not a truncated existence: the consumers name the bound and form its stage.
<!--zh-->
然后是本章的主要结果。给定一小族序数，有单一序数包含该族的每一个成员。若直接取该族之并，只能得到包含关系：并包含其成员的**元素**，而非这些成员本身，并且没有集合以自身为成员。因此改为对后继族取并。结果明确给出相应的序对，而不只是截断的存在；使用方可以指称这个上界，并构造它所在的层。
<!--ja-->
そして本章の成果物です。小さな順序数の族が与えられると、族のすべての元を含む単一の順序数が得られます。素朴に族の和を取るだけでは包含関係しか得られません。和集合はその要素の**要素**を吸収するのであって、要素そのものを吸収するわけではなく、しかもどの集合も自分自身を含みません。そこで一段の後続を挟み、後続の族の和を取ります。結果は截断された存在ではなく実際の対として与えられ、利用者はこの上界を名指し、その段階を構成できます。
<!--/-->

<!--en-->
The result returns the bound `β` as explicit data, together with its ordinal certificate and, for each index, a strict membership `f x ∈ˢ β`. Later proofs can project the bound and these memberships directly, without eliminating a truncated existence.
<!--zh-->
结果把上界 `β` 作为显式数据返回，并附带其序数证书及每个指标处的严格隶属 `f x ∈ˢ β`。后续证明可以直接投影出这个上界和各项隶属，而无需消去一个截断存在。
<!--ja-->
この結果は、上界 `β` を、その順序数証明と各添字に対する真の所属 `f x ∈ˢ β` とともに明示的なデータとして返します。後の証明は、切断された存在を消去せずに、この上界と各所属を直接取り出せます。
<!--/-->

```agda
boundingOrd : (X : Type ℓ) (f : X → S) → ((x : X) → IsOrd (f x))
            → Σ[ β ∈ S ] (IsOrd β × ((x : X) → ⟨ f x ∈ˢ β ⟩))
boundingOrd X f hf = β , (ordβ , memβ)
  where
  g : X → S
```

<!--en-->
The construction is three lines of mathematics. Replace `f` by its successor `g x = sucV (f x)`; take the union `β` of that family; and apply the union closure just proved, whose hypotheses hold because each `sucV (f x)` is an ordinal by the successor lemma.
<!--zh-->
构造就是三行数学。把 `f` 换成其后继 `g x = sucV (f x)`；取该族的并 `β`；再应用刚证得的并封闭，其假设成立是因为依后继引理每个 `sucV (f x)` 都是序数。
<!--ja-->
構成は三行の数学です。`f` をその後続 `g x = sucV (f x)` に置き換え、その族の和 `β` を取り、いま証明した和の閉性を適用します。仮定は、後続の補題により各 `sucV (f x)` が順序数であることから満たされます。
<!--/-->

```agda
  g x = sucV (f x)
  β : S
  β = ⋃ (sett X g)
  ordβ : IsOrd β
  ordβ = setUnion-ord X g (λ x → suc-ord (hf x))
```

<!--en-->
The memberships are why the detour through successors is necessary. Each `f x` lies strictly inside its own successor, `union-family-in` lifts that into the union, and the union's own transitivity then upgrades the strict memberships to the inclusion the closure arguments use downstream.
<!--zh-->
隶属关系正是必须绕经后继的原因。每个 `f x` 严格属于其自身的后继，`union-family-in` 把它提升进并，而并自身的传递性随后把这些严格隶属升级为下游闭包论证所用到的包含关系。
<!--ja-->
所属関係こそ、後続を経由する必要がある理由です。各 `f x` は自分自身の後続の内側に真に属し、`union-family-in` がそれを和集合の中へ引き上げ、さらに和集合自身の推移性が、この真の所属を、下流の閉性証明が使う包含関係へと格上げします。
<!--/-->

```agda
  memβ : (x : X) → ⟨ f x ∈ˢ β ⟩
  memβ x = union-family-in X g x (f x) (self∈sucV (f x))
```

<!--en-->
The two-element case is worth naming, because it is the one that gets used most: merging two ordinals into a single ordinal strictly containing both. The family is indexed by the booleans, lifted to the ambient universe so that the general lemma applies, and the two memberships are read off at the two indices.
<!--zh-->
二元情形值得单独命名，因为用得最多的正是它：把两个序数合并为一个严格包含二者的序数。族由布尔值索引，抬升到周遭宇宙以便通用引理得以适用，而两条隶属关系在两个索引处读出。
<!--ja-->
二元の場合には名前を付ける価値があります。実際に最もよく使われるのはこの形だからです。すなわち、二つの順序数を、その両方を厳密に含む単一の順序数へと統合します。族はブール値で索引され、一般の補題を適用できるように周辺の宇宙へ持ち上げられ、二つの所属関係はそれぞれの索引で読み出されます。
<!--/-->

<!--en-->
The result packages three pieces of data: the bound β, a proof that β is an ordinal, and the two strict memberships ⟨ σ₁ ∈ˢ β ⟩ and ⟨ σ₂ ∈ˢ β ⟩, combined with nested products. The body simply extracts these from `r`, reading the two memberships at the two boolean indices `lift true` and `lift false`; the `where` block constructs `r` below.
<!--zh-->
结果打包了三份数据：上界 β、β 是序数的证明，以及两条严格隶属 ⟨ σ₁ ∈ˢ β ⟩ 与 ⟨ σ₂ ∈ˢ β ⟩，用嵌套的积类型组合。主体只是从 `r` 中取出这些成分，在两个布尔索引 `lift true` 与 `lift false` 处读出两条隶属；`r` 由下方的 `where` 块构造。
<!--ja-->
結果は三つのデータをまとめたものです。上界 β、β が順序数である証明、そして二つの厳密な所属 ⟨ σ₁ ∈ˢ β ⟩ と ⟨ σ₂ ∈ˢ β ⟩ であり、これらを入れ子になった積で組み合わせます。本体は `r` からこれらを取り出すだけで、二つの所属関係はブール値の索引 `lift true` と `lift false` で読み出します。`r` は下の `where` ブロックで構成されます。
<!--/-->

```agda
bound2 : (σ₁ σ₂ : S) → IsOrd σ₁ → IsOrd σ₂
       → Σ[ β ∈ S ] (IsOrd β × ⟨ σ₁ ∈ˢ β ⟩ × ⟨ σ₂ ∈ˢ β ⟩)
bound2 σ₁ σ₂ o₁ o₂ =
  fst r , (r .snd .fst , r .snd .snd (lift true) , r .snd .snd (lift false))
  where
```

<!--en-->
The indexing type needs one word of care. `Bool` lives in `Type ℓ-zero` while `S` lives in `Type ℓ`, but `boundingOrd` requires its index type to sit in `Type ℓ`. `Lift` raises the level without changing the elements: they become `lift true` and `lift false`. The function `f` sends them to σ₁ and σ₂, and `fo` attaches the corresponding ordinality hypothesis at each index.
<!--zh-->
索引类型需要一句说明。`Bool` 住在 `Type ℓ-zero`，而 `S` 住在 `Type ℓ`，但 `boundingOrd` 要求索引类型落在 `Type ℓ` 中。`Lift` 只抬升层级而不改变元素：元素变成 `lift true` 与 `lift false`。函数 `f` 把它们送到 σ₁ 与 σ₂，`fo` 则在每个索引处附上相应的序数性假设。
<!--ja-->
索引の型について一言注意が必要です。`Bool` は `Type ℓ-zero` に住み、`S` は `Type ℓ` に住みますが、`boundingOrd` は索引の型が `Type ℓ` に属することを要求します。`Lift` は要素を変えずに階数だけを上げ、要素は `lift true` と `lift false` になります。関数 `f` はこれらを σ₁ と σ₂ へ送り、`fo` は各索引に対応する順序数性の仮定を付けます。
<!--/-->

```agda
  f : Lift {ℓ-zero} {ℓ} Bool → S
  f (lift true)  = σ₁
  f (lift false) = σ₂
  fo : (b : Lift {ℓ-zero} {ℓ} Bool) → IsOrd (f b)
  fo (lift true)  = o₁
```

<!--en-->
Nothing new remains to prove. `r` is the general lemma applied to this two-point family; it already supplies an ordinal bound together with a membership for every index, and the two displayed memberships of the result are that same proof instantiated at the two booleans.
<!--zh-->
再没有新东西要证。`r` 就是对这个二点族应用一般引理的结果；它已经给出了序数上界以及对每个索引的隶属，结果的两条隶属不过是同一证明在两个布尔值处的实例。
<!--ja-->
これ以上新たに証明すべきものはありません。`r` はこの二点族に対して一般の補題を適用したものであり、順序数の上界と各索引への所属をすでに備えています。結果に現れる二つの所属は、同じ証明を二つのブール値で具体化したものにすぎません。
<!--/-->

```agda
  fo (lift false) = o₂
  r = boundingOrd (Lift {ℓ-zero} {ℓ} Bool) f fo
```

<!--en-->
## Members

Ordinals are closed downwards: a member of an ordinal is an ordinal. Its own transitivity is the second half of the hypothesis; that its members are transitive follows by pulling them back into the ambient ordinal along transitivity.

The hierarchy chapter's irreflexivity, that no set belongs to itself, is the other fact these arguments need; it is recalled here because this is where the ordinal proofs start reaching for it.
<!--zh-->
## 成员

序数向下封闭：序数的成员是序数。它自身的传递性就是假设的第二半；而成员的传递性，则经传递性把它们拉回外层序数即得。

层级那一章的无自环性，即没有集合属于自身，是这些论证需要的另一个事实；此处提起它，是因为序数的证明正是从这里开始取用。
<!--ja-->
## 要素

順序数は下向きに閉じています。順序数の要素はふたたび順序数です。要素自身の推移性は仮定の後半そのものであり、その要素がさらに推移的であることは、推移性に沿って外側の順序数へ引き戻せば分かります。

階層の章で示した無自己所属性、すなわちどの集合も自分自身に属さないという事実は、これらの議論がもう一つ必要とするものです。順序数の証明がまさにここからそれを用い始めるので、この場で思い出しておきます。
<!--/-->

<!--en-->
Unpacked, the hypothesis `IsOrd A` is a pair: `Atr`, the transitivity of `A`, and `Amem`, the assertion that every member of `A` is transitive. So the first half of the conclusion is just `Amem x x∈A`. For the second half, take `y` with `y ∈ x ∈ A`: transitivity of `A` yields `y ∈ A`, and then `Amem y` says `y` is transitive, which is exactly what is claimed about each member of `x`.
<!--zh-->
拆开来看，假设 `IsOrd A` 是一个序对：`Atr` 即 `A` 的传递性，`Amem` 即「`A` 的每个成员都传递」。于是结论的前半就是 `Amem x x∈A`。后半：设 `y` 满足 `y ∈ x ∈ A`，由 `A` 的传递性得 `y ∈ A`，再由 `Amem y` 知 `y` 传递，这正是要对 `x` 的每个成员所说的话。
<!--ja-->
仮定 `IsOrd A` を分解すると、これは組です。`Atr` は `A` の推移性、`Amem` は「`A` のすべての要素が推移的である」という主張です。したがって結論の前半はそのまま `Amem x x∈A` です。後半については、`y ∈ x ∈ A` なる `y` を取ると、`A` の推移性から `y ∈ A` が得られ、さらに `Amem y` により `y` が推移的だと分かります。これは `x` の各要素について主張していたことそのものです。
<!--/-->

```agda
mem-ord : ∀ {A} → IsOrd A → (x : S) → ⟨ x ∈ˢ A ⟩ → IsOrd x
mem-ord {A} (Atr , Amem) x x∈A =
  Amem x x∈A , (λ y y∈x → Amem y (Atr y∈x x∈A))
```

<!--en-->
## The numerals, and their limit

The hierarchy's numerals are the iterated successors of zero, so they are ordinals by the two facts above, by a single induction. Their limit `ω` is an ordinal too, and that is the fact the collection step will need. Its second half follows directly from the numeral lemmas; its first half, transitivity, says that a member of a numeral is again a numeral, which is another induction, the successor case splitting by the eliminator.

One warning about the reasoning style: membership in `ω` only *merely* presents an index. The proofs below therefore never extract a chosen natural number; they eliminate the truncation into targets that are propositions, such as `IsOrd y` or a membership statement.
<!--zh-->
## 数码，及其极限

层级的数码是零的迭代后继，故由上面两个事实即为序数，只需一层归纳。它们的极限 `ω` 也是序数，而那正是收集步骤将要用到的事实。其第二半由数码直接给出；第一半即传递性，说的是数码的成员仍是数码，那是另一次归纳，后继情形按消去子分情形。

对这种推理方式要提一句：属于 `ω` 只是**仅仅**给出一个索引。因此下面的证明从不取出一个选定的自然数，而是把截断消去到命题值的目标上，例如 `IsOrd y` 或某条隶属陈述。
<!--ja-->
## 数項とその極限

階層の数項は零の後続の繰り返しなので、前節の二つの事実から帰納法によってただちに順序数です。その極限 `ω` も順序数であり、これが後に収集の場面で必要になる事実です。後半は数項に関する補題から直接従います。前半の推移性は「数項の要素は再び数項である」という主張で、これも別の帰納法であり、後続の場合は消去子で場合分けします。

推論の仕方について一言注意しておきます。`ω` への所属は索引を**単に (merely)** 与えるだけです。したがって以下の証明は特定の自然数を選び出すことはせず、`IsOrd y` や所属の主張のように命題値を持つ対象へと截断を消去します。
<!--/-->

<!--en-->
The definition `# zero = ∅` and `# suc n = sucV (# n)` makes the induction one line per case: the empty set is an ordinal by the first section, and the successor of an ordinal is an ordinal by the second.
<!--zh-->
由定义 `# zero = ∅` 与 `# suc n = sucV (# n)`，归纳在每种情形各占一行：空集由第一节可知是序数，序数的后继由第二节可知是序数。
<!--ja-->
定義 `# zero = ∅` と `# suc n = sucV (# n)` により、帰納法は各場合が一行で済みます。空集合は最初の節により順序数であり、順序数の後続は二番目の節により順序数です。
<!--/-->

```agda
numeral-ord : (n : ℕ) → IsOrd (# n)
numeral-ord zero    = ∅-ord
numeral-ord (suc n) = suc-ord (numeral-ord n)
```

<!--en-->
Inside the cumulative hierarchy library, `ω` is presented as the set whose members are indexed by natural numbers, so membership in `ω` amounts to carrying a numerical index. The lemma `#-in-ω` supplies that index for each numeral, and `∈∈ₛ` converts the resulting index into the membership proposition ⟨ `# k` ∈ˢ `ω` ⟩.
<!--zh-->
在累积层级库中，`ω` 被表现为成员由自然数索引的集合，所以属于 `ω` 就相当于携带一个数值索引。引理 `#-in-ω` 为每个数码给出该索引，`∈∈ₛ` 再把所得的索引转成隶属命题 ⟨ `# k` ∈ˢ `ω` ⟩。
<!--ja-->
累積階層のライブラリでは、`ω` はその要素が自然数で索引される集合として提示されます。したがって `ω` への所属とは数値の索引を持つことにほかなりません。補題 `#-in-ω` は各数項に対しその索引を与え、`∈∈ₛ` は得られた索引を所属の命題 ⟨ `# k` ∈ˢ `ω` ⟩ へと変換します。
<!--/-->

```agda

#∈ω : (k : ℕ) → ⟨ (# k) ∈ˢ ω ⟩
#∈ω k = ∈∈ₛ {a = # k} {b = ω} .snd (#-in-ω k)
```

<!--en-->
The next statement is downward closure for numerals, phrased directly as membership in `ω`: every member of `# k` is a member of `ω`. The induction on `k` has a vacuous base, since nothing belongs to the empty set. In the successor case the eliminator for `sucV` splits in two: either `y` already lies in `# k`, where the induction hypothesis applies, or `y` equals `# k` itself, where membership in `ω` follows from the previous lemma.
<!--zh-->
下一条是数码的向下封闭，直接表述为「属于 `ω`」：`# k` 的每个成员都是 `ω` 的成员。对 `k` 的归纳底情形真空成立，因为没有东西属于空集。后继情形由 `sucV` 的消去子分成两支：要么 `y` 已经在 `# k` 中，此时用归纳假设；要么 `y` 等于 `# k` 自身，此时由上一条引理得到属于 `ω`。
<!--ja-->
次は数項の下向き閉性を、`ω` への所属という形で直接述べたものです。つまり `# k` のすべての要素は `ω` の要素です。`k` についての帰納法の底は空虚に成り立ちます。空集合には何も属さないからです。後続の場合は `sucV` の消去子によって二つに分かれます。`y` がすでに `# k` に属する場合は帰納法の仮定を使い、`y` が `# k` 自身と等しい場合は前の補題から `ω` への所属が従います。
<!--/-->

```agda

numeral-mem : (k : ℕ) (y : S) → ⟨ y ∈ˢ (# k) ⟩ → ⟨ y ∈ˢ ω ⟩
numeral-mem zero y y∈ =
  Empty.rec (∅-empty y (∈∈ₛ {a = y} {b = ∅} .fst y∈))
numeral-mem (suc k) y y∈ = ∈sucV-elim (snd (y ∈ˢ ω)) y∈
  (λ y∈#k → numeral-mem k y y∈#k)
```

<!--en-->
Conversely, every member of `ω` is an ordinal. Membership in `ω` merely presents a natural `k` with `# k ≡ y`; the goal `IsOrd y` is a proposition by `isPropIsOrd`, so the truncation may be eliminated into it. Along the path `# k ≡ y` the ordinality of `# k` transports to `y`. No particular index is chosen; the argument works uniformly for whichever one the truncation hides.
<!--zh-->
反过来，`ω` 的每个成员都是序数。属于 `ω` 仅仅给出一个自然数 `k` 使 `# k ≡ y`；目标 `IsOrd y` 由 `isPropIsOrd` 是命题，因此截断可以消去到它上面。沿路径 `# k ≡ y`，`# k` 的序数性被搬运到 `y`。这里没有选定任何具体索引；无论截断背后藏着哪一个，论证都一致适用。
<!--ja-->
逆に、`ω` のすべての要素は順序数です。`ω` への所属は `# k ≡ y` なる自然数 `k` を単に (merely) 与えるだけです。目標の `IsOrd y` は `isPropIsOrd` により命題なので、截断をそれへ消去できます。パス `# k ≡ y` に沿って `# k` の順序数性が `y` へ輸送されます。特定の索引が選ばれることはなく、截断の裏にどの索引が隠れていても議論は一様に通用します。
<!--/-->

```agda
  (λ y≡#k → subst (λ w → ⟨ w ∈ˢ ω ⟩) (sym y≡#k) (#∈ω k))

ω-mem-ord : (y : S) → ⟨ y ∈ˢ ω ⟩ → IsOrd y
ω-mem-ord y y∈ω = PT.rec (isPropIsOrd y)
  (λ { (k , #k≡y) → subst IsOrd #k≡y (numeral-ord (lower k)) })
  y∈ω
```

<!--en-->
Assembling the halves gives `ω-ord : IsOrd ω`. Its first component, `trans-ω`, establishes `isTransV ω`: from `y ∈ x ∈ ω`, the hypothesis on `x` merely presents an index `k` with `# k ≡ x`, and after transporting along that path, `numeral-mem` places `y` in `ω`. This elimination goes into a proposition-valued target, which is what licenses removing the truncation.
<!--zh-->
两半合起来得到 `ω-ord : IsOrd ω`。其第一个分量 `trans-ω` 建立 `isTransV ω`：从 `y ∈ x ∈ ω` 出发，关于 `x` 的假设仅仅给出索引 `k` 使 `# k ≡ x`，沿该路径搬运后，`numeral-mem` 把 `y` 放进 `ω`。这一消去进入命题值的目标，这正是允许去掉截断的理由。
<!--ja-->
二つの半分を組み合わせて `ω-ord : IsOrd ω` が得られます。最初の成分 `trans-ω` は `isTransV ω` を示します。`y ∈ x ∈ ω` から出発すると、`x` についての仮定は `# k ≡ x` なる索引 `k` を単に与えるだけで、そのパスに沿って輸送した後、`numeral-mem` が `y` を `ω` の中に置きます。この消去は命題値の目標への消去であり、それが截断を取り除いてよい根拠です。
<!--/-->

```agda

ω-ord : IsOrd ω
ω-ord = trans-ω , (λ x x∈ω → ω-mem-ord x x∈ω .fst)
  where
  trans-ω : isTransV ω
```

<!--en-->
For each member `x` of `ω`, `ω-mem-ord x x∈ω` proves `IsOrd x`; its first component is the transitivity of `x` required by the second component of `IsOrd ω`. Together the two components yield `IsOrd ω`.
<!--zh-->
对 `ω` 的每个成员 `x`，`ω-mem-ord x x∈ω` 证明 `IsOrd x`；它的第一个分量正是 `IsOrd ω` 的第二个分量所需的 `x` 的传递性。两部分合起来得到 `IsOrd ω`。
<!--ja-->
`ω` の各要素 `x` に対して、`ω-mem-ord x x∈ω` は `IsOrd x` を証明します。その第一成分が、`IsOrd ω` の第二成分に必要な `x` の推移性です。二つの成分を合わせて `IsOrd ω` が得られます。
<!--/-->

```agda
  trans-ω {x} {y} y∈x x∈ω = PT.rec (snd (y ∈ˢ ω))
    (λ { (k , #k≡x) →
      numeral-mem (lower k) y (subst (λ w → ⟨ y ∈ˢ w ⟩) (sym #k≡x) y∈x) })
    x∈ω
```

<!--en-->
## What lies below a numeral

The numerals are not merely ordinals, they are *counted* by ordinals: the members of the numeral for `n` are exactly the numerals for the smaller naturals. The first half of that, elimination, is one induction with the successor eliminator; the second half, that a numeral belonging to a numeral means the indices compare, follows by injectivity. The coding chapters will use these to read an index out of a set, which is what a bound on a variable ultimately means.
<!--zh-->
## 数码之下有什么

数码不只是序数，它们还被序数**计数**：`n` 的数码的成员，恰是更小自然数的数码。前一半说的是消去，它由一次沿后继消去子的归纳得到；后一半，即数码属于数码意味着序号可比，则由单射性得出。编码诸章将用这两件事实从一个集合里读出序号，而这正是变元的界最终的含义。
<!--ja-->
## 数項の下にあるもの

数項は単に順序数であるだけでなく、順序数によって**数え上げ**られています。`n` の数項の要素は、より小さい自然数の数項にちょうど一致します。前者の消去は後続の消去子を用いた一度の帰納法であり、後半、すなわち数項が数項に属することは索引どうしの比較を意味するという部分は、単射性から従います。コーディングの諸章ではこの二つの事実を使って集合から索引を読み出します。これが変数の上界の最終的な意味です。
<!--/-->

<!--en-->
The elimination lemma states that a member `z` of `# n` merely comes from a smaller index: there merely exists `m < n` with `z ≡ # m`. The statement lands in a propositional truncation on purpose. The proof does not choose a witness from the truncation; it uses only the proposition that some such decomposition exists. The base case is vacuous, since membership in the empty set is contradictory.
<!--zh-->
消去引理说：`# n` 的成员 `z` 仅仅来自某个更小的索引，即仅仅存在 `m < n` 使 `z ≡ # m`。陈述有意落在命题截断之中：证明不从截断中选取见证，只使用某个这样的分解存在这一命题。底情形真空成立，因为属于空集导致矛盾。
<!--ja-->
消去の補題は、`# n` の要素 `z` が単に (merely) より小さい索引から来ることを述べます。すなわち、`z ≡ # m` なる `m < n` が単に存在するということです。この主張が意図的に命題的切断の中に置かれている点に注意してください。この証明は切断から証人を選ばず、そのような分解が存在するという命題だけを使います。底の場合は空虚に成り立ちます。空集合への所属は矛盾をもたらすからです。
<!--/-->

```agda
∈#-elim : (n : ℕ) (z : S) → ⟨ z ∈ˢ (# n) ⟩
        → ∥ Σ[ m ∈ ℕ ] ((m < n) × (z ≡ # m)) ∥₁
∈#-elim zero    z h = Empty.rec (∅-empty z (∈∈ₛ {a = z} {b = ∅} .fst h))
∈#-elim (suc n) z h = ∈sucV-elim {A = # n} {x = z}
  {P = ∥ Σ[ m ∈ ℕ ] ((m < suc n) × (z ≡ # m)) ∥₁} squash₁ h
```

<!--en-->
In the successor case the eliminator for `sucV` splits membership in `# (suc n)` into two branches. If `z` lies in `# n`, the induction hypothesis gives `m < n` with `z ≡ # m`, and `≤-suc` lifts that to `m < suc n`. If `z` equals `# n` itself, the witness is `n` itself, with the strict inequality witnessed by `0` and `refl`. For the companion statement `#∈#-elim`, apply this to `z = # a` in `# b`: a truncated triple results, whose equation `# a ≡ # m` the injectivity lemma `#-inj′` turns into `a ≡ m`, and transporting along that identification converts `m < b` into the claimed `a < b`.
<!--zh-->
后继情形中，`sucV` 的消去子把「属于 `# (suc n)`」分成两支。若 `z` 在 `# n` 中，归纳假设给出 `m < n` 与 `z ≡ # m`，再用 `≤-suc` 提升为 `m < suc n`。若 `z` 就是 `# n` 自身，见证即 `n` 本身，其严格不等式由 `0` 与 `refl` 给出。对于配套的 `#∈#-elim`，把它应用于 `# b` 中的 `z = # a`：得到一个截断的三元组，其中方程 `# a ≡ # m` 经单射性引理 `#-inj′` 化为 `a ≡ m`，再沿该等同把 `m < b` 转成所要的 `a < b`。
<!--ja-->
後続の場合、`sucV` の消去子は `# (suc n)` への所属を二つの場合に分けます。`z` が `# n` に属するなら、帰納法の仮定から `z ≡ # m` なる `m < n` が得られ、`≤-suc` によってこれを `m < suc n` へ持ち上げます。`z` が `# n` 自身に等しいなら、証人は `n` 自身であり、狭義の不等式は `0` と `refl` によって与えられます。対応する主張 `#∈#-elim` については、`# b` の中の `z = # a` に対してこれを適用します。截断された三つ組が得られ、その等式 `# a ≡ # m` は単射性の補題 `#-inj′` によって `a ≡ m` に変わり、この同一視に沿って輸送すれば `m < b` が主張の `a < b` に変わります。
<!--/-->

```agda
  (λ z∈#n → PT.map (λ { (m , p , e) → m , ≤-suc p , e }) (∈#-elim n z z∈#n))
  (λ e → ∣ n , (0 , refl) , e ∣₁)

#∈#-elim : (a b : ℕ) → ⟨ (# a) ∈ˢ (# b) ⟩ → a < b
#∈#-elim a b h = PT.rec isProp≤
  (λ { (m , p , e) → subst (_< b) (sym (#-inj′ e)) p })
```

<!--en-->
The final step is the elimination of the truncation itself. The strict order on ℕ is proposition-valued, by `isProp≤`, so eliminating into `a < b` is legitimate; the conclusion needs only that *some* witnessing index works, not a canonical one.
<!--zh-->
最后一步是消去截断本身。ℕ 上的严格序由 `isProp≤` 是命题值的，因此消去到 `a < b` 是合法的；结论只需要**某个**见证索引成立，并不需要典范的那个。
<!--ja-->
最後の段階は截断そのものの消去です。ℕ 上の狭義の順序は `isProp≤` により命題値を持つので、`a < b` へ消去するのは正当です。結論が必要とするのは、**どこかの**証明索引が機能することだけで、標準的なものである必要はありません。
<!--/-->

```agda
  (∈#-elim b (# a) h)
```

<!--en-->
## Recap

Zero, successors and small unions of ordinals are ordinals, and `boundingOrd`{.Agda} bounds any small family by a single ordinal. The bound converts pointwise ordinal bounds for any small family into one strict common bound. Later chapters use these results independently: the ZF axiom proofs use ordinal bounds to collect stages, while the finite-ordinal lemmas and `ω-ord` support the treatment of infinity and later coding arguments.
<!--zh-->
## 小结

零、后继与序数的小并都是序数，而 `boundingOrd`{.Agda} 以单一序数界住任一小族。这一上界把任意小族的逐点序数界合并为一个严格公共界。后续各章分别使用这些结果：ZF 公理证明用序数界收集层，有限序数引理与 `ω-ord` 则用于无穷公理及后面的编码论证。
<!--ja-->
## まとめ

零、後続、順序数からなる小さな族の和集合はいずれも順序数であり、`boundingOrd`{.Agda} は任意の小さな族を単一の順序数で抑えます。この上界は、任意の小さな族に対する要素ごとの順序数上界を、一つの厳密な共通上界へまとめます。後の章ではこれらの結果を別々に使います。ZF 公理の証明は順序数上界で段階を集め、有限順序数の補題と `ω-ord` は無限公理や後の符号化で使われます。
<!--/-->
