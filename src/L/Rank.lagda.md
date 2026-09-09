<!--en-->
# Von Neumann rank

The rank of a set is the union of the successors of the ranks of its members. Membership recursion defines it; rank strictly increases along membership, is always an ordinal, bounds every set beneath a sufficiently large ordinal, and fixes ordinals.
<!--zh-->
# Von Neumann 秩

集合的秩是其成员各自秩的后继之并。秩由隶属递归定义；它沿隶属关系严格增长，始终是序数，把每个集合界在足够大的序数之下，并固定每个序数。
<!--ja-->
# von Neumann ランク

集合のランクは、その各要素のランクの後続の和集合です。所属再帰で定義され、所属に沿って狭義単調に増加し、常に順序数となり、各集合を十分大きな順序数の下に置き、順序数を固定します。
<!--/-->

<!--en-->
Two facts about it carry this part of the book. The rank of any set is an
ordinal, so rank really is a measurement in ordinals; and an ordinal is its own
rank, so rank is the *canonical* ordinal index rather than a second, parallel
numbering. The second fact is what lets a question about stages be turned into
a question about ranks and back again, and the collection step of infinity is
exactly such a question.

A remark on how the recursion is set up, because it uses the same device as
the tower. Nothing here needs an external type of ordinals: rank takes values in the
hierarchy itself, and the recursion runs on well-founded membership, which
regularity directly guarantees. So the whole chapter is constructive, and the
classical assumption that the next chapter introduces is not needed for any of
it.
<!--zh-->
本书这一部分要用到关于秩的两个事实。任何集合的秩都是序数，故秩确实是以序数进行的度量；而序数是自身的秩，故秩是**典范的**序数索引，不是另一套平行的编号。第二个事实使得关于阶段的问题可以换成关于秩的问题，再换回来，而无穷公理的收集那一步恰是这样一个问题。

关于递归的架设方式说一句，因为它与塔用的是同一个手法。此处不需要任何外部的序数类型：秩取值于层级自身，而递归跑在良基的成员关系上，这一点由正则性直接保证。所以整章是构造性的，下一章引入的经典假设在这里一处也用不上。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth

module L.Rank {ℓ : Level} where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ}
  using ( 𝒮ᵥ; extensionalV; ∈-induction; ∈-induction-compute )
open import V.Model {ℓ} using ( union-family-in; union-family-out; ∈sucV-elim; self∈sucV )
open import L.Constructible {ℓ} using ( IsOrd )
open import L.Ordinal {ℓ} using ( suc-ord; setUnion-ord; mem-ord )

open import Cubical.Functions.Logic using ( ⇔toPath )
import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.HITs.CumulativeHierarchy.Base using ( sett )
open import Cubical.HITs.CumulativeHierarchy.Properties
  using ( ∈∈ₛ; ∈-asFiber; ⟪_⟫; ⟪_⟫↪; ∈ₛ⟪_⟫↪_ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ⋃_; module InfinitySet )
open InfinitySet using ( sucV )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ
```

<!--en-->
## The recursion

The step takes the union, over the members of `x`, of the successors of their
ranks. As with the tower, the recursive calls run over the *small* type of
members, and the computation rule holds propositionally rather than
definitionally, which is all any later proof asks of it.
<!--zh-->
## 递归

步进取 `x` 的各成员之秩的后继的并。与塔一样，递归调用跑在成员的**小**类型上，而计算规则是命题性地而非定义性地成立，这也正是后文任何证明对它的全部要求。
<!--ja-->
## 再帰

`rank x`{.Agda} は、`x` の各要素 `y` に対する `sucV (rank y)` の和集合として所属再帰で定義されます。計算法則は、ランクについての後続の帰納証明でこの定義を展開します。
<!--/-->

<!--en-->
The rank itself is sealed, for the same reason the tower is: it unfolds to an
accessibility eliminator, and any goal that mentions the rank of a set built by
nesting, a pair inside a pair inside a pair, drags that eliminator through
normalization. Measured, on a goal four constructions deep: **163 seconds
without the seal, 1.4 with**. `rank-compute`{.Agda} is the official unfolding
and lives inside the seal, so nothing downstream loses anything.
<!--zh-->
秩本身定义为不透明，理由与塔相同：展开后会出现可及性消去子；任何涉及嵌套集合之秩的目标，例如对子中的对中的对，都会在归一化时展开该消去子。对四层嵌套构造的实测是：**透明时 163 秒，不透明时 1.4 秒**。`rank-compute`{.Agda} 是受控使用的展开定理，因此下游仍可取得秩的计算规则。
<!--/-->

```agda
rankStep : (x : S) → (∀ y → y ∈ᵗ x → S) → S
rankStep x rec = ⋃ (sett ⟪ x ⟫ (λ m → sucV (rec (⟪ x ⟫↪ m) (mem m))))
  where
  mem : (m : ⟪ x ⟫) → ⟪ x ⟫↪ m ∈ᵗ x
  mem m = ∈∈ₛ {a = ⟪ x ⟫↪ m} {b = x} .snd (∈ₛ⟪ x ⟫↪ m)

opaque
  rank : S → S
  rank = ∈-induction rankStep

  rank-compute : (x : S) → rank x ≡ rankStep x (λ y _ → rank y)
  rank-compute = ∈-induction-compute rankStep
```

<!--en-->
## Rank strictly increases along membership

The one fact that makes rank a descent measure. It is the outward half of the
fixed-point argument below with the ordinality hypothesis dropped: the same union
witness, no `IsOrd`{.Agda} anywhere. A recursion that must descend into a set
built by nesting, rather than into a member, has no membership to induct on and
uses this instead.
<!--zh-->
## 秩沿成员关系严格增长

使秩成为一把下降尺的那一条事实。它就是下文不动点论证的向外那一半，去掉了序数假设：同一个并的见证，全程不见 `IsOrd`{.Agda}。一场必须下降进「由嵌套造出的集合」而非下降进某个成员的递归，没有成员关系可供归纳，于是改用这一条。
<!--ja-->
## ランクは所属に沿って狭義単調に増加する

`x ∈ y` なら、`rank x`{.Agda} の後続は `rank y`{.Agda} を作る和集合の一項です。したがって `rank x ∈ rank y` が成り立ちます。
<!--/-->



```agda
rank-mono : (x y : S) → ⟨ x ∈ˢ y ⟩ → ⟨ rank x ∈ˢ rank y ⟩
rank-mono x y x∈y = subst (λ w → ⟨ rank x ∈ˢ w ⟩) (sym (rank-compute y))
  (union-family-in ⟪ y ⟫ (λ m → sucV (rank (⟪ y ⟫↪ m))) (fib .fst) (rank x)
    (subst (λ w → ⟨ rank x ∈ˢ sucV (rank w) ⟩) (sym (fib .snd)) (self∈sucV (rank x))))
  where
  fib = ∈-asFiber {a = x} {b = y} x∈y
```

<!--en-->
## Rank is an ordinal

One membership induction. Unfold once; the inductive hypothesis makes each
member's rank an ordinal, successors of ordinals are ordinals, and the previous
chapter's closure under small unions gives that the union of the family is
again an ordinal.
<!--zh-->
## 秩是序数

一次成员归纳。展开一次；归纳假设给出每个成员的秩是序数，序数的后继是序数，而上一章的小并封闭性保证这一族的并仍是序数。
<!--ja-->
## ランクは順序数

各要素のランクが順序数であるという帰納仮定から、その後続も順序数となり、それらの和集合も順序数になります。よってすべての集合のランクは順序数です。
<!--/-->



```agda
rank-ord : (A : S) → IsOrd (rank A)
rank-ord = ∈-induction {P = λ A → IsOrd (rank A)} step
  where
  step : (A : S) → (∀ y → y ∈ᵗ A → IsOrd (rank y)) → IsOrd (rank A)
  step A IH = subst IsOrd (sym (rank-compute A))
    (setUnion-ord ⟪ A ⟫ (λ m → sucV (rank (⟪ A ⟫↪ m)))
      (λ m → suc-ord (IH (⟪ A ⟫↪ m) (mem m))))
    where
    mem : (m : ⟪ A ⟫) → ⟪ A ⟫↪ m ∈ᵗ A
    mem m = ∈∈ₛ {a = ⟪ A ⟫↪ m} {b = A} .snd (∈ₛ⟪ A ⟫↪ m)
```

<!--en-->
## Bounding a rank

If every member's rank lies in an ordinal, the rank of the set is included in
that ordinal. Every member of the defining union lies in a successor of a
member's rank; transitivity closes the inclusion. Both ordinal fixed points and
bounds on the ranks in a constructible stage use this argument.
<!--zh-->
## 界住秩

若一个集合的每个成员的秩都属于某序数，则该集合的秩包含于该序数：定义之并的每个成员都落在某个成员之秩的后继中，传递性给出所需包含。序数的不动点性质与可构造阶段中的秩界都用这条论证。
<!--ja-->
## ランクの上界

`β` が順序数で、`A` の各要素のランクを含むなら、ランクの再帰方程式と `β` の推移性により `rank A ⊆ β` が従います。この補題は集合全体のランクを一つの順序数で抑えます。
<!--/-->

```agda
rank-upper : (A β : S) → IsOrd β
           → ((y : S) → ⟨ y ∈ˢ A ⟩ → ⟨ rank y ∈ˢ β ⟩)
           → (x : S) → ⟨ x ∈ˢ rank A ⟩ → ⟨ x ∈ˢ β ⟩
rank-upper A β oβ bound x hx = PT.rec (snd (x ∈ˢ β))
  (λ { (m , hm) → ∈sucV-elim (snd (x ∈ˢ β)) hm
    (λ h → oβ .fst h (below m))
    (λ q → subst (λ w → ⟨ w ∈ˢ β ⟩) (sym q) (below m)) })
  (union-family-out ⟪ A ⟫ s x
    (subst (λ w → ⟨ x ∈ˢ w ⟩) (rank-compute A) hx))
  where
  s : ⟪ A ⟫ → S
  s m = sucV (rank (⟪ A ⟫↪ m))
  below : (m : ⟪ A ⟫) → ⟨ rank (⟪ A ⟫↪ m) ∈ˢ β ⟩
  below m = bound (⟪ A ⟫↪ m)
    (∈∈ₛ {a = ⟪ A ⟫↪ m} {b = A} .snd (∈ₛ⟪ A ⟫↪ m))
```

<!--en-->
## Ordinals are their own rank

Again by membership induction, and this time the proof is an extensionality
between `rank A` and `A`. Left to right, an element of `rank A` sits inside the
successor of the rank of some member, and that rank *is* the member by the
inductive hypothesis, so the element is the member or belongs to it, and either
way it belongs to `A` by transitivity. Right to left, a member of `A` is the
rank of itself, hence belongs to the successor of that rank, which is one
branch of the union.
<!--zh-->
## 序数是自身的秩

仍是成员归纳，而这次的证明是 `rank A` 与 `A` 之间的一次外延。从左到右：`rank A` 的元素落在某个成员之秩的后继里面，而依归纳假设那个秩**就是**该成员，故该元素或就是该成员，或属于它，两种情形都经传递性属于 `A`。从右到左：`A` 的成员是自身的秩，故属于该秩的后继，而那是并的一支。
<!--ja-->
## 順序数は自分自身のランクである

`A` が順序数なら、各要素のランクは帰納法でその要素自身に等しくなります。ランクの計算法則と外延性を用いると `rank A ≡ A` が得られます。
<!--/-->

<!--en-->
The shape of the argument is worth one remark: extensionality is applied to
`rank A` and `A` directly, both of them neutral terms, and the nested union is
only ever reached through the computation rule as a path. Feeding the unfolded
union to extensionality instead would force the checker to normalize a deeply
nested set expression, which is the standard way these proofs become
uncheckable.
<!--zh-->
这里的论证结构值得说明：外延性直接用于 `rank A` 与 `A`，二者都保持为中性项；嵌套的并只通过计算规则以路径形式出现。若把展开后的并直接交给外延性，检查器就必须归一化深层嵌套的集合表达式，这正是此类证明容易变得无法检查的原因。
<!--/-->

```agda
rank-fix : (A : S) → IsOrd A → rank A ≡ A
rank-fix = ∈-induction {P = λ A → IsOrd A → rank A ≡ A} step
  where
  step : (A : S) → (∀ y → y ∈ᵗ A → IsOrd y → rank y ≡ y)
       → IsOrd A → rank A ≡ A
  step A IH ordA = extensionalV (λ x → ⇔toPath (toA x) (fromA x))
    where
    toA : (x : S) → ⟨ x ∈ˢ rank A ⟩ → ⟨ x ∈ˢ A ⟩
    toA = rank-upper A A ordA
      (λ y hy → subst (λ w → ⟨ w ∈ˢ A ⟩)
        (sym (IH y hy (mem-ord {A = A} ordA y hy))) hy)

    fromA : (x : S) → ⟨ x ∈ˢ A ⟩ → ⟨ x ∈ˢ rank A ⟩
    fromA x x∈A = subst (λ w → ⟨ w ∈ˢ rank A ⟩)
      (IH x x∈A (mem-ord {A = A} ordA x x∈A)) (rank-mono x A x∈A)
```

<!--en-->
## Recap

`rank`{.Agda} measures every set by an ordinal (`rank-ord`{.Agda}) and fixes
the ordinals themselves (`rank-fix`{.Agda}), which together certify it as the
canonical index. Both proofs are membership inductions on regularity, so the
chapter uses no additional assumptions. What it gives is the ability to ask
"how far up does this set appear" and get an ordinal answer, and the next two
chapters use that on the one remaining question about the tower: which
ordinals appear at which stage.
<!--zh-->
## 小结

`rank`{.Agda} 以序数度量每个集合 (`rank-ord`{.Agda})，并固定序数自身 (`rank-fix`{.Agda})，二者合起来认证它为典范索引。两个证明都是正则性上的成员归纳，故本章不引入任何额外假设。它给出「这个集合到多高才现身」这一问题的序数答案，而接下来两章将用它回答关于塔的最后一个问题：哪些序数出现在哪个阶段。
<!--ja-->
## まとめ

ランクは所属に沿って増加する順序数であり、指定された順序数上界の中に収まります。順序数に対しては `rank-fix`{.Agda} がランクを恒等写像にするため、ランクと順序数階層が一致します。
<!--/-->
