# Rank

<!--en-->
Every set has a rank: the least stage of the cumulative hierarchy at which it
appears, measured in ordinals. The definition is one of the oldest in set
theory and reads as a recursion on membership: the rank of `x` is the least
ordinal above the ranks of all members of `x`, which is the union of their
successors.

Two facts about it carry this part of the book. The rank of any set is an
ordinal, so rank really is a measurement in ordinals; and an ordinal is its own
rank, so rank is the *canonical* ordinal index rather than a second, parallel
numbering. The second fact is what lets a question about stages be turned into
a question about ranks and back again, and the collection step of infinity is
exactly such a question.

A remark on how the recursion is set up, because it is the same trick the tower
used. Nothing here needs an external type of ordinals: rank takes values in the
hierarchy itself, and the recursion runs on well-founded membership, which
regularity supplied for free. So the whole chapter is constructive, and the
classical assumption that the next chapter introduces is not needed for any of
it.
<!--zh-->
每个集合都有秩：它在累积层级中现身的最低阶段，以序数度量。这个定义是集合论中最古老的定义之一，读起来就是一条沿成员关系的递归：`x` 的秩是高于 `x` 全部成员之秩的最小序数，也就是它们的后继之并。

关于它有两个事实支撑本书这一部分。任何集合的秩都是序数，故秩确实是以序数进行的度量；而序数是自身的秩，故秩是**典范的**序数索引，不是另一套平行编号。第二个事实使得关于阶段的问题可以换成关于秩的问题再换回来，而无穷公理的收集那一步恰是这样一个问题。

关于递归的架设方式说一句，因为这与塔用的是同一个手法。此处不需要任何外部的序数类型：秩取值于层级自身，而递归跑在良基的成员关系上，那是正则性免费供应的。所以整章是构造性的，下一章引入的经典假设在这里一处也用不上。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth

module L.Rank {ℓ : Level} where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ}
  using ( 𝒮ᵥ; extensionalV; ∈-induction; ∈-induction-compute )
open import V.Model {ℓ} using ( ∈sucV-elim; self∈sucV )
open import L.Constructible {ℓ} using ( IsOrd )
open import L.Ordinal {ℓ} using ( suc-ord; setUnion-ord; mem-ord )

open import Cubical.Functions.Logic using ( ⇔toPath )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁ )
open import Cubical.HITs.CumulativeHierarchy.Base using ( sett )
open import Cubical.HITs.CumulativeHierarchy.Properties
  using ( _∈ₛ_; ∈∈ₛ; ∈-asFiber; ⟪_⟫; ⟪_⟫↪; ∈ₛ⟪_⟫↪_ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ⋃_; union-ax; module InfinitySet )
open InfinitySet using ( sucV )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ
```

<!--en-->
## The recursion
<!--zh-->
## 递归
<!--/-->

<!--en-->
The step takes the union, over the members of `x`, of the successors of their
ranks. As with the tower, the recursive calls run over the *small* type of
members, and the computation rule holds propositionally rather than
definitionally, which is all any later proof asks of it.

The rank itself is sealed, for the same reason the tower is: it unfolds to an
accessibility eliminator, and any goal that mentions the rank of a set built by
nesting, a pair inside a pair inside a pair, drags that eliminator through
normalization. Measured, on a goal four constructions deep: **163 seconds
without the seal, 1.4 with**. `rank-compute`{.Agda} is the official unfolding
and lives inside the seal, so nothing downstream loses anything.
<!--zh-->
步进取 `x` 的成员上、其秩之后继的并。与塔一样，递归调用跑在成员的**小**类型上，而计算规则是命题级而非定义性成立，这也正是后文任何证明对它的全部要求。

秩本身被封起来，理由与塔相同：它展开成一个可及性消去子，而任何提到「由嵌套造出的集合」之秩的目标，例如对子里的对里的对，都会把那个消去子拖进归一化。实测，在一个四层深的构造上：**不封 163 秒，封了 1.4 秒**。`rank-compute`{.Agda} 是官方展开式且住在封内，故下游不失去任何东西。
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
## Rank is an ordinal
<!--zh-->
## 秩是序数
<!--/-->

<!--en-->
One membership induction. Unfold once; the inductive hypothesis makes each
member's rank an ordinal, successors of ordinals are ordinals, and the previous
chapter's closure under small unions collects the family back into an ordinal.
<!--zh-->
一次成员归纳。展开一次；归纳假设使每个成员的秩是序数，序数的后继是序数，而上一章的小并封闭性把这一族收回成序数。
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
## Ordinals are their own rank
<!--zh-->
## 序数是自身的秩
<!--/-->

<!--en-->
Again by membership induction, and this time the proof is an extensionality
between `rank A` and `A`. Left to right, an element of `rank A` sits inside the
successor of the rank of some member, and that rank *is* the member by the
inductive hypothesis, so the element is the member or belongs to it, and either
way it belongs to `A` by transitivity. Right to left, a member of `A` is the
rank of itself, hence belongs to the successor of that rank, which is one
branch of the union.

The shape of the argument is worth one remark: extensionality is applied to
`rank A` and `A` directly, both of them neutral terms, and the nested union is
only ever reached through the computation rule as a path. Feeding the unfolded
union to extensionality instead would force the checker to normalize a deeply
nested set expression, which is the standard way these proofs become
uncheckable.
<!--zh-->
仍是成员归纳，而这次的证明是 `rank A` 与 `A` 之间的一次外延。从左到右：`rank A` 的元素落在某个成员之秩的后继里面，而依归纳假设那个秩**就是**该成员，故该元素或就是该成员、或属于它，两种情形都经传递性属于 `A`。从右到左：`A` 的成员是自身的秩，故属于该秩的后继，而那是并的一支。

论证的形状值得说一句：外延性直接施于 `rank A` 与 `A`，二者都是中性项，而那个嵌套的并只经计算规则以路径的形式被触及。若改把展开后的并喂给外延性，就会迫使检查器归一化一个深层嵌套的集合表达式，那正是这类证明变得不可检查的标准途径。
<!--/-->

```agda
rank-fix : (A : S) → IsOrd A → rank A ≡ A
rank-fix = ∈-induction {P = λ A → IsOrd A → rank A ≡ A} step
  where
  step : (A : S) → (∀ y → y ∈ᵗ A → IsOrd y → rank y ≡ y)
       → IsOrd A → rank A ≡ A
  step A IH ordA = extensionalV (λ x → ⇔toPath (toA x) (fromA x))
    where
    s : ⟪ A ⟫ → S
    s m = sucV (rank (⟪ A ⟫↪ m))
    mem : (m : ⟪ A ⟫) → ⟨ ⟪ A ⟫↪ m ∈ˢ A ⟩
    mem m = ∈∈ₛ {a = ⟪ A ⟫↪ m} {b = A} .snd (∈ₛ⟪ A ⟫↪ m)
    rk : (m : ⟪ A ⟫) → rank (⟪ A ⟫↪ m) ≡ ⟪ A ⟫↪ m
    rk m = IH (⟪ A ⟫↪ m) (mem m) (mem-ord {A = A} ordA (⟪ A ⟫↪ m) (mem m))

    toA : (x : S) → ⟨ x ∈ˢ rank A ⟩ → ⟨ x ∈ˢ A ⟩
    toA x x∈r = PT.rec (snd (x ∈ˢ A))
      (λ { (v , (v∈ₛsett , x∈ₛv)) → PT.rec (snd (x ∈ˢ A))
          (λ { (m , sm≡v) →
              ∈sucV-elim (snd (x ∈ˢ A))
                (∈∈ₛ {a = x} {b = sucV (rank (⟪ A ⟫↪ m))} .snd
                  (subst (λ w → ⟨ x ∈ₛ w ⟩) (sym sm≡v) x∈ₛv))
                (λ x∈rm → ordA .fst (subst (λ w → ⟨ x ∈ˢ w ⟩) (rk m) x∈rm) (mem m))
                (λ x≡rm → subst (λ w → ⟨ w ∈ˢ A ⟩) (sym (x≡rm ∙ rk m)) (mem m)) })
          (∈∈ₛ {a = v} {b = sett ⟪ A ⟫ s} .snd v∈ₛsett) })
      (union-ax (sett ⟪ A ⟫ s) x .fst
        (∈∈ₛ {a = x} {b = ⋃ (sett ⟪ A ⟫ s)} .fst
          (subst (λ w → ⟨ x ∈ˢ w ⟩) (rank-compute A) x∈r)))

    fromA : (x : S) → ⟨ x ∈ˢ A ⟩ → ⟨ x ∈ˢ rank A ⟩
    fromA x x∈A = subst (λ w → ⟨ x ∈ˢ w ⟩) (sym (rank-compute A))
      (∈∈ₛ {a = x} {b = ⋃ (sett ⟪ A ⟫ s)} .snd
        (union-ax (sett ⟪ A ⟫ s) x .snd
          ∣ sucV (rank (⟪ A ⟫↪ m)) , (sm∈ₛsett , x∈ₛsm) ∣₁))
      where
      fibx = ∈-asFiber {a = x} {b = A} x∈A
      m = fibx .fst
      q : ⟪ A ⟫↪ m ≡ x
      q = fibx .snd
      sm∈ₛsett : ⟨ sucV (rank (⟪ A ⟫↪ m)) ∈ₛ sett ⟪ A ⟫ s ⟩
      sm∈ₛsett = ∈∈ₛ {a = sucV (rank (⟪ A ⟫↪ m))} {b = sett ⟪ A ⟫ s} .fst
        ∣ m , refl ∣₁
      x∈ₛsm : ⟨ x ∈ₛ sucV (rank (⟪ A ⟫↪ m)) ⟩
      x∈ₛsm = ∈∈ₛ {a = x} {b = sucV (rank (⟪ A ⟫↪ m))} .fst
        (subst (λ w → ⟨ w ∈ˢ sucV (rank (⟪ A ⟫↪ m)) ⟩) (rk m ∙ q)
          (self∈sucV (rank (⟪ A ⟫↪ m))))
```

<!--en-->
## Recap
<!--zh-->
## 小结
<!--/-->

<!--en-->
`rank`{.Agda} measures every set by an ordinal (`rank-ord`{.Agda}) and fixes
the ordinals themselves (`rank-fix`{.Agda}), which together certify it as the
canonical index. Both proofs are membership inductions on regularity, so the
chapter costs nothing in assumptions. What it buys is the ability to ask "how
far up does this set appear" and get an ordinal answer, and the next two
chapters spend that on the one remaining question about the tower: which
ordinals appear at which stage.
<!--zh-->
`rank`{.Agda} 以序数度量每个集合 (`rank-ord`{.Agda})，并固定序数自身 (`rank-fix`{.Agda})，二者合起来认证它为典范索引。两个证明都是正则性上的成员归纳，故本章在假设上分文不花。它买到的是「这个集合到多高才现身」这一问的序数答案，而接下来两章会把它花在关于塔的最后一个问题上：哪些序数出现在哪个阶段。
<!--/-->
