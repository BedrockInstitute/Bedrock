# Zero, successors, and limits

<!--en-->
The constructible tower needed almost no ordinal theory: its recursion ran
over membership on every set at once, so one equation covered zero,
successors, and limits, and the ordinals only entered through the stage
predicate `IsOrd` and the bound supply of the ordinal chapter. The rud
hierarchy recurses differently. It is a transfinite recursion on the
internal ordinals with an explicit zero clause, an explicit successor
clause, and an explicit limit clause, so the recursion must classify
ordinals before it can run. That classification is this chapter's whole
content: the limit predicate, the zero/successor/limit trichotomy, and the
handful of successor and membership facts the three clauses will spend.
Everything here is concrete ordinal material, so unlike the definability
walks there are no abstract module parameters. The trichotomy is the one
genuinely classical statement, and it takes the excluded middle as a module
parameter in the packaging the comparison chapter established.
<!--zh-->
可构造塔几乎不需要序数理论：它的递归直接在一切集合上沿成员关系运行，一条方程便覆盖零、后继与极限，序数只经由阶段谓词 `IsOrd` 与序数章的上界供给进入。rud 层级则按另一种方式递归。它是对内部序数的超穷递归，显式区分零、后继与极限三种情形，故递归开跑之前必须先给序数分类。这个分类就是本章的全部内容：极限谓词、零/后继/极限三歧，以及三种情形将要花掉的少量后继与成员事实。此处全是具体序数材料，故不同于可定义性诸行走，不需要抽象模块参数。三歧是唯一真正经典的一句，它沿用比较一章确立的打包方式，把排中律取作模块参数。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module L.Rud.OrdArith {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ; ∈-irrefl )
open import V.Model {ℓ} using ( ∈sucV-elim; self∈sucV )
open import L.Constructible {ℓ} using ( IsOrd; isPropIsOrd )
open import L.Ordinal {ℓ} using ( mem-ord )

open import Cubical.Foundations.HLevels using ( isProp× )
open import Cubical.Data.Sigma.Properties using ( Σ≡Prop )
open import Cubical.Data.Sum using ( _⊎_; inl; inr )
open import Cubical.Data.Sum.Properties using ( isProp⊎ )
import Cubical.Data.Empty as Empty
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ∈∈ₛ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ∅; ∅-empty; module InfinitySet )
open InfinitySet using ( sucV )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ
```

<!--en-->
## The successor predicate
<!--zh-->
## 后继谓词
<!--/-->

<!--en-->
The trichotomy's second case names the successor's predecessor, and for the
case analysis to be a proposition it must know that a successor is unique:
two ordinals with the same successor are equal. The proof is a two-way case
analysis through the successor eliminator. Each of `β` and `γ` is a member
of the other's successor, hence a member of the other or equal to it;
equality in either direction finishes, and the two-membership case is a
two-step cycle that transitivity of `β` closes into self-membership, which
regularity forbids.
<!--zh-->
三歧的第二种情形要点名后继的前驱，而要让分情形成为命题，还须知道后继唯一：后继相同的两个序数相等。证明是沿后继消去子的两路分情形。`β` 与 `γ` 各是对方后继的成员，故各是对方的成员或与之相等；任一等式收工，而两个隶属并存的情形构成两步环，`β` 的传递性把它闭成自属，正则性则禁止自属。
<!--/-->

```agda
sucV-inj-ord : {β γ : S} → IsOrd β → IsOrd γ → sucV β ≡ sucV γ → β ≡ γ
sucV-inj-ord {β} {γ} ordβ ordγ eq = go (memOr β γ β∈) (memOr γ β γ∈)
  where
  β∈ : ⟨ β ∈ˢ sucV γ ⟩
  β∈ = subst (λ w → ⟨ β ∈ˢ w ⟩) eq (self∈sucV β)

  γ∈ : ⟨ γ ∈ˢ sucV β ⟩
  γ∈ = subst (λ w → ⟨ γ ∈ˢ w ⟩) (sym eq) (self∈sucV γ)

  memOr : (u w : S) → ⟨ u ∈ˢ sucV w ⟩ → ⟨ u ∈ˢ w ⟩ ⊎ (u ≡ w)
  memOr u w h = ∈sucV-elim {A = w} {x = u}
    (isProp⊎ (snd (u ∈ˢ w)) (isSetS u w) excl) h inl inr
    where
    excl : ⟨ u ∈ˢ w ⟩ → u ≡ w → Empty.⊥
    excl u∈w u≡w = ∈-irrefl u (subst (λ t → ⟨ u ∈ˢ t ⟩) (sym u≡w) u∈w)

  go : (⟨ β ∈ˢ γ ⟩ ⊎ (β ≡ γ)) → (⟨ γ ∈ˢ β ⟩ ⊎ (γ ≡ β)) → β ≡ γ
  go (inl β∈γ) (inl γ∈β) = Empty.rec (∈-irrefl β (ordβ .fst {x = γ} {y = β} β∈γ γ∈β))
  go (inl _)    (inr γ≡β) = sym γ≡β
  go (inr β≡γ)  _         = β≡γ
```

<!--en-->
With uniqueness in hand, "being the successor of an ordinal" is a
proposition, so the excluded middle can be applied to it. The witness is the
predecessor itself, packaged with its ordinality, which is what the
recursion's successor clause will spend.
<!--zh-->
唯一性在手，「是某序数的后继」即为命题，可以喂给排中律。见证就是前驱本身，连同它的序数性一起打包，这正是递归的后继情形将要花掉的东西。
<!--/-->

```agda
isSucc : S → hProp (ℓ-suc ℓ)
isSucc α = (Σ[ β ∈ S ] (IsOrd β × (sucV β ≡ α))) , isPropSucc
  where
  isPropSucc : isProp (Σ[ β ∈ S ] (IsOrd β × (sucV β ≡ α)))
  isPropSucc u v = Σ≡Prop (λ β → isProp× (isPropIsOrd β) (isSetS (sucV β) α))
    (sucV-inj-ord (u .snd .fst) (v .snd .fst) (u .snd .snd ∙ sym (v .snd .snd)))
```

<!--en-->
Two reads of the successor clause follow directly from the hierarchy. The
predecessor belongs to the ordinal it points at, since it belongs to its own
successor; and when the target is an ordinal, so is the predecessor, by
downward closure.
<!--zh-->
后继子句的两条读式直接从层级得出。前驱属于它所指的序数，因为它属于自身的后继；而目标为序数时，前驱亦为序数，由向下封闭。
<!--/-->

```agda
predecessor-mem : (β α : S) → sucV β ≡ α → ⟨ β ∈ˢ α ⟩
predecessor-mem β α eq = subst (λ w → ⟨ β ∈ˢ w ⟩) eq (self∈sucV β)

predecessor-ord : (β α : S) → IsOrd α → sucV β ≡ α → IsOrd β
predecessor-ord β α ordα eq = mem-ord {A = α} ordα β (predecessor-mem β α eq)
```

<!--en-->
And a successor is never zero: the successor of `β` contains `β`, while the
empty set contains nothing. This is the disjointness fact the zero and
successor cases of the trichotomy rest on.
<!--zh-->
以及后继永不为零：`β` 的后继包含 `β`，而空集空无一物。这是三歧的零与后继两种情形所依据的互斥事实。
<!--/-->

```agda
succ-not-zero : (β : S) → sucV β ≡ ∅ → Empty.⊥
succ-not-zero β eq = ∅-empty β (∈∈ₛ {a = β} {b = ∅} .fst (predecessor-mem β ∅ eq))
```

<!--en-->
## The limit predicate
<!--zh-->
## 极限谓词
<!--/-->

<!--en-->
A limit ordinal is an ordinal that is neither zero nor a successor. All
three conjuncts are propositions, so the predicate is an hProp, and the
limit clause reads it by the three projections: it is an ordinal, it is not
zero, and it is not a successor. Since the last is "not a successor of an
ordinal", a successor is never a limit.
<!--zh-->
极限序数是指既非零也非后继的序数。三个合取项都是命题，故这个谓词是 hProp，极限情形经三个投影读它：它是序数、它非零、它非后继。由于最后一条是「非某序数的后继」，后继永不是极限。
<!--/-->

```agda
isLimit : S → hProp (ℓ-suc ℓ)
isLimit α = ( IsOrd α × ((α ≡ ∅) → Empty.⊥) × (⟨ isSucc α ⟩ → Empty.⊥) )
          , isProp× (isPropIsOrd α)
              (isProp× (isPropΠ (λ _ → Empty.isProp⊥)) (isPropΠ (λ _ → Empty.isProp⊥)))

isLimit-ord : (α : S) → ⟨ isLimit α ⟩ → IsOrd α
isLimit-ord _ lim = lim .fst

isLimit-not-zero : (α : S) → ⟨ isLimit α ⟩ → α ≡ ∅ → Empty.⊥
isLimit-not-zero _ lim = lim .snd .fst

isLimit-not-succ : (α : S) → ⟨ isLimit α ⟩ → ⟨ isSucc α ⟩ → Empty.⊥
isLimit-not-succ _ lim = lim .snd .snd

succ-not-limit : (β : S) → IsOrd β → ⟨ isLimit (sucV β) ⟩ → Empty.⊥
succ-not-limit β ordβ lim = isLimit-not-succ (sucV β) lim (β , (ordβ , refl))
```

<!--en-->
The limit clause's membership fact: every member of a limit is an ordinal,
by downward closure. The recursion's limit case needs exactly this to hand
its inductive hypothesis an ordinal at each member.
<!--zh-->
极限情形的成员事实：极限的每个成员都是序数，由向下封闭。递归的极限情形正是借此在每位成员处把序数交给归纳假设。
<!--/-->

```agda
limit-mem-ord : (α : S) → ⟨ isLimit α ⟩ → (x : S) → ⟨ x ∈ˢ α ⟩ → IsOrd x
limit-mem-ord α lim x x∈α = mem-ord {A = α} (isLimit-ord α lim) x x∈α
```

<!--en-->
## The trichotomy
<!--zh-->
## 三歧
<!--/-->

<!--en-->
The chapter's deliverable: every ordinal is zero, a successor, or a limit.
The excluded middle decides the first two cases, and the third is their
joint negation. In the successor case the witness carries the predecessor
together with its ordinality, so the recursion's successor clause can
descend to it without further work, and the limit case arrives ready for
the union clause.
<!--zh-->
本章的交付物：每个序数或是零、或是后继、或是极限。排中律判定前两种情形，第三种是它们共同的否定。后继情形中的见证随身携带前驱及其序数性，递归的后继情形无须再作他用即可沿它下降，极限情形则直接备好给并的情形。
<!--/-->

```agda
ord-case : (α : S) → IsOrd α
         → (α ≡ ∅) ⊎ (⟨ isSucc α ⟩ ⊎ ⟨ isLimit α ⟩)
ord-case α ordα = decide (lem ((α ≡ ∅) , isSetS α ∅)) (lem (isSucc α))
  where
  decide : (α ≡ ∅) ⊎ ((α ≡ ∅) → Empty.⊥)
         → ⟨ isSucc α ⟩ ⊎ (⟨ isSucc α ⟩ → Empty.⊥)
         → (α ≡ ∅) ⊎ (⟨ isSucc α ⟩ ⊎ ⟨ isLimit α ⟩)
  decide (inl z) _         = inl z
  decide (inr nz) (inl s)  = inr (inl s)
  decide (inr nz) (inr ns) = inr (inr (ordα , nz , ns))
```

<!--en-->
## Recap
<!--zh-->
## 小结
<!--/-->

<!--en-->
This chapter classifies ordinals. `ord-case`{.Agda} splits any ordinal into
zero, successor, or limit; `isLimit`{.Agda} names the third case as an hProp
with its three reads; and the successor lemmas supply the predecessor, its
membership, and the disjointness facts the split rests on. The recursion's
three clauses are exactly the three disjuncts: the base at zero, one step at
a successor, the union over members at a limit. The union fact itself is not
re-proved here; the ordinal chapter's `setUnion-ord`{.Agda} already covers
the limit clause, indexed by the small family of members. The hierarchy
chapter of the rud development spends all of this.
<!--zh-->
本章给序数分类。`ord-case`{.Agda} 把每个序数分成零、后继或极限；`isLimit`{.Agda} 把第三种情形命名为 hProp 并配三条读式；后继诸引理则供应前驱、其成员关系，以及分情形所依据的互斥事实。递归的三种情形恰是三个析取支：零处取基底、后继处走一步、极限处沿成员取并。并的事实此处不再重证；序数章的 `setUnion-ord`{.Agda} 已经覆盖极限情形，以成员的小族为索引。rud 开发的层级一章将花掉这一切。
<!--/-->
