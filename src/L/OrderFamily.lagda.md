# The order family

<!--en-->
The wing's internal order is two objects, and the classical text names both
in one lemma (SZ 1.11(1)): each level's order is an element, and the orders
of the levels below a level form a sequence that is again one set. The second
object, the family table, can be built over the first without any formula:
the table is a `sett`{.Agda} over the small presentation of the index, its
membership is read at the small index, and the two assembly laws, the
successor agreement and the limit union, follow from the interface alone.
This chapter fixes that interface, the per-level order as an element, builds
the table over it, proves the two laws, and closes the interface at the empty
level. The object-language formula that discharges the interface, and the
initial-segment facts, belong to later chapters (the order-formula chapter
and the initial-segment chapter); nothing here needs a formula.
<!--zh-->
翼的内部序是两个对象，经典文本在一条引理里同时点名二者 (SZ 1.11 (1))：每一层的序是一个元素，而一层之下诸层的序构成一个序列，这个序列也是一个集合。第二个对象，即族表，可以在第一个对象之上无需任何公式地建成：表是索引的小呈现上的 `sett`{.Agda}，其隶属在小索引处读出，而两条装配律，后继相合与极限之并，单凭界面即成立。本章定下那个界面，即「每一层的序作为元素」，在其上建表、证两条律，并在空层处闭合界面。兑付界面的对象语言公式，以及初始段诸事实，属于后面的章节 (序公式章与初始段章)；此处的一切都不需要公式。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; sett )

module L.OrderFamily {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) (A : V ℓ) where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ; extensionalV )
open import V.Model {ℓ} using ( self∈sucV; ∈sucV-elim )
open import V.Coding {ℓ} using ( pr )
open import V.Presentation {ℓ} using ( member; fiber )
open import L.Constructible {ℓ} using ( IsOrd )
open import L.Ordinal {ℓ} using ( mem-ord; suc-ord )
open import L.Ordinal.Linear {ℓ} lem using ( ord-tri; Tri )
open import L.Rud.OrdArith {ℓ} lem using ( isLimit )
open import L.Rud.Step {ℓ} lem A using
  ( step; step-in-self; step-⊆; step-∈; step-mono∈; step-trans
  ; Sset; Sset-mono; Sset-zero; Sset-suc; Sset-limit )
open import L.Rud.Hierarchy {ℓ} lem step step-⊆ step-∈ step-mono∈ step-trans
  using ( Sset-levelFam; Sset-index-mono )
open import L.Rud.Order {ℓ} lem A using ( Member; Sset-below; order-agrees )
open import Cubical.Data.Sum using ( _⊎_; inl; inr )
open import Cubical.Functions.Logic using ( ⇔toPath )
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁; squash₁ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ∅; ∅-empty; ⋃_; union-ax; module InfinitySet )
open InfinitySet using ( sucV )
open import Cubical.HITs.CumulativeHierarchy.Properties
  using ( _∈ₛ_; ∈∈ₛ; ⟪_⟫; ⟪_⟫↪ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ
```

<!--en-->
## The per-level order as an element

The interface bundles four facts about the order element at a level. It is an
element of the level's successor, the honest reading the W3 gate recorded for
the family-table statement. A pair of members lies in it exactly when the
pair is below in the level's order, in both directions. And every member of
it is such a pair, which is what makes the element the internalized relation
rather than a set that happens to carry the pairs. The ordinality of the
level is a separate hypothesis, handed to each certificate at the point of
use, never packed into the element or its index: the interface is a dependent
sum indexed by the level alone. The order-formula chapter will discharge it:
its formula carves the pair set as a definable subset, which is how the
two-way read and the level membership are proved.
<!--zh-->
## 作为元素的逐层之序

界面把关于某层序元素的四件事打成一组。它是该层后继的一个元素，即 W3 门为族表陈述记下的诚实读法。一对成员落在它里面，当且仅当该对在该层之序中居下，两个方向都如此。而它的每个成员都是这样的一对，正是这一点使元素成为内化的关系，而非一个碰巧装着诸对的集合。层的序数性是单独一条假设，在使用处交给每份证书，从不打进元素或其索引：界面是只以层为索引的相依和。序公式章将兑付它：其公式把对集刻成可定义子集，双向读法与层隶属正是这样证出的。
<!--/-->

```agda
OrderAtAt : S → Type (ℓ-suc ℓ)
OrderAtAt α =
  Σ[ w ∈ S ] ( ⟨ w ∈ˢ Sset (sucV α) ⟩
             × ((ordα : IsOrd α) (m n : Member α) → Sset-below α ordα m n
                → ⟨ pr (m .fst) (n .fst) ∈ˢ w ⟩)
             × ((ordα : IsOrd α) (m n : Member α)
                → ⟨ pr (m .fst) (n .fst) ∈ˢ w ⟩
                → Sset-below α ordα m n)
             × ((ordα : IsOrd α) (z : S) → ⟨ z ∈ˢ w ⟩
                → ∥ Σ[ m ∈ Member α ] Σ[ n ∈ Member α ]
                    (z ≡ pr (m .fst) (n .fst)) ∥₁) )
```

<!--en-->
The pair read at the small presentation is the shape the order-formula
chapter's adequacy will consume: the presentation implicits are pinned
through the presentation head, and the memberships are stated at
`⟪ Sset α ⟫`{.Agda}, never at a concrete tower index.
<!--zh-->
小呈现处的对读式，就是序公式章的充分性将要消费的形状：呈现隐参经呈现头部钉死，隶属陈述在 `⟪ Sset α ⟫`{.Agda} 处，绝不在具体塔索引处。
<!--/-->

```agda
orderAt-small : (α : S) (ordα : IsOrd α) (oa : OrderAtAt α)
              → (a b : ⟪ Sset α ⟫)
              → (⟨ pr (⟪ Sset α ⟫↪ a) (⟪ Sset α ⟫↪ b) ∈ˢ oa .fst ⟩
                → Sset-below α ordα (⟪ Sset α ⟫↪ a , member (Sset α) a)
                                     (⟪ Sset α ⟫↪ b , member (Sset α) b))
              × (Sset-below α ordα (⟪ Sset α ⟫↪ a , member (Sset α) a)
                                   (⟪ Sset α ⟫↪ b , member (Sset α) b)
                → ⟨ pr (⟪ Sset α ⟫↪ a) (⟪ Sset α ⟫↪ b) ∈ˢ oa .fst ⟩)
orderAt-small α ordα oa a b =
  oa .snd .snd .snd .fst ordα (⟪ Sset α ⟫↪ a , member (Sset α) a)
                              (⟪ Sset α ⟫↪ b , member (Sset α) b) ,
  oa .snd .snd .fst ordα (⟪ Sset α ⟫↪ a , member (Sset α) a)
                         (⟪ Sset α ⟫↪ b , member (Sset α) b)
```

<!--en-->
One piece of vocabulary is needed before the table: pointwise inclusion of
sets, with mutual inclusion giving equality by the hierarchy's
extensionality. This is the only equality engine the assembly laws use.
<!--zh-->
建表之前需要一件词汇：集合的逐点包含，互相包含按层级的外延性给出相等。这是装配律唯一用到的相等引擎。
<!--/-->

```agda
_⊆_ : S → S → Type (ℓ-suc ℓ)
u ⊆ v = (x : S) → ⟨ x ∈ˢ u ⟩ → ⟨ x ∈ˢ v ⟩

ext-⊆ : {u v : S} → u ⊆ v → v ⊆ u → u ≡ v
ext-⊆ {u} {v} sub sup = extensionalV (λ x → ⇔toPath (sub x) (sup x))
```

<!--en-->
## The family table

The family table assembles the levels into one order. Over a family of order
elements, the table at a level `β` is the set of the order elements at the
members of `β`, indexed by the small presentation `⟪ β ⟫`{.Agda}, exactly the
W2 family pattern. The construction is sealed at its birth site, and its two
membership readings, the hit and the out-read, are proved inside the seal:
membership in the table is merely being hit by the family, so each reading is
the identity. This is the pattern of the codes chapter, applied to orders.
<!--zh-->
## 族表

族表把诸层装进一个序。给定一族序元素，在层 `β` 处，表是 `β` 的诸成员处序元素之集，以小呈现 `⟪ β ⟫`{.Agda} 为索引，正是 W2 族模式。构造在其诞生处封印，两条隶属读法，命中与读出，在封印之内证出：属于这个表仅仅是被族命中，故每条读法都是恒等。这是码章的模式，施于序。
<!--/-->

```agda
module OrderFamily (oaf : (α : S) → OrderAtAt α) where

  orderAt : (α : S) → S
  orderAt α = oaf α .fst

  orderAt-in : (α : S) → ⟨ orderAt α ∈ˢ Sset (sucV α) ⟩
  orderAt-in α = oaf α .snd .fst

  orderAt-pair-in : (α : S) (ordα : IsOrd α) (m n : Member α)
                  → Sset-below α ordα m n
                  → ⟨ pr (m .fst) (n .fst) ∈ˢ orderAt α ⟩
  orderAt-pair-in α ordα = oaf α .snd .snd .fst ordα

  orderAt-pair-out : (α : S) (ordα : IsOrd α) (m n : Member α)
                   → ⟨ pr (m .fst) (n .fst) ∈ˢ orderAt α ⟩
                   → Sset-below α ordα m n
  orderAt-pair-out α ordα = oaf α .snd .snd .snd .fst ordα

  orderAt-pairs : (α : S) (ordα : IsOrd α) (z : S)
                → ⟨ z ∈ˢ orderAt α ⟩
                → ∥ Σ[ m ∈ Member α ] Σ[ n ∈ Member α ]
                    (z ≡ pr (m .fst) (n .fst)) ∥₁
  orderAt-pairs α ordα = oaf α .snd .snd .snd .snd ordα

  orderFam : (β : S) → ⟪ β ⟫ → S
  orderFam β m = orderAt (⟪ β ⟫↪ m)

  opaque
    orderTable : (β : S) → S
    orderTable β = sett ⟪ β ⟫ (orderFam β)

    orderTable-hit : (β : S) (m : ⟪ β ⟫)
                   → ⟨ orderFam β m ∈ˢ orderTable β ⟩
    orderTable-hit β m = ∣ m , refl ∣₁

    orderTable-out : (β : S) (z : S)
                   → ⟨ z ∈ˢ orderTable β ⟩
                   → ∥ Σ[ m ∈ ⟪ β ⟫ ] (orderFam β m ≡ z) ∥₁
    orderTable-out β z h = h
```

<!--en-->
The table itself as an element of a level is a definable set, and needs the
order-formula chapter; what is proved here is that its entries are all in
place. Each entry lies in the level one past `β`: the order element at `γ`
lives one past `γ` by the interface, the index of the entry is a member of
`β`, so the successor of `γ` is included in `β`, and the tower is monotone in
its index. This is the part of SZ 1.11(1)'s "in particular" that the
interface alone supplies.
<!--zh-->
表自身作为某层的元素是一个可定义集，需要序公式章；此处证的是它的条目全部就位。每个条目都落在 `β` 之后一层：`γ` 处的序元素按界面住在 `γ` 之后一层，条目的索引是 `β` 的成员，故 `γ` 的后继包含于 `β`，而塔对索引单调。这是 SZ 1.11 (1) 的「特别地」那句里界面单独供应的一部分。
<!--/-->

```agda
  orderTable-level : (β : S) (ordβ : IsOrd β) (m : ⟪ β ⟫)
                   → ⟨ orderFam β m ∈ˢ Sset (sucV β) ⟩
  orderTable-level β ordβ m = Sset-mono {α = sucV β} {β = β} (self∈sucV β)
    (orderAt γ)
    (Sset-index-mono {α = sucV γ} {β = β} sucγ⊆β (orderAt γ)
      (orderAt-in γ))
    where
    γ : S
    γ = ⟪ β ⟫↪ m
    γ∈β : ⟨ γ ∈ˢ β ⟩
    γ∈β = member β m
    ordγ : IsOrd γ
    ordγ = mem-ord {β} ordβ γ γ∈β
    sucγ⊆β : sucV γ ⊆ β
    sucγ⊆β z z∈sucγ = ∈sucV-elim (snd (z ∈ˢ β)) z∈sucγ
      (λ z∈γ → ordβ .fst {x = γ} {y = z} z∈γ γ∈β)
      (λ z≡γ → subst (λ w → ⟨ w ∈ˢ β ⟩) (sym z≡γ) γ∈β)
```

<!--en-->
## The assembly laws

Two laws say how the table assembles the per-level orders into one order, and
both follow from the interface alone. The successor agreement: a pair of old
members is below in the order at the successor exactly when it is below at
the earlier level, because the key of a set does not mention the level it is
read at, the delivered coherence of the producer order. The limit assembly:
at a limit, the order element is the union of the table, the element-level
reading of the classical limit clause. One direction takes a pair below at
the limit, finds the two members' birth levels below the limit, takes the
greater as the common stage, and re-reads the pair at that stage; the other
reads an entry of the table, sees the pair, and lifts the comparison back to
the limit.
<!--zh-->
## 装配律

两条律说明表如何把逐层之序装进一个序，二者都单凭界面成立。后继相合：一对旧成员在后继之序中居下，当且仅当它在更早一层居下，因为一个集合的键不提及它被读取的那一层，即生产者序已交付的相合。极限装配：在极限处，序元素是表的并，即经典极限子句的元素级读法。一个方向取极限处居下的一对，找到两个成员的诞生层，取较大者为公共阶段，在该阶段重读这一对；另一方向读出一个条目，看见这一对，再把比较抬回极限。
<!--/-->

```agda
  orderAt-suc-old : (β : S) (ordβ : IsOrd β) (x y : S)
                  → (hx : ⟨ x ∈ˢ Sset β ⟩) (hy : ⟨ y ∈ˢ Sset β ⟩)
                  → (⟨ pr x y ∈ˢ orderAt (sucV β) ⟩
                    → ⟨ pr x y ∈ˢ orderAt β ⟩)
                  × (⟨ pr x y ∈ˢ orderAt β ⟩
                    → ⟨ pr x y ∈ˢ orderAt (sucV β) ⟩)
  orderAt-suc-old β ordβ x y hx hy = fwd , bwd
    where
    x∈suc : ⟨ x ∈ˢ Sset (sucV β) ⟩
    x∈suc = Sset-mono {α = sucV β} {β = β} (self∈sucV β) x hx
    y∈suc : ⟨ y ∈ˢ Sset (sucV β) ⟩
    y∈suc = Sset-mono {α = sucV β} {β = β} (self∈sucV β) y hy
    agree : Sset-below (sucV β) (suc-ord ordβ) (x , x∈suc) (y , y∈suc)
          ≡ Sset-below β ordβ (x , hx) (y , hy)
    agree = order-agrees (sucV β) β (suc-ord ordβ) ordβ x y x∈suc y∈suc hx hy
    fwd : ⟨ pr x y ∈ˢ orderAt (sucV β) ⟩
        → ⟨ pr x y ∈ˢ orderAt β ⟩
    fwd h = orderAt-pair-in β ordβ (x , hx) (y , hy)
      (transport agree (orderAt-pair-out (sucV β) (suc-ord ordβ)
        (x , x∈suc) (y , y∈suc) h))
    bwd : ⟨ pr x y ∈ˢ orderAt β ⟩
        → ⟨ pr x y ∈ˢ orderAt (sucV β) ⟩
    bwd h = orderAt-pair-in (sucV β) (suc-ord ordβ) (x , x∈suc) (y , y∈suc)
      (transport (sym agree) (orderAt-pair-out β ordβ (x , hx) (y , hy) h))
```

<!--en-->
Two helpers carry the limit assembly. The membership of a member of a limit
level in an earlier level is read through the delivered limit equation, and
the cover lemma places the order element at an arbitrary earlier stage inside
the table.
<!--zh-->
两条辅助承载极限装配。极限层成员在更早层的隶属经已交付的极限方程读出；覆盖引理把任意更早阶段处的序元素放进表里。
<!--/-->

```agda
  member-in : (β : S) (ordβ : IsOrd β) (x : S) (hx : ⟨ x ∈ˢ Sset β ⟩)
            → (limβ : ⟨ isLimit β ⟩)
            → ∥ Σ[ m ∈ ⟪ β ⟫ ] (⟨ x ∈ˢ Sset (⟪ β ⟫↪ m) ⟩) ∥₁
  member-in β ordβ x hx limβ = PT.rec squash₁ go1
    (union-ax (sett ⟪ β ⟫ (Sset-levelFam β)) x .fst
      (∈∈ₛ {a = x} {b = ⋃ (sett ⟪ β ⟫ (Sset-levelFam β))} .fst
        (subst (λ w → ⟨ x ∈ˢ w ⟩) (Sset-limit β limβ) hx)))
    where
    go3 : (v : S) (x∈ₛv : ⟨ x ∈ₛ v ⟩)
        → Σ[ m ∈ ⟪ β ⟫ ] (Sset-levelFam β m ≡ v)
        → ∥ Σ[ m ∈ ⟪ β ⟫ ] (⟨ x ∈ˢ Sset (⟪ β ⟫↪ m) ⟩) ∥₁
    go3 v x∈ₛv (m , e) = ∣ m , subst (λ w → ⟨ x ∈ˢ w ⟩) (sym e)
      (∈∈ₛ {a = x} {b = v} .snd x∈ₛv) ∣₁
    go2 : (v : S) (x∈ₛv : ⟨ x ∈ₛ v ⟩)
        → ∥ Σ[ m ∈ ⟪ β ⟫ ] (Sset-levelFam β m ≡ v) ∥₁
        → ∥ Σ[ m ∈ ⟪ β ⟫ ] (⟨ x ∈ˢ Sset (⟪ β ⟫↪ m) ⟩) ∥₁
    go2 v x∈ₛv = PT.rec squash₁ (go3 v x∈ₛv)
    go1 : Σ[ v ∈ S ] (⟨ v ∈ₛ sett ⟪ β ⟫ (Sset-levelFam β) ⟩ × ⟨ x ∈ₛ v ⟩)
        → ∥ Σ[ m ∈ ⟪ β ⟫ ] (⟨ x ∈ˢ Sset (⟪ β ⟫↪ m) ⟩) ∥₁
    go1 (v , (v∈ₛsett , x∈ₛv)) = go2 v x∈ₛv
      (∈∈ₛ {a = v} {b = sett ⟪ β ⟫ (Sset-levelFam β)} .snd v∈ₛsett)

  orderTable-cover : (β : S) (ε : S) (ε∈β : ⟨ ε ∈ˢ β ⟩)
                   → ⟨ orderAt ε ∈ˢ orderTable β ⟩
  orderTable-cover β ε ε∈β =
    subst (λ v → ⟨ orderAt v ∈ˢ orderTable β ⟩)
      (fiber β ε∈β .snd)
      (orderTable-hit β (fiber β ε∈β .fst))
```

```agda
  orderAt-limit : (β : S) (ordβ : IsOrd β) (limβ : ⟨ isLimit β ⟩)
                → orderAt β ≡ ⋃ (orderTable β)
  orderAt-limit β ordβ limβ = ext-⊆ sub sup
    where
    sub : (z : S) → ⟨ z ∈ˢ orderAt β ⟩ → ⟨ z ∈ˢ (⋃ (orderTable β)) ⟩
    sub z z∈ = PT.rec (snd (z ∈ˢ (⋃ (orderTable β)))) pairs-step
      (orderAt-pairs β ordβ z z∈)
      where
      pairs-step : Σ[ m ∈ Member β ] Σ[ n ∈ Member β ] (z ≡ pr (m .fst) (n .fst))
                 → ⟨ z ∈ˢ (⋃ (orderTable β)) ⟩
      pairs-step (m , n , e) = PT.rec (snd (z ∈ˢ (⋃ (orderTable β)))) x-step
        (member-in β ordβ (m .fst) (m .snd) limβ)
        where
        belowβ : Sset-below β ordβ m n
        belowβ = orderAt-pair-out β ordβ m n
          (subst (λ w → ⟨ w ∈ˢ orderAt β ⟩) e z∈)
        x-step : Σ[ gm ∈ ⟪ β ⟫ ] ⟨ m .fst ∈ˢ Sset (⟪ β ⟫↪ gm) ⟩
               → ⟨ z ∈ˢ (⋃ (orderTable β)) ⟩
        x-step (gm , x∈γ) = PT.rec (snd (z ∈ˢ (⋃ (orderTable β)))) y-step
          (member-in β ordβ (n .fst) (n .snd) limβ)
          where
          y-step : Σ[ gn ∈ ⟪ β ⟫ ] ⟨ n .fst ∈ˢ Sset (⟪ β ⟫↪ gn) ⟩
                 → ⟨ z ∈ˢ (⋃ (orderTable β)) ⟩
          y-step (gn , y∈δ) = choose (ord-tri γ ordγ δ ordδ)
            where
            γ : S
            γ = ⟪ β ⟫↪ gm
            δ : S
            δ = ⟪ β ⟫↪ gn
            γ∈β : ⟨ γ ∈ˢ β ⟩
            γ∈β = member β gm
            δ∈β : ⟨ δ ∈ˢ β ⟩
            δ∈β = member β gn
            ordγ : IsOrd γ
            ordγ = mem-ord {β} ordβ γ γ∈β
            ordδ : IsOrd δ
            ordδ = mem-ord {β} ordβ δ δ∈β
            via : (ε : S) → (⟨ γ ∈ˢ ε ⟩ ⊎ (γ ≡ ε)) → (⟨ δ ∈ˢ ε ⟩ ⊎ (δ ≡ ε))
                → ⟨ ε ∈ˢ β ⟩ → ⟨ z ∈ˢ (⋃ (orderTable β)) ⟩
            via ε x∈ε y∈ε ε∈β = ∈∈ₛ {a = z} {b = ⋃ (orderTable β)} .snd
              (union-ax (orderTable β) z .snd
                ∣ orderAt ε , (entry∈ₛ , z∈ₛentry) ∣₁)
              where
              ordε : IsOrd ε
              ordε = mem-ord {β} ordβ ε ε∈β
              liftStage : (η : S) (w : S) → ⟨ w ∈ˢ Sset η ⟩
                        → (⟨ η ∈ˢ ε ⟩ ⊎ (η ≡ ε)) → ⟨ w ∈ˢ Sset ε ⟩
              liftStage η w w∈η (inl η∈ε) = Sset-mono {α = ε} {β = η} η∈ε w w∈η
              liftStage η w w∈η (inr η≡ε) = subst (λ v → ⟨ w ∈ˢ Sset v ⟩) η≡ε w∈η
              x∈ε' : ⟨ m .fst ∈ˢ Sset ε ⟩
              x∈ε' = liftStage γ (m .fst) x∈γ x∈ε
              y∈ε' : ⟨ n .fst ∈ˢ Sset ε ⟩
              y∈ε' = liftStage δ (n .fst) y∈δ y∈ε
              belowε : Sset-below ε ordε (m .fst , x∈ε') (n .fst , y∈ε')
              belowε = transport (sym (order-agrees ε β ordε ordβ
                (m .fst) (n .fst) x∈ε' y∈ε' (m .snd) (n .snd))) belowβ
              z∈entry : ⟨ z ∈ˢ orderAt ε ⟩
              z∈entry = subst (λ w → ⟨ w ∈ˢ orderAt ε ⟩) (sym e)
                (orderAt-pair-in ε ordε (m .fst , x∈ε') (n .fst , y∈ε') belowε)
              entry∈ : ⟨ orderAt ε ∈ˢ orderTable β ⟩
              entry∈ = orderTable-cover β ε ε∈β
              entry∈ₛ : ⟨ orderAt ε ∈ₛ orderTable β ⟩
              entry∈ₛ = ∈∈ₛ {a = orderAt ε} {b = orderTable β} .fst entry∈
              z∈ₛentry : ⟨ z ∈ₛ orderAt ε ⟩
              z∈ₛentry = ∈∈ₛ {a = z} {b = orderAt ε} .fst z∈entry
            choose : Tri γ δ → ⟨ z ∈ˢ (⋃ (orderTable β)) ⟩
            choose (inl γ∈δ) = via δ (inl γ∈δ) (inr refl) δ∈β
            choose (inr (inl γ≡δ)) = via γ (inr refl) (inr (sym γ≡δ)) γ∈β
            choose (inr (inr δ∈γ)) = via γ (inr refl) (inl δ∈γ) γ∈β

    sup : (z : S) → ⟨ z ∈ˢ (⋃ (orderTable β)) ⟩ → ⟨ z ∈ˢ orderAt β ⟩
    sup z z∈⋃ = PT.rec (snd (z ∈ˢ orderAt β)) cover-step
      (union-ax (orderTable β) z .fst
        (∈∈ₛ {a = z} {b = ⋃ (orderTable β)} .fst z∈⋃))
      where
      cover-step : Σ[ v ∈ S ] (⟨ v ∈ₛ orderTable β ⟩ × ⟨ z ∈ₛ v ⟩)
                 → ⟨ z ∈ˢ orderAt β ⟩
      cover-step (v , (v∈ₛt , z∈ₛv)) = PT.rec (snd (z ∈ˢ orderAt β))
        entry-step (orderTable-out β v
          (∈∈ₛ {a = v} {b = orderTable β} .snd v∈ₛt))
        where
        entry-step : Σ[ m ∈ ⟪ β ⟫ ] (orderFam β m ≡ v)
                   → ⟨ z ∈ˢ orderAt β ⟩
        entry-step (m , e) = PT.rec (snd (z ∈ˢ orderAt β)) pair-step
          (orderAt-pairs γ ordγ z z∈γ)
          where
          γ : S
          γ = ⟪ β ⟫↪ m
          γ∈β : ⟨ γ ∈ˢ β ⟩
          γ∈β = member β m
          ordγ : IsOrd γ
          ordγ = mem-ord {β} ordβ γ γ∈β
          z∈γ : ⟨ z ∈ˢ orderAt γ ⟩
          z∈γ = subst (λ w → ⟨ z ∈ˢ w ⟩) (sym e)
            (∈∈ₛ {a = z} {b = v} .snd z∈ₛv)
          pair-step : Σ[ m' ∈ Member γ ] Σ[ n' ∈ Member γ ]
                      (z ≡ pr (m' .fst) (n' .fst))
                    → ⟨ z ∈ˢ orderAt β ⟩
          pair-step (m' , n' , e') = subst (λ w → ⟨ w ∈ˢ orderAt β ⟩) (sym e')
            (orderAt-pair-in β ordβ (x , x∈β) (y , y∈β) belowβ)
            where
            x : S
            x = m' .fst
            y : S
            y = n' .fst
            belowγ : Sset-below γ ordγ m' n'
            belowγ = orderAt-pair-out γ ordγ m' n'
              (subst (λ w → ⟨ w ∈ˢ orderAt γ ⟩) e' z∈γ)
            x∈β : ⟨ x ∈ˢ Sset β ⟩
            x∈β = Sset-mono {α = β} {β = γ} γ∈β x (m' .snd)
            y∈β : ⟨ y ∈ˢ Sset β ⟩
            y∈β = Sset-mono {α = β} {β = γ} γ∈β y (n' .snd)
            belowβ : Sset-below β ordβ (x , x∈β) (y , y∈β)
            belowβ = transport (order-agrees γ β ordγ ordβ
              x y (m' .snd) (n' .snd) x∈β y∈β) belowγ
```

<!--en-->
## The base instance

The interface is inhabited at the empty level. The order at `∅` relates no
members, so its element is the empty set, which is a member of the level's
successor. The certificates at `∅` are the vacuous readings, and this
positive control shows the family-table laws are not conditional on an empty
interface.
<!--zh-->
## 基底实例

界面在空层处有居民。`∅` 处的序不关联任何成员，故其元素就是空集，而空集是层后继的成员。`∅` 处的证书都是空洞读法，这条正对照表明族表诸律并非以空界面为前提。
<!--/-->

```agda
∅∅ : (x : S) → ⟨ x ∈ˢ ∅ ⟩ → Empty.⊥
∅∅ x h = ∅-empty x (∈∈ₛ {a = x} {b = ∅} .fst h)

member-absurd : (m : Member ∅) → Empty.⊥
member-absurd m = ∅∅ (m .fst) (subst (λ w → ⟨ m .fst ∈ˢ w ⟩) (Sset-zero) (m .snd))

base-in : ⟨ ∅ ∈ˢ Sset (sucV ∅) ⟩
base-in = subst (λ w → ⟨ ∅ ∈ˢ w ⟩) (sym (Sset-suc ∅))
  (subst (λ w → ⟨ w ∈ˢ step (Sset ∅) ⟩) (Sset-zero) (step-in-self (Sset ∅)))

base-pair-in : (ordα : IsOrd ∅) (m n : Member ∅) → Sset-below ∅ ordα m n
             → ⟨ pr (m .fst) (n .fst) ∈ˢ ∅ ⟩
base-pair-in ordα m n _ = Empty.rec (member-absurd m)

base-pair-out : (ordα : IsOrd ∅) (m n : Member ∅)
              → ⟨ pr (m .fst) (n .fst) ∈ˢ ∅ ⟩
              → Sset-below ∅ ordα m n
base-pair-out ordα m n h = Empty.rec (member-absurd m)

base-pairs : (ordα : IsOrd ∅) (z : S) → ⟨ z ∈ˢ ∅ ⟩
           → ∥ Σ[ m ∈ Member ∅ ] Σ[ n ∈ Member ∅ ]
               (z ≡ pr (m .fst) (n .fst)) ∥₁
base-pairs ordα z h = Empty.rec (∅∅ z h)

base : OrderAtAt ∅
base = ∅ , base-in , (base-pair-in , (base-pair-out , base-pairs))
```

<!--en-->
## Recap

The chapter fixes the per-level order as an element, the interface the
order-formula chapter will discharge, and builds over it the family table
that assembles the levels into one order. The table is a `sett`{.Agda} over
the small presentation of the index, sealed with its two membership readings;
its entries lie in the level one past the index by the interface and the
tower's index monotonicity. The successor agreement and the limit assembly
show how the table reads back into the per-level orders: the order at a
successor agrees with the order below on old members, and the order at a
limit is the union of the table, the element-level reading of the classical
limit clause. The interface is inhabited at the empty level, where the order
element is the empty set. What remains for the order-formula chapter is the
formula whose definable set is the order element, and what remains for the
initial-segment chapter is the reading of the table's own level membership.
<!--zh-->
## 小结

本章定下「每一层的序作为元素」，即序公式章将要兑付的界面，并在其上建成把诸层装进一个序的族表。表是索引的小呈现上的 `sett`{.Agda}，以两条隶属读法封印；按界面与塔的索引单调性，其条目落在索引之后一层。后继相合与极限装配说明表如何读回逐层之序：后继处的序与下方之序在旧成员上一致，而极限处的序是表的并，即经典极限子句的元素级读法。界面在空层处有居民，那里的序元素就是空集。留给序公式章的是其可定义集恰为序元素的那条公式，留给初始段章的是表自身层隶属的读法。
<!--/-->
