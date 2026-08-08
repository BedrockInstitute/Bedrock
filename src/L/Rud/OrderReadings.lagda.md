# The order read at a level

<!--en-->
The canonical order is one comparison, read at every level at once, and this
chapter is that reading. The machinery lives in `L.Rud.Order`{.Agda}: the
producer tree, its lexicographic comparison, the least-producer key, and the
level order pulled back along it. This chapter reads the order off the key at a
level. Four readings follow: a stage-bounded producer whose stage belongs to
the index describes a member of the level; the reading of two sets does not
depend on the level it is read at; a member's key carries its birth stage; and
the successor clauses say how an old member precedes a new one.
<!--zh-->
典范的序是同一个比较，在所有层上一并读取，而本章就是那次读取。机制住在 `L.Rud.Order`{.Agda} 里：生产者树、它的字典比较、最小生产者键，以及沿键拉回的层序。本章在某一层上经键读出序。由此得四条读法：阶段落在索引之内的循阶生产者描述该层的一个成员；两个集合的读法与读取它们的层无关；成员的键携带它的诞生阶段；后继处的诸子句说出旧成员如何先于新成员。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V )

module L.Rud.OrderReadings {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) (A : V ℓ) where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ; ∈-irrefl )
open import V.Model {ℓ} using ( ∈sucV-elim; self∈sucV )
open import L.Constructible {ℓ} using ( IsOrd )
open import L.Ordinal {ℓ} using ( suc-ord )
open import L.Ordinal.Linear {ℓ} lem using ( ord-tri ) renaming ( Tri to OrdTri )
open import L.Rud.Step {ℓ} lem A
  using ( Fof; step-in-img; u'; u'-in; u-self-in
        ; Sset; Sset-in; Sset-mono; Sset-mem )
open import L.WellOrder.Base {ℓ-suc ℓ} using ( Tri; lt; eq; gt )
open import L.Rud.Order {ℓ} lem A
  using ( Member; memberKey; member-trace; leastTrace-value; leastTrace-least
        ; leastTrace; HasTrace; trace-exists; traceTri; stage-mono; stage-below
        ; prod-stage; prod-value; prod-self; prod-image; Producer; StageBounded
        ; Trace; Earlier; _⊰_ )
open import Cubical.Data.Sum using ( _⊎_; inl; inr )
open import Cubical.HITs.CumulativeHierarchy.Constructions using ( module InfinitySet )
open InfinitySet using ( sucV )
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( squash₁ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ
```

<!--en-->
## The producer view, first direction

A producer describes a set: the self producer of `δ` describes the level `S_δ`,
and an image producer describes the value of its operation on the two sets its
arguments describe. The first direction of the view says that description lands
where it should. A stage-bounded producer whose stage belongs to an ordinal `α`
describes a member of `S_α`: the arguments of an image sit in `S_δ ∪ {S_δ}` by
stage-boundedness, so the step admits the value, and the level admits the step. This is
`step-in` realizing every producer, read through the sealed surface and nothing
else.
<!--zh-->
## 生产者视角，第一方向

一个生产者描述一个集合：`δ` 的自身生产者描述层 `S_δ`，而一个像生产者描述其运算施于两个参数所描述之集的值。视角的第一个方向说：描述落在它该落的地方。阶段属于序数 `α` 的循阶生产者描述 `S_α` 的一个成员：由循阶性，像的参数落在 `S_δ ∪ {S_δ}` 中，故 step 接纳该值，而层接纳 step。这就是 `step-in` 实现每个生产者，且只经封印的表面读出。
<!--/-->

```agda
prod-mem : (α : S) → IsOrd α → (p : Producer) → StageBounded p
         → ⟨ prod-stage p .fst ∈ˢ α ⟩ → ⟨ prod-value p ∈ˢ Sset α ⟩
prod-mem α _ (prod-self δ) _ h = Sset-mem {α = α} {β = δ .fst} h
prod-mem α _ (prod-image δ i p q) ((vp , ep) , (vq , eqq)) h =
  Sset-in α (δ .fst) (Fof i (prod-value p) (prod-value q)) h
    (step-in-img (Sset (δ .fst)) (Fof i (prod-value p) (prod-value q)) i
      (prod-value p) (prod-value q)
      (toArg p vp ep (prod-mem (δ .fst) (δ .snd) p vp))
      (toArg q vq eqq (prod-mem (δ .fst) (δ .snd) q vq))
      refl)
  where
  toArg : (r : Producer) (w : StageBounded r) → Earlier δ r
        → (⟨ prod-stage r .fst ∈ˢ δ .fst ⟩ → ⟨ prod-value r ∈ˢ Sset (δ .fst) ⟩)
        → ⟨ prod-value r ∈ˢ u' (Sset (δ .fst)) ⟩
  toArg r _ (inl h') f = u'-in (Sset (δ .fst)) (prod-value r) (f h')
  toArg (prod-self ε) _ (inr e) _ =
    subst (λ z → ⟨ Sset (z .fst) ∈ˢ u' (Sset (δ .fst)) ⟩) (sym e)
      (u-self-in (Sset (δ .fst)))
  toArg (prod-image _ _ _ _) _ (inr e) _ = Empty.rec* e
```

<!--en-->
## The reading at a level

Two members of a level are compared by the tree order read through their keys,
and `Sset-below` is that reading. The coherence section below says the reading
does not depend on the level it is read at.
<!--zh-->
## 层上的读法

某层的两个成员，按经各自键读出的树序比较，`Sset-below` 就是那次读法。下文的相容一节将说明：这个读法与它所读取的层无关。
<!--/-->

```agda
Sset-below : (α : S) → IsOrd α → Member α → Member α → Type (ℓ-suc ℓ)
Sset-below α ordα m n = memberKey α ordα m ⊰ memberKey α ordα n
```

<!--en-->
## Coherence

Here is the lemma the classical construction needs and never states. The key of
a set does not mention the level the set is read at: it is the least producer of
the set, full stop. So two levels that both contain a set assign it the same key,
and the comparison of two such sets is literally the same type at both levels.
The form the texts use, the order of a level restricted to an earlier level, is
the special case: for `β` a member of `α`, cumulativity supplies the missing
membership and the statement below is the restriction. So the union taken at a
limit index is a union of restrictions of one relation rather than a union of
unrelated ones.
<!--zh-->
## 相容

这就是经典构造需要却从不陈述的那条引理。一个集合的键不提及该集合被读取的那一层：它就是这个集合的最小生产者，仅此而已。故同时含有某集合的两层给它同一个键，而这样两个集合的比较在两层上是字面相同的类型。文献所用的形式，即某层的序限制到更早一层，是其特例：当 `β` 是 `α` 的成员时，累积性补上缺的那份隶属，下面这句就是那个限制。故极限索引处所取的并，是同一个关系诸限制之并，不是互不相干者之并。
<!--/-->

```agda
leastTrace-irrel : (x : S) (h k : HasTrace x) → leastTrace x h ≡ leastTrace x k
leastTrace-irrel x h k = cong (leastTrace x) (squash₁ h k)

order-coherent : (α β : S) (ordα : IsOrd α) (ordβ : IsOrd β) (x : S)
               → (xα : ⟨ x ∈ˢ Sset α ⟩) (xβ : ⟨ x ∈ˢ Sset β ⟩)
               → memberKey α ordα (x , xα) ≡ memberKey β ordβ (x , xβ)
order-coherent α β ordα ordβ x xα xβ =
  leastTrace-irrel x (member-trace α ordα (x , xα)) (member-trace β ordβ (x , xβ))

-- perf: a transported membership proof inside a compared type forces the
-- successor index's union tower to normalize; the memberships stay variables
order-agrees : (α β : S) (ordα : IsOrd α) (ordβ : IsOrd β) (x y : S)
             → (xα : ⟨ x ∈ˢ Sset α ⟩) (yα : ⟨ y ∈ˢ Sset α ⟩)
             → (xβ : ⟨ x ∈ˢ Sset β ⟩) (yβ : ⟨ y ∈ˢ Sset β ⟩)
             → Sset-below α ordα (x , xα) (y , yα)
             ≡ Sset-below β ordβ (x , xβ) (y , yβ)
order-agrees α β ordα ordβ x y xα yα xβ yβ = cong₂ _⊰_
  (order-coherent α β ordα ordβ x xα xβ)
  (order-coherent α β ordα ordβ y yα yβ)
```

<!--en-->
## The birth stage

The order compares stages first, so the least producer of a set carries the least
stage at which the set is produced at all. That is the set's birth stage, and it
comes out of the minimality of the key rather than out of a separate search: the
stage of a producer never rises along the order, so a producer that is least is
least in stage as well.

Three readings follow. The stage of a member of a level is a member of the index;
the member is already in the level one step past its stage; and no earlier level
contains it, since any level that does supplies a producer whose stage the least
one cannot exceed.
<!--zh-->
## 诞生阶段

序先比阶段，故一个集合的最小生产者携带该集合被产出的最小阶段。那就是该集合的诞生阶段，而它出自键的极小性、而非另一场搜索：生产者的阶段沿序从不上升，故最小的生产者在阶段上也最小。

由此得三条读式。层的成员的阶段是索引的成员；该成员在其阶段之后一步的层中已经在场；且更早的层都不含它，因为任何含它的层都供出一个生产者，最小者的阶段不可能超过它。
<!--/-->

```agda
stage-least : (x : S) (h : HasTrace x) (γ : S) → IsOrd γ → (t : Trace)
            → prod-value (t .fst) ≡ x → ⟨ prod-stage (t .fst) .fst ∈ˢ γ ⟩
            → ⟨ prod-stage (leastTrace x h .fst) .fst ∈ˢ γ ⟩
stage-least x h γ ordγ t v st = go (traceTri (leastTrace x h) t)
  where
  k : Trace
  k = leastTrace x h
  fromStage : ⟨ prod-stage (k .fst) .fst ∈ˢ prod-stage (t .fst) .fst ⟩
              ⊎ (prod-stage (k .fst) ≡ prod-stage (t .fst))
            → ⟨ prod-stage (k .fst) .fst ∈ˢ γ ⟩
  fromStage (inl m) =
    ordγ .fst {x = prod-stage (t .fst) .fst} {y = prod-stage (k .fst) .fst} m st
  fromStage (inr e) = subst (λ z → ⟨ z .fst ∈ˢ γ ⟩) (sym e) st
  go : Tri (k ⊰ t) (k ≡ t) (t ⊰ k) → ⟨ prod-stage (k .fst) .fst ∈ˢ γ ⟩
  go (lt h') = fromStage (stage-mono (k .fst) (t .fst) h')
  go (eq e) = fromStage (inr (cong (λ s → prod-stage (s .fst)) e))
  go (gt h') = Empty.rec (leastTrace-least x h t v h')

memberStage : (α : S) → IsOrd α → Member α → S
memberStage α ordα m = prod-stage (memberKey α ordα m .fst) .fst

memberStage-ord : (α : S) (ordα : IsOrd α) (m : Member α)
                → IsOrd (memberStage α ordα m)
memberStage-ord α ordα m = prod-stage (memberKey α ordα m .fst) .snd

memberStage-least : (α : S) (ordα : IsOrd α) (m : Member α)
                  → (γ : S) → IsOrd γ → ⟨ m .fst ∈ˢ Sset γ ⟩
                  → ⟨ memberStage α ordα m ∈ˢ γ ⟩
memberStage-least α ordα m γ ordγ h = PT.rec (snd (memberStage α ordα m ∈ˢ γ))
  (λ { (t , st , v) →
     stage-least (m .fst) (member-trace α ordα m) γ ordγ t v st })
  (trace-exists γ ordγ (m .fst) h)

memberStage-in : (α : S) (ordα : IsOrd α) (m : Member α)
               → ⟨ memberStage α ordα m ∈ˢ α ⟩
memberStage-in α ordα m = memberStage-least α ordα m α ordα (m .snd)

memberStage-first : (α : S) (ordα : IsOrd α) (m : Member α)
                  → ⟨ m .fst ∈ˢ Sset (sucV (memberStage α ordα m)) ⟩
memberStage-first α ordα m =
  subst (λ z → ⟨ z ∈ˢ Sset (sucV (memberStage α ordα m)) ⟩)
    (leastTrace-value (m .fst) (member-trace α ordα m))
    (prod-mem (sucV (memberStage α ordα m)) (suc-ord (memberStage-ord α ordα m))
      (memberKey α ordα m .fst) (memberKey α ordα m .snd)
      (self∈sucV (memberStage α ordα m)))
```

<!--en-->
## The successor clauses

What the order does at a successor index is now readable off the pieces, and it
is the classical recipe. A member of `S_{β+1}` that is not already in `S_β` is
born exactly at `β`: it cannot be born earlier, since a set born earlier is
already in `S_β`, one level past its own birth being at or below `β`. So an old
member's birth stage is a member of `β` while a new member's is `β` itself, and
the first clause of the comparison puts every old member below every new one.
Two old members are compared by the order of `S_β`, which is `order-agrees`{.Agda}
read at the successor index. Two new members share the stage `β`, so the comparison falls
through to the arm, then the operation index, then the two arguments, exactly as
the definition of `≺` reads.
<!--zh-->
## 后继处的诸子句

序在后继索引处做什么，如今可以从各部件上读出，而它正是那个经典配方。`S_{β+1}` 中尚不在 `S_β` 里的成员恰在 `β` 处诞生：它不能更早诞生，因为更早诞生的集合已经在 `S_β` 中，其诞生之后一层不高于 `β`。故旧成员的诞生阶段是 `β` 的成员，而新成员的诞生阶段就是 `β`，于是比较的第一条子句把每个旧成员放在每个新成员之下。两个旧成员按 `S_β` 的序比较，这就是 `order-agrees`{.Agda} 在后继索引处的读法。两个新成员共享阶段 `β`，故比较落到臂、再到运算索引、再到两个参数，与 `≺` 的定义所读一模一样。
<!--/-->

```agda
memberStage-new : (β : S) (ordβ : IsOrd β) (m : Member (sucV β))
                → (⟨ m .fst ∈ˢ Sset β ⟩ → Empty.⊥)
                → memberStage (sucV β) (suc-ord ordβ) m ≡ β
memberStage-new β ordβ m fresh =
  ∈sucV-elim {A = β} {x = δ} (isSetS δ β)
    (memberStage-in (sucV β) ordS m)
    (λ δ∈β → Empty.rec (fresh (inLevel δ∈β)))
    (λ e → e)
  where
  ordS : IsOrd (sucV β)
  ordS = suc-ord ordβ
  δ : S
  δ = memberStage (sucV β) ordS m
  ordδ : IsOrd δ
  ordδ = memberStage-ord (sucV β) ordS m
  atSuc : ⟨ m .fst ∈ˢ Sset (sucV δ) ⟩
  atSuc = memberStage-first (sucV β) ordS m
  inLevel : ⟨ δ ∈ˢ β ⟩ → ⟨ m .fst ∈ˢ Sset β ⟩
  inLevel δ∈β = go (ord-tri (sucV δ) (suc-ord ordδ) β ordβ)
    where
    go : OrdTri (sucV δ) β → ⟨ m .fst ∈ˢ Sset β ⟩
    go (inl h) = Sset-mono {α = β} {β = sucV δ} h (m .fst) atSuc
    go (inr (inl e)) = subst (λ z → ⟨ m .fst ∈ˢ Sset z ⟩) e atSuc
    go (inr (inr h)) = Empty.rec* {A = ⟨ m .fst ∈ˢ Sset β ⟩}
      (∈sucV-elim {A = δ} {x = β} (isProp⊥* {ℓ-suc ℓ}) h
        (λ β∈δ → lift (∈-irrefl β (ordβ .fst {x = δ} {y = β} β∈δ δ∈β)))
        (λ β≡δ → lift (∈-irrefl β (subst (λ z → ⟨ z ∈ˢ β ⟩) (sym β≡δ) δ∈β))))

old-before-new : (β : S) (ordβ : IsOrd β) (x y : S)
               → (x∈ : ⟨ x ∈ˢ Sset (sucV β) ⟩) (y∈ : ⟨ y ∈ˢ Sset (sucV β) ⟩)
               → ⟨ x ∈ˢ Sset β ⟩ → (⟨ y ∈ˢ Sset β ⟩ → Empty.⊥)
               → Sset-below (sucV β) (suc-ord ordβ) (x , x∈) (y , y∈)
old-before-new β ordβ x y x∈ y∈ old fresh =
  stage-below (memberKey (sucV β) (suc-ord ordβ) (x , x∈) .fst)
              (memberKey (sucV β) (suc-ord ordβ) (y , y∈) .fst)
              (subst (λ z → ⟨ memberStage (sucV β) (suc-ord ordβ) (x , x∈) ∈ˢ z ⟩)
                (sym (memberStage-new β ordβ (y , y∈) fresh))
                (memberStage-least (sucV β) (suc-ord ordβ) (x , x∈) β ordβ old))
```

<!--en-->
## Recap
<!--zh-->
## 小结
<!--/-->

<!--en-->
The readings are in place. A stage-bounded producer whose stage belongs to the
index describes a member of the level, and the level's order reads the tree
order through the key. The key does not mention the level, so the reading
agrees across levels (`order-coherent`{.Agda}, `order-agrees`{.Agda}); it
carries the birth stage (`memberStage-first`{.Agda}, `memberStage-least`{.Agda});
and the successor clauses put every old member below every new one
(`memberStage-new`{.Agda}, `old-before-new`{.Agda}). The machinery stays in
`L.Rud.Order`{.Agda}; this chapter is the surface its consumers read.
<!--zh-->
诸读法就位。阶段落在索引之内的循阶生产者描述该层的一个成员，而层的序经键读出树序。键不提及层，故读法跨层一致 (`order-coherent`{.Agda}、`order-agrees`{.Agda})；键携带诞生阶段 (`memberStage-first`{.Agda}、`memberStage-least`{.Agda})；后继处的诸子句把每个旧成员排在每个新成员之下 (`memberStage-new`{.Agda}、`old-before-new`{.Agda})。机制留在 `L.Rud.Order`{.Agda} 里，本章是它的消费者所读的那层表面。
<!--/-->
