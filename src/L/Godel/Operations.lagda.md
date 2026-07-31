# Gödel operations

<!--en-->
A finite stock of set operations, each as elementary as pairing, and the
membership laws that read each one back. Later chapters compose them where
formulas would otherwise be spent: what a defining formula carves in one
unreadable stroke, a finite composition of these operations builds in steps a
set can watch. This chapter owes nothing to the excluded middle and assumes
nothing beyond the level: every operation is a plain construction on the
hierarchy, and every law is fiber bookkeeping.

The operations arrive in four working groups. The product and the membership
graph make relations into sets; the union and the difference are the Boolean
pair; the two selections cut a family down by comparing two recorded values;
and the extension and the shift move a whole recorded assignment up or down by
one slot. One design fact governs every definition, and it is load-bearing
rather than aesthetic: **each operation is a single set former**, its members
indexed by one telescope, never a union of two formers. The union operation
itself is no exception: it is one former over a sum of index types.
<!--zh-->
一批有穷的集合运算，每个都与配对同级地初等，连同把每个运算读回去的隶属定律。后面的章将在本要花公式的地方改为复合它们：一条定义公式一笔刻出而无从旁观的东西，这些运算的有穷复合一步一步搭出来，而集合看得见每一步。本章不欠排中律，也不在层级之外另设假设：每个运算都是层级上的朴素构造，每条定律都是纤维记账。

诸运算分四个工作组到场。积与隶属图把关系做成集合；并与差是布尔那一对；两个选择靠比较两个被记录的取值来裁剪一族；而扩张与移位把一整个被记录的赋值整体上移或下移一位。有一条设计事实统辖每个定义，而它是承重的、不是审美的：**每个运算都是单个集合形成子**，其成员由一个望远镜索引，绝不写成两个形成子之并。并运算自己也不例外：它是落在索引类型之和上的一个形成子。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude

module L.Godel.Operations {ℓ : Level} where

open import V.Hierarchy {ℓ} using ( extensionalV )
open import V.Coding {ℓ} using ( pr )
open import V.Model {ℓ} using ( pair-spec; pair-singleton; union-spec; self∈sucV )

open import Cubical.Foundations.Prelude using ( subst2 )
open import Cubical.Foundations.HLevels using ( isProp× )
import Cubical.Data.Empty as Empty
import Cubical.Data.Sum as Sum
open Sum using ( _⊎_; inl; inr )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁ )
open import Cubical.Functions.Logic using ( ⇔toPath )
open import Cubical.Data.Unit using ( Unit*; tt* )
open import Cubical.HITs.CumulativeHierarchy.Base
  using ( V; sett; _∈_; setIsSet )
open import Cubical.HITs.CumulativeHierarchy.Properties
  using ( _∈ₛ_; ∈∈ₛ; ⟪_⟫; ⟪_⟫↪; ∈ₛ⟪_⟫↪_; ∈-asFiber )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ∅; ∅-empty; ⁅_,_⁆; ⁅_⁆s; ⋃_; module InfinitySet )
open InfinitySet using ( sucV )
```

<!--en-->
## Reading a member

Three conversions between the two membership relations, and the elementary
singleton and union readings the laws below lean on. A member of a `sett` is
merely a fiber of its indexing family; `∈-asFiber`{.Agda} hands the fiber over,
and everything in this chapter that says "read a member back" is that handover
followed by projections.
<!--zh-->
## 读一个成员

两种隶属关系之间的三个转换，加上下面诸定律所倚靠的单点集与并的初等读式。`sett` 的成员仅仅是其索引族的一个纤维；`∈-asFiber`{.Agda} 把纤维递过来，而本章一切「把成员读回去」都是这次递交再接投影。
<!--/-->

```agda
private
  memb : (a : V ℓ) (m : ⟪ a ⟫) → ⟨ ⟪ a ⟫↪ m ∈ a ⟩
  memb a m = ∈∈ₛ {a = ⟪ a ⟫↪ m} {b = a} .snd (∈ₛ⟪ a ⟫↪ m)

  toSmall : (a b : V ℓ) → ⟨ a ∈ b ⟩ → ⟨ a ∈ₛ b ⟩
  toSmall a b = ∈∈ₛ {a = a} {b = b} .fst

  toBig : (a b : V ℓ) → ⟨ a ∈ₛ b ⟩ → ⟨ a ∈ b ⟩
  toBig a b = ∈∈ₛ {a = a} {b = b} .snd

singleton-self : (z : V ℓ) → ⟨ z ∈ ⁅ z ⁆s ⟩
singleton-self z = subst (λ w → ⟨ z ∈ w ⟩) (pair-singleton z)
  (subst ⟨_⟩ (sym (pair-spec z z z)) ∣ inl refl ∣₁)

singleton-in : {z x : V ℓ} → x ≡ z → ⟨ x ∈ ⁅ z ⁆s ⟩
singleton-in {z} {x} e =
  subst (λ w → ⟨ w ∈ ⁅ z ⁆s ⟩) (sym e) (singleton-self z)

singleton-out : {z x : V ℓ} → ⟨ x ∈ ⁅ z ⁆s ⟩ → x ≡ z
singleton-out {z} {x} h = PT.rec (setIsSet x z) (Sum.rec (λ e → e) (λ e → e))
  (subst ⟨_⟩ (pair-spec z z x)
    (subst (λ w → ⟨ x ∈ w ⟩) (sym (pair-singleton z)) h))

∈⋃-in : {a x y : V ℓ} → ⟨ y ∈ a ⟩ → ⟨ x ∈ y ⟩ → ⟨ x ∈ ⋃ a ⟩
∈⋃-in {a} {x} {y} hy hx = subst ⟨_⟩ (sym (union-spec a x)) ∣ y , hy , hx ∣₁
```

<!--en-->
## Two unions down

A Kuratowski pair holds its components two membership steps below the set that
holds the pair. `pool`{.Agda} is that double union, the bounding set every
operation on recorded pairs indexes its components over, and its two readings
extract the left and the right component of any pair held in a set.
<!--zh-->
## 两层并之下

Kuratowski 对把自己的分量放在「装着这个对的集合」之下两个隶属步处。`pool`{.Agda} 就是那个双重并，是每个作用于被记录之对的运算为其分量作索引的界集，而它的两条读式从任何被装着的对中取出左右分量。
<!--/-->

```agda
private
  l∈pair : {a b : V ℓ} → ⟨ a ∈ ⁅ a , b ⁆ ⟩
  l∈pair {a} {b} = subst ⟨_⟩ (sym (pair-spec a b a)) ∣ inl refl ∣₁

  r∈pair : {a b : V ℓ} → ⟨ b ∈ ⁅ a , b ⁆ ⟩
  r∈pair {a} {b} = subst ⟨_⟩ (sym (pair-spec a b b)) ∣ inr refl ∣₁

  pair∈pr : {a b : V ℓ} → ⟨ ⁅ a , b ⁆ ∈ pr a b ⟩
  pair∈pr {a} {b} = r∈pair {a = ⁅ a ⁆s} {b = ⁅ a , b ⁆}

pool : V ℓ → V ℓ
pool X = ⋃ ⋃ X

pool-left : {X a b : V ℓ} → ⟨ pr a b ∈ X ⟩ → ⟨ a ∈ pool X ⟩
pool-left {X} {a} {b} h =
  ∈⋃-in {a = ⋃ X} {x = a} {y = ⁅ a , b ⁆}
    (∈⋃-in {a = X} {x = ⁅ a , b ⁆} {y = pr a b} h (pair∈pr {a = a} {b = b}))
    (l∈pair {a = a} {b = b})

pool-right : {X a b : V ℓ} → ⟨ pr a b ∈ X ⟩ → ⟨ b ∈ pool X ⟩
pool-right {X} {a} {b} h =
  ∈⋃-in {a = ⋃ X} {x = b} {y = ⁅ a , b ⁆}
    (∈⋃-in {a = X} {x = ⁅ a , b ⁆} {y = pr a b} h (pair∈pr {a = a} {b = b}))
    (r∈pair {a = a} {b = b})
```

<!--en-->
## Product and the membership graph

The two operations that make relations into sets. The product holds every
recorded pair of a member of `X` with a member of `Y`; the membership graph
holds the pairs among them whose components are themselves related by
membership. Each law states one direction: the `-in` direction assembles the
indexing fiber from the given memberships, and the `-out` direction reads the
fiber back into components, memberships, and the pair equation.
<!--zh-->
## 积与隶属图

把关系做成集合的那两个运算。积装着「`X` 的成员与 `Y` 的成员」的每一个被记录的对；隶属图装着其中「两个分量自身又以隶属相关联」的那些对。每条定律各陈述一个方向：`-in` 方向从给定的隶属装配出索引纤维，`-out` 方向把纤维读回成分量、隶属与对等式。
<!--/-->

```agda
product : V ℓ → V ℓ → V ℓ
product X Y = sett (⟪ X ⟫ × ⟪ Y ⟫)
  (λ p → pr (⟪ X ⟫↪ (p .fst)) (⟪ Y ⟫↪ (p .snd)))

product-in : {X Y u v : V ℓ}
           → ⟨ u ∈ X ⟩ → ⟨ v ∈ Y ⟩ → ⟨ pr u v ∈ product X Y ⟩
product-in {X} {Y} {u} {v} hu hv =
  ∣ (fu .fst , fv .fst) , cong₂ pr (fu .snd) (fv .snd) ∣₁
  where
  fu = ∈-asFiber {a = u} {b = X} hu
  fv = ∈-asFiber {a = v} {b = Y} hv

product-out : {X Y w : V ℓ} → ⟨ w ∈ product X Y ⟩
            → ∥ Σ[ u ∈ V ℓ ] Σ[ v ∈ V ℓ ]
                (⟨ u ∈ X ⟩ × ⟨ v ∈ Y ⟩ × (w ≡ pr u v)) ∥₁
product-out {X} {Y} = PT.map λ { ((m , k) , e) →
  ⟪ X ⟫↪ m , ⟪ Y ⟫↪ k , memb X m , memb Y k , sym e }

memberGraph : V ℓ → V ℓ → V ℓ
memberGraph X Y = sett
  ( Σ[ m ∈ ⟪ X ⟫ ] Σ[ k ∈ ⟪ Y ⟫ ] ⟨ ⟪ X ⟫↪ m ∈ₛ ⟪ Y ⟫↪ k ⟩ )
  (λ p → pr (⟪ X ⟫↪ (p .fst)) (⟪ Y ⟫↪ (p .snd .fst)))

memberGraph-in : {X Y u v : V ℓ} → ⟨ u ∈ X ⟩ → ⟨ v ∈ Y ⟩ → ⟨ u ∈ v ⟩
               → ⟨ pr u v ∈ memberGraph X Y ⟩
memberGraph-in {X} {Y} {u} {v} hu hv huv =
  ∣ ( fu .fst , fv .fst
    , toSmall (⟪ X ⟫↪ (fu .fst)) (⟪ Y ⟫↪ (fv .fst))
        (subst2 (λ p q → ⟨ p ∈ q ⟩) (sym (fu .snd)) (sym (fv .snd)) huv) )
  , cong₂ pr (fu .snd) (fv .snd) ∣₁
  where
  fu = ∈-asFiber {a = u} {b = X} hu
  fv = ∈-asFiber {a = v} {b = Y} hv

memberGraph-out : {X Y w : V ℓ} → ⟨ w ∈ memberGraph X Y ⟩
                → ∥ Σ[ u ∈ V ℓ ] Σ[ v ∈ V ℓ ]
                    (⟨ u ∈ X ⟩ × ⟨ v ∈ Y ⟩ × ⟨ u ∈ v ⟩ × (w ≡ pr u v)) ∥₁
memberGraph-out {X} {Y} = PT.map λ { ((m , k , s) , e) →
  ⟪ X ⟫↪ m , ⟪ Y ⟫↪ k , memb X m , memb Y k
  , toBig (⟪ X ⟫↪ m) (⟪ Y ⟫↪ k) s , sym e }
```

<!--en-->
## Union, intersection, and difference

The Boolean stock. The union here is **not** the library's: the library
reaches a binary union through the union of a pair of sets, which is a former
applied to formers, and a membership read against that shape has to normalize
the outer former before it can see the inner ones. This union is one `sett`
over the sum of the two index types, so a membership question meets exactly
one former. The intersection carries the second membership in its fiber, and
it is primitive rather than derived, because carving it out of two
differences would trade a membership for a double refutation, which does not
come back without deciding. The difference indexes the members of `X` by the
refutation of their membership in `Y`; all directions here are constructive,
because whatever the fiber owes is carried, never decided.
<!--zh-->
## 并、交、差

布尔存货。此处的并**不是**库的那一个：库经由「两个集合所成之对的并」抵达二元并，那是形成子套形成子，而对着那个形状的隶属读式必须先把外层形成子正规化才能看见内层。这个并是落在两个索引类型之和上的单个 `sett`，于是一个隶属问题恰好遇到一个形成子。交把第二份隶属携带在纤维里，且是初等的、不是派生的，因为用两层差刻出交，等于把一份隶属换成一份双重反驳，而后者不判定就回不来。差以「在 `Y` 中隶属的反驳」为索引挑出 `X` 的成员；此处所有方向都是构造性的，因为纤维所欠的都被携带，从不被判定。
<!--/-->

```agda
_∪_ : V ℓ → V ℓ → V ℓ
X ∪ Y = sett (⟪ X ⟫ ⊎ ⟪ Y ⟫) (Sum.rec ⟪ X ⟫↪ ⟪ Y ⟫↪)

∪-left : {X Y x : V ℓ} → ⟨ x ∈ X ⟩ → ⟨ x ∈ X ∪ Y ⟩
∪-left {X} {Y} {x} hx = ∣ inl (f .fst) , f .snd ∣₁
  where f = ∈-asFiber {a = x} {b = X} hx

∪-right : {X Y x : V ℓ} → ⟨ x ∈ Y ⟩ → ⟨ x ∈ X ∪ Y ⟩
∪-right {X} {Y} {x} hx = ∣ inr (f .fst) , f .snd ∣₁
  where f = ∈-asFiber {a = x} {b = Y} hx

∪-out : {X Y x : V ℓ} → ⟨ x ∈ X ∪ Y ⟩ → ∥ ⟨ x ∈ X ⟩ ⊎ ⟨ x ∈ Y ⟩ ∥₁
∪-out {X} {Y} {x} = PT.map
  λ { (inl m , e) → inl (subst (λ z → ⟨ z ∈ X ⟩) e (memb X m))
    ; (inr k , e) → inr (subst (λ z → ⟨ z ∈ Y ⟩) e (memb Y k)) }

_∩_ : V ℓ → V ℓ → V ℓ
X ∩ Y = sett (Σ[ m ∈ ⟪ X ⟫ ] ⟨ ⟪ X ⟫↪ m ∈ₛ Y ⟩) (λ p → ⟪ X ⟫↪ (p .fst))

∩-in : {X Y x : V ℓ} → ⟨ x ∈ X ⟩ → ⟨ x ∈ Y ⟩ → ⟨ x ∈ X ∩ Y ⟩
∩-in {X} {Y} {x} hx hy =
  ∣ ( f .fst
    , toSmall (⟪ X ⟫↪ (f .fst)) Y
        (subst (λ z → ⟨ z ∈ Y ⟩) (sym (f .snd)) hy) )
  , f .snd ∣₁
  where f = ∈-asFiber {a = x} {b = X} hx

∩-out : {X Y x : V ℓ} → ⟨ x ∈ X ∩ Y ⟩ → ⟨ x ∈ X ⟩ × ⟨ x ∈ Y ⟩
∩-out {X} {Y} {x} = PT.rec
  (isProp× (snd (x ∈ X)) (snd (x ∈ Y)))
  λ { ((m , s) , e) →
      subst (λ z → ⟨ z ∈ X ⟩) e (memb X m)
    , subst (λ z → ⟨ z ∈ Y ⟩) e (toBig (⟪ X ⟫↪ m) Y s) }

_∖_ : V ℓ → V ℓ → V ℓ
X ∖ Y = sett (Σ[ m ∈ ⟪ X ⟫ ] (⟨ ⟪ X ⟫↪ m ∈ₛ Y ⟩ → ⊥* {ℓ}))
             (λ p → ⟪ X ⟫↪ (p .fst))

∖-in : {X Y x : V ℓ} → ⟨ x ∈ X ⟩ → (⟨ x ∈ Y ⟩ → Empty.⊥) → ⟨ x ∈ X ∖ Y ⟩
∖-in {X} {Y} {x} hx nx =
  ∣ ( f .fst
    , (λ h → Empty.rec (nx
        (subst (λ z → ⟨ z ∈ Y ⟩) (f .snd)
          (toBig (⟪ X ⟫↪ (f .fst)) Y h)))) )
  , f .snd ∣₁
  where f = ∈-asFiber {a = x} {b = X} hx

∖-out : {X Y x : V ℓ} → ⟨ x ∈ X ∖ Y ⟩
      → ⟨ x ∈ X ⟩ × (⟨ x ∈ Y ⟩ → Empty.⊥)
∖-out {X} {Y} {x} = PT.rec
  (isProp× (snd (x ∈ X)) (isPropΠ (λ _ → Empty.isProp⊥)))
  λ { ((m , nm) , e) →
      subst (λ z → ⟨ z ∈ X ⟩) e (memb X m)
    , (λ hxY → lower (nm
        (toSmall (⟪ X ⟫↪ m) Y
          (subst (λ z → ⟨ z ∈ Y ⟩) (sym e) hxY)))) }

∖-self : (X : V ℓ) → X ∖ X ≡ ∅
∖-self X = extensionalV λ w → ⇔toPath
  (λ h → Empty.rec (∖-out {X = X} {Y = X} {x = w} h .snd
                     (∖-out {X = X} {Y = X} {x = w} h .fst)))
  (λ h → Empty.rec (∅-empty w (toSmall w ∅ h)))
```

<!--en-->
## The two selections

A selection cuts a family of sets down to those members holding two recorded
values in a fixed relation, and the places the two values are recorded at are
**parameters**: two key sets, drawn from outside. Each fiber carries the member,
one key from each key set, the recorded value at each key, and the relating
fact. `selectMember`{.Agda} relates the two values by membership;
`selectEqual`{.Agda} asks the two keys to record **one** value, which is
equality said without an equation. The `-sub` reading returns the member to its
family, and the `-wit` reading hands the whole fiber back.
<!--zh-->
## 两个选择

选择把一族集合裁剪到「在固定关系中持有两个被记录取值」的那些成员，而两个取值被记录的位置是**参数**：两个键集，自外部取来。每个纤维携带成员、各键集中的一个键、各键处被记录的取值，以及那条关联事实。`selectMember`{.Agda} 以隶属关联两个取值；`selectEqual`{.Agda} 则要求两个键记录**同一个**取值，这是不写等式说出的相等。`-sub` 读式把成员归还其族，`-wit` 读式把整个纤维递回来。
<!--/-->

```agda
-- perf: sealed at birth, like the family; consumers instantiate the
-- selections at composed concrete set formers
opaque
  selectMember : V ℓ → V ℓ → V ℓ → V ℓ
  selectMember X Ka Kb = sett
    ( Σ[ m ∈ ⟪ X ⟫ ] Σ[ a ∈ ⟪ Ka ⟫ ] Σ[ b ∈ ⟪ Kb ⟫ ]
      Σ[ u ∈ ⟪ pool (⟪ X ⟫↪ m) ⟫ ] Σ[ v ∈ ⟪ pool (⟪ X ⟫↪ m) ⟫ ]
      ( ⟨ pr (⟪ Ka ⟫↪ a) (⟪ pool (⟪ X ⟫↪ m) ⟫↪ u) ∈ₛ ⟪ X ⟫↪ m ⟩
      × ⟨ pr (⟪ Kb ⟫↪ b) (⟪ pool (⟪ X ⟫↪ m) ⟫↪ v) ∈ₛ ⟪ X ⟫↪ m ⟩
      × ⟨ ⟪ pool (⟪ X ⟫↪ m) ⟫↪ u ∈ₛ ⟪ pool (⟪ X ⟫↪ m) ⟫↪ v ⟩ ) )
    (λ p → ⟪ X ⟫↪ (p .fst))

opaque
  unfolding selectMember

  selectMember-in : {X Ka Kb w a b u v : V ℓ}
                  → ⟨ w ∈ X ⟩ → ⟨ a ∈ Ka ⟩ → ⟨ b ∈ Kb ⟩
                  → ⟨ pr a u ∈ w ⟩ → ⟨ pr b v ∈ w ⟩ → ⟨ u ∈ v ⟩
                  → ⟨ w ∈ selectMember X Ka Kb ⟩
  selectMember-in {X} {Ka} {Kb} {w} {a} {b} {u} {v} hw ha hb hau hbv huv =
    ∣ ( fw .fst , fa .fst , fb .fst , fu .fst , fv .fst
      , toSmall (pr (⟪ Ka ⟫↪ (fa .fst)) pu) W
          (subst2 (λ p q → ⟨ pr p q ∈ W ⟩)
            (sym (fa .snd)) (sym (fu .snd)) hau')
      , toSmall (pr (⟪ Kb ⟫↪ (fb .fst)) pv) W
          (subst2 (λ p q → ⟨ pr p q ∈ W ⟩)
            (sym (fb .snd)) (sym (fv .snd)) hbv')
      , toSmall pu pv
          (subst2 (λ p q → ⟨ p ∈ q ⟩)
            (sym (fu .snd)) (sym (fv .snd)) huv) )
    , fw .snd ∣₁
    where
    fw : Σ[ m ∈ ⟪ X ⟫ ] (⟪ X ⟫↪ m ≡ w)
    fw = ∈-asFiber {a = w} {b = X} hw
    W : V ℓ
    W = ⟪ X ⟫↪ (fw .fst)
    fa : Σ[ m ∈ ⟪ Ka ⟫ ] (⟪ Ka ⟫↪ m ≡ a)
    fa = ∈-asFiber {a = a} {b = Ka} ha
    fb : Σ[ m ∈ ⟪ Kb ⟫ ] (⟪ Kb ⟫↪ m ≡ b)
    fb = ∈-asFiber {a = b} {b = Kb} hb
    hau' : ⟨ pr a u ∈ W ⟩
    hau' = subst (λ z → ⟨ pr a u ∈ z ⟩) (sym (fw .snd)) hau
    hbv' : ⟨ pr b v ∈ W ⟩
    hbv' = subst (λ z → ⟨ pr b v ∈ z ⟩) (sym (fw .snd)) hbv
    fu : Σ[ m ∈ ⟪ pool W ⟫ ] (⟪ pool W ⟫↪ m ≡ u)
    fu = ∈-asFiber {a = u} {b = pool W}
           (pool-right {X = W} {a = a} {b = u} hau')
    fv : Σ[ m ∈ ⟪ pool W ⟫ ] (⟪ pool W ⟫↪ m ≡ v)
    fv = ∈-asFiber {a = v} {b = pool W}
           (pool-right {X = W} {a = b} {b = v} hbv')
    pu pv : V ℓ
    pu = ⟪ pool W ⟫↪ (fu .fst)
    pv = ⟪ pool W ⟫↪ (fv .fst)

  selectMember-sub : {X Ka Kb w : V ℓ}
                   → ⟨ w ∈ selectMember X Ka Kb ⟩ → ⟨ w ∈ X ⟩
  selectMember-sub {X} {Ka} {Kb} {w} = PT.rec (snd (w ∈ X))
    λ { ((m , _) , e) → subst (λ z → ⟨ z ∈ X ⟩) e (memb X m) }

  selectMember-wit : {X Ka Kb w : V ℓ} → ⟨ w ∈ selectMember X Ka Kb ⟩
                   → ∥ Σ[ a ∈ V ℓ ] Σ[ b ∈ V ℓ ] Σ[ u ∈ V ℓ ] Σ[ v ∈ V ℓ ]
                       ( ⟨ a ∈ Ka ⟩ × ⟨ b ∈ Kb ⟩
                       × ⟨ pr a u ∈ w ⟩ × ⟨ pr b v ∈ w ⟩ × ⟨ u ∈ v ⟩ ) ∥₁
  selectMember-wit {X} {Ka} {Kb} {w} = PT.map
    λ { ((m , a , b , u , v , sau , sbv , suv) , e) →
        ⟪ Ka ⟫↪ a , ⟪ Kb ⟫↪ b
      , ⟪ pool (⟪ X ⟫↪ m) ⟫↪ u , ⟪ pool (⟪ X ⟫↪ m) ⟫↪ v
      , memb Ka a , memb Kb b
      , subst (λ z → ⟨ pr (⟪ Ka ⟫↪ a) (⟪ pool (⟪ X ⟫↪ m) ⟫↪ u) ∈ z ⟩)
          e (toBig (pr (⟪ Ka ⟫↪ a) (⟪ pool (⟪ X ⟫↪ m) ⟫↪ u)) (⟪ X ⟫↪ m) sau)
      , subst (λ z → ⟨ pr (⟪ Kb ⟫↪ b) (⟪ pool (⟪ X ⟫↪ m) ⟫↪ v) ∈ z ⟩)
          e (toBig (pr (⟪ Kb ⟫↪ b) (⟪ pool (⟪ X ⟫↪ m) ⟫↪ v)) (⟪ X ⟫↪ m) sbv)
      , toBig (⟪ pool (⟪ X ⟫↪ m) ⟫↪ u) (⟪ pool (⟪ X ⟫↪ m) ⟫↪ v) suv }

opaque
  selectEqual : V ℓ → V ℓ → V ℓ → V ℓ
  selectEqual X Ka Kb = sett
    ( Σ[ m ∈ ⟪ X ⟫ ] Σ[ a ∈ ⟪ Ka ⟫ ] Σ[ b ∈ ⟪ Kb ⟫ ]
      Σ[ u ∈ ⟪ pool (⟪ X ⟫↪ m) ⟫ ]
      ( ⟨ pr (⟪ Ka ⟫↪ a) (⟪ pool (⟪ X ⟫↪ m) ⟫↪ u) ∈ₛ ⟪ X ⟫↪ m ⟩
      × ⟨ pr (⟪ Kb ⟫↪ b) (⟪ pool (⟪ X ⟫↪ m) ⟫↪ u) ∈ₛ ⟪ X ⟫↪ m ⟩ ) )
    (λ p → ⟪ X ⟫↪ (p .fst))

opaque
  unfolding selectEqual

  selectEqual-in : {X Ka Kb w a b u : V ℓ}
                 → ⟨ w ∈ X ⟩ → ⟨ a ∈ Ka ⟩ → ⟨ b ∈ Kb ⟩
                 → ⟨ pr a u ∈ w ⟩ → ⟨ pr b u ∈ w ⟩
                 → ⟨ w ∈ selectEqual X Ka Kb ⟩
  selectEqual-in {X} {Ka} {Kb} {w} {a} {b} {u} hw ha hb hau hbu =
    ∣ ( fw .fst , fa .fst , fb .fst , fu .fst
      , toSmall (pr (⟪ Ka ⟫↪ (fa .fst)) pu) W
          (subst2 (λ p q → ⟨ pr p q ∈ W ⟩)
            (sym (fa .snd)) (sym (fu .snd)) hau')
      , toSmall (pr (⟪ Kb ⟫↪ (fb .fst)) pu) W
          (subst2 (λ p q → ⟨ pr p q ∈ W ⟩)
            (sym (fb .snd)) (sym (fu .snd)) hbu') )
    , fw .snd ∣₁
    where
    fw : Σ[ m ∈ ⟪ X ⟫ ] (⟪ X ⟫↪ m ≡ w)
    fw = ∈-asFiber {a = w} {b = X} hw
    W : V ℓ
    W = ⟪ X ⟫↪ (fw .fst)
    fa : Σ[ m ∈ ⟪ Ka ⟫ ] (⟪ Ka ⟫↪ m ≡ a)
    fa = ∈-asFiber {a = a} {b = Ka} ha
    fb : Σ[ m ∈ ⟪ Kb ⟫ ] (⟪ Kb ⟫↪ m ≡ b)
    fb = ∈-asFiber {a = b} {b = Kb} hb
    hau' : ⟨ pr a u ∈ W ⟩
    hau' = subst (λ z → ⟨ pr a u ∈ z ⟩) (sym (fw .snd)) hau
    hbu' : ⟨ pr b u ∈ W ⟩
    hbu' = subst (λ z → ⟨ pr b u ∈ z ⟩) (sym (fw .snd)) hbu
    fu : Σ[ m ∈ ⟪ pool W ⟫ ] (⟪ pool W ⟫↪ m ≡ u)
    fu = ∈-asFiber {a = u} {b = pool W}
           (pool-right {X = W} {a = a} {b = u} hau')
    pu : V ℓ
    pu = ⟪ pool W ⟫↪ (fu .fst)

  selectEqual-sub : {X Ka Kb w : V ℓ}
                  → ⟨ w ∈ selectEqual X Ka Kb ⟩ → ⟨ w ∈ X ⟩
  selectEqual-sub {X} {Ka} {Kb} {w} = PT.rec (snd (w ∈ X))
    λ { ((m , _) , e) → subst (λ z → ⟨ z ∈ X ⟩) e (memb X m) }

  selectEqual-wit : {X Ka Kb w : V ℓ} → ⟨ w ∈ selectEqual X Ka Kb ⟩
                  → ∥ Σ[ a ∈ V ℓ ] Σ[ b ∈ V ℓ ] Σ[ u ∈ V ℓ ]
                      ( ⟨ a ∈ Ka ⟩ × ⟨ b ∈ Kb ⟩
                      × ⟨ pr a u ∈ w ⟩ × ⟨ pr b u ∈ w ⟩ ) ∥₁
  selectEqual-wit {X} {Ka} {Kb} {w} = PT.map
    λ { ((m , a , b , u , sau , sbu) , e) →
        ⟪ Ka ⟫↪ a , ⟪ Kb ⟫↪ b , ⟪ pool (⟪ X ⟫↪ m) ⟫↪ u
      , memb Ka a , memb Kb b
      , subst (λ z → ⟨ pr (⟪ Ka ⟫↪ a) (⟪ pool (⟪ X ⟫↪ m) ⟫↪ u) ∈ z ⟩)
          e (toBig (pr (⟪ Ka ⟫↪ a) (⟪ pool (⟪ X ⟫↪ m) ⟫↪ u)) (⟪ X ⟫↪ m) sau)
      , subst (λ z → ⟨ pr (⟪ Kb ⟫↪ b) (⟪ pool (⟪ X ⟫↪ m) ⟫↪ u) ∈ z ⟩)
          e (toBig (pr (⟪ Kb ⟫↪ b) (⟪ pool (⟪ X ⟫↪ m) ⟫↪ u)) (⟪ X ⟫↪ m) sbu) }
```

<!--en-->
## Extension and shift

The operations that move a recorded assignment by one slot. `extendGraph`{.Agda}
puts a new value at the first key and renumbers every existing key one step up
by the von Neumann successor; its three laws are the two ways in, at the new
key and along the renumbering, and the reading that splits a member back into
the two cases. `tailGraph`{.Agda} is the inverse renumbering, dropping whatever
the first key records. `extendFamily`{.Agda} and `shiftDown`{.Agda} lift the
two to a family: every extension of a member of `X` by a value from `Y`, and
the shift of every member.
<!--zh-->
## 扩张与移位

把被记录的赋值移动一位的运算。`extendGraph`{.Agda} 在首键处放一个新取值，并把既有的每个键沿冯·诺伊曼后继整体上移一步；它的三条定律是两条进入方向 (在新键处、沿重编号) 与把成员拆回两种情形的读式。`tailGraph`{.Agda} 是逆向的重编号，弃掉首键所记录的东西。`extendFamily`{.Agda} 与 `shiftDown`{.Agda} 把两者提升到族上：`X` 的成员被 `Y` 的取值所作的每一次扩张，以及每个成员的移位。
<!--/-->

```agda
-- perf: sealed at birth like the shift; the index's pool is a ⋃-tower
-- and an open head re-normalizes it at every concrete set former (the
-- constant-atom case did not finish in eighteen minutes open)
opaque
  extendGraph : V ℓ → V ℓ → V ℓ
  extendGraph y γ = sett
    ( Unit* {ℓ}
    ⊎ ( Σ[ a ∈ ⟪ pool γ ⟫ ] Σ[ v ∈ ⟪ pool γ ⟫ ]
        ⟨ pr (⟪ pool γ ⟫↪ a) (⟪ pool γ ⟫↪ v) ∈ₛ γ ⟩ ) )
    (λ { (inl _) → pr ∅ y
       ; (inr p) → pr (sucV (⟪ pool γ ⟫↪ (p .fst)))
                      (⟪ pool γ ⟫↪ (p .snd .fst)) })

opaque
  unfolding extendGraph

  extendGraph-zero : {y γ : V ℓ} → ⟨ pr ∅ y ∈ extendGraph y γ ⟩
  extendGraph-zero {y} {γ} = ∣ inl tt* , refl ∣₁

  extendGraph-suc : {y γ a v : V ℓ}
                  → ⟨ pr a v ∈ γ ⟩ → ⟨ pr (sucV a) v ∈ extendGraph y γ ⟩
  extendGraph-suc {y} {γ} {a} {v} h =
    ∣ inr ( fa .fst , fv .fst
          , toSmall (pr (⟪ pool γ ⟫↪ (fa .fst)) (⟪ pool γ ⟫↪ (fv .fst))) γ
              (subst2 (λ p q → ⟨ pr p q ∈ γ ⟩)
                (sym (fa .snd)) (sym (fv .snd)) h) )
    , cong₂ (λ p q → pr (sucV p) q) (fa .snd) (fv .snd) ∣₁
    where
    fa : Σ[ m ∈ ⟪ pool γ ⟫ ] (⟪ pool γ ⟫↪ m ≡ a)
    fa = ∈-asFiber {a = a} {b = pool γ}
           (pool-left {X = γ} {a = a} {b = v} h)
    fv : Σ[ m ∈ ⟪ pool γ ⟫ ] (⟪ pool γ ⟫↪ m ≡ v)
    fv = ∈-asFiber {a = v} {b = pool γ}
           (pool-right {X = γ} {a = a} {b = v} h)

  extendGraph-out : {y γ z : V ℓ} → ⟨ z ∈ extendGraph y γ ⟩
                  → ∥ (z ≡ pr ∅ y)
                    ⊎ (Σ[ a ∈ V ℓ ] Σ[ v ∈ V ℓ ]
                        (⟨ pr a v ∈ γ ⟩ × (z ≡ pr (sucV a) v))) ∥₁
  extendGraph-out {y} {γ} {z} = PT.map
    λ { (inl _ , e) → inl (sym e)
      ; (inr (a , v , s) , e) →
          inr ( ⟪ pool γ ⟫↪ a , ⟪ pool γ ⟫↪ v
              , toBig (pr (⟪ pool γ ⟫↪ a) (⟪ pool γ ⟫↪ v)) γ s
              , sym e ) }

-- perf: sealed at birth; the index's ⋃-tower re-normalizes in every
-- downstream obligation at a concrete set former when the head is open:
-- the tuple shift equation 446 s open against 1.0 s sealed, the
-- existential satisfaction case 250 s open against 3 s sealed
opaque
  tailGraph : V ℓ → V ℓ
  tailGraph w = sett
    ( Σ[ a ∈ ⟪ ⋃ pool w ⟫ ] Σ[ v ∈ ⟪ pool w ⟫ ]
      ⟨ pr (sucV (⟪ ⋃ pool w ⟫↪ a)) (⟪ pool w ⟫↪ v) ∈ₛ w ⟩ )
    (λ p → pr (⟪ ⋃ pool w ⟫↪ (p .fst)) (⟪ pool w ⟫↪ (p .snd .fst)))

opaque
  unfolding tailGraph

  tailGraph-in : {w a v : V ℓ}
               → ⟨ pr (sucV a) v ∈ w ⟩ → ⟨ pr a v ∈ tailGraph w ⟩
  tailGraph-in {w} {a} {v} h =
    ∣ ( fa .fst , fv .fst
      , toSmall
          (pr (sucV (⟪ ⋃ pool w ⟫↪ (fa .fst))) (⟪ pool w ⟫↪ (fv .fst))) w
          (subst2 (λ p q → ⟨ pr (sucV p) q ∈ w ⟩)
            (sym (fa .snd)) (sym (fv .snd)) h) )
    , cong₂ pr (fa .snd) (fv .snd) ∣₁
    where
    fa : Σ[ m ∈ ⟪ ⋃ pool w ⟫ ] (⟪ ⋃ pool w ⟫↪ m ≡ a)
    fa = ∈-asFiber {a = a} {b = ⋃ pool w}
           (∈⋃-in {a = pool w} {x = a} {y = sucV a}
             (pool-left {X = w} {a = sucV a} {b = v} h) (self∈sucV a))
    fv : Σ[ m ∈ ⟪ pool w ⟫ ] (⟪ pool w ⟫↪ m ≡ v)
    fv = ∈-asFiber {a = v} {b = pool w}
           (pool-right {X = w} {a = sucV a} {b = v} h)

  tailGraph-out : {w z : V ℓ} → ⟨ z ∈ tailGraph w ⟩
                → ∥ Σ[ a ∈ V ℓ ] Σ[ v ∈ V ℓ ]
                    (⟨ pr (sucV a) v ∈ w ⟩ × (z ≡ pr a v)) ∥₁
  tailGraph-out {w} {z} = PT.map λ { ((a , v , s) , e) →
    ⟪ ⋃ pool w ⟫↪ a , ⟪ pool w ⟫↪ v
    , toBig (pr (sucV (⟪ ⋃ pool w ⟫↪ a)) (⟪ pool w ⟫↪ v)) w s , sym e }

-- perf: sealed at birth; the family sits over concrete set formers in
-- every consumer, and an open head re-normalizes their presentations
opaque
  extendFamily : V ℓ → V ℓ → V ℓ
  extendFamily X Y = sett (⟪ X ⟫ × ⟪ Y ⟫)
    (λ p → extendGraph (⟪ Y ⟫↪ (p .snd)) (⟪ X ⟫↪ (p .fst)))

opaque
  unfolding extendFamily

  extendFamily-in : {X Y γ y : V ℓ} → ⟨ γ ∈ X ⟩ → ⟨ y ∈ Y ⟩
                  → ⟨ extendGraph y γ ∈ extendFamily X Y ⟩
  extendFamily-in {X} {Y} {γ} {y} hγ hy =
    ∣ (fγ .fst , fy .fst) , cong₂ extendGraph (fy .snd) (fγ .snd) ∣₁
    where
    fγ : Σ[ m ∈ ⟪ X ⟫ ] (⟪ X ⟫↪ m ≡ γ)
    fγ = ∈-asFiber {a = γ} {b = X} hγ
    fy : Σ[ m ∈ ⟪ Y ⟫ ] (⟪ Y ⟫↪ m ≡ y)
    fy = ∈-asFiber {a = y} {b = Y} hy

  extendFamily-out : {X Y w : V ℓ} → ⟨ w ∈ extendFamily X Y ⟩
                   → ∥ Σ[ γ ∈ V ℓ ] Σ[ y ∈ V ℓ ]
                       (⟨ γ ∈ X ⟩ × ⟨ y ∈ Y ⟩ × (w ≡ extendGraph y γ)) ∥₁
  extendFamily-out {X} {Y} = PT.map λ { ((mγ , my) , e) →
    ⟪ X ⟫↪ mγ , ⟪ Y ⟫↪ my , memb X mγ , memb Y my , sym e }

shiftDown : V ℓ → V ℓ
shiftDown X = sett ⟪ X ⟫ (λ m → tailGraph (⟪ X ⟫↪ m))

shiftDown-in : {X z : V ℓ} → ⟨ z ∈ X ⟩ → ⟨ tailGraph z ∈ shiftDown X ⟩
shiftDown-in {X} {z} h = ∣ f .fst , cong tailGraph (f .snd) ∣₁
  where f = ∈-asFiber {a = z} {b = X} h

shiftDown-out : {X w : V ℓ} → ⟨ w ∈ shiftDown X ⟩
              → ∥ Σ[ z ∈ V ℓ ] (⟨ z ∈ X ⟩ × (tailGraph z ≡ w)) ∥₁
shiftDown-out {X} = PT.map λ { (m , e) → ⟪ X ⟫↪ m , memb X m , e }
```

<!--en-->
## Recap

Ten operations and a bounding helper, each a single set former with its
membership laws: `product`{.Agda} and `memberGraph`{.Agda} make relations into
sets, `_∪_`{.Agda}, `_∩_`{.Agda} and `_∖_`{.Agda} are the Boolean stock,
`selectMember`{.Agda}
and `selectEqual`{.Agda} compare two recorded values at parameter keys,
`extendGraph`{.Agda} and `extendFamily`{.Agda} extend a recorded assignment
while `tailGraph`{.Agda} under `shiftDown`{.Agda} shifts one away, and
`pool`{.Agda} bounds the components of every recorded pair. Nothing here
assumes the excluded middle. The stock is deliberately not closed: an
operation enters this chapter when a later chapter needs it, and what the
later chapters do with these is compose them.
<!--zh-->
## 小结

十个运算与一个界定辅助，每个都是带隶属定律的单个集合形成子：`product`{.Agda} 与 `memberGraph`{.Agda} 把关系做成集合，`_∪_`{.Agda}、`_∩_`{.Agda} 与 `_∖_`{.Agda} 是布尔存货，`selectMember`{.Agda} 与 `selectEqual`{.Agda} 在参数键处比较两个被记录的取值，`extendGraph`{.Agda} 与 `extendFamily`{.Agda} 扩张一个被记录的赋值而 `tailGraph`{.Agda} 经 `shiftDown`{.Agda} 移走一个，`pool`{.Agda} 为每个被记录之对的分量设界。此处无一假设排中律。这批存货有意不封口：一个运算在后面某章需要它时进入本章，而后面诸章对它们做的事，就是复合。
<!--/-->
