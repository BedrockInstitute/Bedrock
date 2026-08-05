# The order formula

<!--en-->
The order family chapter fixed the interface, the per-level order as an
element, and booked to this chapter the residue that discharges it: the
order formula, its two-way adequacy, and the carve that places the order
element in a level. This chapter runs the D-10 check first, as the gate
prescribes, and the check is decisive: the recorded targets, the uniform
formula, the two-way adequacy at the intended generality, and the
successor-offset placement, are not establishable at the delivered face.
The general-level formula needs the internalized level story and the
producer lex, which descends unboundedly and is not finitely expressible
without the coded satisfaction; the successor offset is the same-index
discharge the bridge already records as false, and the honest placement
is a limit level. What is buildable, and is built here, is the expressible
instance: at `sucV ∅`, the unique level where the successor clause is the
whole order, the chapter delivers the formula's self-below-image clause,
its soundness direction against the delivered order, and the carve, the
order element as the satisfaction set of the formula, placed in any limit
level above, with the pair-out read and the pairs clause. The image-image
clause, the completeness direction, and the general level are named as the
residues, each with its exact type.
<!--zh-->
序族章定下界面，即「每一层的序作为元素」，并把兑付它的残余记到本章账上：序公式、它的双向充分性，以及把序元素放进某层的刻法。本章先跑 D-10 检查，正如门所规定，而检查是决定性的：记录在案的目标，即逐层统一的公式、在预定一般性下的双向充分性、以及后继偏移的放置，在已交付的面孔上都不可建立。一般层的公式需要内化的层故事与生产者字典序，而后者无界地下降，没有编码的满足机器便无法有限表达；后继偏移正是桥已记作假命题的同索引兑付，诚实的放置落在某个极限层。可建者，本章即建：在 `sucV ∅` 处，即后继子句就是整个序的唯一一层，本章交付公式的「自身在像下」子句、它对照已交付之序的健全方向，以及刻法，即把序元素作为公式的满足集，放入其上任意极限层，连同读出对的那一方向与「成员皆对」子句。「像对像」子句、完备方向与一般层，作为残余逐条具名，各带精确类型。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V )

module L.OrderFormula {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) (A : V ℓ) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula; var; con; _≐_; _∧̇_; ¬̇_ )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Coding {ℓ} using ( pr )
open import L.Constructible {ℓ} using ( IsOrd; isPropIsOrd )
open import L.Ordinal {ℓ} using ( ∅-ord; suc-ord )
open import Cubical.HITs.CumulativeHierarchy.Constructions using
  ( ∅; ∅-empty; module InfinitySet )
open InfinitySet using ( sucV )
open import L.Rud.Step {ℓ} lem A using
  ( Sset; step; step-in-self; step-in-img; Sset-zero; Sset-suc; Op16
  ; Fof; u-self-in )
open import L.Rud.Order {ℓ} lem A using
  ( Member; memberKey; member-trace; leastTrace-value; leastTrace-least
  ; memberStage-new; prod-stage; prod-value; prod-self; prod-image
  ; Producer; Ord; Trace; Sset-below; _⊰_; _≺_
  ; StageBounded; isPropStageBounded )
open import L.Definability {ℓ} using ( module DefOf )
open import Cubical.HITs.CumulativeHierarchy.Properties using
  ( ⟪_⟫; ⟪_⟫↪; ∈∈ₛ; ∈-asFiber )
open import Cubical.Data.Sigma using ( Σ≡Prop )
import Cubical.Data.Sum as Sum
open Sum using ( inr )
open import Cubical.Data.Unit using ( tt* )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁ )
import Cubical.Data.Empty as Empty

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ
```

<!--en-->
## The D-10 record

The recorded targets, checked for truth at the intended generality before
any proof is attempted, with the corrections beside the originals.

**B1, the order formula, uniform in the level.** The recorded target is a
formula `σ< : Formula ⟪ Sset α ⟫ 2` at every level `α`, whose satisfaction
reads the level's order. At the intended generality the stage-quantified
clauses are not expressible: the clause "x lies in the level at `δ`" needs
the term `Sset δ` with `δ` bound, and the object language has no function
symbols and no internalized level predicate, the same gap the codes chapter
records for the code set. The successor-clause form, the value-enumeration
shape the gate named, is expressible only where the successor clause is the
whole order, and that is the unique level `sucV ∅`.

**B2, the two-way adequacy.** The recorded target is the pair of directions
`⊨ σ< (a, b) ⟷ Sset-below α ordα a b` at the intended generality. The
same-stage clause compares the least producers lexicographically, by the
operation index and then by the arguments, and the argument comparison
descends through the producer trees without bound. A finite formula cannot
express the descent without the internalized satisfaction, which the tree
does not carry and which the retiring cone paid its whole cost for. The
soundness direction at the expressible instance is delivered here; the
completeness direction and the image-image clause are the residues.

**B3, the carve and the instantiation of the interface.** The recorded
target places the order element at `Sset (sucV α)`, the interface's first
field. At the intended generality the order element is a definable set of
pairs, and the tower absorbs definable subsets only at limit levels, the
omega-block of slack of the classical 1.7 and the same-index discharge the
bridge already records as false. The corrected placement, delivered here,
is the limit level: the order element at `sucV ∅` is a member of every
limit level above it.

The interface `OrderAtAt` as delivered is therefore not instantiable as
stated at any level with a nontrivial order; the chapter delivers the
corrected content and names the residue.
<!--zh-->
## D-10 记录

先在任何证明之前，把记录在案的目标放在预定一般性下核验真伪，并在原目标旁记下修正。

**B1，逐层统一的序公式。** 记录目标是每一层 `α` 处的一条公式 `σ< : Formula ⟪ Sset α ⟫ 2`，其满足读出该层的序。在预定一般性下，以阶段为量词的子句不可表达：「x 落在 `δ` 处的层里」需要词项 `Sset δ` 而 `δ` 被绑定，对象语言既无函数符号、也无内化的层谓词，这正是码章为码集记下的同一道缺口。后继子句形态，即门所点名的值枚举形状，只在后继子句即整个序之处可表达，而那唯一一层就是 `sucV ∅`。

**B2，双向充分性。** 记录目标是在预定一般性下的两个方向 `⊨ σ< (a, b) ⟷ Sset-below α ordα a b`。同阶段子句按字典序比较最小生产者，先比运算索引、再比参数，而参数比较沿生产者树无界下降。没有内化的满足机器，有限公式无法表达这段下降；树里没有这台机器，而退役锥为它付了全部代价。可表达实例处的健全方向本章交付；完备方向与「像对像」子句是残余。

**B3，刻法与界面的实例化。** 记录目标把序元素放在 `Sset (sucV α)`，即界面的第一字段。在预定一般性下，序元素是定义出的对之集，而塔只在极限层吸收可定义子集，即经典 1.7 的 ω 块裕量，也是桥已记作假命题的同索引兑付。修正后的放置，本章交付，是极限层：`sucV ∅` 处的序元素属于其上的每个极限层。

界面 `OrderAtAt` 照原样在序不平凡的任何一层都不可实例化；本章交付修正后的内容，并具名残余。
<!--/-->

<!--en-->
## The level where the successor clause is the whole order

Everything below is at `u = Sset (sucV ∅)`, the unique level whose fresh
members are the whole order. The two kinds of member are the self, which is
the empty set, and the sixteen image values `Fof i ∅ ∅`, each a member of
the level by the step's image arm with the two argument levels as
parameters. The freshness hypothesis, that nothing lies in the previous
level, is the empty-set refutation.
<!--zh-->
## 后继子句即整个序的那一层

以下一切都落在 `u = Sset (sucV ∅)`，即新成员就是整个序的那唯一一层。两类成员是自身，即空集，以及十六个像值 `Fof i ∅ ∅`，各经 step 的像臂、以两个参数层为参数而成为该层成员。新鲜性假设，「更早一层空无一物」，就是空集反驳。
<!--/-->

```agda
module Level where

  β : V ℓ
  β = ∅

  ordβ : IsOrd β
  ordβ = ∅-ord

  ordS : IsOrd (sucV β)
  ordS = suc-ord ordβ

  u : V ℓ
  u = Sset (sucV β)

  u-step : u ≡ step (Sset β)
  u-step = Sset-suc β

  ∅∈u : ⟨ ∅ ∈ˢ u ⟩
  ∅∈u = subst (λ w → ⟨ ∅ ∈ˢ w ⟩) (sym u-step)
    (subst (λ v → ⟨ v ∈ˢ step (Sset β) ⟩) (Sset-zero) (step-in-self (Sset β)))

  img : Op16 → V ℓ
  img i = Fof i (Sset β) (Sset β)

  img∈u : (i : Op16) → ⟨ img i ∈ˢ u ⟩
  img∈u i = subst (λ v → ⟨ img i ∈ˢ v ⟩) (sym u-step)
    (step-in-img (Sset β) (img i) i (Sset β) (Sset β)
      (u-self-in (Sset β)) (u-self-in (Sset β)) refl)

  fresh : (x : V ℓ) → ⟨ x ∈ˢ Sset β ⟩ → Empty.⊥
  fresh x h = ∅-empty x (∈∈ₛ {a = x} {b = ∅} .fst
    (subst (λ w → ⟨ x ∈ˢ w ⟩) (Sset-zero) h))
```

<!--en-->
## The key decomposition

The soundness direction reads the formula's satisfaction back into the
delivered order, and the bridge is the least producer. The key of a member
of the level is decomposed by the named-helper shape the sealing probe
cured: the case analysis runs on the key as data, never `with`-cased, and
the boundedness of the key's arguments travels with it. Three facts carry
the clause. The key of the empty set is the self producer, by the
leastness of the key. The key of any other member is an image at the common
stage, since the only self-produced value at the level is the empty set.
And the self producer precedes every image at the same stage, which is the
comparison's own second clause.
<!--zh-->
## 键的分解

健全方向把公式的满足读回已交付之序，而桥就是最小生产者。层的成员的键用密封探针已治愈的具名辅助形状分解：情形分析把键当数据处理，绝不用 `with` 去分，键的参数有界性随行。三条事实承载这条子句。空集的键是自身生产者，凭键的极小性。任何其他成员的键是公共阶段处的一个像，因为该层唯一自身产出的值就是空集。而自身生产者先于同一阶段的每个像，这正是比较自身的第二条子句。
<!--/-->

```agda
module Keys where
  open Level

  data KeyShape : Type (ℓ-suc ℓ) where
    kself : Ord → KeyShape
    kimg  : Ord → Op16 → Producer → Producer → KeyShape

  keyBack : (m : Member (sucV β)) → Trace → KeyShape → Type (ℓ-suc ℓ)
  keyBack m t (kself δ) = memberKey (sucV β) ordS m ≡ (prod-self δ , tt*)
  keyBack m t (kimg δ i p q) =
    Σ[ w ∈ StageBounded (prod-image δ i p q) ]
      (memberKey (sucV β) ordS m ≡ (prod-image δ i p q , w))

  keyDecomp : (m : Member (sucV β))
            → Σ[ s ∈ KeyShape ] keyBack m (memberKey (sucV β) ordS m) s
  keyDecomp m = go (memberKey (sucV β) ordS m) refl
    where
    go : (t : Trace) → memberKey (sucV β) ordS m ≡ t
       → Σ[ s ∈ KeyShape ] keyBack m t s
    go (prod-self δ , w) e = kself δ , e
    go (prod-image δ i p q , w) e = kimg δ i p q , (w , e)

  keyStageβ : (m : Member (sucV β))
            → prod-stage (memberKey (sucV β) ordS m .fst) ≡ (β , ordβ)
  keyStageβ m = Σ≡Prop isPropIsOrd (memberStage-new β ordβ m (fresh (m .fst)))

  keyOfSelf : (m : Member (sucV β)) (p : m .fst ≡ ∅)
            → memberKey (sucV β) ordS m ≡ (prod-self (β , ordβ) , tt*)
  keyOfSelf m p = go (keyDecomp m)
    where
    t : Trace
    t = prod-self (β , ordβ) , tt*
    v : prod-value (t .fst) ≡ m .fst
    v = Sset-zero ∙ sym p
    go : Σ[ s ∈ KeyShape ] keyBack m (memberKey (sucV β) ordS m) s
       → memberKey (sucV β) ordS m ≡ (prod-self (β , ordβ) , tt*)
    go (kself δ , e) = e ∙ Σ≡Prop isPropStageBounded
      (cong prod-self (sym (cong (λ s → prod-stage (s .fst)) e) ∙ keyStageβ m))
    go (kimg δ i a b , (w , e)) =
      Empty.rec (leastTrace-least (m .fst)
        (member-trace (sucV β) ordS m) t v belowKey)
      where
      imgBelow : prod-self (β , ordβ) ≺ prod-image δ i a b
      imgBelow = inr (sym (sym (cong (λ s → prod-stage (s .fst)) e) ∙ keyStageβ m))
      belowKey : t ⊰ memberKey (sucV β) ordS m
      belowKey =
        subst (λ w → prod-self (β , ordβ) ≺ w .fst) (sym e) imgBelow

  keyIsImg : (m : Member (sucV β)) (q : m .fst ≡ ∅ → Empty.⊥)
           → Σ[ i ∈ Op16 ] Σ[ p ∈ Producer ] Σ[ r ∈ Producer ]
               Σ[ w ∈ StageBounded (prod-image (β , ordβ) i p r) ]
               (memberKey (sucV β) ordS m ≡ (prod-image (β , ordβ) i p r , w))
  keyIsImg m q = go (keyDecomp m)
    where
    go : Σ[ s ∈ KeyShape ] keyBack m (memberKey (sucV β) ordS m) s
       → Σ[ i ∈ Op16 ] Σ[ p ∈ Producer ] Σ[ r ∈ Producer ]
             Σ[ w ∈ StageBounded (prod-image (β , ordβ) i p r) ]
             (memberKey (sucV β) ordS m ≡ (prod-image (β , ordβ) i p r , w))
    go (kself δ , e) = Empty.rec (q (self-val δ))
      where
      self-val : (δ : Ord) → m .fst ≡ ∅
      self-val δ = sym (leastTrace-value (m .fst) (member-trace (sucV β) ordS m))
        ∙ cong (λ s → prod-value (s .fst)) e
        ∙ cong (λ γ → Sset (γ .fst))
            (sym (cong (λ s → prod-stage (s .fst)) e) ∙ keyStageβ m)
        ∙ Sset-zero
    go (kimg δ i p r , (w , e)) = i , p , r , (substB , path)
      where
      δβ : δ ≡ (β , ordβ)
      δβ = sym (cong (λ s → prod-stage (s .fst)) e) ∙ keyStageβ m
      substB : StageBounded (prod-image (β , ordβ) i p r)
      substB = subst (λ d → StageBounded (prod-image d i p r)) δβ w
      path : memberKey (sucV β) ordS m ≡
             (prod-image (β , ordβ) i p r , substB)
      path = e ∙ Σ≡Prop isPropStageBounded (cong (λ d → prod-image d i p r) δβ)

  selfLtImg : (m n : Member (sucV β))
            → memberKey (sucV β) ordS m ≡ (prod-self (β , ordβ) , tt*)
            → Σ[ i ∈ Op16 ] Σ[ p ∈ Producer ] Σ[ r ∈ Producer ]
                Σ[ w ∈ StageBounded (prod-image (β , ordβ) i p r) ]
                (memberKey (sucV β) ordS n ≡ (prod-image (β , ordβ) i p r , w))
            → Sset-below (sucV β) ordS m n
  selfLtImg m n em (i , p , r , (w , en)) =
    subst (λ (t : Trace) → t .fst ≺ memberKey (sucV β) ordS n .fst) (sym em)
      (subst (λ (t : Trace) → prod-self (β , ordβ) ≺ t .fst) (sym en) (inr refl))
```

<!--en-->
## The formula, and the soundness direction

The formula states the one expressible clause of the order at the level:
the first member is the self, the empty set, and the second is not. Its
satisfaction is read at the small index, and the atom's content is the
empty-set equality of the two values, the constant's index transported
through the presentation. The soundness direction runs the key facts: a
satisfied clause gives the first value empty and the second not, so the
first key is the self and the second is an image, and the self precedes the
image at the common stage. The completeness direction is the residue, named
in the D-10 record.
<!--zh-->
## 公式，与健全方向

公式陈述该层之序唯一可表达的那条子句：第一个成员是自身，即空集，第二个不是。其满足在小索引处读出，原子的内容是两值间的空集等式，常量的索引经表示搬运。健全方向跑过键事实：被满足的子句给出第一个值为空、第二个非空，于是第一个键是自身、第二个是像，而自身在同一阶段先于像。完备方向是残余，已在 D-10 记录中具名。
<!--/-->

```agda
module Adeq where
  open Level
  open Keys
  module U = DefOf u
  open U using ( ι; _⊨ᵐ_ )
  open import Cubical.HITs.CumulativeHierarchy.Properties using ( ∈ₛ⟪_⟫↪_ )

  selfIdx : ⟪ u ⟫
  selfIdx = ∈-asFiber {a = ∅} {b = u} ∅∈u .fst

  selfEq : ⟪ u ⟫↪ selfIdx ≡ ∅
  selfEq = ∈-asFiber {a = ∅} {b = u} ∅∈u .snd

  -- The first projection of the inner embedding is the presentation map,
  -- definitionally.
  ιfst : (m : ⟪ u ⟫) → fst (ι m) ≡ ⟪ u ⟫↪ m
  ιfst m = refl

  toMem : (a : ⟪ u ⟫) → Member (sucV β)
  toMem a = ⟪ u ⟫↪ a , ∈∈ₛ {a = ⟪ u ⟫↪ a} {b = u} .snd (∈ₛ⟪ u ⟫↪ a)

  σ< : Formula ⟪ u ⟫ 2
  σ< = (var zero ≐ con selfIdx) ∧̇ ¬̇ (var (suc zero) ≐ con selfIdx)

  atom-out : (a b : ⟪ u ⟫)
           → ⟨ (ι a ∷ ι b ∷ []) ⊨ᵐ (var zero ≐ con selfIdx) ⟩ → ⟪ u ⟫↪ a ≡ ∅
  atom-out a b h = sym (ιfst a) ∙ h ∙ ιfst selfIdx ∙ selfEq

  atom-in : (a b : ⟪ u ⟫) → ⟪ u ⟫↪ a ≡ ∅
          → ⟨ (ι a ∷ ι b ∷ []) ⊨ᵐ (var zero ≐ con selfIdx) ⟩
  atom-in a b e = ιfst a ∙ e ∙ sym selfEq ∙ sym (ιfst selfIdx)

  neq-out : (a b : ⟪ u ⟫)
          → ⟨ (ι a ∷ ι b ∷ []) ⊨ᵐ (¬̇ (var (suc zero) ≐ con selfIdx)) ⟩
          → (⟪ u ⟫↪ b ≡ ∅ → Empty.⊥)
  neq-out a b h e = h (atom-in b a e)

  sat-out : (a b : ⟪ u ⟫)
          → ⟨ (ι a ∷ ι b ∷ []) ⊨ᵐ σ< ⟩ → Sset-below (sucV β) ordS (toMem a) (toMem b)
  sat-out a b (h₁ , h₂) =
    selfLtImg (toMem a) (toMem b)
      (keyOfSelf (toMem a) (atom-out a b h₁))
      (keyIsImg (toMem b) (neq-out a b h₂))
```

<!--en-->
## The carve, and the corrected placement

The order element is the satisfaction set of the formula, built by the
satisfaction engine at the carrier: the set of pairs `pr x y` of members of
the level satisfying the formula. The engine's abstract closure, read at
the concrete limit level, places the set in any limit level above, the
corrected offset of the D-10 record; the out-read, a pair in the order
element is below at the level, follows from the engine's adequacy at the
tuple and the soundness direction; and the pairs clause, every member of
the order element is a pair of members of the level, is the engine's tuple
decode.
<!--zh-->
## 刻法，与修正后的放置

序元素是公式的满足集，由满足集引擎在载体处建成：该层成员中满足公式的对 `pr x y` 之集。引擎的抽象闭包，在具体极限层处读出，把该集放入其上任意极限层，即 D-10 记录的修正偏移；读出方向，「序元素中的对在该层居下」，由引擎在元组处的充分性连同健全方向得出；「成员皆对」子句，「序元素的每个成员都是该层成员的一对」，就是引擎的元组解码。
<!--/-->

```agda
module Carve where
  open Level
  module U = DefOf u
  open U using ( SM; ι )
  open import L.Rud.SatSets {ℓ} lem A using ( module Sat )
  open import L.Rud.Step {ℓ} lem A using ( Sset-mem; Sset-trans; Jset-rud )
  open import L.Rud.OrdArith {ℓ} lem using ( isLimit )

  Utr : (x y : S) → ⟨ x ∈ˢ y ⟩ → ⟨ y ∈ˢ u ⟩ → ⟨ x ∈ˢ u ⟩
  Utr x y x∈y y∈u = Sset-trans (sucV β) {x = y} {y = x} x∈y y∈u

  module OrderAt (μ : S) (limμ : ⟨ isLimit μ ⟩) (suc∈μ : ⟨ sucV β ∈ˢ μ ⟩) where
    Jtr : (a b : S) → ⟨ b ∈ˢ Sset μ ⟩ → ⟨ a ∈ˢ b ⟩ → ⟨ a ∈ˢ Sset μ ⟩
    Jtr a b b∈J a∈b = Sset-trans μ {x = b} {y = a} a∈b b∈J
    Jrud : (i : Op16) (a b : S) → ⟨ a ∈ˢ Sset μ ⟩ → ⟨ b ∈ˢ Sset μ ⟩
         → ⟨ Fof i a b ∈ˢ Sset μ ⟩
    Jrud i a b = Jset-rud μ limμ i a b
    JU : ⟨ u ∈ˢ Sset μ ⟩
    JU = Sset-mem {α = μ} {β = sucV β} suc∈μ
    module S = Sat u Utr (λ z → ⟨ z ∈ˢ Sset μ ⟩) Jtr Jrud JU

    orderAt : S
    orderAt = S.T 1 Adeq.σ<

    orderAt-in : ⟨ orderAt ∈ˢ Sset μ ⟩
    orderAt-in = S.hT 1 Adeq.σ<

    Tup≡pr : (a b : ⟪ u ⟫)
           → S.Tup 1 (ι a ∷ ι b ∷ []) ≡ pr (⟪ u ⟫↪ a) (⟪ u ⟫↪ b)
    Tup≡pr a b = cong₂ pr (Adeq.ιfst a) (Adeq.ιfst b)

    pair-out : (a b : ⟪ u ⟫)
             → ⟨ pr (⟪ u ⟫↪ a) (⟪ u ⟫↪ b) ∈ˢ orderAt ⟩
             → Sset-below (sucV β) ordS (Adeq.toMem a) (Adeq.toMem b)
    pair-out a b h = Adeq.sat-out a b
      (S.adeq-mem 1 Adeq.σ< (ι a ∷ ι b ∷ [])
        (subst (λ w → ⟨ w ∈ˢ S.T 1 Adeq.σ< ⟩) (Tup≡pr a b) h))

    pairs : (z : S) → ⟨ z ∈ˢ orderAt ⟩
          → ∥ Σ[ m ∈ SM ] Σ[ n ∈ SM ]
              (z ≡ pr (fst m) (fst n)) ∥₁
    pairs z h = PT.map split (S.Us-in 1 z (S.T-sub 1 Adeq.σ< z h))
      where
      split : Σ[ δ ∈ Vec SM 2 ] (z ≡ S.Tup 1 δ)
           → Σ[ m ∈ SM ] Σ[ n ∈ SM ]
               (z ≡ pr (fst m) (fst n))
      split ((m ∷ n ∷ []) , e) = m , n , (e ∙ Tup≡pr1 m n)
        where
        Tup≡pr1 : (m n : SM) → S.Tup 1 (m ∷ n ∷ []) ≡ pr (fst m) (fst n)
        Tup≡pr1 m n = refl
```

<!--en-->
## The residues

Three residues remain, each stated with its exact type. **The image-image
clause:** the formula comparing two fresh members at the level, the
value-enumeration shape with the least-producer conjuncts present, whose
soundness needs the key's operation to be read off the value and whose
decode is the op-leastness content the pricing named. **The completeness
direction:** `(a b : ⟪ u ⟫) → Sset-below (sucV β) ordS (toMem a) (toMem b)
→ ⟨ (ι a ∷ ι b ∷ []) ⊨ᵐ σ< ⟩`, which the image-image case blocks. **The
general level:** the formula at `⟪ Sset α ⟫` for a variable `α`, which
needs the internalized level story and the internalized satisfaction, the
content the retiring cone priced at its full cost. The interface's
successor-offset placement is corrected to the limit level, and the
instantiation of the interface as delivered remains open at every level
with a nontrivial order.
<!--zh-->
## 残余

三条残余，各带精确类型。**「像对像」子句：** 比较该层两个新成员的公式，即带最小生产者合取项的值枚举形状，其健全需要从值读出键的运算，其解码正是定价所点名的运算极小性内容。**完备方向：** `(a b : ⟪ u ⟫) → Sset-below (sucV β) ordS (toMem a) (toMem b) → ⟨ (ι a ∷ ι b ∷ []) ⊨ᵐ σ< ⟩`，被「像对像」情形挡住。**一般层：** 变元 `α` 处 `⟪ Sset α ⟫` 上的公式，需要内化的层故事与内化的满足机器，即退役锥按其全部代价定价的内容。界面的后继偏移放置已修正为极限层，而照原样的界面实例化在序不平凡的任何一层仍然开放。
<!--/-->

<!--en-->
## Recap

The chapter runs the D-10 check on the order formula's recorded targets and
builds what the check leaves expressible. At the level `sucV ∅`, where the
successor clause is the whole order, the formula's self-below-image clause
is delivered with its soundness direction against the delivered order,
through the key decomposition the sealing probe cured; the carve places
the order element, the satisfaction set of the formula, in any limit level
above, with the pair-out read and the pairs clause. The image-image
clause, the completeness direction, and the general-level formula are the
named residues, each gated on the internalized satisfaction the tree does
not carry.
<!--zh-->
## 小结

本章对序公式记录在案的目标跑 D-10 检查，并建造检查后仍可表达之物。在 `sucV ∅` 处，即后继子句就是整个序的那一层，公式的「自身在像下」子句连同对照已交付之序的健全方向交付，途经密封探针已治愈的键分解；刻法把序元素，即公式的满足集，放入其上任意极限层，连同读出对的方向与「成员皆对」子句。「像对像」子句、完备方向与一般层公式是具名的残余，各以树中未载的内化满足机器为闸。
<!--/-->
