<!--en-->
# The constructible hierarchy and universe

The constructible hierarchy starts from the empty set and repeatedly applies definable power set at ordinal stages, taking unions at limits. The resulting stages are transitive and monotone; their union forms the transitive class `L`{.Agda} and its restricted set-theoretic structure.
<!--zh-->
# 可构造层级与可构造宇宙

可构造层级从空集开始，在序数阶段反复施加可定义幂集，并在极限处取并。所得阶段具有传递性与单调性；其并形成传递类 `L`{.Agda} 及其限制集合论结构。
<!--ja-->
# 構成可能階層と構成可能宇宙

構成可能階層は空集合から始まり、順序数段階で定義可能冪集合を繰り返し、極限では和集合を取ります。各段階は推移的かつ単調であり、その合併が推移的クラス `L`{.Agda} とその制限された集合論的構造を与えます。
<!--/-->

<!--en-->
One design choice does most of the work. The tower is indexed not by a separate
type of ordinals but by **sets themselves**, through the recursion on membership
that regularity licensed: `Lset α = ⋃ { Def (Lset β) ∣ β ∈ α }`. This single
equation covers zero, successors, and limits at once, and on von Neumann
ordinals it is exactly Gödel's tower. Alongside it runs an inductive predicate
`isLayer`{.Agda}, "being a stage", whose constructors are the tower's closure
principles; the two views cooperate throughout.
<!--zh-->
一个设计选择承担了大部分工作。塔的索引不是另立的序数类型，而是**集合自身**，凭借正则性所授权的沿成员关系的递归：`Lset α = ⋃ { Def (Lset β) ∣ β ∈ α }`。这一条方程同时覆盖零、后继与极限，而在冯·诺伊曼序数上它恰是哥德尔的塔。与之并行的是归纳谓词 `isLayer`{.Agda}，「是一个层」，其构造子就是塔的闭包原则；两个视角全章协作。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth

module L.Constructible {ℓ : Level} where

open import FOL.ZFStructure using ( ZFStructure; _↾_; module hPropStructure; Transitive )
open import FOL.Syntax using ( Formula )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ; ∈-induction; ∈-induction-compute )
open import V.Model {ℓ} using ( union-family-in; union-family-out )
open import L.Definability {ℓ} using ( module DefOf )

open import Cubical.Foundations.HLevels using ( isProp× )
import Cubical.Data.Empty as Empty
import Cubical.Data.Sum as Sum
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁ )
open import Cubical.HITs.CumulativeHierarchy.Base using ( sett )
open import Cubical.HITs.CumulativeHierarchy.Properties
  using ( ∈∈ₛ; ∈-asFiber; ⟪_⟫; ⟪_⟫↪; ∈ₛ⟪_⟫↪_ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ∅; ∅-empty; ⁅_,_⁆; pairing-ax; ⋃_; union-ax; _∪_ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ

𝒟 : S → S
𝒟 A = DefOf.Def A
```

<!--en-->
## Transitive sets

Every stage of the hierarchy is transitive: the empty set is transitive, definable power set preserves transitivity, and unions of transitive sets remain transitive. These closure facts match the constructors used to build layers.
<!--zh-->
## 传递集

层级的每个阶段都是传递的：空集传递，可定义幂集保持传递性，传递集之并仍然传递。这些封闭性事实与构造层所用的构造子逐一对应。
<!--ja-->
## 推移的集合

階層の各段階は推移的です。空集合は推移的であり、定義可能冪集合は推移性を保存し、推移的集合の和も推移的です。これらの閉性は層を作る構成子に対応します。
<!--/-->

<!--en-->
(`𝒟` is the book's short glyph for the previous chapter's `Def`, matching the usual script letter for the operator.)
<!--zh-->
(`𝒟` 是上一章 `Def` 在本书中的短记号，对齐这个算子惯用的花体字母。)
<!--/-->

```agda
isTransV : S → Type (ℓ-suc ℓ)
isTransV A = Transitive 𝒮ᵥ (λ x → x ∈ˢ A)

isPropIsTransV : (A : S) → isProp (isTransV A)
isPropIsTransV A p q i {x} {y} y∈x x∈A = (y ∈ˢ A) .snd (p y∈x x∈A) (q y∈x x∈A) i

∅-trans : isTransV ∅
∅-trans {x} y∈x x∈∅ = Empty.rec (∅-empty x (∈∈ₛ {a = x} {b = ∅} .fst x∈∅))

𝒟-trans : ∀ {A} → isTransV A → isTransV (𝒟 A)
𝒟-trans {A} Atr {x} {y} y∈x x∈𝒟A =
  DefOf.Refine.A⊆Def A Atr y (DefOf.Def∋⊆A A x x∈𝒟A y y∈x)

⋃-trans : (x : S) → ((y : S) → ⟨ y ∈ˢ x ⟩ → isTransV y) → isTransV (⋃ x)
⋃-trans x mem {u} {v} v∈u u∈⋃x =
  ∈∈ₛ {a = v} {b = ⋃ x} .snd (union-ax x v .snd
    (PT.map
      (λ { (w , (w∈ₛx , u∈ₛw)) →
        let w∈x = ∈∈ₛ {a = w} {b = x} .snd w∈ₛx
            u∈w = ∈∈ₛ {a = u} {b = w} .snd u∈ₛw
        in w , (w∈ₛx , ∈∈ₛ {a = v} {b = w} .fst (mem w w∈x v∈u u∈w)) })
      (union-ax x u .fst (∈∈ₛ {a = u} {b = ⋃ x} .fst u∈⋃x))))

∪-trans : ∀ {A B} → isTransV A → isTransV B → isTransV (A ∪ B)
∪-trans {A} {B} tA tB = ⋃-trans ⁅ A , B ⁆ prem
  where
  prem : (y : S) → ⟨ y ∈ˢ ⁅ A , B ⁆ ⟩ → isTransV y
  prem y y∈ = PT.rec (isPropIsTransV y)
    (λ { (Sum.inl p) → subst isTransV (sym p) tA
       ; (Sum.inr p) → subst isTransV (sym p) tB })
    (pairing-ax A B y .fst (∈∈ₛ {a = y} {b = ⁅ A , B ⁆} .fst y∈))

setUnion-trans : (X : Type ℓ) (f : X → S) → ((x : X) → isTransV (f x))
               → isTransV (⋃ (sett X f))
setUnion-trans X f hf = ⋃-trans (sett X f)
  (λ y → PT.rec (isPropIsTransV y)
    (λ { (x , fx≡y) → subst isTransV fx≡y (hf x) }))
```

<!--en-->
## Ordinals, just the predicate

The tower's honest indices are the von Neumann ordinals, and inside a
well-founded, extensional universe the classical definition shrinks to almost
nothing: an **ordinal** is a transitive set of transitive sets.
Well-foundedness and extensionality need not be asked, the hierarchy supplies
them globally, and linearity is a classical theorem for later, not part of the
notion. This chapter needs only the predicate and its propositionality; the
theory of ordinals gets its own chapters when the closure proofs need it.
<!--zh-->
## 序数，仅取谓词

塔的诚实索引是冯·诺伊曼序数，而在良基、外延的宇宙里，经典定义缩得几乎不剩什么：**序数**就是由传递集组成的传递集。良基与外延无须写进定义，层级全局供应；线序是留待后文的经典定理，不属于概念本身。本章只需要这个谓词及其命题性；序数的理论等闭包证明用到时另章展开。
<!--ja-->
## 順序数の述語

ここで順序数とは、推移的で、かつ各要素も推移的な集合です。この段階では順序関係の一般論を展開せず、構成可能階層の添字に必要な述語だけを用います。
<!--/-->



```agda
IsOrd : S → Type (ℓ-suc ℓ)
IsOrd A = isTransV A × ((x : S) → ⟨ x ∈ˢ A ⟩ → isTransV x)

isPropIsOrd : (A : S) → isProp (IsOrd A)
isPropIsOrd A = isProp× (isPropIsTransV A)
                  (isPropΠ λ x → isPropΠ λ _ → isPropIsTransV x)
```

<!--en-->
## Layers

`isLayer A` says "A is a stage of the tower". Three ideas, five constructors:
the base, closure under `𝒟`, and closure under unions in three strengths
(members-all-layers, binary, small-indexed family). The binary and family forms
are not derivable from the general one: `union-layer`{.Agda} demands an
*untruncated* layer proof for each member, which pair membership cannot supply,
while weakening it to a truncated premise would break the structural recursion
of the transitivity proof below. Registering them as constructors dissolves the
dilemma, and does not change which sets are constructible, since a union's
members were already members of the parts. The family form is what later makes
limit stages like `L_ω` possible.
<!--zh-->
## 层

`isLayer A` 说「A 是塔的一个阶段」。三个想法，五个构造子：基底、对 `𝒟` 封闭，以及三种力度的并封闭 (成员皆层、二元、小索引族)。二元与族形式不能从一般形式派生：`union-layer`{.Agda} 要求逐成员**不加截断**的层证明，配对隶属给不出；而把前提弱化为截断版又会破坏下文传递性证明的结构递归。把它们注册为构造子，两难俱解，且不改变哪些集合可构造，因为并的成员本就是各部分的成员。族形式正是日后极限阶段 (如 `L_ω`) 的来路。
<!--ja-->
## 層

層は空集合、定義可能冪集合、または小さな族の和として得られる集合です。各構成子が推移性を保存するので、すべての層は推移的です。
<!--/-->

<!--en-->
Every layer is transitive: one induction, each case the matching closure lemma.
<!--zh-->
每个层都传递：一次归纳，各情形恰是对应的闭包引理。
<!--/-->

```agda
data isLayer : S → Type (ℓ-suc ℓ) where
  ∅-layer        : isLayer ∅
  𝒟-layer        : ∀ {A} → isLayer A → isLayer (𝒟 A)
  union-layer    : (x : S) → ((y : S) → ⟨ y ∈ˢ x ⟩ → isLayer y) → isLayer (⋃ x)
  union₂-layer   : ∀ {A B} → isLayer A → isLayer B → isLayer (A ∪ B)
  setUnion-layer : (X : Type ℓ) (f : X → S)
                 → ((x : X) → isLayer (f x)) → isLayer (⋃ (sett X f))

layer-trans : ∀ {A} → isLayer A → isTransV A
layer-trans ∅-layer = ∅-trans
layer-trans (𝒟-layer {A} lA) = 𝒟-trans {A} (layer-trans lA)
layer-trans (union-layer x mem) = ⋃-trans x (λ y y∈x → layer-trans (mem y y∈x))
layer-trans (union₂-layer lA lB) = ∪-trans (layer-trans lA) (layer-trans lB)
layer-trans (setUnion-layer X f hf) = setUnion-trans X f (λ x → layer-trans (hf x))
```

<!--en-->
## The tower

Now the tower itself, by recursion on membership. Two technical seals first:
`𝒟` unfolds to a heavy `sett` over formulas, and the recursion machinery
itself unfolds to the accessibility eliminator, so both would otherwise be
dragged into every later conversion; `opaque`{.Agda} makes `𝒟ₒ` and the tower
black boxes, unsealed only where a lemma genuinely needs the contents, with
`Lset-compute`{.Agda} as the tower's official unfolding. The step takes the union, over the members `β` of
`α`, of `𝒟ₒ` applied to the recursive values, and the computation rule holds
propositionally.
<!--zh-->
## 塔

现在造塔本身，沿成员关系递归。先上两道技术封印：`𝒟` 展开是公式上沉重的 `sett`，递归机器自身又展开成可及性消去子，二者都会被拖进日后的每一次转换；`opaque`{.Agda} 让 `𝒟ₒ` 与塔成为黑箱，只在真正需要内容的引理处开封，`Lset-compute`{.Agda} 是塔的官方展开式。步进取 `α` 的成员 `β` 上 `𝒟ₒ` 作用于递归值的并，计算规则命题级成立。
<!--ja-->
## 階層

`Lset α`{.Agda} は順序数 `α` の要素に対応する以前の定義可能段階を集めます。所属再帰がこの定義を与え、各 `Lset α`{.Agda} が層であり推移的であることを同時に示せます。
<!--/-->



```agda
opaque
  𝒟ₒ : S → S
  𝒟ₒ A = 𝒟 A

LsetStep : (α : S) → (∀ β → β ∈ᵗ α → S) → S
LsetStep α rec = ⋃ (sett ⟪ α ⟫ (λ m → 𝒟ₒ (rec (⟪ α ⟫↪ m) (mem m))))
  where
  mem : (m : ⟪ α ⟫) → ⟪ α ⟫↪ m ∈ᵗ α
  mem m = ∈∈ₛ {a = ⟪ α ⟫↪ m} {b = α} .snd (∈ₛ⟪ α ⟫↪ m)

opaque
  Lset : S → S
  Lset = ∈-induction LsetStep

opaque
  unfolding Lset
  Lset-compute : (α : S) → Lset α ≡ LsetStep α (λ β _ → Lset β)
  Lset-compute = ∈-induction-compute LsetStep
```

<!--en-->
Every value of the tower is a layer: unfold once with `Lset-compute`{.Agda}, use
the inductive hypothesis on each member, raise by `𝒟ₒ-layer`{.Agda} (the seal
opened exactly here), and close the family union with
`setUnion-layer`{.Agda}.
<!--zh-->
塔的每个值都是层：用 `Lset-compute`{.Agda} 展开一次，对每个成员用归纳假设，经 `𝒟ₒ-layer`{.Agda} 升一层 (封印恰在此处开启)，再用 `setUnion-layer`{.Agda} 把族并收回层。
<!--/-->

```agda
opaque
  unfolding 𝒟ₒ
  𝒟ₒ-layer : ∀ {A} → isLayer A → isLayer (𝒟ₒ A)
  𝒟ₒ-layer = 𝒟-layer

Lset-layer : (α : S) → isLayer (Lset α)
Lset-layer = ∈-induction step
  where
  step : (α : S) → (∀ β → β ∈ᵗ α → isLayer (Lset β)) → isLayer (Lset α)
  step α IH = subst isLayer (sym (Lset-compute α))
    (setUnion-layer ⟪ α ⟫ (λ m → 𝒟ₒ (Lset (⟪ α ⟫↪ m)))
      (λ m → 𝒟ₒ-layer (IH (⟪ α ⟫↪ m) (mem m))))
    where
    mem : (m : ⟪ α ⟫) → ⟪ α ⟫↪ m ∈ᵗ α
    mem m = ∈∈ₛ {a = ⟪ α ⟫↪ m} {b = α} .snd (∈ₛ⟪ α ⟫↪ m)
```

<!--en-->
## Stages compared

Two more facts about the tower carry every closure argument in the chapters
ahead, and both are cheap once the seal is opened in the right place.
<!--zh-->
## 阶段之间的比较

关于塔还有两个事实，承载着后续诸章的每一个闭包论证，而只要在对的地方开封，二者都很廉价。
<!--ja-->
## 段階の比較

`β ∈ α` なら、`β` の段階で定義可能な集合は `α` の段階に含まれます。所属の特徴付けからこの包含を得て、構成可能階層の狭義単調性を示します。
<!--/-->

<!--en-->
The first names the operator's membership. `𝒟ₒ A` was built as the set of
definable subsets of `A`, so belonging to it is, by construction, "merely, is
some `defSet φ`": exhibiting a formula together with an extensional equation is
exactly what it takes to place a set inside the operator. The seal opens for one
line and closes again.

The second unfolds the tower once and reads the union both ways. A stage is the
union, over the members of its index, of `𝒟ₒ` of the earlier stages; so belonging
to a stage is exactly belonging to `𝒟ₒ` of some earlier stage, and that
equivalence is given as its two directions, since that is how consumers use it.
Going in is a member of the union named by its index; coming out is the union
axiom followed by naming the fibre.

Monotonicity is then a corollary, not a construction: a lower stage sits inside
`𝒟ₒ` of itself by the previous chapter's refinement bound applied to a transitive
set, and going in carries it up. Stating the characterization rather than the
corollary costs nothing here and saves the later chapters from re-deriving the
union structure each time they need to walk down it. The seal opens once more,
for the inclusion the other way: what the operator produces are subsets of what
it was given, so a member of `𝒟ₒ A` never has a member outside `A`.
<!--zh-->
第一条给算子的隶属命名。`𝒟ₒ A` 造出来就是 `A` 的可定义子集之集，故属于它按构造即「仅仅是某个 `defSet φ`」：要把一个集合放进算子里，拿出一条公式连同一个外延等式恰好就够。封印开一行，随即合上。

第二条把塔展开一次，再把那个并两头都读一遍。一个阶段是沿其索引的成员、对更早诸阶段的 `𝒟ₒ` 取的并；故属于一个阶段，恰是属于某个更早阶段的 `𝒟ₒ`，而这条等价按其两个方向给出，因为消费方正是这样用它的。进去是成为该并的成员，由其索引点名；出来是并公理，随后为纤维命名。

单调性于是是推论，而非构造：低阶段经上一章的精化界线施于传递集而落在自身的 `𝒟ₒ` 里面，再由「进去」抬上去。陈述这条刻画而非那条推论，此处不费分文，却省去后续诸章每次要沿并向下走时重新推导一遍并的结构。封印再开一次，为的是反向的那条包含：算子产出的都是它所收下者的子集，故 `𝒟ₒ A` 的成员绝不会有 `A` 之外的成员。
<!--/-->

```agda
opaque
  unfolding 𝒟ₒ
  𝒟ₒ-intro : (A x : S)
           → ∥ Σ[ φ ∈ Formula ⟪ A ⟫ 1 ] (DefOf.defSet A φ ≡ x) ∥₁
           → ⟨ x ∈ˢ 𝒟ₒ A ⟩
  𝒟ₒ-intro A x p = p

  𝒟ₒ-inv : (A x : S) → ⟨ x ∈ˢ 𝒟ₒ A ⟩
         → ∥ Σ[ φ ∈ Formula ⟪ A ⟫ 1 ] (DefOf.defSet A φ ≡ x) ∥₁
  𝒟ₒ-inv A x p = p
```

The pair the stage-cardinality construction takes at its limit step, one term:
the definable power set at the stage, read as a map from formulas
(`DefOf.defSet` at the stage), and the inversion that recovers a member's
defining formula (`𝒟ₒ-inv` at the stage).

```agda
  Lset⊆𝒟ₒ : (β x : S) → ⟨ x ∈ˢ Lset β ⟩ → ⟨ x ∈ˢ 𝒟ₒ (Lset β) ⟩
  Lset⊆𝒟ₒ β x = DefOf.Refine.A⊆Def (Lset β) (layer-trans (Lset-layer β)) x

  𝒟ₒ∋⊆ : (A x : S) → ⟨ x ∈ˢ 𝒟ₒ A ⟩ → (y : S) → ⟨ y ∈ˢ x ⟩ → ⟨ y ∈ˢ A ⟩
  𝒟ₒ∋⊆ A = DefOf.Def∋⊆A A

stageFam : (α : S) → ⟪ α ⟫ → S
stageFam α m = 𝒟ₒ (Lset (⟪ α ⟫↪ m))

Lset-in : (α δ x : S) → ⟨ δ ∈ˢ α ⟩ → ⟨ x ∈ˢ 𝒟ₒ (Lset δ) ⟩ → ⟨ x ∈ˢ Lset α ⟩
Lset-in α δ x δ∈α x∈𝒟ₒδ =
  subst (λ w → ⟨ x ∈ˢ w ⟩) (sym (Lset-compute α))
    (union-family-in ⟪ α ⟫ (stageFam α) (fib .fst) x
      (subst (λ δ → ⟨ x ∈ˢ 𝒟ₒ (Lset δ) ⟩) (sym (fib .snd)) x∈𝒟ₒδ))
  where
  fib = ∈-asFiber {a = δ} {b = α} δ∈α

Lset-out : (α x : S) → ⟨ x ∈ˢ Lset α ⟩
         → ∥ Σ[ δ ∈ S ] (⟨ δ ∈ˢ α ⟩ × ⟨ x ∈ˢ 𝒟ₒ (Lset δ) ⟩) ∥₁
Lset-out α x x∈Lα = PT.map
  (λ { (m , hx) → ⟪ α ⟫↪ m
    , (∈∈ₛ {a = ⟪ α ⟫↪ m} {b = α} .snd (∈ₛ⟪ α ⟫↪ m) , hx) })
  (union-family-out ⟪ α ⟫ (stageFam α) x
    (subst (λ w → ⟨ x ∈ˢ w ⟩) (Lset-compute α) x∈Lα))

Lset-mono : {α β : S} → ⟨ β ∈ˢ α ⟩ → {x : S} → ⟨ x ∈ˢ Lset β ⟩ → ⟨ x ∈ˢ Lset α ⟩
Lset-mono {α} {β} β∈α {x} x∈Lβ = Lset-in α β x β∈α (Lset⊆𝒟ₒ β x x∈Lβ)
```

<!--en-->
## The class L, and its structure

A set is **constructible** when some ordinal stage of the tower contains it.
The ordinal bound is part of the definition on purpose: the later theory
extracts stage ordinals, and this shape hands them over by construction. `L` is
a transitive class: stages are transitive, and the witnessing ordinal does not
move.
<!--zh-->
## 类 L，及其结构

一个集合是**可构造的**，指塔的某个序数阶段包含它。序数界故意写进定义：后文的理论要提取阶段序数，这个形状按构造直接交货。`L` 是传递类：阶段传递，见证序数不动。
<!--ja-->
## クラス L とその構造

集合が `L` に属するとは、ある順序数段階 `Lset α`{.Agda} に属することです。段階の推移性と単調性から `L` は推移的クラスとなり、周囲の構造を `L` に制限した構造 `𝒮ₗ`{.Agda} が得られます。
<!--/-->



```agda
isL : S → Ω
isL x = ⋁ S (λ α → ((IsOrd α , isPropIsOrd α) ⊓ (x ∈ˢ Lset α)))

isL-trans : Transitive 𝒮ᵥ isL
isL-trans {x} {y} y∈x x∈L = PT.rec (snd (isL y))
  (λ { (α , (ordα , x∈Lα)) →
    ∣ α , (ordα , layer-trans (Lset-layer α) y∈x x∈Lα) ∣₁ })
  x∈L
```

<!--en-->
Sitting in an ordinal stage *is* the definition, so the bridge in that direction
is the constructor itself. It is named because the chapters ahead reach for it
constantly: every closure proof ends by exhibiting a stage.
<!--zh-->
落在某个序数阶段中**就是**定义，故这个方向的桥就是构造子本身。之所以为它命名，是因为后续诸章会不断取用：每个闭包证明都以拿出一个阶段收尾。
<!--/-->

```agda
Lset→isL : (α : S) → IsOrd α → (x : S) → ⟨ x ∈ˢ Lset α ⟩ → ⟨ isL x ⟩
Lset→isL α oα x x∈Lα = ∣ α , (oα , x∈Lα) ∣₁
```

<!--en-->
And the chapter's deliverable: the constructible universe **as a structure**.
The restriction the structure chapter built for exactly this moment carves
`𝒮ʟ` out of `𝒮ᵥ`; its carrier is the constructible sets, its relations are
inherited, and the entire framework, syntax, satisfaction, the model record,
applies to it verbatim. The subscript is a small capital ʟ.
<!--zh-->
然后是本章的交付物：**作为结构的**可构造宇宙。结构章正为此刻打造的限制，从 `𝒮ᵥ` 中裁出 `𝒮ʟ`：载体是可构造集，关系原样继承，而整套框架，语法、满足、模型 record，逐字适用于它。下标是小型大写的 ʟ。
<!--/-->

```agda
𝒮ʟ : ZFStructure (hPropAlgebra (ℓ-suc ℓ))
𝒮ʟ = 𝒮ᵥ ↾ isL
```

<!--en-->
## Recap

The tower `Lset`{.Agda} rises by membership recursion, one equation for zero,
successors, and limits; `isLayer`{.Agda} names its closure principles and
`layer-trans`{.Agda} makes every stage transitive. `isL`{.Agda} is containment
in some ordinal stage, transitive as a class, and `𝒮ʟ`{.Agda} packages the
constructible sets as a structure. What the book must now prove is that this
world satisfies ZFC; the next chapter takes stock of exactly what that demands.
<!--zh-->
## 小结

塔 `Lset`{.Agda} 沿成员递归升起，一条方程通吃零、后继与极限；`isLayer`{.Agda} 点名其闭包原则，`layer-trans`{.Agda} 使每个阶段传递。`isL`{.Agda} 是「落在某个序数阶段中」，作为类传递，`𝒮ʟ`{.Agda} 把可构造集打包为结构。本书接下来要证的，是这个世界满足 ZFC；下一章先把这笔账目盘点清楚。
<!--ja-->
## まとめ

順序数で添字付けた `Lset`{.Agda} は、定義可能冪集合と和集合を繰り返す推移的で単調な階層です。ある段階に現れる集合全体が構成可能クラス `L` と、その制限構造 `𝒮ₗ`{.Agda} を与えます。
<!--/-->
