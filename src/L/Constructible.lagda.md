# The constructible universe

<!--en-->
Part 4 opens on the book's protagonist. Gödel's **constructible universe** is
what remains of a universe of sets when every appeal to arbitrary subsets is
replaced by the previous chapter's operator: start from nothing, take definable
subsets at every step, collect at every limit. The textbook writes it as a tower,
`L₀ = ∅`, `L_{α+1} = Def(L_α)`, unions at limits, and `L` is everything that
ever appears in the tower. This chapter builds the tower and the class `L`, and
packages the result as a structure `𝒮ʟ`, the world the rest of this part
studies.

One design choice does most of the work. The tower is indexed not by a separate
type of ordinals but by **sets themselves**, through the recursion on membership
that regularity licensed: `Lset α = ⋃ { Def (Lset β) ∣ β ∈ α }`. This single
equation covers zero, successors, and limits at once, and on von Neumann
ordinals it is exactly Gödel's tower. Alongside it runs an inductive predicate
`isLayer`{.Agda}, "being a stage", whose constructors are the tower's closure
principles; the two views cooperate throughout.
<!--zh-->
第四部以本书的主角开幕。哥德尔的**可构造宇宙**，是把一个集合宇宙里对任意子集的每次诉求都换成上一章那个算子之后剩下的东西：从空无出发，每一步只取可定义子集，每个极限处收拢。教科书把它写成一座塔，`L₀ = ∅`、`L_{α+1} = Def(L_α)`、极限取并，`L` 就是塔中出现过的一切。本章建起这座塔与类 `L`，并把结果打包成结构 `𝒮ʟ`，本部余下章节研究的世界。

一个设计选择承担了大部分工作。塔的索引不是另立的序数类型，而是**集合自身**，凭借正则性所授权的沿成员关系的递归：`Lset α = ⋃ { Def (Lset β) ∣ β ∈ α }`。这一条方程同时覆盖零、后继与极限，而在冯·诺伊曼序数上它恰是哥德尔的塔。与之并行的是归纳谓词 `isLayer`{.Agda}，「是一个层」，其构造子就是塔的闭包原则；两个视角全章协作。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth

module L.Constructible {ℓ : Level} where

open import FOL.ZFStructure using ( ZFStructure; _↾_; module hPropStructure; Transitive )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ; ∈-induction; ∈-induction-compute )
open import L.Definability {ℓ} using ( module DefOf )

open import Cubical.Foundations.HLevels using ( isProp× )
import Cubical.Data.Empty as Empty
import Cubical.Data.Sum as Sum
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁ )
open import Cubical.HITs.CumulativeHierarchy.Base using ( sett )
open import Cubical.HITs.CumulativeHierarchy.Properties
  using ( ∈∈ₛ; ⟪_⟫; ⟪_⟫↪; ∈ₛ⟪_⟫↪_ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ∅; ∅-empty; ⁅_,_⁆; pairing-ax; ⋃_; union-ax; _∪_ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ

𝒟 : S → S
𝒟 A = DefOf.Def A
```

<!--en-->
(`𝒟` is the book's short glyph for the previous chapter's `Def`, matching the
usual script letter for the operator.)

## Transitive sets
<!--zh-->
(`𝒟` 是上一章 `Def` 在本书中的短记号，对齐这个算子惯用的花体字母。)

## 传递集
<!--/-->

<!--en-->
The tower's stages will all be transitive sets, and the closure lemmas for
transitivity mirror, one for one, the layer constructors to come. A set is
**transitive** when membership in it is a transitive class in the sense of the
absoluteness chapter. The empty set is transitive vacuously; `𝒟` preserves
transitivity, the two halves being exactly the previous chapter's refinement
bounds (members of `𝒟 A` are subsets of `A`, and `A ⊆ 𝒟 A`); unions of
transitive sets are transitive. Because transitivity is a proposition, the
truncations in pair and family membership are harmless, giving the binary and
small-indexed union cases.
<!--zh-->
塔的每个阶段都将是传递集，而传递性的闭包引理与稍后的层构造子一一镜像。集合是**传递的**，指属于它构成绝对性章意义下的传递类。空集真空传递；`𝒟` 保传递，两半恰是上一章的精化界线 (`𝒟 A` 的成员是 `A` 的子集，且 `A ⊆ 𝒟 A`)；传递集之并传递。由于传递性是命题，配对与族隶属里的截断无碍，二元并与小索引并两个情形随之而得。
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
<!--zh-->
## 序数，仅取谓词
<!--/-->

<!--en-->
The tower's honest indices are the von Neumann ordinals, and inside a
well-founded, extensional universe the classical definition shrinks to almost
nothing: an **ordinal** is a transitive set of transitive sets.
Well-foundedness and extensionality need not be asked, the hierarchy supplies
them globally, and linearity is a classical theorem for later, not part of the
notion. This chapter needs only the predicate and its propositionality; the
theory of ordinals gets its own chapters when Part 4 needs them.
<!--zh-->
塔的诚实索引是冯·诺伊曼序数，而在良基、外延的宇宙里，经典定义缩得几乎不剩什么：**序数**就是由传递集组成的传递集。良基与外延无须写进定义，层级全局供应；线序是留待后文的经典定理，不属于概念本身。本章只需要这个谓词及其命题性；序数的理论等第四部用到时另章展开。
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
<!--zh-->
## 层
<!--/-->

<!--en-->
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

Every layer is transitive: one induction, each case the matching closure lemma.
<!--zh-->
`isLayer A` 说「A 是塔的一个阶段」。三个想法，五个构造子：基底、对 `𝒟` 封闭，以及三种力度的并封闭 (成员皆层、二元、小索引族)。二元与族形式不能从一般形式派生：`union-layer`{.Agda} 要求逐成员**不加截断**的层证明，配对隶属给不出；而把前提弱化为截断版又会破坏下文传递性证明的结构递归。把它们注册为构造子，两难俱解，且不改变哪些集合可构造，因为并的成员本就是各部分的成员。族形式正是日后极限阶段 (如 `L_ω`) 的来路。

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
<!--zh-->
## 塔
<!--/-->

<!--en-->
Now the tower itself, by recursion on membership. Two technical seals first:
`𝒟` unfolds to a heavy `sett` over formulas, and the recursion machinery
itself unfolds to the accessibility eliminator, so both would otherwise be
dragged into every later conversion; `opaque`{.Agda} makes `𝒟ₒ` and the tower
black boxes, unsealed only where a lemma genuinely needs the contents, with
`Lset-compute`{.Agda} as the tower's official unfolding. The step takes the union, over the members `β` of
`α`, of `𝒟ₒ` applied to the recursive values, and the computation rule holds
propositionally.
<!--zh-->
现在造塔本身，沿成员关系递归。先上两道技术封印：`𝒟` 展开是公式上沉重的 `sett`，递归机器自身又展开成可及性消去子，二者都会被拖进日后的每一次转换；`opaque`{.Agda} 让 `𝒟ₒ` 与塔成为黑箱，只在真正需要内容的引理处开封，`Lset-compute`{.Agda} 是塔的官方展开式。步进取 `α` 的成员 `β` 上 `𝒟ₒ` 作用于递归值的并，计算规则命题级成立。
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
## The class L, and its structure
<!--zh-->
## 类 L，及其结构
<!--/-->

<!--en-->
A set is **constructible** when some ordinal stage of the tower contains it.
The ordinal bound is part of the definition on purpose: the later theory
extracts stage ordinals, and this shape hands them over by construction. `L` is
a transitive class: stages are transitive, and the witnessing ordinal does not
move.
<!--zh-->
一个集合是**可构造的**，指塔的某个序数阶段包含它。序数界故意写进定义：后文的理论要提取阶段序数，这个形状按构造直接交货。`L` 是传递类：阶段传递，见证序数不动。
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
<!--zh-->
## 小结
<!--/-->

<!--en-->
The tower `Lset`{.Agda} rises by membership recursion, one equation for zero,
successors, and limits; `isLayer`{.Agda} names its closure principles and
`layer-trans`{.Agda} makes every stage transitive. `isL`{.Agda} is containment
in some ordinal stage, transitive as a class, and `𝒮ʟ`{.Agda} packages the
constructible sets as a structure. What the book must now prove is that this
world satisfies ZFC; the next chapter takes stock of exactly what that demands.
<!--zh-->
塔 `Lset`{.Agda} 沿成员递归升起，一条方程通吃零、后继与极限；`isLayer`{.Agda} 点名其闭包原则，`layer-trans`{.Agda} 使每个阶段传递。`isL`{.Agda} 是「落在某个序数阶段中」，作为类传递，`𝒮ʟ`{.Agda} 把可构造集打包为结构。本书接下来要证的，是这个世界满足 ZFC；下一章先把这笔账目盘点清楚。
<!--/-->
