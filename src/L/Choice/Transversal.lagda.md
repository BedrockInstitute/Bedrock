<!--en-->
# Choice by a transversal
<!--zh-->
# 以横截集实现选择
<!--ja-->
# 横断集合による選択
<!--/-->

<!--en-->
This chapter proves the axiom of choice for `𝒮ʟ` by separating the least member
of every cell under a stage-bounded internal well-order and showing that the
resulting set meets each pairwise-disjoint cell exactly once.
<!--zh-->
本章证明 `𝒮ʟ` 的选择公理：在循阶的内部良序下，从每一格分离出最小成员，并证明所得集合与每个两两不交的格恰交于一点。
<!--ja-->
本章では `𝒮ʟ` の選択公理を証明する。段階有界な内部の整列順序で各セルの最小要素を分出し、得られた集合が互いに素な各セルとちょうど一点で交わることを示す。
<!--/-->

<!--en-->
This chapter proves the axiom of choice at `𝒮ʟ` in the **transversal** form
used by the model record: given a set whose members
are inhabited and pairwise disjoint, merely a set meeting each member in exactly
one point.

The shape of the argument is the classical one, with its expensive step already
paid. The textbook well-orders the universe and takes the least member of every
cell. A well-order of all of `L` is a relation on a proper class, and this book
never built one; what the previous chapters built instead is a well-order of each
**stage**, uniformly, and, at every ordinal, as an element of the model. That is
enough, because a set is small. One ordinal bounds a family, its members and
their members all at once, and inside the tower at that ordinal the choosing is
an ordinary least-element search.

So the chapter is four moves. The **bound**: the stage chapter's bounding ordinal
for the family, above the family's own stage and hence above every member of
every member of it. The **order there**: the table's relation at that ordinal, an
element of the model, with two lemmas reading membership in it against the meta
comparison in both directions. The **description**: "some member of the family
contains this set, and nothing in that member precedes it", a formula with the
order as a constant, which the model's own separation cuts a set out with. The
**count**: that set meets each member in exactly one point, existence from the
least element and uniqueness from pairwise disjointness, which is what
disjointness is for and the only place the book uses it.

There is a fifth thing, and it is an observation rather than a move. Choice is
stated relative to a ZF model on this carrier, because the intersection it names
is that model's derived operation; and the whole of that dependence is one
transport along the intersection's specification.
<!--zh-->
本章证明选择公理在 `𝒮ʟ` 处的实例，采用模型 record 所用的**横截**形式：给定一个集合，其成员非空且两两不交，则仅仅存在一个与它每个成员恰交于一点的集合。

论证的形状就是经典的那个，只是那昂贵的一步早已付讫。教科书把宇宙良序化，再取每一格中最小的成员。`L` 整体的良序是真类上的关系，本书从未造过一个；前几章造出来的，是每个**阶段**上的良序，一致地造出，且在每个序数处都作为模型的一个元素。这就够了，因为集合是小的。单个序数一举界住一个族、它的成员与它们的成员，而在那个序数处的塔之内，选取不过是一次普通的极小元搜索。

于是本章只有四步。**上界**：阶段那一章为该族给出的上界序数，在该族自身的阶段之上，从而在它每个成员的每个成员之上。**那里的序**：表在那个序数处的关系，作为模型的一个元素，配两条引理把对它的隶属与元层面的比较双向读通。**那条描述**：「该族的某个成员含有这个集合，且那个成员中没有任何东西排在它之前」，一条以那个序为常元的公式，模型自家的分离据以雕出一个集合。**计数**：那个集合与每个成员恰交于一点，存在性来自极小元，唯一性来自两两不交，而这正是不交性的用途，也是全书唯一用到它的地方。

还有第五样东西，但它是一句观察、不是一步。选择相对于此载体上的一个 ZF 模型陈述，因为它所点名的交是那个模型的派生运算；而这份依赖的全部，不过是沿交的规格的一次搬运。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module L.Choice.Transversal {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula; var; con; _∈̇_; _∧̇_; ¬̇_; ∃̇_ )
import FOL.ZFModel
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Coding {ℓ} using ( pr )
open import L.Constructible {ℓ}
  using ( 𝒮ʟ; isL; isL-trans; IsOrd; Lset; Lset→isL )
open import L.Axioms.Basic {ℓ} using ( LsetS )
open import L.Choice.FirstIntersectionStage {ℓ} lem using ( bound-below₂ )
open import L.Choice.StageOrders {ℓ} lem using ( Mem; relOf )
open import L.Choice.InternalWellOrder {ℓ} lem using ( module Bound )
open import L.Coding.Model {ℓ} using ( appC; appC-adequate )
open import L.WellOrder.Base {ℓ-suc ℓ}
  using ( SWO; IsLeast; isPropLeastOf; leastOf )

open import Cubical.Data.Sigma using ( Σ≡Prop )
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁; ∣_∣₁ )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_; setIsSet )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ

module ModelL = FOL.ZFModel 𝒮ʟ
open ModelL using ( isZFModel )

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL renaming ( _⊨ᵐ_ to _⊨_ )
```

<!--en-->
## The description
<!--zh-->
## 那条描述
<!--ja-->
## 選択を表す論理式
<!--/-->

<!--en-->
`Pick`{.Agda} is the one-variable formula saying that a point lies in a member
of the family and has no predecessor there under the chosen relation.
<!--zh-->
`Pick`{.Agda} 是一条单自由变元公式，断言该点属于族的某个成员，且在选定关系下，该成员中没有点排在它之前。
<!--ja-->
`Pick`{.Agda} は一自由変数の論理式であり、点が族のある要素に属し、選んだ関係の下でその中に先行する点がないことを述べる。
<!--/-->

<!--en-->

One formula, one free variable, two constants. Of a set `z` it says: some member
of the family contains `z`, and nothing in that member precedes `z` under the
order. The application atom takes the order directly as a constant. The family
is likewise named directly, since it appears only under a membership atom.

The formula is sealed, by the standing law that a description read at constants
is sealed where it is built. Here that law is free rather than decisive: sealed
and unsealed both check in 2.3 s, and the chapter says so rather than borrowing
someone else's number. The reason is worth one line, because it says what the
earlier measurements were really about. Those descriptions carried coded syntax
inside them, and each satisfaction at a concrete environment normalized a whole
hierarchy description; this one carries four atoms and one application, so there
is nothing large to unfold. The seal stays, because it costs nothing and because
a later reader of this description should not have to re-measure.
<!--zh-->

一条公式，一个自由变元，两个常元。它对一个集合 `z` 说：该族的某个成员含有 `z`，且那个成员中没有任何东西在那个序下排在 `z` 之前。应用原子直接把那个序当作常元。族也直接点名，因为它只出现在一条隶属原子之下。

那条公式被封印，依的是常设定律：读在常元上的描述要在被造出之处封印。但在此处这条定律是免费的、而非决定性的：封印与不封印都检查 2.3 秒，本章据实说出这一点，而不去借用别处的数字。理由值得写一行，因为它说清了此前那些实测究竟在测什么。那些描述内部装着已编码的语法，每次在具体环境上的满足关系都要把一整条层级描述正规化；而这一条装的是四条原子与一次应用，没有什么大东西可展开。封印仍然保留，因为它分文不花，也因为日后读这条描述的人不该被迫重测一遍。
<!--/-->

Perf: sealed by the standing law (a description read at constants), though
measured here at 2.3 s either way: this description names no coded syntax.

```agda
opaque
  Pick : S → S → Formula S 1
  Pick c r =
    ∃̇ ( (var zero ∈̇ con c)
      ∧̇ ( (var (suc zero) ∈̇ var zero)
        ∧̇ (¬̇ ∃̇ ( (var zero ∈̇ var (suc zero))
               ∧̇ appC r zero (suc (suc zero)) )) ) )
```

<!--en-->
## The transversal
<!--zh-->
## 横截集
<!--ja-->
## 横断集合
<!--/-->

<!--en-->
Inside the bounding stage, least-element search chooses one point per cell;
separation collects those points, and disjointness proves uniqueness in every
intersection.
<!--zh-->
在上界阶段之内，极小元搜索为每一格选出一点；分离把这些点收集成集，而不交性证明每次相交中的唯一性。
<!--ja-->
上界段階の内部で最小要素の探索が各セルから一点を選び、分出公理がそれらを集合に集め、互いに素であることから各交わりでの一意性が従う。
<!--/-->

<!--en-->

The module fixes the ZF model supplying the intersection, the family, and the
family's two hypotheses. The choice-stage construction supplies the bound and
order at the family itself: `β`{.Agda} is an ordinal above the family's own
stage, hence above its members and their members, and above `ω` where the names
live; `W`{.Agda} is the well-order of the members of the tower at `β`{.Agda}; and
`rel`{.Agda} is that same order as an **element of the model**, which is what
lets it be named by a constant in the description at all.

`Cell x`{.Agda} is the predicate "is a member of `x`" on those members, and
`least`{.Agda} applies the generic search from `L.WellOrder.Base`{.Agda} to it.
The same search serves finite-stage orders and name selection, and will serve
later GCH constructions; here its role is specific: it turns the stage order
into one chosen representative for each cell. This is where excluded middle
buys the choice needed by the transversal.

`pick-in`{.Agda} and `pick-out`{.Agda} are the description's two readings, and
neither is a corollary of the other: one builds a satisfaction out of a least
element, the other extracts a least element from a satisfaction, and each has to
move a set between the two ways it can be presented, as an element of `L` and as
a member of the tower at `β`{.Agda}. Every truncation payload is named,
`Two`{.Agda} and `Predecessor`{.Agda}, so that neither reading writes the nesting
out; the negation is the one place a truncation is eliminated into the empty
type, and it is eliminated in a named helper.

Then the separation and the counting. `transversalSet`{.Agda} is the model's own
separation, at the tower at `β`{.Agda}, by the description. `Cut`{.Agda} fixes a
member of the family: the centre of the intersection is the least element, which
is in the transversal because `pick-in`{.Agda} says so and in the member because
being least includes being there. Uniqueness is where disjointness is spent.
Another point of the intersection satisfies the description, so it is least in
**some** member of the family; it also lies in this one; so the two members meet
and are equal; so it is least in this member too, and least elements are unique
by trichotomy alone. The generic uniqueness theorem
`isPropLeastOf`{.Agda} closes precisely this last comparison.
<!--zh-->

本模块固定下供应交运算的那个 ZF 模型、那个族，以及该族的两条假设。选择构造的阶段部分在该族自身处供应上界与序：`β`{.Agda} 是一个高于该族自身阶段的序数，从而高于它的成员及其成员，也高于诸名字所住的 `ω`；`W`{.Agda} 是 `β`{.Agda} 处塔的诸成员上的良序；而 `rel`{.Agda} 就是同一个序作为**模型的一个元素**，正是这一点才使它能在描述中被一个常元点名。

`Cell x`{.Agda} 是那些成员之上「是 `x` 的成员」这条谓词，而 `least`{.Agda} 把 `L.WellOrder.Base`{.Agda} 的泛型搜索施于它。同一搜索此前已用于有穷阶段序与名字选取，后面还用于 GCH 构造；它在此处的具体职责，是把阶段序变成每一格的一个选定代表。这正是排中律为横截集买来的选取。

`pick-in`{.Agda} 与 `pick-out`{.Agda} 是那条描述的两条读式，而两者互不为对方的推论：一条由极小元造出一个满足关系，另一条由满足关系取出一个极小元，且各自都要把一个集合在它可被呈现的两种形态之间搬动，即作为 `L` 的元素与作为 `β`{.Agda} 处塔的成员。两个截断载荷分别名为 `Two`{.Agda} 与 `Predecessor`{.Agda}，于是两条读式都不必把嵌套写开；否定式是唯一一处把截断消去到空类型的地方，而它是在一个具名辅助件里消去的。

随后是分离与计数。`transversalSet`{.Agda} 就是模型自家的分离，施于 `β`{.Agda} 处的塔，依那条描述。`Cut`{.Agda} 固定该族的一个成员：交的收缩中心就是那个极小元，它在横截集中，因为 `pick-in`{.Agda} 如此说；它在那个成员中，因为「是极小的」本身就包含「在那里」。唯一性正是不交性被花掉之处。交的另一个点满足那条描述，故它在该族的**某个**成员中是极小的；它同时又落在眼前这个成员里；故那两个成员相交，从而相等；故它在这个成员中也是极小的，而极小元仅凭三歧就唯一。泛型唯一性定理 `isPropLeastOf`{.Agda} 恰好收束这最后一次比较。
<!--/-->

```agda
module Trans (zf : isZFModel) (a : S)
             (inh : (x : S) → ⟨ x ∈ˢ a ⟩ → ∥ Σ[ y ∈ S ] ⟨ y ∈ˢ x ⟩ ∥₁)
             (disj : (x y : S) → ⟨ x ∈ˢ a ⟩ → ⟨ y ∈ˢ a ⟩
                   → ∥ Σ[ z ∈ S ] (⟨ z ∈ˢ x ⟩ × ⟨ z ∈ˢ y ⟩) ∥₁ → x ≡ y)
             where
  open ModelL.isZFModel zf using ( separate; separate-spec; _∩_; ∩-spec )
  private
    module B = Bound (fst a) (snd a)

  β : V ℓ
  β = B.boundOrd

  oβ : IsOrd β
  oβ = B.boundOrd-ord

  W : SWO (Mem (Lset β))
  W = B.boundOrder

  rel : S
  rel = B.orderL

  elt : Mem (Lset β) → S
  elt m = fst m , Lset→isL β oβ (fst m) (snd m)

  Cell : S → Mem (Lset β) → hProp (ℓ-suc ℓ)
  Cell x m = fst m ∈ fst x

  Least : S → S → Type (ℓ-suc ℓ)
  Least x z = Σ[ h ∈ ⟨ fst z ∈ Lset β ⟩ ] IsLeast W (Cell x) (fst z , h)

  private
    members : (x : S) → ⟨ x ∈ˢ a ⟩ → ∥ Σ[ m ∈ Mem (Lset β) ] ⟨ Cell x m ⟩ ∥₁
    members x x∈a = PT.map atMember (inh x x∈a)
      where
      atMember : Σ[ y ∈ S ] ⟨ y ∈ˢ x ⟩ → Σ[ m ∈ Mem (Lset β) ] ⟨ Cell x m ⟩
      atMember (y , y∈x) =
        (fst y , bound-below₂ (fst a) (snd a) (fst x) (fst y) y∈x x∈a) , y∈x

    least : (x : S) → ⟨ x ∈ˢ a ⟩ → Σ[ m ∈ Mem (Lset β) ] IsLeast W (Cell x) m
    least x x∈a = leastOf W lem (Cell x) (members x x∈a)

    Predecessor : S → S → S → Type (ℓ-suc ℓ)
    Predecessor x z w = ⟨ w ∈ˢ x ⟩
                      × ⟨ (w ∷ x ∷ z ∷ []) ⊨ appC rel zero (suc (suc zero)) ⟩

    Two : S → S → Type (ℓ-suc ℓ)
    Two x z = ⟨ x ∈ˢ a ⟩
            × (⟨ z ∈ˢ x ⟩
              × (∥ Σ[ w ∈ S ] Predecessor x z w ∥₁
                 → Lift {j = ℓ-suc ℓ} Empty.⊥))

    Out : S → Type (ℓ-suc ℓ)
    Out z = ∥ Σ[ x ∈ S ] (⟨ x ∈ˢ a ⟩ × Least x z) ∥₁

  opaque
    unfolding Pick

    pick-in : (x : S) → ⟨ x ∈ˢ a ⟩ → (z : S) → Least x z
            → ⟨ (z ∷ []) ⊨ Pick a rel ⟩
    pick-in x x∈a z (hz , (z∈x , mini)) =
      ∣ x , (x∈a , (z∈x , neg)) ∣₁
      where
      noPredecessor : Σ[ w ∈ S ] Predecessor x z w → Empty.⊥
      noPredecessor (w , (w∈x , hap)) = mini (fst w , hw) w∈x lt
        where
        hw : ⟨ fst w ∈ Lset β ⟩
        hw = bound-below₂ (fst a) (snd a) (fst x) (fst w) w∈x x∈a
        hpr : ⟨ pr (fst w) (fst z) ∈ fst rel ⟩
        hpr = subst ⟨_⟩ (appC-adequate rel zero (suc (suc zero)) (w ∷ x ∷ z ∷ [])) hap
        lt : relOf W (fst w , hw) (fst z , hz)
        lt = B.orderL-rep (fst w , hw) (fst z , hz) hpr

      neg : ∥ Σ[ w ∈ S ] Predecessor x z w ∥₁
          → Lift {j = ℓ-suc ℓ} Empty.⊥
      neg q = lift (PT.rec Empty.isProp⊥ noPredecessor q)

    pick-out : (z : S) → ⟨ (z ∷ []) ⊨ Pick a rel ⟩ → Out z
    pick-out z = PT.rec PT.squash₁ atTwo
      where
      atTwo : Σ[ x ∈ S ] Two x z → Out z
      atTwo (x , (x∈a , (z∈x , neg))) = ∣ x , (x∈a , (hz , (z∈x , mini))) ∣₁
        where
        hz : ⟨ fst z ∈ Lset β ⟩
        hz = bound-below₂ (fst a) (snd a) (fst x) (fst z) z∈x x∈a

        mini : (b : Mem (Lset β)) → ⟨ Cell x b ⟩
             → relOf W b (fst z , hz) → Empty.⊥
        mini b b∈x lt = lower (neg ∣ elt b , (b∈x , hap) ∣₁)
          where
          hpr : ⟨ pr (fst b) (fst z) ∈ fst rel ⟩
          hpr = B.orderL-fill b (fst z , hz) lt
          hap : ⟨ (elt b ∷ x ∷ z ∷ []) ⊨ appC rel zero (suc (suc zero)) ⟩
          hap = subst ⟨_⟩
            (sym (appC-adequate rel zero (suc (suc zero)) (elt b ∷ x ∷ z ∷ []))) hpr

  transversalSet : S
  transversalSet = separate (LsetS β oβ) (Pick a rel)

  private
    csp : (z : S) → (z ∈ˢ transversalSet)
                  ≡ ((z ∈ˢ LsetS β oβ) ⊓ ((z ∷ []) ⊨ Pick a rel))
    csp = separate-spec (LsetS β oβ) (Pick a rel)

    inC : (z : S) → ⟨ fst z ∈ Lset β ⟩ → ⟨ (z ∷ []) ⊨ Pick a rel ⟩
        → ⟨ z ∈ˢ transversalSet ⟩
    inC z hL hp = subst ⟨_⟩ (sym (csp z)) (hL , hp)

    outC : (z : S) → ⟨ z ∈ˢ transversalSet ⟩ → ⟨ (z ∷ []) ⊨ Pick a rel ⟩
    outC z h = snd (subst ⟨_⟩ (csp z) h)

  module Cut (x : S) (x∈a : ⟨ x ∈ˢ a ⟩) where
    private
      m : Mem (Lset β)
      m = least x x∈a .fst

      lm : IsLeast W (Cell x) m
      lm = least x x∈a .snd

      z₀ : S
      z₀ = elt m

      inMeet : (z : S) → ⟨ z ∈ˢ transversalSet ⟩ → ⟨ z ∈ˢ x ⟩
             → ⟨ z ∈ˢ (transversalSet ∩ x) ⟩
      inMeet z hc hx = subst ⟨_⟩ (sym (∩-spec transversalSet x z)) (hc , hx)

      outMeet : (z : S) → ⟨ z ∈ˢ (transversalSet ∩ x) ⟩
              → ⟨ z ∈ˢ transversalSet ⟩ × ⟨ z ∈ˢ x ⟩
      outMeet z h = subst ⟨_⟩ (∩-spec transversalSet x z) h

      centre : Σ[ z ∈ S ] ⟨ z ∈ˢ (transversalSet ∩ x) ⟩
      centre = z₀ , inMeet z₀
        (inC z₀ (snd m) (pick-in x x∈a z₀ (snd m , lm))) (fst lm)

      same : (z : S) → ⟨ z ∈ˢ (transversalSet ∩ x) ⟩ → fst z ≡ fst m
      same z h = PT.rec (setIsSet (fst z) (fst m)) atOut
                   (pick-out z (outC z (fst (outMeet z h))))
        where
        z∈x : ⟨ z ∈ˢ x ⟩
        z∈x = snd (outMeet z h)

        atOut : Σ[ x' ∈ S ] (⟨ x' ∈ˢ a ⟩ × Least x' z) → fst z ≡ fst m
        atOut (x' , (x'∈a , (hz , lz))) =
          cong (λ p → fst (fst p))
            (isPropLeastOf W (Cell x) ((fst z , hz) , lz') (m , lm))
          where
          x≡x' : x ≡ x'
          x≡x' = disj x x' x∈a x'∈a ∣ z , (z∈x , fst lz) ∣₁

          lz' : IsLeast W (Cell x) (fst z , hz)
          lz' = subst (λ y → IsLeast W (Cell y) (fst z , hz)) (sym x≡x') lz

    meetsOnce : isContr (Σ[ z ∈ S ] ⟨ z ∈ˢ (transversalSet ∩ x) ⟩)
    meetsOnce = centre , atPoint
      where
      atPoint : (p : Σ[ z ∈ S ] ⟨ z ∈ˢ (transversalSet ∩ x) ⟩) → centre ≡ p
      atPoint (z , h) = sym (Σ≡Prop
        (λ w → snd (w ∈ˢ (transversalSet ∩ x)))
        (Σ≡Prop (λ v → snd (isL v)) (same z h)))

  transversal : (x : S) → ⟨ x ∈ˢ a ⟩
              → isContr (Σ[ z ∈ S ] ⟨ z ∈ˢ (transversalSet ∩ x) ⟩)
  transversal = Cut.meetsOnce
```

<!--en-->
## The theorem

<!--zh-->
## 定理
<!--ja-->
## 選択公理
<!--/-->

<!--en-->
The final wrapper converts the transversal construction into the exact choice
field required by the ZF model record on `𝒮ʟ`.
<!--zh-->
最后的封装把横截集构造转成 `𝒮ʟ` 上 ZF 模型 record 所要求的选择字段。
<!--ja-->
最後のラッパーは横断集合の構成を、`𝒮ʟ` 上の ZF モデルの record が要求する選択フィールドへ変換する。
<!--/-->

<!--en-->

`ChoiceStatement`{.Agda} is the statement the frontier used to hold, moved here
verbatim and no longer a debt: the model's choice field at `𝒮ʟ`, relative to a
ZF model on this carrier because the intersection is that model's derived
operation. `hasChoiceL`{.Agda} proves it. The root chapter applies it to the very
model it is assembling, which is why the statement quantifies over the model in
the first place.

This line supplies the Choice field used by the root theorem. Its statement
remains relative to the ZF model being assembled because intersection is the
derived operation of that model.
<!--zh-->

`ChoiceStatement`{.Agda} 就是前沿曾经持有的那条陈述，原样移到此处，且不再是一笔债：模型的选择字段在 `𝒮ʟ` 处的样子，是相对于此载体上的一个 ZF 模型而言的，因为那个交是那个模型的派生运算。`hasChoiceL`{.Agda} 证出它。根章把它施于正在装配的那个模型自身，而这正是这条陈述一开始就要对模型作全称的原因。

这一行供应根定理所用的选择字段。它仍相对于正在装配的 ZF 模型陈述，因为交是该模型的派生运算。
<!--/-->

```agda
ChoiceStatement : isZFModel → Type (ℓ-suc ℓ)
ChoiceStatement zf =
  (a : S)
  → ((x : S) → ⟨ x ∈ˢ a ⟩ → ∥ Σ[ y ∈ S ] ⟨ y ∈ˢ x ⟩ ∥₁)
  → ((x y : S) → ⟨ x ∈ˢ a ⟩ → ⟨ y ∈ˢ a ⟩
       → ∥ Σ[ z ∈ S ] (⟨ z ∈ˢ x ⟩ × ⟨ z ∈ˢ y ⟩) ∥₁ → x ≡ y)
  → ∥ Σ[ c ∈ S ] ((x : S) → ⟨ x ∈ˢ a ⟩
       → isContr (Σ[ z ∈ S ] ⟨ z ∈ˢ (c ∩ x) ⟩)) ∥₁
  where open ModelL.isZFModel zf using ( _∩_ )

hasChoiceL : (zf : isZFModel) → ChoiceStatement zf
hasChoiceL zf a inh disj = ∣ T.transversalSet , T.transversal ∣₁
  where module T = Trans zf a inh disj
```

<!--en-->
## Recap
<!--zh-->
## 小结
<!--ja-->
## まとめ
<!--/-->

<!--en-->
`Pick`{.Agda}, the bounded stage order, and separation together produce the
transversal whose exact-one-point property supplies `hasChoiceL`{.Agda}.
<!--zh-->
`Pick`{.Agda}、循阶的阶段序与分离共同产出横截集，其恰交于一点的性质供应 `hasChoiceL`{.Agda}。
<!--ja-->
`Pick`{.Agda}、段階有界な順序、分出公理から横断集合が得られ、その各セルと一点だけで交わる性質が `hasChoiceL`{.Agda} を与える。
<!--/-->

<!--en-->
`Pick`{.Agda} is the description: some member of the family contains this set,
and nothing in that member precedes it. `pick-in`{.Agda} and `pick-out`{.Agda}
are its two readings against being a least element of a member.
`transversalSet`{.Agda} is what the model's separation cuts out with it, over the
tower at the family's bounding ordinal, and `transversal`{.Agda} counts the
intersection with each member: one point, existence from the least-element
search and uniqueness from pairwise disjointness. `hasChoiceL`{.Agda} is the
model's choice field, and with it the frontier is empty and gone.

One measurement, and it is a law declining to bite. A description read at
constants is sealed where it is built, and that law was worth ninety-nine fold
where it was found; here it is worth nothing, 2.3 s either way, because this
description carries no coded syntax. The seal stays, and the number is recorded
so that the law keeps its true shape: it is about what a description **contains**,
not about where it is read.
<!--zh-->
`Pick`{.Agda} 是那条描述：该族的某个成员含有这个集合，且那个成员中没有任何东西排在它之前。`pick-in`{.Agda} 与 `pick-out`{.Agda} 是它对着「是某个成员的极小元」的两条读式。`transversalSet`{.Agda} 是模型的分离据它而在该族的上界序数处的塔之上雕出的东西，而 `transversal`{.Agda} 数清它与每个成员之交：恰一点，存在性来自那场极小元搜索，唯一性来自两两不交。`hasChoiceL`{.Agda} 就是模型的选择字段，有了它，前沿即告清空并被删除。

一次实测，且是一条定律偏偏没有咬人。读在常元上的描述要在被造出之处封印，而这条定律在被发现之处值九十九倍；在此处它一文不值，封印与否都是 2.3 秒，因为这条描述不携带任何已编码的语法。封印仍然保留，而那个数字仍被记下来，好让这条定律保持它真正的形状：它关乎一条描述**装着什么**，而不关乎它被读在哪里。
<!--/-->

<!--en-->
## What the book was for
<!--zh-->
## 本书是为了什么
<!--ja-->
## 本書が目指したもの
<!--/-->

<!--en-->
The completed Choice chain supplies the missing model field, so under the single
stated excluded-middle hypothesis the constructible universe satisfies ZFC.
<!--zh-->
完成的 Choice 构造链供应最后缺少的模型字段，故在唯一明示的排中律假设下，可构造宇宙满足 ZFC。
<!--ja-->
完成した Choice の構成列が最後のモデル・フィールドを与えるので、明示された唯一の排中律の仮定の下で構成可能宇宙は ZFC を満たす。
<!--/-->

<!--en-->
This is the end of the chain, so it is worth saying plainly what stands. **In
cubical Agda, granted one instance of the excluded middle at the model's own
truth level, the constructible universe is a model of ZFC.** Read with the
ambient-hierarchy result that the hierarchy models ZF, that is Gödel's relative consistency of
choice in semantic form: a universe satisfying ZF contains inside it a
sub-universe satisfying ZFC, so an inconsistency of ZFC would already be an
inconsistency of ZF.

Every price is printed on the label. The host is cubical Agda with its universe
tower, informally about as strong as ZFC plus an inaccessible; excluded middle
is a module parameter rather than an axiom, and it is the only hypothesis the
theorem carries; and the development has no postulates or holes. This chapter
supplies the Choice field that `L.Model`{.Agda} combines with the earlier ZF
structure.
<!--zh-->
这是 Choice 构造链的终点，故值得把立住的东西平白说一遍。**在 cubical Agda 之内，给定模型自身真值层级上的一份排中律，可构造宇宙是 ZFC 的模型。**与环境层级满足 ZF 的结果合读，这就是哥德尔的选择公理相对一致性的语义形式：满足 ZF 的宇宙内部含有一个满足 ZFC 的子宇宙，故 ZFC 的任何矛盾都早已是 ZF 的矛盾。

每一分价格都印在标签上。宿主是带宇宙塔的 cubical Agda，其强度非形式地约当于 ZFC 加一个不可达基数；排中律是模块参数而非公理，且是这条定理携带的唯一假设；本开发中处处没有公设、没有洞。本章交付选择公理字段，`L.Model`{.Agda} 再把它与此前的 ZF 结构装配起来。
<!--/-->
