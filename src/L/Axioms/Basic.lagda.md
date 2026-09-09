<!--en-->
# The basic axioms
<!--zh-->
# 基本公理
<!--ja-->
# 基本公理
<!--/-->

<!--en-->
This chapter proves extensionality, regularity, empty set, pairing, and union for
the constructible universe, using transitivity for inherited laws and definable
subsets of one stage for the constructed sets.
<!--zh-->
本章证明可构造宇宙的外延公理、正则公理、空集公理、配对公理与并公理：传递性给出继承来的定律，而单一阶段的可定义子集给出所构造的集合。
<!--ja-->
本章では構成可能宇宙について、外延性公理、正則性公理、空集合の公理、対の公理、和集合の公理を証明する。継承される法則には推移性を、構成する集合には一つの段階の定義可能部分集合を用いる。
<!--/-->

<!--en-->
The frontier opened with eleven debts. This chapter pays the first five, and
they are the five that ask least: extensionality, regularity, the empty set,
pairing, and union. Two of them descend from the ambient hierarchy for free,
because `L` is a transitive sub-universe and those axioms survive restriction to
any transitive class. The other three are genuine constructions, and all three
run the same argument.

That argument is worth naming before it appears three times. To place a set in
`L` one must exhibit it as a definable subset of a single stage. So a closure
proof has three moves: find one stage holding all the ingredients, write a
formula that carves the target out of that stage, and check that the formula's
extension is exactly the target. The first move is the bounding ordinal of the
previous chapter, the second is the definability operator two chapters back, and
the third is one application of extensionality in the ambient hierarchy. Union
needs no search at all, since one stage already holds its single argument;
pairing needs the bound; the empty set needs neither, and could be carved out of
any stage whatsoever.

Nothing here is classical. A reader who knows the textbook proof may expect the
stages of two constructible sets to be *compared*, one of them shown to be the
larger. Comparison is exactly what a bound makes unnecessary.
<!--zh-->
前沿开出十一笔债。本章偿还头五笔，也是要求最低的五笔：外延、正则、空集、配对与并。其中两笔从环境层级免费下降，因为 `L` 是传递的子宇宙，而这两条公理在限制到任何传递类之后仍然成立。另外三笔是货真价实的构造，而三者跑的是同一套论证。

那套论证值得在它出现三次之前先行命名。要把一个集合放进 `L`，必须把它呈现为**单一阶段**的可定义子集。于是闭包证明有三步：找一个装得下全部材料的阶段，写一条从该阶段中刻出目标的公式，再验证公式的外延恰是目标。第一步是上一章的上界序数，第二步是前两章的可定义性算子，第三步是环境层级中的一次外延性应用。并根本不需要搜索，因为已有一个阶段装着它唯一的实参；配对需要那个上界；空集两者皆不需要，从任何阶段里都刻得出来。

此处没有任何经典逻辑。熟悉教科书证明的读者也许预期要**比较**两个可构造集的阶段，指认其中较大的那个。上界所免除的，恰恰就是比较。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth

module L.Axioms.Basic {ℓ : Level} where

open import FOL.Syntax using ( Formula; var; con; _≐_; _∈̇_; _∨̇_; ⊤̇; ⊥̇; ∃̇∈ )
open import FOL.ZFStructure using ( ↾-reflects; module hPropStructure )
import FOL.ZFModel
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ; extensionalV; regularityV )
open import V.Model {ℓ}
  using ( empty-spec; pair-spec; union-spec; self∈sucV; ∈sucV-elim
        ; pair-singleton )
open import V.Coding {ℓ} using ( pr )
open import L.Definability {ℓ} using ( module DefOf )
open import L.Constructible {ℓ}
  using ( 𝒮ʟ; isL; isL-trans; IsOrd; Lset; Lset-layer
        ; layer-trans; 𝒟ₒ; 𝒟ₒ-intro; Lset-in; Lset-out; Lset⊆𝒟ₒ
        ; Lset-mono; Lset→isL )
open import L.Ordinal {ℓ} using ( ∅-ord; suc-ord; bound2 )

open import Cubical.Data.FinData using ( zero; suc )
open import Cubical.Data.Sum using ( inl; inr )
open import Cubical.Functions.Logic using ( ⇔toPath )
open import Cubical.Foundations.Prelude using ( isPropIsContr )
open import Cubical.Induction.WellFounded using ( Acc; acc; WellFounded )
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁; squash₁ )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_; sett )
open import Cubical.HITs.CumulativeHierarchy.Properties
  using ( _∈ₛ_; ∈∈ₛ; ∈-asFiber; extensionality; _⊆_; ⟪_⟫; ⟪_⟫↪ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ∅; ∅-empty; ⁅_,_⁆; ⁅_⁆s; pairing-ax; ⋃_; union-ax
        ; module InfinitySet )
open InfinitySet using ( sucV )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ

module ModelL = FOL.ZFModel 𝒮ʟ
open ModelL using ( SetOf; setOf-unique )
```

<!--en-->
## Definable subsets are constructible
<!--zh-->
## 可定义子集是可构造的
<!--ja-->
## 定義可能部分集合は構成可能である
<!--/-->

<!--en-->
`defInL`{.Agda} places every definable subset of an ordinal stage into the next
constructible level, and `isL-Lset`{.Agda} records that each ordinal stage itself
belongs to `L`.
<!--zh-->
`defInL`{.Agda} 把序数阶段的每个可定义子集放入下一可构造层，而 `isL-Lset`{.Agda} 记录每个序数阶段自身都属于 `L`。
<!--ja-->
`defInL`{.Agda} は順序数段階の各定義可能部分集合を次の構成可能な層へ入れ、`isL-Lset`{.Agda} は各順序数段階そのものが `L` に属することを記録する。
<!--/-->

<!--en-->
The closing step of every construction below is the same: a definable subset of a stage is
itself constructible. The stage `Lset σ` sits one level down in the tower from
`Lset (sucV σ)`, whose defining union runs over the members of `sucV σ`; and `σ`
is one of those members. So the operator applied to `Lset σ` is one member of
that union, and everything inside it belongs to the next stage, which is a stage
because successors of ordinals are ordinals.
<!--zh-->
下文每个构造的最后一步都相同：阶段的可定义子集自身可构造。`Lset σ` 在塔中比 `Lset (sucV σ)` 低一级，而后者定义中的并遍取 `sucV σ` 的成员；`σ` 正是其中一个成员。因此，算子作用于 `Lset σ` 所得是该并的一个成员，其中的每个对象都属于下一阶段；序数的后继仍是序数，所以后者确实是一个阶段。
<!--/-->

```agda
𝒟ₒ→isL : (σ : V ℓ) → IsOrd σ → (x : V ℓ) → ⟨ x ∈ 𝒟ₒ (Lset σ) ⟩ → ⟨ isL x ⟩
𝒟ₒ→isL σ oσ x x∈𝒟ₒσ = Lset→isL (sucV σ) (suc-ord oσ) x
  (Lset-in (sucV σ) σ x (self∈sucV σ) x∈𝒟ₒσ)
```

<!--en-->
Composing that with the recognition principle for the operator gives the form
every later construction actually uses, and it deserves a name of its own: to
put a set in `L`, exhibit a stage, a formula, and an extensional equation saying
the formula defines exactly that set. Nothing else is ever required, and the
three constructions below are its first three instances.
<!--zh-->
把它与算子的识别原则复合，就得到日后每个构造实际使用的形式，值得单独命名：要把一个集合放进 `L`，需要一个阶段、一条公式，以及一条说明该公式的外延恰为该集合的等式。此外别无要求，而下面三个构造正是它的头三个实例。
<!--/-->

```agda
defSet→isL : (σ : V ℓ) → IsOrd σ → (x : V ℓ)
           → ∥ Σ[ φ ∈ Formula ⟪ Lset σ ⟫ 1 ] (DefOf.defSet (Lset σ) φ ≡ x) ∥₁
           → ⟨ isL x ⟩
defSet→isL σ oσ x p = 𝒟ₒ→isL σ oσ x (𝒟ₒ-intro (Lset σ) x p)
```

<!--en-->
The zeroth instance is the stage itself. The formula "true" defines the whole of
a set, so a stage is a definable subset of itself, and constructible one stage
later. It is what lets a stage be *named* by a formula, which every later chapter
that bounds quantifiers by a stage needs.

The certificate is sealed, and only the certificate. The pairing has to keep reducing, since
"lies in this bound" and "lies in this stage" are the same statement only because
it does; but the certificate unfolds through definability into the smallness
machinery, and it is carried by every type that mentions the constant. A chapter
that separates with a formula relativized to a stage takes minutes rather than
seconds without this one line.
<!--zh-->
第零个实例是阶段自身。公式「真」定义出一个集合的全体，故阶段是它自身的可定义子集，而在下一阶段可构造。正是这一点使阶段可以被一条公式**点名**，而此后每个用阶段界住量词的章节都需要它。

被固定下来的只是那份证书，且仅是证书本身。配对仍须继续规约，因为「落在这个界内」与「落在这个阶段内」是同一句话，而这正依赖于它的规约；证书则经可定义性一路展开到小性机器，并且出现在一个常元中，每个提到该常元的类型都要携带它。一章若用相对化到某阶段的公式作分离，缺少这一行，证明耗时便以分钟计而非以秒计。
<!--/-->

```agda
opaque
  isL-Lset : (β : V ℓ) → IsOrd β → ⟨ isL (Lset β) ⟩
  isL-Lset β oβ = 𝒟ₒ→isL β oβ (Lset β)
    (𝒟ₒ-intro (Lset β) (Lset β) ∣ ⊤̇ , DefOf.defSet⊤≡A (Lset β) ∣₁)

LsetS : (β : V ℓ) → IsOrd β → S
LsetS β oβ = Lset β , isL-Lset β oβ
```

<!--en-->
## The successor stage
<!--zh-->
## 后继阶段
<!--ja-->
## 後者段階
<!--/-->

<!--en-->
`Lset-suc`{.Agda} proves that the stage at a successor ordinal is exactly the
definable powerset of the preceding stage, by establishing both inclusions.
<!--zh-->
`Lset-suc`{.Agda} 通过证明两个包含方向，表明后继序数处的阶段恰为前一阶段的可定义幂集。
<!--ja-->
`Lset-suc`{.Agda} は二つの包含を証明し、後者順序数における段階が直前の段階の定義可能冪集合とちょうど一致することを示す。
<!--/-->

<!--en-->
The tower's step is the definable powerset, and at a successor index the step is
all there is: `Lset (sucV σ)` is `𝒟ₒ (Lset σ)` exactly. Both inclusions read off
the stage characterization and use nothing else. For one, `σ` is a member of its
own successor, so the operator applied to `Lset σ` is one member of the union
that the next stage is. For the other, a member of `Lset (sucV σ)` lies in
`𝒟ₒ (Lset δ)` for some `δ` in `sucV σ`; either `δ` is a member of `σ`, and then
the set is already in `Lset σ` and so among its definable subsets, or `δ` is `σ`
and the inclusion is immediate. Neither half relativizes anything, and neither needs
the operator to be monotone. Ordinality is not needed either, and is carried only
so that the three statements of this section take the same arguments.
<!--zh-->
塔的步进是可定义幂集；在后继索引处，`Lset (sucV σ)` 恰是 `𝒟ₒ (Lset σ)`。两个包含方向都可由阶段刻画直接得到。其一，`σ` 属于自身的后继，所以算子作用于 `Lset σ` 所得是下一阶段定义中那个并的成员。其二，`Lset (sucV σ)` 的成员属于某个 `δ ∈ sucV σ` 对应的 `𝒟ₒ (Lset δ)`；若 `δ` 是 `σ` 的成员，该集合已在 `Lset σ` 中，因而是它的可定义子集；若 `δ` 就是 `σ`，结论直接成立。两种情形都不使用相对化或算子单调性。这里也不需要序数性；保留该假设只是为了让本节三条陈述使用相同形式的参数。
<!--/-->

The identity asks nothing of `σ`{.Agda}. It was stated with an ordinality
hypothesis and the hypothesis turned out to be dead: neither inclusion touches
it, because the one that could have is carried by transitivity of a stage, which
is ordinal-free. The two statements below do need it, through the successor of an
ordinal being one.

<!--zh-->
这条恒等式对 `σ`{.Agda} 没有任何要求。它当初带着一条序数性假设被陈述出来，而那条假设结果是多余的：两个包含关系都不用到它，因为本可能用到它的那一步由「阶段的传递性」承担，而后者与序数无关。下面那两条陈述则确实需要它，经由「序数的后继是序数」。
<!--/-->

```agda
Lset-suc : (σ : V ℓ) → Lset (sucV σ) ≡ 𝒟ₒ (Lset σ)
Lset-suc σ = extensionality (Lset (sucV σ)) (𝒟ₒ (Lset σ)) (sub₁ , sub₂)
  where
  fromEarlier : (x : V ℓ)
              → Σ[ δ ∈ V ℓ ] (⟨ δ ∈ sucV σ ⟩ × ⟨ x ∈ 𝒟ₒ (Lset δ) ⟩)
              → ⟨ x ∈ 𝒟ₒ (Lset σ) ⟩
  fromEarlier x (δ , (δ∈suc , x∈𝒟ₒδ)) =
    ∈sucV-elim {A = σ} {x = δ} (snd (x ∈ 𝒟ₒ (Lset σ))) δ∈suc
      (λ δ∈σ → Lset⊆𝒟ₒ σ x (Lset-in σ δ x δ∈σ x∈𝒟ₒδ))
      (λ δ≡σ → subst (λ w → ⟨ x ∈ 𝒟ₒ (Lset w) ⟩) δ≡σ x∈𝒟ₒδ)

  sub₁ : ⟨ Lset (sucV σ) ⊆ 𝒟ₒ (Lset σ) ⟩
  sub₁ x x∈ₛ = ∈∈ₛ {a = x} {b = 𝒟ₒ (Lset σ)} .fst
    (PT.rec (snd (x ∈ 𝒟ₒ (Lset σ))) (fromEarlier x)
      (Lset-out (sucV σ) x (∈∈ₛ {a = x} {b = Lset (sucV σ)} .snd x∈ₛ)))

  sub₂ : ⟨ 𝒟ₒ (Lset σ) ⊆ Lset (sucV σ) ⟩
  sub₂ x x∈ₛ = ∈∈ₛ {a = x} {b = Lset (sucV σ)} .fst
    (Lset-in (sucV σ) σ x (self∈sucV σ)
      (∈∈ₛ {a = x} {b = 𝒟ₒ (Lset σ)} .snd x∈ₛ))
```

<!--en-->
The identity turns a fact about the tower into a fact about the operator. A stage
is constructible one stage later, so the definable powerset of a stage is
constructible outright, and it packages as a set of `L`. Its certificate is
sealed exactly as the stage's was, and for the same reason: it is carried
as part of the definition of a constant.
<!--zh-->
这条等式把关于塔的事实转成关于算子的事实。阶段在下一阶段可构造，故阶段的可定义幂集本身就可构造，并打包成 `L` 的一个集合。它的可构造性证书与阶段的证书一样，在定义处保持不透明；理由也相同：该证书会作为常元定义的一部分被携带。
<!--/-->

```agda
opaque
  isL-𝒟ₒ : (σ : V ℓ) → IsOrd σ → ⟨ isL (𝒟ₒ (Lset σ)) ⟩
  isL-𝒟ₒ σ oσ = subst (λ w → ⟨ isL w ⟩) (Lset-suc σ)
    (isL-Lset (sucV σ) (suc-ord oσ))

𝒟ₒS : (σ : V ℓ) → IsOrd σ → S
𝒟ₒS σ oσ = 𝒟ₒ (Lset σ) , isL-𝒟ₒ σ oσ
```

<!--en-->
That packaging is what a later chapter needs. A description of the definable
powerset written at a carrier that is a bound *variable* is adequate only where
that carrier's definable subsets are constructible, because the description
quantifies over `L` and can name only what lives there. At a variable carrier
that is a side condition carried along with every use of the description. At a stage
it is discharged for good: the definable subsets of a stage are constructible by
`𝒟ₒ→isL`{.Agda} above, and the set of them is `𝒟ₒS`{.Agda}. The successor
identity is what makes both hold, at every stage at once.
<!--zh-->
这份打包正是后续章节需要的材料。若把可定义幂集的描述写在一个作为**约束变元**的载体上，那么只有当该载体的可定义子集都可构造时，描述才足够，因为它对 `L` 量化，只能涉及其中的元素。在变元载体上，这是每次使用描述时都要携带的条件；在阶段上，该条件一次得到证明便可反复使用：阶段的可定义子集经 `𝒟ₒ→isL`{.Agda} 可构造，而它们组成的集合是 `𝒟ₒS`{.Agda}。后继等式使这两点在每个阶段同时成立。
<!--/-->

<!--en-->
## Finite families
<!--zh-->
## 有穷族
<!--ja-->
## 有限族
<!--/-->

<!--en-->
The finite-disjunction formula shows that any finite indexed family of members
of one stage forms a constructible set, with exact membership lemmas
`finSet-in`{.Agda} and `finSet-out`{.Agda}.
<!--zh-->
有穷析取公式证明：由同一阶段成员组成的任意有穷索引族都形成一个可构造集合，并给出精确的 `finSet-in`{.Agda} 与 `finSet-out`{.Agda} 成员引理。
<!--ja-->
有限論理和の論理式により、一つの段階の要素からなる任意の有限添字族が構成可能集合をなすことを示し、正確な所属補題 `finSet-in`{.Agda} と `finSet-out`{.Agda} を得る。
<!--/-->

<!--en-->
The first instance is general, and it is the one later chapters use most: any
finite family of members of a stage is a set of `L`. The formula is the finite
disjunction of "equals this one", built by recursion on the length with falsity
at zero, and the family's members are named as constants because they are members
of the stage.

Membership in the carved set and being hit by the family are the same statement,
and the induction proving so is the whole content. The construction subsumes
pairing, which is its two-element case, and it is what puts a recursion's table
of values at a single stage: a finite table drawn from a stage is a set of `L`
without any further argument.

The identification of the carved set with the family (`defSet≡`{.Agda}) is stated
in its own right, and with it the reading a later chapter actually consumes: a
finite family drawn from a stage spans a **definable subset** of that stage, and
so a member of the stage above it (`finSet∈𝒟ₒ`{.Agda}). Read from the other side,
that is the statement that a stage with finitely many members has no subsets
beyond the definable ones.
<!--zh-->
第一个实例是通用的，也是后续诸章用得最多的：阶段的任何有穷成员族都是 `L` 的一个集合。所用的公式是「等于这一个」的有穷析取，沿长度递归构造，在零处取假；族的诸成员则以常元命名，因为它们是该阶段的成员。

属于所定义的集合与被该族命中是同一回事，证明这一点的那次归纳就是全部内容。这个构造涵盖配对：配对是它的二元情形。它也说明，递归的取值表安置在单一阶段上时，取自某阶段的有穷表无须进一步论证就是 `L` 的集合。

所定义的集合与那个族的等同 (`defSet≡`{.Agda}) 单独陈述，并同时给出后续某章实际使用的那种读法：取自某阶段的有穷族张成该阶段的一个**可定义子集**，从而是它上面那个阶段的成员 (`finSet∈𝒟ₒ`{.Agda})。从另一侧读，这句话说的是：只有有穷多个成员的阶段，除可定义子集之外再无别的子集。
<!--/-->

```agda
finSet : (n : ℕ) → (Fin n → V ℓ) → V ℓ
finSet n h = sett (Lift {ℓ-zero} {ℓ} (Fin n)) (λ i → h (lower i))

finSet-in : (n : ℕ) (h : Fin n → V ℓ) (y : V ℓ)
          → ∥ Σ[ i ∈ Fin n ] (h i ≡ y) ∥₁ → ⟨ y ∈ finSet n h ⟩
finSet-in n h y = PT.map (λ { (i , q) → lift i , q })

finSet-out : (n : ℕ) (h : Fin n → V ℓ) (y : V ℓ)
           → ⟨ y ∈ finSet n h ⟩ → ∥ Σ[ i ∈ Fin n ] (h i ≡ y) ∥₁
finSet-out n h y = PT.map (λ { (i , q) → lower i , q })

module FinOf (σ : V ℓ) (oσ : IsOrd σ) where
  module DefC = DefOf (Lset σ)

  finDisj : (n : ℕ) → (Fin n → ⟪ Lset σ ⟫) → Formula ⟪ Lset σ ⟫ 1
  finDisj zero    g = ⊥̇
  finDisj (suc n) g =
    (var zero ≐ con (g zero)) ∨̇ finDisj n (λ i → g (suc i))

  private
    Hits : (n : ℕ) (g : Fin n → ⟪ Lset σ ⟫) (y : V ℓ) → Type (ℓ-suc ℓ)
    Hits n g y = ∥ Σ[ i ∈ Fin n ] (⟪ Lset σ ⟫↪ (g i) ≡ y) ∥₁

    sat→hits : (n : ℕ) (g : Fin n → ⟪ Lset σ ⟫) (m : ⟪ Lset σ ⟫)
             → ⟨ (DefC.ι m ∷ []) DefC.⊨ᵐ finDisj n g ⟩
             → Hits n g (⟪ Lset σ ⟫↪ m)
    sat→hits zero    g m bot = Empty.rec* bot
    sat→hits (suc n) g m = PT.rec squash₁
      (λ { (inl e)  → ∣ zero , sym e ∣₁
         ; (inr sat) → PT.map (λ { (i , q) → suc i , q })
                         (sat→hits n (λ i → g (suc i)) m sat) })

    hits→sat : (n : ℕ) (g : Fin n → ⟪ Lset σ ⟫) (m : ⟪ Lset σ ⟫)
             → Hits n g (⟪ Lset σ ⟫↪ m)
             → ⟨ (DefC.ι m ∷ []) DefC.⊨ᵐ finDisj n g ⟩
    hits→sat zero g m =
      PT.rec (snd ((DefC.ι m ∷ []) DefC.⊨ᵐ finDisj zero g)) (λ { (() , _) })
    hits→sat (suc n) g m =
      PT.rec (snd ((DefC.ι m ∷ []) DefC.⊨ᵐ finDisj (suc n) g))
        (λ { (zero  , q) → ∣ inl (sym q) ∣₁
           ; (suc i , q) →
             ∣ inr (hits→sat n (λ j → g (suc j)) m ∣ i , q ∣₁) ∣₁ })

  defSet≡ : (n : ℕ) (g : Fin n → ⟪ Lset σ ⟫)
          → DefC.defSet (finDisj n g) ≡ finSet n (λ i → ⟪ Lset σ ⟫↪ (g i))
  defSet≡ n g = extensionality _ _ (sub₁ , sub₂)
    where
    F = finSet n (λ i → ⟪ Lset σ ⟫↪ (g i))
    sub₁ : ⟨ DefC.defSet (finDisj n g) ⊆ F ⟩
    sub₁ y y∈ₛ = ∈∈ₛ {a = y} {b = F} .fst (PT.rec (snd (y ∈ F))
      (λ { ((m , h) , q) →
        subst (λ v → ⟨ v ∈ F ⟩) q
          (finSet-in n (λ i → ⟪ Lset σ ⟫↪ (g i)) (⟪ Lset σ ⟫↪ m)
            (sat→hits n g m
              (subst ⟨_⟩ (DefC.defSet-mem (finDisj n g) m)
                ∣ (m , h) , refl ∣₁))) })
      (∈∈ₛ {a = y} {b = DefC.defSet (finDisj n g)} .snd y∈ₛ))
    sub₂ : ⟨ F ⊆ DefC.defSet (finDisj n g) ⟩
    sub₂ y y∈ₛ = PT.rec (snd (y ∈ₛ DefC.defSet (finDisj n g)))
      (λ { (i , q) →
        subst (λ v → ⟨ v ∈ₛ DefC.defSet (finDisj n g) ⟩) q
          (∈∈ₛ {a = ⟪ Lset σ ⟫↪ (g i)} {b = DefC.defSet (finDisj n g)} .fst
            (subst ⟨_⟩ (sym (DefC.defSet-mem (finDisj n g) (g i)))
              (hits→sat n g (g i) ∣ i , refl ∣₁))) })
      (finSet-out n (λ i → ⟪ Lset σ ⟫↪ (g i)) y
        (∈∈ₛ {a = y} {b = F} .snd y∈ₛ))

  finSet∈𝒟ₒ : (n : ℕ) (g : Fin n → ⟪ Lset σ ⟫)
            → ⟨ finSet n (λ i → ⟪ Lset σ ⟫↪ (g i)) ∈ 𝒟ₒ (Lset σ) ⟩
  finSet∈𝒟ₒ n g = 𝒟ₒ-intro (Lset σ) _ ∣ finDisj n g , defSet≡ n g ∣₁

  finSetL : (n : ℕ) (h : Fin n → V ℓ) → ((i : Fin n) → ⟨ h i ∈ Lset σ ⟩)
          → ⟨ isL (finSet n h) ⟩
  finSetL n h hσ = defSet→isL σ oσ (finSet n h)
    ∣ finDisj n g , (defSet≡ n g ∙ cong (finSet n) (funExt qg)) ∣₁
    where
    g : Fin n → ⟪ Lset σ ⟫
    g i = ∈-asFiber {a = h i} {b = Lset σ} (hσ i) .fst
    qg : (i : Fin n) → ⟪ Lset σ ⟫↪ (g i) ≡ h i
    qg i = ∈-asFiber {a = h i} {b = Lset σ} (hσ i) .snd
```

<!--en-->
## Two sets, one stage
<!--zh-->
## 两个集合，一个阶段
<!--ja-->
## 二つの集合を一つの段階へ
<!--/-->

<!--en-->
`isL-directed`{.Agda} uses an ordinal bound to place any two constructible sets
in one common stage, preparing the finite-family construction for pairing.
<!--zh-->
`isL-directed`{.Agda} 用序数上界把任意两个可构造集合放进同一公共阶段，为以有穷族构造配对作准备。
<!--ja-->
`isL-directed`{.Agda} は順序数の上界を用いて任意の二つの構成可能集合を一つの共通段階へ入れ、有限族による対の構成を準備する。
<!--/-->

<!--en-->
Pairing needs both of its arguments visible at the same stage. Each is
constructible, so each has a stage of its own; the bounding ordinal of the
previous chapter turns those two ordinals into one that contains both, and
monotonicity carries both sets up into its stage. The two-element family is the
lifted booleans, since the bound is stated for families indexed at the level of
the hierarchy.
<!--zh-->
配对需要它的两个实参在同一阶段上可见。二者各自可构造，故各有自己的阶段；上一章的上界序数把那两个序数并成一个同时包含二者的序数，而单调性把两个集合一并抬进它的阶段。两元族取提升后的布尔值，因为那条上界是对层级那一级的索引族陈述的。
<!--/-->

```agda
isL-directed : (x y : V ℓ) → ⟨ isL x ⟩ → ⟨ isL y ⟩
             → ∥ Σ[ σ ∈ V ℓ ] (IsOrd σ × (⟨ x ∈ Lset σ ⟩ × ⟨ y ∈ Lset σ ⟩)) ∥₁
isL-directed x y px py = PT.rec2 squash₁ go px py
  where
  Bound : Type (ℓ-suc ℓ)
  Bound = Σ[ σ ∈ V ℓ ] (IsOrd σ × (⟨ x ∈ Lset σ ⟩ × ⟨ y ∈ Lset σ ⟩))
  go : Σ[ α ∈ V ℓ ] (IsOrd α × ⟨ x ∈ Lset α ⟩)
     → Σ[ β ∈ V ℓ ] (IsOrd β × ⟨ y ∈ Lset β ⟩) → ∥ Bound ∥₁
  go (α , (oα , x∈Lα)) (β , (oβ , y∈Lβ)) =
    ∣ bnd .fst , (bnd .snd .fst , ( Lset-mono (bnd .snd .snd .fst) x∈Lα
                                  , Lset-mono (bnd .snd .snd .snd) y∈Lβ )) ∣₁
    where bnd = bound2 α β oα oβ
```

<!--en-->
## The two inherited axioms
<!--zh-->
## 继承来的两条公理
<!--ja-->
## 継承される二つの公理
<!--/-->

<!--en-->
Transitivity of `L` restricts the ambient hierarchy's extensionality and
well-founded membership to proofs of the axiom of extensionality and regularity
inside the constructible carrier.
<!--zh-->
`L` 的传递性把环境层级的外延性与良基隶属限制到可构造载体内，从而证明外延公理与正则公理。
<!--ja-->
`L` の推移性により、周囲の階層の外延性と整礎な所属を構成可能な台へ制限し、その内部で外延性公理と正則性公理を証明する。
<!--/-->

<!--en-->
Extensionality and regularity are not constructions at all: they descend from
the ambient hierarchy to any transitive sub-universe. For extensionality, two
constructible sets with the same constructible members have the same members
outright, because every member is itself constructible by transitivity; the
hierarchy's extensionality equates the underlying sets, and the restriction
reflects the path back. Regularity restricts even more easily: membership in the
sub-universe *is* membership in the hierarchy, so accessibility transfers along
the underlying set, member by member.
<!--zh-->
外延与正则根本不是构造：它们从环境层级下降到任何传递的子宇宙。看外延：两个可构造集若可构造成员相同，则成员干脆全同，因为每个成员经传递性自身可构造；层级的外延性等同底层集合，限制再把路径反射回来。正则的下降更省事：子宇宙里的成员关系**就是**层级里的成员关系，可及性沿底层集合逐成员转移。
<!--/-->

```agda
extensionalL : {a b : S} → ((x : S) → (x ∈ˢ a) ≡ (x ∈ˢ b)) → a ≡ b
extensionalL {a} {b} h =
  ↾-reflects {𝒮 = 𝒮ᵥ} {M = isL} (extensionalV {a = fst a} {b = fst b} vwise)
  where
  vwise : (v : V ℓ) → (v ∈ fst a) ≡ (v ∈ fst b)
  vwise v = ⇔toPath fwd bwd
    where
    fwd : ⟨ v ∈ fst a ⟩ → ⟨ v ∈ fst b ⟩
    fwd v∈a = subst ⟨_⟩ (h (v , isL-trans v∈a (a .snd))) v∈a
    bwd : ⟨ v ∈ fst b ⟩ → ⟨ v ∈ fst a ⟩
    bwd v∈b = subst ⟨_⟩ (sym (h (v , isL-trans v∈b (b .snd)))) v∈b

regularityL : WellFounded _∈ᵗ_
regularityL (v , p) = accL v (regularityV v) p
  where
  module Vmem = hPropStructure 𝒮ᵥ
  accL : (u : V ℓ) → Acc Vmem._∈ᵗ_ u → (q : u ∈ᶜ isL) → Acc _∈ᵗ_ (u , q)
  accL u (acc rec) q = acc (λ { (y , r) y∈ → accL y (rec y y∈) r })
```

<!--en-->
## Uniqueness, for free
<!--zh-->
## 唯一性，白拿
<!--ja-->
## 外延性から得られる一意性
<!--/-->

<!--en-->
`uniqueL`{.Agda} uses extensionality to show that any set realizing a fixed
membership predicate is unique, so later axiom fields need only construct a
merely existing witness.
<!--zh-->
`uniqueL`{.Agda} 用外延性证明，实现固定成员谓词的集合是唯一的，故后续公理字段只须构造一个「仅仅存在」层面的见证。
<!--ja-->
`uniqueL`{.Agda} は外延性により、固定された所属述語を実現する集合が一意であることを示すため、後の公理フィールドでは命題的切り詰められた存在の証人を構成するだけでよい。
<!--/-->

<!--en-->
Every existence field of the model record demands *unique* existence, and
extensionality has just made uniqueness automatic: a set realising a given
membership condition is determined by that condition. So each construction below
need only produce a witness, and it suffices to produce it merely, since being
the unique such set is a proposition.
<!--zh-->
模型 record 的每个存在字段要求的都是**唯一**存在，而外延性恰好使唯一性自动成立：实现给定隶属条件的集合由该条件决定。于是下文每个构造只须给出一个见证，且给出「仅仅存在」的证明即可，因为「是那个唯一的集合」本身是命题。
<!--/-->

```agda
uniqueL : (Q : S → Ω) → SetOf Q → isContr (SetOf Q)
uniqueL = setOf-unique extensionalL

mere→uniqueL : (Q : S → Ω) → ∥ SetOf Q ∥₁ → isContr (SetOf Q)
mere→uniqueL Q = PT.rec isPropIsContr (uniqueL Q)
```

<!--en-->
## The empty set
<!--zh-->
## 空集
<!--ja-->
## 空集合
<!--/-->

<!--en-->
The false object-language formula carves the ambient empty set as a definable
subset, and `hasEmptyL`{.Agda} packages its constructibility and empty-membership
specification.
<!--zh-->
对象语言中的假公式把环境空集定义为可定义子集，而 `hasEmptyL`{.Agda} 封装其可构造性与空成员规格。
<!--ja-->
対象言語の偽な論理式が周囲の空集合を定義可能部分集合として切り出し、`hasEmptyL`{.Agda} がその構成可能性と要素をもたないという仕様をまとめる。
<!--/-->

<!--en-->
The falsehood of the object language carves nothing out of any stage: a member
of `defSet ⊥̇` would carry a proof of falsehood at its index. So `defSet ⊥̇` is
the empty set, one extensionality apart, and the empty set is therefore
constructible. Its specification is inherited along the underlying set, since
membership in `L` is membership in the hierarchy.
<!--zh-->
对象语言的假在任何阶段中都定义不出元素：`defSet ⊥̇` 的成员会在其索引处包含一个假的证明。因此，`defSet ⊥̇` 经外延性等于空集，从而空集可构造。它的规格由底层集合继承，因为 `L` 中的隶属就是层级中的隶属。
<!--/-->

```agda
∅∈𝒟ₒ : (σ : V ℓ) → ⟨ ∅ ∈ 𝒟ₒ (Lset σ) ⟩
∅∈𝒟ₒ σ = 𝒟ₒ-intro (Lset σ) ∅ ∣ ⊥̇ , defSet⊥≡∅ ∣₁
  where
  module DefC = DefOf (Lset σ)
  defSet⊥≡∅ : DefC.defSet ⊥̇ ≡ ∅
  defSet⊥≡∅ = extensionality (DefC.defSet ⊥̇) ∅ (sub₁ , sub₂)
    where
    sub₁ : ⟨ DefC.defSet ⊥̇ ⊆ ∅ ⟩
    sub₁ y y∈ₛ = PT.rec (snd (y ∈ₛ ∅))
      (λ { ((m , h) , q) → Empty.rec* h })
      (∈∈ₛ {a = y} {b = DefC.defSet ⊥̇} .snd y∈ₛ)
    sub₂ : ⟨ ∅ ⊆ DefC.defSet ⊥̇ ⟩
    sub₂ y y∈ₛ = Empty.rec (∅-empty y y∈ₛ)

∅∈L : ⟨ isL ∅ ⟩
∅∈L = 𝒟ₒ→isL ∅ ∅-ord ∅ (∅∈𝒟ₒ ∅)

∅ʟ : S
∅ʟ = ∅ , ∅∈L

hasEmptyL : isContr (SetOf (λ _ → ⊥))
hasEmptyL = uniqueL _ (∅ʟ , (λ x → empty-spec (fst x)))
```

<!--en-->
## Pairing, bounded by a stage
<!--zh-->
## 受阶段界住的配对
<!--ja-->
## 一つの段階内で対を作る
<!--/-->

<!--en-->
For two members of one stage, a two-constant disjunction carves their unordered
pair as a definable subset and proves its membership specification.
<!--zh-->
对同一阶段的两个成员，一条含两个常元的析取公式把其无序对定义为该可定义子集，并证明其成员规格。
<!--ja-->
一つの段階の二要素について、二定数の論理和がその非順序対を定義可能部分集合として切り出し、所属の仕様を証明する。
<!--/-->

<!--en-->
The unordered pair of two members of a stage is a definable subset of that
stage: each of them is `⟪ Lset σ ⟫↪` of some index, and the formula naming those
two indices carves out exactly the pair. Checking that takes one extensionality
against the hierarchy's own pairing axiom, in both directions: a member of the
definable subset satisfies the disjunction, hence is one of the two; and each of
the two satisfies it, hence is a member.

Nothing in the argument concerns the model. What it says is a fact about the
tower, and it is stated as one, because the constructions that need it most are
not the pairing axiom: an ordered pair in Kuratowski's encoding is two unordered
pairs deep, so a graph, a table or a sequence written with ordered pairs lands
two stages above its entries, and that is the only reason such a thing can be
placed at a stage at all.

Ordinality is not asked for, exactly as the successor identity does not ask for
it, and for the same reason: carving is not comparison. The singleton is the
degenerate pair, and the ordered pair is the pair of a singleton with a pair.
<!--zh-->
一个阶段的两个成员，其无序对是该阶段的可定义子集：二者各是某个索引的 `⟪ Lset σ ⟫↪`，而点名那两个索引的公式恰好定义出这个对。验证它要对照层级自己的配对公理做一次双向外延：可定义子集的成员满足那个析取，故是二者之一；而二者各自满足它，故是成员。

论证里没有一处关乎模型，说的是塔本身的一条事实，故照这样陈述：最需要它的构造并不是配对公理。Kuratowski 编码下的有序对嵌套了两层无序对，故以有序对写成的图、表或序列，落在其条目之上两个阶段处；这正是这类东西得以安置在某个阶段上的唯一理由。

此处不涉及序数性，后继恒等式也不涉及，理由相同：这里做的是构造，而非比较。单点集是退化的对，而有序对是单点集与对所成的对。
<!--/-->

```agda
pair∈𝒟ₒ : (σ x y : V ℓ) → ⟨ x ∈ Lset σ ⟩ → ⟨ y ∈ Lset σ ⟩
        → ⟨ ⁅ x , y ⁆ ∈ 𝒟ₒ (Lset σ) ⟩
pair∈𝒟ₒ σ x y x∈ y∈ = 𝒟ₒ-intro (Lset σ) ⁅ x , y ⁆ ∣ φ , defSet≡ ∣₁
  where
  module DefC = DefOf (Lset σ)
  mₓ = ∈-asFiber {a = x} {b = Lset σ} x∈ .fst
  qₓ : ⟪ Lset σ ⟫↪ mₓ ≡ x
  qₓ = ∈-asFiber {a = x} {b = Lset σ} x∈ .snd
  mᵧ = ∈-asFiber {a = y} {b = Lset σ} y∈ .fst
  qᵧ : ⟪ Lset σ ⟫↪ mᵧ ≡ y
  qᵧ = ∈-asFiber {a = y} {b = Lset σ} y∈ .snd

  φ : Formula ⟪ Lset σ ⟫ 1
  φ = (var zero ≐ con mₓ) ∨̇ (var zero ≐ con mᵧ)

  defSet≡ : DefC.defSet φ ≡ ⁅ x , y ⁆
  defSet≡ =
      extensionality (DefC.defSet φ) ⁅ ⟪ Lset σ ⟫↪ mₓ , ⟪ Lset σ ⟫↪ mᵧ ⁆
        (sub₁ , sub₂)
    ∙ cong₂ ⁅_,_⁆ qₓ qᵧ
    where
    sub₁ : ⟨ DefC.defSet φ ⊆ ⁅ ⟪ Lset σ ⟫↪ mₓ , ⟪ Lset σ ⟫↪ mᵧ ⁆ ⟩
    sub₁ w w∈ₛ = PT.rec (snd (w ∈ₛ ⁅ ⟪ Lset σ ⟫↪ mₓ , ⟪ Lset σ ⟫↪ mᵧ ⁆))
      (λ { ((m , h) , q) →
        subst (λ v → ⟨ v ∈ₛ ⁅ ⟪ Lset σ ⟫↪ mₓ , ⟪ Lset σ ⟫↪ mᵧ ⁆ ⟩) q
          (pairing-ax (⟪ Lset σ ⟫↪ mₓ) (⟪ Lset σ ⟫↪ mᵧ) (⟪ Lset σ ⟫↪ m) .snd
            (subst ⟨_⟩ (DefC.defSet-mem φ m) ∣ (m , h) , refl ∣₁)) })
      (∈∈ₛ {a = w} {b = DefC.defSet φ} .snd w∈ₛ)
    sub₂ : ⟨ ⁅ ⟪ Lset σ ⟫↪ mₓ , ⟪ Lset σ ⟫↪ mᵧ ⁆ ⊆ DefC.defSet φ ⟩
    sub₂ w w∈ₛ = PT.rec (snd (w ∈ₛ DefC.defSet φ))
      (λ { (inl p) → memOf mₓ ∣ inl refl ∣₁ p
         ; (inr p) → memOf mᵧ ∣ inr refl ∣₁ p })
      (pairing-ax (⟪ Lset σ ⟫↪ mₓ) (⟪ Lset σ ⟫↪ mᵧ) w .fst w∈ₛ)
      where
      memOf : (mᵢ : ⟪ Lset σ ⟫) → ⟨ (DefC.ι mᵢ ∷ []) DefC.⊨ᵐ φ ⟩
            → w ≡ ⟪ Lset σ ⟫↪ mᵢ → ⟨ w ∈ₛ DefC.defSet φ ⟩
      memOf mᵢ sat p = subst (λ v → ⟨ v ∈ₛ DefC.defSet φ ⟩) (sym p)
        (∈∈ₛ {a = ⟪ Lset σ ⟫↪ mᵢ} {b = DefC.defSet φ} .fst
          (subst ⟨_⟩ (sym (DefC.defSet-mem φ mᵢ)) sat))

pair∈Lset-suc : (σ x y : V ℓ) → ⟨ x ∈ Lset σ ⟩ → ⟨ y ∈ Lset σ ⟩
              → ⟨ ⁅ x , y ⁆ ∈ Lset (sucV σ) ⟩
pair∈Lset-suc σ x y x∈ y∈ =
  subst (λ w → ⟨ ⁅ x , y ⁆ ∈ w ⟩) (sym (Lset-suc σ)) (pair∈𝒟ₒ σ x y x∈ y∈)

sgl∈Lset-suc : (σ x : V ℓ) → ⟨ x ∈ Lset σ ⟩ → ⟨ ⁅ x ⁆s ∈ Lset (sucV σ) ⟩
sgl∈Lset-suc σ x x∈ = subst (λ w → ⟨ w ∈ Lset (sucV σ) ⟩) (pair-singleton x)
  (pair∈Lset-suc σ x x x∈ x∈)

pr∈Lset-suc : (σ x y : V ℓ) → ⟨ x ∈ Lset σ ⟩ → ⟨ y ∈ Lset σ ⟩
            → ⟨ pr x y ∈ Lset (sucV (sucV σ)) ⟩
pr∈Lset-suc σ x y x∈ y∈ = pair∈Lset-suc (sucV σ) ⁅ x ⁆s ⁅ x , y ⁆
  (sgl∈Lset-suc σ x x∈) (pair∈Lset-suc σ x y x∈ y∈)
```

<!--en-->
## Pairing
<!--zh-->
## 配对
<!--ja-->
## 対の公理
<!--/-->

<!--en-->
`hasPairL`{.Agda} first places two arbitrary constructible sets in a common stage,
then applies the bounded pair construction and the uniqueness principle.
<!--zh-->
`hasPairL`{.Agda} 先把任意两个可构造集合放进公共阶段，再施用有界配对构造与唯一性原理。
<!--ja-->
`hasPairL`{.Agda} はまず任意の二つの構成可能集合を共通段階へ入れ、次に有界な対の構成と一意性原理を適用する。
<!--/-->

<!--en-->
The axiom is then the lemma above at a common stage for the two arguments, with
the closure lemma above putting the result in `L` and the specification inherited
from the hierarchy along the underlying sets.
<!--zh-->
于是这条公理就是：对两个实参的公共阶段应用上面的引理，随后由收尾引擎把结果放进 `L`，其规格沿底层集合从层级继承。
<!--/-->

```agda
module PairOf (a b : S) where
  Q : S → Ω
  Q x = (x ≈ˢ a) ⊔ (x ≈ˢ b)

  mkPair : (σ : V ℓ) → IsOrd σ → ⟨ fst a ∈ Lset σ ⟩ → ⟨ fst b ∈ Lset σ ⟩
         → SetOf Q
  mkPair σ oσ fa∈ fb∈ = pairElt , (λ z → pair-spec (fst a) (fst b) (fst z))
    where
    pairElt : S
    pairElt = ⁅ fst a , fst b ⁆
            , 𝒟ₒ→isL σ oσ ⁅ fst a , fst b ⁆ (pair∈𝒟ₒ σ (fst a) (fst b) fa∈ fb∈)

  build : ∥ SetOf Q ∥₁
  build = PT.rec squash₁
    (λ { (σ , (oσ , (fa∈ , fb∈))) → ∣ mkPair σ oσ fa∈ fb∈ ∣₁ })
    (isL-directed (fst a) (fst b) (a .snd) (b .snd))

hasPairL : (a b : S) → isContr (SetOf (λ x → (x ≈ˢ a) ⊔ (x ≈ˢ b)))
hasPairL a b = mere→uniqueL (PairOf.Q a b) (PairOf.build a b)
```

<!--en-->
## Union
<!--zh-->
## 并
<!--ja-->
## 和集合の公理
<!--/-->

<!--en-->
Stage transitivity bounds every member of every member of a constructible set,
so a bounded existential formula carves its union and `hasUnionL`{.Agda} proves
the exact membership law.
<!--zh-->
阶段传递性界住一个可构造集合的成员之成员，故有界存在公式雕出其并，而 `hasUnionL`{.Agda} 证明精确成员律。
<!--ja-->
段階の推移性が構成可能集合の各要素の全要素を抑えるため、有界存在の論理式がその和集合を切り出し、`hasUnionL`{.Agda} が正確な所属法則を証明する。
<!--/-->

<!--en-->
No search is required: a stage containing the argument already contains every
member of every member of it, because stages are transitive. The formula is a
bounded existential, "some member of the argument has me as a member", and its
quantifier ranges over the stage, which is exactly why transitivity is what makes
the argument go through. The final step completes the specification: the model
record quantifies over constructible witnesses while the hierarchy's union axiom
quantifies over all of them, and transitivity of the class identifies the two.
<!--zh-->
这里不需要搜索：装着实参的阶段同时也装着实参的成员的每个成员，因为阶段是传递的。公式是一个有界存在：「实参的某个成员以我为成员」，其量词跑遍那个阶段；传递性正是论证得以走通的原因。最后一步补全规格：模型 record 对可构造的见证量化，层级的并公理对全部见证量化，而类的传递性使二者一致。
<!--/-->

```agda
module UnionOf (a : S) where
  Q : S → Ω
  Q x = ⋁ S (λ y → (y ∈ˢ a) ⊓ (x ∈ˢ y))

  mkUnion : (σ : V ℓ) → IsOrd σ → ⟨ fst a ∈ Lset σ ⟩ → SetOf Q
  mkUnion σ oσ fa∈ = unionElt , spec
    where
    module DefA = DefOf (Lset σ)
    Atrans = layer-trans (Lset-layer σ)
    mₐ = ∈-asFiber {a = fst a} {b = Lset σ} fa∈ .fst
    qₐ : ⟪ Lset σ ⟫↪ mₐ ≡ fst a
    qₐ = ∈-asFiber {a = fst a} {b = Lset σ} fa∈ .snd

    φ : Formula ⟪ Lset σ ⟫ 1
    φ = ∃̇∈ (con mₐ) (var (suc zero) ∈̇ var zero)

    defSet≡ : DefA.defSet φ ≡ ⋃ (fst a)
    defSet≡ = extensionality (DefA.defSet φ) (⋃ (fst a)) (sub₁ , sub₂)
      where
      sub₁ : ⟨ DefA.defSet φ ⊆ ⋃ (fst a) ⟩
      sub₁ y y∈ₛ = PT.rec (snd (y ∈ₛ ⋃ (fst a)))
        (λ { ((m , h) , q) →
          subst (λ w → ⟨ w ∈ₛ ⋃ (fst a) ⟩) q
            (PT.rec (snd (⟪ Lset σ ⟫↪ m ∈ₛ ⋃ (fst a)))
              (λ { (v , (fstv∈mₐ , m∈fstv)) →
                union-ax (fst a) (⟪ Lset σ ⟫↪ m) .snd
                  ∣ fst v
                  , ( ∈∈ₛ {a = fst v} {b = fst a} .fst
                        (subst (λ w → ⟨ fst v ∈ w ⟩) qₐ fstv∈mₐ)
                    , ∈∈ₛ {a = ⟪ Lset σ ⟫↪ m} {b = fst v} .fst m∈fstv ) ∣₁ })
              (subst ⟨_⟩ (DefA.defSet-mem φ m) ∣ (m , h) , refl ∣₁)) })
        (∈∈ₛ {a = y} {b = DefA.defSet φ} .snd y∈ₛ)
      sub₂ : ⟨ ⋃ (fst a) ⊆ DefA.defSet φ ⟩
      sub₂ y y∈ₛ = PT.rec (snd (y ∈ₛ DefA.defSet φ))
        (λ { (v , (v∈ₛfa , y∈ₛv)) → member v v∈ₛfa y∈ₛv })
        (union-ax (fst a) y .fst y∈ₛ)
        where
        member : (v : V ℓ) → ⟨ v ∈ₛ fst a ⟩ → ⟨ y ∈ₛ v ⟩
               → ⟨ y ∈ₛ DefA.defSet φ ⟩
        member v v∈ₛfa y∈ₛv =
          subst (λ w → ⟨ w ∈ₛ DefA.defSet φ ⟩) q'
            (∈∈ₛ {a = ⟪ Lset σ ⟫↪ m'} {b = DefA.defSet φ} .fst
              (subst ⟨_⟩ (sym (DefA.defSet-mem φ m')) sat))
          where
          v∈fa = ∈∈ₛ {a = v} {b = fst a} .snd v∈ₛfa
          y∈v = ∈∈ₛ {a = y} {b = v} .snd y∈ₛv
          v∈A = Atrans {x = fst a} {y = v} v∈fa fa∈
          y∈A = Atrans {x = v} {y = y} y∈v v∈A
          fib = ∈-asFiber {a = y} {b = Lset σ} y∈A
          m' = fib .fst
          q' = fib .snd
          sat : ⟨ (DefA.ι m' ∷ []) DefA.⊨ᵐ φ ⟩
          sat = ∣ (v , v∈A)
                , ( subst (λ w → ⟨ v ∈ w ⟩) (sym qₐ) v∈fa
                  , subst (λ w → ⟨ w ∈ v ⟩) (sym q') y∈v ) ∣₁

    union∈𝒟ₒ : ⟨ ⋃ (fst a) ∈ 𝒟ₒ (Lset σ) ⟩
    union∈𝒟ₒ = 𝒟ₒ-intro (Lset σ) (⋃ (fst a)) ∣ φ , defSet≡ ∣₁

    unionElt : S
    unionElt = ⋃ (fst a) , 𝒟ₒ→isL σ oσ (⋃ (fst a)) union∈𝒟ₒ

    spec : (z : S) → (z ∈ˢ unionElt) ≡ Q z
    spec z = union-spec (fst a) (fst z) ∙ bridge
      where
      bridge : ⋁ (V ℓ) (λ y → (y ∈ fst a) ⊓ (fst z ∈ y)) ≡ Q z
      bridge = ⇔toPath
        (PT.map (λ { (y , py) →
          (y , isL-trans {x = fst a} {y = y} (py .fst) (a .snd)) , py }))
        (PT.map (λ { (y , py) → fst y , py }))

  build : ∥ SetOf Q ∥₁
  build = PT.rec squash₁ (λ { (σ , (oσ , fa∈)) → ∣ mkUnion σ oσ fa∈ ∣₁ }) (a .snd)

hasUnionL : (a : S) → isContr (SetOf (λ x → ⋁ S (λ y → (y ∈ˢ a) ⊓ (x ∈ˢ y))))
hasUnionL a = mere→uniqueL (UnionOf.Q a) (UnionOf.build a)
```

<!--en-->
## Recap
<!--zh-->
## 小结
<!--ja-->
## まとめ
<!--/-->

<!--en-->
The chapter supplies five ZF fields: extensionality and regularity by restriction,
and empty set, pairing, and union by carving definable subsets of bounded stages.
<!--zh-->
本章确立五个 ZF 字段：外延公理与正则公理由限制得到，空集、配对与并则由有界阶段上的可定义子集构造出来。
<!--ja-->
本章は五つの ZF フィールドを与える。外延性公理と正則性公理は制限から、空集合、対、和集合は有界な段階の定義可能部分集合を切り出すことから得られる。
<!--/-->

<!--en-->
Five model fields, none of them assumed. Extensionality and regularity came down
from the hierarchy along transitivity, and with extensionality in hand every
later field needs only a witness, since uniqueness follows. The empty set,
pairing and union were each obtained from a single stage by a single formula,
with the bounding ordinal supplying that stage where two arguments had to meet.
The remaining tasks at the frontier are thereby reduced by three, and the pattern
established here, one stage, one formula, one extensionality, is the pattern
the remaining constructions follow. The pairing construction is also stated on
its own, as a fact about the tower rather than about the model: `pair∈Lset-suc`{.Agda} puts the
unordered pair of two members of a stage in the next stage,
`sgl∈Lset-suc`{.Agda} the singleton, and `pr∈Lset-suc`{.Agda} the ordered pair
two stages up, which is what places anything written with ordered pairs at a
stage at all.
<!--zh-->
五个模型字段，无一靠假设。外延与正则沿传递性从层级下降；有了外延性，日后每个字段只需一个见证，唯一性随之而来。空集、配对与并各由单一公式从单一阶段中构造出来；两个实参须会合时，所需的阶段由上界序数提供。前沿余下的任务因此减少三项；此处确立的模式，即一个阶段、一条公式、一次外延，正是余下各构造所遵循的模式。配对那次构造也单独陈述一遍，作为关于塔而非关于模型的事实：`pair∈Lset-suc`{.Agda} 把一个阶段的两个成员的无序对放进下一个阶段，`sgl∈Lset-suc`{.Agda} 放单点集，`pr∈Lset-suc`{.Agda} 把有序对放到高两个阶段处；这也正是以有序对写成的任何东西得以安置在某个阶段上的原因。
<!--/-->
