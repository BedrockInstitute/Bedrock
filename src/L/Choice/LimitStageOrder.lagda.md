<!--en-->
# The limit-stage order inside L
<!--zh-->
# L 内部的极限层序
<!--ja-->
# L の内部にある極限段階の順序
<!--/-->

<!--en-->
This chapter describes the finite-level comparison inside the object language,
uses separation to realize the limit-stage order as a set in `L`, and supplies
that set to the code-order slot needed by the name construction.
<!--zh-->
本章在对象语言中描述有穷层号比较，用分离把极限层序实现为 `L` 中的集合，再把该集合供应给名字构造所需的码序位。
<!--ja-->
本章では有限レベルの比較を対象言語で記述し、分出公理で極限段階の順序を `L` 内の集合として実現し、その集合を名前の構成が必要とする符号順序スロットへ渡す。
<!--/-->

<!--en-->
The Choice construction has reduced its obligation at each stage, and
`L.Choice.NameComparison` named what was left: the frame that internalizes the naming
comparison holds a **relation slot for the codes**, and what that slot wants is
the order on the members of the limit stage, `limitOrder`{.Agda}, as a set of the
model. Nothing built it. This chapter does.

The order is level-primary. A member of the limit stage first appears at some
finite stage, the least such numeral is its **level**, and two members of
different levels are compared by their levels alone. Two members of one level are
compared by that level's own order, which is comparison at the **earliest
disagreement**: the two sets differ somewhere, and the least point of difference
under the previous stage's order decides, with the set holding it placed later.

So there are two keys, and each has to be said in the object language. The first
is short and the machinery for it exists: a numeral is the level of a set when
the tower there holds the set and no smaller numeral's tower does. The second is
a recursion along the numerals whose values are relations, and a recursion whose
values are sets cannot be named by a term, so what gets described is an
**approximation**, exactly as the tower and the order table were described. The
two keys are then joined by a disjunction, and the model's own separation
extracts the order from a bound containing the relevant ordered pairs.
<!--zh-->
Choice 构造在每层都把自己的债务归约成更小的一笔，而 `L.Choice.NameComparison`{.Agda} 点出了剩下的那笔：内化命名比较的那个框架持有一个**为诸码所设的关系位**，而那一位所要的，是极限层诸成员上的那个序 `limitOrder`{.Agda}，作为模型的一个集合。本章造出这个集合。

那个序以层号为主键。极限层的成员首次现身于某个有穷层，最小的这种数码就是它的**层号**，而层号不同的两个成员仅凭层号比较。同层的两个成员按那一层自己的序比较，而后者是在**最先分歧处**的比较：两个集合总在某处相异，而在上一层自己的序之下最小的那个相异点作出裁决，持有它的那个集合排在后面。

这里有两个键，而且都必须在对象语言中表达。第一个键较简单，所需构造已经具备：一个数码是某集合的层号，意思是该数码处的塔包含这个集合，而更小数码处的塔都不包含它。第二个键由沿诸数码的递归给出，其取值是关系。由于取值为集合的递归不能由一个词项直接命名，这里描述的是递归的**逼近**，方式与塔及序之表相同。随后以析取连接两个键，再由模型中的分离从包含所有相关有序对的集合界中取出所需关系。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module L.Choice.LimitStageOrder {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using
  ( Formula; var; con; _∈̇_; _∧̇_; _∨̇_; ¬̇_; _⇒̇_; ∃̇_; ∀̇_; ∀̇∈ )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Coding {ℓ} using ( pr; pr-inj; #mono; #-inj′ )
open import L.Constructible {ℓ}
  using ( 𝒮ʟ; isL; isL-trans; Lset; Lset→isL; IsOrd )
open import L.Ordinal {ℓ} using ( numeral-ord; #∈ω; ∈#-elim; #∈#-elim; ω-ord )
open import L.Axioms.Basic {ℓ} using ( LsetS )
open import L.Axioms.Infinity {ℓ} lem using ( ωʟ )
open import L.Axioms.Full {ℓ} lem using ( hasSeparationL )
open import L.Recursion {ℓ} lem using ( smallDom )
open import L.Coding.Model {ℓ} using ( appAt; appAt-adequate; prAtL; prAtL-adequate; prʟ; prʟ-fst )
open import L.Coding.Expressions {ℓ} using ( numL )
open import L.Coding.HierarchySequence {ℓ} lem using ( LsetGraphAt )
open import L.Hierarchy {ℓ} lem using ( Lset-only; Lset-defines )
open import L.Choice.FiniteStageOrders {ℓ} lem
  using ( Limit; level; level-in; levelData; limitOrder
        ; before; precedes; Agrees; Witness; finiteStage )
open import L.Choice.NameComparison {ℓ} lem using ( module Adequacy )
open import L.WellOrder.Base {ℓ-suc ℓ} using ( SWO; Tri; lt; eq; gt )

import FOL.Absoluteness
open import Cubical.Data.Sum using ( _⊎_; inl; inr )
open import Cubical.Foundations.Prelude using ( subst2 )
open import Cubical.Data.Nat.Order using ( _<_; _≟_ )
import Cubical.Data.Nat.Order as NatOrder
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁; ∣_∣₁; squash₁ )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_; setIsSet )
open import Cubical.HITs.CumulativeHierarchy.Properties
  using ( ⟪_⟫; ⟪_⟫↪; ∈-asFiber; ∈∈ₛ; ∈ₛ⟪_⟫↪_ )
open import Cubical.HITs.CumulativeHierarchy.Constructions using ( module InfinitySet )
open InfinitySet using ( #_; ω )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL renaming ( _⊨ᵐ_ to _⊨_ )

open SWO limitOrder using () renaming ( _<∙_ to _≺ˡ_ )

private
  sh2 : ∀ {n} → Fin n → Fin (suc (suc n))
  sh2 i = suc (suc i)
```

Perf: the tower at a numeral is sealed where it is built, as in the birth
description of the previous chapter (measured there at 178 s against 2 s).

```agda
opaque
  towerS : ℕ → S
  towerS k = LsetS (# k) (numeral-ord k)

  towerS-fst : (k : ℕ) → fst (towerS k) ≡ Lset (# k)
  towerS-fst k = refl

  numS : ℕ → S
  numS k = # k , numL k

  numS-fst : (k : ℕ) → fst (numS k) ≡ # k
  numS-fst k = refl

towerGraph : ∀ {n} (j : ℕ) (δ : S ^ n) (i : Fin n) → fst (lookup i δ) ≡ # j
           → ⟨ (towerS j ∷ δ) ⊨ LsetGraphAt zero (suc i) ⟩
towerGraph j δ i q = Lset-defines zero (suc i) (towerS j ∷ δ)
  (subst IsOrd (sym q) (numeral-ord j))
  (towerS-fst j ∙ cong Lset (sym q))
```

<!--en-->
## The level, said inside

<!--zh-->
## 层号，在内部说出
<!--ja-->
## レベルを内部で述べる
<!--/-->

<!--en-->
`LevelAt`{.Agda} describes that a numeral is the least finite stage containing a
given member of `Lset ω`{.Agda}, with fill and read lemmas against `level`{.Agda}.
<!--zh-->
`LevelAt`{.Agda} 描述一个数码是包含给定 `Lset ω`{.Agda} 成员的最小有穷层，并以填充与读取引理对应 `level`{.Agda}。
<!--ja-->
`LevelAt`{.Agda} は、ある数項が与えられた `Lset ω`{.Agda} の要素を含む最小の有限段階であることを記述し、fill/read 補題で `level`{.Agda} と対応づける。
<!--/-->

<!--en-->

Three conjuncts, and no constant other than `ω` itself. The slot `b` holds a
member of `ω`, so it holds a numeral; there is a tower at `b` and the slot `x`
belongs to it; and for every member of `b`, that is, every smaller numeral, the
tower there does **not** hold `x`. The tower is reached by the sequence chapter's
graph, which is the only way to reach it, since the hierarchy is described and
not named by a term.

The third conjunct is the first universal quantifier used anywhere in this part.
It costs nothing, and the reason is worth recording: the indexed conjunction is a
genuine product and object implication is a function, so the obligation is
discharged by a lambda with no truncation to eliminate, and the numeral decoding
under it lands in absurdity, which is a proposition, so the truncation there is
absorbed in one line.

Both readings stand at **variable** slots in a variable environment, and the level
itself arrives as a **variable numeral** carrying its own defining equation. That
is not a stylistic choice. With `level a`{.Agda} inlined at its occurrences the
section takes 145 s; with the numeral as a parameter and `refl`{.Agda} at the call
site it takes 1.8 s, and the eighty-fold difference is the classical accessibility
recursion that computes the level being forced open by conversion at a slot.
<!--zh-->

三个合取项，且除 `ω` 自身外不指称任何常元。位 `b` 持有 `ω` 的一个成员，故它持有一个数码；`b` 处有一座塔，而位 `x` 属于它；并且对 `b` 的每个成员、亦即每个更小的数码，那里的塔**不**包含 `x`。塔经由序列那一章的图得到，而这是得到它的唯一途径，因为层级是被描述的、不是被某个词项命名的。

第三个合取项是本部任何地方头一次用上全称量词之处。它不花分文，而理由值得记下：指标合取是货真价实的乘积，对象蕴含是函数，故这笔债由一个 lambda 交割，没有任何截断要消去；而它之下的数码解码落在荒谬里，荒谬是命题，故那里的截断一行就被吸收。

两条读式都站在变元环境的**变元**位上，而层号自身以**变元数码**的身份到场、携带它自己的定义等式。这不是文体上的取舍。把 `level a`{.Agda} 就地内联在它出现的各处，本节要跑 145 秒；把数码取作参数，在调用处填 `refl`{.Agda}，则是 1.8 秒；而这八十倍之差，正是算出层号的那场经典可及性递归被槽位处的转换检查撬开所致。
<!--/-->

```agda
LevelAt : ∀ {n} → Fin n → Fin n → Formula S n
LevelAt b x =
  (var b ∈̇ con ωʟ)
  ∧̇ ( ∃̇ ( LsetGraphAt zero (suc b) ∧̇ (var (suc x) ∈̇ var zero) )
    ∧̇ ∀̇∈ (var b) (∀̇ ( LsetGraphAt zero (suc zero)
                     ⇒̇ ¬̇ (var (sh2 x) ∈̇ var zero) )) )

module Level (a : Limit) (k : ℕ) (qk : level a ≡ k) where
  private
    aIn : ⟨ fst a ∈ Lset (# k) ⟩
    aIn = subst (λ j → ⟨ fst a ∈ Lset (# j) ⟩) qk (level-in a)

    aMin : (m : ℕ) → ⟨ fst a ∈ Lset (# m) ⟩ → m < k → Empty.⊥
    aMin m h hm = levelData a .snd .snd m h
      (lift (subst (λ j → m < j) (sym qk) hm))

  module _ {n : ℕ} (b x : Fin n) (γ : S ^ n) where
    private
      Body : S → Type (ℓ-suc ℓ)
      Body c = ⟨ (c ∷ γ) ⊨ LsetGraphAt zero (suc b) ⟩
             × ⟨ fst (lookup x γ) ∈ fst c ⟩

    LevelAt-in : fst (lookup b γ) ≡ # k → fst (lookup x γ) ≡ fst a
               → ⟨ γ ⊨ LevelAt b x ⟩
    LevelAt-in qb qx = hω , (hex , hmin)
      where
      hω : ⟨ fst (lookup b γ) ∈ ω ⟩
      hω = subst (λ u → ⟨ u ∈ ω ⟩) (sym qb) (#∈ω k)

      hex : ⟨ γ ⊨ ∃̇ ( LsetGraphAt zero (suc b) ∧̇ (var (suc x) ∈̇ var zero) ) ⟩
      hex = ∣ towerS k , (towerGraph k γ b qb , hm) ∣₁
        where
        hm : ⟨ fst (lookup x γ) ∈ fst (towerS k) ⟩
        hm = subst (λ u → ⟨ fst (lookup x γ) ∈ u ⟩) (sym (towerS-fst k))
          (subst (λ u → ⟨ u ∈ Lset (# k) ⟩) (sym qx) aIn)

      hmin : ⟨ γ ⊨ ∀̇∈ (var b) (∀̇ ( LsetGraphAt zero (suc zero)
                                  ⇒̇ ¬̇ (var (sh2 x) ∈̇ var zero) )) ⟩
      hmin u u∈ c hg hmem = lift (PT.rec Empty.isProp⊥ step
        (∈#-elim k (fst u) (subst (λ w → ⟨ fst u ∈ w ⟩) qb u∈)))
        where
        step : Σ[ m ∈ ℕ ] ((m < k) × (fst u ≡ # m)) → Empty.⊥
        step (m , (hm , qu)) = aMin m inStage hm
          where
          qc : fst c ≡ Lset (fst u)
          qc = Lset-only zero (suc zero) (c ∷ u ∷ γ) hg
            (subst IsOrd (sym qu) (numeral-ord m))
          inStage : ⟨ fst a ∈ Lset (# m) ⟩
          inStage = subst (λ w → ⟨ fst a ∈ Lset w ⟩) qu
            (subst (λ w → ⟨ w ∈ Lset (fst u) ⟩) qx
              (subst (λ w → ⟨ fst (lookup x γ) ∈ w ⟩) qc hmem))

    LevelAt-out : ⟨ γ ⊨ LevelAt b x ⟩ → fst (lookup x γ) ≡ fst a
                → fst (lookup b γ) ≡ # k
    LevelAt-out (hω , (hex , hmin)) qx =
      PT.rec (setIsSet (fst (lookup b γ)) (# k)) named hω
      where
      notAbove : (m : ℕ) → fst (lookup b γ) ≡ # m → k < m → Empty.⊥
      notAbove m qb hk = lower (hmin (numS k)
        (subst (λ w → ⟨ w ∈ fst (lookup b γ) ⟩) (sym (numS-fst k))
          (subst (λ w → ⟨ # k ∈ w ⟩) (sym qb) (#mono k m hk)))
        (towerS k) (towerGraph k (numS k ∷ γ) zero (numS-fst k))
        (subst (λ w → ⟨ fst (lookup x γ) ∈ w ⟩) (sym (towerS-fst k))
          (subst (λ w → ⟨ w ∈ Lset (# k) ⟩) (sym qx) aIn)))

      notBelow : (m : ℕ) → fst (lookup b γ) ≡ # m → m < k → Empty.⊥
      notBelow m qb hm = PT.rec Empty.isProp⊥ atTower hex
        where
        atTower : Σ[ c ∈ S ] Body c → Empty.⊥
        atTower (c , (hg , hmem)) = aMin m inStage hm
          where
          qc : fst c ≡ Lset (# m)
          qc = Lset-only zero (suc b) (c ∷ γ) hg
                 (subst IsOrd (sym qb) (numeral-ord m))
             ∙ cong Lset qb
          inStage : ⟨ fst a ∈ Lset (# m) ⟩
          inStage = subst (λ w → ⟨ w ∈ Lset (# m) ⟩) qx
            (subst (λ w → ⟨ fst (lookup x γ) ∈ w ⟩) qc hmem)

      named : Σ[ j ∈ Lift ℕ ] (# (lower j) ≡ fst (lookup b γ))
            → fst (lookup b γ) ≡ # k
      named (j , qj) = qb ∙ cong #_ (decide (lower j ≟ k))
        where
        qb : fst (lookup b γ) ≡ # (lower j)
        qb = sym qj
        decide : NatOrder.Trichotomy (lower j) k → lower j ≡ k
        decide (NatOrder.lt h) = Empty.rec (notBelow (lower j) qb h)
        decide (NatOrder.eq e) = e
        decide (NatOrder.gt h) = Empty.rec (notAbove (lower j) qb h)
```

<!--en-->
## The earliest disagreement, said inside

<!--zh-->
## 最先的分歧，在内部说出
<!--ja-->
## 最初の相違を内部で述べる
<!--/-->

<!--en-->
`BeforeAt`{.Agda} internalizes the earliest-disagreement relation at a numeral
stage, and its two readings connect satisfaction with `before`{.Agda}.
<!--zh-->
`BeforeAt`{.Agda} 把数码层处的最先分歧关系内化，其两条读式把满足关系与 `before`{.Agda} 对应起来。
<!--ja-->
`BeforeAt`{.Agda} は数項段階での最初の相違の関係を内部化し、その二つの読みが充足関係と `before`{.Agda} を対応づける。
<!--/-->

<!--en-->

The second key is one step of the finite chapter's comparison, and this section
writes that step down with **nothing concrete in it**: the base relation and the
base stage are held in slots, and the two sets being compared are held in slots
too. That genericity is not a flourish. The relation the step consults is the
value of a recursion, so it can never be a constant at the point where the step
is used; it arrives as a variable, and the whole description has to be able to
stand there.

What the step says is what the finite chapter says. There is a `z` in the stage
which belongs to `y` and not to `x`, and every member `w` of the stage that the
base relation puts before `z` belongs to `x` exactly when it belongs to `y`. The
one place where the object language cannot copy the meta-language verbatim is the
membership of the base relation: `pr w z` is a pair, and a pair is described and
not named, so the atom is the model chapter's `appAt`{.Agda}.

Both directions are one bookkeeping step apart. The meta-language quantifies over
sets of the hierarchy and the object language over elements of the model, so
each witness that crosses has to acquire or shed its constructibility proof, and
the proof is available because a member of a set of `L` is an element of `L`. The
pair that carries it is **sealed** where it is built, for the reason the previous
chapter measured: it is the pair, not the set inside it, that reaches the slot.
<!--zh-->

第二个键是有穷那一章那次比较的单独一步，而本节把这一步写下来，且**其中不含任何具体之物**：基底关系与基底层被握在槽位里，被比较的那两个集合也被握在槽位里。这种通用性不是花架子。那一步所查阅的关系是一场递归的取值，故在这一步被使用之处，它绝不可能是常元；它以变元身份到场，而整条描述必须站得住。

那一步所说的，就是有穷那一章所说的。层中存在一个 `z`，它属于 `y` 而不属于 `x`，且层中凡被基底关系排在 `z` 之前的成员 `w`，属于 `x` 当且仅当属于 `y`。对象语言唯一无法逐字抄写元语言之处，是基底关系的那次隶属：`pr w z` 是一个对，而对是被描述的、不是被命名的，故那个原子是模型那一章的 `appAt`{.Agda}。

两个方向只需多做一步核对。元语言量化层级中的集合，对象语言量化模型中的元素，因此每个跨越这层边界的见证都要补上或去掉可构造性证明；该证明存在，因为 `L` 的集合的成员就是 `L` 的元素。携带证明的那个对在构造之处被**封装**，理由已在上一章通过实测说明：进入槽位的是整个对，而不是其中的集合。
<!--/-->

Perf: a member of a set of the model, paired with the constructibility proof it
inherits, is sealed where it is built (the previous chapter's measurement).

```agda
opaque
  memS : (A : S) (z : V ℓ) → ⟨ z ∈ fst A ⟩ → S
  memS A z h = z , isL-trans {x = fst A} {y = z} h (snd A)

  memS-fst : (A : S) (z : V ℓ) (h : ⟨ z ∈ fst A ⟩) → fst (memS A z h) ≡ z
  memS-fst A z h = refl

PrecedesAt : ∀ {n} → Fin n → Fin n → Fin n → Fin n → Formula S n
PrecedesAt r A x y =
  ∃̇ ( (var zero ∈̇ var (suc A))
    ∧̇ ( (var zero ∈̇ var (suc y))
      ∧̇ ( ¬̇ (var zero ∈̇ var (suc x))
        ∧̇ ∀̇∈ (var (suc A))
             ( appAt (sh2 r) zero (suc zero)
             ⇒̇ ( ((var zero ∈̇ var (sh2 x)) ⇒̇ (var zero ∈̇ var (sh2 y)))
               ∧̇ ((var zero ∈̇ var (sh2 y)) ⇒̇ (var zero ∈̇ var (sh2 x))) ) ) ) ) )

module Precedes {n : ℕ} (r A x y : Fin n) (γ : S ^ n)
                (R : V ℓ → V ℓ → Ω)
                (Rrep : (u v : S) → ⟨ pr (fst u) (fst v) ∈ fst (lookup r γ) ⟩
                      → ⟨ R (fst u) (fst v) ⟩)
                (Rfill : (u v : S) → ⟨ R (fst u) (fst v) ⟩
                       → ⟨ pr (fst u) (fst v) ∈ fst (lookup r γ) ⟩)
                where
  private
    Aʟ : S
    Aʟ = lookup A γ

    xv : V ℓ
    xv = fst (lookup x γ)

    yv : V ℓ
    yv = fst (lookup y γ)

    Both : V ℓ → Type (ℓ-suc ℓ)
    Both w = (⟨ w ∈ xv ⟩ → ⟨ w ∈ yv ⟩) × (⟨ w ∈ yv ⟩ → ⟨ w ∈ xv ⟩)

    Agreeing : S → Type (ℓ-suc ℓ)
    Agreeing z = (w : S) → ⟨ fst w ∈ fst Aʟ ⟩
               → ⟨ (w ∷ z ∷ γ) ⊨ appAt (sh2 r) zero (suc zero) ⟩
               → Both (fst w)

    Body : S → Type (ℓ-suc ℓ)
    Body z = ⟨ fst z ∈ fst Aʟ ⟩
           × ( ⟨ fst z ∈ yv ⟩
             × ( (⟨ fst z ∈ xv ⟩ → Lift {j = ℓ-suc ℓ} Empty.⊥) × Agreeing z ) )

  PrecedesAt-out : ⟨ γ ⊨ PrecedesAt r A x y ⟩
                 → ⟨ precedes R (fst Aʟ) xv yv ⟩
  PrecedesAt-out = PT.rec squash₁ atZ
    where
    atZ : Σ[ z ∈ S ] Body z → ⟨ precedes R (fst Aʟ) xv yv ⟩
    atZ (z , (z∈A , (z∈y , (z∉x , hag)))) =
      ∣ fst z , (z∈A , (z∈y , ((λ h → lower (z∉x h)) , ag))) ∣₁
      where
      ag : Agrees R (fst Aʟ) xv yv (fst z)
      ag w w∈A hR = subst Both (memS-fst Aʟ w w∈A) (hag wS w∈A' happ)
        where
        wS : S
        wS = memS Aʟ w w∈A
        w∈A' : ⟨ fst wS ∈ fst Aʟ ⟩
        w∈A' = subst (λ u → ⟨ u ∈ fst Aʟ ⟩) (sym (memS-fst Aʟ w w∈A)) w∈A
        hp : ⟨ pr (fst wS) (fst z) ∈ fst (lookup r γ) ⟩
        hp = Rfill wS z
          (subst (λ u → ⟨ R u (fst z) ⟩) (sym (memS-fst Aʟ w w∈A)) hR)
        happ : ⟨ (wS ∷ z ∷ γ) ⊨ appAt (sh2 r) zero (suc zero) ⟩
        happ = subst ⟨_⟩
          (sym (appAt-adequate (sh2 r) zero (suc zero) (wS ∷ z ∷ γ))) hp

  PrecedesAt-in : ⟨ precedes R (fst Aʟ) xv yv ⟩
                → ⟨ γ ⊨ PrecedesAt r A x y ⟩
  PrecedesAt-in = PT.rec squash₁ atZ
    where
    atZ : Σ[ z ∈ V ℓ ] Witness R (fst Aʟ) xv yv z
        → ⟨ γ ⊨ PrecedesAt r A x y ⟩
    atZ (z , (z∈A , (z∈y , (z∉x , ag)))) =
      ∣ zS , (z∈A' , (z∈y' , (z∉x' , hag))) ∣₁
      where
      zS : S
      zS = memS Aʟ z z∈A
      qz : fst zS ≡ z
      qz = memS-fst Aʟ z z∈A
      z∈A' : ⟨ fst zS ∈ fst Aʟ ⟩
      z∈A' = subst (λ u → ⟨ u ∈ fst Aʟ ⟩) (sym qz) z∈A
      z∈y' : ⟨ fst zS ∈ yv ⟩
      z∈y' = subst (λ u → ⟨ u ∈ yv ⟩) (sym qz) z∈y
      z∉x' : ⟨ fst zS ∈ xv ⟩ → Lift {j = ℓ-suc ℓ} Empty.⊥
      z∉x' h = lift (z∉x (subst (λ u → ⟨ u ∈ xv ⟩) qz h))
      hag : Agreeing zS
      hag w w∈A happ = ag (fst w) w∈A hR
        where
        hp : ⟨ pr (fst w) (fst zS) ∈ fst (lookup r γ) ⟩
        hp = subst ⟨_⟩ (appAt-adequate (sh2 r) zero (suc zero) (w ∷ zS ∷ γ)) happ
        hR : ⟨ R (fst w) z ⟩
        hR = subst (λ u → ⟨ R (fst w) u ⟩) qz (Rrep w zS hp)
```

<!--en-->
## The order, composed

<!--zh-->
## 那个序，接合起来
<!--ja-->
## 順序を合成する
<!--/-->

<!--en-->
The formula `Lim`{.Agda} compares two limit-stage members first by their least
levels and, when those agree, by the internal earliest-disagreement relation.
<!--zh-->
公式 `Lim`{.Agda} 先比较两个极限层成员的最小层号；层号相同时，再用内部的最先分歧关系比较。
<!--ja-->
論理式 `Lim`{.Agda} は二つの極限段階の要素をまず最小レベルで比較し、レベルが等しいときは内部化した最初の相違の関係で比較する。
<!--/-->

<!--en-->

The two keys are joined here, and the second one enters as a **named hypothesis**
rather than a construction: a formula saying that the relation at a numeral held
in a slot puts one slot before another, for two sets **confined to the stage at
that numeral**, together with its two readings against the finite chapter's
`before`{.Agda}. Everything from here on is generic in that description, and the
last section says exactly what discharging it needs. The confinement costs the
two call sites below nothing, because each already carries the level equation of
both sets it compares.

The composition is a disjunction, and its two disjuncts bind different numbers of
levels. The first binds two, one for each side, and compares them by membership,
which is the order on numerals. The second binds **one**, asserts that it is the
level of both sides, and hands the comparison to the relation there. Binding one
numeral rather than two is what keeps an equation between levels out of the
object language, where it would have to be written with the object equality and
converted back.

Reading the disjunction the other way costs one lemma, and it is the one the
order table chapter already isolated for every strict well-order at once: object
disjunction is truncated and the meta comparison is not, so trichotomy is
consulted first, the strict case hands the comparison over untouched, and the
other two cases have absurdity for a goal, where the truncation may be opened.
<!--zh-->

两个键在此连接。第二个键以**具名假设**而非现成构造的形式给出：其中包括一条公式，表达「某个槽位所持数码处的关系把一个槽位排在另一个之前」；被比较的两个集合还须**限制在该数码处的层之内**，并配有相对于有穷一章 `before`{.Agda} 的两条读式。此后的论证都对这条描述保持通用，最后一节再说明实现它所需的条件。这项层限制不会增加下面两个使用处的工作，因为两处都已有被比较集合的层号等式。

接合是一个析取，而它的两支所绑定的层号个数不同。第一支绑两个，每边一个，并按隶属比较它们，那就是数码上的序。第二支绑**一个**，断言它是两边的层号，并把比较交给那里的关系。绑一个数码而不是两个，正是把「层号之间的等式」挡在对象语言之外的办法；否则那个等式就得用对象等词写出、再换回来。

反向读取该析取需要一条引理，即序之表一章已经为每个严格良序隔离出的引理。对象语言的析取带有截断，而元层比较没有截断，因此先按三歧分情形：严格情形直接给出比较；另两种情形的目标是荒谬，所以可以在这些分支中消去截断。
<!--/-->

Perf: the limit stage and its members, sealed where they are built.

```agda
opaque
  limitEl : Limit → S
  limitEl a = fst a , Lset→isL ω ω-ord (fst a) (snd a)

  limitEl-fst : (a : Limit) → fst (limitEl a) ≡ fst a
  limitEl-fst a = refl

  prS : S → S → S
  prS a b = prʟ a b

  prS-fst : (a b : S) → fst (prS a b) ≡ pr (fst a) (fst b)
  prS-fst a b = prʟ-fst a b

pairsBound : Σ[ D ∈ S ] ((u v : Limit) → ⟨ pr (fst u) (fst v) ∈ fst D ⟩)
pairsBound = d .fst , onPair
  where
  ixL : ⟪ Lset ω ⟫ → S
  ixL m = ⟪ Lset ω ⟫↪ m , Lset→isL ω ω-ord (⟪ Lset ω ⟫↪ m)
    (∈∈ₛ {a = ⟪ Lset ω ⟫↪ m} {b = Lset ω} .snd (∈ₛ⟪ Lset ω ⟫↪ m))

  d : Σ[ D ∈ S ] ((p : ⟪ Lset ω ⟫ × ⟪ Lset ω ⟫)
                  → ⟨ prʟ (ixL (fst p)) (ixL (snd p)) ∈ˢ D ⟩)
  d = smallDom (⟪ Lset ω ⟫ × ⟪ Lset ω ⟫) (λ p → prʟ (ixL (fst p)) (ixL (snd p)))

  onPair : (u v : Limit) → ⟨ pr (fst u) (fst v) ∈ fst (d .fst) ⟩
  onPair u v = subst (λ t → ⟨ t ∈ fst (d .fst) ⟩)
    (prʟ-fst (ixL (fu .fst)) (ixL (fv .fst)) ∙ cong₂ pr (fu .snd) (fv .snd))
    (d .snd (fu .fst , fv .fst))
    where
    fu = ∈-asFiber {a = fst u} {b = Lset ω} (snd u)
    fv = ∈-asFiber {a = fst v} {b = Lset ω} (snd v)

strictLimit : (a b : Limit) → ∥ a ≺ˡ b ∥₁ → a ≺ˡ b
strictLimit a b h = decide (SWO.tri∙ limitOrder a b)
  where
  decide : Tri (a ≺ˡ b) (a ≡ b) (b ≺ˡ a) → a ≺ˡ b
  decide (lt k) = k
  decide (eq q) = Empty.rec (PT.rec Empty.isProp⊥
    (λ k → SWO.irr∙ limitOrder b (subst (λ t → t ≺ˡ b) q k)) h)
  decide (gt k) = Empty.rec (PT.rec Empty.isProp⊥
    (λ j → SWO.irr∙ limitOrder a (SWO.trans∙ limitOrder a b a j k)) h)

levelStage : (a : Limit) (k : ℕ) → level a ≡ k → ⟨ fst a ∈ finiteStage k ⟩
levelStage a k q = subst (λ j → ⟨ fst a ∈ Lset (# j) ⟩) q (level-in a)

module Described
  (BeforeAt : ∀ {n} → Fin n → Fin n → Fin n → Formula S n)
  (BeforeAt-in : ∀ {n} (b x y : Fin n) (γ : S ^ n) (m : ℕ)
               → fst (lookup b γ) ≡ # m
               → ⟨ fst (lookup x γ) ∈ finiteStage m ⟩
               → ⟨ fst (lookup y γ) ∈ finiteStage m ⟩
               → ⟨ before m (fst (lookup x γ)) (fst (lookup y γ)) ⟩
               → ⟨ γ ⊨ BeforeAt b x y ⟩)
  (BeforeAt-out : ∀ {n} (b x y : Fin n) (γ : S ^ n) (m : ℕ)
                → fst (lookup b γ) ≡ # m
                → ⟨ fst (lookup x γ) ∈ finiteStage m ⟩
                → ⟨ fst (lookup y γ) ∈ finiteStage m ⟩
                → ⟨ γ ⊨ BeforeAt b x y ⟩
                → ⟨ before m (fst (lookup x γ)) (fst (lookup y γ)) ⟩)
  where
```

Perf: the composed description is sealed where it is built; unsealed, the
separation's condition unfolds it under two binders and does not finish.

```agda
  opaque
    LimitOrdAt : ∀ {n} → Fin n → Fin n → Formula S n
    LimitOrdAt x y =
      ∃̇ ( ∃̇ ( LevelAt (suc zero) (sh2 x)
             ∧̇ ( LevelAt zero (sh2 y) ∧̇ (var (suc zero) ∈̇ var zero) ) ) )
      ∨̇ ∃̇ ( LevelAt zero (suc x)
           ∧̇ ( LevelAt zero (suc y) ∧̇ BeforeAt zero (suc x) (suc y) ) )

  module Order {n : ℕ} (x y : Fin n) (γ : S ^ n)
               (u v : Limit) (ku kv : ℕ)
               (qu : level u ≡ ku) (qv : level v ≡ kv)
               (qx : fst (lookup x γ) ≡ fst u)
               (qy : fst (lookup y γ) ≡ fst v)
               where
    private
      module Lu = Level u ku qu
      module Lv = Level v kv qv

      Split : S → S → Type (ℓ-suc ℓ)
      Split c d = ⟨ (d ∷ c ∷ γ) ⊨ LevelAt (suc zero) (sh2 x) ⟩
                × ( ⟨ (d ∷ c ∷ γ) ⊨ LevelAt zero (sh2 y) ⟩
                  × ⟨ fst c ∈ fst d ⟩ )

      Same : S → Type (ℓ-suc ℓ)
      Same c = ⟨ (c ∷ γ) ⊨ LevelAt zero (suc x) ⟩
             × ( ⟨ (c ∷ γ) ⊨ LevelAt zero (suc y) ⟩
               × ⟨ (c ∷ γ) ⊨ BeforeAt zero (suc x) (suc y) ⟩ )

      split-in : ku < kv → Split (numS ku) (numS kv)
      split-in hlt =
          Lu.LevelAt-in (suc zero) (sh2 x) (numS kv ∷ numS ku ∷ γ)
            (numS-fst ku) qx
        , ( Lv.LevelAt-in zero (sh2 y) (numS kv ∷ numS ku ∷ γ)
              (numS-fst kv) qy
          , subst2 (λ s t → ⟨ s ∈ t ⟩) (sym (numS-fst ku)) (sym (numS-fst kv))
              (#mono ku kv hlt) )

      same-in : (e : level v ≡ level u)
              → ⟨ before (level u) (fst u) (fst v) ⟩ → Same (numS ku)
      same-in e h =
          Lu.LevelAt-in zero (suc x) (numS ku ∷ γ) (numS-fst ku) qx
        , ( Level.LevelAt-in v ku (e ∙ qu) zero (suc y) (numS ku ∷ γ)
              (numS-fst ku) qy
          , BeforeAt-in zero (suc x) (suc y) (numS ku ∷ γ) ku (numS-fst ku)
              (subst (λ t → ⟨ t ∈ finiteStage ku ⟩) (sym qx)
                (levelStage u ku qu))
              (subst (λ t → ⟨ t ∈ finiteStage ku ⟩) (sym qy)
                (levelStage v ku (e ∙ qu)))
              (subst2 (λ s t → ⟨ before ku s t ⟩) (sym qx) (sym qy)
                (subst (λ j → ⟨ before j (fst u) (fst v) ⟩) qu h)) )

      split-out : (c d : S) → Split c d → level u < level v
      split-out c d (hx , (hy , hlt)) = subst2 _<_ (sym qu) (sym qv)
        (#∈#-elim ku kv (subst2 (λ s t → ⟨ s ∈ t ⟩) qc qd hlt))
        where
        qc : fst c ≡ # ku
        qc = Lu.LevelAt-out (suc zero) (sh2 x) (d ∷ c ∷ γ) hx qx
        qd : fst d ≡ # kv
        qd = Lv.LevelAt-out zero (sh2 y) (d ∷ c ∷ γ) hy qy

      same-out : (c : S) → Same c
               → (level v ≡ level u) × ⟨ before (level u) (fst u) (fst v) ⟩
      same-out c (hx , (hy , hb)) = e , below
        where
        qc : fst c ≡ # ku
        qc = Lu.LevelAt-out zero (suc x) (c ∷ γ) hx qx
        qc' : fst c ≡ # kv
        qc' = Lv.LevelAt-out zero (suc y) (c ∷ γ) hy qy
        e : level v ≡ level u
        e = qv ∙ sym (#-inj′ (sym qc ∙ qc')) ∙ sym qu
        xIn : ⟨ fst (lookup x γ) ∈ finiteStage ku ⟩
        xIn = subst (λ t → ⟨ t ∈ finiteStage ku ⟩) (sym qx) (levelStage u ku qu)
        yIn : ⟨ fst (lookup y γ) ∈ finiteStage ku ⟩
        yIn = subst (λ t → ⟨ t ∈ finiteStage ku ⟩) (sym qy)
          (levelStage v ku (e ∙ qu))
        below : ⟨ before (level u) (fst u) (fst v) ⟩
        below = subst (λ j → ⟨ before j (fst u) (fst v) ⟩) (sym qu)
          (subst2 (λ s t → ⟨ before ku s t ⟩) qx qy
            (BeforeAt-out zero (suc x) (suc y) (c ∷ γ) ku qc xIn yIn hb))

    opaque
      unfolding LimitOrdAt

      LimitOrdAt-in : u ≺ˡ v → ⟨ γ ⊨ LimitOrdAt x y ⟩
      LimitOrdAt-in h = decide-in h
        where
        lower-in : ku < kv → ⟨ γ ⊨ LimitOrdAt x y ⟩
        lower-in hlt = ∣ inl ∣ numS ku , ∣ numS kv , split-in hlt ∣₁ ∣₁ ∣₁

        inner-in : (e : level v ≡ level u)
                 → ⟨ before (level u) (fst u) (fst v) ⟩
                 → ⟨ γ ⊨ LimitOrdAt x y ⟩
        inner-in e k = ∣ inr ∣ numS ku , same-in e k ∣₁ ∣₁

        decide-in : Lift {ℓ-zero} {ℓ-suc ℓ} (level u < level v)
                  ⊎ ((level v ≡ level u)
                     × ⟨ before (level u) (fst u) (fst v) ⟩)
                  → ⟨ γ ⊨ LimitOrdAt x y ⟩
        decide-in (inl k)       = lower-in (subst2 _<_ qu qv (lower k))
        decide-in (inr (e , k)) = inner-in e k

      LimitOrdAt-out : ⟨ γ ⊨ LimitOrdAt x y ⟩ → ∥ u ≺ˡ v ∥₁
      LimitOrdAt-out = PT.rec squash₁ decide
        where
        atSplit : (c : S) → Σ[ d ∈ S ] Split c d → ∥ u ≺ˡ v ∥₁
        atSplit c (d , hs) = ∣ inl (lift (split-out c d hs)) ∣₁

        atSame : Σ[ c ∈ S ] Same c → ∥ u ≺ˡ v ∥₁
        atSame (c , hs) = ∣ inr (same-out c hs) ∣₁

        decide : ⟨ γ ⊨ ∃̇ ( ∃̇ ( LevelAt (suc zero) (sh2 x)
                            ∧̇ ( LevelAt zero (sh2 y)
                              ∧̇ (var (suc zero) ∈̇ var zero) ) ) ) ⟩
               ⊎ ⟨ γ ⊨ ∃̇ ( LevelAt zero (suc x)
                         ∧̇ ( LevelAt zero (suc y)
                           ∧̇ BeforeAt zero (suc x) (suc y) ) ) ⟩
               → ∥ u ≺ˡ v ∥₁
        decide (inl h) = PT.rec squash₁
          (λ { (c , hd) → PT.rec squash₁ (atSplit c) hd }) h
        decide (inr h) = PT.rec squash₁ atSame h
```

<!--en-->
## The order, as a set

<!--zh-->
## 那个序，作为一个集合
<!--ja-->
## 順序を集合にする
<!--/-->

<!--en-->
Separation over ordered pairs in `Lset ω`{.Agda} turns `Lim`{.Agda} into
`limitOrderL`{.Agda}, with representation lemmas in both directions.
<!--zh-->
在 `Lset ω`{.Agda} 的有序对上施行分离，把 `Lim`{.Agda} 化为 `limitOrderL`{.Agda}，并给出双向表示引理。
<!--ja-->
`Lset ω`{.Agda} の順序対に分出公理を適用して `Lim`{.Agda} を `limitOrderL`{.Agda} にし、双方向の表現補題を得る。
<!--/-->

<!--en-->

The pairs the order relates are contained in a single set: the members of the
limit stage form a small family of elements of `L` and so do their pairs; the
recursion chapter's bounding lemma confines them all at once. Separation with the
condition below then yields exactly the pairs wanted. The condition is one
existential pair binding the two components, with the pairing described rather
than named, joined to the comparison.

The two representation lemmas are the chapter's main results, and they are stated
in the form the internalization chapter's `Adequacy.Keys`{.Agda} requires: the
same two arguments, the same pairing on the left, and the bundle's own comparison
on the right. Their proofs read the separation's specification in each direction:
the components are recovered by injectivity of the pairing one way, and supplied
by the model's own pairing the other. Reading back also uses the untruncation
lemma, since a membership is a proposition and the comparison is not.
<!--zh-->

与那个序相关的诸对并没有超出单独一个集合：极限层的成员构成 `L` 元素的一个小族，它们的诸对也是；递归那一章的界层引理一举把它们全部限制在内。随后，用下面这条条件作分离，就恰好得到想要的那些对。这条条件由一对存在量词约束两个分量，配对是被描述的而非被点名的，再接上那次比较。

两条表示引理是本章的主要结果，它们按内化那一章的 `Adequacy.Keys`{.Agda} 所要求的形式陈述：同样两个实参、左边同样的配对、右边那个束自己的比较。它们的证明就是把分离的条件分两个方向读出来：一个方向由配对的单射性取回两个分量，另一个方向由模型自身的配对给出它们。读回来还要用到那条脱截断引理，因为隶属是命题而比较不是。
<!--/-->

```agda
  Cond₀ : Formula S 1
  Cond₀ = ∃̇ ( ∃̇ ( prAtL (sh2 zero) (suc zero) zero
                 ∧̇ LimitOrdAt (suc zero) zero ) )
```

Perf: the separation is a description read at constants, so the set it carves is
sealed where it is built.

```agda
  opaque
    codeOrder : S
    codeOrder = hasSeparationL (pairsBound .fst) Cond₀ .fst .fst

    codeOrder-mem : (z : S) → (z ∈ˢ codeOrder)
                  ≡ ((z ∈ˢ pairsBound .fst) ⊓ ((z ∷ []) ⊨ Cond₀))
    codeOrder-mem = hasSeparationL (pairsBound .fst) Cond₀ .fst .snd

  private
    Inner : S → S → S → Type (ℓ-suc ℓ)
    Inner z c d = ⟨ (d ∷ c ∷ z ∷ []) ⊨ prAtL (sh2 zero) (suc zero) zero ⟩
                × ⟨ (d ∷ c ∷ z ∷ []) ⊨ LimitOrdAt (suc zero) zero ⟩

    Outer : S → Type (ℓ-suc ℓ)
    Outer z = Σ[ c ∈ S ] ∥ (Σ[ d ∈ S ] Inner z c d) ∥₁

    cond-in : (z c d : S) → Inner z c d → ⟨ (z ∷ []) ⊨ Cond₀ ⟩
    cond-in z c d hi = ∣ c , ∣ d , hi ∣₁ ∣₁

    cond-out : (z : S) → ⟨ (z ∷ []) ⊨ Cond₀ ⟩ → ∥ Outer z ∥₁
    cond-out z h = h

  codeOrder-fill : (u v : Limit) → u ≺ˡ v
                 → ⟨ pr (fst u) (fst v) ∈ fst codeOrder ⟩
  codeOrder-fill u v h =
    subst (λ t → ⟨ t ∈ fst codeOrder ⟩) qz
      (subst ⟨_⟩ (sym (codeOrder-mem (prS (limitEl u) (limitEl v))))
        (inBound , cond-in (prS (limitEl u) (limitEl v))
                     (limitEl u) (limitEl v) (hpr , hord)))
    where
    qz : fst (prS (limitEl u) (limitEl v)) ≡ pr (fst u) (fst v)
    qz = prS-fst (limitEl u) (limitEl v)
       ∙ cong₂ pr (limitEl-fst u) (limitEl-fst v)

    inBound : ⟨ fst (prS (limitEl u) (limitEl v)) ∈ fst (pairsBound .fst) ⟩
    inBound = subst (λ t → ⟨ t ∈ fst (pairsBound .fst) ⟩) (sym qz)
      (pairsBound .snd u v)

    hpr : ⟨ (limitEl v ∷ limitEl u ∷ prS (limitEl u) (limitEl v) ∷ [])
          ⊨ prAtL (sh2 zero) (suc zero) zero ⟩
    hpr = subst ⟨_⟩ (sym (prAtL-adequate (sh2 zero) (suc zero) zero
      (limitEl v ∷ limitEl u ∷ prS (limitEl u) (limitEl v) ∷ [])))
      (prS-fst (limitEl u) (limitEl v))

    hord : ⟨ (limitEl v ∷ limitEl u ∷ prS (limitEl u) (limitEl v) ∷ [])
          ⊨ LimitOrdAt (suc zero) zero ⟩
    hord = Order.LimitOrdAt-in (suc zero) zero
      (limitEl v ∷ limitEl u ∷ prS (limitEl u) (limitEl v) ∷ [])
      u v (level u) (level v) refl refl (limitEl-fst u) (limitEl-fst v) h

  codeOrder-rep : (u v : Limit)
                → ⟨ pr (fst u) (fst v) ∈ fst codeOrder ⟩ → u ≺ˡ v
  codeOrder-rep u v h = strictLimit u v
    (PT.rec squash₁ atC
      (cond-out (prS (limitEl u) (limitEl v))
        (subst ⟨_⟩ (codeOrder-mem (prS (limitEl u) (limitEl v))) inSet .snd)))
    where
    qz : fst (prS (limitEl u) (limitEl v)) ≡ pr (fst u) (fst v)
    qz = prS-fst (limitEl u) (limitEl v)
       ∙ cong₂ pr (limitEl-fst u) (limitEl-fst v)

    inSet : ⟨ fst (prS (limitEl u) (limitEl v)) ∈ fst codeOrder ⟩
    inSet = subst (λ t → ⟨ t ∈ fst codeOrder ⟩) (sym qz) h

    atD : (c d : S) → Inner (prS (limitEl u) (limitEl v)) c d → ∥ u ≺ˡ v ∥₁
    atD c d (hpr , hord) = Order.LimitOrdAt-out (suc zero) zero
      (d ∷ c ∷ prS (limitEl u) (limitEl v) ∷ []) u v (level u) (level v)
      refl refl (sym (split .fst)) (sym (split .snd)) hord
      where
      qcd : pr (fst u) (fst v) ≡ pr (fst c) (fst d)
      qcd = sym qz
        ∙ subst ⟨_⟩ (prAtL-adequate (sh2 zero) (suc zero) zero
            (d ∷ c ∷ prS (limitEl u) (limitEl v) ∷ [])) hpr
      split : (fst u ≡ fst c) × (fst v ≡ fst d)
      split = pr-inj qcd

    atC : Outer (prS (limitEl u) (limitEl v)) → ∥ u ≺ˡ v ∥₁
    atC (c , hd) = PT.rec squash₁ (λ { (d , hi) → atD c d hi }) hd
```

<!--en-->
## The code slot, filled

<!--zh-->
## 那个为诸码所设的位，已填上
<!--ja-->
## 符号用のスロットを埋める
<!--/-->

<!--en-->
The realized limit order now fills the code-relation slot in the internal name
frame, and its representation lemmas discharge both required readings.
<!--zh-->
实现出的极限序现在用作内部名字框架中的码关系，其表示引理给出所需的两条读式。
<!--ja-->
実現された極限順序が内部の名前フレームにある符号関係のスロットを埋め、その表現補題が必要な二つの読みを満たす。
<!--/-->

<!--en-->

The frame the naming comparison is internalized in takes two relation slots, one
for the codes and one for the parameters, each with the two directions saying what
it holds. The code slot is what this chapter was written for, and here it is
filled: the set is `codeOrder`{.Agda} and the two directions are the two lemmas
just proved, at the same two arguments and with no adapter in between.

The parameter slot stays open, and that is not an omission. It is the order on the
carrier the naming is being done over, which is a parameter of the whole
construction, and the previous part supplies it at every stage. What is filled
here is exactly the half that had no supplier.
<!--zh-->

内化命名比较的那个框架取两个关系位，一个对应诸码、一个对应诸参数，各自带有关于「它持有什么」的两个方向。为诸码所设的那一位正是本章的目标：在此处它由 `codeOrder`{.Agda} 给出，两个方向就是刚证完的那两条引理，实参相同，中间不需要任何转换。

为诸参数所设的那一位尚未确定，而这并非遗漏。它是「命名所依托的那个载体上的序」，是整个构造的一个参数，上一部在每层处都已为它提供取值。本章此处确定的，正是先前没有供给来源的那一半。
<!--/-->

```agda
  module CodeKeys (A : V ℓ) (pA : ⟨ isL A ⟩) (w : SWO ⟪ A ⟫) where
    private
      module Ad = Adequacy A pA w

    open SWO w using () renaming ( _<∙_ to _≺ₚ_ )

    module AtParams (Ps : S)
      (Prep : (a b : ⟪ A ⟫) → ⟨ pr (Ad.ix a) (Ad.ix b) ∈ fst Ps ⟩ → a ≺ₚ b)
      (Pfill : (a b : ⟪ A ⟫) → a ≺ₚ b → ⟨ pr (Ad.ix a) (Ad.ix b) ∈ fst Ps ⟩)
      where
      open Ad.Keys codeOrder Ps codeOrder-rep codeOrder-fill Prep Pfill public
```

<!--en-->
## What is left, named exactly

<!--zh-->
## 剩下什么，点准了名
<!--ja-->
## 残る仮定を正確に述べる
<!--/-->

<!--en-->
After fixing the code relation, the remaining adequacy obligations are isolated
as the two directions relating the object-language step to the meta step.
<!--zh-->
固定码关系后，余下的充分性义务被准确隔离为对象语言步进与元步进之间的两个方向。
<!--ja-->
符号関係を固定した後に残る妥当性の義務を、対象言語のステップとメタ言語のステップを結ぶ二方向として正確に切り出す。
<!--/-->

<!--en-->

One hypothesis of `Described`{.Agda} is open, and it is the whole of what stands
between this chapter and an unconditional theorem: a formula `BeforeAt`{.Agda}
saying that the earliest-disagreement order at the numeral held in one slot puts
a second slot before a third, for two sets confined to the stage at that
numeral, together with its two readings against the finite chapter's
`before`{.Agda}.

Discharging it is one thing and not several, and the shape is settled. The
relation at a numeral is the value of a recursion along the numerals, so what has
to be described is an **approximation**, a set recording at each numeral below its
domain the relation there, exactly as the tower and the order table are described:
a graph quantifying over approximations, a value lemma pinning every value an
approximation records, and the approximation at each numeral exhibited on the meta
side. Two things make it less laborious here than either earlier description. The
index is a member of `ωʟ`{.Agda}, a set, so the outer induction is on a natural number and
the class-collection half of the hierarchy chapter does not arise. And the step is
already written: `PrecedesAt`{.Agda} is the recursion's step condition, generic in
the slot the previous relation is held in, which is exactly the form a graph must
consult it in.

Two things make it more laborious. The value at a numeral is a relation rather than a
stage, so each step is a separation over the pairs of a finite stage rather than a
definable powerset; and the previous relation enters a slot inside the step, so
it must appear as a variable together with its defining equation and never as an
application, on pain of the restriction that Law 1 names.
<!--zh-->

`Described`{.Agda} 还有一条假设未确定，而它就是本章与一条无条件定理之间仅剩的距离：一条公式 `BeforeAt`{.Agda}，说「某个槽位所持有的数码处、按最先分歧处的那个序，把第二个槽位排在第三个之前」，其中被比较的两个集合限制在该数码处的层之内；这对应有穷那一章的 `before`{.Agda} 的两条读式。

兑现它是一件事而不是几件，其形式已经确定。某个数码处的关系是沿诸数码的一次递归的取值，故要被描述的是一个**逼近**：一个集合，在它定义域以下的每个数码处记录那里的关系；其方式与塔、与序之表被描述的方式完全相同：一个对诸逼近作量化的图、一条确认逼近所记录的每个取值的值引理，以及在元层面把每个数码处的逼近直接给出。有两件事使它比前两处描述都更省力。索引是 `ωʟ`{.Agda} 的成员，而 `ωʟ`{.Agda} 是个集合，故外层归纳是对一个自然数作的，层级那一章涉及真类收集的那部分论证根本不会出现。而那一步已经写好：`PrecedesAt`{.Agda} 就是这场递归的步进条件，且对「上一个关系被存放在哪一位」保持通用，而这正是一个图使用它时所要求的形式。

也有两件事使它更费力。某个数码处的取值是关系而非层，故每一步是在一个有穷层的诸对之上作分离，而不是取可定义幂集；而且上一个关系要进入那一步内部的一个槽位，所以它必须以变元身份连同自己的定义等式一起出现，绝不可以是一个应用，否则就会违反第一条定律所指出的那条限制。
<!--/-->

<!--en-->
## Recap

<!--zh-->
## 小结
<!--ja-->
## まとめ
<!--/-->

<!--en-->
The chapter realizes `limitOrder`{.Agda} as `limitOrderL`{.Agda}, proves its two
membership readings, and uses them to close the code-order side of the frame.
<!--zh-->
本章把 `limitOrder`{.Agda} 实现为 `limitOrderL`{.Agda}，证明其两条隶属读式，并据此闭合框架的码序一侧。
<!--ja-->
本章は `limitOrder`{.Agda} を `limitOrderL`{.Agda} として実現し、所属についての二つの読みを証明して、フレームの符号順序側を閉じる。
<!--/-->

<!--en-->

`LevelAt`{.Agda} is the level said in the object language, three conjuncts and no
constant but `ω`: the slot holds a member of `ω`, the tower there holds the set,
and no smaller numeral's tower does. `LevelAt-in`{.Agda} and
`LevelAt-out`{.Agda} are its two readings at variable slots in a variable
environment, with the level itself appearing as a **variable numeral** carrying its
defining equation, which is the difference between 145 s and 1.8 s: the level is a
classical accessibility recursion, and conversion at a slot exposes it.

`PrecedesAt`{.Agda} is one step of the earliest-disagreement comparison with
nothing concrete in it: the base relation and the base stage are held in slots, so
the description can stand where the relation is the value of a recursion.
`PrecedesAt-out`{.Agda} and `PrecedesAt-in`{.Agda} are its two readings against
`precedes`{.Agda}, one bookkeeping step apart, since a witness crossing between
the languages acquires or sheds its constructibility proof, and the pair carrying
that proof is sealed.

`strictLimit`{.Agda} takes the truncation off a comparison, by splitting on
trichotomy before eliminating anything. `Described`{.Agda} is the frame:
`LimitOrdAt`{.Agda} joins the two keys as a disjunction whose first disjunct binds
two levels and compares them by membership and whose second binds **one**, so no
equation between levels ever enters the object language;
`Order.LimitOrdAt-in`{.Agda} and `Order.LimitOrdAt-out`{.Agda} are its two
readings against `limitOrder`{.Agda}'s own comparison.

`pairsBound`{.Agda} confines every pair the order could relate, by the recursion
chapter's bounding lemma over the small family of members of the limit stage, and
`codeOrder`{.Agda} is the separation of `Cond₀`{.Agda} out of it, sealed where it
is built. `codeOrder-fill`{.Agda} and `codeOrder-rep`{.Agda} are the two
representation lemmas, and `CodeKeys.AtParams`{.Agda} is the internalization
chapter's `Adequacy.Keys`{.Agda} with its **code slot filled by them**, at the
same two arguments and with no adapter.

Two measurements are recorded, and each reflects the same law seen earlier.
A case split whose scrutinee is a **bundle's** comparison and whose conclusion is a
satisfaction does not finish; written on an explicit sum with the branches as
named helpers its cost is negligible (past 300 s against 2.4 s). And the composed
description must be **sealed where it is built**: the separation's condition
unfolds it under two binders, and unsealed that reduction does not finish either
(past 300 s against 2.7 s), which is the same law the previous chapter measured at
160 s per reading.
<!--zh-->

`LevelAt`{.Agda} 是层号在对象语言中的说法，三个合取项，且除 `ω` 外不点名任何常元：该位置持有 `ω` 的一个成员、那里的塔含有这个集合、而没有更小数码的塔含有它。`LevelAt-in`{.Agda} 与 `LevelAt-out`{.Agda} 是它落在变元环境的变元位上的两条读式，而层号自身以**变元数码**的身份出现，并携带它的定义等式；这正是 145 秒与 1.8 秒之差的来源：层号是一场经典可及性递归，而槽位处的转换检查会把它揭示出来。

`PrecedesAt`{.Agda} 只描述最先分歧处的一步比较，本身不含任何具体对象：基底关系与基底层都保留为槽位参数，因此它也适用于「关系是某场递归之取值」的情形。`PrecedesAt-out`{.Agda} 与 `PrecedesAt-in`{.Agda} 是它相对于 `precedes`{.Agda} 的两条读式；二者只相差一步核对，因为在两种语言之间转换的见证需要补上或去掉可构造性证明，而携带该证明的对已经封装。

`strictLimit`{.Agda} 消去一次比较上的截断，方法是在消去任何内容之前先按三歧分情形。`Described`{.Agda} 是所用框架：`LimitOrdAt`{.Agda} 以析取连接两个键，第一支绑定两个层号并按隶属比较，第二支只绑定**一个**层号，因此层号之间的等式不进入对象语言。`Order.LimitOrdAt-in`{.Agda} 与 `Order.LimitOrdAt-out`{.Agda} 是它相对于 `limitOrder`{.Agda} 自身比较的两条读式。

`pairsBound`{.Agda} 为该序可能关联的每一个对给出集合界，依据是将递归一章的界层引理用于极限层诸成员构成的小族。`codeOrder`{.Agda} 用 `Cond₀`{.Agda} 从这个界中分离出来，并在构造之处封装。`codeOrder-fill`{.Agda} 与 `codeOrder-rep`{.Agda} 是两条表示引理；`CodeKeys.AtParams`{.Agda} 就是内化一章的 `Adequacy.Keys`{.Agda}，其**为诸码所设的位由它们填上**，实参相同，中间无须转换。

记录两次实测，二者都体现了前面已见过的同一条规律。一次分情形：若被检者是某个**束**的比较、而其结论是一个满足关系，就跑不完；把它写在一个显式的和上、诸支取作具名辅助，代价便可以忽略 (超过 300 秒对 2.4 秒)。而那条接合起来的描述必须**在造出之处封印**：分离的那条条件会在两层绑定之下把它展开，不封印时那次归约同样跑不完 (超过 300 秒对 2.7 秒)，与上一章实测的每条读式 160 秒是同一条规律。
<!--/-->
