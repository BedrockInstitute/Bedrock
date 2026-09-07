<!--en-->
# Canonical names for successor-stage members

A member of a successor stage is determined by a formula and finitely many parameters from the preceding stage. This chapter packages that data as a name, proves that every member has one, and orders all names so that a least representative can be chosen.
<!--zh-->
# 后继阶段成员的典范名字

后继阶段的成员由一条公式及前一阶段中的有限多个参数确定。本章把这些数据封装成名字，证明每个成员都有名字，再良序化所有名字，以便选出最小代表。
<!--ja-->
# 後者段階の要素の正準な名前

後者段階の要素は、一つの論理式と直前の段階から取った有限個のパラメータによって定まる。本章ではそのデータを名前としてまとめ、すべての要素が名前をもつことを示し、最小の代表を選べるよう名前全体を整列する。
<!--/-->

<!--en-->
A member of a successor stage is a definable subset of the stage below, and the
previous chapters have said what that means twice over: once as a formula with
parameters drawn from that stage, and once, after the parameters left the syntax,
as a **parameter-free formula together with a vector of parameters**. The second
form is the one that can be compared. Its formula is a finite piece of syntax, so
its code is a hereditarily finite set and has already appeared at the tower's
limit level, where the previous chapter well-ordered everything; its parameters
are members of the stage below, which the construction ahead will have
well-ordered by then. A **name** is that pair, with the arity between them, and
this chapter builds it, shows every member of the successor stage has one, and
well-orders the names.

The order is a three-key lexicographic comparison, written out. Nothing here is
an instance of a general order on dependent sums, and that is deliberate: such a
thing would have to carry a family of orders indexed by the first key and prove
its four laws in that generality, which is a larger theorem than the one wanted,
for a single use. The three keys are named, and each is compared by an order that
already exists.
<!--zh-->
后继阶段的成员就是下面那个阶段的可定义子集，而前几章已经把这句话说了两遍：一遍说成带参数的公式，参数取自那个阶段；另一遍在参数离开语法之后，说成**一条无参公式配上一个参数向量**。可比较的是后一种形式。它的公式是一段有穷的语法，故它的码是遗传有穷集，早已现身于塔的极限层，而上一章正是在那里把一切良序化了；它的参数是下面那个阶段的成员，而到那时后续构造已经把那个阶段良序化。**名字**就是这样一对，中间夹着元数；本章造出它，证明后继阶段的每个成员都有一个，并把诸名字良序化。

那个序是一次写开了的三键字典序比较。此处没有任何东西是「依值和上的一般序」的实例，而这是有意为之：那样一件东西得携带一族以第一个键为索引的序，并在那种一般性下证出它的四条定律，而这比所要的定理更大，却只用一次。三个键各有其名，而每个键都由一个已然存在的序来比较。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module L.Choice.CanonicalNames {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using
  ( Term; con; var
  ; Formula; _∈̇_; _≐_; _∧̇_; _∨̇_; _⇒̇_; ⊥̇; ∃̇_; ∀̇_; ∀̇∈; ∃̇∈ )
import FOL.Semantics
open import FOL.Manipulation.ConstantMapping using ( mapTm; embed )
open import FOL.Manipulation.Relabelling using ( embed-⊨ )
open import FOL.Manipulation.ConstantOccurrences using ( countFo; constantsFo )
open import FOL.Manipulation.ParameterAbstraction using ( absFo; ⊨-abs₁ )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Coding {ℓ} using ( pr; module VCode )
open import V.Model {ℓ} using ( self∈sucV )
open import L.Constructible {ℓ}
  using ( Lset; Lset-mono; 𝒟ₒ; 𝒟ₒ-inv )
open import L.Definability {ℓ} using ( module DefOf )
open import L.Ordinal {ℓ} using ( numeral-ord; #∈ω )
open import L.Ordinal.Stages {ℓ} lem using ( ord∈Lset-suc )
open import L.Axioms.Basic {ℓ} using ( pr∈Lset-suc )
open import L.Choice.FiniteStageOrders {ℓ} lem using ( Limit; inSome; limitOrder; Tri-map )
open import L.WellOrder.Base {ℓ-suc ℓ}
  using ( Tri; lt; eq; gt; SWO; IsLeast; leastOf )

open import Cubical.Foundations.Prelude using ( toPathP )
open import Cubical.Foundations.Transport using ( constSubstCommSlice )
open import Cubical.Foundations.Equiv using ( equivFun; invEq )
open import Cubical.Functions.Embedding using ( isEmbedding→Inj )
open import Cubical.Functions.Logic using ( ⇔toPath )
open import Cubical.Data.Nat using ( _+_; +-comm )
open import Cubical.Data.Nat.Order using ( _<_; <-trans; ¬m<m; <-wellfounded; _≟_ )
import Cubical.Data.Nat.Order as NatOrder
open import Cubical.Data.FinData using ( toℕ )
open import Cubical.Data.Sigma using ( ΣPathP )
open import Cubical.Data.Sum using ( _⊎_; inl; inr )
open import Cubical.Data.Vec using ( map )
open import Cubical.Induction.WellFounded
  using ( Acc; acc; WellFounded; module WFI )
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁ )
open import Cubical.HITs.CumulativeHierarchy.Base using ( sett )
open import Cubical.HITs.CumulativeHierarchy.Properties
  using ( ⟪_⟫; ⟪_⟫↪; isEmb⟪_⟫↪ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet )
open InfinitySet using ( #_; ω )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ
```

<!--en-->
## A parameter-free code is hereditarily finite
<!--zh-->
## 无参的码是遗传有穷的
<!--ja-->
## パラメータなしコードは遺伝的有限である
<!--/-->

<!--en-->
The first key of a name is the code of its parameter-free formula. Such a finite syntax code is hereditarily finite, so it already belongs to the limit stage where the established well-order can compare it.
<!--zh-->
名字的第一个键是其无参公式的码。这样的有限语法码是遗传有穷的，因此早已属于极限阶段，可以由既有良序比较。
<!--ja-->
名前の第一の鍵は、パラメータなし論理式のコードである。この有限な構文コードは遺伝的有限なので、既に極限段階に属し、そこで構成済みの整列順序によって比較できる。
<!--/-->

<!--en-->
The first key wants the formula as a member of `Lset ω`{.Agda}, so the first
thing to establish is that its code is one. Read the coding chapter's clauses and
nothing else is used: a numeral for the tag, a numeral for a de Bruijn index, and
Kuratowski pairs holding the parts. The one construction that could leave the
finite world is the constant clause, which puts an arbitrary set into the code,
and a parameter-free formula has no constants at all.

So two closure facts suffice, and both are lifted rather than re-derived: the
previous chapter's `inSome`{.Agda} says a member of `Lset ω`{.Agda} has appeared
by some finite stage, and the basic-axioms chapter's `pr∈Lset-suc`{.Agda} says a
Kuratowski pair of two members of a stage appears two stages later. Climbing from
one finite stage to a later one is monotonicity applied along the numerals'
successors, which is the only recursion this section runs.
<!--zh-->
第一个键要把公式当作 `Lset ω`{.Agda} 的成员，故首先要立的就是「它的码是这样一个成员」。读一遍编码那一章的诸子句便知别无他物：一个数码作标签，一个数码作 de Bruijn 序号，以及装着各部分的 Kuratowski 对。唯一可能走出有穷世界的构造是常元那一条，它把一个任意集合放进码里，而无参公式压根没有常元。

于是两条封闭性事实就够了，而两条都是搬来的、不是重推的：上一章的 `inSome`{.Agda} 说 `Lset ω`{.Agda} 的成员到某个有穷阶段为止已经现身，而基本公理那一章的 `pr∈Lset-suc`{.Agda} 说两个阶段成员的 Kuratowski 对在两阶之后现身。从一个有穷阶段爬到更晚的阶段，是单调性沿着数码的后继逐级施用，而这也是本节所跑的唯一一场递归。
<!--/-->

```agda
private
  AtStage : S → Type (ℓ-suc ℓ)
  AtStage x = Σ[ k ∈ ℕ ] ⟨ x ∈ˢ Lset (# k) ⟩

  raiseTo : (x : S) (d k : ℕ) → ⟨ x ∈ˢ Lset (# k) ⟩ → ⟨ x ∈ˢ Lset (# (d + k)) ⟩
  raiseTo x zero    k h = h
  raiseTo x (suc d) k h = Lset-mono (self∈sucV (# (d + k))) (raiseTo x d k h)

numeral∈limit : (k : ℕ) → ⟨ (# k) ∈ˢ Lset ω ⟩
numeral∈limit k = Lset-mono (#∈ω (suc k)) (ord∈Lset-suc (# k) (numeral-ord k))

pr∈limit : (x y : S) → ⟨ x ∈ˢ Lset ω ⟩ → ⟨ y ∈ˢ Lset ω ⟩
         → ⟨ pr x y ∈ˢ Lset ω ⟩
pr∈limit x y hx hy = PT.rec (snd (pr x y ∈ˢ Lset ω))
  (λ atX → PT.rec (snd (pr x y ∈ˢ Lset ω)) (both atX) (inSome y hy))
  (inSome x hx)
  where
  both : AtStage x → AtStage y → ⟨ pr x y ∈ˢ Lset ω ⟩
  both (j , hj) (k , hk) = Lset-mono (#∈ω (suc (suc (k + j))))
    (pr∈Lset-suc (# (k + j)) x y (raiseTo x k j hj)
      (subst (λ n → ⟨ y ∈ˢ Lset (# n) ⟩) (+-comm j k) (raiseTo y j k hk)))

tag∈limit : (k : ℕ) (x : S) → ⟨ x ∈ˢ Lset ω ⟩ → ⟨ VCode.mkTag k x ∈ˢ Lset ω ⟩
tag∈limit k x h = pr∈limit (# k) x (numeral∈limit k) h
```

<!--en-->
The induction itself is then twelve one-line clauses, ten for the formula
constructors and two for the terms, and the constant clause is discharged by the
empty type's eliminator. Nothing about the tag numbers matters beyond their being
numerals.
<!--zh-->
归纳本身于是是十二条一行的子句，十条对应公式的构造子，两条对应词项，而常元那一条由空类型的消去子打发。标签的编号除了「是数码」之外无关紧要。
<!--/-->

```agda
codeTm∈limit : ∀ {n} (t : Term (⊥* {ℓ}) n)
             → ⟨ VCode.⌜ mapTm Empty.rec* t ⌝ᵗ ∈ˢ Lset ω ⟩
codeTm∈limit (con c) = Empty.rec* c
codeTm∈limit (var i) = tag∈limit 1 (# (toℕ i)) (numeral∈limit (toℕ i))

code∈limit : ∀ {n} (χ : Formula (⊥* {ℓ}) n) → ⟨ VCode.⌜ embed χ ⌝ ∈ˢ Lset ω ⟩
code∈limit (t ∈̇ u)  = tag∈limit 0 _ (pr∈limit _ _ (codeTm∈limit t) (codeTm∈limit u))
code∈limit (t ≐ u)  = tag∈limit 1 _ (pr∈limit _ _ (codeTm∈limit t) (codeTm∈limit u))
code∈limit (φ ∧̇ ψ)  = tag∈limit 2 _ (pr∈limit _ _ (code∈limit φ) (code∈limit ψ))
code∈limit (φ ∨̇ ψ)  = tag∈limit 3 _ (pr∈limit _ _ (code∈limit φ) (code∈limit ψ))
code∈limit (φ ⇒̇ ψ)  = tag∈limit 4 _ (pr∈limit _ _ (code∈limit φ) (code∈limit ψ))
code∈limit ⊥̇        = tag∈limit 5 _ (numeral∈limit 0)
code∈limit (∃̇ φ)    = tag∈limit 6 _ (code∈limit φ)
code∈limit (∀̇ φ)    = tag∈limit 7 _ (code∈limit φ)
code∈limit (∀̇∈ t φ) = tag∈limit 8 _ (pr∈limit _ _ (codeTm∈limit t) (code∈limit φ))
code∈limit (∃̇∈ t φ) = tag∈limit 9 _ (pr∈limit _ _ (codeTm∈limit t) (code∈limit φ))
```

<!--en-->
The pair of the code with that membership is what the first key compares. One
small fact travels with it, proved once by path induction: moving a formula from
one arity to an equal one leaves its code alone. The trichotomy below needs
exactly this, at the point where two names have been found to have the same
arity.
<!--zh-->
第一个键所比较的，是「码与那条隶属」之对。有一件小事随它同行，并由一次路径归纳证一遍：把一条公式从一个元数搬到与之相等的元数，不动它的码。下面的三歧恰在「两个名字被发现元数相同」之处需要这一条。
<!--/-->

```agda
limitCode : ∀ {n} → Formula (⊥* {ℓ}) n → Limit
limitCode χ = VCode.⌜ embed χ ⌝ , code∈limit χ

code-shift : {i j : ℕ} (e : i ≡ j) (χ : Formula (⊥* {ℓ}) (suc i))
           → VCode.⌜ embed (subst (λ k → Formula (⊥* {ℓ}) (suc k)) e χ) ⌝
           ≡ VCode.⌜ embed χ ⌝
code-shift e χ = sym (constSubstCommSlice
  (λ k → Formula (⊥* {ℓ}) (suc k)) S (λ _ ψ → VCode.⌜ embed ψ ⌝) e χ)

```

<!--en-->
## A parameter-free formula is recovered from its image
<!--zh-->
## 无参公式可从它的像还原
<!--ja-->
## パラメータなし論理式はその像から復元できる
<!--/-->

<!--en-->
Coding does not identify two different parameter-free formulas. Injectivity follows by decoding the hereditarily finite image and then using injectivity of the syntax encoding.
<!--zh-->
编码不会把两条不同的无参公式等同起来。先从遗传有穷的像解码，再用语法编码的单射性，即得这一单射性。
<!--ja-->
符号化によって異なるパラメータなし論理式が同一視されることはない。遺伝的有限な像を復号し、構文の符号化の単射性を使えば、この単射性が得られる。
<!--/-->

<!--en-->
Two names with the same first key must turn out to be built from the same
formula, or the comparison would rank two different names as neither below the
other and equal to nothing. The coding chapter proved its own injectivity, but it
proved it over the working syntax, whose constant domain is the carrier; what is
needed here is injectivity for the parameter-free formulas, which reach that
syntax through `embed`{.Agda}.

The gap is closed by an **erasure** running the other way, and the erasure can be
crude because it only has to be a left inverse on the parameter-free formulas. A
constant is sent to the variable of index zero, which is available because every
formula in sight has at least one free variable, and every other clause is the
identity on the constructor. On a formula that had no constants to begin with the
erasure changes nothing, one clause at a time, and injectivity is then three
compositions.
<!--zh-->
第一个键相同的两个名字，必须结果由同一条公式造出，否则那次比较就会把两个不同的名字判为「互不更小、又不与任何东西相等」。编码那一章证过它自己的单射性，但它是对工作语法证的，那里的常元域是载体；此处所需的是无参公式的单射性，而无参公式经 `embed`{.Agda} 抵达那套语法。

这道缝由一场反向的**抹除**填平，而抹除可以粗糙，因为它只需在无参公式上作左逆。常元被送到序号为零的变量，那个变量总在，因为视野中的每条公式至少有一个自由变量；其余每条子句都是构造子上的恒等。对一条本来就没有常元的公式，抹除逐条子句什么也没改，于是单射性就是三次复合。
<!--/-->

```agda
private
  eraseTm : ∀ {n} → Term S (suc n) → Term (⊥* {ℓ}) (suc n)
  eraseTm (con x) = var zero
  eraseTm (var i) = var i

  eraseFo : ∀ {n} → Formula S (suc n) → Formula (⊥* {ℓ}) (suc n)
  eraseFo (t ∈̇ u)  = eraseTm t ∈̇ eraseTm u
  eraseFo (t ≐ u)  = eraseTm t ≐ eraseTm u
  eraseFo (φ ∧̇ ψ)  = eraseFo φ ∧̇ eraseFo ψ
  eraseFo (φ ∨̇ ψ)  = eraseFo φ ∨̇ eraseFo ψ
  eraseFo (φ ⇒̇ ψ)  = eraseFo φ ⇒̇ eraseFo ψ
  eraseFo ⊥̇        = ⊥̇
  eraseFo (∃̇ φ)    = ∃̇ eraseFo φ
  eraseFo (∀̇ φ)    = ∀̇ eraseFo φ
  eraseFo (∀̇∈ t φ) = ∀̇∈ (eraseTm t) (eraseFo φ)
  eraseFo (∃̇∈ t φ) = ∃̇∈ (eraseTm t) (eraseFo φ)

  eraseTm-embed : ∀ {n} (t : Term (⊥* {ℓ}) (suc n))
                → eraseTm (mapTm Empty.rec* t) ≡ t
  eraseTm-embed (con c) = Empty.rec* c
  eraseTm-embed (var i) = refl

  eraseFo-embed : ∀ {n} (χ : Formula (⊥* {ℓ}) (suc n)) → eraseFo (embed χ) ≡ χ
  eraseFo-embed (t ∈̇ u)  = cong₂ _∈̇_ (eraseTm-embed t) (eraseTm-embed u)
  eraseFo-embed (t ≐ u)  = cong₂ _≐_ (eraseTm-embed t) (eraseTm-embed u)
  eraseFo-embed (φ ∧̇ ψ)  = cong₂ _∧̇_ (eraseFo-embed φ) (eraseFo-embed ψ)
  eraseFo-embed (φ ∨̇ ψ)  = cong₂ _∨̇_ (eraseFo-embed φ) (eraseFo-embed ψ)
  eraseFo-embed (φ ⇒̇ ψ)  = cong₂ _⇒̇_ (eraseFo-embed φ) (eraseFo-embed ψ)
  eraseFo-embed ⊥̇        = refl
  eraseFo-embed (∃̇ φ)    = cong ∃̇_ (eraseFo-embed φ)
  eraseFo-embed (∀̇ φ)    = cong ∀̇_ (eraseFo-embed φ)
  eraseFo-embed (∀̇∈ t φ) = cong₂ ∀̇∈ (eraseTm-embed t) (eraseFo-embed φ)
  eraseFo-embed (∃̇∈ t φ) = cong₂ ∃̇∈ (eraseTm-embed t) (eraseFo-embed φ)

code-inj : ∀ {n} (χ ψ : Formula (⊥* {ℓ}) (suc n))
         → VCode.⌜ embed χ ⌝ ≡ VCode.⌜ embed ψ ⌝ → χ ≡ ψ
code-inj χ ψ e = sym (eraseFo-embed χ)
               ∙ cong eraseFo (VCode.⌜⌝-inj (embed χ) (embed ψ) e)
               ∙ eraseFo-embed ψ
```

<!--en-->
## The naming data
<!--zh-->
## 命名数据
<!--ja-->
## 名前を構成するデータ
<!--/-->

<!--en-->
A name records an arity, a parameter-free formula with one output variable, and a parameter vector of that arity. Its denotation is the subset of the stage cut out by the formula under that environment.
<!--zh-->
一个名字记录元数、一条多出一个输出变量的无参公式，以及相应长度的参数向量。它所指称的是该公式在这个环境下从阶段中刻出的子集。
<!--ja-->
名前は、アリティ、一つの出力変数を余分にもつパラメータなし論理式、そのアリティのパラメータ列を記録する。その指示対象は、この環境で論理式が段階から切り出す部分集合である。
<!--/-->

<!--en-->
Everything below is relative to one set `A`, the stage the names are written
over, and on one well-order of that stage's members, so the chapter works in a
module `Naming A w`. A **name** is an arity, a parameter-free formula with one
more free variable than that, and a vector of that many parameters drawn from
`A`'s small member type. The extra variable is the one a subset is carved by;
the rest receive the parameters, and the first key is read off the formula at
once.
<!--zh-->
以下一切都相对于一个集合 `A`，即诸名字所依据写出的那个阶段，也相对于那个阶段的成员上的一个良序，故本章在模块 `Naming A w` 中工作。一个**名字**是一个元数、一条比该元数多一个自由变量的无参公式，以及一个由 `A` 的小成员类型取出的、长度为该元数的参数向量。多出来的那个变量正是子集被刻出时所用的那个；其余的接收诸参数，而第一个键当即从那条公式读出。
<!--/-->

Perf: the naming data are definitions of this module, not of another.

```agda
module Naming (A : S) (w : SWO ⟪ A ⟫) where
  module DA = DefOf A
  open DA using ( _⊨ᵐ_ )

  Name : Type ℓ
  Name = Σ[ k ∈ ℕ ] (Formula (⊥* {ℓ}) (suc k) × Vec ⟪ A ⟫ k)

  arity : Name → ℕ
  arity a = a .fst

  formula : (a : Name) → Formula (⊥* {ℓ}) (suc (arity a))
  formula a = a .snd .fst

  params : (a : Name) → Vec ⟪ A ⟫ (arity a)
  params a = a .snd .snd

  codeOf : Name → Limit
  codeOf a = limitCode (formula a)
```

<!--en-->
What a name denotes is the subset of `A` its formula selects when the parameters
are supplied in the **environment**, which is where the previous chapter put
them. The environment is one member followed by the parameters, all read into the
restricted carrier by the definable powerset's own constant interpretation, and
the satisfaction is the inner one, so the denotation is a subset of `A` carved by
exactly the notion `Def A`{.Agda} was defined by. Smallness is inherited: the
inner satisfaction at any formula and any environment is small, so the subset is
a `sett`{.Agda} over a small index type with no resizing spent.
<!--zh-->
一个名字所**指称**的，是当参数由**环境**供给时、它的公式所选中的 `A` 的子集，而上一章正是把参数放在了那里。环境是一个成员后接诸参数，全部经可定义幂集自家的常元解释读进限制载体，而满足取内层那一个；于是指称就是由「`Def A`{.Agda} 据以定义的那个概念」刻出的 `A` 的子集，分毫不差。小性是继承来的：任何公式在任何环境处的内层满足皆小，故那个子集是小索引类型上的一个 `sett`{.Agda}，降层分文未花。
<!--/-->

```agda
  private
    module SemM = FOL.Semantics (hPropAlgebra (ℓ-suc ℓ)) DA.𝒮M
    open SemM using ( _^_ )

    subsetOf : (⟪ A ⟫ → hProp ℓ) → S
    subsetOf P = sett (Σ[ m ∈ ⟪ A ⟫ ] ⟨ P m ⟩) (λ p → ⟪ A ⟫↪ (p .fst))

    ⟪⟫↪-inj : {m' m : ⟪ A ⟫} → ⟪ A ⟫↪ m' ≡ ⟪ A ⟫↪ m → m' ≡ m
    ⟪⟫↪-inj {m'} {m} = isEmbedding→Inj isEmb⟪ A ⟫↪ m' m

  environment : (a : Name) → ⟪ A ⟫ → DA.SM ^ (suc (arity a))
  environment a m = DA.ι m ∷ map DA.ι (params a)

  satAt : (a : Name) → ⟪ A ⟫ → hProp ℓ
  satAt a m = DA.⊨ᵐ-small (embed (formula a)) (environment a m) .fst

  denote : Name → S
  denote a = subsetOf (satAt a)
```

<!--en-->
The specification says the word "denotes" literally: a member of `A` belongs to
the denotation exactly when the inner world satisfies the name's formula at the
environment the name prescribes. The compression to a small proposition was only
an encoding, and the equivalence carries it back.
<!--zh-->
规格把「指称」二字逐字兑现：`A` 的一个成员属于该指称，当且仅当内层世界在该名字所规定的环境处满足它的公式。压缩成小命题只是编码，而那个等价把它原样送回。
<!--/-->

```agda
  denote-mem : (a : Name) (m : ⟪ A ⟫)
             → (⟪ A ⟫↪ m ∈ˢ denote a) ≡ (environment a m ⊨ᵐ embed (formula a))
  denote-mem a m = ⇔toPath fwd bwd
    where
    decode = DA.⊨ᵐ-small (embed (formula a)) (environment a m)
    fwd : ⟨ ⟪ A ⟫↪ m ∈ˢ denote a ⟩ → ⟨ environment a m ⊨ᵐ embed (formula a) ⟩
    fwd = PT.rec (snd (environment a m ⊨ᵐ embed (formula a)))
      (λ { ((m' , h) , q) →
        invEq (decode .snd) (subst (λ v → ⟨ satAt a v ⟩) (⟪⟫↪-inj q) h) })
    bwd : ⟨ environment a m ⊨ᵐ embed (formula a) ⟩ → ⟨ ⟪ A ⟫↪ m ∈ˢ denote a ⟩
    bwd h = ∣ (m , equivFun (decode .snd) h) , refl ∣₁
```

<!--en-->
## Every member of the successor stage has a name
<!--zh-->
## 后继阶段的每个成员都有名字
<!--ja-->
## 後者段階の各要素は名前をもつ
<!--/-->

<!--en-->
The definable-power-set specification supplies a formula with constants for each successor-stage member. Abstracting those constants produces the parameter-free formula and parameter vector that form its name.
<!--zh-->
可定义幂集的规格为后继阶段的每个成员给出一条带常元的公式。把这些常元抽象出去，就得到构成其名字的无参公式与参数向量。
<!--ja-->
定義可能冪集合の仕様は、後者段階の各要素に定数付き論理式を与える。その定数を抽象すると、名前を構成するパラメータなし論理式とパラメータ列が得られる。
<!--/-->

<!--en-->
A member of `𝒟ₒ A`{.Agda} is, by that operator's own specification, merely a
subset definable by a formula of one free variable with constants from `A`; and
the previous chapter turned such a formula into a parameter-free one of higher
arity together with the constants it mentioned. Reading the second off the first
is the whole of naming, and it is a function.
<!--zh-->
按那个算子自己的规格，`𝒟ₒ A`{.Agda} 的成员仅仅是「由带 `A` 中常元的单变量公式可定义的子集」；而上一章把这样一条公式变成了一条元数更高的无参公式，外加它所提到的诸常元。从前者读出后者，就是命名的全部，而且它是一个函数。
<!--/-->

```agda
  nameOf : Formula ⟪ A ⟫ 1 → Name
  nameOf φ = countFo φ , (absFo φ , constantsFo φ)
```

<!--en-->
Its adequacy is the previous chapter's, spent here. Two readings of a
parameter-free formula are in play and they have to be identified first: the
name's denotation reads it inside the constant domain `⟪ A ⟫`{.Agda}, through
`embed`{.Agda}, while the abstraction theorem reads it at the empty constant
domain. The two interpretations are functions out of the empty type, so they
agree, and saying so is the only bookkeeping the identification costs.
<!--zh-->
它的充分性就是上一章的那一条，在此花掉。场上有两种读一条无参公式的方式，必须先把它们认同：名字的指称经 `embed`{.Agda} 在常元域 `⟪ A ⟫`{.Agda} 之内读它，而抽象定理在空常元域处读它。两个解释都是从空类型出发的函数，故它们相符，而把这句话说出来就是这次认同的全部记账。
<!--/-->

```agda
  private
    emptySat : (f : ⊥* {ℓ} → DA.SM) {n : ℕ}
             → DA.SM ^ n → Formula (⊥* {ℓ}) n → Ω
    emptySat f γ χ = γ ⊨ᶠ χ
      where open SemM.At (⊥* {ℓ}) f using () renaming ( _⊨_ to _⊨ᶠ_ )

    sameReading : (λ (b : ⊥* {ℓ}) → DA.ι (Empty.rec* b)) ≡ Empty.rec*
    sameReading = funExt (λ b → Empty.rec* b)

    absSat : (φ : Formula ⟪ A ⟫ 1) (m : ⟪ A ⟫)
           → (environment (nameOf φ) m ⊨ᵐ embed (formula (nameOf φ)))
           ≡ ((DA.ι m ∷ []) ⊨ᵐ φ)
    absSat φ m =
        embed-⊨ (hPropAlgebra (ℓ-suc ℓ)) DA.𝒮M DA.ι (absFo φ)
          (environment (nameOf φ) m)
      ∙ cong (λ f → emptySat f (environment (nameOf φ) m) (absFo φ)) sameReading
      ∙ sym (⊨-abs₁ (hPropAlgebra (ℓ-suc ℓ)) DA.𝒮M DA.ι φ (DA.ι m))

    satAt-abs : (φ : Formula ⟪ A ⟫ 1) (m : ⟪ A ⟫)
              → satAt (nameOf φ) m ≡ DA.smallSat φ m
    satAt-abs φ m = ⇔toPath fwd bwd
      where
      big = DA.⊨ᵐ-small (embed (formula (nameOf φ))) (environment (nameOf φ) m)
      small = DA.⊨ᵐ-small φ (DA.ι m ∷ [])
      fwd : ⟨ satAt (nameOf φ) m ⟩ → ⟨ DA.smallSat φ m ⟩
      fwd h = equivFun (small .snd) (subst ⟨_⟩ (absSat φ m) (invEq (big .snd) h))
      bwd : ⟨ DA.smallSat φ m ⟩ → ⟨ satAt (nameOf φ) m ⟩
      bwd h = equivFun (big .snd)
        (subst ⟨_⟩ (sym (absSat φ m)) (invEq (small .snd) h))
```

<!--en-->
Both subsets are cut out of `A` by a small predicate on its members, so once the
two predicates are equal the two sets are equal by a congruence, with no appeal
to extensionality. Completeness follows by transporting along that equality, and
it is stated truncated because that is how the definable powerset gives up a
formula in the first place.
<!--zh-->
两个子集都是由 `A` 的成员上的一条小谓词从 `A` 中割出，故两条谓词一旦相等，两个集合便由一次同余而相等，无须援引外延性。完备性沿那条等式搬运即得，而它陈述成截断的，因为可定义幂集本来就是这样交出一条公式的。
<!--/-->

```agda
  denote-defSet : (φ : Formula ⟪ A ⟫ 1) → denote (nameOf φ) ≡ DA.defSet φ
  denote-defSet φ = cong subsetOf (funExt (satAt-abs φ))

  names-complete : (x : S) → ⟨ x ∈ˢ 𝒟ₒ A ⟩
                 → ∥ Σ[ a ∈ Name ] (denote a ≡ x) ∥₁
  names-complete x h = PT.map named (𝒟ₒ-inv A x h)
    where
    named : Σ[ φ ∈ Formula ⟪ A ⟫ 1 ] (DA.defSet φ ≡ x)
          → Σ[ a ∈ Name ] (denote a ≡ x)
    named (φ , q) = nameOf φ , (denote-defSet φ ∙ q)
```

<!--en-->
## The order on the parameter vectors
<!--zh-->
## 参数向量上的序
<!--ja-->
## パラメータ列上の順序
<!--/-->

<!--en-->
Parameter vectors are compared at their first differing position by the given well-order of the stage. Allowing the two vectors to carry separate lengths avoids transporting one vector after equality of arities has been proved.
<!--zh-->
参数向量在首次相异的位置由阶段上的既定良序比较。让两个向量各自保留长度，可避免在证明元数相等后搬运其中一个向量。
<!--ja-->
パラメータ列は、最初に異なる位置で段階上の所与の整列順序によって比較する。二つの列が別々の長さをもてるようにすると、アリティの等しさを示した後で一方を移送せずに済む。
<!--/-->

<!--en-->
The module's second parameter is the well-order of the stage's members, and the
rest of the chapter spends it. The third key compares parameter vectors, and it
compares them in the obvious way: at the first position where they differ, the
given order decides.

The comparison is written across **two lengths**, and the two cases where a
vector runs out are the empty type. That costs nothing where the lengths are
equal, which is the only place the comparison is ever reached, and it buys the
absence of a transport: the second key has already pronounced the arities equal
by then, but the two vectors still have syntactically different lengths, and a
comparison demanding one length would have to move one of them first.
<!--zh-->
模块的第二个参数就是该阶段成员上的那个良序，本章余下部分把它花掉。第三个键比较参数向量，而它的比较方式显而易见：在它们首次相异之处，由给定的序裁决。

这次比较跨**两个长度**书写，而向量走完的那两种情形取空类型。在长度相等处这分文不花，而那也是这次比较唯一会被抵达之处；换来的则是「不必搬运」：那时第二个键已经宣布诸元数相等，可两个向量的长度在语法上仍然不同，而一个只认单一长度的比较，就得先把其中一个搬过去。
<!--/-->

```agda
  open SWO limitOrder using () renaming
    ( _<∙_ to _≺_ ; tri∙ to ≺-tri ; irr∙ to ≺-irr
    ; trans∙ to ≺-trans ; wf∙ to ≺-wf )
  open SWO w using () renaming
    ( _<∙_ to _≺ₚ_ ; tri∙ to ≺ₚ-tri ; irr∙ to ≺ₚ-irr
    ; trans∙ to ≺ₚ-trans ; wf∙ to ≺ₚ-wf )

  infix 20 _≺ᵥ_
  _≺ᵥ_ : ∀ {j k} → Vec ⟪ A ⟫ j → Vec ⟪ A ⟫ k → Type (ℓ-suc ℓ)
  []      ≺ᵥ []      = ⊥*
  []      ≺ᵥ (y ∷ q) = ⊥*
  (x ∷ p) ≺ᵥ []      = ⊥*
  (x ∷ p) ≺ᵥ (y ∷ q) = (x ≺ₚ y) ⊎ ((x ≡ y) × (p ≺ᵥ q))
```

<!--en-->
Three of the four laws are immediate inductions. Irreflexivity and trichotomy ask
for equal lengths, since only there is a vector equal to another at all;
transitivity does not, and gets three vectors of three lengths, with every case
but the all-inhabited one refuted by the empty type.
<!--zh-->
四条定律里有三条是当即的归纳。非自反与三歧要求长度相等，因为只有在那里一个向量才谈得上与另一个相等；传递性则不要求，它拿到三个长度各异的向量，而除「三者皆非空」之外的每个情形都由空类型反驳。
<!--/-->

```agda
  ≺ᵥ-irr : ∀ {k} (p : Vec ⟪ A ⟫ k) → p ≺ᵥ p → Empty.⊥
  ≺ᵥ-irr []      h             = Empty.rec* h
  ≺ᵥ-irr (x ∷ p) (inl h)       = ≺ₚ-irr x h
  ≺ᵥ-irr (x ∷ p) (inr (_ , h)) = ≺ᵥ-irr p h

  ≺ᵥ-trans : ∀ {i j k} (p : Vec ⟪ A ⟫ i) (q : Vec ⟪ A ⟫ j) (r : Vec ⟪ A ⟫ k)
           → p ≺ᵥ q → q ≺ᵥ r → p ≺ᵥ r
  ≺ᵥ-trans []      []      r       h k = Empty.rec* h
  ≺ᵥ-trans []      (y ∷ q) r       h k = Empty.rec* h
  ≺ᵥ-trans (x ∷ p) []      r       h k = Empty.rec* h
  ≺ᵥ-trans (x ∷ p) (y ∷ q) []      h k = Empty.rec* k
  ≺ᵥ-trans (x ∷ p) (y ∷ q) (z ∷ r) (inl h) (inl k) = inl (≺ₚ-trans x y z h k)
  ≺ᵥ-trans (x ∷ p) (y ∷ q) (z ∷ r) (inl h) (inr (e , k)) =
    inl (subst (λ v → x ≺ₚ v) e h)
  ≺ᵥ-trans (x ∷ p) (y ∷ q) (z ∷ r) (inr (e , h)) (inl k) =
    inl (subst (λ v → v ≺ₚ z) (sym e) k)
  ≺ᵥ-trans (x ∷ p) (y ∷ q) (z ∷ r) (inr (e , h)) (inr (e' , k)) =
    inr (e ∙ e' , ≺ᵥ-trans p q r h k)

  ≺ᵥ-tri : ∀ {k} (p q : Vec ⟪ A ⟫ k) → Tri (p ≺ᵥ q) (p ≡ q) (q ≺ᵥ p)
  ≺ᵥ-tri []      []      = eq refl
  ≺ᵥ-tri (x ∷ p) (y ∷ q) = decide (≺ₚ-tri x y)
    where
    decide : Tri (x ≺ₚ y) (x ≡ y) (y ≺ₚ x)
           → Tri ((x ∷ p) ≺ᵥ (y ∷ q)) ((x ∷ p) ≡ (y ∷ q)) ((y ∷ q) ≺ᵥ (x ∷ p))
    decide (lt h) = lt (inl h)
    decide (gt h) = gt (inl h)
    decide (eq e) =
      Tri-map (λ h → inr (e , h)) (cong₂ _∷_ e) (λ h → inr (sym e , h))
        (≺ᵥ-tri p q)
```

<!--en-->
Well-foundedness is the one that needs a plan. Descending from a vector, the head
either drops in the given order, and then the tail is replaced by an arbitrary
one of the same length, or the head stays and the tail drops. So the descent is
two nested inductions: the given order's well-foundedness for the head, and the
tail's accessibility for the tail, with the arbitrary tails supplied by the
statement one length down. That third ingredient is why the whole thing recurses
on the length as well, and why the head's induction is taken as an induction
principle rather than as a second recursive argument: with all three appetites
served in one recursion the descent has no single decreasing measure to offer.
<!--zh-->
需要谋划的是良基性。从一个向量向下走，头部或者按给定的序下降，此时尾部被换成同长的任意一个；或者头部不动而尾部下降。故这次下降是两层嵌套的归纳：头部用给定序的良基性，尾部用尾部的可及性，而那些任意的尾部由「短一格的那条陈述」供给。正是这第三样配料使整件事也对长度递归，也正因如此，头部的归纳取作归纳原理、而非取作第二个递归实参：若三副胃口都在同一场递归里伺候，那次下降就交不出单一的递减尺度。
<!--/-->

```agda
  private
    consAcc : (k : ℕ) → ((r : Vec ⟪ A ⟫ k) → Acc (_≺ᵥ_ {k} {k}) r)
            → (y : ⟪ A ⟫) (q : Vec ⟪ A ⟫ k) → Acc (_≺ᵥ_ {k} {k}) q
            → Acc (_≺ᵥ_ {suc k} {suc k}) (y ∷ q)
    consAcc k prev = WFI.induction ≺ₚ-wf onHead
      where
      onHead : (y : ⟪ A ⟫)
             → ((z : ⟪ A ⟫) → z ≺ₚ y → (q : Vec ⟪ A ⟫ k)
                  → Acc (_≺ᵥ_ {k} {k}) q → Acc (_≺ᵥ_ {suc k} {suc k}) (z ∷ q))
             → (q : Vec ⟪ A ⟫ k) → Acc (_≺ᵥ_ {k} {k}) q
             → Acc (_≺ᵥ_ {suc k} {suc k}) (y ∷ q)
      onHead y ih q (acc rq) = acc step
        where
        step : (r : Vec ⟪ A ⟫ (suc k)) → r ≺ᵥ (y ∷ q)
             → Acc (_≺ᵥ_ {suc k} {suc k}) r
        step (z ∷ r) (inl h)       = ih z h r (prev r)
        step (z ∷ r) (inr (e , h)) =
          subst (λ v → Acc (_≺ᵥ_ {suc k} {suc k}) (v ∷ r)) (sym e)
            (onHead y ih r (rq r h))

  ≺ᵥ-wf : (k : ℕ) (p : Vec ⟪ A ⟫ k) → Acc (_≺ᵥ_ {k} {k}) p
  ≺ᵥ-wf zero    []      = acc (λ { [] h → Empty.rec* h })
  ≺ᵥ-wf (suc k) (x ∷ p) = consAcc k (≺ᵥ-wf k) x p (≺ᵥ-wf k p)
```

<!--en-->
One derived fact travels with the comparison and is proved by path induction:
moving a vector along an equality of lengths does not change what it is below or
above. The two places that need it are the trichotomy and the descent, both of
which meet two vectors whose lengths are equal but not identical.
<!--zh-->
还有一件派生的事实随这次比较同行，并由一次路径归纳证出：把一个向量沿长度的等式搬过去，不改变它在谁之下、在谁之上。需要它的有两处，即三歧与下降，二者遇到的都是「长度相等但并非同一」的两个向量。
<!--/-->

```agda
  private
    ≺ᵥ-subst-left : {i j k : ℕ} (e : i ≡ j) (p : Vec ⟪ A ⟫ i) (q : Vec ⟪ A ⟫ k)
                  → (subst (Vec ⟪ A ⟫) e p ≺ᵥ q) ≡ (p ≺ᵥ q)
    ≺ᵥ-subst-left e p q = sym (constSubstCommSlice
      (Vec ⟪ A ⟫) (Type (ℓ-suc ℓ)) (λ _ v → v ≺ᵥ q) e p)

    ≺ᵥ-subst-right : {i j k : ℕ} (e : i ≡ j) (p : Vec ⟪ A ⟫ k) (q : Vec ⟪ A ⟫ i)
                   → (p ≺ᵥ subst (Vec ⟪ A ⟫) e q) ≡ (p ≺ᵥ q)
    ≺ᵥ-subst-right e p q = sym (constSubstCommSlice
      (Vec ⟪ A ⟫) (Type (ℓ-suc ℓ)) (λ _ v → p ≺ᵥ v) e q)

```

<!--en-->
## Three keys, in order
<!--zh-->
## 三个键，依次
<!--ja-->
## 三つの鍵を順に比較する
<!--/-->

<!--en-->
Names are ordered lexicographically by formula code, arity, and parameter vector. The comparison is written as three explicit cases, so its trichotomy and transitivity follow one key at a time.
<!--zh-->
名字依次按公式码、元数与参数向量作字典序比较。比较写成三个明确情形，因而三歧性与传递性都可逐键证明。
<!--ja-->
名前は論理式コード、アリティ、パラメータ列の順に辞書式で比較する。比較を三つの場合として明示することで、三分性と推移性を鍵ごとに示せる。
<!--/-->

<!--en-->
The comparison of names is the lexicographic one on those three keys, written
out as a sum rather than declared as an inductive relation. That is a
measurement, not a taste: an inductive declaration is checked for positivity, and
positivity checking normalizes the constructors' arguments, which here means
unfolding the limit order down to the search it is defined by. Written as a sum
nothing unfolds, and the three cases read off the shape.
<!--zh-->
名字之间的比较，就是这三个键上的字典序比较，写成和类型、而非声明为归纳关系。这是一次测量，不是口味：归纳声明要过正性检查，而正性检查会把诸构造子的实参归一化，在此就意味着把那个极限序展开到它据以定义的那场搜寻。写成和类型则什么也不展开，而三个情形从形状上直接读出。
<!--/-->

```agda
  infix 20 _≺ₙ_
  _≺ₙ_ : Name → Name → Type (ℓ-suc ℓ)
  a ≺ₙ b = (codeOf a ≺ codeOf b)
         ⊎ ( (codeOf b ≡ codeOf a)
           × ( (arity a < arity b)
             ⊎ ((arity b ≡ arity a) × (params a ≺ᵥ params b)) ) )
```

<!--en-->
Irreflexivity and transitivity are then the three keys' own laws, sorted by case.
The mixed cases of transitivity carry an equality of one key across the other's
comparison, and that is all the bookkeeping there is; the parameter case appeals
to the vector comparison at three lengths, which is why that one was proved
across lengths.
<!--zh-->
于是非自反与传递就是三个键各自的定律，按情形归类。传递性的混合情形把一个键的等式带过另一个键的比较，而全部记账仅此而已；参数那一情形援引三个长度上的向量比较，而这正是当初把那一条跨长度证出的原因。
<!--/-->

```agda
  ≺ₙ-irr : (a : Name) → a ≺ₙ a → Empty.⊥
  ≺ₙ-irr a (inl h)                 = ≺-irr (codeOf a) h
  ≺ₙ-irr a (inr (_ , inl h))       = ¬m<m h
  ≺ₙ-irr a (inr (_ , inr (_ , h))) = ≺ᵥ-irr (params a) h

  ≺ₙ-trans : (a b c : Name) → a ≺ₙ b → b ≺ₙ c → a ≺ₙ c
  ≺ₙ-trans a b c (inl h) (inl k) =
    inl (≺-trans (codeOf a) (codeOf b) (codeOf c) h k)
  ≺ₙ-trans a b c (inl h) (inr (q , _)) =
    inl (subst (λ v → codeOf a ≺ v) (sym q) h)
  ≺ₙ-trans a b c (inr (q , _)) (inl k) =
    inl (subst (λ v → v ≺ codeOf c) q k)
  ≺ₙ-trans a b c (inr (q , inl h)) (inr (q' , inl k)) =
    inr (q' ∙ q , inl (<-trans h k))
  ≺ₙ-trans a b c (inr (q , inl h)) (inr (q' , inr (e , _))) =
    inr (q' ∙ q , inl (subst (λ j → arity a < j) (sym e) h))
  ≺ₙ-trans a b c (inr (q , inr (e , _))) (inr (q' , inl k)) =
    inr (q' ∙ q , inl (subst (λ j → j < arity c) e k))
  ≺ₙ-trans a b c (inr (q , inr (e , h))) (inr (q' , inr (e' , k))) =
    inr (q' ∙ q , inr (e' ∙ e , ≺ᵥ-trans (params a) (params b) (params c) h k))
```

<!--en-->
Trichotomy descends the keys, each new one reached only when the previous one has
pronounced equality. The last stop is the only one with work in it. There the
arities are equal but not identical, so the first name's parameters are moved to
the second's length before the vectors are compared, and the two strict verdicts
are moved back; and when the vectors agree, the two names agree, because the
first key's equality now says the formulas have the same code, and a code
determines a parameter-free formula.

Everything here is stated at the two names themselves rather than at their
components. That is the second measurement of the chapter: a statement made at a
name's three projections is equal to one made at the name only up to eta, and
matching the two forced the whole limit order open, at eighty-seven seconds for
one lemma.
<!--zh-->
三歧沿诸键下行，每个新键唯有在前一个宣布相等时才被抵达。最后一站是唯一有活干的一站。在那里诸元数相等但并非同一，故先把第一个名字的参数搬到第二个的长度上，再比较两个向量，然后把两种严格判决搬回来；而当两个向量相符时，两个名字相符，因为第一个键的等式此刻说两条公式有相同的码，而一个码决定一条无参公式。

此处一切都陈述在两个名字自身上，而非陈述在它们的分量上。这是本章的第二次测量：在一个名字的三个投影上作的陈述，与在那个名字上作的陈述只在 eta 的意义下相等，而把两者对上会把整个极限序逼开，一条引理八十七秒。
<!--/-->

```agda
  ≺ₙ-tri : (a b : Name) → Tri (a ≺ₙ b) (a ≡ b) (b ≺ₙ a)
  ≺ₙ-tri a b = byCodes (≺-tri (codeOf a) (codeOf b))
    where
    byCodes : Tri (codeOf a ≺ codeOf b) (codeOf a ≡ codeOf b) (codeOf b ≺ codeOf a)
            → Tri (a ≺ₙ b) (a ≡ b) (b ≺ₙ a)
    byCodes (lt h) = lt (inl h)
    byCodes (gt h) = gt (inl h)
    byCodes (eq ec) = byArities (arity a ≟ arity b)
      where
      byArities : NatOrder.Trichotomy (arity a) (arity b)
                → Tri (a ≺ₙ b) (a ≡ b) (b ≺ₙ a)
      byArities (NatOrder.lt h) = lt (inr (sym ec , inl h))
      byArities (NatOrder.gt h) = gt (inr (ec , inl h))
      byArities (NatOrder.eq e) =
        byParams (≺ᵥ-tri (subst (Vec ⟪ A ⟫) e (params a)) (params b))
        where
        shifted : Vec ⟪ A ⟫ (arity b)
        shifted = subst (Vec ⟪ A ⟫) e (params a)

        sameFormula : subst (λ k → Formula (⊥* {ℓ}) (suc k)) e (formula a)
                    ≡ formula b
        sameFormula =
          code-inj (subst (λ k → Formula (⊥* {ℓ}) (suc k)) e (formula a))
            (formula b)
            (code-shift e (formula a) ∙ cong fst ec)

        byParams : Tri (shifted ≺ᵥ params b) (shifted ≡ params b)
                       (params b ≺ᵥ shifted)
                 → Tri (a ≺ₙ b) (a ≡ b) (b ≺ₙ a)
        byParams (lt h) = lt (inr (sym ec , inr (sym e ,
          transport (≺ᵥ-subst-left e (params a) (params b)) h)))
        byParams (gt h) = gt (inr (ec , inr (e ,
          transport (≺ᵥ-subst-right e (params b) (params a)) h)))
        byParams (eq ep) =
          eq (ΣPathP (e , ΣPathP (toPathP sameFormula , toPathP ep)))
```

<!--en-->
## Descending the three keys
<!--zh-->
## 沿三个键下降
<!--ja-->
## 三つの鍵に沿って降下する
<!--/-->

<!--en-->
Well-foundedness follows by nested descent: first through formula codes, then arities, then parameter vectors. Each layer recurses on one accessibility proof, matching the lexicographic structure of the comparison.
<!--zh-->
良基性来自嵌套下降：先沿公式码，再沿元数，最后沿参数向量。每一层只对一份可及性证明递归，与字典序比较的结构吻合。
<!--ja-->
整礎性は、論理式コード、アリティ、パラメータ列の順に入れ子になった降下から従う。各層は一つの到達可能性の証明だけについて再帰し、辞書式比較の構造と一致する。
<!--/-->

<!--en-->
Well-foundedness is the same descent read as a recursion, one stage per key.
Innermost, the code and the arity are fixed and the parameters descend, with the
vector's accessibility as the decreasing argument; in the middle, the code is
fixed and the arity descends; outermost, the code descends. Each stage is a
separate function taking the outer stages' induction hypotheses as arguments, so
each recurses on exactly one accessibility proof and the recursion is structural
everywhere.

The name always arrives as a name, with equations saying where its keys sit. That
is the same law as the trichotomy's, met again: an accessibility stated at a
name's components would have to be matched against one stated at the name.
<!--zh-->
良基性就是同一次下降读作递归，一个键一层。最内层，码与元数固定，诸参数下降，递减的实参是向量的可及性；中间一层，码固定，元数下降；最外层，码下降。每一层各是一个函数，把外层的诸归纳假设当实参收进来，于是每一层恰对一份可及性证明递归，处处都是结构递归。

名字总是以名字的身份到场，外加若干说明它的诸键坐在哪里的等式。这与三歧那一条是同一条规矩，此番再度出现：陈述在一个名字的诸分量上的可及性，将不得不与陈述在那个名字上的可及性对上。
<!--/-->

```agda
  private
    accAtParam : (c : Limit)
               → ((b : Name) → codeOf b ≺ c → Acc _≺ₙ_ b)
               → (k : ℕ)
               → ((b : Name) → codeOf b ≡ c → arity b < k → Acc _≺ₙ_ b)
               → (p : Vec ⟪ A ⟫ k) → Acc (_≺ᵥ_ {k} {k}) p
               → (a : Name) → codeOf a ≡ c → (ek : arity a ≡ k)
               → subst (Vec ⟪ A ⟫) ek (params a) ≡ p
               → Acc _≺ₙ_ a
    accAtParam c ihC k ihK p (acc rp) a qc ek qp = acc step
      where
      step : (b : Name) → b ≺ₙ a → Acc _≺ₙ_ b
      step b (inl h)           = ihC b (subst (λ v → codeOf b ≺ v) qc h)
      step b (inr (q , inl h)) = ihK b (sym q ∙ qc) (subst (λ j → arity b < j) ek h)
      step b (inr (q , inr (e , h))) =
        accAtParam c ihC k ihK pb (rp pb hb) b (sym q ∙ qc) eb refl
        where
        eb : arity b ≡ k
        eb = sym e ∙ ek
        pb : Vec ⟪ A ⟫ k
        pb = subst (Vec ⟪ A ⟫) eb (params b)
        hb : pb ≺ᵥ p
        hb = subst (λ v → pb ≺ᵥ v) qp
          (transport (sym (≺ᵥ-subst-right ek pb (params a)))
            (transport (sym (≺ᵥ-subst-left eb (params b) (params a))) h))

    accAtArity : (c : Limit)
               → ((b : Name) → codeOf b ≺ c → Acc _≺ₙ_ b)
               → (k : ℕ) → Acc _<_ k
               → (a : Name) → codeOf a ≡ c → arity a ≡ k → Acc _≺ₙ_ a
    accAtArity c ihC k (acc rk) a qc ek =
      accAtParam c ihC k ihK (subst (Vec ⟪ A ⟫) ek (params a))
        (≺ᵥ-wf k (subst (Vec ⟪ A ⟫) ek (params a))) a qc ek refl
      where
      ihK : (b : Name) → codeOf b ≡ c → arity b < k → Acc _≺ₙ_ b
      ihK b q h = accAtArity c ihC (arity b) (rk (arity b) h) b q refl

    accAtCode : (c : Limit) → Acc _≺_ c → (a : Name) → codeOf a ≡ c → Acc _≺ₙ_ a
    accAtCode c (acc rc) a qc =
      accAtArity c ihC (arity a) (<-wellfounded (arity a)) a qc refl
      where
      ihC : (b : Name) → codeOf b ≺ c → Acc _≺ₙ_ b
      ihC b h = accAtCode (codeOf b) (rc (codeOf b) h) b refl

  ≺ₙ-wf : WellFounded _≺ₙ_
  ≺ₙ-wf a = accAtCode (codeOf a) (≺-wf (codeOf a)) a refl
```

<!--en-->
## The bundle, and the least name
<!--zh-->
## 束，与最小的名字
<!--ja-->
## 整列順序と最小の名前
<!--/-->

<!--en-->
The three-key relation satisfies the four laws of a strict well-order. Applying least-element search to this order turns any inhabited family of names into a definite least name.
<!--zh-->
三键关系满足严格良序的四条定律。把最小元搜索用于这个序，就能从任意非空名字族中得到一个确定的最小名字。
<!--ja-->
三つの鍵による関係は、狭義整列順序の四つの法則を満たす。この順序に最小要素の探索を適用すると、要素をもつ任意の名前の族から確定した最小の名前が得られる。
<!--/-->

<!--en-->
The four laws packaged are a strict well-order on the names, which is the
interface the choosing device takes; and the least-element search of the
well-order chapter, applied to it, turns a merely inhabited family of names into
a definite one. This is the whole of what the names were built for: a family of
sets over one stage becomes a family of names, and a family of names has a least
member.
<!--zh-->
四条定律打成束，就是诸名字上的一个严格良序，而那正是选取装置取用的接口；而良序那一章的取极小元搜索施于其上，便把一族仅仅非空的名字变成一个确定的名字。这就是造出诸名字的全部目的：单一阶段之上的一族集合成为一族名字，而一族名字有极小元。
<!--/-->

```agda
  nameOrder : SWO (Name)
  nameOrder = record
    { _<∙_   = _≺ₙ_
    ; tri∙   = ≺ₙ-tri
    ; irr∙   = ≺ₙ-irr
    ; trans∙ = ≺ₙ-trans
    ; wf∙    = ≺ₙ-wf }

  leastName : (P : Name → hProp (ℓ-suc ℓ))
            → ∥ Σ[ a ∈ Name ] ⟨ P a ⟩ ∥₁ → Σ[ a ∈ Name ] IsLeast nameOrder P a
  leastName = leastOf nameOrder lem
```

<!--en-->
## Recap
<!--zh-->
## 小结
<!--ja-->
## まとめ
<!--/-->

<!--en-->
Every successor-stage member now has a name, and the names carry a strict well-order. Formula-code injectivity and the three-key descent ensure that least names can serve as canonical representatives in the choice construction.
<!--zh-->
现在，后继阶段的每个成员都有名字，而且诸名字带有严格良序。公式码的单射性与三键下降保证最小名字可以在选择构造中充当典范代表。
<!--ja-->
これで後者段階の各要素は名前をもち、名前全体には狭義整列順序が入った。論理式コードの単射性と三つの鍵による降下により、最小の名前を選択構成の正準的な代表として使える。
<!--/-->

<!--en-->
A `Name`{.Agda} is an arity, a parameter-free formula of one more variable, and a
vector of parameters from the stage; `denote`{.Agda} is the subset it carves, and
`denote-mem`{.Agda} says so in the inner semantics the definable powerset is
defined by. `names-complete`{.Agda} says every member of the successor stage is
denoted, truncated, which is how the definable powerset gives up its formula.

`code∈limit`{.Agda} puts the first key where the previous chapter's order can
reach it, and `code-inj`{.Agda} makes that key faithful; `_≺ᵥ_`{.Agda} orders the
third key across lengths, and `_≺ₙ_`{.Agda} is the three-key comparison itself,
with all four laws and `leastName`{.Agda}, the least name of a non-empty family.

Three costs were measured, and every one of them is the same accident seen from
a different side: something forces the limit order open, and the limit order
unfolds into a search for a least ordinal. An inductive declaration of the
comparison forces it in the positivity check; a statement made at a name's
projections rather than at the name forces it when the two are matched, at
eighty-seven seconds a lemma; and naming data reached from **another** module
forces it at every comparison of codes, which was the largest of the three.
Written as a sum, stated at names throughout, and with the data defined where it
is used, the chapter costs nothing.
<!--zh-->
一个 `Name`{.Agda} 是一个元数、一条多一个变量的无参公式，以及一个取自该阶段的参数向量；`denote`{.Agda} 是它刻出的子集，而 `denote-mem`{.Agda} 在可定义幂集据以定义的那套内层语义中把这件事说出来。`names-complete`{.Agda} 说后继阶段的每个成员都被指称，且是截断的，因为可定义幂集本来就是这样交出它的公式的。

`code∈limit`{.Agda} 把第一个键放到上一章那个序够得着的地方，而 `code-inj`{.Agda} 使那个键忠实；`_≺ᵥ_`{.Agda} 跨长度地给第三个键排序，而 `_≺ₙ_`{.Agda} 就是那次三键比较本身，连同四条定律与 `leastName`{.Agda}，即非空族中最小的名字。

三笔代价被量出，而每一笔都是同一次意外的不同侧面：某样东西把极限序逼开，而极限序展开就是一场「最小序数」的搜寻。把那次比较声明为归纳关系，会在正性检查中把它逼开；陈述在一个名字的诸投影上、而非陈述在那个名字上的东西，会在两者对上时把它逼开，一条引理八十七秒；而从**另一个**模块够到的命名数据，会在每一次码的比较处把它逼开，这是三者中最大的一笔。写成和类型、全程陈述在名字上、并把数据定义在它被使用之处，本章分文不花。
<!--/-->
