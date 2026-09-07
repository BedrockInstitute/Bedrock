<!--en-->
# Well-orders on finite stages
<!--zh-->
# 有限阶段上的良序
<!--ja-->
# 有限段階上の整列順序
<!--/-->

<!--en-->
This chapter proves that every numeral-indexed stage is finite and equips it
with the earliest-disagreement well-order, then combines stage number and local
order to well-order the limit stage.
<!--zh-->
本章证明每个以数码为索引的阶段都是有穷的，并以最先分歧赋予其良序；随后结合阶段号与局部序来良序化极限阶段。
<!--ja-->
本章では、数項で添字づけられた各段階が有限であることを証明し、最初の相違による整列順序を与える。さらに段階番号と局所順序を組み合わせて極限段階を整列順序づける。
<!--/-->

<!--en-->
The earlier choice construction locates, for each cell of a family, the stage at which
the cell first has a member, and showed that this stage is a successor. Every
member of the cell that appears exactly there is therefore a definable subset of
one and the same set: a name written over a single stage. What is still missing
is a way to **compare** those names, and comparison is what this chapter builds,
at the bottom of the tower.

Two claims carry it. The first is that each stage indexed by a numeral is
finite, in the precise sense given below: it comes with a finite list of sets
that hits all of its members. The second is that a finite stage carries a
well-order, obtained by comparing two of its members at the earliest point where
they disagree, and giving the larger place to whichever of the two contains that
point.

The second claim is the mathematical content, and it is a claim about **finite**
sets in an essential way. Order the subsets of the natural numbers by that same
recipe and there is an infinite descent: the set of all numbers, then all
numbers from one on, then all from two on, and so forth, each step deleting the
earliest surviving point and so landing strictly lower. Nothing about the recipe
forbids this; what forbids it over a finite base is that a finite base has only
finitely many subsets, so a search for a smallest one terminates. That is exactly
how the well-foundedness proof below goes: a finite list plus a linear order
yields a smallest member of any inhabited property, by scanning the list and
keeping the best hit; and "every inhabited property has a smallest member" is,
classically, well-foundedness.

The finiteness climbs the tower because the definable subsets of a finite set
are all of its subsets, and a set with a list has only finitely many subsets, one
for each vector of bits over that list. So a list of the stage yields a list of
the next stage, and the recursion needs nothing else.

The limit stage is then assembled without any further work about how the finite
orders sit inside one another, because they do not: comparison at the earliest
disagreement does not extend from one stage to the next. The floor number is the
primary key instead. Two members of the limit that first appear at different
finite stages are compared by those stage numbers alone; two that first appear at
the same stage are compared by that stage's own order. Nothing else is needed,
and nothing else is true.
<!--zh-->
先前的选择构造为一个族的每一格定位了该格首次拥有成员的阶段，并证明了它是一个后继。于是该格中恰在那里现身的每个成员，都是同一个集合的可定义子集：一个写在单一阶段之上的名字。尚缺的是**比较**这些名字的办法，而本章要在塔的底部造出的正是这种比较。

两个论断撑起本章。第一，凡以数码为索引的阶段都是有穷的，其确切含义见下文：它附带一份有穷的集合清单，命中它的全部成员。第二，有穷阶段带有一个良序，其比较方式是看两个成员最先在何处出现分歧，并把较大的位置判给二者中含有该处的那一个。

第二个论断是数学内容所在，而它在本质上是关于**有穷**集合的论断。若把同一套配方用到自然数的子集上，就会出现无穷下降：全体自然数，然后是从一开始的全体，再是从二开始的全体，如此下去，每一步删掉最先幸存的那一点，因而严格落到更低处。配方本身并不禁止这件事；在有穷基底上禁止它的，是有穷基底只有有穷多个子集，故寻找最小者的搜索会终止。下文良基性的证明走的正是这条路：一份有穷清单加上一个线序，就给出任何非空性质的最小成员，办法是扫过清单并留下最好的一次命中；而「每个非空性质都有最小成员」在经典意义下就是良基性。

有穷性之所以能沿塔上爬，是因为有穷集合的可定义子集就是它的全部子集，而带清单的集合只有有穷多个子集，每个清单上的位向量对应一个。于是一个阶段的清单给出下一个阶段的清单，递归再无所求。

极限阶段随即装配起来，不必再为「有穷诸序如何互相嵌套」多费功夫，因为它们并不嵌套：按最先分歧处比较的序，并不从一个阶段延拓到下一个阶段。取而代之的主键是楼层号。极限中首次现身于不同有穷阶段的两个成员，仅凭那两个阶段号比较；首次现身于同一阶段的两个成员，则按那个阶段自己的序比较。别的都不需要，也别的都不成立。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module L.Choice.FiniteStageOrders {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ; extensionalV )
open import L.Constructible {ℓ} using ( IsOrd; Lset; Lset-out; 𝒟ₒ; 𝒟ₒ∋⊆ )
open import L.Ordinal {ℓ} using ( numeral-ord )
open import L.Axioms.Basic {ℓ}
  using ( finSet; finSet-in; finSet-out; Lset-suc; module FinOf )
open import L.WellOrder.Base {ℓ-suc ℓ}
  using ( Tri; lt; eq; gt; SWO; IsLeast; leastOf; natOrder )

open import Cubical.Data.Bool using ( Bool; true; false; false≢true )
open import Cubical.Data.Nat using ( _+_ )
open import Cubical.Data.Nat.Order using ( _<_; <-trans; ¬m<m; <-wellfounded; _≟_ )
import Cubical.Data.Nat.Order as NatOrder
open import Cubical.Data.Sigma using ( Σ≡Prop )
open import Cubical.Data.Sum using ( _⊎_; inl; inr )
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁ )
open import Cubical.Functions.Logic using ( ⇔toPath )
open import Cubical.Induction.WellFounded
  using ( Acc; acc; WellFounded; isPropAcc; module WFI )
open import Cubical.Relation.Nullary using ( isProp¬ )
open import Cubical.HITs.CumulativeHierarchy.Properties
  using ( ∈∈ₛ; ∈-asFiber; ⟪_⟫; ⟪_⟫↪ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ∅; ∅-empty; module InfinitySet )
open InfinitySet using ( #_; ω )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ
```

<!--en-->
## Tallies
<!--zh-->
## 点名册
<!--ja-->
## 有限な数え上げ
<!--/-->

<!--en-->
A `Tally`{.Agda} presents every member of a set by a finite indexed family,
allowing repetitions and requiring neither injectivity nor decidable equality.
<!--zh-->
`Tally`{.Agda} 用一个有穷索引族呈现集合的每个成员，允许重复，也不要求单射性或可判定相等。
<!--ja-->
`Tally`{.Agda} は集合の全要素を有限添字族で提示し、重複を許し、単射性も決定可能な等しさも要求しない。
<!--/-->

<!--en-->
Finiteness enters as a **tally**: a number, a family of that many sets all
belonging to `A`, and the statement that every member of `A` is merely one of
them. `onto` reads "the family hits everyone".

Nothing is asked about repetitions and nothing is asked about deciding equality:
a tally is a surjection from a finite index, not a bijection. That is deliberate.
The two uses ahead are a scan (which does not mind seeing an element twice) and
a bit vector (which does not mind either), and asking for less means the tally of
the next stage is cheaper to build. The whole finiteness vocabulary of this
chapter is this record plus the index arithmetic that builds one tally out of
another.
<!--zh-->
有穷性以**点名册**的身份入场：一个数、这么多个都属于 `A` 的集合所成的族，外加一句「`A` 的每个成员都仅仅是其中之一」。`onto` 读作「该族命中所有人」。

对重复不作要求，对判定相等也不作要求：点名册是从有穷索引出发的满射，不是双射。这是有意为之。前方的两处用法是一次扫描 (看见同一个元素两次也无妨) 与一个位向量 (同样无妨)，而要求得越少，下一个阶段的点名册就越便宜。本章全部的有穷性词汇，就是这个 record 加上「由一份点名册造出另一份」的索引算术。
<!--/-->

```agda
record Tally (A : S) : Type (ℓ-suc ℓ) where
  field
    size   : ℕ
    item   : Fin size → S
    inside : (i : Fin size) → ⟨ item i ∈ˢ A ⟩
    onto   : (x : S) → ⟨ x ∈ˢ A ⟩ → ∥ Σ[ i ∈ Fin size ] (item i ≡ x) ∥₁
```

<!--en-->
## Splitting a finite index
<!--zh-->
## 劈开一个有穷索引
<!--ja-->
## 有限添字を分割する
<!--/-->

<!--en-->
The maps `splitFin`{.Agda} and `joinFin`{.Agda} identify an index below a sum
with an index in one summand, supplying the arithmetic used to enumerate masks.
<!--zh-->
`splitFin`{.Agda} 与 `joinFin`{.Agda} 把和以下的索引与某个加数中的索引对应起来，供应枚举掩码所需的算术。
<!--ja-->
`splitFin`{.Agda} と `joinFin`{.Agda} は和より小さい添字を一方の加数の添字に対応させ、マスクの列挙に必要な算術を与える。
<!--/-->

<!--en-->
Tallying a power set means enumerating bit vectors, and there are twice as many
vectors of length `n + 1` as of length `n`. So one piece of index arithmetic is
needed: an index below `a + b` is either an index below `a` or an index below
`b`, and conversely. Only one of the two round trips is ever used, so only that
one is proved; `bumpLeft` is the shift that makes the recursion on `a` type-check.
<!--zh-->
为幂集清点，意味着枚举位向量，而长度为 `n + 1` 的向量数是长度为 `n` 的两倍。于是需要一小块索引算术：小于 `a + b` 的索引，要么是小于 `a` 的索引，要么是小于 `b` 的索引，反之亦然。两个来回中只有一个真正被用到，故只证那一个；`bumpLeft` 则是让沿 `a` 的递归通过类型检查的那次移位。
<!--/-->

```agda
bumpLeft : {a b : ℕ} → Fin a ⊎ Fin b → Fin (suc a) ⊎ Fin b
bumpLeft (inl i) = inl (suc i)
bumpLeft (inr j) = inr j

joinFin : (a : ℕ) {b : ℕ} → Fin a ⊎ Fin b → Fin (a + b)
joinFin zero    (inr j)       = j
joinFin (suc a) (inl zero)    = zero
joinFin (suc a) (inl (suc i)) = suc (joinFin a (inl i))
joinFin (suc a) (inr j)       = suc (joinFin a (inr j))

splitFin : (a : ℕ) {b : ℕ} → Fin (a + b) → Fin a ⊎ Fin b
splitFin zero    j       = inr j
splitFin (suc a) zero    = inl zero
splitFin (suc a) (suc i) = bumpLeft (splitFin a i)

split-join : (a : ℕ) {b : ℕ} (x : Fin a ⊎ Fin b) → splitFin a (joinFin a x) ≡ x
split-join zero    (inr j)       = refl
split-join (suc a) (inl zero)    = refl
split-join (suc a) (inl (suc i)) = cong bumpLeft (split-join a (inl i))
split-join (suc a) (inr j)       = cong bumpLeft (split-join a (inr j))
```

<!--en-->
## Enumerating the masks
<!--zh-->
## 枚举掩码
<!--ja-->
## マスクを列挙する
<!--/-->

<!--en-->
`maskAt`{.Agda} enumerates every Boolean vector of a fixed length, and
`mask-onto`{.Agda} proves that every selection pattern occurs.
<!--zh-->
`maskAt`{.Agda} 枚举固定长度的全部布尔向量，而 `mask-onto`{.Agda} 证明每种选取模式都会出现。
<!--ja-->
`maskAt`{.Agda} は固定長のすべてのブール・ベクトルを列挙し、`mask-onto`{.Agda} は各選択パターンが現れることを証明する。
<!--/-->

<!--en-->
A **mask** of length `n` is a vector of `n` bits; it will say, of a tallied set,
which entries to keep. There are `maskCount n` of them, that number being two to
the `n` written as an iterated doubling, and `maskAt` reads an index as a mask:
split the index in half, and the half it lands in supplies the leading bit while
the rest supplies the tail. Every mask is read off some index, which is
`mask-onto`, and that is the only property of the enumeration anyone needs. It is
not injective on the nose and does not have to be.
<!--zh-->
长度为 `n` 的**掩码**是一个 `n` 位的向量；对一个已清点的集合，它说明保留哪些条目。掩码共有 `maskCount n` 个，这个数是二的 `n` 次幂，写成反复加倍的形式，而 `maskAt` 把一个索引读成一个掩码：把索引对半劈开，它落在哪一半就由哪一半供给首位，其余部分供给尾巴。每个掩码都从某个索引读得，这就是 `mask-onto`，而这也是任何人对这个枚举唯一需要的性质。它并非逐点单射，也不必是。
<!--/-->

```agda
maskCount : ℕ → ℕ
maskCount zero    = 1
maskCount (suc n) = maskCount n + maskCount n

maskCons : (n : ℕ) → (Fin (maskCount n) → Vec Bool n)
         → Fin (maskCount n) ⊎ Fin (maskCount n) → Vec Bool (suc n)
maskCons n r (inl j) = false ∷ r j
maskCons n r (inr j) = true  ∷ r j

maskAt : (n : ℕ) → Fin (maskCount n) → Vec Bool n
maskAt zero    j = []
maskAt (suc n) j = maskCons n (maskAt n) (splitFin (maskCount n) j)

mask-onto : (n : ℕ) (v : Vec Bool n) → Σ[ j ∈ Fin (maskCount n) ] (maskAt n j ≡ v)
mask-onto zero    []          = zero , refl
mask-onto (suc n) (false ∷ v) =
  joinFin (maskCount n) (inl (mask-onto n v .fst))
  , (cong (maskCons n (maskAt n)) (split-join (maskCount n) (inl (mask-onto n v .fst)))
     ∙ cong (false ∷_) (mask-onto n v .snd))
mask-onto (suc n) (true ∷ v)  =
  joinFin (maskCount n) (inr (mask-onto n v .fst))
  , (cong (maskCons n (maskAt n)) (split-join (maskCount n) (inr (mask-onto n v .fst)))
     ∙ cong (true ∷_) (mask-onto n v .snd))
```

<!--en-->
## Selecting a sub-family
<!--zh-->
## 选出一个子族
<!--ja-->
## 部分族を選び出す
<!--/-->

<!--en-->
`select`{.Agda} filters a finite family by a Boolean mask, while its membership
lemmas connect selected entries with the positions marked true.
<!--zh-->
`select`{.Agda} 按布尔掩码筛选一个有穷族，其成员引理则把选中的条目与标为真的位置对应起来。
<!--ja-->
`select`{.Agda} はブール・マスクで有限族を絞り込み、その要素補題は選ばれた項と真に印づけられた位置を対応させる。
<!--/-->

<!--en-->
`select` applies a mask to a family: it keeps the entries whose bit is `true` and
returns them as a family again, together with its own length. The length is
**produced by the recursion**, which is the point: nothing has to be counted, and
no arithmetic relates the answer to the mask.

Two specifications say what the result contains, and both are untruncated,
because each is read straight off the same recursion. `marks` runs in the other
direction, turning a decision on the entries into the mask that records it.
<!--zh-->
`select` 把掩码作用到一个族上：它保留那些位为 `true` 的条目，并把它们重新交回为一个族，连同族自身的长度。长度是**由递归产生**的，这正是关键：无须计数，也没有任何算术把答案与掩码联系起来。

两条规格说明结果含有什么，且二者都不带截断，因为它们都是从同一次递归上直接读出的。`marks` 走的是反方向，把对诸条目的一次判定变成记录该判定的掩码。
<!--/-->

```agda
selectStep : {ℓ' : Level} {X : Type ℓ'} → X → Σ[ k ∈ ℕ ] (Fin k → X)
           → Σ[ k ∈ ℕ ] (Fin k → X)
selectStep {X = X} x (k , g) = suc k , h
  where
  h : Fin (suc k) → X
  h zero    = x
  h (suc i) = g i

select : {ℓ' : Level} {X : Type ℓ'} (n : ℕ) → (Fin n → X) → Vec Bool n
       → Σ[ k ∈ ℕ ] (Fin k → X)
select zero    f v           = zero , λ ()
select (suc n) f (false ∷ v) = select n (λ i → f (suc i)) v
select (suc n) f (true ∷ v)  = selectStep (f zero) (select n (λ i → f (suc i)) v)

select-out : {ℓ' : Level} {X : Type ℓ'} (n : ℕ) (f : Fin n → X) (v : Vec Bool n)
             (j : Fin (select n f v .fst))
           → Σ[ i ∈ Fin n ] ((lookup i v ≡ true) × (select n f v .snd j ≡ f i))
select-out zero    f []          ()
select-out (suc n) f (false ∷ v) j       = step (select-out n (λ i → f (suc i)) v j)
  where
  step : Σ[ i ∈ Fin n ] ((lookup i v ≡ true)
           × (select n (λ i → f (suc i)) v .snd j ≡ f (suc i)))
       → Σ[ i ∈ Fin (suc n) ] ((lookup i (false ∷ v) ≡ true)
           × (select (suc n) f (false ∷ v) .snd j ≡ f i))
  step (i , e , q) = suc i , (e , q)
select-out (suc n) f (true ∷ v)  zero    = zero , (refl , refl)
select-out (suc n) f (true ∷ v)  (suc j) = step (select-out n (λ i → f (suc i)) v j)
  where
  step : Σ[ i ∈ Fin n ] ((lookup i v ≡ true)
           × (select n (λ i → f (suc i)) v .snd j ≡ f (suc i)))
       → Σ[ i ∈ Fin (suc n) ] ((lookup i (true ∷ v) ≡ true)
           × (select (suc n) f (true ∷ v) .snd (suc j) ≡ f i))
  step (i , e , q) = suc i , (e , q)

select-in : {ℓ' : Level} {X : Type ℓ'} (n : ℕ) (f : Fin n → X) (v : Vec Bool n)
            (i : Fin n) → lookup i v ≡ true
          → Σ[ j ∈ Fin (select n f v .fst) ] (select n f v .snd j ≡ f i)
select-in zero    f []          ()      e
select-in (suc n) f (false ∷ v) zero    e = Empty.rec (false≢true e)
select-in (suc n) f (false ∷ v) (suc i) e = select-in n (λ i → f (suc i)) v i e
select-in (suc n) f (true ∷ v)  zero    e = zero , refl
select-in (suc n) f (true ∷ v)  (suc i) e = step (select-in n (λ i → f (suc i)) v i e)
  where
  step : Σ[ j ∈ Fin (select n (λ i → f (suc i)) v .fst) ]
           (select n (λ i → f (suc i)) v .snd j ≡ f (suc i))
       → Σ[ j ∈ Fin (select (suc n) f (true ∷ v) .fst) ]
           (select (suc n) f (true ∷ v) .snd j ≡ f (suc i))
  step (j , q) = suc j , q

marks : {ℓ' : Level} {X : Type ℓ'} (n : ℕ) → (Fin n → X) → (X → Bool) → Vec Bool n
marks zero    f d = []
marks (suc n) f d = d (f zero) ∷ marks n (λ i → f (suc i)) d

marks-lookup : {ℓ' : Level} {X : Type ℓ'} (n : ℕ) (f : Fin n → X) (d : X → Bool)
               (i : Fin n) → lookup i (marks n f d) ≡ d (f i)
marks-lookup (suc n) f d zero    = refl
marks-lookup (suc n) f d (suc i) = marks-lookup n (λ i → f (suc i)) d i
```

<!--en-->
## A truth value, decided into a bit
<!--zh-->
## 把一个真值判定成一位
<!--ja-->
## 真理値を一ビットに決定する
<!--/-->

<!--en-->
Excluded middle turns each proposition into the Boolean bit used by a mask, and
the two specifications recover truth and falsity from that bit.
<!--zh-->
排中律把每个命题化为掩码所用的布尔位，而两条规格从该位分别读回真与假。
<!--ja-->
排中律は各命題をマスクで使うブール値へ変え、二つの仕様はそのビットから真と偽をそれぞれ読み戻す。
<!--/-->

<!--en-->
The excluded middle hands over a disjunction, and a mask wants a bit, so the two
have to be introduced to each other. The verdict is taken as an argument rather
than looked up inside the definition: that is what lets the two round-trip lemmas
be proved by matching on it, with the truth value itself given explicitly, since
an implicit argument buried under `⟨_⟩` is never inferred.
<!--zh-->
排中律交出的是一个析取，而掩码要的是一位，故须为二者引见。裁决作为实参收下，而不是在定义内部去查：正是这一点让两条来回引理能靠对它作模式匹配来证明；而真值本身显式给出，因为埋在 `⟨_⟩` 之下的隐式实参从来推不出来。
<!--/-->

```agda
decideOf : (P : Ω) → (⟨ P ⟩ ⊎ (⟨ P ⟩ → Empty.⊥)) → Bool
decideOf P (inl _) = true
decideOf P (inr _) = false

decide-true : (P : Ω) (s : ⟨ P ⟩ ⊎ (⟨ P ⟩ → Empty.⊥)) → ⟨ P ⟩ → decideOf P s ≡ true
decide-true P (inl _)  p = refl
decide-true P (inr np) p = Empty.rec (np p)

decide-sound : (P : Ω) (s : ⟨ P ⟩ ⊎ (⟨ P ⟩ → Empty.⊥)) → decideOf P s ≡ true → ⟨ P ⟩
decide-sound P (inl p) _ = p
decide-sound P (inr _) e = Empty.rec (false≢true e)
```

<!--en-->
## The definable subsets of a tallied stage
<!--zh-->
## 已清点阶段的可定义子集
<!--ja-->
## 数え上げられた段階の定義可能部分集合
<!--/-->

<!--en-->
From a tally of `Lset σ`{.Agda}, `PowerStep.powerTally`{.Agda} enumerates every
definable subset by choosing a mask and forming the corresponding finite set.
<!--zh-->
从 `Lset σ`{.Agda} 的点名册出发，`PowerStep.powerTally`{.Agda} 通过选择掩码并形成相应有穷集，枚举每个可定义子集。
<!--ja-->
`Lset σ`{.Agda} の数え上げから、`PowerStep.powerTally`{.Agda} はマスクを選んで対応する有限集合を作り、すべての定義可能部分集合を列挙する。
<!--/-->

<!--en-->
Here is the step that makes finiteness climb. Fix an ordinal `σ` and a tally of
the stage `Lset σ`. Each entry of the tally is a member of that stage, so each
has a name in the stage's small member type, which is what the basic-axioms
chapter's finite disjunction wants; `part` applies a mask to those names and
takes the finite set they span. That set is a definable subset of the stage, for
the reason recorded there: the finite disjunction of "equals this one" carves it
out.

Two specifications relate membership in `part v` to the mask, in each direction.
Then the converse: given any definable subset `x`, mark each entry of the tally
according to whether it belongs to `x`, and `part` of that mask **is** `x`. One
direction is immediate from the specification; the other needs that `x` stays
inside the stage, so that every member of `x` is hit by the tally in the first
place. So the masks tally the definable subsets, and a tally of a stage yields a
tally of the next.
<!--zh-->
下面就是让有穷性上爬的那一步。固定一个序数 `σ` 与阶段 `Lset σ` 的一份点名册。点名册的每个条目都是该阶段的成员，故各自在该阶段的小成员类型中有一个名字，而这正是基本公理一章的有穷析取所要的；`part` 把掩码作用到这些名字上，取它们张成的有穷集合。该集合是这个阶段的可定义子集，理由已记在那里：「等于这一个」的有穷析取把它刻了出来。

两条规格把属于 `part v` 与掩码双向联系起来。然后是逆向：给定任一可定义子集 `x`，按点名册的每个条目是否属于 `x` 给它打上标记，则该掩码的 `part` **就是** `x`。一个方向由规格直接得到；另一个方向需要 `x` 不出该阶段，这样 `x` 的每个成员才首先会被点名册命中。于是诸掩码为可定义子集清了点，而一个阶段的点名册给出下一个阶段的点名册。
<!--/-->

```agda
module PowerStep (σ : S) (oσ : IsOrd σ) (t : Tally (Lset σ)) where
  open Tally t
  open FinOf σ oσ using ( finSet∈𝒟ₒ )

  index : Fin size → ⟪ Lset σ ⟫
  index i = ∈-asFiber {a = item i} {b = Lset σ} (inside i) .fst

  index-eq : (i : Fin size) → ⟪ Lset σ ⟫↪ (index i) ≡ item i
  index-eq i = ∈-asFiber {a = item i} {b = Lset σ} (inside i) .snd

  chosen : Vec Bool size → Σ[ k ∈ ℕ ] (Fin k → ⟪ Lset σ ⟫)
  chosen v = select size index v

  part : Vec Bool size → S
  part v = finSet (chosen v .fst) (λ j → ⟪ Lset σ ⟫↪ (chosen v .snd j))

  part-def : (v : Vec Bool size) → ⟨ part v ∈ˢ 𝒟ₒ (Lset σ) ⟩
  part-def v = finSet∈𝒟ₒ (chosen v .fst) (chosen v .snd)

  part-out : (v : Vec Bool size) (y : S) → ⟨ y ∈ˢ part v ⟩
           → ∥ Σ[ i ∈ Fin size ] ((lookup i v ≡ true) × (item i ≡ y)) ∥₁
  part-out v y y∈ = PT.map step
    (finSet-out (chosen v .fst) (λ j → ⟪ Lset σ ⟫↪ (chosen v .snd j)) y y∈)
    where
    step : Σ[ j ∈ Fin (chosen v .fst) ] (⟪ Lset σ ⟫↪ (chosen v .snd j) ≡ y)
         → Σ[ i ∈ Fin size ] ((lookup i v ≡ true) × (item i ≡ y))
    step (j , q) = out .fst
                 , ( out .snd .fst
                   , (sym (index-eq (out .fst))
                      ∙ cong ⟪ Lset σ ⟫↪ (sym (out .snd .snd)) ∙ q) )
      where
      out : Σ[ i ∈ Fin size ] ((lookup i v ≡ true) × (chosen v .snd j ≡ index i))
      out = select-out size index v j

  part-mem : (v : Vec Bool size) (i : Fin size) → lookup i v ≡ true
           → ⟨ item i ∈ˢ part v ⟩
  part-mem v i e = subst (λ w → ⟨ w ∈ˢ part v ⟩) path
    (finSet-in (chosen v .fst) (λ j → ⟪ Lset σ ⟫↪ (chosen v .snd j))
      (⟪ Lset σ ⟫↪ (chosen v .snd (ins .fst))) ∣ ins .fst , refl ∣₁)
    where
    ins : Σ[ j ∈ Fin (chosen v .fst) ] (chosen v .snd j ≡ index i)
    ins = select-in size index v i e
    path : ⟪ Lset σ ⟫↪ (chosen v .snd (ins .fst)) ≡ item i
    path = cong ⟪ Lset σ ⟫↪ (ins .snd) ∙ index-eq i

  maskOf : S → Vec Bool size
  maskOf x = marks size item (λ y → decideOf (y ∈ˢ x) (lem (y ∈ˢ x)))

  part-mask : (x : S) → ⟨ x ∈ˢ 𝒟ₒ (Lset σ) ⟩ → part (maskOf x) ≡ x
  part-mask x x∈ = extensionalV (λ y → ⇔toPath (fwd y) (bwd y))
    where
    fwd : (y : S) → ⟨ y ∈ˢ part (maskOf x) ⟩ → ⟨ y ∈ˢ x ⟩
    fwd y y∈ = PT.rec (snd (y ∈ˢ x)) step (part-out (maskOf x) y y∈)
      where
      step : Σ[ i ∈ Fin size ] ((lookup i (maskOf x) ≡ true) × (item i ≡ y))
           → ⟨ y ∈ˢ x ⟩
      step (i , e , q) = subst (λ w → ⟨ w ∈ˢ x ⟩) q
        (decide-sound (item i ∈ˢ x) (lem (item i ∈ˢ x))
          (sym (marks-lookup size item
                 (λ z → decideOf (z ∈ˢ x) (lem (z ∈ˢ x))) i) ∙ e))
    bwd : (y : S) → ⟨ y ∈ˢ x ⟩ → ⟨ y ∈ˢ part (maskOf x) ⟩
    bwd y y∈x = PT.rec (snd (y ∈ˢ part (maskOf x))) step
      (onto y (𝒟ₒ∋⊆ (Lset σ) x x∈ y y∈x))
      where
      step : Σ[ i ∈ Fin size ] (item i ≡ y) → ⟨ y ∈ˢ part (maskOf x) ⟩
      step (i , q) = subst (λ w → ⟨ w ∈ˢ part (maskOf x) ⟩) q
        (part-mem (maskOf x) i
          (marks-lookup size item (λ z → decideOf (z ∈ˢ x) (lem (z ∈ˢ x))) i
           ∙ decide-true (item i ∈ˢ x) (lem (item i ∈ˢ x))
               (subst (λ w → ⟨ w ∈ˢ x ⟩) (sym q) y∈x)))

  powerTally : Tally (𝒟ₒ (Lset σ))
  powerTally = record
    { size   = maskCount size
    ; item   = λ j → part (maskAt size j)
    ; inside = λ j → part-def (maskAt size j)
    ; onto   = cover }
    where
    cover : (x : S) → ⟨ x ∈ˢ 𝒟ₒ (Lset σ) ⟩
          → ∥ Σ[ j ∈ Fin (maskCount size) ] (part (maskAt size j) ≡ x) ∥₁
    cover x x∈ = ∣ mask-onto size (maskOf x) .fst
                 , (cong part (mask-onto size (maskOf x) .snd) ∙ part-mask x x∈) ∣₁
```

<!--en-->
## Smallest elements, and well-foundedness
<!--zh-->
## 最小元与良基性
<!--ja-->
## 最小要素と整礎性
<!--/-->

<!--en-->
A finite tally lets `leastOfTally`{.Agda} scan any inhabited predicate for its
least witness; classically, this least-element principle yields well-foundedness.
<!--zh-->
有穷点名册让 `leastOfTally`{.Agda} 扫描任意非空谓词以找到最小见证；在经典逻辑下，这条最小元原理给出良基性。
<!--ja-->
有限な数え上げにより `leastOfTally`{.Agda} は任意の inhabited な述語を走査して最小の証人を求め、古典論理の下でこの最小要素原理から整礎性が得られる。
<!--/-->

<!--en-->
Now the half of the argument that uses the tally rather than building one. Fix a
type with a relation that is trichotomous, irreflexive and transitive, that is,
everything a strict well-order asks for except being well founded.

`scan` walks a finite family and returns either an entry that satisfies the
predicate and is smallest among the entries that do, or the assurance that no
entry satisfies it. It is a plain recursion on the length: at each step the
excluded middle decides the predicate at the head, trichotomy compares the head
with the best found so far, and the four combinations are the four clauses.
Nothing is truncated anywhere, which matters, because the caller wants an actual
element and not a mere existence.

Given a family that hits everyone, `least` upgrades this to a smallest element
of any inhabited predicate over the whole type: the "no entry satisfies it"
branch is refuted by the witness, whose fibre in the family the predicate would
have to hit.

Well-foundedness follows, and this is where the finiteness is spent. Being
accessible is a proposition, so the excluded middle decides it. If some element
were not accessible, there would be a smallest inaccessible one; everything below
it is then accessible, which makes it accessible after all. The contradiction is
the proof.
<!--zh-->
现在轮到论证中使用点名册、而非制造点名册的那一半。固定一个类型及其上一个三歧、非自反且传递的关系，也就是严格良序所要求的一切，只差良基。

`scan` 走过一个有穷族，返回的要么是一个满足该谓词、且在满足者之中最小的条目，要么是「没有条目满足它」的保证。它是沿长度的普通递归：每一步由排中律判定谓词在头部是否成立，由三歧比较头部与迄今为止的最佳者，四种组合即四条子句。全程无一处截断，而这很要紧，因为调用方要的是一个货真价实的元素，不是仅仅的存在性。

给定一个命中所有人的族，`least` 把它升级为「整个类型上任一非空谓词的最小元」：「没有条目满足它」那一支被见证者驳倒，因为该谓词本该命中它在族中的纤维。

良基性随之而来，而有穷性正是花在这里。可及是一个命题，故排中律判定它。若某个元素不可及，则存在一个最小的不可及者；于是比它小的一切皆可及，这反倒使它可及。矛盾即是证明。
<!--/-->

```agda
module Search {A : Type (ℓ-suc ℓ)} (_≺_ : A → A → Type (ℓ-suc ℓ))
              (tri : (a b : A) → Tri (a ≺ b) (a ≡ b) (b ≺ a))
              (irr : (a : A) → a ≺ a → Empty.⊥)
              (trans : (a b c : A) → a ≺ b → b ≺ c → a ≺ c) where

  Least : (P : A → Ω) → A → Type (ℓ-suc ℓ)
  Least P m = ⟨ P m ⟩ × ((b : A) → ⟨ P b ⟩ → b ≺ m → Empty.⊥)

  Found : (P : A → Ω) (n : ℕ) (f : Fin n → A) → Type (ℓ-suc ℓ)
  Found P n f =
    (Σ[ i ∈ Fin n ] (⟨ P (f i) ⟩ × ((j : Fin n) → ⟨ P (f j) ⟩ → f j ≺ f i → Empty.⊥)))
    ⊎ ((i : Fin n) → ⟨ P (f i) ⟩ → Empty.⊥)

  scan : (P : A → Ω) (n : ℕ) (f : Fin n → A) → Found P n f
  scan P zero    f = inr (λ ())
  scan P (suc n) f = combine (scan P n (λ i → f (suc i))) (lem (P (f zero)))
    where
    combine : Found P n (λ i → f (suc i))
            → (⟨ P (f zero) ⟩ ⊎ (⟨ P (f zero) ⟩ → Empty.⊥)) → Found P (suc n) f
    combine (inl (i , pi , mi)) (inl p₀) = decide (tri (f zero) (f (suc i)))
      where
      decide : Tri (f zero ≺ f (suc i)) (f zero ≡ f (suc i)) (f (suc i) ≺ f zero)
             → Found P (suc n) f
      decide (lt h) = inl (zero , (p₀ , minAt))
        where
        minAt : (j : Fin (suc n)) → ⟨ P (f j) ⟩ → f j ≺ f zero → Empty.⊥
        minAt zero    pj hj = irr (f zero) hj
        minAt (suc j) pj hj = mi j pj (trans (f (suc j)) (f zero) (f (suc i)) hj h)
      decide (eq h) = inl (suc i , (pi , minAt))
        where
        minAt : (j : Fin (suc n)) → ⟨ P (f j) ⟩ → f j ≺ f (suc i) → Empty.⊥
        minAt zero    pj hj = irr (f (suc i)) (subst (λ w → w ≺ f (suc i)) h hj)
        minAt (suc j) pj hj = mi j pj hj
      decide (gt h) = inl (suc i , (pi , minAt))
        where
        minAt : (j : Fin (suc n)) → ⟨ P (f j) ⟩ → f j ≺ f (suc i) → Empty.⊥
        minAt zero    pj hj = irr (f (suc i)) (trans (f (suc i)) (f zero) (f (suc i)) h hj)
        minAt (suc j) pj hj = mi j pj hj
    combine (inl (i , pi , mi)) (inr n₀) = inl (suc i , (pi , minAt))
      where
      minAt : (j : Fin (suc n)) → ⟨ P (f j) ⟩ → f j ≺ f (suc i) → Empty.⊥
      minAt zero    pj hj = Empty.rec (n₀ pj)
      minAt (suc j) pj hj = mi j pj hj
    combine (inr none) (inl p₀) = inl (zero , (p₀ , minAt))
      where
      minAt : (j : Fin (suc n)) → ⟨ P (f j) ⟩ → f j ≺ f zero → Empty.⊥
      minAt zero    pj hj = irr (f zero) hj
      minAt (suc j) pj hj = Empty.rec (none j pj)
    combine (inr none) (inr n₀) = inr atAll
      where
      atAll : (i : Fin (suc n)) → ⟨ P (f i) ⟩ → Empty.⊥
      atAll zero    p = n₀ p
      atAll (suc i) p = none i p

  module Over (n : ℕ) (f : Fin n → A)
              (cov : (a : A) → ∥ Σ[ i ∈ Fin n ] (f i ≡ a) ∥₁) where

    least : (P : A → Ω) → ∥ Σ[ a ∈ A ] ⟨ P a ⟩ ∥₁ → Σ[ m ∈ A ] Least P m
    least P h = decide (scan P n f)
      where
      nowhere : ((i : Fin n) → ⟨ P (f i) ⟩ → Empty.⊥) → Empty.⊥
      nowhere none = PT.rec Empty.isProp⊥ atWitness h
        where
        atWitness : Σ[ a ∈ A ] ⟨ P a ⟩ → Empty.⊥
        atWitness (a , pa) = PT.rec Empty.isProp⊥
          (λ { (i , q) → none i (subst (λ w → ⟨ P w ⟩) (sym q) pa) }) (cov a)
      decide : Found P n f → Σ[ m ∈ A ] Least P m
      decide (inl (i , pi , mi)) = f i , (pi , everywhere)
        where
        everywhere : (b : A) → ⟨ P b ⟩ → b ≺ f i → Empty.⊥
        everywhere b pb hb = PT.rec Empty.isProp⊥
          (λ { (j , q) → mi j (subst (λ w → ⟨ P w ⟩) (sym q) pb)
                              (subst (λ w → w ≺ f i) (sym q) hb) }) (cov b)
      decide (inr none) = Empty.rec (nowhere none)

    wellFounded : WellFounded _≺_
    wellFounded a = fromDec (lem (Acc _≺_ a , isPropAcc a))
      where
      fromDec : (Acc _≺_ a ⊎ (Acc _≺_ a → Empty.⊥)) → Acc _≺_ a
      fromDec (inl h) = h
      fromDec (inr nh) = Empty.rec (found .snd .fst (acc below))
        where
        NotAcc : A → Ω
        NotAcc b = (Acc _≺_ b → Empty.⊥) , isProp¬ _
        found : Σ[ m ∈ A ] Least NotAcc m
        found = least NotAcc ∣ a , nh ∣₁
        below : (b : A) → b ≺ found .fst → Acc _≺_ b
        below b hb = pick (lem (Acc _≺_ b , isPropAcc b))
          where
          pick : (Acc _≺_ b ⊎ (Acc _≺_ b → Empty.⊥)) → Acc _≺_ b
          pick (inl h)  = h
          pick (inr nb) = Empty.rec (found .snd .snd b nb hb)
```

<!--en-->
## The earliest disagreement
<!--zh-->
## 最先的分歧
<!--ja-->
## 最初の相違
<!--/-->

<!--en-->
Two subsets are ordered by the least base element on which membership differs;
the following proofs establish trichotomy, transitivity, and irreflexivity, and
use finiteness for well-foundedness.
<!--zh-->
两个子集按隶属发生差异的最小基底元素排序；下文证明三歧性、传递性与非自反性，并用有穷性得到良基性。
<!--ja-->
二つの部分集合を、所属が異なる最小の基底要素によって順序づける。以下では三分性、推移性、非反射性を証明し、有限性から整礎性を得る。
<!--/-->

<!--en-->
Fix a set `A` and a relation `R` on sets, to be read as an order on the members
of `A`. Two subsets of `A` are compared by looking at where they disagree. A
witness that `x` comes before `y` is a member `z` of `A` that belongs to `y` and
not to `x`, such that `x` and `y` **agree** below `z`, meaning that every member
of `A` that `R` puts before `z` belongs to one exactly when it belongs to the
other. Read backwards: `z` is the earliest point of disagreement, and `y` is the
one that has it.

Irreflexivity is immediate and needs no hypothesis at all: a witness for `x`
against itself would belong to `x` and not belong to `x`.
<!--zh-->
固定一个集合 `A` 与集合之上的一个关系 `R`，后者读作 `A` 的诸成员上的一个序。`A` 的两个子集，按它们在何处分歧来比较。「`x` 先于 `y`」的见证，是 `A` 的一个成员 `z`，它属于 `y` 而不属于 `x`，且 `x` 与 `y` 在 `z` 之下**一致**，意即 `A` 中被 `R` 排在 `z` 之前的每个成员，属于其中之一当且仅当属于另一个。倒过来读：`z` 就是最先的分歧点，而 `y` 是持有它的那一个。

非自反性立刻成立，且完全不需要任何前提：`x` 对自己的见证会既属于 `x` 又不属于 `x`。
<!--/-->

```agda
Agrees : (R : S → S → Ω) (A x y z : S) → Type (ℓ-suc ℓ)
Agrees R A x y z = (w : S) → ⟨ w ∈ˢ A ⟩ → ⟨ R w z ⟩
                 → (⟨ w ∈ˢ x ⟩ → ⟨ w ∈ˢ y ⟩) × (⟨ w ∈ˢ y ⟩ → ⟨ w ∈ˢ x ⟩)

Witness : (R : S → S → Ω) (A x y z : S) → Type (ℓ-suc ℓ)
Witness R A x y z =
  ⟨ z ∈ˢ A ⟩ × ⟨ z ∈ˢ y ⟩ × (⟨ z ∈ˢ x ⟩ → Empty.⊥) × Agrees R A x y z

precedes : (R : S → S → Ω) (A : S) → S → S → Ω
precedes R A x y = ∥ Σ[ z ∈ S ] Witness R A x y z ∥₁ , PT.squash₁

precedes-irrefl : (R : S → S → Ω) (A x : S) → ⟨ precedes R A x x ⟩ → Empty.⊥
precedes-irrefl R A x = PT.rec Empty.isProp⊥ (λ { (z , _ , z∈ , z∉ , _) → z∉ z∈ })
```

<!--en-->
Transitivity and trichotomy do need hypotheses on the base order, and the two
need different ones, so both are collected in one module: trichotomy and
transitivity of `R` on the members of `A`, and the smallest-element principle
for `R` over those members. In the tower these come from the stage below.

Transitivity is a comparison of two witnesses. If `x` comes before `y` at `p` and
`y` comes before `z` at `q`, then `p` and `q` cannot be equal, since `p` belongs
to `y` and `q` does not; and whichever of the two is smaller witnesses that `x`
comes before `z`. Both branches check the same two things: that the smaller point
is on the right side, and that the agreement below it composes.
<!--zh-->
传递性与三歧确实需要关于基底序的前提，而二者所需不同，故一并收进一个模块：`R` 在 `A` 的诸成员上的三歧与传递，以及 `R` 在那些成员上的最小元原则。在塔中，这些都来自下面那个阶段。

传递性是两个见证之间的比较。若 `x` 在 `p` 处先于 `y`，`y` 在 `q` 处先于 `z`，则 `p` 与 `q` 不可能相等，因为 `p` 属于 `y` 而 `q` 不属于；而二者中较小的那个就见证了 `x` 先于 `z`。两支要核对的是同样两件事：较小的那一点站对了边，以及它之下的一致性可以复合。
<!--/-->

```agda
module Difference (R : S → S → Ω) (A : S)
  (baseTri : (a b : S) → ⟨ a ∈ˢ A ⟩ → ⟨ b ∈ˢ A ⟩ → Tri ⟨ R a b ⟩ (a ≡ b) ⟨ R b a ⟩)
  (baseTrans : (a b c : S) → ⟨ R a b ⟩ → ⟨ R b c ⟩ → ⟨ R a c ⟩)
  (baseLeast : (P : S → Ω) → ∥ Σ[ a ∈ S ] (⟨ a ∈ˢ A ⟩ × ⟨ P a ⟩) ∥₁
             → Σ[ m ∈ S ] (⟨ m ∈ˢ A ⟩ × ⟨ P m ⟩
                 × ((b : S) → ⟨ b ∈ˢ A ⟩ → ⟨ P b ⟩ → ⟨ R b m ⟩ → Empty.⊥)))
  where

  precedes-trans : (x y z : S) → ⟨ precedes R A x y ⟩ → ⟨ precedes R A y z ⟩
                 → ⟨ precedes R A x z ⟩
  precedes-trans x y z hxy hyz =
    PT.rec PT.squash₁ (λ wp → PT.rec PT.squash₁ (both wp) hyz) hxy
    where
    both : Σ[ p ∈ S ] Witness R A x y p → Σ[ q ∈ S ] Witness R A y z q
         → ⟨ precedes R A x z ⟩
    both (p , p∈A , p∈y , p∉x , agp) (q , q∈A , q∈z , q∉y , agq) =
      decide (baseTri p q p∈A q∈A)
      where
      decide : Tri ⟨ R p q ⟩ (p ≡ q) ⟨ R q p ⟩ → ⟨ precedes R A x z ⟩
      decide (lt h) = ∣ p , (p∈A , (agq p p∈A h .fst p∈y , (p∉x , ag))) ∣₁
        where
        ag : Agrees R A x z p
        ag w w∈A hw =
            (λ wx → agq w w∈A (baseTrans w p q hw h) .fst (agp w w∈A hw .fst wx))
          , (λ wz → agp w w∈A hw .snd (agq w w∈A (baseTrans w p q hw h) .snd wz))
      decide (eq h) = Empty.rec (q∉y (subst (λ v → ⟨ v ∈ˢ y ⟩) h p∈y))
      decide (gt h) = ∣ q , (q∈A , (q∈z , (q∉x , ag))) ∣₁
        where
        q∉x : ⟨ q ∈ˢ x ⟩ → Empty.⊥
        q∉x qx = q∉y (agp q q∈A h .fst qx)
        ag : Agrees R A x z q
        ag w w∈A hw =
            (λ wx → agq w w∈A hw .fst (agp w w∈A (baseTrans w q p hw h) .fst wx))
          , (λ wz → agp w w∈A (baseTrans w q p hw h) .snd (agq w w∈A hw .snd wz))
```

<!--en-->
Trichotomy is where the excluded middle and the smallest-element principle are
spent. Ask whether the two subsets disagree anywhere in `A`. If they do not, they
agree everywhere in `A`; since both stay inside `A`, they agree everywhere at
all, and extensionality identifies them. If they do, there is an earliest point
of disagreement, and one further decision, whether that point belongs to the
first subset, says which way the comparison goes. Agreement below the point is
free in both branches: nothing below it disagrees, by the choice of the point.

The excluded middle is used a second time inside `agree`, to turn "not
disagreeing" into "agreeing"; that step is exactly a double negation and cannot
be had for less.
<!--zh-->
三歧正是花掉排中律与最小元原则的地方。先问这两个子集在 `A` 中是否有分歧之处。若没有，则它们在 `A` 中处处一致；又因二者都不出 `A`，故它们根本就处处一致，外延性把它们认同。若有，则存在一个最先的分歧点，再作一次判定，即该点是否属于第一个子集，就说明比较朝哪个方向走。该点之下的一致性在两支中都是白得的：按该点的选法，它之下无一处分歧。

排中律在 `agree` 内部第二次被使用，用来把「没有分歧」变成「一致」；这一步恰是一次双重否定的消去，再便宜不了。
<!--/-->

```agda
  precedes-tri : (x y : S) → ((w : S) → ⟨ w ∈ˢ x ⟩ → ⟨ w ∈ˢ A ⟩)
                           → ((w : S) → ⟨ w ∈ˢ y ⟩ → ⟨ w ∈ˢ A ⟩)
               → Tri ⟨ precedes R A x y ⟩ (x ≡ y) ⟨ precedes R A y x ⟩
  precedes-tri x y x⊆ y⊆ = decide (lem (Some , PT.squash₁))
    where
    Apart : S → Ω
    Apart w = ∥ (⟨ w ∈ˢ x ⟩ × (⟨ w ∈ˢ y ⟩ → Empty.⊥))
              ⊎ ((⟨ w ∈ˢ x ⟩ → Empty.⊥) × ⟨ w ∈ˢ y ⟩) ∥₁ , PT.squash₁
    Some : Type (ℓ-suc ℓ)
    Some = ∥ Σ[ a ∈ S ] (⟨ a ∈ˢ A ⟩ × ⟨ Apart a ⟩) ∥₁
    agree : (w : S) → (⟨ Apart w ⟩ → Empty.⊥)
          → (⟨ w ∈ˢ x ⟩ → ⟨ w ∈ˢ y ⟩) × (⟨ w ∈ˢ y ⟩ → ⟨ w ∈ˢ x ⟩)
    agree w na = fwd , bwd
      where
      fwd : ⟨ w ∈ˢ x ⟩ → ⟨ w ∈ˢ y ⟩
      fwd wx = pick (lem (w ∈ˢ y))
        where
        pick : (⟨ w ∈ˢ y ⟩ ⊎ (⟨ w ∈ˢ y ⟩ → Empty.⊥)) → ⟨ w ∈ˢ y ⟩
        pick (inl h)  = h
        pick (inr nh) = Empty.rec (na ∣ inl (wx , nh) ∣₁)
      bwd : ⟨ w ∈ˢ y ⟩ → ⟨ w ∈ˢ x ⟩
      bwd wy = pick (lem (w ∈ˢ x))
        where
        pick : (⟨ w ∈ˢ x ⟩ ⊎ (⟨ w ∈ˢ x ⟩ → Empty.⊥)) → ⟨ w ∈ˢ x ⟩
        pick (inl h)  = h
        pick (inr nh) = Empty.rec (na ∣ inr (nh , wy) ∣₁)
    same : (Some → Empty.⊥) → x ≡ y
    same ns = extensionalV step
      where
      nApart : (w : S) → ⟨ Apart w ⟩ → Empty.⊥
      nApart w ha = ns ∣ w , (inA , ha) ∣₁
        where
        inA : ⟨ w ∈ˢ A ⟩
        inA = PT.rec (snd (w ∈ˢ A))
          (λ { (inl (wx , _)) → x⊆ w wx ; (inr (_ , wy)) → y⊆ w wy }) ha
      step : (w : S) → (w ∈ˢ x) ≡ (w ∈ˢ y)
      step w = ⇔toPath (agree w (nApart w) .fst) (agree w (nApart w) .snd)
    decide : (Some ⊎ (Some → Empty.⊥))
           → Tri ⟨ precedes R A x y ⟩ (x ≡ y) ⟨ precedes R A y x ⟩
    decide (inr ns) = eq (same ns)
    decide (inl hs) = side (lem (m ∈ˢ x))
      where
      found : Σ[ m ∈ S ] (⟨ m ∈ˢ A ⟩ × ⟨ Apart m ⟩
                × ((b : S) → ⟨ b ∈ˢ A ⟩ → ⟨ Apart b ⟩ → ⟨ R b m ⟩ → Empty.⊥))
      found = baseLeast Apart hs
      m : S
      m = found .fst
      m∈A : ⟨ m ∈ˢ A ⟩
      m∈A = found .snd .fst
      apartM : ⟨ Apart m ⟩
      apartM = found .snd .snd .fst
      belowM : (w : S) → ⟨ w ∈ˢ A ⟩ → ⟨ R w m ⟩ → ⟨ Apart w ⟩ → Empty.⊥
      belowM w w∈A hw ha = found .snd .snd .snd w w∈A ha hw
      side : (⟨ m ∈ˢ x ⟩ ⊎ (⟨ m ∈ˢ x ⟩ → Empty.⊥))
           → Tri ⟨ precedes R A x y ⟩ (x ≡ y) ⟨ precedes R A y x ⟩
      side (inl mx) = gt ∣ m , (m∈A , (mx , (m∉y , ag))) ∣₁
        where
        m∉y : ⟨ m ∈ˢ y ⟩ → Empty.⊥
        m∉y my = PT.rec Empty.isProp⊥
          (λ { (inl (_ , nmy)) → nmy my ; (inr (nmx , _)) → nmx mx }) apartM
        ag : Agrees R A y x m
        ag w w∈A hw = agree w (belowM w w∈A hw) .snd , agree w (belowM w w∈A hw) .fst
      side (inr nmx) = lt ∣ m , (m∈A , (my , (nmx , ag))) ∣₁
        where
        my : ⟨ m ∈ˢ y ⟩
        my = PT.rec (snd (m ∈ˢ y))
          (λ { (inl (mx , _)) → Empty.rec (nmx mx) ; (inr (_ , h)) → h }) apartM
        ag : Agrees R A x y m
        ag w w∈A hw = agree w (belowM w w∈A hw)
```

<!--en-->
## The finite stages
<!--zh-->
## 有穷诸阶段
<!--ja-->
## 有限段階
<!--/-->

<!--en-->
Recursion over numerals carries both a tally and an earliest-disagreement
well-order from each finite stage to the next.
<!--zh-->
沿数码的递归把点名册与最先分歧良序从每个有穷阶段一并带到下一阶段。
<!--ja-->
数項上の再帰により、数え上げと最初の相違による整列順序を各有限段階から次の段階へ同時に運ぶ。
<!--/-->

<!--en-->
The stages indexed by numerals are the finite ones, and the order on each is
built by recursion: stage zero is empty, and the order on the stage after `n` is
comparison at the earliest disagreement over stage `n`, with stage `n`'s own
order as the base. `before-irrefl` holds at every stage and needs no induction,
since irreflexivity of the comparison needed no hypothesis and stage zero carries
no comparison at all.
<!--zh-->
以数码为索引的阶段就是有穷的那些，而每个阶段上的序沿递归造出：零阶段是空的，而 `n` 之后那个阶段上的序，是在阶段 `n` 之上按最先分歧处的比较，以阶段 `n` 自己的序为基底。`before-irrefl` 在每个阶段都成立且无须归纳，因为该比较的非自反性本就不要前提，而零阶段根本不带任何比较。
<!--/-->

```agda
Tri-map : {ℓ₁ ℓ₂ ℓ₃ ℓ₄ ℓ₅ ℓ₆ : Level}
          {A₁ : Type ℓ₁} {B₁ : Type ℓ₂} {C₁ : Type ℓ₃}
          {A₂ : Type ℓ₄} {B₂ : Type ℓ₅} {C₂ : Type ℓ₆}
        → (A₁ → A₂) → (B₁ → B₂) → (C₁ → C₂) → Tri A₁ B₁ C₁ → Tri A₂ B₂ C₂
Tri-map f g h (lt a) = lt (f a)
Tri-map f g h (eq b) = eq (g b)
Tri-map f g h (gt c) = gt (h c)

finiteStage : ℕ → S
finiteStage n = Lset (# n)

before : ℕ → S → S → Ω
before zero    x y = ⊥
before (suc n) = precedes (before n) (finiteStage n)

before-irrefl : (n : ℕ) (x : S) → ⟨ before n x x ⟩ → Empty.⊥
before-irrefl zero    x h = Empty.rec* h
before-irrefl (suc n) x h = precedes-irrefl (before n) (finiteStage n) x h

zero-empty : (x : S) → ⟨ x ∈ˢ finiteStage zero ⟩ → Empty.⊥
zero-empty x h = PT.rec Empty.isProp⊥ step (Lset-out (# zero) x h)
  where
  step : Σ[ δ ∈ S ] (⟨ δ ∈ˢ ∅ ⟩ × ⟨ x ∈ˢ 𝒟ₒ (Lset δ) ⟩) → Empty.⊥
  step (δ , δ∈ , _) = ∅-empty δ (∈∈ₛ {a = δ} {b = ∅} .fst δ∈)
```

<!--en-->
What the recursion has to carry is a tally, trichotomy and transitivity, and
nothing else: irreflexivity is free at every stage, and well-foundedness is
derived where it is used rather than transported. A point of a stage is a set
together with its membership, which is a proposition, so two points are equal as
soon as their sets are; that is the only bookkeeping in passing between the
statements about sets and the bundle, whose carrier must be a type.
<!--zh-->
递归必须携带的是一份点名册、三歧与传递，别无其他：非自反性在每个阶段都是白得的，而良基性在用到之处现推、不搬运。阶段的一个点，是一个集合连同它的隶属证明，而隶属是命题，故两个点只要集合相等就相等；这就是在「关于集合的陈述」与「载体必须是类型的那个束」之间往返时，全部的记账工作。
<!--/-->

```agda
Point : ℕ → Type (ℓ-suc ℓ)
Point n = Σ[ x ∈ S ] ⟨ x ∈ˢ finiteStage n ⟩

Below : (n : ℕ) → Point n → Point n → Type (ℓ-suc ℓ)
Below n a b = ⟨ before n (a .fst) (b .fst) ⟩

record StageOrder (n : ℕ) : Type (ℓ-suc ℓ) where
  field
    tally : Tally (finiteStage n)
    tri   : (x y : S) → ⟨ x ∈ˢ finiteStage n ⟩ → ⟨ y ∈ˢ finiteStage n ⟩
          → Tri ⟨ before n x y ⟩ (x ≡ y) ⟨ before n y x ⟩
    trans : (x y z : S) → ⟨ before n x y ⟩ → ⟨ before n y z ⟩ → ⟨ before n x z ⟩

module Ordered (n : ℕ) (r : StageOrder n) where
  open StageOrder r public
  open Tally tally

  triPoint : (a b : Point n) → Tri (Below n a b) (a ≡ b) (Below n b a)
  triPoint a b = Tri-map id (Σ≡Prop (λ z → snd (z ∈ˢ finiteStage n))) id
    (tri (a .fst) (b .fst) (a .snd) (b .snd))

  points : Fin size → Point n
  points i = item i , inside i

  covers : (a : Point n) → ∥ Σ[ i ∈ Fin size ] (points i ≡ a) ∥₁
  covers a = PT.map (λ { (i , q) → i , Σ≡Prop (λ z → snd (z ∈ˢ finiteStage n)) q })
    (onto (a .fst) (a .snd))

  open Search (Below n) triPoint (λ a → before-irrefl n (a .fst))
              (λ a b c → trans (a .fst) (b .fst) (c .fst)) public
  open Over size points covers public

  order : SWO (Point n)
  order = record
    { _<∙_   = Below n
    ; tri∙   = triPoint
    ; irr∙   = λ a → before-irrefl n (a .fst)
    ; trans∙ = λ a b c → trans (a .fst) (b .fst) (c .fst)
    ; wf∙    = wellFounded }

  leastMem : (P : S → Ω) → ∥ Σ[ a ∈ S ] (⟨ a ∈ˢ finiteStage n ⟩ × ⟨ P a ⟩) ∥₁
           → Σ[ m ∈ S ] (⟨ m ∈ˢ finiteStage n ⟩ × ⟨ P m ⟩
               × ((b : S) → ⟨ b ∈ˢ finiteStage n ⟩ → ⟨ P b ⟩
                          → ⟨ before n b m ⟩ → Empty.⊥))
  leastMem P h = found .fst .fst
               , ( found .fst .snd
                 , ( found .snd .fst
                   , (λ b b∈ pb hb → found .snd .snd (b , b∈) pb hb) ) )
    where
    Q : Point n → Ω
    Q a = P (a .fst)
    found : Σ[ m ∈ Point n ] Least Q m
    found = least Q (PT.map (λ { (a , a∈ , pa) → (a , a∈) , pa }) h)
```

<!--en-->
And the recursion itself. At zero everything is discharged by the stage being
empty. At a successor the tally is the previous stage's tally raised through the
definable power set, and the two order facts are the two theorems about the
earliest disagreement, applied with the previous stage supplying its trichotomy,
its transitivity and its smallest elements. The identification of a successor
stage with the definable power set below it is used three times, once per field,
and each time only to move a membership statement across it.
<!--zh-->
然后是递归本身。零处，一切都由该阶段为空而清账。后继处，点名册是上一个阶段的点名册经可定义幂集抬上来的，而两条序的事实就是关于最先分歧处的那两条定理，施用时由上一个阶段供给它的三歧、它的传递与它的最小元。「后继阶段与其下的可定义幂集相认同」这一点用了三次，每个字段一次，且每次都只用来把一句隶属陈述搬过去。
<!--/-->

```agda
stageOrder : (n : ℕ) → StageOrder n
stageOrder zero = record { tally = empty ; tri = triZero ; trans = transZero }
  where
  empty : Tally (finiteStage zero)
  empty = record
    { size   = zero
    ; item   = λ ()
    ; inside = λ ()
    ; onto   = λ x x∈ → Empty.rec (zero-empty x x∈) }
  triZero : (x y : S) → ⟨ x ∈ˢ finiteStage zero ⟩ → ⟨ y ∈ˢ finiteStage zero ⟩
          → Tri ⟨ before zero x y ⟩ (x ≡ y) ⟨ before zero y x ⟩
  triZero x y x∈ y∈ = Empty.rec (zero-empty x x∈)
  transZero : (x y z : S) → ⟨ before zero x y ⟩ → ⟨ before zero y z ⟩
            → ⟨ before zero x z ⟩
  transZero x y z h k = Empty.rec* h
stageOrder (suc n) = record { tally = raised ; tri = triSuc ; trans = transSuc }
  where
  module Prev = Ordered n (stageOrder n)
  module Diff = Difference (before n) (finiteStage n) Prev.tri Prev.trans Prev.leastMem
  module Power = PowerStep (# n) (numeral-ord n) Prev.tally

  step : finiteStage (suc n) ≡ 𝒟ₒ (finiteStage n)
  step = Lset-suc (# n)

  raised : Tally (finiteStage (suc n))
  raised = record
    { size   = Tally.size Power.powerTally
    ; item   = Tally.item Power.powerTally
    ; inside = λ i → subst (λ w → ⟨ Tally.item Power.powerTally i ∈ˢ w ⟩) (sym step)
                       (Tally.inside Power.powerTally i)
    ; onto   = λ x x∈ → Tally.onto Power.powerTally x
                          (subst (λ w → ⟨ x ∈ˢ w ⟩) step x∈) }

  members : (x : S) → ⟨ x ∈ˢ finiteStage (suc n) ⟩
          → (w : S) → ⟨ w ∈ˢ x ⟩ → ⟨ w ∈ˢ finiteStage n ⟩
  members x x∈ = 𝒟ₒ∋⊆ (finiteStage n) x (subst (λ v → ⟨ x ∈ˢ v ⟩) step x∈)

  triSuc : (x y : S) → ⟨ x ∈ˢ finiteStage (suc n) ⟩ → ⟨ y ∈ˢ finiteStage (suc n) ⟩
         → Tri ⟨ before (suc n) x y ⟩ (x ≡ y) ⟨ before (suc n) y x ⟩
  triSuc x y x∈ y∈ = Diff.precedes-tri x y (members x x∈) (members y y∈)

  transSuc : (x y z : S) → ⟨ before (suc n) x y ⟩ → ⟨ before (suc n) y z ⟩
           → ⟨ before (suc n) x z ⟩
  transSuc = Diff.precedes-trans
```

<!--en-->
## The limit stage
<!--zh-->
## 极限阶段
<!--ja-->
## 極限段階
<!--/-->

<!--en-->
Every member of `Lset ω`{.Agda} receives its least finite level; comparing levels
first and the local stage order second gives the limit-stage well-order.
<!--zh-->
`Lset ω`{.Agda} 的每个成员取得其最小有穷层号；先比较层号、再比较局部阶段序，便得到极限阶段良序。
<!--ja-->
`Lset ω`{.Agda} の各要素に最小の有限レベルを与え、まずレベルを、次に局所的な段階順序を比較して、極限段階の整列順序を得る。
<!--/-->

<!--en-->
A member of the limit stage appears at some finite stage, since the limit is the
union of the stages below it and each of those is indexed by a numeral. Among
the numerals at which it has appeared there is a smallest, and that number is
its **level**. This is the one place where the well-order of the natural numbers
is spent, and the smallest-element theorem of the well-order chapter is what
spends it.
<!--zh-->
极限阶段的成员现身于某个有穷阶段，因为极限是其下诸阶段的并，而它们各自都以数码为索引。在它已现身的那些数码之中有一个最小者，那个数就是它的**层号**。这是本章唯一花掉自然数良序的地方，而花掉它的正是良序那一章的极小元定理。
<!--/-->

```agda
Limit : Type (ℓ-suc ℓ)
Limit = Σ[ x ∈ S ] ⟨ x ∈ˢ Lset ω ⟩

inSome : (x : S) → ⟨ x ∈ˢ Lset ω ⟩ → ∥ Σ[ n ∈ ℕ ] ⟨ x ∈ˢ finiteStage n ⟩ ∥₁
inSome x h = PT.rec PT.squash₁ atStage (Lset-out ω x h)
  where
  atStage : Σ[ δ ∈ S ] (⟨ δ ∈ˢ ω ⟩ × ⟨ x ∈ˢ 𝒟ₒ (Lset δ) ⟩)
          → ∥ Σ[ n ∈ ℕ ] ⟨ x ∈ˢ finiteStage n ⟩ ∥₁
  atStage (δ , δ∈ω , x∈) = PT.map named δ∈ω
    where
    named : Σ[ k ∈ Lift ℕ ] (# (lower k) ≡ δ) → Σ[ n ∈ ℕ ] ⟨ x ∈ˢ finiteStage n ⟩
    named (k , q) = suc (lower k)
      , subst (λ w → ⟨ x ∈ˢ w ⟩) (sym (Lset-suc (# (lower k))))
          (subst (λ w → ⟨ x ∈ˢ 𝒟ₒ (Lset w) ⟩) (sym q) x∈)

levelData : (a : Limit)
          → Σ[ n ∈ ℕ ] IsLeast natOrder (λ m → a .fst ∈ˢ finiteStage m) n
levelData a =
  leastOf natOrder lem (λ m → a .fst ∈ˢ finiteStage m) (inSome (a .fst) (a .snd))

level : Limit → ℕ
level a = levelData a .fst

level-in : (a : Limit) → ⟨ a .fst ∈ˢ finiteStage (level a) ⟩
level-in a = levelData a .snd .fst
```

<!--en-->
The order on the limit takes the level as the primary key: a member of a lower
level comes first, and two members of the same level are compared by that level's
own order. The equation between levels is carried in the second alternative, and
carried in the direction that lets the second member be read at the first's
level, which is what keeps the definition free of any transport.

Irreflexivity and transitivity are case analyses on that alternative, with the
level equations moving the stage-order facts to the level where they are needed.
Trichotomy compares levels first and defers to the stage only when they agree.
<!--zh-->
极限上的序以层号为主键：层号较低的成员排在前面，而同层的两个成员按该层自己的序比较。层号之间的等式携带在第二支中，且携带的方向使得第二个成员可以在第一个成员的层上读出，正是这一点让定义中不出现任何搬运。

非自反与传递是对那一支的分情形，其中层号等式把阶段序的事实搬到需要它的那一层上。三歧先比较层号，只有层号相同时才交给阶段处理。
<!--/-->

```agda
_≺_ : Limit → Limit → Type (ℓ-suc ℓ)
a ≺ b = Lift {ℓ-zero} {ℓ-suc ℓ} (level a < level b)
      ⊎ ((level b ≡ level a) × ⟨ before (level a) (a .fst) (b .fst) ⟩)

limit-irrefl : (a : Limit) → a ≺ a → Empty.⊥
limit-irrefl a (inl h)       = ¬m<m (lower h)
limit-irrefl a (inr (_ , h)) = before-irrefl (level a) (a .fst) h

limit-trans : (a b c : Limit) → a ≺ b → b ≺ c → a ≺ c
limit-trans a b c (inl h)       (inl k)       = inl (lift (<-trans (lower h) (lower k)))
limit-trans a b c (inl h)       (inr (q , _)) =
  inl (lift (subst (λ j → level a < j) (sym q) (lower h)))
limit-trans a b c (inr (q , _)) (inl k)       =
  inl (lift (subst (λ j → j < level c) q (lower k)))
limit-trans a b c (inr (q , hab)) (inr (p , hbc)) = inr (p ∙ q , joined)
  where
  moved : ⟨ before (level a) (b .fst) (c .fst) ⟩
  moved = subst (λ j → ⟨ before j (b .fst) (c .fst) ⟩) q hbc
  joined : ⟨ before (level a) (a .fst) (c .fst) ⟩
  joined = StageOrder.trans (stageOrder (level a)) (a .fst) (b .fst) (c .fst) hab moved

limit-tri : (a b : Limit) → Tri (a ≺ b) (a ≡ b) (b ≺ a)
limit-tri a b = byLevel (level a ≟ level b)
  where
  byLevel : NatOrder.Trichotomy (level a) (level b) → Tri (a ≺ b) (a ≡ b) (b ≺ a)
  byLevel (NatOrder.lt h) = lt (inl (lift h))
  byLevel (NatOrder.gt h) = gt (inl (lift h))
  byLevel (NatOrder.eq p) = same
    (StageOrder.tri (stageOrder (level a)) (a .fst) (b .fst) (level-in a) b∈)
    where
    b∈ : ⟨ b .fst ∈ˢ finiteStage (level a) ⟩
    b∈ = subst (λ j → ⟨ b .fst ∈ˢ finiteStage j ⟩) (sym p) (level-in b)
    same : Tri ⟨ before (level a) (a .fst) (b .fst) ⟩ (a .fst ≡ b .fst)
               ⟨ before (level a) (b .fst) (a .fst) ⟩
         → Tri (a ≺ b) (a ≡ b) (b ≺ a)
    same (lt h) = lt (inr (sym p , h))
    same (eq q) = eq (Σ≡Prop (λ z → snd (z ∈ˢ Lset ω)) q)
    same (gt h) = gt (inr (p , subst (λ j → ⟨ before j (b .fst) (a .fst) ⟩) p h))
```

<!--en-->
Well-foundedness is two nested inductions, and they are kept apart on purpose.
The outer one is induction on the level, in the library's packaged form, and it
hands down a hypothesis covering every lower level. The inner one is an ordinary
descent along the accessibility that the finite stage already has, which is
legitimate precisely because that stage is finite. A step down in level appeals
to the outer hypothesis; a step within a level appeals to the inner one; and
since the inner function recurses on nothing but its own accessibility argument,
the two never have to be compared.
<!--zh-->
良基性是两层嵌套的归纳，而把它们分开是有意的。外层是对层号的归纳，取库封装好的形式，它交下一个覆盖所有更低层的假设。内层是沿有穷阶段本已具备的可及性作普通下降，而这之所以合法，恰恰是因为那个阶段有穷。降一层的一步诉诸外层假设；层内的一步诉诸内层假设；而由于内层函数除自己的可及性实参外不沿任何东西递归，二者从不需要放在一起比较。
<!--/-->

```agda
accInside : (k : ℕ)
          → ((m : ℕ) → m < k → (b : Limit) → level b ≡ m → Acc _≺_ b)
          → (u : Point k) → Acc (Below k) u
          → (b : Limit) → level b ≡ k → b .fst ≡ u .fst → Acc _≺_ b
accInside k ih u (acc ru) b q e = acc step
  where
  step : (c : Limit) → c ≺ b → Acc _≺_ c
  step c (inl h) = ih (level c) (subst (λ j → level c < j) q (lower h)) c refl
  step c (inr (qb , hc)) = accInside k ih pc (ru pc below) c qc refl
    where
    qc : level c ≡ k
    qc = sym qb ∙ q
    pc : Point k
    pc = c .fst , subst (λ j → ⟨ c .fst ∈ˢ finiteStage j ⟩) qc (level-in c)
    below : Below k pc u
    below = subst (λ v → ⟨ before k (c .fst) v ⟩) e
              (subst (λ j → ⟨ before j (c .fst) (b .fst) ⟩) qc hc)

accByLevel : (k : ℕ) → (b : Limit) → level b ≡ k → Acc _≺_ b
accByLevel = WFI.induction <-wellfounded outer
  where
  outer : (k : ℕ) → ((m : ℕ) → m < k → (b : Limit) → level b ≡ m → Acc _≺_ b)
        → (b : Limit) → level b ≡ k → Acc _≺_ b
  outer k ih b q = accInside k ih here
    (Ordered.wellFounded k (stageOrder k) here) b q refl
    where
    here : Point k
    here = b .fst , subst (λ j → ⟨ b .fst ∈ˢ finiteStage j ⟩) q (level-in b)

limit-wf : WellFounded _≺_
limit-wf a = accByLevel (level a) a refl

limitOrder : SWO Limit
limitOrder = record
  { _<∙_   = _≺_
  ; tri∙   = limit-tri
  ; irr∙   = limit-irrefl
  ; trans∙ = limit-trans
  ; wf∙    = limit-wf }
```

<!--en-->
## Recap
<!--zh-->
## 小结
<!--ja-->
## まとめ
<!--/-->

<!--en-->
Finite tallies climb through definable powersets, support the well-founded
earliest-disagreement order at every numeral stage, and culminate in
`limitOrder`{.Agda} on `Lset ω`{.Agda}.
<!--zh-->
有穷点名册沿可定义幂集上升，支撑每个数码阶段处良基的最先分歧序，并最终给出 `Lset ω`{.Agda} 上的 `limitOrder`{.Agda}。
<!--ja-->
有限な数え上げは定義可能冪集合を通じて上昇し、各数項段階で整礎な最初の相違の順序を支え、最後に `Lset ω`{.Agda} 上の `limitOrder`{.Agda} を与える。
<!--/-->

<!--en-->
`Tally`{.Agda} is all the finiteness this chapter owns: a finite family that hits
every member, with no injectivity and no decidable equality asked for.
`PowerStep.powerTally`{.Agda} carries one up to the definable power set, by
enumerating the bit vectors over the tally and observing that every subset of a
tallied stage is definable; `stageOrder`{.Agda} then runs that step along the
numerals, so every finite stage has a tally.

`precedes`{.Agda} compares two subsets at the earliest point where they
disagree. It is irreflexive for free, transitive by comparing two witnesses, and
trichotomous by the excluded middle together with the base's smallest elements.
Well-foundedness is not a property of the comparison at all: it comes from the
tally, through `Search`{.Agda}, and would fail over an infinite base, which is
why the finiteness had to be established first.

`limitOrder`{.Agda} is a strict well-order on the members of `Lset ω`{.Agda},
with the level as the primary key and each finite stage's own order inside a
level. It is the interface the axiom of choice will take: with it,
`leastOf`{.Agda} picks a member out of any inhabited property of members of the
limit stage, and picks the same one every time.
<!--zh-->
`Tally`{.Agda} 就是本章拥有的全部有穷性：一个命中每个成员的有穷族，既不要求单射，也不要求可判定的相等。`PowerStep.powerTally`{.Agda} 把它抬到可定义幂集上，办法是枚举点名册上的位向量，并指出已清点阶段的每个子集都可定义；`stageOrder`{.Agda} 随后沿诸数码跑完这一步，于是每个有穷阶段都有一份点名册。

`precedes`{.Agda} 在两个子集最先分歧之处比较它们。它的非自反性是白得的，传递性由比较两个见证得到，三歧则由排中律连同基底的最小元得到。良基性压根不是这个比较自身的性质：它来自点名册，经由 `Search`{.Agda}，且在无穷基底上会失效，这正是必须先立下有穷性的原因。

`limitOrder`{.Agda} 是 `Lset ω`{.Agda} 诸成员上的一个严格良序，以层号为主键，层内则用各有穷阶段自己的序。它就是选择公理将要取用的接口：有了它，`leastOf`{.Agda} 能从极限阶段诸成员的任一非空性质中挑出一个成员，且每次挑出同一个。
<!--/-->
