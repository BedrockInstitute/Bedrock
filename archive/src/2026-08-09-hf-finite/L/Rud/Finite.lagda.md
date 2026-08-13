# Finite tallies

<!--en-->
The hereditarily-finite carrier chapter consumes finiteness in two places:
the generic tally machinery (a finite family hitting every member of a set,
the masks that turn a subset into a bit vector, the step that raises a tally
to the definable power set, and the search that finds a smallest element of
an inhabited property over a finite base), and its first-limit instances
(the tally of every finite level of the S-tower, the limit predicate at `ω`,
and the power obligation at a finite carrier the level holds). This chapter
is that content's surviving home, harvested from the retiring choice tree
and the retiring base-block chapter. The machinery is written parameterized
by its carrier, relation, or level; only the first-limit block is fixed at
`ω`, where the finiteness itself lives, because a member of `ω` is exactly a
numeral.
<!--zh-->
遗传有穷载体一章在两处消费有穷性：通用的点名册机器 (命中集合每个成员的有穷族、把子集变成位向量的掩码、把点名册抬到可定义幂集上的步进，以及在有限基底上为非空性质找出最小元的搜索)，及其第一个极限处的实例 (S 塔每个有穷层的点名册、`ω` 处的极限谓词，以及「被层级收下的有穷载体的幂义务」)。本章就是那份内容的幸存住处，自退役的选择树与退役的基块章收割而来。机器一律以其载体、关系或层级为参数；只有第一个极限块固定在 `ω` 处，因为有穷性本身住在那里，`ω` 的成员恰是数码。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V )

module L.Rud.Finite {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) (A : V ℓ) where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ; extensionalV; ∈-irrefl )
open import L.Constructible {ℓ} using ( IsOrd; Lset; 𝒟ₒ; 𝒟ₒ∋⊆ )
open import L.Ordinal {ℓ} using ( numeral-ord; ω-ord; #∈ω )
open import L.WellOrder.Base {ℓ-suc ℓ} using ( Tri; lt; eq; gt )
open import L.Axioms.Basic {ℓ}
  using ( finSet; finSet-in; finSet-out; Lset-suc; module FinOf )
open import L.Rud.Ops {ℓ} using ( F0; F5; F0-spec; F5-spec )
open import L.Rud.OrdArith {ℓ} lem using ( isLimit; isSucc; predecessor-mem )
open import L.Rud.Step {ℓ} lem A using
  ( step; Sset; Sset-trans; Sset-suc; Sset-zero
  ; step-in; step-in-self; step-in-img; step-out
  ; u'; u-self-in; u'-in; u'-cases; split→u'
  ; StepArm; arm-member; arm-self; arm-image
  ; Op16; Fof; Fof-f0; Fof-f5; f0; f5
  ; op0; op1; op2; op3; op4; op5; op6; op7; op8; op9; op10; op11; op12; op13; op14; op15
  ; Jset-rud )
open import L.Rud.Bridge {ℓ} lem A using ( Lset-zero; ∅∈Sset )

open import Cubical.HITs.CumulativeHierarchy.Properties
  using ( ⟪_⟫; ⟪_⟫↪; ∈ₛ⟪_⟫↪_; ∈-asFiber; ∈∈ₛ; _≡ₕ_ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ∅; ∅-empty; module InfinitySet )
module IS = InfinitySet {ℓ}
open import Cubical.Data.Sum using ( _⊎_; inl; inr )
open import Cubical.Data.Nat using ( _+_; _·_ )
open import Cubical.Data.Bool using ( Bool; true; false; false≢true )
open import Cubical.Foundations.Function using ( _∘_ )
open import Cubical.Foundations.Equiv using ( _≃_; invEq; retEq )
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁; squash₁ )
open import Cubical.Functions.Logic using ( ⇔toPath )
open import Cubical.Data.FinData.Properties
  using ( module FinSumChar; module FinProdChar )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ
```

<!--en-->
## Tallies
<!--zh-->
## 点名册
<!--/-->

<!--en-->
Finiteness enters as a **tally**: a number, a family of that many sets all
belonging to `A`, and the statement that every member of `A` is merely one of
them. `onto` reads "the family hits everyone".

Nothing is asked about repetitions and nothing is asked about deciding
equality: a tally is a surjection from a finite index, not a bijection. That
is deliberate. The two uses ahead are a scan (which does not mind seeing an
element twice) and a bit vector (which does not mind either), and asking for
less means the tally of the next stage is cheaper to build. The whole
finiteness vocabulary of this chapter is this record plus the index
arithmetic that builds one tally out of another.
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
<!--/-->

<!--en-->
Tallying a power set means enumerating bit vectors, and there are twice as
many vectors of length `n + 1` as of length `n`. So one piece of index
arithmetic is needed: an index below `a + b` is either an index below `a` or
an index below `b`, and conversely. Only one of the two round trips is ever
used, so only that one is proved; `bumpLeft` is the shift that makes the
recursion on `a` type-check.
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
<!--/-->

<!--en-->
A **mask** of length `n` is a vector of `n` bits; it will say, of a tallied
set, which entries to keep. There are `maskCount n` of them, that number
being two to the `n` written as an iterated doubling, and `maskAt` reads an
index as a mask: split the index in half, and the half it lands in supplies
the leading bit while the rest supplies the tail. Every mask is read off
some index, which is `mask-onto`, and that is the only property of the
enumeration anyone needs. It is not injective on the nose and does not have
to be.
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
## Selecting a sub-family, and marking one
<!--zh-->
## 选出一个子族，以及打上标记
<!--/-->

<!--en-->
`select` applies a mask to a family: it keeps the entries whose bit is `true`
and returns them as a family again, together with its own length. The length
is **produced by the recursion**, which is the point: nothing has to be
counted, and no arithmetic relates the answer to the mask.

Two specifications say what the result contains, and both are untruncated,
because each is read straight off the same recursion. `marks` runs in the
other direction, turning a decision on the entries into the mask that
records it.
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
select-out (suc n) f (false ∷ v) j       = go (select-out n (λ i → f (suc i)) v j)
  where
  go : Σ[ i ∈ Fin n ] ((lookup i v ≡ true)
         × (select n (λ i → f (suc i)) v .snd j ≡ f (suc i)))
     → Σ[ i ∈ Fin (suc n) ] ((lookup i (false ∷ v) ≡ true)
         × (select (suc n) f (false ∷ v) .snd j ≡ f i))
  go (i , e , q) = suc i , (e , q)
select-out (suc n) f (true ∷ v)  zero    = zero , (refl , refl)
select-out (suc n) f (true ∷ v)  (suc j) = go (select-out n (λ i → f (suc i)) v j)
  where
  go : Σ[ i ∈ Fin n ] ((lookup i v ≡ true)
         × (select n (λ i → f (suc i)) v .snd j ≡ f (suc i)))
     → Σ[ i ∈ Fin (suc n) ] ((lookup i (true ∷ v) ≡ true)
         × (select (suc n) f (true ∷ v) .snd (suc j) ≡ f i))
  go (i , e , q) = suc i , (e , q)

select-in : {ℓ' : Level} {X : Type ℓ'} (n : ℕ) (f : Fin n → X) (v : Vec Bool n)
            (i : Fin n) → lookup i v ≡ true
          → Σ[ j ∈ Fin (select n f v .fst) ] (select n f v .snd j ≡ f i)
select-in zero    f []          ()      e
select-in (suc n) f (false ∷ v) zero    e = Empty.rec (false≢true e)
select-in (suc n) f (false ∷ v) (suc i) e = select-in n (λ i → f (suc i)) v i e
select-in (suc n) f (true ∷ v)  zero    e = zero , refl
select-in (suc n) f (true ∷ v)  (suc i) e = go (select-in n (λ i → f (suc i)) v i e)
  where
  go : Σ[ j ∈ Fin (select n (λ i → f (suc i)) v .fst) ]
         (select n (λ i → f (suc i)) v .snd j ≡ f (suc i))
     → Σ[ j ∈ Fin (select (suc n) f (true ∷ v) .fst) ]
         (select (suc n) f (true ∷ v) .snd j ≡ f (suc i))
  go (j , q) = suc j , q

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
<!--/-->

<!--en-->
The excluded middle hands over a disjunction, and a mask wants a bit, so the
two have to be introduced to each other. The verdict is taken as an argument
rather than looked up inside the definition: that is what lets the two
round-trip lemmas be proved by matching on it, with the truth value itself
given explicitly, since an implicit argument buried under `⟨_⟩` is never
inferred.
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
<!--/-->

<!--en-->
Here is the step that makes finiteness climb. Fix an ordinal `σ` and a tally
of the stage `Lset σ`. Each entry of the tally is a member of that stage, so
each has a name in the stage's small member type, which is what the
basic-axioms chapter's finite disjunction wants; `part` applies a mask to
those names and takes the finite set they span. That set is a definable
subset of the stage, for the reason recorded there: the finite disjunction
of "equals this one" carves it out.

Two specifications relate membership in `part v` to the mask, in each
direction. Then the converse: given any definable subset `x`, mark each entry
of the tally according to whether it belongs to `x`, and `part` of that mask
**is** `x`. One direction is immediate from the specification; the other
needs that `x` stays inside the stage, so that every member of `x` is hit by
the tally in the first place. So the masks tally the definable subsets, and a
tally of a stage yields a tally of the next.
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
  part-out v y y∈ = PT.map go
    (finSet-out (chosen v .fst) (λ j → ⟪ Lset σ ⟫↪ (chosen v .snd j)) y y∈)
    where
    go : Σ[ j ∈ Fin (chosen v .fst) ] (⟪ Lset σ ⟫↪ (chosen v .snd j) ≡ y)
       → Σ[ i ∈ Fin size ] ((lookup i v ≡ true) × (item i ≡ y))
    go (j , q) = out .fst
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
    fwd y y∈ = PT.rec (snd (y ∈ˢ x)) go (part-out (maskOf x) y y∈)
      where
      go : Σ[ i ∈ Fin size ] ((lookup i (maskOf x) ≡ true) × (item i ≡ y))
         → ⟨ y ∈ˢ x ⟩
      go (i , e , q) = subst (λ w → ⟨ w ∈ˢ x ⟩) q
        (decide-sound (item i ∈ˢ x) (lem (item i ∈ˢ x))
          (sym (marks-lookup size item
                 (λ z → decideOf (z ∈ˢ x) (lem (z ∈ˢ x))) i) ∙ e))
    bwd : (y : S) → ⟨ y ∈ˢ x ⟩ → ⟨ y ∈ˢ part (maskOf x) ⟩
    bwd y y∈x = PT.rec (snd (y ∈ˢ part (maskOf x))) go
      (onto y (𝒟ₒ∋⊆ (Lset σ) x x∈ y y∈x))
      where
      go : Σ[ i ∈ Fin size ] (item i ≡ y) → ⟨ y ∈ˢ part (maskOf x) ⟩
      go (i , q) = subst (λ w → ⟨ w ∈ˢ part (maskOf x) ⟩) q
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
## Smallest elements over a finite base
<!--zh-->
## 有限基底上的最小元
<!--/-->

<!--en-->
Now the half of the argument that uses the tally rather than building one.
Fix a type with a relation that is trichotomous, irreflexive and transitive,
that is, everything a strict well-order asks for except being well founded.

`scan` walks a finite family and returns either an entry that satisfies the
predicate and is smallest among the entries that do, or the assurance that no
entry satisfies it. It is a plain recursion on the length: at each step the
excluded middle decides the predicate at the head, trichotomy compares the
head with the best found so far, and the four combinations are the four
clauses. Nothing is truncated anywhere, which matters, because the caller
wants an actual element and not a mere existence.

Given a family that hits everyone, `least` upgrades this to a smallest
element of any inhabited predicate over the whole type: the "no entry
satisfies it" branch is refuted by the witness, whose fibre in the family the
predicate would have to hit. This chapter's consumer asks only for the
smallest element, so the well-foundedness half of the delivered search (which
would buy accessibility from the same scan) is not carried here.
<!--zh-->
现在轮到论证中使用点名册、而非制造点名册的那一半。固定一个类型及其上一个三歧、非自反且传递的关系，也就是严格良序所要求的一切，只差良基。

`scan` 走过一个有穷族，返回的要么是一个满足该谓词、且在满足者之中最小的条目，要么是「没有条目满足它」的保证。它是沿长度的普通递归：每一步由排中律判定谓词在头部是否成立，由三歧比较头部与迄今为止的最佳者，四种组合即四条子句。全程无一处截断，而这很要紧，因为调用方要的是一个货真价实的元素，不是仅仅的存在性。

给定一个命中所有人的族，`least` 把它升级为「整个类型上任一非空谓词的最小元」：「没有条目满足它」那一支被见证者驳倒，因为该谓词本该命中它在族中的纤维。本章的消费者只索取最小元，故已交付搜索中把同一扫描买成可及性的良基半边不在此处携带。
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
```

<!--en-->
## The L-side tallies of the finite stages
<!--zh-->
## 有穷阶段的 L 侧点名册
<!--/-->

<!--en-->
The constructible stages indexed by numerals are finite, and their tallies
are the one fact the power obligation needs about the L-side: the tally of
the stage is carried up to the definable power set by `PowerStep.powerTally`,
and the successor stage is the definable power of the stage below it. The
delivered order machinery that once accompanied this iteration (the
earliest-disagreement comparison and the limit order) has no consumer here,
so the iteration is carried tally-only.
<!--zh-->
以数码为索引的可构造阶段有穷，而它们的点名册就是幂义务关于 L 侧所需的唯一事实：阶段的名册由 `PowerStep.powerTally` 抬到可定义幂集上，后继阶段又恰是其下阶段的可定义幂。曾伴随这次迭代的序机器 (最先分歧处的比较与极限序) 在此没有消费者，故迭代只带点名册。
<!--/-->

```agda
ltally : (n : ℕ) → Tally (Lset (IS.# n))
ltally zero = subst Tally (sym Lset-zero) empty
  where
  empty : Tally ∅
  empty = record
    { size   = zero
    ; item   = λ ()
    ; inside = λ ()
    ; onto   = λ x x∈ → Empty.rec (∅-empty x (∈∈ₛ {a = x} {b = ∅} .fst x∈)) }
ltally (suc n) = record
  { size   = Tally.size Power.powerTally
  ; item   = Tally.item Power.powerTally
  ; inside = λ i → subst (λ w → ⟨ Tally.item Power.powerTally i ∈ˢ w ⟩) (sym stepEq)
                       (Tally.inside Power.powerTally i)
  ; onto   = λ x x∈ → Tally.onto Power.powerTally x
                        (subst (λ w → ⟨ x ∈ˢ w ⟩) stepEq x∈) }
  where
  module Power = PowerStep (IS.# n) (numeral-ord n) (ltally n)
  stepEq : Lset (IS.# (suc n)) ≡ 𝒟ₒ (Lset (IS.# n))
  stepEq = Lset-suc (IS.# n)
```

<!--en-->
## Tallies on the S-tower
<!--zh-->
## S 塔上的点名册
<!--/-->

<!--en-->
The new content of the S-side is its own tally: every `Sset (# n)` is finite.
The step is a union over the finite square, so a tally of `u` yields one of
`step u` in three pieces: a tally of `u ∪ {u}` (the members of `u` plus `u`
itself), an enumeration of the argument square as an index arithmetic on
`Fin`, and the sixteen image values over that square, read through the sealed
membership surface of the step. The square is enumerated at the finite index
by the library's sum and product equivalences, and memberships are read at
small indices only. No fiber is ever extracted from the presentation of a
union.
<!--zh-->
S 侧的新内容就是它自己的点名册：每个 `Sset (# n)` 都有穷。step 是有限平方上的并，故 `u` 的点名册给出 `step u` 的，分三件：`u ∪ {u}` 的点名册 (`u` 的成员加 `u` 自身)、作为 `Fin` 索引算术的参数平方枚举，以及该平方上十六个像值，全部经由 step 的封印成员表面读出。平方在有穷索引处由库的和与积等价枚举，成员关系只在小区处读出。绝不从某个并的表示中提取纤维。
<!--/-->

```agda
-- perf: R-35/P-c: the square and the sixteen images are enumerated at the Fin
-- index (FinSumChar/FinProdChar); membership is read only through the sealed
-- step surface and the sett's small index, never via ⋃-fiber extraction
module Sside (u : S) (t : Tally u) where
  open Tally t public

  K : ℕ
  K = suc size

  up : Fin K → S
  up zero    = u
  up (suc i) = item i

  up-inside : (i : Fin K) → ⟨ up i ∈ˢ u' u ⟩
  up-inside zero    = u-self-in u
  up-inside (suc i) = u'-in u (item i) (inside i)

  up-onto : (x : S) → ⟨ x ∈ˢ u' u ⟩ → ∥ Σ[ i ∈ Fin K ] (up i ≡ x) ∥₁
  up-onto x h = go (u'-cases u x h)
    where
    go : (⟨ x ∈ˢ u ⟩ ⊎ (x ≡ u)) → ∥ Σ[ i ∈ Fin K ] (up i ≡ x) ∥₁
    go (inl x∈u) = PT.map (λ { (i , q) → suc i , q }) (onto x x∈u)
    go (inr x≡u) = ∣ zero , sym x≡u ∣₁

  name : Fin K → ⟪ u' u ⟫
  name i = ∈-asFiber {a = up i} {b = u' u} (up-inside i) .fst

  name-eq : (i : Fin K) → ⟪ u' u ⟫↪ (name i) ≡ up i
  name-eq i = ∈-asFiber {a = up i} {b = u' u} (up-inside i) .snd

  Esq : Fin K × Fin K ≃ Fin (K · K)
  Esq = FinProdChar.Equiv K K

  pairIdx : Fin K → Fin K → Fin (K · K)
  pairIdx i j = Esq .fst (i , j)

  pair-ret : (i j : Fin K) → invEq Esq (pairIdx i j) ≡ (i , j)
  pair-ret i j = retEq Esq (i , j)

  imgItem : (i : Op16) → Fin (K · K) → S
  imgItem i j = Fof i (⟪ u' u ⟫↪ (name (invEq Esq j .fst)))
                      (⟪ u' u ⟫↪ (name (invEq Esq j .snd)))

  img-inside : (i : Op16) (j : Fin (K · K)) → ⟨ imgItem i j ∈ˢ step u ⟩
  img-inside i j = step-in-img u (imgItem i j) i a b a∈ b∈ refl
    where
    p : Fin K × Fin K
    p = invEq Esq j
    a : S
    a = ⟪ u' u ⟫↪ (name (p .fst))
    b : S
    b = ⟪ u' u ⟫↪ (name (p .snd))
    a∈ : ⟨ a ∈ˢ u' u ⟩
    a∈ = ∈∈ₛ {a = a} {b = u' u} .snd (∈ₛ⟪ u' u ⟫↪ (name (p .fst)))
    b∈ : ⟨ b ∈ˢ u' u ⟩
    b∈ = ∈∈ₛ {a = b} {b = u' u} .snd (∈ₛ⟪ u' u ⟫↪ (name (p .snd)))

  img-onto : (i : Op16) (a b : S) (a∈ : ⟨ a ∈ˢ u' u ⟩) (b∈ : ⟨ b ∈ˢ u' u ⟩)
           → (x : S) → ⟨ x ≡ₕ Fof i a b ⟩
           → ∥ Σ[ j ∈ Fin (K · K) ] (imgItem i j ≡ x) ∥₁
  img-onto i a b a∈ b∈ x x≡ =
    PT.rec squash₁ (λ { (ia , ea) →
      PT.map (λ { (ib , eb) → pairIdx ia ib , path ia ib ea eb }) (up-onto b b∈) })
      (up-onto a a∈)
    where
    path : (ia ib : Fin K) → up ia ≡ a → up ib ≡ b → imgItem i (pairIdx ia ib) ≡ x
    path ia ib ea eb =
      cong₂ (Fof i) (first ia ea) (second ib eb) ∙ sym x≡
      where
      first : (ia : Fin K) → up ia ≡ a
            → ⟪ u' u ⟫↪ (name (invEq Esq (pairIdx ia ib) .fst)) ≡ a
      first ia ea = cong (λ q → ⟪ u' u ⟫↪ (name (q .fst))) (pair-ret ia ib) ∙ name-eq ia ∙ ea
      second : (ib : Fin K) → up ib ≡ b
             → ⟪ u' u ⟫↪ (name (invEq Esq (pairIdx ia ib) .snd)) ≡ b
      second ib eb = cong (λ q → ⟪ u' u ⟫↪ (name (q .snd))) (pair-ret ia ib) ∙ name-eq ib ∙ eb

  sixteen : ℕ
  sixteen = suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (zero))))))))))))))))

  op16 : Fin sixteen → Op16
  op16 zero                                     = op0
  op16 (suc zero)                               = op1
  op16 (suc (suc zero))                         = op2
  op16 (suc (suc (suc zero)))                   = op3
  op16 (suc (suc (suc (suc zero))))             = op4
  op16 (suc (suc (suc (suc (suc zero)))))       = op5
  op16 (suc (suc (suc (suc (suc (suc zero)))))) = op6
  op16 (suc (suc (suc (suc (suc (suc (suc zero)))))))                     = op7
  op16 (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))               = op8
  op16 (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))         = op9
  op16 (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))   = op10
  op16 (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))) = op11
  op16 (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))))) = op12
  op16 (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))))) = op13
  op16 (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))))))) = op14
  op16 (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))))))) = op15

  op16Onto : (i : Op16) → Σ[ j ∈ Fin sixteen ] (op16 j ≡ i)
  op16Onto op0  = zero , refl
  op16Onto op1  = suc zero , refl
  op16Onto op2  = suc (suc zero) , refl
  op16Onto op3  = suc (suc (suc zero)) , refl
  op16Onto op4  = suc (suc (suc (suc zero))) , refl
  op16Onto op5  = suc (suc (suc (suc (suc zero)))) , refl
  op16Onto op6  = suc (suc (suc (suc (suc (suc zero))))) , refl
  op16Onto op7  = suc (suc (suc (suc (suc (suc (suc zero)))))) , refl
  op16Onto op8  = suc (suc (suc (suc (suc (suc (suc (suc zero))))))) , refl
  op16Onto op9  = suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) , refl
  op16Onto op10 = suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))) , refl
  op16Onto op11 = suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))) , refl
  op16Onto op12 = suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))) , refl
  op16Onto op13 = suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))))) , refl
  op16Onto op14 = suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))))) , refl
  op16Onto op15 = suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))))))) , refl

  E16 : Fin sixteen × Fin (K · K) ≃ Fin (sixteen · (K · K))
  E16 = FinProdChar.Equiv sixteen (K · K)

  imgItem16 : Fin (sixteen · (K · K)) → S
  imgItem16 j = imgItem (op16 (invEq E16 j .fst)) (invEq E16 j .snd)

  img-inside16 : (j : Fin (sixteen · (K · K))) → ⟨ imgItem16 j ∈ˢ step u ⟩
  img-inside16 j = img-inside (op16 (invEq E16 j .fst)) (invEq E16 j .snd)

  img-onto16 : (i : Op16) (a b : S) (a∈ : ⟨ a ∈ˢ u' u ⟩) (b∈ : ⟨ b ∈ˢ u' u ⟩)
             → (x : S) → ⟨ x ≡ₕ Fof i a b ⟩
             → ∥ Σ[ j ∈ Fin (sixteen · (K · K)) ] (imgItem16 j ≡ x) ∥₁
  img-onto16 i a b a∈ b∈ x x≡ = PT.map atIdx (img-onto i a b a∈ b∈ x x≡)
    where
    atIdx : Σ[ j ∈ Fin (K · K) ] (imgItem i j ≡ x)
          → Σ[ j ∈ Fin (sixteen · (K · K)) ] (imgItem16 j ≡ x)
    atIdx (j , q) = E16 .fst (op16Onto i .fst , j) , path j q
      where
      path : (j : Fin (K · K)) → imgItem i j ≡ x → imgItem16 (E16 .fst (op16Onto i .fst , j)) ≡ x
      path j q = cong (λ r → imgItem (op16 (r .fst)) (r .snd)) (retEq E16 (op16Onto i .fst , j))
               ∙ cong (λ w → Fof w (⟪ u' u ⟫↪ (name (invEq Esq j .fst)))
                                 (⟪ u' u ⟫↪ (name (invEq Esq j .snd)))) (op16Onto i .snd)
               ∙ q

  Esum : Fin K ⊎ Fin (sixteen · (K · K)) ≃ Fin (K + sixteen · (K · K))
  Esum = FinSumChar.Equiv K (sixteen · (K · K))

  stepSplit : Fin K ⊎ Fin (sixteen · (K · K)) → S
  stepSplit (inl i)  = up i
  stepSplit (inr j') = imgItem16 j'

  stepItem : Fin (K + sixteen · (K · K)) → S
  stepItem j = stepSplit (invEq Esum j)

  step-inside : (j : Fin (K + sixteen · (K · K))) → ⟨ stepItem j ∈ˢ step u ⟩
  step-inside j = go (invEq Esum j)
    where
    go : (s : Fin K ⊎ Fin (sixteen · (K · K))) → ⟨ stepSplit s ∈ˢ step u ⟩
    go (inl zero)    = step-in-self u
    go (inl (suc i)) = step-in u (item i) (inside i)
    go (inr j')      = img-inside16 j'

  step-onto : (x : S) → ⟨ x ∈ˢ step u ⟩
            → ∥ Σ[ j ∈ Fin (K + sixteen · (K · K)) ] (stepItem j ≡ x) ∥₁
  step-onto x x∈ = PT.rec squash₁ go (step-out u x x∈)
    where
    atInl : Σ[ i ∈ Fin K ] (up i ≡ x)
          → Σ[ j ∈ Fin (K + sixteen · (K · K)) ] (stepItem j ≡ x)
    atInl (i , q) = Esum .fst (inl i) , (cong stepSplit (retEq Esum (inl i)) ∙ q)
    atInr : Σ[ j' ∈ Fin (sixteen · (K · K)) ] (imgItem16 j' ≡ x)
          → Σ[ j ∈ Fin (K + sixteen · (K · K)) ] (stepItem j ≡ x)
    atInr (j' , q) = Esum .fst (inr j') , (cong stepSplit (retEq Esum (inr j')) ∙ q)
    go : StepArm u x → ∥ Σ[ j ∈ Fin (K + sixteen · (K · K)) ] (stepItem j ≡ x) ∥₁
    go (arm-member x∈u) = PT.map atInl (up-onto x (u'-in u x x∈u))
    go (arm-self x≡u)   = ∣ atInl (zero , sym x≡u) ∣₁
    go (arm-image i a b a-split b-split x≡) =
      PT.map atInr
        (img-onto16 i a b (split→u' u a a-split) (split→u' u b b-split) x x≡)

  stepTally : Tally (step u)
  stepTally = record
    { size   = K + sixteen · (K · K)
    ; item   = stepItem
    ; inside = step-inside
    ; onto   = step-onto }

sTally : (n : ℕ) → Tally (Sset (IS.# n))
sTally zero = record
  { size   = zero
  ; item   = λ ()
  ; inside = λ ()
  ; onto   = λ x x∈ → Empty.rec (∅-empty x (∈∈ₛ {a = x} {b = ∅} .fst
      (subst (λ w → ⟨ x ∈ˢ w ⟩) Sset-zero x∈))) }
sTally (suc n) = record
  { size   = Tally.size st
  ; item   = Tally.item st
  ; inside = λ i → subst (λ w → ⟨ Tally.item st i ∈ˢ w ⟩) (sym stepEq)
                        (Tally.inside st i)
  ; onto   = λ x x∈ → Tally.onto st x (subst (λ w → ⟨ x ∈ˢ w ⟩) stepEq x∈) }
  where
  st : Tally (step (Sset (IS.# n)))
  st = Sside.stepTally (Sset (IS.# n)) (sTally n)
  stepEq : Sset (IS.# (suc n)) ≡ step (Sset (IS.# n))
  stepEq = Sset-suc (IS.# n)
```

<!--en-->
## The first limit
<!--zh-->
## 第一个极限
<!--/-->

<!--en-->
The tower's limit machinery is parameterized by the limit predicate, and at
`ω` two of its three conjuncts are missing from the record: that `ω` is not
zero, and that it is not a successor. The first is the numeral zero entering
`ω`. The second takes a hypothetical predecessor: the predecessor belongs to
`ω`, so it is one of the numerals, so its successor is also a numeral and
hence a member of `ω`; but its successor is `ω` itself, and regularity
forbids self-membership.

With the limit predicate in hand, the level's closure under the basis
operations is the instantiation of the delivered rud closure at `ω`
(`op-in-J`), and the empty set's membership in the level is the delivered
zero-membership read at the numeral zero (`∅∈Ssetω`).
<!--zh-->
塔的极限机器以极限谓词为参数，而在 `ω` 处，它的三个合取项中两个缺于记录：`ω` 非零，且 `ω` 非后继。其一是数码零进入 `ω`。其二取一个假想的前驱：前驱属于 `ω`，故它是某个数码，于是它的后继也是数码，从而是 `ω` 的成员；但它的后继就是 `ω` 自身，正则性禁止自属。

极限谓词在手之后，层级对基底运算的封闭就是已交付 rud 闭包在 `ω` 处的实例 (`op-in-J`)，空集在层级中的隶属则是已交付零隶属读式在数码零处的读法 (`∅∈Ssetω`)。
<!--/-->

```agda
limω : ⟨ isLimit IS.ω ⟩
limω = (ω-ord , (ω-not-zero , ω-not-succ))
  where
  ω-not-zero : (IS.ω ≡ ∅) → Empty.⊥
  ω-not-zero e = ∅-empty ∅ (∈∈ₛ {a = ∅} {b = ∅} .fst (subst (λ w → ⟨ ∅ ∈ˢ w ⟩) e (#∈ω zero)))
  ω-not-succ : ⟨ isSucc IS.ω ⟩ → Empty.⊥
  ω-not-succ (β , ordβ , e) = PT.rec Empty.isProp⊥ numeral-of (predecessor-mem β IS.ω e)
    where
    numeral-of : Σ[ k ∈ Lift ℕ ] (IS.# (lower k) ≡ β) → Empty.⊥
    numeral-of (k , q) = ∈-irrefl IS.ω
      (subst (λ w → ⟨ w ∈ˢ IS.ω ⟩) (cong IS.sucV q ∙ e) (#∈ω (suc (lower k))))

∅∈Ssetω : ⟨ ∅ ∈ˢ Sset IS.ω ⟩
∅∈Ssetω = ∅∈Sset IS.ω (#∈ω 0)

op-in-J : (i : Op16) → (a b : S) → ⟨ a ∈ˢ Sset IS.ω ⟩ → ⟨ b ∈ˢ Sset IS.ω ⟩
        → ⟨ Fof i a b ∈ˢ Sset IS.ω ⟩
op-in-J i a b a∈ b∈ = Jset-rud IS.ω limω i a b a∈ b∈

opF0 : (a b : S) → ⟨ a ∈ˢ Sset IS.ω ⟩ → ⟨ b ∈ˢ Sset IS.ω ⟩ → ⟨ F0 a b ∈ˢ Sset IS.ω ⟩
opF0 a b a∈ b∈ = subst (λ w → ⟨ w ∈ˢ Sset IS.ω ⟩) (Fof-f0 a b) (op-in-J f0 a b a∈ b∈)

opF5 : (a b : S) → ⟨ a ∈ˢ Sset IS.ω ⟩ → ⟨ b ∈ˢ Sset IS.ω ⟩ → ⟨ F5 a b ∈ˢ Sset IS.ω ⟩
opF5 a b a∈ b∈ = subst (λ w → ⟨ w ∈ˢ Sset IS.ω ⟩) (Fof-f5 a b) (op-in-J f5 a b a∈ b∈)
```

<!--en-->
## Finite tables in the limit level
<!--zh-->
## 极限层中的有穷表
<!--/-->

<!--en-->
The workhorse lemma: a finite table whose entries all lie in `Sset ω` spans a
set that is itself a member of `Sset ω`. The proof is an induction on the
table's length. The empty table is the empty set, which enters `Sset ω`
through the first numeral. A table with a head is the singleton of its head
united with the tail's set, and the union is realized as the union operation
applied to the unordered pair of the singleton and the tail: both are members
of `Sset ω` by the induction hypothesis, and the limit level is closed under
every operation of the basis (`Jset-rud`), so the composite is a member. The
equality between the table and the operation composite is proved
extensionally in both directions, by the two-armed membership specifications
of the pair and the union.
<!--zh-->
工作马引理：一张条目全部落在 `Sset ω` 里的有穷表，张成的集合自身是 `Sset ω` 的成员。证明沿表的长度归纳。空表即空集，空集经第一个数码进入 `Sset ω`。带头的表是头之单点集与尾之集合的并，而这个并实现为并运算作用于单点集与尾集所成的无序对：二者由归纳假设都是 `Sset ω` 的成员，而极限层对基底的每个运算封闭 (`Jset-rud`)，故复合仍是成员。表与运算复合之间的等式按两个方向外延地证明，用对与并的双臂成员规格。
<!--/-->

```agda
ext-⊆ : {u v : S} → ((x : S) → ⟨ x ∈ˢ u ⟩ → ⟨ x ∈ˢ v ⟩)
      → ((x : S) → ⟨ x ∈ˢ v ⟩ → ⟨ x ∈ˢ u ⟩) → u ≡ v
ext-⊆ sub sup = extensionalV (λ x → ⇔toPath (sub x) (sup x))

finSet0∅ : (h : Fin 0 → S) → finSet 0 h ≡ ∅
finSet0∅ h = ext-⊆ sub sup
  where
  sub : (y : S) → ⟨ y ∈ˢ finSet 0 h ⟩ → ⟨ y ∈ˢ ∅ ⟩
  sub y y∈ = PT.rec (snd (y ∈ˢ ∅)) (λ { (() , _) }) (finSet-out 0 h y y∈)
  sup : (y : S) → ⟨ y ∈ˢ ∅ ⟩ → ⟨ y ∈ˢ finSet 0 h ⟩
  sup y y∈ = Empty.rec (∅-empty y (∈∈ₛ {a = y} {b = ∅} .fst y∈))

finSetSuc : (n : ℕ) (h : Fin (suc n) → S)
          → finSet (suc n) h
          ≡ F5 (F0 (F0 (h zero) (h zero)) (finSet n (h ∘ suc))) (h zero)
finSetSuc n h = ext-⊆ sub sup
  where
  X : S
  X = finSet n (h ∘ suc)
  P : S
  P = F0 (F0 (h zero) (h zero)) X
  sub : (y : S) → ⟨ y ∈ˢ finSet (suc n) h ⟩ → ⟨ y ∈ˢ F5 P (h zero) ⟩
  sub y y∈ = PT.rec (snd (y ∈ˢ F5 P (h zero))) go (finSet-out (suc n) h y y∈)
    where
    go : Σ[ i ∈ Fin (suc n) ] (h i ≡ y) → ⟨ y ∈ˢ F5 P (h zero) ⟩
    go (zero , q) = F5-spec P (h zero) y .snd
      ∣ F0 (h zero) (h zero)
      , ( F0-spec (F0 (h zero) (h zero)) X (F0 (h zero) (h zero)) .snd ∣ inl refl ∣₁
        , F0-spec (h zero) (h zero) y .snd ∣ inl (sym q) ∣₁ ) ∣₁
    go (suc i , q) = F5-spec P (h zero) y .snd
      ∣ X , ( F0-spec (F0 (h zero) (h zero)) X X .snd ∣ inr refl ∣₁
            , finSet-in n (h ∘ suc) y ∣ i , q ∣₁ ) ∣₁
  sup : (y : S) → ⟨ y ∈ˢ F5 P (h zero) ⟩ → ⟨ y ∈ˢ finSet (suc n) h ⟩
  sup y y∈ = PT.rec (snd (y ∈ˢ finSet (suc n) h)) go
    (F5-spec P (h zero) y .fst y∈)
    where
    go : Σ[ v ∈ S ] ⟨ (v ∈ˢ P) ⊓ (y ∈ˢ v) ⟩ → ⟨ y ∈ˢ finSet (suc n) h ⟩
    go (v , v∈P , y∈v) = atV
      (F0-spec (F0 (h zero) (h zero)) X v .fst v∈P)
      where
      atV : ⟨ (v ≡ₕ F0 (h zero) (h zero)) ⊔ (v ≡ₕ X) ⟩ → ⟨ y ∈ˢ finSet (suc n) h ⟩
      atV hv = PT.rec (snd (y ∈ˢ finSet (suc n) h)) atCases hv
        where
        atCases : (⟨ v ≡ₕ F0 (h zero) (h zero) ⟩ ⊎ ⟨ v ≡ₕ X ⟩) → ⟨ y ∈ˢ finSet (suc n) h ⟩
        atCases (inl v≡) = atSingl
          (F0-spec (h zero) (h zero) y .fst (subst (λ w → ⟨ y ∈ˢ w ⟩) v≡ y∈v))
          where
          atSingl : ⟨ (y ≡ₕ h zero) ⊔ (y ≡ₕ h zero) ⟩ → ⟨ y ∈ˢ finSet (suc n) h ⟩
          atSingl hy = PT.rec (snd (y ∈ˢ finSet (suc n) h)) atEq hy
            where
            atEq : (⟨ y ≡ₕ h zero ⟩ ⊎ ⟨ y ≡ₕ h zero ⟩) → ⟨ y ∈ˢ finSet (suc n) h ⟩
            atEq (inl y≡) = finSet-in (suc n) h y ∣ zero , sym y≡ ∣₁
            atEq (inr y≡) = finSet-in (suc n) h y ∣ zero , sym y≡ ∣₁
        atCases (inr v≡) = atX (subst (λ w → ⟨ y ∈ˢ w ⟩) v≡ y∈v)
          where
          atX : ⟨ y ∈ˢ X ⟩ → ⟨ y ∈ˢ finSet (suc n) h ⟩
          atX y∈X = PT.rec (snd (y ∈ˢ finSet (suc n) h))
            (λ { (i , q) → finSet-in (suc n) h y ∣ suc i , q ∣₁ })
            (finSet-out n (h ∘ suc) y y∈X)

finSetMem : (n : ℕ) (h : Fin n → S) → ((i : Fin n) → ⟨ h i ∈ˢ Sset IS.ω ⟩)
          → ⟨ finSet n h ∈ˢ Sset IS.ω ⟩
finSetMem zero h hin = subst (λ w → ⟨ w ∈ˢ Sset IS.ω ⟩) (sym (finSet0∅ h)) ∅∈Ssetω
finSetMem (suc n) h hin =
  subst (λ w → ⟨ w ∈ˢ Sset IS.ω ⟩) (sym (finSetSuc n h)) big
  where
  S1 : S
  S1 = F0 (h zero) (h zero)
  X : S
  X = finSet n (h ∘ suc)
  S1∈ : ⟨ S1 ∈ˢ Sset IS.ω ⟩
  S1∈ = opF0 (h zero) (h zero) (hin zero) (hin zero)
  X∈ : ⟨ X ∈ˢ Sset IS.ω ⟩
  X∈ = finSetMem n (h ∘ suc) (λ i → hin (suc i))
  big : ⟨ F5 (F0 S1 X) (h zero) ∈ˢ Sset IS.ω ⟩
  big = opF5 (F0 S1 X) (h zero) (opF0 S1 X S1∈ X∈) (hin zero)
```

<!--en-->
## The power obligation at a finite carrier
<!--zh-->
## 有穷载体处的幂义务
<!--/-->

<!--en-->
Fix a finite carrier `Lset (# k)` that the tower holds, together with its
tally. Every part of a mask is a finite table of members of the carrier,
hence a finite table of members of `Sset ω`, so the table lemma places each
part in the level. The collection of parts is itself a finite table of
members of the level, so the table lemma places the collection in the level
as well. The definable power of the carrier is exactly that collection, by
the mask round trip in one direction and the definability of every part in
the other. That is the power obligation: the definable power of a finite
carrier that the tower holds is again held by the tower. The tally is stated
as a parameter, so the obligation reads over any finiteness evidence of the
carrier; the L-side iteration supplies it.

The instance at a member of `ω` is then assembled in the shape the consumer
uses: a member of `ω` is merely a numeral, so the power obligation at that
numeral, transported across the numeral equality, gives the definable power
of the constructible stage at `ζ`; and the successor collapse identifies that
power with the stage one step up.
<!--zh-->
固定塔所收下的一个有穷载体 `Lset (# k)`，连同它的点名册。每个掩码的 `part` 都是载体成员所成的有穷表，从而是 `Sset ω` 成员所成的有穷表，故表引理把每个 `part` 放进该层。诸 `part` 的全体自身是层成员所成的有穷表，故表引理也把全体放进该层。载体的可定义幂恰是那个全体，一个方向用掩码来回，另一个方向用每个 `part` 的可定义性。这就是幂义务：塔收下的有穷载体的可定义幂，仍被塔收下。点名册写成参数，故义务对载体的任何有穷性证据都成立；L 侧迭代供给它。

`ω` 成员处的实例随后按消费者使用的形状装配：`ω` 的成员仅仅是某个数码，故该数码处的幂义务经数码等式搬运，给出 `ζ` 处可构造阶段的可定义幂；后继坍缩再把该幂认同为再上一层的阶段。
<!--/-->

```agda
module Power (k : ℕ) (C∈J : ⟨ Lset (IS.# k) ∈ˢ Sset IS.ω ⟩)
             (tally : Tally (Lset (IS.# k))) where
  σ : S
  σ = IS.# k
  oσ : IsOrd σ
  oσ = numeral-ord k
  t : Tally (Lset σ)
  t = tally
  module PS = PowerStep σ oσ t

  carrier : (w : S) → ⟨ w ∈ˢ Lset σ ⟩ → ⟨ w ∈ˢ Sset IS.ω ⟩
  carrier w w∈L = Sset-trans IS.ω {x = Lset σ} {y = w} w∈L C∈J

  part-in-J : (v : Vec Bool (Tally.size t)) → ⟨ PS.part v ∈ˢ Sset IS.ω ⟩
  part-in-J v =
    finSetMem (PS.chosen v .fst) (λ j → ⟪ Lset σ ⟫↪ (PS.chosen v .snd j))
      (λ j → carrier (⟪ Lset σ ⟫↪ (PS.chosen v .snd j))
        (∈∈ₛ {a = ⟪ Lset σ ⟫↪ (PS.chosen v .snd j)} {b = Lset σ} .snd
          (∈ₛ⟪ Lset σ ⟫↪ (PS.chosen v .snd j))))

  M : ℕ
  M = maskCount (Tally.size t)
  fam : Fin M → S
  fam j = PS.part (maskAt (Tally.size t) j)

  defPow≡finSet : 𝒟ₒ (Lset σ) ≡ finSet M fam
  defPow≡finSet = ext-⊆ sub sup
    where
    sub : (y : S) → ⟨ y ∈ˢ 𝒟ₒ (Lset σ) ⟩ → ⟨ y ∈ˢ finSet M fam ⟩
    sub y y∈ = finSet-in M fam y ∣ mo .fst
      , (cong PS.part (mo .snd) ∙ PS.part-mask y y∈) ∣₁
      where
      mo : Σ[ j ∈ Fin M ] (maskAt (Tally.size t) j ≡ PS.maskOf y)
      mo = mask-onto (Tally.size t) (PS.maskOf y)
    sup : (y : S) → ⟨ y ∈ˢ finSet M fam ⟩ → ⟨ y ∈ˢ 𝒟ₒ (Lset σ) ⟩
    sup y y∈ = PT.rec (snd (y ∈ˢ 𝒟ₒ (Lset σ))) go (finSet-out M fam y y∈)
      where
      go : Σ[ j ∈ Fin M ] (fam j ≡ y) → ⟨ y ∈ˢ 𝒟ₒ (Lset σ) ⟩
      go (j , q) = subst (λ w → ⟨ w ∈ˢ 𝒟ₒ (Lset σ) ⟩) q
        (PS.part-def (maskAt (Tally.size t) j))

  defPow∈J : ⟨ 𝒟ₒ (Lset σ) ∈ˢ Sset IS.ω ⟩
  defPow∈J = subst (λ w → ⟨ w ∈ˢ Sset IS.ω ⟩) (sym defPow≡finSet)
    (finSetMem M fam (λ j → part-in-J (maskAt (Tally.size t) j)))

baseDefPow : (ζ : S) → ⟨ ζ ∈ˢ IS.ω ⟩ → ⟨ Lset ζ ∈ˢ Sset IS.ω ⟩
           → ⟨ 𝒟ₒ (Lset ζ) ∈ˢ Sset IS.ω ⟩
baseDefPow ζ ζ∈ω L∈ = PT.rec (snd (𝒟ₒ (Lset ζ) ∈ˢ Sset IS.ω)) go ζ∈ω
  where
  go : Σ[ k ∈ Lift ℕ ] (IS.# (lower k) ≡ ζ) → ⟨ 𝒟ₒ (Lset ζ) ∈ˢ Sset IS.ω ⟩
  go (k , q) = subst (λ w → ⟨ 𝒟ₒ w ∈ˢ Sset IS.ω ⟩) (cong Lset q)
    (Power.defPow∈J (lower k) L∈k (ltally (lower k)))
    where
    L∈k : ⟨ Lset (IS.# (lower k)) ∈ˢ Sset IS.ω ⟩
    L∈k = subst (λ w → ⟨ w ∈ˢ Sset IS.ω ⟩) (sym (cong Lset q)) L∈

baseStage∈J : (ζ : S) → ⟨ ζ ∈ˢ IS.ω ⟩ → ⟨ Lset ζ ∈ˢ Sset IS.ω ⟩
            → ⟨ Lset (IS.sucV ζ) ∈ˢ Sset IS.ω ⟩
baseStage∈J ζ ζ∈ω L∈ = subst (λ w → ⟨ w ∈ˢ Sset IS.ω ⟩) (sym (Lset-suc ζ))
  (baseDefPow ζ ζ∈ω L∈)
```

<!--en-->
## Recap
<!--zh-->
## 小结
<!--/-->

<!--en-->
This chapter is the surviving home of the finite-tally content the
hereditarily-finite carrier consumes. `Tally` is the whole finiteness
vocabulary; the masks, `select`, `marks` and the decision trio are the index
arithmetic that moves a tally around; `PowerStep` raises a tally to the
definable power set and `ltally` runs that step along the numerals, while the
S-side module runs the sixteen-image step and `sTally` certifies that every
finite level of the S-tower is finite. The first-limit block places the empty
set and the basis operations in `Sset ω` (`∅∈Ssetω`, `op-in-J`), proves the
table lemma `finSetMem`, and discharges the power obligation `Power` at a
held finite carrier, whose `ω`-level assembly is `baseStage∈J`. `Search`'s
smallest-element scan is the classical pick the ordinal content of the
carrier uses.
<!--zh-->
本章是遗传有穷载体所消费的有穷点名册内容的幸存住处。`Tally` 就是全部的有穷性词汇；掩码、`select`、`marks` 与判定三件套是搬运点名册的索引算术；`PowerStep` 把点名册抬到可定义幂集上，`ltally` 沿诸数码跑完这一步，S 侧模块则跑过十六像的 step，`sTally` 证明 S 塔的每个有穷层都有穷。第一个极限块把空集与基底运算放进 `Sset ω` (`∅∈Ssetω`、`op-in-J`)，证明表引理 `finSetMem`，并在被收下的有穷载体处兑付幂义务 `Power`，其 `ω` 层装配就是 `baseStage∈J`。`Search` 的最小元扫描，正是载体序数内容所用的经典挑选。
<!--/-->
