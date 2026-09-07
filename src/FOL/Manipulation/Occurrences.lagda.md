# Constants by occurrence

<!--en-->
A formula's constants form an ordered list of occurrences. This chapter counts
and enumerates them, supplies the index arithmetic used by abstraction, and
handles the boundary case in which the list is empty.
<!--zh-->
公式的常量组成一列有序的出现。本章计数并枚举这些出现，给出抽象所需的序号算术，并处理该列为空的边界情形。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

module FOL.Manipulation.Occurrences where

open import Base.Prelude
open import FOL.Syntax using
  ( Term; con; var; Formula; _∈̇_; _≐_; _∧̇_; _∨̇_; _⇒̇_; ⊥̇; ∃̇_; ∀̇_; ∀̇∈; ∃̇∈ )
open import FOL.Manipulation.Mapping using ( mapTm; mapFo )
open import Cubical.Data.Nat using ( _+_; snotz )
open import Cubical.Data.Vec using ( _++_; map )
import Cubical.Data.Empty as Empty
```

## Counting by occurrence
<!--zh-->
## 逐次出现地计数
<!--/-->

<!--en-->
The design point of the chapter is decided here, before any syntax moves. A
formula's constants are counted **by occurrence, not by value**: a formula with
`k` constant-occurrences yields a vector of length `k`, and two occurrences of the
same constant are two entries of that vector, holding the same set twice.

A reader who expects the *set* of constants a formula mentions will look for the
decidable equality that would let two occurrences of one constant be recognized as
one, and will not find it. There is none to find: the constant domain is an
arbitrary type, nothing obliges its equality to be decidable, and on a carrier of
sets it demonstrably is not. Counting by occurrence is what frees the whole
chapter from that demand. The price is an abstraction of higher arity than
strictly necessary, paid in variables that receive a value twice over, and nothing
downstream can tell the difference: a vector of parameters is a vector of
parameters.

The count is a structural recursion over the ten constructors, with a term's
count feeding it: a constant is one occurrence, a variable is none. Where a
constructor has two parts, the counts add, left part first.
<!--zh-->
本章的设计要点在此定下，早于任何语法的挪动。一条公式的常量**按出现计数，而非按取值**：带 `k` 次常量出现的公式给出长度为 `k` 的向量，同一常量的两次出现就是该向量的两个条目，把同一个集合装了两遍。

若读者期待的是公式所提及的常量之**集**，他会去找那件能把同一常量的两次出现认作一次的可判定相等，并且找不到。本就没有可找的：常量域是任意类型，没有任何东西迫使它的相等可判定，而在集合的载体上它显然不可判定。逐次出现地计数，正是让整章摆脱这项索求的关键。代价是抽象出来的元数高于严格必要的元数，以「同一取值被喂了两遍」的变量支付，而下游分辨不出差别：参数向量就是参数向量。

计数是对十个构造子的一次结构递归，由词项的计数供料：常量算一次出现，变量算零次。构造子分两部分处的计数相加，左部在先。
<!--/-->

```agda
countTm : ∀ {ℓc} {K : Type ℓc} {n} → Term K n → ℕ
countTm (con c) = suc zero
countTm (var i) = zero

countFo : ∀ {ℓc} {K : Type ℓc} {n} → Formula K n → ℕ
countFo (t ∈̇ u)  = countTm t + countTm u
countFo (t ≐ u)  = countTm t + countTm u
countFo (φ ∧̇ ψ)  = countFo φ + countFo ψ
countFo (φ ∨̇ ψ)  = countFo φ + countFo ψ
countFo (φ ⇒̇ ψ)  = countFo φ + countFo ψ
countFo ⊥̇        = zero
countFo (∃̇ φ)    = countFo φ
countFo (∀̇ φ)    = countFo φ
countFo (∀̇∈ t φ) = countTm t + countFo φ
countFo (∃̇∈ t φ) = countTm t + countFo φ
```

<!--en-->
Collecting is the same recursion written a second time, and it has to be a second
recursion rather than one returning both: the **length** of the vector it returns
is precisely what the first computes, so the count must already exist for the
collection to be typeable at all. Every clause mirrors its counterpart above, with
`++` where the count had `+`, so the constants come out in the order the formula
mentions them, left to right.
<!--zh-->
收集是同一场递归写第二遍，而且必须是第二场递归、而非一场同时交出两者：它所返回的向量的**长度**恰是第一场算出的东西，故计数必须先在，收集才有类型可言。每条子句都照抄上面的对应子句，只把 `+` 换成 `++`，于是常量按公式提及它们的次序、自左而右出列。
<!--/-->

```agda
constantsTm : ∀ {ℓc} {K : Type ℓc} {n} (t : Term K n) → Vec K (countTm t)
constantsTm (con c) = c ∷ []
constantsTm (var i) = []

constantsFo : ∀ {ℓc} {K : Type ℓc} {n} (φ : Formula K n) → Vec K (countFo φ)
constantsFo (t ∈̇ u)  = constantsTm t ++ constantsTm u
constantsFo (t ≐ u)  = constantsTm t ++ constantsTm u
constantsFo (φ ∧̇ ψ)  = constantsFo φ ++ constantsFo ψ
constantsFo (φ ∨̇ ψ)  = constantsFo φ ++ constantsFo ψ
constantsFo (φ ⇒̇ ψ)  = constantsFo φ ++ constantsFo ψ
constantsFo ⊥̇        = []
constantsFo (∃̇ φ)    = constantsFo φ
constantsFo (∀̇ φ)    = constantsFo φ
constantsFo (∀̇∈ t φ) = constantsTm t ++ constantsFo φ
constantsFo (∃̇∈ t φ) = constantsTm t ++ constantsFo φ
```

<!--en-->
## Where the new variables go
<!--zh-->
## 新变量安置在哪
<!--/-->

<!--en-->
The abstraction raises the arity from `n` to `n + k`: the original `n` variables
keep their de Bruijn indices, and the `k` constant-occurrences are read off the
`k` slots that follow. That layout is not a preference, it is what the binders
allow. A quantifier's body lives in a context with one more variable, index `0`
being the one just bound, so a parameter block placed **before** the variables
would have to be renumbered at every binder. Placed **after** them, `suc n + k` is
`suc (n + k)` on the nose: the block simply rides one index higher inside the
body, and four binding constructors cost nothing at all. This is also the whole
of what "the abstracted variables must not be captured" comes to here. The block
sits above every binder, and no binder ever reaches it.

Two placements do the index arithmetic, and each is three lines. `padRight b`
reads an index of the first `a` slots of `a + b`; `padLeft a` reads an index of
the last `b`. They are one another's mirror, and the asymmetry in their arguments
is the asymmetry of the recursion: `padRight` recurses on the index, `padLeft` on
the number of slots it steps over.
<!--zh-->
抽象把元数从 `n` 抬到 `n + k`：原有的 `n` 个变量保留各自的 de Bruijn 序号，`k` 次常量出现则从随后的 `k` 个位读出。这个布局不是偏好，而是约束子所允许的唯一布局。量词的公式体住在多一个变量的语境里，序号 `0` 是刚被约束的那个，故参数块若置于变量**之前**，每遇一个约束子就得重新编号。置于变量**之后**，`suc n + k` 分毫不差就是 `suc (n + k)`：该块在体内只是整体高一个序号，四个约束构造子于是分文不花。「被抽象出的变量不可被捕获」在此也就只剩这一句话：该块坐在每个约束子之上，没有哪个约束子够得着它。

两件安置装置承担序号算术，各占三行。`padRight b` 读 `a + b` 中头 `a` 个位的序号，`padLeft a` 读末 `b` 个位的序号。二者互为镜像，参数的不对称正是递归的不对称：`padRight` 对序号递归，`padLeft` 对它跨过的位数递归。
<!--/-->

```agda
padRight : ∀ {a} b → Fin a → Fin (a + b)
padRight b zero    = zero
padRight b (suc i) = suc (padRight b i)

padLeft : ∀ a {b} → Fin b → Fin (a + b)
padLeft zero    j = j
padLeft (suc a) j = suc (padLeft a j)
```

<!--en-->
Each placement has one law, and it is the law an environment obeys: looking up a
padded index in a concatenated vector is looking up the original index in the
corresponding half. Both are proved by hand, clause by clause, over the vector and
the index together; a proof routed through some library round trip between an
index of a sum and a pair of indices would only invite a conversion problem where
there is none. A third law of the same kind reads a mapped vector, and it is the
one that lets the interpretation of the constants pass through the collection.
<!--zh-->
每件安置装置各有一条定律，正是环境所遵守的那一条：在拼接向量中查一个被补位的序号，就是在对应的那一半中查原序号。两条都逐子句手写，同时对向量与序号递归；若绕道某个库中的往返，把「和的序号」与「一对序号」互换，只会在本无转换问题之处招来一个。同类的第三条定律读一个被映射过的向量，正是它让常量的解释穿过收集。
<!--/-->

```agda
lookup-padRight : ∀ {ℓa} {A : Type ℓa} {a b} (p : Vec A a) (q : Vec A b) (i : Fin a)
                → lookup (padRight b i) (p ++ q) ≡ lookup i p
lookup-padRight []      q ()
lookup-padRight (x ∷ p) q zero    = refl
lookup-padRight (x ∷ p) q (suc i) = lookup-padRight p q i

lookup-padLeft : ∀ {ℓa} {A : Type ℓa} a {b} (p : Vec A a) (q : Vec A b) (j : Fin b)
               → lookup (padLeft a j) (p ++ q) ≡ lookup j q
lookup-padLeft zero    []      q j = refl
lookup-padLeft (suc a) (x ∷ p) q j = lookup-padLeft a p q j

lookup-map : ∀ {ℓa ℓb} {A : Type ℓa} {B : Type ℓb} {n}
             (f : A → B) (v : Vec A n) (j : Fin n)
           → lookup j (map f v) ≡ f (lookup j v)
lookup-map f []      ()
lookup-map f (x ∷ v) zero    = refl
lookup-map f (x ∷ v) (suc j) = lookup-map f v j
```

<!--en-->
The count: formulas over `K` with one free variable inject into the disjoint
union over `k` of the parameter-free arity-`k` shapes paired with `k`-tuples of
constants. A constant occurrence becomes a marker variable in the shape; the
tuple lists the constants in traversal order, padded with one copy of the first
constant.

```agda
module ZeroOccurrences {ℓ : Level} (K : Type ℓ) where

```

The boundary case: a formula with no constants closes the shape under `∃̇`;
`erase` removes the constants, and `erase-inv` re-enters the domain.

```agda
  plus-zero-l : {a b : ℕ} → a + b ≡ 0 → a ≡ 0
  plus-zero-l {zero} {b} p = refl
  plus-zero-l {suc a} {b} p = Empty.rec (snotz p)

  plus-zero-r : {a b : ℕ} → a + b ≡ 0 → b ≡ 0
  plus-zero-r {zero} {b} p = p
  plus-zero-r {suc a} {b} p = Empty.rec (snotz p)

  eraseTm : {n : ℕ} (t : Term K n) → countTm t ≡ 0 → Term (⊥* {ℓ}) n
  eraseTm (con a) p = Empty.rec {A = Term (⊥* {ℓ}) _} (snotz p)
  eraseTm (var i) _ = var i

  erase : {n : ℕ} (φ : Formula K n) → countFo φ ≡ 0 → Formula (⊥* {ℓ}) n
  erase (t ∈̇ u) p = eraseTm t (plus-zero-l p) ∈̇ eraseTm u (plus-zero-r p)
  erase (t ≐ u) p = eraseTm t (plus-zero-l p) ≐ eraseTm u (plus-zero-r p)
  erase (φ ∧̇ ψ) p = erase φ (plus-zero-l p) ∧̇ erase ψ (plus-zero-r p)
  erase (φ ∨̇ ψ) p = erase φ (plus-zero-l p) ∨̇ erase ψ (plus-zero-r p)
  erase (φ ⇒̇ ψ) p = erase φ (plus-zero-l p) ⇒̇ erase ψ (plus-zero-r p)
  erase ⊥̇ _ = ⊥̇
  erase (∃̇ φ) p = ∃̇ erase φ p
  erase (∀̇ φ) p = ∀̇ erase φ p
  erase (∀̇∈ t φ) p = ∀̇∈ (eraseTm t (plus-zero-l p)) (erase φ (plus-zero-r p))
  erase (∃̇∈ t φ) p = ∃̇∈ (eraseTm t (plus-zero-l p)) (erase φ (plus-zero-r p))

  eraseTm-inv : {n : ℕ} (t : Term K n) (p : countTm t ≡ 0)
              → mapTm Empty.rec* (eraseTm t p) ≡ t
  eraseTm-inv (con a) p = Empty.rec (snotz p)
  eraseTm-inv (var i) _ = refl

  erase-inv : {n : ℕ} (φ : Formula K n) (p : countFo φ ≡ 0)
            → mapFo Empty.rec* (erase φ p) ≡ φ
  erase-inv (t ∈̇ u) p =
    cong₂ _∈̇_ (eraseTm-inv t (plus-zero-l p)) (eraseTm-inv u (plus-zero-r p))
  erase-inv (t ≐ u) p =
    cong₂ _≐_ (eraseTm-inv t (plus-zero-l p)) (eraseTm-inv u (plus-zero-r p))
  erase-inv (φ ∧̇ ψ) p =
    cong₂ _∧̇_ (erase-inv φ (plus-zero-l p)) (erase-inv ψ (plus-zero-r p))
  erase-inv (φ ∨̇ ψ) p =
    cong₂ _∨̇_ (erase-inv φ (plus-zero-l p)) (erase-inv ψ (plus-zero-r p))
  erase-inv (φ ⇒̇ ψ) p =
    cong₂ _⇒̇_ (erase-inv φ (plus-zero-l p)) (erase-inv ψ (plus-zero-r p))
  erase-inv ⊥̇ _ = refl
  erase-inv (∃̇ φ) p = cong ∃̇_ (erase-inv φ p)
  erase-inv (∀̇ φ) p = cong ∀̇_ (erase-inv φ p)
  erase-inv (∀̇∈ t φ) p =
    cong₂ ∀̇∈ (eraseTm-inv t (plus-zero-l p)) (erase-inv φ (plus-zero-r p))
  erase-inv (∃̇∈ t φ) p =
    cong₂ ∃̇∈ (eraseTm-inv t (plus-zero-l p)) (erase-inv φ (plus-zero-r p))
```

<!--en-->
## Recap
<!--zh-->
## 小结
<!--/-->

<!--en-->
Occurrences provide a finite interface to a formula's constants. Their count
indexes the enumeration and later parameter abstraction; when it is zero,
`ZeroOccurrences` removes the empty constant domain without losing syntax.
<!--zh-->
常量出现为公式的常量提供有限接口。计数索引枚举及后续的参数抽象；计数为零时，`ZeroOccurrences` 消去空常量域而不损失语法。
<!--/-->
