# Recursive definitions are internalizable

<!--en-->
A definition by recursion produces a table: an index, and for each index a value.
The table is a family in the meta-language, and the question this chapter answers
is when it is a *set of `L`*. Everything later that speaks about a
recursively-defined notion inside the object language needs an answer, because a
formula can only name a set.

The answer is short, and the reason it is short is worth stating first. The hard
version of this question asks for a table to be definable *inside a stage*, where
what a formula means is not what it means outside, so the certificate has to be
absolute, so every clause of it has to be Δ₀ and every constant of it has to be
bounded by the stage. That is a heavy discipline and it is the shape the question
usually takes.

It is not the shape it takes here, because the previous chapters paid for the
general case once. Replacement in `L` holds for formulas of *any* complexity, and
its formulas are read at the class model, where a formula means what it means. So
a recursion whose graph is expressible at all, at any complexity, has its table
in `L`: the table is the replacement image, and there is nothing else to prove.

What is left is exactly what should be left. The graph must be expressible, and
the recursion must be single-valued. Neither is generic; both are the mathematics
of whatever is being defined.
<!--zh-->
一个递归定义产出一张表：一个索引，以及每个索引处的一个值。这张表是元语言中的一个族，而本章要回答的问题是：它何时是 **`L` 的集合**。此后凡在对象语言之内谈论某个递归定义的概念的地方，都需要一个答案，因为公式只能点名集合。

答案很短，而它为何这么短，值得先说。这个问题的困难版本要求一张表在**某个阶段之内**可定义，而在那里公式的含义与在外面不同，于是证书必须绝对，于是它的每条子句都得是 Δ₀，它的每个常元都得被该阶段界住。那是一套沉重的纪律，也是这个问题通常呈现的形状。

它在此处不是那个形状，因为前几章已经一次性买断了一般情形。`L` 中的替换对**任意**复杂度的公式成立，而它的公式是在类模型处读的，在那里公式的含义就是它的含义。故凡图可表达的递归，无论多复杂，其表都在 `L` 中：那张表就是替换的像，此外无须再证。

剩下的恰是该剩下的。图必须可表达，而递归必须单值。二者都不通用；二者都是被定义之物自身的数学。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module L.Recursion {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula )
import FOL.Absoluteness
import FOL.ZFModel
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans )
open import L.Axioms.Full {ℓ} lem using ( hasReplacementL )

import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ

module ModelL = FOL.ZFModel 𝒮ʟ
open ModelL using ( SetOf )

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL renaming ( _⊨ᵐ_ to _⊨_ )
```

<!--en-->
## What a recursion has to supply
<!--zh-->
## 一个递归须供给什么
<!--/-->

<!--en-->
Three things, and the record names them so that an instance is a filled form
rather than a re-run of an argument.

The **domain** is the index set, and it is an element of the model, so the
indices are sets of `L` and the whole index is one set. The **graph** is a
formula in two variables, the value first and the index second, in the order the
model's replacement field states. Its constants may be any elements of `L`, so a
recursion that reads an already-internalized table names it here, and there is no
further condition on it: no complexity bound, no bound on where its constants
live.

**Single-valuedness** is what turns a relation into a definition. It is stated as
contractibility rather than as existence plus uniqueness, which is the same thing
and is what the field consumes. Stated this way it also *is* the value function:
the centre is the value, and the rest of the chapter reads it off.
<!--zh-->
三样，而 record 为它们命名，好让一个实例是一张填好的表格，而非再跑一遍论证。

**定义域**是索引集，且是模型的元素，故诸索引都是 `L` 的集合，而整个索引是一个集合。**图**是二元公式，值在前、索引在后，与模型的替换字段所陈述的顺序相同。它的常元可以是 `L` 的任意元素，故读取某张已内化之表的递归就在此处点名它，而对它别无进一步的条件：无复杂度上界，也不限定它的常元住在哪里。

**单值性**是把关系变成定义的那样东西。它陈述为可缩而非「存在加唯一」，二者是同一回事，而字段消费的正是前者。这样陈述它同时**就是**那个值函数：中心即是值，本章其余部分把它读出来。
<!--/-->

```agda
record Recursion : Type (ℓ-suc (ℓ-suc ℓ)) where
  field
    dom   : S
    graph : Formula S 2
    funct : (x : S) → ⟨ x ∈ˢ dom ⟩
          → isContr (Σ[ y ∈ S ] ⟨ (y ∷ x ∷ []) ⊨ graph ⟩)
```

<!--en-->
## The table
<!--zh-->
## 那张表
<!--/-->

<!--en-->
The table is the replacement image, so it is an element of `L` by construction
rather than by a theorem, and its membership specification is the field's own
output. The two directions of that specification are what instances use: a value
at an index is in the table, and a member of the table is a value at some index.

The value function comes off the single-valuedness, together with the two facts
an instance wants about it: it satisfies the graph, and it is the *only* thing
that does. Uniqueness is what lets an instance identify the value it computed by
hand with the one the table records.
<!--zh-->
这张表就是替换的像，故它是 `L` 的元素乃出于构造而非出于定理，而它的隶属规格就是那条字段自己的输出。规格的两个方向正是诸实例所用：某索引处的值属于该表，而该表的成员是某索引处的值。

值函数从单值性中读出，连同实例想要的两条事实：它满足那个图，而且它是**唯一**满足的东西。唯一性正是使实例能把它手算出的值与表所记录的值认同起来的东西。
<!--/-->

```agda
module Of (R : Recursion) where
  open Recursion R public

  private
    Image : S → Ω
    Image y = ⋁ S (λ x → (x ∈ˢ dom) ⊓ ((y ∷ x ∷ []) ⊨ graph))

    r : SetOf Image
    r = hasReplacementL dom graph funct .fst

  table : S
  table = r .fst

  table-mem : (y : S) → (y ∈ˢ table) ≡ Image y
  table-mem = r .snd

  table-in : (x y : S) → ⟨ x ∈ˢ dom ⟩ → ⟨ (y ∷ x ∷ []) ⊨ graph ⟩
           → ⟨ y ∈ˢ table ⟩
  table-in x y x∈ h = subst ⟨_⟩ (sym (table-mem y)) ∣ x , (x∈ , h) ∣₁

  table-out : (y : S) → ⟨ y ∈ˢ table ⟩ → ⟨ Image y ⟩
  table-out y h = subst ⟨_⟩ (table-mem y) h

  val : (x : S) → ⟨ x ∈ˢ dom ⟩ → S
  val x x∈ = funct x x∈ .fst .fst

  val-graph : (x : S) (x∈ : ⟨ x ∈ˢ dom ⟩)
            → ⟨ (val x x∈ ∷ x ∷ []) ⊨ graph ⟩
  val-graph x x∈ = funct x x∈ .fst .snd

  val-uniq : (x : S) (x∈ : ⟨ x ∈ˢ dom ⟩) (y : S)
           → ⟨ (y ∷ x ∷ []) ⊨ graph ⟩ → val x x∈ ≡ y
  val-uniq x x∈ y h = cong fst (funct x x∈ .snd (y , h))

  val∈table : (x : S) (x∈ : ⟨ x ∈ˢ dom ⟩) → ⟨ val x x∈ ∈ˢ table ⟩
  val∈table x x∈ = table-in x (val x x∈) x∈ (val-graph x x∈)
```

<!--en-->
## What this does and does not say
<!--zh-->
## 这说了什么、没说什么
<!--/-->

<!--en-->
It says: a single-valued definable relation on a set of `L` has its table in `L`,
and the value function is total on the domain. Every recursion whose values are
determined by a formula is covered, whatever the formula's complexity and
wherever its constants live.

It does not say that any particular recursion *has* such a formula. Writing the
graph of a recursion in the object language is the work, and it is the same work
whether or not this chapter exists; what this chapter removes is the second job
that usually rides along with it, of making that formula bounded and its
constants stage-local so that a stage can read it. That job is gone, and it was
the larger of the two.

It also does not say the domain is easy. An index set of syntax has to be shown
to be a set of `L` before it can be a domain, and that is its own obligation,
discharged once per index and shared by every recursion over it.
<!--zh-->
它说：`L` 的集合上的单值可定义关系，其表在 `L` 中，而值函数在定义域上是全的。凡取值由一条公式所决定的递归都被涵盖，无论那条公式多复杂，也无论它的常元住在哪里。

它没有说任何特定的递归**拥有**这样一条公式。把一个递归的图写进对象语言是实打实的活，而无论本章存在与否，那份活都一样；本章免去的是通常与之同行的第二份活：把那条公式弄成有界的、把它的常元弄成阶段局部的，好让某个阶段能读它。那份活没有了，而它是两者中较大的一份。

它也没有说定义域好办。一个语法的索引集必须先被证明是 `L` 的集合，才能充当定义域，那是它自己的一笔债，每个索引偿付一次，而其上的每个递归共享它。
<!--/-->

<!--en-->
## Recap
<!--zh-->
## 小结
<!--/-->

<!--en-->
`Recursion`{.Agda} is the form an instance fills: a domain in `L`, a graph of any
complexity, and single-valuedness. `Of`{.Agda} reads off the table, its two
membership directions, and the value function with its uniqueness.

The chapter is a wrapper around `hasReplacementL`{.Agda}, and that is the point.
The general-formula comprehension fields were the expensive thing; once they are
paid, internalizing a recursion is not a theorem but a corollary, and the
per-clause absoluteness discipline that the bounded setting forces never has to
be entered.
<!--zh-->
`Recursion`{.Agda} 是实例要填的表格：`L` 中的定义域、任意复杂度的图，以及单值性。`Of`{.Agda} 把那张表、它的两个隶属方向、以及带唯一性的值函数读出来。

本章是 `hasReplacementL`{.Agda} 的一层包装，而这正是要点。任意公式的概括字段才是贵的东西；一旦付清，内化一个递归就不是定理而是推论，而有界情形所强加的逐子句绝对性纪律，压根无须踏入。
<!--/-->
