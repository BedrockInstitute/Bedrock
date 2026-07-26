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
open import FOL.Syntax using ( Formula; ∃̇_ )
import FOL.Absoluteness
import FOL.ZFModel
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ}
  using ( 𝒮ʟ; isL; isL-trans; IsOrd; Lset-mono )
open import L.Ordinal {ℓ} using ( boundingOrd )
open import L.Stage {ℓ} lem using ( stage; stage-ord; stage-mem )
open import L.Axioms.Basic {ℓ} using ( LsetS )
open import L.Axioms.Full {ℓ} lem using ( hasReplacementL )

open import Cubical.Data.Sigma using ( Σ≡Prop )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁ )

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
## What a graph may not do
<!--zh-->
## 一个图不可以做什么
<!--/-->

<!--en-->
One line, stated because it decides a design question that otherwise gets decided
by wasted work. Satisfaction is read at the model, so an existential quantifier
of the object language ranges over the model: to satisfy one is to produce an
element of `L`, not merely a set.

The consequence is a rule about what may appear in a graph. A graph may say
"there is a `y` such that ..." only when the `y` it needs is *already* known to
be an element of `L`. In particular a graph may not describe an object by
asserting the existence of the very object being described: that describes
nothing, because discharging the assertion is exactly the problem it was meant to
solve. A table of values may therefore not be reached by writing "there is a
table satisfying the recursion equations"; it has to be reached by naming
something smaller that is already in hand, and letting this chapter collect the
pieces.
<!--zh-->
一行，之所以写出来，是因为它决定一个设计问题，而这个问题若不写出来就要靠白做的工来决定。满足关系是在模型处读的，故对象语言的存在量词在模型上取值：满足它就是拿出 `L` 的一个元素，而不只是一个集合。

由此得到一条关于「图里可以出现什么」的规矩。一个图可以说「存在一个 `y` 使得……」，仅当它所需的那个 `y` **已经**知道是 `L` 的元素。特别地，一个图不可以这样描述一个对象：断言被描述者本身存在。那什么也没描述，因为兑现那个断言，恰恰就是它本要解决的问题。取值表因而不能靠写「存在一张满足递归方程的表」来抵达；它必须靠点名某个更小的、已经在手的东西来抵达，再由本章把碎片收拢。
<!--/-->

```agda
witnessInModel : ∀ {n} (γ : S ^ n) (φ : Formula S (suc n))
               → ⟨ γ ⊨ (∃̇ φ) ⟩ → ∥ (Σ[ x ∈ S ] ⟨ (x ∷ γ) ⊨ φ ⟩) ∥₁
witnessInModel γ φ h = h
```

<!--en-->
Of the three, the domain is the one that looks like it might be hard, and it is
not. An index set is usually given as a family in the meta-language, indexed by
some type of the ambient size: the closed formulas, the pairs of them, whatever
the recursion is over. Such a family does not have to be collected into a set at
all. It only has to be *contained* in one, and any small family of elements of
`L` is contained in a single stage, by the bounding lemma applied to their
earliest stages. A stage is a set of `L`, so it serves as the domain.

The recursion is then defined on more than its intended indices, and that costs
nothing: the graph is made total by giving the uninteresting elements a default
value, and the intended table is recovered by separation, which is now available
for arbitrary formulas. So the obligation "the index set is a set of `L`", which
an instance would otherwise discharge by internalizing its own syntax, is
discharged here once for every instance at once.
<!--zh-->
三者之中，看起来可能难办的是定义域，而它并不难。索引集通常以元语言中的族给出，由某个周遭大小的类型索引：闭公式、闭公式之对，或该递归所遍历的任何东西。这样的族根本不必被收集成一个集合。它只需被**包含**在某个集合里，而 `L` 的任何小族都被包含在单一阶段中，只需把界层引理施于它们的最早阶段。阶段是 `L` 的集合，故可充当定义域。

于是递归定义在比其预期索引更多的东西上，而这不费分文：把无关的元素赋一个默认值，图便成为全函数，而预期的那张表经分离取回，而分离如今对任意公式可用。于是「索引集是 `L` 的集合」这笔债，本来要由实例自行内化其语法来偿付，此处一举为所有实例偿清。
<!--/-->

```agda
smallDom : (X : Type ℓ) (f : X → S) → Σ[ d ∈ S ] ((x : X) → ⟨ f x ∈ˢ d ⟩)
smallDom X f = LsetS β oβ , mem
  where
  b = boundingOrd X (λ x → stage (fst (f x)) (f x .snd))
        (λ x → stage-ord (fst (f x)) (f x .snd))
  β = b .fst
  oβ : IsOrd β
  oβ = b .snd .fst
  mem : (x : X) → ⟨ f x ∈ˢ LsetS β oβ ⟩
  mem x = Lset-mono {α = β} {β = stage (fst (f x)) (f x .snd)} (b .snd .snd x)
            (stage-mem (fst (f x)) (f x .snd))
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
## Defining a function, rather than a relation
<!--zh-->
## 定义一个函数，而非一个关系
<!--/-->

<!--en-->
Asking an instance for single-valuedness is asking the wrong thing, because an
instance never has a relation to start with. It has a **function**, written in
the meta-language by ordinary recursion, and what it wants is that function's
table. The recursion itself is Agda's business, not the object language's: the
step, the well-founded descent, the pattern match on the constructors, all of
that happens outside and none of it needs internalizing. Only the *graph* does.

So the form to fill is a function together with a formula that defines it, and
defining it is two implications. One says the formula holds of the function's own
value, the other that nothing else satisfies it. Single-valuedness then comes for
free, because a type of things equal to a given one is contractible, and that is
the whole derivation.

This is where the chapter's title is earned. A recursive definition is
internalizable when its graph is expressible, and nothing about the recursion's
shape, its depth, its order of descent, or the complexity of its clauses appears
in the condition.
<!--zh-->
向实例索取单值性是索取错了东西，因为实例手上从来就没有关系。它手上有的是一个**函数**，以寻常递归写在元语言里，而它想要的是那个函数的表。递归本身是 Agda 的事，不是对象语言的事：步进、良基下降、对构造子的模式匹配，全都发生在外面，无一需要内化。要内化的只有那个**图**。

于是要填的表格是「一个函数，连同一条定义它的公式」，而「定义它」就是两条蕴含。一条说该公式在函数自己的取值处成立，另一条说别无他物满足它。单值性随之白得，因为「与给定之物相等者」构成的类型可缩，而全部推导仅此而已。

本章的标题在此处挣得。一个递归定义可内化，当它的图可表达；而递归的形状、它的深度、它下降的次序、它诸子句的复杂度，都不出现在这个条件里。
<!--/-->

```agda
record Definition : Type (ℓ-suc (ℓ-suc ℓ)) where
  field
    dom     : S
    fn      : S → S
    graph   : Formula S 2
    defines : (x : S) → ⟨ x ∈ˢ dom ⟩ → ⟨ (fn x ∷ x ∷ []) ⊨ graph ⟩
    only    : (x : S) → ⟨ x ∈ˢ dom ⟩ → (y : S)
            → ⟨ (y ∷ x ∷ []) ⊨ graph ⟩ → y ≡ fn x

asRecursion : Definition → Recursion
asRecursion D = record
  { dom   = D.dom
  ; graph = D.graph
  ; funct = λ x x∈ → (D.fn x , D.defines x x∈)
          , λ { (y , h) → Σ≡Prop (λ w → snd ((w ∷ x ∷ []) ⊨ D.graph))
                            (sym (D.only x x∈ y h)) } }
  where module D = Definition D
```

<!--en-->
And the theorem in the form an instance consumes: the image of a definable
function on a set of `L` is a set of `L`, with its two membership directions. The
backward one is truncated, because a member of the image is the value at *some*
index and the index is not recoverable; every consumer so far only needs it
truncated.
<!--zh-->
以及定理在实例所消费的那个形式：`L` 的集合上，可定义函数的像是 `L` 的集合，附其两个隶属方向。反向是截断的，因为像的成员是**某个**索引处的值，而那个索引取不回来；至此每个消费方也都只需要截断的形式。
<!--/-->

```agda
module Image (D : Definition) where
  open Definition D public
  private
    module R = Of (asRecursion D)

  table : S
  table = R.table

  fn∈table : (x : S) → ⟨ x ∈ˢ dom ⟩ → ⟨ fn x ∈ˢ table ⟩
  fn∈table x x∈ = R.table-in x (fn x) x∈ (defines x x∈)

  table→fn : (y : S) → ⟨ y ∈ˢ table ⟩
           → ∥ (Σ[ x ∈ S ] (⟨ x ∈ˢ dom ⟩ × (y ≡ fn x))) ∥₁
  table→fn y h = PT.map (λ { (x , (x∈ , sat)) → x , (x∈ , only x x∈ y sat) })
    (R.table-out y h)
```

<!--en-->
## What this does and does not say
<!--zh-->
## 这说了什么、没说什么
<!--/-->

<!--en-->
It says: a function on a set of `L` whose graph is expressible has its table in
`L`. Every recursion whose values are determined by a formula is covered,
whatever the formula's complexity and wherever its constants live, and the
recursion itself stays in the meta-language where it was written.

It does not say that any particular recursion *has* such a formula. Writing the
graph of a recursion in the object language is the work, and it is the same work
whether or not this chapter exists; what this chapter removes is the second job
that usually rides along with it, of making that formula bounded and its
constants stage-local so that a stage can read it. That job is gone, and it was
the larger of the two.

It also does not leave the domain as an obligation. `smallDom`{.Agda} discharges
it for every instance at once: a small family of elements of `L` is contained in
a stage, and a stage is a set of `L`. What an instance supplies is that its
indices are elements of `L`, one at a time, which for coded syntax is pairing and
the numerals.
<!--zh-->
它说：`L` 的集合上，图可表达的函数，其表在 `L` 中。凡取值由一条公式所决定的递归都被涵盖，无论那条公式多复杂，也无论它的常元住在哪里，而递归本身留在它被写下的元语言里。

它没有说任何特定的递归**拥有**这样一条公式。把一个递归的图写进对象语言是实打实的活，而无论本章存在与否，那份活都一样；本章免去的是通常与之同行的第二份活：把那条公式弄成有界的、把它的常元弄成阶段局部的，好让某个阶段能读它。那份活没有了，而它是两者中较大的一份。

它也没有把定义域留作债务。`smallDom`{.Agda} 一举为所有实例偿清：`L` 的小族被包含在某个阶段里，而阶段是 `L` 的集合。实例要供给的是「它的诸索引逐个都是 `L` 的元素」，而对编码后的语法，那就是配对与数码。
<!--/-->

<!--en-->
## Recap
<!--zh-->
## 小结
<!--/-->

<!--en-->
`Definition`{.Agda} is the form an instance fills: a domain in `L`, a function
written in the meta-language, and a formula that defines its graph, in the two
directions. `smallDom`{.Agda} fills the domain for any small family of elements
of `L`, and single-valuedness is derived, so **the defining formula and its
adequacy are the entire obligation**. `Image`{.Agda} reads off the table and its
two membership directions.

The chapter is a wrapper around `hasReplacementL`{.Agda}, and that is the point.
The general-formula comprehension fields were the expensive thing; once they are
paid, internalizing a recursion is not a theorem but a corollary, and the
per-clause absoluteness discipline that the bounded setting forces never has to
be entered.
<!--zh-->
`Definition`{.Agda} 是实例要填的表格：`L` 中的定义域、一个写在元语言里的函数，以及一条按两个方向定义其图的公式。`smallDom`{.Agda} 为 `L` 元素的任意小族填好定义域，而单值性是推导出来的，故**那条定义公式与它的适足性就是全部的债**。`Image`{.Agda} 把那张表与它的两个隶属方向读出来。

本章是 `hasReplacementL`{.Agda} 的一层包装，而这正是要点。任意公式的概括字段才是贵的东西；一旦付清，内化一个递归就不是定理而是推论，而有界情形所强加的逐子句绝对性纪律，压根无须踏入。
<!--/-->
