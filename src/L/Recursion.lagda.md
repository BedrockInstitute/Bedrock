<!--en-->
# Internalizing recursive definitions in L

Replacement collects the values of a definable single-valued relation on a domain in `L` into a set of `L`. The interface accepts either an explicit value function or a relation known merely to have a unique value at each point, and returns the internal table used by later recursive constructions.
<!--zh-->
# L 中递归定义的内部化

`L` 中的替换把定义域上可定义单值关系的诸取值收集成 `L` 的一个集合。本章既接受显式取值函数，也接受仅知每点有唯一取值的关系，并给出后续递归构造所用的内部表。
<!--ja-->
# L における再帰的定義の内部化

`L` の置換公理は、`L` 内の定義域上にある定義可能な単値関係の値を `L` の集合へ集めます。明示的な値関数がある場合と、各点で値が一意に存在することだけが分かる場合の両方を扱い、後の再帰構成が使う内部表を与えます。
<!--/-->

<!--en-->
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
答案很短，而它为何这么短，值得先说。这个问题的困难版本要求一张表在**某一层之内**可定义，而在那里公式的含义与在外面不同，于是证书必须绝对，它的每条子句都得是 Δ₀，它的每个常元都得被该层界住。那是一套沉重的纪律，也是这个问题通常呈现的形状。

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
open import L.Constructible {ℓ}
  using ( 𝒮ʟ; isL; isL-trans; IsOrd; Lset-mono )
open import L.Ordinal {ℓ} using ( boundingOrd )
open import L.Stage {ℓ} lem using ( stage; stage-ord; stage-mem )
open import L.Axioms.Basic {ℓ} using ( LsetS )
open import L.Axioms.Full {ℓ} lem using ( hasReplacementL )

open import Cubical.Data.Sigma using ( Σ≡Prop )
open import Cubical.Foundations.Prelude using ( isPropIsContr )
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

Three things, and the record names them so that an instance is a filled form
rather than a re-run of an argument.
<!--zh-->
## 递归须提供什么

三样，而 record 为它们命名，好让一个实例是一张填好的表格，而非再跑一遍论证。
<!--ja-->
## 再帰が与えるべきもの

内部化する再帰は、集合で抑えられた定義域、整礎的な先行関係、各点の値を以前の値から一意に定める論理式を与えます。これらの条件が表の存在と一意性を支えます。
<!--/-->

<!--en-->
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
**定义域**是索引集，并且是模型中的元素；因此各个索引都是 `L` 的集合，整个索引集也是一个集合。**图**是二元公式，值在前、索引在后，与模型的替换字段采用相同顺序。公式的常元可以是 `L` 的任意元素，因此读取已内化表的递归可以在这里指定该表；除此之外没有额外条件，既无复杂度上界，也不限制常元所属的层。

**单值性**使关系成为定义。这里把它陈述为可缩，而不是「存在且唯一」；二者等价，字段要求的是前一种形式。按这种形式陈述时，它同时给出值函数：可缩类型的中心就是该值，本章其余部分将使用这个中心。
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
Of the three, the domain is the one that looks like it might be hard, and it is
not. An index set is usually given as a family in the meta-language, indexed by
some type of the ambient size: the closed formulas, the pairs of them, whatever
the recursion is over. Such a family does not have to be collected into a set at
all. It only has to be *contained* in one, and any small family of elements of
`L` is contained in a single stage, by the bounding lemma applied to their
earliest stages. A stage is a set of `L`, so it serves as the domain.

The recursion is then defined on more than its intended indices, and this
requires nothing extra: the graph is made total by giving the uninteresting
elements a default value, and the intended table is recovered by separation,
which is now available for arbitrary formulas. So the requirement that the index
set be a set of `L`, which an instance would otherwise meet by internalizing its
own syntax, is met here for every instance at once.
<!--zh-->
三者之中，看起来可能难办的是定义域，而它并不难。索引集通常以元语言中的族给出，由某个周遭大小的类型索引：闭公式、闭公式的对，或该递归所遍历的任何东西。这样的族根本不必被收集成一个集合。它只需被**包含**在某个集合里，而 `L` 的任何小族都被包含在单一层中，只需把界层引理施于它们的最早层。层是 `L` 的集合，故可充当定义域。

于是递归可以定义在比预期索引更大的域上，而不增加额外要求：给无关元素指定默认值，图就成为全函数；再用已适用于任意公式的分离取回预期的表。原本每个实例都要通过内化自身语法来满足「索引集是 `L` 的集合」这一要求，现在可以统一解决。
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

The table is the replacement image, so it is an element of `L` by construction
rather than by a theorem, and its membership specification is the field's own
output. The two directions of that specification are what instances use: a value
at an index is in the table, and a member of the table is a value at some index.
<!--zh-->
## 表

这张表就是替换的像，故它是 `L` 的元素乃出于构造而非出于定理，而它的隶属规格就是那条字段自己的输出。规格的两个方向正是诸实例所用：某索引处的值属于该表，而该表的成员是某索引处的值。
<!--ja-->
## 表

表は、既に計算した入力と値を順序対として集めた集合です。局所的な正しさと先行点への閉性を課すことで、整礎帰納法が各入力に唯一の正しい値があることを示せます。
<!--/-->

<!--en-->
The value function comes off the single-valuedness, with the fact an instance
wants about it: it is the *only* thing that satisfies the graph. Uniqueness is
what lets an instance identify the value it computed by hand with the one the
table records.
<!--zh-->
值函数从单值性中读出，连同实例所需的那条事实：它是**唯一**满足那个图的东西。正是唯一性让实例能把自行算出的值与表所记录的值等同起来。
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

  val-uniq : (x : S) (x∈ : ⟨ x ∈ˢ dom ⟩) (y : S)
           → ⟨ (y ∷ x ∷ []) ⊨ graph ⟩ → val x x∈ ≡ y
  val-uniq x x∈ y h = cong fst (funct x x∈ .snd (y , h))

```

<!--en-->
## When the value function cannot be written down

The form below asks an instance for a function on the whole model. That is the
right thing to ask when the instance has one, and the wrong thing when its
indices are *encoded*: a recursion over coded syntax knows what to do at a code,
and to say what it does at an arbitrary element of the model it would first have
to decide whether that element is a code and, if so, recover the syntax it
encodes. Nothing in the recursion needs that, and paying for it would be paying
for a decoding the instance never uses.
<!--zh-->
## 无法直接写出取值函数时

下面那张表格向实例索取一个定义在整个模型上的函数。当实例确实有一个时，这索取得对；而当它的索引是**编码**的时候，就索取错了：对编码语法的递归知道在一个码处该做什么，而要说出它在模型的任意元素处做什么，就得先判定那个元素是不是码，若是还得把它所编码的语法还原出来。递归本身不需要这些，而为它付账，等于为一次实例从不使用的解码付账。
<!--ja-->
## 値関数を直接書けない場合

関係が各入力に一意な値を与えることだけが分かる場合、命題的切り詰めの外へ値関数を直接取り出せないことがあります。代わりに表の存在と関数性を命題として組み立て、必要な箇所で一意性を使います。
<!--/-->

<!--en-->
Single-valuedness does not need it either, and the reason is worth naming.
Contractibility is a proposition. So an instance may decide by cases, and may
take apart a truncated witness, on the way to proving it: what has to be produced
is a value, and it only has to be produced *merely*. The lemma below is that
observation, and it is what a recursion over an encoded index uses in place of
the form below.
<!--zh-->
单值性同样不需要它，而这个理由值得点名。可缩性是命题。故实例可以在通往它的证明途中分情形判定，也可以拆开一个截断的见证：要拿出来的是一个取值，而它只需**仅仅**被拿出来。下面这条引理就是这个观察，也是「对编码索引的递归」用来代替下面那张表格的东西。
<!--/-->

```agda
mereFunct : (graph : Formula S 2) (x : S)
          → ∥ (Σ[ y ∈ S ] (⟨ (y ∷ x ∷ []) ⊨ graph ⟩
                          × ((y' : S) → ⟨ (y' ∷ x ∷ []) ⊨ graph ⟩ → y' ≡ y))) ∥₁
          → isContr (Σ[ y ∈ S ] ⟨ (y ∷ x ∷ []) ⊨ graph ⟩)
mereFunct graph x = PT.rec isPropIsContr
  (λ { (y , (hy , uniq)) → (y , hy)
     , (λ { (y' , hy') → Σ≡Prop (λ w → snd ((w ∷ x ∷ []) ⊨ graph))
                           (sym (uniq y' hy')) }) })
```

<!--en-->
## Defining a function, rather than a relation

Asking an instance for single-valuedness is asking the wrong thing, because an
instance never has a relation to start with. It has a **function**, written in
the meta-language by ordinary recursion, and what it wants is that function's
table. The recursion itself is Agda's business, not the object language's: the
step, the well-founded descent, the pattern match on the constructors, all of
that happens outside and none of it needs internalizing. Only the *graph* does.
<!--zh-->
## 定义函数而非关系

向实例索取单值性是索取错了东西，因为实例手上从来就没有关系。它手上有的是一个**函数**，以寻常递归写在元语言里，而它想要的是那个函数的表。递归本身是 Agda 的事，不是对象语言的事：步进、良基下降、对构造子的模式匹配，全都发生在外面，无一需要内化。要内化的只有那个**图**。
<!--ja-->
## 関係ではなく関数を定義する

値を明示的な関数として与えられる定義は、等号でそのグラフを表す再帰へ変換できます。`asRecursion`{.Agda} はこの変換を行い、一般の内部化定理を通常の再帰的関数へ適用します。
<!--/-->

<!--en-->
So the data to supply is a function together with a formula that defines it, and
defining it is two implications. One says the formula holds of the function's own
value, the other that nothing else satisfies it. Single-valuedness then follows
immediately, because a type of things equal to a given one is contractible, and
that is the whole derivation.

This is where the chapter's central claim takes hold. A recursive definition is
internalizable when its graph is expressible, and nothing about the recursion's
shape, its depth, its order of descent, or the complexity of its clauses appears
in the condition.
<!--zh-->
于是需要给出的数据是「一个函数，连同一条定义它的公式」，而「定义它」就是两条蕴含：一条说该公式在函数自身的取值处成立，另一条说别无他物满足它。单值性由此直接得出，因为「与给定之物相等者」构成的类型可缩；全部推导仅此而已。

本章的主张正是在此处成立的。一个递归定义只要其图可表达，便可被内化；而递归的形状、它的深度、它下降的次序、它诸子句的复杂度，都不出现在这个条件里。
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
再陈述定理在实例中实际使用的形式：`L` 的集合上，可定义函数的像是 `L` 的集合，并附上其两个隶属方向。反向是截断的，因为像的成员是**某个**索引处的值，而那个索引无法取回；至此每个使用该定理的场合也只需要这个截断的形式。
<!--/-->

```agda
module Image (D : Definition) where
  open Definition D public
  private
    module R = Of (asRecursion D)

  table : S
  table = R.table

```

<!--en-->
## What this does and does not say

It says: a function on a set of `L` whose graph is expressible has its table in
`L`. Every recursion whose values are determined by a formula is covered,
whatever the formula's complexity and wherever its constants live, and the
recursion itself stays in the meta-language where it was written.
<!--zh-->
## 定理所述的范围

定理断言：对于 `L` 中的集合，若一个函数的图可以由公式表达，则该函数的表属于 `L`。只要递归的取值由公式确定，定理就适用，不论公式的复杂度如何，也不限制其常元所属的层；递归本身仍在元语言中定义。
<!--ja-->
## 定理が述べる範囲

内部化定理は、指定した集合領域上で再帰のグラフが `L` に属することを示します。クラス全体の関数を一度に集合にするのではなく、後の議論に必要な各集合サイズの切片を与えます。
<!--/-->

<!--en-->
It does not say that any particular recursion *has* such a formula. Writing the
graph of a recursion in the object language is work that has to be done
regardless of whether this chapter exists; what this chapter removes is the
second job that usually comes with it, of making that formula bounded and its
constants stage-local so that a stage can read it. That job is removed here,
and it is the larger of the two.

It also does not leave the domain to the user. `smallDom`{.Agda} provides it for
every instance at once: a small family of elements of `L` is contained in
a stage, and a stage is a set of `L`. What an instance supplies is that its
indices are elements of `L`, one at a time, which for coded syntax is pairing and
the numerals.
<!--zh-->
它没有说任何特定的递归**拥有**这样一条公式。把一个递归的图写进对象语言，这项工作无论如何都要做，与本章是否存在无关；本章免去的是通常随之而来的另一项工作：把那条公式弄成有界的、把它的常元弄成层局部的，好让某一层能读它。这项工作在此被免去了，而它是两项中较大的一项。

它也没有把定义域的问题留给使用者。`smallDom`{.Agda} 一次性地为所有实例给出定义域：`L` 的小族被包含在某一层里，而层是 `L` 的集合。实例需要供给的是「它的诸索引逐个都是 `L` 的元素」，而对编码后的语法，那就是配对与数码。
<!--/-->

<!--en-->
## Recap

`Definition`{.Agda} is the form an instance fills when it has a function on the
whole model to offer: a domain in `L`, that function, and a formula that defines
its graph, in the two directions. An instance whose indices are encoded has no
such function without a decoder it does not otherwise need, and fills
`Recursion`{.Agda} directly through `mereFunct`{.Agda} instead, which is sound
because contractibility is a proposition. `smallDom`{.Agda} fills the domain for any small family of elements
of `L`, and single-valuedness is derived, so **the defining formula and its
adequacy are the entire obligation**. `Image`{.Agda} reads off the table and its
two membership directions.
<!--zh-->
## 小结

`Definition`{.Agda} 是实例在「手上有一个定义于整个模型的函数」时需要给出的数据：`L` 中的定义域、那个函数，以及一条按两个方向定义其图的公式。索引为编码的实例没有那样的函数，除非另配一个它本不需要的解码器；这类实例改经 `mereFunct`{.Agda} 直接填 `Recursion`{.Agda}，而那是可靠的，因为可缩性是命题。`smallDom`{.Agda} 为 `L` 元素的任意小族给出定义域，而单值性是推导出来的，故**剩下需要验证的只有那条定义公式与它的充分性**。`Image`{.Agda} 把那张表连同它的两个隶属方向读出来。
<!--ja-->
## まとめ

`Definition`{.Agda} は `L` 内の定義域、周囲の関数、そのグラフを定義する論理式と妥当性をまとめます。値関数を直接持たない符号化された場合は `mereFunct`{.Agda} から `Recursion`{.Agda} を与えられ、`smallDom`{.Agda} が小さな族の定義域を作り、`Image`{.Agda} が内部化された表を読み出します。
<!--/-->

<!--en-->
The chapter is a wrapper around `hasReplacementL`{.Agda}, and that is the point.
The general-formula comprehension fields are the expensive part; once they are in
place, internalizing a recursion is a corollary, and the per-clause
absoluteness discipline that the bounded setting imposes never has to be carried
out.
<!--zh-->
本章是 `hasReplacementL`{.Agda} 的一层包装，而这正是关键。任意公式的概括字段是代价较高的部分；一旦具备该字段，内化递归就是一个推论，无须再处理有界情形要求的逐子句绝对性。
<!--/-->
