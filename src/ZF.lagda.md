# Models

<!--en-->
Part 1 built a language, gave it worlds to talk about, and pinned down meaning. But
nothing so far deserves the name set theory: a bare structure believes nothing. Its
membership relation need not admit an empty set, need not pair two elements, need
not gather the subsets of anything. What a universe of sets must provide is exactly
what the **axioms of ZF** say, and this chapter states them. Not as postulates,
though: the book never extends its metatheory, and its structures are many, not one
chosen universe. A **model of ZF** is a record whose fields *are* the axioms, so
"`𝒮` satisfies ZF" means nothing more mysterious than "this record has an
inhabitant at `𝒮`".
<!--zh-->
第一部造出了语言，给了它可谈论的世界，并钉下了含义。但至此还没有任何东西配得上「集合论」之名：裸结构什么都不信，它的成员关系未必容纳空集，未必能配对两个元素，未必聚得起谁的子集。一个集合宇宙必须供应什么，正是 **ZF 公理**要说的内容，本章把它们陈述出来。但不是作为公设：本书从不扩充自己的元理论，且本书的结构有许多个，而非某个钦定的宇宙。**ZF 模型**是一个以公理为字段的 record，于是「`𝒮` 满足 ZF」并无任何神秘之处：它只是说这个 record 在 `𝒮` 处有居民。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import FOL.Structure using ( ZFStructure; _∈ᵗ_ )

module ZF {ℓ} (𝒮 : ZFStructure (hPropAlgebra ℓ)) where
```

<!--en-->
Two standing choices, both announced in earlier chapters and both exercised here
for the first time. The truth algebra is the canonical `hPropAlgebra`{.Agda}: axioms
assert facts, and the book's mathematical facts live in `hProp`{.Agda} (per the
scope discipline, opening the algebra is what brings the logic symbols into
scope). And the constant interpretation is the canonical one from the semantics
chapter: the constant domain is the carrier itself and `ι` is the identity, so a
parameter appearing in a formula simply *is* the set it names.
<!--zh-->
两项常设选择，都在前面章节宣布过，都在此第一次真正上场。真值代数取典范的 `hPropAlgebra`{.Agda}：公理断言事实，而本书数学的事实住在 `hProp`{.Agda} (按作用域纪律，逻辑符号恰经打开代数入场)。常量解释也取语义章的典范情形：常量域就是载体自身，`ι` 为恒等，于是公式里出现的参数就**是**它指名的那个集合。
<!--/-->

```agda
open import FOL.Syntax using ( Formula; var; con; _∈̇_ )
open import FOL.Semantics (hPropAlgebra ℓ) 𝒮 using ( module At )
open import Cubical.Foundations.Prelude using ( isPropIsContr )
open import Cubical.Data.Sigma using ( Σ≡Prop )
open import Cubical.Induction.WellFounded using ( WellFounded; wf→x≮x )
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁ )

open TruthAlgebra (hPropAlgebra ℓ)
open ZFStructure 𝒮

private
  ι : S → S
  ι x = x

open At ι using ( _⊨_ )
```

<!--en-->
## Realizing a class as a set
<!--zh-->
## 把类实现为集合
<!--/-->

<!--en-->
Nearly every axiom to come has the same shape: *there is a set whose members are
exactly the so-and-so*. Pin down the "so-and-so" first. A **class** is a
propositional predicate on the carrier, `S → Ω`: something whose membership can be
stated, with no promise that any set collects it. (Classes have already appeared in
disguise: the restriction `𝒮 ↾ M` of the structure chapter cuts along exactly such
an `M`.) `IsSetOf Q b`{.Agda} then says the set `b` **realizes** the class `Q`,
membership for membership. Realization is pointwise equality in `hProp`, hence a
proposition, and `SetOf Q`{.Agda} packages a realizer with its evidence.
<!--zh-->
接下来的公理几乎全是同一个形状：**存在一个集合，其成员恰好是如此这般者**。先把「如此这般」定准。**类**是载体上的命题值谓词 `S → Ω`：可以谈论隶属，却不许诺有集合把它收拢。(类其实早已亮过相：结构章的限制 `𝒮 ↾ M` 就是沿这样一个 `M` 裁剪。) 于是 `IsSetOf Q b`{.Agda} 说集合 `b` 逐成员地**实现**类 `Q`。实现是 `hProp` 中的逐点相等，故为命题；`SetOf Q`{.Agda} 把实现者与证据打包。
<!--/-->

```agda
IsSetOf : (S → Ω) → S → Type (ℓ-suc ℓ)
IsSetOf Q b = (x : S) → (x ∈ˢ b) ≡ Q x

isPropIsSetOf : (Q : S → Ω) (b : S) → isProp (IsSetOf Q b)
isPropIsSetOf Q b = isPropΠ (λ x → isSetHProp _ _)

SetOf : (S → Ω) → Type (ℓ-suc ℓ)
SetOf Q = Σ[ b ∈ S ] IsSetOf Q b
```

<!--en-->
How many realizers can one class have? Under **extensionality** (sets with the same
members are equal; it will be the first field of the record) the answer is at most
one, in the strong, structural sense: any single realizer makes the whole type of
realizers contractible. The lemma takes extensionality as an explicit input,
because the record that will provide it has not been defined yet.
<!--zh-->
一个类能有几个实现者？在**外延公理** (成员相同的集合相等；它将是 record 的第一个字段) 之下，答案是至多一个，且是结构意义上的强「至多一」：任何一个实现者都让实现者的整个类型可缩。这条引理把外延性作为显式输入，因为供应它的 record 尚未定义。
<!--/-->

```agda
setOf-unique : ({a b : S} → ((x : S) → (x ∈ˢ a) ≡ (x ∈ˢ b)) → a ≡ b)
             → (Q : S → Ω) → SetOf Q → isContr (SetOf Q)
setOf-unique ext Q (b , sp) = (b , sp) , λ { (b' , sp') →
  Σ≡Prop (isPropIsSetOf Q) (ext (λ x → sp x ∙ sym (sp' x))) }
```

<!--en-->
## The description operator
<!--zh-->
## 摹状词算子
<!--/-->

<!--en-->
`isContr`{.Agda} is the host's **unique existence**, so `isContr (SetOf Q)` reads:
*there is exactly one set of the `Q`s*. Every existence axiom below takes this
form, and the payoff is immediate: given unique existence, "the set such that" is a
projection. The operator `℩` (a rotated iota, Russell's notation, read "that")
extracts the centre of contraction, and its specification is the second
projection. Where a classical treatment must adopt a description axiom to pass
from unique existence to a term, here the passage is two `fst`{.Agda}s.
<!--zh-->
`isContr`{.Agda} 是宿主的**唯一存在**，于是 `isContr (SetOf Q)` 读作：**恰有一个由 `Q` 者组成的集合**。下面的存在性公理全部取这个形态，而回报立竿见影：有了唯一存在，「那个满足条件的集合」就是一次投影。算子 `℩` (倒转的 iota，罗素的记号，读作「that」) 取出收缩中心，其规格是第二投影。经典处理要想从唯一存在走到一个词项，必须添一条描述公理；此处这段路只是两次 `fst`{.Agda}。
<!--/-->

```agda
℩ : {Q : S → Ω} → isContr (SetOf Q) → S
℩ c = c .fst .fst

℩-spec : {Q : S → Ω} (c : isContr (SetOf Q)) → IsSetOf Q (℩ c)
℩-spec c = c .fst .snd
```

<!--en-->
## Subsets
<!--zh-->
## 子集
<!--/-->

<!--en-->
One derived relation completes the vocabulary: `a ⊆ˢ b` when every member of `a`
is a member of `b`. The superscript is the structure-layer mark, as always.
<!--zh-->
还差一个派生关系把词汇备齐：`a ⊆ˢ b` 谓 `a` 的每个成员都是 `b` 的成员。上标一如既往是结构层的层标记。
<!--/-->

```agda
_⊆ˢ_ : S → S → Ω
a ⊆ˢ b = ⋀ S (λ x → (x ∈ˢ a) ⇒ (x ∈ˢ b))

infix 20 _⊆ˢ_
```

<!--en-->
## The axioms, as a record
<!--zh-->
## 公理，作为 record
<!--/-->

<!--en-->
Here is the heart of the chapter. The fields are the familiar list: extensionality,
regularity, empty set, pairing, union, separation, replacement, power set
(infinity joins below). Three of them repay a closer look before the code.

**Separation and replacement consume the book's own formulas.** A textbook writes
"for every formula `φ`"; these two fields take a `Formula S 1`{.Agda} or
`Formula S 2`{.Agda} and interpret it with the satisfaction relation of the
semantics chapter. The language built in Part 1 stops being an object of
contemplation here and starts bearing weight. Why formulas, and not arbitrary host
predicates `S → Ω`? Because that stronger schema is a different, second-order
theory: the point of ZF's separation is that only *first-order describable*
properties are guaranteed to cut sets out of sets. The gap between "predicate" and
"formula" is mathematical content, and Part 4's protagonist lives inside exactly
that gap.

**Regularity is stated at the meta level** (some books call it foundation): the
membership relation is well-founded, with `WellFounded`{.Agda} taken from the host
library rather than from any object-language sentence. The next section explains
why no sentence could do the job.

Everything else takes the unique-existence form just prepared, and will hand its
set over through `℩`.
<!--zh-->
这里是本章的心脏。字段就是熟悉的那串清单：外延、正则、空集、配对、并、分离、替换、幂集 (无穷稍后加入)。看代码之前，有三处值得多停留一眼。

**分离与替换消费本书自家的公式。**教科书写「对每条公式 `φ`」；这两个字段就收一条 `Formula S 1`{.Agda} 或 `Formula S 2`{.Agda}，并用语义章的满足关系解释它。第一部造出的语言在此不再是观赏对象，而开始承重。为什么收公式，而不收任意宿主谓词 `S → Ω`？因为那个更强的模式是另一门二阶理论：ZF 分离公理的要义恰在于，只有**一阶可描述**的性质才保证能从集合中切出集合。「谓词」与「公式」之间的落差是数学内容，第四部的主角就住在这道落差里。

**正则公理陈述在元层面** (有些书称基础公理)：成员关系是良基的，其中 `WellFounded`{.Agda} 取自宿主库，而非任何对象语言的句子。为什么没有句子能胜任，下一节交代。

其余字段全部取刚备好的唯一存在形态，届时经 `℩` 交出各自的集合。
<!--/-->

```agda
record isZFModel : Type (ℓ-suc ℓ) where
  field
    extensional    : {a b : S} → ((x : S) → (x ∈ˢ a) ≡ (x ∈ˢ b)) → a ≡ b
    regularity     : WellFounded (_∈ᵗ_ 𝒮)
    hasEmpty       : isContr (SetOf (λ _ → ⊥))
    hasPair        : (a b : S) → isContr (SetOf (λ x → (x ≈ˢ a) ⊔ (x ≈ˢ b)))
    hasUnion       : (a : S) → isContr (SetOf (λ x → ⋁ S (λ y → (y ∈ˢ a) ⊓ (x ∈ˢ y))))
    hasSeparation  : (a : S) (φ : Formula S 1)
                   → isContr (SetOf (λ x → (x ∈ˢ a) ⊓ ((x ∷ []) ⊨ φ)))
    hasReplacement : (a : S) (φ : Formula S 2)
                   → ((x : S) → ⟨ x ∈ˢ a ⟩ → isContr (Σ[ y ∈ S ] ⟨ (y ∷ x ∷ []) ⊨ φ ⟩))
                   → isContr (SetOf (λ y → ⋁ S (λ x → (x ∈ˢ a) ⊓ ((y ∷ x ∷ []) ⊨ φ))))
    hasPower       : (a : S) → isContr (SetOf (λ x → x ⊆ˢ a))
```

<!--en-->
Read each `λ` back into words and the familiar statements reappear. Nothing
realizes `⊥`, so `hasEmpty`{.Agda} is the empty set. The pair's members are
whatever equals `a` or `b`; the union's members are the members of members.
Separation keeps those members of `a` that satisfy `φ` (the environment `x ∷ []`
plugs the sole free variable). Replacement first asks `φ` to be functional on `a`,
one output per input in the `isContr`{.Agda} sense, then collects the outputs. The
power set's members are the subsets.
<!--zh-->
把每个 `λ` 读回自然语言，熟悉的陈述一一归位。没有谁实现 `⊥`，所以 `hasEmpty`{.Agda} 就是空集。配对的成员是与 `a` 或 `b` 相等者；并的成员是成员的成员。分离留下 `a` 中满足 `φ` 的成员 (环境 `x ∷ []` 把唯一的自由变量填上)。替换先要求 `φ` 在 `a` 上是函数性的，即 `isContr`{.Agda} 意义下一进一出，再收集输出。幂集的成员就是子集。
<!--/-->

<!--en-->
## Why regularity lives at the meta level
<!--zh-->
## 正则公理为何住在元层面
<!--/-->

<!--en-->
Every other axiom speaks either the object language or plain membership;
regularity alone reaches for the host's notion of well-foundedness. It has to:
**no first-order sentence expresses external well-foundedness**. The classical
argument deserves telling, though the book only tells it; nothing below depends on
it, and compactness is not developed here. Suppose some sentence held in exactly
the well-founded structures. Extend the language with fresh constants
$a_0, a_1, a_2, \dots$ and the axioms $a_{n+1} \in a_n$. Finitely many of these
axioms ask only for a descending chain of some finite length, which well-founded
structures supply; so every finite fragment of the extended theory has a model. The
**compactness theorem** of classical model theory then yields one structure
satisfying all of it at once: it satisfies the sentence, yet the constants trace an
infinite descending ∈-chain through it. So the sentence never captured
well-foundedness in the first place.

Compactness is a property of first-order logic itself; no choice of host system
moves this line, and a formalization can only choose where to be honest about it.
Here the choice is: regularity lives at the meta level, as a field. The ceiling
also has a productive face. It shows that the first-order shadow of a structure is
strictly coarser than the structure, so restricting attention to "what first-order
formulas can see" is a genuine restriction. Part 4 builds its universe out of
precisely that restriction; were the shadow lossless, the construction would
return everything and prove nothing.
<!--zh-->
其余公理说的要么是对象语言，要么是单纯的成员关系；唯独正则公理伸手去取宿主的良基概念。这是不得不然：**没有任何一阶句子能表达外部良基性**。这个经典论证值得讲一遍，尽管本书只讲不证；下文不依赖它，紧致性也不在本书展开。假设某句子恰好在良基结构中成立。给语言添上新常量 $a_0, a_1, a_2, \dots$ 与公理 $a_{n+1} \in a_n$。这些公理中的有限多条只要求一条有限长的下降链，良基结构供应得起；于是扩充理论的每个有限片段都有模型。经典模型论的**紧致性定理**随即给出一个一次满足全部公理的结构：它满足那个句子，常量却在其中划出一条无穷下降的 ∈-链。可见那个句子从头就没有抓住良基性。

紧致性是一阶逻辑自身的性质；换任何宿主系统都动不了这条线，形式化能选择的只是在哪里对它诚实。此处的选择是：正则公理住在元层面，作为字段。这道天花板也有多产的一面。它表明结构的一阶影子严格粗于结构本身，于是把眼光限制到「一阶公式看得见的东西」是一次真正的限制。第四部的宇宙恰恰用这次限制建成；影子若是无损的，那个构造将原样吐回一切，什么也证明不了。
<!--/-->

<!--en-->
## The derived operations
<!--zh-->
## 派生运算
<!--/-->

<!--en-->
Now `℩` discharges each unique existence into an operation, and `℩-spec`{.Agda}
into its specification; every specification below is literally one projection. The
union of a pair gives binary union, and binary union gives the **successor**
`a ⁺ = a ∪ {a}` (the pair of `a` with itself is the singleton): von Neumann's step
from a set to the next, the ladder the axiom of infinity will climb.
<!--zh-->
现在让 `℩` 把每个唯一存在兑成运算，让 `℩-spec`{.Agda} 兑成规格；下面每条规格都不折不扣是一次投影。配对之并给出二元并，二元并给出**后继** `a ⁺ = a ∪ {a}` (`a` 与自身的配对即单点集)：冯·诺伊曼从一个集合迈向下一个的那一步，也是无穷公理稍后要攀的梯子。
<!--/-->

```agda
  ∅ : S
  ∅ = ℩ hasEmpty

  ∅-spec : IsSetOf (λ _ → ⊥) ∅
  ∅-spec = ℩-spec hasEmpty

  pair : S → S → S
  pair a b = ℩ (hasPair a b)

  pair-spec : ∀ a b → IsSetOf (λ x → (x ≈ˢ a) ⊔ (x ≈ˢ b)) (pair a b)
  pair-spec a b = ℩-spec (hasPair a b)

  ⋃ : S → S
  ⋃ a = ℩ (hasUnion a)

  ⋃-spec : ∀ a → IsSetOf (λ x → ⋁ S (λ y → (y ∈ˢ a) ⊓ (x ∈ˢ y))) (⋃ a)
  ⋃-spec a = ℩-spec (hasUnion a)

  _∪_ : S → S → S
  a ∪ b = ⋃ (pair a b)

  _⁺ : S → S
  a ⁺ = a ∪ pair a a

  separate : (a : S) → Formula S 1 → S
  separate a φ = ℩ (hasSeparation a φ)

  separate-spec : ∀ a φ → IsSetOf (λ x → (x ∈ˢ a) ⊓ ((x ∷ []) ⊨ φ)) (separate a φ)
  separate-spec a φ = ℩-spec (hasSeparation a φ)

  𝒫 : S → S
  𝒫 a = ℩ (hasPower a)

  𝒫-spec : ∀ a → IsSetOf (λ x → x ⊆ˢ a) (𝒫 a)
  𝒫-spec a = ℩-spec (hasPower a)
```

<!--en-->
## First dividend: intersection without an axiom
<!--zh-->
## 第一笔红利：不设公理的交
<!--/-->

<!--en-->
Binary intersection is deliberately **not** a field. The two-symbol formula
`var zero ∈̇ con b`{.Agda} says "the variable is a member of `b`"; hand it to
`separate`{.Agda} at `a` and the axioms hand back `a ∩ b`. Better: its
specification *is* the separation specification, verbatim, because satisfaction of
that formula computes to `x ∈ˢ b` by the defining clauses of `⊨`. The faithfulness
the semantics chapter promised is now paying out in sets, not just in logic.

This is also the chapter's honest confession. One formula was cheap to write by
hand. But the book will need a formula for every predicate it ever wants to
separate or replace along, each with a proof that the formula means that
predicate, and hand-assembling syntax at that scale is out of the question.
Turning host predicates into formulas, certificate included, is a craft of its
own, the *reification* framework catalogued at the book's tail; the witnesses
it runs on, the Levy grades and their travel theorems, are already in hand from
the close of Part 1.
<!--zh-->
二元交刻意**不设**为字段。两个符号的公式 `var zero ∈̇ con b`{.Agda} 说「该变量是 `b` 的成员」；把它递给 `separate`{.Agda} 作用在 `a` 上，公理便交回 `a ∩ b`。更妙的是：它的规格就**是**分离的规格，一字不差，因为按 `⊨` 的定义子句，那条公式的满足直接计算为 `x ∈ˢ b`。语义章许诺的忠实性，此刻开始以集合、而不只是以逻辑付账。

这也是本章的坦白。一条公式手写便宜。可本书今后想沿着分离或替换使用的每个谓词都需要一条公式，每条还得配上「公式的含义恰是该谓词」的证明，那样的规模之下手工拼装语法绝无可能。把宿主谓词变成公式、随附保义证书，这门手艺自成一体，即编在书末的 reification 框架；它所依赖的见证，即 Lévy 分级与其旅行定理，第一部收束时已然在手。
<!--/-->

```agda
  _∩_ : S → S → S
  a ∩ b = separate a (var zero ∈̇ con b)

  ∩-spec : ∀ a b x → (x ∈ˢ (a ∩ b)) ≡ ((x ∈ˢ a) ⊓ (x ∈ˢ b))
  ∩-spec a b x = separate-spec a (var zero ∈̇ con b) x
```

<!--en-->
## Infinity
<!--zh-->
## 无穷
<!--/-->

<!--en-->
One axiom remains, the one that forces a genuinely infinite set into existence.
The **numerals** are the von Neumann naturals: `∅`, `∅ ⁺`, `(∅ ⁺) ⁺`, and so on.
The record takes the chain itself as a field, pinned down by two propositional
equations phrased in raw membership and equality: the zeroth numeral has no
members, and the members of a successor numeral are exactly the previous numeral
and its members. By extensionality the two equations say precisely
`numeral zero ≡ ∅` and `numeral (suc n) ≡ numeral n ⁺`, so nothing is weaker than
defining the chain outright. What is gained is room: the equations never mention
the derived `∅`{.Agda} and `_⁺`{.Agda}, so a concrete model may present the chain
in whatever form its carrier computes best and discharge them without ever
unfolding the description operator.
<!--zh-->
只剩一条公理了，正是那条强迫一个真正无穷的集合存在的公理。**数码**就是冯·诺伊曼自然数：`∅`、`∅ ⁺`、`(∅ ⁺) ⁺`，如此下去。record 把这条链本身收作字段，用两条以裸成员与裸等词措辞的命题方程钉死：第零个数码没有成员，后继数码的成员恰是前一个数码及其成员。经外延公理，这两条方程说的正是 `numeral zero ≡ ∅` 与 `numeral (suc n) ≡ numeral n ⁺`，所以比起直接定义这条链，强度分毫未减。换来的是余地：方程从不提及派生的 `∅`{.Agda} 与 `_⁺`{.Agda}，于是具体模型可以用其载体算得最顺手的形式给出这条链，兑现方程时完全不必展开摹状词算子。
<!--/-->

```agda
  field
    numeral      : ℕ → S
    numeral-zero : (z : S) → ⟨ z ∈ˢ numeral zero ⟩ → Empty.⊥
    numeral-suc  : (n : ℕ) (z : S)
                 → (⟨ z ∈ˢ numeral (suc n) ⟩ → ⟨ (z ∈ˢ numeral n) ⊔ (z ≈ˢ numeral n) ⟩)
                 × (⟨ (z ∈ˢ numeral n) ⊔ (z ≈ˢ numeral n) ⟩ → ⟨ z ∈ˢ numeral (suc n) ⟩)
```

<!--en-->
`isNumeral`{.Agda} is the class this chain sweeps out: *equal to some numeral*.
The quantification runs over `ℕ` lifted to the working level, since the book's
indexing data lives at the bottom universe. The **axiom of infinity**, in the
strong form this book uses, then says: that class is a set. Stated this way it is
strictly stronger than the usual "some set contains `∅` and is closed under
successor", and it is the version that makes `ω` directly usable as *the* set of
naturals: every member of `ω` is a numeral, not merely every numeral a member.
<!--zh-->
`isNumeral`{.Agda} 是这条链扫出的类：**与某个数码相等**。量化取提升到工作层级的 `ℕ`，因为本书的索引数据住在最底层宇宙。而**无穷公理**，取本书采用的强形式，说的就是：这个类是集合。如此陈述严格强于通常的「存在一个含 `∅` 且对后继封闭的集合」，而正是这个版本让 `ω` 可以直接当作**那个**自然数集来用：`ω` 的每个成员都是数码，而不只是每个数码都是成员。
<!--/-->

```agda
  isNumeral : S → Ω
  isNumeral x = ⋁ (Lift {ℓ-zero} {ℓ} ℕ) (λ n → x ≈ˢ numeral (lower n))

  field
    hasInfinity : isContr (SetOf isNumeral)

  ω : S
  ω = ℩ hasInfinity

  ω-spec : IsSetOf isNumeral ω
  ω-spec = ℩-spec hasInfinity
```

<!--en-->
## First theorems
<!--zh-->
## 最初的定理
<!--/-->

<!--en-->
Extensionality upgrades the whole existence apparatus once and for all. Any
realizer is the unique realizer (`uniqueSetOf`{.Agda}); and even a *merely*
existing realizer, hidden under propositional truncation, reproduces unique
existence (`mereSetOf→isContr`{.Agda}). The pattern of the classical description
axiom recurs here as a theorem: to build "the set of the `Q`s" it will always
suffice to show some set of the `Q`s merely exists. Regularity draws first blood
too: no set is a member of itself.
<!--zh-->
外延公理把整套存在装置一次性升级。任何实现者都是唯一实现者 (`uniqueSetOf`{.Agda})；哪怕只是**仅仅**存在、藏在命题截断之下的实现者，也能复现唯一存在 (`mereSetOf→isContr`{.Agda})。经典描述公理的模式在此以定理身份重现：今后要造「由 `Q` 者组成的那个集合」，永远只需证明这样的集合仅仅存在。正则公理也开了第一刀：没有集合是自己的成员。
<!--/-->

```agda
  uniqueSetOf : (Q : S → Ω) → SetOf Q → isContr (SetOf Q)
  uniqueSetOf = setOf-unique extensional

  mereSetOf→isContr : (Q : S → Ω) → ∥ SetOf Q ∥₁ → isContr (SetOf Q)
  mereSetOf→isContr Q = PT.rec isPropIsContr (uniqueSetOf Q)

  x∉x : (x : S) → ⟨ x ∈ˢ x ⟩ → Empty.⊥
  x∉x x h = wf→x≮x regularity h
```

<!--en-->
## ZFC: choice as an extension
<!--zh-->
## ZFC：作为扩展的选择公理
<!--/-->

<!--en-->
The line between ZF and ZFC is drawn as a record boundary, because the book's
capstone lives on that line: Part 4 constructs, inside any model of ZF, a
sub-universe satisfying choice, and folding choice into the base record would
erase the very distinction that construction is about. The **axiom of choice** is
taken in choice-set form: given a set `a` whose members are nonempty and pairwise
disjoint, some set meets each member of `a` in exactly one point. This form is
stated with membership and the derived intersection alone; its equivalence with
the other formulations is model-internal mathematics, deferred until needed. Note
that the hypotheses and the conclusion all wear the truncation `∥_∥₁`{.Agda}:
choice asserts bare existence, promising no canonical choice set, and that
reticence is exactly its force.
<!--zh-->
ZF 与 ZFC 的分界线画成了 record 的边界，因为本书的压轴戏就住在这条线上：第四部将在任意 ZF 模型内部构造一个满足选择公理的子宇宙，若把选择混入基础 record，恰恰抹掉了那个构造所要谈论的分界。**选择公理**取选择集形态：给定一个集合 `a`，其成员非空且两两不交，则存在一个集合与 `a` 的每个成员恰交于一点。这个形态仅用成员关系与派生的交即可陈述；它与其他表述的等价性属于模型内部的数学，推迟到需要时再证。留意各前提与结论都穿着截断 `∥_∥₁`{.Agda}：选择公理断言的是赤裸的存在，不许诺任何典范选择集，而这份缄默正是它的力量所在。
<!--/-->

```agda
record isZFCModel : Type (ℓ-suc ℓ) where
  field
    zf : isZFModel
  open isZFModel zf public
  field
    hasChoice :
      (a : S)
      → ((x : S) → ⟨ x ∈ˢ a ⟩ → ∥ Σ[ y ∈ S ] ⟨ y ∈ˢ x ⟩ ∥₁)
      → ((x y : S) → ⟨ x ∈ˢ a ⟩ → ⟨ y ∈ˢ a ⟩
           → ∥ Σ[ z ∈ S ] (⟨ z ∈ˢ x ⟩ × ⟨ z ∈ˢ y ⟩) ∥₁ → x ≡ y)
      → ∥ Σ[ c ∈ S ] ((x : S) → ⟨ x ∈ˢ a ⟩
           → isContr (Σ[ z ∈ S ] ⟨ z ∈ˢ (c ∩ x) ⟩)) ∥₁
```

<!--en-->
## Recap
<!--zh-->
## 小结
<!--/-->

<!--en-->
A model of ZF is a record: extensionality, meta-level regularity (the compactness
ceiling makes any other placement dishonest), unique-existence fields for the
constructions, separation and replacement consuming the book's own formulas, and
strong infinity through the numeral chain. `℩` turns fields into operations whose
specifications are projections; intersection fell out of separation and a
two-symbol formula, the first set built by feeding the framework its own language.
`isZFCModel`{.Agda} adds choice on top. The record's appetite for formulas is now
the book's outstanding debt; the reification framework at the book's tail is the
factory that will pay it, running on the witnesses Part 1 already forged.
<!--zh-->
ZF 模型是一个 record：外延公理、元层面的正则公理 (紧致性天花板使其他任何安置都不诚实)、以唯一存在形态陈述的诸构造字段、消费本书自家公式的分离与替换，以及经数码链的强无穷。`℩` 把字段兑成运算，规格皆为投影；交由分离加一条两符号公式落袋，是框架吃自家语言造出的第一个集合。`isZFCModel`{.Agda} 在其上添加选择。record 对公式的胃口成了本书的未清之债；书末的 reification 框架是将来还债的工厂，其燃料，即见证，第一部已锻造完毕。
<!--/-->
