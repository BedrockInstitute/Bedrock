<!--en-->
# Models of ZF and ZFC

A bare structure becomes a model of set theory by supplying witnesses for the ZF axioms. This chapter formulates those witnesses as record fields, develops the set-description operations they provide, and extends a ZF model to ZFC by adding the axiom of choice.
<!--zh-->
# ZF 与 ZFC 的模型

一个裸结构通过为 ZF 公理提供见证而成为集合论模型。本章将这些见证表述为 record 字段，构造由它们给出的集合描述运算，并加入选择公理，把 ZF 模型扩展为 ZFC 模型。
<!--ja-->
# ZF と ZFC のモデル

公理を持たない構造は、ZF の各公理の証拠を与えることで集合論のモデルになります。本章ではその証拠を record のフィールドとして定式化し、そこから得られる集合記述の演算を整え、選択公理を加えて ZF モデルを ZFC へ拡張します。
<!--/-->

<!--en-->
The first-order logic chapters built a language, gave it worlds to talk about, and pinned down meaning. But
nothing so far deserves the name set theory: a bare structure asserts nothing. Its
membership relation need not admit an empty set, need not pair two elements, and need
not gather the subsets of anything. What a universe of sets must provide is exactly
what the **axioms of ZF** say, and this chapter states them. Not as postulates,
though: the book never extends its metatheory, and its structures are many, not one
chosen universe. A **model of ZF** is a record whose fields *are* the axioms, so
"`𝒮` satisfies ZF" means nothing more mysterious than "this record has an
inhabitant at `𝒮`".
<!--zh-->
前面几章建立了一阶逻辑：造出了语言，给出了它可谈论的世界，也确定了含义。但至此还没有任何东西配得上「集合论」之名：裸结构对一切都未作断言，它的成员关系未必容纳空集，未必能配对两个元素，也未必能聚出子集。一个集合宇宙必须提供什么，正是 **ZF 公理**所陈述的内容，本章把它们一一写出。但这不是把它们作为公设：本书从不扩充自己的元理论，而且书中的结构有许多个，并非只选定某一个宇宙。**ZF 模型**是一个以公理为字段的 record，因此「`𝒮` 满足 ZF」没有任何神秘之处：它只是说这个 record 在 `𝒮` 处有实例。
<!--/-->



```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import FOL.ZFStructure using ( ZFStructure; module hPropStructure )

module FOL.ZFModel {ℓ} (𝒮 : ZFStructure (hPropAlgebra ℓ)) where
```

<!--en-->
Two standing choices, both announced in earlier chapters and both exercised here
for the first time. The truth algebra is the canonical `hPropAlgebra`{.Agda}: axioms
assert facts, and the book's mathematical facts live in `hProp`{.Agda} (per the
scope discipline, opening the algebra is what brings the logic symbols into
scope). And the constant interpretation is the canonical one from the semantics
chapter: the constant domain is the carrier itself and the interpretation is
`id`{.Agda}, so a parameter appearing in a formula simply *is* the set it names.
<!--zh-->
两项常设选择都在前面章节宣布过，在此第一次真正派上用场。真值代数取典范的 `hPropAlgebra`{.Agda}：公理断言事实，而本书数学的事实就落在 `hProp`{.Agda} 中 (按作用域规则，打开该代数后逻辑符号即可使用)。常元解释也取语义章的典范情形：常元域就是载体自身，解释就是 `id`{.Agda}，于是公式里出现的参数就**是**它指名的那个集合。
<!--/-->

```agda
open import FOL.Syntax using ( Formula; var; con; _∈̇_ )
open import FOL.Semantics (hPropAlgebra ℓ) 𝒮 using ( module At )
open import Cubical.Data.Sigma using ( Σ≡Prop )
open import Cubical.Induction.WellFounded using ( WellFounded )
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁ )

open TruthAlgebra (hPropAlgebra ℓ)
open hPropStructure 𝒮

open At S id using ( _⊨_ )
```

<!--en-->
## Realizing a class as a set

Nearly every axiom to come has the same shape: *there is a set whose members are
exactly the so-and-so*. Pin down the "so-and-so" first. A **class** is a
propositional predicate on the carrier, `S → Ω`: something whose membership can be
stated, with no promise that any set collects it. (Classes have already appeared in
disguise: the restriction `𝒮 ↾ M` of the structure chapter cuts along exactly such
an `M`.) `IsSetOf Q b`{.Agda} then says the set `b` **realizes** the class `Q`,
membership for membership. Realization is pointwise equality in `hProp`, hence a
proposition, and `SetOf Q`{.Agda} packages a realizer with its evidence.
<!--zh-->
## 把类实现为集合

接下来的公理几乎全是同一个形状：**存在一个集合，其成员恰好是如此这般者**。先把「如此这般」说清楚。**类**是载体上的命题值谓词 `S → Ω`：可以对它谈论隶属，却不保证有集合恰好收齐它的全部成员。(类在前面已经出现过：结构章的限制 `𝒮 ↾ M` 正是沿这样一个 `M` 进行的。) 于是 `IsSetOf Q b`{.Agda} 说集合 `b` 逐成员地**实现**类 `Q`。实现是 `hProp` 中的逐点相等，故为命题；`SetOf Q`{.Agda} 把实现者与其证据一并给出。
<!--ja-->
## クラスを集合として実現する

`SetOf Q`{.Agda} は、クラス `Q` と同じ要素を持つ集合とその仕様を組にします。外延性があれば、そのような集合は一意なので、存在証拠から正準な代表を安全に取り出せます。
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
一个类能有几个实现者？在**外延公理** (成员相同的集合相等；它将是 record 的第一个字段) 之下，答案是至多一个，而且是结构意义上的强「至多一」：任何一个实现者都使实现者的整个类型可缩。这条引理把外延性作为显式输入，因为提供外延性的 record 此时还没有定义。
<!--/-->

```agda
setOf-unique : ({a b : S} → ((x : S) → (x ∈ˢ a) ≡ (x ∈ˢ b)) → a ≡ b)
             → (Q : S → Ω) → SetOf Q → isContr (SetOf Q)
setOf-unique ext Q (b , sp) = (b , sp) , λ { (b' , sp') →
  Σ≡Prop (isPropIsSetOf Q) (ext (λ x → sp x ∙ sym (sp' x))) }
```

<!--en-->
## The description operator

`isContr`{.Agda} is the host's **unique existence**, so `isContr (SetOf Q)` reads:
*there is exactly one set of the `Q`s*. Every existence axiom below takes this
form, and the payoff is immediate: given unique existence, "the set such that" is a
projection. The operator `℩` (a rotated iota, Russell's notation, read "that")
extracts the centre of contraction, and its specification is the second
projection. Where a classical treatment must adopt a description axiom to pass
from unique existence to a term, here the passage is two `fst`{.Agda}s.
<!--zh-->
## 摹状词算子

`isContr`{.Agda} 是宿主的**唯一存在**，因此 `isContr (SetOf Q)` 读作：**恰有一个由 `Q` 者组成的集合**。后面的存在性公理都采用这一形式，其好处立即可见：有了唯一存在，「那个满足条件的集合」就是一次投影。算子 `℩` (倒转的 iota，罗素的记号，读作「that」) 取出收缩中心，其规格是第二投影。经典处理中，要从唯一存在得到一个词项，必须另加描述公理；这里则只需两次 `fst`{.Agda}。
<!--ja-->
## 確定記述の演算子

一意存在する集合を `℩`{.Agda} で選び、その要素条件を `℩-spec`{.Agda} で読み戻します。これは任意選択ではなく、一意性を証明した記述だけに使う演算です。
<!--/-->



```agda
℩ : {Q : S → Ω} → isContr (SetOf Q) → S
℩ c = c .fst .fst

℩-spec : {Q : S → Ω} (c : isContr (SetOf Q)) → IsSetOf Q (℩ c)
℩-spec c = c .fst .snd
```

<!--en-->
## Subsets

One derived relation completes the vocabulary: `a ⊆ˢ b` when every member of `a`
is a member of `b`. The superscript is the structure-layer mark, as always.
<!--zh-->
## 子集

还需要一个派生关系来补全词汇：`a ⊆ˢ b` 谓 `a` 的每个成员都是 `b` 的成员。上标一如既往是结构层的层标记。
<!--ja-->
## 部分集合

`A ⊆ˢ B`{.Agda} は、`A` の各要素が `B` にも属することを表します。この関係は、分出や冪集合の公理を簡潔に述べるための基礎になります。
<!--/-->



```agda
_⊆ˢ_ : S → S → Ω
a ⊆ˢ b = ⋀ S (λ x → (x ∈ˢ a) ⇒ (x ∈ˢ b))

infix 20 _⊆ˢ_
```

<!--en-->
## The axioms, as a record

Here is the heart of the chapter. The fields are the familiar list: extensionality,
regularity, empty set, pairing, union, separation, replacement, power set
(infinity joins below). Three of them repay a closer look before the code.
<!--zh-->
## 公理，作为 record

这里是本章的核心。字段就是熟悉的那串清单：外延、正则、空集、配对、并、分离、替换、幂集 (无穷稍后加入)。看代码之前，有三处值得多看一眼。
<!--ja-->
## record としての ZF 公理

`isZFModel`{.Agda} は外延性、正則性、空集合、対、和集合、分出、置換、冪集合、無限などの証拠を一つの record に集めます。各フィールドは具体的な構造で証明すべき性質です。
<!--/-->

<!--en-->
**Separation and replacement take the book's own formulas as input.** A textbook writes
"for every formula `φ`"; these two fields take a `Formula S 1`{.Agda} or
`Formula S 2`{.Agda} and interpret it with the satisfaction relation of the
semantics chapter. The language built in the first-order logic chapters is no longer
merely an object of study here; it now does real work. Why formulas, and not arbitrary host
predicates `S → Ω`? Because that stronger schema belongs to a different, second-order
theory: the point of ZF's separation is that only *first-order describable*
properties are guaranteed to cut sets out of sets. The gap between "predicate" and
"formula" is mathematical content, and the constructible universe lives inside exactly
that gap.

**Regularity is stated at the meta level** (some books call it foundation): the
membership relation is well-founded, with `WellFounded`{.Agda} taken from the host
library rather than from any object-language sentence. The next section explains
why no sentence could do the job.

Everything else takes the unique-existence form just prepared, and each will obtain
its set through `℩`.
<!--zh-->
**分离与替换以本书自己的公式为输入。**教科书写「对每条公式 `φ`」；这两个字段则收一条 `Formula S 1`{.Agda} 或 `Formula S 2`{.Agda}，并用语义章的满足关系解释它。一阶逻辑诸章造出的语言在此不再只是被研究的对象，而真正派上了用场。为什么收公式，而不收任意宿主谓词 `S → Ω`？因为那个更强的模式属于另一门二阶理论：ZF 分离公理的要义恰在于，只有**一阶可描述**的性质才保证能从集合中切出集合。「谓词」与「公式」之间的落差是数学内容，可构造宇宙正处在这道落差之中。

**正则公理陈述在元层面** (有些书称基础公理)：成员关系是良基的，其中 `WellFounded`{.Agda} 取自宿主库，而非任何对象语言的句子。为什么没有句子能胜任，下一节交代。

其余字段全部采用刚准备好的唯一存在形态，届时各自经 `℩` 得到相应的集合。
<!--/-->

```agda
record isZFModel : Type (ℓ-suc ℓ) where
  field
    extensional    : {a b : S} → ((x : S) → (x ∈ˢ a) ≡ (x ∈ˢ b)) → a ≡ b
    regularity     : WellFounded _∈ᵗ_
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
把每个 `λ` 读回自然语言，熟悉的陈述一一归位。没有谁实现 `⊥`，所以 `hasEmpty`{.Agda} 就是空集。配对的成员是与 `a` 或 `b` 相等者；并的成员是成员的成员。分离留下 `a` 中满足 `φ` 的成员 (环境 `x ∷ []` 把唯一的自由变量填上)。替换先要求 `φ` 在 `a` 上是函数性的，即在 `isContr`{.Agda} 意义下一进一出，再收集输出。幂集的成员就是子集。
<!--/-->

<!--en-->
## Why regularity lives at the meta level

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
<!--zh-->
## 正则公理为何置于元层面

其余公理说的要么是对象语言，要么是单纯的成员关系；唯独正则公理要借助宿主的良基概念。这是不得不然：**没有任何一阶句子能表达外部良基性**。这个经典论证值得讲一遍，尽管本书只讲不证；下文不依赖它，紧致性也不在本书展开。假设某句子恰好在良基结构中成立。给语言添上新常元 $a_0, a_1, a_2, \dots$ 与公理 $a_{n+1} \in a_n$。这些公理中的有限多条只要求一条有限长的下降链，良基结构足以供应；于是扩充理论的每个有限片段都有模型。经典模型论的**紧致性定理**随即给出一个一次满足全部公理的结构：它满足那个句子，常元却在其中划出一条无穷下降的 ∈-链。可见那个句子从头就没有刻画良基性。
<!--ja-->
## 正則性公理をメタレベルに置く理由

正則性公理は任意の一階式ではなく、構造の Type 値の所属関係が整礎であることとして記録します。この強い形から所属に沿う再帰と帰納を直接利用できます。
<!--/-->

<!--en-->
Compactness is a property of first-order logic itself; no choice of host system
changes that, and a formalization can only choose where to state it explicitly.
Here the choice is: regularity lives at the meta level, as a field. This limitation
also has a productive face: it shows that the first-order fragment of a
structure captures strictly less than the whole structure, so restricting attention
to "what first-order formulas can see" is a genuine restriction. The
constructible-universe development builds its universe out of precisely this
restriction; if the first-order fragment were lossless, the construction would
return everything and prove nothing.
<!--zh-->
紧致性是一阶逻辑自身的性质，更换宿主系统不会改变这一事实；形式化只能明确选择在哪一层陈述正则公理。这里把正则公理作为元层面的字段。这个限制也说明，结构的一阶可表达信息严格少于结构的全部信息，因此只考虑一阶公式能够表达的性质确实缩小了范围。可构造宇宙各章正是利用这一限制来构造其宇宙；如果一阶表达保留了结构的全部信息，该构造只会得到原来的全部对象，无法证明所需结果。
<!--/-->

<!--en-->
## The derived operations

Now `℩` turns each unique existence into an operation, and `℩-spec`{.Agda}
turns it into its specification; every specification below is literally one
projection. The union of a pair gives binary union, and binary union gives the
**successor** `a ⁺ = a ∪ {a}` (the pair of `a` with itself is the
singleton): this is von Neumann's step from one set to the next, the step the
axiom of infinity will later use.
<!--zh-->
## 派生运算

现在用 `℩` 把每个唯一存在实现为运算，并用 `℩-spec`{.Agda} 给出规格；下面每条规格都是一次投影。配对之并给出二元并，二元并又给出**后继** `a ⁺ = a ∪ {a}` (`a` 与自身的配对即单点集)：这是从一个集合到下一个集合的冯·诺伊曼后继步骤，也是无穷公理稍后所用的那一步。
<!--ja-->
## 公理から得られる演算

モデルの存在フィールドと確定記述を組み合わせ、空集合、対、和集合、分出集合、像、冪集合を実際の集合を返す演算として定義します。各仕様定理が元の公理を使いやすい等式に変えます。
<!--/-->



```agda
  ∅ : S
  ∅ = ℩ hasEmpty

  pair : S → S → S
  pair a b = ℩ (hasPair a b)

  pair-spec : ∀ a b → IsSetOf (λ x → (x ≈ˢ a) ⊔ (x ≈ˢ b)) (pair a b)
  pair-spec a b = ℩-spec (hasPair a b)

  ⋃ : S → S
  ⋃ a = ℩ (hasUnion a)

  _∪_ : S → S → S
  a ∪ b = ⋃ (pair a b)

  separate : (a : S) → Formula S 1 → S
  separate a φ = ℩ (hasSeparation a φ)

  separate-spec : ∀ a φ → IsSetOf (λ x → (x ∈ˢ a) ⊓ ((x ∷ []) ⊨ φ)) (separate a φ)
  separate-spec a φ = ℩-spec (hasSeparation a φ)

  𝒫 : S → S
  𝒫 a = ℩ (hasPower a)

```

<!--en-->
## First dividend: intersection without an axiom

Binary intersection is deliberately **not** a field. The two-symbol formula
`var zero ∈̇ con b`{.Agda} says "the variable is a member of `b`"; pass it to
`separate`{.Agda} at `a` and the axioms return `a ∩ b`. Its
specification is exactly the separation specification, verbatim, because
satisfaction of that formula computes to `x ∈ˢ b` by the defining
clauses of `⊨`. The faithfulness proved in the semantics chapter can therefore be
used directly to construct sets.
<!--zh-->
## 第一笔红利：不设公理的交

二元交刻意**不设**为字段。两个符号的公式 `var zero ∈̇ con b`{.Agda} 表示「该变量是 `b` 的成员」；把它传给 `separate`{.Agda} 并作用于 `a`，分离公理就给出 `a ∩ b`。它的规格与分离的规格完全相同，因为按 `⊨` 的定义子句，该公式的满足直接计算为 `x ∈ˢ b`。这说明语义章证明的忠实性可以直接用于构造集合。
<!--ja-->
## 第一の帰結：公理を使わない共通部分

共通部分は新しい公理を必要としません。和集合で候補の上界を作り、分出によってすべての構成集合に属する要素だけを残すことで、その仕様を証明します。
<!--/-->

<!--en-->
This is also a candid remark about the chapter. One formula was cheap to write by
hand. But the book will need a formula for every predicate it ever wants to
separate or replace along, each with a proof that the formula means that
predicate, and hand-assembling syntax at that scale is out of the question.
Turning host predicates into formulas, certificate included, is a technique of its
own, the *reification* framework catalogued at the book's tail; the witnesses
it runs on, the Levy grades and their travel theorems, are already in hand from
the close of the first-order logic chapters.
<!--zh-->
这也是本章的坦白。手写一条公式很容易。可本书今后想沿着分离或替换使用的每个谓词都需要一条公式，每条还得配上「公式的含义恰是该谓词」的证明，那样的规模之下手工拼装语法绝无可能。把宿主谓词变成公式、随附保义证书，这套方法自成一体，即编在书末的 reification 框架；它所依赖的见证，即 Lévy 分级与其旅行定理，到绝对性定理完成时便可备齐。
<!--/-->

```agda
  _∩_ : S → S → S
  a ∩ b = separate a (var zero ∈̇ con b)

  ∩-spec : ∀ a b x → (x ∈ˢ (a ∩ b)) ≡ ((x ∈ˢ a) ⊓ (x ∈ˢ b))
  ∩-spec a b x = separate-spec a (var zero ∈̇ con b) x
```

<!--en-->
## Infinity

One axiom remains, the one that forces a genuinely infinite set into existence.
The **numerals** are the von Neumann naturals: `∅`, `∅ ⁺`, `(∅ ⁺) ⁺`, and so on.
The record takes the chain itself as a field, pinned down by two propositional
equations phrased in raw membership and equality: the zeroth numeral has no
members, and the members of a successor numeral are exactly the previous numeral
and its members. By extensionality the two equations yield precisely
`numeral zero ≡ ∅` and `numeral (suc n) ≡ numeral n ⁺`, so this is exactly as strong as
defining the chain outright. What is gained is latitude: the equations never mention
the derived `∅`{.Agda}, so a concrete model may present the chain in whatever
form is most convenient to compute with on its carrier and discharge them without ever unfolding the
description operator.
<!--zh-->
## 无穷

只剩无穷公理，它要求一个真正无穷的集合存在。**数码**是冯·诺伊曼自然数：`∅`、`∅ ⁺`、`(∅ ⁺) ⁺`，如此继续。record 把数码链本身作为字段，并用两条以裸成员与裸等词表述的命题方程确定它：第零个数码没有成员，后继数码的成员恰是前一个数码及其成员。由外延公理，这两条方程分别给出 `numeral zero ≡ ∅` 与 `numeral (suc n) ≡ numeral n ⁺`，所以其强度与直接定义数码链相同。方程不提及派生的 `∅`{.Agda}，因此具体模型可以采用最便于载体计算的数码链定义，并在证明方程时避免展开摹状词算子。
<!--ja-->
## 無限

無限公理の証拠から集合 `ω` と零、後続閉包を取り出します。さらに仕様を使って、`ω` の要素がちょうど有限数項であることを示す準備を整えます。
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
`isNumeral`{.Agda} determines the class of objects *equal to some numeral*.
The quantification runs over `ℕ` lifted to the working level, since the book's
indexing data lives at the bottom universe. The **axiom of infinity**, in the
strong form this book uses, then says: that class is a set. Stated this way it is
strictly stronger than the usual "some set contains `∅` and is closed under
successor", and it is the version that makes `ω` directly usable as *the* set of
naturals: every member of `ω` is a numeral, not merely every numeral a member.
<!--zh-->
`isNumeral`{.Agda} 所定出的类，由**与某个数码相等**的对象组成。量化取提升到工作层级的 `ℕ`，因为本书的索引数据住在最底层宇宙。而**无穷公理**，取本书采用的强形式，说的就是：这个类是集合。如此陈述严格强于通常的「存在一个含 `∅` 且对后继封闭的集合」，而正是这个版本让 `ω` 可以直接当作**那个**自然数集来用：`ω` 的每个成员都是数码，而不只是每个数码都是成员。
<!--/-->

```agda
  isNumeral : S → Ω
  isNumeral x = ⋁ (Lift {ℓ-zero} {ℓ} ℕ) (λ n → x ≈ˢ numeral (lower n))

  field
    hasInfinity : isContr (SetOf isNumeral)

  ω : S
  ω = ℩ hasInfinity

```

<!--en-->
## First theorems

Extensionality upgrades the whole existence apparatus once and for all. Any
realizer is the unique realizer.
<!--zh-->
## 最初的定理

外延公理把整套存在机制一次性升级；由此，任何实现者都是唯一实现者。
<!--ja-->
## 最初の定理

空集合の一意性や自己所属の否定など、モデル record からただちに使える集合論の基本定理を導きます。これらは後の具体的モデルでも同じ名前で利用されます。
<!--/-->



<!--en-->
## ZFC: choice as an extension

The distinction between ZF and ZFC is drawn as a record boundary: the constructible-universe chapters
construct, inside any model of ZF, a sub-universe satisfying choice, and adding
choice to the base record would make inexpressible the very distinction that
construction is about. The **axiom of choice** is taken in choice-set form: given
a set `a` whose members are nonempty and pairwise disjoint, some set meets each
member of `a` in exactly one point. This form is stated with membership and the
derived intersection alone; its equivalence with the other formulations is
model-internal mathematics, deferred until needed. Note that the hypotheses and
the conclusion all carry the truncation `∥_∥₁`{.Agda}: choice asserts that a choice set
exists, but specifies no canonical one.
<!--zh-->
## ZFC：作为扩展的选择公理

ZF 与 ZFC 的区别对应 record 的边界，因为可构造宇宙诸章将在任意 ZF 模型内部构造一个满足选择公理的子宇宙。若把选择公理加入基础 record，就无法表达这个构造所研究的区别。这里采用选择集形式的**选择公理**：给定集合 `a`，若其成员非空且两两不交，则存在一个集合，与 `a` 的每个成员恰交于一点。该形式只用成员关系和派生的交即可陈述；它与其他形式的等价性属于模型内部的数学，留待需要时证明。各前提与结论都带有截断 `∥_∥₁`{.Agda}：选择公理断言选择集存在，但不指定典范的选择集。
<!--ja-->
## ZFC：選択公理による拡張

`isZFCModel`{.Agda} は ZF モデルに、空でない集合族から選択関数を与えるフィールドを加えます。選択を独立した拡張にすることで、ZF までの証明に不要な仮定を混ぜません。
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

A model of ZF is a record: extensionality, meta-level regularity (the compactness
ceiling rules out any other faithful placement), unique-existence fields for the
constructions, separation and replacement using the book's own formulas, and
strong infinity through the numeral chain. `℩` turns fields into operations whose
specifications are projections; intersection was obtained from separation and a
two-symbol formula, the first set the framework derives in its own language.
`isZFCModel`{.Agda} adds choice on top. Later coding chapters satisfy the record's
requirement on formulas by representing syntax and satisfaction inside `L`; the
Lévy witnesses developed here control the bounded formulas used along the way.
<!--zh-->
## 小结

ZF 模型是一个 record：包含外延公理、置于元层面的正则公理 (紧致性限制说明其他位置不能忠实表达预期含义)、以唯一存在形式陈述的构造字段、使用本书公式的分离与替换，以及由数码链给出的强无穷公理。`℩` 把构造字段转为运算，其规格都是投影。交由分离和一条双符号公式构造，是框架首次用自身语言得到集合。`isZFCModel`{.Agda} 在此基础上添加选择公理。后续编码诸章在 `L` 内表示语法与满足关系，以满足 record 对公式的要求；这里建立的 Lévy 见证则控制其中使用的有界公式。
<!--ja-->
## まとめ

ZF モデルは公理の証拠を record として持ち、確定記述から通常の集合演算と仕様定理を得ます。ZFC は同じ構造に選択公理の証拠だけを追加したものです。
<!--/-->
