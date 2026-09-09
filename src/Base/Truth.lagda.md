<!--en-->
# Truth values

First-order semantics needs a type of truth values together with operations for connectives and quantifiers. This chapter records exactly that data in `TruthAlgebra`{.Agda}, then supplies the canonical instance whose truth values are propositions.
<!--zh-->
# 真值

一阶语义需要一个真值类型，以及解释联结词与量词的运算。本章用 `TruthAlgebra`{.Agda} 准确记录这些数据，再给出以命题为真值的典范实例。
<!--ja-->
# 真理値

一階意味論には、真理値の型と、結合子および量化子を解釈する演算が必要です。本章ではそのデータを `TruthAlgebra`{.Agda} に記録し、命題を真理値とする正準な実例を与えます。
<!--/-->

<!--en-->
When a formula is evaluated, the result must land in a type of truth
values. The book proceeds in two directions that require different answers. In
the part leading to the constructible universe, propositions
(`hProp`{.Agda}) serve as truth values; in the forcing part, truth values are
taken from a complete Boolean algebra instead. The choice is therefore left
open: the semantic codomain is a parameter, called a **truth algebra**, and
everything built over such a structure serves both parts.
<!--zh-->
公式求值的结果要落在一个真值类型上。本书后续两个方向对答案的要求不同：通往可构造宇宙的部分，以命题 (`hProp`{.Agda}) 作真值即可；力迫部分则要求真值取自完备布尔代数。因此这一选择不固定：语义值域是一个参数，称为**真值代数**，在这类结构上建立的一切结果对两种情形通用。
<!--/-->



```agda
{-# OPTIONS --cubical --safe --guardedness #-}

module Base.Truth where

open import Base.Prelude
import Cubical.Functions.Logic as Logic
  using ( _⊓_; _⊔_; _⇒_; ¬_; ⊤; ∃[]-syntax; ∀[]-syntax )
```

<!--en-->
## The interface

The record below is a **pure operation signature**: it specifies eight operations
and requires no laws about them (no associativity, no distributivity, no lattice
axioms). A law placed in an interface would have to be proved separately by
every instance; meanwhile, everything the framework core builds over `Ω`
treats the operations as black boxes, needing only congruence (equal inputs give
equal outputs: the `cong`{.Agda} of the Prelude), which holds for any operations
whatsoever. Laws are needed only by later theorems about particular models, and
those are proved at a concrete instance, where the laws are theorems of the
instance rather than assumptions of the interface. Leaving out laws therefore
costs nothing: a semantics joins the book by providing eight operations, with no
proofs required.
<!--zh-->
## 接口

下面的 record 是**纯运算签名**：只规定八个运算，不要求它们满足任何定律 (不要结合律、分配律，也不要任何格公理)。定律若进入接口，每个实例都得另行证明；而框架核心在 `Ω` 上构建的一切都把这些运算当作黑箱，只用到同余 (输入相等则输出相等，即序章的 `cong`{.Agda})，同余对任意运算都成立。定律只有后面关于具体模型的定理才需要，而那些定理本来就在具体实例上证明，届时定律是实例上的定理而非接口上的假设。因此不带定律毫无代价：一个语义要加入本书，只需给出八个运算，不必附带任何证明。
<!--ja-->
## インターフェース

`TruthAlgebra`{.Agda} は、真理値型 `Ω`、二項結合子、否定、真偽、有界な添字型上の積と和を指定します。意味論に不要な代数法則は仮定しません。
<!--/-->



```agda
record TruthAlgebra (ℓ ℓ' : Level) : Type (ℓ-suc (ℓ-max ℓ ℓ')) where
  field
    Ω      : Type ℓ'
    isSetΩ : isSet Ω
    _⊓_ _⊔_ _⇒_ : Ω → Ω → Ω
    ¬_     : Ω → Ω
    ⊤ ⊥    : Ω
    ⋀ ⋁    : (A : Type ℓ) → (A → Ω) → Ω

  infixr 12 _⊓_ _⊔_
  infixr 10 _⇒_
  infix  13 ¬_
```

<!--en-->
Symbol by symbol: `⊓` reads "and" (meet), `⊔` reads "or" (join), `⇒` reads
"implies", `¬` reads "not", `⊤` reads "true", `⊥` reads "false"; `⋀` and its dual
`⋁` are meet and join indexed by an arbitrary small type, and quantifier semantics
will be given by exactly them. The fixity levels here deliberately match
the object-language connectives introduced later, so mixed expressions read the same
across layers. Object negation and truth are later derived from implication and
falsity; the independent fields here remain the metalanguage operations.

Here the book lays down its **scope discipline for logical symbols**: these eight symbols are
the book's only logic notation, and the Prelude deliberately exports none of them,
so the only way they enter scope is by opening a truth algebra
(`open TruthAlgebra 𝕋`{.Agda}). Whichever algebra a chapter opens, that is what its logic
symbols mean: no symbol ever has two readings in one scope. Generic chapters open an
abstract `𝕋`; chapters on the propositional side open the canonical instance below.
<!--zh-->
逐个符号：`⊓` 读「且」(交)，`⊔` 读「或」(并)，`⇒` 读「蕴含」，`¬` 读「非」，`⊤` 读「真」，`⊥` 读「假」；`⋀` 与其对偶 `⋁` 是按任意小类型索引的交与并，量词语义正由它们给出。这里的优先级刻意与之后引入的对象语言联结词同级，跨层的混合表达式因此读法一致。对象语言的否定与真随后由蕴涵和假派生；这里的独立字段仍是元语言运算。

本书在此立下**逻辑符号的作用域规则**：这八个符号是全书仅有的逻辑记号，序章刻意不导出其中任何一个，于是它们进入作用域的唯一方式就是打开某个真值代数 (`open TruthAlgebra 𝕋`{.Agda})。一章打开哪个代数，它的逻辑符号就是那个代数的运算：任一作用域中，没有符号会有两种读法。泛型章节打开抽象的 `𝕋`；命题侧的章节打开下面的典范实例。
<!--/-->

<!--en-->
## The canonical instance: hProp

Propositions form a truth algebra. Everything in this sentence stands on univalence:
that `hProp`{.Agda} is a set, and that the operations below are well defined on it,
are theorems of the cubical library, not assumptions.
<!--zh-->
## 典范实例：hProp

命题构成一个真值代数。这一事实以 univalence 为依据：`hProp`{.Agda} 是集合，下列运算在其上良定义；这些在 cubical 库中都是定理而非假设。
<!--ja-->
## 正準な実例：hProp

命題 `hProp`{.Agda} は正準な真理値代数になります。論理結合子は命題の演算で解釈され、全称量化は Π 型、存在量化は命題的切り詰めを施した Σ 型で解釈されます。
<!--/-->



```agda
hPropAlgebra : ∀ ℓ → TruthAlgebra ℓ (ℓ-suc ℓ)
hPropAlgebra ℓ = record
  { Ω      = hProp ℓ
  ; isSetΩ = isSetHProp
  ; _⊓_    = Logic._⊓_
  ; _⊔_    = Logic._⊔_
  ; _⇒_    = Logic._⇒_
  ; ¬_     = Logic.¬_
  ; ⊤      = Logic.⊤
  ; ⊥      = ⊥* , isProp⊥*
  ; ⋀      = λ A P → Logic.∀[]-syntax P
  ; ⋁      = λ A P → Logic.∃[]-syntax P }
```

<!--en-->
Three points worth keeping:

1. **The abstraction costs nothing.** Record projections compute on a concrete
   instance, so `TruthAlgebra._⊓_ (hPropAlgebra ℓ)`{.Agda} **is** the library's `_⊓_`{.Agda},
   definitionally. Working at the hProp instance is exactly as if the abstraction
   had never happened: whatever held by `refl`{.Agda} before still holds by
   `refl`{.Agda}.
2. The `⊥` field takes the level-polymorphic pair `(⊥* , isProp⊥*)`{.Agda}, since the
   library's falsum is pinned to the bottom universe. This is also the whole
   relationship between the two symbols: the truth value `⊥` is the host type
   `⊥*`{.Agda} packaged with its propositionality, so `⟨ ⊥ ⟩` **is** `⊥*`{.Agda}.
   Write `⊥` where a truth value is expected and `⊥*`{.Agda} where a type is
   expected; the two positions are not interchangeable, and the type checker
   polices the division.
3. `⋁` is the propositionally truncated existential and `⋀` is a genuine Π type:
   the shape of constructive semantics. Chapters on the hProp side may still take
   proof devices (`∃[ x ] …` sugar, truncation eliminators) straight from the
   library; they are definitionally the same operations, not a second meaning.
<!--zh-->
三个值得记住的要点：

1. **抽象零成本。**record 投影在具体实例上按定义计算，所以 `TruthAlgebra._⊓_ (hPropAlgebra ℓ)`{.Agda} 定义性地**就是**库的 `_⊓_`{.Agda}。在 hProp 实例上工作与从未抽象过完全一样：凡此前由 `refl`{.Agda} 成立的等式，如今照旧由 `refl`{.Agda} 成立。
2. `⊥` 字段取层级多态的对 `(⊥* , isProp⊥*)`{.Agda}，因为库的假固定在最底层宇宙。这也是两个符号之间的全部关系：真值 `⊥` 就是宿主类型 `⊥*`{.Agda} 连同其命题性一起构成的，故 `⟨ ⊥ ⟩` **就是** `⊥*`{.Agda}。要真值的位置写 `⊥`，要类型的位置写 `⊥*`{.Agda}；两个位置不可互换，由类型检查器负责区分。
3. `⋁` 是命题截断的存在量词，`⋀` 就是真正的 Π 类型：这正是构造性语义的形态。hProp 侧的章节仍可直接从库中取用证明手段 (`∃[ x ] …` 糖衣、截断消去子)：它们与本实例的字段定义性相同，不构成第二套含义。
<!--/-->

<!--en-->
## A seat reserved for forcing

The forcing part of this book will provide the second instance: the regular-open
Boolean completion of a forcing poset, with `Ω` a complete Boolean algebra. The
record above will carry it unchanged, and the symbol family `∈ᴮ ≈ᴮ` is already
reserved for that instance.
<!--zh-->
## 为力迫预留的席位

本书的力迫部分将给出第二个实例：力迫偏序的正则开代数布尔完备化，其中 `Ω` 是完备布尔代数。上面的 record 届时原样沿用，符号族 `∈ᴮ ≈ᴮ` 正是为该实例准备的。
<!--ja-->
## 強制法のための余地

意味論は抽象的な `TruthAlgebra`{.Agda} だけに依存します。そのため、後の強制法では真理値を完備ブール代数に替えても、同じ構文と意味論を再利用できます。
<!--/-->



<!--en-->
## Recap

Truth values are a parameter: the operation-only record `TruthAlgebra`{.Agda}, whose
eight symbols are the book's entire logic notation, with `hPropAlgebra`{.Agda} as the
canonical, definitionally transparent instance. Next: the size vocabulary of
impredicativity, and then the one classical principle that redeems it.
<!--zh-->
## 小结

真值是一个参数：只含运算的 record `TruthAlgebra`{.Agda}，其八个符号就是全书的全部逻辑记号；`hPropAlgebra`{.Agda} 是典范且定义性透明的实例。接下来是非直谓性的尺寸词汇，以及随后处理它的那一条经典原理。
<!--ja-->
## まとめ

`TruthAlgebra`{.Agda} は論理式の意味に必要な演算だけを抽象化します。`hPropAlgebra`{.Agda} は通常の命題値意味論を与え、同じインターフェースが後の別の真理値にも対応します。
<!--/-->
