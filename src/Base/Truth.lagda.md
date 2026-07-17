# Truth values

<!--en-->
When a formula is evaluated, the result has to live somewhere: a type of truth
values. The usual answer is the type of propositions, `hProp`{.Agda}. But this
book is headed for forcing, where truth values live in a complete Boolean algebra
instead. So the answer is not hard-wired: the semantic codomain is a parameter,
called a **truth algebra**, and everything built over it serves both destinations.
<!--zh-->
公式求值的结果必须落脚在某处：一个真值类型。通常的答案是命题类型 `hProp`{.Agda}。但本书的目的地包括力迫，届时真值将改住完备布尔代数。所以这个答案不被焊死：语义值域是一个参数，称为**真值代数**，其上构建的一切同时服务两个目的地。
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
<!--zh-->
## 接口
<!--/-->

<!--en-->
The record below is a **pure operation signature**: it asks for eight operations
and not a single law about them (no associativity, no distributivity, no lattice
axioms). A law in an interface is a debt every instance must pay, and here nobody
would ever collect it: everything the framework core builds over `Ω` treats the
operations as black boxes, needing only congruence (equal inputs give equal
outputs: the `cong`{.Agda} of the Prelude), which holds for any operations
whatsoever. Laws are needed only by later theorems about particular models, and
those work at a concrete instance, where the laws are theorems rather than
assumptions. Staying law-free therefore costs nothing, and buys a cheap ticket of
admission: a semantics joins the book by handing over eight operations, owing no
proofs.
<!--zh-->
下面的 record 是**纯运算签名**：只索要八个运算，对它们不要求任何定律 (不要结合律、分配律，也不要任何格公理)。接口里的每条定律都是每个实例必须偿付的债务，而这里根本无人收账：框架核心在 `Ω` 上构建的一切都把这些运算当黑箱，只需要同余 (输入相等则输出相等，即序章的 `cong`{.Agda})，而同余对任意运算都成立。定律只有后面关于具体模型的定理才需要，而那些定理本来就在具体实例上进行，届时定律是实例上的定理而非接口上的假设。零定律因此毫无代价，换来的是廉价的入场券：一个语义要加入本书，交出八个运算即可，不欠任何证明。
<!--/-->

```agda
record TruthAlg (ℓ ℓ' : Level) : Type (ℓ-suc (ℓ-max ℓ ℓ')) where
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
across layers.

Here the book's **scope discipline for logic** is laid down: these eight symbols are
the book's only logic notation, and the Prelude deliberately exports none of them,
so the only way they enter scope is by opening a truth algebra
(`open TruthAlg 𝕋`). Whichever algebra a chapter opens, that is what its logic
symbols mean: no symbol ever has two readings in one scope. Generic chapters open an
abstract `𝕋`; chapters on the propositional side open the canonical instance below.
<!--zh-->
逐个符号：`⊓` 读「且」(交)，`⊔` 读「或」(并)，`⇒` 读「蕴含」，`¬` 读「非」，`⊤` 读「真」，`⊥` 读「假」；`⋀` 与其对偶 `⋁` 是按任意小类型索引的交与并，量词语义正由它们给出。这里的优先级刻意与之后引入的对象语言联结词同级，跨层的混合表达式因此读法一致。

本书**逻辑符号的作用域纪律**在此立下：这八个符号是全书仅有的逻辑记号，序章刻意不导出其中任何一个，于是它们进入作用域的唯一方式就是打开某个真值代数 (`open TruthAlg 𝕋`)。一章打开哪个代数，它的逻辑符号就是那个代数的运算：任一作用域中，没有符号会有两种读法。泛型章节打开抽象的 `𝕋`；命题侧的章节打开下面的典范实例。
<!--/-->

<!--en-->
## The canonical instance: hProp
<!--zh-->
## 典范实例：hProp
<!--/-->

<!--en-->
Propositions form a truth algebra. Everything in this sentence stands on univalence:
that `hProp`{.Agda} is a set, and that the operations below are well defined on it,
are theorems of the cubical library, not assumptions.
<!--zh-->
命题构成一个真值代数。这句话的全部内容都站在 univalence 上：`hProp`{.Agda} 是集合、下列运算在其上良定义，这些在 cubical 库里都是定理而非假设。
<!--/-->

```agda
hPropAlg : ∀ {ℓ} → TruthAlg ℓ (ℓ-suc ℓ)
hPropAlg {ℓ} = record
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
   instance, so `TruthAlg._⊓_ hPropAlg` **is** the library's `_⊓_`{.Agda},
   definitionally. Working at the hProp instance is exactly as if the abstraction
   had never happened: whatever held by `refl`{.Agda} before still holds by
   `refl`{.Agda}.
2. The `⊥` field takes the level-polymorphic pair `(⊥* , isProp⊥*)`, since the
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

1. **抽象零成本。**record 投影在具体实例上按定义计算，所以 `TruthAlg._⊓_ hPropAlg` 定义性地**就是**库的 `_⊓_`{.Agda}。在 hProp 实例上工作与从未抽象过完全一样：凡此前由 `refl`{.Agda} 成立的等式，如今照旧由 `refl`{.Agda} 成立。
2. `⊥` 字段取层级多态的对 `(⊥* , isProp⊥*)`，因为库的假固定在最底层宇宙。这也是两个符号之间的全部关系：真值 `⊥` 就是宿主类型 `⊥*`{.Agda} 连同其命题性打包而成，故 `⟨ ⊥ ⟩` **就是** `⊥*`{.Agda}。要真值的位置写 `⊥`，要类型的位置写 `⊥*`{.Agda}；两个位置不可互换，分工由类型检查器把守。
3. `⋁` 是命题截断的存在量词，`⋀` 是货真价实的 Π 类型：这正是构造性语义的形态。hProp 侧的章节仍可直接从库中取用证明手段 (`∃[ x ] …` 糖衣、截断消去子)：它们与本实例的字段定义性相同，不构成第二套含义。
<!--/-->

<!--en-->
## A seat reserved for forcing
<!--zh-->
## 为力迫预留的席位
<!--/-->

<!--en-->
The forcing part of this book will provide the second instance: the regular-open
Boolean completion of a forcing poset, with `Ω` a complete Boolean algebra. The
record above will carry it unchanged, and the symbol family `∈ᴮ ≈ᴮ` is already
reserved for that day.
<!--zh-->
本书的力迫部分将给出第二个实例：力迫偏序的正则开代数布尔完备化，`Ω` 是完备布尔代数。上面的 record 届时原样承接，符号族 `∈ᴮ ≈ᴮ` 已为那一天预留。
<!--/-->

<!--en-->
## Recap
<!--zh-->
## 小结
<!--/-->

<!--en-->
Truth values are a parameter: the operation-only record `TruthAlg`{.Agda}, whose
eight symbols are the book's entire logic notation, with `hPropAlg`{.Agda} as the
canonical, definitionally transparent instance. Next: the one classical principle
this book ever appeals to, stated as an interface.
<!--zh-->
真值是一个参数：只含运算的 record `TruthAlg`{.Agda}，其八个符号就是全书的全部逻辑记号；`hPropAlg`{.Agda} 是典范且定义性透明的实例。下一章：本书唯一诉诸的经典原理，以接口的形式陈述。
<!--/-->
