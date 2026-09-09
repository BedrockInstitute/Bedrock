<!--en-->
# Prelude

This chapter gathers the host-language notions needed to read every later theorem statement: universes, paths, h-levels, propositions, pairs, natural-number indices, and the empty type. It also explains why proof-specific operations remain in the chapters that first need them.
<!--zh-->
# 基础词汇

本章汇集读懂后续定理陈述所需的宿主语言概念：宇宙、路径、h-层级、命题、序对、自然数指标与空类型。它也说明，证明专用的运算为何留在首次需要它们的章节中。
<!--ja-->
# 基礎語彙

本章では、後の定理の主張を読むために必要なホスト言語の概念、宇宙、道、h-レベル、命題、対、自然数の添字、空型をまとめます。また、証明だけに使う演算を、それが最初に必要となる章に置く理由も説明します。
<!--/-->

<!--en-->
Every chapter of this book is literate Agda: the prose and the machine-checked code
it explains live in the same file, commentary first, code right after. As the opening
chapter, this chapter first states one discipline that fixes how the book
is read (every name is traceable to its source), then re-exports, from the cubical
library, the small host-language vocabulary on which the whole development depends.
Nothing is proved here; skim it now, and return whenever a symbol looks unfamiliar.
<!--zh-->
本书的每一章都是文学化 Agda：解说的文稿与经机器检查的代码位于同一文件，解说在前，代码紧随其后。作为开篇，本章先说明一条决定全书读法的纪律 (任何名字都可溯源)，再从 cubical 标准库公开引入全书依赖的一小套宿主语言词汇。本章不证明任何东西；现在可以速览，之后遇到陌生符号再回来查阅。
<!--/-->



<!--en-->
## Traceable names

One machine-enforced convention is stated up front, because it changes how the book
is read: **every import lists exactly the names it takes**. A chapter's import block
therefore doubles as its precise list of prerequisites, and "where does this name
come from" always has a visible answer on the page. This chapter and the next are
the only two exceptions in the book: they are opened wholesale, so a name not
listed in any import comes from one of these two chapters.
<!--zh-->
## 名字可溯源

有一条由机器强制执行的纪律须在开篇言明，因为它改变本书的读法：**每条 import 都精确列出所取的名字**。一章的 import 块因此兼作它的先修清单，「这个名字从哪来」在页面上总有答案。本章与下一章是全书仅有的两个例外：它们被整体导入，凡未见于任何 import 清单的名字都来自这两章。
<!--ja-->
## 名前を追跡できるようにする

各 import は受け取る名前を明示するので、import 欄がその章の正確な前提一覧になります。例外は二つの共通ハブである本章と次章で、ここからの名前だけはまとめて開かれます。
<!--/-->



```agda
{-# OPTIONS --cubical --safe --guardedness #-}

module Base.Prelude where
```

<!--en-->
## The host vocabulary

The re-exports follow, one import at a time; each is preceded by an explanation of
what it brings and how the book uses it.
<!--zh-->
## 宿主词汇

以下逐条引入，一段说明对应一条 import：它带来什么，本书用它做什么。
<!--ja-->
## ホスト言語の語彙

`Type`、道の等式、`isProp`、`isSet`、`hProp`、Σ 型、自然数と有限添字を公開します。これらは集合論の対象言語ではなく、その構文とモデルを記述するホスト言語の語彙です。
<!--/-->

<!--en-->
The host organises its types into a tower of Tarski-style universes with explicit
levels. `Level`{.Agda} is the type of the levels themselves, with its arithmetic
`ℓ-zero`{.Agda}, `ℓ-suc`{.Agda}, `ℓ-max`{.Agda}; `Type ℓ`{.Agda} is the universe
at level `ℓ`, and it is itself a type at the next level up, in `Type (ℓ-suc ℓ)`{.Agda}. Whenever
the book surveys a totality ("all sets", "all propositions"), these levels are what
specify how large a totality is being surveyed.
<!--zh-->
宿主把类型组织成一座层级显式的塔斯基式宇宙塔。`Level`{.Agda} 是层级本身的类型，配有层级算术 `ℓ-zero`{.Agda}、`ℓ-suc`{.Agda}、`ℓ-max`{.Agda}；`Type ℓ`{.Agda} 是第 `ℓ` 层宇宙，它自身又属于高一层的 `Type (ℓ-suc ℓ)`{.Agda}。本书凡检视某个总体 (「所有集合」「所有命题」)，都由这套层级精确说明该总体有多大。
<!--/-->

```agda
open import Cubical.Foundations.Prelude public
  using ( Type; Level; ℓ-zero; ℓ-suc; ℓ-max )
```

<!--en-->
`_≡_`{.Agda} is the path type, the host's equality, and it comes with the following
standard tools: `refl`{.Agda} (reflexivity), `sym`{.Agda} (symmetry), `_∙_`{.Agda}
(composition of paths), `cong`{.Agda} and `cong₂`{.Agda} (every function respects
equality), `transport`{.Agda} and `subst`{.Agda} (carrying an inhabitant along a
path), and `funExt`{.Agda} (pointwise equal functions are equal).
<!--zh-->
`_≡_`{.Agda} 是路径类型，即宿主的相等，配有以下常用工具：`refl`{.Agda} (自反)、`sym`{.Agda} (对称)、`_∙_`{.Agda} (路径复合)、`cong`{.Agda} 与 `cong₂`{.Agda} (任何函数都尊重相等)、`transport`{.Agda} 与 `subst`{.Agda} (沿路径搬移元素)，以及 `funExt`{.Agda} (逐点相等的函数相等)。
<!--/-->

```agda
open import Cubical.Foundations.Prelude public
  using ( _≡_; refl; sym; _∙_; cong; cong₂; transport; subst; funExt )
```

<!--en-->
The h-level predicates grade a type by how much equality structure it carries:
`isProp`{.Agda} (any two inhabitants are equal), `isSet`{.Agda} (equality itself is
a proposition), `isContr`{.Agda} (exactly one inhabitant, up to a path), and
`isProp→isSet`{.Agda} connecting them. `isContr`{.Agda} is how this book says
**unique existence**, following the convention explained in the Charter.
<!--zh-->
h-层级谓词按「相等结构的多少」为类型分级：`isProp`{.Agda} (任意两个元素相等)、`isSet`{.Agda} (相等本身是命题)、`isContr`{.Agda} (在路径意义下恰有一个元素)；`isProp→isSet`{.Agda} 说明命题也是集合。`isContr`{.Agda} 就是本书表述**唯一存在**的方式，这一关键决策在纲领中有完整论述。
<!--/-->

```agda
open import Cubical.Foundations.Prelude public
  using ( isProp; isSet; isContr; isProp→isSet )
```

<!--en-->
`Lift`{.Agda} makes a copy of a type at a higher universe level: the standard remedy
when a type sits at a level lower than required. `lift`{.Agda} and `lower`{.Agda} move
**elements** between the type and its copy, and are mutually inverse; the asymmetry
appears at the level of types: a type can always be copied upward, but there is in
general no way to move one down. (The exception is propositions: the classical
boundary chapter will show that excluded middle provides exactly the downward
direction.)
<!--zh-->
`Lift`{.Agda} 把一个类型复制到更高的宇宙层级：当某个类型所处的层级低于需要时，这是标准的补救办法。`lift`{.Agda} 与 `lower`{.Agda} 在原类型与其副本之间搬运**元素**，两者互逆；不对称出现在类型层面：类型总能向上复制，却一般无法向下搬移。(例外是命题：经典边界一章将看到，排中律恰好提供这个向下方向。)
<!--/-->

```agda
open import Cubical.Foundations.Prelude public
  using ( Lift; lift; lower )
```

<!--en-->
`hProp`{.Agda} packages a type with a proof that it is a proposition: the type of
truth values on the classical side of this book. The two accompanying facts deserve
spelling out. `isSetHProp`{.Agda} says that `hProp`{.Agda} is itself a **set**: by
univalence, a path between two propositions is the same thing as a bi-implication
between them, and that is itself a proposition, so equality of propositions carries
no structure beyond truth. This is the fact that qualifies `hProp`{.Agda} as a type
of truth values in the next chapter (the `isSetΩ` field will demand exactly it).
`isPropΠ`{.Agda} says that propositions are **closed under Π types**: if `B x` is a
proposition for every `x`, then `(x : A) → B x` is one too. It is the reason a
universally quantified truth value is again a truth value.
<!--zh-->
`hProp`{.Agda} 由一个类型及其命题性证明组成，是本书经典侧的真值类型。这里引入的两条事实说明它为何适用。`isSetHProp`{.Agda} 证明 `hProp`{.Agda} 自身是**集合**：由 univalence，两个命题之间的路径等同于它们之间的双向蕴含，而双向蕴含本身是命题，所以命题之间的相等除真假之外不携带额外结构。下一章以 `hProp`{.Agda} 作为真值类型时，`isSetΩ` 字段要求的正是这一事实。`isPropΠ`{.Agda} 说明命题在 **Π 类型下封闭**：若对每个 `x`，`B x` 都是命题，则 `(x : A) → B x` 也是命题。因此，全称量化的真值仍是真值。
<!--/-->

```agda
open import Cubical.Foundations.HLevels public
  using ( hProp; isSetHProp; isPropΠ )
```

<!--en-->
`⟨_⟩`{.Agda} (read "the underlying type of") projects the underlying type back out
of an `hProp`{.Agda}; for `P : hProp ℓ`{.Agda} the proposition-hood proof is just
`P .snd`{.Agda}, and the book gives it no separate name.
<!--zh-->
`⟨_⟩`{.Agda} (读作「延展」) 把底层类型从 `hProp`{.Agda} 中投影出来；对 `P : hProp ℓ`{.Agda}，其命题性证明就是 `P .snd`{.Agda}，本书不为它另设名字。
<!--/-->

```agda
open import Cubical.Foundations.Structure public
  using ( ⟨_⟩ )
```

<!--en-->
The chapter also introduces one derived notation. A **class** over a carrier `A` is a
propositional predicate `A → hProp ℓ`, and `x ∈ᶜ M` (read "x belongs to the
class M") is exactly `⟨ M x ⟩`: the library's powerset membership under a marked
name. The superscript `ᶜ` marks *class*, keeping the notation apart from the
object-level memberships to come, which denote sets rather than host-level
predicates.
<!--zh-->
此外还有一个派生记号。载体 `A` 上的**类**是命题值谓词 `A → hProp ℓ`，而 `x ∈ᶜ M` (读作「x 属于类 M」) 恰是 `⟨ M x ⟩`：即库的幂集成员关系，只是换用一个带标记的名字。上标 `ᶜ` 标示**类**，用以把这个记号与后文的诸对象层成员关系区分开，后者指称集合，而非宿主层的谓词。
<!--/-->

```agda
open import Cubical.Foundations.Powerset public
  using () renaming ( _∈_ to _∈ᶜ_ )
```

<!--en-->
Dependent pairs: `Σ`{.Agda} with its `Σ-syntax`{.Agda} sugar, the plain product
`_×_`{.Agda}, the pairing `_,_`{.Agda}, and the projections `fst`{.Agda} and
`snd`{.Agda}. A Σ type pairs an object with data that depends on that object.
<!--zh-->
依值对包括 `Σ`{.Agda} 及其便捷记法 `Σ-syntax`{.Agda}，此外还有普通的积 `_×_`{.Agda}、配对 `_,_`{.Agda}，以及投影 `fst`{.Agda} 与 `snd`{.Agda}。Σ 类型用于把一个对象与依赖于该对象的数据组成一对。
<!--/-->

```agda
open import Cubical.Data.Sigma public
  using ( Σ; Σ-syntax; _×_; _,_; fst; snd )
```

<!--en-->
The natural numbers `ℕ`{.Agda}, with `zero`{.Agda} and `suc`{.Agda}. They index
everything finite, first of all the number of free variables of a formula.
<!--zh-->
自然数 `ℕ`{.Agda}，构造子 `zero`{.Agda} 与 `suc`{.Agda}。一切有限事物都由它们索引，首先就是公式的自由变量个数。
<!--/-->

```agda
open import Cubical.Data.Nat public
  using ( ℕ; zero; suc )
```

<!--en-->
Vectors: `Vec A n`{.Agda} is a list of exactly `n` elements of `A`, built with `[]`{.Agda}
and `_∷_`{.Agda} and queried with `lookup`{.Agda}. Vectors are the basic material for
variable environments and appear in the first-order logic chapters.
<!--zh-->
向量：`Vec A n`{.Agda} 是恰含 `n` 个 `A` 元素的表，由 `[]`{.Agda} 与 `_∷_`{.Agda} 构造，用 `lookup`{.Agda} 查询。向量是构造变量环境的基本材料，将在一阶逻辑各章中使用。
<!--/-->

```agda
open import Cubical.Data.Vec public
  using ( Vec; []; _∷_; lookup )
```

<!--en-->
`Fin n` is the type with exactly `n` elements; it will serve as the type of
variables of an `n`-variable formula. Its constructors overload `zero`{.Agda} and
`suc`{.Agda}, and the type checker disambiguates.
<!--zh-->
`Fin n` 是恰有 `n` 个元素的类型；它将充当 `n` 元公式的变量类型。其构造子与自然数同名，即 `zero`{.Agda}、`suc`{.Agda}，由类型检查器消歧。
<!--/-->

```agda
open import Cubical.Data.FinData public
  using ( Fin; zero; suc )
```

<!--en-->
Finally, the level-polymorphic empty type `⊥*`{.Agda}, with `isProp⊥*`{.Agda}. Note
the star: this is a host-layer **type**, at whatever level is needed, not the truth
value `⊥` of the next chapter.
<!--zh-->
最后是层级多态的空类型 `⊥*`{.Agda}，连同 `isProp⊥*`{.Agda}。注意星号：这是宿主层的**类型**，其层级可以按需要选择，不是下一章的真值 `⊥`。
<!--/-->

```agda
open import Cubical.Data.Empty public
  using ( ⊥*; isProp⊥* )
```

<!--en-->
The only function defined in this chapter is the smallest one imaginable: the
level-polymorphic identity function. It serves as the book's canonical
constant interpretation: a constant standing for the very set it names is
precisely `id`{.Agda}.
<!--zh-->
本章定义的唯一一个函数是层级多态的恒等函数 `id`{.Agda}。它用作本书的典范常元解释：将常元解释为该常元所指名的集合。
<!--/-->

```agda
id : ∀ {ℓ} {A : Type ℓ} → A → A
id x = x
```

<!--en-->
## Recap

In scope from here on: universes, paths, h-levels, `hProp`{.Agda} with `⟨_⟩`{.Agda}
and the class membership `∈ᶜ`{.Agda}, pairs, `ℕ`{.Agda}, `Vec`{.Agda}, `Fin`{.Agda},
`⊥*`{.Agda}, and the identity `id`{.Agda}. This chapter proves nothing, defines
only `id`{.Agda}, and introduces no logic symbols: every notion of
the book is introduced in the chapter where it is first needed, and the logic
arrives with the truth algebra, next.
<!--zh-->
## 小结

自此进入作用域的有：宇宙、路径、h-层级、`hProp`{.Agda} 与 `⟨_⟩`{.Agda} 及类隶属 `∈ᶜ`{.Agda}、对与积、`ℕ`{.Agda}、`Vec`{.Agda}、`Fin`{.Agda}、`⊥*`{.Agda}，以及恒等 `id`{.Agda}。本章不证明任何东西，定义的只有 `id`{.Agda}，也没有引入逻辑符号：每个概念都在首次需要它的章节引入，逻辑符号将在下一章随真值代数一同引入。
<!--ja-->
## まとめ

以後は、宇宙、パス、h-レベル、`hProp`{.Agda} と `⟨_⟩`{.Agda}、クラス所属 `∈ᶜ`{.Agda}、積、`ℕ`{.Agda}、`Vec`{.Agda}、`Fin`{.Agda}、`⊥*`{.Agda}、恒等写像 `id`{.Agda} を共通語彙として使います。本章で定義したのは `id`{.Agda} だけで、論理記号は次章の真理値代数とともに導入されます。
<!--/-->
