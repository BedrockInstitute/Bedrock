# Prelude

<!--en-->
Every chapter of this book is literate Agda: the prose and the machine-checked code
it explains live in the same file, commentary first, code right after. This opening
chapter sets the table. It first lays down one discipline that fixes how the book
is read (every name is traceable to its source), then re-exports, from the cubical
library, the small host-language vocabulary the whole development stands on.
Nothing is proved here; skim it now, and return when a symbol looks unfamiliar.
<!--zh-->
本书的每一章都是文学化 Agda：解说的文稿与它所解说的经机器检查的代码同住一个文件，解说先行，代码紧随其后。这开篇一章负责摆桌子：先立下一条决定本书读法的纪律 (任何名字都可溯源)；再从 cubical 标准库转出全书立足的一小套宿主语言词汇。本章不证明任何东西；现在可以速览，之后遇到陌生符号再回来查。
<!--/-->

<!--en-->
## Traceable names
<!--zh-->
## 名字可溯源
<!--/-->

<!--en-->
One machine-enforced convention is stated up front, because it changes how the book
is read: **every import lists exactly the names it takes**. A chapter's import block
therefore doubles as its precise list of prerequisites, and "where does this name
come from" always has a visible answer on the page. The deliberate exception is the
book's two designated hubs, this chapter and the next: they are opened wholesale,
so a name not listed in any import comes from a hub.
<!--zh-->
有一条由机器执法的纪律须在开篇言明，因为它改变本书的读法：**每条 import 都精确列出所取的名字**。一章的 import 块因此兼作它的先修清单，「这个名字从哪来」在页面上总有答案。有意设置的例外是全书指定的两个枢纽，即本章与下一章：它们被整体打开，凡未见于任何 import 清单的名字都来自枢纽。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

module Base.Prelude where
```

<!--en-->
## The host vocabulary
<!--zh-->
## 宿主词汇
<!--/-->

<!--en-->
The re-exports follow, one import at a time; before each, what it brings and why
the book wants it.

The host organises its types into a tower of Tarski-style universes with explicit
levels. `Level`{.Agda} is the type of the levels themselves, with its arithmetic
`ℓ-zero`{.Agda}, `ℓ-suc`{.Agda}, `ℓ-max`{.Agda}; `Type`{.Agda}` ℓ` is the universe
at level `ℓ`, and it is itself a type one floor up, in `Type (ℓ-suc ℓ)`. Whenever
the book surveys a totality ("all sets", "all propositions"), this level bookkeeping
is what says how large a totality is being surveyed.
<!--zh-->
以下逐条转出，一段说明领一条 import：它带来什么，本书要它做什么。

宿主把类型组织成一座塔斯基式宇宙塔，层级显式。`Level`{.Agda} 是层级本身的类型，配有层级算术 `ℓ-zero`{.Agda}、`ℓ-suc`{.Agda}、`ℓ-max`{.Agda}；`Type`{.Agda}` ℓ` 是第 `ℓ` 层宇宙，它自身又是高一层的类型，住在 `Type (ℓ-suc ℓ)` 里。本书凡检视某个总体 (「所有集合」「所有命题」)，都由这套层级记账精确说明检视的总体有多大。
<!--/-->

```agda
open import Cubical.Foundations.Prelude public
  using ( Type; Level; ℓ-zero; ℓ-suc; ℓ-max )
```

<!--en-->
`_≡_`{.Agda} is the path type, the host's equality, and these are its everyday
tools: `refl`{.Agda} (reflexivity), `sym`{.Agda} (symmetry), `_∙_`{.Agda}
(composition of paths), `cong`{.Agda} and `cong₂`{.Agda} (every function respects
equality), `transport`{.Agda} and `subst`{.Agda} (carrying an inhabitant along a
path), and `funExt`{.Agda} (pointwise equal functions are equal).
<!--zh-->
`_≡_`{.Agda} 是路径类型，即宿主的相等，随行的是它的日常工具：`refl`{.Agda} (自反)、`sym`{.Agda} (对称)、`_∙_`{.Agda} (路径复合)、`cong`{.Agda} 与 `cong₂`{.Agda} (任何函数都尊重相等)、`transport`{.Agda} 与 `subst`{.Agda} (沿路径搬运居民)，以及 `funExt`{.Agda} (逐点相等的函数相等)。
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
**unique existence**, a load-bearing choice explained in the Charter.
<!--zh-->
h-层级谓词按「相等结构的多少」为类型分级：`isProp`{.Agda} (任意两个居民相等)、`isSet`{.Agda} (相等本身是命题)、`isContr`{.Agda} (恰有一个居民，在路径意义下)，以及把它们串起来的 `isProp→isSet`{.Agda}。`isContr`{.Agda} 就是本书表述**唯一存在**的方式，这一承重决策在纲领中有完整论述。
<!--/-->

```agda
open import Cubical.Foundations.Prelude public
  using ( isProp; isSet; isContr; isProp→isSet )
```

<!--en-->
`Lift`{.Agda} moves a type to a higher universe level, with `lift`{.Agda} and
`lower`{.Agda} converting back and forth: the standard patch when something lives
one floor too low.
<!--zh-->
`Lift`{.Agda} 把一个类型抬到更高的宇宙层级，`lift`{.Agda} 与 `lower`{.Agda} 负责来回转换：当某个东西住得低了一层，这就是标准补丁。
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
`hProp`{.Agda} 把一个类型与其命题性证明打包：它就是本书经典侧的真值类型。随行的两条事实值得说清。`isSetHProp`{.Agda} 说的是 `hProp`{.Agda} 自身是**集合**：由 univalence，两个命题之间的路径就是它们之间的双向蕴含，而双向蕴含本身是命题，所以命题之间的相等除真假之外不携带任何额外结构。正是这条事实使 `hProp`{.Agda} 有资格在下一章充当真值类型 (`isSetΩ` 字段要求的恰是它)。`isPropΠ`{.Agda} 说的是命题在 **Π 类型下封闭**：若对每个 `x`，`B x` 都是命题，则 `(x : A) → B x` 也是命题。这就是全称量化的真值仍是真值的原因。
<!--/-->

```agda
open import Cubical.Foundations.HLevels public
  using ( hProp; isSetHProp; isPropΠ )
```

<!--en-->
`⟨_⟩`{.Agda} (read "the underlying type of") projects the underlying type back out
of an `hProp`{.Agda}; for `P : hProp ℓ` the proposition-hood proof is just
`P .snd`, and the book gives it no separate name.
<!--zh-->
`⟨_⟩`{.Agda} (读作「延展」) 把底层类型从 `hProp`{.Agda} 中投影出来；对 `P : hProp ℓ`，其命题性证明就是 `P .snd`，本书不为它另设名字。
<!--/-->

```agda
open import Cubical.Foundations.Structure public
  using ( ⟨_⟩ )
```

<!--en-->
Dependent pairs: `Σ`{.Agda} with its `Σ-syntax`{.Agda} sugar, the plain product
`_×_`{.Agda}, the pairing `_,_`{.Agda}, and the projections `fst`{.Agda} and
`snd`{.Agda}. A Σ type is how the book bundles a thing with a property of it.
<!--zh-->
依值对：`Σ`{.Agda} 及其糖衣 `Σ-syntax`{.Agda}、普通的积 `_×_`{.Agda}、配对 `_,_`{.Agda}，以及投影 `fst`{.Agda} 与 `snd`{.Agda}。Σ 类型是本书「把东西与它的性质捆在一起」的方式。
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
Vectors: `Vec A n` is a list of exactly `n` elements of `A`, built with `[]`{.Agda}
and `_∷_`{.Agda} and queried with `lookup`{.Agda}. Vectors are the raw material of
variable environments, coming in Part 1.
<!--zh-->
向量：`Vec A n` 是恰含 `n` 个 `A` 元素的表，由 `[]`{.Agda} 与 `_∷_`{.Agda} 构造，用 `lookup`{.Agda} 查询。向量是变量环境的原材料，将在第一部登场。
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
`Fin n` 是恰有 `n` 个元素的类型；它将充当 `n` 元公式的变量类型。其构造子与自然数同名 `zero`{.Agda}、`suc`{.Agda}，由类型检查器消歧。
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
最后是层级多态的空类型 `⊥*`{.Agda}，连同 `isProp⊥*`{.Agda}。注意星号：这是宿主层的**类型**，层级随需而定，不是下一章的真值 `⊥`。
<!--/-->

```agda
open import Cubical.Data.Empty public
  using ( ⊥*; isProp⊥* )
```

<!--en-->
## Recap
<!--zh-->
## 小结
<!--/-->

<!--en-->
In scope from here on: universes, paths, h-levels, `hProp`{.Agda} with `⟨_⟩`{.Agda},
pairs, `ℕ`{.Agda}, `Vec`{.Agda}, `Fin`{.Agda}, and `⊥*`{.Agda}. This chapter defines
nothing of its own, and the logic symbols are deliberately absent: every notion of
the book is introduced in the chapter where it first earns its keep, and the logic
arrives with the truth algebra, next.
<!--zh-->
自此进入作用域的有：宇宙、路径、h-层级、`hProp`{.Agda} 与 `⟨_⟩`{.Agda}、对与积、`ℕ`{.Agda}、`Vec`{.Agda}、`Fin`{.Agda}，以及 `⊥*`{.Agda}。本章没有任何自己的定义，逻辑符号也刻意缺席：本书的每个概念都在它初次派上用场的章节引入，而逻辑随下一章的真值代数登场。
<!--/-->
