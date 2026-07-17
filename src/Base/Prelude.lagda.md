# Prelude

<!--en-->
Every chapter of this book is literate Agda: the prose you are reading and the
machine-checked code live in the same file. This opening chapter sets the table.
It first lays down two disciplines governing how names come into scope, then
re-exports, from the cubical library, the small host-language vocabulary the whole
development stands on. Nothing is proved here; skim it now, and return when a
symbol looks unfamiliar.
<!--zh-->
本书的每一章都是文学化 Agda：你正在读的文稿与经机器检查的代码同住一个文件。这开篇一章负责摆桌子：先立下两条纪律，约束名字如何进入作用域；再从 cubical 标准库转出全书立足的一小套宿主语言词汇。本章不证明任何东西；现在可以速览，之后遇到陌生符号再回来查。
<!--/-->

<!--en-->
## Two disciplines
<!--zh-->
## 两条纪律
<!--/-->

<!--en-->
Both are machine-enforced conventions of the codebase, stated here because each one
changes how the book is read:

1. **Logic symbols have one source.** This chapter exports none of
   `⊓ ⊔ ⇒ ¬ ⊤ ⊥ ⋀ ⋁`; they come only from opening a truth algebra (next chapter).
   So whenever you meet a logic symbol, its meaning is the corresponding operation
   of whichever algebra the chapter has open: no symbol ever has two readings in
   one scope.
2. **Names are traceable on the page.** Every import lists exactly the names it
   takes, so a chapter's import block doubles as its precise list of prerequisites,
   and "where does this name come from" always has a visible answer. The deliberate
   exception is the book's two designated hubs, this chapter and the next: they are
   opened wholesale, so a name not listed in any import comes from a hub.
<!--zh-->
这两条纪律由机器执法，写在这里是因为它们各自改变本书的读法：

1. **逻辑符号只有一个来源。**本章不导出 `⊓ ⊔ ⇒ ¬ ⊤ ⊥ ⋀ ⋁` 中的任何一个；它们只能来自打开某个真值代数 (下一章)。于是每当你遇到逻辑符号，其含义就是所在章节打开的那个代数中的对应运算：任一作用域中，没有符号会有两种读法。
2. **名字在页面上可溯源。**每条 import 都精确列出所取的名字，一章的 import 块因此兼作它的先修清单，「这个名字从哪来」在页面上总有答案。有意设置的例外是全书指定的两个枢纽，即本章与下一章：它们被整体打开，凡未见于任何 import 清单的名字都来自枢纽。
<!--/-->

<!--en-->
## The host vocabulary
<!--zh-->
## 宿主词汇
<!--/-->

<!--en-->
The host organises its types into a tower of Tarski-style universes with explicit
levels. `Level`{.Agda} is the type
of the levels themselves, with its arithmetic `ℓ-zero`{.Agda}, `ℓ-suc`{.Agda},
`ℓ-max`{.Agda}; `Type`{.Agda}` ℓ` is the universe at level `ℓ`, and it is itself a
type one floor up, in `Type (ℓ-suc ℓ)`. Whenever the book surveys a totality
("all sets", "all propositions"), this level bookkeeping is what says how large a
totality is being surveyed. `_≡_`{.Agda} is
the path type, the host's equality, with the usual kit (`refl`{.Agda}, `sym`{.Agda},
`_∙_`{.Agda} for composition, `cong`{.Agda}, `transport`{.Agda}, `subst`{.Agda},
`funExt`{.Agda}). The h-level predicates grade a type by how much equality structure
it carries: `isProp`{.Agda} (any two inhabitants are equal), `isSet`{.Agda} (equality
itself is a proposition), and `isContr`{.Agda} (exactly one inhabitant, up to a
path). `isContr`{.Agda} is how this book says **unique existence**, a load-bearing
choice explained in the Charter. `hProp`{.Agda} packages a type with a proof that it
is a proposition, and `⟨_⟩`{.Agda} projects the underlying type back out (read it
"the underlying type of"). Then the data: dependent pairs
`Σ`{.Agda} and products `_×_`{.Agda}, natural numbers `ℕ`{.Agda}, vectors
`Vec`{.Agda} with finite indices `Fin`{.Agda} (the raw material of variable
environments), and the level-polymorphic empty type `⊥*`{.Agda}.
<!--zh-->
宿主把类型组织成一座塔斯基式宇宙塔，层级显式。`Level`{.Agda} 是层级本身的类型，配有层级算术 `ℓ-zero`{.Agda}、`ℓ-suc`{.Agda}、`ℓ-max`{.Agda}；`Type`{.Agda}` ℓ` 是第 `ℓ` 层宇宙，它自身又是高一层的类型，住在 `Type (ℓ-suc ℓ)` 里。本书凡检视某个总体 (「所有集合」「所有命题」)，都由这套层级记账精确说明检视的总体有多大。`_≡_`{.Agda} 是路径类型，即宿主的相等，配齐常用件 (`refl`{.Agda}、`sym`{.Agda}、复合 `_∙_`{.Agda}、`cong`{.Agda}、`transport`{.Agda}、`subst`{.Agda}、`funExt`{.Agda})。h-层级谓词按「相等结构的多少」为类型分级：`isProp`{.Agda} (任意两个居民相等)、`isSet`{.Agda} (相等本身是命题)、`isContr`{.Agda} (恰有一个居民，在路径意义下)。`isContr`{.Agda} 就是本书表述**唯一存在**的方式，这一承重决策在纲领中有完整论述。`hProp`{.Agda} 把一个类型与其命题性证明打包，`⟨_⟩`{.Agda} 把底层类型投影出来 (读作「延展」)。然后是数据件：依值对 `Σ`{.Agda} 与积 `_×_`{.Agda}、自然数 `ℕ`{.Agda}、向量 `Vec`{.Agda} 与有限索引 `Fin`{.Agda} (变量环境的原材料)，以及层级多态的空类型 `⊥*`{.Agda}。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

module Base.Prelude where

open import Cubical.Foundations.Prelude public
  using ( Type; Level; ℓ-zero; ℓ-suc; ℓ-max
        ; _≡_; refl; sym; _∙_; cong; cong₂
        ; transport; subst; funExt
        ; isProp; isSet; isContr; isProp→isSet
        ; Lift; lift; lower )
open import Cubical.Foundations.HLevels public
  using ( hProp; isSetHProp; isPropΠ )
open import Cubical.Foundations.Structure public
  using ( ⟨_⟩ )
open import Cubical.Data.Sigma public
  using ( Σ; Σ-syntax; _×_; _,_; fst; snd )
open import Cubical.Data.Nat public
  using ( ℕ; zero; suc )
open import Cubical.Data.Vec public
  using ( Vec; []; _∷_; lookup )
open import Cubical.Data.FinData public
  using ( Fin; zero; suc )
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
