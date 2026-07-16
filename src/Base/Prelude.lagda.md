# Prelude

<!--en-->
Every chapter of this book is literate Agda: the prose you are reading and the
machine-checked code live in the same file. This opening chapter sets the table. It
re-exports, from the cubical library, the small host-language vocabulary the whole
development stands on, and it fixes two disciplines about how names enter scope.
Nothing is proved here; skim it now, and return when a symbol looks unfamiliar.
<!--zh-->
本书的每一章都是文学化 Agda：你正在读的文稿与经机器检查的代码同住一个文件。这开篇一章负责摆桌子：它从 cubical 标准库转出全书立足的一小套宿主语言词汇，并确立两条名字进入作用域的纪律。本章不证明任何东西；现在可以速览，之后遇到陌生符号再回来查。
<!--/-->

<!--en-->
## The host vocabulary
<!--zh-->
## 宿主词汇
<!--/-->

<!--en-->
`Type`{.Agda} and `Level`{.Agda} are the universes: every type lives at some level,
and `ℓ-zero`{.Agda}, `ℓ-suc`{.Agda}, `ℓ-max`{.Agda} navigate them. `_≡_`{.Agda} is
the path type, the host's equality, with the usual kit (`refl`{.Agda}, `sym`{.Agda},
`_∙_`{.Agda} for composition, `cong`{.Agda}, `transport`{.Agda}, `subst`{.Agda},
`funExt`{.Agda}). The h-level predicates grade a type by how much equality structure
it carries: `isProp`{.Agda} (any two inhabitants are equal), `isSet`{.Agda} (equality
itself is a proposition), and `isContr`{.Agda} (exactly one inhabitant, up to a
path). `isContr`{.Agda} is how this book says **unique existence**, a load-bearing
choice explained in the Charter. `hProp`{.Agda} packages a type with a proof that it
is a proposition, and `⟨_⟩`{.Agda} projects the underlying type back out (read it
"the underlying type of"; typed `\<` `\>`). Then the data: dependent pairs
`Σ`{.Agda} and products `_×_`{.Agda}, natural numbers `ℕ`{.Agda}, vectors
`Vec`{.Agda} with finite indices `Fin`{.Agda} (the raw material of variable
environments), and the level-polymorphic empty type `⊥*`{.Agda}.
<!--zh-->
`Type`{.Agda} 与 `Level`{.Agda} 是宇宙：每个类型都住在某一层级，`ℓ-zero`{.Agda}、`ℓ-suc`{.Agda}、`ℓ-max`{.Agda} 在层级间导航。`_≡_`{.Agda} 是路径类型，即宿主的相等，配齐常用件 (`refl`{.Agda}、`sym`{.Agda}、复合 `_∙_`{.Agda}、`cong`{.Agda}、`transport`{.Agda}、`subst`{.Agda}、`funExt`{.Agda})。h-层级谓词按「相等结构的多少」为类型分级：`isProp`{.Agda} (任意两个居民相等)、`isSet`{.Agda} (相等本身是命题)、`isContr`{.Agda} (恰有一个居民，在路径意义下)。`isContr`{.Agda} 就是本书表述**唯一存在**的方式，这一承重决策在纲领中有完整论述。`hProp`{.Agda} 把一个类型与其命题性证明打包，`⟨_⟩`{.Agda} 把底层类型投影出来 (读作「延展」，输入 `\<` `\>`)。然后是数据件：依值对 `Σ`{.Agda} 与积 `_×_`{.Agda}、自然数 `ℕ`{.Agda}、向量 `Vec`{.Agda} 与有限索引 `Fin`{.Agda} (变量环境的原材料)，以及层级多态的空类型 `⊥*`{.Agda}。
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
Two disciplines, both machine-enforced, both worth knowing as a reader:

1. **This chapter exports no logic.** The symbols `⊓ ⊔ ⇒ ¬ ⊤ ⊥ ⋀ ⋁` have exactly
   one source in the whole book: the truth algebra of the next chapter. Whichever
   algebra a chapter opens, that is what its logic symbols mean, so every logic
   symbol has one meaning in any scope.
2. **Every import carries an explicit list** of the names it takes, so the export
   surface is always visible. The two exceptions are this chapter and the next: they
   are the book's designated hubs, curated precisely so that later chapters can open
   them wholesale.
<!--zh-->
两条纪律，均由机器执法，读者也值得知道：

1. **本章不导出任何逻辑运算。**符号 `⊓ ⊔ ⇒ ¬ ⊤ ⊥ ⋀ ⋁` 在全书只有一个来源：下一章的真值代数。一章打开哪个代数，它的逻辑符号就是哪个代数的运算，因此任一作用域中每个逻辑符号只有一个含义。
2. **每条 import 都带显式名单**，列出所取的名字，导出面永远可见。仅有的两个例外是本章与下一章：它们是全书指定的枢纽，之所以精心策划，正是为了让后续章节整体打开。
<!--/-->

<!--en-->
## Environments
<!--zh-->
## 环境
<!--/-->

<!--en-->
An environment assigns values to $n$ free variables. The book writes `S ^ n`
for it, a vector of length $n$, matching the traditional superscript $S^n$
(`_^_`{.Agda} reads "power"; typed `^`). It is nothing but notation:
<!--zh-->
环境为 $n$ 个自由变量指派取值。本书将其写作 `S ^ n`，即长度为 $n$ 的向量，对齐传统上标记号 $S^n$ (`_^_`{.Agda} 读作「幂」，输入 `^`)。它只是记号：
<!--/-->

```agda
infixl 30 _^_

_^_ : ∀ {ℓ} → Type ℓ → ℕ → Type ℓ
A ^ n = Vec A n
```

<!--en-->
## Absurdity
<!--zh-->
## 荒谬消去
<!--/-->

<!--en-->
From the empty type anything follows. `absurd`{.Agda} is that standard elimination
for the lifted empty `⊥*`{.Agda}; closed syntax will later use `⊥*`{.Agda} as its
constant domain, and `absurd`{.Agda} interprets the constants that do not exist.
<!--zh-->
从空类型可以推出一切。`absurd`{.Agda} 就是提升空类型 `⊥*`{.Agda} 的这一标准消去；封闭语法之后会以 `⊥*`{.Agda} 作为常量域，而 `absurd`{.Agda} 负责解释那些不存在的常量。
<!--/-->

```agda
absurd : ∀ {ℓ ℓ'} {A : Type ℓ'} → ⊥* {ℓ} → A
absurd (lift ())
```

<!--en-->
## Recap
<!--zh-->
## 小结
<!--/-->

<!--en-->
In scope from here on: universes, paths, h-levels, `hProp`{.Agda} with `⟨_⟩`{.Agda},
pairs, `ℕ`{.Agda}, `Vec`{.Agda}, `Fin`{.Agda}, `⊥*`{.Agda}, environments `A ^ n`,
and `absurd`{.Agda}. Logic symbols are deliberately absent: they arrive with the
truth algebra, next.
<!--zh-->
自此进入作用域的有：宇宙、路径、h-层级、`hProp`{.Agda} 与 `⟨_⟩`{.Agda}、对与积、`ℕ`{.Agda}、`Vec`{.Agda}、`Fin`{.Agda}、`⊥*`{.Agda}、环境 `A ^ n`，以及 `absurd`{.Agda}。逻辑符号刻意缺席：它们随下一章的真值代数登场。
<!--/-->
