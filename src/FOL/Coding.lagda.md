# Syntax as sets

<!--en-->
Everything so far has kept formulas outside the sets they talk about: a formula
is host-level data, a set is a point of the structure, and satisfaction is the
bridge. Part 4 needs the other direction. To say inside a model that some set is
definable, or to compare two formulas by an order that a model can see, the
formulas themselves must be sets. This chapter injects them.

The encoding is deliberately dull. There is no arithmetization, no Gödel
numbering, no recursion trick: a formula's code is a tagged pair, the tag being
the constructor's index and the payload the codes of its parts. Recursion stays
where it belongs, on the host's inductive `Formula`{.Agda}, and the code is a
boundary format. The one elegance is that a set constant is already a set, so
constants are their own codes.

What the chapter takes as parameters is exactly what the encoding needs: a
pairing operation with injectivity, and an injection of the naturals. Nothing
else about the structure matters, so the chapter is generic and the hierarchy
instantiates it later.

A word on the deliverable that matters most. Alongside the code function there
is an inductive relation `Codes`{.Agda}, "this set codes that formula", whose
constructors carry sub-derivations at the sub-code positions. Reasoning about
codes goes through that relation rather than through equations between code
*values*, and the reason is practical: a code value is a deeply nested pair, and
an equation between two of them forces a typechecker to unfold both. The
relation makes the shape a constructor index instead, so matching is syntactic
and the values are never normalized.
<!--zh-->
迄今为止的一切都把公式留在它们所谈论的集合之外：公式是宿主层的数据，集合是结构的点，满足关系是二者之间的桥。第四部需要相反的方向。要在模型内部说某个集合可定义，或者用模型看得见的序去比较两条公式，公式自身就必须是集合。本章把它们注入进去。

这套编码刻意平淡。没有算术化，没有哥德尔编号，没有递归花招：公式的码是一个带标签的对，标签是构造子的序号，载荷是各部分的码。递归留在它该在的地方，即宿主的归纳类型 `Formula`{.Agda} 上，而码是一种边界格式。唯一的优雅之处是：集合常量本来就是集合，故常量即自身的码。

本章取作参数的，恰是编码所需的东西：一个带单射性的配对运算，以及自然数的一个单射。关于结构的其余一切都无关紧要，故本章是泛型的，层级稍后才来实例化它。

关于最要紧的那件交付物说一句。除码函数之外，还有一个归纳关系 `Codes`{.Agda}，读作「这个集合编码那条公式」，其构造子在子码的位置上携带子推导。关于码的推理走这个关系，而不走码**值**之间的等式，理由是实际的：码值是深层嵌套的对，而两个码值之间的等式会迫使类型检查器把两边都展开。这个关系把形状变成构造子索引，于是匹配是句法的，而码值从不被归一化。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import FOL.ZFStructure using ( ZFStructure )

module FOL.Coding {ℓ} (𝒮 : ZFStructure (hPropAlgebra ℓ))
  (pr       : ZFStructure.S 𝒮 → ZFStructure.S 𝒮 → ZFStructure.S 𝒮)
  (pr-inj   : ∀ {a b c d} → pr a b ≡ pr c d → (a ≡ c) × (b ≡ d))
  (encℕ     : ℕ → ZFStructure.S 𝒮)
  (encℕ-inj : ∀ {j k} → encℕ j ≡ encℕ k → j ≡ k)
  where

open ZFStructure 𝒮 using ( S )
open import FOL.Syntax
  using ( Term; con; var; Formula
        ; _∈̇_; _≐_; _∧̇_; _∨̇_; _⇒̇_; ¬̇_; ⊤̇; ⊥̇; ∃̇_; ∀̇_; ∀̇∈; ∃̇∈ )

import Cubical.Data.Empty as Empty
open import Cubical.Data.Nat using ( znots; snotz )
open import Cubical.Data.FinData using ( toℕ; inj-toℕ )
```

<!--en-->
## Tagged pairs
<!--zh-->
## 带标签的对
<!--/-->

<!--en-->
The one construction: a constructor index paired with a payload. Injectivity
comes straight from the two parameters, and the clash pattern packages the case
that will recur whenever two different constructors are compared.
<!--zh-->
唯一的构造：构造子序号与载荷配成对。单射性直接来自那两个参数，而冲突模式把「两个不同构造子相比较」时反复出现的情形打包起来。
<!--/-->

```agda
mkTag : ℕ → S → S
mkTag k x = pr (encℕ k) x

mkTag-inj : ∀ {j k x y} → mkTag j x ≡ mkTag k y → (j ≡ k) × (x ≡ y)
mkTag-inj p = encℕ-inj (pr-inj p .fst) , pr-inj p .snd

clash : ∀ {j k x y} {A : Type ℓ} → (j ≡ k → Empty.⊥) → mkTag j x ≡ mkTag k y → A
clash ne p = Empty.rec (ne (mkTag-inj p .fst))
```

<!--en-->
## Codes
<!--zh-->
## 码
<!--/-->

<!--en-->
Terms first, where the promised elegance appears: a set constant needs no
encoding, since it is already a set, and only the variable index has to be
injected. Terms are separated enough that their injectivity is immediate.
<!--zh-->
先看项，承诺的那点优雅在此出现：集合常量无须编码，因为它本来就是集合，只有变元的序号要被注入。项的分隔足够清楚，其单射性立得。
<!--/-->

```agda
⌜_⌝ᵗ : ∀ {n} → Term S n → S
⌜ con x ⌝ᵗ = mkTag 0 x
⌜ var i ⌝ᵗ = mkTag 1 (encℕ (toℕ i))

⌜⌝ᵗ-inj : ∀ {n} (t u : Term S n) → ⌜ t ⌝ᵗ ≡ ⌜ u ⌝ᵗ → t ≡ u
⌜⌝ᵗ-inj (con x) (con y) p = cong con (mkTag-inj p .snd)
⌜⌝ᵗ-inj (con x) (var j) p = clash znots p
⌜⌝ᵗ-inj (var i) (con y) p = clash snotz p
⌜⌝ᵗ-inj (var i) (var j) p = cong var (inj-toℕ (encℕ-inj (mkTag-inj p .snd)))
```

<!--en-->
Then formulas: twelve constructors, twelve tags. Binary constructors pair the
two sub-codes, unary ones take the sub-code bare, and the two constants take a
dummy payload since the tag already tells them apart.
<!--zh-->
然后是公式：十二个构造子，十二个标签。二元构造子把两个子码配成对，一元的直接取子码，而两个常量取一个虚载荷，因为标签已经把它们区分开了。
<!--/-->

```agda
⌜_⌝ : ∀ {n} → Formula S n → S
⌜ t ∈̇ u ⌝   = mkTag 0  (pr ⌜ t ⌝ᵗ ⌜ u ⌝ᵗ)
⌜ t ≐ u ⌝   = mkTag 1  (pr ⌜ t ⌝ᵗ ⌜ u ⌝ᵗ)
⌜ φ ∧̇ ψ ⌝   = mkTag 2  (pr ⌜ φ ⌝ ⌜ ψ ⌝)
⌜ φ ∨̇ ψ ⌝   = mkTag 3  (pr ⌜ φ ⌝ ⌜ ψ ⌝)
⌜ φ ⇒̇ ψ ⌝   = mkTag 4  (pr ⌜ φ ⌝ ⌜ ψ ⌝)
⌜ ¬̇ φ ⌝     = mkTag 5  ⌜ φ ⌝
⌜ ⊤̇ ⌝       = mkTag 6  (encℕ 0)
⌜ ⊥̇ ⌝       = mkTag 7  (encℕ 0)
⌜ ∃̇ φ ⌝     = mkTag 8  ⌜ φ ⌝
⌜ ∀̇ φ ⌝     = mkTag 9  ⌜ φ ⌝
⌜ ∀̇∈ t φ ⌝  = mkTag 10 (pr ⌜ t ⌝ᵗ ⌜ φ ⌝)
⌜ ∃̇∈ t φ ⌝  = mkTag 11 (pr ⌜ t ⌝ᵗ ⌜ φ ⌝)
```

<!--en-->
## The coding relation
<!--zh-->
## 编码关系
<!--/-->

<!--en-->
And the chapter's real interface. `Codes s φ` says the set `s` codes the formula
`φ`, as an indexed inductive family whose constructors carry sub-derivations
exactly where the code function makes recursive calls. It is the same
information as the code function, presented so that a proof can match on the
*shape* of the coding rather than compute with the code.
<!--zh-->
然后是本章真正的接口。`Codes s φ` 说集合 `s` 编码公式 `φ`，是一个索引归纳族，其构造子恰在码函数作递归调用之处携带子推导。它与码函数携带同样的信息，只是呈现方式使得证明可以在编码的**形状**上匹配，而不必对码作计算。
<!--/-->

```agda
data CodesT {n : ℕ} : S → Term S n → Type ℓ where
  c-con : (x : S)     → CodesT (mkTag 0 x) (con x)
  c-var : (i : Fin n) → CodesT (mkTag 1 (encℕ (toℕ i))) (var i)

data Codes : {n : ℕ} → S → Formula S n → Type ℓ where
  c-∈  : ∀ {n s s'} {t u : Term S n}
       → CodesT s t → CodesT s' u → Codes (mkTag 0 (pr s s')) (t ∈̇ u)
  c-≐  : ∀ {n s s'} {t u : Term S n}
       → CodesT s t → CodesT s' u → Codes (mkTag 1 (pr s s')) (t ≐ u)
  c-∧  : ∀ {n s s'} {φ ψ : Formula S n}
       → Codes s φ → Codes s' ψ → Codes (mkTag 2 (pr s s')) (φ ∧̇ ψ)
  c-∨  : ∀ {n s s'} {φ ψ : Formula S n}
       → Codes s φ → Codes s' ψ → Codes (mkTag 3 (pr s s')) (φ ∨̇ ψ)
  c-⇒  : ∀ {n s s'} {φ ψ : Formula S n}
       → Codes s φ → Codes s' ψ → Codes (mkTag 4 (pr s s')) (φ ⇒̇ ψ)
  c-¬  : ∀ {n s} {φ : Formula S n}
       → Codes s φ → Codes (mkTag 5 s) (¬̇ φ)
  c-⊤  : ∀ {n} → Codes {n} (mkTag 6 (encℕ 0)) ⊤̇
  c-⊥  : ∀ {n} → Codes {n} (mkTag 7 (encℕ 0)) ⊥̇
  c-∃  : ∀ {n s} {φ : Formula S (suc n)}
       → Codes s φ → Codes (mkTag 8 s) (∃̇ φ)
  c-∀  : ∀ {n s} {φ : Formula S (suc n)}
       → Codes s φ → Codes (mkTag 9 s) (∀̇ φ)
  c-∀∈ : ∀ {n s s'} {t : Term S n} {φ : Formula S (suc n)}
       → CodesT s t → Codes s' φ → Codes (mkTag 10 (pr s s')) (∀̇∈ t φ)
  c-∃∈ : ∀ {n s s'} {t : Term S n} {φ : Formula S (suc n)}
       → CodesT s t → Codes s' φ → Codes (mkTag 11 (pr s s')) (∃̇∈ t φ)
```

<!--en-->
Two facts tie the relation to the function. Every formula is coded by its own
code, so the relation is inhabited wherever it should be; and any code for a
formula is *the* code of that formula, so the relation adds nothing beyond the
function. Both are one structural recursion, and the second is the one later
chapters lean on: it converts a derivation, which is cheap to match on, into the
equation, which is expensive to normalize, at exactly the point where the
equation is finally needed.
<!--zh-->
两个事实把关系与函数系在一起。每条公式都被它自己的码所编码，故该关系在该有的地方都有居民；而公式的任何一个码都**就是**那条公式的码，故该关系并不比函数多出什么。两者都是一次结构递归，而后者是后续诸章倚重的：它把推导 (匹配起来廉价) 换成等式 (归一化起来昂贵)，恰在等式终于被需要的那一点上。
<!--/-->

```agda
codesT-complete : ∀ {n} (t : Term S n) → CodesT ⌜ t ⌝ᵗ t
codesT-complete (con x) = c-con x
codesT-complete (var i) = c-var i

codes-complete : ∀ {n} (φ : Formula S n) → Codes ⌜ φ ⌝ φ
codes-complete (t ∈̇ u)  = c-∈  (codesT-complete t) (codesT-complete u)
codes-complete (t ≐ u)  = c-≐  (codesT-complete t) (codesT-complete u)
codes-complete (φ ∧̇ ψ)  = c-∧  (codes-complete φ)  (codes-complete ψ)
codes-complete (φ ∨̇ ψ)  = c-∨  (codes-complete φ)  (codes-complete ψ)
codes-complete (φ ⇒̇ ψ)  = c-⇒  (codes-complete φ)  (codes-complete ψ)
codes-complete (¬̇ φ)    = c-¬  (codes-complete φ)
codes-complete ⊤̇        = c-⊤
codes-complete ⊥̇        = c-⊥
codes-complete (∃̇ φ)    = c-∃  (codes-complete φ)
codes-complete (∀̇ φ)    = c-∀  (codes-complete φ)
codes-complete (∀̇∈ t φ) = c-∀∈ (codesT-complete t) (codes-complete φ)
codes-complete (∃̇∈ t φ) = c-∃∈ (codesT-complete t) (codes-complete φ)

codesT-canon : ∀ {n s} {t : Term S n} → CodesT s t → s ≡ ⌜ t ⌝ᵗ
codesT-canon (c-con x) = refl
codesT-canon (c-var i) = refl

codes-canon : ∀ {n s} {φ : Formula S n} → Codes s φ → s ≡ ⌜ φ ⌝
codes-canon (c-∈ ct cu) =
  cong (mkTag 0)  (cong₂ pr (codesT-canon ct) (codesT-canon cu))
codes-canon (c-≐ ct cu) =
  cong (mkTag 1)  (cong₂ pr (codesT-canon ct) (codesT-canon cu))
codes-canon (c-∧ c d)   = cong (mkTag 2)  (cong₂ pr (codes-canon c) (codes-canon d))
codes-canon (c-∨ c d)   = cong (mkTag 3)  (cong₂ pr (codes-canon c) (codes-canon d))
codes-canon (c-⇒ c d)   = cong (mkTag 4)  (cong₂ pr (codes-canon c) (codes-canon d))
codes-canon (c-¬ c)     = cong (mkTag 5)  (codes-canon c)
codes-canon c-⊤         = refl
codes-canon c-⊥         = refl
codes-canon (c-∃ c)     = cong (mkTag 8)  (codes-canon c)
codes-canon (c-∀ c)     = cong (mkTag 9)  (codes-canon c)
codes-canon (c-∀∈ ct c) =
  cong (mkTag 10) (cong₂ pr (codesT-canon ct) (codes-canon c))
codes-canon (c-∃∈ ct c) =
  cong (mkTag 11) (cong₂ pr (codesT-canon ct) (codes-canon c))
```

<!--en-->
Canonicity already gives what "the code determines the formula" is usually
stated for: two derivations over the same code force the two formulas to have
the same code, and every later argument in the book that needs to recover a
formula from its code has a derivation in hand. So the direct injectivity of
`⌜_⌝`{.Agda}, which would require comparing all twelve constructors against all
twelve, is not proved here; it is not needed by any consumer, and the relation
above is the interface those consumers were designed around.
<!--zh-->
典范性已经给出了「码决定公式」通常要陈述的内容：同一个码上的两份推导，迫使两条公式拥有相同的码；而本书此后每个需要从码还原公式的论证，手里都有一份推导。故 `⌜_⌝`{.Agda} 的直接单射性，那需要把十二个构造子与十二个逐一相比，此处不予证明；没有任何消费方需要它，而上面那个关系正是那些消费方所围绕设计的接口。
<!--/-->

<!--en-->
## Recap
<!--zh-->
## 小结
<!--/-->

<!--en-->
Formulas are now sets: `⌜_⌝`{.Agda} tags a constructor index onto the codes of
the parts, constants coding themselves. The interface downstream is the relation
`Codes`{.Agda}, complete (`codes-complete`{.Agda}) and canonical
(`codes-canon`{.Agda}), which keeps code values out of the equations a
typechecker has to normalize. Everything is generic in the structure, needing
only an injective pairing and an injection of the naturals; the hierarchy
supplies both.
<!--zh-->
公式如今是集合了：`⌜_⌝`{.Agda} 把构造子序号贴在各部分的码上，而常量编码自身。下游的接口是关系 `Codes`{.Agda}，它完备 (`codes-complete`{.Agda}) 且典范 (`codes-canon`{.Agda})，使码值不出现在类型检查器必须归一化的等式里。一切都对结构泛型，只需一个单射的配对与自然数的一个单射；层级把二者都供上。
<!--/-->
