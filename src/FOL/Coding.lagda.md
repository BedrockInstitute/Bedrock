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
## Recap
<!--zh-->
## 小结
<!--/-->

<!--en-->
Formulas are now sets: `⌜_⌝`{.Agda} tags a constructor index onto the codes of
the parts, constants coding themselves. The interface downstream is the relation
`Codes`{.Agda}, which keeps code values out of the equations a typechecker has
to normalize. Everything is generic in the structure, needing only an injective
pairing and an injection of the naturals; the hierarchy supplies both.
<!--zh-->
公式如今是集合了：`⌜_⌝`{.Agda} 把构造子序号贴在各部分的码上，而常量编码自身。下游的接口是关系 `Codes`{.Agda}，它使码值不出现在类型检查器必须归一化的等式里。一切都对结构泛型，只需一个单射的配对与自然数的一个单射；层级把二者都供上。
<!--/-->

<!--en-->
## Codes determine formulas
<!--zh-->
## 码决定公式
<!--/-->

<!--en-->
Two formulas of the same arity with the same code are the same formula. The
statement was dropped once, on the ground that its natural proof is a grid of
twelve by twelve of which a hundred and thirty-two clauses carry no mathematics,
and that the `Codes`{.Agda} relation was what every consumer had been designed
around. A consumer arrived that wants the equation rather than the relation, and
it wants it for a reason no relation answers: a recursion's table is a **set**, so
if two occurrences of different subformulas shared a code the table would be
genuinely multi-valued, and its existence, not merely its proof, would fail.

The grid does not have to be written. The constructor is recoverable from the
tag, and the tag is a number, so what a formula's constructor *is* can be
**computed** from it: one type family over the tag saying what having that tag
looks like, one function producing it, and the tag equation the pairing's
injectivity yields carries the second to the first. Twelve clauses each, and
twelve more for the case analysis, in place of a hundred and forty-four.

That is the same move the constructibility chapter makes to match twelve
constructors against eight demands, and it is worth saying once in general: **when
a case analysis is indexed by two things that a tag already relates, compute one
side from the tag instead of matching both.**
<!--zh-->
同一元数、同一码的两条公式是同一条公式。这条陈述曾被丢掉，理由是它的自然证明是一张十二乘十二的网格，其中一百三十二条子句不含数学，而每个消费方当初都是围绕 `Codes`{.Agda} 关系设计的。如今来了一个要等式而非要关系的消费方，而它要的理由是任何关系都答不了的：递归的表是一个**集合**，故若两处不同子公式共用一个码，那张表就真的多值，垮掉的将是它的**存在性**，而不只是它的证明。

那张网格不必写。构造子可从标签还原，而标签是一个数，故一条公式的构造子**是什么**可以从标签**算**出来：一个以标签为索引的类型族，说出「带那个标签」长什么样；一个函数把它造出来；而配对的单射性所给出的那条标签等式把后者搬到前者上。两者各十二条子句，再加十二条作情形分析，取代一百四十四条。

这与可构造性那一章「把十二个构造子对上八项要求」所用的是同一个动作，而它值得一般地说一次：**当一次情形分析由两样东西索引、而某个标签已经把它们关联起来时，就从标签算出一侧，不要两侧都匹配。**
<!--/-->

```agda
tagOf : ∀ {n} → Formula S n → ℕ
tagOf (t ∈̇ u)  = 0
tagOf (t ≐ u)  = 1
tagOf (a ∧̇ b)  = 2
tagOf (a ∨̇ b)  = 3
tagOf (a ⇒̇ b)  = 4
tagOf (¬̇ a)    = 5
tagOf ⊤̇        = 6
tagOf ⊥̇        = 7
tagOf (∃̇ a)    = 8
tagOf (∀̇ a)    = 9
tagOf (∀̇∈ t a) = 10
tagOf (∃̇∈ t a) = 11

payOf : ∀ {n} → Formula S n → S
payOf (t ∈̇ u)  = pr ⌜ t ⌝ᵗ ⌜ u ⌝ᵗ
payOf (t ≐ u)  = pr ⌜ t ⌝ᵗ ⌜ u ⌝ᵗ
payOf (a ∧̇ b)  = pr ⌜ a ⌝ ⌜ b ⌝
payOf (a ∨̇ b)  = pr ⌜ a ⌝ ⌜ b ⌝
payOf (a ⇒̇ b)  = pr ⌜ a ⌝ ⌜ b ⌝
payOf (¬̇ a)    = ⌜ a ⌝
payOf ⊤̇        = encℕ 0
payOf ⊥̇        = encℕ 0
payOf (∃̇ a)    = ⌜ a ⌝
payOf (∀̇ a)    = ⌜ a ⌝
payOf (∀̇∈ t a) = pr ⌜ t ⌝ᵗ ⌜ a ⌝
payOf (∃̇∈ t a) = pr ⌜ t ⌝ᵗ ⌜ a ⌝

shape : ∀ {n} (φ : Formula S n) → ⌜ φ ⌝ ≡ mkTag (tagOf φ) (payOf φ)
shape (t ∈̇ u)  = refl
shape (t ≐ u)  = refl
shape (a ∧̇ b)  = refl
shape (a ∨̇ b)  = refl
shape (a ⇒̇ b)  = refl
shape (¬̇ a)    = refl
shape ⊤̇        = refl
shape ⊥̇        = refl
shape (∃̇ a)    = refl
shape (∀̇ a)    = refl
shape (∀̇∈ t a) = refl
shape (∃̇∈ t a) = refl

Match : ∀ {n} → ℕ → Formula S n → Type ℓ
Match {n} 0  φ = Σ[ t ∈ Term S n ] (Σ[ u ∈ Term S n ] (φ ≡ (t ∈̇ u)))
Match {n} 1  φ = Σ[ t ∈ Term S n ] (Σ[ u ∈ Term S n ] (φ ≡ (t ≐ u)))
Match {n} 2  φ = Σ[ a ∈ Formula S n ] (Σ[ b ∈ Formula S n ] (φ ≡ (a ∧̇ b)))
Match {n} 3  φ = Σ[ a ∈ Formula S n ] (Σ[ b ∈ Formula S n ] (φ ≡ (a ∨̇ b)))
Match {n} 4  φ = Σ[ a ∈ Formula S n ] (Σ[ b ∈ Formula S n ] (φ ≡ (a ⇒̇ b)))
Match {n} 5  φ = Σ[ a ∈ Formula S n ] (φ ≡ (¬̇ a))
Match     6  φ = φ ≡ ⊤̇
Match     7  φ = φ ≡ ⊥̇
Match {n} 8  φ = Σ[ a ∈ Formula S (suc n) ] (φ ≡ (∃̇ a))
Match {n} 9  φ = Σ[ a ∈ Formula S (suc n) ] (φ ≡ (∀̇ a))
Match {n} 10 φ = Σ[ t ∈ Term S n ] (Σ[ a ∈ Formula S (suc n) ] (φ ≡ ∀̇∈ t a))
Match {n} 11 φ = Σ[ t ∈ Term S n ] (Σ[ a ∈ Formula S (suc n) ] (φ ≡ ∃̇∈ t a))
Match     _  _ = Empty.⊥*

matches : ∀ {n} (φ : Formula S n) → Match (tagOf φ) φ
matches (t ∈̇ u)  = t , (u , refl)
matches (t ≐ u)  = t , (u , refl)
matches (a ∧̇ b)  = a , (b , refl)
matches (a ∨̇ b)  = a , (b , refl)
matches (a ⇒̇ b)  = a , (b , refl)
matches (¬̇ a)    = a , refl
matches ⊤̇        = refl
matches ⊥̇        = refl
matches (∃̇ a)    = a , refl
matches (∀̇ a)    = a , refl
matches (∀̇∈ t a) = t , (a , refl)
matches (∃̇∈ t a) = t , (a , refl)

⌜⌝-inj : ∀ {n} (φ ψ : Formula S n) → ⌜ φ ⌝ ≡ ⌜ ψ ⌝ → φ ≡ ψ

private
  go : ∀ {n} (φ ψ : Formula S n) → Match (tagOf φ) ψ → payOf φ ≡ payOf ψ → φ ≡ ψ
  go (t ∈̇ u) ψ (t' , (u' , q)) p =
    cong₂ _∈̇_ (⌜⌝ᵗ-inj t t' (pr-inj (p ∙ cong payOf q) .fst))
              (⌜⌝ᵗ-inj u u' (pr-inj (p ∙ cong payOf q) .snd)) ∙ sym q
  go (t ≐ u) ψ (t' , (u' , q)) p =
    cong₂ _≐_ (⌜⌝ᵗ-inj t t' (pr-inj (p ∙ cong payOf q) .fst))
              (⌜⌝ᵗ-inj u u' (pr-inj (p ∙ cong payOf q) .snd)) ∙ sym q
  go (a ∧̇ b) ψ (a' , (b' , q)) p =
    cong₂ _∧̇_ (⌜⌝-inj a a' (pr-inj (p ∙ cong payOf q) .fst))
              (⌜⌝-inj b b' (pr-inj (p ∙ cong payOf q) .snd)) ∙ sym q
  go (a ∨̇ b) ψ (a' , (b' , q)) p =
    cong₂ _∨̇_ (⌜⌝-inj a a' (pr-inj (p ∙ cong payOf q) .fst))
              (⌜⌝-inj b b' (pr-inj (p ∙ cong payOf q) .snd)) ∙ sym q
  go (a ⇒̇ b) ψ (a' , (b' , q)) p =
    cong₂ _⇒̇_ (⌜⌝-inj a a' (pr-inj (p ∙ cong payOf q) .fst))
              (⌜⌝-inj b b' (pr-inj (p ∙ cong payOf q) .snd)) ∙ sym q
  go (¬̇ a) ψ (a' , q) p = cong ¬̇_ (⌜⌝-inj a a' (p ∙ cong payOf q)) ∙ sym q
  go ⊤̇ ψ q p = sym q
  go ⊥̇ ψ q p = sym q
  go (∃̇ a) ψ (a' , q) p = cong ∃̇_ (⌜⌝-inj a a' (p ∙ cong payOf q)) ∙ sym q
  go (∀̇ a) ψ (a' , q) p = cong ∀̇_ (⌜⌝-inj a a' (p ∙ cong payOf q)) ∙ sym q
  go (∀̇∈ t a) ψ (t' , (a' , q)) p =
    cong₂ ∀̇∈ (⌜⌝ᵗ-inj t t' (pr-inj (p ∙ cong payOf q) .fst))
             (⌜⌝-inj a a' (pr-inj (p ∙ cong payOf q) .snd)) ∙ sym q
  go (∃̇∈ t a) ψ (t' , (a' , q)) p =
    cong₂ ∃̇∈ (⌜⌝ᵗ-inj t t' (pr-inj (p ∙ cong payOf q) .fst))
             (⌜⌝-inj a a' (pr-inj (p ∙ cong payOf q) .snd)) ∙ sym q

⌜⌝-inj φ ψ e = go φ ψ
  (subst (λ k → Match k ψ) (sym (tp .fst)) (matches ψ)) (tp .snd)
  where
  tp = mkTag-inj (sym (shape φ) ∙ e ∙ shape ψ)
```
