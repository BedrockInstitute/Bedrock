# Semantics

<!--en-->
Three things turn syntax into meaning: a structure `𝒮` to be talked about, an
interpretation of the constants, and an environment giving values to the free
variables. The first is a parameter of this whole chapter, along with the truth
algebra it is valued in; the generic development speaks through the abstract `𝕋`,
as the scope discipline prescribes.
<!--zh-->
把语法变成含义需要三样东西：被谈论的结构 `𝒮`、常量的解释，以及给自由变量赋值的环境。第一样连同它取值的真值代数是本章整体的参数；泛型开发按作用域纪律的安排，经抽象的 `𝕋` 说话。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import FOL.Structure using ( ZFStructure; _^_ )

module FOL.Semantics {ℓ ℓ'} (𝕋 : TruthAlg ℓ ℓ') (𝒮 : ZFStructure 𝕋) where

open import FOL.Syntax using
  ( Term; con; var
  ; Formula; _∈̇_; _≐_; _∧̇_; _∨̇_; _⇒̇_; ¬̇_; ⊤̇; ⊥̇; ∃̇_; ∀̇_; ∀̇∈; ∃̇∈
  ; mapTm; mapFo; Closed; embed; absurd )

open TruthAlg 𝕋
open ZFStructure 𝒮
```

<!--en-->
## Evaluation and satisfaction
<!--zh-->
## 求值与满足
<!--/-->

<!--en-->
The remaining ingredient, the constant interpretation `ι : K → S`, is fixed once by
an inner module `At`{.Agda}: everyday work happens under one fixed `ι` (the
canonical case takes the carrier itself as constant domain, with `ι` the identity),
while the occasional lemma that crosses interpretations, such as those at the end
of this chapter, uses qualified names.
<!--zh-->
剩下那样原料，常量解释 `ι : K → S`，由内部模块 `At`{.Agda} 一次固定：日常工作在一个固定的 `ι` 下进行 (典范情形以载体自身为常量域，`ι` 取恒等)，偶尔需要跨解释的引理，如本章末那几条，则以限定名访问。
<!--/-->

```agda
module At {ℓc} {K : Type ℓc} (ι : K → S) where
```

<!--en-->
Two readings, both straight from the textbook: `⟦_⟧`{.Agda} reads "the value of",
and `_⊨_`{.Agda} reads "satisfies", with the environment on the left, `γ ⊨ φ`.
Evaluation of a term either asks `ι` (a constant) or looks up the environment (a
variable). Satisfaction is a single structural recursion over the twelve
constructors.
<!--zh-->
两个记号都直接来自教科书：`⟦_⟧`{.Agda} 读作「取值」，`_⊨_`{.Agda} 读作「满足」，环境在左，写 `γ ⊨ φ`。词项求值要么问 `ι` (常量)，要么查环境 (变量)。满足关系是对十二个构造子的一次结构递归。
<!--/-->

```agda
  ⟦_⟧ : ∀ {n} → Term K n → S ^ n → S
  ⟦ con k ⟧ γ = ι k
  ⟦ var i ⟧ γ = lookup i γ

  infix 6 _⊨_

  _⊨_ : ∀ {n} → S ^ n → Formula K n → Ω
  γ ⊨ (t ∈̇ u)  = ⟦ t ⟧ γ ∈ˢ ⟦ u ⟧ γ
  γ ⊨ (t ≐ u)  = ⟦ t ⟧ γ ≈ˢ ⟦ u ⟧ γ
  γ ⊨ (φ ∧̇ ψ)  = (γ ⊨ φ) ⊓ (γ ⊨ ψ)
  γ ⊨ (φ ∨̇ ψ)  = (γ ⊨ φ) ⊔ (γ ⊨ ψ)
  γ ⊨ (φ ⇒̇ ψ)  = (γ ⊨ φ) ⇒ (γ ⊨ ψ)
  γ ⊨ (¬̇ φ)    = ¬ (γ ⊨ φ)
  γ ⊨ ⊤̇        = ⊤
  γ ⊨ ⊥̇        = ⊥
  γ ⊨ (∃̇ φ)    = ⋁ S (λ x → (x ∷ γ) ⊨ φ)
  γ ⊨ (∀̇ φ)    = ⋀ S (λ x → (x ∷ γ) ⊨ φ)
  γ ⊨ (∀̇∈ t φ) = ⋀ S (λ x → (x ∈ˢ ⟦ t ⟧ γ) ⇒ ((x ∷ γ) ⊨ φ))
  γ ⊨ (∃̇∈ t φ) = ⋁ S (λ x → (x ∈ˢ ⟦ t ⟧ γ) ⊓ ((x ∷ γ) ⊨ φ))
```

<!--en-->
Look at the right-hand sides: each is **exactly** the truth algebra's corresponding
operation, applied to the meanings of the subformulas. Object conjunction means
host conjunction, the object quantifiers mean `⋀` and `⋁` over the carrier; there
is no translation layer in between. A formula with `n` free variables thus means a
function `S ^ n → Ω`{.Agda}, deliberately the same shape as a **predicate** written
directly in the host language; later in this part a bridge is built between the
two, and this faithfulness is what will make every plank of that bridge a one-line
congruence.

The two bounded clauses deserve a second look: their quantification is pinned to
the members of `⟦ t ⟧ γ`. This is where the tameness promised in the syntax
chapter physically lives, and later chapters return to these two lines again and
again.
<!--zh-->
看各子句的右端：每一条都**恰好是**真值代数的对应运算，作用在子公式的含义上。对象合取的含义就是宿主合取，对象量词的含义就是载体上的 `⋀` 与 `⋁`，中间没有任何翻译层。于是带 `n` 个自由变量的公式，含义是一个 `S ^ n → Ω`{.Agda} 型的函数，与宿主语言直接写出的**谓词**刻意同形；本部稍后将在两者之间架桥，而这份忠实性将让那座桥的每一块板都归于一行同余。

两条有界子句值得再看一眼：它们的量化被钉在 `⟦ t ⟧ γ` 的成员上。语法章许诺的驯良性，物理上就住在这里，后面的章节将一次次回到这两行。
<!--/-->

<!--en-->
## Relabelling preserves meaning
<!--zh-->
## 重标记保语义
<!--/-->

<!--en-->
Relabelling constants along `f : K → K'` and then evaluating under `ι` is the same
as evaluating under `ι ∘ f` directly. One structural induction, every case a
congruence; the two term cases are even `refl`{.Agda}.
<!--zh-->
沿 `f : K → K'` 重标记常量后在 `ι` 下求值，与直接在 `ι ∘ f` 下求值相同。一次结构归纳，每个情形都是同余；两个词项情形干脆是 `refl`{.Agda}。
<!--/-->

```agda
⟦⟧-map : ∀ {ℓc ℓd} {K : Type ℓc} {K' : Type ℓd} (f : K → K') (ι : K' → S)
         {n} (t : Term K n) (γ : S ^ n)
       → At.⟦_⟧ ι (mapTm f t) γ ≡ At.⟦_⟧ (λ k → ι (f k)) t γ
⟦⟧-map f ι (con k) γ = refl
⟦⟧-map f ι (var i) γ = refl

⊨-map : ∀ {ℓc ℓd} {K : Type ℓc} {K' : Type ℓd} (f : K → K') (ι : K' → S)
        {n} (φ : Formula K n) (γ : S ^ n)
      → At._⊨_ ι γ (mapFo f φ) ≡ At._⊨_ (λ k → ι (f k)) γ φ
⊨-map f ι (t ∈̇ u)  γ = cong₂ _∈ˢ_ (⟦⟧-map f ι t γ) (⟦⟧-map f ι u γ)
⊨-map f ι (t ≐ u)  γ = cong₂ _≈ˢ_ (⟦⟧-map f ι t γ) (⟦⟧-map f ι u γ)
⊨-map f ι (φ ∧̇ ψ)  γ = cong₂ _⊓_ (⊨-map f ι φ γ) (⊨-map f ι ψ γ)
⊨-map f ι (φ ∨̇ ψ)  γ = cong₂ _⊔_ (⊨-map f ι φ γ) (⊨-map f ι ψ γ)
⊨-map f ι (φ ⇒̇ ψ)  γ = cong₂ _⇒_ (⊨-map f ι φ γ) (⊨-map f ι ψ γ)
⊨-map f ι (¬̇ φ)    γ = cong ¬_ (⊨-map f ι φ γ)
⊨-map f ι ⊤̇        γ = refl
⊨-map f ι ⊥̇        γ = refl
⊨-map f ι (∃̇ φ)    γ = cong (⋁ S) (funExt (λ x → ⊨-map f ι φ (x ∷ γ)))
⊨-map f ι (∀̇ φ)    γ = cong (⋀ S) (funExt (λ x → ⊨-map f ι φ (x ∷ γ)))
⊨-map f ι (∀̇∈ t φ) γ = cong (⋀ S) (funExt (λ x →
  cong₂ _⇒_ (cong (x ∈ˢ_) (⟦⟧-map f ι t γ)) (⊨-map f ι φ (x ∷ γ))))
⊨-map f ι (∃̇∈ t φ) γ = cong (⋁ S) (funExt (λ x →
  cong₂ _⊓_ (cong (x ∈ˢ_) (⟦⟧-map f ι t γ)) (⊨-map f ι φ (x ∷ γ))))
```

<!--en-->
The corollary the closed syntax was waiting for: a closed formula entering any
constant domain through `embed`{.Agda} keeps its meaning. The data axis and the
working syntax share one semantics; nothing needs proving twice.
<!--zh-->
封闭语法等候的推论：闭公式经 `embed`{.Agda} 进入任何常量域，含义不变。数据轴与工作语法共享同一套语义，无一事需证两遍。
<!--/-->

```agda
embed-⊨ : ∀ {ℓe ℓc} {K : Type ℓc} (ι : K → S) {n} (φ : Closed {ℓe} n) (γ : S ^ n)
        → At._⊨_ ι γ (embed φ) ≡ At._⊨_ (λ b → ι (absurd b)) γ φ
embed-⊨ ι = ⊨-map absurd ι
```

<!--en-->
## Recap
<!--zh-->
## 小结
<!--/-->

<!--en-->
Meaning is structural recursion: `⟦_⟧`{.Agda} evaluates terms, `γ ⊨ φ` lands in the
truth algebra, and each clause is the corresponding algebra operation, nothing
more. Formulas with `n` free variables mean functions `S ^ n → Ω`{.Agda}, the same
shape as host predicates, and relabelling constants never disturbs meaning. The
one bridge still missing between formulas and predicates is built before this part
closes.
<!--zh-->
含义就是结构递归：`⟦_⟧`{.Agda} 给词项取值，`γ ⊨ φ` 落进真值代数，每条子句恰是对应的代数运算，分毫不多。带 `n` 个自由变量的公式，含义是 `S ^ n → Ω`{.Agda} 型函数，与宿主谓词同形；重标记常量永不扰动含义。公式与谓词之间尚缺的那座桥，在本部收束前架起。
<!--/-->
