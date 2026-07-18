# Absoluteness

<!--en-->
The certificates earn their keep. The scene is the one Part 4 will play out at
scale: a model, a sub-world `𝒮 ↾ M` carved out by a class, and formulas asked on
both sides. This chapter names the one condition that tames the passage,
**transitivity** of `M` (members of members stay in `M`, exactly what the empty
question of the previous chapter needed), and mechanizes the textbook theorem:
**Δ₀ formulas are absolute between a transitive class and the universe**, with the
Σ₁-upward and Π₁-downward transfers as cheap extensions, and, as the capstone, the
one-line composition that turns an inner graded representation into outer
satisfaction.
<!--zh-->
证书开始挣饭钱。这里的场景正是第四部将要大规模上演的那一幕：一个模型，一个由类裁出的子世界 `𝒮 ↾ M`，同一批公式两侧各问一遍。本章给驯服这趟通行的唯一条件起名：`M` 的**传递性** (成员的成员不出 `M`，恰是上一章那个空集之问所需要的)；然后机械化教科书定理：**Δ₀ 公式在传递类与全宇宙之间绝对**，Σ₁ 向上、Π₁ 向下两条转移作为廉价延伸。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

module FOL.Absoluteness where

open import Base.Prelude
open import Base.Truth
open import FOL.Structure using ( ZFStructure; _∈ᵗ_; _↾_; _^_ )
open import FOL.Syntax using ( Term; con; var; Formula; ∀̇∈; ∃̇∈ )
open import FOL.Graded using
  ( Δ₀; δ-∈; δ-≐; δ-∧; δ-∨; δ-⇒; δ-¬; δ-⊤; δ-⊥; δ-∀∈; δ-∃∈
  ; Σ₁; σ-Δ₀; σ-∃; Π₁; π-Δ₀; π-∀ )
import FOL.Semantics
open import Cubical.Data.Vec using ( map )
open import Cubical.Functions.Logic using ( ⇔toPath )
import Cubical.HITs.PropositionalTruncation as PT
```

<!--en-->
## Transitive classes
<!--zh-->
## 传递类
<!--/-->

<!--en-->
A class `M` over a carrier is **transitive** when members of its members stay in
it. Transitivity is exactly the hypothesis of this chapter's theorems, so here is
where it gets its name.
<!--zh-->
载体上的类 `M`，若成员的成员仍在其中，称为**传递**。传递性正是本章诸定理的前提，所以它在这里得名。
<!--/-->

```agda
Transitive : ∀ {ℓ} (𝒮 : ZFStructure (hPropAlg {ℓ}))
           → (ZFStructure.S 𝒮 → hProp ℓ) → Type ℓ
Transitive 𝒮 M = ∀ {x y} → _∈ᵗ_ 𝒮 y x → ⟨ M x ⟩ → ⟨ M y ⟩
```

<!--en-->
## The setting: one syntax, two semantics
<!--zh-->
## 设置：一套语法，两套语义
<!--/-->

<!--en-->
Fix an ambient structure `𝒮` and a transitive class `M`; the inner world is the
restriction `𝒮 ↾ M`, whose carrier `SM` consists of `M`'s members. The syntax
takes `K := SM`: constants in a formula can only be members of `M`, the parameter
discipline enforced by the type. The same formula family then receives **two
semantics**: evaluated outside, in `𝒮`, with constants interpreted through
`fst`{.Agda}; and evaluated inside, in `𝒮 ↾ M`, with constants standing for
themselves. Relativization is thus not a syntactic operation but two
instantiations of one generic semantics; the superscripts `ᵛ` and `ᵐ` on the
satisfaction symbols read "evaluated where".
<!--zh-->
固定环境结构 `𝒮` 与传递类 `M`；内层世界是限制结构 `𝒮 ↾ M`，其载体 `SM` 由 `M` 的成员组成。语法取 `K := SM`：公式中的常量只能是 `M` 的成员，参数纪律由类型强制。同一族公式于是得到**两套语义**：在外层 `𝒮` 中求值，常量经 `fst`{.Agda} 解释；在内层 `𝒮 ↾ M` 中求值，常量即其自身。相对化因此不是句法操作，而是同一泛型语义的两次实例化；满足符号上的上标 `ᵛ` 与 `ᵐ` 读作「在哪里求值」。
<!--/-->

```agda
module Single {ℓ} (𝒮 : ZFStructure (hPropAlg {ℓ}))
              (M : ZFStructure.S 𝒮 → hProp ℓ)
              (trans : Transitive 𝒮 M) where

  open TruthAlg (hPropAlg {ℓ})
  open ZFStructure 𝒮

  SM : Type ℓ
  SM = Σ[ x ∈ S ] ⟨ M x ⟩

  𝒮M : ZFStructure (hPropAlg {ℓ})
  𝒮M = 𝒮 ↾ M

  module SemV = FOL.Semantics (hPropAlg {ℓ}) 𝒮
  module SemM = FOL.Semantics (hPropAlg {ℓ}) 𝒮M

  open module V = SemV.At {K = SM} fst public
    renaming ( _⊨_ to _⊨ᵛ_ ; ⟦_⟧ to ⟦_⟧ᵛ )
  open module Mse = SemM.At {K = SM} (λ m → m) public
    renaming ( _⊨_ to _⊨ᵐ_ ; ⟦_⟧ to ⟦_⟧ᵐ )
```

<!--en-->
Inner and outer environments are related by projecting every entry; two private
dictionary lemmas settle the term level, where a constant is its own value on both
sides and a variable is a lookup.
<!--zh-->
内外环境经逐项投影相关；两条私有的字典引理解决词项层：常量在两侧都是自身的值，变量是一次查表。
<!--/-->

```agda
  private
    lookup-fst : ∀ {n} (i : Fin n) (δ : SM ^ n)
               → lookup i (map fst δ) ≡ fst (lookup i δ)
    lookup-fst zero    (m ∷ δ) = refl
    lookup-fst (suc i) (m ∷ δ) = lookup-fst i δ

    ⟦⟧-fst : ∀ {n} (t : Term SM n) (δ : SM ^ n)
           → fst (⟦ t ⟧ᵐ δ) ≡ ⟦ t ⟧ᵛ (map fst δ)
    ⟦⟧-fst (con m) δ = refl
    ⟦⟧-fst (var i) δ = sym (lookup-fst i δ)
```

<!--en-->
## The theorem
<!--zh-->
## 定理
<!--/-->

<!--en-->
One induction over the Δ₀ certificate. The connective cases are congruences; the
atoms go through the term lemmas (equality is the structure field `≈ˢ` on both
sides, so even that case is a `cong₂`{.Agda}). The transitivity hypothesis is
consumed **only in the two bounded-quantifier cases**, and there lies the whole
mathematical content: outward, a member `x` of `⟦ t ⟧` must be re-packed as a
member of `M`, and `x ∈ ⟦ t ⟧` together with `⟦ t ⟧ ∈ M` yields exactly that by
transitivity. The machine locates the textbook proof's load-bearing step to the
character.
<!--zh-->
对 Δ₀ 证书做一次归纳。联结词情形皆同余；原子走词项引理 (等词两侧都是结构字段 `≈ˢ`，连这个情形也归于 `cong₂`{.Agda})。传递性前提**只在两个有界量词情形被消费**，全部数学内容就在那里：往外走时，`⟦ t ⟧` 的成员 `x` 须重新打包为 `M` 的成员，而 `x ∈ ⟦ t ⟧` 加 `⟦ t ⟧ ∈ M` 经传递性恰好给出这一点。教科书证明的承重步被机器定位到字符。
<!--/-->

```agda
  abs₀ : ∀ {n} {φ : Formula SM n} → Δ₀ φ → (δ : SM ^ n)
       → (δ ⊨ᵐ φ) ≡ ((map fst δ) ⊨ᵛ φ)
  abs₀ (δ-∈ {t = t} {u}) δ = cong₂ _∈ˢ_ (⟦⟧-fst t δ) (⟦⟧-fst u δ)
  abs₀ (δ-≐ {t = t} {u}) δ = cong₂ _≈ˢ_ (⟦⟧-fst t δ) (⟦⟧-fst u δ)
  abs₀ (δ-∧ d e) δ = cong₂ _⊓_ (abs₀ d δ) (abs₀ e δ)
  abs₀ (δ-∨ d e) δ = cong₂ _⊔_ (abs₀ d δ) (abs₀ e δ)
  abs₀ (δ-⇒ d e) δ = cong₂ _⇒_ (abs₀ d δ) (abs₀ e δ)
  abs₀ (δ-¬ d)   δ = cong ¬_ (abs₀ d δ)
  abs₀ δ-⊤ δ = refl
  abs₀ δ-⊥ δ = refl
  abs₀ (δ-∀∈ {t = t} {φ = φ} d) δ = ⇔toPath fwd bwd
    where
    tm : SM
    tm = ⟦ t ⟧ᵐ δ
    p : fst tm ≡ ⟦ t ⟧ᵛ (map fst δ)
    p = ⟦⟧-fst t δ
    fwd : ⟨ δ ⊨ᵐ (∀̇∈ t φ) ⟩ → ⟨ (map fst δ) ⊨ᵛ (∀̇∈ t φ) ⟩
    fwd h x hx =
      let hx' = subst (λ s → ⟨ x ∈ˢ s ⟩) (sym p) hx
          xm  = x , trans hx' (snd tm)
      in subst ⟨_⟩ (abs₀ d (xm ∷ δ)) (h xm hx')
    bwd : ⟨ (map fst δ) ⊨ᵛ (∀̇∈ t φ) ⟩ → ⟨ δ ⊨ᵐ (∀̇∈ t φ) ⟩
    bwd g xm hxm =
      subst ⟨_⟩ (sym (abs₀ d (xm ∷ δ)))
            (g (fst xm) (subst (λ s → ⟨ fst xm ∈ˢ s ⟩) p hxm))
  abs₀ (δ-∃∈ {t = t} {φ = φ} d) δ = ⇔toPath fwd bwd
    where
    tm : SM
    tm = ⟦ t ⟧ᵐ δ
    p : fst tm ≡ ⟦ t ⟧ᵛ (map fst δ)
    p = ⟦⟧-fst t δ
    fwd : ⟨ δ ⊨ᵐ (∃̇∈ t φ) ⟩ → ⟨ (map fst δ) ⊨ᵛ (∃̇∈ t φ) ⟩
    fwd = PT.map λ { (xm , hxm , hφ) →
            fst xm
          , subst (λ s → ⟨ fst xm ∈ˢ s ⟩) p hxm
          , subst ⟨_⟩ (abs₀ d (xm ∷ δ)) hφ }
    bwd : ⟨ (map fst δ) ⊨ᵛ (∃̇∈ t φ) ⟩ → ⟨ δ ⊨ᵐ (∃̇∈ t φ) ⟩
    bwd = PT.map λ { (x , hx , hφ) →
            let hx' = subst (λ s → ⟨ x ∈ˢ s ⟩) (sym p) hx
                xm  = x , trans hx' (snd tm)
            in xm , hx' , subst ⟨_⟩ (sym (abs₀ d (xm ∷ δ))) hφ }
```

<!--en-->
## Σ₁ upward, Π₁ downward
<!--zh-->
## Σ₁ 向上，Π₁ 向下
<!--/-->

<!--en-->
The extensions are one constructor each, and note the asymmetry: **neither
consumes transitivity**. An inner existential witness travels outward through
`fst`{.Agda}; an outer universal is instantiated at `fst`{.Agda}. Only Δ₀'s
bounded quantifiers ever needed the hypothesis; the machine states the textbook's
fine print exactly.
<!--zh-->
两条延伸各一个构造子，且注意其不对称：**都不消费传递性**。内层的存在见证经 `fst`{.Agda} 走向外层；外层的全称在 `fst`{.Agda} 处实例化。只有 Δ₀ 的有界量词才需要那条前提；教科书的小字被机器一字不差地陈述出来。
<!--/-->

```agda
  σ₁-up : ∀ {n} {φ : Formula SM n} → Σ₁ φ → (δ : SM ^ n)
        → ⟨ δ ⊨ᵐ φ ⟩ → ⟨ (map fst δ) ⊨ᵛ φ ⟩
  σ₁-up (σ-Δ₀ d) δ = subst ⟨_⟩ (abs₀ d δ)
  σ₁-up (σ-∃ s)  δ = PT.map λ { (xm , h) → fst xm , σ₁-up s (xm ∷ δ) h }

  π₁-down : ∀ {n} {φ : Formula SM n} → Π₁ φ → (δ : SM ^ n)
          → ⟨ (map fst δ) ⊨ᵛ φ ⟩ → ⟨ δ ⊨ᵐ φ ⟩
  π₁-down (π-Δ₀ d) δ = subst ⟨_⟩ (sym (abs₀ d δ))
  π₁-down (π-∀ s)  δ h xm = π₁-down s (xm ∷ δ) (h (fst xm))
```

<!--en-->
## Recap
<!--zh-->
## 小结
<!--/-->

<!--en-->
Transitive classes named, and over them the theorem: `abs₀`{.Agda} makes Δ₀
formulas absolute, with transitivity consumed exactly at the bounded quantifiers;
`σ₁-up`{.Agda} and `π₁-down`{.Agda} extend the transfer one quantifier kind each,
free of the hypothesis. These theorems are pure certificate arithmetic; the
composition that will spend them wholesale is catalogued with the reification
framework at the book's tail.
<!--zh-->
传递类得名，其上是定理本体：`abs₀`{.Agda} 使 Δ₀ 公式绝对，传递性恰在有界量词处被消费；`σ₁-up`{.Agda} 与 `π₁-down`{.Agda} 各以一种量词延伸转移，且不花前提。这些定理是纯粹的证书算术；将要成批花费它们的那次复合，编在书末的 reification 框架里。
<!--/-->
