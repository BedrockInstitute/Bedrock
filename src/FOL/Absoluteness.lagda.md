<!--en-->
# Absoluteness

A formula is absolute when it has the same truth value in a structure and in a transitive substructure containing its parameters. This chapter proves that every Δ₀ formula is absolute, then derives the one-way preservation laws for Σ₁ and Π₁ formulas.
<!--zh-->
# 绝对性

若一条公式在某结构与包含其参数的传递子结构中具有相同真值，就称它是绝对的。本章证明每条 Δ₀ 公式都具有绝对性，再推出 Σ₁ 与 Π₁ 公式的单向保持律。
<!--ja-->
# 絶対性

論理式が、そのパラメータを含む構造と推移的部分構造で同じ真理値を持つとき、その論理式は絶対的です。本章ではすべての Δ₀ 論理式の絶対性を証明し、Σ₁ と Π₁ の一方向の保存則を導きます。
<!--/-->

<!--en-->
The Levy witnesses earn their keep. The scene is the one the constructible-universe chapters will play out at
scale: a model, a sub-world `𝒮 ↾ M` carved out by a class, and formulas asked on
both sides. The one condition that tames the passage, **transitivity** of `M`
(members of members stay in `M`, exactly what the empty question of the previous
chapter needed), was minted with the structures; this chapter spends it,
mechanizing the textbook theorem:
**Δ₀ formulas are absolute between a transitive class and the universe**, with the
Σ₁-upward and Π₁-downward transfers as cheap extensions, and, as the capstone, the
one-line composition that turns an inner graded representation into outer
satisfaction.
<!--zh-->
Lévy 见证开始挣饭钱。这里的场景正是可构造宇宙诸章将要大规模上演的那一幕：一个模型，一个由类裁出的子世界 `𝒮 ↾ M`，同一批公式两侧各问一遍。驯服这次通行的唯一条件，`M` 的**传递性** (成员的成员不出 `M`，恰是上一章那个空集之问所需要的)，已随结构一章铸下；本章将它花出，把教科书定理机械化：**Δ₀ 公式在传递类与全宇宙之间绝对**，Σ₁ 向上、Π₁ 向下两条转移作为廉价延伸。
<!--/-->



```agda
{-# OPTIONS --cubical --safe --guardedness #-}

module FOL.Absoluteness where

open import Base.Prelude
open import Base.Truth
open import FOL.ZFStructure using ( ZFStructure; Transitive; _↾_ )
open import FOL.Syntax using ( Term; con; var; Formula; ∀̇∈; ∃̇∈ )
open import FOL.LevyHierarchy using
  ( Δ₀; δ-∈; δ-≐; δ-∧; δ-∨; δ-⇒; δ-⊥; δ-∀∈; δ-∃∈
  ; Σ₁; σ-Δ₀; σ-∃; Π₁; π-Δ₀; π-∀ )
import FOL.Semantics
open import Cubical.Data.Vec using ( map )
open import Cubical.Functions.Logic using ( ⇔toPath )
import Cubical.HITs.PropositionalTruncation as PT
```

<!--en-->
## The setting: one syntax, two semantics

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
## 设置：一套语法，两套语义

固定环境结构 `𝒮` 与传递类 `M`；内层世界是限制结构 `𝒮 ↾ M`，其载体 `SM` 由 `M` 的成员组成。语法取 `K := SM`：公式中的常元只能是 `M` 的成员，参数须满足的规则由类型强制保证。同一族公式于是得到**两套语义**：在外层 `𝒮` 中求值，常元经 `fst`{.Agda} 解释；在内层 `𝒮 ↾ M` 中求值，常元即其自身。相对化因此不是句法操作，而是同一泛型语义的两次实例化；满足符号上的上标 `ᵛ` 与 `ᵐ` 读作「在哪里求值」。
<!--ja-->
## 設定：一つの構文と二つの意味論

同じ論理式を、周囲の構造 `𝒮` と推移的クラスへの制限 `𝒮M` の二箇所で解釈します。部分構造の台は Σ 型で表され、第一射影を通じて周囲の構造と同じ対象をパラメータとして読みます。
<!--/-->



```agda
module Single {ℓ} (𝒮 : ZFStructure (hPropAlgebra ℓ))
              (M : ZFStructure.S 𝒮 → hProp ℓ)
              (trans : Transitive 𝒮 M) where

  open TruthAlgebra (hPropAlgebra ℓ)
  open ZFStructure 𝒮

  SM : Type ℓ
  SM = Σ[ x ∈ S ] (x ∈ᶜ M)

  𝒮M : ZFStructure (hPropAlgebra ℓ)
  𝒮M = 𝒮 ↾ M

  module SemV = FOL.Semantics (hPropAlgebra ℓ) 𝒮
  module SemM = FOL.Semantics (hPropAlgebra ℓ) 𝒮M

  open SemV using ( _^_ ) public

  open module V = SemV.At SM fst public
    renaming ( _⊨_ to _⊨ᵛ_ ; ⟦_⟧ to ⟦_⟧ᵛ )
  open module Mse = SemM.At SM id public
    renaming ( _⊨_ to _⊨ᵐ_ ; ⟦_⟧ to ⟦_⟧ᵐ )
```

<!--en-->
Inner and outer environments are related by projecting every entry; two private
dictionary lemmas settle the term level, where a constant is its own value on both
sides and a variable is a lookup.
<!--zh-->
内外环境经逐项投影相互关联；词项层由两条私有的引理处理：常元在两侧都取自身为值，变量只需一次查表。
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

One induction over the Δ₀ witness. The connective cases are congruences; the
atoms go through the term lemmas (equality is the structure field `≈ˢ` on both
sides, so even that case is a `cong₂`{.Agda}). The transitivity hypothesis is
consumed **only in the two bounded-quantifier cases**, and there lies the whole
mathematical content: outward, a member `x` of `⟦ t ⟧` must be re-packed as a
member of `M`, and `x ∈ ⟦ t ⟧` together with `⟦ t ⟧ ∈ᶜ M` yields exactly that by
transitivity. The machine locates the textbook proof's load-bearing step to the
character.
<!--zh-->
## 定理

对 Δ₀ 见证作归纳。联结词情形都是同余；原子情形使用词项引理 (等词两侧都是结构字段 `≈ˢ`，因此也归于 `cong₂`{.Agda})。传递性前提**只在两个有界量词情形使用**，全部数学内容都在这里：从内层转到外层时，`⟦ t ⟧` 的成员 `x` 必须重新给出为 `M` 的成员，而 `x ∈ ⟦ t ⟧` 与 `⟦ t ⟧ ∈ᶜ M` 经传递性正好提供这一事实。机器检查由此准确定位了教科书证明的关键步骤。
<!--ja-->
## Δ₀ 絶対性定理

Δ₀ 論理式では量化子が集合によって有界です。推移性が有界量化の範囲を一致させるため、構造帰納法により内部と外部の充足関係が等しいことを証明できます。
<!--/-->



```agda
  abs₀ : ∀ {n} {φ : Formula SM n} → Δ₀ φ → (δ : SM ^ n)
       → (δ ⊨ᵐ φ) ≡ ((map fst δ) ⊨ᵛ φ)
  abs₀ (δ-∈ {t = t} {u}) δ = cong₂ _∈ˢ_ (⟦⟧-fst t δ) (⟦⟧-fst u δ)
  abs₀ (δ-≐ {t = t} {u}) δ = cong₂ _≈ˢ_ (⟦⟧-fst t δ) (⟦⟧-fst u δ)
  abs₀ (δ-∧ d e) δ = cong₂ _⊓_ (abs₀ d δ) (abs₀ e δ)
  abs₀ (δ-∨ d e) δ = cong₂ _⊔_ (abs₀ d δ) (abs₀ e δ)
  abs₀ (δ-⇒ d e) δ = cong₂ _⇒_ (abs₀ d δ) (abs₀ e δ)
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

The extensions are one constructor each, and note the asymmetry: **neither
consumes transitivity**. An inner existential witness travels outward through
`fst`{.Agda}; an outer universal is instantiated at `fst`{.Agda}. Only Δ₀'s
bounded quantifiers ever needed the hypothesis; the machine states the textbook's
fine print exactly.
<!--zh-->
## Σ₁ 向上，Π₁ 向下

两条延伸各带一个构造子，且注意其不对称：**都不使用传递性前提**。内层的存在见证经 `fst`{.Agda} 送到外层；外层的全称在 `fst`{.Agda} 处实例化。只有 Δ₀ 的有界量词才需要那条前提；教科书里以小字注明的条件，在这里被逐字写成前提。
<!--ja-->
## Σ₁ は上向き、Π₁ は下向き

Σ₁ の存在証人が部分構造にあれば周囲の構造でも使えるので真理は上向きに保存されます。否定を通して、Π₁ の真理は周囲から部分構造へ下向きに保存されます。
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

Transitive classes named, and over them the theorem: `abs₀`{.Agda} makes Δ₀
formulas absolute, with transitivity consumed exactly at the bounded quantifiers;
`σ₁-up`{.Agda} and `π₁-down`{.Agda} extend the transfer one quantifier kind each,
free of the hypothesis. These theorems are pure arithmetic on the Levy witnesses; the
composition that will spend them wholesale is catalogued with the reification
framework at the book's tail.
<!--zh-->
## 小结

传递类一名即由此而来。定理本体如下：`abs₀`{.Agda} 使 Δ₀ 公式绝对，传递性恰在有界量词处被使用；`σ₁-up`{.Agda} 与 `π₁-down`{.Agda} 各以一种量词延伸完成转移，且不需要前提。这些定理是对 Lévy 见证的纯粹算术；后文将成批使用它们的那次复合，编排在书末的 reification 框架里。
<!--ja-->
## まとめ

推移的部分構造は Δ₀ 論理式の真理値を完全に保ちます。この双方向の絶対性から、量化子を一つ加えた Σ₁ の上向き保存と Π₁ の下向き保存が得られます。
<!--/-->
