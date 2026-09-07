<!--en-->
# Variable renaming

A map between finite variable contexts acts on terms and formulas by renaming free variables while leaving constants fixed. The accompanying agreement relation on environments gives one semantic theorem that covers weakening, exchange, and contraction.
<!--zh-->
# 变量改名

有限变量语境之间的映射通过改名自由变量作用于词项与公式，同时保持常元不变。环境上的相符关系给出一条语义定理，统一涵盖弱化、交换与收缩。
<!--ja-->
# 変数の改名

有限な変数文脈の間の写像は、定数を固定したまま自由変数を改名して項と論理式へ作用します。環境の一致関係を用いる一つの意味論的定理が、弱化、交換、縮約をまとめて扱います。
<!--/-->

<!--en-->
The syntax chapter pointed out an absence: no substitution, no weakening. The
quantifier clauses take bodies in an extended context directly, so the classical
apparatus for moving variables around never has to exist. What little variable
motion the book does need is covered by one device: **renaming**, a map
`ρ : Fin n → Fin m` pushed through a formula, with a single correctness theorem
that handles weakening, exchange, and contraction in one stroke.
<!--zh-->
语法章点过一处缺席：没有替换，没有弱化。量词子句直接取扩展语境中的公式体，经典的那套变量搬运装置根本无需存在。本书确实需要的那一点变量挪动，由一个机件包办：**改名**，即沿公式推送一个映射 `ρ : Fin n → Fin m`，配一条正确性定理，弱化、交换、收缩一并了断。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

module FOL.Manipulation.Renaming where

open import Base.Prelude
open import Base.Truth
open import FOL.ZFStructure using ( ZFStructure )
open import FOL.Syntax using
  ( Term; con; var
  ; Formula; _∈̇_; _≐_; _∧̇_; _∨̇_; _⇒̇_; ⊥̇; ∃̇_; ∀̇_; ∀̇∈; ∃̇∈ )
import FOL.Semantics
```

<!--en-->
## The syntactic layer

`renameTm`{.Agda} and `renameFo`{.Agda} push a map `Fin n → Fin m` through the syntax. Beneath a binder, `liftρ`{.Agda} fixes the newly bound variable and shifts the old variables through the given map.
<!--zh-->
## 语法层

`renameTm`{.Agda} 与 `renameFo`{.Agda} 将映射 `Fin n → Fin m` 贯穿语法。在约束子之下，`liftρ`{.Agda} 固定新约束的变量，并通过给定映射移动原有变量。
<!--ja-->
## 構文の水準

`renameTm`{.Agda} と `renameFo`{.Agda} は写像 `Fin n → Fin m` を構文へ通します。束縛子の下では、`liftρ`{.Agda} が新しく束縛された変数を固定し、元の変数を与えられた写像で移します。
<!--/-->



```agda
liftρ : ∀ {n m} → (Fin n → Fin m) → Fin (suc n) → Fin (suc m)
liftρ ρ zero    = zero
liftρ ρ (suc i) = suc (ρ i)

renameTm : ∀ {ℓc} {K : Type ℓc} {n m} → (Fin n → Fin m) → Term K n → Term K m
renameTm ρ (con k) = con k
renameTm ρ (var i) = var (ρ i)

renameFo : ∀ {ℓc} {K : Type ℓc} {n m} → (Fin n → Fin m) → Formula K n → Formula K m
renameFo ρ (t ∈̇ u)  = renameTm ρ t ∈̇ renameTm ρ u
renameFo ρ (t ≐ u)  = renameTm ρ t ≐ renameTm ρ u
renameFo ρ (φ ∧̇ ψ)  = renameFo ρ φ ∧̇ renameFo ρ ψ
renameFo ρ (φ ∨̇ ψ)  = renameFo ρ φ ∨̇ renameFo ρ ψ
renameFo ρ (φ ⇒̇ ψ)  = renameFo ρ φ ⇒̇ renameFo ρ ψ
renameFo ρ ⊥̇        = ⊥̇
renameFo ρ (∃̇ φ)    = ∃̇ renameFo (liftρ ρ) φ
renameFo ρ (∀̇ φ)    = ∀̇ renameFo (liftρ ρ) φ
renameFo ρ (∀̇∈ t φ) = ∀̇∈ (renameTm ρ t) (renameFo (liftρ ρ) φ)
renameFo ρ (∃̇∈ t φ) = ∃̇∈ (renameTm ρ t) (renameFo (liftρ ρ) φ)
```

<!--en-->
## The semantic layer

`Agrees ρ γ δ`{.Agda} says that the two environments assign equal values to variables related by `ρ`. This condition survives extension beneath a binder, and structural induction then proves equal term denotations and equal satisfaction for renamed formulas.
<!--zh-->
## 语义层

`Agrees ρ γ δ`{.Agda} 表示两个环境为经 `ρ` 对应的变量指派相等取值。该条件在约束子下扩展环境时仍保持，结构归纳遂证明改名后词项释义与公式满足关系相等。
<!--ja-->
## 意味論の水準

`Agrees ρ γ δ`{.Agda} は、`ρ` で対応する変数に二つの環境が等しい値を割り当てることを表します。この条件は束縛子の下で環境を拡張しても保たれ、構造帰納法によって改名後の項の表示と論理式の充足関係が等しいと分かります。
<!--/-->



```agda
module Sat {ℓ ℓ'} (𝕋 : TruthAlgebra ℓ ℓ') (𝒮 : ZFStructure 𝕋)
           {ℓc} {K : Type ℓc} (ι : K → ZFStructure.S 𝒮) where

  open TruthAlgebra 𝕋
  open ZFStructure 𝒮

  private module Sem = FOL.Semantics 𝕋 𝒮
  open Sem using ( _^_ )
  open Sem.At K ι using ( _⊨_; ⟦_⟧ )

  Agrees : ∀ {n m} → (Fin n → Fin m) → S ^ m → S ^ n → Type ℓ
  Agrees ρ γ δ = ∀ i → lookup (ρ i) γ ≡ lookup i δ
```

<!--en-->
The correctness theorem: a renamed formula in the big environment means the same
as the original in the small one. Terms first, then the usual induction, every
case a congruence, the binder cases stepping through `agrees∷`{.Agda}. Weakening
(inserting an unused variable), exchange, and contraction are all instances,
obtained by choosing `ρ`.
<!--zh-->
正确性定理：变换后的公式在大环境中的含义，与原公式在小环境中的相同。先词项，然后照例归纳，每个情形一条同余，约束子情形踩着 `agrees∷`{.Agda} 过河。弱化 (插入未用的变量)、交换、收缩全是特例，取相应的 `ρ` 即得。
<!--/-->

```agda
  agrees∷ : ∀ {n m} {ρ : Fin n → Fin m} {γ : S ^ m} {δ : S ^ n}
            (x : S) → Agrees ρ γ δ → Agrees (liftρ ρ) (x ∷ γ) (x ∷ δ)
  agrees∷ x ag zero    = refl
  agrees∷ x ag (suc i) = ag i

  ⟦⟧-rename : ∀ {n m} (ρ : Fin n → Fin m) (t : Term K n)
              (γ : S ^ m) (δ : S ^ n) → Agrees ρ γ δ
            → ⟦ renameTm ρ t ⟧ γ ≡ ⟦ t ⟧ δ
  ⟦⟧-rename ρ (con k) γ δ ag = refl
  ⟦⟧-rename ρ (var i) γ δ ag = ag i

  ⊨-rename : ∀ {n m} (ρ : Fin n → Fin m) (φ : Formula K n)
             (γ : S ^ m) (δ : S ^ n) → Agrees ρ γ δ
           → (γ ⊨ renameFo ρ φ) ≡ (δ ⊨ φ)
  ⊨-rename ρ (t ∈̇ u)  γ δ ag = cong₂ _∈ˢ_ (⟦⟧-rename ρ t γ δ ag) (⟦⟧-rename ρ u γ δ ag)
  ⊨-rename ρ (t ≐ u)  γ δ ag = cong₂ _≈ˢ_ (⟦⟧-rename ρ t γ δ ag) (⟦⟧-rename ρ u γ δ ag)
  ⊨-rename ρ (φ ∧̇ ψ)  γ δ ag = cong₂ _⊓_ (⊨-rename ρ φ γ δ ag) (⊨-rename ρ ψ γ δ ag)
  ⊨-rename ρ (φ ∨̇ ψ)  γ δ ag = cong₂ _⊔_ (⊨-rename ρ φ γ δ ag) (⊨-rename ρ ψ γ δ ag)
  ⊨-rename ρ (φ ⇒̇ ψ)  γ δ ag = cong₂ _⇒_ (⊨-rename ρ φ γ δ ag) (⊨-rename ρ ψ γ δ ag)
  ⊨-rename ρ ⊥̇        γ δ ag = refl
  ⊨-rename ρ (∃̇ φ)    γ δ ag = cong (⋁ S) (funExt (λ x →
    ⊨-rename (liftρ ρ) φ (x ∷ γ) (x ∷ δ) (agrees∷ x ag)))
  ⊨-rename ρ (∀̇ φ)    γ δ ag = cong (⋀ S) (funExt (λ x →
    ⊨-rename (liftρ ρ) φ (x ∷ γ) (x ∷ δ) (agrees∷ x ag)))
  ⊨-rename ρ (∀̇∈ t φ) γ δ ag = cong (⋀ S) (funExt (λ x →
    cong₂ _⇒_ (cong (x ∈ˢ_) (⟦⟧-rename ρ t γ δ ag))
              (⊨-rename (liftρ ρ) φ (x ∷ γ) (x ∷ δ) (agrees∷ x ag))))
  ⊨-rename ρ (∃̇∈ t φ) γ δ ag = cong (⋁ S) (funExt (λ x →
    cong₂ _⊓_ (cong (x ∈ˢ_) (⟦⟧-rename ρ t γ δ ag))
              (⊨-rename (liftρ ρ) φ (x ∷ γ) (x ∷ δ) (agrees∷ x ag))))
```

<!--en-->
## Recap

Variable renaming consists of the syntactic maps, environment agreement, and the theorem `⊨-rename`{.Agda}. Choosing the context map specializes this single interface to weakening, exchange, or contraction.
<!--zh-->
## 小结

变量改名由语法映射、环境相符关系与定理 `⊨-rename`{.Agda} 组成。选择不同语境映射，即可将这一统一接口特化为弱化、交换或收缩。
<!--ja-->
## まとめ

変数の改名は、構文写像、環境の一致、定理 `⊨-rename`{.Agda} からなります。文脈の写像を選ぶことで、この一つのインターフェースを弱化、交換、縮約へ特殊化できます。
<!--/-->
