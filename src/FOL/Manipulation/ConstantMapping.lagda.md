<!--en-->
# Mapping constants

A function between constant domains acts on syntax by replacing every constant and leaving every variable untouched. This chapter defines that action on terms and formulas, proves functoriality under composition, and embeds parameter-free syntax into any constant domain.
<!--zh-->
# 映射常元

常元域之间的函数通过替换每个常元、保持每个变量不变而作用于语法。本章定义它对词项与公式的作用，证明它对复合的函子性，并把无参语法嵌入任意常元域。
<!--ja-->
# 定数の写像

定数域の間の関数は、各定数を置き換え、変数をそのままにすることで構文に作用します。本章では項と論理式への作用を定義し、合成に関する関手性を証明し、パラメータを持たない構文を任意の定数域へ埋め込みます。
<!--/-->

<!--en-->
The constant domain is a parameter of first-order syntax. This chapter gives its
functorial action: maps relabel constants in terms and formulas, composition is
preserved, and parameter-free formulas enter every constant domain.
<!--zh-->
常元域是第一阶语法的参数。本章给出它的函子作用：映射在项与公式中重标常元，复合得以保持，而无参公式可进入任意常元域。
<!--/-->



```agda
{-# OPTIONS --cubical --safe --guardedness #-}

module FOL.Manipulation.ConstantMapping where

open import Base.Prelude
open import FOL.Syntax using
  ( Term; con; var; Formula; _∈̇_; _≐_; _∧̇_; _∨̇_; _⇒̇_; ⊥̇; ∃̇_; ∀̇_; ∀̇∈; ∃̇∈ )
import Cubical.Data.Empty as Empty
```

<!--en-->
## Syntax level

The syntax is functorial in its constant domain: a map `K → K'` pushes through a term or formula, relabelling constants while preserving de Bruijn variables and logical structure. The identity and composition laws then follow by structural induction.
<!--zh-->
## 语法层

语法对常元域是函子式的：映射 `K → K'` 贯穿词项或公式，对常元改名，同时保持 de Bruijn 变量和逻辑结构。恒等映射与复合的法则随即由结构归纳得到。
<!--ja-->
## 構文への作用

`mapTm`{.Agda} と `mapFo`{.Agda} は定数にだけ関数を適用し、de Bruijn 変数と論理式の構造を保存します。恒等写像と合成に関する法則は構造帰納法で従います。
<!--/-->

```agda
mapTm : ∀ {ℓ ℓ'} {K : Type ℓ} {K' : Type ℓ'} {n}
      → (K → K') → Term K n → Term K' n
mapTm f (con k) = con (f k)
mapTm f (var i) = var i

mapFo : ∀ {ℓ ℓ'} {K : Type ℓ} {K' : Type ℓ'} {n}
      → (K → K') → Formula K n → Formula K' n
mapFo f (t ∈̇ u)  = mapTm f t ∈̇ mapTm f u
mapFo f (t ≐ u)  = mapTm f t ≐ mapTm f u
mapFo f (φ ∧̇ ψ)  = mapFo f φ ∧̇ mapFo f ψ
mapFo f (φ ∨̇ ψ)  = mapFo f φ ∨̇ mapFo f ψ
mapFo f (φ ⇒̇ ψ)  = mapFo f φ ⇒̇ mapFo f ψ
mapFo f ⊥̇        = ⊥̇
mapFo f (∃̇ φ)    = ∃̇ mapFo f φ
mapFo f (∀̇ φ)    = ∀̇ mapFo f φ
mapFo f (∀̇∈ t φ) = ∀̇∈ (mapTm f t) (mapFo f φ)
mapFo f (∃̇∈ t φ) = ∃̇∈ (mapTm f t) (mapFo f φ)
```

<!--en-->
Two such maps in a row are one map. The first concrete use comes when the coding
bridge sends constants from the members of a carrier into its inner structure
and then into the language of `L`: `mapFo-comp`{.Agda} erases that intermediate
constant domain. The same need returns in the later coding, choice, and GCH
chapters, so the law belongs to the syntax-level interface rather than to any
one application. Both term cases are `refl`{.Agda}, because a variable carries
no constant and a constant is relabelled by application.
<!--zh-->
连着两次这样的映射就是一次映射。它第一次具体登场时，编码桥先把常元从载体的成员送入其内层结构，再送入 `L` 的语言；`mapFo-comp`{.Agda} 消去的正是这个中间常元域。后续编码、选择与 GCH 各章还会反复遇到同一需要，故这条法则属于句法层接口，而不属于任何一个应用。两个词项情形都是 `refl`{.Agda}，因为变元不携带常元，而常元的变换就是把映射施用上去。
<!--/-->

```agda
mapTm-comp : ∀ {ℓ ℓ' ℓ''} {K : Type ℓ} {K' : Type ℓ'} {K'' : Type ℓ''} {n}
             (f : K → K') (g : K' → K'') (t : Term K n)
           → mapTm g (mapTm f t) ≡ mapTm (λ k → g (f k)) t
mapTm-comp f g (con k) = refl
mapTm-comp f g (var i) = refl

mapFo-comp : ∀ {ℓ ℓ' ℓ''} {K : Type ℓ} {K' : Type ℓ'} {K'' : Type ℓ''} {n}
             (f : K → K') (g : K' → K'') (φ : Formula K n)
           → mapFo g (mapFo f φ) ≡ mapFo (λ k → g (f k)) φ
mapFo-comp f g (t ∈̇ u)  = cong₂ _∈̇_ (mapTm-comp f g t) (mapTm-comp f g u)
mapFo-comp f g (t ≐ u)  = cong₂ _≐_ (mapTm-comp f g t) (mapTm-comp f g u)
mapFo-comp f g (φ ∧̇ ψ)  = cong₂ _∧̇_ (mapFo-comp f g φ) (mapFo-comp f g ψ)
mapFo-comp f g (φ ∨̇ ψ)  = cong₂ _∨̇_ (mapFo-comp f g φ) (mapFo-comp f g ψ)
mapFo-comp f g (φ ⇒̇ ψ)  = cong₂ _⇒̇_ (mapFo-comp f g φ) (mapFo-comp f g ψ)
mapFo-comp f g ⊥̇        = refl
mapFo-comp f g (∃̇ φ)    = cong ∃̇_ (mapFo-comp f g φ)
mapFo-comp f g (∀̇ φ)    = cong ∀̇_ (mapFo-comp f g φ)
mapFo-comp f g (∀̇∈ t φ) = cong₂ ∀̇∈ (mapTm-comp f g t) (mapFo-comp f g φ)
mapFo-comp f g (∃̇∈ t φ) = cong₂ ∃̇∈ (mapTm-comp f g t) (mapFo-comp f g φ)
```

<!--en-->
The most-travelled instance: entering a constant domain from **no** constants.
The syntax chapter introduced the **parameter-free formulas**, the data axis
with the empty type as constant domain; like sentences they bear no separate
name, the type `Formula (⊥* {ℓ}) n` says it whole. From the empty type anything
follows, the library's eliminator `Empty.rec*`{.Agda} says so, and relabelling
along it embeds a parameter-free formula into the syntax over any domain
whatsoever.
<!--zh-->
走动最勤的实例：从**没有**常元的域进入任何常元域。语法章介绍过**无参公式**，即以空类型为常元域的数据轴；与句子一样，本书不为它另设名字，类型 `Formula (⊥* {ℓ}) n` 已经说完全部。从空类型可以推出一切，库的消去子 `Empty.rec*`{.Agda} 说的正是这句话，沿它变换，无参公式便嵌入任意常元域上的语法。
<!--/-->

```agda
embed : ∀ {ℓ ℓ'} {K : Type ℓ'} {n} → Formula (⊥* {ℓ}) n → Formula K n
embed = mapFo Empty.rec*
```

<!--en-->
## Recap

`mapTm` and `mapFo` express the syntax-level action of a map of constant domains;
`mapFo-comp` gives functoriality, and `embed` is the parameter-free instance.
<!--zh-->
## 小结

`mapTm` 与 `mapFo` 表达常元域映射在语法层的作用；`mapFo-comp` 给出函子性，`embed` 是无参实例。
<!--ja-->
## まとめ

定数の写像は項と論理式の形および自由変数の個数を変えません。合成則と空の定数域からの埋め込みが、後の定数改名とパラメータ抽象化の基礎になります。
<!--/-->
