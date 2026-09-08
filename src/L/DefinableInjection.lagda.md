<!--en-->
# Turning a definable injection into an internal code

An externally described function becomes useful to `L` only when its graph is a set of the model. This chapter turns a definable injective map between sets of `L` into the coded injection used by the counting chapters.
<!--zh-->
# 把可定义单射化为内部编码

一个从外部描述的函数，只有当其图是模型中的集合时才能供 `L` 使用。本章把 `L` 中集合之间的可定义单射化为计数章节所需的编码单射。
<!--ja-->
# 定義可能な単射を内部コードにする

外部から記述した関数を `L` の中で使うには、そのグラフがモデルの集合でなければならない。本章では `L` の集合間の定義可能な単射を、計数の章で使う符号化された単射へ変える。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module L.DefinableInjection {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Coding {ℓ} using ( pr )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans )
open import L.Recursion {ℓ} lem using ( Recursion )
open import L.Recursion.Graph {ℓ} lem
  using () renaming ( module Graph to RecursionGraph )
open import L.Coding.Injection {ℓ} lem using ( injAt; injAt-in )
open import L.Cardinal {ℓ} lem using ( InjCode; InjL )

open import Cubical.Data.Sigma using ( Σ≡Prop )
open import Cubical.HITs.CumulativeHierarchy.Base using ( _∈_ )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ using ( S )
open hPropStructure 𝒮ᵥ using ( _∈ˢ_ )

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans using ( _^_; _⊨ᵐ_ )
open AbsL using ( _^_ ) renaming ( _⊨ᵐ_ to _⊨_ )
```

<!--en-->
## What it means for a function to be definable

A formula defines a function on one set and into another when it holds at the intended value and nowhere else. This interface keeps the graph orientation and its domain and codomain explicit.
<!--zh-->
## 函数可定义的含义

若一条公式在预期函数值处成立且不在别处成立，它就在一个集合上、向另一个集合定义了函数。这个接口明确记录图的方向、定义域与陪域。
<!--ja-->
## 関数が定義可能であるとは何か

ある論理式が意図した関数値で成り立ち、それ以外では成り立たないとき、その論理式は一方の集合から他方への関数を定義する。このインターフェースはグラフの向き、定義域、終域を明示する。
<!--/-->

A function on the members of a set of L, landing in a set of L, whose graph an
object-language formula defines: the formula holds of the function's own value
(`defines`) and of nothing else (`only`). Value first, index second, as
`Recursion.graph`.

```agda
record DefinableMap : Type (ℓ-suc (ℓ-suc ℓ)) where
  field
    dom cod : S
    fn      : (x : S) → ⟨ fst x ∈ˢ fst dom ⟩ → S
    into    : (x : S) (m : ⟨ fst x ∈ˢ fst dom ⟩) → ⟨ fst (fn x m) ∈ˢ fst cod ⟩
    graph   : Formula S 2
    defines : (x : S) (m : ⟨ fst x ∈ˢ fst dom ⟩)
            → ⟨ (fn x m ∷ x ∷ []) ⊨ graph ⟩
    only    : (x : S) (m : ⟨ fst x ∈ˢ fst dom ⟩) (y : S)
            → ⟨ (y ∷ x ∷ []) ⊨ graph ⟩ → y ≡ fn x m
```

<!--en-->
## Encoding graph entries as ordered pairs

The graph is represented as a set, so each input-output entry must first be expressed as an ordered-pair formula. The value occupies the first semantic slot and the input the second, matching the recursion interface.
<!--zh-->
## 把图的表项编码成有序对

图由一个集合表示，因此每个输入输出表项必须先写成有序对公式。值占据第一个语义槽位，输入占据第二个，与递归接口一致。
<!--ja-->
## グラフの項目を順序対として符号化する

グラフは集合として表すため、各入出力項目をまず順序対の論理式で表現する。値を意味論上の第一スロット、入力を第二スロットに置き、再帰のインターフェースに合わせる。
<!--/-->

<!--en-->
## Constructing the graph inside L

Replacement collects the uniquely defined values into a set of ordered pairs in `L`. Its reading supplies totality on the domain, containment of values in the codomain, and agreement with the defining formula.
<!--zh-->
## 在 L 内部构造函数图

替换把唯一确定的值收集成 `L` 中的有序对集合。对该集合的读取给出定义域上的全域性、函数值属于陪域，以及它与定义公式的一致性。
<!--ja-->
## L の内部でグラフを構成する

置換によって、一意に定まる値を `L` の順序対の集合として集める。その読みから、定義域上の全域性、値が終域に属すること、定義する論理式との一致が得られる。
<!--/-->

`Recursion.funct` takes the membership proof, so `fn` fills it as it stands: no
total extension off `dom` and no use of `lem`. The table is the replacement
image (src/L/Recursion.lagda.md, `Of`).

```agda
module Graph (M : DefinableMap) where
  open DefinableMap M public
```

The recursion graph supplies the pair table, its readers, and the first two
conjuncts. The codomain contributes only the range proof below.

```agda
  private
    R : Recursion
    R = record
      { dom = dom ; graph = graph
      ; funct = λ x m → (fn x m , defines x m)
          , λ { (y , h) → Σ≡Prop (λ w → snd ((w ∷ x ∷ []) ⊨ graph)) (sym (only x m y h)) } }

  open RecursionGraph R public
    using ( Mem; isPropMem; F; F-in; F-out; Fib; isPropFib; pair-out; γ; sv; dm )

  ran : (x y : S) → ⟨ pr (fst x) (fst y) ∈ fst F ⟩ → ⟨ fst y ∈ fst cod ⟩
  ran x y h = subst (λ w → ⟨ w ∈ fst cod ⟩) (sym e) (into x m)
    where
    m = fst (pair-out x y h)
    e = snd (pair-out x y h)
```

<!--en-->
## From external injectivity to a coded injection

If the definable function is injective, the graph set satisfies the model's internal injection predicate. The external map is therefore available to later chapters as a coded injection in `L`.
<!--zh-->
## 从外部单射性得到编码单射

若可定义函数是单射，图集合便满足模型内部的单射谓词。因此，后续章节可以把这个外部映射用作 `L` 中的编码单射。
<!--ja-->
## 外部の単射性から符号化された単射へ

定義可能な関数が単射なら、そのグラフ集合はモデル内部の単射述語を満たす。したがって後の章では、この外部写像を `L` における符号化された単射として利用できる。
<!--/-->

```agda
module Inj (M : DefinableMap)
           (inj : (x : S) (m : ⟨ fst x ∈ˢ fst (DefinableMap.dom M) ⟩)
                  (x' : S) (m' : ⟨ fst x' ∈ˢ fst (DefinableMap.dom M) ⟩)
                → fst (DefinableMap.fn M x m) ≡ fst (DefinableMap.fn M x' m')
                → fst x ≡ fst x') where

  open Graph M public

  ij : ⟨ γ ⊨ injAt zero ⟩
  ij = injAt-in zero γ (λ y x x' p q →
    let (m , e)   = pair-out x y p
        (m' , e') = pair-out x' y q
    in inj x m x' m' (sym e ∙ e'))

  code : InjCode F dom cod
  code = sv , dm , ij , ran

  injL : InjL dom cod
  injL = ∣ F , code ∣₁
```
