<!--en-->
# Main theorems

This chapter collects the development’s three principal model-theoretic results with their complete assumptions: the cumulative hierarchy models ZF and, under choice, ZFC; the constructible universe models ZFC; and the constructible universe satisfies GCH.
<!--zh-->
# 主要定理

本章汇集整个开发的三项主要模型论结果及其完整假设：累积层级是 ZF 的模型，并在选择下成为 ZFC 的模型；可构造宇宙是 ZFC 的模型；可构造宇宙满足 GCH。
<!--ja-->
# 主要定理

本章は、この展開の三つの主要なモデル論的結果とその仮定をまとめます。累積階層は ZF のモデルであり、選択の下では ZFC のモデルです。構成可能宇宙は ZFC のモデルであり、さらに GCH を満たします。
<!--/-->



```agda
{-# OPTIONS --cubical --safe --guardedness #-}

module Landmarks where

open import Base.Prelude
open import Base.Impredicativity using ( Impredicativity )
open import Base.Classical using ( LEM )
open import Base.Choice using ( SetChoice )
open import V.Hierarchy using ( 𝒮ᵥ )
open import FOL.ZFModel using ( isZFModel; isZFCModel )
open import L.Constructible using ( 𝒮ʟ )
import V.Model
import L.Model
import L.GCH
import L.GCH.Theorem
```

<!--en-->
## The hierarchy models ZF(C)

The main result is classical: granted one instance of the excluded middle at the
model's own truth level, the cumulative hierarchy is a model of ZF (chapter
`V.Model`{.Agda}). The precise version carries the hypothesis as a suffix
and requires only the foundational impredicativity package; and by Diaconescu's theorem
(chapter `Base.Choice`{.Agda}), one instance of set-level choice yields
ZFC.
<!--zh-->
## 层级满足 ZF(C)

主要结果采用经典形式：给定模型自身真值层上的排中律，累积层级是 ZF 的模型 (章节 `V.Model`{.Agda})。带假设后缀的精确版本只要求基础章节打包的非直谓性接口。再经 Diaconescu 定理 (章节 `Base.Choice`{.Agda})，一份集合层选择即可得到 ZFC。
<!--ja-->
## 累積階層は ZF (C) のモデル

累積階層は、命題リサイズをまとめた非可述性から ZF のモデルになります。排中律はその仮定を導き、集合レベルの選択はさらに選択公理を与えるため、同じ階層について ZFC のモデルも得られます。
<!--/-->

```agda
V⊨ZF : ∀ {ℓ : Level} → LEM (ℓ-suc ℓ) → isZFModel (𝒮ᵥ {ℓ})
V⊨ZF = V.Model.V⊨ZF

V⊨ZF-impredicative : ∀ {ℓ : Level} → Impredicativity ℓ → isZFModel (𝒮ᵥ {ℓ})
V⊨ZF-impredicative = V.Model.VModel.V⊨ZF-impredicative

V⊨ZFC : ∀ {ℓ : Level} → SetChoice (ℓ-suc ℓ) → isZFCModel (𝒮ᵥ {ℓ})
V⊨ZFC = V.Model.V⊨ZFC
```

<!--en-->
## The constructible universe models ZFC

The book's main theorem (chapter `L.Model`{.Agda}): given one instance of the
excluded middle at the model's truth level, the constructible structure models
ZFC. There is a single hypothesis, and it is the same one used in the previous landmark. Read with the previous landmark, it is the semantic form of
the relative consistency of choice: a ZF universe carries a ZFC sub-universe
inside it.
<!--zh-->
## 可构造宇宙满足 ZFC

本书的主定理 (章节 `L.Model`{.Agda}) 是：给定模型真值层上的排中律，可构造结构满足 ZFC。它只有这一个假设，并且与上一项结果使用同一假设。与上一项合看，这给出选择公理相对一致性的语义形式：ZF 宇宙内部包含一个 ZFC 子宇宙。
<!--ja-->
## 構成可能宇宙は ZFC のモデル

モデルの真理値レベルで一つの排中律を仮定すると、構成可能構造 `𝒮ʟ` は ZFC を満たします。累積階層の ZF モデルと合わせると、これは選択公理の相対無矛盾性を意味論的に表します。
<!--/-->

```agda
L⊨ZFC : ∀ {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) → isZFCModel (𝒮ʟ {ℓ})
L⊨ZFC = L.Model.L⊨ZFC
```

<!--en-->
## The constructible universe models GCH

The second result (chapter `L.GCH.Theorem`{.Agda}): under the same single
hypothesis, the constructible structure satisfies the generalized continuum
hypothesis, stated in L's own terms: for every infinite cardinal κ of L, the
model's power set of κ and the successor cardinal of κ inject into each other by
injections that are themselves elements of L (chapter `L.GCH`{.Agda} states it).
<!--zh-->
## 可构造宇宙满足 GCH

第二个结果 (章节 `L.GCH.Theorem`{.Agda})：在同一唯一假设下，可构造结构满足广义连续统假设，且以 L 自己的语言陈述：对 L 的每个无穷基数 κ，模型自身的 κ 的幂集与 κ 的后继基数之间存在互相的单射，而这些单射本身是 L 的元素 (章节 `L.GCH`{.Agda} 给出陈述)。
<!--ja-->
## 構成可能宇宙は GCH を満たす

同じ一つの排中律の下で、`L` の各無限基数について、その冪集合と後続基数の間に `L` の要素である双方向の単射が存在します。これが構成可能宇宙における GCH の内部的な主張です。
<!--/-->

```agda
L⊨GCH : ∀ {ℓ : Level} (lem : LEM (ℓ-suc ℓ))
      → L.GCH.GCHStatement lem (L.Model.L⊨ZF lem)
L⊨GCH lem = L.GCH.Theorem.L⊨GCH lem
```
