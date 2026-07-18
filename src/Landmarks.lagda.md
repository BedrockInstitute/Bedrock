# Landmarks

<!--en-->
The trophy case. Each landmark below restates a milestone theorem of the book in
one self-contained signature, with its full bill of assumptions on display, and
names the chapter that proves it. Nothing here is new mathematics; the point is
stable anchors: a reader, or a paper, can cite a landmark without caring where
inside the book its proof lives.
<!--zh-->
奖杯陈列室。下面每座地标都以一条自足的签名重述本书的一项里程碑定理，假设账单全额陈列，并指认证明它的章节。此处没有新数学；要义在于稳定的锚点：读者或论文可以直接引用地标，而不必关心其证明住在书中何处。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

module Landmarks where

open import Base.Prelude
open import Base.Classical using ( LEM )
open import V.Hierarchy using ( 𝒮ᵥ )
import ZF.Model
import V.Model
import L.Constructible
import L.Frontier
import L.Model
```

<!--en-->
## The hierarchy models ZF(C)

Granted resizing, the cumulative hierarchy is a model of ZF (chapter
`V.Model`{.Agda}); the excluded middle redeems the resizing, so the classical
reader assumes only the Part 0 interface; and an independent set-level choice
upgrades the model to ZFC.
<!--zh-->
## 层级满足 ZF(C)

给定降层，累积层级是 ZF 的模型 (章节 `V.Model`{.Agda})；排中律可代付降层，故经典读者只需第零部的接口；再加独立的集合层选择，模型升级为 ZFC。
<!--/-->

```agda
V⊨ZF : ∀ {ℓ : Level} → V.Model.VResizing {ℓ} → ZF.Model.ZFModel (𝒮ᵥ {ℓ})
V⊨ZF = V.Model.VModel.V⊨ZF

V⊨ZF-classical : ∀ {ℓ : Level} (lem : ∀ {ℓ'} → LEM ℓ')
               → ZF.Model.ZFModel (𝒮ᵥ {ℓ})
V⊨ZF-classical lem = V.Model.VModel.V⊨ZF (V.Model.lem→VResizing lem)

V⊨ZFC : ∀ {ℓ : Level} → V.Model.VResizing {ℓ} → V.Model.SetChoice {ℓ}
      → ZF.Model.ZFCModel (𝒮ᵥ {ℓ})
V⊨ZFC = V.Model.VZFC.V⊨ZFC
```

<!--en-->
## The constructible universe models ZFC

The book's main theorem, in its current, honestly conditional form (chapter
`L.Model`{.Agda}): given the excluded-middle interface and the frontier, the
registry of statements the remaining parts still owe, the constructible
structure models ZFC. This landmark upgrades automatically as the frontier
shrinks, and sheds its second hypothesis the day the registry empties. Read
with the previous landmark, it is the semantic form of the relative
consistency of choice: a ZF universe carries a ZFC sub-universe inside it.
<!--zh-->
## 可构造宇宙满足 ZFC

本书的主定理，以其当前的、诚实带条件的形式 (章节 `L.Model`{.Agda})：给定排中律接口与前沿，即余部尚欠陈述的登记簿，可构造结构满足 ZFC。此地标随前沿缩减自动升级，登记簿清空之日卸下第二个假设。与上一座地标合读，这就是选择公理相对一致性的语义形式：ZF 宇宙的体内携带着一个 ZFC 子宇宙。
<!--/-->

```agda
L⊨ZFC : ∀ {ℓ : Level} (lem : ∀ {ℓ'} → LEM ℓ') (F : L.Frontier.Frontier {ℓ})
      → ZF.Model.ZFCModel (L.Constructible.𝒮ʟ {ℓ})
L⊨ZFC = L.Model.L⊨ZFC
```
