# Landmarks

<!--en-->
The trophy case, and it stands at the entrance on purpose. Each landmark below
restates a milestone theorem of the book in one self-contained signature, with
its full bill of assumptions on display, and names the chapter that proves it.
On a first reading nothing here is expected to make sense yet: these signatures
are the destination, and learning to read them, symbol by symbol and assumption
by assumption, is what the rest of the book is for. Come back after each part
lands. For the returning reader the landmarks are stable anchors: a paper can
cite one without caring where inside the book its proof lives.
<!--zh-->
奖杯陈列室，而且是故意摆在入口处的。下面每座地标都以一条自足的签名重述本书的一项里程碑定理，假设账单全额陈列，并指认证明它的章节。初读时这里的一切都不指望被看懂：这些签名就是目的地，而学会逐个符号、逐条假设地读懂它们，正是全书其余部分的任务。每读完一部，请回到这里。对回访的读者，地标是稳定的锚点：论文可以直接引用，而不必关心其证明住在书中何处。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

module Landmarks where

open import Base.Prelude
open import Base.Classical using ( LEM )
open import Base.Choice using ( SetChoice )
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

V⊨ZFC : ∀ {ℓ : Level} → V.Model.VResizing {ℓ} → SetChoice ℓ
      → ZF.Model.ZFCModel (𝒮ᵥ {ℓ})
V⊨ZFC = V.Model.VZFC.V⊨ZFC
```

<!--en-->
And by Diaconescu's theorem (chapter `Base.Choice`{.Agda}), the whole bill
compresses into one hypothesis: level-polymorphic set choice alone.
<!--zh-->
再经 Diaconescu 定理 (章节 `Base.Choice`{.Agda})，整份账单压成一个假设：单凭层级多态的集合层选择。
<!--/-->

```agda
V⊨ZFC-fromChoice : ∀ {ℓ : Level} → (∀ {ℓ'} → SetChoice ℓ')
                 → ZF.Model.ZFCModel (𝒮ᵥ {ℓ})
V⊨ZFC-fromChoice = V.Model.V⊨ZFC-fromChoice
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
