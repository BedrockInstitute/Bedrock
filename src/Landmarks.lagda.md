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
open import Base.Classical using ( LEM; Impredicativity )
open import Base.Choice using ( SetChoice )
open import V.Hierarchy using ( 𝒮ᵥ )
open import ZF using ( isZFModel; isZFCModel )
open import L.Constructible using ( 𝒮ʟ )
import V.Model
import L.Frontier
import L.Model
```

<!--en-->
## The hierarchy models ZF(C)

The headline is classical: granted one instance of the excluded middle, at the
model's own truth level, the cumulative hierarchy is a model of ZF (chapter
`V.Model`{.Agda}). Its exact-price form carries the hypothesis as a suffix,
charging only Part 0's impredicativity packing; and by Diaconescu's theorem
(chapter `Base.Choice`{.Agda}), one instance of set-level choice funds the
upgrade all the way to ZFC.
<!--zh-->
## 层级满足 ZF(C)

主打名是经典版：给定模型自身真值层上的一份排中律，累积层级是 ZF 的模型 (章节 `V.Model`{.Agda})。其精确价格版以后缀携带假设，只收第零部的非直谓性打包；再经 Diaconescu 定理 (章节 `Base.Choice`{.Agda})，一份集合层选择就资助到 ZFC。
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

The book's main theorem, in its current, honestly conditional form (chapter
`L.Model`{.Agda}): given one instance of the excluded middle at the model's truth level, and the
frontier, the registry of statements the remaining parts still owe, the
constructible structure models ZFC. This landmark upgrades automatically as the frontier
shrinks, and sheds its second hypothesis the day the registry empties. Read
with the previous landmark, it is the semantic form of the relative
consistency of choice: a ZF universe carries a ZFC sub-universe inside it.
<!--zh-->
## 可构造宇宙满足 ZFC

本书的主定理，以其当前的、诚实带条件的形式 (章节 `L.Model`{.Agda})：给定模型真值层上的一份排中律与前沿 (余部尚欠陈述的登记簿)，可构造结构满足 ZFC。此地标随前沿缩减自动升级，登记簿清空之日卸下第二个假设。与上一座地标合读，这就是选择公理相对一致性的语义形式：ZF 宇宙的体内携带着一个 ZFC 子宇宙。
<!--/-->

```agda
L⊨ZFC : ∀ {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) (F : L.Frontier.Frontier {ℓ})
      → isZFCModel (𝒮ʟ {ℓ})
L⊨ZFC = L.Model.L⊨ZFC
```
