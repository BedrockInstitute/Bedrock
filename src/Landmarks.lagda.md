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

The headline is classical: granted one instance of the excluded middle, at the
model's own truth level, the cumulative hierarchy is a model of ZF (chapter
`V.Model`{.Agda}). Its exact-price form carries the hypothesis as a suffix,
charging only the foundational impredicativity package; and by Diaconescu's theorem
(chapter `Base.Choice`{.Agda}), one instance of set-level choice funds the
upgrade all the way to ZFC.
<!--zh-->
## 层级满足 ZF(C)

主打名是经典版：给定模型自身真值层上的一份排中律，累积层级是 ZF 的模型 (章节 `V.Model`{.Agda})。其精确价格版以后缀携带假设，只收基础章节给出的非直谓性打包；再经 Diaconescu 定理 (章节 `Base.Choice`{.Agda})，一份集合层选择就资助到 ZFC。
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
ZFC. One hypothesis, and it is the same one the previous landmark pays. Read with the previous landmark, it is the semantic form of
the relative consistency of choice: a ZF universe carries a ZFC sub-universe
inside it.
<!--zh-->
## 可构造宇宙满足 ZFC

本书的主定理 (章节 `L.Model`{.Agda})：给定模型真值层上的一份排中律，可构造结构满足 ZFC。一个假设，而它与上一座地标所付的是同一个。与上一座地标合读，这就是选择公理相对一致性的语义形式：ZF 宇宙的体内携带着一个 ZFC 子宇宙。
<!--/-->

```agda
L⊨ZFC : ∀ {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) → isZFCModel (𝒮ʟ {ℓ})
L⊨ZFC = L.Model.L⊨ZFC
```

<!--en-->
## The constructible universe models GCH

The second trophy (chapter `L.GCH.Theorem`{.Agda}): under the same single
hypothesis, the constructible structure satisfies the generalized continuum
hypothesis, stated in L's own terms: for every infinite cardinal κ of L, the
model's power set of κ and the successor cardinal of κ inject into each other by
injections that are themselves elements of L (chapter `L.GCH`{.Agda} states it).
<!--zh-->
## 可构造宇宙满足 GCH

第二座奖杯 (章节 `L.GCH.Theorem`{.Agda})：在同一个唯一假设下，可构造结构满足广义连续统假设，且以 L 自己的语言陈述：对 L 的每个无穷基数 κ，模型自身的 κ 的幂集与 κ 的后继基数之间存在互相的单射，而这些单射本身是 L 的元素 (章节 `L.GCH`{.Agda} 给出陈述)。
<!--/-->

```agda
L⊨GCH : ∀ {ℓ : Level} (lem : LEM (ℓ-suc ℓ))
      → L.GCH.GCHStatement lem (L.Model.L⊨ZF lem)
L⊨GCH lem = L.GCH.Theorem.L⊨GCH lem
```
