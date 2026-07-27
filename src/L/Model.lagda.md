# The root: L ⊨ ZFC

<!--en-->
This is the root of the book, the chapter every other chapter exists to serve.
Read its statement with care, because the care is the content.

**What is proven.** Within cubical Agda, the constructible structure `𝒮ʟ` is a
model of ZFC: `L⊨ZFC`{.Agda} below. Together with Part 3, where the ambient
hierarchy models ZF, this is the **relative consistency of choice** in semantic
form: a universe satisfying ZF contains a sub-universe satisfying ZFC, so any
inconsistency of ZFC would already be an inconsistency of ZF.

**Relative to what.** To the host. The construction lives inside cubical Agda
with its universe tower, a metatheory informally about as strong as ZFC plus an
inaccessible cardinal. The book never claims an unconditional "Con(ZFC)";
consistency here is always consistency *relative to the declared host*, and the
host's strength is a price printed on the label, not hidden in the machinery.
This is no defect of mechanization: every consistency proof anywhere is relative
to the metatheory that carries it, and the only choice is whether to say so.

**What is assumed, today.** The module takes two parameters: one instance of
the excluded middle, at the model's own truth level, and the previous chapter's
**frontier**, the registry of statements not yet proven.
Given these, the theorem below is an ordinary, machine-checked theorem, and it
compiles today. Every remaining part of the book shrinks the frontier; when the
registry is empty its parameter disappears, and this page's statement stands
with the excluded middle alone. The chapter is therefore two things at once: the
book's main theorem, and its progress meter.
<!--zh-->
这里是本书的根，其余每一章都为它服务的那一章。请仔细读它的陈述，因为这份仔细本身就是内容。

**证了什么。**在 cubical Agda 之内，可构造结构 `𝒮ʟ` 是 ZFC 的模型：下文的 `L⊨ZFC`{.Agda}。与第三部 (环境层级满足 ZF) 合观，这就是语义形式的**选择公理相对一致性**：满足 ZF 的宇宙内部含有满足 ZFC 的子宇宙，故 ZFC 的任何矛盾都早已是 ZF 的矛盾。

**相对于什么。**相对于宿主。整个构造住在带宇宙塔的 cubical Agda 里，这个元理论的强度非形式地约当于 ZFC 加一个不可达基数。本书从不宣称无条件的「Con (ZFC)」；此处的一致性永远是**相对于申明的宿主**的一致性，宿主的强度是印在标签上的价格，不是藏在机器里的暗账。这并非机械化的缺陷：任何地方的任何一致性证明都相对于承载它的元理论，可选的只是说不说出来。

**今天假设了什么。**本模块收两个参数：一份排中律实例，取模型自己的真值层级；以及上一章的**前沿**，尚未证明的陈述之登记簿。给定二者，下面的定理是一条普通的、机器检验的定理，今天就能编译。本书余下各部不断缩减前沿；登记簿清空之日，其参数消失，本页的陈述便只倚排中律独立成立。所以本章同时是两样东西：本书的主定理，与它的进度表。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import L.Frontier using ( Frontier )

module L.Model {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) (F : Frontier {ℓ}) where

open import FOL.ZFStructure using ( module hPropStructure )
import FOL.ZFModel
open import L.Constructible {ℓ} using ( 𝒮ʟ )
open import L.Axioms.Basic {ℓ}
  using ( extensionalL; regularityL; hasEmptyL; hasPairL; hasUnionL )
open import L.Axioms.Numerals {ℓ}
  using ( numeralL; numeralL-zero; numeralL-suc )
open import L.Axioms.Infinity {ℓ} lem using ( hasInfinityL )
open import L.Axioms.Full {ℓ} lem using ( hasSeparationL; hasReplacementL )
open import L.Axioms.Power {ℓ} lem using ( hasPowerL )

open hPropStructure 𝒮ʟ
open Frontier F

module ModelL = FOL.ZFModel 𝒮ʟ
open ModelL using ( isZFModel; isZFCModel )
```

<!--en-->
## The theorem
<!--zh-->
## 定理
<!--/-->

<!--en-->
Assembly. All twelve fields of `isZFModel`{.Agda} now come from the axiom
chapters, none from the frontier, and
the choice field is applied to the very model being assembled, in the structural
form the frontier states it. The proportion is the progress bar: every chapter
that pays a debt moves a field from the second column to the first.
<!--zh-->
合龙。`isZFModel`{.Agda} 的十二个字段如今全部来自诸公理章，无一取自前沿，选择字段则以前沿所陈述的结构形式，作用于正被装配的这个模型自身。这个比例就是进度条：每一章还清一笔债，就把一个字段从第二栏挪到第一栏。
<!--/-->

```agda
L⊨ZF : isZFModel
L⊨ZF = record
  { extensional    = extensionalL
  ; regularity     = regularityL
  ; hasEmpty       = hasEmptyL
  ; hasPair        = hasPairL
  ; hasUnion       = hasUnionL
  ; hasSeparation  = hasSeparationL
  ; hasReplacement = hasReplacementL
  ; hasPower       = hasPowerL
  ; numeral        = numeralL
  ; numeral-zero   = numeralL-zero
  ; numeral-suc    = numeralL-suc
  ; hasInfinity    = hasInfinityL }

L⊨ZFC : isZFCModel
L⊨ZFC = record { zf = L⊨ZF ; hasChoice = hasChoiceL L⊨ZF }
```

<!--en-->
## Recap
<!--zh-->
## 小结
<!--/-->

<!--en-->
The root stands: `L⊨ZFC`{.Agda}, the constructible structure models ZFC, proven
from the excluded-middle interface and the frontier. What the reader should
carry away is the shape of the claim: a semantic, relative consistency theorem,
priced in the open. **Every field of ZF is now a theorem rather than a
hypothesis**, and what is left of the frontier is choice alone.
<!--zh-->
根已立起：`L⊨ZFC`{.Agda}，可构造结构满足 ZFC，由排中律接口与前沿证得。读者该带走的是这个论断的形状：一条语义的、相对的一致性定理，价格摆在明处。**ZF 的每个字段如今都是定理而非假设**，而前沿所剩的只有选择一条。
<!--/-->
