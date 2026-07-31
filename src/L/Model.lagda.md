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

**What is assumed.** One instance of the excluded middle, at the model's own
truth level. That is the whole bill. The module took a second parameter for most
of the book's life, the **frontier**, a registry of statements not yet proven;
the registry emptied when the previous chapter paid the last of them, and the
parameter, together with the chapter that held it, is gone. What is left is a
theorem in the ordinary sense, with one hypothesis, both of whose halves are
printed on this page.
<!--zh-->
这里是本书的根，其余每一章都为它服务的那一章。请仔细读它的陈述，因为这份仔细本身就是内容。

**证了什么。**在 cubical Agda 之内，可构造结构 `𝒮ʟ` 是 ZFC 的模型：下文的 `L⊨ZFC`{.Agda}。与第三部 (环境层级满足 ZF) 合观，这就是语义形式的**选择公理相对一致性**：满足 ZF 的宇宙内部含有满足 ZFC 的子宇宙，故 ZFC 的任何矛盾都早已是 ZF 的矛盾。

**相对于什么。**相对于宿主。整个构造住在带宇宙塔的 cubical Agda 里，这个元理论的强度非形式地约当于 ZFC 加一个不可达基数。本书从不宣称无条件的「Con (ZFC)」；此处的一致性永远是**相对于申明的宿主**的一致性，宿主的强度是印在标签上的价格，不是藏在机器里的暗账。这并非机械化的缺陷：任何地方的任何一致性证明都相对于承载它的元理论，可选的只是说不说出来。

**假设了什么。**一份排中律实例，取模型自己的真值层级。账单全在这里了。本模块在全书大半光景里还收第二个参数，即**前沿**，尚未证明的陈述之登记簿；上一章还清最后一笔时登记簿清空，那个参数连同持有它的那一章一并消失。剩下的是一条通常意义上的定理，只带一个假设，而这个假设的两半都印在本页上。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module L.Model {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

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
open import L.Choice.Transversal {ℓ} lem using ( hasChoiceL )

open hPropStructure 𝒮ʟ

module ModelL = FOL.ZFModel 𝒮ʟ
open ModelL using ( isZFModel; isZFCModel )
```

<!--en-->
## The theorem
<!--zh-->
## 定理
<!--/-->

<!--en-->
Assembly, and every line of it is now an axiom chapter. The twelve fields of
`isZFModel`{.Agda} come from Parts 4's axiom chapters, and the choice field comes
from `L.Choice.Transversal`{.Agda}, applied to the very model being assembled:
choice is stated relative to a ZF model on this carrier, because the
intersection it names is that model's derived operation, and the model it is
applied to is the one built on the line above.
<!--zh-->
合龙，而如今每一行都出自某一章公理。`isZFModel`{.Agda} 的十二个字段来自第四部诸公理章，选择字段来自 `L.Choice.Transversal`{.Agda}，作用于正被装配的这个模型自身：选择相对于此载体上的一个 ZF 模型陈述，因为它所点名的交是那个模型的派生运算，而它所作用的那个模型，正是上一行造出来的那个。
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
The root stands, and it stands unconditionally: `L⊨ZFC`{.Agda}, the constructible
structure models ZFC, from the excluded-middle interface and nothing else. What
the reader should carry away is the shape of the claim: a semantic, relative
consistency theorem, priced in the open. **Every field of ZFC is a theorem rather
than a hypothesis**, choice included, and there is no registry left to shrink.
<!--zh-->
根已立起，且是无条件地立起：`L⊨ZFC`{.Agda}，可构造结构满足 ZFC，只由排中律接口证得，别无其他。读者该带走的是这个论断的形状：一条语义的、相对的一致性定理，价格摆在明处。**ZFC 的每个字段都是定理而非假设**，选择在内，而再没有登记簿可缩了。
<!--/-->
