<!--en-->
# The constructible universe models ZFC

The previously proved axiom packages assemble into `L⊨ZF`{.Agda}, and the constructible choice theorem extends it to `L⊨ZFC`{.Agda}. Both results require exactly one instance of excluded middle at the truth-value level of the model.
<!--zh-->
# 可构造宇宙是 ZFC 的模型

此前证明的各公理包组装成 `L⊨ZF`{.Agda}，再由可构造选择定理扩展为 `L⊨ZFC`{.Agda}。两项结果恰好需要模型真值层级上的一个排中律实例。
<!--ja-->
# 構成可能宇宙は ZFC のモデル

これまでに示した各公理を組み立てると `L⊨ZF`{.Agda} が得られ、構成可能な選択の定理を加えると `L⊨ZFC`{.Agda} になります。どちらも、モデルの真理値のレベルにおける一つの排中律だけを仮定します。
<!--/-->

<!--en-->
**What is proven.** Within cubical Agda, the constructible structure `𝒮ʟ` is a
model of ZFC: `L⊨ZFC`{.Agda} below. Together with the ambient-hierarchy result
that the hierarchy models ZF, this is the **relative consistency of choice** in semantic
form: a universe satisfying ZF contains a sub-universe satisfying ZFC, so any
inconsistency of ZFC would already be an inconsistency of ZF.

**Relative to what.** To the host metatheory. The construction is carried out inside
cubical Agda with its universe tower, a metatheory informally about as strong
as ZFC plus an inaccessible cardinal. The book never claims an unconditional
"Con(ZFC)"; consistency here is always consistency *relative to the declared
host*, and the host's strength is counted explicitly. This is not a defect specific
to mechanization: every consistency proof anywhere is relative to the
metatheory that carries it, and the only choice is whether to say so.

**What is assumed.** One instance of excluded middle at the model's own truth
level. That is the only assumption. Every construction used below has already been
proved in the preceding chapters; the final theorem carries exactly this
classical hypothesis.
<!--zh-->
**证了什么。**在 cubical Agda 之内，可构造结构 `𝒮ʟ` 是 ZFC 的模型：下文的 `L⊨ZFC`{.Agda}。与环境层级满足 ZF 的结果合观，这就是语义形式的**选择公理相对一致性**：满足 ZF 的宇宙内部含有满足 ZFC 的子宇宙，故 ZFC 的任何矛盾都早已是 ZF 的矛盾。

**相对于什么。**相对于宿主元理论。整个构造在带宇宙塔的 cubical Agda 中进行，该元理论的强度可非形式地看作 ZFC 加一个不可达基数。本书不声称无条件的「Con (ZFC)」；这里的一致性始终是相对于所声明宿主元理论的一致性，并明确计入宿主的强度。这不是机械化特有的缺陷：任何一致性证明都相对于承载该证明的元理论，区别只在于是否明确声明这一点。

**假设了什么。**一份排中律实例，取在模型自己的真值层级上。全部假设即此一项。下文使用的每项构造都已在前面的章节得到证明，最终定理恰以这一项经典假设为前提。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
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

The assembly is now complete, and each component comes from the corresponding
axiom chapter. The twelve fields of
`isZFModel`{.Agda} come from Parts 4's axiom chapters, and the choice field comes
from `L.Choice.Transversal`{.Agda}, applied to the very model being assembled:
choice is stated relative to a ZF model on this carrier, because the
intersection it names is that model's derived operation, and the model it is
applied to is the one built on the line above.
<!--zh-->
## 定理

全部字段至此汇齐，每一行都来自相应的公理章节。`isZFModel`{.Agda} 的十二个字段分别来自可构造公理阶段的各章，选择字段来自 `L.Choice.Transversal`{.Agda}，并应用于刚刚构造的模型自身。选择是在此载体上的一个 ZF 模型中陈述的，因为它所指的交是该模型的派生运算，而它所作用的模型正是上一行构造的那个。
<!--ja-->
## 定理

`L⊨ZF`{.Agda} は、外延性、正則性、空集合、対、和集合、分出、置換、冪集合、数項、無限の各証明を一つのモデル構造体へまとめます。`L⊨ZFC`{.Agda} は、その ZF モデルに `L` 内部の選択定理を加えます。
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

The root is established, with no further construction needed: `L⊨ZFC`{.Agda}, the
constructible structure models ZFC, proved from the declared excluded-middle
interface and nothing else. What the reader should carry away is the shape of
the claim: a semantic, relative consistency theorem whose metatheoretic
assumption is stated openly. **Every field of ZFC is a theorem rather than a
hypothesis**, choice included, and there are no other assumptions.
<!--zh-->
## 小结

根基至此确立，而且不再需要额外构造：`L⊨ZFC`{.Agda} 表明可构造结构满足 ZFC；证明只使用申明的排中律接口，没有其他前提。这里得到的是一条语义形式的相对一致性定理，其元理论前提已经明确申明。**ZFC 的每个字段都是定理而非假设**，其中也包括选择；除此之外没有其他假设。
<!--ja-->
## まとめ

構成可能構造は、一つの排中律から ZF と選択公理のすべての欄を満たします。したがって `L⊨ZFC`{.Agda} は、追加の集合論的仮定を持たず、明示された同じ古典的仮定だけに依存します。この結果は、明示されたメタ理論上の仮定の下で、相対無矛盾性を意味論的に表します。
<!--/-->
