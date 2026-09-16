<!--en-->
# The constructible universe models ZFC

The constructible structure `𝒮ʟ` satisfies every axiom of ZF, and its canonical well-order supplies the axiom of choice. The resulting statements are `L⊨ZF`{.Agda} and `L⊨ZFC`{.Agda}. Both are proved in cubical Agda from one explicitly stated instance of excluded middle at the truth-value level of the model.
<!--zh-->
# 可构造宇宙是 ZFC 的模型

可构造结构 `𝒮ʟ` 满足 ZF 的全部公理，而它的典范良序进一步给出选择公理。所得陈述分别记作 `L⊨ZF`{.Agda} 与 `L⊨ZFC`{.Agda}。两者都在立方 Agda 中证明，只采用一项明确声明的排中律实例，其层级与模型的命题宇宙相同。
<!--ja-->
# 構成可能宇宙は ZFC のモデル

構成可能構造 `𝒮ʟ` は ZF のすべての公理を満たし、その標準的な整列順序から選択公理も得られます。得られる主張を `L⊨ZF`{.Agda} と `L⊨ZFC`{.Agda} と記します。いずれも cubical Agda の中で証明され、モデルの命題宇宙と同じレベルにある、明示された一つの排中律だけを用います。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Classical using ( LEM )

module L.Model {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
```

<!--en-->
This is a semantic relative-consistency result. The host metatheory constructs both the ambient hierarchy and its constructible substructure, then verifies the axioms directly in the latter. Accordingly, the theorem does not assert an unqualified consistency statement: it exhibits a model of ZFC relative to the metatheory in which the formalization is carried out.
<!--zh-->
这是一项语义形式的相对一致性结果。宿主元理论构造外围层级及其可构造子结构，并在后者中逐项验证公理。因此，本章并不声称无条件的一致性；它相对于承载形式化的元理论给出一个 ZFC 模型。
<!--ja-->
これは意味論的な相対無矛盾性の結果です。宿主メタ理論の中で周囲の階層とその構成可能な部分構造を作り、後者において各公理を直接検証します。したがって、無条件の無矛盾性を主張するのではなく、形式化を担うメタ理論に相対して ZFC のモデルを与えます。
<!--/-->

```agda
import FOL.ZFModel
open import L.Constructible {ℓ} using ( 𝒮ʟ )
open import L.Axioms.Basic {ℓ}
  using ( extensionalL; regularityL; hasEmptyL; hasPairL; hasUnionL )
open import L.Axioms.Numerals {ℓ}
```

<!--en-->
The elementary set operations and numerals are obtained constructively. The proofs of infinity, separation, replacement, power set, and the constructible choice theorem use the selected excluded-middle instance. This distinction records exactly where classical reasoning enters the model.
<!--zh-->
基本集合运算与数词以构造方式得到。无穷、分离、替换、幂集以及可构造选择定理的证明则使用所选的排中律实例。这一区分准确标出了经典推理进入模型的位置。
<!--ja-->
基本的な集合演算と数項は構成的に得られます。無限、分出、置換、冪集合、および構成可能な選択定理の証明は、選んだ排中律の実例を用います。この区別により、古典的推論がモデルに入る箇所が正確に示されます。
<!--/-->

```agda
  using ( numeralL; numeralL-zero; numeralL-suc )
open import L.Axioms.Infinity {ℓ} lem using ( hasInfinityL )
open import L.Axioms.Full {ℓ} lem using ( hasSeparationL; hasReplacementL )
open import L.Axioms.Power {ℓ} lem using ( hasPowerL )
open import L.Choice.Transversal {ℓ} lem using ( hasChoiceL )
```

<!--en-->
## The ZF model

The model structure collects twelve verified clauses. Extensionality, regularity, the empty set, pairing, and union are constructive properties of `L`. Separation and replacement provide the two formula schemes, while the power-set and infinity chapters supply the corresponding sets. The numeral clauses identify the internal natural-number sequence.
<!--zh-->
## ZF 模型

模型结构汇集十二项已经验证的条款。外延公理、正则公理、空集、配对与并集是 `L` 的构造性性质；分离与替换给出两个公式模式；幂集章与无穷章给出相应的集合；三个数词条款则确定模型内部的自然数序列。
<!--ja-->
## ZF モデル

モデル構造は、検証済みの十二の条項をまとめます。外延性、正則性、空集合、対、和集合は `L` の構成的な性質です。分出と置換が二つの論理式図式を与え、冪集合と無限の章が対応する集合を与えます。三つの数項の条項は、モデル内部の自然数列を定めます。
<!--/-->

```agda

open hPropStructure 𝒮ʟ

module ModelL = FOL.ZFModel 𝒮ʟ
open ModelL using ( isZFModel; isZFCModel )
L⊨ZF : isZFModel
L⊨ZF = record
```

<!--en-->
The first five fields state the elementary structural and set-forming principles. Each field receives a theorem already proved for the same membership structure, so their conclusions share one interpretation of sets, membership, and formulas.
<!--zh-->
记录的前五个字段陈述基本的结构性质与集合构造原理。每个字段都填入此前对同一成员结构证明的定理，因而它们对集合、成员关系与公式采用同一种解释。
<!--ja-->
レコードの最初の五つの欄は、基本的な構造上の性質と集合形成原理を述べます。各欄には同じ所属構造について証明された定理が入り、集合、所属、論理式はすべて同じ解釈を共有します。
<!--/-->

```agda
  { extensional    = extensionalL
  ; regularity     = regularityL
  ; hasEmpty       = hasEmptyL
  ; hasPair        = hasPairL
  ; hasUnion       = hasUnionL
```

<!--en-->
The next fields add separation, replacement, power sets, and the zero clause for numerals. The two schemes quantify over formulas interpreted in the same structure, while the power-set field fixes the model’s own power-set operation.
<!--zh-->
接下来的字段加入分离、替换、幂集以及数词的零条款。两个公理模式量化在同一结构中解释的公式，而幂集字段确定模型自身的幂集运算。
<!--ja-->
続く欄は、分出、置換、冪集合、および数項の零の条項を加えます。二つの公理図式は同じ構造で解釈される論理式にわたって量化し、冪集合の欄はモデル自身の冪集合演算を定めます。
<!--/-->

```agda
  ; hasSeparation  = hasSeparationL
  ; hasReplacement = hasReplacementL
  ; hasPower       = hasPowerL
  ; numeral        = numeralL
  ; numeral-zero   = numeralL-zero
```

<!--en-->
The successor equation for numerals and the existence of infinity complete the twelve fields. At this point the record is closed, and `L⊨ZF`{.Agda} is a proof that the constructible structure satisfies all of ZF.
<!--zh-->
数词的后继方程与无穷集合的存在补全最后两个字段。记录至此闭合，`L⊨ZF`{.Agda} 已经证明可构造结构满足完整的 ZF。
<!--ja-->
数項の後続方程式と無限集合の存在が最後の二つの欄を満たします。ここでレコードが閉じ、`L⊨ZF`{.Agda} は構成可能構造が ZF 全体を満たすことの証明となります。
<!--/-->

```agda
  ; numeral-suc    = numeralL-suc
  ; hasInfinity    = hasInfinityL }
```

<!--en-->
## Adding choice

An `isZFCModel` consists of a ZF model together with the choice statement interpreted by that model. The constructible well-order theorem supplies choice for `L⊨ZF`{.Agda}; in particular, the intersections appearing in that statement are the intersections derived from this very ZF structure. Adding this proof yields `L⊨ZFC`{.Agda}. Thus every ZFC axiom is established as a theorem under the declared excluded-middle hypothesis.
<!--zh-->
## 加入选择公理

`isZFCModel` 由一个 ZF 模型和在该模型中解释的选择陈述组成。可构造良序定理为 `L⊨ZF`{.Agda} 给出选择公理；特别地，该陈述中的交集正是由这一 ZF 结构导出的交集。加入这份证明便得到 `L⊨ZFC`{.Agda}。因此，在已经声明的排中律假设下，ZFC 的每条公理都作为定理成立。
<!--ja-->
## 選択公理を加える

`isZFCModel` は、ZF モデルと、そのモデルで解釈された選択の主張からなります。構成可能な整列順序の定理が `L⊨ZF`{.Agda} に選択公理を与えます。とくに、その主張に現れる共通部分は、まさにこの ZF 構造から導かれる共通部分です。この証明を加えると `L⊨ZFC`{.Agda} が得られます。したがって、宣言した排中律の仮定のもとで、ZFC の各公理はすべて定理として確立されます。
<!--/-->

```agda

L⊨ZFC : isZFCModel
L⊨ZFC = record { zf = L⊨ZF ; hasChoice = hasChoiceL L⊨ZF }
```
