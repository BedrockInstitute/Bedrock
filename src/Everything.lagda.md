# Bedrock

<!--en-->
This catalog is the reading path through the checked development. `Landmarks` is the sole preview: it states the two completed endpoints, `L⊨ZFC` and `L⊨GCH`, each from exactly `LEM (ℓ-suc ℓ)`. Every later chapter appears once, after its mathematical prerequisites.
<!--zh-->
这份目录给出已检验开发的阅读路径。`Landmarks` 是唯一的开篇预览：它陈述两个已经证明的终点 `L⊨ZFC` 与 `L⊨GCH`，二者都恰从 `LEM (ℓ-suc ℓ)` 出发。此后每章只出现一次，并位于其数学前提之后。
<!--/-->

<!--en-->
## Preview

Start with the destination. These signatures state exactly what the book proves
and which classical assumption each endpoint consumes.

- `Landmarks`{.Agda}: states the completed `L⊨ZFC` and `L⊨GCH` theorems with their exact assumption.
<!--zh-->
## 开篇预览

先看终点。这些签名准确陈述全书证明了什么，以及每个终点花费哪项经典假设。

- `Landmarks`{.Agda}：先展示 L 满足 ZFC 与 GCH 的最终定理。
<!--/-->
```agda
{-# OPTIONS --cubical --safe --guardedness #-}

module Everything where

import Landmarks
```

<!--en-->
## Foundations

The proofs need a common language for propositions, universe size, and the two
classical interfaces. This stage makes those assumptions explicit before any set model appears.

- `Base.Prelude`{.Agda}: re-exports the statement-level types and notation used throughout the book.
- `Base.Truth`{.Agda}: builds the algebra of proposition-valued truth.
- `Base.Impredicativity`{.Agda}: packages propositional resizing with a small classifier.
- `Base.Classical`{.Agda}: derives the impredicativity package from excluded middle.
- `Base.Choice`{.Agda}: states set-level choice and derives excluded middle from it.
<!--zh-->
## 基础

全书先统一命题、宇宙大小与两项经典接口的语言。在任何集合模型出现之前，本部先把所用假设明写出来。

- `Base.Prelude`{.Agda}：陈述全书共用的类型与记号。
- `Base.Truth`{.Agda}：建立命题值代数。
- `Base.Impredicativity`{.Agda}：打包降层与小分类器接口。
- `Base.Classical`{.Agda}：由排中律兑现非直谓性。
- `Base.Choice`{.Agda}：陈述集合选择并推出排中律。
<!--/-->
```agda
import Base.Prelude
import Base.Truth
import Base.Impredicativity
import Base.Classical
import Base.Choice
```

<!--en-->
## First-order logic

ZFC and GCH will be proved inside a model, so their syntax and semantics must
themselves be mathematical objects. This stage supplies formulas, complexity, substitution, and coding for the later internal arguments.

- `FOL.Syntax`{.Agda}: defines first-order terms and formulas.
- `FOL.ZFStructure`{.Agda}: defines the operations and relations of a set-theoretic structure.
- `FOL.Semantics`{.Agda}: interprets terms and formulas in a structure.
- `FOL.LevyHierarchy`{.Agda}: classifies formulas by the Lévy hierarchy.
- `FOL.Absoluteness`{.Agda}: proves absoluteness for Δ₀ formulas.
- `FOL.ZFModel`{.Agda}: packages the axioms required of ZF and ZFC models.
- `FOL.Manipulation.Mapping`{.Agda}: maps constants uniformly through terms and formulas.
- `FOL.Manipulation.Renaming`{.Agda}: renames de Bruijn variables while preserving meaning.
- `FOL.Manipulation.Relabelling`{.Agda}: relabels constants and proves semantic invariance.
- `FOL.Manipulation.Relativize`{.Agda}: restricts every quantifier to a chosen carrier.
- `FOL.Manipulation.Bounding`{.Agda}: supports partial relabelling when all constants are in its domain.
- `FOL.Manipulation.Occurrences`{.Agda}: counts and enumerates constants by occurrence.
- `FOL.Manipulation.Parameters`{.Agda}: abstracts constant occurrences into environment slots.
- `FOL.Coding`{.Agda}: encodes syntax as sets and proves formula-code injectivity.
<!--zh-->
## 一阶逻辑

ZFC 与 GCH 将在模型内部得到证明，故其语法与语义本身必须成为数学对象。本部给出公式、复杂度、代换与编码，供后面的内部论证使用。

- `FOL.Syntax`{.Agda}：定义项与公式。
- `FOL.ZFStructure`{.Agda}：定义集合论语言的结构。
- `FOL.Semantics`{.Agda}：解释公式的含义。
- `FOL.LevyHierarchy`{.Agda}：刻画公式的 Lévy 层级。
- `FOL.Absoluteness`{.Agda}：证明 Δ₀ 公式的绝对性。
- `FOL.ZFModel`{.Agda}：汇集 ZF 与 ZFC 模型字段。
- `FOL.Manipulation.Mapping`{.Agda}：统一常元映射。
- `FOL.Manipulation.Renaming`{.Agda}：统一变量改名。
- `FOL.Manipulation.Relabelling`{.Agda}：证明常元重标保持含义。
- `FOL.Manipulation.Relativize`{.Agda}：把量词限制到一个载体。
- `FOL.Manipulation.Bounding`{.Agda}：沿部分映射重标有界常元。
- `FOL.Manipulation.Occurrences`{.Agda}：按出现计数并枚举常元。
- `FOL.Manipulation.Parameters`{.Agda}：把常元抽象成环境参数。
- `FOL.Coding`{.Agda}：把语法编码为集合。
<!--/-->
```agda
import FOL.Syntax
import FOL.ZFStructure
import FOL.Semantics
import FOL.LevyHierarchy
import FOL.Absoluteness
import FOL.ZFModel
import FOL.Manipulation.Mapping
import FOL.Manipulation.Renaming
import FOL.Manipulation.Relabelling
import FOL.Manipulation.Relativize
import FOL.Manipulation.Bounding
import FOL.Manipulation.Occurrences
import FOL.Manipulation.Parameters
import FOL.Coding
```

<!--en-->
## The ambient hierarchy

The cumulative hierarchy is the ambient universe in which all later sets and
codes are built. Its presentation, smallness, and model theorems provide the concrete semantics that the abstract logic now needs.

- `V.Hierarchy`{.Agda}: constructs the cumulative hierarchy and its membership structure.
- `V.Presentation`{.Agda}: turns hierarchy membership into small indexing data.
- `V.Collapse`{.Agda}: collapses extensional well-founded graphs to hierarchy sets.
- `V.Smallness`{.Agda}: proves atomic and Δ₀ truth values small, yielding Δ₀ separation and inner smallness.
- `V.Model`{.Agda}: assembles the cumulative hierarchy as a model of ZF and ZFC.
- `V.CantorBernstein`{.Agda}: turns injections between small index types into a bijection.
- `V.Coding`{.Agda}: instantiates syntax coding in the cumulative hierarchy.
<!--zh-->
## 环境层级

累积层级是后面一切集合与码的环境宇宙。它的成员表示、小性与模型定理，为刚建立的抽象逻辑提供具体语义。

- `V.Hierarchy`{.Agda}：建立累积层级及其成员关系。
- `V.Presentation`{.Agda}：给出集合成员的索引表示。
- `V.Collapse`{.Agda}：构造外延良基关系的塌缩。
- `V.Smallness`{.Agda}：证明原子与 Δ₀ 真值足够小，并推出 Δ₀ 分离与内部小性。
- `V.Model`{.Agda}：组装累积层级的 ZF 与 ZFC 模型。
- `V.CantorBernstein`{.Agda}：把小索引类型间的双向单射化为双射。
- `V.Coding`{.Agda}：在累积层级中实现语法编码。
<!--/-->
```agda
import V.Hierarchy
import V.Presentation
import V.Collapse
import V.Smallness
import V.Model
import V.CantorBernstein
import V.Coding
```

<!--en-->
## Constructible stages and the axioms

Definability now generates the stages of `L`, while ordinals and rank control
where constructions live. Reflection then upgrades bounded closure facts to the full ZF schemes and leaves only Choice for the ZFC endpoint.

- `L.Definability`{.Agda}: collects parameter-definable subsets into one set.
- `L.Constructible`{.Agda}: builds the stages, class, and structure of the constructible universe.
- `L.Ordinal`{.Agda}: develops ordinals and their closure under successors and small unions.
- `L.Rank`{.Agda}: measures sets by an ordinal-valued rank.
- `L.Ordinal.Linear`{.Agda}: proves trichotomy for ordinals of `L`.
- `L.Ordinal.Stages`{.Agda}: identifies exactly which ordinals occur at each constructible stage.
- `L.WellOrder.Base`{.Agda}: packages strict well-orders, constructs the natural-number example and selects least elements.
- `L.Stage`{.Agda}: selects the first stage at which a constructible set appears.
- `L.Axioms.Basic`{.Agda}: proves extensionality, regularity, empty set, pairing, and union in `L`.
- `L.Axioms.Separation`{.Agda}: proves Δ₀ separation and replacement in `L`.
- `L.Reflect`{.Agda}: reflects one existential formula into a constructible stage.
- `L.ReflectFo`{.Agda}: reflects an arbitrary formula into a constructible stage.
- `L.Axioms.Full`{.Agda}: uses reflection to prove full separation and replacement.
- `L.Axioms.Power`{.Agda}: constructs the power set internal to `L`.
- `L.Absoluteness`{.Agda}: transfers hierarchy formulas between ambient satisfaction and satisfaction inside `L`.
- `L.Axioms.Numerals`{.Agda}: constructs the numeral chain in `L` and proves its projection equations.
- `L.Axioms.Infinity`{.Agda}: uses the numeral chain to prove infinity in `L`.
<!--zh-->
## 可构造阶段与公理

可定义性现在生成 `L` 的诸阶段，序数与秩则控制各种构造落在哪一层。反射随后把有界闭包提升为完整的 ZF 模式，使 ZFC 终点只余选择公理。

- `L.Definability`{.Agda}：把可定义子集组成集合。
- `L.Constructible`{.Agda}：构造 L 的阶段与模型载体。
- `L.Ordinal`{.Agda}：提供序数及其闭包性质。
- `L.Rank`{.Agda}：以序数值秩度量集合。
- `L.Ordinal.Linear`{.Agda}：证明 L 中序数三歧。
- `L.Ordinal.Stages`{.Agda}：刻画各阶段出现的序数。
- `L.WellOrder.Base`{.Agda}：定义严格良序，构造自然数的例子，并选取极小元。
- `L.Stage`{.Agda}：选出集合首次出现的阶段。
- `L.Axioms.Basic`{.Agda}：证明 L 的基本模型公理。
- `L.Axioms.Separation`{.Agda}：证明 Δ₀ 分离与替换。
- `L.Reflect`{.Agda}：把一个存在式反射到阶段。
- `L.ReflectFo`{.Agda}：把整条公式反射到阶段。
- `L.Axioms.Full`{.Agda}：由反射推出完全分离与替换。
- `L.Axioms.Power`{.Agda}：构造 L 内幂集。
- `L.Absoluteness`{.Agda}：在环境满足与 L 内满足之间搬运层级公式。
- `L.Axioms.Numerals`{.Agda}：构造并钉定 L 内数码链。
- `L.Axioms.Infinity`{.Agda}：由数码链证明无穷公理。
<!--/-->
```agda
import L.Definability
import L.Constructible
import L.Ordinal
import L.Rank
import L.Ordinal.Linear
import L.Ordinal.Stages
import L.WellOrder.Base
import L.Stage
import L.Axioms.Basic
import L.Axioms.Separation
import L.Reflect
import L.ReflectFo
import L.Axioms.Full
import L.Axioms.Power
import L.Absoluteness
import L.Axioms.Numerals
import L.Axioms.Infinity
```

<!--en-->
## Internal coding: expressions and domains

To reason about truth inside `L`, the external syntax must be readable there as
sets. This stage builds the elementary readers and the closed code domains on which an internal recursion may safely descend.

- `L.Coding.Base`{.Agda}: provides Δ₀ readers for singletons, pairs, tags, and membership.
- `L.Coding.Environment`{.Agda}: represents finite environments by set-valued graphs.
- `L.Coding.Model`{.Agda}: builds the internal dictionary for pairs, applications, domains, codes, environments, and tags.
- `L.Coding.Expressions`{.Agda}: builds code expressions and adequate readers for their values.
- `L.Coding.Quantification`{.Agda}: provides bounded frames and semantic readers for quantifying over coded pairs.
- `L.Coding.Closure`{.Agda}: defines domains closed under immediate subcodes and proves its readers.
- `L.Coding.Descent`{.Agda}: proves that every immediate code component has lower rank.
- `L.Coding.Injection`{.Agda}: expresses injections by formulas and coded graphs.
- `L.Coding.InL`{.Agda}: proves that formula codes are constructible.
- `L.Coding.Closed`{.Agda}: proves that the subformula closure is itself closed.
- `L.Recursion`{.Agda}: internalizes well-founded recursive definitions as set graphs.
<!--zh-->
## 内部编码：表达式与定义域

要在 `L` 内部推理真值，外部语法必须在那里作为集合被读出。本部建立基础读式与封闭码域，使内部递归能够安全地沿码下降。

- `L.Coding.Base`{.Agda}：给出单点、配对、标签与隶属的 Δ₀ 读式。
- `L.Coding.Environment`{.Agda}：把有限环境表示为集合。
- `L.Coding.Model`{.Agda}：建立配对、应用、定义域、码、环境与标签的内部字典。
- `L.Coding.Expressions`{.Agda}：组合码表达式及其读式。
- `L.Coding.Quantification`{.Agda}：给出量化码化配对的有界框架与语义读式。
- `L.Coding.Closure`{.Agda}：刻画对子码封闭的定义域。
- `L.Coding.Descent`{.Agda}：证明码的组成部分秩更低。
- `L.Coding.Injection`{.Agda}：在对象语言中表示单射。
- `L.Coding.InL`{.Agda}：证明公式码可构造。
- `L.Coding.Closed`{.Agda}：证明子公式闭包自身封闭。
- `L.Recursion`{.Agda}：把良基递归内部化。
<!--/-->
```agda
import L.Coding.Base
import L.Coding.Environment
import L.Coding.Model
import L.Coding.Expressions
import L.Coding.Quantification
import L.Coding.Closure
import L.Coding.Descent
import L.Coding.Injection
import L.Coding.InL
import L.Coding.Closed
import L.Recursion
```

<!--en-->
## Internal coding: tables and uniform satisfaction

The closed domains support tables whose clauses compute semantic values. By the
end of this stage, satisfaction and the constructible hierarchy are uniformly describable inside `L`, ready for both Choice and GCH.

- `L.Coding.EnvSet`{.Agda}: shows that all environments over a fixed carrier form a set.
- `L.Coding.Sat`{.Agda}: constructs the semantic value for one formula.
- `L.Coding.Bridge`{.Agda}: identifies recursive values with semantic satisfaction.
- `L.Coding.Table`{.Agda}: constructs a recursion table and characterizes its entries.
- `L.Coding.Sound`{.Agda}: proves that the recursion table satisfies every clause.
- `L.Coding.Slot`{.Agda}: proves that a formula’s subcode slot is closed.
- `L.Coding.Shape`{.Agda}: recognizes well-formed arity-tagged code keys.
- `L.Coding.Recover`{.Agda}: recovers a formula from a well-formed code.
- `L.Coding.Bound`{.Agda}: bounds all relevant codes at a limit stage.
- `L.Coding.Tower`{.Agda}: constructs the tower of environment sets and proves its formula, reader, and satisfaction interfaces.
- `L.Coding.CodeSet`{.Agda}: collects all formulas over a carrier into one code set.
- `L.Coding.CodeDomain`{.Agda}: packages code shape and closure with soundness, completeness, and satisfaction theorems.
- `L.Coding.Clauses`{.Agda}: defines the semantic relations, clause family, frame, and bridges for satisfaction recursion.
- `L.Coding.Pinned`{.Agda}: proves uniqueness of the recursion on a subcode-closed domain.
- `L.Coding.Graph`{.Agda}: defines the object-language graph of uniform satisfaction.
- `L.Coding.Uniform`{.Agda}: evaluates every member of the whole code set uniformly.
- `L.Coding.Powerset`{.Agda}: describes the definable powerset with the carrier in a slot.
- `L.Coding.Sequence`{.Agda}: describes the constructible hierarchy as a sequence.
- `L.Hierarchy`{.Agda}: realizes the constructible hierarchy inside its own model.
<!--zh-->
## 内部编码：表与统一满足关系

封闭定义域承载依子句计算语义值的表。本部结束时，满足关系与可构造层级都能在 `L` 内统一描述，从而为选择公理与 GCH 同时备妥工具。

- `L.Coding.EnvSet`{.Agda}：证明固定载体上的环境成集。
- `L.Coding.Sat`{.Agda}：构造单条公式的满足值。
- `L.Coding.Bridge`{.Agda}：识别递归值与语义满足。
- `L.Coding.Table`{.Agda}：构造递归表并读出条目。
- `L.Coding.Sound`{.Agda}：证明递归表满足各子句。
- `L.Coding.Slot`{.Agda}：证明公式的子码槽封闭。
- `L.Coding.Shape`{.Agda}：识别良构码键。
- `L.Coding.Recover`{.Agda}：从良构码恢复公式。
- `L.Coding.Bound`{.Agda}：为极限处的码取界。
- `L.Coding.Tower`{.Agda}：构造各元数的环境塔，并给出其公式、读式与满足接口。
- `L.Coding.CodeSet`{.Agda}：把所有公式码组成集合。
- `L.Coding.CodeDomain`{.Agda}：把码的形状与封闭性汇成定义域，并证明可靠性、完备性与满足定理。
- `L.Coding.Clauses`{.Agda}：给出满足递归的语义关系、子句族、框架与桥梁。
- `L.Coding.Pinned`{.Agda}：在封闭码集上钉定递归。
- `L.Coding.Graph`{.Agda}：描述统一满足图。
- `L.Coding.Uniform`{.Agda}：在整个码集上统一求值。
- `L.Coding.Powerset`{.Agda}：在对象语言中描述可定义幂集。
- `L.Coding.Sequence`{.Agda}：把 L 的层级描述成序列。
- `L.Hierarchy`{.Agda}：在模型内部实现可构造层级。
<!--/-->
```agda
import L.Coding.EnvSet
import L.Coding.Sat
import L.Coding.Bridge
import L.Coding.Table
import L.Coding.Sound
import L.Coding.Slot
import L.Coding.Shape
import L.Coding.Recover
import L.Coding.Bound
import L.Coding.Tower
import L.Coding.CodeSet
import L.Coding.CodeDomain
import L.Coding.Clauses
import L.Coding.Pinned
import L.Coding.Graph
import L.Coding.Uniform
import L.Coding.Powerset
import L.Coding.Sequence
import L.Hierarchy
```

<!--en-->
## The canonical well-order and Choice

Uniform descriptions let `L` compare names rather than arbitrary external sets.
Finite-stage orders grow into a global canonical order, whose least elements produce the transversal required by Choice.

- `L.Choice.Stage`{.Agda}: selects the first stage at which a constructible set appears.
- `L.Choice.Finite`{.Agda}: well-orders the finite stages and their limit.
- `L.Choice.Name`{.Agda}: assigns formulas and parameter vectors as names for stage members.
- `L.Choice.Step`{.Agda}: constructs the canonical order one stage at a time.
- `L.Choice.Internal`{.Agda}: describes the canonical order in the object language.
- `L.Choice.Table`{.Agda}: constructs the canonical order relation as a set and characterizes its members.
- `L.Choice.Faithful`{.Agda}: proves that the internal order description has its intended meaning.
- `L.Choice.Adequate`{.Agda}: proves the described step agrees with the named-stage construction.
- `L.Choice.Limit`{.Agda}: represents the order on the limit stage by a set in `L`.
- `L.Choice.Before`{.Agda}: internalizes the family of earliest-disagreement relations.
- `L.Choice.Order`{.Agda}: assembles the global canonical order of `L`.
- `L.Choice.Transversal`{.Agda}: chooses least members to construct a transversal and prove Choice.
- `L.Model`{.Agda}: assembles the basic axioms, full schemes, Power, Infinity, and Choice into `L⊨ZFC`.
<!--zh-->
## 典范良序与选择公理

统一描述使 `L` 能比较名字，而无须直接比较任意外部集合。有穷阶段上的序扩展为全局典范序，其极小元给出选择公理所需的横截集。

- `L.Choice.Stage`{.Agda}：选出集合首次出现的阶段。
- `L.Choice.Finite`{.Agda}：良序化有限阶段及其极限。
- `L.Choice.Name`{.Agda}：给阶段成员赋公式与参数名。
- `L.Choice.Step`{.Agda}：为每个阶段构造一步良序。
- `L.Choice.Internal`{.Agda}：在对象语言中描述这套序。
- `L.Choice.Table`{.Agda}：把典范序关系构造成集合并刻画其成员。
- `L.Choice.Faithful`{.Agda}：证明内部描述忠实。
- `L.Choice.Adequate`{.Agda}：证明描述的一步适足。
- `L.Choice.Limit`{.Agda}：把极限阶段的序表示成 L 集合。
- `L.Choice.Before`{.Agda}：内部化最先分歧关系族。
- `L.Choice.Order`{.Agda}：组装 L 的全局典范序。
- `L.Choice.Transversal`{.Agda}：以最小元构造选择横截集。
- `L.Model`{.Agda}：把基本公理、完全模式、幂集、无穷与选择组装为 `L⊨ZFC`。
<!--/-->
```agda
import L.Choice.Stage
import L.Choice.Finite
import L.Choice.Name
import L.Choice.Step
import L.Choice.Internal
import L.Choice.Table
import L.Choice.Faithful
import L.Choice.Adequate
import L.Choice.Limit
import L.Choice.Before
import L.Choice.Order
import L.Choice.Transversal
import L.Model
```

<!--en-->
## Ordinals and cardinals for GCH

With ZFC established, the remaining goal is cardinal arithmetic inside `L`.
These chapters provide coded injections, order types, collapse, and larger cardinals before the final counting argument begins.

- `L.Ordinal.SquareLaw`{.Agda}: builds the ordinal and Gödel pair orders used by the square law.
- `L.Cardinal`{.Agda}: relates cardinality, injections, and coded injections in `L`.
- `L.GCH`{.Agda}: states the generalized continuum hypothesis internally to `L`.
- `L.CantorBernstein`{.Agda}: turns mutual coded injections in `L` into a coded bijection.
- `L.Mostowski`{.Agda}: collapses a transitive well-founded relation to ordinal-valued sets.
- `L.CardinalAbove`{.Agda}: constructs an ordinal `L`-cardinal above any given `L`-cardinal.
<!--zh-->
## GCH 所需的序数与基数

ZFC 已经建立，余下目标是在 `L` 内进行基数算术。本部先备齐编码单射、序型、塌缩与更大基数，再进入最后的计数论证。

- `L.Ordinal.SquareLaw`{.Agda}：建立序数平方律所需的良序。
- `L.Cardinal`{.Agda}：刻画 L 内基数与编码单射。
- `L.GCH`{.Agda}：陈述 L 内的广义连续统假设。
- `L.CantorBernstein`{.Agda}：把 L 中的双向编码单射化为编码双射。
- `L.Mostowski`{.Agda}：塌缩传递良基关系为序数。
- `L.CardinalAbove`{.Agda}：构造更大的 L 基数。
<!--/-->
```agda
import L.Ordinal.SquareLaw
import L.Cardinal
import L.GCH
import L.CantorBernstein
import L.Mostowski
import L.CardinalAbove
```

<!--en-->
## GCH: the internal tools

GCH reduces to bounding subsets by a sufficiently high constructible stage.
The following route internalizes definability, builds and counts Skolem hulls, derives the two cardinal injections, and assembles the theorem.

- `L.GCH.Definable`{.Agda}: turns a definable injection into a coded injection.
- `L.InjChain`{.Agda}: composes and pairs coded injections into `L`.
- `L.GCH.Assembly`{.Agda}: derives GCH from four explicit internal hypotheses.
- `L.GCH.SatFrame`{.Agda}: provides the graph frame for the uniform satisfaction table.
- `L.GCH.SatDescribe`{.Agda}: describes the satisfaction table by a Δ₀ formula.
- `L.GCH.DefDescribe`{.Agda}: describes the definable powerset by a Δ₀ formula.
- `L.GCH.Complete`{.Agda}: constructs adequate and superadequate stages.
- `L.GCH.OmegaRec`{.Agda}: internalizes ω-recursion for a definable step.
- `L.GCH.Hull`{.Agda}: constructs a Skolem hull and its transitive collapse.
- `L.GCH.HierDescribe`{.Agda}: describes the constructible hierarchy by a Δ₀ formula.
- `L.GCH.Condense`{.Agda}: identifies a collapsed superadequate hull with a constructible stage.
- `L.GCH.BelowSucc`{.Agda}: injects every ordinal below a successor cardinal into its base.
- `L.GCH.OrderType`{.Agda}: shows that the order type of a well-founded relation in `L` is in `L`.
- `L.GCH.CardOf`{.Agda}: assigns an internal cardinal to every ordinal of `L`.
- `L.GCH.Pairing`{.Agda}: proves the square law for infinite `L`-cardinals.
- `L.GCH.Least`{.Agda}: represents least witnesses by a definable map.
- `L.GCH.SuccIntoPower`{.Agda}: injects the successor cardinal into the power set.
- `L.GCH.Sequences`{.Agda}: injects finite sequences over an infinite ordinal back into it.
- `L.GCH.StageCount`{.Agda}: internally injects every infinite stage into its index.
- `L.GCH.HullIn`{.Agda}: proves that the hull and its collapse are elements of `L`.
- `L.GCH.HullCount`{.Agda}: internally counts the hull generated by a counted start.
- `L.GCH.StageCounted`{.Agda}: counts the constructible stage at an infinite ordinal.
- `L.GCH.BoundedSubset`{.Agda}: proves the internal bounded-subset theorem.
- `L.GCH.Theorem`{.Agda}: combines the bounds to prove that `L` satisfies GCH.
<!--zh-->
## GCH：内部工具

GCH 归结为用足够高的可构造阶段界住各个子集。以下路线内部化可定义性，构造并计数 Skolem 壳，得到两向基数单射，最后组装定理。

- `L.GCH.Definable`{.Agda}：把可定义单射编码进 L。
- `L.InjChain`{.Agda}：组合并配对通向 L 的单射。
- `L.GCH.Assembly`{.Agda}：把四项内部假设组装为 GCH。
- `L.GCH.SatFrame`{.Agda}：给统一满足表的图设框架。
- `L.GCH.SatDescribe`{.Agda}：以 Δ₀ 公式描述满足表。
- `L.GCH.DefDescribe`{.Agda}：以 Δ₀ 公式描述可定义幂集。
- `L.GCH.Complete`{.Agda}：取得适足与超适足阶段。
- `L.GCH.OmegaRec`{.Agda}：内部化可定义步骤的 ω 递归。
- `L.GCH.Hull`{.Agda}：构造 Skolem 壳及其塌缩。
- `L.GCH.HierDescribe`{.Agda}：以 Δ₀ 公式描述层级。
- `L.GCH.Condense`{.Agda}：把塌缩壳识别为 L 阶段。
- `L.GCH.BelowSucc`{.Agda}：把后继基数以下序数注入基数。
- `L.GCH.OrderType`{.Agda}：证明 L 内良基关系的序型仍在 L。
- `L.GCH.CardOf`{.Agda}：为每个 L 序数取得内部基数。
- `L.GCH.Pairing`{.Agda}：证明 L 基数的平方律。
- `L.GCH.Least`{.Agda}：把最小见证表示为可定义映射。
- `L.GCH.SuccIntoPower`{.Agda}：把后继基数注入幂集。
- `L.GCH.Sequences`{.Agda}：把有限序列注入无限序数。
- `L.GCH.StageCount`{.Agda}：在内部计数无限阶段。
- `L.GCH.HullIn`{.Agda}：证明壳及其塌缩属于 L。
- `L.GCH.HullCount`{.Agda}：在内部计数可数起点的壳。
- `L.GCH.StageCounted`{.Agda}：计数无限序数处的 L 阶段。
- `L.GCH.BoundedSubset`{.Agda}：证明内部有界子集定理。
- `L.GCH.Theorem`{.Agda}：合拢并证明 L 满足 GCH。
<!--/-->
```agda
import L.GCH.Definable
import L.InjChain
import L.GCH.Assembly
import L.GCH.SatFrame
import L.GCH.SatDescribe
import L.GCH.DefDescribe
import L.GCH.Complete
import L.GCH.OmegaRec
import L.GCH.Hull
import L.GCH.HierDescribe
import L.GCH.Condense
import L.GCH.BelowSucc
import L.GCH.OrderType
import L.GCH.CardOf
import L.GCH.Pairing
import L.GCH.Least
import L.GCH.SuccIntoPower
import L.GCH.Sequences
import L.GCH.StageCount
import L.GCH.HullIn
import L.GCH.HullCount
import L.GCH.StageCounted
import L.GCH.BoundedSubset
import L.GCH.Theorem
```
