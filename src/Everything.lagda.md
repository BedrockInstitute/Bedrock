<!--en-->
# Bedrock: a reading guide

This book studies why the constructible universe L satisfies ZFC and the generalized continuum hypothesis. After a preview of the final theorems, we learn the logical foundations, construct L, prove its axioms, and compare cardinalities. The catalog gives one possible reading order; once shared prerequisites are in place, you can follow several topics in parallel.
<!--zh-->
# Bedrock：阅读指南

本书研究可构造宇宙 L 为什么满足 ZFC 与广义连续统假设。我们先预览最终定理，再学习逻辑基础、构造 L、证明公理并比较基数。目录给出一种可行的阅读顺序；共同先修就绪后，你可以按照兴趣并行学习多个主题。
<!--ja-->
# Bedrock：読書案内

この本では，構成可能宇宙 L が ZFC と一般連続体仮説を満たすことを学びます。最初に最終定理を眺め，命題と一階論理の基礎から，L の構成，公理の証明，基数の比較へ進みます。以下の目次は一つの読書例です。前提を学んだ後は，関心に合わせて複数の主題を並行して読めます。
<!--/-->

<!--en-->
### Parallel routes and their meeting points

The prerequisite graph determines which chapters are ready to read; the catalog
numbers do not impose a timetable. Each branch below still requires its own
prerequisites, shown in the dependency map. At a meeting point, complete the
required material from both branches. A branch may also use earlier shared
material that the other branch does not need.

| Shared preparation | Topics that can proceed separately | Where they meet |
|---|---|---|
| Foundations, first-order syntax and semantics | Constant/variable manipulation; the ambient hierarchy, smallness and model | `L.Definability` uses semantic relabelling and ambient smallness; `L.Constructible` also needs `V.Model`. Occurrence abstraction can continue separately until names need it. |
| Constructible stages, ordinals and basic axioms | External canonical orders in `Choice.FiniteStageOrders`, `Choice.CanonicalNames`, `Choice.StageOrders`; internal satisfaction coding through `Coding.UniformSatisfaction` | `Choice.NameComparison` uses the names and uniform satisfaction; `Choice.OrderTable` also needs the step construction. Names need occurrence abstraction and syntax coding; the internal route needs the full schemes and numerals. |
| The relevant constructibility and coding prerequisites | Complete the Choice proof; develop the ordinal/cardinal tools, coded injections, Cantor-Bernstein and `CardinalAbove` | The cardinal tools do not require `Choice.Transversal` or `L.Model`. The final `GCH.Theorem` requires `L.Model` together with the cardinal bounds. The intervening GCH proof has additional shared dependencies. |
| The required coding and order interfaces | Satisfaction/hierarchy descriptions; Skolem hull construction | `GCH.CondensationTransfer` combines `GCH.SkolemHull`, `GCH.HierarchyDescription` and `GCH.AdequateStages`. The hull branch already needs `Choice.StageOrders`; it is not independent of all Choice material. |

For example, `L.WellOrder.Base` can be read when the order route needs it,
without first finishing the satisfaction route. Conversely, satisfaction coding
does not require completing the canonical order. Long separation between two
chapters on this example path therefore need not represent a wait on either
branch. Local examples and applications still matter within each chosen route.
<!--zh-->
### 并行路线与汇合点

先修图决定哪些章节已经可以阅读，目录序号不规定统一进度。下表各分支仍须完成自身的先修，具体见依赖地图；进入汇合章节时，再完成两边所需的内容。一条分支也可能使用另一条分支不需要的早期公共材料。

| 共同准备 | 可以分别推进的主题 | 汇合条件 |
|---|---|---|
| 基础、一阶语法与语义 | 常元与变量操作；环境层级、小性与模型 | `L.Definability` 同时使用语义重标与环境小性；`L.Constructible` 还需要 `V.Model`。出现抽象可继续独立推进，到名字构造时再接入 |
| 可构造阶段、序数与基本公理 | `Choice.FiniteStageOrders`、`Choice.CanonicalNames`、`Choice.StageOrders` 的外部典范序；通向 `Coding.UniformSatisfaction` 的内部满足编码 | `Choice.NameComparison` 同时使用名字与统一满足；`Choice.OrderTable` 还需要一步序构造。名字线需要出现抽象与语法编码；内部编码线需要完全公理模式与数码 |
| 各自所需的可构造性与编码基础 | 完成 Choice 证明；发展序数基数工具、编码单射、Cantor-Bernstein 与 `CardinalAbove` | 这些基数工具不依赖 `Choice.Transversal` 或 `L.Model`。最终 `GCH.Theorem` 需要 `L.Model` 与基数界共同就绪；中间的 GCH 证明另有共享依赖 |
| 所需的编码与序接口 | 满足关系、层级的描述；Skolem 壳构造 | `GCH.CondensationTransfer` 汇合 `GCH.SkolemHull`、`GCH.HierarchyDescription` 与 `GCH.AdequateStages`。壳线已需要 `Choice.StageOrders`，不能说它独立于所有 Choice 内容 |

例如，序构造线在需要时就可以转入 `L.WellOrder.Base`，无须先读完满足关系线；反过来，满足编码也无须等待典范序全部完成。因此，这条示例路线中相隔很远的两章，不一定在任何一条分支上造成等待。每条选定路线内部，仍应关注本章实例与实际应用。
<!--ja-->
### 並行するルートと合流点

前提となる章を読み終えれば，その先の主題に進めます。目次の番号は共通の時間割ではありません。各ルートに必要な前提を依存マップで確かめ，二つのルートが合流する章では両方の内容を揃えましょう。

| 共通の準備 | 別々に進められる主題 | 合流するところ |
|---|---|---|
| 基礎，一階論理の構文と意味論 | 定数と変数の操作；周囲の階層，小ささ，モデル | `L.Definability` は定数の改名と周囲の小ささを使い，`L.Constructible` はさらに `V.Model` を使います。出現の抽象は，名前の構成で必要になるまで別に学べます |
| 構成可能段階，順序数，基本公理 | `Choice.FiniteStageOrders`，`Choice.CanonicalNames`，`Choice.StageOrders` の外部の正準順序；`Coding.UniformSatisfaction` までの内部の充足関係の符号化 | `Choice.NameComparison` は名前と一様な充足関係を合わせ，`Choice.OrderTable` は一段階の順序構成も使います。名前には出現の抽象と構文の符号化，内部の符号化には完全な公理図式と数項が必要です |
| 各主題に必要な構成可能性と符号化 | 選択公理の証明；順序数と基数，符号化された単射，Cantor-Bernstein，`CardinalAbove` | 基数の道具は `Choice.Transversal` や `L.Model` を必要としません。最終的な `GCH.Theorem` では `L.Model` と基数の上界を合わせます。途中の GCH の議論には別の共有前提もあります |
| 必要な符号化と順序の結果 | 充足関係と階層の記述；Skolem 包の構成 | `GCH.CondensationTransfer` は `GCH.SkolemHull`，`GCH.HierarchyDescription`，`GCH.AdequateStages` を合わせます。包のルートも `Choice.StageOrders` を必要とするため，選択公理の全内容から独立ではありません |

例えば，順序のルートで必要になった時点で `L.WellOrder.Base` に進めます。充足関係のルートを先に終える必要はありません。逆に，充足関係の符号化も正準順序の完成を待つ必要はありません。この例示ルートで離れている二章が，各分岐でも長い待ち時間を生むとは限りません。
<!--/-->

<!--en-->
The closed code domain is described before it is used in satisfaction formulas. Its soundness and completeness are proved in `L.Coding.CodeDomainAdequacy` when the GCH description route needs them; that proof is not a prerequisite for the whole internal-coding route.
<!--zh-->
封闭码定义域先被描述，再用于满足关系公式。其可靠性与完备性在 GCH 描述路线需要时，由 `L.Coding.CodeDomainAdequacy` 证明；整条内部编码路线不必以这份证明为先修。
<!--ja-->
閉じた符号の定義域を先に記述し，充足関係の論理式で使います。その健全性と完全性は，GCH の記述ルートで必要になるときに `L.Coding.CodeDomainAdequacy` で証明します。内部の符号化ルート全体の前提として先に読む必要はありません。
<!--/-->

<!-- bedrock-routes
{
  "version": 1,
  "routes": [
    {
      "id": "common-foundations",
      "title": {
        "en": "Common foundations",
        "zh": "共同基础",
        "ja": "共通の基礎"
      },
      "description": {
        "en": "Shared propositions, first-order syntax, semantics, and model interfaces.",
        "zh": "共用的命题、一阶语法、语义与模型接口。",
        "ja": "命題，一階論理の構文と意味，集合論の構造を学びます。"
      },
      "chapters": [
        "Base.Prelude",
        "Base.Truth",
        "Base.Impredicativity",
        "Base.Classical",
        "Base.Choice",
        "FOL.Syntax",
        "FOL.ZFStructure",
        "FOL.Semantics",
        "FOL.LevyHierarchy",
        "FOL.Absoluteness",
        "FOL.ZFModel",
        "FOL.Coding"
      ]
    },
    {
      "id": "fol-operations",
      "title": {
        "en": "Operations on formulas",
        "zh": "公式操作",
        "ja": "論理式の操作"
      },
      "description": {
        "en": "Mapping, renaming, relabelling, bounds, occurrences, and parameters.",
        "zh": "公式的映射、改名、重标、有界化、出现与参数抽象。",
        "ja": "定数の写像，変数の改名，有界化，出現とパラメータの抽象を学びます。"
      },
      "chapters": [
        "FOL.Manipulation.ConstantMapping",
        "FOL.Manipulation.Renaming",
        "FOL.Manipulation.Relabelling",
        "FOL.Manipulation.Relativization",
        "FOL.Manipulation.ConstantBounding",
        "FOL.Manipulation.ConstantOccurrences",
        "FOL.Manipulation.ParameterAbstraction"
      ]
    },
    {
      "id": "ambient-model",
      "title": {
        "en": "The ambient model",
        "zh": "环境模型",
        "ja": "周囲のモデル"
      },
      "description": {
        "en": "The cumulative hierarchy, small truth values, model, and concrete codes.",
        "zh": "累积层级、小真值、模型与具体编码。",
        "ja": "累積階層，真理値の大きさ，モデル，具体的な符号を学びます。"
      },
      "chapters": [
        "V.Hierarchy",
        "V.Smallness",
        "V.Model",
        "V.Coding"
      ]
    },
    {
      "id": "constructible-axioms",
      "title": {
        "en": "Constructible stages and axioms",
        "zh": "可构造阶段与公理",
        "ja": "構成可能段階と公理"
      },
      "description": {
        "en": "Definability, stages, ordinals, reflection, and the axioms before Choice.",
        "zh": "可定义性、阶段、序数、反射与选择之前的公理。",
        "ja": "定義可能性，段階，順序数，反映から，選択以外の公理を証明します。"
      },
      "chapters": [
        "L.Definability",
        "L.Constructible",
        "L.Ordinal",
        "L.Rank",
        "L.Ordinal.Linear",
        "L.Ordinal.Stages",
        "L.Stage",
        "L.Axioms.Basic",
        "L.Axioms.Separation",
        "L.ExistentialReflection",
        "L.FormulaReflection",
        "L.Axioms.Full",
        "L.Axioms.Power",
        "L.Absoluteness",
        "L.Axioms.Numerals",
        "L.Axioms.Infinity"
      ]
    },
    {
      "id": "canonical-order",
      "title": {
        "en": "The external canonical order",
        "zh": "外部典范序",
        "ja": "外部の正準順序"
      },
      "description": {
        "en": "Well-orders, finite stages, names, and the external order step.",
        "zh": "良序、有限阶段、名字与外部序步骤。",
        "ja": "整列順序，有限段階，名前，段階ごとの順序を学びます。"
      },
      "chapters": [
        "L.Choice.FirstIntersectionStage",
        "L.WellOrder.Base",
        "L.Choice.FiniteStageOrders",
        "L.Choice.CanonicalNames",
        "L.Choice.StageOrders"
      ]
    },
    {
      "id": "internal-satisfaction",
      "title": {
        "en": "Internal coding and satisfaction",
        "zh": "内部编码与满足关系",
        "ja": "内部の符号化と充足関係"
      },
      "description": {
        "en": "Readers, code domains, recursion tables, uniform satisfaction, and hierarchy.",
        "zh": "读式、码域、递归表、统一满足关系与层级。",
        "ja": "符号の読み取り，閉じた定義域，再帰表，一様な充足関係と階層を学びます。"
      },
      "chapters": [
        "L.Coding.PairFormulas",
        "L.Coding.Environment",
        "L.Coding.Model",
        "L.Coding.Expressions",
        "L.Coding.Closure",
        "L.Coding.Descent",
        "L.Coding.CodeConstructibility",
        "L.Coding.SubformulaClosure",
        "L.Coding.EnvironmentSet",
        "L.Coding.Satisfaction",
        "L.Coding.SatisfactionBridge",
        "L.Coding.SatisfactionTable",
        "L.Coding.EnvironmentAgreement",
        "L.Coding.SlotClosure",
        "L.Coding.CodeShape",
        "L.Coding.FormulaRecovery",
        "L.Coding.NumeralBound",
        "L.Coding.Quantification",
        "L.Recursion",
        "L.Recursion.Graph",
        "L.Coding.EnvironmentTower",
        "L.Coding.CodeSet",
        "L.Coding.CodeDomain",
        "L.Coding.SatisfactionClauses",
        "L.Coding.CodeAlphabet",
        "L.Coding.SatisfactionClauseSemantics",
        "L.Coding.PinnedRecursion",
        "L.Coding.SatisfactionGraph",
        "L.Coding.UniformSatisfaction",
        "L.Coding.DefinablePowerSet",
        "L.Coding.HierarchySequence",
        "L.Hierarchy"
      ]
    },
    {
      "id": "choice-completion",
      "title": {
        "en": "Internal order and Choice",
        "zh": "内部典范序与选择",
        "ja": "内部の順序と選択公理"
      },
      "description": {
        "en": "The external order and uniform coding meet to prove Choice and ZFC.",
        "zh": "外部序与统一编码汇合，证明选择公理与 ZFC。",
        "ja": "外部の順序と一様な符号化を合わせ，選択公理と ZFC を証明します。"
      },
      "chapters": [
        "L.Choice.NameComparison",
        "L.Choice.OrderTable",
        "L.Choice.StageOrderAdequacy",
        "L.Choice.NameComparisonAdequacy",
        "L.Choice.LimitStageOrder",
        "L.Choice.EarliestDisagreement",
        "L.Choice.InternalWellOrder",
        "L.Choice.Transversal",
        "L.Model"
      ]
    },
    {
      "id": "cardinal-tools",
      "title": {
        "en": "Ordinal and cardinal tools",
        "zh": "序数与基数工具",
        "ja": "順序数と基数"
      },
      "description": {
        "en": "Presentations, square laws, coded injections, cardinals, and GCH assembly.",
        "zh": "呈现、平方律、编码单射、基数与 GCH 组装。",
        "ja": "集合の提示，平方律，符号化された単射と基数を学び，GCH の証明を組み立てます。"
      },
      "chapters": [
        "V.Presentation",
        "L.Ordinal.SquareLaw",
        "L.Coding.Injection",
        "L.Cardinal",
        "L.DefinableInjection",
        "L.InjectionComposition",
        "L.GCH",
        "V.CantorBernstein",
        "L.CantorBernstein",
        "L.Mostowski",
        "L.CardinalAbove",
        "L.GCH.Assembly"
      ]
    },
    {
      "id": "gch-descriptions",
      "title": {
        "en": "Descriptions for GCH",
        "zh": "GCH 的内部描述",
        "ja": "GCH の内部記述"
      },
      "description": {
        "en": "Descriptions of satisfaction, definability, adequate stages, and hierarchy.",
        "zh": "满足关系、可定义性、充分阶段与层级的内部描述。",
        "ja": "充足関係，定義可能性，十分な段階と階層を内部で記述します。"
      },
      "chapters": [
        "L.Coding.SatisfactionGraphSet",
        "L.Coding.CodeDomainAdequacy",
        "L.GCH.SatisfactionDescription",
        "L.GCH.DefinablePowerSetDescription",
        "L.GCH.AdequateStages",
        "L.GCH.OmegaRecursion",
        "L.GCH.HierarchyDescription"
      ]
    },
    {
      "id": "hulls-and-counting",
      "title": {
        "en": "Hulls, collapse, and counting",
        "zh": "壳、塌缩与计数",
        "ja": "包，崩壊と数え上げ"
      },
      "description": {
        "en": "The hull branch meets order and description branches to prove the bounds.",
        "zh": "壳分支与序及描述分支汇合，证明基数界。",
        "ja": "包の構成を順序と内部記述に結び付け，基数の上界を証明します。"
      },
      "chapters": [
        "L.Choice.StageOrders",
        "L.Coding.CodeConstructibility",
        "V.Collapse",
        "L.GCH.SkolemHull",
        "L.GCH.HierarchyDescription",
        "L.GCH.CondensationTransfer",
        "L.GCH.BelowSuccessorCardinal",
        "L.GCH.OrderType",
        "L.GCH.CardinalRepresentative",
        "L.GCH.CardinalSquareLaw",
        "L.GCH.LeastWitnessMap",
        "L.GCH.SuccessorIntoPowerSet",
        "L.GCH.FiniteSequenceCoding",
        "L.GCH.StageCountingTools",
        "L.GCH.ConstructibleHull",
        "L.GCH.HullCounting",
        "L.GCH.StageInjection",
        "L.GCH.BoundedSubset",
        "L.GCH.Theorem"
      ]
    }
  ]
}
-->

<!--en-->
## Preview

Start with the destination. These signatures state exactly what the book proves
and which classical assumption each endpoint consumes.

- `Landmarks`{.Agda}: Main theorems
<!--zh-->
## 开篇预览

先看终点。这些签名准确陈述全书证明了什么，以及每个终点花费哪项经典假设。

- `Landmarks`{.Agda}：主要定理
<!--ja-->
## 最終定理の展望

まず，この本が目指す定理の形を見ます。L が ZFC と一般連続体仮説を満たすという主張と，その証明で仮定する排中律を確認します。証明に必要な概念は，後の章で順に学びます。

- `Landmarks`{.Agda}：主要定理
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

- `Base.Prelude`{.Agda}: Prelude
- `Base.Truth`{.Agda}: Truth values
- `Base.Impredicativity`{.Agda}: Impredicativity
- `Base.Classical`{.Agda}: The classical boundary
- `Base.Choice`{.Agda}: Choice
<!--zh-->
## 基础

全书先统一命题、宇宙大小与两项经典接口的语言。在任何集合模型出现之前，本部先把所用假设明确写出。

- `Base.Prelude`{.Agda}：基础词汇
- `Base.Truth`{.Agda}：真值
- `Base.Impredicativity`{.Agda}：非直谓性
- `Base.Classical`{.Agda}：经典逻辑的边界
- `Base.Choice`{.Agda}：选择原理
<!--ja-->
## 基礎

命題について推論するための記法と，型が属する宇宙の大きさを学びます。続いて，排中律と集合に対する選択原理を区別し，これらが命題の大きさにどのような影響を与えるかを調べます。

- `Base.Prelude`{.Agda}：基礎語彙
- `Base.Truth`{.Agda}：真理値
- `Base.Impredicativity`{.Agda}：非可述性
- `Base.Classical`{.Agda}：古典論理との境界
- `Base.Choice`{.Agda}：選択原理
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

- `FOL.Syntax`{.Agda}: The object language
- `FOL.ZFStructure`{.Agda}: Structures
- `FOL.Semantics`{.Agda}: Semantics
- `FOL.LevyHierarchy`{.Agda}: The Lévy hierarchy
- `FOL.Absoluteness`{.Agda}: Absoluteness
- `FOL.ZFModel`{.Agda}: Models of ZF and ZFC
- `FOL.Manipulation.ConstantMapping`{.Agda}: Mapping constants
- `FOL.Manipulation.Renaming`{.Agda}: Variable renaming
- `FOL.Manipulation.Relabelling`{.Agda}: Constant relabelling
- `FOL.Manipulation.Relativization`{.Agda}: Relativization
- `FOL.Manipulation.ConstantBounding`{.Agda}: Constant bounding
- `FOL.Manipulation.ConstantOccurrences`{.Agda}: Constants by occurrence
- `FOL.Manipulation.ParameterAbstraction`{.Agda}: Parameter abstraction
- `FOL.Coding`{.Agda}: Syntax as sets
<!--zh-->
## 一阶逻辑

ZFC 与 GCH 将在模型内部得到证明，故其语法与语义本身必须成为数学对象。本部给出公式、复杂度、代换与编码，供后面的内部论证使用。

- `FOL.Syntax`{.Agda}：对象语言
- `FOL.ZFStructure`{.Agda}：结构
- `FOL.Semantics`{.Agda}：语义
- `FOL.LevyHierarchy`{.Agda}：莱维层级
- `FOL.Absoluteness`{.Agda}：绝对性
- `FOL.ZFModel`{.Agda}：ZF 与 ZFC 的模型
- `FOL.Manipulation.ConstantMapping`{.Agda}：映射常元
- `FOL.Manipulation.Renaming`{.Agda}：变量改名
- `FOL.Manipulation.Relabelling`{.Agda}：常元改名
- `FOL.Manipulation.Relativization`{.Agda}：相对化
- `FOL.Manipulation.ConstantBounding`{.Agda}：常元有界性
- `FOL.Manipulation.ConstantOccurrences`{.Agda}：逐次出现地处理常元
- `FOL.Manipulation.ParameterAbstraction`{.Agda}：参数抽象
- `FOL.Coding`{.Agda}：作为集合的语法
<!--ja-->
## 一階論理

集合論の主張を論理式として書き，構造の中でその意味を定めます。論理式の複雑さ，変数や定数の操作，集合による符号化を学ぶことで，後に L 自身の中で論理式を扱う準備ができます。

- `FOL.Syntax`{.Agda}：対象言語
- `FOL.ZFStructure`{.Agda}：構造
- `FOL.Semantics`{.Agda}：意味論
- `FOL.LevyHierarchy`{.Agda}：レヴィ階層
- `FOL.Absoluteness`{.Agda}：絶対性
- `FOL.ZFModel`{.Agda}：ZF と ZFC のモデル
- `FOL.Manipulation.ConstantMapping`{.Agda}：定数の写像
- `FOL.Manipulation.Renaming`{.Agda}：変数の改名
- `FOL.Manipulation.Relabelling`{.Agda}：定数の改名
- `FOL.Manipulation.Relativization`{.Agda}：相対化
- `FOL.Manipulation.ConstantBounding`{.Agda}：定数の有界性
- `FOL.Manipulation.ConstantOccurrences`{.Agda}：出現ごとに扱う定数
- `FOL.Manipulation.ParameterAbstraction`{.Agda}：パラメータ抽象
- `FOL.Coding`{.Agda}：集合としての構文
<!--/-->
```agda
import FOL.Syntax
import FOL.ZFStructure
import FOL.Semantics
import FOL.LevyHierarchy
import FOL.Absoluteness
import FOL.ZFModel
import FOL.Manipulation.ConstantMapping
import FOL.Manipulation.Renaming
import FOL.Manipulation.Relabelling
import FOL.Manipulation.Relativization
import FOL.Manipulation.ConstantBounding
import FOL.Manipulation.ConstantOccurrences
import FOL.Manipulation.ParameterAbstraction
import FOL.Coding
```

<!--en-->
## The ambient hierarchy

The cumulative hierarchy is the ambient universe in which all later sets and
codes are built. Its smallness, model theorems, and syntax coding provide the concrete semantics that the abstract logic now needs.

- `V.Hierarchy`{.Agda}: The cumulative hierarchy
- `V.Smallness`{.Agda}: Small truth values in the cumulative hierarchy
- `V.Model`{.Agda}: The cumulative hierarchy models ZF and ZFC
- `V.Coding`{.Agda}: Coding inside the cumulative hierarchy
<!--zh-->
## 环境层级

累积层级是后面一切集合与码的环境宇宙。它的小性、模型定理与语法编码，为刚建立的抽象逻辑提供具体语义。

- `V.Hierarchy`{.Agda}：累积层级
- `V.Smallness`{.Agda}：累积层级中的小真值
- `V.Model`{.Agda}：累积层级是 ZF 与 ZFC 的模型
- `V.Coding`{.Agda}：累积层级内的符号化
<!--ja-->
## 周囲の累積階層

累積階層 V を，これから集合を構成する宇宙として調べます。帰属関係と真理値の大きさを確かめ，V が集合論の公理を満たすことを学び，論理式を具体的な集合で表します。

- `V.Hierarchy`{.Agda}：累積階層
- `V.Smallness`{.Agda}：累積階層における小さな真理値
- `V.Model`{.Agda}：累積階層は ZF と ZFC のモデル
- `V.Coding`{.Agda}：累積階層の内部での符号化
<!--/-->
```agda
import V.Hierarchy
import V.Smallness
import V.Model
import V.Coding
```

<!--en-->
## Constructible stages and the axioms

Definability now generates the stages of `L`, while ordinals and rank control
where constructions live. Reflection then upgrades bounded closure facts to the full ZF schemes and leaves only Choice for the ZFC endpoint.

- `L.Definability`{.Agda}: Definable subsets of a set
- `L.Constructible`{.Agda}: The constructible hierarchy and universe
- `L.Ordinal`{.Agda}: Ordinal closure and finite ordinals
- `L.Rank`{.Agda}: Von Neumann rank
- `L.Ordinal.Linear`{.Agda}: Ordinals are linearly ordered by membership
- `L.Ordinal.Stages`{.Agda}: Locating ordinals in the constructible hierarchy
- `L.Stage`{.Agda}: The index of the least constructible stage
- `L.Axioms.Basic`{.Agda}: The basic axioms
- `L.Axioms.Separation`{.Agda}: Separation and replacement, bounded
- `L.ExistentialReflection`{.Agda}: Existential reflection into a constructible stage
- `L.FormulaReflection`{.Agda}: Reflection for an arbitrary formula
- `L.Axioms.Full`{.Agda}: Separation and replacement, in full
- `L.Axioms.Power`{.Agda}: The power set in L
- `L.Absoluteness`{.Agda}: From ambient formulas to formulas over L
- `L.Axioms.Numerals`{.Agda}: The numeral chain
- `L.Axioms.Infinity`{.Agda}: The axiom of infinity in L
<!--zh-->
## 可构造阶段与公理

可定义性现在生成可构造宇宙 `L` 的诸阶段，序数与秩则控制各种构造落在哪一层。反射随后把有界闭包提升为完整的 ZF 模式，使 ZFC 终点只余选择公理。

- `L.Definability`{.Agda}：集合的可定义子集
- `L.Constructible`{.Agda}：可构造层级与可构造宇宙
- `L.Ordinal`{.Agda}：序数的封闭性与有限序数
- `L.Rank`{.Agda}：Von Neumann 秩
- `L.Ordinal.Linear`{.Agda}：序数由隶属关系线性排序
- `L.Ordinal.Stages`{.Agda}：在可构造层级中定位序数
- `L.Stage`{.Agda}：最小可构造阶段的索引
- `L.Axioms.Basic`{.Agda}：基本公理
- `L.Axioms.Separation`{.Agda}：有界分离与替换
- `L.ExistentialReflection`{.Agda}：存在公式到可构造阶段的反射
- `L.FormulaReflection`{.Agda}：任意公式的反射
- `L.Axioms.Full`{.Agda}：完整的分离与替换
- `L.Axioms.Power`{.Agda}：L 中的幂集
- `L.Absoluteness`{.Agda}：环境公式到 L 上公式
- `L.Axioms.Numerals`{.Agda}：数码链
- `L.Axioms.Infinity`{.Agda}：L 中的无穷公理
<!--ja-->
## 構成可能段階と公理

パラメータを用いて定義できる部分集合を集め，構成可能宇宙 L の段階を作ります。順序数とランクで集合の位置を調べ，反映を用いて分出と置換を証明します。さらに，L の内部で冪集合と無限集合を構成します。

- `L.Definability`{.Agda}：集合の定義可能な部分集合
- `L.Constructible`{.Agda}：構成可能階層と構成可能宇宙
- `L.Ordinal`{.Agda}：順序数の閉性と有限順序数
- `L.Rank`{.Agda}：von Neumann ランク
- `L.Ordinal.Linear`{.Agda}：順序数は所属によって線形に順序付けられる
- `L.Ordinal.Stages`{.Agda}：構成可能階層の中で順序数を位置付ける
- `L.Stage`{.Agda}：最小の構成可能段階の添字
- `L.Axioms.Basic`{.Agda}：基本公理
- `L.Axioms.Separation`{.Agda}：有界な分出公理と置換公理
- `L.ExistentialReflection`{.Agda}：存在論理式の構成可能段階への反映
- `L.FormulaReflection`{.Agda}：任意の論理式に対する反映
- `L.Axioms.Full`{.Agda}：完全な分出公理と置換公理
- `L.Axioms.Power`{.Agda}：L における冪集合
- `L.Absoluteness`{.Agda}：周囲の論理式から L 上の論理式へ
- `L.Axioms.Numerals`{.Agda}：数項列
- `L.Axioms.Infinity`{.Agda}：L における無限公理
<!--/-->
```agda
import L.Definability
import L.Constructible
import L.Ordinal
import L.Rank
import L.Ordinal.Linear
import L.Ordinal.Stages
import L.Stage
import L.Axioms.Basic
import L.Axioms.Separation
import L.ExistentialReflection
import L.FormulaReflection
import L.Axioms.Full
import L.Axioms.Power
import L.Absoluteness
import L.Axioms.Numerals
import L.Axioms.Infinity
```

<!--en-->
## Internal coding: expressions and domains

To reason about truth inside `L`, the external syntax must be readable there as
sets. This stage builds the elementary readers and the closed code domains on which later recursive tables may safely descend.

- `L.Coding.PairFormulas`{.Agda}: Formulas for singletons and pairs
- `L.Coding.Environment`{.Agda}: Finite environments as set-coded graphs
- `L.Coding.Model`{.Agda}: Coding formulas over the constructible model
- `L.Coding.Expressions`{.Agda}: Formula expressions for coded recursion
- `L.Coding.Closure`{.Agda}: Subcode-closed domains
- `L.Coding.Descent`{.Agda}: Rank descent through coded pairs
- `L.Coding.CodeConstructibility`{.Agda}: Constructible codes and subformula trees
- `L.Coding.SubformulaClosure`{.Agda}: Closure under subformulas
<!--zh-->
## 内部编码：表达式与定义域

要在 `L` 内部推理真值，外部语法必须在那里作为集合被读出。本部建立基础读式与封闭码域，使后续递归表能够安全地沿码下降。

- `L.Coding.PairFormulas`{.Agda}：单点集与有序对的公式
- `L.Coding.Environment`{.Agda}：作为集合编码图的有穷环境
- `L.Coding.Model`{.Agda}：可构造模型上的公式符号化
- `L.Coding.Expressions`{.Agda}：码化递归所用的公式表达式
- `L.Coding.Closure`{.Agda}：对子码封闭的定义域
- `L.Coding.Descent`{.Agda}：沿编码对作秩下降
- `L.Coding.CodeConstructibility`{.Agda}：可构造编码与子公式树
- `L.Coding.SubformulaClosure`{.Agda}：对子公式封闭
<!--ja-->
## 内部の符号化：式と定義域

L の内部で論理式について語るには，その符号や代入環境を集合として認識する必要があります。対やタグを読む論理式から始め，部分論理式の符号を含む閉じた定義域を作ります。

- `L.Coding.PairFormulas`{.Agda}：単集合と対を表す論理式
- `L.Coding.Environment`{.Agda}：集合で符号化した有限環境
- `L.Coding.Model`{.Agda}：構成可能モデル上の論理式の符号化
- `L.Coding.Expressions`{.Agda}：符号化再帰のための論理式表現
- `L.Coding.Closure`{.Agda}：部分符号に閉じた定義域
- `L.Coding.Descent`{.Agda}：符号化された対に沿う階数降下
- `L.Coding.CodeConstructibility`{.Agda}：構成可能なコードと部分式の木
- `L.Coding.SubformulaClosure`{.Agda}：部分式についての閉包
<!--/-->
```agda
import L.Coding.PairFormulas
import L.Coding.Environment
import L.Coding.Model
import L.Coding.Expressions
import L.Coding.Closure
import L.Coding.Descent
import L.Coding.CodeConstructibility
import L.Coding.SubformulaClosure
```

<!--en-->
## Internal coding: tables and uniform satisfaction

This stage builds tables whose clauses compute semantic values, then brings in
bounded pair quantification and internal recursion for their uniform description. By the end of this stage, satisfaction and the constructible hierarchy are uniformly describable inside `L`, ready for both Choice and GCH.

- `L.Coding.EnvironmentSet`{.Agda}: The set of fixed-length environments
- `L.Coding.Satisfaction`{.Agda}: Satisfaction by recursion on formulas
- `L.Coding.SatisfactionBridge`{.Agda}: Satisfaction and the recursion value
- `L.Coding.SatisfactionTable`{.Agda}: Satisfaction tables over subformulas
- `L.Coding.EnvironmentAgreement`{.Agda}: Agreement of environment sets
- `L.Coding.SlotClosure`{.Agda}: Closing a code slot under its seven constructors
- `L.Coding.CodeShape`{.Agda}: Recognizing well-formed constructor keys
- `L.Coding.FormulaRecovery`{.Agda}: Recovering formulas from codes
- `L.Coding.NumeralBound`{.Agda}: Numerals in a successor-closed ordinal stage
- `L.Coding.Quantification`{.Agda}: Quantifying over coded pairs and finite formula families
- `L.Recursion`{.Agda}: Internalizing recursive definitions in L
- `L.Recursion.Graph`{.Agda}: Graphs of recursive definitions
- `L.Coding.EnvironmentTower`{.Agda}: The environment tower
- `L.Coding.CodeSet`{.Agda}: The set of all formula codes
- `L.Coding.CodeDomain`{.Agda}: Describing the closed domain of formula codes
- `L.Coding.SatisfactionClauses`{.Agda}: Describing the satisfaction table
- `L.Coding.CodeAlphabet`{.Agda}: The alphabet of formula codes
- `L.Coding.SatisfactionClauseSemantics`{.Agda}: Reading and validating the satisfaction clauses
- `L.Coding.PinnedRecursion`{.Agda}: Recursion pinned to a subcode-closed index set
- `L.Coding.SatisfactionGraph`{.Agda}: The satisfaction graph formula
- `L.Coding.UniformSatisfaction`{.Agda}: Uniform satisfaction over all codes
- `L.Coding.DefinablePowerSet`{.Agda}: A formula for the definable power set
- `L.Coding.HierarchySequence`{.Agda}: A sequence for the constructible hierarchy
- `L.Hierarchy`{.Agda}: The constructible hierarchy inside L
<!--zh-->
## 内部编码：表与统一满足关系

本部先构造依子句计算语义值的表，再引入有界配对量化与内部递归，统一描述这些表。本部结束时，满足关系与可构造层级都能在 `L` 内统一描述，从而为选择公理与 GCH 同时备妥工具。

- `L.Coding.EnvironmentSet`{.Agda}：定长环境之集
- `L.Coding.Satisfaction`{.Agda}：沿公式递归构造满足关系
- `L.Coding.SatisfactionBridge`{.Agda}：满足关系与递归取值
- `L.Coding.SatisfactionTable`{.Agda}：子公式上的满足关系表
- `L.Coding.EnvironmentAgreement`{.Agda}：环境集的一致性
- `L.Coding.SlotClosure`{.Agda}：使编码槽位对七种构造闭合
- `L.Coding.CodeShape`{.Agda}：良构构造子键的识别
- `L.Coding.FormulaRecovery`{.Agda}：从码恢复公式
- `L.Coding.NumeralBound`{.Agda}：对后继封闭的序数阶段中的数码
- `L.Coding.Quantification`{.Agda}：对码化有序对分量与有穷公式族量化
- `L.Recursion`{.Agda}：L 中递归定义的内部化
- `L.Recursion.Graph`{.Agda}：递归定义的图
- `L.Coding.EnvironmentTower`{.Agda}：环境塔
- `L.Coding.CodeSet`{.Agda}：全体公式码之集
- `L.Coding.CodeDomain`{.Agda}：描述封闭的公式码定义域
- `L.Coding.SatisfactionClauses`{.Agda}：描述满足关系表
- `L.Coding.CodeAlphabet`{.Agda}：公式码的字母表
- `L.Coding.SatisfactionClauseSemantics`{.Agda}：读取并验证满足关系子句
- `L.Coding.PinnedRecursion`{.Agda}：固定在对子码封闭的索引集上的递归
- `L.Coding.SatisfactionGraph`{.Agda}：满足关系图公式
- `L.Coding.UniformSatisfaction`{.Agda}：全部编码上的一致满足关系
- `L.Coding.DefinablePowerSet`{.Agda}：可定义幂集的公式
- `L.Coding.HierarchySequence`{.Agda}：可构造层级的序列
- `L.Hierarchy`{.Agda}：L 内部的可构造层级
<!--ja-->
## 内部の符号化：表と一様な充足関係

論理式の意味を再帰的に計算し，その値を表に集めます。部分論理式を扱う各節と表の一意性を調べ，充足関係を一様に記述します。この記述から，定義可能冪集合と構成可能階層も L の内部で表せるようになります。

- `L.Coding.EnvironmentSet`{.Agda}：固定長環境の集合
- `L.Coding.Satisfaction`{.Agda}：論理式上の再帰による充足関係
- `L.Coding.SatisfactionBridge`{.Agda}：充足関係と再帰の値
- `L.Coding.SatisfactionTable`{.Agda}：部分式上の充足関係表
- `L.Coding.EnvironmentAgreement`{.Agda}：環境の集合の一致
- `L.Coding.SlotClosure`{.Agda}：コードスロットを七つの構成子について閉じる
- `L.Coding.CodeShape`{.Agda}：整形式な構成子キーの認識
- `L.Coding.FormulaRecovery`{.Agda}：コードから論理式を復元する
- `L.Coding.NumeralBound`{.Agda}：後者演算について閉じた順序数段階の数項
- `L.Coding.Quantification`{.Agda}：符号化された順序対の成分と有限論理式族を量化する
- `L.Recursion`{.Agda}：L における再帰的定義の内部化
- `L.Recursion.Graph`{.Agda}：再帰的定義のグラフ
- `L.Coding.EnvironmentTower`{.Agda}：環境の塔
- `L.Coding.CodeSet`{.Agda}：すべての論理式の符号からなる集合
- `L.Coding.CodeDomain`{.Agda}：閉じた論理式符号の定義域を記述する
- `L.Coding.SatisfactionClauses`{.Agda}：充足関係表を記述する
- `L.Coding.CodeAlphabet`{.Agda}：論理式符号のアルファベット
- `L.Coding.SatisfactionClauseSemantics`{.Agda}：充足関係の節の読み取りと検証
- `L.Coding.PinnedRecursion`{.Agda}：部分符号で閉じた添字集合に固定された再帰
- `L.Coding.SatisfactionGraph`{.Agda}：充足関係のグラフを表す論理式
- `L.Coding.UniformSatisfaction`{.Agda}：全コード上の一様な充足関係
- `L.Coding.DefinablePowerSet`{.Agda}：定義可能な冪集合を表す論理式
- `L.Coding.HierarchySequence`{.Agda}：構成可能階層を表す列
- `L.Hierarchy`{.Agda}：L の内部における構成可能階層
<!--/-->
```agda
import L.Coding.EnvironmentSet
import L.Coding.Satisfaction
import L.Coding.SatisfactionBridge
import L.Coding.SatisfactionTable
import L.Coding.EnvironmentAgreement
import L.Coding.SlotClosure
import L.Coding.CodeShape
import L.Coding.FormulaRecovery
import L.Coding.NumeralBound
import L.Coding.Quantification
import L.Recursion
import L.Recursion.Graph
import L.Coding.EnvironmentTower
import L.Coding.CodeSet
import L.Coding.CodeDomain
import L.Coding.SatisfactionClauses
import L.Coding.CodeAlphabet
import L.Coding.SatisfactionClauseSemantics
import L.Coding.PinnedRecursion
import L.Coding.SatisfactionGraph
import L.Coding.UniformSatisfaction
import L.Coding.DefinablePowerSet
import L.Coding.HierarchySequence
import L.Hierarchy
```

<!--en-->
## The canonical well-order and Choice

Uniform descriptions let `L` compare names rather than arbitrary external sets.
Finite-stage orders grow into a global canonical order, whose least elements produce the transversal required by Choice.

- `L.Choice.FirstIntersectionStage`{.Agda}: The first stage meeting a set
- `L.WellOrder.Base`{.Agda}: Strict well-orders and least-element search
- `L.Choice.FiniteStageOrders`{.Agda}: Well-orders on finite stages
- `L.Choice.CanonicalNames`{.Agda}: Canonical names for successor-stage members
- `L.Choice.StageOrders`{.Agda}: Well-orders on all stages
- `L.Choice.NameComparison`{.Agda}: Formulas for name comparison
- `L.Choice.OrderTable`{.Agda}: An internal table of stage orders
- `L.Choice.StageOrderAdequacy`{.Agda}: Adequacy of the stage-order description
- `L.Choice.NameComparisonAdequacy`{.Agda}: Adequacy of name comparison
- `L.Choice.LimitStageOrder`{.Agda}: The limit-stage order inside L
- `L.Choice.EarliestDisagreement`{.Agda}: An internal family of earliest-disagreement relations
- `L.Choice.InternalWellOrder`{.Agda}: The internal canonical well-order
- `L.Choice.Transversal`{.Agda}: Choice by a transversal
- `L.Model`{.Agda}: The constructible universe models ZFC
<!--zh-->
## 典范良序与选择公理

统一描述使 `L` 能比较名字，而无须直接比较任意外部集合。有限阶段上的序扩展为全局典范序，其极小元给出选择公理所需的横截集。

- `L.Choice.FirstIntersectionStage`{.Agda}：首次与集合相交的阶段
- `L.WellOrder.Base`{.Agda}：严格良序与最小元搜索
- `L.Choice.FiniteStageOrders`{.Agda}：有限阶段上的良序
- `L.Choice.CanonicalNames`{.Agda}：后继阶段成员的典范名字
- `L.Choice.StageOrders`{.Agda}：各阶段上的良序
- `L.Choice.NameComparison`{.Agda}：名字比较的公式
- `L.Choice.OrderTable`{.Agda}：阶段序的内部表
- `L.Choice.StageOrderAdequacy`{.Agda}：阶段序描述的充分性
- `L.Choice.NameComparisonAdequacy`{.Agda}：名字比较的充分性
- `L.Choice.LimitStageOrder`{.Agda}：L 内部的极限阶段序
- `L.Choice.EarliestDisagreement`{.Agda}：最早分歧关系的内部族
- `L.Choice.InternalWellOrder`{.Agda}：内部典范良序
- `L.Choice.Transversal`{.Agda}：以横截集实现选择
- `L.Model`{.Agda}：可构造宇宙是 ZFC 的模型
<!--ja-->
## 正準整列順序と選択公理

定義に使う論理式とパラメータを集合の名前とし，その名前を比較して L を整列します。有限段階から段階ごとの順序へ進み，それらが合うことを確かめます。最後に各集合の最小元を選び，選択公理と ZFC の証明を完成させます。

- `L.Choice.FirstIntersectionStage`{.Agda}：集合と交わる最初の段階
- `L.WellOrder.Base`{.Agda}：狭義整列順序と最小要素の探索
- `L.Choice.FiniteStageOrders`{.Agda}：有限段階上の整列順序
- `L.Choice.CanonicalNames`{.Agda}：後者段階の要素の正準な名前
- `L.Choice.StageOrders`{.Agda}：各段階上の整列順序
- `L.Choice.NameComparison`{.Agda}：名前の比較を表す論理式
- `L.Choice.OrderTable`{.Agda}：段階順序の内部の表
- `L.Choice.StageOrderAdequacy`{.Agda}：段階順序の記述の妥当性
- `L.Choice.NameComparisonAdequacy`{.Agda}：名前の比較の妥当性
- `L.Choice.LimitStageOrder`{.Agda}：L の内部にある極限段階の順序
- `L.Choice.EarliestDisagreement`{.Agda}：最初の相違の関係からなる内部の族
- `L.Choice.InternalWellOrder`{.Agda}：内部の正準整列順序
- `L.Choice.Transversal`{.Agda}：横断集合による選択
- `L.Model`{.Agda}：構成可能宇宙は ZFC のモデル
<!--/-->
```agda
import L.Choice.FirstIntersectionStage
import L.WellOrder.Base
import L.Choice.FiniteStageOrders
import L.Choice.CanonicalNames
import L.Choice.StageOrders
import L.Choice.NameComparison
import L.Choice.OrderTable
import L.Choice.StageOrderAdequacy
import L.Choice.NameComparisonAdequacy
import L.Choice.LimitStageOrder
import L.Choice.EarliestDisagreement
import L.Choice.InternalWellOrder
import L.Choice.Transversal
import L.Model
```

<!--en-->
## Ordinals, injections and cardinals

We compare sets by representing injections inside L. Small presentations and ordinal orders lead to internal cardinality, definable injection graphs, and their composition. These tools support Cantor–Schröder–Bernstein, larger cardinals, and the later GCH bounds. They can be studied alongside the Choice route once their own prerequisites are ready.

- `V.Presentation`{.Agda}: Small presentations of sets
- `L.Ordinal.SquareLaw`{.Agda}: Ordinal indices, the Gödel pair order, and finite indices
- `L.Coding.Injection`{.Agda}: Coded injections
- `L.Cardinal`{.Agda}: Cardinals and coded injections inside L
- `L.DefinableInjection`{.Agda}: Turning a definable injection into an internal code
- `L.InjectionComposition`{.Agda}: Composition and inclusion of coded injections
- `L.GCH`{.Agda}: The generalized continuum hypothesis inside L
- `V.CantorBernstein`{.Agda}: Cantor–Schröder–Bernstein for small presentations
- `L.CantorBernstein`{.Agda}: Cantor–Schröder–Bernstein inside L
- `L.Mostowski`{.Agda}: Collapsing a transitive well-founded relation
- `L.CardinalAbove`{.Agda}: An ordinal L-cardinal above every L-cardinal
<!--zh-->
## 序数、单射与基数

我们通过在 L 内部表示单射来比较集合。小呈现与序数上的序引出内部基数、可定义单射图及其复合。这些工具用于 Cantor–Schröder–Bernstein 定理、更大基数的构造和后续 GCH 的基数界；只要各自的先修内容就绪，就可以与选择公理路线并行学习。

- `V.Presentation`{.Agda}：集合的小呈现
- `L.Ordinal.SquareLaw`{.Agda}：序数指标、Gödel 对序与有穷指标
- `L.Coding.Injection`{.Agda}：编码单射
- `L.Cardinal`{.Agda}：L 内部的基数与编码单射
- `L.DefinableInjection`{.Agda}：把可定义单射化为内部编码
- `L.InjectionComposition`{.Agda}：编码单射的复合与包含
- `L.GCH`{.Agda}：L 内部的广义连续统假设
- `V.CantorBernstein`{.Agda}：小呈现上的 Cantor–Schröder–Bernstein 定理
- `L.CantorBernstein`{.Agda}：L 内部的 Cantor–Schröder–Bernstein 定理
- `L.Mostowski`{.Agda}：传递良基关系的塌缩
- `L.CardinalAbove`{.Agda}：任意 L 基数之上的序数 L 基数
<!--ja-->
## 順序数，単射，基数

L の内部で単射を表すことで集合の大きさを比較します。小さな提示と順序数上の順序から，内部の基数，定義可能な単射のグラフ，その合成へ進みます。これらの道具は Cantor–Schröder–Bernstein 定理，より大きな基数の構成，後の GCH の基数評価に使われます。各章の前提が揃えば，選択公理のルートと並行して読めます。

- `V.Presentation`{.Agda}：集合の小さな提示
- `L.Ordinal.SquareLaw`{.Agda}：順序数の添字、Gödel 対順序、有限添字
- `L.Coding.Injection`{.Agda}：符号化された単射
- `L.Cardinal`{.Agda}：L の内部における基数と符号化された単射
- `L.DefinableInjection`{.Agda}：定義可能な単射を内部コードにする
- `L.InjectionComposition`{.Agda}：符号化された単射の合成と包含
- `L.GCH`{.Agda}：L の内部における一般連続体仮説
- `V.CantorBernstein`{.Agda}：小さな提示に対する Cantor–Schröder–Bernstein の定理
- `L.CantorBernstein`{.Agda}：L の内部における Cantor–Schröder–Bernstein の定理
- `L.Mostowski`{.Agda}：推移的な整礎関係の崩壊
- `L.CardinalAbove`{.Agda}：任意の L 基数より大きい順序数 L 基数
<!--/-->
```agda
import V.Presentation
import L.Ordinal.SquareLaw
import L.Coding.Injection
import L.Cardinal
import L.DefinableInjection
import L.InjectionComposition
import L.GCH
import V.CantorBernstein
import L.CantorBernstein
import L.Mostowski
import L.CardinalAbove
```

<!--en-->
## Proving GCH

GCH reduces to bounding subsets by a sufficiently high constructible stage.
The following route internalizes definability, builds and counts Skolem hulls, derives the two cardinal injections, and assembles the theorem.

- `L.GCH.Assembly`{.Agda}: Assembling GCH from four internal bounds
- `L.Coding.SatisfactionGraphSet`{.Agda}: An internal graph of uniform satisfaction
- `L.Coding.CodeDomainAdequacy`{.Agda}: Soundness and completeness of the closed code domain
- `L.GCH.SatisfactionDescription`{.Agda}: A Δ₀ description of the satisfaction table
- `L.GCH.DefinablePowerSetDescription`{.Agda}: A Δ₀ description of the definable power set
- `L.GCH.AdequateStages`{.Agda}: Adequate stages for the GCH argument
- `L.GCH.OmegaRecursion`{.Agda}: Iterating a definable step through ω
- `V.Collapse`{.Agda}: The Mostowski collapse
- `L.GCH.SkolemHull`{.Agda}: Building and collapsing a Skolem hull
- `L.GCH.HierarchyDescription`{.Agda}: A Δ₀ description of the constructible hierarchy
- `L.GCH.CondensationTransfer`{.Agda}: Transferring structure through condensation
- `L.GCH.BelowSuccessorCardinal`{.Agda}: Ordinals below a successor cardinal inject into its base
- `L.GCH.OrderType`{.Agda}: Constructing order types inside L
- `L.GCH.CardinalRepresentative`{.Agda}: Choosing a cardinal representative for an ordinal
- `L.GCH.CardinalSquareLaw`{.Agda}: The square law for infinite L-cardinals
- `L.GCH.LeastWitnessMap`{.Agda}: Least witnesses form a definable map
- `L.GCH.SuccessorIntoPowerSet`{.Agda}: Injecting the successor cardinal into the power set
- `L.GCH.FiniteSequenceCoding`{.Agda}: Coding finite sequences below an infinite ordinal
- `L.GCH.StageCountingTools`{.Agda}: The counting tools for infinite constructible stages
- `L.GCH.ConstructibleHull`{.Agda}: Locating the hull and its collapse inside L
- `L.GCH.HullCounting`{.Agda}: Counting a Skolem hull from a counted start
- `L.GCH.StageInjection`{.Agda}: Injecting an infinite constructible stage into its index
- `L.GCH.BoundedSubset`{.Agda}: Bounded subsets appear at controlled stages
- `L.GCH.Theorem`{.Agda}: The constructible universe satisfies GCH
<!--zh-->
## 证明 GCH

GCH 归结为用足够高的可构造阶段界住各个子集。以下路线内部化可定义性，构造并计数 Skolem 壳，得到两向基数单射，最后组装定理。

- `L.GCH.Assembly`{.Agda}：从四条内部界装配 GCH
- `L.Coding.SatisfactionGraphSet`{.Agda}：统一满足关系的内部图
- `L.Coding.CodeDomainAdequacy`{.Agda}：封闭码定义域的可靠性与完备性
- `L.GCH.SatisfactionDescription`{.Agda}：满足表的 Δ₀ 描述
- `L.GCH.DefinablePowerSetDescription`{.Agda}：可定义幂集的 Δ₀ 描述
- `L.GCH.AdequateStages`{.Agda}：GCH 论证所需的充分阶段
- `L.GCH.OmegaRecursion`{.Agda}：沿 ω 迭代可定义步骤
- `V.Collapse`{.Agda}：Mostowski 塌缩
- `L.GCH.SkolemHull`{.Agda}：构造并塌缩 Skolem 壳
- `L.GCH.HierarchyDescription`{.Agda}：可构造层级的 Δ₀ 描述
- `L.GCH.CondensationTransfer`{.Agda}：通过凝聚搬运结构
- `L.GCH.BelowSuccessorCardinal`{.Agda}：后继基数以下的序数单射到其基数
- `L.GCH.OrderType`{.Agda}：在 L 内部构造序型
- `L.GCH.CardinalRepresentative`{.Agda}：为序数选取基数代表
- `L.GCH.CardinalSquareLaw`{.Agda}：L 中无穷基数的平方律
- `L.GCH.LeastWitnessMap`{.Agda}：最小见证构成可定义映射
- `L.GCH.SuccessorIntoPowerSet`{.Agda}：把后继基数单射到幂集
- `L.GCH.FiniteSequenceCoding`{.Agda}：在无穷序数以下编码有限序列
- `L.GCH.StageCountingTools`{.Agda}：计数无穷可构造阶段的工具
- `L.GCH.ConstructibleHull`{.Agda}：在 L 中定位 Skolem 壳及其塌缩
- `L.GCH.HullCounting`{.Agda}：从已计数的起点计数 Skolem 壳
- `L.GCH.StageInjection`{.Agda}：把无穷可构造阶段单射到其指标
- `L.GCH.BoundedSubset`{.Agda}：有界子集在受控阶段出现
- `L.GCH.Theorem`{.Agda}：可构造宇宙满足 GCH
<!--ja-->
## GCH の証明

一般連続体仮説の証明を，部分集合が現れる段階の上界と，その段階の大きさの評価に分けて学びます。充足関係と構成可能階層の内部記述を，Skolem 包とその崩壊に結び付け，冪集合と後続基数を比較する二方向の単射を得ます。

- `L.GCH.Assembly`{.Agda}：四つの内部上界から GCH を組み立てる
- `L.Coding.SatisfactionGraphSet`{.Agda}：一様な充足関係の内部グラフ
- `L.Coding.CodeDomainAdequacy`{.Agda}：閉じた符号の定義域の健全性と完全性
- `L.GCH.SatisfactionDescription`{.Agda}：充足関係表の Δ₀ 記述
- `L.GCH.DefinablePowerSetDescription`{.Agda}：定義可能冪集合の Δ₀ 記述
- `L.GCH.AdequateStages`{.Agda}：GCH の議論に必要な十分な段階
- `L.GCH.OmegaRecursion`{.Agda}：定義可能な操作を ω に沿って反復する
- `V.Collapse`{.Agda}：Mostowski 崩壊
- `L.GCH.SkolemHull`{.Agda}：Skolem 包を構成して崩壊させる
- `L.GCH.HierarchyDescription`{.Agda}：構成可能階層の Δ₀ 記述
- `L.GCH.CondensationTransfer`{.Agda}：凝縮を通して構造を移す
- `L.GCH.BelowSuccessorCardinal`{.Agda}：後続基数より小さい順序数をその基数へ単射する
- `L.GCH.OrderType`{.Agda}：L の内部で順序型を構成する
- `L.GCH.CardinalRepresentative`{.Agda}：順序数の基数代表を選ぶ
- `L.GCH.CardinalSquareLaw`{.Agda}：L の無限基数における平方律
- `L.GCH.LeastWitnessMap`{.Agda}：最小の証人が定義可能な写像をなす
- `L.GCH.SuccessorIntoPowerSet`{.Agda}：後続基数を冪集合へ単射する
- `L.GCH.FiniteSequenceCoding`{.Agda}：無限順序数の下で有限列をコード化する
- `L.GCH.StageCountingTools`{.Agda}：無限な構成可能段階を数える道具
- `L.GCH.ConstructibleHull`{.Agda}：包とその崩壊を L の内部に置く
- `L.GCH.HullCounting`{.Agda}：数えられた始集合から Skolem 包を数える
- `L.GCH.StageInjection`{.Agda}：無限構成可能段階をその添字へ単射する
- `L.GCH.BoundedSubset`{.Agda}：有界部分集合が現れる段階を制御する
- `L.GCH.Theorem`{.Agda}：構成可能宇宙は GCH を満たす
<!--/-->
```agda
import L.GCH.Assembly
import L.Coding.SatisfactionGraphSet
import L.Coding.CodeDomainAdequacy
import L.GCH.SatisfactionDescription
import L.GCH.DefinablePowerSetDescription
import L.GCH.AdequateStages
import L.GCH.OmegaRecursion
import V.Collapse
import L.GCH.SkolemHull
import L.GCH.HierarchyDescription
import L.GCH.CondensationTransfer
import L.GCH.BelowSuccessorCardinal
import L.GCH.OrderType
import L.GCH.CardinalRepresentative
import L.GCH.CardinalSquareLaw
import L.GCH.LeastWitnessMap
import L.GCH.SuccessorIntoPowerSet
import L.GCH.FiniteSequenceCoding
import L.GCH.StageCountingTools
import L.GCH.ConstructibleHull
import L.GCH.HullCounting
import L.GCH.StageInjection
import L.GCH.BoundedSubset
import L.GCH.Theorem
```
