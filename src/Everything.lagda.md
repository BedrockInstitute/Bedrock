# Bedrock

<!--en-->
*Laying the groundwork for the metaphysics of V.*

A machine-checked development, in Cubical Agda, of the set theory underlying contemporary
questions about the universe of sets: forcing, inner models, and the structure of V. The
immediate target is a full mechanization of `L` ⊨ GCH, with the cumulative hierarchy `V`
realised as a higher inductive type. The full treatment is in the
[Charter](https://github.com/BedrockInstitute/Bedrock/blob/main/docs/en/CHARTER.md).

This site is generated from literate Agda; this page is the book's **reading
catalog**: the table of contents in learning order, which the chapter-end
navigation also follows. For the structural view, by namespace, use the module
tree in the sidebar. The mathematics proper is under construction: the groundwork,
logic, and model parts are in place, and the parts on the cumulative hierarchy
and the constructible universe follow.
<!--zh-->
*为 V 的形而上学奠基。*

一项在 Cubical Agda 中的机器验证工作，针对当代集合宇宙问题背后的那部分集合论：力迫、内模型，以及 V 的结构。当前目标是完整机械化 `L` ⊨ GCH，其中累积层级 `V` 以高阶归纳类型实现。完整论述见 [纲领](https://github.com/BedrockInstitute/Bedrock/blob/main/docs/zh/CHARTER.md)。

本站点由文学化 Agda 生成；本页是全书的**阅读目录**：按学习顺序排列，每章页尾的导航循此顺序。按知识结构浏览，请用侧边栏按命名空间分组的模块树。数学本体正在施工中：奠基、逻辑与模型诸部已就位，累积层级与可构造宇宙两部随后。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}
module Everything where
```

<!--en-->
## Landmarks: where the book ends up

- `Landmarks`{.Agda}: the trophy case, displayed at the entrance: the milestone
  theorems restated as self-contained signatures with their full assumption
  bills, `V⊨ZF`{.Agda} (and its classical redemption), `V⊨ZFC`{.Agda}, and the
  frontier-conditional `L⊨ZFC`{.Agda}, with `V⊨ZFC-fromChoice`{.Agda} as the
  single-hypothesis form. Read it first to see the destination; understanding
  the signatures is what the rest of the book is for.
<!--zh-->
## 地标：本书的终点

- `Landmarks`{.Agda}：奖杯陈列室，摆在入口处：里程碑定理以自足签名重述，假设账单全额陈列：`V⊨ZF`{.Agda} (及其经典代付版)、`V⊨ZFC`{.Agda} (及其单假设版 `V⊨ZFC-fromChoice`{.Agda})，与带前沿条件的 `L⊨ZFC`{.Agda}。先读它，看清目的地；至于读懂这些签名，正是全书其余部分的任务。
<!--/-->

```agda
import Landmarks
```

<!--en-->
## Part 0: the groundwork

- `Base.Prelude`{.Agda}: the curated host vocabulary (universes, paths, h-levels,
  `hProp`{.Agda}, pairs, the indexing data), and the traceability discipline that
  governs how the book is read.
- `Base.Truth`{.Agda}: the truth algebra `TruthAlg`{.Agda}, a law-free operation
  signature that is the book's sole source of logic symbols, with its canonical
  instance `hPropAlg`{.Agda}.
- `Base.Classical`{.Agda}: the classical boundary: excluded middle as the parameter
  interface `LEM`{.Agda}, and its two dividends, a small classifier of propositions
  and propositional resizing.
- `Base.Choice`{.Agda}: the boundary's second interface: set-level choice
  `SetChoice`{.Agda}, stated levelwise like `LEM`{.Agda}, with Diaconescu's
  theorem mechanized at once: choice proves the excluded middle
  (`choice→lem`{.Agda}).
<!--zh-->
## 第零部：奠基

- `Base.Prelude`{.Agda}：精选的宿主词汇 (宇宙、路径、h-层级、`hProp`{.Agda}、依值对与索引数据)，以及决定本书读法的可溯源纪律。
- `Base.Truth`{.Agda}：真值代数 `TruthAlg`{.Agda}，零定律的运算签名，全书逻辑符号的唯一来源；附典范实例 `hPropAlg`{.Agda}。
- `Base.Classical`{.Agda}：经典边界：排中律作为参数接口 `LEM`{.Agda}，及其两笔红利，命题的小分类器与命题降层。
- `Base.Choice`{.Agda}：边界的第二个接口：集合层选择 `SetChoice`{.Agda}，与 `LEM`{.Agda} 同款逐层级陈述；Diaconescu 定理当场机器化：选择证明排中律 (`choice→lem`{.Agda})。
<!--/-->

```agda
import Base.Prelude
import Base.Truth
import Base.Classical
import Base.Choice
```

<!--en-->
## Part 1: first-order logic as an object of study

- `FOL.Syntax`{.Agda}: the object language: a deeply embedded `Formula`{.Agda} with
  the constant domain as a parameter, intrinsic scoping, and every constructor
  primitive; sentences and parameter-free formulas.
- `FOL.Structure`{.Agda}: the structures formulas talk about: carrier, equality,
  and membership, valued in a truth algebra; restriction `↾` and environments.
- `FOL.Semantics`{.Agda}: evaluation `⟦_⟧`{.Agda} and satisfaction `_⊨_`{.Agda} by
  structural recursion, each clause exactly its truth-algebra operation;
  relabelling preserves meaning.
<!--zh-->
## 第一部：作为研究对象的一阶逻辑

- `FOL.Syntax`{.Agda}：对象语言：深嵌入的 `Formula`{.Agda}，常量域作参数，作用域内蕴，构造子全原语；句子与无参公式。
- `FOL.Structure`{.Agda}：公式所谈论的结构：载体、等词与成员，取值于真值代数；限制 `↾` 与环境。
- `FOL.Semantics`{.Agda}：结构递归给出的求值 `⟦_⟧`{.Agda} 与满足 `_⊨_`{.Agda}，每条子句恰是对应的真值代数运算；重标记保含义。
<!--/-->

```agda
import FOL.Syntax
import FOL.Structure
import FOL.Semantics
```

<!--en-->
## Part 2: what a model of ZF is

- `ZF.Model`{.Agda}: the axioms as a record: `ZFModel`{.Agda} with extensionality,
  meta-level regularity (the compactness ceiling), unique existence discharged by
  the description operator `℩`, separation and replacement consuming the book's
  own formulas, and strong infinity through the numeral chain; `ZFCModel`{.Agda}
  adds choice as an extension.
<!--zh-->
## 第二部：何谓 ZF 模型

- `ZF.Model`{.Agda}：公理作为 record：`ZFModel`{.Agda} 含外延公理、元层面的正则公理 (紧致性天花板)、经摹状词算子 `℩` 兑现的唯一存在、消费本书自家公式的分离与替换，以及经数码链的强无穷；`ZFCModel`{.Agda} 以扩展形式添加选择公理。
<!--/-->

```agda
import ZF.Model
```

<!--en-->
## The formula factory (Part 1 resumed)

Separation and replacement accept only formulas; these chapters set up the
representation notion and the certificates that make formulas portable.

- `FOL.Reification.Base`{.Agda}: representation, the bridge: a formula paired with
  its adequacy certificate; `translate`{.Agda} and `adequacy`{.Agda} as the only
  exits.
- `FOL.Reification.Graded`{.Agda}: the Levy hierarchy as inductive certificates:
  Δ₀ by absence, Σ₁/Π₁, the alternating Σₙ/Πₙ tower, and graded representations.
- `FOL.Reification.Absoluteness`{.Agda}: transitive classes and the Δ₀
  absoluteness theorem `abs₀`{.Agda}; Σ₁ transfers up, Π₁ down; `transfer`{.Agda}
  composes adequacy with absoluteness.
<!--zh-->
## 公式工厂 (第一部再续)

分离与替换只收公式；这几章立起表示概念，并给公式配上可携的证书。

- `FOL.Reification.Base`{.Agda}：表示，即那座桥：公式配上其适足性证书；`translate`{.Agda} 与 `adequacy`{.Agda} 是仅有的出口。
- `FOL.Reification.Graded`{.Agda}：作为归纳证书的列维层级：缺席即 Δ₀、Σ₁/Π₁、交替的 Σₙ/Πₙ 之塔，以及分级表示。
- `FOL.Reification.Absoluteness`{.Agda}：传递类与 Δ₀ 绝对性定理 `abs₀`{.Agda}；Σ₁ 向上、Π₁ 向下；`transfer`{.Agda} 把适足性与绝对性复合。
<!--/-->

```agda
import FOL.Reification.Base
import FOL.Reification.Graded
import FOL.Reification.Absoluteness
```

<!--en-->
## Part 3: the cumulative hierarchy realizes ZF(C)

- `V.Hierarchy`{.Agda}: the library's higher inductive type `V`{.Agda}: sets as
  images of small families, extensional equality as a path constructor; the
  structure `𝒮ᵥ`{.Agda} in one line, with extensionality and regularity banked
  free.
- `V.Smallness`{.Agda}: the smallness toolkit: atoms compress through the
  library, connectives and bounded quantifiers pass witnesses along,
  `separateFromSmall`{.Agda} is the one pipe to sets; `Δ₀-small`{.Agda} makes Δ₀
  separation an axiom-free theorem (`separateΔ₀`{.Agda}).
- `V.Model`{.Agda}: the summit: stock sets reshaped, replacement and strong
  infinity for free, `VResizing`{.Agda} pricing full separation and power set
  (redeemed classically by `lem→VResizing`{.Agda}); assembly `V⊨ZF`{.Agda},
  with `SetChoice`{.Agda} the upgrade `V⊨ZFC`{.Agda}, and by Diaconescu the
  single-hypothesis `V⊨ZFC-fromChoice`{.Agda}.
<!--zh-->
## 第三部：累积层级实现 ZF(C)

- `V.Hierarchy`{.Agda}：库的高阶归纳类型 `V`{.Agda}：集合是小族的像，外延相等是路径构造子；结构 `𝒮ᵥ`{.Agda} 一行插入，外延与正则免费入账。
- `V.Smallness`{.Agda}：小性工具链：原子经库压缩，联结词与有界量词传递见证，`separateFromSmall`{.Agda} 是通往集合的唯一水管；`Δ₀-small`{.Agda} 让 Δ₀ 分离成为零公理定理 (`separateΔ₀`{.Agda})。
- `V.Model`{.Agda}：本部之巅：库存换形，替换与强无穷白得，`VResizing`{.Agda} 为全分离与幂集标价 (经典侧由 `lem→VResizing`{.Agda} 代付)；合龙 `V⊨ZF`{.Agda}，加 `SetChoice`{.Agda} 得 `V⊨ZFC`{.Agda}，经 Diaconescu 更有单假设的 `V⊨ZFC-fromChoice`{.Agda}。
<!--/-->

```agda
import V.Hierarchy
import V.Smallness
import V.Model
```

<!--en-->
## Part 4: the constructible universe

- `V.Definability`{.Agda}: the single step: `Def A`, the definable subsets of
  `A` with parameters from `A`: syntax as index set, inner satisfaction for
  meaning, essential smallness footing the bill; `A ∈ Def A` always, and
  `A ⊆ Def A` under transitivity.
- `L.Constructible`{.Agda}: the tower `Lset`{.Agda} by membership recursion,
  one equation for zero, successors, and limits; the layer predicate
  `isLayer`{.Agda} with `layer-trans`{.Agda}; the class `isL`{.Agda} and the
  structure `𝒮ʟ`{.Agda}.
<!--zh-->
## 第四部：可构造宇宙

- `V.Definability`{.Agda}：那一步：`Def A`，带 `A` 中参数可定义的 `A` 的子集之集：语法当索引集，内层满足给含义，本质小性买单；`A ∈ Def A` 恒成立，传递性下 `A ⊆ Def A`。
- `L.Constructible`{.Agda}：沿成员递归的塔 `Lset`{.Agda}，一条方程通吃零、后继与极限；层谓词 `isLayer`{.Agda} 与 `layer-trans`{.Agda}；类 `isL`{.Agda} 与结构 `𝒮ʟ`{.Agda}。
<!--/-->

```agda
import V.Definability
import L.Constructible
```

<!--en-->
The root, stated today and finished over the remaining parts:

- `L.Frontier`{.Agda}: the debt registry: eleven fields, each the verbatim
  statement of a model field at `𝒮ʟ`; proven fields get deleted, and the book
  is done when the record is empty.
- `L.Model`{.Agda}: the root chapter: the honest relative-consistency framing;
  extensionality and regularity descend along transitivity; `L⊨ZF`{.Agda} and
  `L⊨ZFC`{.Agda} assembled from the frontier.
<!--zh-->
根，今日陈述，余部完成：

- `L.Frontier`{.Agda}：债务登记簿：十一个字段，每个都是模型字段在 `𝒮ʟ` 处的原文陈述；字段证毕即删，簿清则书成。
- `L.Model`{.Agda}：根章：诚实的相对一致性表述；外延与正则沿传递性下降；`L⊨ZF`{.Agda} 与 `L⊨ZFC`{.Agda} 由前沿合龙。
<!--/-->

```agda
import L.Frontier
import L.Model
```

<!--en-->
## Tools in waiting

Three chapters with, as of today, no consumer anywhere in the trunk: the
combinator assembly line, the variable calculus, and relativization. Their first
consumers arrive with Part 4's deeper machinery; they read last so the main line
stays unbroken.

- `FOL.Reification.Combinators`{.Agda}: the certificate algebra: one combinator per
  constructor, every certificate a single congruence.
- `FOL.Renaming`{.Agda}: the book's entire variable calculus: `renameFo`{.Agda} on
  syntax, and the one correctness theorem `⊨-rename`{.Agda} covering weakening,
  exchange, and contraction.
- `FOL.Reification.Relativize`{.Agda}: tightening unbounded quantifiers to a
  constant bound, Δ₀ certificate included, with the correctness equation.
<!--zh-->
## 候用的工具

三章至今在主干上没有任何消费者：组合子流水线、变量演算与相对化。它们的首批消费者随第四部的深层机器到来；读在最后，好让主线不断。

- `FOL.Reification.Combinators`{.Agda}：证书代数：一构造子一组合子，每张证书一次同余。
- `FOL.Renaming`{.Agda}：本书全部的变量演算：语法上的 `renameFo`{.Agda}，与一条通吃弱化、交换、收缩的正确性定理 `⊨-rename`{.Agda}。
- `FOL.Reification.Relativize`{.Agda}：把无界量词收紧到常量界，Δ₀ 证书随附，并给出正确性等式。
<!--/-->

```agda
import FOL.Reification.Combinators
import FOL.Renaming
import FOL.Reification.Relativize
```

