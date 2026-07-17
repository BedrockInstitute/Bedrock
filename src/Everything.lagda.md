# Bedrock

<!--en-->
*Laying the groundwork for the metaphysics of V.*

A machine-checked development, in Cubical Agda, of the set theory underlying contemporary
questions about the universe of sets: forcing, inner models, and the structure of V. The
immediate target is a full mechanization of `L` ⊨ GCH, with the cumulative hierarchy `V`
realised as a higher inductive type. The full treatment is in the
[Charter](https://github.com/BedrockInstitute/Bedrock/blob/main/docs/en/CHARTER.md).

This site is generated from literate Agda; this page is the book's table of contents,
in reading order (the sidebar follows it). The mathematics proper is under
construction: the groundwork part is in place, and the parts on logic, models, the
cumulative hierarchy, and the constructible universe follow.
<!--zh-->
*为 V 的形而上学奠基。*

一项在 Cubical Agda 中的机器验证工作，针对当代集合宇宙问题背后的那部分集合论：力迫、内模型，以及 V 的结构。当前目标是完整机械化 `L` ⊨ GCH，其中累积层级 `V` 以高阶归纳类型实现。完整论述见 [纲领](https://github.com/BedrockInstitute/Bedrock/blob/main/docs/zh/CHARTER.md)。

本站点由文学化 Agda 生成；本页是全书目录，按阅读顺序排列 (侧边栏与之一致)。数学本体正在施工中：奠基部分已就位，逻辑、模型、累积层级与可构造宇宙诸部随后。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}
module Everything where
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
<!--zh-->
## 第零部：奠基

- `Base.Prelude`{.Agda}：精选的宿主词汇 (宇宙、路径、h-层级、`hProp`{.Agda}、依值对与索引数据)，以及决定本书读法的可溯源纪律。
- `Base.Truth`{.Agda}：真值代数 `TruthAlg`{.Agda}，零定律的运算签名，全书逻辑符号的唯一来源；附典范实例 `hPropAlg`{.Agda}。
- `Base.Classical`{.Agda}：经典边界：排中律作为参数接口 `LEM`{.Agda}，及其两笔红利，命题的小分类器与命题降层。
<!--/-->

```agda
import Base.Prelude
import Base.Truth
import Base.Classical
```

<!--en-->
## Part 1: first-order logic as an object of study

- `FOL.Syntax`{.Agda}: the object language: a deeply embedded `Formula`{.Agda} with
  the constant domain as a parameter, intrinsic scoping, and every constructor
  primitive; sentences and the parameter-free syntax.
- `FOL.Structure`{.Agda}: the structures formulas talk about: carrier, equality,
  and membership, valued in a truth algebra; restriction `↾` and environments.
- `FOL.Semantics`{.Agda}: evaluation `⟦_⟧`{.Agda} and satisfaction `_⊨_`{.Agda} by
  structural recursion, each clause exactly its truth-algebra operation;
  relabelling preserves meaning.
- `FOL.Renaming`{.Agda}: the book's entire variable calculus: `renameFo`{.Agda} on
  syntax, and the one correctness theorem `⊨-rename`{.Agda} covering weakening,
  exchange, and contraction.
<!--zh-->
## 第一部：作为研究对象的一阶逻辑

- `FOL.Syntax`{.Agda}：对象语言：深嵌入的 `Formula`{.Agda}，常量域作参数，作用域内蕴，构造子全原语；句子与无参数语法。
- `FOL.Structure`{.Agda}：公式所谈论的结构：载体、等词与成员，取值于真值代数；限制 `↾` 与环境。
- `FOL.Semantics`{.Agda}：结构递归给出的求值 `⟦_⟧`{.Agda} 与满足 `_⊨_`{.Agda}，每条子句恰是对应的真值代数运算；重标记保含义。
- `FOL.Renaming`{.Agda}：本书全部的变量演算：语法上的 `renameFo`{.Agda}，与一条通吃弱化、交换、收缩的正确性定理 `⊨-rename`{.Agda}。
<!--/-->

```agda
import FOL.Syntax
import FOL.Structure
import FOL.Semantics
import FOL.Renaming
```
