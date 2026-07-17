# Bedrock

<!--en-->
*Laying the groundwork for the metaphysics of V.*

A machine-checked development, in Cubical Agda, of the set theory underlying contemporary
questions about the universe of sets: forcing, inner models, and the structure of V. The
immediate target is a full mechanization of `L` ⊨ GCH, with the cumulative hierarchy `V`
realised as a higher inductive type. The full treatment is in the
[Charter](https://github.com/BedrockInstitute/Bedrock/blob/main/docs/en/CHARTER.md).

This site is generated from literate Agda. The groundwork part `Base/` is in place: the
host vocabulary, the truth-value algebra, and the classical boundary. The mathematics
proper is under construction. Browse from the sidebar, or in the import list below,
both of which follow the book's reading order.
<!--zh-->
*为 V 的形而上学奠基。*

一项在 Cubical Agda 中的机器验证工作，针对当代集合宇宙问题背后的那部分集合论：力迫、内模型，以及 V 的结构。当前目标是完整机械化 `L` ⊨ GCH，其中累积层级 `V` 以高阶归纳类型实现。完整论述见 [纲领](https://github.com/BedrockInstitute/Bedrock/blob/main/docs/zh/CHARTER.md)。

本站点由文学化 Agda 生成。奠基部分 `Base/` 已就位：宿主词汇、真值代数与经典边界。数学本体正在施工中。可从侧边栏或下方的导入列表中浏览，两者都遵循本书的阅读顺序。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}
module Everything where

import Base.Prelude
import Base.Truth
import Base.Classical
```
