<!--en-->
# Milestones

This page gathers the book's proved endpoint results and offers a concise entrance to the routes that lead to them.
<!--zh-->
# 里程碑

本页汇集全书已经证明的最终成果，也为通往这些成果的阅读路线提供简明入口。
<!--ja-->
# マイルストーン

このページでは、本書で証明された到達点をまとめ、そこへ至る読書ルートへの簡潔な入口も示す。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

module Milestones where
```

<!--en-->
**Theorem 0.** `SetChoice`{.Agda} implies `LEM`{.Agda}, which in turn implies `ΩResizing`{.Agda}.
<!--zh-->
**定理0** `SetChoice`{.Agda} 蕴含 `LEM`{.Agda}，而 `LEM`{.Agda} 蕴含 `ΩResizing`{.Agda}。
<!--ja-->
**定理0** `SetChoice`{.Agda} は `LEM`{.Agda} を含意し、`LEM`{.Agda} はさらに `ΩResizing`{.Agda} を含意する。
<!--/-->

```agda
open import Base.Choice public using ( SetChoice→LEM )
open import Base.Classical public using ( LEM→ΩResizing )
```

<!--en-->
**Theorem 1.** Assuming `ΩResizing`{.Agda}, the [HIT]{.term-ref #higher-inductive-type} cumulative hierarchy [V](V.Hierarchy.html#𝒮ᵥ){.Agda} is a model of [ZF](FOL.ZFModel.html#isZFModel).
<!--zh-->
**定理1** 假设 `ΩResizing`{.Agda}，[HIT]{.term-ref #higher-inductive-type} 累积层级 [V](V.Hierarchy.html#𝒮ᵥ){.Agda} 是 [ZF](FOL.ZFModel.html#isZFModel) 的模型。
<!--ja-->
**定理1** `ΩResizing`{.Agda} を仮定すると、[HIT]{.term-ref #higher-inductive-type} による累積階層 [V](V.Hierarchy.html#𝒮ᵥ){.Agda} は [ZF](FOL.ZFModel.html#isZFModel) のモデルである。
<!--/-->

```agda
open import V.Model public using ( V⊨ZF )
```

<!--en-->
**Theorem 2.** Assuming `SetChoice`{.Agda}, the [HIT]{.term-ref #higher-inductive-type} cumulative hierarchy [V](V.Hierarchy.html#𝒮ᵥ){.Agda} is a model of [ZFC](FOL.ZFModel.html#isZFCModel).
<!--zh-->
**定理2** 假设 `SetChoice`{.Agda}，[HIT]{.term-ref #higher-inductive-type} 累积层级 [V](V.Hierarchy.html#𝒮ᵥ){.Agda} 是 [ZFC](FOL.ZFModel.html#isZFCModel) 的模型。
<!--ja-->
**定理2** `SetChoice`{.Agda} を仮定すると、[HIT]{.term-ref #higher-inductive-type} による累積階層 [V](V.Hierarchy.html#𝒮ᵥ){.Agda} は [ZFC](FOL.ZFModel.html#isZFCModel) のモデルである。
<!--/-->

```agda
open import V.Model public using ( V⊨ZFC )
```

<!--en-->
**Theorem 3.** Assuming `LEM`{.Agda}, the constructible universe [L](L.Constructible.html#𝒮ʟ){.Agda} is a model of [ZFC](FOL.ZFModel.html#isZFCModel).
<!--zh-->
**定理3** 假设 `LEM`{.Agda}，可构造宇宙 [L](L.Constructible.html#𝒮ʟ){.Agda} 是 [ZFC](FOL.ZFModel.html#isZFCModel) 的模型。
<!--ja-->
**定理3** `LEM`{.Agda} を仮定すると、構成可能宇宙 [L](L.Constructible.html#𝒮ʟ){.Agda} は [ZFC](FOL.ZFModel.html#isZFCModel) のモデルである。
<!--/-->

```agda
open import L.Model public using ( L⊨ZFC )
```

<!--en-->
**Theorem 4.** Assuming `LEM`{.Agda}, the constructible universe [L](L.Constructible.html#𝒮ʟ){.Agda} satisfies the [generalized continuum hypothesis](L.GCH.html#GCHStatement) internally.
<!--zh-->
**定理4** 假设 `LEM`{.Agda}，可构造宇宙 [L](L.Constructible.html#𝒮ʟ){.Agda} 在内部满足[广义连续统假设](L.GCH.html#GCHStatement)。
<!--ja-->
**定理4** `LEM`{.Agda} を仮定すると、構成可能宇宙 [L](L.Constructible.html#𝒮ʟ){.Agda} は内部的に[一般連続体仮説](L.GCH.html#GCHStatement)を満たす。
<!--/-->

```agda
open import L.GCH.Theorem public using ( L⊨GCH )
```
