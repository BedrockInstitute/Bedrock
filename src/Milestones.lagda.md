<!--en-->
# Milestones

This page gathers the book's proved endpoint results and offers a concise entrance to the routes that lead to them. Each entry states a theorem in ordinary mathematical language, then imports the exact Agda declaration that proves it.
<!--zh-->
# 里程碑

本页汇集全书已经证明的最终成果，也为通往这些成果的阅读路线提供简明入口。每一项先用传统数学书的语言陈述定理，再直接导入证明它的 Agda 声明。
<!--ja-->
# マイルストーン

このページでは、本書で証明された到達点をまとめ、そこへ至る読書ルートへの簡潔な入口も示します。各項目はまず通常の数学書の言葉で定理を述べ、その後にそれを証明する Agda の宣言を直接インポートします。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

module Milestones where
```

<!--en-->
**Theorem 1.** Under the excluded-middle assumption, the host-level `V` is a model of ZF.
<!--zh-->
**定理1** 在排中律假设下，宿主层 `V` 是 ZF 的模型。
<!--ja-->
**定理1** 排中律の仮定のもとで、ホストレベルの `V` は ZF のモデルです。
<!--/-->

```agda
open import V.Model public using ( V⊨ZF )
```

<!--en-->
**Theorem 2.** Under the host-level axiom-of-choice assumption, the host-level `V` is a model of ZFC.
<!--zh-->
**定理2** 在宿主层选择公理的假设下，宿主层 `V` 是 ZFC 的模型。
<!--ja-->
**定理2** ホストレベルの選択公理の仮定のもとで、ホストレベルの `V` は ZFC のモデルです。
<!--/-->

```agda
open import V.Model public using ( V⊨ZFC )
```

<!--en-->
**Theorem 3.** Under the excluded-middle assumption, the constructible universe `L` is a model of ZFC.
<!--zh-->
**定理3** 在排中律假设下，可构造宇宙 `L` 是 ZFC 的模型。
<!--ja-->
**定理3** 排中律の仮定のもとで、構成可能宇宙 `L` は ZFC のモデルです。
<!--/-->

```agda
open import L.Model public using ( L⊨ZFC )
```

<!--en-->
**Theorem 4.** Under the same excluded-middle assumption, the constructible universe `L` satisfies the generalized continuum hypothesis internally.
<!--zh-->
**定理4** 在同一个排中律假设下，可构造宇宙 `L` 在内部满足广义连续统假设。
<!--ja-->
**定理4** 同じ排中律の仮定のもとで、構成可能宇宙 `L` は内部的に一般連続体仮説を満たします。
<!--/-->

```agda
open import L.GCH.Theorem public using ( L⊨GCH )
```
