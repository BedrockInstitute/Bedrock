<!--en-->
# Milestones

This page gathers the book's proved endpoint results and offers a concise entrance to the routes that lead to them. Each entry states a theorem in ordinary mathematical language, then imports the exact Agda declaration that proves it.
<!--zh-->
# 里程碑

本页汇集全书已经证明的最终成果，也为通往这些成果的阅读路线提供简明入口。每一项先用传统数学书的语言陈述定理，再直接导入证明它的 Agda 声明。
<!--ja-->
# マイルストーン

このページでは、本書で証明された到達点をまとめ、そこへ至る読書ルートへの簡潔な入口も示す。各項目はまず通常の数学書の言葉で定理を述べ、その後にそれを証明する Agda の宣言を直接インポートする。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

module Milestones where
```

<!--en-->
**Theorem 1.** Under Ω-resizing from level `ℓ-suc ℓ` to level `ℓ`, the host-level cumulative hierarchy `V ℓ` is a model of ZF.
<!--zh-->
**定理1** 在从层级 `ℓ-suc ℓ` 到层级 `ℓ` 的命题宇宙换级假设下，宿主层的累积层级 `V ℓ` 是 ZF 的模型。
<!--ja-->
**定理1** レベル `ℓ-suc ℓ` からレベル `ℓ` への命題宇宙リサイズの仮定のもとで、ホストレベルの累積階層 `V ℓ` は ZF のモデルである。
<!--/-->

```agda
open import V.Model public using ( V⊨ZF )
```

<!--en-->
**Theorem 2.** Under the host-level axiom-of-choice assumption, the host-level cumulative hierarchy `V ℓ` is a model of ZFC.
<!--zh-->
**定理2** 在宿主层选择公理的假设下，宿主层的累积层级 `V ℓ` 是 ZFC 的模型。
<!--ja-->
**定理2** ホストレベルの選択公理の仮定のもとで、ホストレベルの累積階層 `V ℓ` は ZFC のモデルである。
<!--/-->

```agda
open import V.Model public using ( V⊨ZFC )
```

<!--en-->
**Theorem 3.** Under the excluded-middle assumption, the constructible universe `L` is a model of ZFC.
<!--zh-->
**定理3** 在排中律假设下，可构造宇宙 `L` 是 ZFC 的模型。
<!--ja-->
**定理3** 排中律の仮定のもとで、構成可能宇宙 `L` は ZFC のモデルである。
<!--/-->

```agda
open import L.Model public using ( L⊨ZFC )
```

<!--en-->
**Theorem 4.** Under the same excluded-middle assumption, the constructible universe `L` satisfies the generalized continuum hypothesis internally.
<!--zh-->
**定理4** 在排中律假设下，可构造宇宙 `L` 在内部满足广义连续统假设。
<!--ja-->
**定理4** 同じ排中律の仮定のもとで、構成可能宇宙 `L` は内部的に一般連続体仮説を満たす。
<!--/-->

```agda
open import L.GCH.Theorem public using ( L⊨GCH )
```
