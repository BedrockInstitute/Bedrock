```agda
{-# OPTIONS --cubical --safe --guardedness #-}
module Origin where
```

<!--en-->
# Origin
<!--zh-->
# 原点
<!--ja-->
# 原点
<!--/-->

<!--en-->

Origin joins the beginning of the book to its end: first a reason for the journey, then the results to which its proofs lead.
<!--zh-->

原点连接本书的开篇与收尾：先说明这段探索为何而来，再汇集各条证明路线最终抵达的成果。
<!--ja-->

原点は本書の始まりと終わりをつなぐ。まず探究の動機を述べ、続いて各証明の道筋が到達する成果をまとめる。
<!--/-->

<!--en-->
## Preface

*Laying the groundwork for the metaphysics of [V](V.Hierarchy.html#𝒮ᵥ){.Agda}.* Bedrock develops machine-checked set theory in Cubical Agda, as groundwork for questions about the universe of sets. Its first completed goal is that the constructible universe satisfies ZFC and GCH. The chapters build the language, models and proofs needed to reach these results; the milestones below give a view of the destination before the journey begins.

The guiding choice is to express mathematics in the host language wherever possible, using a deeply embedded first-order language when formulas themselves are the objects of study. Cubical type theory also lets us construct the cumulative hierarchy as a higher inductive type. This is a choice of mathematical foundation, not a claim that the metatheory is weaker than the theories it studies.

Beyond this first goal lie questions about forcing, inner models and the structure of [V](V.Hierarchy.html#𝒮ᵥ){.Agda}. They motivate the project, but are not results claimed by this book. The purpose is to provide verified groundwork for those questions, not to settle them by philosophical declaration. This preface draws on the project's [README](https://github.com/BedrockInstitute/Bedrock#readme).

## Milestones
<!--zh-->
## 前言

*为 [V](V.Hierarchy.html#𝒮ᵥ){.Agda} 的形而上学奠基。* Bedrock 在 Cubical Agda 中发展经过机器检验的集合论，为关于集合宇宙的探问提供基础。首个已经完成的目标是：可构造宇宙满足 ZFC 与 GCH。全书逐步建立抵达这些成果所需的语言、模型与证明；下面的里程碑则让我们在出发前先看见终点。

这项工作的基本选择，是尽可能用宿主语言表达数学，只在公式本身成为研究对象时使用深嵌入的一阶语言。立方类型论还允许我们把累积层级构造为高阶归纳类型。这是一种数学基础的选择，并不声称元理论比所研究的理论更弱。

越过首个目标，还有关于力迫、内模型和 [V](V.Hierarchy.html#𝒮ᵥ){.Agda} 的结构的问题。它们是项目的动力，而不是本书已经宣告的成果。我们的目的，是为这些探问提供经过验证的根基，而非用哲学宣言代替答案。本节节选改写自项目的 [README](https://github.com/BedrockInstitute/Bedrock/blob/main/docs/zh/README.md)。

## 里程碑
<!--ja-->
## 前書き

*[V](V.Hierarchy.html#𝒮ᵥ){.Agda} の形而上学のために基礎を築く。* Bedrock は Cubical Agda で機械検証された集合論を展開し、集合宇宙についての問いに土台を与える。最初に達成した目標は、構成可能宇宙が ZFC と GCH を満たすことである。本書はそのための言語、モデル、証明を順に構築する。以下のマイルストーンは、出発前に到達点を見渡すためのものである。

基本方針は、できる限りホスト言語で数学を表現し、式自体が研究対象となる場合に深く埋め込まれた一階言語を使うことである。また、立方型理論では累積階層を高階帰納型として構成できる。これは数学的基礎の選択であり、メタ理論が研究対象の理論より弱いという主張ではない。

最初の目標の先には、強制、内部モデル、[V](V.Hierarchy.html#𝒮ᵥ){.Agda} の構造についての問いがある。それらはプロジェクトの動機であって、本書ですでに得られた成果ではない。目指すのは、哲学的な宣言で答えを決めることではなく、検証された土台を築くことである。本節はプロジェクトの [README](https://github.com/BedrockInstitute/Bedrock/blob/main/docs/ja/README.md) から抜粋し、書き直したものである。

## マイルストーン
<!--/-->

<!--en-->
**Theorem 0** `SetChoice`{.Agda} implies `LEM`{.Agda}, which in turn implies `ΩResizing`{.Agda}.
<!--zh-->
**定理0** `SetChoice`{.Agda} 蕴含 `LEM`{.Agda}，而 `LEM`{.Agda} 蕴含 `ΩResizing`{.Agda}。
<!--ja-->
**定理0** `SetChoice`{.Agda} は `LEM`{.Agda} を含意し、`LEM`{.Agda} はさらに `ΩResizing`{.Agda} を含意する。
<!--/-->

```agda
open import Base.Choice public using ( SetChoice→LEM )
open import Base.Classical public using ( LEM→ΩResizing )
```

∎

<!--en-->
**Theorem 1** Assuming `ΩResizing`{.Agda}, the [HIT]{.term-ref #higher-inductive-type} cumulative hierarchy [V](V.Hierarchy.html#𝒮ᵥ){.Agda} is a model of [ZF](FOL.ZFModel.html#isZFModel).
<!--zh-->
**定理1** 假设 `ΩResizing`{.Agda}，[HIT]{.term-ref #higher-inductive-type} 累积层级 [V](V.Hierarchy.html#𝒮ᵥ){.Agda} 是 [ZF](FOL.ZFModel.html#isZFModel) 的模型。
<!--ja-->
**定理1** `ΩResizing`{.Agda} を仮定すると、[HIT]{.term-ref #higher-inductive-type} による累積階層 [V](V.Hierarchy.html#𝒮ᵥ){.Agda} は [ZF](FOL.ZFModel.html#isZFModel) のモデルである。
<!--/-->

```agda
open import V.Model public using ( V⊨ZF )
```

∎

<!--en-->
**Theorem 2** Assuming `SetChoice`{.Agda}, the [HIT]{.term-ref #higher-inductive-type} cumulative hierarchy [V](V.Hierarchy.html#𝒮ᵥ){.Agda} is a model of [ZFC](FOL.ZFModel.html#isZFCModel).
<!--zh-->
**定理2** 假设 `SetChoice`{.Agda}，[HIT]{.term-ref #higher-inductive-type} 累积层级 [V](V.Hierarchy.html#𝒮ᵥ){.Agda} 是 [ZFC](FOL.ZFModel.html#isZFCModel) 的模型。
<!--ja-->
**定理2** `SetChoice`{.Agda} を仮定すると、[HIT]{.term-ref #higher-inductive-type} による累積階層 [V](V.Hierarchy.html#𝒮ᵥ){.Agda} は [ZFC](FOL.ZFModel.html#isZFCModel) のモデルである。
<!--/-->

```agda
open import V.Model public using ( V⊨ZFC )
```

∎

<!--en-->
**Theorem 3** Assuming `LEM`{.Agda}, the constructible universe [L](L.Constructible.html#𝒮ʟ){.Agda} is a model of [ZFC](FOL.ZFModel.html#isZFCModel).
<!--zh-->
**定理3** 假设 `LEM`{.Agda}，可构造宇宙 [L](L.Constructible.html#𝒮ʟ){.Agda} 是 [ZFC](FOL.ZFModel.html#isZFCModel) 的模型。
<!--ja-->
**定理3** `LEM`{.Agda} を仮定すると、構成可能宇宙 [L](L.Constructible.html#𝒮ʟ){.Agda} は [ZFC](FOL.ZFModel.html#isZFCModel) のモデルである。
<!--/-->

```agda
open import L.Model public using ( L⊨ZFC )
```

∎

<!--en-->
**Theorem 4** Assuming `LEM`{.Agda}, the constructible universe [L](L.Constructible.html#𝒮ʟ){.Agda} satisfies the [generalized continuum hypothesis](L.GCH.html#GCHStatement) internally.
<!--zh-->
**定理4** 假设 `LEM`{.Agda}，可构造宇宙 [L](L.Constructible.html#𝒮ʟ){.Agda} 在内部满足[广义连续统假设](L.GCH.html#GCHStatement)。
<!--ja-->
**定理4** `LEM`{.Agda} を仮定すると、構成可能宇宙 [L](L.Constructible.html#𝒮ʟ){.Agda} は内部的に[一般連続体仮説](L.GCH.html#GCHStatement)を満たす。
<!--/-->

```agda
open import L.GCH.Theorem public using ( L⊨GCH )
```

∎
