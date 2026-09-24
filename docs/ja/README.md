<p align="center"><img src="../../site/static/assets/banner.png" alt="" width="800"></p>

<h1><img src="../../site/static/assets/brand.svg" alt="" height="56" align="middle"> Bedrock</h1>

[English](../../README.md) · [中文](../zh/README.md) · **日本語**

[![CI](https://github.com/BedrockInstitute/Bedrock/actions/workflows/ci.yml/badge.svg)](https://github.com/BedrockInstitute/Bedrock/actions/workflows/ci.yml)
![Status: early](https://img.shields.io/badge/status-early-orange)
[![Agda](https://img.shields.io/badge/Agda-2.8.0-blue)](https://github.com/agda/agda)
[![cubical](https://img.shields.io/badge/cubical-0.9-blue)](https://github.com/agda/cubical)
[![Content: CC BY-NC-SA 4.0](https://img.shields.io/badge/content-CC%20BY--NC--SA%204.0-lightgrey.svg)](https://creativecommons.org/licenses/by-nc-sa/4.0/)
[![Code: AGPL-3.0-only](https://img.shields.io/badge/code-AGPL--3.0--only-blue.svg)](https://www.gnu.org/licenses/agpl-3.0.html)
[![REUSE status](https://api.reuse.software/badge/github.com/BedrockInstitute/Bedrock)](https://api.reuse.software/info/github.com/BedrockInstitute/Bedrock)

*V の形而上学に礎を据える。*

[Cubical Agda](https://github.com/agda/cubical) における機械検証の開発であり、現代の集合宇宙をめぐる問いの背後にある集合論、すなわち強制法、内部モデル、そして V の構造を対象とする。

## 最初の目標、証明済み

最初の自己完結した目標は、次を完全に機械化することであった。

> **`L` ⊨ GCH**。ここで `L` は、高次帰納型として実現された累積階層 `V` の上に構成される構成可能階層である。これはホストの内部における意味論的な定理である。

**それは証明された。**`L⊨GCH` と `L⊨ZFC` はいずれも [src/Origin.lagda.md](../../src/Origin.lagda.md) に述べられており、どちらも `LEM (ℓ-suc ℓ)` のみに依存する。内部の基数、内部の単射、モデル自身の冪集合である。証明項は `src/L/GCH/Theorem.lagda.md` の `L⊨GCH` である。

その内容はゲーデルの 1938 年の結果だが、辿る経路は教科書のものではなく、GCH に対して誰かがこれまで辿ったものでもない。これが最初の礎石としてふさわしいのは、本プロジェクトの残り全体が必要とする基盤層、すなわち深い埋め込みによる一階言語、累積階層、`L`、そして二重意味論の機構を、ことごとく動かすからである。しかも一行目から、下に述べるホスト言語最大主義の方針に立脚している。これを正しく仕上げることが、以後のすべてが立脚する基盤を較正する。

2026-09-22 現在：**空行を除く Agda コード 25,931 行 · プロジェクトキャッシュ削除後の型検査 203.17 秒 (Cubical キャッシュ保持) · 最大 RSS 1.57 GiB。**

2026-09-24 現在、ソースの依存グラフは 120 章、重複を除く直接 import 1,511 辺、推移簡約 227 辺からなり、最長の鎖は 31 モジュールである。これらはサイトのハブとプレビューのフィルターを適用する前の値である。

## 方向

この最初の礎石を越えて、長期的な目標は、機械化された集合論を、それが現在止まっている地点の先へと推し進めることにある。既存の強制法の形式化はコーエン (1963) で止まっているが、目標は今世紀の成果に到達することである。すなわち、多宇宙を研究するための道具としての強制法、基礎モデルの定義可能性、マントル、そして「V がそもそも確定した構造をもつのか」という、より大きな問いである。

これらは目標であって、約束ではない。いずれも、検証されて初めてここで宣言される。

## 基盤

本プロジェクトの目標は、V の形而上学に決着をつけることではなく、それに検証済みの礎を据えることにある。論争を裁定する定理 (基礎モデルの定義可能性、マントル、強制法での絶対性) を機械化することは、文字どおりの意味での基盤づくりにほかならない。

すべての出発点となるのが、**ホスト言語最大主義**である。教科書の ZF 公理を逐語的に書き写し、その周囲で証明支援系を調整するのではなく、あらゆる概念を型理論に固有の語法で再構成する。その結果、ホスト言語は数学の記述に用いられ、深い埋め込みによる `Formula` はそれ自体が研究対象となるときにのみ扱われる。これは基盤づくりの逆に映るかもしれない。だが証明支援系が与えるのは厳密さであって還元的な基底ではなく、厳密さはメタ理論の強さに依存しない。この方針こそが機械検証を可能にし、その代価も公然と表明される。

この礎は中立でもある。集合論の地質学は、単一宇宙観と多宇宙観のそれぞれが欠いてきた厳密な足場を両者に与え、論争を、仮定される無限公理の強さによってパラメータ化する。ゆえに本プロジェクトは、いずれの側にも与しない。

完全な論述は [綱領](CHARTER.md) にある。

## なぜ Cubical か

Cubical 型理論は現代型理論の最前線であり、いままさに書かれつつある数学の基礎である。一方、V の形而上学は同じ探究のうちで最も古典的な分野であり、「数学的宇宙とは何か」という最も古い問いである。最も古典的な基礎の問いを最も現代的な基礎へと持ち込むことは、しぶしぶ甘受すべき制約ではなく、むしろ本プロジェクトの目的の一つである。両者のあいだの対照は、意図して保たれている。

この選択は技術的にも引き合う。累積階層 V はここで高次帰納型として実現され、cubical はそれを、仮定として措くのではなく計算可能なものにする。だが、より深い理由は、その緊張そのものにある。

## 命名

*Bedrock (岩盤)* は最も深い基礎モデルである。それがそもそも存在するか否かは、それ自体が大基数に敏感な微妙な問題である (薄葉の定理)。この語はまた、ありふれた意味、すなわち探究の下にある土台、としても読める。両義はともに意図されている。

## 著者について

本プロジェクトのすべての内容は AI の補助のもとで作成されているが、その一行一行は、本文書も含めて、著者が一字一句、目を通している。

## 依存

本プロジェクトは、以下に固定したバージョンのツールチェインに対して型検査される。

| コンポーネント | バージョン |
| --- | --- |
| [Agda](https://github.com/agda/agda) | 2.8.0 |
| [cubical](https://github.com/agda/cubical) | 0.9 |
| [Python](https://www.python.org) | 3.11+ |

`make check` (型検査、ソースと教材の検査、および両方のテスト群) とサイトのビルドは Python 3.11+ を必要とする。開発用ツール (`reuse` リンター) は [requirements-dev.txt](../../requirements-dev.txt) に固定され、`make venv` でローカルの仮想環境に導入される。プッシュのたびに、[GitHub Actions](../../.github/workflows/ci.yml) によって上記のバージョンに対して型検査される。

初回のクローン後は、固定されたサブモジュールを初期化してからツールチェインを導入する：

```sh
git submodule update --init --recursive
make bootstrap
make check
```

## ウェブサイトの基盤

任意の `outcrop-agda` コンパイラー計装、ビルド、型情報の出力、並列スケジューラーも Outcrop が提供する。Bedrock は [ライブラリの固定](../../dev/agda-libraries.json)、入口モジュール、数学上の検査、リソースとデプロイの設定を保持する。[ツールチェインの説明](../../dev/AGDA-ENVIRONMENT.md)を参照。通常の Markdown 描画に Agda の導入は不要である。

サイトは [Outcrop](https://github.com/BedrockInstitute/Outcrop) を使用し、`outcrop/` サブモジュールでその版を固定する。**Outcrop Core** は Markdown と任意のコンパイラー意味情報を描画する。**Outcrop Site** は学習ルート、依存グラフ、多言語検索、型情報と定義モーダル、外観設定、Ask AI、再利用可能な検査規則を含む教材サイト全体を提供する。Bedrock は [site/project.json](../../site/project.json) を通じて本文、目次、用語、ブランド、数学上の方針を与える。

サブモジュールの初期化後、`make venv` がローカルのパッケージを導入する。既存の仮想環境では `.venv/bin/python -m pip install -e ./outcrop` も利用できる。`make site` で構築し、`make serve` でプレビューする。[インスタンスの説明](../../site/README.md) と [Outcrop の構成](../../outcrop/docs/ARCHITECTURE.md) を参照。他の教材も、Bedrock の数学やサイト実装を複製せずに同じ基盤を利用できる。

## 貢献

AI エージェントは [AGENTS.md](../../AGENTS.md) の唯一の規則集を、人間の貢献者は [CONTRIBUTING.md](../../CONTRIBUTING.md) を参照してください。

## ライセンス

Bedrock は複数ライセンスを採用しており、ファイルごとの条項は [`REUSE.toml`](../../REUSE.toml) に宣言され、`reuse lint` が検証する。要するに、

- **[CC BY-NC-SA 4.0](https://creativecommons.org/licenses/by-nc-sa/4.0/)**：数学・文章・ブランドマーク (`src/`、`docs/`、`README`、`site/static/assets/`)。
- **[AGPL-3.0-only](https://www.gnu.org/licenses/agpl-3.0.html)**：その他すべてのプロジェクト自身のコードと構成 (取り込んだ [1lab](https://1lab.dev) フロントエンドを含む)。
- **[OFL-1.1](https://openfontlicense.org)**：Outcrop が提供する自己ホストのウェブフォント (`outcrop/src/outcrop/site/resources/static/fonts/`)。

完全なライセンス本文は [`LICENSES/`](../../LICENSES/) にある。第三者のクレジットと AGPL 第 13 条の対応ソース表明は [NOTICE](../../NOTICE) を参照。

Outcrop はファイルごとのライセンスと、継承した第三者資産およびフォントの帰属を別途管理する。

© 2026 Bedrock Institute。
