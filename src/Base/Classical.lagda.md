<!--en-->
# The classical boundary

This book develops classical set theory inside constructive Cubical type theory. Keeping the ambient foundation constructive makes the boundary of classical reasoning visible: definitions and proofs that do not need excluded middle remain constructive, while a theorem that does need it receives it as an explicit parameter. If classical logic were built into the ambient theory from the outset, the statements themselves would no longer reveal that distinction.
<!--zh-->
# 经典逻辑的边界

本书以构造主义的 Cubical 类型论为基础，在其中发展经典集合论。保留构造主义的基础，可以清楚划出经典推理的边界：不需要排中律的定义和证明仍然是构造主义的；真正需要排中律的定理，则把它作为显式参数。如果一开始就在基础理论中预设经典逻辑，定理的陈述本身就无法再显示这种区别。
<!--ja-->
# 古典論理との境界

本書は、構成的な Cubical 型理論を基礎として、その中で古典集合論を展開する。基礎を構成的なまま保つことで、古典的推論との境界が明確になる。排中律を必要としない定義と証明は構成的なまま残り、排中律を本当に必要とする定理だけが、それを明示的な引数として受け取る。初めから基礎理論に古典論理を組み込めば、定理の主張そのものからこの違いを読み取れなくなる。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

module Base.Classical where

open import Cubical.Foundations.Isomorphism using ( iso; isoToEquiv )
```

<!--en-->
Besides marking the point at which the development becomes classical, excluded middle resolves the two smallness questions left open in the preceding chapter:

- Propositional resizing: given `P : hProp ℓ₁`{.Agda}, can we find a proposition at a chosen level `ℓ₂` whose underlying type is equivalent to that of `P`?
- Ω-resizing: can the whole type `hProp ℓ₁`{.Agda} be presented by a single type in `Type ℓ₂`{.Agda}?
<!--zh-->
排中律不仅标志着本书进入经典推理之处，还能解决上一章留下的两个命题大小问题：

- 命题换级：给定 `P : hProp ℓ₁`{.Agda}，能否在指定层级 `ℓ₂` 找到一个命题，使其底层类型与 `P` 的底层类型等价？
- 命题宇宙换级：能否用 `Type ℓ₂`{.Agda} 中的单一类型呈现整个 `hProp ℓ₁`{.Agda}？
<!--ja-->
排中律は、本書が古典的推論へ移る箇所を示すだけでなく、前章に残された命題の小ささに関する二つの問題も解決する。

- 命題リサイズ：`P : hProp ℓ₁`{.Agda} が与えられたとき、指定したレベル `ℓ₂` に、基礎型が `P` の基礎型と同値な命題を見つけられるか。
- 命題宇宙リサイズ：型 `hProp ℓ₁`{.Agda} 全体を `Type ℓ₂`{.Agda} の一つの型で提示できるか。
<!--/-->

```agda

open import Base.Prelude
open import Base.Impredicativity
  using ( Resizing; ΩResizing; ΩResizing→Resizing )
```

<!--en-->
## Excluded middle

Excluded middle supplies a decision for every proposition. Since propositions inhabit different universes, this principle must be stated one level at a time.

**Definition** (`LEM`{.Agda}) We write `LEM ℓ`{.Agda} for excluded middle at level `ℓ`{.Agda}, and define it as the dependent function below. For each `P : hProp ℓ`{.Agda}, it returns a decision `Dec ⟨ P ⟩`{.Agda}: `yes`{.Agda} carries a proof of `P`, while `no`{.Agda} carries a refutation. Because the function ranges over the whole proposition universe `hProp ℓ`{.Agda}, `LEM ℓ`{.Agda} inhabits `Type (ℓ-suc ℓ)`{.Agda}. Its level index therefore records exactly which propositions the classical assumption can decide.
<!--zh-->
## 排中律

排中律为每个命题给出真假的判定。命题分居不同的宇宙，因此这条原理需要逐层陈述。

**定义** (`LEM`{.Agda}) 我们把「`ℓ`{.Agda} 层的排中律」记作 `LEM ℓ`{.Agda}，并将其定义为以下依值函数：对每个 `P : hProp ℓ`{.Agda}，它返回判定 `Dec ⟨ P ⟩`{.Agda}；`yes`{.Agda} 携带 `P` 的证明，`no`{.Agda} 则携带它的反驳。由于这个函数量化整个命题宇宙 `hProp ℓ`{.Agda}，`LEM ℓ`{.Agda} 位于 `Type (ℓ-suc ℓ)`{.Agda}。它的层级指标因而准确标明了这项经典假设可以判定哪些命题。
<!--ja-->
## 排中律

排中律は、各命題に真偽の判定を与える。命題は異なる宇宙に住むため、この原理はレベルごとに述べる必要がある。

**定義** (`LEM`{.Agda}) ここでは「レベル `ℓ`{.Agda} での排中律」を `LEM ℓ`{.Agda} と表し、次の依存関数として定義する。各 `P : hProp ℓ`{.Agda} に対して判定 `Dec ⟨ P ⟩`{.Agda} を返し、`yes`{.Agda} は `P` の証明を、`no`{.Agda} はその反証を運ぶ。この関数は命題宇宙 `hProp ℓ`{.Agda} 全体を量化するので、`LEM ℓ`{.Agda} は `Type (ℓ-suc ℓ)`{.Agda} に住む。したがって、そのレベル添字は、この古典的仮定がどの命題を判定できるかを正確に記録する。
<!--/-->

```agda

LEM : ∀ ℓ → Type (ℓ-suc ℓ)
LEM ℓ = (P : hProp ℓ) → Dec ⟨ P ⟩
```

<!--en-->
**Fact** (`isPropLEM`{.Agda}) At every level `ℓ`{.Agda}, excluded middle `LEM ℓ`{.Agda} is itself a proposition.
<!--zh-->
**事实** (`isPropLEM`{.Agda}) 对每个层级 `ℓ`{.Agda}，排中律 `LEM ℓ`{.Agda} 本身也是命题。
<!--ja-->
**事実** (`isPropLEM`{.Agda}) 各レベル `ℓ`{.Agda} で、排中律 `LEM ℓ`{.Agda} 自体も命題である。
<!--/-->

```agda
isPropLEM : ∀ {ℓ} → isProp (LEM ℓ)
```

<!--en-->
**Proof** For each `P : hProp ℓ`{.Agda}, `isPropDec`{.Agda} makes `Dec ⟨ P ⟩`{.Agda} a proposition. The closure of propositions under dependent functions, `isPropΠ`{.Agda}, then proves the claim pointwise.
<!--zh-->
**证明** 对每个 `P : hProp ℓ`{.Agda}，`isPropDec`{.Agda} 说明 `Dec ⟨ P ⟩`{.Agda} 是命题。再由命题对依赖函数的封闭性 `isPropΠ`{.Agda} 逐点证明结论。
<!--ja-->
**証明** 各 `P : hProp ℓ`{.Agda} に対して、`isPropDec`{.Agda} は `Dec ⟨ P ⟩`{.Agda} が命題であることを示す。命題の依存関数に対する閉性 `isPropΠ`{.Agda} を用いれば、主張が各点で従う。
<!--/-->

```agda
isPropLEM {ℓ} = isPropΠ λ P → isPropDec ⟨ P ⟩isProp
```

∎

<!--en-->
**Lemma** (`lowerLEM`{.Agda}) Excluded middle at a successor level implies excluded middle at the level immediately below. Repeating the lemma descends through further successor levels.
<!--zh-->
**引理** (`lowerLEM`{.Agda}) 后继层级上的排中律蕴含紧邻低一层的排中律。反复应用该引理，即可继续逐层下降。
<!--ja-->
**補題** (`lowerLEM`{.Agda}) 後続レベルでの排中律から、直下のレベルでの排中律が従う。この補題を繰り返し適用すれば、さらに一段ずつ下降できる。
<!--/-->

```agda
lowerLEM : ∀ {ℓ} → LEM (ℓ-suc ℓ) → LEM ℓ
```

<!--en-->
**Proof** Let `lem : LEM (ℓ-suc ℓ)`{.Agda} be given, and fix `P : hProp ℓ`{.Agda}. The hypothesis cannot decide `P` directly because it expects a proposition at level `ℓ-suc ℓ`{.Agda}. We therefore form the higher-level proposition whose underlying type is `Lift ⟨ P ⟩`{.Agda}; its propositionhood certificate is `isOfHLevelLift 1 ⟨ P ⟩isProp`{.Agda}. Applying `lem`{.Agda} to this pair decides the lifted copy of `P`.

The two panels below show how to turn that decision into `Dec ⟨ P ⟩`{.Agda}. The positive branch uses `lower`; the negative branch assumes a proof of `P` and refutes its lifted image. The function `mapDec`{.Agda} assembles these conversions.
<!--zh-->
**证明** 给定 `lem : LEM (ℓ-suc ℓ)`{.Agda}，并固定 `P : hProp ℓ`{.Agda}。`lem` 要求输入 `ℓ-suc ℓ`{.Agda} 层的命题，因而不能直接判定 `P`。为此，构造一个高层命题：其底层类型是 `Lift ⟨ P ⟩`{.Agda}，命题性证书是 `isOfHLevelLift 1 ⟨ P ⟩isProp`{.Agda}。把这一对交给 `lem`{.Agda}，便得到 `P` 的抬升副本的判定。

下图的两个分支说明如何把这一判定转回 `Dec ⟨ P ⟩`{.Agda}：肯定分支使用 `lower`，否定分支则假设 `P` 的证明，并反驳其抬升后的像。函数 `mapDec`{.Agda} 把这两种转换合在一起。
<!--ja-->
**証明** `lem : LEM (ℓ-suc ℓ)`{.Agda} が与えられたとし、`P : hProp ℓ`{.Agda} を固定する。`lem` はレベル `ℓ-suc ℓ`{.Agda} の命題を要求するため、`P` を直接判定することはできない。そこで、基礎型を `Lift ⟨ P ⟩`{.Agda}、命題性の証明を `isOfHLevelLift 1 ⟨ P ⟩isProp`{.Agda} とする上位レベルの命題を作る。この対を `lem`{.Agda} に渡せば、`P` の持ち上げられたコピーを判定できる。

下図の二つの分岐は、この判定を `Dec ⟨ P ⟩`{.Agda} へ戻す方法を示す。肯定の分岐では `lower` を用い、否定の分岐では `P` の証明を仮定してその持ち上げた像を反駁する。関数 `mapDec`{.Agda} が二つの変換をまとめる。
<!--/-->

<figure class="book-diagram type-comparison path-figure" id="fig-lower-lem" aria-describedby="fig-lower-lem-caption">
<div class="diagram-framed">
<div class="type-comparison-panels">
<section class="type-comparison-panel">


$$\operatorname{yes}\,x$$

<div class="path-stage diagram-compact-stage" style="aspect-ratio:360/260">
<svg viewBox="0 0 360 260" aria-hidden="true" focusable="false">
<rect class="diagram-space-shape" x="15" y="10" width="330" height="85"/>
<rect class="diagram-space-shape" x="15" y="165" width="330" height="85"/>
<path class="diagram-map-line" d="M180 74 L180 216"/>
<path class="diagram-map-tip" d="M176 209 L180 216 L184 209"/>
<circle class="diagram-point" cx="180" cy="70" r="4"/>
<circle class="diagram-point" cx="180" cy="220" r="4"/>
</svg>
<span class="path-label" style="left:50%;top:12.6923%">$\operatorname{Lift}\langle P\rangle$</span>
<span class="path-label" style="left:60.5556%;top:26.9231%">$x$</span>
<span class="path-label" style="left:65.8333%;top:50%">$\operatorname{lower}$</span>
<span class="path-label" style="left:16.6667%;top:71.9231%">$\langle P\rangle$</span>
<span class="path-label" style="left:67.2222%;top:84.6154%">$\operatorname{lower}\,x$</span>
</div>

$$\operatorname{yes}\,(\operatorname{lower}\,x)$$


</section>
<section class="type-comparison-panel">


$$\operatorname{no}\,\mathit{np}$$

<div class="path-stage diagram-compact-stage" style="aspect-ratio:360/260">
<svg viewBox="0 0 360 260" aria-hidden="true" focusable="false">
<rect class="diagram-space-shape" x="15" y="10" width="330" height="85"/>
<rect class="diagram-space-shape" x="15" y="165" width="330" height="85"/>
<path class="diagram-map-line" d="M180 216 L180 74"/>
<path class="diagram-map-tip" d="M184 81 L180 74 L176 81"/>
<circle class="diagram-point" cx="180" cy="70" r="4"/>
<circle class="diagram-point" cx="180" cy="220" r="4"/>
</svg>
<span class="path-label" style="left:50%;top:12.6923%">$\operatorname{Lift}\langle P\rangle$</span>
<span class="path-label" style="left:66.9444%;top:26.9231%">$\operatorname{lift}\,p$</span>
<span class="path-label" style="left:64.4444%;top:50%">$\operatorname{lift}$</span>
<span class="path-label" style="left:16.6667%;top:71.9231%">$\langle P\rangle$</span>
<span class="path-label" style="left:60.5556%;top:84.6154%">$p$</span>
</div>

$$\mathit{np}\,(\operatorname{lift}\,p):\bot_0$$


</section>
</div>
</div>
<figcaption id="fig-lower-lem-caption">
<!--en-->
A positive decision sends its proof downward by `lower`. A negative decision refutes a hypothetical `p : ⟨ P ⟩` by sending it upward with `lift` and applying `np`.
<!--zh-->
肯定判定通过 `lower` 把证明向下搬移。否定判定则临时假设 `p : ⟨ P ⟩`，经 `lift` 向上搬移，再由 `np` 得到矛盾。
<!--ja-->
肯定の判定では `lower` で証明を下へ移す。否定の判定では `p : ⟨ P ⟩` を一時的に仮定し、`lift` で上へ移して `np` を適用し、矛盾を得る。
<!--/-->
</figcaption>
</figure>

```agda
lowerLEM {ℓ} lem P =
  mapDec lower (λ np p → np (lift p))
    (lem (Lift ⟨ P ⟩ , isOfHLevelLift 1 ⟨ P ⟩isProp))
  where
  open import Cubical.Foundations.HLevels using ( isOfHLevelLift )
  open import Cubical.Relation.Nullary using ( mapDec )
```

∎

<!--en-->
## Ω-resizing from excluded middle

Once every proposition at the source level can be decided, each can be represented by one of two Boolean labels. For arbitrary levels `ℓ₁`{.Agda} and `ℓ₂`{.Agda}, `ΩResizing ℓ₁ ℓ₂`{.Agda} asks for one type in `Type ℓ₂`{.Agda} equivalent to the entire type `hProp ℓ₁`{.Agda}. This chapter constructs such a classifier from excluded middle at `ℓ₁`{.Agda}. The general theorem `ΩResizing→Resizing`{.Agda} then turns this small presentation of the proposition universe into `Resizing ℓ₁ ℓ₂`{.Agda}: every source-level proposition receives an equivalent representative at the target level.

The classifier uses `Bool`{.Agda}, whose two constructors `true`{.Agda} and `false`{.Agda} serve as its labels. We import precisely these three names here.
<!--zh-->
## 由排中律得到命题宇宙换级

一旦源层的每个命题都可以判定，就能用两个布尔标签之一来代表它。对任意层级 `ℓ₁`{.Agda} 与 `ℓ₂`{.Agda}，`ΩResizing ℓ₁ ℓ₂`{.Agda} 要求 `Type ℓ₂`{.Agda} 中有一个与整个 `hProp ℓ₁`{.Agda} 类型等价的类型。本章从 `ℓ₁`{.Agda} 层的排中律构造这样的分类器，再应用一般定理 `ΩResizing→Resizing`{.Agda}，把这个对命题宇宙的小表示转化为 `Resizing ℓ₁ ℓ₂`{.Agda}：源层的每个命题在目标层都有一个与之类型等价的代表。

分类器采用 `Bool`{.Agda}，以它的两个构造子 `true`{.Agda} 与 `false`{.Agda} 作为标签。这里恰好引入这三个名称。
<!--ja-->
## 排中律から得られる命題宇宙リサイズ

始域レベルのすべての命題を判定できれば、それぞれを二つのブールラベルの一方で表せる。任意のレベル `ℓ₁`{.Agda} と `ℓ₂`{.Agda} に対して、`ΩResizing ℓ₁ ℓ₂`{.Agda} は型 `hProp ℓ₁`{.Agda} 全体と同値な一つの型を `Type ℓ₂`{.Agda} に要求する。本章は `ℓ₁`{.Agda} での排中律からそのような分類子を構成し、一般定理 `ΩResizing→Resizing`{.Agda} によって、この命題宇宙の小さな表示を `Resizing ℓ₁ ℓ₂`{.Agda} へ移す。すなわち、始域レベルの各命題が終域レベルに同値な代表をもつ。

分類子には `Bool`{.Agda} を用い、その二つの構成子 `true`{.Agda} と `false`{.Agda} をラベルとする。ここでは、ちょうどこの三つの名前を導入する。
<!--/-->

```agda

open import Cubical.Data.Bool using ( Bool; true; false )
```

<!--en-->
The labels are codes, not themselves propositions in `hProp ℓ₁`{.Agda}. Since `Bool`{.Agda} lies in `Type ℓ-zero`{.Agda}, the code type is lifted to `Lift {ℓ-zero} {ℓ₂} Bool`{.Agda} in the target universe `Type ℓ₂`{.Agda}. Its two labels will represent `⊤`{.Agda} and `⊥`{.Agda}, both available in `hProp ℓ₁`{.Agda} at every level. Constructing an equivalence between this target-level code type and the proposition universe will therefore give the required Ω-resizing.
<!--zh-->
这些标签只是编码，并非 `hProp ℓ₁`{.Agda} 中的命题。`Bool`{.Agda} 位于 `Type ℓ-zero`{.Agda}，所以要把编码类型提升为目标宇宙 `Type ℓ₂`{.Agda} 中的 `Lift {ℓ-zero} {ℓ₂} Bool`{.Agda}。它的两个标签将分别代表 `hProp ℓ₁`{.Agda} 中的 `⊤`{.Agda} 与 `⊥`{.Agda}，而这两个命题可用于任意层级。只要构造出这个目标层编码类型与命题宇宙之间的等价，就得到了所需的命题宇宙换级。
<!--ja-->
これらのラベルは符号であり、それ自体が `hProp ℓ₁`{.Agda} の命題なのではない。`Bool`{.Agda} は `Type ℓ-zero`{.Agda} に住むため、符号の型を終域宇宙 `Type ℓ₂`{.Agda} の `Lift {ℓ-zero} {ℓ₂} Bool`{.Agda} へ持ち上げる。その二つのラベルは、任意のレベルで使える `hProp ℓ₁`{.Agda} の `⊤`{.Agda} と `⊥`{.Agda} をそれぞれ表す。この終域レベルの符号の型と命題宇宙との同値を構成すれば、求める命題宇宙リサイズが得られる。
<!--/-->

<!--en-->
The construction has two stages. First we define encoding from an explicit decision `Dec ⟨ P ⟩`{.Agda}, then decoding, and finally the two round-trip laws. These four auxiliary results remain private and use no excluded middle. The public theorem then invokes excluded middle to supply a decision for every `P` and assembles the four results into the equivalence.
<!--zh-->
构造分为两步。第一步先根据显式判定 `Dec ⟨ P ⟩`{.Agda} 定义编码，再定义解码，最后证明两条往返律。这四项辅助结果保持私有，并且都不使用排中律。第二步的公开定理才调用排中律，为每个 `P` 统一给出判定，并把这四项结果组装成所需的等价。
<!--ja-->
構成は二段階に分かれる。第一段階では、まず明示的な判定 `Dec ⟨ P ⟩`{.Agda} から符号化を定義し、次に復号を定義し、最後に二つの往復則を証明する。この四つの補助結果は非公開のままであり、いずれも排中律を使わない。第二段階の公開定理で初めて排中律を呼び出し、各 `P` に判定を一様に与え、この四つの結果を求める同値へ組み立てる。
<!--/-->

<!--en-->
**Lemma** (`encodeB`{.Agda}) There is an encoding operation that takes a proposition `P` together with its decision and returns a code in `Lift {ℓ-zero} {ℓ₂} Bool`{.Agda}.
<!--zh-->
**引理** (`encodeB`{.Agda}) 存在一个编码操作，它以命题 `P` 及其判定为输入，返回 `Lift {ℓ-zero} {ℓ₂} Bool`{.Agda} 中的编码。
<!--ja-->
**補題** (`encodeB`{.Agda}) 命題 `P` とその判定を入力として受け取り、`Lift {ℓ-zero} {ℓ₂} Bool`{.Agda} の符号を返す符号化操作が存在する。
<!--/-->

```agda

private
  encodeB : ∀ {ℓ₁ ℓ₂} (P : hProp ℓ₁) → Dec ⟨ P ⟩ → Lift {ℓ-zero} {ℓ₂} Bool
```

<!--en-->
**Proof** Inspect the supplied decision. The `yes`{.Agda} branch returns `lift true`{.Agda}, while the `no`{.Agda} branch returns `lift false`{.Agda}. Both branches discard the particular proof or refutation and retain only which outcome holds. Because the decision is supplied explicitly, encoding uses no excluded middle.
<!--zh-->
**证明** 考察给定的判定。`yes`{.Agda} 分支返回 `lift true`{.Agda}，`no`{.Agda} 分支返回 `lift false`{.Agda}。两个分支都舍去具体的证明或反驳，只保留哪一种结果成立。由于判定是显式给出的，编码过程不使用排中律。
<!--ja-->
**証明** 与えられた判定を調べる。`yes`{.Agda} の枝は `lift true`{.Agda} を返し、`no`{.Agda} の枝は `lift false`{.Agda} を返す。どちらの枝も具体的な証明や反証を捨て、どちらの結果が成り立つかだけを保持する。判定は明示的に与えられるため、符号化は排中律を使わない。
<!--/-->

```agda
  encodeB P (yes _) = lift true
  encodeB P (no _)  = lift false
```

∎

<!--en-->
**Lemma** (`decodeB`{.Agda}) There is a decoding operation that takes a code in `Lift {ℓ-zero} {ℓ₂} Bool`{.Agda} and returns a proposition in `hProp ℓ₁`{.Agda}.
<!--zh-->
**引理** (`decodeB`{.Agda}) 存在一个解码操作，它以 `Lift {ℓ-zero} {ℓ₂} Bool`{.Agda} 中的编码为输入，返回 `hProp ℓ₁`{.Agda} 中的命题。
<!--ja-->
**補題** (`decodeB`{.Agda}) `Lift {ℓ-zero} {ℓ₂} Bool`{.Agda} の符号を入力として受け取り、`hProp ℓ₁`{.Agda} の命題を返す復号操作が存在する。
<!--/-->

```agda
  decodeB : ∀ {ℓ₁ ℓ₂} → Lift {ℓ-zero} {ℓ₂} Bool → hProp ℓ₁
```

<!--en-->
**Proof** Inspect the supplied code. The `lift true`{.Agda} branch returns `⊤`{.Agda}, while the `lift false`{.Agda} branch returns `⊥`{.Agda}. Both branches discard the label and retain only the proposition it represents. Because the two cases are handled directly, decoding also uses no excluded middle.
<!--zh-->
**证明** 考察给定的编码。`lift true`{.Agda} 分支返回 `⊤`{.Agda}，`lift false`{.Agda} 分支返回 `⊥`{.Agda}。两个分支都舍去标签，只保留它所代表的命题。由于两种情形都是直接给出的，解码过程同样不使用排中律。
<!--ja-->
**証明** 与えられた符号を調べる。`lift true`{.Agda} の枝は `⊤`{.Agda} を返し、`lift false`{.Agda} の枝は `⊥`{.Agda} を返す。どちらの枝もラベルを捨て、それが表す命題だけを保持する。二つの場合を直接与えるため、復号も排中律を使わない。
<!--/-->

```agda
  decodeB (lift true)  = ⊤
  decodeB (lift false) = ⊥
```

∎

<!--en-->
**Lemma** (`secB`{.Agda}) For every proposition `P` and decision `d`, encoding with `encodeB`{.Agda} and then decoding with `decodeB`{.Agda} recovers `P` in `hProp`: `decodeB (encodeB P d) ≡ P`{.Agda}.
<!--zh-->
**引理** (`secB`{.Agda}) 对任意命题 `P` 及其判定 `d`，先用 `encodeB`{.Agda} 编码，再用 `decodeB`{.Agda} 解码，会在 `hProp` 中恢复 `P`：`decodeB (encodeB P d) ≡ P`{.Agda}。
<!--ja-->
**補題** (`secB`{.Agda}) 任意の命題 `P` とその判定 `d` に対して、`encodeB`{.Agda} で符号化してから `decodeB`{.Agda} で復号すると、`hProp` で `P` が復元される。すなわち `decodeB (encodeB P d) ≡ P`{.Agda} である。
<!--/-->

```agda
  secB : ∀ {ℓ₁ ℓ₂} (P : hProp ℓ₁) (d : Dec ⟨ P ⟩)
       → decodeB {ℓ₁} {ℓ₂} (encodeB {ℓ₁} {ℓ₂} P d) ≡ P
```

<!--en-->
**Proof** Split on `d`. If `d = yes p`{.Agda}, encoding selects `lift true`{.Agda} and decoding returns `⊤`{.Agda}, so the goal becomes `⊤ ≡ P`{.Agda}. Propositional extensionality `⇔toPath`{.Agda} constructs this path from the map returning `p` and the map returning `tt*`{.Agda}. If `d = no np`{.Agda}, encoding selects `lift false`{.Agda} and decoding returns `⊥`{.Agda}, so the goal becomes `⊥ ≡ P`{.Agda}. Its two maps are the absurd function `λ ()` and the refutation `np` followed by elimination from `⊥₀`{.Agda}. Thus decoding after encoding recovers a proposition equal to `P` in both cases.
<!--zh-->
**证明** 对 `d` 分情形。若 `d = yes p`{.Agda}，编码选出 `lift true`{.Agda}，解码得到 `⊤`{.Agda}，所以目标化为 `⊤ ≡ P`{.Agda}。命题外延性 `⇔toPath`{.Agda} 从两个方向的映射构造这条路径：一个映射返回 `p`，另一个映射返回 `tt*`{.Agda}。若 `d = no np`{.Agda}，编码选出 `lift false`{.Agda}，解码得到 `⊥`{.Agda}，所以目标化为 `⊥ ≡ P`{.Agda}。两个方向的映射分别是荒谬函数 `λ ()`，以及先应用反驳 `np`、再从 `⊥₀`{.Agda} 消去的函数。因此在两种情形下，先编码再解码都会恢复一个与 `P` 相等的命题。
<!--ja-->
**証明** `d` について場合分けする。`d = yes p`{.Agda} なら、符号化は `lift true`{.Agda} を選び、復号は `⊤`{.Agda} を返すため、ゴールは `⊤ ≡ P`{.Agda} となる。命題外延性 `⇔toPath`{.Agda} は、`p` を返す写像と `tt*`{.Agda} を返す写像からこのパスを構成する。`d = no np`{.Agda} なら、符号化は `lift false`{.Agda} を選び、復号は `⊥`{.Agda} を返すため、ゴールは `⊥ ≡ P`{.Agda} となる。両方向の写像は、荒謬関数 `λ ()` と、反証 `np` を適用してから `⊥₀`{.Agda} から消去する関数である。したがって、どちらの場合も符号化してから復号すると `P` と等しい命題が復元される。
<!--/-->

```agda
  secB {ℓ₁} {ℓ₂} P (yes p) = ⇔toPath (λ _ → p) (λ _ → tt*)
  secB {ℓ₁} {ℓ₂} P (no np) = ⇔toPath (λ ()) (λ p → ⊥₀-rec (np p))
```

∎

<!--en-->
**Lemma** (`retrB`{.Agda}) For every code `b` and decision `d` of the proposition it decodes to, decoding with `decodeB`{.Agda} and then encoding with `encodeB`{.Agda} recovers `b`: `encodeB (decodeB b) d ≡ b`{.Agda}.
<!--zh-->
**引理** (`retrB`{.Agda}) 对任意编码 `b` 及其解码所得命题的判定 `d`，先用 `decodeB`{.Agda} 解码，再用 `encodeB`{.Agda} 编码，会恢复 `b`：`encodeB (decodeB b) d ≡ b`{.Agda}。
<!--ja-->
**補題** (`retrB`{.Agda}) 任意の符号 `b` と、その復号で得た命題の判定 `d` に対して、`decodeB`{.Agda} で復号してから `encodeB`{.Agda} で符号化すると `b` が復元される。すなわち `encodeB (decodeB b) d ≡ b`{.Agda} である。
<!--/-->

```agda
  retrB : ∀ {ℓ₁ ℓ₂} (b : Lift {ℓ-zero} {ℓ₂} Bool)
          (d : Dec ⟨ decodeB {ℓ₁} {ℓ₂} b ⟩)
        → encodeB {ℓ₁} {ℓ₂} (decodeB {ℓ₁} {ℓ₂} b) d ≡ b
```

<!--en-->
**Proof** Split on `b` and then on `d`, giving four cases. If `b = lift true`{.Agda}, decoding returns `⊤`{.Agda}. A proof selects `lift true`{.Agda} again, so the equality is `refl`{.Agda}; a refutation is impossible because applying it to `tt*`{.Agda} produces an element of `⊥₀`{.Agda}. If `b = lift false`{.Agda}, decoding returns `⊥`{.Agda}. A proof is impossible by the empty pattern `()`; a refutation selects `lift false`{.Agda} again, so the equality is `refl`{.Agda}. Thus encoding after decoding recovers the original code in every possible case.
<!--zh-->
**证明** 先对 `b` 分情形，再对 `d` 分情形，共有四种组合。若 `b = lift true`{.Agda}，解码得到 `⊤`{.Agda}。证明会再次选出 `lift true`{.Agda}，所以等式由 `refl`{.Agda} 成立；反驳则不可能存在，因为把它用于 `tt*`{.Agda} 就会得到 `⊥₀`{.Agda} 的元素。若 `b = lift false`{.Agda}，解码得到 `⊥`{.Agda}。证明因空模式 `()` 而不可能；反驳会再次选出 `lift false`{.Agda}，所以等式也由 `refl`{.Agda} 成立。因此在所有可能的情形下，先解码再编码都会恢复原编码。
<!--ja-->
**証明** まず `b` について場合分けし、次に `d` について場合分けするので、組合せは四つである。`b = lift true`{.Agda} なら、復号は `⊤`{.Agda} を返す。証明は再び `lift true`{.Agda} を選ぶため、等式は `refl`{.Agda} で成り立つ。反証は `tt*`{.Agda} に適用すると `⊥₀`{.Agda} の元を生じるため不可能である。`b = lift false`{.Agda} なら、復号は `⊥`{.Agda} を返す。証明は空パターン `()` によって不可能であり、反証は再び `lift false`{.Agda} を選ぶため、等式は `refl`{.Agda} で成り立つ。したがって、可能なすべての場合に復号してから符号化すると元の符号が復元される。
<!--/-->

```agda
  retrB {ℓ₁} {ℓ₂} (lift true)  (yes _)  = refl
  retrB {ℓ₁} {ℓ₂} (lift true)  (no n⊤) = ⊥₀-rec (n⊤ tt*)
  retrB {ℓ₁} {ℓ₂} (lift false) (yes ())
  retrB {ℓ₁} {ℓ₂} (lift false) (no _)  = refl
```

∎

<!--en-->
The two round-trip laws show that encoding and decoding become mutually inverse once a decision is supplied uniformly for every proposition. The resulting classifier will therefore be a genuine type equivalence, not merely a surjective labelling of propositions by two truth values.
<!--zh-->
两条往返律共同表明：只要能为每个命题统一给出判定，编码与解码就互为逆映射。因此，所得分类器将给出真正的类型等价，而不只是用两个真值标签满射地覆盖命题。
<!--ja-->
二つの往復則から、各命題に判定を一様に与えられれば、符号化と復号が互いに逆写像になることがわかる。したがって、得られる分類子は二つの真理値ラベルで命題を全射的に覆うだけではなく、真正な型同値を与える。
<!--/-->

<!--en-->
The candidate witness is the pair `(Lift Bool , ...)`{.Agda}. Its first component lies in `Type ℓ₂`{.Agda}, and its second will be an equivalence `hProp ℓ₁ ≃ Lift Bool`{.Agda}. No ordering between `ℓ₁` and `ℓ₂` is required. The downward instance used later takes `ℓ₁ = ℓ-suc ℓ` and `ℓ₂ = ℓ`, but equal or higher target levels are allowed as well. Excluded middle has only one remaining role: it supplies the decisions used by the encoder uniformly; all four private results above are constructive.
<!--zh-->
候选见证是序对 `(Lift Bool , ...)`{.Agda}：第一分量位于 `Type ℓ₂`{.Agda}，第二分量将是类型等价 `hProp ℓ₁ ≃ Lift Bool`{.Agda}。这里不要求 `ℓ₁` 与 `ℓ₂` 具有任何大小关系。后文使用的向下实例取 `ℓ₁ = ℓ-suc ℓ`、`ℓ₂ = ℓ`，但目标层级也可以与源层级相同或更高。排中律只剩下一项作用：为编码器统一提供所需的判定；以上四项私有结果都是构造主义的。
<!--ja-->
候補となる証拠は対 `(Lift Bool , ...)`{.Agda} である。第一成分は `Type ℓ₂`{.Agda} に住み、第二成分は型同値 `hProp ℓ₁ ≃ Lift Bool`{.Agda} となる。ここでは `ℓ₁` と `ℓ₂` の大小関係を要求しない。後で使う下向きの実例では `ℓ₁ = ℓ-suc ℓ`、`ℓ₂ = ℓ` とするが、終域レベルが始域レベルと同じ場合や高い場合も許される。排中律に残された役割は一つだけであり、符号化器が必要とする判定を一様に供給することである。以上の四つの非公開な結果はいずれも構成的である。
<!--/-->

<!--en-->
**Theorem** (`lem→ΩResizing`{.Agda}) For arbitrary levels `ℓ₁`{.Agda} and `ℓ₂`{.Agda}, excluded middle at the source level `ℓ₁`{.Agda} implies Ω-resizing from `ℓ₁`{.Agda} to `ℓ₂`{.Agda}.
<!--zh-->
**定理** (`lem→ΩResizing`{.Agda}) 对任意层级 `ℓ₁`{.Agda} 与 `ℓ₂`{.Agda}，源层 `ℓ₁`{.Agda} 的排中律蕴含从 `ℓ₁`{.Agda} 到 `ℓ₂`{.Agda} 的命题宇宙换级。
<!--ja-->
**定理** (`lem→ΩResizing`{.Agda}) 任意のレベル `ℓ₁`{.Agda} と `ℓ₂`{.Agda} に対して、始域レベル `ℓ₁`{.Agda} での排中律は、`ℓ₁`{.Agda} から `ℓ₂`{.Agda} への命題宇宙リサイズを導く。
<!--/-->

```agda
lem→ΩResizing : ∀ {ℓ₁ ℓ₂} → LEM ℓ₁ → ΩResizing ℓ₁ ℓ₂
```

<!--en-->
**Proof** Choose `Lift Bool`{.Agda} as the first component. For the second, use `isoToEquiv`{.Agda} to turn the following isomorphism into an equivalence. Its forward map sends `P` to `encodeB P (lem P)`{.Agda}, and its backward map is `decodeB`{.Agda}. The round-trip laws are `retrB`{.Agda} and `secB`{.Agda}, each instantiated with the decision supplied by `lem`. These two components form the required witness of `ΩResizing ℓ₁ ℓ₂`{.Agda}.
<!--zh-->
**证明** 取 `Lift Bool`{.Agda} 为第一分量。第二分量使用 `isoToEquiv`{.Agda}，把下面的同构转化为类型等价。同构的正向映射把 `P` 送到 `encodeB P (lem P)`{.Agda}，逆向映射是 `decodeB`{.Agda}；两条往返律分别使用 `retrB`{.Agda} 与 `secB`{.Agda}，并以 `lem` 给出的判定将其具体化。这两个分量共同构成 `ΩResizing ℓ₁ ℓ₂`{.Agda} 所需的见证。
<!--ja-->
**証明** 第一成分として `Lift Bool`{.Agda} を選ぶ。第二成分には `isoToEquiv`{.Agda} を用い、次の同型を型同値へ変換する。同型の順写像は `P` を `encodeB P (lem P)`{.Agda} へ送り、逆写像は `decodeB`{.Agda} である。二つの往復則には、`lem` が与える判定で具体化した `retrB`{.Agda} と `secB`{.Agda} を用いる。この二つの成分が `ΩResizing ℓ₁ ℓ₂`{.Agda} に必要な証拠を構成する。
<!--/-->

<!--en-->
The two round-trip laws close the two triangles below. Fix `lem : LEM ℓ₁`, abbreviate the code type `Lift {ℓ-zero} {ℓ₂} Bool` by $B$, and write $E(P) := \operatorname{encodeB}\,P\,(\operatorname{lem}\,P)$ and $D := \operatorname{decodeB}$. Each round trip returns a point connected to its starting point by the indicated path.
<!--zh-->
下面两个三角形分别由两条往返律闭合。固定 `lem : LEM ℓ₁`，把编码类型 `Lift {ℓ-zero} {ℓ₂} Bool` 简写为 $B$，并记 $E(P) := \operatorname{encodeB}\,P\,(\operatorname{lem}\,P)$、$D := \operatorname{decodeB}$。每次往返所得的点，都由标出的路径与出发点相连。
<!--ja-->
下の二つの三角形は、それぞれ二つの往復則によって閉じる。`lem : LEM ℓ₁` を固定し、符号の型 `Lift {ℓ-zero} {ℓ₂} Bool` を $B$ と略記し、$E(P) := \operatorname{encodeB}\,P\,(\operatorname{lem}\,P)$、$D := \operatorname{decodeB}$ と書く。各往復で得られる点は、示したパスによって出発点と結ばれる。
<!--/-->

<figure class="book-diagram type-comparison path-figure" id="fig-classical-roundtrips" aria-describedby="fig-classical-roundtrips-caption">
<div class="type-comparison-panels classical-roundtrips">
<div class="path-stage" style="aspect-ratio:360/300">
<svg viewBox="0 0 360 300" aria-hidden="true" focusable="false">
<rect class="diagram-space-shape" x="105" y="5" width="150" height="95"/>
<rect class="diagram-space-shape" x="5" y="145" width="350" height="150"/>
<path class="diagram-map-line" d="M78 200 L174 89 M186 89 L282 200"/>
<path class="diagram-map-tip" d="M166 92 L174 89 L174 97 M274 197 L282 200 L282 192"/>
<path class="diagram-path" d="M75 205 Q180 295 285 205"/>
<circle class="diagram-point" cx="180" cy="80" r="4"/>
<circle class="diagram-point" cx="75" cy="205" r="4"/>
<circle class="diagram-point" cx="285" cy="205" r="4"/>
</svg>
<span class="path-label" style="left:50%;top:8.33%">$B$</span>
<span class="path-label" style="left:50%;top:18.33%">$E(P)$</span>
<span class="path-label" style="left:50%;top:56.67%">$\operatorname{hProp}\,\ell_1$</span>
<span class="path-label" style="left:20.83%;top:82%">$P$</span>
<span class="path-label" style="left:79.17%;top:82%">$D(E(P))$</span>
<span class="path-label" style="left:25%;top:39%">$E$</span>
<span class="path-label" style="left:75%;top:39%">$D$</span>
<span class="path-label" style="left:50%;top:88.67%">$\operatorname{secB}$</span>
</div>
<div class="path-stage" style="aspect-ratio:360/300">
<svg viewBox="0 0 360 300" aria-hidden="true" focusable="false">
<rect class="diagram-space-shape" x="105" y="5" width="150" height="95"/>
<rect class="diagram-space-shape" x="5" y="145" width="350" height="150"/>
<path class="diagram-map-line" d="M78 200 L174 89 M186 89 L282 200"/>
<path class="diagram-map-tip" d="M166 92 L174 89 L174 97 M274 197 L282 200 L282 192"/>
<path class="diagram-path" d="M75 205 Q180 295 285 205"/>
<circle class="diagram-point" cx="180" cy="80" r="4"/>
<circle class="diagram-point" cx="75" cy="205" r="4"/>
<circle class="diagram-point" cx="285" cy="205" r="4"/>
</svg>
<span class="path-label" style="left:50%;top:8.33%">$\operatorname{hProp}\,\ell_1$</span>
<span class="path-label" style="left:50%;top:18.33%">$D(b)$</span>
<span class="path-label" style="left:50%;top:56.67%">$B$</span>
<span class="path-label" style="left:20.83%;top:82%">$b$</span>
<span class="path-label" style="left:79.17%;top:82%">$E(D(b))$</span>
<span class="path-label" style="left:25%;top:39%">$D$</span>
<span class="path-label" style="left:75%;top:39%">$E$</span>
<span class="path-label" style="left:50%;top:88.67%">$\operatorname{retrB}$</span>
</div>
</div>
<figcaption id="fig-classical-roundtrips-caption">
<!--en-->
Encoding and decoding are inverse up to paths. Excluded middle supplies the decisions in $E$; with explicit decisions, encoding, decoding and both round-trip laws are constructive.
<!--zh-->
编码与解码在路径意义下互为逆映射。排中律为 $E$ 提供判定；给定显式判定后，编码、解码与两条往返律都是构造主义的。
<!--ja-->
符号化と復号はパスの意味で互いに逆となる。排中律は $E$ に判定を供給する。明示的な判定が与えられれば、符号化・復号と二つの往復則はいずれも構成的である。
<!--/-->
</figcaption>
</figure>

```agda
lem→ΩResizing lem = Lift Bool , isoToEquiv (iso
  (λ P → encodeB P (lem P)) decodeB
  (λ b → retrB {ℓ₁ = _} b (lem (decodeB b)))
  (λ P → secB {ℓ₂ = _} P (lem P)))
```

∎

<!--en-->
**Corollary** (`lem→resizing`{.Agda}) For arbitrary levels `ℓ₁`{.Agda} and `ℓ₂`{.Agda}, excluded middle at the source level `ℓ₁`{.Agda} implies propositional resizing from `ℓ₁`{.Agda} to `ℓ₂`{.Agda}.
<!--zh-->
**推论** (`lem→resizing`{.Agda}) 对任意层级 `ℓ₁`{.Agda} 与 `ℓ₂`{.Agda}，源层 `ℓ₁`{.Agda} 的排中律蕴含从 `ℓ₁`{.Agda} 到 `ℓ₂`{.Agda} 的命题换级。
<!--ja-->
**系** (`lem→resizing`{.Agda}) 任意のレベル `ℓ₁`{.Agda} と `ℓ₂`{.Agda} に対して、始域レベル `ℓ₁`{.Agda} での排中律は、`ℓ₁`{.Agda} から `ℓ₂`{.Agda} への命題リサイズを導く。
<!--/-->

```agda
lem→resizing : ∀ {ℓ₁ ℓ₂} → LEM ℓ₁ → Resizing ℓ₁ ℓ₂
```

<!--en-->
**Proof** Apply `lem→ΩResizing`{.Agda}, then convert the resulting proposition-universe resizing with the general theorem `ΩResizing→Resizing`{.Agda}.
<!--zh-->
**证明** 先应用 `lem→ΩResizing`{.Agda} 得到命题宇宙换级，再用一般定理 `ΩResizing→Resizing`{.Agda} 将其转化为命题换级。
<!--ja-->
**証明** まず `lem→ΩResizing`{.Agda} を適用して命題宇宙リサイズを得てから、一般定理 `ΩResizing→Resizing`{.Agda} によって命題リサイズへ変換する。
<!--/-->

```agda
lem→resizing lem = ΩResizing→Resizing (lem→ΩResizing lem)
```

∎

<!--en-->
## Recap

This chapter stated excluded middle level by level as `LEM ℓ`{.Agda}, proved that it is itself a proposition, and used `lowerLEM`{.Agda} to obtain the instance immediately below a successor level. From `LEM ℓ₁`{.Agda}, `lem→ΩResizing`{.Agda} constructs `ΩResizing ℓ₁ ℓ₂`{.Agda} at any target level `ℓ₂`{.Agda}; composing this result with `ΩResizing→Resizing`{.Agda} gives `Resizing ℓ₁ ℓ₂`{.Agda}. Thus one source-level assumption of excluded middle resolves both size questions posed at the beginning of the chapter.
<!--zh-->
## 小结

本章把排中律逐层写成 `LEM ℓ`{.Agda}，证明它本身是命题，并用 `lowerLEM`{.Agda} 从后继层级的排中律得到紧邻低一层的实例。给定 `LEM ℓ₁`{.Agda}，`lem→ΩResizing`{.Agda} 对任意目标层级 `ℓ₂`{.Agda} 构造 `ΩResizing ℓ₁ ℓ₂`{.Agda}；再与 `ΩResizing→Resizing`{.Agda} 复合，便得到 `Resizing ℓ₁ ℓ₂`{.Agda}。因此，源层级上的同一个排中律假设解决了本章开头提出的两个大小问题。
<!--ja-->
## まとめ

本章では排中律をレベルごとに `LEM ℓ`{.Agda} と定め、それ自身が命題であることを示し、`lowerLEM`{.Agda} によって後続レベルの排中律から直下の実例を得た。`LEM ℓ₁`{.Agda} が与えられると、`lem→ΩResizing`{.Agda} は任意の目標レベル `ℓ₂`{.Agda} に対して `ΩResizing ℓ₁ ℓ₂`{.Agda} を構成する。さらに `ΩResizing→Resizing`{.Agda} と合成すれば、`Resizing ℓ₁ ℓ₂`{.Agda} が得られる。したがって、始域レベルでの一つの排中律の仮定が、本章の冒頭で挙げた二つの大きさの問題をともに解決する。
<!--/-->
