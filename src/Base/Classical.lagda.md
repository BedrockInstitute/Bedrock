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

That decision is converted back to a decision of `P` in two cases:

- A proof `x : Lift ⟨ P ⟩`{.Agda} yields the proof `lower x : ⟨ P ⟩`{.Agda}.
- A refutation `np : Lift ⟨ P ⟩ → ⊥₀`{.Agda} yields a refutation of `P`: given `p : ⟨ P ⟩`{.Agda}, lift it and apply `np`{.Agda}, obtaining `np (lift p) : ⊥₀`{.Agda}.

The function `mapDec`{.Agda} performs exactly these two conversions, producing the required `Dec ⟨ P ⟩`{.Agda}.
<!--zh-->
**证明** 给定 `lem : LEM (ℓ-suc ℓ)`{.Agda}，并固定 `P : hProp ℓ`{.Agda}。`lem` 要求输入 `ℓ-suc ℓ`{.Agda} 层的命题，因而不能直接判定 `P`。为此，构造一个高层命题：其底层类型是 `Lift ⟨ P ⟩`{.Agda}，命题性证书是 `isOfHLevelLift 1 ⟨ P ⟩isProp`{.Agda}。把这一对交给 `lem`{.Agda}，便得到 `P` 的抬升副本的判定。

再分两种情形把该判定转回 `P` 的判定：

- 若得到证明 `x : Lift ⟨ P ⟩`{.Agda}，则 `lower x : ⟨ P ⟩`{.Agda} 证明 `P`。
- 若得到反驳 `np : Lift ⟨ P ⟩ → ⊥₀`{.Agda}，则它也能反驳 `P`：给定 `p : ⟨ P ⟩`{.Agda}，先将其抬升，再应用 `np`{.Agda}，便得到 `np (lift p) : ⊥₀`{.Agda}。

`mapDec`{.Agda} 恰好完成这两种转换，由此给出所需的 `Dec ⟨ P ⟩`{.Agda}。
<!--ja-->
**証明** `lem : LEM (ℓ-suc ℓ)`{.Agda} が与えられたとし、`P : hProp ℓ`{.Agda} を固定する。`lem` はレベル `ℓ-suc ℓ`{.Agda} の命題を要求するため、`P` を直接判定することはできない。そこで、基礎型を `Lift ⟨ P ⟩`{.Agda}、命題性の証明を `isOfHLevelLift 1 ⟨ P ⟩isProp`{.Agda} とする上位レベルの命題を作る。この対を `lem`{.Agda} に渡せば、`P` の持ち上げられたコピーを判定できる。

得られた判定を、次の二つの場合に分けて `P` の判定へ戻す。

- 証明 `x : Lift ⟨ P ⟩`{.Agda} が得られたなら、`lower x : ⟨ P ⟩`{.Agda} が `P` を証明する。
- 反証 `np : Lift ⟨ P ⟩ → ⊥₀`{.Agda} が得られたなら、それは `P` も反証する。実際、`p : ⟨ P ⟩`{.Agda} を仮定し、持ち上げて `np`{.Agda} に渡せば、`np (lift p) : ⊥₀`{.Agda} を得る。

`mapDec`{.Agda} はまさにこの二つの変換を行い、必要な `Dec ⟨ P ⟩`{.Agda} を与える。
<!--/-->

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
The labels are not themselves propositions. They form the code type, which must inhabit the chosen target universe. Since `Bool`{.Agda} lies in `Type ℓ-zero`{.Agda}, we use `Lift {ℓ-zero} {ℓ₂} Bool`{.Agda} in `Type ℓ₂`{.Agda}. Decoding will send its two labels to values of `hProp ℓ₁`{.Agda}; paths in `hProp` will then show that those values represent the intended propositions. The code type and `hProp ℓ₁`{.Agda} may lie in different universes, which is precisely what allows the resulting equivalence to resize the proposition universe.
<!--zh-->
标签本身不是命题，而是编码类型中的两个值；这个编码类型必须位于指定的目标宇宙。`Bool`{.Agda} 位于 `Type ℓ-zero`{.Agda}，所以这里采用 `Type ℓ₂`{.Agda} 中的 `Lift {ℓ-zero} {ℓ₂} Bool`{.Agda}。解码会把两个标签送到 `hProp ℓ₁`{.Agda} 中的值，再用 `hProp` 中的路径证明这些值确实代表相应的命题。编码类型与 `hProp ℓ₁`{.Agda} 可以位于不同宇宙，所得等价因此能够实现命题宇宙换级。
<!--ja-->
ラベル自体は命題ではなく、符号の型に属する二つの値である。この符号の型は、指定した終域宇宙に住まなければならない。`Bool`{.Agda} は `Type ℓ-zero`{.Agda} に住むため、ここでは `Type ℓ₂`{.Agda} の `Lift {ℓ-zero} {ℓ₂} Bool`{.Agda} を用いる。復号によって二つのラベルを `hProp ℓ₁`{.Agda} の値へ送り、さらに `hProp` のパスによって、その値が意図した命題を表すことを示す。符号の型と `hProp ℓ₁`{.Agda} は異なる宇宙に住めるため、得られる同値は命題宇宙のリサイズを実現できる。
<!--/-->

<!--en-->
We first define decoding and encoding without using excluded middle. Decoding assigns a representative proposition to each label. Encoding accepts an explicit decision of `P` and selects the corresponding label. After proving that these maps are inverse for every supplied decision, excluded middle will provide the decisions uniformly.
<!--zh-->
我们先在不使用排中律的情况下定义解码与编码。解码为每个标签指定代表命题；编码接受 `P` 的显式判定，并据此选择标签。两条逆律将对任意给定的判定成立。最后才使用排中律，为所有命题统一提供所需的判定。
<!--ja-->
まず、排中律を使わずに復号と符号化を定義する。復号は各ラベルに代表命題を割り当てる。符号化は `P` の判定を明示的に受け取り、それに応じてラベルを選ぶ。二つの逆法則は、どの判定が与えられても成り立つように証明する。最後にだけ排中律を使い、すべての命題に必要な判定を一様に与える。
<!--/-->

<!--en-->
The two representatives are the propositions `⊤`{.Agda} and `⊥`{.Agda} introduced in the Prelude. Their underlying types are respectively the lifted unit type and the lifted empty type `⊥*`{.Agda}. Both propositions are available at every level `ℓ₁`, so they can serve as the two values in `hProp ℓ₁`{.Agda} denoted by the Boolean labels.
<!--zh-->
两个代表是《基础词汇》中引入的命题 `⊤`{.Agda} 与 `⊥`{.Agda}。它们的底层类型分别是抬升后的单位类型与空类型 `⊥*`{.Agda}。这两个命题可用于任意层级 `ℓ₁`，因而能够作为 `hProp ℓ₁`{.Agda} 中由布尔标签指称的两个值。
<!--ja-->
二つの代表は、「基礎語彙」で導入した命題 `⊤`{.Agda} と `⊥`{.Agda} である。その基礎型は、それぞれ持ち上げられた単位型と空型 `⊥*`{.Agda} である。どちらの命題も任意のレベル `ℓ₁` で使えるため、ブールラベルが指す `hProp ℓ₁`{.Agda} の二つの値として利用できる。
<!--/-->

<!--en-->
We begin with the private decoding map. Its type sends a lifted Boolean label to the proposition in `hProp ℓ₁`{.Agda} represented by that label. The map remains private because the Boolean code is only auxiliary data for proving the public resizing theorem.
<!--zh-->
先定义私有的解码映射。它把提升后的布尔标签送到 `hProp ℓ₁`{.Agda} 中由该标签代表的命题。布尔编码只是证明公开换级定理时使用的辅助资料，因此这个映射不对外公开。
<!--ja-->
まず、非公開の復号写像を定義する。その型は、持ち上げたブールラベルを、そのラベルが表す `hProp ℓ₁`{.Agda} の命題へ送る。ブール符号は公開されるリサイズ定理を証明するための補助データにすぎないため、この写像は公開しない。
<!--/-->

```agda

private
  decodeB : ∀ {ℓ₁ ℓ₂} → Lift {ℓ-zero} {ℓ₂} Bool → hProp ℓ₁
```

<!--en-->
The defining equations send `lift true`{.Agda} to `⊤`{.Agda} and `lift false`{.Agda} to `⊥`{.Agda}. By themselves they merely assign representatives; the two inverse laws below will show that no proposition or Boolean code is lost.
<!--zh-->
两条定义式把 `lift true`{.Agda} 送到 `⊤`{.Agda}，把 `lift false`{.Agda} 送到 `⊥`{.Agda}。这两式本身只负责指派代表；下面两条逆律将证明命题与布尔编码都不会在往返中丢失。
<!--ja-->
二つの定義式は、`lift true`{.Agda} を `⊤`{.Agda} へ、`lift false`{.Agda} を `⊥`{.Agda} へ送る。これらの式だけでは代表を割り当てたにすぎない。後に続く二つの逆法則が、命題もブール符号も往復で失われないことを示す。
<!--/-->

```agda
  decodeB (lift true)  = ⊤
  decodeB (lift false) = ⊥
```

<!--en-->
Encoding goes in the opposite direction. Given `P` together with a decision of `P`, it returns `true`{.Agda} for a proof and `false`{.Agda} for a refutation. The decision is an explicit argument rather than something `encodeB`{.Agda} derives, so this definition itself uses no excluded middle.
<!--zh-->
编码沿相反方向进行。给定 `P` 及其判定，若得到证明便返回 `true`{.Agda}，若得到反驳便返回 `false`{.Agda}。判定是显式参数，并非由 `encodeB`{.Agda} 自行导出，因此这个定义本身不使用排中律。
<!--ja-->
符号化は逆向きに進む。`P` とその判定を受け取り、証明が得られた場合は `true`{.Agda}、反証が得られた場合は `false`{.Agda} を返す。判定は `encodeB`{.Agda} 自身が導くのではなく、明示的な引数として与えられるため、この定義そのものは排中律を使わない。
<!--/-->

<!--en-->
Pattern matching examines the decision, not the proposition `P` itself. `yes`{.Agda} yields `lift true`{.Agda} and `no`{.Agda} yields `lift false`{.Agda}. In either branch the proof or refutation is discarded, because the code records only which alternative holds. The result lies in `Lift {ℓ-zero} {ℓ₂} Bool`{.Agda}, exactly the domain expected by `decodeB`{.Agda}.
<!--zh-->
模式匹配考察的是判定，而不是命题 `P` 本身。`yes`{.Agda} 分支给出 `lift true`{.Agda}，`no`{.Agda} 分支给出 `lift false`{.Agda}。两个分支都会舍去具体的证明或反驳，因为编码只记录哪一种情形成立。结果属于 `Lift {ℓ-zero} {ℓ₂} Bool`{.Agda}，恰好可以作为 `decodeB`{.Agda} 的输入。
<!--ja-->
パターンマッチが調べるのは命題 `P` 自身ではなく、その判定である。`yes`{.Agda} の枝は `lift true`{.Agda} を、`no`{.Agda} の枝は `lift false`{.Agda} を返す。どちらの枝でも具体的な証明や反証は捨てる。符号が記録するのは、どちらが成り立つかだけだからである。結果は `Lift {ℓ-zero} {ℓ₂} Bool`{.Agda} に属し、`decodeB`{.Agda} の入力に正確に一致する。
<!--/-->

```agda
  encodeB : ∀ {ℓ₁ ℓ₂} (P : hProp ℓ₁) → Dec ⟨ P ⟩ → Lift {ℓ-zero} {ℓ₂} Bool
  encodeB P (yes _) = lift true
  encodeB P (no _)  = lift false
```

<!--en-->
The first inverse law says that the representative chosen through a decision has the same truth value as `P`. Concretely, `secB` proves `decodeB (encodeB P d) ≡ P`{.Agda}, a path between `hProp` values. The proof strategy in both cases is the same: give maps in both directions and let propositional extensionality `⇔toPath`{.Agda} assemble the path.
<!--zh-->
第一条逆律说，经由判定选出的代表与 `P` 有相同的真值。具体地，`secB` 证明 `decodeB (encodeB P d) ≡ P`{.Agda}，这是 `hProp` 值之间的一条路径。两种情形的证明策略相同：给出双向的映射，再由命题外延性 `⇔toPath`{.Agda} 组装出路径。
<!--ja-->
最初の逆法則は、判定を通して選ばれた代表が `P` と同じ真理値を持つことを述べる。具体的には `secB` が `decodeB (encodeB P d) ≡ P`{.Agda}、つまり `hProp` 値の間のパスを証明する。どちらの場合も証明の戦略は同じで、両方向の写像を与え、命題外延性 `⇔toPath`{.Agda} にパスを組み立てさせる。
<!--/-->

<!--en-->
If the decision was a proof `p`, the goal is `⊤ ≡ P`{.Agda}. The map from `⊤`{.Agda} to `⟨ P ⟩`{.Agda} is simply `p`, the decided witness; in the reverse direction every input goes to the unique proof of `⊤`{.Agda}. If the decision was a refutation `np`, the goal is `⊥ ≡ P`{.Agda}. Out of `⊥*`{.Agda} there is no constructor to match, which the absurd pattern `λ ()` expresses; in the other direction `np` itself sends each proof of `⟨ P ⟩`{.Agda} to a contradiction. In both branches the chosen representative is path-equal to `P`, so the encoding round trip loses no truth value.
<!--zh-->
若判定是证明 `p`，目标是 `⊤ ≡ P`{.Agda}。从 `⊤`{.Agda} 到 `⟨ P ⟩`{.Agda} 的映射就是判定所得的见证 `p`；反方向上，所有输入都映到 `⊤`{.Agda} 的唯一证明。若判定是反驳 `np`，目标是 `⊥ ≡ P`{.Agda}。从 `⊥*`{.Agda} 出发没有构造子可匹配，荒谬模式 `λ ()` 表达的正是这一点；另一个方向直接由 `np` 把 `⟨ P ⟩`{.Agda} 的每个证明送入矛盾。两个分支中，所选代表都与 `P` 路径相等，于是编码的往返不丢失任何真值。
<!--ja-->
判定が証明 `p` だった場合、ゴールは `⊤ ≡ P`{.Agda} である。`⊤`{.Agda} から `⟨ P ⟩`{.Agda} への写像は判定で得た証拠 `p` そのものであり、逆方向ではすべての入力を `⊤`{.Agda} の唯一の証明へ送る。判定が反証 `np` だった場合、ゴールは `⊥ ≡ P`{.Agda} である。`⊥*`{.Agda} には照合すべき構成子がないことを荒謬パターン `λ ()` が表し、逆方向では `np` 自身が `⟨ P ⟩`{.Agda} の各証明を矛盾へ送る。どちらの分岐でも選ばれた代表は `P` とパスで等しく、符号化の往復が真理値を失わないことがわかる。
<!--/-->

```agda
  secB : ∀ {ℓ₁ ℓ₂} (P : hProp ℓ₁) (d : Dec ⟨ P ⟩)
       → decodeB {ℓ₁} {ℓ₂} (encodeB {ℓ₁} {ℓ₂} P d) ≡ P
  secB {ℓ₁} {ℓ₂} P (yes p) = ⇔toPath (λ _ → p) (λ _ → tt*)
  secB {ℓ₁} {ℓ₂} P (no np) = ⇔toPath (λ ()) (λ p → ⊥₀-rec (np p))
```

<!--en-->
The second inverse law states `encodeB (decodeB b) d ≡ b`{.Agda}: decode a label, then encode the resulting proposition, and recover the original label. In the final classifier, excluded middle will supply `d`, but its computational form is not fixed. Consequently `retrB`{.Agda} must work for **every** decision of the decoded proposition. There are four combinations. The two compatible ones reduce to `refl`{.Agda}; the other two are impossible because `⊤`{.Agda} is inhabited and `⊥`{.Agda} is empty.
<!--zh-->
第二条逆律是 `encodeB (decodeB b) d ≡ b`{.Agda}：先解码标签，再编码所得命题，应当返回原标签。在最终的分类器中，`d` 由排中律给出，但它具体如何计算并不确定。因此，`retrB`{.Agda} 必须对解码所得命题的**每一种**判定都成立。证明共有四种组合：两个相容的分支归约为 `refl`{.Agda}；另两个分支不可能出现，因为 `⊤`{.Agda} 有元素，而 `⊥`{.Agda} 为空。
<!--ja-->
第二の逆法則は `encodeB (decodeB b) d ≡ b`{.Agda}、すなわちラベルを復号して得た命題を再び符号化すると、元のラベルに戻ることを述べる。完成した分類子では排中律が `d` を与えるが、その具体的な計算の形は定まらない。したがって `retrB`{.Agda} は、復号された命題の**どの**判定に対しても成り立つ必要がある。組合せは四つあり、両立する二つの枝は `refl`{.Agda} に簡約される。残りの二つは、`⊤`{.Agda} に要素があり `⊥`{.Agda} が空であるため起こりえない。
<!--/-->

```agda
  retrB : ∀ {ℓ₁ ℓ₂} (b : Lift {ℓ-zero} {ℓ₂} Bool)
          (d : Dec ⟨ decodeB {ℓ₁} {ℓ₂} b ⟩)
        → encodeB {ℓ₁} {ℓ₂} (decodeB {ℓ₁} {ℓ₂} b) d ≡ b
```

<!--en-->
For `b = lift true`{.Agda}, decoding gives `⊤`{.Agda}. Encoding with a proof returns `lift true`{.Agda}, and the goal is definitionally `refl`{.Agda}. The alleged refutation branch cannot occur: applying it to the unique proof of `⊤`{.Agda} would give an element of the empty type, leaving no case to prove.
<!--zh-->
当 `b = lift true`{.Agda} 时，解码得 `⊤`{.Agda}。配以证明编码返回 `lift true`{.Agda}，目标按定义就是 `refl`{.Agda}。所谓反驳的分支不可能出现：把它用于 `⊤`{.Agda} 的唯一证明，就会得到空类型的元素，因此没有需要证明的情形。
<!--ja-->
`b = lift true`{.Agda} のとき、復号は `⊤`{.Agda} を返す。証明とともに符号化すれば `lift true`{.Agda} が返り、ゴールは定義上 `refl`{.Agda} である。反証の分岐は起こりえない。`⊤`{.Agda} の唯一の証明に適用すれば空型の元が得られるため、証明すべき場合は残らない。
<!--/-->

```agda
  retrB {ℓ₁} {ℓ₂} (lift true)  (yes _)  = refl
  retrB {ℓ₁} {ℓ₂} (lift true)  (no n⊤) = ⊥₀-rec (n⊤ tt*)
```

<!--en-->
For `b = lift false`{.Agda}, decoding gives `⊥`{.Agda} with underlying type `⊥*`{.Agda}. An alleged proof of it would be a term of the empty type, so the absurd pattern `()` ends that branch at once; encoding with a refutation returns `lift false`{.Agda}, again by `refl`{.Agda}. Across all four cases, the label returned always equals the label we started from, whichever decision is supplied.
<!--zh-->
当 `b = lift false`{.Agda} 时，解码得 `⊥`{.Agda}，其底层类型为 `⊥*`{.Agda}。它的所谓证明将是空类型的项，荒谬模式 `()` 立即结束该分支；配以反驳编码返回 `lift false`{.Agda}，同样由 `refl`{.Agda} 完成。纵观四种情形，无论供给哪种判定，返回的标签总等于出发时的标签。
<!--ja-->
`b = lift false`{.Agda} のとき、復号は `⊥`{.Agda}、すなわち基礎型 `⊥*`{.Agda} を持つ命題を返す。そのいわゆる証明は空型の項になるはずなので、荒謬パターン `()` がこの分岐を直ちに終わらせ、反証とともに符号化すれば `lift false`{.Agda} が返り、これも `refl`{.Agda} で済む。四つの場合を通して、どの判定が供給されようとも、返されるラベルは出発点のラベルと等しくなる。
<!--/-->

```agda
  retrB {ℓ₁} {ℓ₂} (lift false) (yes ())
  retrB {ℓ₁} {ℓ₂} (lift false) (no _)  = refl
```

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
**Proof** The pieces above assemble the classifier promised by `ΩResizing ℓ₁ ℓ₂`{.Agda}: the code type is `Lift {ℓ-zero} {ℓ₂} Bool`{.Agda} in `Type ℓ₂`{.Agda}, and it is type equivalent to `hProp ℓ₁`{.Agda}. The equivalence comes from an isomorphism whose forward map decides each `P` and encodes it, while its backward map is `decodeB`{.Agda}. The inverse laws are `retrB`{.Agda} and `secB`{.Agda}, instantiated with the decisions supplied by `lem`. This final assembly is the only place where excluded middle is invoked; the encoder and the inverse laws themselves remain constructive.
<!--zh-->
**证明** 把以上各部分组装成 `ΩResizing ℓ₁ ℓ₂`{.Agda} 所要求的分类器。其编码类型是 `Type ℓ₂`{.Agda} 中的 `Lift {ℓ-zero} {ℓ₂} Bool`{.Agda}，并且与 `hProp ℓ₁`{.Agda} 类型等价。这个等价来自一个同构：正向映射先判定每个 `P`，再将其编码；逆向映射则是 `decodeB`{.Agda}。两条逆律分别由 `retrB`{.Agda} 与 `secB`{.Agda} 给出，其中所需的判定均由 `lem` 提供。整个构造只在最后组装时调用排中律；编码器和逆律本身仍是构造主义的。
<!--ja-->
**証明** 以上の部品を `ΩResizing ℓ₁ ℓ₂`{.Agda} が要求する分類子へ組み立てる。符号の型は `Type ℓ₂`{.Agda} に住む `Lift {ℓ-zero} {ℓ₂} Bool`{.Agda} であり、`hProp ℓ₁`{.Agda} と型同値である。この同値は、順写像が各 `P` を判定して符号化し、逆写像が `decodeB`{.Agda} である同型から得られる。二つの逆法則には、`lem` が供給する判定で具体化した `retrB`{.Agda} と `secB`{.Agda} を使う。排中律を呼び出すのはこの最後の組み立てだけであり、符号化器と逆法則そのものは構成的なままである。
<!--/-->

<!--en-->
The pair `(Lift Bool , ...)` witnesses `ΩResizing ℓ₁ ℓ₂`{.Agda}: its first component has type `Type ℓ₂`{.Agda}, and its second is an equivalence `hProp ℓ₁ ≃ Lift Bool`{.Agda}. No ordering between `ℓ₁` and `ℓ₂` is assumed. In the downward instance used later, `ℓ₁ = ℓ-suc ℓ` and `ℓ₂ = ℓ`, so the proposition universe is presented one level down; the theorem itself is more general and also permits equal or higher target levels. The two inverse laws certify both directions of the equivalence, not merely a surjective labelling of propositions by truth values.
<!--zh-->
序对 `(Lift Bool , ...)` 是 `ΩResizing ℓ₁ ℓ₂`{.Agda} 的见证：第一分量类型为 `Type ℓ₂`{.Agda}，第二分量是类型等价 `hProp ℓ₁ ≃ Lift Bool`{.Agda}。这里不假设 `ℓ₁` 与 `ℓ₂` 有任何大小关系。在后文使用的向下实例中，`ℓ₁ = ℓ-suc ℓ` 且 `ℓ₂ = ℓ`，命题宇宙因此被呈现在低一层；但定理本身更一般，也允许目标层级相同或更高。两条逆律认证了等价的两个方向，所以所得结果不只是用真值标签满射地覆盖命题。
<!--ja-->
対 `(Lift Bool , ...)` が `ΩResizing ℓ₁ ℓ₂`{.Agda} の証拠である。第一成分は `Type ℓ₂`{.Agda} の型で、第二成分は型同値 `hProp ℓ₁ ≃ Lift Bool`{.Agda} である。ここでは `ℓ₁` と `ℓ₂` の大小関係を仮定しない。後で使う下向きの実例では `ℓ₁ = ℓ-suc ℓ`、`ℓ₂ = ℓ` なので、命題宇宙は一つ下のレベルで提示される。しかし定理そのものはより一般的で、終域レベルが同じ場合や高い場合も許す。二つの逆法則は同値の両方向を保証しており、単に真理値のラベルで命題を全射的に覆うだけではない。
<!--/-->

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
