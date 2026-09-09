<!--en-->
# The classical boundary

Excluded middle says that every proposition is either true or false. Cubical type theory does not assume it, so chapters that use classical reasoning receive it explicitly. This chapter defines that assumption and derives the two smallness principles needed later: a small classifier for propositions and propositional resizing.
<!--zh-->
# 经典逻辑的边界

排中律说每个命题要么真，要么假。Cubical 类型论并不预设它，因此使用经典推理的章节会显式接收这项假设。本章定义排中律，并由它推出后文所需的两条小性原理：命题的小分类器与命题降层。
<!--ja-->
# 古典論理との境界

排中律は、すべての命題が真または偽であると述べます。Cubical 型理論は排中律を仮定しないため、古典的推論を使う章はこの仮定を明示的に受け取ります。本章では排中律を定義し、後で必要となる命題の小分類子と命題リサイズを導きます。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

module Base.Classical where

open import Base.Prelude
open import Base.Truth
open import Base.Impredicativity
  using ( isSmall; Resizing; HPropSmallness; Impredicativity )
open import Cubical.Data.Sum using ( _⊎_; inl; inr )
import Cubical.Data.Empty as Empty
open import Cubical.Data.Bool using ( Bool; true; false )
open import Cubical.Data.Unit using ( tt* )
open import Cubical.Foundations.Equiv using ( propBiimpl→Equiv )
open import Cubical.Foundations.Isomorphism using ( iso; isoToEquiv )
open import Cubical.Functions.Logic using ( ⇔toPath )
```

<!--en-->
## The statement

`LEM ℓ`{.Agda} decides every proposition in `hProp ℓ`{.Agda}. Its level index records exactly where classical reasoning enters a later theorem.
<!--zh-->
## 陈述

`LEM ℓ`{.Agda} 判定 `hProp ℓ`{.Agda} 中的每个命题。层级指标准确记录经典推理在后续定理中从何处进入。
<!--ja-->
## 排中律の主張

`LEM ℓ`{.Agda} は `hProp ℓ`{.Agda} の各命題を判定します。レベルの添字により、後の定理で古典的推論がどこから入るかが明示されます。
<!--/-->

```agda
LEM : ∀ ℓ → Type (ℓ-suc ℓ)
LEM ℓ = (P : hProp ℓ) → ⟨ P ⟩ ⊎ (⟨ P ⟩ → Empty.⊥)
```

<!--en-->
`LEM ℓ`{.Agda} says: every proposition at level `ℓ` is either true or false. Why
this particular form? In univalent foundations a type-level global choice or
excluded middle is inconsistent with univalence; what can consistently be assumed is
exactly this propositional form, quantified over `hProp`{.Agda}. The foundation
itself forces the honest phrasing.

A chapter that works classically takes `(lem : ∀ {ℓ} → LEM ℓ)`{.Agda} in its module
telescope and passes it along when importing other classical chapters. The
consequence is worth pausing on: **whether a theorem uses excluded middle is a
compile-time fact.** The classical debt is part of a chapter's type, visible at
every import site, instead of an invisible global axiom; and since nothing is
postulated, the whole book carries Agda's `--safe` seal.
<!--zh-->
`LEM ℓ`{.Agda} 说的是：层级 `ℓ` 上的每个命题要么真要么假。为什么取这个形式？在 univalent 基础中，类型层的全局选择或排中律与 univalence 不相容；能够一致地假设的恰是这个对 `hProp`{.Agda} 量化的命题形式。是基础本身逼出了这个诚实的措辞。

经典论证的章节在模块参数表中取 `(lem : ∀ {ℓ} → LEM ℓ)`{.Agda}，并在导入其他经典章节时把它传递下去。这带来一个值得停下体会的后果：**一条定理是否用了排中律，是编译期事实。**经典债务是章节类型的一部分，在每个导入处可见，而不是一条看不见的全局公理；又因为无一处 postulate，全书佩戴 Agda 的 `--safe` 印章。
<!--/-->

<!--en-->
One transfer lemma before the dividends. Excluded middle passes **downward**
through the levels: to decide a small proposition, lift its underlying type one
universe up, decide there, and lower the verdict. So a single instance of
`LEM`{.Agda} at a higher level silently covers every level below it, a fact the
end of this chapter spends.
<!--zh-->
红利之前先备一条传递引理。排中律沿层级**向下**通行：要判定一个小命题，把其底层类型抬高一层宇宙，在那里判定，再把裁决降回来。于是较高层级上的单个 `LEM`{.Agda} 实例默默覆盖其下每一层，本章结尾就要花掉这个事实。
<!--/-->

```agda
lowerLEM : ∀ {ℓ} → LEM (ℓ-suc ℓ) → LEM ℓ
lowerLEM {ℓ} lem P = fromLifted (lem lifted)
  where
  lifted : hProp (ℓ-suc ℓ)
  lifted = Lift ⟨ P ⟩ , λ x y → cong lift (P .snd (lower x) (lower y))
  fromLifted : ⟨ lifted ⟩ ⊎ (⟨ lifted ⟩ → Empty.⊥) → ⟨ P ⟩ ⊎ (⟨ P ⟩ → Empty.⊥)
  fromLifted (inl p)  = inl (lower p)
  fromLifted (inr np) = inr (λ p → np (lift p))
```

<!--en-->
## The first dividend: a small classifier

A classical proposition has one of two truth values. This section turns that observation into an equivalence between `hProp ℓ`{.Agda} and the small type `Lift Bool`{.Agda}.
<!--zh-->
## 第一笔红利：小分类器

经典命题只有两个真值。本节把这一观察化为 `hProp ℓ`{.Agda} 与小类型 `Lift Bool`{.Agda} 之间的等价。
<!--ja-->
## 第一の帰結：小分類子

古典的な命題の真理値は二つです。この節では、その事実を `hProp ℓ`{.Agda} と小さな型 `Lift Bool`{.Agda} の同値として表します。
<!--/-->

<!--en-->
Classically a proposition has only two possible values, and this has direct
consequences at the universe level. First the classifier: `HPropSmallness ℓ`{.Agda}, defined
in the previous chapter, asks for a small type equivalent to `hProp ℓ`{.Agda}.
Classically it is `Lift Bool`{.Agda}, at **every** level `ℓ`. In the four
helpers below, the **decision** of a proposition (a proof, or a refutation) is taken
as an ordinary argument, so the constructions involved use no classical
principles. excluded middle is used only at the final assembly, to supply those
decisions.
<!--zh-->
经典地看，命题只有两个可能的值，这在宇宙层级上有直接后果。先看分类器：上一章定义的 `HPropSmallness ℓ`{.Agda} 要求一个与 `hProp ℓ`{.Agda} 等价的小类型；经典情况下，在**每一个**层级 `ℓ` 上都可取 `Lift Bool`{.Agda}。下面四个辅助定义把命题的**判定** (一个证明或一个反驳) 作为普通参数，因此其中的实际构造都不使用经典原理。排中律只在最后组合这些定义时用于提供判定。
<!--/-->

<!--en-->
The chapter first makes good on the scope discipline described above: it opens
the canonical instance, taking exactly its `⊤`{.Agda} and `⊥`{.Agda}. From here on the
two symbols denote the truth values of the hProp algebra, and by definitional
transparency this `⊥`{.Agda} is the pair `(⊥* , isProp⊥*)`{.Agda} itself. Next the decoding
direction, from Booleans to propositions, is defined: `decodeB`{.Agda} sends `true`{.Agda} to
`⊤`{.Agda} and `false`{.Agda} to `⊥`{.Agda}. The domain is
`Lift {ℓ-zero} {ℓ} Bool`{.Agda} rather than `Bool`{.Agda}, since `Bool`{.Agda}
lives in the bottom universe while propositions live in universe `ℓ`; the lifted copy
puts the two ends of the coming equivalence in the same universe.
<!--zh-->
本章先落实前文的作用域规则：打开典范实例，只取其中的 `⊤`{.Agda} 与 `⊥`{.Agda}。从此这两个符号表示 hProp 代数的真值；由定义性透明，这个 `⊥`{.Agda} 就是 `(⊥* , isProp⊥*)`{.Agda} 这个对本身。接着定义从布尔值到命题的解码：`decodeB`{.Agda} 把 `true`{.Agda} 映到 `⊤`{.Agda}，把 `false`{.Agda} 映到 `⊥`{.Agda}。定义域使用 `Lift {ℓ-zero} {ℓ} Bool`{.Agda} 而非 `Bool`{.Agda}，因为 `Bool`{.Agda} 属于最底层宇宙，而命题属于 `ℓ` 层宇宙；提升后的副本使等价两端属于同一宇宙。
<!--/-->

```agda
open module Canonical {ℓ : Level} = TruthAlgebra (hPropAlgebra ℓ) using ( ⊤; ⊥ )

private
  decodeB : ∀ {ℓ} → Lift {ℓ-zero} {ℓ} Bool → hProp ℓ
  decodeB (lift true)  = ⊤
  decodeB (lift false) = ⊥
```

<!--en-->
The encoding direction has a hidden asymmetry. Its would-be signature is
`hProp ℓ → Lift Bool`{.Agda}, the exact inverse of `decodeB`{.Agda}, but no such
function can be defined: unlike `lift true`{.Agda} and `lift false`{.Agda}, an
arbitrary proposition `P` is not something one can pattern-match on, so there is no case
split "if `P` holds, otherwise" to write. `encodeB`{.Agda} therefore takes one
extra argument, a decision `d` of `P`, and matches on **that**: a proof gives
`true`{.Agda}, a refutation gives `false`{.Agda}. The shape mirrors
`decodeB`{.Agda}, but the thing being inspected is the decision supplied as input, not
the proposition itself. No excluded middle is used here; the decision is an input.
<!--zh-->
编码方向藏着一处不对称。它「本该」有签名 `hProp ℓ → Lift Bool`{.Agda}，即 `decodeB`{.Agda} 的严格逆向，但这样的函数定义不出来：与 `lift true`{.Agda}、`lift false`{.Agda} 不同，任意命题 `P` 不是可以对其做模式匹配的对象，写不出「若 `P` 成立、否则如何」的分支。因此 `encodeB`{.Agda} 多收一个参数，即 `P` 的判定 `d`，改为对**它**做匹配：有证明就取 `true`{.Agda}，有反驳就取 `false`{.Agda}。形状与 `decodeB`{.Agda} 相仿，但被检视的对象是作为输入给出的判定，而不是命题本身。这里没有用到排中律；判定是输入。
<!--/-->

```agda
  encodeB : ∀ {ℓ} (P : hProp ℓ) → ⟨ P ⟩ ⊎ (⟨ P ⟩ → Empty.⊥) → Lift {ℓ-zero} {ℓ} Bool
  encodeB P (inl _) = lift true
  encodeB P (inr _) = lift false
```

<!--en-->
The first round trip encodes `P` and then decodes, obtaining `P` itself. The tool is
`⇔toPath`{.Agda}, the library's propositional extensionality: between propositions,
maps in both directions already make a path (in this book that principle is a
theorem, not an axiom). If the decision is a proof `p`, the goal is
`⊤ ≡ P`{.Agda}: the map from `⊤`{.Agda} to `P` is the answer `p`,
and in the other direction every input maps to
`tt*`{.Agda}, the inhabitant of `⊤`{.Agda}. If the decision is a refutation `np`, the
goal is `⊥ ≡ P`{.Agda}: out of `⊥*`{.Agda} there is no constructor to match,
which is what the absurd pattern `λ ()` expresses, and any proof `p` of `P` is
refuted by `np`, with `Empty.rec`{.Agda} eliminating the resulting absurdity.
<!--zh-->
第一趟往返把 `P` 编码后再解码，并得到 `P` 本身。这里使用库的命题外延性 `⇔toPath`{.Agda}：命题之间的双向映射给出一条路径 (在本书中，这是定理而非公理)。若判定给出证明 `p`，目标是 `⊤ ≡ P`{.Agda}：从 `⊤`{.Agda} 到 `P` 的映射取 `p`，反向映射把所有输入映到 `⊤`{.Agda} 的元素 `tt*`{.Agda}。若判定给出反驳 `np`，目标是 `⊥ ≡ P`{.Agda}：从 `⊥*`{.Agda} 出发没有构造子可匹配，荒谬模式 `λ ()` 表示的正是这一点；任意 `P` 的证明 `p` 都与 `np` 矛盾，`Empty.rec`{.Agda} 随即消去相应的空类型。
<!--/-->

```agda
  secB : ∀ {ℓ} (P : hProp ℓ) (d : ⟨ P ⟩ ⊎ (⟨ P ⟩ → Empty.⊥))
       → decodeB (encodeB P d) ≡ P
  secB P (inl p)  = ⇔toPath (λ _ → p) (λ _ → tt*)
  secB P (inr np) = ⇔toPath (λ ()) (λ p → Empty.rec (np p))
```

<!--en-->
The other round trip encodes the decoding of a Boolean `b` and gives back `b`. One
subtlety deserves attention: when the classifier is assembled, it is excluded middle that
decides `decodeB b`{.Agda}, but which decision it supplies cannot be determined in
advance. So `retrB`{.Agda} proves the equation for **every** decision `d`, by
four cases. `true`{.Agda} with a proof: `refl`{.Agda}. `true`{.Agda} with an alleged
refutation `n⊤`: impossible, since `⊤`{.Agda} does hold, and `n⊤ tt*`{.Agda} is a
contradiction. `false`{.Agda} with an alleged proof: that proof is a term of `⊥*`{.Agda}, and
the absurd pattern `()` terminates the branch immediately. `false`{.Agda} with a
refutation: `refl`{.Agda}.
<!--zh-->
另一趟往返把布尔值 `b` 解码后再编码，并得到 `b`。组合分类器时，排中律判定 `decodeB b`{.Agda}，但无法预先确定它给出哪一种判定。因此，`retrB`{.Agda} 对**每一个**判定 `d` 证明该等式，共分四种情形。`true`{.Agda} 配证明时结果是 `refl`{.Agda}；配反驳 `n⊤` 时，由 `n⊤ tt*`{.Agda} 得到矛盾。`false`{.Agda} 配证明时，该证明是 `⊥*`{.Agda} 的项，荒谬模式 `()` 立即结束该分支；配反驳时结果是 `refl`{.Agda}。
<!--/-->

```agda
  retrB : ∀ {ℓ} (b : Lift {ℓ-zero} {ℓ} Bool)
          (d : ⟨ decodeB b ⟩ ⊎ (⟨ decodeB b ⟩ → Empty.⊥))
        → encodeB (decodeB b) d ≡ b
  retrB (lift true)  (inl _)  = refl
  retrB (lift true)  (inr n⊤) = Empty.rec (n⊤ tt*)
  retrB (lift false) (inl ())
  retrB (lift false) (inr _)  = refl
```

<!--en-->
The assembly. `iso`{.Agda} packages the four components (decode; decide, then encode; the
two round trips), and `isoToEquiv`{.Agda} turns the isomorphism into an
equivalence. Count the occurrences of `lem`: three, and all three serve the same
purpose, supplying the decisions that the constructive helpers require as inputs.
This is the entire use of excluded middle in this section.
<!--zh-->
总装。`iso`{.Agda} 把四件套打包 (解码；先判定、再编码；两趟往返)，`isoToEquiv`{.Agda} 把同构升级为等价。数一数 `lem` 被使用的次数：三次，且三次用途相同，即按构造性辅助函数的要求，为它们提供所需的判定。这就是排中律在这笔红利中的全部作用。
<!--/-->

```agda
lem→hPropSmallness : ∀ {ℓ} → LEM ℓ → HPropSmallness ℓ
lem→hPropSmallness lem = Lift Bool , isoToEquiv (iso decodeB
  (λ P → encodeB P (lem P))
  (λ P → secB P (lem P))
  (λ b → retrB b (lem (decodeB b))))
```

<!--en-->
## The second dividend: propositional resizing

Resizing replaces a proposition one universe higher by an equivalent small proposition. A decision reduces the proof to the two small propositions `⊤` and `⊥`.
<!--zh-->
## 第二笔红利：命题降层

命题降层把高一层宇宙中的命题换成等价的小命题。判定把证明归结为两个小命题 `⊤` 与 `⊥`。
<!--ja-->
## 第二の帰結：命題リサイズ

命題リサイズは、一段上の宇宙にある命題を同値な小さい命題に置き換えます。判定により、証明は小さい命題 `⊤` と `⊥` の二場合に帰着します。
<!--/-->

<!--en-->
Second, `Resizing`{.Agda}: every proposition one universe up is small.
Classically, decide the proposition: if it holds it is equivalent to `⊤`, if it
fails to `⊥`, and both are small.
<!--zh-->
第二笔，`Resizing`{.Agda}：高一层的每个命题都是小的。经典地做：判定该命题，若成立则等价于 `⊤`，若不成立则等价于 `⊥`，而两者都是小的。
<!--/-->

<!--en-->
As before, the construction starts from the given decision, using `P .snd`{.Agda} directly;
the propositionality proof mentioned in the Prelude. If `P` holds, take the
`⊤`{.Agda} of level `ℓ`: between propositions, maps in both directions
already form an **equivalence of underlying types**, and `propBiimpl→Equiv`{.Agda}
produces exactly this equivalence from the two propositionality proofs and the two
maps; the map from `P` to `⊤`{.Agda} sends every input to `tt*`{.Agda}, and in the
other direction it uses the given `p`. If `P` fails, take `⊥`{.Agda}, with the same
two absurdity maps as in `secB`{.Agda}. The first result was a path between
propositions (`⇔toPath`{.Agda}); here the result is an equivalence between their
underlying types, so the same pair of maps is passed to
`propBiimpl→Equiv`{.Agda} instead.
<!--zh-->
与之前一样，构造从给定的判定开始，其中直接使用 `P .snd`{.Agda}，即序章提到的命题性证明。若 `P` 成立，就取 `ℓ` 层的 `⊤`{.Agda}：命题之间的双向映射足以构成**底层类型的等价**，`propBiimpl→Equiv`{.Agda} 正是由两侧的命题性证明和这两个映射给出该等价；从 `P` 到 `⊤`{.Agda} 的映射把所有输入映到 `tt*`{.Agda}，反向映射取已有的 `p`。若 `P` 不成立，就取 `⊥`{.Agda}，两个方向的映射与 `secB`{.Agda} 中相同。第一笔结果是命题之间的路径 (`⇔toPath`{.Agda})，这里的结果则是底层类型之间的等价，因此同一对映射被传给 `propBiimpl→Equiv`{.Agda}。
<!--/-->

```agda
private
  resizeDec : ∀ {ℓ} (P : hProp (ℓ-suc ℓ)) → ⟨ P ⟩ ⊎ (⟨ P ⟩ → Empty.⊥)
            → isSmall P
  resizeDec P (inl p)  = ⊤ , propBiimpl→Equiv (P .snd) (⊤ .snd) (λ _ → tt*) (λ _ → p)
  resizeDec P (inr np) = ⊥ , propBiimpl→Equiv (P .snd) (⊥ .snd)
                               (λ p → Empty.rec (np p)) (λ ())
```

<!--en-->
The final assembly is one line: decide `P` using excluded middle, and pass the
decision along. The signature shows that a single instance of excluded middle
at the higher level `ℓ-suc ℓ` is needed here, and no other classical assumption.
<!--zh-->
最后的组合只有一行：用排中律判定 `P`，再把判定传入。签名表明这里需要较高层级 `ℓ-suc ℓ` 上的一次排中律实例，除此之外不需要经典假设。
<!--/-->

```agda
lem→resizing : ∀ {ℓ} → LEM (ℓ-suc ℓ) → Resizing ℓ
lem→resizing lem P = resizeDec P (lem P)
```

<!--en-->
## Redeeming the packing

The two consequences fill the fields of `Impredicativity ℓ`{.Agda}. The higher-level excluded middle supplies resizing directly and reaches the classifier through `lowerLEM`{.Agda}.
<!--zh-->
## 赎回打包

这两个结论填入 `Impredicativity ℓ`{.Agda} 的字段。高层排中律直接给出命题降层，并经 `lowerLEM`{.Agda} 给出小分类器。
<!--ja-->
## 二つの帰結をまとめる

二つの帰結を `Impredicativity ℓ`{.Agda} のフィールドにまとめます。高いレベルの排中律から命題リサイズを直接得て、`lowerLEM`{.Agda} を通して小分類子も得ます。
<!--/-->

<!--en-->
The previous chapter packages the two principles as `Impredicativity`{.Agda} because later chapters always need them together; this does not mean that either principle implies the other. A **single instance** of excluded middle at the higher level proves both: propositional resizing uses that instance directly, while `lowerLEM`{.Agda} derives the lower-level instance required by the classifier. The cumulative-hierarchy chapters use this account to state precisely which assumptions their model fields require.
<!--zh-->
上一章把两项原理合为接口 `Impredicativity`{.Agda}，因为后文总是同时需要它们；这不表示二者相互蕴含，任何一项都不能推出另一项。排中律可以同时证明二者，而且只需较高层级上的**单个实例**：命题降层直接使用该实例，`lowerLEM`{.Agda} 从中得到分类器所需的低层实例。累积层级诸章将据此准确列出模型字段需要的假设。
<!--/-->

```agda
lem→impredicativity : ∀ {ℓ} → LEM (ℓ-suc ℓ) → Impredicativity ℓ
lem→impredicativity lem = record
  { resizing       = lem→resizing lem
  ; hPropSmallness = lem→hPropSmallness (lowerLEM lem) }
```

<!--en-->
## Recap

Excluded middle is now an explicit, level-indexed assumption. It descends to lower levels and yields both components of the impredicativity interface used by the model chapters.
<!--zh-->
## 小结

排中律现在是显式且带层级指标的假设。它能下降到较低层级，并给出模型章节所用非直谓性接口的两个组成部分。
<!--ja-->
## まとめ

排中律は、レベルを添えた明示的な仮定になりました。より低いレベルへ移すことができ、モデルの章で使う非可述性インターフェースの二つの要素を与えます。
<!--/-->

<!--en-->
Excluded middle is stated as the interface `LEM`{.Agda}, taken by chapters that need it
as an explicit parameter and never assumed globally; the boundary between
constructive and classical mathematics can therefore be checked at compile time.
Excluded middle yields the previous chapter's two interfaces: the
small classifier by `lem→hPropSmallness`{.Agda} and propositional resizing
by `lem→resizing`{.Agda}, and `lem→impredicativity`{.Agda} combines the two into
`Impredicativity`{.Agda}. The cumulative-hierarchy chapters will use this interface to
satisfy the smallness assumptions behind full separation and the
power set of the cumulative hierarchy `V`.
<!--zh-->
排中律以接口 `LEM`{.Agda} 的形式陈述，需要它的章节将其作为显式参数，而不作全局假设；构造数学与经典数学的边界因此可在编译时检查。排中律给出上一章的两个接口：`lem→hPropSmallness`{.Agda} 构造小分类器，`lem→resizing`{.Agda} 构造命题降层，`lem→impredicativity`{.Agda} 将二者合为 `Impredicativity`{.Agda}。累积层级诸章将使用该接口，满足累积层级 `V` 的全分离和幂集所需的小性假设。
<!--/-->
