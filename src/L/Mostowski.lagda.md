<!--en-->
# Collapsing a transitive well-founded relation

How much set-theoretic structure does a relation carry on its own? Fix a small type `A` with a well-founded, transitive relation `_≺_` valued in `Type ℓ`. Mostowski's answer: the relation alone determines a function `col : A → SV.S` by recursion, with

`col p = { col r | r ≺ p }`,

so each point is sent to the set of collapse values of its predecessors. A computation rule characterizes membership in each value, and transitivity of the relation makes every collapse value an ordinal in the sense used here, a transitive set all of whose members are transitive.

A finite example shows the mechanism. Take three points `s`, `r`, `p` with `s ≺ r`, `r ≺ p`, and, by transitivity, `s ≺ p`, and with no other relations. Then `col s` has no members forced by the recursion, `col r = { col s }`, and `col p = { col s, col r }`, and this is exactly the von Neumann picture of `0`, `1`, `2`. The recursion never inspects the points themselves, only their cones of predecessors.

Three features of the setting shape everything that follows. First, `A` and each fiber `x ≺ y` live in `Type ℓ`, so for each `p` the predecessor cone is the small type `Σ[ r ∈ A ] (r ≺ p)`; the `sett`{.Agda} constructor of the hierarchy `V`{.Agda} turns precisely such a small family into a set of `SV.S`. Second, membership in a `sett`-set is by construction a propositional truncation: `⟨ b ∈ˢ a ⟩` says that some index of the family merely hits `b`, not that a chosen index is available. The chapter therefore proves membership in one direction from given data (`r ≺ p` yields `col r ∈ˢ col p`) and, in the other direction, only a merely existing predecessor with an equation of collapse values. Third, the targets of the later eliminations are propositions, such as an equality of sets or `isTransV x`, so eliminating the truncation into them is legitimate. No extensionality hypothesis on `_≺_` appears, so two points with identical predecessor cones are not distinguished: the collapse is canonical, but not claimed to be injective. The construction uses only well-founded recursion and transport; no classical principle is assumed anywhere in this module.
<!--zh-->
# 传递良基关系的塌缩

一个关系自身能携带多少集合论结构？取带良基传递关系 `_≺_` 的小类型 `A`，该关系取值于 `Type ℓ`。Mostowski 的回答是：仅凭这个关系，就能用递归确定一个函数 `col : A → SV.S`，满足

`col p = { col r | r ≺ p }`，

即每个点被送到其前驱的塌缩值所成的集合。一条计算律刻画每个值中的隶属关系，而关系的传递性使每个塌缩值成为这里所说的序数，即自身传递且每个成员也传递。

一个有限的例子可以展示机制。取三点 `s`、`r`、`p`，有 `s ≺ r`、`r ≺ p`，以及传递性所要求的 `s ≺ p`，且无其他关系。递归没有强制 `col s` 的任何成员，`col r = { col s }`，`col p = { col s, col r }`，这正是 von Neumann 的 `0`、`1`、`2` 图景。递归从不检视点本身，只检视它们的前驱锥。

设定的三个特征决定其后的一切。其一，`A` 与每个纤维 `x ≺ y` 都在 `Type ℓ` 中，故对每个 `p`，前驱锥是小类型 `Σ[ r ∈ A ] (r ≺ p)`；层级 `V`{.Agda} 的 `sett`{.Agda} 构造子恰好把这样的小族变成 `SV.S` 中的集合。其二，`sett` 集合中的隶属按构造就是命题截断：`⟨ b ∈ˢ a ⟩` 说的是纯粹存在该族的某个索引，使族在该处的值等于 `b`，而非选定的索引可得。因此本章在一个方向上从给出的数据证明隶属 (`r ≺ p` 给出 `col r ∈ˢ col p`)，在另一方向上只得到纯粹存在的前驱加一条塌缩值等式。其三，之后消去的目标都是命题，如集合间的等式或 `isTransV x`，故向它们消去截断是合法的。这里没有对 `_≺_` 的外延性假设，前驱锥相同的两点不被区分：塌缩是典范的，但并不声称单射。整个构造只用良基递归与传输；这里没有假设任何经典原理。
<!--ja-->
# 推移的な整礎関係の崩壊

関係だけでどれほどの集合論的構造が得られるのか。`Type ℓ` 値の推移的な整礎関係 `_≺_` を持つ小さな型 `A` を固定します。Mostowski の答えは、関係だけから再帰によって関数 `col : A → SV.S` が定まり、

`col p = { col r | r ≺ p }`

つまり各点がその前者の崩壊値からなる集合へ写される、というものです。計算法則が各値への所属を特徴付け、関係の推移性によって各崩壊値はここでいう順序数、すなわち自身が推移的で各要素も推移的な集合になります。

有限の例で仕組みを見ます。三点 `s`、`r`、`p` が `s ≺ r`、`r ≺ p`、および推移性から従う `s ≺ p` だけを関係として持つとすると、再帰は `col s` の要素を何も強制せず、`col r = { col s }`、`col p = { col s, col r }` となります。これはまさに von Neumann の `0`、`1`、`2` の図です。再帰は点そのものを見ず、前者の錐だけを見ます。

設定の三つの特徴がその後のすべてを形作ります。第一に、`A` と各繊維 `x ≺ y` は `Type ℓ` にあるので、各 `p` の前者の錐は小さな型 `Σ[ r ∈ A ] (r ≺ p)` です。階層 `V`{.Agda} の `sett`{.Agda} 構成子はまさにこのような小さな族を `SV.S` の集合に変えます。第二に、`sett` 集合への所属は構成上命題的切り詰めです。`⟨ b ∈ˢ a ⟩` はあるインデックスで族の値が `b` に等しいことが単に存在すると述べるのであって、選ばれたインデックスが得られるとは言いません。したがって本章では、一方向には与えられたデータから所属を証明し (`r ≺ p` が `col r ∈ˢ col p` を与える)、他方向には崩壊値の等式を伴う、単に存在する前者しか得られません。第三に、後の消去の目標は集合の等式や `isTransV x` といった命題なので、そこへの切り詰めの消去は正当です。`_≺_` に対する外延性の仮定は現れず、同じ前者の錐を持つ二点は区別されません。崩壊は正準ですが、単射であるとは主張しません。構成は整礎再帰と輸送だけを用い、ここでは古典的な原理を何も仮定しません。
<!--/-->

<!--en-->
The collapse lands in the set-level carrier of the cumulative hierarchy, so its output is made of genuine sets rather than of points of `A`. That carrier, written `SV.S` below, is a type whose equality types are propositions, and its membership `_∈ˢ_` packages each membership statement as an `hProp`: an underlying type `⟨ b ∈ˢ a ⟩` together with a proof that this type is a proposition. Working against this fixed vocabulary, the chapter's theorems can state membership and transitivity with the hierarchy's own relation rather than with a new one.
<!--zh-->
塌缩落在累积层级的集合层载体中，因此其输出由真正的集合构成，而非 `A` 的点。该载体在下文记作 `SV.S`；它是 h-集，也就是任意两元素之间的相等类型都是命题。其成员关系 `_∈ˢ_` 把每条隶属陈述打包成一个 `hProp`：底层类型 `⟨ b ∈ˢ a ⟩` 连同该类型为命题的证明。因此，隶属与传递性都可以直接用层级自身的关系陈述。
<!--ja-->
崩壊は累積階層の集合レベルの台に着地します。したがって出力は `A` の点ではなく集合です。この台を以下では `SV.S` と書きます。これは h-集合、すなわち任意の二要素の間の等式型が命題となる型です。所属関係 `_∈ˢ_` は各所属の主張を `hProp`、つまり根底の型 `⟨ b ∈ˢ a ⟩` とその型が命題である証明の対として与えます。したがって所属と推移性は階層本来の関係で直接述べられます。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth

module L.Mostowski {ℓ : Level} where

open import FOL.ZFStructure using ( module hPropStructure )
```

<!--en-->
Two ingredients drive the construction. The first is the image operation `sett`{.Agda} of the hierarchy: from a small index type `X` and a family `X → V ℓ` it forms the set of that family's values, with membership holding merely when some index hits the target. The second is the well-foundedness certificate `WellFounded _≺_`, the assertion that every element of `A` is accessible along `≺`; its induction principle builds recursively defined functions, and its companion computation law records what such a function does at each point. Propositional truncation enters through `∥ _ ∥₁` with introduction `∣ _ ∣₁`, because membership in an image is truncated by design. The ordinal target `IsOrd`, transitivity `isTransV`, and its propositionhood proof `isPropIsTransV` come from the development of `L` and appear only at the end, where the final theorem needs them.
<!--zh-->
构造由两个要素驱动。其一是层级的像运算 `sett`{.Agda}：从小索引类型 `X` 和族 `X → V ℓ` 造出该族取值的集合，隶属仅在某个索引命中目标时纯粹地成立。其二是良基性证书 `WellFounded _≺_`，即 `A` 的每个元素沿 `≺` 可及；其归纳原理构造递归定义的函数，配套的计算律记录该函数在每点的行为。命题截断经由 `∥ _ ∥₁` 与其引入 `∣ _ ∣₁` 进入，因为像中的隶属按设计就是截断的。序数目标 `IsOrd`、传递性 `isTransV` 及其命题性证明 `isPropIsTransV` 来自 `L` 的构造，只在最后定理需要它们时出现。
<!--ja-->
構成を駆動する要素は二つです。第一は階層の像演算 `sett`{.Agda} で、小さなインデックス型 `X` と族 `X → V ℓ` からその族の値の集合を形作り、所属はあるインデックスが目標に命中するときに単に成り立ちます。第二は整礎性の証明 `WellFounded _≺_`、すなわち `A` のすべての要素が `≺` に沿って到達可能であるという主張で、その帰納原理が再帰的に定義された関数を構成し、付随する計算法則が各点での振る舞いを記録します。命題的切り詰めは `∥ _ ∥₁` とその導入 `∣ _ ∣₁` を通して現れます。像への所属は設計上切り詰められているからです。順序数の目標 `IsOrd`、推移性 `isTransV`、そしてその命題性の証明 `isPropIsTransV` は `L` の構成から来ており、最後の定理がそれらを必要とするときにだけ現れます。
<!--/-->

```agda
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ} using ( IsOrd; isTransV; isPropIsTransV )

open import Cubical.HITs.CumulativeHierarchy.Base using ( sett )
open import Cubical.Induction.WellFounded using ( WellFounded; module WFI )
import Cubical.HITs.PropositionalTruncation as PT
```

<!--en-->
The hierarchy structure uses the hProp truth-value algebra at level `ℓ-suc ℓ`. Independently, `A` and every fiber `x ≺ y` lie in `Type ℓ`, so each predecessor cone is a small index type to which `sett`{.Agda} applies. These size facts are all the construction needs; no excluded-middle hypothesis occurs.
<!--zh-->
层级结构使用层级 `ℓ-suc ℓ` 的 hProp 真值代数。另一方面，`A` 与每个纤维 `x ≺ y` 都在 `Type ℓ` 中，所以每个前驱锥都是可供 `sett`{.Agda} 使用的小索引类型。构造只需要这些大小事实，不需要排中律。
<!--ja-->
階層構造はレベル `ℓ-suc ℓ` の hProp 真理値代数を使います。一方、`A` と各繊維 `x ≺ y` は `Type ℓ` にあるので、各前者の錐は `sett`{.Agda} を適用できる小さな添字型です。構成に必要な大きさの事実はこれだけで、排中律は仮定しません。
<!--/-->

```agda
open PT using ( ∣_∣₁; ∥_∥₁ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
module SV = hPropStructure 𝒮ᵥ
open SV using ( _∈ˢ_ )
```

<!--en-->
The construction now has two tasks. First, derive the two membership laws for the collapse: a given predecessor produces a member, while a member reflects to a merely existing predecessor with the same collapse value. Second, use those laws in well-founded induction to prove `IsOrd (col p)` for every `p`. The asymmetry between explicit input and truncated output is essential in both tasks.
<!--zh-->
下面完成两个任务。首先证明塌缩的两条隶属律：给定一个前驱即可构造相应成员，而从一个成员反推时，只能得到纯粹存在的前驱及其塌缩值等式。随后在良基归纳中使用这两条定律，证明每个 `p` 都满足 `IsOrd (col p)`。显式输入与截断输出之间的不对称在两步中都不可省略。
<!--ja-->
以下では二つの課題を果たします。まず崩壊の二つの所属法則を示します。与えられた前者から要素を構成できる一方、要素から逆に得られるのは、崩壊値の等式を伴って単に存在する前者だけです。次にこの二法則を整礎帰納法で用い、各 `p` について `IsOrd (col p)` を証明します。明示的な入力と切り詰められた出力の非対称性は両方の課題で本質的です。
<!--/-->

<!--en-->
Well-foundedness is what licenses the recursion. The induction principle obtained from `wf` says that, to define a family `P` on `A`, it suffices at each `p` to construct `P p` from values of `P` at every predecessor `r ≺ p`. The transitivity witness `≺-trans` is not needed to define `col`; it enters later when proving that the resulting sets are transitive.
<!--zh-->
良基性为递归提供依据。由 `wf` 得到的归纳原理说：要在 `A` 上定义一族 `P`，只需对每个 `p`，从所有前驱 `r ≺ p` 处 `P` 的值构造 `P p`。传递性见证 `≺-trans` 不参与 `col` 的定义；它在随后证明所得集合传递时才使用。
<!--ja-->
再帰を可能にするのは整礎性です。`wf` から得られる帰納原理によれば、`A` 上の族 `P` を定義するには、各 `p` で全ての前者 `r ≺ p` における `P` の値から `P p` を構成すれば十分です。推移性の証拠 `≺-trans` は `col` の定義には使われず、得られた集合の推移性を後で証明するときに使われます。
<!--/-->

```agda
module Mostowski (A : Type ℓ) (_≺_ : A → A → Type ℓ)
                 (wf : WellFounded _≺_)
                 (≺-trans : {x y z : A} → x ≺ y → y ≺ z → x ≺ z) where

  module W = WFI wf using ( induction; induction-compute )

  colStep : (p : A) → (∀ r → r ≺ p → SV.S) → SV.S
```

<!--en-->
The recursion step is the image of the predecessor cone. Given `p` and a recursive call `rec` that already knows `col r` for each `r ≺ p`, the step forms `sett (Σ[ r ∈ A ] (r ≺ p)) (λ z → rec (fst z) (snd z))`: the index type is the total space of pairs `(r , r ≺ p)`, and the family sends such a pair to `rec r`. Abstractly this is exactly the set `{ col r | r ≺ p }`, the collapsing equation the chapter announced. Note how the step type quantifies over arbitrary step functions `rec`, which is what makes the same data serve both the definition and, via the computation law below, reasoning about it.
<!--zh-->
递归步就是前驱锥的像。给定 `p` 和已经知道每个 `r ≺ p` 的 `col r` 的递归调用 `rec`，该步造出 `sett (Σ[ r ∈ A ] (r ≺ p)) (λ z → rec (fst z) (snd z))`：索引类型是偶对 `(r , r ≺ p)` 的全空间，族把这样的偶对送到 `rec r`。抽象地说，这正是本章宣告的塌缩方程 `{ col r | r ≺ p }`。注意步型对任意的步函数 `rec` 做了量化，这使同一份数据既用于定义，也经由下面的计算律用于推理。
<!--ja-->
再帰の一段は前者の錐の像です。`p` と、各 `r ≺ p` に対してすでに `col r` を知る再帰呼び出し `rec` が与えられれば、この段は `sett (Σ[ r ∈ A ] (r ≺ p)) (λ z → rec (fst z) (snd z))` を形作ります。インデックス型は対 `(r , r ≺ p)` の全空間であり、族はその対を `rec r` へ送ります。抽象的には、これがまさに章の冒頭で宣言した崩壊方程式 `{ col r | r ≺ p }` です。段の型が任意の段関数 `rec` を量化している点に注目してください。おかげで同じデータが定義と、後述の計算法則を通した推論の両方に使えます。
<!--/-->

```agda
  colStep p rec = sett (Σ[ r ∈ A ] (r ≺ p)) (λ z → rec (fst z) (snd z))

  opaque
    col : A → SV.S
    col = W.induction {P = λ _ → SV.S} colStep

    col-eq : (p : A) → col p ≡ sett (Σ[ r ∈ A ] (r ≺ p)) (λ z → col (fst z))
```

<!--en-->
The function `col` is defined by well-founded induction. Its computation rule `col-eq` identifies `col p` with the image of the predecessor cone under `col` itself. Later membership proofs use this equality to pass between the recursively defined value and the explicit image, where membership has the truncated-preimage classification supplied by `sett`{.Agda}.
<!--zh-->
函数 `col` 由良基归纳定义。其计算律 `col-eq` 把 `col p` 等同于前驱锥在 `col` 下的像。随后的隶属证明用这条等式在递归定义的值与显式像之间转换，而在显式像中，隶属具有 `sett`{.Agda} 给出的截断原像分类。
<!--ja-->
関数 `col` は整礎帰納法で定義されます。その計算規則 `col-eq` は `col p` を前者の錐の `col` による像と同一視します。後の所属証明ではこの等式を使い、再帰的に定義された値と明示的な像の間を移ります。明示的な像への所属には `sett`{.Agda} が与える切り詰められた逆像の分類があります。
<!--/-->

```agda
    col-eq = W.induction-compute colStep

  col-in : (p r : A) → r ≺ p → ⟨ col r ∈ˢ col p ⟩
  col-in p r rp =
    subst (λ v → ⟨ col r ∈ˢ v ⟩) (sym (col-eq p)) ∣ (r , rp) , refl ∣₁

  col-out : (p : A) (b : SV.S) → ⟨ b ∈ˢ col p ⟩
```

<!--en-->
Membership admits a computation law in each direction, and the two are usefully asymmetric. Forward: if `r ≺ p` is given, then `col r` is a member of `col p`. The witness is the pair `(r , rp)` together with the path `refl` recording that `col r` is hit at index `r`; transporting along `col-eq p` (in the form `sym`, since the equation was proved in the other direction) moves this member of the explicit image into the type `⟨ col r ∈ˢ col p ⟩`. Backward: an arbitrary membership `⟨ b ∈ˢ col p ⟩` yields only the truncated statement that some `r ≺ p` merely exists with `col r ≡ b`. The proof transports the membership along `col-eq p` back to membership in the explicit image, which is by construction a truncated preimage, then relabels the index data as a predecessor with an equation. Nothing here selects a specific `r`; the truncation `∥ _ ∥₁` is the honest record of what membership reveals.
<!--zh-->
隶属在两个方向上各有一条计算律，且两者有意味深长的不对称。正向：若给定 `r ≺ p`，则 `col r` 是 `col p` 的成员。其见证是偶对 `(r , rp)` 连同记录 `col r` 在索引 `r` 处被命中的路径 `refl`；沿 `col-eq p` 传输 (取 `sym` 形式，因为方程是按另一方向证明的) 把这个显式像的成员移入类型 `⟨ col r ∈ˢ col p ⟩`。反向：任意的隶属 `⟨ b ∈ˢ col p ⟩` 只给出截断的陈述：纯粹地存在某个 `r ≺ p` 使 `col r ≡ b`。证明沿 `col-eq p` 把隶属传输回显式像中的隶属；该隶属按构造就是截断的原像，再把索引数据改写为带等式的前驱。这里没有任何一步选定具体的 `r`；截断 `∥ _ ∥₁` 忠实记录了隶属所能揭示的信息。
<!--ja-->
所属には両方向の計算法則があり、両者は有益な非対称を示します。順方向：`r ≺ p` が与えられれば `col r` は `col p` の要素です。証拠は対 `(r , rp)` と、`col r` がインデックス `r` で命中することを記録するパス `refl` であり、`col-eq p` に沿って (等式は逆向きに証明されているので `sym` の形で) 輸送することで、この明示的な像の要素が型 `⟨ col r ∈ˢ col p ⟩` へ移ります。逆方向：任意の所属 `⟨ b ∈ˢ col p ⟩` から得られるのは、切り詰められた主張、すなわち `col r ≡ b` となる `r ≺ p` が単に存在することだけです。証明は所属を `col-eq p` に沿って明示的な像への所属へ輸送し、それは構成により切り詰められた原像なので、インデックスのデータを等式を伴う前者として読み替えます。ここで特定の `r` を選ぶことは一切ありません。切り詰め `∥ _ ∥₁` が、所属から分かることの正直な記録です。
<!--/-->

```agda
          → ∥ Σ[ r ∈ A ] ((r ≺ p) × (col r ≡ b)) ∥₁
  col-out p b b∈ =
    PT.map (λ z → fst (fst z) , snd (fst z) , snd z)
      (subst (λ v → ⟨ b ∈ˢ v ⟩) (col-eq p) b∈)

  col-ord : (p : A) → IsOrd (col p)
```

<!--en-->
The final theorem says every collapse value is an ordinal, where `IsOrd (col p)` unpacks to a pair: `col p` is transitive, and each of its members is transitive. The proof runs by well-founded induction on `p`, so the induction hypothesis `rec` provides `IsOrd (col r)` for every predecessor `r ≺ p`, and the goal is assembled from its two components. This is the one place where the hypothesis `≺-trans` earns its keep; before reading the two clauses, picture a three-point chain `s ≺ r ≺ p`: transitivity of the relation is exactly what lets membership facts about `col r` be replayed inside `col p`.
<!--zh-->
最后的定理说每个塌缩值都是序数，其中 `IsOrd (col p)` 展开为一对：`col p` 传递，且其每个成员都传递。证明对 `p` 做良基归纳，故归纳假设 `rec` 对每个前驱 `r ≺ p` 提供 `IsOrd (col r)`，目标由其两个分量组装。这是假设 `≺-trans` 发挥作用的地方；在阅读两个子句之前，先想象三点链 `s ≺ r ≺ p`：关系的传递性正是让关于 `col r` 的隶属事实能在 `col p` 内重演的关键。
<!--ja-->
最後の定理は、すべての崩壊値が順序数であると言います。`IsOrd (col p)` は対に展開され、`col p` が推移的であることと、その各要素が推移的であることからなります。証明は `p` 上の整礎帰納で進み、帰納の仮定 `rec` が各前者 `r ≺ p` に対して `IsOrd (col r)` を供給し、目標はその二つの成分から組み上がります。仮定 `≺-trans` が力を発揮するのはまさにここです。二つの節を読む前に、三点の列 `s ≺ r ≺ p` を思い浮かべてください。関係の推移性こそが、`col r` についての所属の事実を `col p` の中で再演することを可能にします。
<!--/-->

```agda
  col-ord = W.induction {P = λ p → IsOrd (col p)} ih
    where
    ih : (p : A) → (∀ r → r ≺ p → IsOrd (col r)) → IsOrd (col p)
    ih p rec = tr , mem
      where
```

<!--en-->
The first clause, that every member of `col p` is transitive, starts from `col-out p x x∈`: the member `x` is `col r` for some merely existing predecessor `r ≺ p`, with an equation `e : col r ≡ x`. The induction hypothesis supplies `isTransV (col r)`, and `subst isTransV e` transports that proof along the equation to type `isTransV x`. The elimination of the truncation is legitimate because the target `isTransV x` is a proposition, certified by `isPropIsTransV x`; no witness is being extracted, only a proposition is being established from a merely existing case analysis.
<!--zh-->
第一个子句说 `col p` 的每个成员都传递。证明从 `col-out p x x∈` 出发：成员 `x` 是某个纯粹存在的前驱 `r ≺ p` 的 `col r`，并带等式 `e : col r ≡ x`。归纳假设提供 `isTransV (col r)`，`subst isTransV e` 沿该等式把这一证明传送到类型 `isTransV x`。截断消去合法，因为目标 `isTransV x` 是命题，由 `isPropIsTransV x` 证明；这里没有抽取见证，只是从纯粹存在的情形分析中确立一个命题。
<!--ja-->
最初の節は、`col p` のすべての要素が推移的であるというものです。証明は `col-out p x x∈` から始まります。要素 `x` は、単に存在する前者 `r ≺ p` に対する `col r` であり、等式 `e : col r ≡ x` を伴います。帰納の仮定が `isTransV (col r)` を供給し、`subst isTransV e` がその証明を等式に沿って型 `isTransV x` へ輸送します。切り詰めの消去が正当なのは、目標の `isTransV x` が命題であり `isPropIsTransV x` がそれを証明するからです。証拠を取り出すのではなく、単に存在する場合分けから命題を確立しているだけです。
<!--/-->

```agda
      mem : (x : SV.S) → ⟨ x ∈ˢ col p ⟩ → isTransV x
      mem x x∈ = PT.rec (isPropIsTransV x)
        (λ z → subst isTransV (snd (snd z)) (rec (fst z) (fst (snd z)) .fst))
        (col-out p x x∈)
      tr : isTransV (col p)
```

<!--en-->
The second clause proves `col p` itself transitive: given `y ∈ x` and `x ∈ col p`, show `y ∈ col p`. First peel `x ∈ col p` through `col-out`, obtaining merely some `r ≺ p` with `col r ≡ x`. The equation transports the given `y ∈ x` into `⟨ y ∈ˢ col r ⟩`, which is where the running example's middle link `r` finally connects the two ends of the chain.
<!--zh-->
第二个子句证明 `col p` 自身传递：给定 `y ∈ x` 与 `x ∈ col p`，要证 `y ∈ col p`。先把 `x ∈ col p` 经 `col-out` 剥开，纯粹地得到某个 `r ≺ p` 使 `col r ≡ x`。该等式把已给的 `y ∈ x` 传输入 `⟨ y ∈ˢ col r ⟩`，运行示例中的中间环节 `r` 正是在这里把链条两端接了起来。
<!--ja-->
第二の節は `col p` 自身の推移性を示します。`y ∈ x` と `x ∈ col p` が与えられたとき `y ∈ col p` を示します。まず `x ∈ col p` を `col-out` で剥がし、`col r ≡ x` となる `r ≺ p` が単に得られます。この等式が与えられた `y ∈ x` を `⟨ y ∈ˢ col r ⟩` へ輸送し、実行例の中間の環 `r` がまさにここで列の両端をつなぎます。
<!--/-->

```agda
      tr {x} {y} y∈x x∈col = PT.rec (snd (y ∈ˢ col p)) outer (col-out p x x∈col)
        where
        outer : Σ[ r ∈ A ] ((r ≺ p) × (col r ≡ x)) → ⟨ y ∈ˢ col p ⟩
        outer (r , rp , e) =
          PT.rec (snd (y ∈ˢ col p)) inner
```

<!--en-->
Now the chain closes. From `y ∈ col r`, `col-out` applied at `r` yields merely some `s ≺ r` with `col s ≡ y`; call its equation `e2`. Relation transitivity composes `s ≺ r` with `r ≺ p` to give `s ≺ p`, and `col-in p s` promotes `col s` to a member of `col p`. Finally `subst` along `e2` replaces `col s` by `y` in the membership target, delivering `⟨ y ∈ˢ col p ⟩`. Both eliminations of truncation land in the proposition `⟨ y ∈ˢ col p ⟩`, and the whole argument uses only well-founded recursion, transport, and the transitivity hypothesis: no classical principle enters anywhere in this chapter.
<!--zh-->
现在链条闭合。从 `y ∈ col r` 出发，在 `r` 处应用 `col-out` 纯粹地给出某个 `s ≺ r` 使 `col s ≡ y`；记其等式为 `e2`。关系传递性把 `s ≺ r` 与 `r ≺ p` 复合成 `s ≺ p`，`col-in p s` 把 `col s` 提升为 `col p` 的成员。最后沿 `e2` 用 `subst` 在隶属目标中把 `col s` 换成 `y`，得到 `⟨ y ∈ˢ col p ⟩`。两次截断消去都落在命题 `⟨ y ∈ˢ col p ⟩` 中，整个论证只用良基递归、传输和传递性假设：本章任何地方都没有经典原理进入。
<!--ja-->
これで列が閉じます。`y ∈ col r` から、`r` で `col-out` を適用すると、`col s ≡ y` となる `s ≺ r` が単に得られ、その等式を `e2` とします。関係の推移性が `s ≺ r` と `r ≺ p` を合成して `s ≺ p` を与え、`col-in p s` が `col s` を `col p` の要素へ引き上げます。最後に `e2` に沿った `subst` が所属の目標の中で `col s` を `y` に置き換え、`⟨ y ∈ˢ col p ⟩` が得られます。切り詰めの消去はどちらも命題 `⟨ y ∈ˢ col p ⟩` の中に着地し、議論全体が使うのは整礎再帰、輸送、そして推移性の仮定だけです。古典的な原理は本章のどこにも入りません。
<!--/-->

```agda
            (col-out r y (subst (λ v → ⟨ y ∈ˢ v ⟩) (sym e) y∈x))
          where
          inner : Σ[ s ∈ A ] ((s ≺ r) × (col s ≡ y)) → ⟨ y ∈ˢ col p ⟩
          inner (s , sr , e2) =
            subst (λ v → ⟨ v ∈ˢ col p ⟩) e2 (col-in p s (≺-trans sr rp))
```
