<!--en-->
# Rank descent through coded pairs

A later well-founded recursion will proceed over codes and, at each step, process an immediate component of the code it is given. For the recursion to be well-founded it needs a measure that strictly decreases from the code to that component. Membership will not supply one. The Kuratowski pair is defined as `pr a b = ⁅ ⁅ a ⁆s , ⁅ a , b ⁆ ⁆`{.Agda}: a component such as `b` is reached only through the intermediate unordered pair `⁅ a , b ⁆`{.Agda}, and that intermediate set is not itself a code. An induction on membership therefore cannot carry a hypothesis about codes across them.

Rank can. Rank increases strictly along membership, and its values are ordinals, whose membership is transitive; so a finite membership chain collapses into a single comparison of ordinals, and the recursion can instead be justified by induction on rank. This chapter assembles exactly those comparisons: one step for each side of an ordered pair, and their composition into the four-step descent from each side of a paired payload to the outer tagged code.
<!--zh-->
# 沿编码对作秩下降

后续将对编码作良基递归，并在每一步处理所给码的一个直接部件。递归要良基，就需要一个从码到该部件严格下降的度量。成员关系给不出这个度量。Kuratowski 对定义为 `pr a b = ⁅ ⁅ a ⁆s , ⁅ a , b ⁆ ⁆`{.Agda}：像 `b` 这样的部件必须经过中间的无序对 `⁅ a , b ⁆`{.Agda} 才能到达，而这个中间集合本身并不是码。故沿成员关系进行的归纳无法把关于码的假设搬过它们。

秩可以。秩沿成员关系严格增长，且取值于序数，而序数的成员关系是传递的；于是有限的成员链收缩为一次序数比较，递归便可改为按**秩**作良基归纳。本章组装的正是这些比较：有序对每一侧各一步，再把它们复合成从成对载荷的每一侧到外层带标签码的四步下降。
<!--ja-->
# 符号化された対に沿う階数降下

後では符号に対して整礎再帰を行い、各段階で与えられた符号の直下の成分を処理します。再帰が整礎であるためには、符号からその成分へと狭義に減少する尺度が必要です。所属関係はそれを与えてくれません。Kuratowski 対は `pr a b = ⁅ ⁅ a ⁆s , ⁅ a , b ⁆ ⁆`{.Agda} と定義されるので、`b` のような成分に届くには、中間の非順序対 `⁅ a , b ⁆`{.Agda} を経なければならず、この中間集合そのものは符号ではありません。したがって所属に関する帰納は、符号についての仮定をそれらの間へ運ぶことができません。

階数ならできます。階数は所属に沿って狭義に増加し、その値は順序数であり、順序数の所属は推移的です。そこで有限の所属の連鎖は一つの順序数の比較へと縮み、再帰は符号そのものではなく**階数**に関する整礎帰納によって正当化できます。本章が組み立てるのはまさにこの比較です。順序対の各側ごとに一段階、さらにそれを合成して、対になったペイロードの各側から外側のタグ付き符号への 4 段階の降下を得ます。
<!--/-->

<!--en-->
The mathematical setting is the cumulative hierarchy: its carrier `S`, its proposition-valued membership `∈ˢ`, and the structure `𝒮ᵥ` that packages the set-theoretic operations. One preliminary is worth stating before any descent is proved. A well-founded recursion needs a strict measure, and the measure used later is the von Neumann rank, defined and studied in the chapter on rank; there `rank-mono` records that rank increases strictly along membership, and `rank-ord` that every rank is an ordinal.
<!--zh-->
数学背景是累积层级：其载体 `S`、命题值的隶属关系 `∈ˢ`，以及打包诸集合论运算的结构 `𝒮ᵥ`。在证明任何下降之前，值得先明确一件预备事项。良基递归需要一个严格度量，而此后所用的度量是 von Neumann 秩，它在与秩有关的章节中定义并研究；在那里，`rank-mono` 记录秩沿隶属关系严格增长，`rank-ord` 记录每个秩都是序数。
<!--ja-->
数学的な舞台は累積階層です。その台 `S`、命題値をとる所属 `∈ˢ`、そして集合論的演算をひとまとめにした構造 `𝒮ᵥ` です。降下を証明する前に一つ、準備をはっきりさせておきます。整礎再帰には狭義の尺度が必要で、後で使う尺度は von Neumann の階数です。これはランクの章で定義され研究されています。そこでは `rank-mono` が階数が所属に沿って狭義に増加することを、`rank-ord` がすべての階数が順序数であることを記録しています。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude

module L.Coding.Descent {ℓ : Level} where

open import FOL.ZFStructure using ( module hPropStructure )
```

<!--en-->
The concrete problem can be seen from the shape of the code. A component of `pr a b` is not a member of `pr a b` directly: it is wrapped inside the unordered pair `⁅ a , b ⁆`{.Agda}, which in turn is one of the two members of the outer unordered pair. Membership gives a chain of steps rather than one edge, and the links of the chain are sets that carry no code structure at all. What replaces the chain is a strict inequality between ordinals, obtained by translating each membership edge through the rank and then composing.
<!--zh-->
从码的形状就能看出具体困难。`pr a b` 的部件并不是 `pr a b` 的直接成员：它被包在无序对 `⁅ a , b ⁆`{.Agda} 内，而后者又是外层无序对的两个成员之一。成员关系给出的是一条多步的链，而非一条边，且链上的环节是完全不携带码结构的集合。取代这条链的是序数之间的一个严格不等式：先把每条成员边经秩翻译，再复合起来。
<!--ja-->
具体的な難しさは符号の形から読み取れます。`pr a b` の成分は `pr a b` の直接の要素ではありません。それは非順序対 `⁅ a , b ⁆`{.Agda} の中に包まれ、後者はさらに外側の非順序対の 2 つの要素の一つです。所属が与えるのは 1 本の辺ではなく複数段階の連鎖であり、連鎖の環となる集合はまったく符号の構造を持たないものです。この連鎖の代わりとなるのが、各所属の辺を階数を通して翻訳し、それを合成して得られる順序数どうしの狹義の不等式です。
<!--/-->

```agda
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Coding {ℓ} using ( pr )
open import L.Rank {ℓ} using ( rank; rank-mono; rank-ord )

import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁ )
```

<!--en-->
The comparison uses three ingredients from the hierarchy: the unordered pair `⁅ u , v ⁆`{.Agda}, the pairing axiom `pairing-ax`, which classifies membership in an unordered pair propositionally, and `∈∈ₛ`, which converts membership in the underlying set sense into the structural membership `∈ˢ` and back. The sum type `_⊎_` will carry the explicit choice between the two components: `inl` for the left, `inr` for the right. Keeping the choice explicit rather than merely exists matters here, because the descent proof must pick out which component of the pair is being descended into.
<!--zh-->
这个比较用到层级的三个材料：无序对 `⁅ u , v ⁆`{.Agda}、以命题方式刻画无序对成员关系的配对公理 `pairing-ax`，以及在底层数据的成员与结构化成员 `∈ˢ` 之间转换的 `∈∈ₛ`。和类型 `_⊎_` 将承载两个分量之间的显式选择：`inl` 取左，`inr` 取右。这里保持选择的显式性、而非「仅仅存在」，是重要的，因为下降证明必须指明下降进入的是对的哪一个分量。
<!--ja-->
この比較には階層からの 3 つの材料を使います。非順序対 `⁅ u , v ⁆`{.Agda}、非順序対への所属を命題として特徴づける対の公理 `pairing-ax`、そして根底の集合としての所属と構造化された所属 `∈ˢ` とを相互に変換する `∈∈ₛ` です。和型 `_⊎_` は 2 つの成分の明示的な選択を運びます。左には `inl`、右には `inr` です。ここで選択を「単に存在する」ではなく明示的に保つことが重要なのは、降下の証明が対のどちらの成分へ降りるのかを指摘しなければならないからです。
<!--/-->

```agda
open import Cubical.Data.Sum using ( _⊎_; inl; inr )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ∈∈ₛ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ⁅_,_⁆; pairing-ax; ⁅_⁆s )

```

<!--en-->
The crucial distinction is where transitivity is available. Arbitrary set membership is not treated as transitive. After each membership edge has been sent through `rank-mono`, however, the intermediate objects are ordinals, and `rank-ord` supplies the transitivity needed to compose their strict inequalities.
<!--zh-->
关键区别在于传递性可用的位置。这里不把任意集合的隶属关系视为传递的；只有每条成员边先经 `rank-mono` 化为秩之间的关系后，中间对象才是序数，`rank-ord` 才提供复合这些严格不等式所需的传递性。
<!--ja-->
重要なのは、推移性を使える場所の区別です。任意の集合の所属を推移的とはみなしません。各所属の辺を `rank-mono` で階数どうしの関係へ移した後にはじめて、中間の対象が順序数となり、`rank-ord` がその狭義の不等式を合成するための推移性を与えます。
<!--/-->

```agda
open hPropStructure 𝒮ᵥ
```

<!--en-->
## The steps

The descent argument rests on two reusable facts. The first is the membership edge into an unordered pair: if `w` is, explicitly, `u` or `v`, then `w` belongs to `⁅ u , v ⁆`{.Agda}. The second is the rank step: one membership edge `x ∈ˢ y` together with a rank descent from `y` to `z` yields a rank descent from `x` to `z`. Together they turn chains of membership into single comparisons of ordinals, at arbitrary sets rather than at any particular pair expression.
<!--zh-->
## 诸步

下降论证立于两条可复用的事实。其一是进入无序对的成员边：若 `w` 显式地等于 `u` 或 `v`，则 `w` 属于 `⁅ u , v ⁆`{.Agda}。其二是秩的步骤：一条成员边 `x ∈ˢ y` 加上一段从 `y` 到 `z` 的秩下降，就给出从 `x` 到 `z` 的秩下降。两者合起来把成员关系的链化为单次序数比较，并且在任意集合上成立，不局限于任何具体的对表达式。
<!--ja-->
## 階数を下げる基本段階

降下の議論は 2 つの再利用可能な事実に立っています。第 1 は非順序対への所属の辺です。`w` が `u` か `v` に明示的に等しいなら、`w` は `⁅ u , v ⁆`{.Agda} に属します。第 2 は階数の段階です。1 本の所属の辺 `x ∈ˢ y` と `y` から `z` への階数降下があれば、`x` から `z` への階数降下が得られます。両者を合わせると、所属の連鎖が一つの順序数の比較に変わります。しかも任意の集合について成り立ち、特定の対の式に限定されません。
<!--/-->

<!--en-->
The pairing axiom classifies membership in `⁅ u , v ⁆`{.Agda} as a truncated disjunction: it is merely the case that a member equals `u` or equals `v`. The helper `pair∈` produces the reverse direction with the truncation removed: it takes an explicit sum `w ≡ u ⊎ w ≡ v` and returns a proof of `⟨ w ∈ˢ ⁅ u , v ⁆ ⟩`, by inserting `∣ h ∣₁` into the truncated side of `pairing-ax` and then converting through `∈∈ₛ`. This is exactly the direction a descent proof needs: given which component we are descending into, membership follows without any further case analysis. The composition step `trans≺` then does the rank translation. Since `rank z` is an ordinal by `rank-ord z`, membership below `rank z` is transitive, so `rank x ∈ˢ rank y` and `rank y ∈ˢ rank z` compose into `rank x ∈ˢ rank z`; the first hypothesis is `rank-mono x y` applied to `x ∈ˢ y`. Note that transitivity is used on the ordinal rank, never assumed for membership of arbitrary sets.
<!--zh-->
配对公理把 `⁅ u , v ⁆` 的成员关系刻画为截断的析取：「成员等于 `u` 或等于 `v`」整体仅仅成立。辅助引理 `pair∈` 给出去掉截断的逆向：它取显式的和 `w ≡ u ⊎ w ≡ v`，通过把 `∣ h ∣₁` 放入 `pairing-ax` 的截断一侧、再经 `∈∈ₛ` 转换，返回 `⟨ w ∈ˢ ⁅ u , v ⁆ ⟩` 的证明。这正是下降证明所需的方向：已指明下降进入哪个分量，成员关系便无须再分情形地随之而来。复合步骤 `trans≺` 随后做秩的翻译。由 `rank-ord z`，`rank z` 是序数，故 `rank z` 以下的成员关系是传递的，故 `rank x ∈ˢ rank y` 与 `rank y ∈ˢ rank z` 复合成 `rank x ∈ˢ rank z`；第一个假设就是把 `rank-mono x y` 施于 `x ∈ˢ y`。注意传递性只用在序数秩上，从不假设任意集合的成员关系传递。
<!--ja-->
対の公理は `⁅ u , v ⁆` の所属を切り詰められた選言として特徴づけます。「要素が `u` に等しいか `v` に等しい」という選言全体が切り詰められています。補題 `pair∈` は、切り詰めを外した逆向きを与えます。明示的な和 `w ≡ u ⊎ w ≡ v` を受け取り、`∣ h ∣₁` を `pairing-ax` の切り詰められた側に挿入し、`∈∈ₛ` で変換して、`⟨ w ∈ˢ ⁅ u , v ⁆ ⟩` の証明を返します。これがまさに降下の証明に必要な方向です。どちらの成分へ降りるかが指摘されていれば、場合分けなしに所属が従います。合成の段階 `trans≺` が次に階数への翻訳を行います。`rank-ord z` により `rank z` は順序数であり、`rank z` の下での所属は推移的なので、`rank x ∈ˢ rank y` と `rank y ∈ˢ rank z` は `rank x ∈ˢ rank z` に合成されます。第 1 の仮定は `x ∈ˢ y` に `rank-mono x y` を施したものです。推移性を使うのは順序数としての階数についてであって、任意の集合の所属について推移性を仮定することは決してない、と注意してください。
<!--/-->

```agda
pair∈ : (u v w : S) → (w ≡ u) ⊎ (w ≡ v) → ⟨ w ∈ˢ ⁅ u , v ⁆ ⟩
pair∈ u v w h = ∈∈ₛ {a = w} {b = ⁅ u , v ⁆} .snd (pairing-ax u v w .snd ∣ h ∣₁)

trans≺ : (x y z : S) → ⟨ x ∈ˢ y ⟩ → ⟨ rank y ∈ˢ rank z ⟩ → ⟨ rank x ∈ˢ rank z ⟩
trans≺ x y z x∈y ry∈rz = rank-ord z .fst (rank-mono x y x∈y) ry∈rz

```

<!--en-->
## Into a tagged payload

With the two steps in hand, the descents for coded pairs follow by reading the shape of the Kuratowski pair. A component `x` of `pr a b` reaches the code through two membership edges: `x` belongs to `⁅ a , b ⁆`{.Agda}, and `⁅ a , b ⁆`{.Agda} belongs to `pr a b`. So `pair-component≺` proves the two-step descent for either component, with no condition on the tag. Specializing to the second component gives `payload≺`, the descent from a payload to its tagged code. A paired payload `pr a b` under a tag `c` then needs one more composition, and here the two sides genuinely differ: `leftPart` descends into the first component inside the payload and then composes with the payload descent, while `rightPart` simply applies the payload descent twice. Throughout, the tag `c` is an arbitrary set; nothing requires it to be a numeral or to be descended into.
<!--zh-->
## 进入带标签的载荷

有了两条基本步骤，编码对的下降只需读出 Kuratowski 对的形状。`pr a b` 的部件 `x` 经过两条成员边到达整条码：`x` 属于 `⁅ a , b ⁆`{.Agda}，而 `⁅ a , b ⁆`{.Agda} 属于 `pr a b`。故 `pair-component≺` 对任一分量证明这条两步下降，对标签不加任何条件。取第二分量即得 `payload≺`：从载荷到其带标签码的下降。标签 `c` 之下的成对载荷 `pr a b` 还需再复合一次，而这里两侧确实不同：`leftPart` 先降入载荷内部的第一分量，再与载荷下降复合；`rightPart` 只是把载荷下降施用两次。通篇标签 `c` 是任意集合，无须是数码，也不被降入。
<!--ja-->
## タグ付きコードのペイロードへ降りる

2 つの基本段階が手もとにあれば、符号化された対の降下は Kuratowski 対の形を読むだけで得られます。`pr a b` の成分 `x` が符号全体に届くには 2 本の所属の辺を経ます。`x` は `⁅ a , b ⁆`{.Agda} に属し、`⁅ a , b ⁆`{.Agda} は `pr a b` に属する。そこで `pair-component≺` は任意の成分についてこの 2 段階の降下を証明し、タグには何の条件も課しません。第 2 成分に限定すると `payload≺`、すなわちペイロードからそのタグ付き符号への降下が得られます。タグ `c` のもとの対になったペイロード `pr a b` にはもう一度の合成が要りますが、ここで両側は実際に異なります。`leftPart` はまずペイロードの内側の第 1 成分へ降り、それからペイロード降下と合成します。`rightPart` はペイロード降下を 2 回施すだけです。通じてタグ `c` は任意の集合であり、数項である必要も、そこへ降りることもありません。
<!--/-->

<!--en-->
The two edges are supplied explicitly. For the first, `pair∈ a b x h` uses the given choice `h : x ≡ a ⊎ x ≡ b`. For the second, the choice is `inr refl`: the unordered pair `⁅ a , b ⁆`{.Agda} is definitionally the right member of the outer pair, so `pair∈ ⁅ a ⁆s ⁅ a , b ⁆ ⁅ a , b ⁆ (inr refl)` proves its membership in `pr a b`, and `rank-mono` turns that into the rank inequality `rank ⁅ a , b ⁆ ∈ˢ rank (pr a b)`. Then `trans≺` composes. Note how the middle set `⁅ a , b ⁆`{.Agda} appears only inside this proof: the statement of `pair-component≺` mentions nothing but the code and the chosen component. The specialization `payload≺` reads `z` as the right component of `pr c z`, again by `inr refl`, giving the descent from a payload to its tagged code for arbitrary tag `c`.
<!--zh-->
两条边都被显式给出。第一条用给定的选择 `h : x ≡ a ⊎ x ≡ b` 经 `pair∈ a b x h`。第二条的选择是 `inr refl`：无序对 `⁅ a , b ⁆`{.Agda} 定义性地就是外层对的右成员，故 `pair∈ ⁅ a ⁆s ⁅ a , b ⁆ ⁅ a , b ⁆ (inr refl)` 证明它在 `pr a b` 中的成员关系，`rank-mono` 再把它变成秩不等式 `rank ⁅ a , b ⁆ ∈ˢ rank (pr a b)`。然后 `trans≺` 复合两者。注意中间集合 `⁅ a , b ⁆`{.Agda} 只出现在证明内部：`pair-component≺` 的命题除码与所选分量外不提任何东西。特化 `payload≺` 再次用 `inr refl` 把 `z` 读作 `pr c z` 的右分量，给出对任意标签 `c` 从载荷到其带标签码的下降。
<!--ja-->
2 本の辺は明示的に供給されます。第 1 は与えられた選択 `h : x ≡ a ⊎ x ≡ b` を `pair∈ a b x h` で使います。第 2 の選択は `inr refl` です。非順序対 `⁅ a , b ⁆`{.Agda} は定義的に外側の対の右の要素なので、`pair∈ ⁅ a ⁆s ⁅ a , b ⁆ ⁅ a , b ⁆ (inr refl)` がその所属を証明し、`rank-mono` がそれを階数の不等式 `rank ⁅ a , b ⁆ ∈ˢ rank (pr a b)` に変えます。そして `trans≺` が両者を合成します。途中の集合 `⁅ a , b ⁆`{.Agda} がこの証明の内部にしか現れないことに注意してください。`pair-component≺` の命題は符号と選ばれた成分以外に何も言及しません。特殊化 `payload≺` は再び `inr refl` によって `z` を `pr c z` の右成分と読み、任意のタグ `c` に対するペイロードからそのタグ付き符号への降下を与えます。
<!--/-->

```agda
pair-component≺ : (a b x : S) → (x ≡ a) ⊎ (x ≡ b) → ⟨ rank x ∈ˢ rank (pr a b) ⟩
pair-component≺ a b x h = trans≺ x ⁅ a , b ⁆ (pr a b) (pair∈ a b x h)
  (rank-mono ⁅ a , b ⁆ (pr a b) (pair∈ ⁅ a ⁆s ⁅ a , b ⁆ ⁅ a , b ⁆ (inr refl)))

payload≺ : (c z : S) → ⟨ rank z ∈ˢ rank (pr c z) ⟩
payload≺ c z = pair-component≺ c z z (inr refl)
```

<!--en-->
Both lemmas under the tag compose at the ordinal `rank (pr c (pr a b))`, using the transitivity field of `rank-ord`. The asymmetry between them reflects the nesting. For `leftPart`, the target `a` is the first component inside the payload, so the first edge is `pair-component≺ a b a (inl refl)`, giving `rank a ∈ˢ rank (pr a b)`, and the second edge is the payload descent `payload≺ c (pr a b)`. For `rightPart`, the target `b` is the second component of the payload itself, so both edges are payload descents: `payload≺ a b` from `b` to `pr a b`, then `payload≺ c (pr a b)` from the payload to the outer tagged code. In both cases the conclusion has the same shape, `rank a` or `rank b` belonging to `rank (pr c (pr a b))`, which is precisely the measure decrease a later recursion on tagged codes will demand of each immediate component.
<!--zh-->
两条带标签的引理都在序数 `rank (pr c (pr a b))` 处复合，用的是 `rank-ord` 的传递性分量。两者之间的不对称反映嵌套结构。对 `leftPart`，目标 `a` 是载荷内部的第一分量，故第一条边是 `pair-component≺ a b a (inl refl)`，给出 `rank a ∈ˢ rank (pr a b)`，第二条边是载荷下降 `payload≺ c (pr a b)`。对 `rightPart`，目标 `b` 是载荷自身的第二分量，故两条边都是载荷下降：`payload≺ a b` 从 `b` 到 `pr a b`，再 `payload≺ c (pr a b)` 从载荷到外层带标签码。两种情形的结论形状相同：`rank a` 或 `rank b` 属于 `rank (pr c (pr a b))`，这正是后续对带标签码所作的良基递归对每个直接部件所要求的度量下降。
<!--ja-->
タグのもとの両補題は、順序数 `rank (pr c (pr a b))` において合成されます。使うのは `rank-ord` の推移性のフィールドです。両者の非対称性は入れ子の構造を反映しています。`leftPart` では目標 `a` はペイロードの内側の第 1 成分なので、第 1 の辺は `pair-component≺ a b a (inl refl)` で、`rank a ∈ˢ rank (pr a b)` を与えます。第 2 の辺はペイロード降下 `payload≺ c (pr a b)` です。`rightPart` では目標 `b` はペイロード自身の第 2 成分なので、両方の辺がペイロード降下です。`payload≺ a b` が `b` から `pr a b` へ、次に `payload≺ c (pr a b)` がペイロードから外側のタグ付き符号へ。どちらの場合も結論は同じ形、`rank a` または `rank b` が `rank (pr c (pr a b))` に属する、であり、これは後のタグ付き符号上の整礎再帰が各直下の成分に要求する尺度の減少そのものです。
<!--/-->

```agda

leftPart : (c a b : S) → ⟨ rank a ∈ˢ rank (pr c (pr a b)) ⟩
leftPart c a b = rank-ord (pr c (pr a b)) .fst
  (pair-component≺ a b a (inl refl)) (payload≺ c (pr a b))

rightPart : (c a b : S) → ⟨ rank b ∈ˢ rank (pr c (pr a b)) ⟩
rightPart c a b = rank-ord (pr c (pr a b)) .fst (payload≺ a b) (payload≺ c (pr a b))
```
