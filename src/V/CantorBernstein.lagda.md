<!--en-->
# Cantor–Schröder–Bernstein for small presentations

Mutual injections between the small presentations of two sets determine a bijection. The proof first constructs the bijection for small types under excluded middle, then gives a generic form that turns any mutually available coded injections into such a bijection.

The classical Cantor–Schröder–Bernstein theorem says that injections $f : A → B$ and $g : B → A$ yield a bijection $A → B$. In this chapter the two types share one universe level ℓ, and the only extra assumption is excluded middle at that level: for every proposition living at level ℓ, a proof or a refutation. The argument itself belongs to the index types $A$ and $B$, not to the sets of the cumulative hierarchy, which is precisely what later lets it be replayed on the member types of arbitrary small presentations. The proof needs to form some propositions by truncation and then to decide them; the setup below therefore fixes both the classical hypothesis and the proposition-valued vocabulary it will be applied to.
<!--zh-->
# 小呈现上的 Cantor–Schröder–Bernstein 定理

两个集合的小呈现之间若有双向单射，便可得到双射。证明先在排中律下为小类型构造双射，再给出通用形式，把任意可双向读出的编码单射转成这类双射。

经典的 Cantor–Schröder–Bernstein 定理说，单射 $f : A → B$ 与 $g : B → A$ 给出双射 $A → B$。本章中两个类型共享同一个宇宙层级 ℓ，而唯一的额外假设是该层级上的排中律：对住在层级 ℓ 的每个命题，给出证明或反驳。论证本身属于指标类型 $A$ 与 $B$，而不属于累积层级中的集合；正因如此，后面才能把它原样搬到任意小呈现的成员类型上。证明需要用命题截断造出一些命题，然后对它们作判定；下面的设置因此同时固定了经典假设，以及将要施加于其上的命题值词汇。
<!--ja-->
# 小さな提示に対する Cantor–Schröder–Bernstein の定理

二つの集合の小さな提示の間に双方向の単射があれば、全単射が得られます。まず排中律の下で小さな型について全単射を構成し、さらに任意の相互に読み出せる符号化された単射からそのような全単射を得る一般的な形にまとめます。

古典的な Cantor–Schröder–Bernstein の定理は、単射 $f : A → B$ と $g : B → A$ から全単射 $A → B$ が得られるというものです。この章では二つの型が同一の宇宙レベル ℓ を共有し、追加の仮定はそのレベルでの排中律、すなわちレベル ℓ に住む各命題に対する証明か反証かだけです。議論そのものは累積階層の集合ではなく指標型 $A$ と $B$ に属します。まさにそのおかげで、後で任意の小さな提示のメンバー型へそのまま再生できるのです。証明は命題を命題的切り詰めで作り、それを判定する必要があるため、以下の設定ではその古典的仮定と、それを適用する命題値の語彙の両方を固定します。
<!--/-->

<!--en-->
A decision at level ℓ is packaged once and reused throughout: `LEM ℓ`{.Agda} takes a proposition `P : hProp ℓ`{.Agda} and returns either a proof of `⟨ P ⟩`{.Agda} or a refutation, a map from `⟨ P ⟩`{.Agda} into the empty type. The module parameter `lem` is therefore an instance at this one level, not a global principle for all levels. Everything constructed in the chapter will be parametric in it, so the hypothesis appears explicitly wherever a classical verdict is consumed.
<!--zh-->
层级 ℓ 上的判定在这里被打包一次并全章复用：`LEM ℓ`{.Agda} 取命题 `P : hProp ℓ`{.Agda}，返回 `⟨ P ⟩`{.Agda} 的证明，或一个反驳，即从 `⟨ P ⟩`{.Agda} 映入空类型的映射。因此模块参数 `lem` 只是这一个层级上的实例，而不是对所有层级都成立的全局原理。本章构造的一切都对它保持参数化，所以每当需要经典裁决时，这一假设都会显式出现。
<!--ja-->
レベル ℓ での判定はここで一度だけまとめられ、章全体で再利用されます。`LEM ℓ`{.Agda} は命題 `P : hProp ℓ`{.Agda} を受け取り、`⟨ P ⟩`{.Agda} の証明か、あるいは `⟨ P ⟩`{.Agda} を空型へ写す反証のどちらかを返します。したがってモジュールパラメータ `lem` はこの一レベルでの実例であって、すべてのレベルに及ぶ大域的な原理ではありません。章で構成されるものはすべてこれに対してパラメトリックであり、古典的な判定が使われる箇所では必ずこの仮定が明示的に現れます。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Classical using ( LEM )

module V.CantorBernstein {ℓ : Level} (lem : LEM ℓ) where

open import Cubical.Functions.Embedding using ( Embedding-into-isSet→isSet )
```

<!--en-->
The proof will form several propositions by truncating an existential: the statement that x lies in the image of g is ∥ Σ[ y ∈ B ] (g y ≡ x) ∥₁, which is merely inhabited rather than carrying a chosen preimage. Such truncated statements are propositions by `squash₁`, and a proof of one cannot be eliminated into arbitrary data, only into a proposition-valued target. That restriction is exactly why the classical hypothesis will be needed: to turn a mere existence into a chosen preimage when the argument requires one.
<!--zh-->
证明将用对存在命题作命题截断来构造若干命题：x 属于 g 的像这一陈述是 ∥ Σ[ y ∈ B ] (g y ≡ x) ∥₁，它仅保留原像存在这一事实，而不携带选定的原像。这类命题截断陈述借助 `squash₁` 成为命题，且其证明只能消解到命题值的目标中，不能得到任意数据。这一限制正是需要经典假设的原因：当论证需要选定原像时，把单纯的存在性变成选定的原像。
<!--ja-->
証明は、存在を命題的切り詰めした命題をいくつも作ります。x が g の像に属するという主張は ∥ Σ[ y ∈ B ] (g y ≡ x) ∥₁ であり、選ばれた原像を持たず、存在することだけが保留されています。このような命題的切り詰めされた主張は `squash₁` によって命題になり、その証明は命題値の対象へは消去できますが、任意のデータへはできません。この制限こそが古典的仮定を必要とする理由です。議論が選ばれた原像を要する場面で、単なる存在性を選ばれた原像へ変えるのに排中律を使います。
<!--/-->

```agda
import Cubical.Data.Sum as Sum
open Sum using ( _⊎_; inl; inr )
import Cubical.Data.Empty as Empty
open import Cubical.Data.Empty.Properties using ( isProp⊥ )
import Cubical.HITs.PropositionalTruncation as PT
```

<!--en-->
Two kinds of propositions dominate the chapter: membership in the image of g, and reachability by a finite alternating chain. Both are stored as elements of `hProp ℓ`, which packages an underlying type with a proof that it is a proposition; `⟨ P ⟩`{.Agda} projects the underlying type, while the propositionhood proof stays in the second component. The remaining imports supply the machinery around them: disjoint sums for the bad/good case split, `isProp⊥` for the refutation side, `Σ≡Prop` for identifying pairs whose second components are proposition-valued, and the cumulative hierarchy together with the fact that a member type `⟪ a ⟫`{.Agda} of a set embeds into a set, which will later certify that the member types are h-sets.
<!--zh-->
本章由两类命题主导：属于 g 的像，以及经由有限交错链可达。二者都存为 `hProp ℓ` 的元素，它把底层类型与「它是命题」的证明打包在一起；`⟨ P ⟩`{.Agda} 投影出底层类型，而命题性证明留在第二个分量。其余导入提供围绕它们的机制：坏/好情形分裂用的不交和、反驳一侧的 `isProp⊥`、对第二分量为命题值的序对作识别的 `Σ≡Prop`，以及累积层级本身与「集合的成员类型 `⟪ a ⟫`{.Agda} 嵌入到一个集合、因而它是 h-集合」这一事实。
<!--ja-->
この章を支配するのは二種類の命題です。g の像への所属と、有限の交互の鎖で到達できることです。どちらも `hProp ℓ` の要素として保存されます。`hProp ℓ` は基礎型と、それが命題であることの証明をひとまとめにするもので、`⟨ P ⟩`{.Agda} が基礎型を取り出し、命題性の証明は第 2 成分に残ります。残りの import はその周辺の機構を供給します。良し悪しの場合分けのための非交和、反証側のための `isProp⊥`、第 2 成分が命題値であるような対を同一視するための `Σ≡Prop`、そして累積階層と、集合のメンバー型 `⟪ a ⟫`{.Agda} がある集合へ埋め込めるため h-集合であるという事実です。
<!--/-->

```agda
open PT using ( ∣_∣₁; ∥_∥₁; squash₁ )
open import Cubical.Data.Sigma using ( Σ≡Prop )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; setIsSet )
open import Cubical.HITs.CumulativeHierarchy.Properties
  using ( ⟪_⟫; ⟪_⟫↪; isEmb⟪_⟫↪ )
```

<!--en-->
Two injections, one each way, give one bijection. This section proves that for two types $A$ and $B$ at the same universe level, with $A$ an h-set, under excluded middle at that level. The construction classifies each element of $A$ as bad or good: the bad elements are those reachable by a finite alternating preimage chain that starts outside the image of $g$. A bad element is sent forward through $f$, a good element back along a chosen inverse of $g$. Excluded middle enters twice, once to decide the badness proposition `C` and once to extract a chosen preimage from the truncated image statement; the chain itself is the predicate family `Cₙ`, and the only structural fact it needs is that $x ↦ g (f x)$ preserves badness.
<!--zh-->
两个方向各一条单射，给出一个双射。本节在层级 ℓ 的排中律下，对同一宇宙层级的两个类型 $A$ 与 $B$(其中 $A$ 是 h-集合) 证明这一点。构造把 $A$ 的每个元素分为坏的或好的：坏元素是那些可由一条从 g 的像之外出发的有限交错原像链到达的元素。坏元素经 $f$ 向前送，好元素沿 g 的选定逆像送回。排中律进入两次：一次判定坏性命题 `C`，一次从命题截断的像陈述中提取选定的原像；链本身是谓词族 `Cₙ`，它唯一需要的结构事实是 $x ↦ g (f x)$ 保持坏性。
<!--ja-->
互いに逆向きの二つの単射から、ひとつの全単射が得られます。この節は、同一の宇宙レベルにある二つの型 $A$ と $B$($A$ は h-集合) について、そのレベルの排中律の下でこれを証明します。構成は $A$ の各元を悪いか良いかに分類します。悪い元とは、g の像の外から始まる有限の交互の原像の鎖で到達できる元のことです。悪い元は f で前へ送り、良い元は g の選ばれた逆像に沿って送り戻します。排中律は二度使われます。一度は悪さの命題 `C` を判定するため、もう一度は命題的切り詰めされた像の主張から選ばれた原像を取り出すためです。鎖そのものは述語族 `Cₙ` であり、必要な構造的事実は $x ↦ g (f x)$ が悪さを保つことだけです。
<!--/-->

<!--en-->
The construction is packaged in a module `Bernstein`{.Agda} taking exactly the classical data: the two types, the h-set structure of $A$, and the two injections, each given as a function together with its injectivity proof. Its first ingredient is the image predicate `imG x`, which asserts merely that some $y ∈ B$ satisfies $g y ≡ x$. No preimage is chosen here; the truncation ∥ ⋯ ∥₁ erases the witness and leaves a proposition, and `squash₁` is the certificate of that propositionhood.
<!--zh-->
整个构造被打包进模块 `Bernstein`{.Agda}，它恰好接受经典的数据：两个类型、$A$ 的 h-集合结构，以及两条单射，每条由函数与其单射性证明共同给出。第一个成分是像谓词 `imG x`，它仅仅断言存在某个 $y ∈ B$ 使 $g y ≡ x$。这里不选定任何原像；命题截断 ∥ ⋯ ∥₁ 抹去见证而留下一个命题，`squash₁` 就是该命题性的证书。
<!--ja-->
構成はモジュール `Bernstein`{.Agda} にまとめられ、受け取るのはまさに古典的なデータです。二つの型、$A$ の h-集合としての構造、そして二つの単射で、各々は関数とその単射性の証明の組として与えられます。最初の材料は像の述語 `imG x` で、ある $y ∈ B$ が $g y ≡ x$ を満たすことを単に (単に) 主張します。ここで原像は選ばれません。命題的切り詰め ∥ ⋯ ∥₁ が証人を消して命題だけを残し、`squash₁` がその命題性の証明書になります。
<!--/-->

```agda
module Bernstein {A B : Type ℓ} (setA : isSet A)
                 (f : A → B) (fi : (x y : A) → f x ≡ f y → x ≡ y)
                 (g : B → A) (gi : (x y : B) → g x ≡ g y → x ≡ y) where

  imG : A → hProp ℓ
  imG x = (∥ Σ[ y ∈ B ] (g y ≡ x) ∥₁ , squash₁)
```

<!--en-->
The base of the badness hierarchy says that x is bad at level zero when it is not in the image of g at all. Since a refutation of `imG x` is a map from `⟨ imG x ⟩` into the empty type, `C₀ x` is a function type, and it is a proposition because a function into a proposition is one. The step `C₊ C x` then says that x is reachable from a bad element by one backward step: merely there are $y ∈ B$ and $z ∈ A$ with $g y ≡ x$, $f z ≡ y$, and z already bad for C. Applying this operator iteratively from `C₀` gives `Cₙ`, so an inhabitant of `Cₙ n x` records an alternating chain x = g y, y = f z, z bad one level down, of length n.
<!--zh-->
坏性层级的基础说：当 x 完全不在 g 的像中时，x 在第零层是坏的。由于 `imG x` 的反驳是从 `⟨ imG x ⟩` 到空类型的映射，`C₀ x` 是函数类型；因为映入命题的函数仍是命题，所以它是命题。步进算子 `C₊ C x` 说：x 可从某个坏元素经一步后退到达，即仅仅存在 $y ∈ B$ 与 $z ∈ A$ 使 $g y ≡ x$、$f z ≡ y$、且 z 对 C 已经是坏的。从 `C₀` 出发迭代该算子得到 `Cₙ`，于是 `Cₙ n x` 的一个元记录了一条长为 n 的交错链：x = g y，y = f z，而 z 在低一层已是坏的。
<!--ja-->
悪さの階層の底辺は、x が g の像にまったく属さないとき x がレベル 0 で悪いと言います。`imG x` の反証とは `⟨ imG x ⟩` から空型への写像なので `C₀ x` は関数型であり、命題への写像はふたたび命題であるため、これは命題です。ステップ演算 `C₊ C x` は、x がどこかの悪い元から一段後退りで到達できること、つまり $g y ≡ x$、$f z ≡ y$、かつ z が C に対してすでに悪いような $y ∈ B$ と $z ∈ A$ が単に存在することを言います。`C₀` からこの演算を繰り返して `Cₙ` が得られ、したがって `Cₙ n x` の元は、x = g y、y = f z、z は一段下で悪い、という長さ n の交互の鎖を記録します。
<!--/-->

```agda

  C₀ : A → hProp ℓ
  C₀ x = ((⟨ imG x ⟩ → Empty.⊥) , isPropΠ (λ _ → isProp⊥))

  C₊ : (A → hProp ℓ) → A → hProp ℓ
  C₊ C x = (∥ Σ[ y ∈ B ] Σ[ z ∈ A ] ((g y ≡ x) × ((f z ≡ y) × ⟨ C z ⟩)) ∥₁ , squash₁)

  Cₙ : ℕ → A → hProp ℓ
```

<!--en-->
The two defining equations of `Cₙ` are computation rules: at index zero it is the base predicate, at the successor it applies the step once. The full badness proposition `C x` then truncates over all chain lengths at once: x is bad when merely some `Cₙ n x` holds. The truncation is essential here, since it collapses the infinitely many levels of the hierarchy into a single proposition at which excluded middle can later be applied.
<!--zh-->
`Cₙ` 的两条定义等式是计算规则：指标为零时是基础谓词，后继时施加一步。完整的坏性命题 `C x` 则对所有链长一次命题截断：只要某个 `Cₙ n x` 单纯成立，x 就是坏的。这里的命题截断是本质的，它把层级中无穷多个层折叠成一个命题，排中律随后可以施加于其上。
<!--ja-->
`Cₙ` の二つの定義等式は計算規則です。添字がゼロなら基底の述語であり、後続ならステップを一度適用します。完全な悪さの命題 `C x` は、すべての鎖の長さにわたって一度に命題的切り詰めします。ある `Cₙ n x` が単に成り立つなら x は悪くなります。ここでの命題的切り詰めは本質的で、階層の無限に多くの段を、後で排中律を適用できる単一の命題へと折りたたみます。
<!--/-->

```agda
  Cₙ zero = C₀
  Cₙ (suc n) = C₊ (Cₙ n)

  C : A → hProp ℓ
  C x = (∥ Σ[ n ∈ ℕ ] ⟨ Cₙ n x ⟩ ∥₁ , squash₁)
```

<!--en-->
Before using the hierarchy, one small bookkeeping lemma is recorded: a badness proof at any fixed level n yields a badness proof. Its content is simply that the pair (n , proof) is a witness for the truncated existential defining `C`, and ∣ ⋯ ∣₁ injects that witness into the truncation. Every later argument that produces a chain of some length will pass through this map.
<!--zh-->
在使用该层级之前，先记录一条小型簿记引理：任意固定层 n 上的坏性证明给出坏性证明。其内容只是：序对 (n , proof) 是定义 `C` 的命题截断存在式的见证，而 ∣ ⋯ ∣₁ 把该见证注入命题截断。此后每个产出某长度链的论证都要经过这个映射。
<!--ja-->
階層を使う前に、小さな簿記の補題を一つ記録します。任意の固定レベル n での悪さの証明は、悪さの証明を与えるというものです。内容は単純で、対 (n , proof) が `C` を定義する命題的切り詰めされた存在文の証人であり、∣ ⋯ ∣₁ がその証人を命題的切り詰めへ注入する、というだけです。後で何らかの長さの鎖を作る議論はすべて、この写像を通ります。
<!--/-->

```agda

  c-in : {x : A} {n : ℕ} → ⟨ Cₙ n x ⟩ → ⟨ C x ⟩
  c-in {x} {n} h = ∣ n , h ∣₁
```

<!--en-->
The one structural fact promised in the lead is now proved: if x is bad, so is g (f x). Given a chain of length n ending at x, one extends it by a single backward step, since x itself serves as the element z and f x as the element y: the required paths g (f x) ≡ g (f x) and f x ≡ f x are both reflexivity, and the old chain is the tail. The result is a chain of length suc n ending at g (f x). Because the input is truncated, the elimination `PT.rec` targets the propositionhood of the output, which is legitimate since `C (g (f x))` is a proposition.
<!--zh-->
引言承诺的那条结构事实现在得证：若 x 是坏的，则 g (f x) 也是坏的。给定一条长为 n、终于 x 的链，只需向后延伸一步：x 自身充当元素 z，f x 充当元素 y，所需的路径 g (f x) ≡ g (f x) 与 f x ≡ f x 都是自反性，而旧链是尾部。结果是一条长为 suc n、终于 g (f x) 的链。由于输入是命题截断的，消去 `PT.rec` 以输出的命题性为目标，这在 `C (g (f x))` 是命题时是合法的。
<!--ja-->
冒頭で約束した構造的事実がここで証明されます。x が悪ければ g (f x) も悪くなります。長さ n で x で終わる鎖が与えられれば、一段後ろへ延ばすだけです。x 自身が元 z として、f x が元 y として働き、必要なパス g (f x) ≡ g (f x) と f x ≡ f x はどちらも反射性であり、古い鎖が尾になります。結果は長さ suc n で g (f x) で終わる鎖です。入力が命題的切り詰めされているため、消去 `PT.rec` は出力の命題性を対象とします。`C (g (f x))` は命題なのでこれは正当です。
<!--/-->

```agda

  gf-closed : {x : A} → ⟨ C x ⟩ → ⟨ C (g (f x)) ⟩
  gf-closed {x} = PT.rec (snd (C (g (f x)))) go
    where
    go : Σ[ n ∈ ℕ ] ⟨ Cₙ n x ⟩ → ⟨ C (g (f x)) ⟩
    go (n , cx) = c-in {x = g (f x)} {n = suc n} ∣ f x , x , (refl , (refl , cx)) ∣₁
```

<!--en-->
Closure under g ∘ f tells us badness propagates forward, but to route elements through h we also need to look one level backward: every badness proof either bottoms out at level zero, or x is of the form g (f z) with z bad. This is exactly what `C-view` delivers. The target is itself truncated, so eliminating into it is unproblematic even though the case analysis on the chain length n is genuine data.
<!--zh-->
g ∘ f 下的封闭性告诉我们坏性向前传播，但为了把元素经 h 路由，我们还需要向回看一层：每个坏性证明要么在第零层见底，要么 x 形如 g (f z) 且 z 是坏的。这正是 `C-view` 所交付的。目标本身是命题截断的，因此即便对链长 n 的情形分析是真正的数据，向其中消去也没有问题。
<!--ja-->
g ∘ f による閉性は悪さが前へ伝わることを教えますが、元を h で振り分けるには一段後ろも見る必要があります。悪さの証明は、レベル 0 で底を突くか、さもなくば x は g (f z) の形で z が悪いかのどちらかです。これこそ `C-view` が与えるものです。対象自身が命題的切り詰めされているので、鎖の長さ n についてのケース分析が実際のデータであっても、そこへの消去は問題ありません。
<!--/-->

```agda

  C-view : {x : A} → ⟨ C x ⟩
         → ∥ (⟨ C₀ x ⟩ ⊎ (Σ[ z ∈ A ] ((g (f z) ≡ x) × ⟨ C z ⟩))) ∥₁
  C-view {x} = PT.rec squash₁ go
    where
```

<!--en-->
The proof splits on the recorded length. At length zero the chain simply asserts that x is outside the image of g, which is the left disjunct verbatim. At length suc n the stored witness is a triple y, z with g y ≡ x, f z ≡ y and a length-n badness proof for z; composing the two paths by way of g gives g (f z) ≡ x, and the shorter chain is included with `c-in`. The right disjunct is exactly the pair (z , that path , that shorter proof), truncated. This lemma is the surjectivity engine later: applied at g y, it either refutes badness outright or produces the preimage z.
<!--zh-->
证明对记录的长度作情形分裂。长度为零时，链只是断言 x 在 g 的像之外，这恰是左析取支。长度为 suc n 时，保存的见证是三元组 y, z，满足 g y ≡ x、f z ≡ y 以及 z 的长为 n 的坏性证明；两条路径经 g 复合得 g (f z) ≡ x，更短的链由 `c-in` 纳入。右析取支恰是序对 (z，该路径，该更短证明) 的命题截断。这条引理是后面满性证明的核心：用在 g y 处，它要么直接反驳坏性，要么给出原像 z。
<!--ja-->
証明は記録された長さについて場合分けします。長さ 0 なら鎖は x が g の像の外であると主張するだけで、これは左の選言肢そのものです。長さ suc n なら保存された証人は y と z の組で、g y ≡ x、f z ≡ y、そして z の長さ n の悪さの証明が成り立ちます。二つのパスを g を経由して合成すれば g (f z) ≡ x が得られ、より短い鎖は `c-in` で取り込まれます。右の選言肢はちょうど対 (z，そのパス，その短い証明) の命題的切り詰めです。この補題は後の全射性の中核です。g y に適用すると、悪さを直接反証するか、さもなくば原像 z を作り出します。
<!--/-->

```agda
    go : Σ[ n ∈ ℕ ] ⟨ Cₙ n x ⟩ → ∥ (⟨ C₀ x ⟩ ⊎ (Σ[ z ∈ A ] ((g (f z) ≡ x) × ⟨ C z ⟩))) ∥₁
    go (zero , c0) = ∣ inl c0 ∣₁
    go (suc n , cs) = PT.map inr (PT.map (λ { (y , z , gy , fz , cz) →
        z , ((cong g fz ∙ gy) , c-in {x = z} {n = n} cz) }) cs)
```

<!--en-->
The second use of excluded middle converts goodness into image membership. Suppose x is good, in the strong sense that `C x` admits a refutation. Deciding the proposition `imG x` gives either a preimage, which is what we want, or a refutation of image membership, that is, a proof of `C₀ x`. But level zero implies badness via `c-in`, contradicting the assumed refutation of `C x`; from that contradiction anything follows. So `notC→imG` produces an inhabitant of `⟨ imG x ⟩`, still merely, not yet a chosen preimage.
<!--zh-->
排中律的第二次使用把好性转成像属于关系。设 x 是好的，取强意义：`C x` 容许一个反驳。判定命题 `imG x` 要么给出原像，这正是我们想要的，要么给出像属于的反驳，即 `C₀ x` 的证明。但第零层经 `c-in` 蕴含坏性，与假设的 `C x` 的反驳矛盾；由该矛盾可推出任何东西。于是 `notC→imG` 产出 `⟨ imG x ⟩` 的一个元，仍只表明原像存在，还没有选定原像。
<!--ja-->
排中律の二度目の使用は、良さを像への所属に変えます。x が良いとします。ここでは `C x` が反証を許すという強い意味で取ります。命題 `imG x` を判定すると、原像が得られるか、望むところです。あるいは像への所属の反証、すなわち `C₀ x` の証明が得られます。しかしレベル 0 は `c-in` を経由して悪さを含意し、仮定された `C x` の反証と矛盾します。この矛盾から何でも出ます。したがって `notC→imG` は `⟨ imG x ⟩` の元を作りますが、それはまだ存在することだけを述べており、まだ原像は選ばれていません。
<!--/-->

```agda

  notC→imG : {x : A} → (⟨ C x ⟩ → Empty.⊥) → ⟨ imG x ⟩
  notC→imG {x} nC = Sum.rec {A = ⟨ imG x ⟩} {B = ⟨ imG x ⟩ → Empty.⊥} {C = ⟨ imG x ⟩}
    (λ h → h) (λ nC₀ → Empty.rec (nC (c-in {n = zero} nC₀)))
    (lem (imG x))
```

<!--en-->
To turn the mere image membership into a chosen preimage, we may eliminate the truncation into the fiber type Σ[ y ∈ B ] (g y ≡ x) itself, provided that type is a proposition. This is where the hypotheses on g and A earn their keep: injectivity of g shows any two preimages y and y' are equal, using the paths p and p' to g x, and the h-set structure of A makes the resulting equality in A a proposition, which `Σ≡Prop` then extends to the whole pair. Note that the h-set assumption is needed exactly here and nowhere else in the construction.
<!--zh-->
为了把单纯的像属于变成选定的原像，可以把命题截断直接消去到纤维类型 Σ[ y ∈ B ] (g y ≡ x) 本身，只要该类型是命题。这正是 g 与 A 上的假设发挥作用之处：g 的单射性利用到 g x 的两条路径 p 与 p′ 证明任意两个原像 y 与 y′ 相等，而 A 的 h-集合结构使 A 中所得的相等成为命题，`Σ≡Prop` 再把这一点扩展到整个序对。注意 h-集合假设恰好只在这里、构造中的其他地方都不需要。
<!--ja-->
単なる像への所属を選ばれた原像に変えるには、その繊維型 Σ[ y ∈ B ] (g y ≡ x) 自身が命題である限り、命題的切り詰めをその型へ直接消去できます。ここで g と A に関する仮定が効きます。g の単射性は、g x へのパス p と p′ を使って任意の二つの原像 y と y′ が等しいことを示し、A の h-集合としての構造が A における等式を命題にするので、`Σ≡Prop` がこれを対全体へ拡げます。h-集合の仮定が必要なのはまさにこの一点だけで、構成の他のどこでもありません。
<!--/-->

```agda

  fiberG-prop : (x : A) → isProp (Σ[ y ∈ B ] (g y ≡ x))
  fiberG-prop x (y , p) (y' , p') = Σ≡Prop {A = B} {B = λ y → g y ≡ x}
    (λ y → setA (g y) x) (gi y y' (p ∙ sym p'))
```

<!--en-->
With fiber propositionhood in hand, `fiberG` is the elimination of the truncated image statement into the fiber type: since the target is a proposition, `PT.rec` applies with the identity on fibers as the action. This is the first point in the argument where a chosen preimage exists as data rather than merely, and it was unlocked by excluded middle plus the h-set structure, not by any property of the truncation alone.
<!--zh-->
有了纤维的命题性，`fiberG` 就是把命题截断的像陈述消去到纤维类型：由于目标是命题，`PT.rec` 以纤维上的恒等映射为作用即可应用。这是论证中第一个选定原像作为数据而非仅仅存在的位置，而打开它的正是排中律加 h-集合结构，不是命题截断自身的任何性质。
<!--ja-->
繊維の命題性が手に入れば、`fiberG` は命題的切り詰めされた像の主張を繊維型へ消去するものです。対象が命題なので、`PT.rec` は繊維上の恒等写像を作用として適用できます。これは議論の中で、選ばれた原像が単にではなくデータとして存在する最初の地点です。それを開いたのは排中律と h-集合としての構造であって、命題的切り詰めそのものの性質ではありません。
<!--/-->

```agda

  fiberG : (x : A) → ⟨ imG x ⟩ → Σ[ y ∈ B ] (g y ≡ x)
  fiberG x = PT.rec (fiberG-prop x) (λ w → w)
```

<!--en-->
For a good element x, the chosen preimage can now be named `ginv x`: it is the first component of the fiber produced by `fiberG` from `notC→imG`. Its spec `ginv-spec` records that g (ginv x) ≡ x, taken from the second component of the same fiber. So on the good side the map h will send x back to a point of B whose g-image is exactly x, as an inverse segment of g deserves.
<!--zh-->
对好元素 x，选定的原像现在可以命名为 `ginv x`：它是 `fiberG` 由 `notC→imG` 产出的纤维的第一个分量。其规格 `ginv-spec` 记录 g (ginv x) ≡ x，取自同一纤维的第二个分量。于是在好的一侧，h 将把 x 送回 B 中一个 g-像恰为 x 的点，这正是作为 g 的逆片段应有的行为。
<!--ja-->
良い元 x に対しては、選ばれた原像を `ginv x` と名付けられます。これは `notC→imG` から `fiberG` が作る繊維の第 1 成分です。仕様 `ginv-spec` は g (ginv x) ≡ x を記録し、同じ繊維の第 2 成分から取られます。したがって良い側では h は x を、g による像がちょうど x である B の点へ送り返します。g の逆の断片としての当然の振る舞いです。
<!--/-->

```agda

  ginv : {x : A} → (⟨ C x ⟩ → Empty.⊥) → B
  ginv {x} nC = fiberG x (notC→imG nC) .fst

  ginv-spec : {x : A} (nC : ⟨ C x ⟩ → Empty.⊥) → g (ginv nC) ≡ x
  ginv-spec {x} nC = fiberG x (notC→imG nC) .snd
```

<!--en-->
The candidate bijection h is now defined on a hypothetical verdict rather than on A directly: given x and a decision d of the badness proposition `C x`, it sends x to f x in the bad case and to `ginv x` in the good case. Working with the verdict as an explicit argument keeps the case analysis honest, and the two lemmas that follow, injectivity and surjectivity relative to a verdict, will be combined with the actual decision supplied by `lem` at the end of the section.
<!--zh-->
候选双射 h 现在定义在假想的裁决上，而非直接定义在 A 上：给定 x 与坏性命题 `C x` 的判定 d，坏情形送 x 到 f x，好情形送到 `ginv x`。把裁决作为显式参数处理使情形分析保持诚实；随后两条引理，即相对于裁决的单射性与满射性，将在本节末与 `lem` 提供的实际判定相结合。
<!--ja-->
候補となる全単射 h は、A に直接ではなく仮想的な判定の上で定義されます。x と悪さの命題 `C x` の判定 d が与えられると、悪いの場合は x を f x へ、良いの場合は `ginv x` へ送ります。判定を明示的な引数として扱うことでケース分析は誠実に保たれ、続く二つの補題、判定に相対的な単射性と全射性は、節の最後で `lem` が与える実際の判定と結合されます。
<!--/-->

```agda

  h : (x : A) → ⟨ C x ⟩ ⊎ (⟨ C x ⟩ → Empty.⊥) → B
  h x (inl _) = f x
  h x (inr nC) = ginv nC
```

<!--en-->
Injectivity of h is proved by four cases on the pair of verdicts. When both sides are bad, h is f on both, and the injectivity of f finishes immediately. When x is bad and x' good, the hypothesis h x dx ≡ h x' dx' says g (f x) ≡ ginv x', hence g (g (f x)) ≡ x' after applying g and the spec of ginv. Since badness propagates along g ∘ f, x bad makes g (f x) bad; transporting the badness of g (f x) along that path with `subst` makes x' bad, contradicting the verdict that x' is good.
<!--zh-->
h 的单射性按裁决对作四种情形证明。两侧都坏时，h 两侧都是 f，由 f 的单射性立即完成。当 x 坏而 x′ 好时，假设 h x dx ≡ h x′ dx′ 说 g (f x) ≡ ginv x′，施加 g 并用 ginv 的规格得 g (g (f x)) ≡ x′。由于坏性沿 g ∘ f 传播，x 坏使 g (f x) 坏；用 `subst` 把 g (f x) 的坏性沿该路径搬运即得 x′ 坏，与 x′ 好的裁决矛盾。
<!--ja-->
h の単射性は判定の対について四つの場合で証明します。両側が悪いのときは h は両側で f であり、f の単射性ですぐ終わります。x が悪く x′ が良いのとき、仮定 h x dx ≡ h x′ dx′ は g (f x) ≡ ginv x′ を言い、g を施して ginv の仕様を使えば g (g (f x)) ≡ x′ が得られます。悪さは g ∘ f に沿って伝わるので、x が悪ければ g (f x) も悪くなります。`subst` で g (f x) の悪さをそのパスに沿って輸送すれば x′ が悪いとなり、x′ が良いという判定と矛盾します。
<!--/-->

```agda

  h-inj : (x x' : A) (dx : ⟨ C x ⟩ ⊎ (⟨ C x ⟩ → Empty.⊥)) (dx' : ⟨ C x' ⟩ ⊎ (⟨ C x' ⟩ → Empty.⊥))
        → h x dx ≡ h x' dx' → x ≡ x'
  h-inj x x' (inl cx) (inl cx') e = fi x x' e
  h-inj x x' (inl cx) (inr nCx') e =
    Empty.rec (nCx' (subst (λ w → ⟨ C w ⟩) (cong g e ∙ ginv-spec nCx') (gf-closed {x = x} cx)))
```

<!--en-->
The mirror case, x good and x' bad, is symmetric: the transport runs along the reversed path and kills x instead. In the final case both sides are good, so h is ginv on both and the equation reads ginv x ≡ ginv x'. Applying g turns it into g (ginv x) ≡ g (ginv x'), and chaining the two specs of ginv around it yields x ≡ x' directly. No h-set assumption is used anywhere in this lemma; injectivity is pure case analysis on verdicts.
<!--zh-->
镜像情形，x 好 x′ 坏，是对称的：搬运沿反向路径进行，被消灭的是 x。最后一种情形两侧都好，h 两侧都是 ginv，等式读作 ginv x ≡ ginv x′。施加 g 把它变成 g (ginv x) ≡ g (ginv x′)，两侧串上 ginv 的两条规格便直接得 x ≡ x′。这条引理处处未用 h-集合假设；单射性纯粹是对裁决的情形分析。
<!--ja-->
鏡像の場合、x が良く x′ が悪いのときは対称です。輸送は逆向きのパスに沿って行われ、消されるのは x の方です。最後の場合は両側が良く、h は両側で ginv となり、等式は ginv x ≡ ginv x′ と読めます。g を施せば g (ginv x) ≡ g (ginv x′) となり、その前後で ginv の二つの仕様をつなげば x ≡ x′ が直接得られます。この補題では h-集合の仮定はどこにも使われず、単射性は判定についての純粋なケース分析です。
<!--/-->

```agda
  h-inj x x' (inr nCx) (inl cx') e =
    Empty.rec (nCx (subst (λ w → ⟨ C w ⟩) (sym (cong g e) ∙ ginv-spec nCx) (gf-closed {x = x'} cx')))
  h-inj x x' (inr nCx) (inr nCx') e = sym (ginv-spec nCx) ∙ cong g e ∙ ginv-spec nCx'
```

<!--en-->
Surjectivity relative to a verdict is stated for each y ∈ B, with the verdict taken on the element g y of A rather than on an element of B. In the good case the preimage is simply g y itself: it is good by assumption, h sends it to `ginv (g y)`, and the spec of ginv together with injectivity of g identifies that value with y. The witness is packaged as a truncated pair since the final theorem only claims mere surjectivity.
<!--zh-->
相对于裁决的满射性对每个 y ∈ B 陈述，裁决取在 A 的元素 g y 上，而非 B 的元素上。好情形下原像就是 g y 自身：按假设它是好的，h 把它送到 `ginv (g y)`，再用 ginv 的规格与 g 的单射性把该值等同于 y。见证被打包成命题截断序对，因为最终定理只宣称仅仅存在的满射性。
<!--ja-->
判定に相対的な全射性は各 y ∈ B について述べられ、判定は B の元ではなく A の元 g y に対して取られます。良いの場合は原像は単純に g y 自身です。仮定によりそれは良く、h はそれを `ginv (g y)` に送り、ginv の仕様と g の単射性でその値を y と同一視します。証人は命題的切り詰めされた対としてまとめられます。最終定理が単なる全射性しか主張しないからです。
<!--/-->

```agda

  h-surj : (y : B) (d : ⟨ C (g y) ⟩ ⊎ (⟨ C (g y) ⟩ → Empty.⊥))
         → ∥ Σ[ x ∈ A ] Σ[ dx ∈ ⟨ C x ⟩ ⊎ (⟨ C x ⟩ → Empty.⊥) ] (h x dx ≡ y) ∥₁
  h-surj y (inr nCgy) = ∣ g y , inr nCgy , gi (ginv nCgy) y (ginv-spec nCgy) ∣₁
```

<!--en-->
In the bad case for g y, `C-view` decomposes the badness proof into two alternatives. The first says g y is outside the image of g, but y itself witnesses its image membership with the path reflexivity, a contradiction that yields anything, in particular the required truncated statement. The second produces z ∈ A with g (f z) ≡ g y and z bad; then z is a preimage, for h z = f z and g (f z) equals g y, so injectivity of g identifies f z with y. Both branches exhibit their witnesses inside one truncation, so no verdict other than the one already assumed is consumed.
<!--zh-->
g y 是坏的情形下，`C-view` 把坏性证明分解为两个选项。第一个说 g y 在 g 的像之外，但 y 自己用自反路径见证了它的像属于关系，这矛盾可推出任何东西，特别是所需的命题截断陈述。第二个给出 z ∈ A 使 g (f z) ≡ g y 且 z 是坏的；此时 z 是原像，因为 h z = f z 且 g (f z) 等于 g y，再由 g 的单射性把 f z 等同于 y。两个分支都在单个命题截断内展示其见证，因此除已假设的裁决外不消耗其他裁决。
<!--ja-->
g y が悪いの場合は `C-view` が悪さの証明を二つの選択肢に分解します。第一は g y が g の像の外にあるというもので、しかし y 自身がパス反射律で像への所属の証人となり、矛盾から何でも、特に必要な命題的切り詰めされた主張が出ます。第二は g (f z) ≡ g y かつ z が悪いような z ∈ A を作り出します。このとき z は原像です。h z = f z であり g (f z) は g y に等しく、g の単射性で f z を y と同一視できるからです。両方の枝が証人を一つの命題的切り詰めの中で示すので、すでに仮定した判定以外の判定は消費されません。
<!--/-->

```agda
  h-surj y (inl cgy) = PT.rec squash₁
    (λ { (inl c0) → Empty.rec (c0 ∣ y , refl ∣₁) ; (inr (z , gfy , cz)) → ∣ z , inl cz , gi (f z) y gfy ∣₁ })
    (C-view {x = g y} cgy)
```

<!--en-->
The final lemma answers an objection to the whole design: h was defined relative to a verdict, yet the theorem needs a single function on A. `h-cons` says the choice of verdict does not matter, for any fixed x the two outputs are equal. Both bad gives reflexivity, either mixed case is contradictory since one verdict refutes the other's witness, and both good reduces to the uniqueness of the chosen preimage: the two fibers produced by `fiberG` are equal because the fiber type is a proposition, and taking first components preserves that equality by congruence. This consistency is what makes the verdict-dependent construction a genuine definition of a map.
<!--zh-->
最后一条引理回应针对整个设计的一个异议：h 是相对于裁决定义的，而定理需要 A 上的单个函数。`h-cons` 说裁决的选择无关紧要：对固定的 x，两个输出相等。都坏时是自反性；混合情形是矛盾的，因为一个裁决反驳另一个的见证；都好时归结为选定原像的唯一性：`fiberG` 产出的两个纤维因纤维类型是命题而相等，取第一分量经合质性保持该相等。正是这种一致性使依赖裁决的构造成为映射的真正定义。
<!--ja-->
最後の補題は設計全体への異議に答えます。h は判定に相対的に定義されましたが、定理には A 上の単一の関数が必要です。`h-cons` は判定の選び方が問題にならない、固定された x に対しては二つの出力が等しい、と言います。両方悪ければ反射律であり、どちらかが混在する場合は一方の判定が他方の証人を反証するので矛盾し、両方良いの場合は選ばれた原像の一意性に帰着します。`fiberG` が作る二つの繊維は、繊維型が命題であるため等しく、第 1 成分を取ることは合同性によってその等式を保ちます。この整合性こそが、判定依存の構成を写像の正当な定義にしているのです。
<!--/-->

```agda

  h-cons : (x : A) (dx dx' : ⟨ C x ⟩ ⊎ (⟨ C x ⟩ → Empty.⊥)) → h x dx ≡ h x dx'
  h-cons x (inl cx) (inl cx') = refl
  h-cons x (inl cx) (inr nCx') = Empty.rec (nCx' cx)
  h-cons x (inr nCx) (inl cx) = Empty.rec (nCx cx)
  h-cons x (inr nCx) (inr nCx') = cong fst (fiberG-prop x (fiberG x (notC→imG nCx)) (fiberG x (notC→imG nCx')))
```

<!--en-->
With consistency established, the verdict can be fed in once and for all. The next three lines assemble the theorem.
<!--zh-->
一致性建立之后，裁决可以一次性给定。接下来三行组装出定理。
<!--ja-->
整合性が確立されれば、判定は一度だけ与えればよくなります。続く三行で定理が組み上がります。
<!--/-->

```agda

  ĥ : A → B
```

<!--en-->
The map `ĥ` is h applied to the canonical verdict `lem (C x)`: excluded middle decides the badness of each x, and h-cons guarantees that any other decision would have produced the same value. This is where the module's hypothesis `lem` is consumed for the definition itself.
<!--zh-->
映射 `ĥ` 是 h 施加于典范裁决 `lem (C x)`：排中律判定每个 x 的坏性，而 h-cons 保证任何其他判定都会产出相同的值。这里正是模块假设 `lem` 被定义本身消耗之处。
<!--ja-->
写像 `ĥ` は h を標準的な判定 `lem (C x)` に適用したものです。排中律が各 x の悪さを判定し、h-cons が他のどんな判定でも同じ値になると保証します。ここでモジュールの仮定 `lem` が定義そのものとして消費されます。
<!--/-->

```agda
  ĥ x = h x (lem (C x))
```

<!--en-->
Injectivity transfers verbatim from the relative version, since the canonical verdicts are particular choices of the verdict arguments: `ĥ-inj x x' e` is exactly `h-inj` at those verdicts.
<!--zh-->
单射性从相对版本逐字转移，因为典范裁决正是裁决参数的特殊选取：`ĥ-inj x x' e` 恰是这些裁决处的 `h-inj`。
<!--ja-->
単射性は相対版からそのまま移ります。標準的な判定は判定引数の特定の選び方にすぎないからです。`ĥ-inj x x' e` はまさにそれらの判定における `h-inj` です。
<!--/-->

```agda

  ĥ-inj : (x x' : A) → ĥ x ≡ ĥ x' → x ≡ x'
  ĥ-inj x x' e = h-inj x x' (lem (C x)) (lem (C x')) e
```

<!--en-->
Surjectivity needs one extra step. The relative lemma `h-surj` applied at the canonical verdict for g y provides a truncated triple x, dx, and a path h x dx ≡ y, but its first two components speak about the hypothetical h x dx rather than `ĥ x`. Rewriting along `h-cons x dx (lem (C x))`, which identifies the two values, and prepending the symmetric path converts the triple into a witness of `ĥ x ≡ y`. The whole statement remains truncated: the theorem asserts that a preimage merely exists.
<!--zh-->
满射性需要额外一步。相对引理 `h-surj` 施加于 g y 的典范裁决，给出命题截断的三元组 x、dx 及路径 h x dx ≡ y，但其前两个分量谈的是假想的 h x dx 而非 `ĥ x`。沿 `h-cons x dx (lem (C x))` 改写，它识别这两个值，再前置对称路径，就把三元组转成 `ĥ x ≡ y` 的见证。整个陈述仍是命题截断的：定理断言原像仅仅存在。
<!--ja-->
全射性にはもう一段必要です。g y に対する標準的な判定に相対補題 `h-surj` を適用すると、命題的切り詰めされた三つ組 x、dx とパス h x dx ≡ y が得られますが、その最初の二つの成分は仮想的な h x dx についてのもので、`ĥ x` についてのものではありません。二つの値を同一視する `h-cons x dx (lem (C x))` に沿って書き換え、対称パスを前につなげれば、三つ組は `ĥ x ≡ y` の証人に変わります。主張全体は命題的切り詰めされたままです。定理は原像が単に存在すると主張するだけです。
<!--/-->

```agda

  ĥ-surj : (y : B) → ∥ Σ[ x ∈ A ] (ĥ x ≡ y) ∥₁
  ĥ-surj y = PT.map (λ { (x , dx , e) → x , sym (h-cons x dx (lem (C x))) ∙ e })
    (h-surj y (lem (C (g y))))
```

<!--en-->
The abstract construction now applies to the cumulative hierarchy itself. Each element a of V comes with a member type ⟪ a ⟫, the type of its members. The Bernstein construction asks for an h-set structure on its first type, so the first step is to certify that ⟪ a ⟫ is one. The embedding ⟪ a ⟫↪ sends each member index to the member it indexes inside V; since V is a set and the embedding is an embedding, its domain inherits set-ness. With that single fact, two mutual injections between ⟪ a ⟫ and ⟪ b ⟫ produce a bijection packaged as a dependent triple.
<!--zh-->
抽象构造现在应用于累积层级本身。V 的每个元素 a 都带有成员类型 ⟪ a ⟫，即其成员的类型。Bernstein 构造要求第一个类型具有 h-集合结构，所以第一步是证明 ⟪ a ⟫ 是 h-集合。嵌入 ⟪ a ⟫↪ 把每个成员指标送到它在 V 内所指标的成员；由于 V 是集合且该映射是嵌入，其定义域继承了集合性。有了这一条事实，⟪ a ⟫ 与 ⟪ b ⟫ 之间的两条互逆单射便产生一个打包成依赖三元组的双射。
<!--ja-->
抽象的な構成を、いよいよ累積階層そのものに適用します。V の各元 a はメンバー型 ⟪ a ⟫、すなわちそのメンバーの型を伴います。Bernstein の構成は第一の型が h-集合であることを要求するので、最初の一歩は ⟪ a ⟫ がそうであることの証明です。埋め込み ⟪ a ⟫↪ は各メンバーの指標を、V の中でそれが指すメンバーへ送ります。V は集合であり、この写像は埋め込みなので、その定義域は集合性を受け継ぎます。この一事実があれば、⟪ a ⟫ と ⟪ b ⟫ の間の相互の単射から、依存する三つ組としてまとめられた全単射が得られます。
<!--/-->

<!--en-->
The set-ness certificate composes two imported facts. The map ⟪ a ⟫↪ is an embedding into V, meaning all its fibers are propositions, and the hierarchy V is a set by its constructor setIsSet. A type that embeds into a set is itself a set, since equality in the domain can be compared after applying the embedding. The signature that follows then states the set-theoretic corollary in the same shape as the abstract theorem: injections f from ⟪ a ⟫ to ⟪ b ⟫ and g back, each with its injectivity proof, taken as explicit hypotheses.
<!--zh-->
集合性证书由两条已导入的事实复合而成。映射 ⟪ a ⟫↪ 是到 V 的嵌入，即其所有纤维都是命题；而层级 V 经其构造子 setIsSet 是集合。嵌入到集合中的类型自身是集合，因为定义域中的相等可以在施加该映射之后比较。随后的签名以与抽象定理相同的形状陈述集合论推论：从 ⟪ a ⟫ 到 ⟪ b ⟫ 的单射 f 与返回的单射 g，连同各自的单射性证明，作为显式假设。
<!--ja-->
集合性の証明書は、取り込まれた二つの事実を合成したものです。写像 ⟪ a ⟫↪ は V への埋め込み、つまりすべての繊維が命題であるような写像であり、階層 V はその構成子 setIsSet により集合です。集合へ埋め込まれる型はそれ自身集合になります。定義域の等式は埋め込みを施した後に比較できるからです。続くシグニチャは、抽象定理と同じ形で集合論的な帰結を述べます。⟪ a ⟫ から ⟪ b ⟫ への単射 f と戻りの単射 g、それぞれの単射性の証明とともに、明示的な仮定として取られます。
<!--/-->

```agda
small-set : (a : V ℓ) → isSet (⟪ a ⟫)
small-set a = Embedding-into-isSet→isSet (⟪ a ⟫↪ , isEmb⟪ a ⟫↪) setIsSet

cantor-bernstein : (a b : V ℓ) (f : ⟪ a ⟫ → ⟪ b ⟫)
    → ((x y : ⟪ a ⟫) → f x ≡ f y → x ≡ y)
    → (g : ⟪ b ⟫ → ⟪ a ⟫) → ((x y : ⟪ b ⟫) → g x ≡ g y → x ≡ y)
```

<!--en-->
The result type is an explicit dependent triple rather than a record: a function h from ⟪ a ⟫ to ⟪ b ⟫, its injectivity as a proposition-valued component, and mere surjectivity, asserting for each y of ⟪ b ⟫ a truncated preimage. The asymmetry between the two side conditions is deliberate and mirrors the abstract theorem: injectivity is stated as honest data, surjectivity only as mere existence. Nothing in the statement quantifies over stages or membership of the hierarchy; everything happens inside the two member types.
<!--zh-->
结果类型是显式的依赖三元组而非记录：从 ⟪ a ⟫ 到 ⟪ b ⟫ 的函数 h，其单射性作为命题值分量，以及仅仅存在的满射性，即对 ⟪ b ⟫ 的每个 y 断言一个命题截断的原像。两侧条件之间的不对称是刻意的，与抽象定理一致：单射性作为真正的数据陈述，满射性只作为单纯存在陈述。陈述中没有任何对层级的层或属于关系的量化；一切都发生在两个成员类型内部。
<!--ja-->
結果の型はレコードではなく明示的な依存する三つ組です。⟪ a ⟫ から ⟪ b ⟫ への関数 h、その単射性を命題値の成分として、そして単なる全射性、すなわち ⟪ b ⟫ の各 y に対する命題的切り詰めされた原像の主張です。二つの側条件の非対称性は意図的なもので、抽象定理と呼応します。単射性は正味のデータとして、全射性は単なる存在として述べられます。主張のどこにも階層の段や所属についての量化はなく、すべては二つのメンバー型の内部で起こります。
<!--/-->

```agda
    → Σ[ h ∈ (⟪ a ⟫ → ⟪ b ⟫) ]
        (((x y : ⟪ a ⟫) → h x ≡ h y → x ≡ y)
      × ((y : ⟪ b ⟫) → ∥ Σ[ x ∈ ⟪ a ⟫ ] (h x ≡ y) ∥₁))
cantor-bernstein a b f fi g gi = M.ĥ , ( M.ĥ-inj , M.ĥ-surj )
  where
```

<!--en-->
The proof is a single instantiation. Instantiating the module `Bernstein` at A = ⟪ a ⟫ and B = ⟪ b ⟫, with the set-ness certificate supplied for A and the two injections passed through unchanged, exposes the components ĥ, ĥ-inj and ĥ-surj; the definition assembles them into the triple. All the work of the previous section is reused without modification.
<!--zh-->
证明是一次单独的实例化。把模块 `Bernstein` 在 A = ⟪ a ⟫、B = ⟪ b ⟫ 处实例化，为 A 提供集合性证书，两条单射原样传入，即暴露出分量 ĥ、ĥ-inj 与 ĥ-surj；定义把它们组装成三元组。上一节的全部工作未经修改地被复用。
<!--ja-->
証明は一回のインスタンス化だけです。モジュール `Bernstein` を A = ⟪ a ⟫、B = ⟪ b ⟫ で実例化し、A に集合性の証明書を供給し、二つの単射をそのまま渡せば、成分 ĥ、ĥ-inj、ĥ-surj が現れます。定義はそれらを三つ組に組み立てます。前節の仕事のすべてが、変更なしに再利用されるのです。
<!--/-->

```agda
  module M = Bernstein {A = ⟪ a ⟫} {B = ⟪ b ⟫} (small-set a) f fi g gi
```

<!--en-->
The corollary above hard-wires the member types of V. A more reusable form keeps the setting abstract: a carrier `C` of codes, an assignment `P` of a small type to each code, and a relation `R a b` expressing that a codes an injection from P a to P b. What ties the abstraction to the previous section is the readback `read`: from an inhabitant of R a b it extracts an actual function together with its injectivity proof. Given one such readback in each direction, the Bernstein construction applies verbatim. Two entry points are provided, one taking the pair of coded injections as data and one taking it merely, with the bijection then merely existing as well.
<!--zh-->
上面的推论把 V 的成员类型写死了。更可复用的形式使设置保持抽象：一个码的载体 `C`、给每个码指派一个小类型的 `P`，以及表达「a 编码了从 P a 到 P b 的单射」的关系 `R a b`。把这一抽象与上一节联系起来的是读回 `read`：从 R a b 的一个元提取出真实的函数及其单射性证明。给定两个方向各一条这样的读回，Bernstein 构造便可逐字应用。这里提供两个入口：一个把这对编码单射作为数据，一个单纯地接受它，此时双射也单纯地存在。
<!--ja-->
上の帰結は V のメンバー型に固定されています。より再利用しやすい形は、設定を抽象的に保ちます。符号の台 `C`、各符号に小さな型を割り当てる `P`、そして a が P a から P b への単射を符号化していることを表す関係 `R a b` です。この抽象を前節と結びつけるのが読み戻し `read` です。R a b の元から、実際の関数とその単射性の証明を取り出します。両方向にそのような読み戻しがあれば、Bernstein の構成はそのまま適用できます。入口は二つ用意されています。一方は符号化された単射の対をデータとして受け取り、もう一方は単なる存在として受け取り、その場合は全単射も単に存在するだけになります。
<!--/-->

<!--en-->
The parameters spell out the exact strength required. The carrier C lives at its own level ℓ₁ and the relation R at ℓ₂, so codes and their relations need not be small; what must be small is each P a, at the fixed level ℓ where excluded middle is available. For every a, P a is assumed an h-set, mirroring the set-ness hypothesis of the Bernstein module. The relation R itself is left completely arbitrary as a type: nothing about it is assumed beyond the readback, which from an inhabitant of R a b returns a pair whose first component is a function P a → P b and whose second is that function's injectivity proof. In particular, the extracted injection is honest data, not a truncated existence.
<!--zh-->
参数恰好列出所需的强度。载体 C 住在自己的层级 ℓ₁，关系 R 在 ℓ₂，因此码及其关系不必是小的；必须小的是每个 P a，它住在排中律可用的固定层级 ℓ。对每个 a，假设 P a 是 h-集合，对应 Bernstein 模块的集合性假设。关系 R 本身作为类型完全任意：除读回外对它不作任何假设，读回从 R a b 的元返回一个序对，第一分量是函数 P a → P b，第二分量是该函数的单射性证明。特别地，提取出的单射是真正的数据，不是命题截断的存在。
<!--ja-->
パラメータは必要な強さを正確に列挙します。台 C はそれ自身のレベル ℓ₁ に、関係 R は ℓ₂ に住むので、符号やその関係は小さくなくて構いません。小さくなければならないのは各 P a で、排中律が使える固定レベル ℓ に住みます。各 a について P a は h-集合だと仮定され、Bernstein モジュールの集合性の仮定に対応します。関係 R 自身は型としてまったく任意です。読み戻し以外には何も仮定しません。読み戻しは R a b の元から、第 1 成分が関数 P a → P b、第 2 成分がその関数の単射性の証明である対を返します。特に、取り出された単射は正味のデータであり、命題的切り詰めされた存在ではありません。
<!--/-->

```agda
module MutualInj {ℓ₁ ℓ₂ : Level} (C : Type ℓ₁) (P : C → Type ℓ)
    (R : (a b : C) → Type ℓ₂)
    (setP : (a : C) → isSet (P a))
    (read : (a b : C) → R a b
          → Σ[ f ∈ (P a → P b) ] ((x y : P a) → f x ≡ f y → x ≡ y)) where
```

<!--en-->
The first entry point states the transfer with the two coded injections as explicit arguments: from a forward code in R a b and a backward code in R b a, it returns the bijection between P a and P b as a triple, in exactly the shape of the previous section. The statement quantifies over inhabitants of the relation, not over their truncation, so the codes are available as data throughout.
<!--zh-->
第一个入口以两条编码单射为显式参数陈述转移：从 R a b 中的前向码与 R b a 中的后向码，它以与上一节完全相同的形状返回 P a 与 P b 之间的双射三元组。陈述量化的是关系的元而非其命题截断，因此码全程作为数据可用。
<!--ja-->
最初の入口は、符号化された二つの単射を明示的な引数として移行を述べます。R a b の前向きの符号と R b a の後ろ向きの符号から、前節とまったく同じ形で P a と P b の間の全単射の三つ組を返します。主張は関係の命題的切り詰めではなく元について量化するので、符号は全体を通じてデータとして手に入ります。
<!--/-->

```agda

  mutual→bijection : (a b : C) → R a b → R b a
    → Σ[ h ∈ (P a → P b) ]
        (((x y : P a) → h x ≡ h y → x ≡ y)
      × ((y : P b) → ∥ Σ[ x ∈ P a ] (h x ≡ y) ∥₁))
  mutual→bijection a b fwd bwd = M.ĥ , ( M.ĥ-inj , M.ĥ-surj )
```

<!--en-->
The definition instantiates the Bernstein module at A = P a and B = P b, and this is where the readback is spent. The forward code fwd is unpacked by `read a b` into its function and injectivity components, and the backward code likewise with the arguments of R and read reversed; each projection is selected with the first and second component accessors. The set-ness field receives `setP a`. What reaches the Bernstein module are therefore genuine injections, and everything proved there applies unchanged.
<!--zh-->
定义在 A = P a、B = P b 处实例化 Bernstein 模块，读回正是在此被消耗。前向码 fwd 经 `read a b` 拆解为函数与单射性分量，后向码同理，只是 R 与 read 的参数对调；每个分量由第一、第二分量的投影选取。集合性字段接受 `setP a`。于是到达 Bernstein 模块的是真正的单射，那里证明的一切原样适用。
<!--ja-->
定義は Bernstein モジュールを A = P a、B = P b で実例化します。読み戻しが使われるのはまさにここです。前向きの符号 fwd は `read a b` によって関数と単射性の成分にほどかれ、後ろ向きの符号も同様ですが、R と read の引数の向きが逆になります。各成分は第 1、第 2 成分の射影で取り出されます。集合性の欄には `setP a` が渡ります。したがって Bernstein モジュールに届くのは正味の単射であり、そこで証明されたことはすべてそのまま適用されます。
<!--/-->

```agda
    where
    module M = Bernstein {A = P a} {B = P b} (setP a)
      (read a b fwd .fst) (read a b fwd .snd)
      (read b a bwd .fst) (read b a bwd .snd)
```

<!--en-->
The second entry point weakens the input to mere existence: instead of codes, it receives truncated statements that such codes merely exist. Its conclusion is correspondingly weakened twice. The bijection statement itself is truncated, and surjectivity was already truncated inside; so the final type asserts that a bijection merely exists, not that any particular one can be named. Weakening is irreversible here: the truncation on the input cannot be eliminated into the data of a bijection, only into a proposition-valued target, which the whole statement is.
<!--zh-->
第二个入口把输入弱化为单纯存在：收到的不是码，而是「这样的码单纯存在」的命题截断陈述。其结论相应地被弱化两次。双射陈述本身被命题截断，而满射性本来就在内部是命题截断的；因此最终类型断言的是双射仅仅存在，而非任何特定的一个可被点名。这种弱化不可逆：输入上的命题截断无法消去到双射的数据中，只能消去到命题值的目标，而整个陈述恰是这样的目标。
<!--ja-->
二つ目の入口は入力を単なる存在まで弱めます。受け取るのは符号ではなく、そのような符号が単に存在するという命題的切り詰めされた主張です。結論もそれに応じて二度弱められます。全単射の主張自身が命題的切り詰めされており、全射性はもともと内部で命題的切り詰めされていました。したがって最終的な型が主張するのは、特定の全単射を名指せることではなく、全単射が単に存在することです。弱めることは不可逆です。入力の命題的切り詰めは全単射のデータへは消去できず、命題値の対象へしか消去できません。主張全体がちょうどそのような対象です。
<!--/-->

```agda

  ∃bijection : (a b : C) → ∥ R a b ∥₁ → ∥ R b a ∥₁
    → ∥ Σ[ h ∈ (P a → P b) ]
        (((x y : P a) → h x ≡ h y → x ≡ y)
      × ((y : P b) → ∥ Σ[ x ∈ P a ] (h x ≡ y) ∥₁)) ∥₁
  ∃bijection a b fwd bwd = PT.rec squash₁
```

<!--en-->
The proof nests two truncation eliminations. Eliminating fwd yields some code w; eliminating bwd yields w'; the target of the inner elimination is the truncation of the whole bijection statement, which is a proposition by squash₁, so producing the explicit triple from `mutual→bijection` and injecting it with ∣ ⋯ ∣₁ is legitimate. The order of the two eliminations is immaterial, as both targets are propositions.
<!--zh-->
证明嵌套两次命题截断消去。消去 fwd 得到某个码 w；消去 bwd 得到 w′；内层消去的目标是整个双射陈述的命题截断，由 squash₁ 是命题，因此从 `mutual→bijection` 产出显式三元组并用 ∣ ⋯ ∣₁ 注入是合法的。两次消去的顺序无关紧要，因为两个目标都是命题。
<!--ja-->
証明は二つの命題的切り詰めの消去を入れ子にします。fwd を消去すればある符号 w が得られ、bwd を消去すれば w′ が得られます。内側の消去の対象は全単射の主張全体の命題的切り詰めであり、squash₁ によって命題なので、`mutual→bijection` から明示的な三つ組を作り ∣ ⋯ ∣₁ で注入するのは正当です。二つの消去の順序は、どちらの対象も命題であるため問題になりません。
<!--/-->

```agda
    (λ w → PT.rec squash₁ (λ w' → ∣ mutual→bijection a b w w' ∣₁) bwd)
    fwd
```
