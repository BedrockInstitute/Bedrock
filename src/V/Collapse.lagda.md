<!--en-->
# The Mostowski collapse

Every set of the ambient cumulative hierarchy comes with a canonical presentation: an index type together with an indexing map that names its elements. This chapter asks the converse question. Suppose we single out a set `X` and look only at the elements of the hierarchy that belong to `X`, with the membership relation inherited from the hierarchy. When is this restricted structure, in effect, just another set? The Mostowski collapse answers: membership recursion defines a collapsing map `π`, the range of `π` on `X` is a transitive set, and if `X` satisfies structure extensionality then `π` is injective on `X`, giving an isomorphism between the carrier and its collapsed range.
<!--zh-->
# Mostowski 塌缩

环境累积层级中的每个集合都带有典范呈现：一个索引类型连同指称其元素的索引映射。本章讨论相反的问题。设我们取定一个集合 `X`，只考察层级中属于 `X` 的元素，并沿用层级自身的隶属关系。这个受限结构在什么意义上本身就是一个集合？Mostowski 塌缩给出了回答：沿隶属关系的递归定义塌缩映射 `π`，`π` 在 `X` 上的像是一个传递集；若 `X` 满足结构外延性，则 `π` 在 `X` 上单射，从而给出载体与其塌缩像之间的同构。
<!--ja-->
# Mostowski 崩壊

周囲の累積階層の各集合は、インデックス型とその要素を指すインデックス写像からなる正準な提示を伴います。本章は逆の問題を扱います。集合 `X` を固定し、階層のうち `X` に属する要素だけを、階層自身の所属関係とともに考えます。この制限された構造は、どのような意味でそれ自身ひとつの集合なのでしょうか。Mostowski 崩壊が答えます。所属関係上の再帰で崩壊写像 `π` を定義すると、`X` 上の `π` の像は推移的集合になり、`X` が構造外延性を満たすなら `π` は `X` 上で単射となり、台とその崩壊像の間の同型が得られます。
<!--/-->

<!--en-->
Three mathematical representations shape the proof. First, membership is proposition-valued: the chapter works in a ZF structure `𝒮ᵥ` whose membership predicates take values in propositions, so a membership statement `⟨ z ∈ˢ x ⟩` names an underlying proposition rather than a bare truth value. Second, a set of the hierarchy is used through its small presentation: an index type together with an indexing function `⟪ x ⟫↪` naming the members of `x`, so that building a new set means presenting it with indices. Third, statements about members are often merely true: the propositional truncation `∥_∥₁` turns a statement of the form `some index witnesses this` into the claim that such a witness merely exists, without choosing one. The levels are worth stating exactly. The carrier type `S` of the hierarchy lives in `Type (ℓ-suc ℓ)`, while every presentation index type such as `⟪ x ⟫` is small, in `Type ℓ`; index types and the carrier therefore do not share a universe level.
<!--zh-->
三种数学表示贯穿整个证明。第一，隶属关系取命题为值：本章在 ZF 结构 `𝒮ᵥ` 中工作，其隶属谓词以命题为值，因此隶属陈述 `⟨ z ∈ˢ x ⟩` 指称一个底层命题，而不是裸的真值。第二，层级中的集合通过其小呈现来使用：一个索引类型连同指名 `x` 之成员的索引函数 `⟪ x ⟫↪`，于是构造新集合就意味着用索引去呈现它。第三，关于成员的陈述常常只是「仅仅为真」：命题截断 `∥_∥₁` 把「某个索引见证此事实」这类陈述变成「这样的见证仅仅存在」，而不选取任何见证。宇宙层级值得精确陈述：层级的载体类型 `S` 落在 `Type (ℓ-suc ℓ)` 中，而每个呈现索引类型 (如 `⟪ x ⟫`) 都是小的，落在 `Type ℓ` 中；因此索引类型与载体并不同处同一个宇宙层级。
<!--ja-->
三つの数学的表現が証明を形づくります。第一に、所属は命題値です。この章は ZF 構造 `𝒮ᵥ` の中で行われ、その所属述語は命題を値に取るため、所属の主張 `⟨ z ∈ˢ x ⟩` は裸の真理値ではなく底にある命題を指します。第二に、階層の集合は小さな提示を通じて使われます。インデックス型と、`x` の要素を名指す索引関数 `⟪ x ⟫↪` の組により、新しい集合を作るとはインデックスで提示することを意味します。第三に、要素についての主張はしばしば単に真であるにすぎません。命題切り詰め `∥_∥₁` は「あるインデックスがこれを証拠づける」という主張を、証拠を選ばずに「そのような証拠が単に存在する」という主張へ変えます。宇宙レベルは正確に述べておくべきです。階層の台の型 `S` は `Type (ℓ-suc ℓ)` に属し、一方 `⟪ x ⟫` のような各提示のインデックス型は小さく `Type ℓ` に属します。したがってインデックス型と台は同じ宇宙レベルを共有しません。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude

module V.Collapse {ℓ : Level} where

open import FOL.ZFStructure using ( module hPropStructure; Transitive )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ; extensionalV; ∈-induction; ∈-induction-compute )
```

<!--en-->
The three representations interlock. A presentation `sett I f` produces a set whose membership is truncated: a member is given by an index, but membership statements only record that such an index merely exists. This is why later lemmas about `π`'s members conclude with truncated pairs, and why eliminating such a truncation is legitimate there: the target of the elimination, being the proposition underlying a membership statement `⟨ _ ⟩`, is again a proposition, so no chosen witness escapes into data. The equivalence `∈∈ₛ` connects the two memberships in play, native membership of the embedding and membership in the small relation, and is used in both directions to convert membership certificates between their two forms.
<!--zh-->
三种表示相互咬合。呈现 `sett I f` 产生的集合，其隶属是截断的：成员由索引给出，但隶属陈述只记录这样的索引仅仅存在。这正是后面关于 `π` 成员的引理以截断对作结的原因，也是在那里消去截断合法的原因：消去的目标是隶属陈述 `⟨ _ ⟩` 的底层命题，本身仍是命题，因此不会有被选取的见证逃逸成数据。等价 `∈∈ₛ` 连接了这里使用的两种隶属：嵌入的原生隶属与小关系中的隶属；两个方向都用于在两种形态之间转换隶属证书。
<!--ja-->
三つの表現は噛み合っています。提示 `sett I f` が作る集合の所属は切り詰められています。要素はインデックスで与えられますが、所属の主張はそのようなインデックスが単に存在することしか記録しません。だからこそ、後の `π` の要素に関する補題は切り詰められた組で結論し、そこで切り詰めを消去することが正当なのです。消去の目標は所属の主張 `⟨ _ ⟩` の底にある命題であり、それ自身も命題なので、選ばれた証拠がデータとして逃げることはありません。同値 `∈∈ₛ` はここで使う二つの所属、すなわち埋め込みの本来の所属と小関係における所属を結び、両方向で所属の証拠を二つの形の間で変換します。
<!--/-->

```agda
open import V.Presentation {ℓ} using ( member; fiber )

open import Cubical.Functions.Logic using ( ⇔toPath )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁ )
open import Cubical.HITs.CumulativeHierarchy.Base using ( sett )
```

<!--en-->
One more representation completes the toolkit: the ambient hierarchy supplies well-founded membership, and with it the principles `∈-induction` and `∈-induction-compute`, which define functions by recursion on membership and record the resulting computation laws; the hierarchy also comes with its own extensionality principle. These drive the collapse: the map `π` will be defined by membership recursion, filtering the members of each set through the carrier `X`. With the representations in place, the first question is what to demand of the carrier `X` itself.
<!--zh-->
还差一种表示就齐备了：环境层级自带良基的隶属关系，连同原理 `∈-induction` 与 `∈-induction-compute`，前者沿隶属关系递归地定义函数，后者记录由此得到的计算律；层级还带有自身的外延性原理。正是它们驱动塌缩：映射 `π` 将由隶属递归定义，把每个集合的成员经载体 `X` 过滤。表示就位之后，第一个问题是我们应当对载体 `X` 本身提出什么要求。
<!--ja-->
もうひとつの表現が道具立てを完成させます。周囲の階層ははじめから整礎な所属を備え、それとともに原理 `∈-induction` と `∈-induction-compute` を与えます。前者は所属に関する再帰で関数を定義し、後者はその結果の計算規則を記録します。階層はさらにそれ自身の外延性の原理も持っています。崩壊を駆動するのはまさにこの仕組みです。写像 `π` は所属の再帰で定義され、各集合の要素を台 `X` を通してフィルタリングします。表現がそろったところで、最初の問いは台 `X` それ自身に何を要求すべきかです。
<!--/-->

```agda
open import Cubical.HITs.CumulativeHierarchy.Properties
  using ( _∈ₛ_; ∈∈ₛ; ⟪_⟫; ⟪_⟫↪; _⊆_ )

open hPropStructure 𝒮ᵥ
```

<!--en-->
## Carrier hypotheses

The collapse takes a set `X : S` as carrier. Two hypotheses on `X` appear in this chapter, and they play different roles. Transitivity says that members of members of `X` are again in `X`; it is what makes the collapsed range behave well. Structure extensionality says that two elements of `X` with the same members of `X` are equal; it is what makes the collapsing map injective, and it alone suffices for the isomorphism half of the chapter.
<!--zh-->
## 载体假设

塌缩以一个集合 `X : S` 为载体。本章出现两个关于 `X` 的假设，作用不同。传递性说 `X` 的元素的元素仍在 `X` 中；它使塌缩的像表现良好。结构外延性说具有相同的 `X` 中成员的两个 `X` 元素相等；它使塌缩映射单射，并且仅它就足以支撑本章的同构部分。
<!--ja-->
## 台に関する仮定

崩壊は集合 `X : S` を台として取ります。本章に現れる `X` についての仮定は二つで、役割が異なります。推移性は、`X` の要素の要素が再び `X` に属することを述べ、崩壊した像の振る舞いを良くします。構造外延性は、`X` 内の同じ要素を持つ `X` の二要素が等しいことを述べ、崩壊写像を単射にします。同型の部分にはこの仮定だけで十分です。
<!--/-->

<!--en-->
The transitivity predicate is phrased exactly as in the absoluteness chapter: `Transitive 𝒮ᵥ (λ x → x ∈ˢ u)` says that if `y` is a member of `x` in the structure and `x` is a member of `u` in the small relation, then `y` is a member of `u`. Since the class here is given by small membership in a fixed set `u`, a transitivity witness for `u` is ordinary closure under members of members, and it lives in `Type (ℓ-suc ℓ)` because it quantifies over structure elements and returns propositions at level `ℓ`.
<!--zh-->
传递性谓词的表述与绝对性章完全一致：`Transitive 𝒮ᵥ (λ x → x ∈ˢ u)` 说的是，若在结构中 `y` 是 `x` 的成员，且在小关系中 `x` 属于 `u`，则 `y` 属于 `u`。由于这里的类由对固定集合 `u` 的小隶属给出，`u` 的传递性见证就是通常的对元素之元素的封闭性；它属于 `Type (ℓ-suc ℓ)`，因为它量化结构元素并返回层级 `ℓ` 的命题。
<!--ja-->
推移性の述語は絶対性の章とまったく同じ形で述べられます。`Transitive 𝒮ᵥ (λ x → x ∈ˢ u)` は、構造において `y` が `x` の要素であり、小関係で `x` が `u` に属するなら `y` も `u` に属する、ということです。ここでのクラスは固定された集合 `u` への小所属で与えられるので、`u` の推移性の証拠は通常の「要素の要素についての閉性」です。構造の要素を量化しレベル `ℓ` の命題を返すため、その型は `Type (ℓ-suc ℓ)` になります。
<!--/-->

```agda
isTrans : S → Type (ℓ-suc ℓ)
isTrans u = Transitive 𝒮ᵥ (λ x → x ∈ˢ u)
```

<!--en-->
Extensionality is the hypothesis that drives injectivity. Stated for a fixed carrier set `X`, it compares two elements `x` and `y` that both lie in `X`: if every member of `X` that belongs to `x` also belongs to `y` and conversely, then `x ≡ y`. This is a path conclusion, not a biconditional between membership statements.
<!--zh-->
外延性是驱动单射性的假设。对固定载体集合 `X` 陈述，它比较同属 `X` 的两个元素 `x` 与 `y`：若 `X` 中属于 `x` 的每个成员也属于 `y`，且反之亦然，则 `x ≡ y`。结论是一条路径，而不是隶属陈述之间的双向蕴含。
<!--ja-->
外延性は単射性を支える仮定です。固定された台の集合 `X` について述べると、`X` に属する二つの要素 `x` と `y` を比較し、`X` の中で `x` に属するすべての要素が `y` にも属し、その逆も成り立つなら `x ≡ y` とします。結論は所属述語の間の双条件ではなく、パスそのものです。
<!--/-->

<!--en-->
Each quantified member `z` ranges over `X` only: the hypothesis `z ∈ᵗ X` restricts attention to carrier members, so the comparison ignores elements outside `X`. The two inclusion halves are stated separately, each as an implication between truncated membership types `⟨ z ∈ˢ _ ⟩`, and only then does the definition conclude with the path `x ≡ y`. No transitivity of `X` appears in this statement; the injectivity proof later uses `isExt X` alone.
<!--zh-->
每个被量化的成员 `z` 只在 `X` 上取值：假设 `z ∈ᵗ X` 把注意力限制在载体成员上，因此比较忽略 `X` 之外的元素。两个包含方向分别陈述为截断隶属类型 `⟨ z ∈ˢ _ ⟩` 之间的蕴含，最后才以路径 `x ≡ y` 作结。该陈述不涉及 `X` 的传递性；后面的单射性证明只使用 `isExt X`。
<!--ja-->
量化される各要素 `z` は `X` の上でのみ動きます。仮定 `z ∈ᵗ X` が注意を台の要素に限定するため、比較は `X` の外側の要素を無視します。包含の二方向はそれぞれ、切り詰められた所属型 `⟨ z ∈ˢ _ ⟩` の間の含意として別々に述べられ、最後にパス `x ≡ y` で結ばれます。この主張に `X` の推移性は現れません。後の単射性の証明は `isExt X` だけを使います。
<!--/-->

```agda
isExt : S → Type (ℓ-suc ℓ)
isExt X = (x y : S) → x ∈ᵗ X → y ∈ᵗ X
        → ((z : S) → z ∈ᵗ X → ⟨ z ∈ˢ x ⟩ → ⟨ z ∈ˢ y ⟩)
        → ((z : S) → z ∈ᵗ X → ⟨ z ∈ˢ y ⟩ → ⟨ z ∈ˢ x ⟩)
        → x ≡ y
```

<!--en-->
The collapsing map is built once and for all, for an arbitrary carrier `X`. Packaging it in a module parameterized by `X` keeps the carrier explicit in every lemma that follows.
<!--zh-->
塌缩映射对任意载体 `X` 一次性构造完成。把它包装成以 `X` 为参数的模块，使载体在其后每个引理中都保持显式。
<!--ja-->
崩壊写像は、任意の台 `X` に対して一度だけ構成されます。`X` を引数とするモジュールにまとめることで、以後のすべての補題で台が明示的に保たれます。
<!--/-->

<!--en-->
Everything from here through the transitivity of the range works for an arbitrary `X : S`; no hypothesis on the carrier is needed until the extensionality section. This is worth noting because the classical statement of the Mostowski collapse often assumes well-foundedness and extensionality up front, while here well-foundedness comes free from the ambient hierarchy, and extensionality enters only where injectivity is proved.
<!--zh-->
从这里直到像的传递性，一切结论都对任意 `X : S` 成立；在外延性一节之前不需要对载体的任何假设。值得指出：Mostowski 塌缩的经典陈述常常预先假定良基性与外延性，而这里良基性由环境层级免费提供，外延性只在证明单射性时才登场。
<!--ja-->
ここから像の推移性までは、任意の `X : S` に対して成り立ちます。外延性の節に入るまで、台についての仮定は一切不要です。これは重要です。Mostowski 崩壊の古典的な定式化では整礎性と外延性を最初から仮定することが多いのですが、ここでは整礎性は周囲の階層からただで得られ、外延性は単射性を証明する場面でのみ使われます。
<!--/-->

```agda
module Collapse (X : S) where
```

<!--en-->
## The recursive collapse

For each set `x`, the map `π`{.Agda} should send `x` to the set of collapse values of those members of `x` that also lie in the carrier `X`. This is a definition by recursion on membership: to know `π x` we only need `π y` for members `y` of `x`. Well-foundedness of membership in the ambient hierarchy licenses exactly this form of definition, and also delivers its computation law.
<!--zh-->
## 递归塌缩

对每个集合 `x`，映射 `π`{.Agda} 应把 `x` 映为 `x` 中同时属于载体 `X` 的那些成员的塌缩值组成的集合。这是一个沿隶属关系的递归定义：要知道 `π x`，只需要 `x` 的成员 `y` 的 `π y`。环境层级中隶属关系的良基性恰好允许这种形式的定义，并同时给出其计算律。
<!--ja-->
## 再帰的な崩壊

各集合 `x` に対し、写像 `π`{.Agda} は、`x` の要素のうち台 `X` にも属するものの崩壊値からなる集合へ `x` を送るべきです。これは所属に関する再帰による定義です。`π x` を知るには `x` の要素 `y` に対する `π y` が分かれば足ります。周囲の階層における所属の整礎性が、まさにこの形の定義を可能にし、その計算規則も与えてくれます。
<!--/-->

<!--en-->
The index type `Fiber x` selects the filtered members: an index `m` into the presentation of `x` such that the named element `⟪ x ⟫↪ m` is a small member of `X`. Because the filter uses the small membership, itself a proposition at level `ℓ`, the fiber type lives in `Type ℓ` and the resulting set is legitimately small. The recursive step then presents a new set: indices are the fibers, and each index names `rec` applied to the corresponding member `⟪ x ⟫↪ m` of `x`, together with the membership proof `member x m` that the recursion principle requires to justify the recursive call. Note the direction of information flow: `fiber` is not used here; the carrier-membership witness is carried inside the fiber as data.
<!--zh-->
索引类型 `Fiber x` 选取被过滤的成员：`x` 的呈现中的一个索引 `m`，使得所指名的元素 `⟪ x ⟫↪ m` 是 `X` 的小成员。由于过滤使用小隶属 (它本身是层级 `ℓ` 的命题)，纤维类型落在 `Type ℓ` 中，所得的集合合法地是小的。递归步随后呈现一个新集合：索引就是这些纤维，每个索引指名 `rec` 作用于 `x` 的相应成员 `⟪ x ⟫↪ m` 的值，并附带递归原理所需的隶属证明 `member x m` 以保证递归调用合法。注意信息的流向：这里没有用 `fiber`；载体隶属的见证作为数据随纤维一起携带。
<!--ja-->
インデックス型 `Fiber x` はフィルタリングされた要素を選びます。`x` の提示におけるインデックス `m` で、名指しされた要素 `⟪ x ⟫↪ m` が `X` の小所属を持つものです。フィルタはそれ自身レベル `ℓ` の命題である小所属を使うので、ファイバー型は `Type ℓ` に属し、得られる集合は正当に小さくなります。再帰のステップは新しい集合を提示します。インデックスがファイバーであり、各インデックスは、`x` の対応する要素 `⟪ x ⟫↪ m` への `rec` の適用を名指します。再帰呼び出しを正当化するため、所属証明 `member x m` も添えられます。情報の流れの向きに注意してください。ここでは `fiber` は使われず、台への所属の証拠はデータとしてファイバーの中に担われています。
<!--/-->

```agda
  Fiber : S → Type ℓ
  Fiber x = Σ[ m ∈ ⟪ x ⟫ ] ⟨ ⟪ x ⟫↪ m ∈ₛ X ⟩

  step : (x : S) → (∀ y → y ∈ᵗ x → S) → S
  step x rec = sett (Fiber x) (λ p → rec (⟪ x ⟫↪ (p .fst)) (member x (p .fst)))
```

<!--en-->
Instantiating the ∈-recursion principle at `step` yields the collapse map `π`. The recursion theorem also provides the equation that unfolds `π x` into the set presented by `step x`, and this equation is what every later argument actually uses.
<!--zh-->
把 ∈ 递归原理在 `step` 处实例化便得到塌缩映射 `π`。递归定理还给出把 `π x` 展开为 `step x` 所呈现集合的等式，后面的每个论证实际使用的正是这条等式。
<!--ja-->
∈ 再帰の原理を `step` で具体化すると崩壊写像 `π` が得られます。再帰定理は、`π x` を `step x` が提示する集合へと展開する等式も与えます。以後の議論が実際に使うのはこの等式です。
<!--/-->

<!--en-->
The definition `π = ∈-induction step` is a single appeal to the recursion principle from the hierarchy chapter: since membership is well-founded, a function defined by the recursive step exists on all of `S`. The `opaque` block marks `π` as sealed, meaning the type checker will not unfold it automatically at use sites; this keeps proof terms that mention `π` small.
<!--zh-->
定义 `π = ∈-induction step` 是对层级章递归原理的一次调用：由于隶属关系良基，由该递归步定义的函数在整个 `S` 上存在。`opaque` 块把 `π` 标记为密封，即类型检查器不会在使用处自动展开它；这使提到 `π` 的证明项保持精简。
<!--ja-->
定義 `π = ∈-induction step` は、階層の章の再帰原理への一度の呼び出しです。所属が整礎であるため、この再帰ステップで定まる関数が `S` 全体に存在します。`opaque` ブロックは `π` を封印として印付けます。型検査器は使用箇所で自動的には展開しなくなり、`π` に言及する証明項が小さく保たれます。
<!--/-->

```agda
  opaque
    π : S → S
    π = ∈-induction step

  opaque
    unfolding π
```

<!--en-->
Sealing alone would hide the definition, so the second block explicitly allows unfolding of `π` and records the computation law: `π x` is equal, by a path, to the set presented by `step x` with the recursive calls `π y` in place. The law is itself supplied by the companion theorem `∈-induction-compute` from the same recursion principle, so no new proof is needed. Later chapters transport membership proofs across this path rather than unfolding the definition.
<!--zh-->
仅靠密封会隐藏定义，所以第二个块显式允许展开 `π` 并记录计算律：`π x` 以一条路径等于 `step x` 在递归调用取为 `π y` 时呈现的集合。这条律由同一递归原理的伴随定理 `∈-induction-compute` 直接提供，无需新的证明。后面的章节沿这条路径搬运隶属证明，而不是展开定义。
<!--ja-->
封印だけでは定義が隠れてしまうため、第二のブロックは `π` の展開を明示的に許し、計算規則を記録します。`π x` が、再帰呼び出しを `π y` とした `step x` の提示する集合とパスで等しい、というものです。この規則は同じ再帰原理の伴う定理 `∈-induction-compute` がそのまま供給するので、新たな証明は要りません。以後の節では定義を展開する代わりに、このパスに沿って所属の証明を輸送します。
<!--/-->

```agda
    π-compute : (x : S) → π x ≡ step x (λ y _ → π y)
    π-compute = ∈-induction-compute step
```

<!--en-->
The first property of `π` describes its members. If `z` belongs to `π x`, then, merely, `z` is the collapse of some element of the carrier. The statement is truncated: we do not choose such an element, we only show that the type of such pairs is inhabited.
<!--zh-->
`π` 的第一条性质刻画它的成员。若 `z` 属于 `π x`，则「仅仅存在」载体中某个元素的塌缩等于 `z`。该陈述是截断的：我们不选取这样的元素，只证明这种对的类型被 inhabit。
<!--ja-->
`π` の最初の性質はその要素を特徴づけます。`z` が `π x` に属するなら、台のある要素の崩壊が `z` に等しいことが単に存在します。この主張は切り詰められています。そのような要素を選ぶのではなく、そのような組の型が住まれていることだけを示すのです。
<!--/-->

<!--en-->
The proof starts from the membership certificate `z∈` and transports it along the computation law of `π`. After rewriting `π x` into `sett (Fiber x) ⋯`, the membership type of a presented set lets us read off an index: a fiber `p` together with a path showing that `π` of the named member equals `z`. So the computation law converts an abstract membership into concrete recursion data.
<!--zh-->
证明从隶属证书 `z∈` 出发，沿 `π` 的计算律进行搬运。把 `π x` 改写为 `sett (Fiber x) ⋯` 之后，呈现集合的隶属类型让我们直接读出索引：一个纤维 `p`，连同指名成员的 `π` 值等于 `z` 的路径。于是计算律把抽象的隶属转化为具体的递归数据。
<!--ja-->
証明は所属の証拠 `z∈` から出発し、`π` の計算規則に沿って輸送します。`π x` を `sett (Fiber x) ⋯` に書き換えると、提示された集合の所属の型からインデックスを読み取れます。ファイバー `p` と、名指しされた要素の `π` の値が `z` に等しいというパスです。こうして計算規則は抽象的な所属を具体的な再帰のデータへ変えます。
<!--/-->

```agda
  π-member : (x z : S) → ⟨ z ∈ˢ π x ⟩
           → ∥ Σ[ y ∈ S ] (⟨ y ∈ˢ X ⟩ × (π y ≡ z)) ∥₁
  π-member x z z∈ = PT.map mk (subst (λ w → ⟨ z ∈ˢ w ⟩) (π-compute x) z∈)
    where
    mk : Σ[ p ∈ Fiber x ] (π (⟪ x ⟫↪ (p .fst)) ≡ z)
```

<!--en-->
The auxiliary function `mk` reshapes this recursion data into the promised form. The witness `⟪ x ⟫↪ (p .fst)` is exactly the member of `x` named by the fiber; the second component `∈∈ₛ ⋯ .snd` converts the fiber's carrier-membership certificate from native to small membership; and the path `q` is reused directly. The result is a truncated pair, built with `PT.map`, so the conclusion remains merely an existence statement even though each ingredient is explicit.
<!--zh-->
辅助函数 `mk` 把这份递归数据重塑为承诺的形式。见证 `⟪ x ⟫↪ (p .fst)` 正是纤维所指名的 `x` 的成员；第二分量 `∈∈ₛ ⋯ .snd` 把纤维的载体隶属证书从原生隶属转换为小隶属；路径 `q` 则直接复用。结果是用 `PT.map` 构造的截断对，因此尽管每个成分都是显式的，结论仍只是存在性陈述。
<!--ja-->
補助関数 `mk` はこの再帰データを約束された形に作り替えます。証拠 `⟪ x ⟫↪ (p .fst)` はファイバーが名指す `x` の要素そのものです。第二成分 `∈∈ₛ ⋯ .snd` はファイバーの台への所属の証拠を本来の所属から小所属へ変換し、パス `q` はそのまま再利用します。結果は `PT.map` で構成される切り詰められた組であり、各成分が明示的でも、結論はあくまで存在の主張のままです。
<!--/-->

```agda
       → Σ[ y ∈ S ] (⟨ y ∈ˢ X ⟩ × (π y ≡ z))
    mk (p , q) = ⟪ x ⟫↪ (p .fst)
               , ( ∈∈ₛ {a = ⟪ x ⟫↪ (p .fst)} {b = X} .snd (p .snd)
                 , q )
```

<!--en-->
## The transitive range

The range of the collapse on the carrier deserves to be a set in its own right. Define `πX`{.Agda} by presenting it with the index type of `X`: its members are the collapse values `π (⟪ X ⟫↪ m)` of carrier elements. This section shows that `πX` is transitive, using only that every member of any collapse value is again a collapse of a carrier element, the content of `π-member`.
<!--zh-->
## 传递的像

塌缩在载体上的像本身应当是一个集合。定义 `πX`{.Agda} 时以 `X` 的索引类型来呈现它：其成员就是载体元素的塌缩值 `π (⟪ X ⟫↪ m)`。本节证明 `πX` 是传递的，只用到 `π-member` 的内容：任何塌缩值的成员本身又是某个载体元素的塌缩。
<!--ja-->
## 推移的な像

台の上での崩壊の像は、それ自身ひとつの集合であるべきです。`πX`{.Agda} は `X` のインデックス型で提示して定義します。その要素は台の要素の崩壊値 `π (⟪ X ⟫↪ m)` です。この節では、任意の崩壊値の要素が再び台の要素の崩壊である、すなわち `π-member` の内容だけを使って、`πX` が推移的であることを示します。
<!--/-->

<!--en-->
The set `πX` is the image of `π` restricted to `X`, built with `sett` over the index type `⟪ X ⟫` of the carrier's own presentation. Its member lemma is a direct reading of that presentation: a member of `πX` is, merely, `π y` for some `y` in `X`, and the proof simply unpacks the index `m` and repackages the path `π (⟪ X ⟫↪ m) ≡ z` together with the membership certificate `member X m` produced by the presentation's faithfulness.
<!--zh-->
集合 `πX` 是 `π` 限制在 `X` 上的像，用 `sett` 建立在载体自身呈现的索引类型 `⟪ X ⟫` 之上。其成员引理是对该呈现的直接解读：`πX` 的成员「仅仅」是某个 `y ∈ X` 的 `π y`；证明只需拆开索引 `m`，把路径 `π (⟪ X ⟫↪ m) ≡ z` 与由呈现的忠实性给出的隶属证书 `member X m` 重新打包。
<!--ja-->
集合 `πX` は `π` を `X` に制限した像であり、台そのものの提示のインデックス型 `⟪ X ⟫` の上に `sett` で構成されます。その要素に関する補題はこの提示をそのまま読んだものです。`πX` の要素は、`X` のある `y` に対する `π y` が単に存在することを述べます。証明はインデックス `m` をほどき、パス `π (⟪ X ⟫↪ m) ≡ z` と、提示の忠実性が与える所属の証拠 `member X m` を組み立て直すだけです。
<!--/-->

```agda
  πX : S
  πX = sett ⟪ X ⟫ (λ m → π (⟪ X ⟫↪ m))

  πX-member : (z : S) → ⟨ z ∈ˢ πX ⟩
            → ∥ Σ[ y ∈ S ] (⟨ y ∈ˢ X ⟩ × (π y ≡ z)) ∥₁
  πX-member z z∈ = PT.map mk z∈
```

<!--en-->
The converse introduction says that `πX` contains all the collapse values it should: if `y` is a member of `X`, then `π y` is a member of `πX`. Here the lemma `fiber` from the presentation chapter is essential. A membership proof `y∈X` yields an actual index `m` and a path `⟪ X ⟫↪ m ≡ y`, and applying `cong π` to that path exhibits `π y` as the collapse value at index `m`. Unlike `π-member`, this direction is not truncated in its input; only the output is wrapped in `∥_∥₁` because membership in a presented set is truncated.
<!--zh-->
反向的引入说 `πX` 包含它应有的所有塌缩值：若 `y` 是 `X` 的成员，则 `π y` 是 `πX` 的成员。这里呈现章的引理 `fiber` 至关重要：隶属证明 `y∈X` 给出实际的索引 `m` 和路径 `⟪ X ⟫↪ m ≡ y`，对该路径施加 `cong π` 便把 `π y` 展示为索引 `m` 处的塌缩值。与 `π-member` 不同，这一方向的输入不是截断的；只有输出因呈现集合的隶属是截断的才包在 `∥_∥₁` 中。
<!--ja-->
逆の導入は、`πX` が持つべき崩壊値をすべて含むことを述べます。`y` が `X` の要素なら `π y` は `πX` の要素です。ここで提示の章の補題 `fiber` が決定的です。所属の証拠 `y∈X` は実際のインデックス `m` とパス `⟪ X ⟫↪ m ≡ y` を与え、そのパスに `cong π` を施すことで `π y` がインデックス `m` における崩壊値として現れます。`π-member` と違ってこの向きの入力は切り詰められておらず、提示された集合への所属が切り詰められているため出力だけが `∥_∥₁` に包まれます。
<!--/-->

```agda
    where
    mk : Σ[ m ∈ ⟪ X ⟫ ] (π (⟪ X ⟫↪ m) ≡ z)
       → Σ[ y ∈ S ] (⟨ y ∈ˢ X ⟩ × (π y ≡ z))
    mk (m , q) = ⟪ X ⟫↪ m , ( member X m , q )

  πX-intro : (y : S) → ⟨ y ∈ˢ X ⟩ → ⟨ π y ∈ˢ πX ⟩
```

<!--en-->
Transitivity of `πX` takes the form demanded by `isTrans`: if `y` is a member of `x` and `x` belongs to the range, then `y` belongs to the range. The proof eliminates the truncated hypothesis `x∈πX` with `PT.rec`, which is legitimate because the goal `⟨ y ∈ˢ πX ⟩` is a proposition. Each witness `z` with `π z ≡ x` and `z ∈ X` reduces the problem to showing `y ∈ π z`.
<!--zh-->
`πX` 的传递性取 `isTrans` 要求的形式：若 `y` 是 `x` 的成员且 `x` 属于像，则 `y` 属于像。证明用 `PT.rec` 消去截断的假设 `x∈πX`，这是合法的，因为目标 `⟨ y ∈ˢ πX ⟩` 是命题。每个满足 `π z ≡ x` 且 `z ∈ X` 的见证都把问题化为 `y ∈ π z`。
<!--ja-->
`πX` の推移性は `isTrans` が要求する形を取ります。`y` が `x` の要素であり `x` が像に属するなら、`y` も像に属します。証明は切り詰められた仮定 `x∈πX` を `PT.rec` で消去します。目標の `⟨ y ∈ˢ πX ⟩` が命題であるため、これは正当です。`π z ≡ x` かつ `z ∈ X` を満たす各証拠 `z` は、問題を `y ∈ π z` の証明に帰着させます。
<!--/-->

```agda
  πX-intro y y∈X = ∣ fiber X y∈X .fst , cong π (fiber X y∈X .snd) ∣₁

  πX-trans : isTrans πX
  πX-trans {x} {y} y∈x x∈πX = PT.rec (snd (y ∈ˢ πX)) go (πX-member x x∈πX)
    where
    go : Σ[ z ∈ S ] (⟨ z ∈ˢ X ⟩ × (π z ≡ x)) → ⟨ y ∈ˢ πX ⟩
```

<!--en-->
The inner step first transports `y∈x` along the path `π z ≡ x` to obtain `y ∈ᵗ π z`, then applies `π-member` to see that `y` is, merely, the collapse of some `w` in `X`. Note the asymmetry with the classical picture: the transitivity proof needs no induction on `y`, because membership in the presented set `π z` already exposes the collapse data directly.
<!--zh-->
内层步骤先把 `y∈x` 沿路径 `π z ≡ x` 搬运得到 `y ∈ᵗ π z`，再用 `π-member` 得知 `y`「仅仅」是 `X` 中某个 `w` 的塌缩。注意与经典图景的不同之处：传递性证明不需要对 `y` 做归纳，因为呈现集合 `π z` 中的隶属已直接暴露了塌缩数据。
<!--ja-->
内側のステップでは、まず `y∈x` をパス `π z ≡ x` に沿って輸送して `y ∈ᵗ π z` を得て、次に `π-member` を適用して、`y` が `X` のある `w` の崩壊として単に存在することを示します。古典的な描像との非対称に注意してください。この推移性の証明は `y` についての帰納を必要としません。提示された集合 `π z` への所属が、崩壊のデータをすでに直接明け渡すからです。
<!--/-->

```agda
    go (z , z∈X , pzx) = PT.rec (snd (y ∈ˢ πX)) go₂ (π-member z y y∈πz)
      where
      y∈πz : y ∈ᵗ π z
      y∈πz = subst (λ w → y ∈ᵗ w) (sym pzx) y∈x
      go₂ : Σ[ w ∈ S ] (⟨ w ∈ˢ X ⟩ × (π w ≡ y)) → ⟨ y ∈ˢ πX ⟩
```

<!--en-->
Finally `go₂` transports the desired membership along the path `π w ≡ y`: since `w` lies in `X`, `πX-intro` gives `⟨ π w ∈ˢ πX ⟩`, and the path identifies `π w` with `y`. With that, `πX-trans` is complete, and the collapse's range is a genuine transitive set.
<!--zh-->
最后 `go₂` 沿路径 `π w ≡ y` 搬运所需的隶属：由于 `w` 属于 `X`，`πX-intro` 给出 `⟨ π w ∈ˢ πX ⟩`，该路径把 `π w` 与 `y` 等同起来。至此 `πX-trans` 完成，塌缩的像是一个真正的传递集。
<!--ja-->
最後に `go₂` は、求める所属をパス `π w ≡ y` に沿って輸送します。`w` は `X` に属するので `πX-intro` が `⟨ π w ∈ˢ πX ⟩` を与え、このパスが `π w` と `y` を同一視します。これで `πX-trans` が完成し、崩壊の像は真の推移的集合になります。
<!--/-->

```agda
      go₂ (w , w∈X , pwy) = subst (λ v → ⟨ v ∈ˢ πX ⟩) pwy (πX-intro w w∈X)
```

<!--en-->
The forward direction records how the collapse respects membership between carrier elements. If `y` is a member of `x` and both lie in the carrier `X`, then `π y` is a member of `π x` in the small relation. This lemma is the workhorse of the isomorphism: both inclusions in the injectivity proof reduce to it. Unlike the truncated `π-member`, here all data is explicit, because the membership `y ∈ᵗ x` itself names a witness.
<!--zh-->
前向引理记录塌缩如何保持载体元素之间的隶属关系。若 `y` 是 `x` 的成员且二者都在载体 `X` 中，则 `π y` 在小关系下是 `π x` 的成员。这条引理是同构证明的主力：单射性证明中的两个包含都化归到它。与截断的 `π-member` 不同，这里所有数据都是显式的，因为 `y ∈ᵗ x` 本身就指名了一个见证。
<!--ja-->
順方向の補題は、台の要素の間の所属が崩壊によってどう保たれるかを記録します。`y` が `x` の要素であり、両者が台 `X` に属するなら、`π y` は小関係において `π x` の要素です。この補題は同型証明の主力であり、単射性の証明に現れる両方の包含がこれに帰着します。切り詰められた `π-member` と違い、所属 `y ∈ᵗ x` そのものが証拠を名指すため、ここではすべてのデータが明示的です。
<!--/-->

<!--en-->
The first ingredient is the fiber of the membership proof. Applying `fiber x` to `yx : y ∈ᵗ x` returns an actual index `m` into the presentation of `x` together with a path `⟪ x ⟫↪ m ≡ y`. This is the same explicit-construction lemma that gave `πX-intro` its witnesses: because the embedding has proposition-valued fibers, the truncated membership can be eliminated into this pair type.
<!--zh-->
第一个成分是隶属证明的原像。把 `fiber x` 作用于 `yx : y ∈ᵗ x`，得到 `x` 的呈现中的一个实际索引 `m`，连同路径 `⟪ x ⟫↪ m ≡ y`。这正是为 `πX-intro` 提供见证的那条显式构造引理：由于嵌入的原像都是命题，截断的隶属可以消去到这个对类型中。
<!--ja-->
最初の材料は所属の証明のファイバーです。`fiber x` を `yx : y ∈ᵗ x` に適用すると、`x` の提示における実際のインデックス `m` と、パス `⟪ x ⟫↪ m ≡ y` が得られます。これは `πX-intro` に証拠を与えたのと同じ明示的構成の補題です。埋め込みのファイバーが命題値なので、切り詰められた所属をこの組の型へ消去できます。
<!--/-->

```agda
  π∈-fwd : (x y : S) → y ∈ᵗ x → y ∈ᵗ X → ⟨ π y ∈ˢ π x ⟩
  π∈-fwd x y yx yu = subst (λ w → ⟨ π y ∈ˢ w ⟩) (sym (π-compute x)) wit
    where
    fib : Σ[ m ∈ ⟪ x ⟫ ] (⟪ x ⟫↪ m ≡ y)
    fib = fiber x yx
```

<!--en-->
The carrier membership `yu` speaks about `y`, but the fiber pair is built from `⟪ x ⟫↪ m`, so the proof transports `yu` backwards along the path `p` to obtain `⟪ x ⟫↪ m ∈ˢ X`, and then converts that native small-membership certificate into the small relation with the forward half of `∈∈ₛ`. This is the one place where the two memberships meet directly, and `∈∈ₛ` is exactly the bridge.
<!--zh-->
载体隶属 `yu` 谈论的是 `y`，而对是从 `⟪ x ⟫↪ m` 构造的，所以证明沿路径 `p` 把 `yu` 反向搬运得到 `⟪ x ⟫↪ m ∈ˢ X`，再用 `∈∈ₛ` 的前向一半把这条原生小隶属证书转换为小关系中的隶属。这是两种隶属直接相遇的唯一场合，`∈∈ₛ` 恰是桥。
<!--ja-->
台への所属 `yu` は `y` についての主張ですが、組は `⟪ x ⟫↪ m` から組み立てられるので、証明はパス `p` に沿って `yu` を逆に輸送して `⟪ x ⟫↪ m ∈ˢ X` を得ます。さらに `∈∈ₛ` の順方向の半分で、この本来の小所属の証拠を小関係の所属へ変換します。二つの所属が直接出会うのはこの一点だけで、`∈∈ₛ` がまさにその橋です。
<!--/-->

```agda
    m : ⟪ x ⟫
    m = fib .fst
    p : ⟪ x ⟫↪ m ≡ y
    p = fib .snd
    sm : ⟨ ⟪ x ⟫↪ m ∈ₛ X ⟩
```

<!--en-->
With the pair `(m , sm)` now inhabiting `Fiber x`, the witness `wit` presents `π y` as a member of the set presented by `step x`: the index names the fiber, and the path component is `cong π p`, identifying `π (⟪ x ⟫↪ m)` with `π y`. Transporting along the computation law of `π x` then places this membership under `π x` itself, completing the forward lemma.
<!--zh-->
此时对 `(m , sm)` 已 inhabit `Fiber x`，见证 `wit` 把 `π y` 展示为 `step x` 所呈现集合的成员：索引指名该纤维，路径分量是 `cong π p`，把 `π (⟪ x ⟫↪ m)` 与 `π y` 等同。再沿 `π x` 的计算律搬运，这个隶属便落在 `π x` 本身之下，前向引理完成。
<!--ja-->
組 `(m , sm)` が `Fiber x` を住むようになると、証拠 `wit` は `π y` を `step x` の提示する集合の要素として示します。インデックスがファイバーを名指し、パス成分は `cong π p` で、`π (⟪ x ⟫↪ m)` を `π y` と同一視します。`π x` の計算規則に沿って輸送すれば、この所属は `π x` 自身の下に置かれ、順方向の補題が完成します。
<!--/-->

```agda
    sm = ∈∈ₛ {a = ⟪ x ⟫↪ m} {b = X} .fst (subst (λ w → ⟨ w ∈ˢ X ⟩) (sym p) yu)
    wit : ⟨ π y ∈ˢ sett (Fiber x) (λ q → π (⟪ x ⟫↪ (q .fst))) ⟩
    wit = ∣ (m , sm) , cong π p ∣₁
```

<!--en-->
## Extensionality and the collapse isomorphism

With the transitive range in place, the remaining question is whether the carrier survives the collapse without merging. This section assumes the carrier's structure extensionality `isExt X` and proves that `π` is injective on `X`, and consequently that membership between carrier elements agrees in both directions with membership between their collapse values. The key move is a recovery lemma: from `⟨ π z ∈ˢ π x ⟩` and a comparison principle, it reconstructs `z ∈ᵗ x`. Only extensionality enters here; no transitivity of the carrier is needed, since the memberships that a transitivity argument would supply are already carried by the fibers or by the quantification built into `isExt X`.
<!--zh-->
## 外延性与塌缩同构

传递的像就位之后，剩下的问题是载体在塌缩下是否不会合并。本节假设载体的结构外延性 `isExt X`，证明 `π` 在 `X` 上单射，从而载体元素之间的隶属与其塌缩值之间的隶属双向一致。关键一步是恢复引理：从 `⟨ π z ∈ˢ π x ⟩` 与一个比较原理出发，它重构 `z ∈ᵗ x`。这里只有外延性登场；不需要载体的传递性，因为传递性论证本可提供的隶属已由纤维或 `isExt X` 内部的量化携带。
<!--ja-->
## 外延性と崩壊同型

推移的な像が整ったところで、残る問いは、台が崩壊によって融合せずに済むかどうかです。この節では台の構造外延性 `isExt X` を仮定し、`π` が `X` 上で単射であること、したがって台の要素間の所属が崩壊値の間の所属と双方向に一致することを示します。鍵となるのは復元の補題です。`⟨ π z ∈ˢ π x ⟩` と比較の原理から `z ∈ᵗ x` を再構成します。ここで使われるのは外延性だけで、台の推移性は不要です。推移性の議論が供給するはずだった所属は、すでにファイバーあるいは `isExt X` の内部の量化によって担われているからです。
<!--/-->

<!--en-->
The recovery lemma takes two inputs. The first is the truncated statement `⟨ π z ∈ˢ π x ⟩`; the second is a comparison principle `same` asserting that any `b` in `x ∩ X` with `π b ≡ π z` must equal `z`. The target `z ∈ᵗ x` is a proposition, so eliminating the truncation with `PT.rec` is legitimate. Transporting the hypothesis along the computation law of `π x` turns it into membership in the set presented by `step x`, whose members are indexed by `Fiber x`.
<!--zh-->
恢复引理接受两个输入。其一是截断陈述 `⟨ π z ∈ˢ π x ⟩`；其二是比较原理 `same`，断言任何属于 `x ∩ X` 且满足 `π b ≡ π z` 的 `b` 必等于 `z`。目标 `z ∈ᵗ x` 是命题，因此用 `PT.rec` 消去截断是合法的。沿 `π x` 的计算律搬运假设，便把它化为 `step x` 所呈现集合的成员，其成员由 `Fiber x` 索引。
<!--ja-->
復元の補題は二つの入力を取ります。第一は切り詰められた主張 `⟨ π z ∈ˢ π x ⟩`、第二は比較の原理 `same` で、`x ∩ X` に属し `π b ≡ π z` を満たす任意の `b` が `z` と等しいと述べます。目標の `z ∈ᵗ x` は命題なので、`PT.rec` による切り詰めの消去は正当です。仮定を `π x` の計算規則に沿って輸送すると、それは `step x` の提示する集合への所属になり、その要素は `Fiber x` で添字づけられます。
<!--/-->

```agda
  private
    π∈-recover : (x z : S) → ⟨ π z ∈ˢ π x ⟩
               → ((b : S) → b ∈ᵗ x → b ∈ᵗ X → π b ≡ π z → b ≡ z)
               → z ∈ᵗ x
    π∈-recover x z h same = PT.rec (snd (z ∈ˢ x))
```

<!--en-->
Given a fiber `p` naming `b = ⟪ x ⟫↪ (p .fst)` as a member of `x`, with the collapse path `π b ≡ π z`, the comparison principle fires. Its hypotheses are discharged directly: `member x (p .fst)` proves `b ∈ᵗ x`, and the second component of `∈∈ₛ` converts the fiber's carrier-membership certificate into `b ∈ᵗ X`. The conclusion `b ≡ z` transports the membership certificate `b ∈ᵗ x` to `z ∈ᵗ x`, which is exactly the goal.
<!--zh-->
给定指名 `b = ⟪ x ⟫↪ (p .fst)` 为 `x` 成员的纤维 `p` 以及塌缩路径 `π b ≡ π z`，比较原理即可触发。其假设直接得到满足：`member x (p .fst)` 证明 `b ∈ᵗ x`，而 `∈∈ₛ` 的第二分量把纤维的载体隶属证书转换为 `b ∈ᵗ X`。结论 `b ≡ z` 把隶属证书 `b ∈ᵗ x` 搬运为 `z ∈ᵗ x`，这正是目标。
<!--ja-->
`x` の要素として `b = ⟪ x ⟫↪ (p .fst)` を名指すファイバー `p` と崩壊のパス `π b ≡ π z` が与えられると、比較の原理が発動します。その仮定は直接満たされます。`member x (p .fst)` が `b ∈ᵗ x` を証明し、`∈∈ₛ` の第二成分がファイバーの台への所属の証拠を `b ∈ᵗ X` に変換します。結論の `b ≡ z` は所属の証拠 `b ∈ᵗ x` を `z ∈ᵗ x` へと輸送し、これがまさに目標です。
<!--/-->

```agda
      (λ { (p , q) → subst (λ w → ⟨ w ∈ˢ x ⟩)
        (same (⟪ x ⟫↪ (p .fst)) (member x (p .fst))
          (∈∈ₛ {a = ⟪ x ⟫↪ (p .fst)} {b = X} .snd (p .snd)) q)
        (member x (p .fst)) })
      (subst (λ w → ⟨ π z ∈ˢ w ⟩) (π-compute x) h)
```

<!--en-->
The extensionality-dependent material now lives in a module taking `Xext : isExt X` as a parameter, so that the hypothesis is explicit and is not silently available elsewhere. Inside, the induction predicate `P` is the injectivity statement itself, relative to the carrier: for `x` in `X`, all `y` in `X` with the same collapse value are equal to `x` by a path. This is the property that membership induction will establish for every element of `x` simultaneously.
<!--zh-->
依赖外延性的材料现在放入一个以 `Xext : isExt X` 为参数的模块，使该假设显式出现，且不会在别处悄悄可用。在模块内部，归纳谓词 `P` 就是相对于载体的单射性陈述本身：对 `X` 中的 `x`，所有塌缩值与之相同的 `y ∈ X` 都经路径等于 `x`。这正是隶属归纳要同时对 `x` 的每个元素建立的性质。
<!--ja-->
外延性に依存する材料は、`Xext : isExt X` を引数とするモジュールの中に置かれ、仮定が明示され、他の場所で黙って使えることはありません。その内部では、帰納の述語 `P` が台を基準にした単射性の主張そのものです。`X` に属する `x` に対し、同じ崩壊値を持つ `X` の任意の `y` がパスによって `x` と等しい、というものです。これが、所属帰納が `x` のすべての要素に対して同時に確立すべき性質です。
<!--/-->

```agda

  module InjExt (Xext : isExt X) where

    P : S → Type (ℓ-suc ℓ)
    P x = (y : S) → x ∈ᵗ X → y ∈ᵗ X → π x ≡ π y → x ≡ y
```

<!--en-->
The two inclusions in the extensionality comparison are proved separately, each by an appeal to the recovery lemma. The first direction moves a member `z` of `x` into `y`: assuming `π x ≡ π y` and the induction hypothesis for members of `x`, it concludes `⟨ z ∈ˢ y ⟩`.
<!--zh-->
外延性比较中的两个包含分别用恢复引理证明。第一方向把 `x` 的成员 `z` 移入 `y`：假设 `π x ≡ π y` 以及对 `x` 成员的归纳假设，结论为 `⟨ z ∈ˢ y ⟩`。
<!--ja-->
外延性の比較に現れる二つの包含は、それぞれ復元の補題によって別々に証明されます。第一の向きは `x` の要素 `z` を `y` へ移します。`π x ≡ π y` と `x` の要素についての帰納法の仮定を仮定して、結論 `⟨ z ∈ˢ y ⟩` を得ます。
<!--/-->

<!--en-->
To show that `z` belongs to `y`, the recovery lemma is applied with target set `y`: it suffices to know that `π z` is a member of `π y`, and that any `b ∈ y ∩ X` collapsing to `π z` equals `z`. The membership part follows from the forward lemma: since `z` is a member of `x` and both lie in `X`, we have `⟨ π z ∈ˢ π x ⟩`, and the path `e : π x ≡ π y` transports this to `⟨ π z ∈ˢ π y ⟩`.
<!--zh-->
为证 `z` 属于 `y`，对目标集合 `y` 应用恢复引理：只需知道 `π z` 是 `π y` 的成员，且任何塌缩到 `π z` 的 `b ∈ y ∩ X` 都等于 `z`。隶属部分由前向引理得到：由于 `z` 是 `x` 的成员且二者都在 `X` 中，有 `⟨ π z ∈ˢ π x ⟩`，路径 `e : π x ≡ π y` 把它搬运为 `⟨ π z ∈ˢ π y ⟩`。
<!--ja-->
`z` が `y` に属することを示すには、目標の集合 `y` で復元の補題を適用します。必要なのは、`π z` が `π y` の要素であることと、`π z` に崩壊する `y ∩ X` の任意の `b` が `z` と等しいことです。所属の部分は順方向の補題から従います。`z` は `x` の要素で両者が `X` に属するので `⟨ π z ∈ˢ π x ⟩` が成り立ち、パス `e : π x ≡ π y` がこれを `⟨ π z ∈ˢ π y ⟩` へ輸送します。
<!--/-->

```agda
    in⊆ : (x y z : S) → x ∈ᵗ X → y ∈ᵗ X → z ∈ᵗ x → z ∈ᵗ X
        → π x ≡ π y
        → ((a : S) → a ∈ᵗ x → P a)
        → ⟨ z ∈ˢ y ⟩
    in⊆ x y z xu yu zx zu e IH = π∈-recover y z
```

<!--en-->
The comparison principle is where the induction hypothesis does its work. If `b ∈ y ∩ X` and `π b ≡ π z`, then applying the symmetric path gives `π z ≡ π b`, and the hypothesis `IH z` at the member `z` of `x` produces `z ≡ b`; symmetrizing yields `b ≡ z` as the principle requires. Note that this direction never needs to know that the witness `b` actually exists, only how it would behave.
<!--zh-->
比较原理正是归纳假设发挥作用之处。若 `b ∈ y ∩ X` 且 `π b ≡ π z`，则对称路径给出 `π z ≡ π b`，对 `x` 的成员 `z` 应用假设 `IH z` 得到 `z ≡ b`；再对称化即得原理所需的 `b ≡ z`。注意这一方向从不需要知道见证 `b` 实际存在，只需知道它若有会如何表现。
<!--ja-->
比較の原理こそ、帰納法の仮定が働く場所です。`b ∈ y ∩ X` かつ `π b ≡ π z` なら、対称なパスから `π z ≡ π b` が得られ、`x` の要素 `z` に対する仮定 `IH z` が `z ≡ b` を生みます。これを対称化すれば、原理が要求する `b ≡ z` になります。この向きでは、証拠 `b` が実際に存在することを知る必要はなく、もし存在すればどう振る舞うかを知るだけで十分です。
<!--/-->

```agda
      (subst (λ w → ⟨ π z ∈ˢ w ⟩) e (π∈-fwd x z zx zu))
      (λ b by bu q → sym (IH z zx b zu bu (sym q)))
```

<!--en-->
The second inclusion runs the same argument in the opposite direction, moving a member `z` of `y` into `x`. Combining the two inclusions yields the induction step for injectivity: under the path `π x ≡ π y`, the two sets have exactly the same members of `X`, so structure extensionality concludes `x ≡ y`.
<!--zh-->
第二个包含沿相反方向运行同一论证，把 `y` 的成员 `z` 移入 `x`。两个包含合起来得到单射性的归纳步：在路径 `π x ≡ π y` 之下，两个集合恰有相同的 `X` 成员，结构外延性于是断言 `x ≡ y`。
<!--ja-->
第二の包含は同じ議論を逆向きに行い、`y` の要素 `z` を `x` へ移します。二つの包含を合わせれば単射性の帰納ステップが得られます。パス `π x ≡ π y` の下で二つの集合は `X` の要素をちょうど同じだけ持ち、構造外延性が `x ≡ y` と結論します。
<!--/-->

<!--en-->
The proof is a mirror of `in⊆`: recovery is applied to the target set `x`, and the collapsed membership `⟨ π z ∈ˢ π x ⟩` comes from the forward lemma at the pair `(y, z)` transported along the reversed path `e`. The only asymmetry is the direction of the given path, which accounts for the swapped roles of `x` and `y`.
<!--zh-->
证明是 `in⊆` 的镜像：对目标集合 `x` 应用恢复引理，而 `⟨ π z ∈ˢ π x ⟩` 来自在对 `(y, z)` 上的前向引理，再沿反向路径 `e` 搬运。唯一的不对称是给定路径的方向，它对应 `x` 与 `y` 角色的互换。
<!--ja-->
証明は `in⊆` の鏡像です。目標の集合 `x` に復元の補題を適用し、切り詰められた所属 `⟨ π z ∈ˢ π x ⟩` は、組 `(y, z)` に対する順方向の補題を逆向きのパス `e` に沿って輸送したものです。非対称なのは与えられたパスの向きだけで、それが `x` と `y` の役割の入れ替わりに対応します。
<!--/-->

```agda
    out⊆ : (x y z : S) → x ∈ᵗ X → y ∈ᵗ X → z ∈ᵗ y → z ∈ᵗ X
         → π y ≡ π x
         → ((a : S) → a ∈ᵗ x → P a)
         → ⟨ z ∈ˢ x ⟩
    out⊆ x y z xu yu zy zu e IH = π∈-recover x z
```

<!--en-->
The comparison clause here is simpler than in `in⊆`: given `b ∈ x ∩ X` with `π b ≡ π z`, the induction hypothesis `IH b` applies directly at `b` and yields `b ≡ z` without any symmetrizing. The recovery lemma then transports `b ∈ᵗ x` along this path, giving `z ∈ᵗ x`, as required.
<!--zh-->
这里的比较子句比 `in⊆` 中的简单：给定 `b ∈ x ∩ X` 与 `π b ≡ π z`，归纳假设 `IH b` 直接在 `b` 处适用，无需对称化便得 `b ≡ z`。恢复引理随后沿该路径把 `b ∈ᵗ x` 搬运为 `z ∈ᵗ x`，正如所需。
<!--ja-->
ここでの比較の節は `in⊆` の場合より単純です。`b ∈ x ∩ X` と `π b ≡ π z` が与えられると、帰納法の仮定 `IH b` は `b` の場所でそのまま適用でき、対称化なしに `b ≡ z` を与えます。復元の補題は続いてこのパスに沿って `b ∈ᵗ x` を `z ∈ᵗ x` へ輸送し、求める結論になります。
<!--/-->

```agda
      (subst (λ w → ⟨ π z ∈ˢ w ⟩) e (π∈-fwd y z zy zu))
      (λ b bx bu q → IH b bx z bu zu q)

    step-inj : (x : S) → ((a : S) → a ∈ᵗ x → P a) → P x
    step-inj x IH y xu yu e = Xext x y xu yu to from
      where
```

<!--en-->
The induction step `step-inj` now assembles the two inclusions into an application of the carrier's extensionality hypothesis `Xext`. Given `x, y ∈ X` and a path `e : π x ≡ π y`, the two clauses `to` and `from` are exactly the comparisons demanded by `isExt X`, each delegating to `in⊆` or `out⊆` with the appropriate orientation of `e`. The conclusion is the path `x ≡ y`, so `P x` holds.
<!--zh-->
归纳步 `step-inj` 现在把两个包含组装成对载体外延性假设 `Xext` 的一次应用。给定 `x, y ∈ X` 与路径 `e : π x ≡ π y`，子句 `to` 与 `from` 正是 `isExt X` 所要求的比较，各自委托给 `in⊆` 或 `out⊆`，并以 `e` 的恰当定向。结论是路径 `x ≡ y`，故 `P x` 成立。
<!--ja-->
帰納ステップ `step-inj` は、二つの包含を台の外延性の仮定 `Xext` への適用へと組み立てます。`x, y ∈ X` とパス `e : π x ≡ π y` が与えられると、節 `to` と `from` は `isExt X` が要求する比較そのものであり、それぞれ `in⊆` か `out⊆` へ、`e` の適切な向きで処理を委ねます。結論はパス `x ≡ y` であり、`P x` が成り立ちます。
<!--/-->

```agda
      to : (z : S) → z ∈ᵗ X → ⟨ z ∈ˢ x ⟩ → ⟨ z ∈ˢ y ⟩
      to z zu zx = in⊆ x y z xu yu zx zu e IH
      from : (z : S) → z ∈ᵗ X → ⟨ z ∈ˢ y ⟩ → ⟨ z ∈ˢ x ⟩
      from z zu zy = out⊆ x y z xu yu zy zu (sym e) IH
```

<!--en-->
The injectivity theorem follows by ∈-induction, since each `step-inj` invocation is exactly the induction step for the predicate `P`.
<!--zh-->
单射性定理由 ∈ 归纳立即得到，因为每次调用 `step-inj` 恰是谓词 `P` 的归纳步。
<!--ja-->
単射性の定理は ∈ 帰納によって直ちに従います。`step-inj` の呼び出しはそのまま述語 `P` の帰納ステップだからです。
<!--/-->

<!--en-->
No new argument is needed: membership induction on the ambient hierarchy produces, for every `x`, the statement `P x` from the step verified above. Unfolding `P`, this is exactly injectivity of `π` on the carrier: two elements of `X` with equal collapse values are equal.
<!--zh-->
无需新论证：对环境层级的隶属归纳从上面验证的步进为每个 `x` 产生 `P x`。展开 `P`，这恰是 `π` 在载体上的单射性：塌缩值相等的两个 `X` 元素相等。
<!--ja-->
新しい議論は要りません。周囲の階層への所属帰納が、上で検証したステップからすべての `x` に対して `P x` を生みます。`P` を展開すれば、これは `π` の台の上での単射性そのものです。崩壊値が等しい `X` の二つの要素は等しい。
<!--/-->

```agda
    π-inj : (x y : S) → x ∈ᵗ X → y ∈ᵗ X → π x ≡ π y → x ≡ y
    π-inj = ∈-induction step-inj
```

<!--en-->
With injectivity in hand, the backward direction of the isomorphism follows immediately: a collapsed membership can be traced back to a genuine membership in the carrier.
<!--zh-->
有了单射性，同构的反向立即得到：塌缩的隶属可以追溯到载体中真正的隶属。
<!--ja-->
単射性が得られたので、同型の逆向きは直ちに従います。崩壊された所属は、台の中の本物の所属へとたどれます。
<!--/-->

<!--en-->
Given `⟨ π y ∈ˢ π x ⟩`, the recovery lemma eliminates a merely existing presentation witness: from a fiber naming some `b ∈ᵗ x` with `π b ≡ π y`, it produces `b ≡ y`, because the comparison clause supplied here applies `π-inj` to conclude the equality outright. Injectivity is what identifies the recovered carrier element with `y`. Transporting the membership certificate of `b` along that path then yields `y ∈ᵗ x`. The elimination is licensed because its target `y ∈ᵗ x` is itself a proposition, being the underlying type of the proposition-valued membership; the witness `b` is never chosen as data, and the conclusion is only the propositional membership statement.
<!--zh-->
给定 `⟨ π y ∈ˢ π x ⟩`，恢复引理对仅仅存在的呈现见证进行消去：从指名某个 `b ∈ᵗ x` 且满足 `π b ≡ π y` 的纤维出发，它给出 `b ≡ y`，因为这里供给的比较子句直接应用 `π-inj` 得出该等式。正是单射性把恢复出的载体元素与 `y` 等同起来。再沿这条路径搬运 `b` 的隶属证书，便得到 `y ∈ᵗ x`。这一消去是合法的，因为其目标 `y ∈ᵗ x` 本身是命题，即命题值隶属的底层类型；见证 `b` 从未被选为数据，结论也只是这条命题值的隶属陈述。
<!--ja-->
`⟨ π y ∈ˢ π x ⟩` が与えられると、復元の補題は単に存在する提示の証拠を消去します。ある `b ∈ᵗ x` が `π b ≡ π y` を満たすことを名指すファイバーから、`b ≡ y` を得ます。ここで供する比較の節が `π-inj` を適用して等式そのものを出すからです。復元された台の要素と `y` を同一視するのは、まさにこの単射性です。続いて `b` の所属の証拠をこのパスに沿って輸送すれば `y ∈ᵗ x` が得られます。この消去が正当なのは、目標の `y ∈ᵗ x` が命題値の所属の底にある型としてそれ自身命題だからです。証拠 `b` がデータとして選ばれることはなく、結論も命題値の所属の主張にとどまります。
<!--/-->

```agda
    π∈-bwd : (x y : S) → x ∈ᵗ X → y ∈ᵗ X → ⟨ π y ∈ˢ π x ⟩ → y ∈ᵗ x
    π∈-bwd x y xu yu h = π∈-recover x y h
      (λ b bx bu q → π-inj b y bu yu q)
```

<!--en-->
Assembling both directions gives the isomorphism reading of the collapse: on the carrier, membership and collapsed membership determine each other.
<!--zh-->
把两个方向合起来便得到塌缩的同构解读：在载体上，隶属与塌缩后的隶属相互决定。
<!--ja-->
両方向を組み合わせると、崩壊の同型としての読みが得られます。台の上では、所属と崩壊された所属が互いを定めます。
<!--/-->

<!--en-->
The packaged result is a pair of implications, not an equivalence type: from `⟨ y ∈ˢ x ⟩` to `⟨ π y ∈ˢ π x ⟩` via the forward lemma, and back via `π∈-bwd`. This is the precise sense in which the collapse is an isomorphism on the carrier: it preserves and reflects membership among elements of `X`, and by `π-inj` it is injective there.
<!--zh-->
打包的结果是一对蕴含，而非等价类型：由 `⟨ y ∈ˢ x ⟩` 经前向引理到 `⟨ π y ∈ˢ π x ⟩`，再经 `π∈-bwd` 返回。这就是塌缩在载体上构成同构的精确含义：它保持且反映 `X` 的元素之间的隶属，并由 `π-inj` 在其上单射。
<!--ja-->
まとめられた結果は、同値の型ではなく一対の含意です。`⟨ y ∈ˢ x ⟩` から順方向の補題経由で `⟨ π y ∈ˢ π x ⟩` へ、そして `π∈-bwd` 経由で戻るものです。崩壊が台の上で同型であるということの正確な意味はこれです。`X` の要素の間の所属を保ちかつ反映し、`π-inj` によりその上で単射です。
<!--/-->

```agda
    iso : (x y : S) → x ∈ᵗ X → y ∈ᵗ X
        → (⟨ y ∈ˢ x ⟩ → ⟨ π y ∈ˢ π x ⟩) × (⟨ π y ∈ˢ π x ⟩ → ⟨ y ∈ˢ x ⟩)
    iso x y xu yu = (λ yx → π∈-fwd x y yx yu) , π∈-bwd x y xu yu
```

<!--en-->
The recursion equation `π x ≡ step x (λ y _ → π y)` is not merely a property of the particular function constructed by `∈-induction`: it characterizes the collapse up to path. Any function `f` satisfying the same recursion equation, with `f` itself in the recursive calls, agrees with `π` everywhere. This uniqueness is what makes the collapse a well-defined object rather than one among possibly many outputs of a construction.
<!--zh-->
递归等式 `π x ≡ step x (λ y _ → π y)` 不仅是 `∈-induction` 所构造的这个特定函数的性质：它在路径意义下刻画了塌缩。任何满足同一递归等式 (递归调用中也是 `f` 自身) 的函数 `f` 都处处与 `π` 一致。这一唯一性使塌缩成为良定义的对象，而不是某个构造的众多可能输出之一。
<!--ja-->
再帰等式 `π x ≡ step x (λ y _ → π y)` は、`∈-induction` が構成した特定の関数の性質にとどまらず、パスの意味で崩壊を特徴づけます。同じ再帰等式を、再帰呼び出しでも `f` 自身を用いて満たす任意の関数 `f` は、`π` とどこでも一致します。この一意性により、崩壊は構成の多数の出力のひとつではなく、well-defined な対象になります。
<!--/-->

<!--en-->
The statement quantifies over all `f : S → S` equipped with the computation rule `h : f x ≡ sett (Fiber x) (λ p → f (⟪ x ⟫↪ (p .fst)))`. Note the shape: like `π`'s own law, the right-hand side presents a set whose members are the `f`-images of the filtered members of `x`. The conclusion is a path family `π x ≡ f x`, proved by ∈-induction, since knowing the equality on members of `x` determines it at `x`.
<!--zh-->
陈述量化所有配备计算规则 `h : f x ≡ sett (Fiber x) (λ p → f (⟪ x ⟫↪ (p .fst)))` 的 `f : S → S`。注意其形状：与 `π` 自身的律一样，右边呈现的集合，其成员是 `x` 中被过滤成员的 `f` 像。结论是路径族 `π x ≡ f x`，由 ∈ 归纳证明，因为在 `x` 的成员处已知等式便决定了在 `x` 处的等式。
<!--ja-->
主張は、計算規則 `h : f x ≡ sett (Fiber x) (λ p → f (⟪ x ⟫↪ (p .fst)))` を備えたすべての `f : S → S` を量化します。その形に注意してください。`π` 自身の法則と同じく、右辺は `x` のフィルタリングされた要素の `f` 像を要素とする集合を提示します。結論はパスの族 `π x ≡ f x` であり、`x` の要素での等式が分かれば `x` での等式が定まるため、∈ 帰納で証明されます。
<!--/-->

```agda
  unique : (f : S → S)
         → ((x : S) → f x ≡ sett (Fiber x) (λ p → f (⟪ x ⟫↪ (p .fst))))
         → (x : S) → π x ≡ f x
  unique f h = ∈-induction stepU
    where
```

<!--en-->
The induction step chains three paths. Starting from `π-compute x`, the left side becomes the set presented by `step x` with `π` in the recursive calls; the middle path `step-eq` changes the recursive calls from `π` to `f`; and `sym (h x)` unfolds `f x`. The composite exhibits `π x ≡ f x` from the induction hypothesis alone.
<!--zh-->
归纳步串联三条路径。从 `π-compute x` 出发，左边变为递归调用取 `π` 时 `step x` 呈现的集合；中间路径 `step-eq` 把递归调用从 `π` 换成 `f`；`sym (h x)` 展开 `f x`。复合路径仅凭归纳假设便展示出 `π x ≡ f x`。
<!--ja-->
帰納ステップは三つのパスを連結します。`π-compute x` から出発すると、左辺は再帰呼び出しに `π` を使う `step x` の提示する集合になります。途中のパス `step-eq` は再帰呼び出しを `π` から `f` へ替え、`sym (h x)` が `f x` を展開します。合成のパスは帰納法の仮定だけから `π x ≡ f x` を示します。
<!--/-->

```agda
    stepU : (x : S) → ((y : S) → y ∈ᵗ x → π y ≡ f y) → π x ≡ f x
    stepU x IH = π-compute x ∙ step-eq ∙ sym (h x)
      where
      step-eq : sett (Fiber x) (λ p → π (⟪ x ⟫↪ (p .fst)))
              ≡ sett (Fiber x) (λ p → f (⟪ x ⟫↪ (p .fst)))
```

<!--en-->
The middle path itself is congruence applied to the presenting function: `sett` is held fixed while the indexing function changes from `λ p → π (⋯)` to `λ p → f (⋯)`, and `funExt` supplies pointwise equality of these two functions. Each point is an instance of the induction hypothesis, applied at the member named by the fiber `p`, with the membership certificate `member x (p .fst)` justifying the recursive call. This is the standard uniqueness argument for definitions by well-founded recursion, adapted to the presented-set constructor.
<!--zh-->
中间路径本身是对呈现函数应用同余性：保持 `sett` 固定，索引函数从 `λ p → π (⋯)` 变为 `λ p → f (⋯)`，`funExt` 提供这两个函数的逐点相等。每一点都是归纳假设的实例，作用于纤维 `p` 所指名的成员，并由隶属证书 `member x (p .fst)` 保证递归调用合法。这是良基递归定义的标准唯一性论证，适配到呈现集合的构造子上。
<!--ja-->
途中のパスそのものは、提示する関数への同一性 (congruence) の適用です。`sett` を固定したまま、インデックス関数を `λ p → π (⋯)` から `λ p → f (⋯)` へ替え、`funExt` がこの二つの関数の各点での等しさを供給します。各点は帰納法の仮定の具体例であり、ファイバー `p` が名指す要素に適用され、所属の証拠 `member x (p .fst)` が再帰呼び出しを正当化します。これは整礎再帰による定義の標準的な一意性の議論を、集合を提示する構成子に合わせたものです。
<!--/-->

```agda
      step-eq = cong (sett (Fiber x)) (funExt ih')
        where
        ih' : (p : Fiber x) → π (⟪ x ⟫↪ (p .fst)) ≡ f (⟪ x ⟫↪ (p .fst))
        ih' p = IH (⟪ x ⟫↪ (p .fst)) (member x (p .fst))
```

<!--en-->
When does the collapse change nothing? If `Y` is a transitive subset of the carrier, meaning every member of a member of `Y` again lies in `Y`, then the filter defining the collapse is full on members of `Y`: nothing is discarded, and so `π y ≡ y` for every `y ∈ᵗ Y`. This fixed-point statement is proved by ∈-induction on `y`, comparing `π y` and `y` through the hierarchy's own extensionality principle.
<!--zh-->
塌缩何时什么都不改变？若 `Y` 是载体的传递子集，即 `Y` 的成员的成员仍在 `Y` 中，则定义塌缩时的过滤对 `Y` 的成员是完全的：没有任何东西被丢弃，故对每个 `y ∈ᵗ Y` 有 `π y ≡ y`。这个不动点命题通过对 `y` 的 ∈ 归纳证明，比较 `π y` 与 `y` 时用的是层级自身的外延性原理。
<!--ja-->
崩壊はいつ何も変えないのでしょうか。`Y` が台の推移的な部分集合、つまり `Y` の要素の要素が再び `Y` に属するなら、崩壊を定めるフィルタは `Y` の要素の上で完全であり、何も捨てられません。したがって各 `y ∈ᵗ Y` に対して `π y ≡ y` が成り立ちます。この不動点の主張は `y` についての ∈ 帰納で証明され、`π y` と `y` の比較には階層自身の外延性の原理を使います。
<!--/-->

<!--en-->
The statement combines the two carrier-side data: the inclusion `⟨ Y ⊆ X ⟩` in the small relation and the transitivity `isTrans Y`, which is closure of `Y` under members of members. The induction hypothesis is stated with both memberships visible: it asserts `π m ≡ m` only for members `m` of `y` that also lie in `Y`, matching exactly the situation the proof will encounter.
<!--zh-->
陈述组合了两个载体侧的数据：小关系下的包含 `⟨ Y ⊆ X ⟩` 与传递性 `isTrans Y`，即 `Y` 对成员的成员的封闭性。归纳假设把两种隶属都写在面上：它只对同时属于 `Y` 的 `y` 的成员 `m` 断言 `π m ≡ m`，恰好对应证明中会遇到的情况。
<!--ja-->
主張は台の側の二つのデータを組み合わせます。小関係における包含 `⟨ Y ⊆ X ⟩` と、推移性 `isTrans Y`、すなわち `Y` の要素の要素についての閉性です。帰納法の仮定は両方の所属を見える形で述べます。`y` の要素のうち `Y` にも属する `m` に対してのみ `π m ≡ m` を主張しており、証明で出会う状況にちょうど合致します。
<!--/-->

```agda
  fixes : (Y : S) → ⟨ Y ⊆ X ⟩ → isTrans Y → (y : S) → y ∈ᵗ Y → π y ≡ y
  fixes Y YX Ytr = ∈-induction stepF
    where
    stepF : (y : S) → ((m : S) → m ∈ᵗ y → m ∈ᵗ Y → π m ≡ m)
          → y ∈ᵗ Y → π y ≡ y
```

<!--en-->
The step compares the two sets through `extensionalV`, the extensionality principle of the hierarchy itself: two sets are equal once they have the same members, formulated here as a family of paths obtained from biconditionals. The direction `to` shows that members of the collapsed set are already members of `y`, and it starts by eliminating the truncated membership `xπ` after transporting it along the computation law, exposing a fiber of `Fiber y` together with the path `π` of the named member equaling `x`.
<!--zh-->
归纳步通过 `extensionalV` 比较两个集合，这是层级自身的外延性原理：只要成员相同两个集合便相等，这里表述为由双向蕴含生成的路径族。方向 `to` 说明塌缩集合的成员已是 `y` 的成员；证明先把截断隶属 `xπ` 沿计算律搬运，再用 `PT.rec` 消去，露出 `Fiber y` 的一个纤维以及指名成员的 `π` 值等于 `x` 的路径。
<!--ja-->
ステップは `extensionalV`、すなわち階層そのものの外延性の原理によって二つの集合を比較します。要素が同じなら集合は等しいというもので、ここでは双条件から作られるパスの族として定式化されています。向き `to` は、崩壊された集合の要素がすでに `y` の要素であることを示し、まず切り詰められた所属 `xπ` を計算規則に沿って輸送してから消去し、`Fiber y` のファイバーと、名指しされた要素の `π` 値が `x` に等しいパスを取り出します。
<!--/-->

```agda
    stepF y IH yY = extensionalV (λ x → ⇔toPath (to x) (from x))
      where
      to : (x : S) → ⟨ x ∈ˢ π y ⟩ → x ∈ᵗ y
      to x xπ = PT.rec (snd (x ∈ˢ y)) go
        (subst (λ w → ⟨ x ∈ˢ w ⟩) (π-compute y) xπ)
```

<!--en-->
Given such a fiber, the named member `⟪ y ⟫↪ (p .fst)` is a member of `y` that lies in `Y` by transitivity, so the induction hypothesis applies to it and fixes it: `π` of it equals itself. Composing the symmetry of this fixed-point path with the collapse path `q` produces a path from the named member to `x`, and transporting the membership certificate along it lands at `x ∈ᵗ y`.
<!--zh-->
给定这样的纤维，所指名的成员 `⟪ y ⟫↪ (p .fst)` 是 `y` 的成员且由传递性属于 `Y`，归纳假设适用于它并将其固定：它的 `π` 值等于它自身。把这个不动点路径的对称与塌缩路径 `q` 复合，得到从指名成员到 `x` 的路径，沿它搬运隶属证书便落在 `x ∈ᵗ y`。
<!--ja-->
そのようなファイバーが与えられると、名指しされた要素 `⟪ y ⟫↪ (p .fst)` は `y` の要素であり、推移性により `Y` にも属するので、帰納法の仮定が適用されてそれを固定します。つまりその `π` 値はそれ自身と等しい。この不動点のパスの対称と崩壊のパス `q` を合成すれば、名指しされた要素から `x` へのパスが得られ、所属の証拠をそれに沿って輸送すれば `x ∈ᵗ y` に着地します。
<!--/-->

```agda
        where
        go : Σ[ p ∈ Fiber y ] (π (⟪ y ⟫↪ (p .fst)) ≡ x) → x ∈ᵗ y
        go (p , q) = subst (λ w → ⟨ w ∈ˢ y ⟩) (sym ih' ∙ q) (member y (p .fst))
          where
          ih' : π (⟪ y ⟫↪ (p .fst)) ≡ ⟪ y ⟫↪ (p .fst)
```

<!--en-->
The direction `from` shows that every member of `y` survives the collapse. Here transitivity of `Y` is used first, to see that `x` itself lies in `Y`; the induction hypothesis then gives the path `π x ≡ x`, and transporting the forward lemma's conclusion `⟨ π x ∈ˢ π y ⟩` along this path relocates the membership at `x` itself, giving `⟨ x ∈ˢ π y ⟩`.
<!--zh-->
方向 `from` 说明 `y` 的每个成员都在塌缩中幸存。这里先用 `Y` 的传递性看出 `x` 本身属于 `Y`；归纳假设随后给出路径 `π x ≡ x`，把前向引理的结论 `⟨ π x ∈ˢ π y ⟩` 沿该路径搬运，隶属便落在 `x` 本身处，得到 `⟨ x ∈ˢ π y ⟩`。
<!--ja-->
向き `from` は、`y` のすべての要素が崩壊を生き延びることを示します。まず `Y` の推移性を使って `x` 自身が `Y` に属することを確認し、次に帰納法の仮定からパス `π x ≡ x` が得られます。順方向の補題の結論 `⟨ π x ∈ˢ π y ⟩` をこのパスに沿って輸送すれば、所属は `x` 自身の場所に移り、`⟨ x ∈ˢ π y ⟩` が得られます。
<!--/-->

```agda
          ih' = IH (⟪ y ⟫↪ (p .fst)) (member y (p .fst))
            (Ytr {x = y} {y = ⟪ y ⟫↪ (p .fst)} (member y (p .fst)) yY)

      from : (x : S) → x ∈ᵗ y → ⟨ x ∈ˢ π y ⟩
      from x xy = subst (λ w → ⟨ w ∈ˢ π y ⟩) (IH x xy x∈Y)
        (π∈-fwd y x xy x∈X)
```

<!--en-->
The two auxiliary facts mirror each other. Membership in `Y` comes from transitivity applied to `x ∈ᵗ y` and `y ∈ᵗ Y`. From that, membership in the carrier `X` follows in two small steps: the backward half of `∈∈ₛ` converts `x ∈ᵗ Y` into the small membership statement, and the hypothesis `YX` carries that statement across the inclusion into `X`, where the forward half of `∈∈ₛ` returns an ordinary membership proof.
<!--zh-->
两个辅助事实互为镜像。`x` 属于 `Y` 由传递性作用于 `x ∈ᵗ y` 与 `y ∈ᵗ Y` 得到。由此，`x` 属于载体 `X` 分两小步得出：`∈∈ₛ` 的反向一半把 `x ∈ᵗ Y` 化为小隶属陈述，假设 `YX` 把该陈述沿包含搬运到 `X`，再由 `∈∈ₛ` 的前向一半返回通常的隶属证明。
<!--ja-->
二つの補助的事実は互いに鏡像です。`x` の `Y` への所属は、推移性を `x ∈ᵗ y` と `y ∈ᵗ Y` に適用して得られます。そこから台 `X` への所属は、小さな二段階で従います。`∈∈ₛ` の逆向きの半分が `x ∈ᵗ Y` を小所属の主張に変え、仮定 `YX` がその主張を包含に沿って `X` へ運び、`∈∈ₛ` の順方向の半分が通常の所属の証明に戻します。
<!--/-->

```agda
        where
        x∈Y : x ∈ᵗ Y
        x∈Y = Ytr {x = y} {y = x} xy yY
        x∈X : x ∈ᵗ X
        x∈X = ∈∈ₛ {a = x} {b = X} .snd
```

<!--en-->
With both directions established, the biconditional for each `x` is converted into a path by `⇔toPath`, and `extensionalV` assembles the resulting family of paths into `π y ≡ y`. Since `y` was an arbitrary member of `Y`, the collapse fixes `Y` pointwise, closing the induction.
<!--zh-->
两个方向都建立后，`⇔toPath` 把每个 `x` 处的双向蕴含转换为路径，`extensionalV` 再把所得的路径族组装成 `π y ≡ y`。由于 `y` 是 `Y` 的任意成员，塌缩逐点固定 `Y`，归纳完成。
<!--ja-->
両方向が確立されれば、`⇔toPath` が各 `x` での双条件をパスに変換し、`extensionalV` が得られたパスの族を `π y ≡ y` へと組み立てます。`y` は `Y` の任意の要素だったので、崩壊は `Y` を各点で固定し、帰納が閉じます。
<!--/-->

```agda
          (YX x (∈∈ₛ {a = x} {b = Y} .fst x∈Y))
```

<!--en-->
The fixed-point statement applies in particular when `Y` is the carrier `X` itself: a transitive carrier is fixed pointwise by the collapse, so on such a carrier the collapsing map is the identity.
<!--zh-->
不动点命题尤其适用于 `Y` 就是载体 `X` 本身的情形：传递的载体被塌缩逐点固定，因此在这样的载体上塌缩映射就是恒等映射。
<!--ja-->
不動点の主張は、`Y` が台 `X` そのものである場合に特に当てはまります。推移的な台は崩壊によって各点で固定され、そのような台の上では崩壊写像は恒等写像になります。
<!--/-->
