<!--en-->
# Von Neumann rank

The rank of a set is the union, over its members, of the successors of their ranks; in symbols, the computation theorem `rank-compute` identifies `rank x` with `rankStep x (λ y _ → rank y)`. Four facts about it are proved in this chapter: `rank-mono` says that rank strictly increases along membership, `rank-ord` says that rank is always an ordinal, `rank-upper` gives a conditional inclusion of a rank into an ordinal, and `rank-fix` says that rank fixes ordinals.

Nothing here needs an external type of ordinals: rank takes values in the hierarchy itself, and the recursion runs on well-founded membership, which regularity directly guarantees. Thus every theorem in this chapter is proved without an excluded-middle parameter.
<!--zh-->
# Von Neumann 秩

集合的秩是其所有成员之秩的后继的并；用记号说，计算定理 `rank-compute` 把 `rank x` 等同于 `rankStep x (λ y _ → rank y)`。本章证明秩的四条性质：`rank-mono` 说秩沿隶属关系严格增长，`rank-ord` 说秩总是序数，`rank-upper` 给出秩包含于某序数的有条件结论，`rank-fix` 说秩固定每个序数。

此处不需要任何外部的序数类型：秩取值于层级自身，而递归依据正则性所保证的成员关系良基性进行。因此本章每条定理都不需要排中律参数。
<!--ja-->
# von Neumann ランク

集合のランクは、その各要素のランクの後続を要素にわたって合わせた和集合です。記号で言えば、計算定理 `rank-compute` が `rank x` を `rankStep x (λ y _ → rank y)` と同一視します。本章で証明するのは四つの事実です。`rank-mono` はランクが所属に沿って狭義単調に増加すること、`rank-ord` はランクが常に順序数であること、`rank-upper` はランクがある順序数に含まれるという条件付きの結論を与えること、そして `rank-fix` はランクが順序数を固定することを言います。

ここでは外部の順序数の型は何も要りません。ランクは階層自身の中に値を取り、再帰は整礎な所属関係の上を走ります。これは正則性公理が直接保証するものです。したがって本章の各定理には排中律のパラメータがありません。
<!--/-->

<!--en-->
Rank is defined inside the cumulative hierarchy `V ℓ`, with carrier `S`. A membership statement `x ∈ˢ y` is proposition-valued, and regularity makes this membership relation well-founded. The induction principle `∈-induction` can therefore define a value in `S` from values already defined for every member.
<!--zh-->
秩直接定义在累积层级 `V ℓ` 的载体 `S` 中。成员关系 `x ∈ˢ y` 是命题值的，而正则性保证这条成员关系良基。因此，成员归纳原理 `∈-induction` 可以利用每个成员处已经定义的值，在当前集合处定义一个 `S` 中的值。
<!--ja-->
ランクは累積階層 `V ℓ` の台 `S` の中で直接定義されます。所属 `x ∈ˢ y` は命題値をとり、正則性によりこの所属関係は整礎です。したがって所属帰納 `∈-induction` は、各要素ですでに定義された値から、現在の集合に対する `S` の値を定義できます。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth

module L.Rank {ℓ : Level} where

open import FOL.ZFStructure using ( module hPropStructure )
```

<!--en-->
For rank, the value at a set must collect the successor ranks of all its members. The operations `sucV` and small indexed union express this construction. Once the recursive member ranks are known to be ordinals, `suc-ord` and `setUnion-ord` show that the collected value is again an ordinal; `mem-ord` later supplies ordinality for members of an ordinal.
<!--zh-->
对秩而言，集合处的值要汇集其所有成员之秩的后继。`sucV` 与小索引并正好表达这一构造。递归得到的成员秩一旦是序数，`suc-ord` 与 `setUnion-ord` 就证明汇集后的值仍是序数；在处理序数自身时，`mem-ord` 再给出其成员的序数性。
<!--ja-->
ランクでは、集合の各要素のランクの後続を集める必要があります。この構成を表すのが `sucV` と小さな添字付き和です。再帰的に得た各要素のランクが順序数なら、`suc-ord` と `setUnion-ord` により集めた値も順序数になります。順序数自身を扱う際には、`mem-ord` がその要素の順序数性を与えます。
<!--/-->

```agda
open import V.Hierarchy {ℓ}
  using ( 𝒮ᵥ; extensionalV; ∈-induction; ∈-induction-compute )
open import V.Model {ℓ} using ( union-family-in; union-family-out; ∈sucV-elim; self∈sucV )
open import L.Constructible {ℓ} using ( IsOrd )
open import L.Ordinal {ℓ} using ( suc-ord; setUnion-ord; mem-ord )
```

<!--en-->
The indexing is genuinely small. Each set `x` has a small member type `⟪ x ⟫` and an embedding `⟪ x ⟫↪` into `S`; `∈ₛ⟪ x ⟫↪ m` proves that the represented set belongs to `x`. Conversely, a given membership proof can be converted by `∈-asFiber` into an index together with a path identifying its represented set with the member. These two directions connect recursion over membership with the small family used by the union.
<!--zh-->
这里的索引确实是小的。每个集合 `x` 都有小成员类型 `⟪ x ⟫` 及其到 `S` 的嵌入 `⟪ x ⟫↪`，而 `∈ₛ⟪ x ⟫↪ m` 证明所表示的集合属于 `x`。反过来，给定成员关系证明，`∈-asFiber` 返回一个索引以及所表示集合与该成员相等的路径。这两个方向把沿成员关系的递归与取并所需的小族连接起来。
<!--ja-->
ここで使う添字は実際に小さいものです。各集合 `x` には小さな要素型 `⟪ x ⟫` と `S` への埋め込み `⟪ x ⟫↪` があり、`∈ₛ⟪ x ⟫↪ m` は表された集合が `x` に属することを示します。逆に、所属の証明から `∈-asFiber` により、添字と、その表示が当の要素に等しいというパスを得られます。この二方向が、所属に沿う再帰と和集合を作る小さな族を結びます。
<!--/-->

```agda

open import Cubical.Functions.Logic using ( ⇔toPath )
import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.HITs.CumulativeHierarchy.Base using ( sett )
open import Cubical.HITs.CumulativeHierarchy.Properties
  using ( ∈∈ₛ; ∈-asFiber; ⟪_⟫; ⟪_⟫↪; ∈ₛ⟪_⟫↪_ )
```

<!--en-->
The recursive step can now be read mathematically: take the small family of members, replace each member by the successor of its recursively computed rank, and form their union. The next section states this construction as `rankStep` and records its computation path.
<!--zh-->
于是递归步可以直接读成数学构造：取成员组成的小族，把每个成员换成其递归所得秩的后继，再对这一族取并。下一节把这个构造写成 `rankStep`，并给出它的计算路径。
<!--ja-->
これで再帰ステップをそのまま数学的に読めます。要素からなる小さな族を取り、各要素を再帰的に得たランクの後続に置き換え、その和集合を作ります。次節ではこの構成を `rankStep` として述べ、計算パスを記録します。
<!--/-->

```agda
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ⋃_; module InfinitySet )
open InfinitySet using ( sucV )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ
```

<!--en-->
## The recursion

The step takes the union, over the members of `x`, of the successors of their ranks. The recursive calls run over the *small* type of members, and the computation law holds propositionally as a path rather than definitionally, which is what later proofs use.
<!--zh-->
## 递归

步进取 `x` 的各成员之秩的后继的并。递归调用跑在成员的**小**类型上，而计算法则作为路径命题性地成立、而非定义性地成立，这正是后文证明所用的形式。
<!--ja-->
## 再帰

ステップは、`x` の各要素のランクの後続の和集合を取ります。再帰呼び出しは要素の**小さな**型の上を走り、計算法則は定義的等式ではなくパスとして命題的に成り立ちます。後の証明が使うのはこの形です。
<!--/-->

<!--en-->
The recursion equation says: to rank a set `x`, rank every member and take the union of the successors. Formally, the family being unioned is indexed by `⟪ x ⟫`, the small type of members, so the expression `⋃ (sett ⟪ x ⟫ …)` is a legal small union; the embedding `⟪ x ⟫↪` turns an index `m` into the actual set `⟪ x ⟫↪ m`, and the helper `mem` supplies the proof that this embedded set really is a member of `x`, which is what the recursive call `rec` demands. Note the shape of the step: it receives the recursive values through a function `rec` rather than calling `rank` directly, which is what makes it usable as the step of `∈-induction`.
<!--zh-->
递归方程说：要对集合 `x` 求秩，就对每个成员求秩，再取其后继的并。形式上，被取并的族以成员的小类型 `⟪ x ⟫` 为索引，故 `⋃ (sett ⟪ x ⟫ …)` 是一次合法的小并；嵌入 `⟪ x ⟫↪` 把索引 `m` 变成实际的集合 `⟪ x ⟫↪ m`，而辅助 `mem` 提供该嵌入集合确实是 `x` 的成员的证明，这正是递归调用 `rec` 所要求的。注意步进函数的形状：它经函数 `rec` 接收递归值，而不直接调用 `rank`，这使它能充当 `∈-induction` 的步进。
<!--ja-->
再帰方程式は次を言います。集合 `x` のランクを求めるには、各要素のランクを求め、その後続の和集合を取る。形式的には、和を取る族は要素の小さな型 `⟪ x ⟫` で添字づけられるので、`⋃ (sett ⟪ x ⟫ …)` は正当な小さな和です。埋め込み `⟪ x ⟫↪` が添字 `m` を実際の集合 `⟪ x ⟫↪ m` に変え、補助 `mem` がこの埋め込まれた集合が実際に `x` の要素であることの証明を供給します。これは再帰呼び出し `rec` が要求するものです。ステップの形に注意してください。`rank` を直接呼ぶのではなく、関数 `rec` を通して再帰的な値を受け取ります。これが `∈-induction` のステップとして使える理由です。
<!--/-->

```agda
rankStep : (x : S) → (∀ y → y ∈ᵗ x → S) → S
rankStep x rec = ⋃ (sett ⟪ x ⟫ (λ m → sucV (rec (⟪ x ⟫↪ m) (mem m))))
  where
  mem : (m : ⟪ x ⟫) → ⟪ x ⟫↪ m ∈ᵗ x
  mem m = ∈∈ₛ {a = ⟪ x ⟫↪ m} {b = x} .snd (∈ₛ⟪ x ⟫↪ m)
```

<!--en-->
The rank itself is the membership induction applied to this step: `∈-induction rankStep` turns the step function into a total family on all of `S`. The definition is marked `opaque` to keep the checker from unfolding the well-founded eliminator inside it. What is available instead is the computation law `rank-compute`, which exposes the recursion equation as a propositional path: `rank x` is a path to `rankStep x (λ y _ → rank y)`, the same equation with `rank` itself filling every recursive call. Later proofs rewrite by this path rather than reducing `rank` directly.
<!--zh-->
秩本身就是把成员归纳用在这个步进上：`∈-induction rankStep` 把步进函数变成整个 `S` 上的全定义族。定义标记为 `opaque`，以免检查器展开其中的良基消去子。取而代之可用的是计算法则 `rank-compute`，它把递归方程作为命题路径暴露出来：`rank x` 有一条到 `rankStep x (λ y _ → rank y)` 的路径，即同一条方程、但每次递归调用都由 `rank` 自身填充。后续证明按这条路径改写，而不直接化简 `rank`。
<!--ja-->
ランクそのものは、このステップに所属帰納を適用したものです。`∈-induction rankStep` がステップ関数を `S` 全体上の全域的な族に変えます。定義には `opaque` が付いており、検証器がその中の整礎消去子を展開しないようにしています。代わりに使えるのが計算法則 `rank-compute` で、これは再帰方程式を命題的なパスとして公開します。`rank x` は `rankStep x (λ y _ → rank y)` へのパスであり、すべての再帰呼び出しが `rank` 自身で満たされた同じ方程式です。後の証明は `rank` を直接簡約せず、このパスで書き換えます。
<!--/-->

```agda

opaque
  rank : S → S
  rank = ∈-induction rankStep

  rank-compute : (x : S) → rank x ≡ rankStep x (λ y _ → rank y)
  rank-compute = ∈-induction-compute rankStep
```

<!--en-->
## Rank strictly increases along membership

The theorem `rank-mono` states that if `x ∈ˢ y` then `rank x ∈ˢ rank y`. It follows directly from the shape of the defining union: `rank y` is a union of successors `sucV (rank w)` indexed by the members `w` of `y`, so exhibiting `rank x` as a member of one such successor suffices. No `IsOrd`{.Agda} hypothesis appears anywhere in the statement.
<!--zh-->
## 秩沿成员关系严格增长

定理 `rank-mono` 说：若 `x ∈ˢ y`，则 `rank x ∈ˢ rank y`。它直接来自定义之并的形状：`rank y` 是以 `y` 的成员 `w` 为索引的后继 `sucV (rank w)` 之并，故只需把 `rank x` 表为其中某个后继的成员。命题中完全不出现 `IsOrd`{.Agda} 假设。
<!--ja-->
## ランクは所属に沿って狭義単調に増加する

定理 `rank-mono` は、`x ∈ˢ y` ならば `rank x ∈ˢ rank y` であることを述べます。これは定義の和の形から直接従います。`rank y` は `y` の要素 `w` で添字づけられた後続 `sucV (rank w)` の和集合であり、`rank x` がそのような後続の一つの要素であることを見れば十分です。命題のどこにも `IsOrd`{.Agda} の仮定は現れません。
<!--/-->

<!--en-->
Given `x ∈ˢ y`, the goal is `rank x ∈ˢ rank y`. Unfold `rank y` once by `rank-compute`: the goal becomes membership in the union `⋃ (sett ⟪ y ⟫ (λ m → sucV (rank (⟪ y ⟫↪ m))))`. Now it suffices to exhibit `rank x` as a member of one family member, namely `sucV (rank w)` for some member `w` of `y`; `self∈sucV` puts `rank x` inside its own successor, and `union-family-in` lifts that into the union, transport along the computation path included.
<!--zh-->
给定 `x ∈ˢ y`，目标是 `rank x ∈ˢ rank y`。先用 `rank-compute` 把 `rank y` 展开一次：目标变成属于并 `⋃ (sett ⟪ y ⟫ (λ m → sucV (rank (⟪ y ⟫↪ m))))`。于是只需把 `rank x` 表为某个族元、即某成员 `w` 的 `sucV (rank w)` 的成员；`self∈sucV` 把 `rank x` 放进它自身的后继，`union-family-in` 再把它提升进并，包括沿计算路径的传输。
<!--ja-->
`x ∈ˢ y` が与えられれば、ゴールは `rank x ∈ˢ rank y` です。まず `rank-compute` で `rank y` を一度展開すると、ゴールは和 `⋃ (sett ⟪ y ⟫ (λ m → sucV (rank (⟪ y ⟫↪ m))))` への所属になります。あとは `rank x` が何らかの族の元、すなわち `y` の要素 `w` に対する `sucV (rank w)` の要素であることを見れば十分です。`self∈sucV` が `rank x` をそれ自身の後続の内側に置き、`union-family-in` が計算パスに沿う輸送込みでそれを和集合の中へ引き上げます。
<!--/-->

```agda
rank-mono : (x y : S) → ⟨ x ∈ˢ y ⟩ → ⟨ rank x ∈ˢ rank y ⟩
rank-mono x y x∈y = subst (λ w → ⟨ rank x ∈ˢ w ⟩) (sym (rank-compute y))
  (union-family-in ⟪ y ⟫ (λ m → sucV (rank (⟪ y ⟫↪ m))) (fib .fst) (rank x)
    (subst (λ w → ⟨ rank x ∈ˢ sucV (rank w) ⟩) (sym (fib .snd)) (self∈sucV (rank x))))
  where
```

<!--en-->
The remaining piece is where the index for the union member comes from. The function `∈-asFiber` turns the given proof `x∈y` into a fiber of the embedding `⟪ y ⟫↪`: a pair whose first component `fib .fst` is an index into `⟪ y ⟫`, and whose second component `fib .snd` is a path saying that the indexed set equals `x`. That path is transported along so that the membership in the successor speaks of `rank x` itself; this is exactly what the code shows.
<!--zh-->
剩下的部分是并的族元所用的索引从何而来。函数 `∈-asFiber` 把给定的证明 `x∈y` 转换为嵌入 `⟪ y ⟫↪` 的一个纤维：一个对，其第一分量 `fib .fst` 是 `⟪ y ⟫` 中的一个索引，第二分量 `fib .snd` 是说被索引的集合等于 `x` 的路径。代码正是沿这条路径传输，使得后继中的隶属谈的是 `rank x` 自身。
<!--ja-->
残る部分は、和の族の元に使う添字がどこから来るかです。関数 `∈-asFiber` は与えられた証明 `x∈y` を埋め込み `⟪ y ⟫↪` のファイバーに変換します。これは対であり、第一成分 `fib .fst` は `⟪ y ⟫` への添字、第二成分 `fib .snd` は添字づけられた集合が `x` に等しいというパスです。コードはまさにこのパスに沿って輸送し、後続への所属が `rank x` 自身について語るようにします。
<!--/-->

```agda
  fib = ∈-asFiber {a = x} {b = y} x∈y
```

<!--en-->
## Rank is an ordinal

One membership induction. Unfold once by `rank-compute`; the inductive hypothesis makes each member's rank an ordinal, the closure lemma `suc-ord` makes each successor an ordinal, and the closure lemma `setUnion-ord` makes the union of that family of ordinals an ordinal again.
<!--zh-->
## 秩是序数

一次成员归纳。先用 `rank-compute` 展开一次；归纳假设给出每个成员的秩是序数，封闭引理 `suc-ord` 给出每个后继是序数，封闭引理 `setUnion-ord` 给出这一族序数之并仍是序数。
<!--ja-->
## ランクは順序数

所属帰納を一度だけ使います。まず `rank-compute` で一度展開します。帰納仮定が各要素のランクを順序数とし、閉性の補題 `suc-ord` が各後続を順序数とし、閉性の補題 `setUnion-ord` がその順序数の族の和を再び順序数とします。
<!--/-->

<!--en-->
The statement quantifies over all sets, so the proof is a membership induction with the predicate `λ A → IsOrd (rank A)`. The induction hypothesis hands us, for each member `y` of `A`, the certificate that `rank y` is an ordinal. Since `rank-compute A` propositionally identifies `rank A` with the step, the goal is reached by transporting `IsOrd` along the computation path `rank-compute A`, so what remains is to show that the union of the step is an ordinal.
<!--zh-->
命题对所有集合量化，故证明是以 `λ A → IsOrd (rank A)` 为谓词的成员归纳。归纳假设对 `A` 的每个成员 `y` 给出「`rank y` 是序数」的证书。由于 `rank-compute A` 在命题意义下把 `rank A` 等同于步进所得，目标可沿计算路径 `rank-compute A` 传输 `IsOrd` 而达成，剩下只需证步进所得的并是序数。
<!--ja-->
主張はすべての集合にわたって量化するので、証明は述語 `λ A → IsOrd (rank A)` に関する所属帰納です。帰納仮定は `A` の各要素 `y` に対して、`rank y` が順序数であるという証明書を渡します。`rank-compute A` が `rank A` とステップを命題的に同一視するので、ゴールは計算パス `rank-compute A` に沿って `IsOrd` を輸送することで到達し、残るのはステップの和が順序数であることの証明だけです。
<!--/-->

```agda
rank-ord : (A : S) → IsOrd (rank A)
rank-ord = ∈-induction {P = λ A → IsOrd (rank A)} step
  where
  step : (A : S) → (∀ y → y ∈ᵗ A → IsOrd (rank y)) → IsOrd (rank A)
  step A IH = subst IsOrd (sym (rank-compute A))
```

<!--en-->
That last step composes two closure facts. Each family member `sucV (rank (⟪ A ⟫↪ m))` is the successor of an ordinal, hence an ordinal by `suc-ord`, with the induction hypothesis and the helper `mem` supplying the input certificate. Then `setUnion-ord` closes the small indexed union of ordinals under union. The chain from hypothesis to conclusion: if the ranks of the members are ordinals, so is the rank of the set.
<!--zh-->
最后一步组合两个封闭事实。每个族元 `sucV (rank (⟪ A ⟫↪ m))` 是某序数的后继，故由 `suc-ord` 是序数，其输入证书由归纳假设与辅助 `mem` 供给。随后 `setUnion-ord` 保证序数的小索引并仍是序数。从假设到结论的链条是：若成员的秩是序数，则集合的秩也是序数。
<!--ja-->
この最後のステップは二つの閉性事実を組み合わせます。各族の元 `sucV (rank (⟪ A ⟫↪ m))` は順序数の後続であり、したがって `suc-ord` により順序数です。入力の証明書は帰納仮定と補助 `mem` が供給します。次に `setUnion-ord` が順序数の小さな添字付き和の閉性を与えます。仮定から結論への連鎖はこうです。要素のランクが順序数なら、集合のランクも順序数である。
<!--/-->

```agda
    (setUnion-ord ⟪ A ⟫ (λ m → sucV (rank (⟪ A ⟫↪ m)))
      (λ m → suc-ord (IH (⟪ A ⟫↪ m) (mem m))))
    where
    mem : (m : ⟪ A ⟫) → ⟪ A ⟫↪ m ∈ᵗ A
    mem m = ∈∈ₛ {a = ⟪ A ⟫↪ m} {b = A} .snd (∈ₛ⟪ A ⟫↪ m)
```

<!--en-->
## Bounding a rank

If every member's rank lies in an ordinal, the rank of the set is included in that ordinal. Every member of the defining union lies in a successor of a member's rank; transitivity closes the inclusion. Both ordinal fixed points and bounds on the ranks in a constructible stage use this argument.
<!--zh-->
## 界住秩

若一个集合的每个成员的秩都属于某序数，则该集合的秩包含于该序数：定义之并的每个成员都落在某个成员之秩的后继中，传递性给出所需包含。序数的不动点性质与可构造层中的秩界都用这条论证。
<!--ja-->
## ランクの上界

`β` が順序数で、`A` の各要素のランクを含むなら、ランクの再帰方程式と `β` の推移性により `rank A ⊆ β` が従います。この補題は集合全体のランクを一つの順序数で抑えます。
<!--/-->

<!--en-->
The statement is a pointwise inclusion, not a strict membership: assuming `IsOrd β` and that every member rank `rank y` lies strictly in `β`, it concludes that every member of `rank A` lies in `β`. The proof eliminates from the shape of the defining union. Membership in the union yields, via `union-family-out`, merely an index `m` with `x ∈ˢ s m`; since the target `x ∈ˢ β` is a proposition, eliminating this truncation is legitimate, and `∈sucV-elim` then splits membership in the successor `s m = sucV (rank (⟪ A ⟫↪ m))` into its two cases.
<!--zh-->
所述是逐点包含而非严格隶属：在 `IsOrd β` 与「每个成员秩 `rank y` 严格属于 `β`」的假设下，结论是 `rank A` 的每个成员都属于 `β`。证明从定义之并的形状出发消去。属于该并经 `union-family-out` 给出仅仅一个索引 `m` 使 `x ∈ˢ s m`；由于目标 `x ∈ˢ β` 是命题，对这个截断做消去是合法的，随后 `∈sucV-elim` 把在后继 `s m = sucV (rank (⟪ A ⟫↪ m))` 中的隶属分成两种情形。
<!--ja-->
主張は狭義の所属ではなく各点ごとの包含です。`IsOrd β` と、すべての要素のランク `rank y` が狭義に `β` に属するという仮定の下で、`rank A` のすべての要素が `β` に属すると結論します。証明は定義の和の形からの消去です。和への所属は `union-family-out` を通して、`x ∈ˢ s m` となる添字 `m` を単に (merely) 与えます。ゴール `x ∈ˢ β` は命題なので、この切り詰めの消去は正当であり、続いて `∈sucV-elim` が後続 `s m = sucV (rank (⟪ A ⟫↪ m))` への所属を二つの場合に分けます。
<!--/-->

```agda
rank-upper : (A β : S) → IsOrd β
           → ((y : S) → ⟨ y ∈ˢ A ⟩ → ⟨ rank y ∈ˢ β ⟩)
           → (x : S) → ⟨ x ∈ˢ rank A ⟩ → ⟨ x ∈ˢ β ⟩
rank-upper A β oβ bound x hx = PT.rec (snd (x ∈ˢ β))
  (λ { (m , hm) → ∈sucV-elim (snd (x ∈ˢ β)) hm
```

<!--en-->
The two cases of the successor are where ordinality earns its keep. If `x` is a member of `rank (⟪ A ⟫↪ m)`, then since β is transitive and that rank is already in β, so is `x`: this is the branch `oβ .fst h (below m)`. If instead `x` equals `rank (⟪ A ⟫↪ m)` outright, the second branch transports the bound `below m` across that path. Either way the conclusion lands in `x ∈ˢ β`. What the eliminator receives from the union is `hm : ⟨ x ∈ˢ s m ⟩` merely, so the fiber `(m , hm)` is consumed inside a propositional elimination and no index is ever extracted as data.
<!--zh-->
后继的两种情形正是序数性发挥作用之处。若 `x` 属于 `rank (⟪ A ⟫↪ m)`，则因 β 传递且该秩已在 β 中，`x` 也在 β 中：这是分支 `oβ .fst h (below m)`。若 `x` 直接等于 `rank (⟪ A ⟫↪ m)`，第二支沿该路径传输界 `below m`。两种情形的结论都落在 `x ∈ˢ β`。`union-family-out` 给出的索引与证明位于命题截断中；由于目标 `x ∈ˢ β` 是命题，`PT.rec` 可以逐个处理其中的 `(m , hm)`，而不选择一个全局索引。
<!--ja-->
後続の二つの場合こそ、順序数性が働く場所です。`x` が `rank (⟪ A ⟫↪ m)` の要素なら、β が推移的でそのランクがすでに β にあることから、`x` も β に属します。これが分岐 `oβ .fst h (below m)` です。`x` が `rank (⟪ A ⟫↪ m)` そのものに等しい場合は、第二の分岐がそのパスに沿って上界 `below m` を輸送します。どちらの場合も結論は `x ∈ˢ β` に着地します。消去子が和集合から受け取るのは単に (merely)`hm : ⟨ x ∈ˢ s m ⟩` なので、ファイバー `(m , hm)` は命題消去の内部で消費され、添字がデータとして取り出されることはありません。
<!--/-->

```agda
    (λ h → oβ .fst h (below m))
    (λ q → subst (λ w → ⟨ w ∈ˢ β ⟩) (sym q) (below m)) })
  (union-family-out ⟪ A ⟫ s x
    (subst (λ w → ⟨ x ∈ˢ w ⟩) (rank-compute A) hx))
  where
```

<!--en-->
The family `s` is the successor-rank family from the recursion equation, sending an index `m` to `sucV (rank (⟪ A ⟫↪ m))`. The fact `below m` is the hypothesis `bound` applied to the embedded member `⟪ A ⟫↪ m` together with its membership proof, yielding `rank (⟪ A ⟫↪ m) ∈ˢ β`. The whole lemma therefore uses no induction: rewrite by the computation law, take the union apart, and let the ordinal's transitivity absorb the successor.
<!--zh-->
族 `s` 就是递归方程中的后继之秩的族，把索引 `m` 映到 `sucV (rank (⟪ A ⟫↪ m))`。事实 `below m` 是把假设 `bound` 作用于被嵌入成员 `⟪ A ⟫↪ m` 及其成员证明，得到 `rank (⟪ A ⟫↪ m) ∈ˢ β`。整个引理因此不依赖任何归纳：按计算法则改写一次，拆开并，让序数的传递性吸收后继。
<!--ja-->
族 `s` は再帰方程式における後続のランクの族で、添字 `m` を `sucV (rank (⟪ A ⟫↪ m))` に送ります。事実 `below m` は仮定 `bound` を埋め込まれた要素 `⟪ A ⟫↪ m` とその所属の証明に適用したもので、`rank (⟪ A ⟫↪ m) ∈ˢ β` を与えます。したがってこの補題全体は帰納を一切使いません。計算法則で一度書き換え、和を分解し、順序数の推移性に後続を吸収させるだけです。
<!--/-->

```agda
  s : ⟪ A ⟫ → S
  s m = sucV (rank (⟪ A ⟫↪ m))
  below : (m : ⟪ A ⟫) → ⟨ rank (⟪ A ⟫↪ m) ∈ˢ β ⟩
  below m = bound (⟪ A ⟫↪ m)
    (∈∈ₛ {a = ⟪ A ⟫↪ m} {b = A} .snd (∈ₛ⟪ A ⟫↪ m))
```

<!--en-->
## Ordinals are their own rank

Again by membership induction, and this time the proof is an extensionality between `rank A` and `A`. Left to right, an element of `rank A` sits inside the successor of the rank of some member, and that rank *is* the member by the inductive hypothesis, so the element is the member or belongs to it, and either way it belongs to `A` by transitivity. Right to left, a member of `A` is the rank of itself, hence belongs to the successor of that rank, which is one branch of the union.
<!--zh-->
## 序数是自身的秩

仍是成员归纳，而这次的证明是 `rank A` 与 `A` 之间的一次外延。从左到右：`rank A` 的元素落在某个成员之秩的后继里面，而依归纳假设那个秩**就是**该成员，故该元素或就是该成员，或属于它，两种情形都经传递性属于 `A`。从右到左：`A` 的成员是自身的秩，故属于该秩的后继，而那是并的一支。
<!--ja-->
## 順序数は自分自身のランクである

再び所属帰納を使います。今回は証明が `rank A` と `A` との間の外延性の適用になります。左から右には、`rank A` の要素はある要素のランクの後続の内側にありますが、帰納仮定によりそのランク**こそ**その要素なので、その要素は対象と一致するか対象に属するかのいずれかであり、どちらの場合も推移性によって `A` に属します。右から左には、`A` の要素はそれ自身のランクに等しいので、そのランクの後続に属し、後続は和の一つの枝です。
<!--/-->

<!--en-->
The theorem states that rank fixes every ordinal, as a path rather than an iff. The induction is set up with a predicate that packages the ordinality hypothesis together with the conclusion, `λ A → IsOrd A → rank A ≡ A`, because the step genuinely needs it: to compare rank A with A it must know that members of the ordinal A are themselves ordinals. So the step receives, alongside the recursive equalities `rank y ≡ y`, the certificate `IsOrd A` and returns the equality at `A`.
<!--zh-->
定理说秩固定每个序数，以路径而非等价的形式。归纳以把序数性假设与结论打包在一起的谓词 `λ A → IsOrd A → rank A ≡ A` 设立，因为步进确实需要它：要比较 rank A 与 A，必须知道序数 A 的成员本身也是序数。于是步进在收到递归等式 `rank y ≡ y` 之外，还收到证书 `IsOrd A`，并返回在 `A` 处的等式。
<!--ja-->
定理は、ランクがすべての順序数を固定することを、同値ではなくパスとして述べます。帰納は、順序数性の仮定と結論を一つにまとめた述語 `λ A → IsOrd A → rank A ≡ A` で立てられます。ステップがこれを実際に必要とするからです。rank A と A を比べるには、順序数 A の要素自身も順序数であることを知らねばなりません。そこでステップは、再帰的な等式 `rank y ≡ y` に加えて証明書 `IsOrd A` を受け取り、`A` での等式を返します。
<!--/-->

```agda
rank-fix : (A : S) → IsOrd A → rank A ≡ A
rank-fix = ∈-induction {P = λ A → IsOrd A → rank A ≡ A} step
  where
  step : (A : S) → (∀ y → y ∈ᵗ A → IsOrd y → rank y ≡ y)
       → IsOrd A → rank A ≡ A
```

<!--en-->
The equality itself comes from `extensionalV`, which turns a pointwise equivalence of membership into a path of sets, and `⇔toPath` packages the two directions. the two sets being compared stay folded. The forward direction `toA` is none other than `rank-upper` at `β = A`: the ordinal bound on member ranks is `A` itself, and the bounding hypothesis is produced on the fly from the induction hypothesis.
<!--zh-->
等式本身来自 `extensionalV`，它把逐点的隶属等价变成集合的路径，`⇔toPath` 打包两个方向。被比较的两个集合保持不展开。向前的方向 `toA` 不是别的，正是取 `β = A` 的 `rank-upper`：作用在成员秩上的序数界就是 `A` 自身，而界定假设由归纳假设当场构造。
<!--ja-->
等式そのものは `extensionalV` から来ます。これは所属の各点ごとの同値を集合のパスに変え、`⇔toPath` が二つの方向をまとめます。比較される二つの集合は展開されないまま保たれます。順方向の `toA` はほかでもなく `β = A` とした `rank-upper` です。要素のランクへの順序数の上界は `A` そのものであり、上界の仮定は帰納仮定からその場で作られます。
<!--/-->

```agda
  step A IH ordA = extensionalV (λ x → ⇔toPath (toA x) (fromA x))
    where
    toA : (x : S) → ⟨ x ∈ˢ rank A ⟩ → ⟨ x ∈ˢ A ⟩
    toA = rank-upper A A ordA
      (λ y hy → subst (λ w → ⟨ w ∈ˢ A ⟩)
```

<!--en-->
Both bounding directions lean on the same fact, `mem-ord`: a member of the ordinal A is again an ordinal, so the induction hypothesis applies to it. For `toA`, the hypothesis required by `rank-upper` is `rank y ∈ˢ A`; since `rank y ≡ y` by IH and `y ∈ˢ A` is given, the transport lands it. For `fromA`, the reverse holds: `rank-mono x A x∈A` gives `rank x ∈ˢ rank A`, and the path `rank x ≡ x` from the IH transports it to `x ∈ˢ rank A`. Every ingredient is now in place, and the path `rank A ≡ A` follows.
<!--zh-->
两个方向都依赖同一事实 `mem-ord`：序数 A 的成员仍是序数，故归纳假设适用于它。对 `toA`，`rank-upper` 要求的假设是 `rank y ∈ˢ A`；由归纳假设 `rank y ≡ y` 且已给 `y ∈ˢ A`，传输即可落位。对 `fromA`，方向相反：`rank-mono x A x∈A` 给出 `rank x ∈ˢ rank A`，而归纳假设的路径 `rank x ≡ x` 把它传输成 `x ∈ˢ rank A`。至此所有材料齐备，路径 `rank A ≡ A` 随之成立。
<!--ja-->
両方向とも同じ事実 `mem-ord` に依存します。順序数 A の要素は再び順序数であり、したがって帰納仮定がそれに適用できます。`toA` に対して `rank-upper` が要求する仮定は `rank y ∈ˢ A` です。帰納仮定により `rank y ≡ y` であり、`y ∈ˢ A` は与えられているので、輸送で収まります。`fromA` では逆向きです。`rank-mono x A x∈A` が `rank x ∈ˢ rank A` を与え、帰納仮定のパス `rank x ≡ x` がそれを `x ∈ˢ rank A` へ輸送します。これで材料がそろい、パス `rank A ≡ A` が従います。
<!--/-->

```agda
        (sym (IH y hy (mem-ord {A = A} ordA y hy))) hy)

    fromA : (x : S) → ⟨ x ∈ˢ A ⟩ → ⟨ x ∈ˢ rank A ⟩
    fromA x x∈A = subst (λ w → ⟨ w ∈ˢ rank A ⟩)
      (IH x x∈A (mem-ord {A = A} ordA x x∈A)) (rank-mono x A x∈A)
```

<!--en-->
## Recap

`rank`{.Agda} measures every set by an ordinal (`rank-ord`{.Agda}) and fixes the ordinals themselves (`rank-fix`{.Agda}), which show that it is an ordinal-valued measure agreeing with each ordinal. Both proofs are membership inductions on regularity, so the chapter uses no additional assumptions. It gives a strict ordinal-valued measure of membership and the fixed-point law needed when the measured set is already an ordinal.
<!--zh-->
## 小结

`rank`{.Agda} 以序数度量每个集合 (`rank-ord`{.Agda})，并固定序数自身 (`rank-fix`{.Agda})，二者表明它是与每个序数一致的序数值度量。两个证明都是正则性上的成员归纳，故本章不引入任何额外假设。它给出沿成员关系严格增长的序数值度量，以及被测集合本身为序数时所需的不动点律。
<!--ja-->
## まとめ

`rank`{.Agda} はすべての集合を順序数で測り (`rank-ord`{.Agda})、順序数自身を固定します (`rank-fix`{.Agda})。この二つは、ランクが各順序数と一致する順序数値尺度であることを示します。どちらの証明も正則性公理の上の所属帰納であり、本章は追加の仮定を一切使いません。これにより、所属に沿って狭義に増加する順序数値尺度と、対象が順序数である場合の不動点法則が得られます。
<!--/-->
