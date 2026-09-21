<!--en-->
# Ordinals below a successor cardinal inject into its base

A successor cardinal is the first cardinal strictly beyond its base. Suppose `δ` is the successor cardinal of `κ` inside `L`. This chapter proves that every ordinal `α ∈ δ` admits an internal injection into `κ`. The proof combines well-founded induction with ordinal trichotomy. Excluded middle has two precise roles: it supplies the trichotomy of ordinals, and in the case `κ ∈ α` it turns the failure of cardinality into the mere existence of a smaller target.
<!--zh-->
# 后继基数以下的序数单射到其基数

后继基数是严格超过其基数的第一个基数。假设 `δ` 是 `L` 内 `κ` 的后继基数，本章证明每个序数 `α ∈ δ` 都有到 `κ` 的内部单射。证明把良基归纳与序数三分法结合起来。排中律有两项明确作用：给出序数三分法；并在 `κ ∈ α` 的情形，把「`α` 不是基数」转化为「仅仅存在一个更小的目标」。
<!--ja-->
# 後続基数より小さい順序数をその基数へ単射する

後続基数は、もとの基数を真に上回る最初の基数である。`δ` が `L` の中で `κ` の後続基数であると仮定する。本章では、任意の順序数 `α ∈ δ` から `κ` への内部単射があることを証明する。証明は整礎帰納法と順序数の三分法を組み合わせる。排中律には二つの明確な役割がある。順序数の三分法を与えることと、`κ ∈ α` の場合に、`α` が基数でないことを、より小さい行き先が単に存在するという形へ変えることである。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Classical using ( LEM )

module L.GCH.BelowSuccessorCardinal {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

```

<!--en-->
Fix one universe level and an instance of excluded middle at the level of the propositions used by the hierarchy. The classical hypothesis is explicit and precisely leveled. It is used first through ordinal trichotomy and later through a direct decision of `Ex`; the remaining ingredients are structural facts about `V`, `L`, ordinals and internal injections.
<!--zh-->
固定一个宇宙层级，并假设在层级所用的命题层上成立排中律。这个经典假设是显式的，其层级也有精确规定。证明先通过序数三分法使用它，随后又用它直接判定 `Ex`；其余材料都是关于 `V`、`L`、序数和内部单射的结构性事实。
<!--ja-->
宇宙レベルを一つ固定し、階層で使われる命題のレベルにおける排中律を仮定する。この古典的仮定は明示され、そのレベルも正確に定められている。証明では、まず順序数の三分法を通して使い、後に `Ex` を直接判定するためにもう一度使う。残りの材料は `V`、`L`、順序数、内部単射についての構造的事実である。
<!--/-->

```agda
open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ; regularityV; ∈-irrefl )
open import L.Constructible {ℓ} using ( 𝒮ʟ; IsOrd; isL )
open import L.Ordinal {ℓ} using ( mem-ord )
open import L.Ordinal.Linear {ℓ} lem using ( Tri; ord-tri )
```

<!--en-->
The argument moves between two structures. The ambient hierarchy supplies well-founded membership and its irreflexivity. The constructible universe supplies the ordinal and cardinal predicates. Ordinal trichotomy compares the current ordinal with `κ`, while inclusion coding and transitivity compose the resulting internal injections.
<!--zh-->
论证在两个结构之间往返。外围层级提供良基的成员关系及其不可反性；可构造宇宙提供序数与基数谓词。序数三分法比较当前序数与 `κ`，包含关系的编码和单射的传递性则构造并复合所得的内部单射。
<!--ja-->
議論は二つの構造の間を行き来する。周囲の階層は整礎的な所属関係とその非反射性を与え、構成可能宇宙は順序数と基数の述語を与える。順序数の三分法が現在の順序数と `κ` を比較し、包含の符号化と単射の推移性が内部単射を構成して合成する。
<!--/-->

```agda
open import L.Cardinal {ℓ} lem using ( InjL; SuccCardL; IsCardinalL )
open import L.InjectionComposition {ℓ} lem using ( inclusion-coded; injl-trans )
```

<!--en-->
The exceptional branch produces only a truncated witness. Accordingly, the proof uses sums and the empty type to analyze a decision, propositional truncation to state mere existence, and well-founded induction to descend through membership. These logical forms match the conclusion `InjL`, which is itself propositionally truncated.
<!--zh-->
特殊分支只产生一个截断的见证。因此，证明用和类型与空类型分析判定，用命题截断表达仅仅存在，并用良基归纳沿成员关系下降。这些逻辑形式与结论 `InjL` 相配，因为 `InjL` 本身也是命题截断。
<!--ja-->
例外となる分岐が与えるのは、切り詰められた証人だけである。そのため、証明は和型と空型で判定を場合分けし、命題的切り詰めで単なる存在を表し、整礎帰納法で所属関係を降りる。これらの論理形式は、命題的に切り詰められた結論 `InjL` と一致する。
<!--/-->

```agda
import Cubical.Induction.WellFounded as WF

open hPropStructure 𝒮ᵥ using ( _∈ˢ_ )
```

<!--en-->
Write `SV.S` for the carrier of the ambient hierarchy. Membership induction takes place on this type: an element is a set of `V`, without yet carrying evidence that it belongs to `L`.
<!--zh-->
以 `SV.S` 表示外围层级的论域。成员归纳在这个类型上进行：它的元素是 `V` 中的集合，此时还没有附带该集合属于 `L` 的证书。
<!--ja-->
周囲の階層の論域を `SV.S` と書く。所属に関する帰納法はこの型の上で行われる。その要素は `V` の集合であり、この時点では `L` に属する証明をまだ伴わない。
<!--/-->

```agda
module SV = hPropStructure 𝒮ᵥ using ( S )
```

<!--en-->
Write `SL.S` for the carrier of the constructible universe. Its elements are pairs consisting of an ambient set and a certificate of constructibility. The predicates `SuccCardL`, `IsCardinalL` and `InjL` concern elements of this carrier.
<!--zh-->
以 `SL.S` 表示可构造宇宙的论域。它的元素是由外围集合及其可构造性证书组成的依值对；`SuccCardL`、`IsCardinalL` 与 `InjL` 都以这个论域的元素为对象。
<!--ja-->
構成可能宇宙の論域を `SL.S` と書く。その要素は、周囲の集合とその構成可能性の証明からなる依存対である。`SuccCardL`、`IsCardinalL`、`InjL` はいずれもこの論域の要素について述べる。
<!--/-->

```agda
module SL = hPropStructure 𝒮ʟ using ( S )
```

<!--en-->
Assume that `δ` is the successor cardinal of `κ`, and let `α` be an ordinal belonging to `δ`. The goal `InjL α κ` says merely that an internal injection from `α` to `κ` exists. This is the precise form of the familiar statement that every ordinal below the successor of `κ` has cardinality at most `κ`.
<!--zh-->
假设 `δ` 是 `κ` 的后继基数，并设序数 `α` 属于 `δ`。目标 `InjL α κ` 仅仅断言存在一个从 `α` 到 `κ` 的内部单射；这正是「`κ` 的后继基数以下每个序数的基数都不超过 `κ`」的形式化表述。
<!--ja-->
`δ` が `κ` の後続基数であり、順序数 `α` が `δ` に属すると仮定する。目標 `InjL α κ` は、`α` から `κ` への内部単射が単に存在することを述べる。これは、`κ` の後続基数より小さい順序数の濃度はすべて `κ` 以下である、という主張の正確な形である。
<!--/-->

```agda
below-succ-injects :
    (κ δ : SL.S) → SuccCardL δ κ
  → (α : SL.S) → IsOrd (fst α) → ⟨ fst α ∈ˢ fst δ ⟩
  → InjL α κ
```

<!--en-->
Well-founded induction is performed on the underlying set of `α`. The predicate `P a` restores exactly the data needed to regard an ambient set `a` as the ordinal under consideration: a constructibility certificate, ordinalhood, and membership in `δ`. Under those assumptions it asks for an internal injection from `(a , la)` to `κ`.
<!--zh-->
良基归纳作用于 `α` 的底层集合。谓词 `P a` 恰好补回把外围集合 `a` 视为当前序数所需的数据：可构造性证书、序数性以及属于 `δ` 的证明。在这些假设下，它要求从 `(a , la)` 到 `κ` 的内部单射。
<!--ja-->
整礎帰納法は `α` の基礎となる集合に施される。述語 `P a` は、周囲の集合 `a` を考察中の順序数とみなすために必要なデータ、すなわち構成可能性の証明、順序数であること、`δ` に属することをちょうど補う。これらの仮定のもとで、`(a , la)` から `κ` への内部単射を要求する。
<!--/-->

```agda
below-succ-injects κ δ (ordδ , _ , κ∈δ , least) α =
  WF.WFI.induction regularityV {P = P} step (fst α) (snd α)
  where
  P : SV.S → Type (ℓ-suc ℓ)
  P a = (la : ⟨ isL a ⟩) → IsOrd a → ⟨ a ∈ˢ fst δ ⟩ → InjL (a , la) κ
```

<!--en-->
Because `κ ∈ δ` and `δ` is an ordinal, `κ` is itself an ordinal. The induction step may therefore apply ordinal trichotomy to `a` and the underlying set of `κ`. Its induction hypothesis is available at every member of `a`, which is exactly what the third trichotomy branch will require.
<!--zh-->
由于 `κ ∈ δ` 且 `δ` 是序数，`κ` 本身也是序数。因此归纳步骤可以对 `a` 与 `κ` 的底层集合应用序数三分法。归纳假设在 `a` 的每个成员处都可用，这恰好是三分法第三个分支所需的条件。
<!--ja-->
`κ ∈ δ` であり `δ` が順序数なので、`κ` 自身も順序数である。したがって帰納段階では、`a` と `κ` の基礎となる集合に順序数の三分法を適用できる。帰納仮定は `a` の各要素で利用でき、これは三分法の第三の分岐が必要とするものである。
<!--/-->

```agda

  ordκ : IsOrd (fst κ)
  ordκ = mem-ord {A = fst δ} ordδ (fst κ) κ∈δ

  step : (a : SV.S) → (∀ a' → ⟨ a' ∈ˢ a ⟩ → P a') → P a
  step a ih la orda a∈δ = go (ord-tri a orda (fst κ) ordκ)
    where
```

<!--en-->
Pair the ambient set `a` with its certificate `la` to obtain the corresponding element `α'` of `L`. This keeps the well-founded induction on the simple carrier `SV.S`, while cardinality statements are made in their proper domain `SL.S`.
<!--zh-->
把外围集合 `a` 与证书 `la` 配成依值对，便得到 `L` 中对应的元素 `α'`。这样，良基归纳仍在较简单的论域 `SV.S` 上进行，而基数陈述则位于其应属的论域 `SL.S` 中。
<!--ja-->
周囲の集合 `a` と証明 `la` を対にして、`L` の対応する要素 `α'` を得る。これにより、整礎帰納法は単純な論域 `SV.S` 上で行いながら、濃度に関する主張は本来の論域 `SL.S` で述べられる。
<!--/-->

```agda
    α' : SL.S
    α' = a , la
```

<!--en-->
Consider the branch `κ ∈ a`. If `α'` were an `L`-cardinal, the leastness clause of `SuccCardL δ κ` would place `δ` inside `α'`. Since `a ∈ δ`, this would give `a ∈ a`, contradicting the irreflexivity of membership. Thus `α'` cannot be a cardinal in this branch.

The type `Ex` states the relevant negation of cardinality positively: merely, there is some `γ ∈ α'` into which `α'` internally injects.
<!--zh-->
考虑 `κ ∈ a` 的分支。如果 `α'` 是 `L`-基数，那么 `SuccCardL δ κ` 的最小性条款会使 `δ` 包含于 `α'`。又因 `a ∈ δ`，便得到 `a ∈ a`，与成员关系的不可反性矛盾。因此在这个分支中，`α'` 不可能是基数。

类型 `Ex` 以肯定形式表达这里所需的非基数性：仅仅存在某个 `γ ∈ α'`，使 `α'` 内部单射到 `γ`。
<!--ja-->
`κ ∈ a` の分岐を考える。もし `α'` が `L`-基数なら、`SuccCardL δ κ` の最小性により `δ` は `α'` に含まれる。`a ∈ δ` なので `a ∈ a` が従い、所属の非反射性に反する。したがってこの分岐では `α'` は基数ではありえない。

型 `Ex` は、ここで必要な非基数性を肯定的に表す。すなわち、`α'` が内部単射するような `γ ∈ α'` が単に存在する、という主張である。
<!--/-->

```agda
    not-card : ⟨ fst κ ∈ˢ a ⟩ → IsCardinalL α' → ⊥₀
    not-card κ∈a c = ∈-irrefl a (least α' orda c κ∈a α' a∈δ)

    Ex : Type (ℓ-suc ℓ)
    Ex = ∥ Σ[ γ ∈ SL.S ] (⟨ fst γ ∈ˢ a ⟩ × InjL α' γ) ∥₁
```

<!--en-->
Apply excluded middle to the proposition `Ex`. If it holds, the required mere witness is already present. If it is refuted, then every proposed member `γ` and injection from `α'` to `γ` yields a contradiction; this is precisely the condition saying that the ordinal `α'` is a cardinal.
<!--zh-->
对命题 `Ex` 应用排中律。若它成立，所需的仅仅见证已经得到；若它被反驳，那么任取成员 `γ` 以及从 `α'` 到 `γ` 的单射都会导出矛盾，这恰好是说序数 `α'` 为基数的条件。
<!--ja-->
命題 `Ex` に排中律を適用する。成立するなら、必要な単なる証人はすでに得られている。反証されるなら、任意の要素 `γ` と `α'` から `γ` への単射が矛盾を導く。これは順序数 `α'` が基数であるという条件にほかならない。
<!--/-->

```agda
    some-γ : ⟨ fst κ ∈ˢ a ⟩ → Ex
    some-γ κ∈a = decide (lem (Ex , squash₁))
      where
      decide : Dec Ex → Ex
```

<!--en-->
The refutation branch is impossible by `not-card`, so both outcomes produce `Ex`. At this step excluded middle provides the case distinction; it does not remove the truncation or choose a particular `γ`.
<!--zh-->
反驳分支与 `not-card` 矛盾，所以两种结果都给出 `Ex`。在这一步，排中律给出分支分析；它没有消去截断，也没有选出某个特定的 `γ`。
<!--ja-->
反証の分岐は `not-card` と矛盾するため、どちらの結果からも `Ex` が得られる。この段階で排中律が与えるのは場合分けである。切り詰めを取り除くことも、特定の `γ` を選ぶこともない。
<!--/-->

```agda
      decide (yes e) = e
      decide (no ¬e) =
        ⊥₀-rec (not-card κ∈a (λ γ γ∈a inj → ¬e ∣ γ , γ∈a , inj ∣₁))
```

<!--en-->
A witness of the untruncated content of `Ex` consists of `γ ∈ a` and an internal injection from `α'` to `γ`. Since members of an ordinal are ordinals and `δ` is transitive, `γ` again satisfies the induction predicate. The induction hypothesis supplies an injection from `γ` to `κ`, and transitivity of internal injection composes the two.
<!--zh-->
`Ex` 的未截断内容给出 `γ ∈ a` 以及从 `α'` 到 `γ` 的内部单射。序数的成员仍是序数，并且 `δ` 具有传递性，所以 `γ` 再次满足归纳谓词。归纳假设给出从 `γ` 到 `κ` 的单射，再由内部单射的传递性把两者复合。
<!--ja-->
`Ex` の切り詰め前の内容は、`γ ∈ a` と `α'` から `γ` への内部単射からなる。順序数の要素は順序数であり、`δ` は推移的なので、`γ` は再び帰納述語を満たす。帰納仮定が `γ` から `κ` への単射を与え、内部単射の推移性が二つを合成する。
<!--/-->

```agda

    from-γ : Σ[ γ ∈ SL.S ] (⟨ fst γ ∈ˢ a ⟩ × InjL α' γ) → InjL α' κ
    from-γ (γ , γ∈a , α↪γ) =
      injl-trans α' γ κ α↪γ
```

<!--en-->
To invoke the induction hypothesis at `γ`, the proof supplies all three components of `P`: constructibility is the second component of `γ`; ordinalhood follows from `γ ∈ a` and the ordinalhood of `a`; membership in `δ` follows from `γ ∈ a ∈ δ` and the transitivity of the ordinal `δ`.
<!--zh-->
在 `γ` 处调用归纳假设，需要依次提供 `P` 的三个条件：`γ` 的第二分量给出可构造性；由 `γ ∈ a` 及 `a` 的序数性得到 `γ` 的序数性；再由 `γ ∈ a ∈ δ` 及序数 `δ` 的传递性得到 `γ ∈ δ`。
<!--ja-->
`γ` で帰納仮定を使うには、`P` の三つの条件をすべて与える。構成可能性は `γ` の第二成分であり、順序数であることは `γ ∈ a` と `a` の順序数性から従い、`δ` への所属は `γ ∈ a ∈ δ` と順序数 `δ` の推移性から従う。
<!--/-->

```agda
        (ih (fst γ) γ∈a (snd γ)
            (mem-ord {A = a} orda (fst γ) γ∈a)
            (ordδ .fst γ∈a a∈δ))
```

<!--en-->
The first trichotomy branch has `a ∈ κ`. Because an ordinal is transitive, every member of `a` is then a member of `κ`; this inclusion is coded as an internal injection from `α'` to `κ`.
<!--zh-->
三分法的第一个分支是 `a ∈ κ`。序数具有传递性，所以 `a` 的每个成员也都是 `κ` 的成员；把这个包含关系编码起来，就得到从 `α'` 到 `κ` 的内部单射。
<!--ja-->
三分法の第一の分岐は `a ∈ κ` である。順序数は推移的なので、`a` の各要素は `κ` の要素でもある。この包含を符号化すれば、`α'` から `κ` への内部単射が得られる。
<!--/-->

```agda

    go : Tri a (fst κ) → InjL α' κ
    go (inl a∈κ)       =
      inclusion-coded α' κ (λ z z∈a → ordκ .fst z∈a a∈κ)
```

<!--en-->
In the equality branch, transport along `a ≡ fst κ` turns the same inclusion into the required injection. In the remaining branch `κ ∈ a`, the truncated witness supplied above is eliminated into `InjL α' κ`; this elimination is valid because `InjL` is itself a proposition.
<!--zh-->
在相等分支中，沿 `a ≡ fst κ` 搬运同一个包含关系即可得到所需单射。在余下的 `κ ∈ a` 分支中，把上面得到的截断见证消去到 `InjL α' κ`；由于 `InjL` 本身是命题，这个消去是合法的。
<!--ja-->
等しい場合には、`a ≡ fst κ` に沿って同じ包含を移送すれば、必要な単射が得られる。残る `κ ∈ a` の場合には、先に得た切り詰められた証人を `InjL α' κ` へ消去する。`InjL` 自身が命題なので、この消去は正当である。
<!--/-->

```agda
    go (inr (inl e))   =
      inclusion-coded α' κ (λ z z∈a → subst (λ w → ⟨ z ∈ˢ w ⟩) e z∈a)
    go (inr (inr κ∈a)) = rec₁ squash₁ from-γ (some-γ κ∈a)
```

<!--en-->
The three branches exhaust ordinal trichotomy. Hence every ordinal below the successor cardinal `δ` internally injects into its base `κ`. Well-founded membership permits the descent to `γ`. Excluded middle is used in two places: `ord-tri` obtains the trichotomy, and the branch above `κ` obtains the truncated smaller target.
<!--zh-->
序数三分法的三个分支至此全部闭合。因此，后继基数 `δ` 以下的每个序数都在内部单射到其基数 `κ`。成员关系的良基性使证明能够下降到 `γ`。排中律用在两处：`ord-tri` 用它取得三分法；高于 `κ` 的分支用它取得截断的小目标。
<!--ja-->
これで順序数の三分法の三つの分岐がすべて閉じる。したがって、後続基数 `δ` より小さい任意の順序数は、その基数 `κ` へ内部単射する。所属の整礎性により、証明は `γ` へ降りられる。排中律は二箇所で使われる。`ord-tri` が三分法を得る箇所と、`κ` より上の分岐が切り詰められた小さい行き先を得る箇所である。
<!--/-->
