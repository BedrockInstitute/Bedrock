<!--en-->
# An internal graph of uniform satisfaction

Let `W` be a constructible set, used both as the alphabet from which formula constants are drawn and as the range of values allowed in environments. The uniform satisfaction construction assigns to every code in `AllCodes W` the set of environments satisfying the coded formula. This chapter proves that the assignment itself has a graph inside `L`: a set whose members are precisely the ordered pairs of a formula code and its satisfaction set. The mathematical step is an instance of replacement. The uniform graph formula has a unique value over every code, so its image over the set `AllCodes W` can be collected as a set.
<!--zh-->
# 统一满足关系的内部图

设 `W` 是一个可构造集合，它既充当公式常元取值的字母表，也充当环境中各项的取值范围。统一满足关系构造为 `AllCodes W` 中的每个公式码指派一个集合，即满足该码所编码公式的所有环境。本章证明，这一指派本身在 `L` 内具有图：存在一个集合，其成员恰好是公式码与相应满足关系集组成的有序对。数学上的关键是替换公理。统一的图公式在每个公式码上都有唯一取值，因此它在集合 `AllCodes W` 上的像可以收集成集合。
<!--ja-->
# 一様な充足関係の内部グラフ

`W` を構成可能集合とし、論理式の定数が値を取るアルファベットと、環境の各成分が値を取る範囲の両方に用います。一様な充足関係の構成は、`AllCodes W` の各論理式符号に、その論理式を満たす環境の集合を割り当てます。本章では、この割り当て自身が `L` の内部にグラフを持つことを証明します。その要素は、論理式符号と対応する充足集合の順序対です。数学的な要点は置換公理です。一様なグラフ論理式は各符号の上で一意な値を持つので、集合 `AllCodes W` 上の像を一つの集合に集められます。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Classical using ( LEM )

module L.Coding.SatisfactionGraphSet {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

```

<!--en-->
Fix such a constructible set `W` and excluded middle at the proposition level required by the coding construction. Ordered pairs are formed in the ambient hierarchy, while the domain, the values and the graph all belong to the constructible carrier `S`.
<!--zh-->
固定这样的可构造集合 `W`，并假设在编码构造所需的命题层上成立排中律。有序对在外围层级中构造，而定义域、取值与图本身都属于可构造论域 `S`。
<!--ja-->
このような構成可能集合 `W` を固定し、符号化に必要な命題のレベルで排中律を仮定します。順序対は周囲の階層で構成されますが、定義域、値、グラフはいずれも構成可能な論域 `S` に属します。
<!--/-->

```agda
open import FOL.ZFStructure using ( module hPropStructure )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Coding {ℓ} using ( pr )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans )
```

<!--en-->
The domain `AllCodes W` is the constructible set of well-formed formula codes over the alphabet at `W`. Formula syntax supplies the type of the graph formula; dependent-pair extensionality will later prove uniqueness of a solution together with its satisfaction certificate.
<!--zh-->
定义域 `AllCodes W` 是可构造集合，由字母表取自 `W` 的良构公式码组成。公式语法给出图公式的类型；依值对的外延性随后用于证明「解及其满足证书」所组成的依值对具有唯一性。
<!--ja-->
定義域 `AllCodes W` は、`W` のアルファベット上の整形式な論理式符号からなる構成可能集合です。論理式の構文がグラフ論理式の型を与え、依存対の外延性が後に、解とその充足証明からなる依存対の一意性を示します。
<!--/-->

```agda
open import L.Coding.CodeSet {ℓ} lem using ( AllCodes )

open import FOL.Syntax using ( Formula )
open import Cubical.Data.Sigma using ( Σ≡Prop )
open import Cubical.Data.Vec using ( _∷_; [] )
```

<!--en-->
Membership in the cumulative hierarchy is truncated existence, so the final description of an arbitrary graph member is truncated as well. The carrier `S` is that of the constructible structure `𝒮ʟ`; each of its elements consists of an ambient set together with a certificate of constructibility.
<!--zh-->
累积层级中的成员关系表达截断的存在，因此任意图成员的最终刻画也采用截断形式。论域 `S` 来自可构造结构 `𝒮ʟ`；它的每个元素都由外围集合及其可构造性证书组成。
<!--ja-->
累積階層の所属は切り詰められた存在を表すため、任意のグラフ要素の最終的な特徴づけも切り詰められた形になります。論域 `S` は構成可能構造 `𝒮ʟ` のもので、その各要素は周囲の集合と構成可能性の証明からなります。
<!--/-->

```agda
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁ )
open import Cubical.HITs.CumulativeHierarchy.Base using ( _∈_ )

open hPropStructure 𝒮ʟ using ( S )
```

<!--en-->
The satisfaction relation used here is the inner semantics of the restricted structure `𝒮ᵥ ↾ isL`, which is the constructible structure `𝒮ʟ`. Constants are interpreted by the identity map on its carrier. Thus `_⊨_` says directly that a formula is satisfied in `L`; no comparison with the ambient semantics is used in this chapter.
<!--zh-->
这里使用的满足关系，是限制结构 `𝒮ᵥ ↾ isL` 上的内层语义，而这个限制结构就是可构造结构 `𝒮ʟ`。常元由其论域上的恒等映射解释。因此，`_⊨_` 直接表示公式在 `L` 中满足；本章不使用它与外围语义之间的比较定理。
<!--ja-->
ここで使う充足関係は、制限構造 `𝒮ᵥ ↾ isL`、すなわち構成可能構造 `𝒮ʟ` 上の内側の意味論です。定数はその論域上の恒等写像で解釈されます。したがって `_⊨_` は、論理式が `L` で満たされることを直接に表し、本章では周囲の意味論との比較定理を使いません。
<!--/-->

```agda

module AbsSF = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans using ( _^_; _⊨ᵐ_ )
open AbsSF using ( _^_ ) renaming ( _⊨ᵐ_ to _⊨_ )

```

<!--en-->
For the fixed `W`, both parameters of the uniform construction are instantiated by this same set, so the code alphabet and the range of environment values are both `W`. `Table.graph W W` is one binary formula describing the value relation uniformly over all members of `AllCodes W`, and `Table.val W W x mx` is its unique value at the particular code `x`.
<!--zh-->
对固定的 `W`，统一构造的两个参数都取这个集合，因此编码字母表与环境取值范围都是 `W`。`Table.graph W W` 是一条统一适用于 `AllCodes W` 全体成员的二元公式，用来描述取值关系；`Table.val W W x mx` 则是它在特定公式码 `x` 处的唯一取值。
<!--ja-->
固定した `W` に対し、一様な構成の二つのパラメータをこの同じ集合で具体化します。したがって、符号のアルファベットと環境の値域はいずれも `W` です。`Table.graph W W` は `AllCodes W` のすべての要素に一様に適用される二項論理式であり、値の関係を記述します。`Table.val W W x mx` は、特定の符号 `x` におけるその一意な値です。
<!--/-->

```agda
open import L.Coding.UniformSatisfaction {ℓ} lem using ( module Table )
open import L.Recursion {ℓ} lem using ( Recursion )
open import L.Recursion.Graph {ℓ} lem using () renaming ( module Graph to MapGraph )

module SatGraph (W : S) where
```

<!--en-->
For a code `x` with membership certificate `mx`, write this unique value as `valOf x mx`. The equation `valOf≡` identifies it definitionally with `Table.val W W x mx`. The notation isolates the mathematical function whose graph is to be collected: a domain member is sent to its satisfaction set.
<!--zh-->
给定公式码 `x` 及其成员证书 `mx`，把这个唯一取值记作 `valOf x mx`。等式 `valOf≡` 在定义上把它识别为 `Table.val W W x mx`。这个记号单独标出将要收集其图的数学函数：每个定义域成员被送到相应的满足关系集。
<!--ja-->
論理式符号 `x` とその所属証明 `mx` に対し、この一意な値を `valOf x mx` と書きます。等式 `valOf≡` は、それを定義上 `Table.val W W x mx` と同一視します。この記法により、グラフを集める対象の数学的な関数、すなわち定義域の要素をその充足集合へ送る関数が明確になります。
<!--/-->

```agda
  opaque
    valOf : (x : S) → ⟨ fst x ∈ fst (AllCodes W) ⟩ → S
    valOf x mx = Table.val W W x mx

    valOf≡ : (x : S) (mx : ⟨ fst x ∈ fst (AllCodes W) ⟩) → valOf x mx ≡ Table.val W W x mx
    valOf≡ x mx = refl
```

<!--en-->
Let `gr` be the single binary formula `Table.graph W W`. Its first free position receives a proposed satisfaction set and its second receives a formula code. The relation it defines is therefore the candidate graph relation between codes and values.
<!--zh-->
令 `gr` 为同一条二元公式 `Table.graph W W`。它的第一个自由位置放置候选满足关系集，第二个自由位置放置公式码。因此，它定义的关系正是公式码与取值之间的候选图关系。
<!--ja-->
`gr` を一つの二項論理式 `Table.graph W W` とします。第一の自由な位置には充足集合の候補が、第二の位置には論理式符号が入ります。したがって、この論理式が定める関係は、符号と値の間のグラフ関係の候補です。
<!--/-->

```agda

  private
    opaque
      unfolding valOf
      gr : Formula S 2
      gr = Table.graph W W
```

<!--en-->
Two facts make `gr` functional. Existence says that `gr` holds of the table value and its code; this is the witness extracted from `Table.funct`. Uniqueness says that any other `y` satisfying the same graph formula equals `valOf x mx`; it is the symmetry of the table's uniqueness theorem.
<!--zh-->
两条事实使 `gr` 成为函数图。存在性说明表中的取值与其公式码满足 `gr`，见证取自 `Table.funct`；唯一性说明任何满足同一图公式的 `y` 都等于 `valOf x mx`，它由表的唯一性定理取对称得到。
<!--ja-->
二つの事実により `gr` は関数的になります。存在性は、表の値とその論理式符号について `gr` が成り立つことを述べ、証人は `Table.funct` から得ます。一意性は、同じグラフ論理式を満たす任意の `y` が `valOf x mx` に等しいことを述べ、表の一意性定理を対称にして得ます。
<!--/-->

```agda

      defines' : (x : S) (mx : ⟨ fst x ∈ fst (AllCodes W) ⟩) → ⟨ (valOf x mx ∷ x ∷ []) ⊨ gr ⟩
      defines' x mx = Table.funct W W x mx .fst .snd

      only' : (x : S) (mx : ⟨ fst x ∈ fst (AllCodes W) ⟩) (y : S) → ⟨ (y ∷ x ∷ []) ⊨ gr ⟩ → y ≡ valOf x mx
      only' x mx y h = sym (Table.val-uniq W W x mx y h)
```

<!--en-->
For each code, the type of solutions to `gr` is contractible. Its centre is the pair consisting of `valOf x mx` and the proof `defines'` that this value satisfies `gr`. Given another solution `(y , h)`, `only'` identifies the values. The remaining components are proofs of a proposition, so `Σ≡Prop` lifts equality of values to equality of the complete dependent pairs. This contractibility is exactly the functional premise needed for replacement.
<!--zh-->
对每个公式码，满足 `gr` 的解类型都是可缩的。它的中心是依值对，由取值 `valOf x mx` 与该取值满足 `gr` 的证明 `defines'` 组成。若另有解 `(y , h)`，`only'` 先识别两个取值；余下的分量都是同一命题的证明，因而 `Σ≡Prop` 把取值的相等提升为两个完整依值对的相等。这个可缩性正是应用替换所需的函数性前提。
<!--ja-->
各論理式符号について、`gr` の解の型は可縮です。その中心は、値 `valOf x mx` と、この値が `gr` を満たす証明 `defines'` からなる依存対です。別の解 `(y , h)` があれば、`only'` がまず二つの値を同一視します。残る成分は同じ命題の証明なので、`Σ≡Prop` が値の等しさを完全な依存対の等しさへ持ち上げます。この可縮性こそ、置換に必要な関数性の前提です。
<!--/-->

```agda

    M : Recursion
    M = record
      { dom = AllCodes W ; graph = gr
      ; funct = λ x mx → (valOf x mx , defines' x mx)
          , λ { (y , h) → Σ≡Prop (λ w → snd ((w ∷ x ∷ []) ⊨ gr)) (sym (only' x mx y h)) } }
```

<!--en-->
Replacement now applies to the functional relation `gr` over the constructible set `AllCodes W`. It collects the ordered pairs `pr (fst x) (fst (valOf x mx))` into a constructible set, denoted `pairs`. Thus the graph is internal to `L`: both its domain and every value are constructible, and replacement forms their pair relation as one set.
<!--zh-->
现在可以对可构造集合 `AllCodes W` 上的函数关系 `gr` 应用替换。它把有序对 `pr (fst x) (fst (valOf x mx))` 收集成可构造集合，记作 `pairs`。因此这张图位于 `L` 内部：定义域及每个取值都是可构造的，替换把它们的配对关系组成一个集合。
<!--ja-->
これで、構成可能集合 `AllCodes W` 上の関数的関係 `gr` に置換を適用できます。順序対 `pr (fst x) (fst (valOf x mx))` が一つの構成可能集合に集められ、これを `pairs` と書きます。したがってグラフは `L` の内部にあります。定義域と各値が構成可能であり、置換がそれらの対関係を一つの集合にするからです。
<!--/-->

```agda

    module G = MapGraph M using ( F; F-in; pair-out )

  opaque
    pairs : S
    pairs = G.F
```

<!--en-->
Every code in `AllCodes W` contributes its graph pair. Concretely, `pairs-in` proves that the ordered pair of the underlying code and the underlying satisfaction set belongs to `pairs`.
<!--zh-->
`AllCodes W` 中的每个公式码都贡献一个图上的有序对。具体而言，`pairs-in` 证明由底层公式码与底层满足关系集组成的有序对属于 `pairs`。
<!--ja-->
`AllCodes W` の各論理式符号は、グラフの順序対を一つ与えます。具体的に `pairs-in` は、基礎となる符号と基礎となる充足集合の順序対が `pairs` に属することを証明します。
<!--/-->

```agda

    pairs-in : (x : S) (mx : ⟨ fst x ∈ fst (AllCodes W) ⟩) → ⟨ pr (fst x) (fst (valOf x mx)) ∈ fst pairs ⟩
    pairs-in = G.F-in
```

<!--en-->
Conversely, suppose an ordered pair `pr (fst x) (fst y)` belongs to `pairs`. The fibre of the replacement image is proposition-valued, so its truncated witness may be eliminated into the dependent pair stating that `x` is in `AllCodes W` and that `y` equals the unique value there. This is the untruncated conclusion of `pairs-out`.
<!--zh-->
反过来，假设有序对 `pr (fst x) (fst y)` 属于 `pairs`。替换像的纤维取值于命题，因此可以把截断见证消去到这样一个依值对：`x` 属于 `AllCodes W`，并且 `y` 等于该处的唯一取值。这就是 `pairs-out` 给出的未截断结论。
<!--ja-->
逆に、順序対 `pr (fst x) (fst y)` が `pairs` に属すると仮定します。置換像のファイバーは命題値なので、切り詰められた証人を、`x` が `AllCodes W` に属し、`y` がそこでの一意な値に等しいことを述べる依存対へ消去できます。これが `pairs-out` の切り詰めなしの結論です。
<!--/-->

```agda

    pairs-out : (x y : S) → ⟨ pr (fst x) (fst y) ∈ fst pairs ⟩
              → Σ[ mx ∈ ⟨ fst x ∈ fst (AllCodes W) ⟩ ] (fst y ≡ fst (valOf x mx))
    pairs-out = G.pair-out
```

<!--en-->
An arbitrary member of `pairs` need not arrive already displayed as an ordered pair. The general image theorem therefore yields only a truncated description: merely, there are a code `x`, a membership certificate `mx`, and an equality exhibiting the member as the pair of `x` and its value. This is precisely `pairs-shape`; the truncation is inherited from membership in the replacement image.
<!--zh-->
`pairs` 的任意成员未必已经以有序对的形式给出。因此，一般的像定理只产生截断的刻画：仅仅存在公式码 `x`、成员证书 `mx` 以及一个等式，把该成员呈现为 `x` 与其取值组成的有序对。这正是 `pairs-shape`；其中的截断来自替换像的成员关系。
<!--ja-->
`pairs` の任意の要素が、最初から順序対として表示されているとは限りません。そのため、一般の像定理が与える特徴づけは切り詰められています。すなわち、論理式符号 `x`、所属証明 `mx`、その要素を `x` と値の順序対として表示する等式が単に存在します。これが `pairs-shape` であり、切り詰めは置換像への所属から受け継がれます。
<!--/-->

```agda
    pairs-shape : (e : S) → ⟨ fst e ∈ fst pairs ⟩
                → ∥ Σ[ x ∈ S ] Σ[ mx ∈ ⟨ fst x ∈ fst (AllCodes W) ⟩ ] (fst e ≡ pr (fst x) (fst (valOf x mx))) ∥₁
    pairs-shape e h = MapGraph.F-out M (fst e) h
```

<!--en-->
The set `pairs` is therefore the internal graph of uniform satisfaction for formulas whose constants and environments range over `W`. Existence and uniqueness of the uniform value make the relation functional; replacement turns that relation into a set of `L`; and the three membership theorems characterize the set both for displayed pairs and for arbitrary members.
<!--zh-->
因此，`pairs` 是统一满足关系的内部图，其中公式常元与环境取值都取自 `W`。统一取值的存在唯一性使关系成为函数；替换把这个关系化为 `L` 中的集合；三条成员定理则分别针对已经呈现的有序对和任意成员刻画这个集合。
<!--ja-->
したがって `pairs` は、論理式の定数と環境の値がともに `W` から取られる一様な充足関係の内部グラフです。一様な値の存在と一意性が関係を関数的にし、置換がその関係を `L` の集合にし、三つの所属定理が、表示された順序対と任意の要素の両方についてこの集合を特徴づけます。
<!--/-->
