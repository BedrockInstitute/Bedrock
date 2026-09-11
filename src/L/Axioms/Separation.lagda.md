<!--en-->
# Separation and replacement, bounded

For a constructible set `a` and a Δ₀ formula `φ`, separation asks for a constructible set containing exactly the members of `a` that satisfy `φ`. Replacement starts with a functional two-variable Δ₀ formula and asks for a constructible set containing exactly its values on `a`. Both constructions must first place the constants named by the formula, and in the replacement case its possible values, inside a common ordinal stage. At that stage, constant relabelling and Δ₀ absoluteness connect definability in the stage with satisfaction in the constructible model.
<!--zh-->
# 有界分离与替换

给定可构造集 `a` 与 Δ₀ 公式 `φ`，分离要求得到一个可构造集，其成员恰为 `a` 中满足 `φ` 的元素。替换从函数性的二元 Δ₀ 公式出发，要求得到一个可构造集，其成员恰为该公式在 `a` 上的取值。两种构造都先要把公式指名的常元置于共同的序数层；替换还要把可能的取值置于其中。在该层上，常元改名与 Δ₀ 绝对性把层内的可定义性同可构造模型中的满足关系连接起来。
<!--ja-->
# 有界な分出公理と置換公理

構成可能集合 `a` と Δ₀ 論理式 `φ` に対し、分出公理は、`φ` を満たす `a` の要素だけを要素とする構成可能集合を求めます。置換公理は関数的な二変数 Δ₀ 論理式から始め、その `a` 上の値だけを要素とする構成可能集合を求めます。どちらの構成でも、まず論理式が名指す定数を共通の順序数段階に置く必要があり、置換の場合はさらに値の候補もそこに置きます。その段階で、定数の改名と Δ₀ 絶対性が、段階内の定義可能性を構成可能モデルでの充足に結びつけます。
<!--/-->

<!--en-->
The module works at a fixed universe level `ℓ` and receives `lem : LEM (ℓ-suc ℓ)`. This hypothesis is available to the stage construction used later; every theorem exported from this parameterized module retains that dependency.
<!--zh-->
模块固定宇宙层级 `ℓ`，并接受 `lem : LEM (ℓ-suc ℓ)`。后文的层构造可以使用这一假设；从这个带参数模块导出的每条定理都保留该依赖。
<!--ja-->
このモジュールは宇宙レベル `ℓ` を固定し、`lem : LEM (ℓ-suc ℓ)` を受け取ります。この仮定は後で用いる段階の構成に渡され、このパラメータ付きモジュールから得られる各定理はその依存を保ちます。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module L.Axioms.Separation {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where
```

<!--en-->
The formulas have constants in the constructible carrier and free variables indexed by their arity. The predicate `Δ₀ φ` certifies that every quantifier in `φ` is bounded. The constructors displayed here are the particular membership, conjunction, and bounded-existential certificates used in the separation and replacement formulas below.
<!--zh-->
公式的常元取自可构造载体，自由变元则由公式的元数编索引。谓词 `Δ₀ φ` 证明 `φ` 中每个量词都有界。这里列出的构造子分别为属于、合取与有界存在提供证书，正好用于下文的分离与替换公式。
<!--ja-->
論理式の定数は構成可能な台から取り、自由変数は論理式のアリティで添字づけられます。述語 `Δ₀ φ` は、`φ` のすべての量化子が有界であることを証明します。ここに挙げる構成子は、所属、連言、有界存在に対する証明を与え、以下の分出と置換の論理式で用いられます。
<!--/-->

```agda

open import FOL.ZFStructure using ( Transitive; module hPropStructure )
open import FOL.Syntax
  using ( Term; con; var; Formula; _∈̇_; _≐_; _∧̇_; _∨̇_; _⇒̇_; ⊥̇
        ; ∃̇_; ∀̇_; ∀̇∈; ∃̇∈ )
open import FOL.LevyHierarchy using ( Δ₀; δ-∈; δ-∧; δ-∃∈ )
```

<!--en-->
A second condition concerns constants rather than quantifiers. `BoundedTm P t` and `BoundedFo P φ` record that each constant occurring in a term or formula satisfies `P`; they apply equally to formulas with bounded or unbounded quantifiers. Given such a certificate, `Relabel` replaces each constant by a name in a chosen stage, while `⊨-map` relates satisfaction before and after the corresponding semantic map.
<!--zh-->
另一个条件约束常元而非量词。`BoundedTm P t` 与 `BoundedFo P φ` 记录词项或公式中出现的每个常元都满足 `P`；它们同样适用于含有界或无界量词的公式。给定这种证书，`Relabel` 把每个常元替换为所选层中的名称，`⊨-map` 则联系相应语义映射前后的满足关系。
<!--ja-->
もう一つの条件は量化子ではなく定数を制約します。`BoundedTm P t` と `BoundedFo P φ` は、項または論理式に現れる各定数が `P` を満たすことを記録し、有界量化子をもつ論理式にも無境界量化子をもつ論理式にも適用されます。その証明があれば、`Relabel` は各定数を選んだ段階内の名前に置き換え、`⊨-map` は対応する意味写像の前後の充足を結びます。
<!--/-->

```agda
open import FOL.Manipulation.ConstantBounding
  using ( BoundedTm; BoundedFo; BoundedTm-mono; BoundedFo-mono; module Relabel )
open import FOL.Manipulation.ConstantMapping using ( mapFo )
open import FOL.Manipulation.Relabelling using ( ⊨-map )
import FOL.Semantics
```

<!--en-->
The semantic comparison uses two structures. `𝒮ᵥ` interprets formulas in the ambient cumulative hierarchy, whereas `𝒮ʟ` interprets them on constructible sets. For a fixed stage, `DefOf` supplies formulas over a small presentation of that stage and the sets they define. This makes it possible to construct a subset at the ambient level and then prove that it belongs to `L`.
<!--zh-->
语义比较涉及两个结构。`𝒮ᵥ` 在周遭累积层级中解释公式，`𝒮ʟ` 则在可构造集上解释公式。对固定层，`DefOf` 给出该层的小表示上的公式以及它们所定义的集合。由此可以先在周遭层级构造子集，再证明它属于 `L`。
<!--ja-->
意味の比較には二つの構造を用います。`𝒮ᵥ` は周囲の累積階層で論理式を解釈し、`𝒮ʟ` は構成可能集合上で解釈します。固定した段階に対して、`DefOf` はその段階の小さな表示上の論理式と、それらが定義する集合を与えます。これにより、周囲の階層で部分集合を構成し、それが `L` に属することを証明できます。
<!--/-->

```agda
import FOL.Absoluteness
import FOL.ZFModel
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Definability {ℓ} using ( module DefOf )
open import L.Constructible {ℓ}
```

<!--en-->
The hierarchy lemmas provide the two bounds needed later. `stage`, together with `stage-ord` and `stage-mem`, chooses the least ordinal stage containing a given constructible set. `bound2` merges two ordinal stages, while `boundingOrd` bounds a small family of stages. Membership can then be raised by `Lset-mono`; definability and `Lset→isL` or `𝒟ₒ→isL` turn the resulting stage membership into constructibility. Finally, `uniqueL` upgrades an explicit set with its extensional specification to the required contractible type of realizers.
<!--zh-->
这些层级引理提供后文所需的两类上界。`stage` 连同 `stage-ord`、`stage-mem` 选出包含给定可构造集的最小序数层。`bound2` 合并两个序数层，`boundingOrd` 则界住一个小的层族。随后可用 `Lset-mono` 抬升成员关系，并由可定义性配合 `Lset→isL` 或 `𝒟ₒ→isL` 得到可构造性。最后，`uniqueL` 把一个带外延规格的显式集合提升为所要求的可缩实现者类型。
<!--ja-->
これらの階層に関する補題は、後で必要になる二種類の上界を与えます。`stage` は `stage-ord`、`stage-mem` とともに、与えられた構成可能集合を含む最小の順序数段階を選びます。`bound2` は二つの順序数段階をまとめ、`boundingOrd` は小さな段階の族を一つの段階で抑えます。その後 `Lset-mono` で所属を上へ移し、定義可能性と `Lset→isL` または `𝒟ₒ→isL` から構成可能性を得ます。最後に `uniqueL` は、外延的仕様を備えた明示的な集合を、要求される可縮な実現者の型へ引き上げます。
<!--/-->

```agda
  using ( 𝒮ʟ; isL; isL-trans; IsOrd; Lset; Lset-layer; layer-trans; Lset-mono
        ; 𝒟ₒ; 𝒟ₒ-intro; Lset→isL )
open import L.Ordinal {ℓ} using ( ∅-ord; boundingOrd; bound2 )
open import L.Stage {ℓ} lem using ( stage; stage-ord; stage-mem )
open import L.Axioms.Basic {ℓ} using ( LsetS; 𝒟ₒ→isL; uniqueL )
```

<!--en-->
Paths between truth values express the membership specifications of the constructed sets. `⇔toPath` builds such a path from the two logical directions. When two constructible model elements have equal underlying sets, `Σ≡Prop` supplies their equality because the constructibility component is proposition-valued. Propositional truncation, introduced by `∣_∣₁`, records existence without selecting a global witness.
<!--zh-->
所构造集合的成员规格以真值之间的路径表达。`⇔toPath` 从两个逻辑方向构造这种路径。当两个可构造模型元素的底层集合相等时，由于可构造性分量是命题，`Σ≡Prop` 给出这两个模型元素的相等。由 `∣_∣₁` 引入的命题截断记录存在，而不在全局选定见证。
<!--ja-->
構成する集合の所属の仕様は、真理値間のパスとして表します。`⇔toPath` は二つの論理的な向きからそのパスを作ります。二つの構成可能なモデル要素の基礎にある集合が等しいとき、構成可能性の成分は命題値なので、`Σ≡Prop` がモデル要素どうしの等しさを与えます。`∣_∣₁` で導入する命題的切り詰めは、大域的な証人を選ばずに存在を記録します。
<!--/-->

```agda

open import Cubical.Functions.Logic using ( ⇔toPath )
open import Cubical.Data.Sigma using ( Σ≡Prop )
open import Cubical.Data.Unit using ( tt* )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁ )
```

<!--en-->
A set in the cumulative hierarchy has a small presentation: `⟪ A ⟫` is its index type and `⟪ A ⟫↪` maps an index to the represented member. Membership can be converted to a fiber consisting of such an index and a path back to the original member by `∈-asFiber`. This index is used locally to relabel constants and to range over all members of a source set.
<!--zh-->
累积层级中的集合具有小表示：`⟪ A ⟫` 是其索引类型，`⟪ A ⟫↪` 把索引映到它所表示的成员。`∈-asFiber` 可把成员关系转换为由这种索引及其回到原成员的路径组成的纤维。这个索引在局部用于常元改名，也用于遍历源集合的全部成员。
<!--ja-->
累積階層の集合には小さな表示があります。`⟪ A ⟫` はその添字型で、`⟪ A ⟫↪` は添字を、それが表す要素へ写します。`∈-asFiber` により、所属を、そのような添字と元の要素へ戻るパスからなるファイバーへ変換できます。この添字は、定数の改名と始集合の全要素にわたる局所的な議論に用いられます。
<!--/-->

```agda
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Constructions using ( ∅ )
open import Cubical.HITs.CumulativeHierarchy.Properties
  using ( ∈∈ₛ; ∈-asFiber; ⟪_⟫; ⟪_⟫↪; ∈ₛ⟪_⟫↪_ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
```

<!--en-->
For the hProp interpretation, `Ω` consists of proposition-valued truth values and `∈ˢ` is membership in the constructible structure. A class `Q : S → Ω` is realized by a constructible set `b` when the path `(x ∈ˢ b) ≡ Q x` is given for every `x`. `SetOf Q` packages `b` with precisely this pointwise extensional specification, which is the conclusion form used by separation and replacement.
<!--zh-->
在 hProp 解释中，`Ω` 由命题值真值组成，`∈ˢ` 是可构造结构中的属于关系。若对每个 `x` 都给出路径 `(x ∈ˢ b) ≡ Q x`，则可构造集 `b` 实现类 `Q : S → Ω`。`SetOf Q` 正是把 `b` 与这一逐点外延规格打包；分离与替换的结论采用这种形式。
<!--ja-->
hProp の解釈では、`Ω` は命題値の真理値からなり、`∈ˢ` は構成可能構造での所属です。すべての `x` についてパス `(x ∈ˢ b) ≡ Q x` が与えられるとき、構成可能集合 `b` はクラス `Q : S → Ω` を実現します。`SetOf Q` は `b` とこの各点での外延的仕様を組にした型であり、分出公理と置換公理の結論はこの形を取ります。
<!--/-->

```agda
open hPropStructure 𝒮ʟ

module ModelL = FOL.ZFModel 𝒮ʟ
open ModelL using ( SetOf )

module SemV = FOL.Semantics (hPropAlgebra (ℓ-suc ℓ)) 𝒮ᵥ
open SemV.At (V ℓ) id using () renaming ( _⊨_ to _⊨v_ )
```

<!--en-->
The constructible sets form a transitive substructure of the ambient hierarchy: if a set is constructible, then each of its members is constructible by `isL-trans`. This is exactly what bounded quantifiers need. An ambient witness lying in the interpretation of a constructible bounding term can be repackaged as an element of the substructure, while an inner witness can be projected outward. Induction on a Δ₀ formula therefore yields `abs₀`, a path between its ambient truth `_⊨v_` and its truth `_⊨_` in the constructible substructure.
<!--zh-->
可构造集构成周遭层级的传递子结构：若一个集合可构造，则由 `isL-trans`，它的每个成员也可构造。这正是有界量词所需的性质。落在可构造界定词项之解释中的周遭见证可以重新打包为子结构的元素，而内层见证可以投影到周遭层级。于是，对 Δ₀ 公式作归纳得到 `abs₀`，即其周遭真值 `_⊨v_` 与可构造子结构中的真值 `_⊨_` 之间的路径。
<!--ja-->
構成可能集合は周囲の階層の推移的部分構造をなします。集合が構成可能なら、その各要素も `isL-trans` によって構成可能です。これは有界量化子に必要な性質そのものです。構成可能な範囲項の解釈に属する周囲の証人は部分構造の要素として組み直せ、内側の証人は周囲の階層へ射影できます。したがって Δ₀ 論理式についての帰納から `abs₀` が得られ、その周囲での真理値 `_⊨v_` と構成可能部分構造での真理値 `_⊨_` の間にパスが与えられます。
<!--/-->

```agda
module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL using ( abs₀ ) renaming ( _⊨ᵐ_ to _⊨_ )
```

<!--en-->
## The replacement image

Fix a source set `a` and a binary formula `φ`. For a possible value `z`, the class `ReplImage a φ` states that some member `x` of `a` is related to `z` by `φ`. The environment `x ∷ z ∷ []` fixes the convention used here: the source occupies slot zero and the image occupies slot one.
<!--zh-->
## 替换的像

固定源集合 `a` 与二元公式 `φ`。对可能的取值 `z`，类 `ReplImage a φ` 表示 `a` 的某个成员 `x` 通过 `φ` 与 `z` 相关。赋值 `x ∷ z ∷ []` 固定此处的约定：源占零号槽，像占一号槽。
<!--ja-->
## 置換による像

始集合 `a` と二変数論理式 `φ` を固定します。値の候補 `z` に対し、クラス `ReplImage a φ` は、`a` のある要素 `x` が `φ` によって `z` と関係づけられることを述べます。割り当て `x ∷ z ∷ []` により、始域がスロット零、像がスロット一を占めるという規約が定まります。
<!--/-->

<!--en-->
The indexed disjunction `⋁ S` gives a propositionally truncated existential over `x : S`. Its body requires both `x ∈ˢ a` and satisfaction of `φ` at `x ∷ z ∷ []`. Hence a proof of `ReplImage a φ z` records that a suitable source exists while leaving the witness inside propositional truncation; later arguments may map or eliminate it only into proposition-valued targets.
<!--zh-->
索引析取 `⋁ S` 给出对 `x : S` 的命题截断存在。其主体同时要求 `x ∈ˢ a`，并要求 `φ` 在赋值 `x ∷ z ∷ []` 下成立。因此，`ReplImage a φ z` 的证明记录合适的源确实存在，同时把见证留在命题截断中；后续论证只能把它映射到截断内，或向命题值目标消去。
<!--ja-->
添字付き選言 `⋁ S` は、`x : S` にわたる命題的に切り詰められた存在を与えます。その本体は `x ∈ˢ a` と、割り当て `x ∷ z ∷ []` における `φ` の充足をともに要求します。したがって `ReplImage a φ z` の証明は、適切な始域の要素が存在することを記録しつつ、証人を命題的切り詰めの中に保ちます。後の議論は、それを切り詰めの内部で写すか、命題値の目標へ消去できます。
<!--/-->

```agda
ReplImage : (a : S) (φ : Formula S 2) → S → Ω
ReplImage a φ z = ⋁ S (λ x → (x ∈ˢ a) ⊓ ((x ∷ z ∷ []) ⊨ φ))
```

<!--en-->
## Bounding a functional image
<!--zh-->
## 界住函数像
<!--ja-->
## 関数的な像を抑える
<!--/-->

<!--en-->
`FunctionalImage`{.Agda} chooses the unique value at each source member and uses
smallness plus an ordinal bound to place every related image in one stage.
<!--zh-->
`FunctionalImage`{.Agda} 为源集合的每个成员选取唯一值，并用小性与序数上界把每个相关像放进单一层。
<!--ja-->
`FunctionalImage`{.Agda} は始集合の各要素で一意な値を選び、小ささと順序数の上界を用いて、関係するすべての像を一つの段階へ入れる。
<!--/-->

<!--en-->
A functional relation on the members of a set has all its values in one stage.
Choose the unique value at each member, use the small member type to bound the
stages of those choices, and use uniqueness to put every related value under the
same bound. The relation is a parameter, so the result is independent of the
variable order used by a particular formula.
<!--zh-->
一个集合的诸成员之上的函数关系，其值全落在同一层。先在每个成员处取唯一值，再用小成员类型界住这些取值的诸层，最后以唯一性把每个相关值置于同一界下。关系作为参数传入，故结果不依赖某条特定公式所用的变量次序。
<!--/-->

```agda
module FunctionalImage (a : S) (R : S → S → Ω)
                       (fc : (x : S) → ⟨ x ∈ˢ a ⟩
                           → isContr (Σ[ y ∈ S ] ⟨ R x y ⟩)) where

  Mem : Type (ℓ-suc ℓ)
  Mem = Σ[ x ∈ S ] ⟨ x ∈ˢ a ⟩

  img : Mem → S
  img p = fc (p .fst) (p .snd) .fst .fst

  img-sat : (p : Mem) → ⟨ R (p .fst) (img p) ⟩
  img-sat p = fc (p .fst) (p .snd) .fst .snd

  img-uniq : (p : Mem) (y : S) → ⟨ R (p .fst) y ⟩ → img p ≡ y
  img-uniq p y h = cong fst (fc (p .fst) (p .snd) .snd (y , h))

  private
    memS : ⟪ fst a ⟫ → Mem
    memS m = (⟪ fst a ⟫↪ m
             , isL-trans fm∈fa (a .snd)) , fm∈fa
      where
      fm∈fa : ⟨ ⟪ fst a ⟫↪ m ∈ fst a ⟩
      fm∈fa = ∈∈ₛ {a = ⟪ fst a ⟫↪ m} {b = fst a} .snd (∈ₛ⟪ fst a ⟫↪ m)

    bImg = boundingOrd ⟪ fst a ⟫
      (λ m → stage (fst (img (memS m))) (img (memS m) .snd))
      (λ m → stage-ord (fst (img (memS m))) (img (memS m) .snd))

  βimg : V ℓ
  βimg = bImg .fst

  βimg-ord : IsOrd βimg
  βimg-ord = bImg .snd .fst

  range∈βimg : (x : S) → ⟨ x ∈ˢ a ⟩ → (y : S) → ⟨ R x y ⟩
              → ⟨ fst y ∈ Lset βimg ⟩
  range∈βimg x x∈a y h = subst (λ w → ⟨ fst w ∈ Lset βimg ⟩) image≡y
    (Lset-mono {α = βimg} {β = stage (fst (img (memS m))) (img (memS m) .snd)}
      (bImg .snd .snd m) (stage-mem (fst (img (memS m))) (img (memS m) .snd)))
    where
    m = ∈-asFiber {a = fst x} {b = fst a} x∈a .fst
    q : memS m .fst ≡ x
    q = Σ≡Prop (λ z → snd (isL z))
      (∈-asFiber {a = fst x} {b = fst a} x∈a .snd)
    image≡y : img (memS m) ≡ y
    image≡y = img-uniq (memS m) y (subst (λ z → ⟨ R z y ⟩) (sym q) h)
```

<!--en-->
## At a fixed stage
<!--zh-->
## 在固定的层上
<!--ja-->
## 固定した段階での構成
<!--/-->

<!--en-->
Inside one ordinal stage, `Below`{.Agda} supplies indices for its constructible
members, and the satisfaction bridge relates formulas over the model carrier to
their relabelled formulas over that stage.
<!--zh-->
在一个固定的序数层内，`Below`{.Agda} 为其中的可构造成员提供索引；满足关系之桥则把模型载体上的公式与该层上经常元改名的公式联系起来。
<!--ja-->
一つの順序数段階の内部で、`Below`{.Agda} がその構成可能な要素の添字を与え、充足関係の橋がモデルの台上の論理式を、その段階上で定数の改名を施した論理式と結ぶ。
<!--/-->

<!--en-->
Everything below is relative to one stage. The predicate `Below` says a member of
the model lies in that stage; the relabelling instance sends such a member to its
index there, and the equation it needs is that the index names the member back,
which is what a fiber of the membership gives.
<!--zh-->
下文一切都相对于一层。谓词 `Below` 表示模型的一个成员落在该层之中；重标实例把这样的成员送到它在其中的索引，而所需的那条等式是「索引把该成员命名回来」，这正由隶属关系的纤维给出。
<!--/-->

```agda
module AtStage (σ : V ℓ) (oσ : IsOrd σ) where
  module DefC = DefOf (Lset σ)

  Atrans : Transitive 𝒮ᵥ DefC.M
  Atrans = layer-trans (Lset-layer σ)

  module RefC = DefC.Refine Atrans
  open RefC.Abs using () renaming ( _⊨ᵛ_ to _⊨σ_ )

  Below : S → Type (ℓ-suc ℓ)
  Below c = ⟨ fst c ∈ Lset σ ⟩

  module RL = Relabel {K = S} {K' = ⟪ Lset σ ⟫} {W = V ℓ}
                fst ⟪ Lset σ ⟫↪ Below
                (λ c p → ∈-asFiber {a = fst c} {b = Lset σ} p .fst)
                (λ c p → ∈-asFiber {a = fst c} {b = Lset σ} p .snd)
```

<!--en-->
The five-step path. Read it from the top: membership in the definable subset is
outer satisfaction of the relabelled formula read through the stage's inclusion;
two applications of the relabelling law move that to the hierarchy's own reading;
the correctness of the partial relabelling identifies the two readings; and
absoluteness brings it back inside the model. Each link is an equation from an
earlier chapter, and the composite is the only place this chapter does anything
delicate.
<!--zh-->
那条五步路径自上而下读来如下：属于可定义子集，就是经该层的含入读出的、重标后公式的外层满足；两次重标律把它转换为层级自身的读法；部分重标的正确性把两种读法等同起来；而绝对性把它带回模型内部。每一环都是前面某章已证的等式，这个复合则是本章唯一需要细致工作的地方。
<!--/-->

```agda
  satBridge : (φ : Formula S 1) (h : BoundedFo Below φ) (dφ : Δ₀ φ)
              (m : ⟪ Lset σ ⟫) (xL : ⟨ isL (⟪ Lset σ ⟫↪ m) ⟩)
            → ((⟪ Lset σ ⟫↪ m ∷ []) ⊨σ (mapFo DefC.ι (RL.liftFo φ h)))
              ≡ (((⟪ Lset σ ⟫↪ m , xL) ∷ []) ⊨ φ)
  satBridge φ h dφ m xL =
      ⊨-map (hPropAlgebra (ℓ-suc ℓ)) 𝒮ᵥ DefC.ι fst (RL.liftFo φ h)
        (⟪ Lset σ ⟫↪ m ∷ [])
    ∙ sym (⊨-map (hPropAlgebra (ℓ-suc ℓ)) 𝒮ᵥ ⟪ Lset σ ⟫↪ id (RL.liftFo φ h)
             (⟪ Lset σ ⟫↪ m ∷ []))
    ∙ cong (λ ψ → (⟪ Lset σ ⟫↪ m ∷ []) ⊨v ψ) (RL.liftFo-correct φ h)
    ∙ ⊨-map (hPropAlgebra (ℓ-suc ℓ)) 𝒮ᵥ fst id φ (⟪ Lset σ ⟫↪ m ∷ [])
    ∙ sym (abs₀ dφ ((⟪ Lset σ ⟫↪ m , xL) ∷ []))

  carveSat : (φ : Formula S 1) (h : BoundedFo Below φ) (dφ : Δ₀ φ)
             (m : ⟪ Lset σ ⟫) (xL : ⟨ isL (⟪ Lset σ ⟫↪ m) ⟩)
           → (⟪ Lset σ ⟫↪ m ∈ DefC.defSet (RL.liftFo φ h))
             ≡ (((⟪ Lset σ ⟫↪ m , xL) ∷ []) ⊨ φ)
  carveSat φ h dφ m xL =
    RefC.abs-defSet (RL.liftFo φ h) (RL.Δ₀-liftFo h dφ) m ∙ satBridge φ h dφ m xL

```

<!--en-->
The carved set is sealed, and the facts about it are proved through the
seal. Unsealed, `defSet` unfolds to a set over formulas, and every later type
mentioning the carved set would carry that unfolding into conversion; sealing it
and exporting exactly what is needed keeps the rest of the chapter working with a
black box.
<!--zh-->
刻出的集合被封装起来，而关于它的事实经这一封装证明。若不封装，`defSet` 会展开为公式之上的一个集合，此后每个提到该集合的类型都会把这次展开带进转换检查；封装起来并只导出所需内容，本章其余部分便可把它当作黑箱使用。
<!--/-->

```agda
  opaque
    carve : Formula ⟪ Lset σ ⟫ 1 → V ℓ
    carve ψ = DefC.defSet ψ

  opaque
    unfolding carve
    carve∈𝒟ₒ : (ψ : Formula ⟪ Lset σ ⟫ 1) → ⟨ carve ψ ∈ 𝒟ₒ (Lset σ) ⟩
    carve∈𝒟ₒ ψ = 𝒟ₒ-intro (Lset σ) (DefC.defSet ψ) ∣ ψ , refl ∣₁

    carve⊆ : (ψ : Formula ⟪ Lset σ ⟫ 1) (y : V ℓ) → ⟨ y ∈ carve ψ ⟩
           → ⟨ y ∈ Lset σ ⟩
    carve⊆ ψ y mem = DefC.defSet⊆A ψ y mem

    imageOut : (φ : Formula S 1) (h : BoundedFo Below φ) (dφ : Δ₀ φ)
               (m : ⟪ Lset σ ⟫) (xL : ⟨ isL (⟪ Lset σ ⟫↪ m) ⟩)
             → ⟨ ⟪ Lset σ ⟫↪ m ∈ carve (RL.liftFo φ h) ⟩
             → ⟨ ((⟪ Lset σ ⟫↪ m , xL) ∷ []) ⊨ φ ⟩
    imageOut φ h dφ m xL mem = subst ⟨_⟩ (carveSat φ h dφ m xL) mem

    imageIn : (φ : Formula S 1) (h : BoundedFo Below φ) (dφ : Δ₀ φ)
              (m : ⟪ Lset σ ⟫) (xL : ⟨ isL (⟪ Lset σ ⟫↪ m) ⟩)
            → ⟨ ((⟪ Lset σ ⟫↪ m , xL) ∷ []) ⊨ φ ⟩
            → ⟨ ⟪ Lset σ ⟫↪ m ∈ carve (RL.liftFo φ h) ⟩
    imageIn φ h dφ m xL sat = subst ⟨_⟩ (sym (carveSat φ h dφ m xL)) sat
```

<!--en-->
One more small tool. Satisfaction depends only on the underlying set, not on the
proof of constructibility carried alongside it, so a satisfaction fact transports
along an equation between underlying sets. Constructibility is propositional, so the
underlying equation gives an equation of model elements directly. The Δ₀
parameters remain in the interfaces used by the callers.
<!--zh-->
还有一个辅助结果。满足关系只依赖底层集合，而不依赖随之携带的可构造性证明，因此满足的事实可沿底层集合之间的等式转移。可构造性是命题，故底层集合的等式直接给出模型元素的等式。Δ₀ 参数保留在供调用方使用的接口中。
<!--/-->

```agda
  opaque
    ⊨-transport : (φ : Formula S 1) (dφ : Δ₀ φ) (u v : S) → fst u ≡ fst v
                → ⟨ (u ∷ []) ⊨ φ ⟩ → ⟨ (v ∷ []) ⊨ φ ⟩
    ⊨-transport φ dφ u v p =
      subst (λ z → ⟨ (z ∷ []) ⊨ φ ⟩) (Σ≡Prop (λ x → snd (isL x)) p)

```

<!--en-->
## Separation at a stage
<!--zh-->
## 在一层上分离
<!--ja-->
## 一つの段階で分出する
<!--/-->

<!--en-->
`carveAt`{.Agda} turns a bounded unary Δ₀ formula whose witnesses stay in the
stage into a constructible set, and `separateAt`{.Agda} specializes it to a
subset of a given set.
<!--zh-->
`carveAt`{.Agda} 把见证落在层内的有界一元 Δ₀ 公式化为可构造集合；`separateAt`{.Agda} 则把它专门用于给定集合的子集。
<!--ja-->
`carveAt`{.Agda} は証人が段階内に留まる有界な一変数 Δ₀ 論理式を構成可能集合へ変え、`separateAt`{.Agda} はそれを与えられた集合の部分集合へ特殊化する。
<!--/-->

<!--en-->
The shared construction carves a bounded unary formula whose satisfying sets
lie in the stage. The carved set is definable, hence constructible; the bridge
and transport identify its members with the formula's satisfaction predicate.
Separation instantiates this construction with the conjunction of membership
in `a` and `φ`. Transitivity supplies the stage cover from the membership conjunct.
<!--zh-->
共享的构造处理一条有界一元公式，其满足者均落在该层中。刻出的集合可定义，故可构造；语义桥与转移把它的成员关系等同于公式的满足谓词。分离则把该构造实例化为「属于 `a`」与 `φ` 的合取；传递性由成员关系这一合取项提供层覆盖。
<!--/-->

```agda
  private
    memberIsL : (m : ⟪ Lset σ ⟫) → ⟨ isL (⟪ Lset σ ⟫↪ m) ⟩
    memberIsL m = Lset→isL σ oσ (⟪ Lset σ ⟫↪ m)
      (∈∈ₛ {a = ⟪ Lset σ ⟫↪ m} {b = Lset σ} .snd (∈ₛ⟪ Lset σ ⟫↪ m))

  carveAt : (χ : Formula S 1) (hχ : BoundedFo Below χ) (dχ : Δ₀ χ)
            (cover : (z : S) → ⟨ (z ∷ []) ⊨ χ ⟩ → ⟨ fst z ∈ Lset σ ⟩)
          → isContr (SetOf (λ z → (z ∷ []) ⊨ χ))
  carveAt χ hχ dχ cover = uniqueL (λ z → (z ∷ []) ⊨ χ) (replElt , spec)
    where
    replElt : S
    replElt = carve (RL.liftFo χ hχ)
            , 𝒟ₒ→isL σ oσ (carve (RL.liftFo χ hχ)) (carve∈𝒟ₒ (RL.liftFo χ hχ))

    spec : (z : S) → (z ∈ˢ replElt) ≡ ((z ∷ []) ⊨ χ)
    spec z = ⇔toPath fwd bwd
      where
      fwd : ⟨ z ∈ˢ replElt ⟩ → ⟨ ((z ∷ []) ⊨ χ) ⟩
      fwd z∈ = ⊨-transport χ dχ (⟪ Lset σ ⟫↪ m , xL) z q (imageOut χ hχ dχ m xL m∈)
        where
        fz∈Lσ = carve⊆ (RL.liftFo χ hχ) (fst z) z∈
        m = ∈-asFiber {a = fst z} {b = Lset σ} fz∈Lσ .fst
        q : ⟪ Lset σ ⟫↪ m ≡ fst z
        q = ∈-asFiber {a = fst z} {b = Lset σ} fz∈Lσ .snd
        xL = memberIsL m
        m∈ : ⟨ ⟪ Lset σ ⟫↪ m ∈ carve (RL.liftFo χ hχ) ⟩
        m∈ = subst (λ w → ⟨ w ∈ carve (RL.liftFo χ hχ) ⟩) (sym q) z∈

      bwd : ⟨ ((z ∷ []) ⊨ χ) ⟩ → ⟨ z ∈ˢ replElt ⟩
      bwd qz = subst (λ w → ⟨ w ∈ carve (RL.liftFo χ hχ) ⟩) q m∈
        where
        fz∈Lσ = cover z qz
        m = ∈-asFiber {a = fst z} {b = Lset σ} fz∈Lσ .fst
        q : ⟪ Lset σ ⟫↪ m ≡ fst z
        q = ∈-asFiber {a = fst z} {b = Lset σ} fz∈Lσ .snd
        xL = memberIsL m
        satz : ⟨ ((⟪ Lset σ ⟫↪ m , xL) ∷ []) ⊨ χ ⟩
        satz = ⊨-transport χ dχ z (⟪ Lset σ ⟫↪ m , xL) (sym q) qz
        m∈ : ⟨ ⟪ Lset σ ⟫↪ m ∈ carve (RL.liftFo χ hχ) ⟩
        m∈ = imageIn χ hχ dχ m xL satz

  separateAt : (a : S) (fa∈σ : ⟨ fst a ∈ Lset σ ⟩)
               (φ : Formula S 1) (h : BoundedFo Below φ) (dφ : Δ₀ φ)
             → isContr (SetOf (λ x → (x ∈ˢ a) ⊓ ((x ∷ []) ⊨ φ)))
  separateAt a fa∈σ φ h dφ =
    carveAt ((var zero ∈̇ con a) ∧̇ φ) ((tt* , fa∈σ) , h) (δ-∧ δ-∈ dφ)
      (λ z q → layer-trans (Lset-layer σ) {x = fst a} {y = fst z} (q .fst) fa∈σ)
```

<!--en-->
## Finding the stage
<!--zh-->
## 找到那一层
<!--ja-->
## 論理式を収める段階を求める
<!--/-->

<!--en-->
Structural recursion over terms and formulas computes an ordinal stage containing
every constant, merging branch bounds and transporting their boundedness proofs.
<!--zh-->
对词项与公式作结构递归，可计算出包含全部常元的序数层，并在分支处合并上界、传输其有界性证明。
<!--ja-->
項と論理式の構造的再帰により全定数を含む順序数段階を計算し、分岐では上界を併合して有界性の証明を輸送する。
<!--/-->

<!--en-->
The construction requires a stage holding every constant of the formula. It obtains one by
recursion on the formula, producing the stage and certificate together. A
constant contributes its own earliest stage, a variable contributes nothing, and
at each branching node the two stages are combined by taking a bound, with
monotonicity raising both certificates to that bound.

The bound of two ordinals is supplied by `bound2`{.Agda} from the ordinal chapter. This is
the only result the recursion needs from ordinal theory.
<!--zh-->
引擎要的是一个装下公式全部常元的层。造一个出来，就是沿公式的一次递归，同时产出层与证书。常元贡献它自己的最早层，变元什么也不贡献，而在每个分叉节点上，两层经界住而合并，单调性把两份证书都抬到合并处。

合并两个序数正是序数那一章的 `bound2`{.Agda}；这次递归对序数理论的全部需求，也到此为止。
<!--/-->

```agda
Below′ : V ℓ → S → Type (ℓ-suc ℓ)
Below′ σ c = ⟨ fst c ∈ Lset σ ⟩


liftTmTo : {σ β : V ℓ} → ⟨ σ ∈ β ⟩ → ∀ {n} (t : Term S n)
         → BoundedTm (Below′ σ) t → BoundedTm (Below′ β) t
liftTmTo {σ} {β} σ∈β t h =
  BoundedTm-mono {P = Below′ σ} {Q = Below′ β}
    (λ (c : S) h' → Lset-mono {α = β} {β = σ} σ∈β {x = fst c} h') t h

liftFoTo : {σ β : V ℓ} → ⟨ σ ∈ β ⟩ → ∀ {n} (φ : Formula S n)
         → BoundedFo (Below′ σ) φ → BoundedFo (Below′ β) φ
liftFoTo {σ} {β} σ∈β φ h =
  BoundedFo-mono {P = Below′ σ} {Q = Below′ β}
    (λ (c : S) h' → Lset-mono {α = β} {β = σ} σ∈β {x = fst c} h') φ h

mkBoundedTm : ∀ {n} (t : Term S n) → Σ[ σ ∈ V ℓ ] (IsOrd σ × BoundedTm (Below′ σ) t)
mkBoundedTm (con c) = stage (fst c) (c .snd)
                    , (stage-ord (fst c) (c .snd) , stage-mem (fst c) (c .snd))
mkBoundedTm (var i) = ∅ , (∅-ord , _)

private
  mkBounded : ∀ {ℓc ℓd} {C : V ℓ → Type ℓc} {D : V ℓ → Type ℓd}
            → (liftC : {σ β : V ℓ} → ⟨ σ ∈ β ⟩ → C σ → C β)
            → (liftD : {σ β : V ℓ} → ⟨ σ ∈ β ⟩ → D σ → D β)
            → (r₁ : Σ[ σ ∈ V ℓ ] (IsOrd σ × C σ))
            → (r₂ : Σ[ σ ∈ V ℓ ] (IsOrd σ × D σ))
            → Σ[ σ ∈ V ℓ ] (IsOrd σ × (C σ × D σ))
  mkBounded liftC liftD r₁ r₂ = b .fst , (b .snd .fst ,
      ( liftC (b .snd .snd .fst) (r₁ .snd .snd)
      , liftD (b .snd .snd .snd) (r₂ .snd .snd) ))
    where
    b  = bound2 (r₁ .fst) (r₂ .fst) (r₁ .snd .fst) (r₂ .snd .fst)

mkBoundedFo : ∀ {n} (φ : Formula S n) → Σ[ σ ∈ V ℓ ] (IsOrd σ × BoundedFo (Below′ σ) φ)
mkBoundedFo (t ∈̇ u) = mkBounded (λ σ∈β → liftTmTo σ∈β t) (λ σ∈β → liftTmTo σ∈β u) (mkBoundedTm t) (mkBoundedTm u)
mkBoundedFo (t ≐ u) = mkBounded (λ σ∈β → liftTmTo σ∈β t) (λ σ∈β → liftTmTo σ∈β u) (mkBoundedTm t) (mkBoundedTm u)
mkBoundedFo (φ ∧̇ ψ) = mkBounded (λ σ∈β → liftFoTo σ∈β φ) (λ σ∈β → liftFoTo σ∈β ψ) (mkBoundedFo φ) (mkBoundedFo ψ)
mkBoundedFo (φ ∨̇ ψ) = mkBounded (λ σ∈β → liftFoTo σ∈β φ) (λ σ∈β → liftFoTo σ∈β ψ) (mkBoundedFo φ) (mkBoundedFo ψ)
mkBoundedFo (φ ⇒̇ ψ) = mkBounded (λ σ∈β → liftFoTo σ∈β φ) (λ σ∈β → liftFoTo σ∈β ψ) (mkBoundedFo φ) (mkBoundedFo ψ)
mkBoundedFo ⊥̇        = ∅ , (∅-ord , _)
mkBoundedFo (∃̇ φ)    = mkBoundedFo φ
mkBoundedFo (∀̇ φ)    = mkBoundedFo φ
mkBoundedFo (∀̇∈ t φ) = mkBounded (λ σ∈β → liftTmTo σ∈β t) (λ σ∈β → liftFoTo σ∈β φ) (mkBoundedTm t) (mkBoundedFo φ)
mkBoundedFo (∃̇∈ t φ) = mkBounded (λ σ∈β → liftTmTo σ∈β t) (λ σ∈β → liftFoTo σ∈β φ) (mkBoundedTm t) (mkBoundedFo φ)
```

<!--en-->
## Δ₀ separation
<!--zh-->
## Δ₀ 分离
<!--ja-->
## Δ₀ 分出公理
<!--/-->

<!--en-->
`separateΔ₀`{.Agda} merges the bounds for the formula's constants and the source
set, then invokes `separateAt`{.Agda} to realize the bounded separation instance.
<!--zh-->
`separateΔ₀`{.Agda} 先把公式常元与源集合的上界合并，再调用 `separateAt`{.Agda} 得到有界分离的实例。
<!--ja-->
`separateΔ₀`{.Agda} は論理式の定数と始集合の上界を併合し、`separateAt`{.Agda} を呼び出して有界な分出公理の事例を実現する。
<!--/-->

<!--en-->
Merge the formula's stage with the argument's own earliest stage,
raise the certificate to the resulting bound, and use these data in the bounded
separation construction. This proves separation for the bounded fragment
unconditionally: it requires neither reflection nor a frontier field, and
uses the results established in the preceding chapters in order.
<!--zh-->
步骤如下：把公式的层与实参自身的最早层合并，把证书抬升到合并后的层，再把结果交给引擎。这正是有界片段的分离公理，无条件成立：既不需要反射，也不需要前沿字段，只是依序使用前几章已经建立的工具。
<!--/-->

```agda
separateΔ₀ : (a : S) (φ : Formula S 1) → Δ₀ φ
           → isContr (SetOf (λ x → (x ∈ˢ a) ⊓ ((x ∷ []) ⊨ φ)))
separateΔ₀ a φ dφ = AtStage.separateAt σ oσ a fa∈σ φ h dφ
  where
  rφ = mkBoundedFo φ
  sa = stage (fst a) (a .snd)
  bb = bound2 (rφ .fst) sa (rφ .snd .fst) (stage-ord (fst a) (a .snd))
  σ  = bb .fst
  oσ = bb .snd .fst
  h  = liftFoTo {σ = rφ .fst} {β = σ} (bb .snd .snd .fst) φ (rφ .snd .snd)
  fa∈σ : ⟨ fst a ∈ Lset σ ⟩
  fa∈σ = Lset-mono {α = σ} {β = sa} (bb .snd .snd .snd) (stage-mem (fst a) (a .snd))
```

<!--en-->
## Δ₀ replacement
<!--zh-->
## Δ₀ 替换
<!--ja-->
## Δ₀ 置換公理
<!--/-->

<!--en-->
`replaceΔ₀`{.Agda} first bounds the functional image and then separates that
stage by the bounded existential defining `ReplImage`{.Agda}.
<!--zh-->
`replaceΔ₀`{.Agda} 先界住函数像，再用定义 `ReplImage`{.Agda} 的有界存在式在该层上分离。
<!--ja-->
`replaceΔ₀`{.Agda} はまず関数的な像を抑え、次に `ReplImage`{.Agda} を定義する有界存在量化でその段階を分出する。
<!--/-->

<!--en-->
Replacement needs one thing more: a stage containing the image. Functionality
gives the common image bound above. Separate that stage by the bounded
existential saying that some member of the argument is related to the candidate;
the resulting predicate is exactly the replacement image.

Worth noting what this does *not* need. The defining formula's only quantifier is
bounded by the argument, so it stays Δ₀ and absoluteness applies to the whole of
it. The work is done by functionality, not by any reflection across structures,
which is the clean line between this lemma and the unbounded case.
<!--zh-->
替换还多需要一个条件：一个装得下像的层。函数性恰好给出上述公共像界。用一条有界存在公式「实参的某个成员与候选者相关」在该层上作分离，所得谓词正是替换的像。

值得注意的是它**不**需要什么：定义公式唯一的量词被实参所界，故它保持 Δ₀，绝对性适用于整条公式。真正起作用的是函数性，而非任何跨结构的反射；这正是本引理与无界情形之间的清晰分界。
<!--/-->

```agda
replaceΔ₀ : (a : S) (φ : Formula S 2) → Δ₀ φ
          → ((x : S) → ⟨ x ∈ˢ a ⟩ → isContr (Σ[ y ∈ S ] ⟨ (x ∷ y ∷ []) ⊨ φ ⟩))
          → isContr (SetOf (ReplImage a φ))
replaceΔ₀ a φ dφ fc =
  subst (λ Q → isContr (SetOf Q)) (sym Q≡)
    (separateΔ₀ (LsetS βimg βimg-ord) imageFo (δ-∃∈ dφ))
  where
  module I = FunctionalImage a (λ x y → (x ∷ y ∷ []) ⊨ φ) fc
  open I using ( βimg; βimg-ord; range∈βimg )

  imageFo : Formula S 1
  imageFo = ∃̇∈ (con a) φ

  BoundedImage : S → Ω
  BoundedImage y = (y ∈ˢ LsetS βimg βimg-ord) ⊓ ((y ∷ []) ⊨ imageFo)

  Q≡ : ReplImage a φ ≡ BoundedImage
  Q≡ = funExt (λ y → ⇔toPath (into y) (λ p → p .snd))
    where
    into : (y : S) → ⟨ ReplImage a φ y ⟩ → ⟨ BoundedImage y ⟩
    into y = PT.rec (snd (BoundedImage y)) λ { (x , (x∈a , h)) →
      range∈βimg x x∈a y h , ∣ x , (x∈a , h) ∣₁ }
```

<!--en-->
## Recap
<!--zh-->
## 小结
<!--ja-->
## まとめ
<!--/-->

<!--en-->
The bounded engine now yields `separateΔ₀`{.Agda} and `replaceΔ₀`{.Agda}, with
formula constants and functional images each confined to an explicit stage.
<!--zh-->
有界引擎现在给出 `separateΔ₀`{.Agda} 与 `replaceΔ₀`{.Agda}，并把公式常元与函数像分别限制在一个明确层内。
<!--ja-->
有界な構成から `separateΔ₀`{.Agda} と `replaceΔ₀`{.Agda} が得られ、論理式の定数と関数的な像はそれぞれ明示的な段階に収められる。
<!--/-->

<!--en-->
Given a stage holding a set and all the constants of a Δ₀ formula,
`separateAt`{.Agda} carves the subset in `L`. Its semantic content is
`carveSat`{.Agda}: membership in the carved set is satisfaction in the model,
along a path supplied by definability, relabelling and absoluteness.
`FunctionalImage`{.Agda} supplies the other ingredient for replacement by bounding
the values of any functional relation. Thus `replaceΔ₀`{.Agda} first bounds its
image and then applies `separateΔ₀`{.Agda} to a bounded existential. For arbitrary
formulas, the full axiom chapter adds reflection only where separation needs it.
<!--zh-->
给定一个装下某集合与某 Δ₀ 公式全部常元的层，`separateAt`{.Agda} 在 `L` 中刻出子集。其语义内容是 `carveSat`{.Agda}：属于刻出的集合就是在模型中满足，所沿道路由可定义性、重标与绝对性给出。`FunctionalImage`{.Agda} 提供替换所需的另一件东西：界住任意函数关系的诸值。因此 `replaceΔ₀`{.Agda} 先界住其像，再把 `separateΔ₀`{.Agda} 施于一条有界存在式。对任意公式，完整公理一章只在分离需要之处加入反射。
<!--/-->
