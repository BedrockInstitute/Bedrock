<!--en-->
# An internal family of earliest-disagreement relations

At each finite stage, `before n` compares two sets at their earliest disagreement. This chapter represents that relation by a set `relAt n` inside `L`, assembles these sets into a numeral-indexed family, and expresses lookup in that family by the object-language formula `BeforeAt`. Instantiating `Described` with this formula yields `codeOrder`, which later supplies the comparison of codes used in name comparison. The chapter itself neither compares names nor proves that comparison well-founded.
<!--zh-->
# 最早分歧关系的内部族

在每个有穷层，`before n` 按两个集合的最早分歧来比较它们。本章在 `L` 内用集合 `relAt n` 表示这条关系，再把这些集合组成以数码为索引的族，并用对象语言公式 `BeforeAt` 表达对该族的查找。以此公式实例化 `Described` 后得到 `codeOrder`，它将在后续名字比较中供应码的比较关系。本章本身既不比较名字，也不证明名字比较的良基性。
<!--ja-->
# 最初の相違の関係からなる内部の族

各有限段階で、`before n` は二つの集合を最初に相違する要素によって比較する。本章では、この関係を `L` 内の集合 `relAt n` で表し、それらを数項で添字づけられた族にまとめ、その族での参照を対象言語の論理式 `BeforeAt` で表す。この論理式によって `Described` を具体化すると `codeOrder` が得られ、後の名前比較でコードの比較関係として使われる。本章自身は名前を比較せず、その比較の整礎性も証明しない。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

```

<!--en-->
The construction uses excluded middle only through the explicit hypothesis that will be attached to the module. Thus the classical assumption remains visible in every result exported from this development.
<!--zh-->
本构造只通过稍后附在模块上的显式假设使用排中律。因此，这一经典假设在本章导出的每项结果中都保持可见。
<!--ja-->
この構成で排中律を使うのは、直後にモジュールへ与える明示的な仮定を通してだけである。したがって、この章から公開される各結果には古典的仮定が明示されたままになる。
<!--/-->

```agda
open import Base.Prelude
open import Base.Classical using ( LEM )

```

<!--en-->
Fix a universe level `ℓ` and assume `LEM (ℓ-suc ℓ)`. All sets, formulas, and proposition-valued relations below live at the levels determined by this choice.
<!--zh-->
固定宇宙层级 `ℓ`，并假设 `LEM (ℓ-suc ℓ)`。下文的集合、公式与命题值关系都处在这一选择所确定的层级上。
<!--ja-->
宇宙レベル `ℓ` を固定し、`LEM (ℓ-suc ℓ)` を仮定する。以下の集合、論理式、命題値関係はすべて、この選択で定まるレベルに属する。
<!--/-->

```agda
module L.Choice.EarliestDisagreement {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

```

<!--en-->
We shall describe relations by first-order formulas over the cumulative hierarchy. Ordered pairs serve as relation entries, and their injectivity will later let us recover the two compared sets from a coded entry.
<!--zh-->
我们将在累积层级上用一阶公式描述关系。有序对充当关系条目，稍后再借助其单射性从编码条目恢复两个被比较的集合。
<!--ja-->
累積階層上の一階論理式によって関係を記述する。関係の要素には順序対を用い、後にはその単射性によって、符号化された要素から比較される二集合を復元する。
<!--/-->

```agda
open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using
  ( Formula; var; con; _∈̇_; _≐_; _∧̇_; ¬̇_; ∃̇_; ∀̇∈; ∃̇∈ )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Coding {ℓ} using ( pr; pr-inj; #mono; #-inj′ )
```

<!--en-->
The finite stage at `n` is `Lset (# n)`, where `# n` is the von Neumann numeral inside the hierarchy. Its ordinal and constructibility proofs let us treat both the stage and each of its members as objects of the model of `L`.
<!--zh-->
第 `n` 个有穷层是 `Lset (# n)`，其中 `# n` 是层级内的冯·诺伊曼数码。关于它的序数性与可构造性的证明，使我们能把该层及其每个成员都视为 `L` 模型中的对象。
<!--ja-->
第 `n` 有限段階は `Lset (# n)` であり、`# n` は階層内のフォン・ノイマン数項である。その順序数性と構成可能性により、この段階とその各要素を `L` のモデルの対象として扱える。
<!--/-->

```agda
open import L.Constructible {ℓ}
  using ( 𝒮ʟ; isL; isL-trans; Lset; Lset→isL; IsOrd; Lset-mono )
open import L.Ordinal {ℓ} using
  ( numeral-ord; #∈ω; ∈#-elim; #∈#-elim; mem-ord; boundingOrd )
open import L.Stage {ℓ} lem using ( stage; stage-ord; stage-mem )
```

<!--en-->
Two set-forming operations play different roles. Separation cuts each single-stage relation out of a bound, while replacement will later collect the relations along the internal `ω`. Finite approximations themselves will instead be built by `finSet` and `finSetL`.
<!--zh-->
两种集合构造承担不同任务。分离从一个界中切出单层关系；替换要到后面才用于沿内部 `ω` 收集这些关系。有穷逼近本身则由 `finSet` 与 `finSetL` 构造。
<!--ja-->
二つの集合構成は異なる役割を担う。分出は一つの段階の関係を上界から切り出し、置換は後で内部の `ω` に沿ってそれらの関係を集める。有限近似そのものは `finSet` と `finSetL` によって構成する。
<!--/-->

```agda
open import L.Axioms.Basic {ℓ}
  using ( extensionalL; LsetS; ∅ʟ; finSet; finSet-in; finSet-out; module FinOf )
open import L.Axioms.Full {ℓ} lem using ( hasSeparationL; hasReplacementL )
open import L.Recursion {ℓ} lem using ( smallDom; mereFunct )
open import L.Axioms.Infinity {ℓ} lem using ( ωʟ )
```

<!--en-->
The mathematical recurrence is already fixed: `before zero` is empty, and `before (suc n)` compares members of the next finite stage by their earliest disagreement over `finiteStage n`, using `before n` for earlier points. `PrecedesAt` expresses that successor step in the object language, while `RecShape` will organize its finite approximations.
<!--zh-->
数学递归已经确定：`before zero` 为空；`before (suc n)` 用 `before n` 排列较早的点，并在 `finiteStage n` 上按最早分歧比较下一有穷层的成员。`PrecedesAt` 在对象语言中表达这个后继步，`RecShape` 则组织它的有穷逼近。
<!--ja-->
数学的な再帰はすでに定まっている。`before zero` は空であり、`before (suc n)` は `before n` で先行する点を順序づけ、`finiteStage n` 上の最初の相違によって次の有限段階の要素を比較する。`PrecedesAt` はこの後続段階を対象言語で表し、`RecShape` はその有限近似を組織する。
<!--/-->

```agda
open import L.Choice.FiniteStageOrders {ℓ} lem
  using ( before; precedes; Agrees; Witness; finiteStage )
open import L.Choice.LimitStageOrder {ℓ} lem
  using ( PrecedesAt; module Precedes; module Described )
open import L.Coding.HierarchySequence {ℓ} lem using ( LsetGraphAt; module RecShape )
```

<!--en-->
Object-language application and extensionality let a formula say that a set is the value of a relation-valued table. They will be used first to describe one recursive step and later to read the completed family at a numeral.
<!--zh-->
对象语言中的应用与外延性，使公式能够断言某个集合是关系值表的一项取值。我们先用它们描述一个递归步，之后再用它们读取完整族在某个数码处的值。
<!--ja-->
対象言語の適用と外延性によって、ある集合が関係値を並べた表の値であることを論理式で述べられる。まず一回の再帰段階を記述するために使い、後には完成した族を数項の位置で読み取るために使う。
<!--/-->

```agda
open import L.Hierarchy {ℓ} lem using ( Lset-only; Lset-defines )
open import L.Coding.Model {ℓ} using ( prAtL; prAtL-adequate; prʟ; prʟ-fst; appAt; appAt-adequate; appC; appC-adequate; domAt-intro )
open import L.Coding.Expressions {ℓ} using ( numL; extAt; extAt-out; extAt-in; extAt-in-both )

```

<!--en-->
The proofs repeatedly transport equalities of sets and ordered pairs. They also require induction over the strict order on natural numbers, which will establish uniqueness of every value recorded by an approximation.
<!--zh-->
证明中会反复沿集合与有序对的等式作运输，还会对自然数严格序作归纳，以证明逼近所记录的每个取值都是唯一确定的。
<!--ja-->
証明では集合と順序対の等式に沿う移送を繰り返し用いる。また、自然数の狭義順序に関する帰納によって、近似に記録された各値が一意に定まることを示す。
<!--/-->

```agda
import FOL.Absoluteness
import FOL.ZFModel
open import Cubical.Foundations.Prelude using ( subst2 )
open import Cubical.Data.Sigma using ( Σ≡Prop )
open import Cubical.Data.Nat.Order using
```

<!--en-->
This induction uses the well-foundedness of natural-number `<`: the value at `k` is determined after all values at smaller indices have been identified. This is separate from any well-foundedness property of `before`.
<!--zh-->
这项归纳使用自然数 `<` 的良基性：先认定所有更小索引处的值，才能确定 `k` 处的值。这与 `before` 本身的任何良基性质是两回事。
<!--ja-->
この帰納で使うのは自然数の `<` の整礎性である。すべての小さい添字で値を同定してから、`k` における値を決定する。これは `before` 自身の整礎性とは別の事柄である。
<!--/-->

```agda
  ( _<_; <-trans; <-asym; pred-≤-pred; <-wellfounded; _≟_ )
import Cubical.Data.Nat.Order as NatOrder
open import Cubical.Induction.WellFounded using ( module WFI )
open import Cubical.Functions.Logic using ( ⇔toPath )
open import Cubical.Data.FinData.Properties using ( toℕ<n; enum; toℕ∘enum )
```

<!--en-->
Several witnesses below are available only under propositional truncation. Such a witness certifies existence without selecting canonical data; it may be eliminated when the target is a proposition, such as membership, `before`, or equality of sets in `V`.
<!--zh-->
下文若干见证只能在命题截断下取得。这种见证只保证存在，并不选出规范资料；只有当目标是命题时才能消去，例如隶属、`before`，或 `V` 中集合的等式。
<!--ja-->
以下では、いくつかの証人は命題的切り詰めの下でだけ得られる。この証人は存在を保証するが、標準的なデータを選び出さない。所属、`before`、または `V` における集合の等式のように、目標が命題である場合に消去できる。
<!--/-->

```agda
open import Cubical.Data.FinData.Base using ( toℕ )
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁; ∣_∣₁; squash₁ )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_; setIsSet )
```

<!--en-->
A set is accessed through a presentation of its members. This presentation lets us range over all members of a finite stage and construct their ordered pairs, while the internal `ω` supplies the eventual domain of the whole family.
<!--zh-->
集合通过其成员的呈现来访问。借助这种呈现，我们可以遍历有穷层的所有成员并构造它们的有序对；内部 `ω` 则提供整个族最终的定义域。
<!--ja-->
集合には、その要素の表示を通してアクセスする。この表示により、有限段階の全要素を走って順序対を構成でき、内部の `ω` は最終的な族全体の定義域を与える。
<!--/-->

```agda
open import Cubical.HITs.CumulativeHierarchy.Properties
  using ( ⟪_⟫; ⟪_⟫↪; ∈-asFiber; ∈∈ₛ; ∈ₛ⟪_⟫↪_ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ∅; ∅-empty; module InfinitySet )
open InfinitySet using ( #_; ω )
```

<!--en-->
From now on formulas are interpreted in the proposition-valued structure carried by the constructible sets.
<!--zh-->
从现在起，公式都在可构造集合所承载的命题值结构中解释。
<!--ja-->
以下では、論理式を構成可能集合がもつ命題値構造で解釈する。
<!--/-->

```agda

open hPropStructure 𝒮ʟ

```

<!--en-->
The carrier `S` consists of a set together with evidence that it belongs to `L`. Thus constructing an internal relation requires both the underlying set and its constructibility evidence.
<!--zh-->
载体 `S` 由一个集合及其属于 `L` 的证明组成。因此，构造内部关系既要给出底层集合，也要给出它的可构造性证明。
<!--ja-->
台 `S` は、集合と、それが `L` に属するという証明からなる。したがって内部関係を構成するには、基礎となる集合とその構成可能性の証明の両方が必要である。
<!--/-->

```agda
module ModelL = FOL.ZFModel 𝒮ʟ
open ModelL using ( SetOf )

```

<!--en-->
Absoluteness connects satisfaction in this structure with the corresponding assertions about the underlying sets. The notation `γ ⊨ φ` will express that a valuation `γ` satisfies an object-language formula `φ`.
<!--zh-->
绝对性把这一结构中的满足关系与底层集合上的相应断言联系起来。记号 `γ ⊨ φ` 表示赋值 `γ` 满足对象语言公式 `φ`。
<!--ja-->
絶対性は、この構造での充足を基礎となる集合についての対応する主張に結びつける。記法 `γ ⊨ φ` は、付値 `γ` が対象言語の論理式 `φ` を満たすことを表す。
<!--/-->

```agda
module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL renaming ( _⊨ᵐ_ to _⊨_ )

```

<!--en-->
Binding two new variables shifts every previous de Bruijn position by two. The map `sh2` records this shift so that each free variable still denotes the same object beneath the new binders.
<!--zh-->
绑定两个新变元会使原有的每个 de Bruijn 位置后移两位。映射 `sh2` 记录这一变化，使每个自由变元在新增绑定之下仍指称原来的对象。
<!--ja-->
二つの新しい変数を束縛すると、既存の各 de Bruijn 位置は二つ後ろへ移る。写像 `sh2` はこの移動を記録し、新しい束縛子の下でも各自由変数が同じ対象を指すようにする。
<!--/-->

```agda
private
  sh2 : ∀ {n} → Fin n → Fin (suc (suc n))
  sh2 i = suc (suc i)

```

<!--en-->
Applying the two-place shift twice gives `sh4`, the adjustment needed under four additional binders.
<!--zh-->
把二位移位应用两次得到 `sh4`，它用于穿过四个新增绑定。
<!--ja-->
二つ分の移動を二度適用して `sh4` を得る。これは四つの束縛子の下で必要な調整である。
<!--/-->

```agda
  sh4 : ∀ {n} → Fin n → Fin (suc (suc (suc (suc n))))
  sh4 i = sh2 (sh2 i)

```

<!--en-->
Similarly, `sh6` preserves references under six additional binders. These shifts change only de Bruijn positions, not the mathematical content of the formulas.
<!--zh-->
同样，`sh6` 在新增六个绑定时保持原有引用。这些移位只改变 de Bruijn 位置，不改变公式的数学内容。
<!--ja-->
同様に、`sh6` は六つの束縛子の下で元の参照を保つ。これらの移動が変えるのは de Bruijn 位置だけであり、論理式の数学的内容ではない。
<!--/-->

```agda
  sh6 : ∀ {n} → Fin n → Fin (suc (suc (suc (suc (suc (suc n))))))
  sh6 i = sh2 (sh4 i)
```

<!--en-->
The object `stageS n` packages the finite stage `Lset (# n)` as an element of the constructible carrier. Keeping this package opaque prevents later reasoning from depending on its particular proof component.
<!--zh-->
对象 `stageS n` 把有穷层 `Lset (# n)` 封装为可构造载体的一个元素。保持这一封装不透明，可使后续论证不依赖其中可构造性证明的具体写法。
<!--ja-->
対象 `stageS n` は有限段階 `Lset (# n)` を構成可能な台の要素としてまとめる。この包みを不透明にしておけば、後の議論は構成可能性証明の具体的な形に依存しない。
<!--/-->

```agda
opaque
  stageS : ℕ → S
  stageS n = LsetS (# n) (numeral-ord n)

```

<!--en-->
The equation `stageS-fst` reveals exactly the mathematical set carried by that package: its first component is `finiteStage n`.
<!--zh-->
等式 `stageS-fst` 恰好揭示该封装所携带的数学集合：它的第一分量是 `finiteStage n`。
<!--ja-->
等式 `stageS-fst` は、この包みが担う数学的集合だけを明らかにする。その第一成分は `finiteStage n` である。
<!--/-->

```agda
  stageS-fst : (n : ℕ) → fst (stageS n) ≡ finiteStage n
  stageS-fst n = refl

```

<!--en-->
The object `numS k` similarly packages the von Neumann numeral `# k` together with the proof that it is constructible.
<!--zh-->
对象 `numS k` 类似地把冯·诺伊曼数码 `# k` 与其可构造性证明封装在一起。
<!--ja-->
対象 `numS k` も同様に、フォン・ノイマン数項 `# k` とその構成可能性の証明をまとめる。
<!--/-->

```agda
  numS : ℕ → S
  numS k = # k , numL k

```

<!--en-->
The equation `numS-fst` lets later formulas read the underlying numeral without exposing the proof stored beside it.
<!--zh-->
等式 `numS-fst` 让后面的公式读取底层数码，而无须展开与它一同保存的证明。
<!--ja-->
等式 `numS-fst` により、後の論理式は隣に保存された証明を展開せずに、基礎となる数項を読み取れる。
<!--/-->

```agda
  numS-fst : (k : ℕ) → fst (numS k) ≡ # k
  numS-fst k = refl

```

<!--en-->
If `z` belongs to a constructible set `A`, transitivity of `L` shows that `z` is constructible as well. The wrapper `memS A z h` records this consequence so that `z` may be used as a model element.
<!--zh-->
若 `z` 属于可构造集合 `A`，则 `L` 的传递性说明 `z` 也可构造。封装 `memS A z h` 记录这一结论，使 `z` 能作为模型元素使用。
<!--ja-->
`z` が構成可能集合 `A` に属するなら、`L` の推移性によって `z` も構成可能である。包み `memS A z h` はこの帰結を記録し、`z` をモデルの要素として使えるようにする。
<!--/-->

```agda
  memS : (A : S) (z : V ℓ) → ⟨ z ∈ fst A ⟩ → S
  memS A z h = z , isL-trans {x = fst A} {y = z} h (snd A)

```

<!--en-->
The first component of `memS A z h` is still the original set `z`; the additional component supplies only its membership in `L`.
<!--zh-->
`memS A z h` 的第一分量仍是原集合 `z`；新增分量只提供它属于 `L` 的证明。
<!--ja-->
`memS A z h` の第一成分は元の集合 `z` のままであり、追加された成分は `L` への所属証明だけを与える。
<!--/-->

```agda
  memS-fst : (A : S) (z : V ℓ) (h : ⟨ z ∈ fst A ⟩) → fst (memS A z h) ≡ z
  memS-fst A z h = refl

```

<!--en-->
For model elements `a` and `b`, `prS a b` forms their ordered pair inside `L`. Relation sets below will contain objects of precisely this form.
<!--zh-->
对模型元素 `a` 与 `b`，`prS a b` 在 `L` 内构造它们的有序对。下文的关系集合正以这种对象为成员。
<!--ja-->
モデル要素 `a` と `b` に対し、`prS a b` はそれらの順序対を `L` の内部で作る。以下の関係集合は、まさにこの形の対象を要素にもつ。
<!--/-->

```agda
  prS : S → S → S
  prS a b = prʟ a b

```

<!--en-->
Forgetting the constructibility evidence recovers the ordinary ordered pair `pr (fst a) (fst b)`. This equation connects internal membership statements with the relation `before` on underlying sets.
<!--zh-->
忘掉可构造性证明后，就恢复普通有序对 `pr (fst a) (fst b)`。这条等式把内部隶属断言与底层集合上的关系 `before` 联系起来。
<!--ja-->
構成可能性の証明を忘れると、通常の順序対 `pr (fst a) (fst b)` が得られる。この等式が、内部の所属命題を基礎となる集合上の関係 `before` に結びつける。
<!--/-->

```agda
  prS-fst : (a b : S) → fst (prS a b) ≡ pr (fst a) (fst b)
  prS-fst a b = prʟ-fst a b

```

<!--en-->
In particular, every member `x` of `finiteStage n` can be lifted to the carrier `S`. The stage itself supplies the constructibility proof required for this lift.
<!--zh-->
特别地，`finiteStage n` 的每个成员 `x` 都能提升到载体 `S`；该层本身提供这项提升所需的可构造性证明。
<!--ja-->
特に、`finiteStage n` の各要素 `x` は台 `S` に持ち上げられる。その段階自身が、この持ち上げに必要な構成可能性の証明を与える。
<!--/-->

```agda
stageEl : (n : ℕ) (x : V ℓ) → ⟨ x ∈ finiteStage n ⟩ → S
stageEl n x h = x , Lset→isL (# n) (numeral-ord n) x h
```

<!--en-->
## Each stage's relation, as an element of `L`
<!--zh-->
## 每层的关系，作为 `L` 的一个元素
<!--ja-->
## 各段階の関係を `L` の要素にする
<!--/-->

<!--en-->
To represent a relation by separation, we first need one set containing every possible entry. The object `pairsAt n` therefore supplies a constructible bound `D` containing `pr u v` whenever both `u` and `v` belong to `finiteStage n`.
<!--zh-->
要用分离表示一条关系，首先需要一个包含所有可能条目的集合。因此，`pairsAt n` 给出可构造界 `D`：只要 `u,v` 都属于 `finiteStage n`，`D` 就包含 `pr u v`。
<!--ja-->
分出によって関係を表すには、まず可能な要素をすべて含む一つの集合が必要である。そこで `pairsAt n` は構成可能な上界 `D` を与え、`u` と `v` がともに `finiteStage n` に属するとき `pr u v` を含むようにする。
<!--/-->

```agda
pairsAt : (n : ℕ)
        → Σ[ D ∈ S ] ((u v : V ℓ) → ⟨ u ∈ finiteStage n ⟩ → ⟨ v ∈ finiteStage n ⟩
                     → ⟨ pr u v ∈ fst D ⟩)
pairsAt n = d .fst , onPair
  where
```

<!--en-->
A presented member of the finite stage already comes with its membership proof. The map `ixL` attaches the resulting constructibility proof, turning each presented member into an element of `S`.
<!--zh-->
有穷层中被呈现的成员已经携带自己的隶属证明。映射 `ixL` 再附上由此得到的可构造性证明，把每个被呈现成员变成 `S` 的元素。
<!--ja-->
有限段階の表示された要素には、その所属証明がすでに付いている。写像 `ixL` は、そこから得られる構成可能性証明を添え、各要素を `S` の要素にする。
<!--/-->

```agda
  ixL : ⟪ finiteStage n ⟫ → S
  ixL m = ⟪ finiteStage n ⟫↪ m
        , Lset→isL (# n) (numeral-ord n) (⟪ finiteStage n ⟫↪ m)
            (∈∈ₛ {a = ⟪ finiteStage n ⟫↪ m} {b = finiteStage n} .snd
              (∈ₛ⟪ finiteStage n ⟫↪ m))
```

<!--en-->
The product of the two presentations indexes every pair of stage members. Applying `smallDom` to their internal ordered pairs places this entire indexed family inside one constructible set `D`.
<!--zh-->
两个呈现的乘积索引了该层成员的每一对。对这些内部有序对应用 `smallDom`，便把整个索引族放入同一个可构造集合 `D` 中。
<!--ja-->
二つの表示の積は、段階の要素からなるすべての対を添字づける。それらの内部順序対に `smallDom` を適用すると、この添字族全体が一つの構成可能集合 `D` に収まる。
<!--/-->

```agda

  d : Σ[ D ∈ S ] ((p : ⟪ finiteStage n ⟫ × ⟪ finiteStage n ⟫)
                  → ⟨ prʟ (ixL (fst p)) (ixL (snd p)) ∈ˢ D ⟩)
  d = smallDom (⟪ finiteStage n ⟫ × ⟪ finiteStage n ⟫)
        (λ p → prʟ (ixL (fst p)) (ixL (snd p)))

```

<!--en-->
Given arbitrary `u,v ∈ finiteStage n`, their membership proofs locate presentation indices `fu` and `fv`. The bound contains the pair at those indices, and transport along the recovered component equalities yields membership of `pr u v` itself.
<!--zh-->
给定任意 `u,v ∈ finiteStage n`，它们的隶属证明给出呈现索引 `fu` 与 `fv`。该界包含这两个索引处的有序对，再沿恢复出的分量等式运输，便得到 `pr u v` 本身属于该界。
<!--ja-->
任意の `u,v ∈ finiteStage n` に対し、その所属証明から表示の添字 `fu` と `fv` が得られる。上界はその添字位置の順序対を含み、復元した成分の等式に沿って移送すれば、`pr u v` 自身の所属が得られる。
<!--/-->

```agda
  onPair : (u v : V ℓ) → ⟨ u ∈ finiteStage n ⟩ → ⟨ v ∈ finiteStage n ⟩
         → ⟨ pr u v ∈ fst (d .fst) ⟩
  onPair u v hu hv = subst (λ t → ⟨ t ∈ fst (d .fst) ⟩)
    (prʟ-fst (ixL (fu .fst)) (ixL (fv .fst)) ∙ cong₂ pr (fu .snd) (fv .snd))
    (d .snd (fu .fst , fv .fst))
```

<!--en-->
The two fibers `fu` and `fv` record exactly the presentation indices and the equalities identifying their represented members with `u` and `v`.
<!--zh-->
两个纤维 `fu` 与 `fv` 恰好记录呈现索引，以及把相应被呈现成员认同为 `u`、`v` 的等式。
<!--ja-->
二つのファイバー `fu` と `fv` は、表示の添字と、そこで表された要素をそれぞれ `u`、`v` と同定する等式を正確に記録する。
<!--/-->

```agda
    where
    fu = ∈-asFiber {a = u} {b = finiteStage n} hu
    fv = ∈-asFiber {a = v} {b = finiteStage n} hv
```

<!--en-->
Suppose that, on the same carrier `A`, every instance of `R' w z` implies `R w z`. Then an earliest-disagreement witness for `R` also gives one for `R'`. The direction reverses because the earlier-point relation occurs as an assumption in the agreement clause.
<!--zh-->
设在同一载体 `A` 上，每个 `R' w z` 都蕴含 `R w z`。那么，关于 `R` 的最早分歧见证也给出关于 `R'` 的见证。方向发生反转，是因为较早点上的关系出现在一致性子句的前件中。
<!--ja-->
同じ台 `A` 上で、各 `R' w z` から `R w z` が従うとする。このとき `R` に関する最初の相違の証人から `R'` に関する証人も得られる。向きが反転するのは、先行点での関係が一致条件の仮定として現れるためである。
<!--/-->

```agda
precedes-map : (R R' : V ℓ → V ℓ → hProp (ℓ-suc ℓ)) (A x y : V ℓ)
             → ((w z : V ℓ) → ⟨ w ∈ A ⟩ → ⟨ z ∈ A ⟩ → ⟨ R' w z ⟩ → ⟨ R w z ⟩)
             → ⟨ precedes R A x y ⟩ → ⟨ precedes R' A x y ⟩
precedes-map R R' A x y f = PT.map step
  where
```

<!--en-->
The disagreement point `z`, its membership in `A` and `y`, and its absence from `x` remain unchanged. Only the proof that `x` and `y` agree before `z` must be converted.
<!--zh-->
分歧点 `z`、它属于 `A` 与 `y` 的证明，以及它不属于 `x` 的证明都保持不变。需要转换的只有 `x` 与 `y` 在 `z` 之前一致的证明。
<!--ja-->
相違点 `z`、その `A` と `y` への所属、および `x` に属さないことは変わらない。変換が必要なのは、`z` より前で `x` と `y` が一致するという証明だけである。
<!--/-->

```agda
  step : Σ[ z ∈ V ℓ ] Witness R A x y z → Σ[ z ∈ V ℓ ] Witness R' A x y z
  step (z , (z∈A , (z∈y , (z∉x , ag)))) =
    z , (z∈A , (z∈y , (z∉x , ag')))
    where
    ag' : Agrees R' A x y z
```

<!--en-->
At an earlier point `w`, an assumption `R' w z` is first mapped to `R w z` and then passed to the original agreement proof. This establishes the required agreement relative to `R'`.
<!--zh-->
在较早点 `w`，先把假设 `R' w z` 映到 `R w z`，再交给原有的一致性证明，由此得到相对于 `R'` 的一致性。
<!--ja-->
先行点 `w` では、仮定 `R' w z` をまず `R w z` に写し、それを元の一致証明に渡す。これにより `R'` に関する必要な一致が得られる。
<!--/-->

```agda
    ag' w w∈A hR' = ag w w∈A (f w z w∈A z∈A hR')
```

<!--en-->
The separation condition receives a candidate relation entry as its only free variable. It existentially binds the previous relation and previous stage, pins them to the supplied constants by equality, and ranges the two endpoints over the current stage.
<!--zh-->
分离条件只把候选关系条目作为自由变元。它用存在量词绑定前一关系与前一层，以等式把它们固定为给定常元，并让两个端点在当前层中取值。
<!--ja-->
分出条件は、候補となる関係要素だけを自由変数として受け取る。前の関係と前の段階を存在量化し、等式によって与えられた定数に固定し、二つの端点を現在の段階の中で動かす。
<!--/-->

```agda
RelCond : (R A A' : S) → Formula S 1
RelCond R A A' =
  ∃̇ ( (var zero ≐ con R)
    ∧̇ ∃̇ ( (var zero ≐ con A)
         ∧̇ ∃̇∈ (con A') ( ∃̇∈ (con A')
```

<!--en-->
The remaining conjunct identifies the candidate with the ordered pair of the two endpoints and asserts `PrecedesAt` over the supplied earlier stage and relation. This is the successor comparison later used in the recursive step; here `RelCond` fixes the earlier stage and relation by constants, whereas the recursive formula obtains the relation from an approximation and identifies the stage through the hierarchy graph.
<!--zh-->
余下的合取把候选条目认同为两个端点的有序对，并断言它们相对于给定的前一层与前一关系满足 `PrecedesAt`。这正是递归步骤稍后采用的后继比较；区别在于，此处的 `RelCond` 用常元固定前一层与前一关系，而递归公式从逼近中取得关系，并通过层级图识别相应的层。
<!--ja-->
残る連言は、候補を二端点の順序対と同定し、与えられた直前の段階と関係に関して `PrecedesAt` が成り立つことを述べる。これは後で再帰ステップに使う後続段階の比較である。ただし、ここでの `RelCond` は直前の段階と関係を定数で固定するのに対し、再帰の論理式は関係を近似から取得し、対応する段階を階層グラフによって同定する。
<!--/-->

```agda
              ( prAtL (sh2 (sh2 zero)) (suc zero) zero
              ∧̇ PrecedesAt (sh2 (suc zero)) (sh2 zero) (suc zero) zero ) ) ) )

```

<!--en-->
Now define the representing sets recursively. At zero the relation is empty; at a successor, separation begins with the bound containing all pairs from the larger finite stage.
<!--zh-->
现在递归定义表示关系的集合。零处关系为空；在后继处，分离从包含较大有穷层全部成员对的界开始。
<!--ja-->
ここで表現集合を再帰的に定義する。ゼロでは関係は空であり、後続では大きい方の有限段階の全要素対を含む上界から分出を始める。
<!--/-->

```agda
opaque
  relAt : ℕ → S
  relAt zero    = ∅ʟ
  relAt (suc n) =
    hasSeparationL (pairsAt (suc n) .fst)
```

<!--en-->
From that bound, `RelCond (relAt n) (stageS n) (stageS (suc n))` selects exactly the pairs whose endpoints are compared by the successor clause based on the preceding relation.
<!--zh-->
在这个界中，`RelCond (relAt n) (stageS n) (stageS (suc n))` 恰好选出那些按以前一关系为基础的后继子句进行比较的端点对。
<!--ja-->
この上界から、`RelCond (relAt n) (stageS n) (stageS (suc n))` は、前の関係に基づく後続節によって比較される端点の対だけを選び出す。
<!--/-->

```agda
      (RelCond (relAt n) (stageS n) (stageS (suc n))) .fst .fst

```

<!--en-->
The equation `relAt-zero` records the base case explicitly, so a purported member of the zero-stage relation can later be reduced to membership in the empty set.
<!--zh-->
等式 `relAt-zero` 显式记录基例，使得以后能把所谓零层关系成员化为对空集的隶属，从而排除它。
<!--ja-->
等式 `relAt-zero` は基底の場合を明示する。これにより、ゼロ段階の関係に属するとされる要素を、後で空集合への所属へ帰着できる。
<!--/-->

```agda
  relAt-zero : relAt zero ≡ ∅ʟ
  relAt-zero = refl

```

<!--en-->
For a successor stage, membership in `relAt (suc n)` has two parts: the candidate lies in the pair bound, and it satisfies the separating formula determined by `relAt n`, the preceding stage, and the current stage.
<!--zh-->
在后继层，属于 `relAt (suc n)` 包含两部分：候选条目属于有序对之界，并且满足由 `relAt n`、前一层与当前层确定的分离公式。
<!--ja-->
後続段階で `relAt (suc n)` に属することは二つの部分からなる。候補が順序対の上界に属し、さらに `relAt n`、前の段階、現在の段階で定まる分出論理式を満たすことである。
<!--/-->

```agda
  relAt-mem : (n : ℕ) (z : S)
            → (z ∈ˢ relAt (suc n))
            ≡ ( (z ∈ˢ pairsAt (suc n) .fst)
              ⊓ ((z ∷ []) ⊨ RelCond (relAt n) (stageS n) (stageS (suc n))) )
  relAt-mem n =
```

<!--en-->
This equivalence is the exact specification supplied by separation. Later proofs use it in both directions, either extracting the formula from membership or assembling membership from a bound proof and a formula proof.
<!--zh-->
这条等价正是分离所给出的精确刻画。后续证明会双向使用它：或从隶属中取出公式，或由界证明与公式证明合成隶属。
<!--ja-->
この同値は分出が与える正確な仕様である。後の証明では、所属から論理式を取り出す向きと、上界の証明と論理式の証明から所属を組み立てる向きの両方で用いる。
<!--/-->

```agda
    hasSeparationL (pairsAt (suc n) .fst)
      (RelCond (relAt n) (stageS n) (stageS (suc n))) .fst .snd

```

<!--en-->
The predicate `Rel n a b` abbreviates membership of the ordered pair `pr a b` in the representing set `relAt n`. The next representation lemmas will show, for stage members, that this predicate is equivalent to `before n a b`.
<!--zh-->
谓词 `Rel n a b` 是有序对 `pr a b` 属于表示集合 `relAt n` 的缩写。接下来的表示引理将证明，对该层成员而言，这一谓词等价于 `before n a b`。
<!--ja-->
述語 `Rel n a b` は、順序対 `pr a b` が表現集合 `relAt n` に属することの略記である。続く表現補題は、段階の要素について、この述語が `before n a b` と同値であることを示す。
<!--/-->

```agda
Rel : ℕ → V ℓ → V ℓ → hProp (ℓ-suc ℓ)
Rel n a b = pr a b ∈ fst (relAt n)

```

<!--en-->
The proofs of those lemmas interpret `PrecedesAt` in an environment of five entries. The names `s1` and `s2` identify the two endpoint and stage positions after the surrounding binders have shifted them.
<!--zh-->
这些引理的证明会在含五个条目的环境中解释 `PrecedesAt`。在外围绑定造成移位后，`s1` 与 `s2` 标出端点槽与层槽的位置。
<!--ja-->
これらの補題の証明では、五つの要素からなる環境で `PrecedesAt` を解釈する。外側の束縛による移動の後で、`s1` と `s2` が端点と段階の位置を指定する。
<!--/-->

```agda
private
  s1 : Fin 5
  s1 = suc zero
  s2 : Fin 5
  s2 = sh2 zero
```

<!--en-->
The remaining positions `s3` and `s4` locate the previous relation and the coded ordered pair. Naming them once keeps the semantic argument aligned with the four roles in `RelCond`.
<!--zh-->
其余位置 `s3` 与 `s4` 分别指向前一关系和编码后的有序对。统一命名这些位置，使语义论证始终与 `RelCond` 中的四种角色对齐。
<!--ja-->
残る位置 `s3` と `s4` は、それぞれ前の関係と符号化された順序対を指す。これらに一度名前を付けることで、意味論的な議論を `RelCond` の四つの役割に対応させたままにできる。
<!--/-->

```agda
  s3 : Fin 5
  s3 = sh2 (suc zero)
  s4 : Fin 5
  s4 = sh2 (sh2 zero)

```

<!--en-->
To recognize an arbitrary member of the relation set, we must recover its two components. `RelOf k zv` therefore asks for `x,y` in `finiteStage k`, an equation identifying `zv` with their ordered pair, and a proof that `before k x y` holds. This witness type contains chosen components, so it is not itself a proposition.
<!--zh-->
要辨认关系集的任意成员，必须恢复它的两个分量。因此，`RelOf k zv` 要求给出 `finiteStage k` 中的 `x,y`、把 `zv` 认同为其有序对的等式，以及 `before k x y` 成立的证明。这个见证类型包含选定的分量，故其本身不一定是命题。
<!--ja-->
関係集合の任意の要素を同定するには、その二つの成分を復元する必要があります。そこで `RelOf k zv` は、`finiteStage k` に属する `x,y`、`zv` をその順序対と同定する等式、そして `before k x y` の証明を要求します。この証人型は選ばれた成分を含むので、それ自体は命題とは限りません。
<!--/-->

```agda
RelOf : (k : ℕ) → V ℓ → Type (ℓ-suc ℓ)
RelOf k zv = Σ[ x ∈ S ] Σ[ y ∈ S ]
  ( ⟨ fst x ∈ finiteStage k ⟩
  × ( ⟨ fst y ∈ finiteStage k ⟩
    × ( (zv ≡ pr (fst x) (fst y)) × ⟨ before k (fst x) (fst y) ⟩ ) ) )
```

<!--en-->
Membership in `relAt k` determines such components only under propositional truncation: the relation records that a suitable presentation exists, without choosing one canonically. In the reverse direction, explicit components and their comparison suffice to insert the pair into the relation.
<!--zh-->
从 `relAt k` 的隶属关系只能在命题截断下得到这样的分量：关系只记录合适的呈现存在，并不规范地选定一份呈现。反过来，显式给出的分量及其比较足以把该有序对写入关系。
<!--ja-->
`relAt k` への所属からこのような成分が得られるのは命題的切り詰めの下だけです。関係は適切な表示の存在を記録しますが、その一つを標準的に選びません。逆向きには、明示された成分とその比較から順序対を関係へ書き込めます。
<!--/-->

```agda

relAt-out : (k : ℕ) (zv : V ℓ) → ⟨ zv ∈ fst (relAt k) ⟩ → ∥ RelOf k zv ∥₁
relAt-in  : (k : ℕ) (zv : V ℓ) → RelOf k zv → ⟨ zv ∈ fst (relAt k) ⟩

```

<!--en-->
The base case reflects `before zero`: since `relAt zero` is empty, a supposed member yields a contradiction. At a successor, membership first exposes the separated condition, whose existential witnesses are available only through propositional truncation.
<!--zh-->
基例反映 `before zero`：`relAt zero` 为空，所以假定的成员会导出矛盾。在后继情形，隶属首先给出分离条件，而其中的存在见证只能经命题截断使用。
<!--ja-->
基底の場合は `before zero` を反映します。`relAt zero` は空なので、要素があると仮定すれば矛盾が得られます。後続の場合、所属からまず分出条件が得られ、その存在証人は命題的切り詰めを通してのみ利用できます。
<!--/-->

```agda
relAt-out zero zv h = Empty.rec
  (∅-empty zv (∈∈ₛ {a = zv} {b = ∅} .fst
    (subst (λ t → ⟨ zv ∈ fst t ⟩) relAt-zero h)))
relAt-out (suc n) zv h = PT.rec squash₁
  (λ { (r , (qr , ha)) → PT.rec squash₁
```

<!--en-->
Opening the truncated witnesses reveals a candidate predecessor relation, its finite stage, and the two components of the pair. The proof keeps the result truncated while it passes these data to the final reconstruction, so no particular presentation escapes as chosen data.
<!--zh-->
逐层打开被截断的见证后，可以看到候选的前一关系、相应有穷层及有序对的两个分量。证明在把这些资料交给最后的重构时始终保留命题截断，因此不会把某份特定呈现作为选定资料带出。
<!--ja-->
切り詰められた証人を順に開くと、候補となる直前の関係、その有限段階、そして順序対の二成分が現れます。最後の再構成へこれらを渡す間も結果を切り詰めたままにするため、特定の表示が選択済みデータとして外へ出ることはありません。
<!--/-->

```agda
    (λ { (a , (qa , hx)) → PT.rec squash₁
      (λ { (x , (x∈ , hy)) → PT.map (atY r a x qr qa x∈) hy }) hx }) ha }) cond
  where
  zS : S
  zS = memS (relAt (suc n)) zv h
```

<!--en-->
The underlying set `zv` is packaged as an element of `L` using its membership in `relAt (suc n)`. This permits the object-language separation condition to be evaluated at the very member being analyzed.
<!--zh-->
由 `zv ∈ relAt (suc n)` 及 `L` 的传递性，可以把底层集合 `zv` 封装成 `L` 的元素。这样便能在当前分析的这个成员上解释对象语言的分离条件。
<!--ja-->
`zv ∈ relAt (suc n)` と `L` の推移性により、基礎集合 `zv` を `L` の要素として包めます。これによって、いま調べている要素そのものにおいて対象言語の分出条件を解釈できます。
<!--/-->

```agda
  qz : fst zS ≡ zv
  qz = memS-fst (relAt (suc n)) zv h

```

<!--en-->
The defining property of separation turns the assumed membership into satisfaction of `RelCond`. Thus the rest of the argument may reason from the mathematical content of the condition rather than merely from membership in the bounded set of pairs.
<!--zh-->
分离的定义性质把所假定的隶属转成 `RelCond` 的满足关系。因此，后续论证可以使用该条件的数学内容，而不只停留在属于有界对集这一事实上。
<!--ja-->
分出の定義的性質により、仮定した所属は `RelCond` の充足へ変わります。したがって以後は、有界な順序対集合への所属だけでなく、その条件の数学的内容を用いて議論できます。
<!--/-->

```agda
  cond : ⟨ (zS ∷ []) ⊨ RelCond (relAt n) (stageS n) (stageS (suc n)) ⟩
  cond = subst ⟨_⟩ (relAt-mem n zS)
    (subst (λ t → ⟨ t ∈ fst (relAt (suc n)) ⟩) (sym qz) h) .snd

```

<!--en-->
For proposed components `x,y`, the remaining body says two things: the analyzed member is their ordered pair, and `x` precedes `y` by earliest disagreement over the preceding stage. The second statement still uses the relation represented by `r`, since the surrounding witness must identify that relation with `relAt n`.
<!--zh-->
对候选分量 `x,y`，剩余公式体陈述两件事：当前分析的成员是它们的有序对，并且 `x` 在前一层上按最早分歧先于 `y`。第二项仍使用 `r` 所表示的关系，因为外围见证还须把该关系认同为 `relAt n`。
<!--ja-->
候補の成分 `x,y` について、残る本体は二つのことを述べます。調べている要素がその順序対であることと、直前の段階上の最初の相違によって `x` が `y` に先行することです。後者はまだ `r` が表す関係を使います。その関係を `relAt n` と同定することは、外側の証人が担います。
<!--/-->

```agda
  Body : (r a x y : S) → Type (ℓ-suc ℓ)
  Body r a x y =
      ⟨ (y ∷ x ∷ a ∷ r ∷ zS ∷ []) ⊨ prAtL s4 s1 zero ⟩
    × ⟨ (y ∷ x ∷ a ∷ r ∷ zS ∷ []) ⊨ PrecedesAt s3 s2 s1 zero ⟩

```

<!--en-->
After `x` has been chosen from the successor stage, `AtY` records the remaining choice of `y` from that same stage together with the pair and comparison facts. This separation of the two choices matches the nested existential structure of `RelCond`.
<!--zh-->
从后继层选定 `x` 后，`AtY` 记录从同一层选择 `y`，并附上配对与比较事实。把两个选择分开，正好对应 `RelCond` 中嵌套的存在结构。
<!--ja-->
後続段階から `x` を選んだ後、`AtY` は同じ段階からの `y` の選択と、順序対および比較の事実を記録します。二つの選択を分けることで、`RelCond` の入れ子になった存在構造に対応します。
<!--/-->

```agda
  AtY : (r a x : S) → Type (ℓ-suc ℓ)
  AtY r a x = Σ[ y ∈ S ] (⟨ fst y ∈ fst (stageS (suc n)) ⟩ × Body r a x y)

```

<!--en-->
Once all witnesses are present, the stage equations place both components in `finiteStage (suc n)`. It remains to identify the analyzed member with their ordered pair and to translate the comparison based on the represented relation into `before (suc n)`; the next lemmas perform these two translations.
<!--zh-->
所有见证齐备后，层等式把两个分量都放入 `finiteStage (suc n)`。余下工作是把当前成员认同为其有序对，并把依据所表示关系作出的比较转成 `before (suc n)`；随后两部分分别完成这两种转换。
<!--ja-->
すべての証人がそろうと、段階の等式によって二成分はいずれも `finiteStage (suc n)` に属します。残るのは、調べている要素をその順序対と同定し、表された関係による比較を `before (suc n)` へ移すことです。続く補題がこの二つの変換を行います。
<!--/-->

```agda
  atY : (r a x : S) → fst r ≡ fst (relAt n) → fst a ≡ fst (stageS n)
      → ⟨ fst x ∈ fst (stageS (suc n)) ⟩ → AtY r a x → RelOf (suc n) zv
  atY r a x qr qa x∈ (y , (y∈ , (hpr , hprec))) =
    x , (y , ( subst (λ t → ⟨ fst x ∈ t ⟩) (stageS-fst (suc n)) x∈
             , ( subst (λ t → ⟨ fst y ∈ t ⟩) (stageS-fst (suc n)) y∈
```

<!--en-->
The equation identifying the supplied relation with `relAt n` lets any recorded predecessor pair be read as `Rel n`. This is one direction needed to interpret the generic `PrecedesAt` statement with the concrete relation constructed here.
<!--zh-->
供应关系与 `relAt n` 的等式，使其中记录的任意前驱对都能读成 `Rel n`。这是用本章构造的具体关系解释通用 `PrecedesAt` 陈述所需的一个方向。
<!--ja-->
与えられた関係を `relAt n` と同定する等式により、そこに記録された任意の先行する対を `Rel n` として読めます。これは、一般的な `PrecedesAt` の主張をここで構成した具体的な関係で解釈するために必要な一方向です。
<!--/-->

```agda
               , (sym qz ∙ qpair , below) ) ) )
    where
    Rrep : (s t : S) → ⟨ pr (fst s) (fst t) ∈ fst (lookup s3 (y ∷ x ∷ a ∷ r ∷ zS ∷ [])) ⟩
         → ⟨ Rel n (fst s) (fst t) ⟩
    Rrep s t p = subst (λ w → ⟨ pr (fst s) (fst t) ∈ w ⟩) qr p
```

<!--en-->
The converse transport writes a proof of `Rel n` back into the supplied relation. Having both directions allows the adequacy theorem for `PrecedesAt` to treat the two presentations as the same base relation.
<!--zh-->
反向搬运把 `Rel n` 的证明写回所供应的关系。有了这两个方向，`PrecedesAt` 的充分性定理便能把两种呈现当作同一个基底关系处理。
<!--ja-->
逆向きの輸送は `Rel n` の証明を与えられた関係へ書き戻します。両方向がそろうことで、`PrecedesAt` の妥当性定理は二つの表示を同じ基底関係として扱えます。
<!--/-->

```agda

    Rfill : (s t : S) → ⟨ Rel n (fst s) (fst t) ⟩
          → ⟨ pr (fst s) (fst t) ∈ fst (lookup s3 (y ∷ x ∷ a ∷ r ∷ zS ∷ [])) ⟩
    Rfill s t p = subst (λ w → ⟨ pr (fst s) (fst t) ∈ w ⟩) (sym qr) p

```

<!--en-->
With these representation maps fixed, the `Precedes` module supplies the semantic bridge between the object-language formula and the host predicate `precedes`. The bridge concerns one comparison step; it does not establish any order laws here.
<!--zh-->
固定这两条表示映射后，`Precedes` 模块提供对象语言公式与宿主谓词 `precedes` 之间的语义桥梁。这座桥只处理一次比较步骤，并不在这里证明任何序性质。
<!--ja-->
これら二つの表示写像を固定すると、`Precedes` モジュールが対象言語の論理式とホスト側の述語 `precedes` を結ぶ意味論的な橋を与えます。この橋が扱うのは一回の比較だけであり、ここで順序の性質を証明するものではありません。
<!--/-->

```agda
    module P = Precedes s3 s2 s1 zero (y ∷ x ∷ a ∷ r ∷ zS ∷ [])
                        (Rel n) Rrep Rfill

```

<!--en-->
Reading `PrecedesAt` yields a `precedes` comparison over the stage supplied by the formula. The stage equation then identifies that carrier with `finiteStage n`, which is the carrier used in the recursive definition of `before (suc n)`.
<!--zh-->
读出 `PrecedesAt` 得到在公式所供应之层上的 `precedes` 比较。层等式再把该载体认同为 `finiteStage n`，也就是 `before (suc n)` 的递归定义所使用的载体。
<!--ja-->
`PrecedesAt` を読み出すと、論理式から与えられた段階上の `precedes` 比較が得られます。段階の等式はその台を `finiteStage n` と同定します。これは `before (suc n)` の再帰的定義が用いる台です。
<!--/-->

```agda
    onStage : ⟨ precedes (Rel n) (finiteStage n) (fst x) (fst y) ⟩
    onStage = subst (λ w → ⟨ precedes (Rel n) w (fst x) (fst y) ⟩)
      (qa ∙ stageS-fst n) (P.PrecedesAt-out hprec)

```

<!--en-->
Inside the agreement clause, every use of the base relation must be converted from `before n` to membership in `relAt n`. The inductive inward lemma performs that conversion, and `precedes-map` then yields exactly the successor relation `before (suc n)`.
<!--zh-->
在一致性子句内部，每次使用基底关系时，都必须把 `before n` 转为 `relAt n` 中的隶属。归纳得到的写入引理完成这一转换，随后 `precedes-map` 恰好给出后继关系 `before (suc n)`。
<!--ja-->
一致の節の内部では、基底関係を使うたびに `before n` から `relAt n` への所属へ変換する必要があります。帰納的に得た書き込み補題がこの変換を行い、`precedes-map` からちょうど後続の関係 `before (suc n)` が得られます。
<!--/-->

```agda
    below : ⟨ before (suc n) (fst x) (fst y) ⟩
    below = precedes-map (Rel n) (before n) (finiteStage n) (fst x) (fst y)
      (λ w t hw ht hb → relAt-in n (pr w t)
        (stageEl n w hw , (stageEl n t ht , (hw , (ht , (refl , hb))))))
      onStage
```

<!--en-->
The adequacy of the pair formula identifies the packaged member with `pr (fst x) (fst y)`. Composing this equation with the packaging equation returns the required equality for the original `zv`.
<!--zh-->
配对公式的充分性把封装后的成员认同为 `pr (fst x) (fst y)`。再与封装等式复合，便得到原始 `zv` 所需的等式。
<!--ja-->
順序対の論理式の妥当性により、包まれた要素は `pr (fst x) (fst y)` と同定されます。この等式を包装の等式と合成すると、元の `zv` に必要な等式が得られます。
<!--/-->

```agda

    qpair : fst zS ≡ pr (fst x) (fst y)
    qpair = subst ⟨_⟩ (prAtL-adequate s4 s1 zero (y ∷ x ∷ a ∷ r ∷ zS ∷ [])) hpr

```

<!--en-->
For `k = 0`, a `RelOf` witness already contains an impossible proof of `before zero`, so the inward direction follows by contradiction. At a successor, the intended pair is inserted into the bounded set and shown to satisfy the separation condition.
<!--zh-->
当 `k = 0` 时，`RelOf` 见证已经包含不可能的 `before zero` 证明，所以写入方向由矛盾得出。在后继情形，目标有序对先被放入有界对集，再证明它满足分离条件。
<!--ja-->
`k = 0` のとき、`RelOf` の証人はすでに不可能な `before zero` の証明を含むため、書き込み方向は矛盾から従います。後続の場合、目的の順序対を有界な順序対集合へ入れ、それが分出条件を満たすことを示します。
<!--/-->

```agda

relAt-in zero zv (x , (y , (x∈ , (y∈ , (qq , hb))))) = Empty.rec* hb
relAt-in (suc n) zv (x , (y , (x∈ , (y∈ , (qq , hb))))) =
  subst (λ t → ⟨ t ∈ fst (relAt (suc n)) ⟩) (prS-fst x y ∙ sym qq)
    (subst ⟨_⟩ (sym (relAt-mem n (prS x y))) (inBound , cond))
  where
```

<!--en-->
The two stage-membership assumptions place the ordered pair inside `pairsAt (suc n)`. This is the bounding half of separation: only pairs of members of the finite stage can enter `relAt (suc n)`.
<!--zh-->
两个层隶属假设把该有序对放入 `pairsAt (suc n)`。这是分离所需的界：只有有穷层成员组成的对才可能进入 `relAt (suc n)`。
<!--ja-->
二つの段階所属の仮定から、その順序対は `pairsAt (suc n)` に入ります。これは分出に必要な境界であり、有限段階の要素からなる対だけが `relAt (suc n)` に入り得ます。
<!--/-->

```agda
  inBound : ⟨ prS x y ∈ˢ pairsAt (suc n) .fst ⟩
  inBound = subst (λ t → ⟨ t ∈ fst (pairsAt (suc n) .fst) ⟩) (sym (prS-fst x y))
    (pairsAt (suc n) .snd (fst x) (fst y) x∈ y∈)

```

<!--en-->
For the reverse construction the environment contains the actual predecessor relation `relAt n`, so its interpretation as `Rel n` needs only identity maps. The same semantic bridge can therefore be used to build `PrecedesAt` from a host comparison.
<!--zh-->
在反向构造中，环境含有实际的前一关系 `relAt n`，故把它解释为 `Rel n` 只需恒等映射。于是可以使用同一座语义桥，从宿主层比较构造 `PrecedesAt`。
<!--ja-->
逆向きの構成では、環境に実際の直前の関係 `relAt n` が入っているため、それを `Rel n` と解釈する写像は恒等写像で足ります。したがって同じ意味論的な橋を使い、ホスト側の比較から `PrecedesAt` を構成できます。
<!--/-->

```agda
  module P = Precedes s3 s2 s1 zero
                      (y ∷ x ∷ stageS n ∷ relAt n ∷ prS x y ∷ [])
                      (Rel n) (λ _ _ p → p) (λ _ _ p → p)

```

<!--en-->
The hypothesis `before (suc n) x y` unfolds to earliest disagreement using `before n`. To express the same agreement with the internal relation, each recorded preceding pair is read out through `relAt-out`; propositional truncation may be eliminated because the target `before n w t` is a proposition.
<!--zh-->
假设 `before (suc n) x y` 展开为以 `before n` 为基底的最早分歧。为了用内部关系表达同一份一致性，每个已记录的前置有序对都经 `relAt-out` 读出；由于目标 `before n w t` 是命题，可以消去命题截断。
<!--ja-->
仮定 `before (suc n) x y` は、`before n` を基底とする最初の相違へ展開されます。同じ一致条件を内部の関係で表すため、記録された各先行対を `relAt-out` で読み出します。目標の `before n w t` は命題なので、命題的切り詰めを除去できます。
<!--/-->

```agda
  held : ⟨ precedes (Rel n) (finiteStage n) (fst x) (fst y) ⟩
  held = precedes-map (before n) (Rel n) (finiteStage n) (fst x) (fst y)
    (λ w t hw ht hR → PT.rec (snd (before n w t)) (readBack w t)
      (relAt-out n (pr w t) hR))
    hb
```

<!--en-->
A recovered `RelOf` witness may name components different from `w,t`, but its pair equation says their ordered pair equals `pr w t`. Injectivity of ordered pairing identifies both components, after which the recorded `before n` proof has the required endpoints.
<!--zh-->
读回的 `RelOf` 见证可能使用不同于 `w,t` 的分量，但其中的配对等式说明其有序对等于 `pr w t`。有序配对的单射性分别认同两个分量，随后所记录的 `before n` 证明便具有所需端点。
<!--ja-->
復元された `RelOf` の証人は `w,t` とは別の成分を名指すかもしれませんが、その順序対の等式は `pr w t` と等しいことを述べます。順序対の単射性が二成分をそれぞれ同定し、記録された `before n` の証明を必要な端点へ移せます。
<!--/-->

```agda
    where
    readBack : (w t : V ℓ) → RelOf n (pr w t) → ⟨ before n w t ⟩
    readBack w t (p , (q , (p∈ , (q∈ , (qq' , hbf))))) =
      subst2 (λ s u → ⟨ before n s u ⟩)
        (sym (pr-inj qq' .fst)) (sym (pr-inj qq' .snd)) hbf
```

<!--en-->
The converted host comparison now satisfies the hypotheses of `PrecedesAt-in`. It supplies the comparison clause needed for the separation formula, with the predecessor stage and relation placed in their designated variables.
<!--zh-->
转换后的宿主层比较已满足 `PrecedesAt-in` 的假设。它给出分离公式所需的比较子句，其中前一层与前一关系位于相应变元中。
<!--ja-->
変換されたホスト側の比較は `PrecedesAt-in` の仮定を満たします。これにより、直前の段階と関係を所定の変数に置いた分出論理式の比較節が得られます。
<!--/-->

```agda

  hprec : ⟨ (y ∷ x ∷ stageS n ∷ relAt n ∷ prS x y ∷ [])
          ⊨ PrecedesAt s3 s2 s1 zero ⟩
  hprec = P.PrecedesAt-in
    (subst (λ w → ⟨ precedes (Rel n) w (fst x) (fst y) ⟩) (sym (stageS-fst n))
      held)
```

<!--en-->
The pair-recognition formula is satisfied because the candidate member was built as `prS x y`. Its adequacy equation connects the internal construction with the underlying ordered pair required by the formula.
<!--zh-->
候选成员本就是 `prS x y`，因此满足配对识别公式。其充分性等式把这一内部构造连接到公式所要求的底层有序对。
<!--ja-->
候補の要素は `prS x y` として構成されているため、順序対を認識する論理式を満たします。その妥当性の等式が、内部の構成を論理式の要求する基礎の順序対へ結び付けます。
<!--/-->

```agda

  hpr : ⟨ (y ∷ x ∷ stageS n ∷ relAt n ∷ prS x y ∷ []) ⊨ prAtL s4 s1 zero ⟩
  hpr = subst ⟨_⟩
    (sym (prAtL-adequate s4 s1 zero
      (y ∷ x ∷ stageS n ∷ relAt n ∷ prS x y ∷ []))) (prS-fst x y)

```

<!--en-->
The presentation equation for `stageS (suc n)` transports each known member of `finiteStage (suc n)` into the stage object used by the formula. No additional closure property is required.
<!--zh-->
`stageS (suc n)` 的呈现等式把 `finiteStage (suc n)` 的每个已知成员搬运到公式使用的层对象中。这里不需要额外的闭包性质。
<!--ja-->
`stageS (suc n)` の表示等式により、`finiteStage (suc n)` の既知の各要素を論理式が用いる段階対象へ輸送できます。追加の閉包性は必要ありません。
<!--/-->

```agda
  onStage : (w : V ℓ) → ⟨ w ∈ finiteStage (suc n) ⟩
          → ⟨ w ∈ fst (stageS (suc n)) ⟩
  onStage w hw = subst (λ t → ⟨ w ∈ t ⟩) (sym (stageS-fst (suc n))) hw

```

<!--en-->
The witnesses just constructed satisfy the complete separation condition: they identify the preceding relation and stage, place `x,y` in the successor stage, and establish both pairing and earliest disagreement. The nested existentials are introduced under propositional truncation, asserting existence without selecting canonical witnesses.
<!--zh-->
刚构造的见证满足完整的分离条件：它们认同前一关系与前一层，把 `x,y` 放入后继层，并建立配对与最早分歧。嵌套存在量词在命题截断下引入，只断言存在，并不选取规范见证。
<!--ja-->
ここまでに構成した証人は分出条件全体を満たします。直前の関係と段階を同定し、`x,y` を後続段階に置き、順序対と最初の相違の両方を確立します。入れ子の存在量化は命題的切り詰めの下で導入され、存在を主張するだけで標準的な証人を選びません。
<!--/-->

```agda
  cond : ⟨ (prS x y ∷ []) ⊨ RelCond (relAt n) (stageS n) (stageS (suc n)) ⟩
  cond = ∣ relAt n , (refl
       , ∣ stageS n , (refl
       , ∣ x , (onStage (fst x) x∈
       , ∣ y , (onStage (fst y) y∈ , (hpr , hprec)) ∣₁) ∣₁) ∣₁) ∣₁
```

<!--en-->
The useful outward interface starts with a known pair `pr u v`, where both endpoints already lie in `finiteStage n`. It eliminates the truncated presentation only into the proposition `before n u v`, so the absence of a canonical presentation causes no loss.
<!--zh-->
实用的读出接口从已知有序对 `pr u v` 出发，并预先假设两个端点都属于 `finiteStage n`。它只把截断呈现消去到命题 `before n u v`，因此没有规范呈现并不会造成损失。
<!--ja-->
実用的な読み出しのインターフェースは、両端点が `finiteStage n` に属すると分かっている順序対 `pr u v` から始まります。切り詰められた表示を除去する先は命題 `before n u v` だけなので、標準的な表示がなくても問題はありません。
<!--/-->

```agda

relAt-rep : (n : ℕ) (u v : V ℓ)
          → ⟨ u ∈ finiteStage n ⟩ → ⟨ v ∈ finiteStage n ⟩
          → ⟨ pr u v ∈ fst (relAt n) ⟩ → ⟨ before n u v ⟩
relAt-rep n u v hu hv h = PT.rec (snd (before n u v)) read (relAt-out n (pr u v) h)
  where
```

<!--en-->
If the recovered presentation uses components `p,q`, equality of its ordered pair with `pr u v` forces `p=u` and `q=v`. Transporting along these two equalities turns the stored comparison into the desired one.
<!--zh-->
若读回的呈现使用分量 `p,q`，其有序对与 `pr u v` 相等便迫使 `p=u` 且 `q=v`。沿这两条等式搬运，就把所存比较转成目标比较。
<!--ja-->
復元した表示が成分 `p,q` を用いていても、その順序対が `pr u v` と等しいことから `p=u` と `q=v` が従います。この二つの等式に沿って輸送すれば、記録された比較が目的の比較になります。
<!--/-->

```agda
  read : RelOf n (pr u v) → ⟨ before n u v ⟩
  read (p , (q , (p∈ , (q∈ , (qq , hbf))))) =
    subst2 (λ s t → ⟨ before n s t ⟩)
      (sym (pr-inj qq .fst)) (sym (pr-inj qq .snd)) hbf

```

<!--en-->
Conversely, stage membership of `u,v` and a proof of `before n u v` form an explicit `RelOf` witness for `pr u v`. The inward lemma then records that pair in `relAt n`, completing the pointwise representation in the other direction.
<!--zh-->
反过来，`u,v` 的层隶属与 `before n u v` 的证明组成 `pr u v` 的显式 `RelOf` 见证。写入引理随后把该对记录进 `relAt n`，完成逐对表示的另一个方向。
<!--ja-->
逆に、`u,v` の段階所属と `before n u v` の証明から、`pr u v` に対する明示的な `RelOf` の証人が得られます。書き込み補題がその対を `relAt n` に記録し、対ごとの表示の逆方向が完成します。
<!--/-->

```agda
relAt-fill : (n : ℕ) (u v : V ℓ)
           → ⟨ u ∈ finiteStage n ⟩ → ⟨ v ∈ finiteStage n ⟩
           → ⟨ before n u v ⟩ → ⟨ pr u v ∈ fst (relAt n) ⟩
relAt-fill n u v hu hv h = relAt-in n (pr u v)
  (stageEl n u hu , (stageEl n v hv , (hu , (hv , (refl , h)))))
```

<!--en-->
## The step, generic in everything it consults
<!--zh-->
## 那一步，对它所查阅的一切保持通用
<!--ja-->
## 参照対象すべてに一般的なステップ
<!--/-->

<!--en-->
The recursive description must accept a relation as data rather than refer directly to `relAt`. `Held r a b` gives the needed interpretation: `r` relates `a` to `b` exactly when it contains their ordered pair.
<!--zh-->
递归描述必须把关系当作资料接收，而不能直接指称 `relAt`。`Held r a b` 给出所需解释：当且仅当 `r` 含有 `a,b` 的有序对时，`r` 才把 `a` 关联到 `b`。
<!--ja-->
再帰的な記述は関係をデータとして受け取る必要があり、`relAt` を直接参照できません。`Held r a b` が必要な解釈を与えます。すなわち、`r` が `a,b` の順序対を含むとき、かつそのときに限り、`r` は `a` を `b` に関係付けます。
<!--/-->

```agda
Held : S → V ℓ → V ℓ → hProp (ℓ-suc ℓ)
Held r a b = pr a b ∈ fst r

```

<!--en-->
One recursive step first seeks an `∈`-maximal member `c` of the current index. When that index is the successor numeral `# (suc n)`, this member is its predecessor `# n`; at zero no such member exists. Consequently the relation defined by the step has no members at zero, without requiring a separate base formula.
<!--zh-->
一次递归步骤先寻找当前索引的一个 `∈`-极大成员 `c`。当该索引是后继数码 `# (suc n)` 时，这个成员就是其前驱 `# n`；在零处则不存在这样的成员。因此，该步骤所定义的关系在零处没有成员，而无须另写基例公式。
<!--ja-->
一回の再帰ステップでは、まず現在の添字の `∈` に関する最大要素 `c` を探します。その添字が後続数項 `# (suc n)` なら、この要素は直前の数項 `# n` です。零ではそのような要素が存在しないため、別の基底論理式を置かなくても、ステップが定める関係には要素がありません。
<!--/-->

```agda
opaque
 RelBodyAt : ∀ {n} → Fin n → Fin n → Fin n → Formula S n
 RelBodyAt z b f =
   ∃̇ ( (var zero ∈̇ var (suc b))
     ∧̇ ( ∀̇∈ (var (suc b)) (¬̇ (var (suc zero) ∈̇ var zero))
```

<!--en-->
Having found `c`, the formula reads from the approximation the relation stored at `c`. The hierarchy graph identifies the stages `Lset (fst c)` and `Lset` of the current index, and the two candidate endpoints range over the latter. These stages become finite stages only when the current index is identified with a numeral.
<!--zh-->
找到 `c` 后，公式从逼近中读取在 `c` 处记录的关系。层级图识别出 `Lset (fst c)` 以及当前索引所确定的 `Lset` 层，两个候选端点都在后一层中取值。只有当当前索引被认同为数码时，这些层才是有穷层。
<!--ja-->
`c` が得られると、論理式は近似から `c` に記録された関係を読み取ります。階層のグラフは `Lset (fst c)` と現在の添字における `Lset` を同定し、二つの候補となる端点は後者の中を動きます。現在の添字が数項と同定されたときに限って、これらは有限段階になります。
<!--/-->

```agda
       ∧̇ ∃̇ ( appAt (sh2 f) (suc zero) zero
            ∧̇ ∃̇ ( LsetGraphAt zero (suc (suc zero))
                 ∧̇ ∃̇ ( LsetGraphAt zero (sh4 b)
                      ∧̇ ∃̇∈ (var zero)
                           ( ∃̇∈ (var (suc zero))
```

<!--en-->
The innermost clauses require the candidate entry to be the ordered pair of those endpoints and compare them by `PrecedesAt` over the predecessor stage, using the relation recovered from the approximation. Thus the formula describes the recursive successor step without naming any particular `relAt n`.
<!--zh-->
最内层子句要求候选条目是两个端点的有序对，并使用从逼近读出的关系，在前一层上以 `PrecedesAt` 比较它们。因此，该公式无需指称任何特定的 `relAt n`，便描述了递归的后继步骤。
<!--ja-->
最も内側の節は、候補の項目が二端点の順序対であることを要求し、近似から読み出した関係を使って、直前の段階上で `PrecedesAt` により両者を比較します。こうして、特定の `relAt n` を名指すことなく再帰の後続ステップを記述します。
<!--/-->

```agda
                               ( prAtL (sh6 z) (suc zero) zero
                               ∧̇ PrecedesAt (suc (suc (suc (suc zero))))
                                             (suc (suc (suc zero)))
                                             (suc zero) zero ) ) ) ) ) ) )

```

<!--en-->
`StepOf` is the meta-level meaning of this formula. It chooses four model elements: a candidate maximal member `c` of the current index, the relation value `r` recorded there, and the endpoints `x,y`; the candidate entry `zv` is already an argument of the predicate. Only after the current index is identified with a numeral will `c` be identified with its predecessor numeral.
<!--zh-->
`StepOf` 是该公式在元层面的含义。它选择四个模型元素：当前索引的候选极大成员 `c`、在那里记录的关系值 `r`，以及端点 `x,y`；候选条目 `zv` 已经是谓词的参数。只有在当前索引被认同为数码后，`c` 才会被认同为它的前驱数码。
<!--ja-->
`StepOf` はこの論理式のメタレベルでの意味です。現在の添字の最大要素となる候補 `c`、そこで記録された関係値 `r`、端点 `x,y` という四つのモデル要素を選びます。候補となる項目 `zv` は、すでに述語の引数です。現在の添字が数項と同定されて初めて、`c` はその直前の数項と同定されます。
<!--/-->

```agda
StepOf : ∀ {n} → Fin n → Fin n → S ^ n → V ℓ → Type (ℓ-suc ℓ)
StepOf b f γ zv =
  Σ[ c ∈ S ] Σ[ r ∈ S ] Σ[ x ∈ S ] Σ[ y ∈ S ]
    ( ⟨ fst c ∈ fst (lookup b γ) ⟩
    × ( ((d : S) → ⟨ fst d ∈ fst (lookup b γ) ⟩ → ⟨ fst c ∈ fst d ⟩ → Empty.⊥)
```

<!--en-->
The accompanying conditions say that `c` belongs to the current index and is `∈`-maximal there, the approximation records `r` at `c`, both endpoints lie in the hierarchy stage indexed by the current value, `zv` is their ordered pair, and `precedes (Held r)` compares them over `Lset (fst c)`. These are the mathematical data needed for one step; finiteness enters later from the numeral equation.
<!--zh-->
附带条件断言：`c` 属于当前索引并且在其中为 `∈`-极大元；逼近在 `c` 处记录 `r`；两个端点都属于当前取值所索引的层级阶段；`zv` 是它们的有序对；并且 `precedes (Held r)` 在 `Lset (fst c)` 上比较它们。这些正是一次递归步骤所需的数学数据；有穷性要到后面才由数码等式给出。
<!--ja-->
付随する条件は、`c` が現在の添字に属してそこで `∈` に関する最大要素であること、近似が `c` で `r` を記録すること、二端点が現在の値で添字づけられた階層の段階に属すること、`zv` がその順序対であること、そして `precedes (Held r)` が `Lset (fst c)` 上で二端点を比較することを述べます。これは一回の再帰ステップに必要な数学的データであり、有限性は後で数項の等式から得られます。
<!--/-->

```agda
      × ( ⟨ pr (fst c) (fst r) ∈ fst (lookup f γ) ⟩
        × ( ⟨ fst x ∈ Lset (fst (lookup b γ)) ⟩
          × ( ⟨ fst y ∈ Lset (fst (lookup b γ)) ⟩
            × ( (zv ≡ pr (fst x) (fst y))
              × ⟨ precedes (Held r) (Lset (fst c)) (fst x) (fst y) ⟩ ) ) ) ) ) )
```

<!--en-->
The semantic correspondence is now proved for arbitrary variables `z,b,f` and an arbitrary environment. The assumption that `lookup b γ` carries an ordinal is used to identify the stages described by the hierarchy graph with the corresponding `Lset` values.
<!--zh-->
下面对任意变元 `z,b,f` 与任意环境证明语义对应。关于 `lookup b γ` 的底层集合为序数这一假设，用于把层级图描述的各阶段认同为相应的 `Lset` 值。
<!--ja-->
ここから、任意の変数 `z,b,f` と任意の環境について意味論的な対応を示します。`lookup b γ` の台となる集合が順序数であるという仮定は、階層グラフが記述する段階を対応する `Lset` の値と同定するために使われます。
<!--/-->

```agda

module _ {n : ℕ} (z b f : Fin n) (γ : S ^ n)
         (ob : IsOrd (fst (lookup b γ))) where
  private
    Body : (c r A A' x y : S) → Type (ℓ-suc ℓ)
    Body c r A A' x y =
```

<!--en-->
After the six existential witnesses have extended the environment, the innermost body retains the two decisive facts: the value denoted by `z` is the ordered pair of `x,y`, and those endpoints satisfy `PrecedesAt` for the recovered stage and relation.
<!--zh-->
六个存在见证扩展环境后，最内层公式体保留两项决定性事实：`z` 所指的值是 `x,y` 的有序对，并且这两个端点相对于已恢复的层与关系满足 `PrecedesAt`。
<!--ja-->
六つの存在証人が環境を拡張した後、最も内側の本体には二つの決定的な事実が残ります。`z` が指す値が `x,y` の順序対であることと、復元された段階と関係について二端点が `PrecedesAt` を満たすことです。
<!--/-->

```agda
        ⟨ (y ∷ x ∷ A' ∷ A ∷ r ∷ c ∷ γ) ⊨ prAtL (sh6 z) (suc zero) zero ⟩
      × ⟨ (y ∷ x ∷ A' ∷ A ∷ r ∷ c ∷ γ)
          ⊨ PrecedesAt (suc (suc (suc (suc zero)))) (suc (suc (suc zero)))
                       (suc zero) zero ⟩

```

<!--en-->
For a fixed first endpoint `x`, `AtY` packages the remaining endpoint `y`, its membership in the current stage, and the two innermost facts. This type mirrors one layer of the formula's nested existential reading.
<!--zh-->
固定第一个端点 `x` 后，`AtY` 封装余下端点 `y`、它属于当前层的证明，以及最内层的两项事实。这个类型对应公式嵌套存在读法中的一层。
<!--ja-->
第一の端点 `x` を固定すると、`AtY` は残る端点 `y`、その現在の段階への所属、そして最も内側の二つの事実をまとめます。この型は、論理式の入れ子になった存在の読みの一層に対応します。
<!--/-->

```agda
    AtY : (c r A A' x : S) → Type (ℓ-suc ℓ)
    AtY c r A A' x = Σ[ y ∈ S ] (⟨ fst y ∈ fst A' ⟩ × Body c r A A' x y)

```

<!--en-->
`MaxOf c` expresses maximality in the membership order: if `d` also belongs to the current index, then `c ∈ d` is impossible. Together with `c` belonging to the index, this makes `c` membership-maximal. For a successor numeral it is the predecessor, while at zero the membership premise for `c` already has no witness.
<!--zh-->
`MaxOf c` 用隶属序表达极大性：若 `d` 也属于当前索引，则 `c ∈ d` 不可能成立。再结合 `c` 属于该索引，便知 `c` 是隶属序下的极大元。对后继数码而言，它就是前驱；在零处，`c` 的隶属前提本身已经没有见证。
<!--ja-->
`MaxOf c` は所属順序での最大性を表します。`d` も現在の添字に属するなら、`c ∈ d` は不可能です。`c` 自身が添字に属することと合わせると、`c` は所属順序で最大になります。後続数項では直前の数項であり、零では `c` の所属という前提の時点ですでに証人がありません。
<!--/-->

```agda
    MaxOf : (c : S) → Type (ℓ-suc ℓ)
    MaxOf c = (d : S) → ⟨ fst d ∈ fst (lookup b γ) ⟩ → ⟨ fst c ∈ fst d ⟩
            → Empty.⊥

```

<!--en-->
To turn the formula's witnesses into `StepOf`, the conversion assumes the membership and maximality of `c`, the approximation entry `(c,r)`, equations identifying the predecessor and current stages, and membership of `x` in the current stage. A final `AtY` witness supplies `y` and the two inner facts.
<!--zh-->
为了把公式见证转成 `StepOf`，该转换假设 `c` 的隶属与极大性、逼近条目 `(c,r)`、认同前一层与当前层的等式，以及 `x` 属于当前层。最后一份 `AtY` 见证供应 `y` 与两项内层事实。
<!--ja-->
論理式の証人を `StepOf` へ変換するため、`c` の所属と最大性、近似の項目 `(c,r)`、直前および現在の段階を同定する等式、そして `x` の現在の段階への所属を仮定します。最後の `AtY` の証人が `y` と二つの内側の事実を与えます。
<!--/-->

```agda
    atY : (c r A A' x : S) → ⟨ fst c ∈ fst (lookup b γ) ⟩ → MaxOf c
        → ⟨ pr (fst c) (fst r) ∈ fst (lookup f γ) ⟩
        → fst A ≡ Lset (fst c) → fst A' ≡ Lset (fst (lookup b γ))
        → ⟨ fst x ∈ fst A' ⟩
        → AtY c r A A' x → StepOf b f γ (fst (lookup z γ))
```

<!--en-->
The stage equation converts the formula's memberships of `x,y` into memberships in `Lset (lookup b γ)`, as required by `StepOf`. The pair equation and the host-level `precedes` comparison are then supplied by the two adequacy arguments below.
<!--zh-->
层等式把公式中 `x,y` 的隶属转换成 `Lset (lookup b γ)` 中的隶属，正好符合 `StepOf` 的要求。配对等式与宿主层 `precedes` 比较随后由下面两项充分性论证给出。
<!--ja-->
段階の等式は、論理式における `x,y` の所属を `Lset (lookup b γ)` への所属へ変換し、`StepOf` の要求に合わせます。順序対の等式とホスト側の `precedes` 比較は、続く二つの妥当性の議論から得られます。
<!--/-->

```agda
    atY c r A A' x c∈ cmax hf qA qA' x∈ (y , (y∈ , (hpr , hprec))) =
      c , (r , (x , (y , (c∈ , (cmax , (hf
        , ( subst (λ t → ⟨ fst x ∈ t ⟩) qA' x∈
          , ( subst (λ t → ⟨ fst y ∈ t ⟩) qA' y∈
            , (qpair , hprec') ) ) ) ) ) ) ) )
```

<!--en-->
Here the relation variable is interpreted directly as `Held r`, so the representation maps are identities. The `Precedes` bridge can therefore read the object-language comparison without any appeal to the already constructed `relAt` family.
<!--zh-->
这里直接把关系变元解释为 `Held r`，所以两条表示映射都是恒等映射。于是 `Precedes` 桥梁可以读出对象语言比较，而无需诉诸已经构造的 `relAt` 族。
<!--ja-->
ここでは関係変数を直接 `Held r` と解釈するため、二つの表示写像は恒等写像です。したがって `Precedes` の橋は、すでに構成した `relAt` の族に頼らずに対象言語の比較を読み出せます。
<!--/-->

```agda
      where
      module P = Precedes (suc (suc (suc (suc zero)))) (suc (suc (suc zero)))
                          (suc zero) zero (y ∷ x ∷ A' ∷ A ∷ r ∷ c ∷ γ)
                          (Held r) (λ _ _ p → p) (λ _ _ p → p)

```

<!--en-->
Reading `PrecedesAt` gives a comparison over the stage object bound in the formula. Its identifying equation transports that carrier to `Lset (fst c)`, yielding exactly the comparison required in `StepOf`.
<!--zh-->
读出 `PrecedesAt` 得到在公式所绑定层对象上的比较。该层的认同等式把载体搬运到 `Lset (fst c)`，从而得到 `StepOf` 所要求的比较。
<!--ja-->
`PrecedesAt` を読み出すと、論理式で束縛された段階対象上の比較が得られます。その段階を同定する等式によって台を `Lset (fst c)` へ輸送すると、ちょうど `StepOf` が要求する比較になります。
<!--/-->

```agda
      hprec' : ⟨ precedes (Held r) (Lset (fst c)) (fst x) (fst y) ⟩
      hprec' = subst (λ t → ⟨ precedes (Held r) t (fst x) (fst y) ⟩) qA
        (P.PrecedesAt-out hprec)

```

<!--en-->
Adequacy of `prAtL` identifies the value denoted by `z` with the ordered pair of the recovered endpoints. This supplies the pair equation in the meta-level step witness.
<!--zh-->
`prAtL` 的充分性把 `z` 所指的值认同为所恢复两端点的有序对。这便给出元层面步骤见证中的配对等式。
<!--ja-->
`prAtL` の妥当性により、`z` が指す値は復元された二端点の順序対と同定されます。これがメタレベルのステップ証人に必要な順序対の等式です。
<!--/-->

```agda
      qpair : fst (lookup z γ) ≡ pr (fst x) (fst y)
      qpair = subst ⟨_⟩
        (prAtL-adequate (sh6 z) (suc zero) zero
          (y ∷ x ∷ A' ∷ A ∷ r ∷ c ∷ γ)) hpr

```

<!--en-->
After the first endpoint `x` is exposed, the remaining endpoint is still known only to exist propositionally. `AtX` records exactly this intermediate state: stage membership of `x` together with a propositionally truncated `AtY` witness.
<!--zh-->
第一个端点 `x` 已经显露后，余下端点仍只在命题意义下存在。`AtX` 正好记录这一中间状态：`x` 的层隶属，以及经过命题截断的 `AtY` 见证。
<!--ja-->
第一の端点 `x` を取り出した後も、残る端点は命題的に存在することしか分かりません。`AtX` はこの中間状態、すなわち `x` の段階所属と命題的に切り詰められた `AtY` の証人を記録します。
<!--/-->

```agda
    AtX : (c r A A' : S) → Type (ℓ-suc ℓ)
    AtX c r A A' = Σ[ x ∈ S ] (⟨ fst x ∈ fst A' ⟩ × ∥ AtY c r A A' x ∥₁)

```

<!--en-->
Because the desired conclusion is itself propositionally truncated, the hidden `y` witness may be used without choosing it outside the proposition. Mapping the pointwise conversion over that truncation preserves precisely the amount of existence supplied by the formula.
<!--zh-->
由于目标结论本身也经过命题截断，可以使用隐藏的 `y` 见证，而不把它作为选定资料带出命题。把逐点转换映射过该截断，恰好保留公式所供应的存在强度。
<!--ja-->
目的の結論自体も命題的に切り詰められているため、隠された `y` の証人を命題の外で選ぶことなく利用できます。その切り詰めの上で各点の変換を写すことで、論理式が与える存在の強さをそのまま保ちます。
<!--/-->

```agda
    atX : (c r A A' : S) → ⟨ fst c ∈ fst (lookup b γ) ⟩ → MaxOf c
        → ⟨ pr (fst c) (fst r) ∈ fst (lookup f γ) ⟩
        → fst A ≡ Lset (fst c) → fst A' ≡ Lset (fst (lookup b γ))
        → AtX c r A A' → ∥ StepOf b f γ (fst (lookup z γ)) ∥₁
    atX c r A A' c∈ cmax hf qA qA' (x , (x∈ , hy)) =
```

<!--en-->
The inner conversion assembles one explicit `StepOf` witness from the recovered data, and `PT.map` places it back under propositional truncation. This finishes the outward semantic reading without producing a canonical predecessor or endpoint witness.
<!--zh-->
内层转换由恢复出的资料装配一份显式 `StepOf` 见证，`PT.map` 再把它放回命题截断之下。由此完成向外的语义读法，同时不产生规范的前驱或端点见证。
<!--ja-->
内側の変換は復元したデータから明示的な `StepOf` の証人を一つ組み立て、`PT.map` がそれを命題的切り詰めの下へ戻します。これで、標準的な直前要素や端点の証人を作ることなく、外向きの意味論的な読みが完了します。
<!--/-->

```agda
      PT.map (atY c r A A' x c∈ cmax hf qA qA' x∈) hy

```

<!--en-->
After the stage at `c` has been recovered, the remaining inner quantifiers identify the stage at the current index. `AtA'` packages a constructible set `A'`, evidence that it satisfies the stage graph there, and the propositionally truncated existence of the still deeper witnesses `x` and `y`. The truncation retains their existence without selecting a distinguished pair of witnesses.
<!--zh-->
找回 `c` 所索引的层之后，余下的内层量词要识别当前索引所索引的层。`AtA'` 打包一个可构造集合 `A'`、它在该处满足层图的证据，以及更内层见证 `x` 与 `y` 的命题截断存在。命题截断保留见证存在这一事实，却不选出一对规范见证。
<!--ja-->
`c` が添字づける段階を復元した後、残る内側の量化は現在の添字が指す段階を同定します。`AtA'` は、構成可能集合 `A'`、それがそこで段階のグラフを満たす証拠、さらに内側にある証人 `x` と `y` の命題的に切り詰められた存在をまとめます。この切り詰めは証人の存在を保ちますが、特定の証人の対を選びません。
<!--/-->

```agda
    AtA' : (c r A : S) → Type (ℓ-suc ℓ)
    AtA' c r A = Σ[ A' ∈ S ]
      ( ⟨ (A' ∷ A ∷ r ∷ c ∷ γ) ⊨ LsetGraphAt zero (sh4 b) ⟩
      × ∥ AtX c r A A' ∥₁ )

```

<!--en-->
To continue from `A'`, the argument keeps the information already obtained about `c`, the table entry `(c,r)`, and the identification of `A` with the stage at `c`. It remains to identify `A'` with the stage at the current ordinal index before the witnesses hidden in `AtX` can be interpreted as a semantic step.
<!--zh-->
要从 `A'` 继续，论证保留已经得到的关于 `c` 的信息、表中的条目 `(c,r)`，以及 `A` 与 `c` 所索引之层的同一视。在把 `AtX` 中隐藏的见证解释为语义步进之前，还须把 `A'` 识别为当前序数索引所索引的层。
<!--ja-->
`A'` から先へ進むため、論証はすでに得られた `c` の情報、表の項目 `(c,r)`、そして `A` と `c` が添字づける段階との同一視を保ちます。`AtX` に隠された証人を意味論的な一ステップとして解釈するには、その前に `A'` を現在の順序数添字が指す段階と同定しなければなりません。
<!--/-->

```agda
    atA' : (c r A : S) → ⟨ fst c ∈ fst (lookup b γ) ⟩ → MaxOf c
         → ⟨ pr (fst c) (fst r) ∈ fst (lookup f γ) ⟩
         → fst A ≡ Lset (fst c)
         → AtA' c r A → ∥ StepOf b f γ (fst (lookup z γ)) ∥₁
    atA' c r A c∈ cmax hf qA (A' , (hg , hx)) =
```

<!--en-->
The stage graph supplies exactly that identification. Its functionality theorem `Lset-only`, applied with the assumed ordinalness of the index, yields `fst A' ≡ Lset (fst (lookup b γ))`; the propositionally truncated `AtX` can then be eliminated into the propositionally truncated step result.
<!--zh-->
层图恰好给出这一同一视。把它的函数性定理 `Lset-only` 用于索引的序数性假设，便得到 `fst A' ≡ Lset (fst (lookup b γ))`；于是可以把命题截断的 `AtX` 消去到命题截断的步进结论中。
<!--ja-->
段階のグラフが、まさにこの同一視を与えます。その関数性定理 `Lset-only` に添字の順序数性を適用すると、`fst A' ≡ Lset (fst (lookup b γ))` が得られます。そこで、命題的に切り詰められた `AtX` を、命題的に切り詰められたステップの結論へ除去できます。
<!--/-->

```agda
      PT.rec squash₁ (atX c r A A' c∈ cmax hf qA qA') hx
      where
      qA' : fst A' ≡ Lset (fst (lookup b γ))
      qA' = Lset-only zero (sh4 b) (A' ∷ A ∷ r ∷ c ∷ γ) hg ob

```

<!--en-->
One quantifier farther out, `AtA` performs the analogous task for the stage indexed by `c`. It consists of a constructible set `A` satisfying the appropriate stage graph and the propositionally truncated existence of an `AtA'` continuation.
<!--zh-->
再向外一层量词，`AtA` 对 `c` 所索引的层完成同样的工作。它由一个满足相应层图的可构造集合 `A`，以及 `AtA'` 后续数据的命题截断存在组成。
<!--ja-->
量化を一つ外へ戻ると、`AtA` は `c` が添字づける段階について同じ役割を果たします。これは、対応する段階のグラフを満たす構成可能集合 `A` と、続きとなる `AtA'` の命題的に切り詰められた存在からなります。
<!--/-->

```agda
    AtA : (c r : S) → Type (ℓ-suc ℓ)
    AtA c r = Σ[ A ∈ S ]
      ( ⟨ (A ∷ r ∷ c ∷ γ) ⊨ LsetGraphAt zero (suc (suc zero)) ⟩
      × ∥ AtA' c r A ∥₁ )

```

<!--en-->
Interpreting this layer first requires the equality that tells us which stage `A` is. Once that equality is available, the truncated continuation can be eliminated into the truncated step, just as at the inner layer.
<!--zh-->
解释这一层时，首先需要一个等式来说明 `A` 究竟是哪一层。得到该等式后，便可像处理内层时一样，把命题截断的后续数据消去到命题截断的步进中。
<!--ja-->
この層を解釈するには、まず `A` がどの段階であるかを示す等式が必要です。その等式が得られれば、内側の層と同様に、切り詰められた続きから切り詰められたステップへ除去できます。
<!--/-->

```agda
    atA : (c r : S) → ⟨ fst c ∈ fst (lookup b γ) ⟩ → MaxOf c
        → ⟨ pr (fst c) (fst r) ∈ fst (lookup f γ) ⟩
        → AtA c r → ∥ StepOf b f γ (fst (lookup z γ)) ∥₁
    atA c r c∈ cmax hf (A , (hg , hA')) =
      PT.rec squash₁ (atA' c r A c∈ cmax hf qA) hA'
```

<!--en-->
Because `c` belongs to the ordinal denoted by `b`, `mem-ord` shows that `c` is itself an ordinal. Functionality of the stage graph at this ordinal then gives `fst A ≡ Lset (fst c)`. No monotonicity of stages is used in this identification.
<!--zh-->
由于 `c` 属于 `b` 所指的序数，`mem-ord` 表明 `c` 本身也是序数。层图在这个序数处的函数性随即给出 `fst A ≡ Lset (fst c)`。这一识别不使用层的单调性。
<!--ja-->
`c` は `b` が指す順序数に属するので、`mem-ord` により `c` 自身も順序数です。この順序数における段階のグラフの関数性から、`fst A ≡ Lset (fst c)` が得られます。この同定に段階の単調性は使いません。
<!--/-->

```agda
      where
      qA : fst A ≡ Lset (fst c)
      qA = Lset-only zero (suc (suc zero)) (A ∷ r ∷ c ∷ γ) hg
        (mem-ord {A = fst (lookup b γ)} ob (fst c) c∈)

```

<!--en-->
The next outer witness is the relation stored by the approximation at `c`. `AtR` records a constructible set `r`, satisfaction of the application formula that says the table contains the entry `(c,r)`, and the propositionally truncated continuation that reconstructs the two required stages.
<!--zh-->
再外一层的见证是逼近表在 `c` 处记录的关系。`AtR` 记录一个可构造集合 `r`、应用公式的满足证据，此公式表示表中含有条目 `(c,r)`，以及用于重建所需两层的后续数据之命题截断。
<!--ja-->
さらに外側の証人は、近似表が `c` に記録する関係です。`AtR` は、構成可能集合 `r`、表が項目 `(c,r)` を含むことを述べる適用論理式の充足、そして必要な二つの段階を復元する続きの命題的切り詰めを記録します。
<!--/-->

```agda
    AtR : (c : S) → Type (ℓ-suc ℓ)
    AtR c = Σ[ r ∈ S ]
      ( ⟨ (r ∷ c ∷ γ) ⊨ appAt (sh2 f) (suc zero) zero ⟩ × ∥ AtA c r ∥₁ )

```

<!--en-->
The adequacy of `appAt` converts its satisfaction judgment into the ambient membership statement for the ordered pair `(c,r)`. With this table entry available, the truncated `AtA` continuation may be eliminated into the truncated semantic step.
<!--zh-->
`appAt` 的充分性把它的满足判断转换成有序对 `(c,r)` 的周遭隶属陈述。有了这个表中条目，就可以把命题截断的 `AtA` 后续数据消去到命题截断的语义步进中。
<!--ja-->
`appAt` の妥当性は、その充足判断を順序対 `(c,r)` についての周囲の所属命題へ変換します。この表の項目が得られると、命題的に切り詰められた `AtA` の続きから、命題的に切り詰められた意味論的ステップへ除去できます。
<!--/-->

```agda
    atR : (c : S) → ⟨ fst c ∈ fst (lookup b γ) ⟩ → MaxOf c
        → AtR c → ∥ StepOf b f γ (fst (lookup z γ)) ∥₁
    atR c c∈ cmax (r , (happ , hA)) = PT.rec squash₁ (atA c r c∈ cmax hf) hA
      where
      hf : ⟨ pr (fst c) (fst r) ∈ fst (lookup f γ) ⟩
```

<!--en-->
Concretely, the recovered fact is `pr (fst c) (fst r) ∈ fst (lookup f γ)`. This is the meta-level form needed by `StepOf`: the approximation denoted by `f` assigns relation `r` to index `c`.
<!--zh-->
具体而言，恢复出的事实是 `pr (fst c) (fst r) ∈ fst (lookup f γ)`。这正是 `StepOf` 所需的元层面形式：`f` 所指的逼近把关系 `r` 赋给索引 `c`。
<!--ja-->
具体的に復元される事実は、`pr (fst c) (fst r) ∈ fst (lookup f γ)` です。これは `StepOf` が必要とするメタレベルの形であり、`f` が指す近似が添字 `c` に関係 `r` を割り当てることを表します。
<!--/-->

```agda
      hf = subst ⟨_⟩ (appAt-adequate (sh2 f) (suc zero) zero (r ∷ c ∷ γ)) happ

```

<!--en-->
At the outermost layer, `AtC` chooses a member `c` of the ordinal index and asserts that no member `d` of that index lies strictly above it, in the sense `c ∈ d`. Thus `c` is a membership-maximal element of the index. When the index is later identified with a nonzero von Neumann numeral, this condition identifies its predecessor; the remaining truncated component supplies the relation and stage data.
<!--zh-->
在最外层，`AtC` 选取序数索引的一个成员 `c`，并断言该索引中不存在满足 `c ∈ d` 的成员 `d`。因此 `c` 是该索引在隶属关系下的极大元。当后文把索引识别为一个非零冯·诺伊曼数码时，这个条件将识别出它的前驱；余下的命题截断分量则提供关系与层的数据。
<!--ja-->
最も外側で、`AtC` は順序数添字の要素 `c` を選び、その添字には `c ∈ d` を満たす要素 `d` がないと主張します。したがって `c` は所属関係に関する添字の極大要素です。後で添字が非零のフォン・ノイマン数項と同定されると、この条件がその直前の数項を同定します。残る命題的に切り詰められた成分は、関係と段階のデータを供給します。
<!--/-->

```agda
    AtC : Type (ℓ-suc ℓ)
    AtC = Σ[ c ∈ S ]
      ( ⟨ fst c ∈ fst (lookup b γ) ⟩
      × ( ⟨ (c ∷ γ) ⊨ ∀̇∈ (var (suc b)) (¬̇ (var (suc zero) ∈̇ var zero)) ⟩
        × ∥ AtR c ∥₁ ) )
```

<!--en-->
The bounded negation in the formula is interpreted in a lifted universe. Lowering it yields the ordinary function `MaxOf c`, which turns any alleged `d` with `d` in the index and `c ∈ d` into a contradiction. The truncated relation witness can then be eliminated through the preceding layers.
<!--zh-->
公式中的有界否定在提升后的宇宙中解释。把它降下便得到普通函数 `MaxOf c`：任何声称既属于该索引又满足 `c ∈ d` 的 `d` 都会导出矛盾。随后可经由前述各层消去命题截断的关系见证。
<!--ja-->
論理式の有界否定は持ち上げられた宇宙で解釈されます。それを降ろすと通常の関数 `MaxOf c` が得られ、添字に属しかつ `c ∈ d` を満たすとされる任意の `d` から矛盾を導けます。すると、切り詰められた関係の証人を先ほどの各層を通して除去できます。
<!--/-->

```agda

    atC : AtC → ∥ StepOf b f γ (fst (lookup z γ)) ∥₁
    atC (c , (c∈ , (hmax , hr))) = PT.rec squash₁ (atR c c∈ cmax) hr
      where
      cmax : MaxOf c
      cmax d hd hc = lower (hmax d hd hc)
```

<!--en-->
These nested interpretations provide the reading direction of the step body. For the converse direction, the same body formula is exposed locally so that an explicit `StepOf` witness can be placed back into its existential and bounded clauses.
<!--zh-->
这些逐层解释给出了步进主体的读出方向。为了建立反向结论，同一个主体公式在局部展开，使一个显式的 `StepOf` 见证能够重新填入其中的存在子句与有界子句。
<!--ja-->
これらの入れ子になった解釈により、ステップ本体を読み出す向きが得られます。逆向きには、同じ本体の論理式を局所的に展開し、明示的な `StepOf` の証人を存在節と有界節へ戻します。
<!--/-->

```agda

  opaque
   unfolding RelBodyAt

```

<!--en-->
Starting from satisfaction of `RelBodyAt`, the outer existential yields only the propositionally truncated existence of `c`. The successive readers recover the remaining data under the same restriction and finally produce `∥ StepOf b f γ (fst (lookup z γ)) ∥₁`. They establish that a step exists without choosing canonical witnesses for its nested quantifiers.
<!--zh-->
从 `RelBodyAt` 的满足证据出发，最外层存在量词只给出 `c` 的命题截断存在。逐层读式在同一限制下恢复余下数据，最终得到 `∥ StepOf b f γ (fst (lookup z γ)) ∥₁`。它们证明某个步进存在，却不为嵌套量词选择规范见证。
<!--ja-->
`RelBodyAt` の充足から始めると、最外側の存在量化が与えるのは `c` の命題的に切り詰められた存在だけです。各層の読みは同じ制限のもとで残りのデータを復元し、最後に `∥ StepOf b f γ (fst (lookup z γ)) ∥₁` を得ます。これはステップの存在を示しますが、入れ子の量化に対する標準的な証人を選びません。
<!--/-->

```agda
   RelBody-out : ⟨ γ ⊨ RelBodyAt z b f ⟩
               → ∥ StepOf b f γ (fst (lookup z γ)) ∥₁
   RelBody-out = PT.rec squash₁ atC

```

<!--en-->
Conversely, an explicit `StepOf` witness already contains `c`, the relation `r`, the compared objects `x,y`, their stage memberships, the ordered-pair equality, and the predecessor comparison. `RelBody-in` rebuilds the two intermediate stages and places all of this data into the nested formula. Its existential clauses are propositionally truncated, so the result asserts satisfaction rather than preserving a canonical tuple of internal witnesses.
<!--zh-->
反过来，一个显式的 `StepOf` 见证已经包含 `c`、关系 `r`、被比较的对象 `x,y`、它们的层隶属、有序对等式与前驱层比较。`RelBody-in` 重建两个中间层，并把这些数据逐一填入嵌套公式。公式的存在子句经过命题截断，因此结论断言公式得到满足，而不保留一组规范的内部见证。
<!--ja-->
逆に、明示的な `StepOf` の証人は、`c`、関係 `r`、比較される対象 `x,y`、それらの段階への所属、順序対の等式、直前の段階での比較をすでに含みます。`RelBody-in` は二つの中間段階を再構成し、このデータを入れ子の論理式へ入れます。存在節は命題的に切り詰められるため、結論は充足を主張しますが、内部の証人からなる標準的な組を保存しません。
<!--/-->

```agda
   RelBody-in : StepOf b f γ (fst (lookup z γ)) → ⟨ γ ⊨ RelBodyAt z b f ⟩
   RelBody-in (c , (r , (x , (y , (c∈ , (cmax , (hf , (x∈ , (y∈
              , (qpair , hprec))))))))))
     = ∣ c , (c∈ , (hmax , ∣ r , (happ , ∣ A , (hgA , ∣ A' , (hgA'
       , ∣ x , (x∈ , ∣ y , (y∈ , (hpr , hprec')) ∣₁) ∣₁) ∣₁) ∣₁) ∣₁)) ∣₁
```

<!--en-->
The first reconstructed fact is that `c` is an ordinal. Every member of an ordinal is an ordinal, so this follows from `c ∈ fst (lookup b γ)` and the ordinalness assumption on that set. It is precisely what is needed to form the constructible stage indexed by `c`.
<!--zh-->
首先要重建的事实是 `c` 为序数。序数的每个成员仍是序数，因此，这由 `c ∈ fst (lookup b γ)` 以及该集合的序数性假设得出；它也正是构造由 `c` 索引的可构造层所需的条件。
<!--ja-->
最初に再構成する事実は、`c` が順序数だということです。順序数の各要素は順序数なので、これは `c ∈ fst (lookup b γ)` とその集合の順序数性から従います。また、`c` を添字とする構成可能段階を作るためにちょうど必要な条件でもあります。
<!--/-->

```agda
     where
     oc : IsOrd (fst c)
     oc = mem-ord {A = fst (lookup b γ)} ob (fst c) c∈

```

<!--en-->
Using this ordinalness, `LsetS` packages `Lset (fst c)` as an element `A` of the model. This is the predecessor-indexed stage on which the earliest-disagreement comparison is evaluated.
<!--zh-->
利用这一序数性，`LsetS` 把 `Lset (fst c)` 打包为模型元素 `A`。最早分歧比较正是在这个由前驱索引的层上求值。
<!--ja-->
この順序数性を用いて、`LsetS` は `Lset (fst c)` を模型の要素 `A` としてまとめます。最初の相違による比較は、この直前の添字が指す段階で評価されます。
<!--/-->

```agda
     A : S
     A = LsetS (fst c) oc

```

<!--en-->
The assumed ordinalness of the current index similarly packages `Lset (fst (lookup b γ))` as `A'`. This second stage supplies the bound containing both objects whose ordered pair is to become a member of the current relation.
<!--zh-->
当前索引的序数性假设同样把 `Lset (fst (lookup b γ))` 打包为 `A'`。第二个层提供集合界，容纳有序对将要成为当前关系成员的两个对象。
<!--ja-->
現在の添字について仮定した順序数性から、同様に `Lset (fst (lookup b γ))` を `A'` としてまとめます。この二つ目の段階が、順序対として現在の関係の要素になる二対象を含む集合の上界を与えます。
<!--/-->

```agda
     A' : S
     A' = LsetS (fst (lookup b γ)) ob

```

<!--en-->
The semantic maximality function must next be expressed by the bounded universal negation in the object language. For each `d` in the index, any proof of `c ∈ d` is sent by `cmax` to contradiction and then lifted to the universe in which formula satisfaction lives.
<!--zh-->
接下来须用对象语言中的有界全称否定表达语义上的极大性函数。对索引中的每个 `d`，任何 `c ∈ d` 的证明都会被 `cmax` 送到矛盾，再提升到公式满足关系所在的宇宙。
<!--ja-->
次に、意味論的な極大性の関数を対象言語の有界全称否定で表します。添字に属する各 `d` について、`c ∈ d` の証明は `cmax` によって矛盾へ送られ、さらに論理式の充足が属する宇宙へ持ち上げられます。
<!--/-->

```agda
     hmax : ⟨ (c ∷ γ) ⊨ ∀̇∈ (var (suc b)) (¬̇ (var (suc zero) ∈̇ var zero)) ⟩
     hmax d hd hc = lift (cmax d hd hc)

```

<!--en-->
The table entry in `StepOf` has the ambient form `pr (fst c) (fst r) ∈ fst (lookup f γ)`. Transport along the inverse of the adequacy path for `appAt` turns this fact into satisfaction of the application atom, which is the form required by the body formula.
<!--zh-->
`StepOf` 中的表条目采用周遭形式 `pr (fst c) (fst r) ∈ fst (lookup f γ)`。沿 `appAt` 充分性路径的逆向搬运，便把这个事实转换为应用原子的满足证据，也就是主体公式所需的形式。
<!--ja-->
`StepOf` の表の項目は、`pr (fst c) (fst r) ∈ fst (lookup f γ)` という周囲の形をしています。`appAt` の妥当性を与える経路の逆向きに沿ってこの事実を輸送すると、本体の論理式が必要とする適用原子の充足になります。
<!--/-->

```agda
     happ : ⟨ (r ∷ c ∷ γ) ⊨ appAt (sh2 f) (suc zero) zero ⟩
     happ = subst ⟨_⟩
       (sym (appAt-adequate (sh2 f) (suc zero) zero (r ∷ c ∷ γ))) hf

```

<!--en-->
The chosen `A` is definitionally the stage at `c`. The presentation theorem for the hierarchy therefore proves the corresponding stage-graph clause from the ordinalness of `c` and reflexivity of the represented value.
<!--zh-->
所选的 `A` 按定义就是 `c` 所索引的层。因此，层级的呈现定理由 `c` 的序数性与被表示取值的自反等式证明相应的层图子句。
<!--ja-->
選んだ `A` は定義により `c` が添字づける段階です。したがって階層の表示定理は、`c` の順序数性と表される値の反射律から、対応する段階グラフの節を証明します。
<!--/-->

```agda
     hgA : ⟨ (A ∷ r ∷ c ∷ γ) ⊨ LsetGraphAt zero (suc (suc zero)) ⟩
     hgA = Lset-defines zero (suc (suc zero)) (A ∷ r ∷ c ∷ γ) oc refl

```

<!--en-->
The same presentation theorem proves the graph clause for `A'`, now at the current index. Here the required ordinalness is the standing assumption `ob`, so the formula recognizes `A'` as exactly the stage that bounds `x` and `y`.
<!--zh-->
同一个呈现定理在当前索引处证明 `A'` 的图子句。这里所需的序数性就是既定假设 `ob`，故公式把 `A'` 精确识别为容纳 `x` 与 `y` 的那一层。
<!--ja-->
同じ表示定理が、今度は現在の添字で `A'` のグラフ節を証明します。必要な順序数性は仮定 `ob` そのものなので、論理式は `A'` を `x` と `y` を含む段階として正確に認識します。
<!--/-->

```agda
     hgA' : ⟨ (A' ∷ A ∷ r ∷ c ∷ γ) ⊨ LsetGraphAt zero (sh4 b) ⟩
     hgA' = Lset-defines zero (sh4 b) (A' ∷ A ∷ r ∷ c ∷ γ) ob refl

```

<!--en-->
The equality in `StepOf` identifies the candidate value denoted by `z` with the Kuratowski pair of `x` and `y`. Transport along the inverse adequacy path for `prAtL` converts this equality into satisfaction of the object-language pairing clause.
<!--zh-->
`StepOf` 中的等式把 `z` 所指的候选取值认同为 `x` 与 `y` 的 Kuratowski 对。沿 `prAtL` 充分性路径的逆向搬运，把这个等式转换为对象语言配对子句的满足证据。
<!--ja-->
`StepOf` の等式は、`z` が指す候補値を `x` と `y` の Kuratowski 対と同定します。`prAtL` の妥当性を与える経路の逆向きに沿う輸送により、この等式を対象言語の対形成節の充足へ変換します。
<!--/-->

```agda
     hpr : ⟨ (y ∷ x ∷ A' ∷ A ∷ r ∷ c ∷ γ) ⊨ prAtL (sh6 z) (suc zero) zero ⟩
     hpr = subst ⟨_⟩
       (sym (prAtL-adequate (sh6 z) (suc zero) zero
         (y ∷ x ∷ A' ∷ A ∷ r ∷ c ∷ γ))) qpair

```

<!--en-->
It remains to translate the predecessor-stage comparison. The instance of `Precedes` interprets the base relation as `Held r`, namely membership of the ordered pair in `r`. Both representation maps are identities because this interpretation is already exactly the membership proposition expected by the object-language application formula.
<!--zh-->
最后还须翻译前驱层上的比较。这里的 `Precedes` 实例把基底关系解释为 `Held r`，也就是有序对属于 `r`。由于这一解释已经与对象语言应用公式所要求的隶属命题完全相同，两个表示映射都取恒等函数。
<!--ja-->
残るのは、直前の段階における比較の翻訳です。ここでの `Precedes` のインスタンスは基底関係を `Held r`、すなわち順序対が `r` に属するという命題として解釈します。この解釈は対象言語の適用論理式が求める所属命題とすでに同じなので、二つの表現写像はいずれも恒等関数です。
<!--/-->

```agda
     module P = Precedes (suc (suc (suc (suc zero)))) (suc (suc (suc zero)))
                         (suc zero) zero (y ∷ x ∷ A' ∷ A ∷ r ∷ c ∷ γ)
                         (Held r) (λ _ _ p → p) (λ _ _ p → p)

```

<!--en-->
With that interpretation fixed, `PrecedesAt-in` converts the semantic earliest-disagreement comparison carried by `StepOf` into satisfaction of `PrecedesAt`. This completes every clause of `RelBodyAt` and hence the converse bridge from semantic steps to the object-language formula.
<!--zh-->
固定这一解释后，`PrecedesAt-in` 把 `StepOf` 携带的语义最早分歧比较转换为 `PrecedesAt` 的满足证据。至此 `RelBodyAt` 的每个子句都已完成，从语义步进返回对象语言公式的桥梁也随之建立。
<!--ja-->
この解釈を固定すると、`PrecedesAt-in` は `StepOf` がもつ意味論的な最初の相違による比較を `PrecedesAt` の充足へ変換します。これで `RelBodyAt` のすべての節が満たされ、意味論的ステップから対象言語の論理式へ戻る橋が完成します。
<!--/-->

```agda
     hprec' : ⟨ (y ∷ x ∷ A' ∷ A ∷ r ∷ c ∷ γ)
              ⊨ PrecedesAt (suc (suc (suc (suc zero)))) (suc (suc (suc zero)))
                           (suc zero) zero ⟩
     hprec' = P.PrecedesAt-in hprec
```

<!--en-->
The body classifies a single candidate ordered pair. A relation value must collect exactly all such candidates, so the next construction takes the extensional closure of this one-step condition over an entire set.
<!--zh-->
上述主体只判定一个候选有序对。一个关系取值必须恰好收集所有这样的候选者，因此下一构造把这个单步条件外延地扩展到整个集合。
<!--ja-->
ここまでの本体は一つの候補となる順序対を分類するだけです。一つの関係値はそのような候補をちょうどすべて集めなければならないため、次の構成ではこの一ステップの条件を集合全体へ外延的に拡張します。
<!--/-->

<!--en-->
## The approximation and the graph
<!--zh-->
## 逼近与那个图
<!--ja-->
## 近似とグラフ
<!--/-->

<!--en-->
`RelStepAt v b f` says that the set denoted by `v` has exactly the elements satisfying `RelBodyAt`, with the candidate bound as the new variable at position zero and the indices `b,f` shifted beneath that binder. Thus it gives both inclusions: every member of the candidate relation realizes a semantic step, and every object realizing such a step belongs to the relation.
<!--zh-->
`RelStepAt v b f` 断言 `v` 所指集合的成员恰好是满足 `RelBodyAt` 的对象，其中候选者绑定为新引入的零号变元，索引 `b,f` 则在该绑定之下相应移位。因此它同时给出两个包含方向：候选关系的每个成员都实现一个语义步骤，而每个实现这种步骤的对象都属于该关系。
<!--ja-->
`RelStepAt v b f` は、`v` が指す集合の要素が `RelBodyAt` を満たす対象とちょうど一致することを述べます。候補は新しい零番の変数に束縛され、添字 `b,f` はその束縛子の下で移動します。したがって二つの包含が得られます。候補関係の各要素は意味論的ステップを実現し、そのようなステップを実現する各対象は候補関係に属します。
<!--/-->

```agda
opaque
  RelStepAt : ∀ {n} → Fin n → Fin n → Fin n → Formula S n
  RelStepAt v b f = extAt v (RelBodyAt zero (suc b) (suc f))

```

<!--en-->
The reading lemmas for this extensional description are valid whenever `fst (lookup b γ)` is an ordinal. The body formula needs this hypothesis to identify the two hierarchy stages appearing in a step witness.
<!--zh-->
只要 `fst (lookup b γ)` 是序数，这一外延描述的读式就成立。主体公式需要该假设来识别步骤见证中出现的两个可构造层。
<!--ja-->
`fst (lookup b γ)` が順序数であれば、この外延的記述の読みが成り立ちます。本体の論理式は、ステップの証人に現れる二つの構成可能段階を同定するためにこの仮定を使います。
<!--/-->

```agda
module _ {n : ℕ} (v b f : Fin n) (γ : S ^ n)
         (ob : IsOrd (fst (lookup b γ))) where
  opaque
   unfolding RelStepAt

```

<!--en-->
The forward inclusion takes a member `w` of the set denoted by `v`, reads the body formula at `w`, and obtains `∥ StepOf b f γ (fst w) ∥₁`. The result is truncated because the body discovers its predecessor, stored relation, and compared components through existential quantifiers.
<!--zh-->
正向包含从 `v` 所指集合的一个成员 `w` 出发，在 `w` 处读出主体公式，并得到 `∥ StepOf b f γ (fst w) ∥₁`。结果经过命题截断，因为主体通过存在量词找出前驱、所记录的关系与被比较的分量。
<!--ja-->
順向きの包含は、`v` が指す集合の要素 `w` から出発し、`w` における本体の論理式を読み、`∥ StepOf b f γ (fst w) ∥₁` を得ます。本体は存在量化によって直前の添字、記録された関係、比較される成分を見つけるため、結果は命題的に切り詰められています。
<!--/-->

```agda
   RelStep-out : ⟨ γ ⊨ RelStepAt v b f ⟩ → (w : S)
               → ⟨ fst w ∈ fst (lookup v γ) ⟩ → ∥ StepOf b f γ (fst w) ∥₁
   RelStep-out h w hw = RelBody-out zero (suc b) (suc f) (w ∷ γ) ob
     (extAt-out v (RelBodyAt zero (suc b) (suc f)) γ h w hw)

```

<!--en-->
The reverse inclusion starts with an explicit semantic step for `w`. `RelBody-in` turns it into satisfaction of the body, and the reverse direction of the extensional description concludes that `w` belongs to the set denoted by `v`.
<!--zh-->
反向包含从 `w` 的一个显式语义步骤出发。`RelBody-in` 把它转换为主体的满足证据，外延描述的反向蕴涵随即推出 `w` 属于 `v` 所指的集合。
<!--ja-->
逆向きの包含は、`w` に対する明示的な意味論的ステップから始めます。`RelBody-in` がそれを本体の充足へ変換し、外延的記述の逆向きの含意から `w` が `v` の指す集合に属することが従います。
<!--/-->

```agda
   RelStep-back : ⟨ γ ⊨ RelStepAt v b f ⟩ → (w : S) → StepOf b f γ (fst w)
                → ⟨ fst w ∈ fst (lookup v γ) ⟩
   RelStep-back h w s = extAt-in v (RelBodyAt zero (suc b) (suc f)) γ h w
     (RelBody-in zero (suc b) (suc f) (w ∷ γ) ob s)

```

<!--en-->
The introduction principle states the exact converse. To prove `RelStepAt`, it suffices to provide a truncated step for every member of the proposed relation and a membership proof for every explicit step witness. These two functions are the two extensional inclusions.
<!--zh-->
引入原理陈述了精确的逆命题。要证明 `RelStepAt`，只须对拟议关系的每个成员给出一个命题截断的步进，并对每个显式步进见证给出一个隶属证明。这两个函数正是外延性的两个包含方向。
<!--ja-->
導入原理はその正確な逆を述べます。`RelStepAt` を証明するには、候補関係の各要素に対して命題的に切り詰められたステップを与え、各明示的ステップ証人に対して所属を証明すれば十分です。この二つの関数が外延性の二つの包含です。
<!--/-->

```agda
   RelStep-in : ((w : S) → ⟨ fst w ∈ fst (lookup v γ) ⟩
                 → ∥ StepOf b f γ (fst w) ∥₁)
              → ((w : S) → StepOf b f γ (fst w)
                 → ⟨ fst w ∈ fst (lookup v γ) ⟩)
              → ⟨ γ ⊨ RelStepAt v b f ⟩
```

<!--en-->
For the first inclusion, each truncated step is mapped through `RelBody-in` and eliminated into the propositional satisfaction judgment. For the second, `RelBody-out` produces a truncated step, which is eliminated into the propositional membership judgment before applying the supplied reverse function. Truncation is removed only because both targets are propositions.
<!--zh-->
对第一个包含方向，每个命题截断的步进先经 `RelBody-in` 映射，再消去到作为命题的满足判断中。对第二个方向，`RelBody-out` 产生一个命题截断的步进；在应用给定的反向函数之前，它被消去到作为命题的隶属判断中。这里能够消去命题截断，仅仅因为两个目标都是命题。
<!--ja-->
第一の包含では、命題的に切り詰められた各ステップを `RelBody-in` で写し、命題である充足判断へ除去します。第二の包含では、`RelBody-out` が命題的に切り詰められたステップを生み、それを与えられた逆向きの関数に渡して、命題である所属判断へ除去します。命題的切り詰めを除去できるのは、どちらの目標も命題だからです。
<!--/-->

```agda
   RelStep-in into back = extAt-in-both v (RelBodyAt zero (suc b) (suc f)) γ
     (λ w hw → PT.rec (snd ((w ∷ γ) ⊨ RelBodyAt zero (suc b) (suc f)))
       (RelBody-in zero (suc b) (suc f) (w ∷ γ) ob) (into w hw))
     (λ w h → PT.rec (snd (fst w ∈ fst (lookup v γ))) (back w)
       (RelBody-out zero (suc b) (suc f) (w ∷ γ) ob h))
```

<!--en-->
This extensional step now instantiates the general recursion-shape construction. The resulting `ApproxAt` describes an initial-segment table whose domain and step clauses agree with `RelStepAt`, while `RelGraphAt` describes a value at the current index supported by such an approximation below it. The table becomes finite when that index is later identified with a numeral.
<!--zh-->
这个外延步进现在实例化通用的递归形状构造。所得 `ApproxAt` 描述一张初始段表，其定义域与逐点步进子句符合 `RelStepAt`；`RelGraphAt` 则描述当前索引处由此前这种逼近支撑的一个取值。后文把该索引识别为数码时，这张表才成为有穷表。
<!--ja-->
この外延的ステップによって、一般的な再帰形状の構成を具体化します。得られる `ApproxAt` は、添字より前の部分を定義域とし、各点でのステップ節が `RelStepAt` に従う表を記述します。`RelGraphAt` は、その近似に支えられた現在の添字での値を記述します。後で添字を数項と同定したとき、この表は有限になります。
<!--/-->

```agda

module A = RecShape RelStepAt
open A using ( ApproxAt; ApproxAt-value; ApproxAt-step
             ; ApproxAt-in; GraphOf; PairOf )
     renaming ( GraphAt to RelGraphAt; Graph-in to RelGraph-in
              ; Graph-out to RelGraph-out; PairGraphAt to PairRelGraphAt
```

<!--en-->
The same construction also provides introduction and elimination principles for the approximation graph and its paired form. The local names `RelGraphAt` and `PairRelGraphAt` record that this generic machinery is being used specifically for the recursively defined relation values.
<!--zh-->
同一构造还为逼近图及其成对形式提供引入与消去原理。局部名称 `RelGraphAt` 与 `PairRelGraphAt` 表明，这套通用机制在此专用于递归定义的关系取值。
<!--ja-->
同じ構成は、近似のグラフとその対にした形についての導入原理と除去原理も与えます。局所名 `RelGraphAt` と `PairRelGraphAt` は、この一般的な仕組みがここでは再帰的に定義された関係値に用いられることを示します。
<!--/-->

```agda
              ; PairGraph-in to PairRelGraph-in
              ; PairGraph-out to PairRelGraph-out )
```

<!--en-->
The formulas so far describe the shape of a recursion without yet identifying its values. The next task is to prove that any table satisfying this shape records exactly the previously constructed sets `relAt m`; correctness of recorded values and presence of the standard entries are separated for that purpose.
<!--zh-->
到目前为止，这些公式只描述递归的形状，尚未识别其取值。下一步要证明，任何满足这一形状的表所记录的恰是先前构造的集合 `relAt m`；为此，证明把已记录取值的正确性与标准条目的存在性分开处理。
<!--ja-->
ここまでの論理式は再帰の形を記述するだけで、その値をまだ同定していません。次の課題は、この形を満たす任意の表が、先に構成した集合 `relAt m` を正確に記録することを示すことです。そのため、記録された値の正しさと標準的な項目の存在を分けて扱います。
<!--/-->

<!--en-->
## The step, against the recursion
<!--zh-->
## 那一步，对着这场递归
<!--ja-->
## 再帰に対するステップ
<!--/-->

<!--en-->
`Values g k` is the correctness condition. For every `m < k`, if `g` contains an entry pairing `# m` with any model element `w`, then the underlying set of `w` equals the underlying set of `relAt m`. This states uniqueness of the set value at an already recorded index; it does not choose a unique proof or witness package.
<!--zh-->
`Values g k` 是正确性条件。对每个 `m < k`，若 `g` 含有把 `# m` 与任意模型元素 `w` 配成的条目，则 `w` 的底层集合等于 `relAt m` 的底层集合。这说明一个已记录索引处的集合值唯一，却不选择唯一的证明或见证包。
<!--ja-->
`Values g k` は正しさの条件です。各 `m < k` について、`g` が `# m` と任意の模型要素 `w` を組にした項目を含むなら、`w` の台集合は `relAt m` の台集合に等しくなります。これは、すでに記録された添字における集合値の一意性を述べますが、一意な証明や証人の組を選ぶものではありません。
<!--/-->

```agda
Values : S → ℕ → Type (ℓ-suc ℓ)
Values g k = (m : ℕ) → m < k → (w : S)
           → ⟨ pr (# m) (fst w) ∈ fst g ⟩ → fst w ≡ fst (relAt m)

```

<!--en-->
`Entries g k` is the complementary completeness condition. It requires the standard entry `(# m, relAt m)` to occur in `g` for every `m < k`. Together, `Values` and `Entries` say that the table has all earlier indices and only the intended set value at each of them.
<!--zh-->
`Entries g k` 是与之配合的完备性条件。它要求每个 `m < k` 的标准条目 `(# m, relAt m)` 都出现在 `g` 中。`Values` 与 `Entries` 合起来表明：表含有所有更小索引，并且每个索引处只记录预期的集合值。
<!--ja-->
`Entries g k` はそれを補う完全性の条件です。各 `m < k` について、標準的な項目 `(# m, relAt m)` が `g` に現れることを要求します。`Values` と `Entries` を合わせると、表がすべての小さい添字をもち、その各添字で意図した集合値だけを記録することが分かります。
<!--/-->

```agda
Entries : S → ℕ → Type (ℓ-suc ℓ)
Entries g k = (m : ℕ) → m < k → ⟨ pr (# m) (fst (relAt m)) ∈ fst g ⟩

```

<!--en-->
Any comparison `before k x y` forces `k` to be a successor. At zero the relation is empty, so a comparison gives a contradiction; at `suc m` the predecessor `m` and the required equality are immediate. This small lemma will let an element of `relAt k` be turned back into the predecessor data required by `StepOf`.
<!--zh-->
任何比较 `before k x y` 都迫使 `k` 为后继数。在零处该关系为空，因此比较会导出矛盾；在 `suc m` 处，前驱 `m` 与所需等式立即可得。这个小引理稍后把 `relAt k` 的成员转换回 `StepOf` 所需的前驱数据。
<!--ja-->
比較 `before k x y` が成り立つなら、`k` は後続数です。零では関係が空なので比較から矛盾が従い、`suc m` では直前の数 `m` と必要な等式がただちに得られます。この補題により、後で `relAt k` の要素を `StepOf` が必要とする直前の数のデータへ戻せます。
<!--/-->

```agda
before-suc : (k : ℕ) (x y : V ℓ) → ⟨ before k x y ⟩ → Σ[ m ∈ ℕ ] (k ≡ suc m)
before-suc zero    x y h = Empty.rec* h
before-suc (suc m) x y h = m , refl

```

<!--en-->
Fix a candidate relation denoted by `v`, an index denoted by `b`, and a table denoted by `f`. The equation `qb` identifies the index with the numeral `# k`, while `vals` and `ents` assert that the table is correct and complete below `k`. Under these hypotheses the semantic step at the index can be compared exactly with membership in `relAt k`.
<!--zh-->
固定 `v` 所指的候选关系、`b` 所指的索引与 `f` 所指的表。等式 `qb` 把索引认同为数码 `# k`，而 `vals` 与 `ents` 断言该表在 `k` 以下正确且完备。在这些假设下，索引处的语义步骤可以与 `relAt k` 中的隶属精确比较。
<!--ja-->
`v` が指す候補関係、`b` が指す添字、`f` が指す表を固定します。等式 `qb` は添字を数項 `# k` と同定し、`vals` と `ents` は表が `k` より下で正しく完全であることを主張します。これらの仮定のもとで、添字における意味論的ステップを `relAt k` への所属と正確に比較できます。
<!--/-->

```agda
module _ {n : ℕ} (v b f : Fin n) (γ : S ^ n) (k : ℕ)
         (qb : fst (lookup b γ) ≡ # k)
         (vals : Values (lookup f γ) k) (ents : Entries (lookup f γ) k) where
  private
    ob : IsOrd (fst (lookup b γ))
```

<!--en-->
The numeral `# k` is an ordinal. Transporting this fact against `qb : fst (lookup b γ) ≡ # k` proves that `fst (lookup b γ)` is an ordinal, which makes the earlier reading and filling lemmas for the step body available.
<!--zh-->
数码 `# k` 是序数。沿 `qb : fst (lookup b γ) ≡ # k` 的反向搬运这一事实，便证明 `fst (lookup b γ)` 为序数，从而可以使用先前关于步骤主体的读式与填入引理。
<!--ja-->
数項 `# k` は順序数です。この事実を `qb : fst (lookup b γ) ≡ # k` に沿って逆向きに輸送すると、`fst (lookup b γ)` が順序数であることが分かり、先に得たステップ本体の読みと書き入れの補題を使えるようになります。
<!--/-->

```agda
    ob = subst IsOrd (sym qb) (numeral-ord k)

```

<!--en-->
Consider an explicit `StepOf` witness for a candidate value `x`. Its maximal element `c` belongs to the index, and `qb` turns this into `fst c ∈ # k`. Numeral membership elimination recovers, under propositional truncation, a natural number `m < k` together with `fst c ≡ # m`; elimination is valid here because the desired membership `x ∈ relAt k` is a proposition.
<!--zh-->
考虑候选取值 `x` 的一个显式 `StepOf` 见证。其中的极大元 `c` 属于该索引，`qb` 把这一点转化为 `fst c ∈ # k`。数码隶属的消去在命题截断下恢复一个自然数 `m < k` 与等式 `fst c ≡ # m`；这里可以消去命题截断，因为目标隶属 `x ∈ relAt k` 是命题。
<!--ja-->
候補値 `x` に対する明示的な `StepOf` の証人を考えます。その極大要素 `c` は添字に属し、`qb` によって `fst c ∈ # k` と読み替えられます。数項への所属を除去すると、命題的切り詰めのもとで自然数 `m < k` と等式 `fst c ≡ # m` が復元されます。ここで切り詰めを除去できるのは、目標の所属 `x ∈ relAt k` が命題だからです。
<!--/-->

```agda
    into : (x : V ℓ) → StepOf b f γ x → ⟨ x ∈ fst (relAt k) ⟩
    into x (c , (r , (xx , (yy , (c∈ , (cmax , (hf , (xx∈ , (yy∈
           , (qx , hprec)))))))))) =
      PT.rec (snd (x ∈ fst (relAt k))) atC
        (∈#-elim k (fst c) (subst (λ t → ⟨ fst c ∈ t ⟩) qb c∈))
```

<!--en-->
For such an `m`, membership in `relAt k` is proved by its introduction lemma. The required `RelOf k x` witness uses the same components `xx` and `yy`, their memberships in `finiteStage k`, the equality identifying `x` with their ordered pair, and a comparison `before k xx yy`. The remaining work is therefore to show that the maximal `c` really corresponds to the immediate predecessor of `k` and to translate the recorded comparison accordingly.
<!--zh-->
对这样一个 `m`，可用 `relAt k` 的引入引理证明所需隶属。相应的 `RelOf k x` 见证沿用分量 `xx` 与 `yy`，并需要它们属于 `finiteStage k`、`x` 与其有序对的等式，以及比较 `before k xx yy`。余下工作因而是证明极大元 `c` 确实对应 `k` 的直接前驱，并据此翻译表中记录的比较。
<!--ja-->
このような `m` に対しては、`relAt k` の導入補題により必要な所属を証明します。対応する `RelOf k x` の証人は、同じ成分 `xx` と `yy`、それらの `finiteStage k` への所属、`x` をその順序対と同定する等式、そして比較 `before k xx yy` を用います。したがって残る仕事は、極大要素 `c` が実際に `k` の直前の数に対応することを示し、それに従って表に記録された比較を翻訳することです。
<!--/-->

```agda
      where
      atC : Σ[ m ∈ ℕ ] ((m < k) × (fst c ≡ # m)) → ⟨ x ∈ fst (relAt k) ⟩
      atC (m , (hm , qc)) = relAt-in k x
        (xx , (yy , (xxk , (yyk , (qx , below)))))
        where
```

<!--en-->
Since `c` is coded by `# m`, its being maximal among the members of `# k` should force `k = suc m`. Trichotomy compares `suc m` with `k`: the equality case gives the desired equation, while each strict case contradicts information already available about `m`, `k`, and maximality.
<!--zh-->
由于 `c` 由 `# m` 编码，而它又是 `# k` 的成员中的极大元，应有 `k = suc m`。三歧性比较 `suc m` 与 `k`：相等情形给出所需等式，两个严格不等情形则分别与已有的 `m`、`k` 关系或极大性矛盾。
<!--ja-->
`c` は `# m` によって符号化され、しかも `# k` の要素の中で極大なので、`k = suc m` でなければなりません。三分律で `suc m` と `k` を比較すると、等しい場合には求める等式が得られ、二つの狭義不等号の場合は、それぞれ既知の `m` と `k` の関係または極大性に矛盾します。
<!--/-->

```agda
        ksuc : k ≡ suc m
        ksuc = decide (suc m ≟ k)
          where
          decide : NatOrder.Trichotomy (suc m) k → k ≡ suc m
          decide (NatOrder.lt hlt) = Empty.rec
```

<!--en-->
If `suc m < k`, then the numeral `#(suc m)` is itself a member of `# k`. Since `c = # m`, we also have `c ∈ #(suc m)`. These two membership facts exhibit a member of the index strictly above `c`, contradicting the maximality clause.
<!--zh-->
若 `suc m < k`，则数码 `#(suc m)` 本身属于 `# k`。又因 `c = # m`，还有 `c ∈ #(suc m)`。这两个隶属事实在索引中给出了一个严格位于 `c` 之上的成员，与极大性子句矛盾。
<!--ja-->
もし `suc m < k` なら、数項 `#(suc m)` 自身が `# k` に属します。また `c = # m` なので、`c ∈ #(suc m)` でもあります。この二つの所属は、添字の中に `c` より真に大きい要素があることを示し、極大性の節に矛盾します。
<!--/-->

```agda
            (cmax (numS (suc m))
              (subst (λ t → ⟨ fst (numS (suc m)) ∈ t ⟩) (sym qb)
                (subst (λ t → ⟨ t ∈ # k ⟩) (sym (numS-fst (suc m)))
                  (#mono (suc m) k hlt)))
              (subst (λ t → ⟨ fst c ∈ t ⟩) (sym (numS-fst (suc m)))
```

<!--en-->
If instead `k < suc m`, removing the successors yields `k ≤ m`, which is incompatible with the already known `m < k`. Hence only equality remains, and reversing the trichotomy equality gives `k ≡ suc m` in the orientation needed below.
<!--zh-->
反之，若 `k < suc m`，去掉后继便得到 `k ≤ m`，这与已知的 `m < k` 不相容。因此只余相等情形；把三歧性给出的等式反向，即得下文所需方向的 `k ≡ suc m`。
<!--ja-->
反対に `k < suc m` なら、後続を外すことで `k ≤ m` が得られ、既知の `m < k` と両立しません。したがって等しい場合だけが残り、三分律から得た等式を反転すると、以下で必要な向きの `k ≡ suc m` が得られます。
<!--/-->

```agda
                (subst (λ t → ⟨ t ∈ # (suc m) ⟩) (sym qc)
                  (#mono m (suc m) NatOrder.≤-refl))))
          decide (NatOrder.eq e) = sym e
          decide (NatOrder.gt hgt) = Empty.rec (<-asym hm (pred-≤-pred hgt))

```

<!--en-->
The step witness already places `xx` in `Lset (fst (lookup b γ))`. Transport along `qb` identifies this set with `Lset (# k)`, which is `finiteStage k`, and therefore supplies the first stage-membership component required by `RelOf k x`.
<!--zh-->
步进见证已经给出 `xx` 属于 `Lset (fst (lookup b γ))`。沿 `qb` 搬运，把这个集合识别为 `Lset (# k)`，也就是 `finiteStage k`，从而得到 `RelOf k x` 所需的第一个层隶属分量。
<!--ja-->
ステップの証人はすでに、`xx` が `Lset (fst (lookup b γ))` に属することを与えています。`qb` に沿って輸送すると、この集合は `Lset (# k)`、すなわち `finiteStage k` と同定され、`RelOf k x` が必要とする第一の段階所属の成分が得られます。
<!--/-->

```agda
        xxk : ⟨ fst xx ∈ finiteStage k ⟩
        xxk = subst (λ t → ⟨ fst xx ∈ Lset t ⟩) qb xx∈

```

<!--en-->
Both endpoints of the pair must lie in the stage indexed by `k`. For the second endpoint, the equation identifying the bound with `# k` changes membership in `Lset (fst (lookup b γ))` into membership in `finiteStage k`.
<!--zh-->
有序对的两个端点都必须属于由 `k` 索引的层。对于第二个端点，界等于 `# k` 的等式把 `Lset (fst (lookup b γ))` 中的隶属关系化为 `finiteStage k` 中的隶属关系。
<!--ja-->
順序対の二つの端点は、いずれも `k` で添字づけられた段階に属さなければならない。第二の端点については、上界を `# k` と同一視する等式により、`Lset (fst (lookup b γ))` への所属を `finiteStage k` への所属に移す。
<!--/-->

```agda
        yyk : ⟨ fst yy ∈ finiteStage k ⟩
        yyk = subst (λ t → ⟨ fst yy ∈ Lset t ⟩) qb yy∈

```

<!--en-->
The table entry indexed by the predecessor numeral records a relation `r`. After the first coordinate is changed from `fst c` to `# m`, the correctness hypothesis `vals` identifies the underlying set of `r` with `relAt m`.
<!--zh-->
以前驱数码为索引的表项记录了关系 `r`。把第一分量从 `fst c` 化为 `# m` 后，正确性假设 `vals` 便把 `r` 的底层集合认同为 `relAt m`。
<!--ja-->
前者の数項で添字づけられた表の項目は、関係 `r` を記録している。第一成分を `fst c` から `# m` に移すと、正しさの仮定 `vals` によって `r` の台集合が `relAt m` と同一視される。
<!--/-->

```agda
        rval : fst r ≡ fst (relAt m)
        rval = vals m hm r
          (subst (λ t → ⟨ pr t (fst r) ∈ fst (lookup f γ) ⟩) qc hf)

```

<!--en-->
The step witness initially compares the endpoints over `Lset (fst c)` using the relation held by `r`. The equations `fst c ≡ # m` and `fst r ≡ fst (relAt m)` rewrite this as `precedes (Rel m) (finiteStage m)`.
<!--zh-->
步进见证起初在 `Lset (fst c)` 上用 `r` 所持的关系比较两个端点。等式 `fst c ≡ # m` 与 `fst r ≡ fst (relAt m)` 把它改写为 `precedes (Rel m) (finiteStage m)`。
<!--ja-->
ステップの証人は初め、`Lset (fst c)` 上で `r` が保持する関係を用いて二つの端点を比較する。等式 `fst c ≡ # m` と `fst r ≡ fst (relAt m)` により、これは `precedes (Rel m) (finiteStage m)` に書き換えられる。
<!--/-->

```agda
        atM : ⟨ precedes (Rel m) (finiteStage m) (fst xx) (fst yy) ⟩
        atM = subst (λ t → ⟨ precedes (λ s u → pr s u ∈ t) (finiteStage m)
                              (fst xx) (fst yy) ⟩) rval
          (subst (λ t → ⟨ precedes (Held r) (Lset t) (fst xx) (fst yy) ⟩) qc
            hprec)
```

<!--en-->
To obtain the recursive comparison, `precedes-map` replaces the base relation `Rel m` by `before m`. Its hypothesis runs in the reverse direction, from `before m` to membership in `relAt m`, because the base relation occurs in the premise of the agreement condition. Thus the result is `before (suc m)`, and the equation `k ≡ suc m` finally yields `before k`.
<!--zh-->
为了得到递归比较，`precedes-map` 把基底关系 `Rel m` 换成 `before m`。由于基底关系出现在一致性条件的前件中，它所需的假设方向相反，即从 `before m` 走向 `relAt m` 中的隶属。因此先得到 `before (suc m)`，再由等式 `k ≡ suc m` 得到 `before k`。
<!--ja-->
再帰的な比較を得るため、`precedes-map` は基底関係 `Rel m` を `before m` に置き換える。基底関係は一致条件の前提に現れるため、必要な仮定の向きは逆であり、`before m` から `relAt m` への所属へ進む。こうしてまず `before (suc m)` が得られ、等式 `k ≡ suc m` から `before k` が従う。
<!--/-->

```agda

        below : ⟨ before k (fst xx) (fst yy) ⟩
        below = subst (λ j → ⟨ before j (fst xx) (fst yy) ⟩) (sym ksuc)
          (precedes-map (Rel m) (before m) (finiteStage m) (fst xx) (fst yy)
            (λ w t hw ht hbf → relAt-fill m w t hw ht hbf) atM)

```

<!--en-->
For the converse direction, a member described by `RelOf k` must be turned into a semantic step witness. The two endpoints are already present; the remaining task is to recover the predecessor index, its relation entry, and the assertion that this predecessor is the maximal member of the bound.
<!--zh-->
在反方向上，要把由 `RelOf k` 描述的成员化为语义步进见证。两个端点已经给出；余下的任务是恢复前驱索引及其关系表项，并证明此前驱是界中的极大成员。
<!--ja-->
逆方向では、`RelOf k` で記述された要素を意味論的なステップの証人へ変換する。二つの端点はすでに与えられており、残る仕事は前者の添字とその関係の項目を復元し、その前者が上界の最大要素であることを示すことである。
<!--/-->

```agda
    from : (x : V ℓ) → RelOf k x → StepOf b f γ x
    from x (xx , (yy , (xx∈ , (yy∈ , (qx , hbf))))) =
      numS m , (relAt m , (xx , (yy , (c∈ , (cmax , (hf , (xxb , (yyb
        , (qx , hprec)))))))))
      where
```

<!--en-->
A proof of `before k` cannot exist when `k` is zero. The lemma `before-suc` therefore extracts a natural number `m` for which the comparison occurs at the successor stage.
<!--zh-->
当 `k` 为零时，`before k` 不可能有证明。因此，引理 `before-suc` 从现有比较中取出自然数 `m`，使该比较发生在后继层。
<!--ja-->
`k` が零なら `before k` の証明は存在しない。したがって補題 `before-suc` は、比較が後者段階で生じるような自然数 `m` を取り出す。
<!--/-->

```agda
      m : ℕ
      m = before-suc k (fst xx) (fst yy) hbf .fst

```

<!--en-->
The same successor analysis supplies the equation `k ≡ suc m`. This equation is the link between the comparison at level `k` and the recursive step whose base data live at level `m`.
<!--zh-->
同一次后继分析还给出等式 `k ≡ suc m`。该等式把第 `k` 层的比较与以第 `m` 层数据为基底的递归步联系起来。
<!--ja-->
同じ後者の分析から等式 `k ≡ suc m` も得られる。この等式が、段階 `k` での比較と、段階 `m` のデータを基底とする再帰のステップを結びつける。
<!--/-->

```agda
      qk : k ≡ suc m
      qk = before-suc k (fst xx) (fst yy) hbf .snd

```

<!--en-->
Since `k` is `suc m`, the predecessor satisfies `m < k`. This bound permits the proof to use both the correctness and the completeness assumptions for the approximation table at index `m`.
<!--zh-->
由于 `k` 等于 `suc m`，前驱满足 `m < k`。这个界使证明能够在索引 `m` 处同时使用逼近表的正确性与完备性假设。
<!--ja-->
`k` は `suc m` なので、前者は `m < k` を満たす。この上界により、添字 `m` における近似表の正しさと完全性の仮定をともに利用できる。
<!--/-->

```agda
      hm : m < k
      hm = subst (λ j → m < j) (sym qk) NatOrder.≤-refl

```

<!--en-->
The numeral representing the predecessor must be a member of the bound stored in `b`. The inequality `m < k` gives `# m ∈ # k`; the equations for `numS m` and the bound transport this membership to the required form.
<!--zh-->
表示前驱的数码必须属于 `b` 中保存的界。不等式 `m < k` 给出 `# m ∈ # k`；关于 `numS m` 与界的等式再把这项隶属关系化为所需形式。
<!--ja-->
前者を表す数項は、`b` に保存された上界の要素でなければならない。不等式 `m < k` から `# m ∈ # k` が得られ、`numS m` と上界についての等式がこの所属を必要な形へ移す。
<!--/-->

```agda
      c∈ : ⟨ fst (numS m) ∈ fst (lookup b γ) ⟩
      c∈ = subst (λ t → ⟨ fst (numS m) ∈ t ⟩) (sym qb)
        (subst (λ t → ⟨ t ∈ # k ⟩) (sym (numS-fst m)) (#mono m k hm))

```

<!--en-->
It remains to show that `# m` is maximal among the members of `# k`. Given `d ∈ # k` and `# m ∈ d`, numeral elimination presents `d` merely as some `# j` with `j < k`; the two memberships would then force both `m < j` and `j ≤ m`.
<!--zh-->
还需证明 `# m` 是 `# k` 的成员中的极大者。给定 `d ∈ # k` 与 `# m ∈ d`，数码消去只在命题截断中把 `d` 表成某个满足 `j < k` 的 `# j`；这两项隶属将同时迫使 `m < j` 与 `j ≤ m`。
<!--ja-->
さらに、`# m` が `# k` の要素のうち最大であることを示す必要がある。`d ∈ # k` と `# m ∈ d` が与えられると、数項の消去は命題的切り詰めの中で `d` を `j < k` を満たすある `# j` として表す。この二つの所属から `m < j` と `j ≤ m` が同時に従う。
<!--/-->

```agda
      cmax : (d : S) → ⟨ fst d ∈ fst (lookup b γ) ⟩
           → ⟨ fst (numS m) ∈ fst d ⟩ → Empty.⊥
      cmax d hd hc = PT.rec Empty.isProp⊥ step
        (∈#-elim k (fst d) (subst (λ t → ⟨ fst d ∈ t ⟩) qb hd))
        where
```

<!--en-->
In a branch where `d ≡ # j`, membership of `d` in `# k = # (suc m)` gives `j ≤ m`. Membership of `# m` in `d` gives the opposing strict inequality `m < j`, so asymmetry of the natural-number order closes the branch.
<!--zh-->
在 `d ≡ # j` 的分支中，`d` 属于 `# k = # (suc m)` 给出 `j ≤ m`。另一方面，`# m` 属于 `d` 给出严格不等式 `m < j`，自然数序的非对称性遂排除该分支。
<!--ja-->
`d ≡ # j` という分岐では、`d` が `# k = # (suc m)` に属することから `j ≤ m` が得られる。一方、`# m` が `d` に属することから狭義不等式 `m < j` が得られるので、自然数順序の非対称性がこの分岐を退ける。
<!--/-->

```agda
        step : Σ[ j ∈ ℕ ] ((j < k) × (fst d ≡ # j)) → Empty.⊥
        step (j , (hj , qd)) = <-asym mj (pred-≤-pred (subst (λ i → j < i) qk hj))
          where
          mj : m < j
          mj = #∈#-elim m j
```

<!--en-->
The derivation of `m < j` uses the exact correspondence between membership of von Neumann numerals and strict order. The equalities for `numS m` and `d ≡ # j` first rewrite the assumed membership into `# m ∈ # j`, after which numeral membership can be decoded.
<!--zh-->
`m < j` 的推导使用冯·诺伊曼数码的隶属关系与严格序之间的准确对应。关于 `numS m` 的等式和 `d ≡ # j` 先把假设的隶属改写为 `# m ∈ # j`，随后即可解码数码隶属。
<!--ja-->
`m < j` の導出には、フォン・ノイマン数項の所属と狭義順序との正確な対応を用いる。`numS m` の等式と `d ≡ # j` により、仮定された所属をまず `# m ∈ # j` に書き換え、その後で数項の所属を復号する。
<!--/-->

```agda
            (subst (λ t → ⟨ t ∈ # j ⟩) (numS-fst m)
              (subst (λ t → ⟨ fst (numS m) ∈ t ⟩) qd hc))

```

<!--en-->
Completeness `ents` supplies the standard table entry `(# m , relAt m)` because `m < k`. Rewriting `# m` as the underlying set of `numS m` gives exactly the entry required by the semantic step witness.
<!--zh-->
由于 `m < k`，完备性 `ents` 给出标准表项 `(# m , relAt m)`。把 `# m` 改写为 `numS m` 的底层集合，便得到语义步进见证所需的表项。
<!--ja-->
`m < k` であるため、完全性 `ents` は標準的な表の項目 `(# m , relAt m)` を与える。`# m` を `numS m` の台集合として書き換えると、意味論的なステップの証人が要求する項目が得られる。
<!--/-->

```agda
      hf : ⟨ pr (fst (numS m)) (fst (relAt m)) ∈ fst (lookup f γ) ⟩
      hf = subst (λ t → ⟨ pr t (fst (relAt m)) ∈ fst (lookup f γ) ⟩)
        (sym (numS-fst m)) (ents m hm)

```

<!--en-->
The `RelOf k` record places the first endpoint in `finiteStage k`, which is `Lset (# k)`. Rewriting `# k` by the bound equation places that endpoint in `Lset (fst (lookup b γ))`, as required by `StepOf`.
<!--zh-->
`RelOf k` 记录把第一个端点置于 `finiteStage k`，也就是 `Lset (# k)`。用界等式改写 `# k` 后，该端点便属于 `Lset (fst (lookup b γ))`，正好满足 `StepOf` 的要求。
<!--ja-->
`RelOf k` の記録は第一の端点を `finiteStage k`、すなわち `Lset (# k)` に置く。上界の等式で `# k` を書き換えると、その端点は `Lset (fst (lookup b γ))` に属し、`StepOf` の要件を満たす。
<!--/-->

```agda
      xxb : ⟨ fst xx ∈ Lset (fst (lookup b γ)) ⟩
      xxb = subst (λ t → ⟨ fst xx ∈ Lset t ⟩) (sym qb) xx∈

```

<!--en-->
The same transport places the second endpoint in the stage determined by the bound. The two endpoint conditions ensure that the reconstructed step remains a bounded relation rather than a comparison over arbitrary sets.
<!--zh-->
同样的运输把第二个端点置于由界确定的层中。这两个端点条件保证重建出的步仍是有界关系，而不是任意集合上的比较。
<!--ja-->
同じ移送によって、第二の端点も上界が定める段階に置かれる。二つの端点条件により、復元されたステップは任意の集合上の比較ではなく、有界な関係にとどまる。
<!--/-->

```agda
      yyb : ⟨ fst yy ∈ Lset (fst (lookup b γ)) ⟩
      yyb = subst (λ t → ⟨ fst yy ∈ Lset t ⟩) (sym qb) yy∈

```

<!--en-->
The comparison stored in `RelOf k` is first rewritten along `k ≡ suc m`, exposing the recursive clause `precedes (before m) (finiteStage m)`. To express the semantic step, its base relation must then be changed from `before m` to membership in `relAt m`.
<!--zh-->
`RelOf k` 中保存的比较先沿 `k ≡ suc m` 改写，从而显出递归子句 `precedes (before m) (finiteStage m)`。为了得到语义步进，还须把其基底关系从 `before m` 换成 `relAt m` 中的隶属。
<!--ja-->
`RelOf k` に保存された比較をまず `k ≡ suc m` に沿って書き換え、再帰節 `precedes (before m) (finiteStage m)` を現す。意味論的なステップを得るには、さらにその基底関係を `before m` から `relAt m` への所属へ置き換えなければならない。
<!--/-->

```agda
      hprec : ⟨ precedes (Held (relAt m)) (Lset (fst (numS m)))
                 (fst xx) (fst yy) ⟩
      hprec = subst (λ t → ⟨ precedes (Held (relAt m)) (Lset t)
                              (fst xx) (fst yy) ⟩) (sym (numS-fst m))
        (precedes-map (before m) (Rel m) (finiteStage m) (fst xx) (fst yy)
```

<!--en-->
Here `precedes-map` uses `relAt-rep`, whose direction is from membership in `relAt m` back to `before m`; contravariance in the agreement premise then produces a comparison based on `Rel m`. Finally the numeral equation rewrites the stage as `Lset (fst (numS m))`, giving the last field of `StepOf`.
<!--zh-->
这里，`precedes-map` 使用方向从 `relAt m` 中的隶属回到 `before m` 的 `relAt-rep`；一致性前件中的反变性于是给出以 `Rel m` 为基底的比较。最后，数码等式把该层改写为 `Lset (fst (numS m))`，从而得到 `StepOf` 的最后一个字段。
<!--ja-->
ここで `precedes-map` は、`relAt m` への所属から `before m` へ戻る向きの `relAt-rep` を用いる。一致条件の前提における反変性により、`Rel m` を基底とする比較が得られる。最後に数項の等式で段階を `Lset (fst (numS m))` に書き換え、`StepOf` の最後の欄を得る。
<!--/-->

```agda
          (λ w t hw ht hR → relAt-rep m w t hw ht hR)
          (subst (λ j → ⟨ before j (fst xx) (fst yy) ⟩) qk hbf))

```

<!--en-->
The lemma `step-rel` proves that any set satisfying the step formula at index `k` equals `relAt k`. Extensionality reduces this set equality to two membership implications. In the forward implication, `RelStep-out` yields a propositionally truncated step witness, and `into` sends any such witness to membership in `relAt k`.
<!--zh-->
引理 `step-rel` 证明：在索引 `k` 处满足步进公式的任意集合都等于 `relAt k`。外延性把这个集合等式化为两个隶属蕴涵。在正向蕴涵中，`RelStep-out` 给出命题截断的步进见证，而 `into` 把其中任意见证送到 `relAt k` 的隶属关系。
<!--ja-->
補題 `step-rel` は、添字 `k` でステップ論理式を満たす任意の集合が `relAt k` に等しいことを示す。外延性により、この集合の等式は二つの所属の含意に帰着する。順方向では、`RelStep-out` が命題的に切り詰められたステップの証人を与え、`into` がその任意の証人を `relAt k` への所属へ送る。
<!--/-->

```agda
  step-rel : ⟨ γ ⊨ RelStepAt v b f ⟩ → fst (lookup v γ) ≡ fst (relAt k)
  step-rel h = cong fst (extensionalL {a = lookup v γ} {b = relAt k} pt)
    where
    fwd : (x : S) → ⟨ fst x ∈ fst (lookup v γ) ⟩ → ⟨ fst x ∈ fst (relAt k) ⟩
    fwd x hx = PT.rec (snd (fst x ∈ fst (relAt k))) (into (fst x))
```

<!--en-->
The truncation may be eliminated here because membership in `relAt k` is a proposition. No particular predecessor or pair witness is selected; only the fact that the original member belongs to the realized relation is retained.
<!--zh-->
这里可以消去命题截断，因为属于 `relAt k` 是一个命题。证明并不选择特定的前驱或有序对见证，只保留原成员属于已实现关系这一事实。
<!--ja-->
ここでは `relAt k` への所属が命題なので、命題的切り詰めを除去できる。特定の前者や順序対の証人を選ぶことはなく、もとの要素が実現された関係に属するという事実だけを保つ。
<!--/-->

```agda
      (RelStep-out v b f γ ob h x hx)

```

<!--en-->
For the reverse membership implication, `relAt-out` gives a propositionally truncated `RelOf k` description of the member. The map `from` reconstructs a `StepOf` witness, and `RelStep-back` then places the member in the set satisfying the step formula.
<!--zh-->
对于反向的隶属蕴涵，`relAt-out` 给出该成员的命题截断的 `RelOf k` 描述。映射 `from` 据此重建 `StepOf` 见证，随后 `RelStep-back` 把该成员放入满足步进公式的集合。
<!--ja-->
逆向きの所属の含意では、`relAt-out` がその要素について命題的に切り詰められた `RelOf k` の記述を与える。写像 `from` がそこから `StepOf` の証人を復元し、`RelStep-back` がその要素をステップ論理式を満たす集合へ入れる。
<!--/-->

```agda
    bwd : (x : S) → ⟨ fst x ∈ fst (relAt k) ⟩ → ⟨ fst x ∈ fst (lookup v γ) ⟩
    bwd x hx = PT.rec (snd (fst x ∈ fst (lookup v γ)))
      (λ ro → RelStep-back v b f γ ob h x (from (fst x) ro))
      (relAt-out k (fst x) hx)

```

<!--en-->
For each constructible element, the two implications give an equivalence between its two membership propositions. Propositional extensionality turns that equivalence into a path, and set extensionality assembles the pointwise paths into the required equality of underlying sets.
<!--zh-->
对于每个可构造元素，两个蕴涵给出两项隶属命题之间的等价。命题外延性把该等价化为路径，集合外延性再把这些逐点路径装配成所需的底层集合等式。
<!--ja-->
各構成可能な要素について、二つの含意は二つの所属命題の間の同値を与える。命題外延性がその同値をパスに変え、集合の外延性が各点のパスを必要な台集合の等式にまとめる。
<!--/-->

```agda
    pt : (x : S) → (fst x ∈ fst (lookup v γ)) ≡ (fst x ∈ fst (relAt k))
    pt x = ⇔toPath (fwd x) (bwd x)

```

<!--en-->
The converse lemma `rel-step` starts from an equality between the proposed value and `relAt k` and proves the step formula. The introduction rule asks for both membership directions. For the first, `toStep` will associate a propositionally truncated semantic step with every member of the proposed value.
<!--zh-->
反向引理 `rel-step` 从候选取值与 `relAt k` 的等式出发，证明步进公式。引入规则要求给出两个隶属方向；在第一个方向中，`toStep` 要为候选取值的每个成员配上一个命题截断的语义步进。
<!--ja-->
逆向きの補題 `rel-step` は、候補となる値と `relAt k` の等式から出発してステップ論理式を示す。導入規則には所属の二方向が必要である。第一の方向では、`toStep` が候補の値の各要素に、命題的に切り詰められた意味論的ステップを対応させる。
<!--/-->

```agda
  rel-step : fst (lookup v γ) ≡ fst (relAt k) → ⟨ γ ⊨ RelStepAt v b f ⟩
  rel-step q = RelStep-in v b f γ ob toStep backStep
    where
    toStep : (w : S) → ⟨ fst w ∈ fst (lookup v γ) ⟩ → ∥ StepOf b f γ (fst w) ∥₁
    toStep w hw = PT.map (from (fst w))
```

<!--en-->
The equality first transports a candidate member into `relAt k`. The outward representation of `relAt k` supplies only a propositionally truncated `RelOf k` record, and `PT.map from` preserves that truncation while converting its possible inhabitants into step witnesses.
<!--zh-->
该等式先把候选成员运入 `relAt k`。`relAt k` 的向外表示只给出命题截断的 `RelOf k` 记录，而 `PT.map from` 在把其中可能的元素化为步进见证时保留这层命题截断。
<!--ja-->
この等式により、まず候補の要素を `relAt k` へ移す。`relAt k` の外向きの表現が与えるのは、命題的に切り詰められた `RelOf k` の記録だけであり、`PT.map from` はその切り詰めを保ったまま、あり得る要素をステップの証人へ変換する。
<!--/-->

```agda
      (relAt-out k (fst w) (subst (λ t → ⟨ fst w ∈ t ⟩) q hw))

```

<!--en-->
The second membership direction starts with an explicit `StepOf` witness. The map `into` proves membership in `relAt k`, and the inverse orientation of the assumed equality transports this membership back to the proposed value.
<!--zh-->
第二个隶属方向从显式的 `StepOf` 见证开始。映射 `into` 证明其属于 `relAt k`，再沿所设等式的反方向把这项隶属运回候选取值。
<!--ja-->
第二の所属の向きは、明示的な `StepOf` の証人から始まる。写像 `into` が `relAt k` への所属を示し、仮定した等式の逆向きに沿って、その所属を候補の値へ戻す。
<!--/-->

```agda
    backStep : (w : S) → StepOf b f γ (fst w) → ⟨ fst w ∈ fst (lookup v γ) ⟩
    backStep w st = subst (λ t → ⟨ fst w ∈ t ⟩) (sym q) (into (fst w) st)
```

<!--en-->
## Every value an approximation records
<!--zh-->
## 逼近所记录的每个取值
<!--ja-->
## 近似が記録するすべての値
<!--/-->

<!--en-->
The lemma `entryOf` turns value correctness into entry completeness. If `j < k`, the approximation has some value at `# j`; if every value recorded there equals `relAt j`, then the standard pair `(# j , relAt j)` itself belongs to the approximation.
<!--zh-->
引理 `entryOf` 把取值正确性化为表项完备性。若 `j < k`，逼近就在 `# j` 处有某个取值；若那里记录的每个取值都等于 `relAt j`，则标准对 `(# j , relAt j)` 本身属于该逼近。
<!--ja-->
補題 `entryOf` は、値の正しさを項目の完全性へ変える。`j < k` なら近似は `# j` で何らかの値をもち、そこに記録されたすべての値が `relAt j` に等しければ、標準的な対 `(# j , relAt j)` 自身が近似に属する。
<!--/-->

```agda
entryOf : ∀ {n} (f a : Fin n) (γ : S ^ n) (k : ℕ)
        → fst (lookup a γ) ≡ # k → ⟨ γ ⊨ ApproxAt f a ⟩
        → (j : ℕ) → j < k
        → ((u : S) → ⟨ pr (# j) (fst u) ∈ fst (lookup f γ) ⟩
           → fst u ≡ fst (relAt j))
```

<!--en-->
Domain completeness in `ApproxAt` supplies the existence of a value `u` at the numeral `# j`, under propositional truncation. Because the target is the proposition that the standard pair is a member, the proof may eliminate this truncation and use the assumed correctness of `u`.
<!--zh-->
`ApproxAt` 中的定义域完备性在命题截断下给出数码 `# j` 处某个取值 `u` 的存在性。由于目标是标准对属于逼近这一命题，证明可以消去该命题截断，并使用所设的 `u` 的正确性。
<!--ja-->
`ApproxAt` の定義域の完全性は、命題的切り詰めのもとで、数項 `# j` におけるある値 `u` の存在を与える。目標は標準的な対が近似に属するという命題なので、この切り詰めを除去して、仮定した `u` の正しさを利用できる。
<!--/-->

```agda
        → ⟨ pr (# j) (fst (relAt j)) ∈ fst (lookup f γ) ⟩
entryOf f a γ k qa h j hj vs =
  PT.rec (snd (pr (# j) (fst (relAt j)) ∈ fst (lookup f γ))) named
    (ApproxAt-value f a γ h (numS j)
      (subst (λ t → ⟨ fst (numS j) ∈ t ⟩) (sym qa)
```

<!--en-->
The domain argument is justified by `j < k`: numeral monotonicity gives `# j ∈ # k`, and the equations for `numS j` and the bound put that membership into the form expected by `ApproxAt-value`. The result asserts that some recorded value exists under propositional truncation; it does not choose a particular value.
<!--zh-->
定义域论证来自 `j < k`：数码的单调性给出 `# j ∈ # k`，关于 `numS j` 与界的等式再把这项隶属化为 `ApproxAt-value` 所需的形式。所得结论只在命题截断下断言某个记录取值存在，并不选定一个具体取值。
<!--ja-->
定義域についての論証は `j < k` に基づく。数項の単調性から `# j ∈ # k` が得られ、`numS j` と上界の等式によって、その所属を `ApproxAt-value` が要求する形へ移す。結論は、命題的切り詰めのもとで何らかの記録値が存在すると述べるだけであり、特定の値を選ばない。
<!--/-->

```agda
        (subst (λ t → ⟨ t ∈ # k ⟩) (sym (numS-fst j)) (#mono j k hj))))
  where
  named : Σ[ u ∈ S ] ⟨ pr (fst (numS j)) (fst u) ∈ fst (lookup f γ) ⟩
        → ⟨ pr (# j) (fst (relAt j)) ∈ fst (lookup f γ) ⟩
  named (u , p) =
```

<!--en-->
Within such a value branch, the numeral equation first normalizes the recorded pair to the form `(# j , u)`. The correctness hypothesis gives `fst u ≡ fst (relAt j)`, and substitution in the second coordinate converts the recorded membership into membership of the standard pair.
<!--zh-->
在这样的取值分支中，数码等式先把记录的对规范为 `(# j , u)`。正确性假设给出 `fst u ≡ fst (relAt j)`，再在第二分量中作替换，就把原表项的隶属化为标准对的隶属。
<!--ja-->
そのような値の分岐では、数項の等式により、記録された対をまず `(# j , u)` の形に整える。正しさの仮定から `fst u ≡ fst (relAt j)` が得られ、第二成分を置換することで、記録された所属を標準的な対の所属へ変換する。
<!--/-->

```agda
    subst (λ t → ⟨ pr (# j) t ∈ fst (lookup f γ) ⟩) (vs u p') p'
    where
    p' : ⟨ pr (# j) (fst u) ∈ fst (lookup f γ) ⟩
    p' = subst (λ t → ⟨ pr t (fst u) ∈ fst (lookup f γ) ⟩) (numS-fst j) p

```

<!--en-->
Fix an approximation whose bound is `# k`. The induction motive `Val m` says that, whenever `m < k`, every constructible value `w` recorded at the key `# m` has the same underlying set as `relAt m`.
<!--zh-->
固定一个界为 `# k` 的逼近。归纳动机 `Val m` 断言：只要 `m < k`，在键 `# m` 处记录的每个可构造取值 `w`，其底层集合都与 `relAt m` 相等。
<!--ja-->
上界が `# k` である近似を固定する。帰納の動機 `Val m` は、`m < k` なら、キー `# m` に記録されたすべての構成可能な値 `w` の台集合が `relAt m` に等しいと述べる。
<!--/-->

```agda
module _ {n : ℕ} (f a : Fin n) (γ : S ^ n) (k : ℕ)
         (qa : fst (lookup a γ) ≡ # k) (h : ⟨ γ ⊨ ApproxAt f a ⟩) where
  private
    Val : ℕ → Type (ℓ-suc ℓ)
    Val m = (m < k) → (w : S) → ⟨ pr (# m) (fst w) ∈ fst (lookup f γ) ⟩
```

<!--en-->
The motive quantifies over every possible recorded value rather than choosing one. Its conclusion is equality of the two underlying sets, which is exactly the form needed both to rewrite table entries and to prove that the approximation is single-valued.
<!--zh-->
这个动机量化所有可能的记录取值，而不选择其中一个。其结论是两个底层集合相等；这种形式既能用来改写表项，也能推出逼近的取值唯一性。
<!--ja-->
この動機は一つの値を選ぶのではなく、記録され得るすべての値を量化する。その結論は二つの台集合の等式であり、表の項目を書き換えるためにも、近似の値の一意性を示すためにも、ちょうど必要な形である。
<!--/-->

```agda
          → fst w ≡ fst (relAt m)

```

<!--en-->
Correctness is proved by well-founded induction on the strict order of natural numbers. To identify a value at `m`, the induction hypothesis provides correctness at every `j < m`; the proof then applies `step-rel` to the proposed value `w` in an environment extended by `w` and the numeral for `m`. This is well-foundedness of natural-number `<`, not well-foundedness of `before`.
<!--zh-->
正确性通过自然数严格序上的良基归纳来证明。为了识别 `m` 处的取值，归纳假设先给出每个 `j < m` 处的正确性；随后，证明在加入 `w` 与表示 `m` 的数码所得的环境中，对候选取值 `w` 应用 `step-rel`。这里使用的是自然数 `<` 的良基性，而不是 `before` 的良基性。
<!--ja-->
正しさは、自然数の狭義順序に関する整礎帰納法で示す。`m` における値を同一視するため、帰納仮定からすべての `j < m` における正しさを得て、`w` と `m` を表す数項で拡張した環境において候補の値 `w` に `step-rel` を適用する。ここで使うのは自然数の `<` の整礎性であり、`before` の整礎性ではない。
<!--/-->

```agda
  approx-val : (m : ℕ) → Val m
  approx-val = WFI.induction <-wellfounded go
    where
    go : (m : ℕ) → ((j : ℕ) → j < m → Val j) → Val m
    go m IH hm w hw = step-rel zero (suc zero) (sh2 f) (w ∷ numS m ∷ γ) m
```

<!--en-->
The hypothesis that `(# m , w)` is recorded lets `ApproxAt-step` expose the step formula satisfied by `w`. To identify that step with `relAt m`, `step-rel` also receives two facts about all smaller indices: recorded values are correct, and every standard entry is present.
<!--zh-->
`(# m , w)` 已被记录这一假设使 `ApproxAt-step` 给出 `w` 所满足的步进公式。为了用 `step-rel` 把这一步认同为 `relAt m`，还需提供关于所有更小索引的两项事实：记录的取值是正确的，并且每个标准表项都存在。
<!--ja-->
`(# m , w)` が記録されているという仮定から、`ApproxAt-step` は `w` が満たすステップ論理式を与える。このステップを `step-rel` によって `relAt m` と同一視するには、さらに小さいすべての添字について、記録値が正しいことと、各標準項目が存在することの二つを渡す。
<!--/-->

```agda
      (numS-fst m) vals ents
      (ApproxAt-step f a γ h (numS m) w
        (subst (λ t → ⟨ pr t (fst w) ∈ fst (lookup f γ) ⟩)
          (sym (numS-fst m)) hw))
      where
```

<!--en-->
For `j < m`, correctness is precisely the induction hypothesis at `j`. Its own bound requirement `j < k` follows by composing `j < m` with the standing assumption `m < k`.
<!--zh-->
对于 `j < m`，正确性正是索引 `j` 处的归纳假设。该假设自身所需的界 `j < k`，由 `j < m` 与当前的 `m < k` 传递得到。
<!--ja-->
`j < m` に対する正しさは、ちょうど添字 `j` における帰納仮定である。その適用に必要な `j < k` は、`j < m` と現在の仮定 `m < k` の推移性から得られる。
<!--/-->

```agda
      vals : Values (lookup (sh2 f) (w ∷ numS m ∷ γ)) m
      vals j hj u hu = IH j hj (<-trans hj hm) u hu

```

<!--en-->
Completeness below `m` follows from `entryOf`. For each `j < m`, transitivity again gives `j < k`, while the induction hypothesis supplies the premise that every value recorded at `j` equals `relAt j`; hence the standard entry at `j` is present.
<!--zh-->
`m` 以下的完备性由 `entryOf` 得到。对于每个 `j < m`，传递性再次给出 `j < k`，归纳假设则提供「在 `j` 处记录的每个取值都等于 `relAt j`」这一前提；因此索引 `j` 处的标准表项确实存在。
<!--ja-->
`m` より下での完全性は `entryOf` から得られる。各 `j < m` について、推移性から再び `j < k` が得られ、帰納仮定は `j` に記録されたすべての値が `relAt j` に等しいという前提を与える。したがって添字 `j` の標準項目が存在する。
<!--/-->

```agda
      ents : Entries (lookup (sh2 f) (w ∷ numS m ∷ γ)) m
      ents j hj = entryOf f a γ k qa h j (<-trans hj hm)
        (λ u p → IH j hj (<-trans hj hm) u p)

```

<!--en-->
Once correctness has been proved at every bounded index, `entryOf` immediately yields completeness of the approximation. Thus `approx-ent` states that each `m < k` contributes the standard pair `(# m , relAt m)` to the recorded table.
<!--zh-->
一旦证明了每个有界索引处的正确性，`entryOf` 就立即给出逼近的完备性。因此，`approx-ent` 断言每个 `m < k` 都使标准对 `(# m , relAt m)` 出现在记录表中。
<!--ja-->
上界内のすべての添字で正しさが示されれば、`entryOf` から直ちに近似の完全性が得られる。したがって `approx-ent` は、各 `m < k` について標準的な対 `(# m , relAt m)` が記録表に含まれることを述べる。
<!--/-->

```agda
  approx-ent : (m : ℕ) → m < k
             → ⟨ pr (# m) (fst (relAt m)) ∈ fst (lookup f γ) ⟩
  approx-ent m hm = entryOf f a γ k qa h m hm (approx-val m hm)

```

<!--en-->
The graph formula hides, under propositional truncation, an approximation up to `k` together with a final step. The lemma `rel-only` eliminates that truncation into an equality of sets, which is a proposition, and asserts that the value stored in `v` must be `relAt k`.
<!--zh-->
图公式在命题截断下隐藏了一个截至 `k` 的逼近及其最后一步。引理 `rel-only` 把该命题截断消去到集合等式这一命题中，并断言 `v` 中保存的取值必为 `relAt k`。
<!--ja-->
グラフ論理式は、`k` までの近似と最後のステップを命題的切り詰めのもとに隠している。補題 `rel-only` は、その切り詰めを命題である集合の等式へ除去し、`v` に保存された値が `relAt k` でなければならないことを述べる。
<!--/-->

```agda
module _ {n : ℕ} (v b : Fin n) (γ : S ^ n) (k : ℕ)
         (qb : fst (lookup b γ) ≡ # k) where
  rel-only : ⟨ γ ⊨ RelGraphAt v b ⟩ → fst (lookup v γ) ≡ fst (relAt k)
  rel-only h = PT.rec (setIsSet (fst (lookup v γ)) (fst (relAt k))) read
    (RelGraph-out v b γ h)
```

<!--en-->
In any represented branch, the graph supplies an approximation `g`, a proof that `g` satisfies `ApproxAt`, and a proof of the step at `k`. The preceding well-founded induction identifies every value recorded by `g` below `k`; `step-rel` then identifies the final value with `relAt k`.
<!--zh-->
在任一被表示的分支中，图给出逼近 `g`、`g` 满足 `ApproxAt` 的证明，以及索引 `k` 处步进成立的证明。前述良基归纳识别 `g` 在 `k` 以下记录的每个取值；`step-rel` 随即把最后的取值认同为 `relAt k`。
<!--ja-->
表された各分岐で、グラフは近似 `g`、`g` が `ApproxAt` を満たす証明、そして添字 `k` におけるステップの証明を与える。先の整礎帰納法が `g` によって `k` より下に記録されたすべての値を同一視し、続いて `step-rel` が最後の値を `relAt k` と同一視する。
<!--/-->

```agda
    where
    read : GraphOf v b γ → fst (lookup v γ) ≡ fst (relAt k)
    read (g , (ha , hs)) =
      step-rel (suc v) (suc b) zero (g ∷ γ) k qb
        (λ m hm w hw → approx-val zero (suc b) (g ∷ γ) k qb ha m hm w hw)
```

<!--en-->
The other input to `step-rel` is completeness of that same approximation below `k`. It is supplied by `approx-ent`, which uses the value theorem to replace each merely existing entry by the corresponding standard entry.
<!--zh-->
`step-rel` 的另一个输入是同一个逼近在 `k` 以下的完备性。该输入由 `approx-ent` 提供；后者使用取值定理，把每个仅知存在的表项替换为相应的标准表项。
<!--ja-->
`step-rel` へのもう一つの入力は、同じ近似が `k` より下で完全であることである。これは `approx-ent` から得られ、値についての定理を用いて、存在だけが知られている各項目を対応する標準項目へ置き換える。
<!--/-->

```agda
        (λ m hm → approx-ent zero (suc b) (g ∷ γ) k qb ha m hm)
        hs
```

<!--en-->
## The approximation, exhibited
<!--zh-->
## 那个逼近的显式构造
<!--ja-->
## 近似を具体的に構成する
<!--/-->

<!--en-->
To prepare the finite family used below for collection by `finSet`, first place all its members in a common constructible stage. More generally, `smallStage` applies ordinal bounding to the individual stages of any small family `g : X → S` and returns an ordinal `σ` such that every `fst (g x)` belongs to `Lset σ`.
<!--zh-->
为了用 `finSet` 收集下文的有限族，先要把它的所有成员放入同一个可构造层。更一般地，`smallStage` 对任意小族 `g : X → S` 的各个所在层作序数界定，得到序数 `σ`，使每个 `fst (g x)` 都属于 `Lset σ`。
<!--ja-->
以下で使う有限族を `finSet` で集めるには、まずその全要素を共通の構成可能段階に置きます。より一般に、`smallStage` は任意の小さな族 `g : X → S` の各要素が属する段階に順序数の上界を取り、すべての `fst (g x)` が `Lset σ` に属するような順序数 `σ` を返します。
<!--/-->

```agda
smallStage : (X : Type ℓ) (g : X → S)
           → Σ[ σ ∈ V ℓ ] (IsOrd σ × ((x : X) → ⟨ fst (g x) ∈ Lset σ ⟩))
smallStage X g = bd .fst , (bd .snd .fst , mem)
  where
  bd = boundingOrd X (λ x → stage (fst (g x)) (g x .snd))
```

<!--en-->
Each `g x` already belongs to the constructible stage at which it is born. The bounding ordinal lies above every such birth stage, so monotonicity of `Lset` transports each membership into the common stage `Lset σ`.
<!--zh-->
每个 `g x` 已经属于其诞生层。所取的界序数位于每个诞生层之上，因此 `Lset` 的单调性把每项隶属关系运入公共层 `Lset σ`。
<!--ja-->
各 `g x` はすでに自身の生成段階に属している。上界となる順序数はそれらすべての生成段階より上にあるので、`Lset` の単調性によって各所属を共通の段階 `Lset σ` へ移せる。
<!--/-->

```agda
         (λ x → stage-ord (fst (g x)) (g x .snd))
  mem : (x : X) → ⟨ fst (g x) ∈ Lset (bd .fst) ⟩
  mem x = Lset-mono {α = bd .fst} {β = stage (fst (g x)) (g x .snd)}
    (bd .snd .snd x) (stage-mem (fst (g x)) (g x .snd))

```

<!--en-->
For a fixed bound `k`, the finite index type `Fin k` enumerates exactly the smaller natural numbers. The family `famOf k` assigns to `i` the constructible ordered pair whose coordinates are the numeral `# (toℕ i)` and the realized relation `relAt (toℕ i)`.
<!--zh-->
固定界 `k` 后，有限索引类型 `Fin k` 恰好枚举比 `k` 小的自然数。族 `famOf k` 把索引 `i` 映到一个可构造有序对，其两分量分别是数码 `# (toℕ i)` 与已实现关系 `relAt (toℕ i)`。
<!--ja-->
上界 `k` を固定すると、有限添字型 `Fin k` は `k` より小さい自然数をちょうど列挙する。族 `famOf k` は添字 `i` に、数項 `# (toℕ i)` と実現された関係 `relAt (toℕ i)` を二成分とする構成可能な順序対を対応させる。
<!--/-->

```agda
private
  famOf : (k : ℕ) → Fin k → S
  famOf k i = prS (numS (toℕ i)) (relAt (toℕ i))

```

<!--en-->
The lifted copy of `Fin k` places this finite index type in the universe expected by `smallStage`. Applying the common-stage lemma to `famOf k` gives one ordinal stage containing every pair, which supplies the constructibility premise later required by `finSetL`.
<!--zh-->
提升后的 `Fin k` 把这个有限索引类型置于 `smallStage` 所需的宇宙中。对 `famOf k` 应用公共层引理，得到包含所有有序对的单个序数层；这正提供了稍后 `finSetL` 所需的可构造性前提。
<!--ja-->
持ち上げた `Fin k` により、この有限添字型を `smallStage` が要求する宇宙に置く。`famOf k` に共通段階の補題を適用すると、すべての順序対を含む一つの順序数段階が得られ、後で `finSetL` が必要とする構成可能性の前提が満たされる。
<!--/-->

```agda
  famBnd : (k : ℕ) → Σ[ σ ∈ V ℓ ] (IsOrd σ
         × ((i : Lift {ℓ-zero} {ℓ} (Fin k)) → ⟨ fst (famOf k (lower i)) ∈ Lset σ ⟩))
  famBnd k = smallStage (Lift {ℓ-zero} {ℓ} (Fin k)) (λ i → famOf k (lower i))

```

<!--en-->
The underlying set of `famOf k i` is the whole ordered pair, not merely its first coordinate. The equation `famEq` unfolds the constructible pairing and the numeral representation to identify it with `pr (# (toℕ i)) (fst (relAt (toℕ i)))`.
<!--zh-->
`famOf k i` 的底层集合是整个有序对，而不只是它的第一分量。等式 `famEq` 展开可构造配对与数码表示，把它认同为 `pr (# (toℕ i)) (fst (relAt (toℕ i)))`。
<!--ja-->
`famOf k i` の台集合は順序対全体であり、その第一成分だけではない。等式 `famEq` は構成可能な対と数項の表現を展開し、それを `pr (# (toℕ i)) (fst (relAt (toℕ i)))` と同一視する。
<!--/-->

```agda
  famEq : (k : ℕ) (i : Fin k)
        → fst (famOf k i) ≡ pr (# (toℕ i)) (fst (relAt (toℕ i)))
  famEq k i = prS-fst (numS (toℕ i)) (relAt (toℕ i))
            ∙ cong (λ t → pr t (fst (relAt (toℕ i)))) (numS-fst (toℕ i))

```

<!--en-->
The approximation `approxSet k` is built by `finSet`, which collects the `Fin k` indexed family of underlying pairs into a finite set. The proof `finSetL` uses their common stage to show that this finite set is an element of `L`. No instance of Replacement is used in this construction.
<!--zh-->
逼近 `approxSet k` 由 `finSet` 构造，它把以 `Fin k` 为索引的底层有序对族收成一个有限集。证明 `finSetL` 利用这些有序对所在的公共层，说明该有限集是 `L` 的元素。这个构造不使用替换公理。
<!--ja-->
近似 `approxSet k` は `finSet` によって構成され、`Fin k` で添字づけられた台の順序対の族を有限集合に集める。証明 `finSetL` はそれらの共通段階を用いて、この有限集合が `L` の要素であることを示す。この構成では置換公理を用いない。
<!--/-->

```agda
opaque
  approxSet : ℕ → S
  approxSet k = finSet k (λ i → fst (famOf k i))
    , FinOf.finSetL (famBnd k .fst) (famBnd k .snd .fst) k
        (λ i → fst (famOf k i)) (λ i → famBnd k .snd .snd (lift i))
```

<!--en-->
The projection equation exposes the underlying set of `approxSet k` as exactly that `finSet`. Subsequent membership lemmas can therefore use the introduction and elimination rules for finite sets to show that its entries are precisely the pairs `(# j , relAt j)` with `j < k`.
<!--zh-->
投影等式表明，`approxSet k` 的底层集合恰好就是这个 `finSet`。因此，后续成员引理可以使用有限集的引入与消去规则，证明其表项恰为满足 `j < k` 的各对 `(# j , relAt j)`。
<!--ja-->
射影の等式により、`approxSet k` の台集合がまさにこの `finSet` であることが分かる。したがって後続の所属補題では、有限集合の導入規則と除去規則を用いて、その項目がちょうど `j < k` を満たす対 `(# j , relAt j)` であることを示せる。
<!--/-->

```agda

  approxSet-fst : (k : ℕ) → fst (approxSet k) ≡ finSet k (λ i → fst (famOf k i))
  approxSet-fst k = refl

```

<!--en-->
The finite approximation contains every intended entry: if `j < k`, then the ordered pair of `# j` and `relAt j` belongs to `approxSet k`. This is a property of the finite-set construction of `approxSet`, not an application of replacement.
<!--zh-->
有限逼近包含每个预期条目：若 `j < k`，则 `# j` 与 `relAt j` 的有序对属于 `approxSet k`。这是 `approxSet` 的有限集构造所具有的性质，并未使用替换。
<!--ja-->
有限近似は意図された各項目を含む。`j < k` ならば、`# j` と `relAt j` の順序対は `approxSet k` に属する。これは `approxSet` の有限集合構成がもつ性質であり、置換を用いたものではない。
<!--/-->

```agda
approx-mem-in : (k j : ℕ) → j < k
              → ⟨ pr (# j) (fst (relAt j)) ∈ fst (approxSet k) ⟩
approx-mem-in k j hj =
  subst (λ t → ⟨ t ∈ fst (approxSet k) ⟩)
    (cong (λ i → pr (# i) (fst (relAt i))) (toℕ∘enum j hj))
```

<!--en-->
The inequality supplies `enum j hj : Fin k`. The equation `famEq` identifies the corresponding member of the finite family with the desired ordered pair, and `finSet-in` inserts it into the set built by `finSet` and certified in `L` by `finSetL`.
<!--zh-->
不等式给出 `enum j hj : Fin k`。等式 `famEq` 把有限族中相应的成员认同为所需的有序对，`finSet-in` 再把它写入由 `finSet` 构造并由 `finSetL` 证明属于 `L` 的集合。
<!--ja-->
不等式から `enum j hj : Fin k` が得られる。等式 `famEq` は有限族の対応する要素を求める順序対と同一視し、`finSet-in` はそれを `finSet` で構成され `finSetL` により `L` に属すると保証された集合へ書き込む。
<!--/-->

```agda
    (subst (λ t → ⟨ pr (# (toℕ (enum j hj))) (fst (relAt (toℕ (enum j hj)))) ∈ t ⟩)
      (sym (approxSet-fst k))
      (finSet-in k (λ i → fst (famOf k i))
        (pr (# (toℕ (enum j hj))) (fst (relAt (toℕ (enum j hj)))))
        ∣ enum j hj , famEq k (enum j hj) ∣₁))
```

<!--en-->
Conversely, membership in `approxSet k` yields only a propositionally truncated assertion that the member is an intended entry indexed by some `j < k`. Thus the lemma describes exactly which pairs occur without choosing a canonical index witness.
<!--zh-->
反过来，属于 `approxSet k` 只给出一个经过命题截断的断言：该成员是由某个 `j < k` 索引的预期条目。因此，这条引理精确刻画了其中出现的有序对，却不选择规范的索引见证。
<!--ja-->
逆に、`approxSet k` への所属から得られるのは、その要素がある `j < k` で添字付けられた意図どおりの項目であるという命題的切り詰めだけである。したがって、この補題は現れる順序対を正確に記述するが、標準的な添字の証人を選ぶものではない。
<!--/-->

```agda

approx-mem-out : (k : ℕ) (y : V ℓ) → ⟨ y ∈ fst (approxSet k) ⟩
               → ∥ Σ[ j ∈ ℕ ] ((j < k) × (y ≡ pr (# j) (fst (relAt j)))) ∥₁
approx-mem-out k y h = PT.map named
  (finSet-out k (λ i → fst (famOf k i)) y
    (subst (λ t → ⟨ y ∈ t ⟩) (approxSet-fst k) h))
```

<!--en-->
An enumerated index `i : Fin k` is sent to the natural number `toℕ i`, together with `toℕ<n i`. Reversing the membership equation and composing it with `famEq` gives the required equality from the original member to the standard pair.
<!--zh-->
枚举索引 `i : Fin k` 被送到自然数 `toℕ i`，并同时带有 `toℕ<n i`。把成员等式反向后与 `famEq` 复合，便得到从原成员到标准有序对的所需等式。
<!--ja-->
列挙された添字 `i : Fin k` を自然数 `toℕ i` に移し、同時に `toℕ<n i` を得る。所属から得た等式を逆向きにして `famEq` と合成すると、元の要素から標準的な順序対への必要な等式が得られる。
<!--/-->

```agda
  where
  named : Σ[ i ∈ Fin k ] (fst (famOf k i) ≡ y)
        → Σ[ j ∈ ℕ ] ((j < k) × (y ≡ pr (# j) (fst (relAt j))))
  named (i , q) = toℕ i , (toℕ<n i , (sym q ∙ famEq k i))
approxVals : (k : ℕ) → Values (approxSet k) k
```

<!--en-->
This membership description proves value correctness. If an entry with first component `# m` occurs below `k`, then its second component is the underlying set of `relAt m`; the propositionally truncated index may be eliminated because equality between sets in `V` is itself a proposition.
<!--zh-->
上述成员刻画给出取值正确性。若首分量为 `# m` 的条目出现在 `k` 以下，则其第二分量就是 `relAt m` 的底层集合；由于 `V` 中集合之间的相等本身是命题，可以消去索引外层的命题截断。
<!--ja-->
この所属の記述から値の正しさが従う。第一成分が `# m` の項目が `k` より下に現れるなら、その第二成分は `relAt m` の台となる集合である。`V` の集合どうしの等しさは命題なので、添字を包む命題的切り詰めを除去できる。
<!--/-->

```agda
approxVals k m hm u hu = PT.rec (setIsSet (fst u) (fst (relAt m))) named
  (approx-mem-out k (pr (# m) (fst u)) hu)
  where
  named : Σ[ j ∈ ℕ ] ((j < k) × (pr (# m) (fst u) ≡ pr (# j) (fst (relAt j))))
        → fst u ≡ fst (relAt m)
```

<!--en-->
Injectivity of ordered pairing separates the equality into its two components. Injectivity of numerals then identifies the recovered index with `m`, so the second-component equality can be transported from `relAt j` to `relAt m`.
<!--zh-->
有序对的单射性把等式分成两个分量。数码的单射性继而把恢复出的索引认同为 `m`，于是第二分量的等式可从 `relAt j` 搬运到 `relAt m`。
<!--ja-->
順序対の単射性は等式を二つの成分に分ける。さらに数項の単射性が復元された添字を `m` と同一視するので、第二成分の等式を `relAt j` から `relAt m` へ移せる。
<!--/-->

```agda
  named (j , (hj , q)) = pr-inj q .snd
    ∙ cong (λ i → fst (relAt i)) (sym (#-inj′ (pr-inj q .fst)))

```

<!--en-->
The complementary property is entry completeness: for every `m < k`, the standard pair `(# m, relAt m)` is present. It follows immediately from the finite-set membership lemma above.
<!--zh-->
与取值正确性相配的是条目完备性：对每个 `m < k`，标准有序对 `(# m, relAt m)` 都在表中。这直接来自上面的有限集成员引理。
<!--ja-->
値の正しさと対になるのが項目の完全性である。各 `m < k` について、標準的な順序対 `(# m, relAt m)` が表に含まれる。これは上の有限集合の所属補題から直ちに従う。
<!--/-->

```agda
approxEnts : (k : ℕ) → Entries (approxSet k) k
approxEnts k m hm = approx-mem-in k m hm

```

<!--en-->
Fix an environment in which `f` denotes `approxSet k` and `a` denotes the numeral `# k`. The remaining task is to verify that this concrete finite table satisfies the abstract approximation formula.
<!--zh-->
固定一个环境，其中 `f` 表示 `approxSet k`，`a` 表示数码 `# k`。余下的任务是验证这张具体的有限表满足抽象的逼近公式。
<!--ja-->
`f` が `approxSet k` を、`a` が数項 `# k` を表す環境を固定する。残る課題は、この具体的な有限表が抽象的な近似の論理式を満たすことの確認である。
<!--/-->

```agda
module _ (k : ℕ) {n : ℕ} (f a : Fin n) (γ : S ^ n)
         (qf : fst (lookup f γ) ≡ fst (approxSet k))
         (qa : fst (lookup a γ) ≡ # k) where
  private
    onDom : (x : S)
```

<!--en-->
The domain condition has two directions. A first component occurring in the table must belong to `# k`, and every member of `# k` must occur as the first component of some table entry. The existential assertion about a second component is interpreted with propositional truncation.
<!--zh-->
定义域条件包含两个方向。表中出现的首分量必须属于 `# k`，而 `# k` 的每个成员都必须作为某个表条目的首分量出现。关于第二分量的存在断言按命题截断解释。
<!--ja-->
定義域の条件には二つの向きがある。表に現れる第一成分は `# k` に属さなければならず、`# k` の各要素は何らかの表項目の第一成分として現れなければならない。第二成分についての存在主張は命題的切り詰めとして解釈される。
<!--/-->

```agda
          → (⟨ ∃[ y ∶ S ] pr (fst x) (fst y) ∈ fst (lookup f γ) ⟩
             → ⟨ fst x ∈ fst (lookup a γ) ⟩)
          × (⟨ fst x ∈ fst (lookup a γ) ⟩
             → ⟨ ∃[ y ∶ S ] pr (fst x) (fst y) ∈ fst (lookup f γ) ⟩)
    onDom x = fwd , bwd
```

<!--en-->
For the first direction, assume merely that some second component forms an entry with `x`. Since the target membership `x ∈ # k` is a proposition, the existential witness may be eliminated before the pair is analyzed through `approx-mem-out`.
<!--zh-->
先看第一个方向，只假设某个第二分量与 `x` 组成了表中条目。目标 `x ∈ # k` 是命题，因此可以先消去存在见证的命题截断，再用 `approx-mem-out` 分析该有序对。
<!--ja-->
第一の向きでは、ある第二成分が `x` とともに表の項目をなすことだけを仮定する。目標の `x ∈ # k` は命題なので、存在証人の命題的切り詰めを除去してから、`approx-mem-out` でその順序対を調べられる。
<!--/-->

```agda
      where
      fwd : ⟨ ∃[ y ∶ S ] pr (fst x) (fst y) ∈ fst (lookup f γ) ⟩
          → ⟨ fst x ∈ fst (lookup a γ) ⟩
      fwd = PT.rec (snd (fst x ∈ fst (lookup a γ))) atY
        where
```

<!--en-->
After transporting the entry into `approxSet k`, `approx-mem-out` produces a propositionally truncated `j < k` and an equality with the standard pair at `j`. Elimination is again valid because the desired membership in the index is a proposition.
<!--zh-->
把该条目搬运到 `approxSet k` 后，`approx-mem-out` 给出经过命题截断的 `j < k`，以及该条目与第 `j` 个标准有序对的等式。所求的索引成员关系是命题，故这里同样可以消去命题截断。
<!--ja-->
その項目を `approxSet k` へ移すと、`approx-mem-out` から命題的切り詰められた `j < k` と、第 `j` の標準的な順序対との等式が得られる。求める添字への所属は命題なので、ここでも命題的切り詰めを除去できる。
<!--/-->

```agda
        atY : Σ[ y ∈ S ] ⟨ pr (fst x) (fst y) ∈ fst (lookup f γ) ⟩
            → ⟨ fst x ∈ fst (lookup a γ) ⟩
        atY (y , p) = PT.rec (snd (fst x ∈ fst (lookup a γ))) named
          (approx-mem-out k (pr (fst x) (fst y))
            (subst (λ t → ⟨ pr (fst x) (fst y) ∈ t ⟩) qf p))
```

<!--en-->
The first-component equality says that the underlying set of `x` is `# j`. The equality interpreting `a` as `# k` reduces the goal to proving that this set belongs to `# k`.
<!--zh-->
首分量等式表明 `x` 的底层集合是 `# j`。再用把 `a` 解释为 `# k` 的等式，目标便化为证明这个集合属于 `# k`。
<!--ja-->
第一成分の等式は、`x` の台となる集合が `# j` であることを述べる。`a` を `# k` と解釈する等式を用いると、目標はこの集合が `# k` に属することへ帰着する。
<!--/-->

```agda
          where
          named : Σ[ j ∈ ℕ ]
                    ((j < k) × (pr (fst x) (fst y) ≡ pr (# j) (fst (relAt j))))
                → ⟨ fst x ∈ fst (lookup a γ) ⟩
          named (j , (hj , q)) = subst (λ t → ⟨ fst x ∈ t ⟩) (sym qa)
```

<!--en-->
Numeral monotonicity turns `j < k` into `# j ∈ # k`. Transport along the first-component equality then proves that the original `x` lies in the required domain.
<!--zh-->
数码单调性把 `j < k` 化为 `# j ∈ # k`。随后沿首分量等式搬运，即可证明原来的 `x` 属于所需定义域。
<!--ja-->
数項の単調性により `j < k` から `# j ∈ # k` が得られる。第一成分の等式に沿って移せば、元の `x` が求める定義域に属することが従う。
<!--/-->

```agda
            (subst (λ t → ⟨ t ∈ # k ⟩) (sym (pr-inj q .fst)) (#mono j k hj))

```

<!--en-->
For the converse direction, membership in `# k` is decoded as a propositionally truncated natural number `j < k` whose numeral is the given element. Mapping this truncated datum will produce the required truncated table entry.
<!--zh-->
反向证明把 `# k` 中的成员关系解码为经过命题截断的自然数 `j < k`，其数码就是给定元素。对这份截断数据作映射，便会得到所需的截断表条目。
<!--ja-->
逆向きでは、`# k` への所属を、与えられた要素が数項となるような自然数 `j < k` の命題的切り詰めとして読み出す。この切り詰められたデータを写せば、必要な表項目の命題的切り詰めが得られる。
<!--/-->

```agda
      bwd : ⟨ fst x ∈ fst (lookup a γ) ⟩
          → ⟨ ∃[ y ∶ S ] pr (fst x) (fst y) ∈ fst (lookup f γ) ⟩
      bwd hx = PT.map named
        (∈#-elim k (fst x) (subst (λ t → ⟨ fst x ∈ t ⟩) qa hx))
        where
```

<!--en-->
For an explicit decoded `j`, choose `relAt j` as the second component. Entry completeness places `(# j, relAt j)` in `approxSet k`, and the equations for the table and for the given first component transport this membership back to the original environment.
<!--zh-->
对一个显式解码出的 `j`，取 `relAt j` 为第二分量。条目完备性把 `(# j, relAt j)` 放入 `approxSet k`，再沿有限表的解释等式和给定首分量的等式搬运，即得到原环境中的成员关系。
<!--ja-->
明示的に得られた `j` に対し、第二成分として `relAt j` を選ぶ。項目の完全性により `(# j, relAt j)` は `approxSet k` に入り、有限表の解釈を与える等式と第一成分の等式に沿って移すことで、元の環境での所属が得られる。
<!--/-->

```agda
        named : Σ[ j ∈ ℕ ] ((j < k) × (fst x ≡ # j))
              → Σ[ y ∈ S ] ⟨ pr (fst x) (fst y) ∈ fst (lookup f γ) ⟩
        named (j , (hj , q)) = relAt j
          , subst (λ t → ⟨ pr (fst x) (fst (relAt j)) ∈ t ⟩) (sym qf)
              (subst (λ t → ⟨ pr t (fst (relAt j)) ∈ fst (approxSet k) ⟩)
```

<!--en-->
The final transport replaces the decoded numeral `# j` by the original first component. Hence every element of the intended domain has an entry, completing the second half of the domain condition.
<!--zh-->
最后一次搬运把解码得到的数码 `# j` 换回原来的首分量。因此，预期定义域中的每个元素都有相应条目，定义域条件的后一半由此完成。
<!--ja-->
最後の移送で、読み出された数項 `# j` を元の第一成分へ戻す。これにより、意図された定義域の各要素に対応する項目が存在し、定義域条件の後半が完成する。
<!--/-->

```agda
                (sym q) (approx-mem-in k j hj))

```

<!--en-->
It remains to verify the pointwise recursion condition. Every pair occurring in the finite table must satisfy `RelStepAt`, so the second component is justified as the recursively determined relation value at the first component.
<!--zh-->
还需验证逐点递归条件。有限表中出现的每个有序对都必须满足 `RelStepAt`，从而说明其第二分量确实是由首分量处的递归所确定的关系值。
<!--ja-->
残るのは各点での再帰条件の確認である。有限表に現れる各順序対が `RelStepAt` を満たすことを示し、第二成分が第一成分における再帰で定まる関係の値であることを保証する。
<!--/-->

```agda
    onStep : (x y : S) → ⟨ pr (fst x) (fst y) ∈ fst (lookup f γ) ⟩
           → ⟨ (y ∷ x ∷ γ) ⊨ RelStepAt zero (suc zero) (sh2 f) ⟩
    onStep x y p = PT.rec (snd ((y ∷ x ∷ γ) ⊨ RelStepAt zero (suc zero) (sh2 f)))
      named
      (approx-mem-out k (pr (fst x) (fst y))
```

<!--en-->
Membership in the table is first transported to `approxSet k` and read by `approx-mem-out`. Its propositionally truncated standard form can be eliminated because satisfaction of `RelStepAt` is a proposition.
<!--zh-->
先把表中的成员关系搬运到 `approxSet k`，再由 `approx-mem-out` 读取。所得标准形式带有命题截断；由于满足 `RelStepAt` 是命题，可以消去这层截断。
<!--ja-->
まず表への所属を `approxSet k` へ移し、`approx-mem-out` で読み取る。得られる標準形は命題的切り詰められているが、`RelStepAt` の充足は命題なので、この切り詰めを除去できる。
<!--/-->

```agda
        (subst (λ t → ⟨ pr (fst x) (fst y) ∈ t ⟩) qf p))
      where
      named : Σ[ j ∈ ℕ ]
                ((j < k) × (pr (fst x) (fst y) ≡ pr (# j) (fst (relAt j))))
            → ⟨ (y ∷ x ∷ γ) ⊨ RelStepAt zero (suc zero) (sh2 f) ⟩
```

<!--en-->
For a recovered entry at `j`, `rel-step` reconstructs the recursion step. Its hypotheses for every `i < j` come from value correctness and entry completeness for `approxSet k`; transitivity of `<` turns `i < j < k` into the bounds those lemmas require.
<!--zh-->
对恢复出的第 `j` 个条目，`rel-step` 重建递归步。它对每个 `i < j` 所需的假设来自 `approxSet k` 的取值正确性与条目完备性；`<` 的传递性把 `i < j < k` 化为这些引理所需的界。
<!--ja-->
復元された第 `j` の項目について、`rel-step` が再帰の一歩を再構成する。各 `i < j` に必要な仮定は `approxSet k` の値の正しさと項目の完全性から得られ、`<` の推移性が `i < j < k` をそれらの補題に必要な境界へ変える。
<!--/-->

```agda
      named (j , (hj , q)) =
        rel-step zero (suc zero) (sh2 f) (y ∷ x ∷ γ) j (pr-inj q .fst)
          (λ i hi u hu → approxVals k i (<-trans hi hj) u
            (subst (λ t → ⟨ pr (# i) (fst u) ∈ t ⟩) qf hu))
          (λ i hi → subst (λ t → ⟨ pr (# i) (fst (relAt i)) ∈ t ⟩) (sym qf)
```

<!--en-->
The first component of the pair equality identifies the argument with `# j`, while its second component identifies the recorded value with `relAt j`. These are precisely the endpoint equalities required by `rel-step`.
<!--zh-->
有序对等式的首分量把实参认同为 `# j`，第二分量则把表中取值认同为 `relAt j`。这正是 `rel-step` 所需的两个端点等式。
<!--ja-->
順序対の等式の第一成分は引数を `# j` と同一視し、第二成分は表の値を `relAt j` と同一視する。これらがちょうど `rel-step` に必要な両端の等式である。
<!--/-->

```agda
            (approxEnts k i (<-trans hi hj)))
          (pr-inj q .snd)

```

<!--en-->
The concrete finite table now satisfies `ApproxAt`: `onDom` proves that its domain is exactly `# k`, and `onStep` proves the recursion condition at every recorded argument. This establishes an approximation without invoking replacement.
<!--zh-->
这张具体的有限表现已满足 `ApproxAt`：`onDom` 证明其定义域恰为 `# k`，`onStep` 证明每个已记录实参都满足递归条件。由此得到的逼近没有使用替换。
<!--ja-->
この具体的な有限表が `ApproxAt` を満たすことが分かった。`onDom` は定義域がちょうど `# k` であることを示し、`onStep` は記録された各引数で再帰条件を示す。この近似の構成には置換を用いていない。
<!--/-->

```agda
  approxSet-approx : ⟨ γ ⊨ ApproxAt f a ⟩
  approxSet-approx = ApproxAt-in f a γ (domAt-intro f a γ onDom) onStep

```

<!--en-->
Consequently, `relAt k` satisfies the recursion graph at the numeral `# k`, provided the environment components denoting the index and candidate value are identified with `# k` and `relAt k`. The finite witness for the existential approximation is `approxSet k`.
<!--zh-->
因此，只要环境中表示索引与候选值的分量分别被认同为 `# k` 与 `relAt k`，`relAt k` 就在数码 `# k` 处满足递归图。存在量化的逼近由有限集合 `approxSet k` 见证。
<!--ja-->
したがって、環境内で添字と候補値を表す成分がそれぞれ `# k` と `relAt k` に同一視されるなら、`relAt k` は数項 `# k` における再帰グラフを満たす。存在量化された近似の証人は有限集合 `approxSet k` である。
<!--/-->

```agda
relAt-graph : ∀ {n} (v b : Fin n) (γ : S ^ n) (k : ℕ)
            → fst (lookup b γ) ≡ # k → fst (lookup v γ) ≡ fst (relAt k)
            → ⟨ γ ⊨ RelGraphAt v b ⟩
relAt-graph v b γ k qb qv = RelGraph-in v b γ (approxSet k)
  (approxSet-approx k zero (suc b) (approxSet k ∷ γ) refl qb)
```

<!--en-->
The graph introduction combines two facts: `approxSet-approx` verifies all earlier arguments, and `rel-step` verifies the current value at `k` using `approxVals` and `approxEnts`. Thus the same finite table supplies exactly the prior information needed to certify `relAt k`.
<!--zh-->
图的引入合并了两个事实：`approxSet-approx` 验证所有较小实参，`rel-step` 则借助 `approxVals` 与 `approxEnts` 验证 `k` 处的当前取值。因此，同一张有限表恰好提供了认证 `relAt k` 所需的全部先前信息。
<!--ja-->
グラフの導入は二つの事実を組み合わせる。`approxSet-approx` がすべての小さい引数を検証し、`rel-step` が `approxVals` と `approxEnts` を用いて `k` における現在の値を検証する。このように、同じ有限表が `relAt k` の保証に必要な先行情報をちょうど与える。
<!--/-->

```agda
  (rel-step (suc v) (suc b) zero (approxSet k ∷ γ) k qb
    (approxVals k) (approxEnts k) qv)
```

<!--en-->
## The family, as an element of `L`
<!--zh-->
## 那一族，作为 `L` 的一个元素
<!--ja-->
## 順序族を `L` の要素にする
<!--/-->

<!--en-->
The finite relations have now been verified one stage at a time. The preceding uniqueness argument used well-founded induction on the natural-number order `<`; it neither establishes nor uses well-foundedness of `before`. The next construction uses replacement over the internal natural numbers to collect all pairs `(# k, relAt k)` into one constructible set graph.
<!--zh-->
至此，各个有限层关系已逐层得到验证。此前的唯一性论证使用自然数次序 `<` 上的良基归纳，既不建立也不使用 `before` 的良基性。下一项构造沿内部自然数使用替换，把所有 `(# k, relAt k)` 收集成一个属于 `L` 的集合图。
<!--ja-->
ここまでで、各有限段階の関係は段階ごとに検証された。先の一意性の議論で用いたのは自然数の順序 `<` に関する整礎帰納であり、`before` の整礎性を示したり用いたりしたわけではない。次は内部自然数上で置換を用い、すべての `(# k, relAt k)` を一つの `L` に属する集合グラフへ集める。
<!--/-->

```agda
private
```

<!--en-->
For any formula `φ` proved equal to the paired recursion graph, `famBuild` returns a constructible set `h` with two precise properties. Every standard pair belongs to `h`, and any member of `h` whose first component is known to be `# k` has second component equal to `relAt k`.
<!--zh-->
对任何已证明等于成对递归图的公式 `φ`，`famBuild` 都返回一个可构造集合 `h`，并带有两条精确性质。每个标准有序对都属于 `h`；而 `h` 中任何首分量已知为 `# k` 的成员，其第二分量都等于 `relAt k`。
<!--ja-->
対にした再帰グラフと等しいことが証明された任意の論理式 `φ` に対し、`famBuild` は二つの正確な性質をもつ構成可能集合 `h` を返す。各標準的な順序対は `h` に属し、第一成分が `# k` と分かっている `h` の任意の要素の第二成分は `relAt k` に等しい。
<!--/-->

```agda
  famBuild : (φ : Formula S 2) → φ ≡ PairRelGraphAt zero (suc zero)
           → Σ[ h ∈ S ]
               ( ((k : ℕ) → ⟨ pr (# k) (fst (relAt k)) ∈ fst h ⟩)
               × ((cS rS : S) (k : ℕ) → fst cS ≡ # k
                  → ⟨ pr (fst cS) (fst rS) ∈ fst h ⟩ → fst rS ≡ fst (relAt k)) )
```

<!--en-->
Replacement requires the fiber of satisfying outputs over each `c ∈ ωʟ` to be contractible. Membership in `ωʟ` provides only a propositionally truncated numeral representation; `PT.map` handles each explicit numeral case, and `mereFunct` combines the truncated existence with value uniqueness.
<!--zh-->
替换要求每个 `c ∈ ωʟ` 上满足公式的输出纤维都是收缩类型。属于 `ωʟ` 只提供经过命题截断的数码表示；`PT.map` 逐个处理显式数码情形，`mereFunct` 再把截断存在性与取值唯一性合成为收缩性。
<!--ja-->
置換を使うには、各 `c ∈ ωʟ` 上で論理式を満たす出力のファイバーが可縮でなければならない。`ωʟ` への所属から得られる数項表示は命題的切り詰めだけである。`PT.map` が明示的な各数項の場合を処理し、`mereFunct` が切り詰められた存在と値の一意性を可縮性へまとめる。
<!--/-->

```agda
  famBuild φ qφ = r .fst .fst , (inFam , outFam)
    where
    fc : (c : S) → ⟨ c ∈ˢ ωʟ ⟩
       → isContr (Σ[ y ∈ S ] ⟨ (y ∷ c ∷ []) ⊨ φ ⟩)
    fc c c∈ = mereFunct φ c (PT.map atK c∈)
```

<!--en-->
In an explicit numeral case `fst c = # j`, the chosen center of the fiber is the constructible ordered pair of `c` and `relAt j`. The proof supplies both its satisfaction of `φ` and equality of every competing satisfying output with this center; it does not choose a canonical `j` outside the truncation.
<!--zh-->
在显式的数码情形 `fst c = # j` 中，纤维的中心取为 `c` 与 `relAt j` 的可构造有序对。证明既给出它对 `φ` 的满足，也证明每个满足 `φ` 的其他输出都等于该中心；它并未从命题截断之外选择规范的 `j`。
<!--ja-->
明示的な数項の場合 `fst c = # j` では、ファイバーの中心として `c` と `relAt j` の構成可能な順序対を取る。その `φ` の充足と、`φ` を満たすほかのすべての出力がこの中心に等しいことを示すが、命題的切り詰めの外で標準的な `j` を選ぶわけではない。
<!--/-->

```agda
      where
      atK : Σ[ j ∈ Lift ℕ ] (# (lower j) ≡ fst c)
          → Σ[ y ∈ S ] ( ⟨ (y ∷ c ∷ []) ⊨ φ ⟩
                       × ((y' : S) → ⟨ (y' ∷ c ∷ []) ⊨ φ ⟩ → y' ≡ y) )
      atK (j , qj) = prS c (relAt (lower j)) , (holds , only)
```

<!--en-->
The numeral decoder gives its equality in the opposite orientation. Reversing it yields `fst c = # j`, the form required to apply the recursion graph theorem at `j`.
<!--zh-->
数码解码器给出的等式方向相反。将其反向便得到 `fst c = # j`，这正是把递归图定理应用于 `j` 所需的形式。
<!--ja-->
数項の読み出しから得られる等式は向きが逆である。それを反転すると `fst c = # j` となり、`j` に再帰グラフの定理を適用するために必要な形が得られる。
<!--/-->

```agda
        where
        qc : fst c ≡ # (lower j)
        qc = sym qj

```

<!--en-->
To prove that the chosen pair satisfies `φ`, the equality identifying `φ` with the paired graph reduces the claim to `PairRelGraphAt`. Pair formation supplies the outer ordered-pair equation, while `relAt-graph` supplies the graph assertion for `relAt j`.
<!--zh-->
为证明选定的有序对满足 `φ`，先用 `φ` 与成对图的等式把目标化为 `PairRelGraphAt`。有序对构造给出外层配对等式，`relAt-graph` 则给出 `relAt j` 的图断言。
<!--ja-->
選んだ順序対が `φ` を満たすことを示すには、`φ` と対にしたグラフとの等式で主張を `PairRelGraphAt` に帰着する。順序対の構成が外側の対の等式を与え、`relAt-graph` が `relAt j` に対するグラフの主張を与える。
<!--/-->

```agda
        holds : ⟨ (prS c (relAt (lower j)) ∷ c ∷ []) ⊨ φ ⟩
        holds = PairRelGraph-in zero (suc zero)
          (prS c (relAt (lower j)) ∷ c ∷ []) φ qφ (relAt (lower j))
          (prS-fst c (relAt (lower j)))
          (relAt-graph zero (sh2 zero)
```

<!--en-->
The graph assertion is instantiated at index `j`: the component representing the index is identified with `# j` by the reversed decoder equation, and the candidate relation is definitionally `relAt j`. This completes the existence half of the fiber proof.
<!--zh-->
图断言在索引 `j` 处实例化：表示索引的分量由反向后的解码等式认同为 `# j`，候选关系按定义就是 `relAt j`。纤维证明的存在性部分由此完成。
<!--ja-->
グラフの主張を添字 `j` で具体化する。添字を表す成分は反転した読み出しの等式により `# j` と同一視され、候補の関係は定義により `relAt j` である。これでファイバーの存在部分が完成する。
<!--/-->

```agda
            (relAt (lower j) ∷ prS c (relAt (lower j)) ∷ c ∷ [])
            (lower j) qc refl)

```

<!--en-->
For uniqueness, let `y'` be any other output satisfying `φ`. Reading the paired graph gives a propositionally truncated decomposition of `y'`; it may be eliminated into `y' = prS c (relAt j)` because equality in `S` is a proposition.
<!--zh-->
为证明唯一性，设 `y'` 是另一个满足 `φ` 的输出。读取成对图得到 `y'` 的一个经过命题截断的分解；由于 `S` 中的相等是命题，可以把该截断消去到目标 `y' = prS c (relAt j)` 中。
<!--ja-->
一意性のため、`φ` を満たす別の出力 `y'` を取る。対にしたグラフを読むと `y'` の命題的切り詰められた分解が得られる。`S` における等しさは命題なので、これを目標 `y' = prS c (relAt j)` へ除去できる。
<!--/-->

```agda
        only : (y' : S) → ⟨ (y' ∷ c ∷ []) ⊨ φ ⟩ → y' ≡ prS c (relAt (lower j))
        only y' h = PT.rec (isSetS y' (prS c (relAt (lower j)))) read
          (PairRelGraph-out zero (suc zero) (y' ∷ c ∷ []) φ qφ h)
          where
          read : PairOf zero (suc zero) (y' ∷ c ∷ []) φ qφ
```

<!--en-->
An explicit decomposition writes `y'` as the pair of `c` with some graph value `z`. The theorem `rel-only` identifies the underlying set of `z` with `relAt j`, and extensional equality of the proof-bearing elements lifts the resulting equality of ordered pairs to `S`.
<!--zh-->
一个显式分解把 `y'` 写成 `c` 与某个图取值 `z` 的有序对。定理 `rel-only` 把 `z` 的底层集合认同为 `relAt j`，而带有属于 `L` 之证明的元素的外延相等，把所得有序对等式提升到 `S` 中。
<!--ja-->
明示的な分解は `y'` を `c` とあるグラフ値 `z` の順序対として表す。定理 `rel-only` は `z` の台となる集合を `relAt j` と同一視し、`L` への所属証明を伴う要素の外延的等しさが、得られた順序対の等式を `S` へ持ち上げる。
<!--/-->

```agda
               → y' ≡ prS c (relAt (lower j))
          read (z , (q , hg)) = Σ≡Prop (λ t → snd (isL t))
            ( q
            ∙ cong (pr (fst c))
                (rel-only zero (sh2 zero) (z ∷ y' ∷ c ∷ []) (lower j) qc hg)
```

<!--en-->
The final equality compares the underlying ordered pair with the packaged constructible pair `prS c (relAt j)`. This proves uniqueness of the set-valued output at the decoded numeral, without asserting uniqueness of the graph witness itself.
<!--zh-->
最后的等式把底层有序对与封装后的可构造有序对 `prS c (relAt j)` 比较。由此得到解码数码处集合取值的唯一性，并不声称图见证本身唯一。
<!--ja-->
最後の等式は、台となる順序対を構成可能な順序対 `prS c (relAt j)` と比較する。これにより、読み出した数項における集合値の一意性が示されるが、グラフの証人そのものの一意性を主張するものではない。
<!--/-->

```agda
            ∙ sym (prS-fst c (relAt (lower j))) )

```

<!--en-->
Replacement over `ωʟ` now yields a contractible type of constructible sets whose members are exactly the outputs `y` for which there merely exists `c ∈ ωʟ` satisfying `φ`. Contractibility makes the resulting set unique; the existential numeral data remains propositionally truncated.
<!--zh-->
现在沿 `ωʟ` 使用替换，得到一个收缩类型，其中的可构造集合恰好以这些 `y` 为成员：只需经过命题截断地存在 `c ∈ ωʟ`，使 `φ` 成立。收缩性保证所得集合唯一，而存在的数码数据仍处于命题截断之中。
<!--ja-->
ここで `ωʟ` 上の置換により、ある `c ∈ ωʟ` が存在して `φ` を満たすという命題的切り詰めが成り立つ出力 `y` を、ちょうど要素とする構成可能集合の可縮な型を得る。可縮性は得られる集合を一意にするが、存在する数項のデータは命題的切り詰めのままである。
<!--/-->

```agda
    r : isContr (SetOf (λ y → ∃[ c ∶ S ] (c ∈ˢ ωʟ) ⊓ ((y ∷ c ∷ []) ⊨ φ)))
    r = hasReplacementL ωʟ φ fc

```

<!--en-->
Each standard pair belongs to the replacement set. The replacement specification is used with witness `numS k`, together with its membership in `ωʟ` and the paired-graph proof for `relAt k`; the packaged pair is then transported to its underlying pair in `V`.
<!--zh-->
每个标准有序对都属于替换所得的集合。对替换的规格取见证 `numS k`，并给出它属于 `ωʟ` 以及 `relAt k` 满足成对图的证明；随后把封装的有序对搬运为它在 `V` 中的底层有序对。
<!--ja-->
各標準的な順序対は置換で得た集合に属する。置換の仕様に証人 `numS k` を与え、その `ωʟ` への所属と `relAt k` に対する対グラフの証明を添える。その後、包装された順序対を `V` における台の順序対へ移す。
<!--/-->

```agda
    inFam : (k : ℕ) → ⟨ pr (# k) (fst (relAt k)) ∈ fst (r .fst .fst) ⟩
    inFam k = subst (λ t → ⟨ t ∈ fst (r .fst .fst) ⟩) qe
      (subst ⟨_⟩ (sym (r .fst .snd (prS (numS k) (relAt k))))
        ∣ numS k , (inω , holds) ∣₁)
      where
```

<!--en-->
The required transport equation unfolds only the packaging: the underlying set of `prS (numS k) (relAt k)` is the ordered pair of `# k` and the underlying set of `relAt k`. The equation for `numS k` supplies the first component.
<!--zh-->
所需搬运等式只展开封装：`prS (numS k) (relAt k)` 的底层集合就是 `# k` 与 `relAt k` 的底层集合所成的有序对。`numS k` 的等式给出其中的首分量。
<!--ja-->
必要な移送の等式は包装だけを展開する。`prS (numS k) (relAt k)` の台となる集合は、`# k` と `relAt k` の台となる集合との順序対である。`numS k` の等式がその第一成分を与える。
<!--/-->

```agda
      qe : fst (prS (numS k) (relAt k)) ≡ pr (# k) (fst (relAt k))
      qe = prS-fst (numS k) (relAt k)
         ∙ cong (λ t → pr t (fst (relAt k))) (numS-fst k)

```

<!--en-->
The witness `numS k` lies in the internal natural numbers because its underlying set is `# k`, and every numeral belongs to `ω`. Transporting `#∈ω k` along `numS-fst` supplies the required membership.
<!--zh-->
见证 `numS k` 属于内部自然数，因为它的底层集合是 `# k`，而每个数码都属于 `ω`。沿 `numS-fst` 搬运 `#∈ω k`，即可得到所需成员关系。
<!--ja-->
証人 `numS k` の台となる集合は `# k` であり、各数項は `ω` に属するので、`numS k` は内部自然数に属する。`#∈ω k` を `numS-fst` に沿って移せば、必要な所属が得られる。
<!--/-->

```agda
      inω : ⟨ numS k ∈ˢ ωʟ ⟩
      inω = subst (λ t → ⟨ t ∈ ω ⟩) (sym (numS-fst k)) (#∈ω k)

```

<!--en-->
The remaining witness shows that the packaged standard pair satisfies `φ`. Pair-graph introduction reduces this to the ordered-pair equation and to the fact that `relAt k` satisfies the recursion graph at `# k`.
<!--zh-->
余下的见证证明封装后的标准有序对满足 `φ`。成对图的引入把目标化为有序对等式，以及 `relAt k` 在 `# k` 处满足递归图这一事实。
<!--ja-->
残る証人は、包装された標準的な順序対が `φ` を満たすことを示す。対グラフの導入により、目標は順序対の等式と、`relAt k` が `# k` における再帰グラフを満たすという事実へ帰着する。
<!--/-->

```agda
      holds : ⟨ (prS (numS k) (relAt k) ∷ numS k ∷ []) ⊨ φ ⟩
      holds = PairRelGraph-in zero (suc zero)
        (prS (numS k) (relAt k) ∷ numS k ∷ []) φ qφ (relAt k)
        (prS-fst (numS k) (relAt k))
        (relAt-graph zero (sh2 zero)
```

<!--en-->
The graph theorem is instantiated directly at `k`. The equation `numS-fst k` identifies the input with `# k`, and reflexivity identifies the candidate output with `relAt k`, completing the standard-entry proof.
<!--zh-->
递归图定理直接在 `k` 处实例化。等式 `numS-fst k` 把输入认同为 `# k`，自反性把候选输出认同为 `relAt k`，从而完成标准条目的证明。
<!--ja-->
再帰グラフの定理を `k` で直接具体化する。等式 `numS-fst k` が入力を `# k` と同一視し、反射律が候補の出力を `relAt k` と同一視することで、標準項目の証明が完成する。
<!--/-->

```agda
          (relAt k ∷ prS (numS k) (relAt k) ∷ numS k ∷ []) k (numS-fst k) refl)

```

<!--en-->
For the converse specification, suppose an ordered pair belongs to the replacement set and its first component is known to be `# k`. The goal is only equality of its second component with `relAt k`, a proposition-valued conclusion into which the truncated replacement membership may be eliminated.
<!--zh-->
对于反向规格，设一个有序对属于替换所得的集合，并且已知其首分量是 `# k`。目标只是证明其第二分量等于 `relAt k`；这是命题值结论，因此可以向其中消去替换成员关系所含的命题截断。
<!--ja-->
逆向きの仕様では、ある順序対が置換で得た集合に属し、その第一成分が `# k` と分かっていると仮定する。目標は第二成分が `relAt k` に等しいことだけであり、これは命題値の結論なので、置換の所属に含まれる命題的切り詰めをそこへ除去できる。
<!--/-->

```agda
    outFam : (cS rS : S) (k : ℕ) → fst cS ≡ # k
           → ⟨ pr (fst cS) (fst rS) ∈ fst (r .fst .fst) ⟩
           → fst rS ≡ fst (relAt k)
    outFam cS rS k qc h =
      PT.rec (setIsSet (fst rS) (fst (relAt k))) atD
```

<!--en-->
The replacement specification yields, propositionally truncated, an internal natural `d` such that the packaged input pair satisfies `φ` over `d`. No numeral is selected here; the later pair equality will identify the underlying set of `d` with the already specified `# k`.
<!--zh-->
替换规格给出一个经过命题截断的内部自然数 `d`，使封装后的输入有序对在 `d` 上满足 `φ`。这里没有选择某个数码；稍后的有序对等式会把 `d` 的底层集合与已经指定的 `# k` 认同。
<!--ja-->
置換の仕様から、包装された入力の順序対が `d` 上で `φ` を満たすような内部自然数 `d` が、命題的切り詰められた形で得られる。ここでは数項を選ばない。後の順序対の等式が、`d` の台となる集合を、すでに指定された `# k` と同一視する。
<!--/-->

```agda
        (subst ⟨_⟩ (r .fst .snd (prS cS rS))
          (subst (λ t → ⟨ t ∈ fst (r .fst .fst) ⟩) (sym (prS-fst cS rS)) h))
      where
      atD : Σ[ d ∈ S ] ( ⟨ d ∈ˢ ωʟ ⟩ × ⟨ (prS cS rS ∷ d ∷ []) ⊨ φ ⟩ )
          → fst rS ≡ fst (relAt k)
```

<!--en-->
Reading the paired graph yields, again under propositional truncation, a relation value `z`, an equation identifying the packaged member with the pair `(d,z)`, and a proof that `z` satisfies the recursion graph at `d`. Equality of sets is propositional, so this truncation can also be eliminated.
<!--zh-->
读取成对图再次在命题截断下给出一个关系取值 `z`、把封装成员认同为有序对 `(d,z)` 的等式，以及 `z` 在 `d` 处满足递归图的证明。集合相等是命题，因此这层截断同样可以消去。
<!--ja-->
対にしたグラフを読むと、再び命題的切り詰めの下で、関係の値 `z`、包装された要素を順序対 `(d,z)` と同一視する等式、そして `z` が `d` における再帰グラフを満たす証明が得られる。集合の等しさは命題なので、この切り詰めも除去できる。
<!--/-->

```agda
      atD (d , (d∈ , hp)) = PT.rec (setIsSet (fst rS) (fst (relAt k))) read
        (PairRelGraph-out zero (suc zero) (prS cS rS ∷ d ∷ []) φ qφ hp)
        where
        read : PairOf zero (suc zero) (prS cS rS ∷ d ∷ []) φ qφ
             → fst rS ≡ fst (relAt k)
```

<!--en-->
After removing the packaging equation, injectivity of ordered pairs identifies the proposed second component with `z`. The theorem `rel-only` then identifies `z` with `relAt k`, once the first-component equation has shown that the graph index is `# k`.
<!--zh-->
去除封装等式后，有序对的单射性把所给第二分量认同为 `z`。一旦首分量等式表明图的索引是 `# k`，定理 `rel-only` 就进一步把 `z` 认同为 `relAt k`。
<!--ja-->
包装の等式を取り除くと、順序対の単射性により、与えられた第二成分が `z` と同一視される。第一成分の等式からグラフの添字が `# k` と分かれば、定理 `rel-only` がさらに `z` を `relAt k` と同一視する。
<!--/-->

```agda
        read (z , (q , hg)) = pr-inj q' .snd
          ∙ rel-only zero (sh2 zero) (z ∷ prS cS rS ∷ d ∷ []) k qd hg
          where
          q' : pr (fst cS) (fst rS) ≡ pr (fst d) (fst z)
          q' = sym (prS-fst cS rS) ∙ q
```

<!--en-->
The needed index equation follows from the first component of the same pair equality. Reversing that component identifies `d` with the original first component, and composing with the hypothesis about that component yields `fst d = # k`.
<!--zh-->
所需的索引等式来自同一个有序对等式的首分量。将该分量反向后，`d` 被认同为原来的首分量；再与关于该首分量的假设复合，便得到 `fst d = # k`。
<!--ja-->
必要な添字の等式は、同じ順序対の等式の第一成分から従う。その成分を反転すると `d` が元の第一成分と同一視され、さらにその第一成分についての仮定と合成して `fst d = # k` を得る。
<!--/-->

```agda
          qd : fst d ≡ # k
          qd = sym (pr-inj q' .fst) ∙ qc

```

<!--en-->
The constructible set selected by `famBuild` for the actual paired recursion graph is named `beforeFam` and kept opaque. Its following specification lemmas expose the standard entries and uniqueness of the set value at every known numeral; this construction supplies an internal relation family, without yet comparing names or proving a final well-order.
<!--zh-->
把实际的成对递归图交给 `famBuild` 后，所得可构造集合被命名为 `beforeFam` 并保持不透明。紧随其后的规格引理将给出所有标准条目，以及每个已知数码处集合取值的唯一性；这一步提供的是内部关系族，尚未比较名字，也未证明最终良序。
<!--ja-->
実際の対にした再帰グラフを `famBuild` に与えて得る構成可能集合を `beforeFam` と名付け、不透明に保つ。直後の仕様補題が、すべての標準項目と、既知の各数項における集合値の一意性を公開する。この構成が与えるのは内部の関係族であり、まだ名前の比較も最終的な整列順序の証明も行っていない。
<!--/-->

```agda
opaque
  beforeFam : S
  beforeFam = famBuild (PairRelGraphAt zero (suc zero)) refl .fst

```

<!--en-->
For each natural number `k`, the internal graph `beforeFam` contains the ordered pair of the numeral `# k` with the realized relation `relAt k`. This is the forward membership law for the family: it inserts the already known numeral and relation directly, without choosing a numeral decoder from a propositional truncation.
<!--zh-->
对每个自然数 `k`，内部图 `beforeFam` 都包含数码 `# k` 与已实现关系 `relAt k` 组成的有序对。这是该族的正向隶属律：它直接写入已经给定的数码与关系，并不从命题截断中选择数码解码见证。
<!--ja-->
各自然数 `k` について、内部グラフ `beforeFam` は、数項 `# k` と実現された関係 `relAt k` の順序対を含みます。これはこの族への正向きの所属則です。すでに与えられた数項と関係を直接書き込むので、命題的切り詰めから数項の復号の証人を選ぶ必要はありません。
<!--/-->

```agda
  beforeFam-in : (k : ℕ) → ⟨ pr (# k) (fst (relAt k)) ∈ fst beforeFam ⟩
  beforeFam-in = famBuild (PairRelGraphAt zero (suc zero)) refl .snd .fst

```

<!--en-->
Conversely, suppose an entry of `beforeFam` has first component equal to `# k`. Its second component then has the same underlying set as `relAt k`. Thus the graph has a unique set value at a specified numeral; this does not provide a canonical decoding witness or assert uniqueness of every proof carried by the construction.
<!--zh-->
反过来，设 `beforeFam` 的一个条目的第一分量等于 `# k`，则其第二分量的底层集合等于 `relAt k` 的底层集合。因此，该图在指定数码处具有唯一的集合值；这既不提供规范的解码见证，也不声称构造所携带的每份证明都唯一。
<!--ja-->
逆に、`beforeFam` のある項の第一成分が `# k` に等しいとします。このとき、その第二成分の台となる集合は `relAt k` の台となる集合に等しくなります。したがって、指定された数項でのグラフの集合値は一意です。しかし、これは標準的な復号の証人を与えるものでも、構成に含まれるすべての証明の一意性を主張するものでもありません。
<!--/-->

```agda
  beforeFam-out : (cS rS : S) (k : ℕ) → fst cS ≡ # k
                → ⟨ pr (fst cS) (fst rS) ∈ fst beforeFam ⟩
                → fst rS ≡ fst (relAt k)
  beforeFam-out = famBuild (PairRelGraphAt zero (suc zero)) refl .snd .snd
```

<!--en-->
## The order at a numeral held in a slot
<!--zh-->
## 某个槽位所持数码处的那个序
<!--ja-->
## スロット内の数項における順序
<!--/-->

<!--en-->
The formula `BeforeAt b x y` asks for a relation `r` in two steps. First, `appC` says that the constant family `beforeFam` assigns `r` to the value denoted by `b`. Then `appAt` says that `r` contains the ordered pair of the objects denoted by `x` and `y`. The next theorem assumes that the value at `b` is the numeral `# m` and identifies this internal statement with `before m` under the precise stage hypotheses stated below.
<!--zh-->
公式 `BeforeAt b x y` 分两步寻找关系 `r`。首先，`appC` 断言常元族 `beforeFam` 在 `b` 所指的值处取值为 `r`；随后，`appAt` 断言 `r` 包含 `x` 与 `y` 所指对象组成的有序对。下一条定理假设 `b` 所指的值为数码 `# m`，并在下文明确列出的层隶属条件下，把这一内部陈述认同为 `before m`。
<!--ja-->
論理式 `BeforeAt b x y` は、二段の主張によって関係 `r` を求めます。まず `appC` が、定数である族 `beforeFam` は `b` が指す値に `r` を割り当てると述べます。次に `appAt` が、`r` は `x` と `y` の指す対象の順序対を含むと述べます。続く定理では、`b` における値が数項 `# m` であると仮定し、以下に明記する段階所属の仮定のもとで、この内部の主張を `before m` と同定します。
<!--/-->

```agda
opaque
  BeforeAt : ∀ {n} → Fin n → Fin n → Fin n → Formula S n
  BeforeAt b x y =
    ∃̇ ( appC beforeFam (suc b) zero ∧̇ appAt zero (suc x) (suc y) )

```

<!--en-->
Fix an environment and a natural number `m`. The equation for `b` says that its value is the numeral `# m`, while the two membership hypotheses place the values denoted by `x` and `y` in `finiteStage m`. These assumptions connect the three variables to one finite-stage comparison; the adequacy theorem is stated only in this restricted context.
<!--zh-->
固定一个环境与自然数 `m`。关于 `b` 的等式说明其值是数码 `# m`，另两条隶属假设则把 `x` 与 `y` 所指的值放入 `finiteStage m`。这些假设把三个变元联系到同一个有限层比较；充分性定理只在这一受限语境中陈述。
<!--ja-->
環境と自然数 `m` を固定します。`b` についての等式は、その値が数項 `# m` であることを述べ、二つの所属の仮定は `x` と `y` が指す値を `finiteStage m` に置きます。これらの仮定によって三つの変数が一つの有限段階での比較に結びつき、妥当性定理はこの制限された文脈でのみ述べられます。
<!--/-->

```agda
module _ {n : ℕ} (b x y : Fin n) (γ : S ^ n) (m : ℕ)
         (qb : fst (lookup b γ) ≡ # m)
         (hx : ⟨ fst (lookup x γ) ∈ finiteStage m ⟩)
         (hy : ⟨ fst (lookup y γ) ∈ finiteStage m ⟩) where
  private
```

<!--en-->
The semantic target is the meta-level proposition that the value denoted by `x` precedes the value denoted by `y` according to `before m`. At this point the argument establishes representation of one finite-stage comparison; it makes no new claim about well-foundedness.
<!--zh-->
语义目标是一个元层面命题：按照 `before m`，`x` 所指的值先于 `y` 所指的值。此处的论证只建立一次有限层比较的表示，并不提出新的良基性结论。
<!--ja-->
意味論的な目標は、`before m` によって `x` の指す値が `y` の指す値に先行するという、メタレベルの命題です。ここで示すのは一つの有限段階での比較の表現であり、整礎性について新たな主張をするものではありません。
<!--/-->

```agda
    Goal : Type (ℓ-suc ℓ)
    Goal = ⟨ before m (fst (lookup x γ)) (fst (lookup y γ)) ⟩

```

<!--en-->
To read a satisfying assignment, temporarily expose the data hidden by the existential: a relation `r`, evidence that the family assigns `r` at `b`, and evidence that `r` contains the pair at `x,y`. This type describes an explicit package, but the semantics of the existential supplies it only under propositional truncation, so no persistent or canonical witness is obtained.
<!--zh-->
为了读出一个满足赋值，先暂时展开存在量词所隐藏的数据：一个关系 `r`、该族在 `b` 处取值为 `r` 的证据，以及 `r` 包含 `x,y` 处有序对的证据。这个类型描述的是一份显式数据包，但存在量词的语义只在命题截断下提供它，因而不会得到可保留或规范的见证。
<!--ja-->
充足する付値を読み出すため、存在量化が隠しているデータを一時的に明示します。それは、関係 `r`、族が `b` で `r` を値に取ることの証拠、そして `r` が `x,y` での順序対を含むことの証拠です。この型は明示的な組を記述しますが、存在量化の意味論がそれを与えるのは命題的切り詰めのもとだけなので、保持可能な証人や標準的な証人は得られません。
<!--/-->

```agda
    AtR : Type (ℓ-suc ℓ)
    AtR = Σ[ r ∈ S ]
      ( ⟨ (r ∷ γ) ⊨ appC beforeFam (suc b) zero ⟩
      × ⟨ (r ∷ γ) ⊨ appAt zero (suc x) (suc y) ⟩ )

```

<!--en-->
From any explicit package of this form, the two application adequacy laws recover ordinary set membership. The family law identifies the underlying set of `r` with that of `relAt m`; after transporting the pair membership along this equality, `relAt-rep` reads it back as `before m`. The two finite-stage membership hypotheses are exactly what permits this final representation step.
<!--zh-->
从任意一份这样的显式数据包出发，两条应用充分性律把公式满足读成通常的集合隶属。族的规律把 `r` 的底层集合识别为 `relAt m` 的底层集合；沿此等式运输有序对的隶属后，`relAt-rep` 再把它读回 `before m`。最后这一步恰好需要前述两条有限层隶属假设。
<!--ja-->
この形の明示的な組から、二つの適用の妥当性則によって、論理式の充足を通常の集合所属へ読み替えます。族についての法則は `r` の台となる集合を `relAt m` の台となる集合と同一視します。この等式に沿って順序対の所属を移送すると、`relAt-rep` がそれを `before m` へ読み戻します。最後の表現の段階で、先の二つの有限段階への所属の仮定がちょうど必要になります。
<!--/-->

```agda
    atR : AtR → Goal
    atR (r , (happ , hmem)) =
      relAt-rep m (fst (lookup x γ)) (fst (lookup y γ)) hx hy
        (subst (λ t → ⟨ pr (fst (lookup x γ)) (fst (lookup y γ)) ∈ t ⟩) qr
          (subst ⟨_⟩ (appAt-adequate zero (suc x) (suc y) (r ∷ γ)) hmem))
```

<!--en-->
The first application fact says internally that `beforeFam` takes the value `r` at the entry stored in `b`. Its adequacy law turns this into the external membership statement that the pair consisting of that entry and `r` belongs to `beforeFam`.
<!--zh-->
第一条应用事实在内部断言：`beforeFam` 在 `b` 所存条目处取值为 `r`。它的充分性律把这条陈述化为外部隶属事实，即该条目与 `r` 组成的有序对属于 `beforeFam`。
<!--ja-->
第一の適用の事実は、`beforeFam` が `b` に格納された項で値 `r` を取ることを内部的に述べています。その妥当性則により、当該の項と `r` の順序対が `beforeFam` に属するという外部の所属命題へ移ります。
<!--/-->

```agda
      where
      hf : ⟨ pr (fst (lookup b γ)) (fst r) ∈ fst beforeFam ⟩
      hf = subst ⟨_⟩ (appC-adequate beforeFam (suc b) zero (r ∷ γ)) happ

```

<!--en-->
Because the entry at `b` is known to equal `# m`, the backward family law now identifies the underlying set of `r` with the underlying set of `relAt m`. This uses uniqueness of the set value at a specified numeral, rather than a global choice of numeral decodings.
<!--zh-->
由于已经知道 `b` 处的条目等于 `# m`，族的反向规律便把 `r` 的底层集合识别为 `relAt m` 的底层集合。这里使用的是指定数码处集合值的唯一性，而不是对数码解码作全局选择。
<!--ja-->
`b` での項が `# m` に等しいと分かっているので、族の逆向きの法則は `r` の台となる集合を `relAt m` の台となる集合と同一視します。ここで使うのは、指定された数項での集合値の一意性であって、数項の復号を大域的に選択することではありません。
<!--/-->

```agda
      qr : fst r ≡ fst (relAt m)
      qr = beforeFam-out (lookup b γ) r m qb hf

```

<!--en-->
We can now prove the two directions of the exact semantic correspondence. Unfolding `BeforeAt` locally exposes its single existential and the two application facts, while the hypotheses on `b`, `x`, and `y` remain part of both statements.
<!--zh-->
现在可以证明精确语义对应的两个方向。局部展开 `BeforeAt` 会显露它的单个存在量词与两条应用事实，而关于 `b`、`x`、`y` 的假设始终保留在两个陈述中。
<!--ja-->
これで、正確な意味論的対応の二方向を証明できます。`BeforeAt` を局所的に展開すると、一つの存在量化と二つの適用の事実が現れますが、`b`、`x`、`y` についての仮定は両方の主張に引き続き含まれています。
<!--/-->

```agda
  opaque
    unfolding BeforeAt

```

<!--en-->
For the outward direction, satisfaction of the existential gives only a propositionally truncated relation package. The proof eliminates that truncation directly into `Goal`, which is a proposition, by applying the conversion above to each hypothetical explicit package. It never extracts an inhabitant of the intermediate type as retained data.
<!--zh-->
在向外方向中，存在量词的满足只给出经过命题截断的关系数据包。证明把该命题截断直接消去到作为命题的 `Goal`：对每份假设中的显式数据包应用上面的转换即可。它并不会抽取并保留中间类型的元素。
<!--ja-->
外向きの方向では、存在量化の充足から得られるのは、命題的切り詰めを受けた関係の組だけです。証明は、仮に明示された各組へ上の変換を適用することで、その切り詰めを命題である `Goal` へ直接消去します。中間の型の要素をデータとして取り出して保持することはありません。
<!--/-->

```agda
    BeforeAt-out : ⟨ γ ⊨ BeforeAt b x y ⟩
                 → ⟨ before m (fst (lookup x γ)) (fst (lookup y γ)) ⟩
    BeforeAt-out h =
      PT.rec (snd (before m (fst (lookup x γ)) (fst (lookup y γ)))) atR h

```

<!--en-->
For the inward direction, a proof of `before m` supplies the relation membership needed for the formula. We exhibit `relAt m` as a suitable relation, prove the two application facts, and then place the whole package under propositional truncation, as required by the existential semantics. This is a constructed witness for this direction, not a canonical witness recovered from a truncation.
<!--zh-->
在向内方向中，`before m` 的证明提供公式所需的关系隶属。我们取 `relAt m` 作为合适的关系，证明两条应用事实，再按存在量词的语义把整份数据包置于命题截断之下。这是为该方向构造的见证，并非从某个命题截断中恢复出的规范见证。
<!--ja-->
内向きの方向では、`before m` の証明から論理式に必要な関係所属が得られます。適切な関係として `relAt m` を提示し、二つの適用の事実を証明した後、存在量化の意味論に従って組全体を命題的切り詰めの中に入れます。これはこの方向のために構成した証人であり、切り詰めから復元した標準的な証人ではありません。
<!--/-->

```agda
    BeforeAt-in : ⟨ before m (fst (lookup x γ)) (fst (lookup y γ)) ⟩
                → ⟨ γ ⊨ BeforeAt b x y ⟩
    BeforeAt-in h = ∣ relAt m , (happ , hmem) ∣₁
      where
      happ : ⟨ (relAt m ∷ γ) ⊨ appC beforeFam (suc b) zero ⟩
```

<!--en-->
The family application follows from the known entry `(# m, relAt m)` in `beforeFam`. Transporting its first component along the equation for `b`, and then using application adequacy in the reverse direction, yields the required internal application fact.
<!--zh-->
族的应用来自 `beforeFam` 中已知的条目 `(# m, relAt m)`。先沿关于 `b` 的等式运输其第一分量，再反向使用应用的充分性，就得到所需的内部应用事实。
<!--ja-->
族への適用は、`beforeFam` に既知の項 `(# m, relAt m)` があることから従います。その第一成分を `b` についての等式に沿って移送し、適用の妥当性を逆向きに使うと、必要な内部の適用事実が得られます。
<!--/-->

```agda
      happ = subst ⟨_⟩
        (sym (appC-adequate beforeFam (suc b) zero (relAt m ∷ γ)))
        (subst (λ t → ⟨ pr t (fst (relAt m)) ∈ fst beforeFam ⟩) (sym qb)
          (beforeFam-in m))

```

<!--en-->
The second application fact comes from `relAt-fill`: the two stage-membership hypotheses and the assumed `before m` comparison place the pair of the values at `x,y` in `relAt m`. Reading application adequacy in the reverse direction turns that membership into satisfaction of `appAt`.
<!--zh-->
第二条应用事实来自 `relAt-fill`：两条有限层隶属假设与给定的 `before m` 比较共同说明，`x,y` 处两个值组成的有序对属于 `relAt m`。反向读取应用的充分性，便把这条隶属转成 `appAt` 的满足。
<!--ja-->
第二の適用の事実は `relAt-fill` から得られます。二つの有限段階への所属の仮定と、仮定された `before m` の比較により、`x,y` での値の順序対が `relAt m` に属します。適用の妥当性を逆向きに読むことで、この所属を `appAt` の充足へ変えます。
<!--/-->

```agda
      hmem : ⟨ (relAt m ∷ γ) ⊨ appAt zero (suc x) (suc y) ⟩
      hmem = subst ⟨_⟩
        (sym (appAt-adequate zero (suc x) (suc y) (relAt m ∷ γ)))
        (relAt-fill m (fst (lookup x γ)) (fst (lookup y γ)) hx hy h)
```

<!--en-->
## The frame, discharged
<!--zh-->
## 那个框架，兑现
<!--ja-->
## フレームの仮定を解消する
<!--/-->

<!--en-->
The two adequacy directions make `BeforeAt` an admissible input to the earlier `Described` framework. That framework first compares the finite levels of two limit-stage codes and, when the levels agree, uses the represented `before` relation within that level; separation then realizes this comparison as the internal relation `codeOrder`. This instantiation supplies the code-order component and does not yet compare names or prove a final internal well-order.
<!--zh-->
这两条充分性方向使 `BeforeAt` 满足先前 `Described` 框架的输入要求。该框架先比较两个极限层编码所在的有限层号；层号相同时，再使用本章所表示的层内 `before` 关系；随后由分离把这种比较实现为内部关系 `codeOrder`。这个实例只供应码序部分，尚未比较名字，也未证明最终的内部良序。
<!--ja-->
二つの妥当性の方向により、`BeforeAt` は先の `Described` の枠組みへの入力になります。その枠組みは、まず二つの極限段階のコードが属する有限段階の番号を比較し、番号が等しいときには、この章で表現した段階内の `before` 関係を用います。さらに分出公理によって、この比較を内部関係 `codeOrder` として実現します。この具体化が与えるのはコード順序の部分であり、まだ名前を比較せず、最終的な内部整列順序も証明しません。
<!--/-->

```agda
private
  module CodeOrder = Described BeforeAt BeforeAt-in BeforeAt-out

```

<!--en-->
The outcome is the relation set `codeOrder` together with two representation laws. `codeOrder-fill` turns a meta-level `limitOrder` comparison into membership in this set, and `codeOrder-rep` reads such membership back. Later name comparison uses these three results for comparing codes; the comparison of parameters is supplied separately.
<!--zh-->
所得结论是关系集 `codeOrder` 及其两条表示律。`codeOrder-fill` 把元层面的 `limitOrder` 比较转成这个集合中的隶属，`codeOrder-rep` 则把这种隶属读回。后续的名字比较用这三项结果比较码，而参数的比较关系另行提供。
<!--ja-->
ここで得られるのは、関係集合 `codeOrder` と二つの表現則です。`codeOrder-fill` はメタレベルの `limitOrder` の比較をこの集合への所属に変え、`codeOrder-rep` はその所属を読み戻します。後の名前比較では、この三つの結果をコードの比較に使い、パラメータの比較関係は別に与えます。
<!--/-->

```agda
open CodeOrder public using ( codeOrder; codeOrder-fill; codeOrder-rep )
```

<!--en-->
## Recap

For every natural number `n`, the set `relAt n` in `L` represents `before n` on members of `finiteStage n`. The recursion graph verifies these values, and Replacement is used only at the end to collect the whole family along `ωʟ` into `beforeFam`; the finite approximations use `finSet` and `finSetL`. If `b` denotes `# m` and the values denoted by `x,y` belong to `finiteStage m`, then `BeforeAt b x y` is equivalent to applying `before m` to those two values. Instantiating `Described` yields `codeOrder`, `codeOrder-fill`, and `codeOrder-rep`, which later provide the comparison of codes without yet comparing names or proving a final internal well-order.
<!--zh-->
## 小结

对每个自然数 `n`，`L` 中的集合 `relAt n` 都在 `finiteStage n` 的成员上表示 `before n`。递归图验证这些取值，只有最后沿 `ωʟ` 把整族收集为 `beforeFam` 时才使用替换；有限逼近使用的是 `finSet` 与 `finSetL`。若 `b` 所指的值是 `# m`，且 `x,y` 所指的值属于 `finiteStage m`，则 `BeforeAt b x y` 等价于用 `before m` 比较这两个值。实例化 `Described` 后得到 `codeOrder`、`codeOrder-fill` 与 `codeOrder-rep`，它们将在后续供应码的比较关系，而本章尚不比较名字，也不证明最终的内部良序。
<!--ja-->
## まとめ

各自然数 `n` について、`L` 内の集合 `relAt n` は `finiteStage n` の要素上で `before n` を表します。再帰グラフがこれらの値を検証し、置換公理を使うのは最後に `ωʟ` に沿って族全体を `beforeFam` へ集めるときだけです。有限近似には `finSet` と `finSetL` を使います。`b` が `# m` を指し、`x,y` の指す値が `finiteStage m` に属するなら、`BeforeAt b x y` はそれら二つの値を `before m` で比較することと同値です。`Described` を具体化して得られる `codeOrder`、`codeOrder-fill`、`codeOrder-rep` は後でコードの比較を与えますが、本章はまだ名前を比較せず、最終的な内部整列順序も証明しません。
<!--/-->
