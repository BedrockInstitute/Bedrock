<!--en-->
# Building and collapsing a Skolem hull

This chapter builds the Skolem hull of a starting set inside a constructible stage, proves that the hull is elementary in the stage, collapses it onto a transitive set by a membership-preserving bijection, and records how satisfaction and bounded formulas travel across that collapse. The key distinction is that the hull itself is only a coded image; transitivity appears only after the Mostowski collapse.
<!--zh-->
# 构造并塌缩 Skolem 壳

本章在可构造层内对起始集合作 Skolem 壳，证明壳在层中初等，再经保持隶属的双射把它塌缩到传递集上，并整理满足关系与有界公式如何跨过这次塌缩。关键区别是：壳本身只是编码所得的像；传递性只在 Mostowski 塌缩之后出现。
<!--ja-->
# Skolem 包を構成して崩壊させる

本章は、構成可能段階の中の始集合の Skolem 包を作り、包が段階の中で初等的であることを示し、所属を保つ全単射によって推移的集合へ崩壊させ、充足関係と有界論理式が崩壊を越えてどう移るかを整理します。重要なのは、包そのものはコードで与えられた像にすぎず、推移性は Mostowski 崩壊の後に初めて得られる、という点です。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

```

<!--en-->
The chapter runs on classical logic, and the hypothesis enters here. The hull construction decides satisfiability of queries, the extensionality proof decides membership in both directions, and the elementarity transfer eliminates double negation; each of these steps consumes excluded middle.
<!--zh-->
本章依赖经典逻辑，假设在此引入。壳的构造要判定查询的可满足性，外延性证明要双向判定隶属，初等性移送要消去双重否定；这些步骤都在消耗排中律。
<!--ja-->
本章は古典論理に依拠し、仮定はここで入ります。包の構成は問いの充足可能性を判定し、外延性の証明は両方向で所属を判定し、初等性の移送は二重否定を除去します。これらの段階はどれも排中律を消費します。
<!--/-->

```agda
open import Base.Prelude
open import Base.Classical using ( LEM )

```

<!--en-->
The module fixes the universe level `ℓ` and states the standing form of the classical hypothesis: excluded middle is received at `ℓ-suc ℓ` as an explicit parameter, never assumed globally, so every theorem of the chapter records exactly which level instance it uses.
<!--zh-->
模块把宇宙层级固定为 `ℓ`，并按本书的固定形式陈述经典假设：排中律以显式参数在 `ℓ-suc ℓ` 处领取，从不全局假设，因此本章每条定理都准确记录所用的是哪个层级的实例。
<!--ja-->
モジュールは宇宙レベル `ℓ` を固定し、本書の常の形式に従って古典的な仮定を明示的に受け取ります。`ℓ-suc ℓ` での排中律が引数として渡され、大域的に仮定されることはなく、本章の各定理はどのレベルの実例を使うかを正確に記録します。
<!--/-->

```agda
module L.GCH.SkolemHull {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

```

<!--en-->
The object language is the book's first-order language: formulas built from terms by equality and membership, closed under the propositional connectives and under unbounded and bounded quantifiers. The predicate `Δ₀` singles out the formulas whose quantifiers are all bounded.
<!--zh-->
对象语言即本书的一阶语言：公式由项经等词与隶属构成，对命题联结词、非有界量词与有界量词封闭。谓词 `Δ₀` 挑出全部量词都有界的公式。
<!--ja-->
対象言語は本書の一階の言語です。論理式は項から等号と所属で作られ、命題の結合子、非有界と有界の量化子の下で閉じています。述語 `Δ₀` は、すべての量化子が有界である論理式を選び出します。
<!--/-->

```agda
open import FOL.ZFStructure using ( ZFStructure; module hPropStructure; _↾_ )
open import FOL.Syntax using
  ( Formula; Term; con; var; _∈̇_; _≐_; _∧̇_; _∨̇_; _⇒̇_; ¬̇_; ⊥̇
  ; ∃̇_; ∀̇_; ∀̇∈; ∃̇∈ )
open import FOL.LevyHierarchy using
```

<!--en-->
The predicate `Δ₀` is an inductive certificate following the structure of a formula: its constructors cover atoms, connectives, and bounded quantifiers, while unbounded quantifiers have no constructor. Such a certificate supports the later absoluteness argument; `countFo` and `constantsFo` record every constant occurrence.
<!--zh-->
谓词 `Δ₀` 是沿公式结构定义的归纳证书：其构造子覆盖原子式、联结词与有界量词，而无界量词没有对应构造子。这种证书支撑后文的绝对性论证；`countFo` 与 `constantsFo` 记录常元的每次出现。
<!--ja-->
述語 `Δ₀` は論理式の構造に沿う帰納的な証拠です。その構成子は原子式・結合子・有界量化子を覆いますが、非有界量化子に対応する構成子はありません。この証拠が後の絶対性の議論を支え、`countFo` と `constantsFo` は定数の各出現を記録します。
<!--/-->

```agda
  ( Δ₀; δ-∈; δ-≐; δ-∧; δ-∨; δ-⇒; δ-⊥; δ-∀∈; δ-∃∈ )
import FOL.Absoluteness
import FOL.Manipulation.ConstantOccurrences
import FOL.Semantics
open import FOL.Manipulation.ConstantOccurrences using ( countFo; constantsFo )
```

<!--en-->
Parameter abstraction replaces constant occurrences by extra environment variables; constant mapping and relabelling change constant alphabets while preserving semantics; and `renameTm` renames variable slots along a context map, providing the weakening by `suc` used below. The ambient hierarchy is opened with its extensionality, the property that sets with the same members are equal.
<!--zh-->
参数抽象用额外的环境变元替换常元出现；常元映射与常元改名在保持语义的同时改变常元字母表；`renameTm` 则沿语境映射改名变元槽，由此得到下文以 `suc` 实现的弱化。外围层级连同其外延性一同打开，外延性即成员相同的集合相等。
<!--ja-->
パラメータ抽象は定数の出現を追加の環境変数で置き換え、定数写像と定数改名は意味を保って定数アルファベットを変えます。`renameTm` は文脈写像に沿って変数の位置を改名し、これにより以下で `suc` による弱化が得られます。周囲の階層は外延性とともに開かれます。同じ要素をもつ集合は等しい、という性質です。
<!--/-->

```agda
open import FOL.Manipulation.ParameterAbstraction using ( absFo; ⊨-abs )
open import FOL.Manipulation.ConstantMapping using ( mapFo; mapTm; mapFo-comp; embed )
open import FOL.Manipulation.Relabelling using ( embed-⊨; mapΔ₀; ⊨-map )
open import FOL.Manipulation.Renaming using ( renameTm )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ; extensionalV )
```

<!--en-->
Presentations index the elements of a set by a small type with an embedding, and their fibers name presented elements. The collapse constructs a transitive image of any carrier `X`; extensionality of the restricted membership relation is needed later to make the collapse map injective on `X`. Δ₀ smallness separates a bounded-definable class into a set. The empty set belongs to every definability successor, and `Lset-suc` identifies the stage at a successor index with the definable powerset of the preceding stage.
<!--zh-->
呈现用一个带嵌入的小类型索引集合的元素，其纤维为被呈现元素命名。塌缩对任意载体 `X` 构造一个传递像；要使塌缩映射在 `X` 上单射，还需受限隶属关系满足外延性。Δ₀ 小性把有界可定义的类分离成集合。空集属于每个可定义性后继，而 `Lset-suc` 把后继指标处的层认同为前一层的可定义幂集。
<!--ja-->
提示は、埋め込みをもつ小さな型で集合の要素を索引づけ、その繊維が提示された要素を名指します。崩壊は任意の台 `X` から推移的な像を構成し、崩壊写像を `X` 上で単射にするために制限された所属関係の外延性を用います。Δ₀ の小ささは、有界に定義できるクラスを集合へ分離します。空集合は各定義可能性後続に属し、`Lset-suc` は後続添字の段階を直前の段階の定義可能冪集合と同一視します。
<!--/-->

```agda
open import V.Presentation {ℓ} using ( member; fiber )
open import V.Collapse {ℓ} using ( module Collapse; isExt; isTrans )
open import V.Smallness {ℓ} using ( separateFromSmall; module Δ₀Small )
open import L.Axioms.Basic {ℓ} using ( ∅∈𝒟ₒ; Lset-suc )
open import L.Constructible {ℓ}
```

<!--en-->
The constructible stage `Lset α` is transitive and its construction is monotone in the index, so a larger index yields a larger stage. The ordinal facts used repeatedly in the hull argument are that members of ordinals are ordinals, that `ω` is an ordinal, that numerals belong to `ω`, and that the empty set is an ordinal.
<!--zh-->
可构造层 `Lset α` 是传递的，且其构造对指数单调，故更大的指数给出更大的层。壳论证中反复用到的序数事实有：序数的成员是序数、`ω` 是序数、数码属于 `ω`、空集是序数。
<!--ja-->
構成可能な段階 `Lset α` は推移的であり、その構成は指数について単調なので、より大きな指数はより大きな段階を与えます。包の議論で繰り返し使う順序数の事実は、順序数の要素が順序数であること、`ω` が順序数であること、数項が `ω` に属すること、空集合が順序数であることです。
<!--/-->

```agda
  using ( 𝒮ʟ; isTransV; IsOrd; Lset; Lset-in; Lset-out; Lset-mono; 𝒟ₒ
        ; layer-trans; Lset-layer )
open import L.Ordinal {ℓ} using ( mem-ord; ω-ord; #∈ω; ∅-ord )
open import L.Ordinal.Stages {ℓ} lem using ( ord∈Lset→∈; rank-Lset )
open import L.Ordinal.Linear {ℓ} lem using ( ord-tri )
```

<!--en-->
Well orders come with a least-element selector: from the truncated existence of some element satisfying a predicate, it returns an element that satisfies the predicate and is least in the well order. The rank characterization of stage membership and the stage orders restricted to a stage carrier feed this selector its inputs, and the coding of unions and singletons builds the finite starting sets used later.
<!--zh-->
良序自带最小元选择器：从「存在某元素满足谓词」的截断陈述出发，它返回一个满足谓词且在良序下最小的元素。层隶属的秩刻画与限制到层载体的层序为该选择器供给输入，而并与单点的编码则构造后文使用的有限起始集合。
<!--ja-->
整列順序には最小要素の選択子が伴います。述語を満たす要素の存在の切り詰められた主張から、述語を満たし整列順序で最小の要素を返します。段階の所属のランクによる特徴づけと、段階の台に制限した段階の順序がこの選択子に入力を供給し、和と単元を符号化する仕組みが、後で使う有限の始集合を作ります。
<!--/-->

```agda
open import L.Rank {ℓ} using ( rank-fix )
open import L.WellOrder.Base {ℓ-suc ℓ} using ( SWO; leastOf )
open import L.Choice.StageOrders {ℓ} lem using ( orderAt )
open import L.Coding.CodeConstructibility {ℓ} using ( cup-out; cup-inl; cup-inr; sgl-out )

```

<!--en-->
The environments of this chapter are vectors of carrier elements, and the operations on them are componentwise: mapping a function over an environment, looking up an index, extending by one element, and concatenating. Pairs with propositional second components record elements together with certificates that never distinguish.
<!--zh-->
本章的环境是载体元素构成的向量，其运算逐分量进行：把函数映射到环境上、按索引查找、添入一个元素、以及拼接。第二分量为命题的对把元素与永不区分的证书一并记录。
<!--ja-->
本章の環境は台の要素のベクトルであり、その演算は成分ごとに行われます。関数を環境へ写すこと、索引で参照すること、要素を一つ加えて延ばすこと、そして連結です。第二成分が命題である対は、要素を、決して区別しない証拠とともに記録します。
<!--/-->

```agda
open import Cubical.Data.Nat using ( _+_ )
open import Cubical.Data.Vec using ( Vec; map; lookup; _∷_; []; _++_ )
open import Cubical.Data.Sigma using ( Σ≡Prop; _×_; _,_ )
open import Cubical.Data.Sum using ( _⊎_; inl; inr )
import Cubical.Data.Sum as Sum
```

<!--en-->
The empty type represents contradiction: `Empty.rec` eliminates an inhabitant into any target, while `isProp⊥` allows a truncation to be eliminated when the target is contradiction. Satisfaction of existential formulas and membership in presented sets are expressed by propositional truncation, so they retain existence without choosing a witness.
<!--zh-->
空类型表示矛盾：`Empty.rec` 可把其元素消去到任意目标，而 `isProp⊥` 使目标为矛盾时可以消去命题截断。存在公式的满足以及呈现集合中的隶属用命题截断表达，因而保留存在性而不选定见证。
<!--ja-->
空型は矛盾を表します。`Empty.rec` はその要素から任意の目標へ消去し、`isProp⊥` は目標が矛盾であるとき命題的切り詰めの消去を可能にします。存在論理式の充足と提示された集合への所属は命題的切り詰めで表され、証人を選ばずに存在だけを保持します。
<!--/-->

```agda
import Cubical.Data.Empty as Empty
open import Cubical.Data.Empty.Properties using ( isProp⊥ )
open import Cubical.Functions.Logic using ( ⇔toPath )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁; ∣_∣₁; squash₁ )
```

<!--en-->
The cumulative hierarchy presents a set by an index type and a valuation. The hull uses the finite tree type `Code` as its index type; formulas occur inside witness codes, but are not themselves the codes. The constructions supply the empty set, unions, unordered-pair and singleton constructions, and the infinite ordinal with its successor.
<!--zh-->
累积层级用索引类型与赋值呈现集合。壳以有限树类型 `Code` 为索引类型；公式是见证码中的字段，并不自身充当码。构造部分供给空集、并、无序对与单点集构造，以及无穷序数及其后继。
<!--ja-->
累積階層は添字型と評価で集合を提示します。包では有限木型 `Code` を添字型とし、論理式は証人コードの一部ですが、それ自体がコードなのではありません。構成は、空集合、和、非順序対と一元集合の構成、そして無限順序数とその後続を供給します。
<!--/-->

```agda
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; sett )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ∅; _∪_; ⁅_,_⁆; ⁅_⁆s; union-ax; pairing-ax; module InfinitySet
        ; SetPackage; SingletonPackage )  -- lint-agda: keep (SetPackage via record projection)
open InfinitySet using ( ω; sucV )
```

<!--en-->
The small membership relation `_∈ₛ_` and its bridge `∈∈ₛ` to the ambient membership `_∈ˢ_` connect the presented reading of a set with its reading inside the hierarchy: what a presentation records internally is exactly what holds in the universe.
<!--zh-->
小隶属关系 `_∈ₛ_` 及其与外围隶属 `_∈ˢ_` 之间的桥 `∈∈ₛ`，把一个集合的呈现读法与它在层级中的读法连接起来：呈现内部所记录的，恰是宇宙中成立的。
<!--ja-->
小さな所属の関係 `_∈ₛ_` と、周囲の所属 `_∈ˢ_` への橋 `∈∈ₛ` は、集合の提示された読みと、階層の中での読みをつなぎます。提示が内部的に記録することは、宇宙で成り立つことと同じです。
<!--/-->

```agda
open import Cubical.HITs.CumulativeHierarchy.Properties
  using ( _∈ₛ_; ∈∈ₛ; ⟪_⟫; ⟪_⟫↪; extensionality )

```

<!--en-->
Opening the ambient structure fixes the unqualified symbols for ambient equality and membership; restricted structures introduced below retain their own semantic interpretations.
<!--zh-->
打开外围结构后，无修饰的等号与隶属符号固定表示外围关系；下文的受限结构仍各有自己的语义解释。
<!--ja-->
周囲の構造を開くことで、修飾のない等号と所属の記号は周囲の関係を表します。一方、制限された各構造は固有の意味論的解釈をもちます。
<!--/-->

```agda
open hPropStructure 𝒮ᵥ

```

<!--en-->
`SemV` supplies the fixed-length ambient environments used when satisfaction is instantiated below. For formulas whose constants range over `𝒮ʟ`, counting occurrences identifies the constant-free case; `erase` then replaces its impossible constants by the empty constant domain without changing satisfaction.
<!--zh-->
`SemV` 给出下文实例化满足关系时使用的定长外围环境。对常元取自 `𝒮ʟ` 的公式，出现次数计数识别无常元情形；`erase` 随后把不可能出现的常元域换为空类型，而不改变满足关系。
<!--ja-->
`SemV` は、以下で充足関係を具体化するときに使う固定長の周囲環境を与えます。定数が `𝒮ʟ` を動く論理式では、出現回数によって定数を含まない場合を識別できます。そのとき `erase` は、充足を変えずに定数領域を空の型へ置き換えます。
<!--/-->

```agda
module SemV = FOL.Semantics 𝒮ᵥ using ( _^_; module At )
open SemV using ( _^_ )
module CS = hPropStructure 𝒮ʟ using ( S )
module Cnt = FOL.Manipulation.ConstantOccurrences.ZeroOccurrences CS.S using ( erase; erase-inv )

```

<!--en-->
With an empty constant domain, `Δ₀-small` shows that the truth value of every bounded formula at every environment is equivalent to a proposition one universe lower; separation requires a separate application of `separateFromSmall`. The term algebra then begins: it is parameterized by a structure, a map of its carrier into the ambient universe, and a well order on that carrier.
<!--zh-->
在空常元域上，`Δ₀-small` 证明每个有界公式在每个环境中的真值都等价于低一层宇宙中的命题；要得到分离还需另行应用 `separateFromSmall`。项代数随之开始：它以一个结构、把其载体映入外围宇宙的映射，以及该载体上的良序为参数。
<!--ja-->
空の定数領域では、`Δ₀-small` は各有界論理式の各環境での真理値が一段低い宇宙の命題と同値であることを示します。分出にはさらに `separateFromSmall` を適用する必要があります。そして項代数が始まります。構造、その台を周囲の宇宙へ写す写像、そして台の上の整列順序を引数とするのです。
<!--/-->

```agda
module D0 = Δ₀Small {ℓc = ℓ-suc ℓ} {K = ⊥* {ℓ-suc ℓ}} (λ b → Empty.rec* b)
  using ( Δ₀-small )
module TermAlgebra (𝒮 : ZFStructure (ℓ-suc ℓ))
                   (toSet : ZFStructure.S 𝒮 → V ℓ)
                   (wo : SWO (ZFStructure.S 𝒮))
```

<!--en-->
The remaining parameters are a default element `junk` and a family of base generators indexed by `K`; only the later hull instance identifies `K` with a presentation of the starting set. The junk value is a bookkeeping device, and the constructions below never inspect it.
<!--zh-->
其余参数是默认元素 `junk` 与以 `K` 为索引的基生成元族；只有后文的壳实例把 `K` 认同为起始集合的一个呈现。垃圾值只是簿记装置，下文的构造从不检视它。
<!--ja-->
残りの引数は、既定の要素 `junk` と、`K` で索引づけられた基底の生成元の族です。`K` を始集合の提示と同一視するのは、後の包の実例です。既定の値は簿記のためのもので、後の構成がそれを調べることはありません。
<!--/-->

```agda
                   (junk : ZFStructure.S 𝒮)
                   {K : Type ℓ} (emb : K → ZFStructure.S 𝒮) where

```

<!--en-->
Only the unqualified Agda name `_∈ˢ_` is hidden from the parameter structure; satisfaction `_⊨₀_` still interprets atomic membership using `𝒮`. Renaming the carrier keeps the chapter's own references to the ambient carrier unambiguous.
<!--zh-->
这里只隐藏参数结构中未加限定的 Agda 名 `_∈ˢ_`；满足关系 `_⊨₀_` 仍用 `𝒮` 解释原子隶属。为载体改名，则使本章对外围载体的指称保持无歧义。
<!--ja-->
ここで隠すのは引数構造の修飾されていない Agda 名 `_∈ˢ_` だけであり、充足関係 `_⊨₀_` の原子的所属は引き続き `𝒮` によって解釈されます。台の名前を替えるのは、本章が周囲の台を指すときの曖昧さをなくすためです。
<!--/-->

```agda
  open ZFStructure 𝒮 hiding ( _∈ˢ_ ) renaming ( S to S𝒮 )

```

<!--en-->
Satisfaction for the term algebra is stated at the trivially empty constant domain: the formulas evaluated are exactly those built without constant symbols, the language of pure membership and equality, and satisfaction is proposition-valued. Every query and closure statement in this section uses this reading.
<!--zh-->
项代数的满足在平凡为空的常元域上陈述：被求值的公式恰是无常元符号构成的那些，即纯粹的隶属与相等语言，且满足取值于命题。本节的每条查询与闭合陈述都采用这一读法。
<!--ja-->
項代数の充足は、自明に空な定数領域のもとで述べられます。評価される論理式は、定数記号を使わずに作られたものだけで、純粋な所属と等号の言語であり、充足は命題値です。この節の各問いと閉包の主張は、すべてこの読みを用います。
<!--/-->

```agda
  private module Sem = FOL.Semantics 𝒮
  open Sem using () renaming ( _^_ to _^𝒮_ )
  module At0 = Sem.At (⊥* {ℓ}) Empty.rec* using ( _⊨_ )
  _⊨₀_ : {n : ℕ} → S𝒮 ^𝒮 n → Formula (⊥* {ℓ}) n → hProp (ℓ-suc ℓ)
  _⊨₀_ = At0._⊨_
```

<!--en-->
The codes form a finite tree algebra over the base generators: a base code names a generator, and a witness code records a query of arity `suc k` together with `k` parameter codes. Because `Code` is inductive, every code is a finite tree, and the entries of `cs` are its immediate parameter subcodes, each of which may itself be a base or witness code.
<!--zh-->
码构成基生成元上的有限树代数：基码指名一个生成元；见证码记录一个元数为 `suc k` 的查询连同 `k` 个参数码。由于 `Code` 是归纳类型，每个码都是有限树；`cs` 的分量是当前码的直接参数子码，每个子码都可再是基码或见证码。
<!--ja-->
コードは、基底の生成元の上の有限な木の代数を作ります。基のコードは生成元を名指し、証人のコードは、アリティが `suc k` の問いと `k` 個の引数のコードを記録します。`Code` は帰納型なので各コードは有限木であり、`cs` の各成分はその直接の引数部分木です。各部分木は基コードでも証人コードでもかまいません。
<!--/-->

```agda

  data Code : Type ℓ where
    base : K → Code
    wit  : (k : ℕ) → Formula (⊥* {ℓ}) (suc k) → Vec Code k → Code

```

<!--en-->
`Sat k ψ vs` is the mere existence of an element satisfying `ψ` at the arbitrary parameter vector `vs`; the closure theorem later specializes `vs` to the values of codes. Satisfiability is stated as truncated existence: it asserts that a witness exists, without producing one.
<!--zh-->
`Sat k ψ vs` 是「存在元素在任意参数向量 `vs` 处满足 `ψ`」的仅仅存在；闭合定理随后把 `vs` 特化为码的取值。可满足性被陈述为截断的存在：它断言见证存在，而不产出见证。
<!--ja-->
`Sat k ψ vs` は、任意の引数のベクトル `vs` のもとで `ψ` を満たす要素の単なる存在です。閉包の定理は後に `vs` をコードの値として特殊化します。充足可能性は切り詰められた存在として述べられ、証人を産み出すことなく、存在を主張するだけです。
<!--/-->

```agda
  Sat : (k : ℕ) → Formula (⊥* {ℓ}) (suc k) → Vec S𝒮 k → Type (ℓ-suc ℓ)
  Sat k ψ vs = ∥ Σ[ a ∈ S𝒮 ] ⟨ (a ∷ vs) ⊨₀ ψ ⟩ ∥₁

```

<!--en-->
Given this truncated existence, `search` returns a least satisfying element for the particular strict well-order supplied as the parameter `wo`. Least is meant in that well order; it is not minimality with respect to membership, and not a comparison of ranks.
<!--zh-->
有了这条截断存在，`search` 就参数 `wo` 所供给的特定严格良序返回一个最小的满足元素。「最小」指该良序下的最小；它既不是关于隶属的极小，也不是秩的比较。
<!--ja-->
この切り詰められた存在が与えられれば、`search` は、引数 `wo` として渡された特定の狭義整列順序のもとで最小の充足要素を返します。最小とはその整列順序での最小のことであり、所属に関する極小でもランクの比較でもありません。
<!--/-->

```agda
  search : (k : ℕ) (ψ : Formula (⊥* {ℓ}) (suc k)) (vs : Vec S𝒮 k)
         → Sat k ψ vs → S𝒮
  search k ψ vs w = leastOf wo {ℓ'' = ℓ-suc ℓ} lem (λ a → (a ∷ vs) ⊨₀ ψ) w .fst

```

<!--en-->
Code vectors are evaluated componentwise, mutually with the evaluation of single codes: the values of the parameters of a witness code are the values of its component codes.
<!--zh-->
码向量逐分量求值，与单个码的求值相互定义：见证码的参数取值即其分量码的取值。
<!--ja-->
コードのベクトルは成分ごとに評価され、単一のコードの評価と相互に定義されます。証人のコードの引数の値は、その成分のコードの値です。
<!--/-->

```agda
  mutual
    vals : {m : ℕ} → Vec Code m → Vec S𝒮 m
    vals [] = []
    vals (c ∷ cs') = val c ∷ vals cs'

```

<!--en-->
A satisfiable witness code evaluates to the least satisfying element; an unsatisfiable one evaluates to `junk`. Since every code contributes a value to the image, `junk` may occur in the hull, while `val-wit` shows that it is irrelevant whenever satisfiability is given.
<!--zh-->
可满足的见证码求值为最小的满足元素；不可满足的见证码求值为 `junk`。由于每个码都向像贡献一个值，`junk` 可能出现在壳中；而 `val-wit` 表明，一旦给出可满足性，`junk` 便无关紧要。
<!--ja-->
充足可能な証人のコードは最小の充足要素へ評価され、充足しない証人のコードは `junk` へ評価されます。すべてのコードが像に値を供給するため、`junk` が包の中に現れることもあります。しかし `val-wit` が示すのは、充足可能性が与えられれば `junk` は無関係だということです。
<!--/-->

```agda
    val : Code → S𝒮
    val (base m) = emb m
    val (wit k ψ cs) = Sum.rec (search k ψ (vals cs)) (λ _ → junk)
                       (lem (Sat k ψ (vals cs) , squash₁))

```

<!--en-->
The small lemma records how a classical decision is used once its propositional target is known inhabited. If the decision is left, propositionhood identifies its inhabitant with `x`, so the eliminator equals `f x`; if it is right, its refutation contradicts `x`, and the case is impossible.
<!--zh-->
这条小引理记录：一旦命题目标已知有元素，经典判定如何被使用。若判定落在左支，命题性把其中的元素与 `x` 认同，故消去式等于 `f x`；若落在右支，其中的否定与 `x` 矛盾，因此该情形不可能。
<!--ja-->
この小さな補題は、命題の目標に要素があると分かったとき、古典的な判定がどのように使われるかを記録します。判定が左枝なら、命題性によりその要素は `x` と同一視され、消去結果は `f x` になります。右枝なら、その否定は `x` と矛盾するため、その場合は不可能です。
<!--/-->

```agda
  sum-stuck : {X : Type (ℓ-suc ℓ)} (x : X) (px : isProp X)
            → (f : X → S𝒮) (g : (X → Empty.⊥) → S𝒮) (s : X ⊎ (X → Empty.⊥))
            → Sum.rec f g s ≡ f x
  sum-stuck x px f g (Sum.inl x') = sym (cong f (px x x'))
  sum-stuck x px f g (Sum.inr h)  = Empty.rec (h x)
```

<!--en-->
Given a satisfiability witness for the query stored in a witness code, this lemma identifies the value of the code with the search's least satisfying element: the junk branch is refuted, and the witnessed branch computes the search.
<!--zh-->
给定见证码所存查询的可满足性见证，这条引理即可确认：该码的取值就是搜索的最小满足元素；垃圾分支被反驳，有见证的分支运行搜索。
<!--ja-->
証人コードに格納された問いの充足可能性の証拠が与えられると、この補題は、そのコードの値が探索の最小の充足要素と同一視されることを示します。既定の枝は反証され、証人のある枝が探索を実行します。
<!--/-->

```agda

  val-wit : (k : ℕ) (ψ : Formula (⊥* {ℓ}) (suc k)) (cs : Vec Code k)
          → (w : Sat k ψ (vals cs)) → val (wit k ψ cs) ≡ search k ψ (vals cs) w
  val-wit k ψ cs w = sum-stuck w squash₁ (search k ψ (vals cs)) (λ _ → junk)
                       (lem (Sat k ψ (vals cs) , squash₁))

```

<!--en-->
Evaluating a code vector is the same as mapping the evaluation over it, proved by a simple recursion. This lets later statements pass freely between the recursive form and the mapped form of an environment.
<!--zh-->
码向量的求值等同于对其映射求值，由简单递归证明。这使得后文的陈述可以在环境的递归形式与映射形式之间自由通行。
<!--ja-->
コードのベクトルの評価は、その上で評価を写すことと同じであり、簡単な再帰で示されます。これにより、後の主張は環境の再帰的な形と写した形の間を自由に行き来できます。
<!--/-->

```agda
  vals≡map : {m : ℕ} (cs : Vec Code m) → vals cs ≡ map val cs
  vals≡map [] = refl
  vals≡map (c ∷ cs') = cong₂ _∷_ refl (vals≡map cs')

```

<!--en-->
The hull is presented exactly as the hierarchy presents its sets: a code family together with a valuation. It is the image of the values of all codes, and the presentation may repeat elements, since different codes may evaluate alike. Membership in the hull is therefore only the truncated existence of a code, and nothing in this chapter claims that the hull is transitive or that it is the smallest closed set.
<!--zh-->
壳的呈现与层级呈现集合的方式相同：一个码族加一个赋值。它是全部码取值的像；由于不同码可能求值相同，呈现可以重复元素。因此壳中的隶属只是「存在某个码」的截断陈述，本章不主张壳传递，也不主张它是最小的闭合集合。
<!--ja-->
包の提示は、階層が集合を提示するのと同じ仕方です。コードの族と評価によります。包はすべてのコードの値の像であり、異なるコードが同じ値に評価されうるので、提示は要素を重複して持ちえます。したがって包の中の所属は、コードの存在の切り詰められた主張にすぎず、包が推移的であることや、最小の閉じた集合であることは、本章では主張されません。
<!--/-->

```agda
  Hull : V ℓ
  Hull = sett Code (λ c → toSet (val c))

```

<!--en-->
Membership in the presentation is direct: the value of any code is a member of the hull, witnessed by that very code.
<!--zh-->
呈现中的隶属是直接的：任何码的取值都是壳的成员，其见证正是该码本身。
<!--ja-->
提示の中の所属は直接です。どのコードの値も包の要素であり、その証人はそのコード自身です。
<!--/-->

```agda
  inHull : (c : Code) → ⟨ toSet (val c) ∈ˢ Hull ⟩
  inHull c = ∣ c , refl ∣₁

```

<!--en-->
Thus every satisfiable coded query has a satisfying witness in the hull. The theorem asserts this closure property; it does not characterize all members of the hull as successful least witnesses.
<!--zh-->
于是每条可满足的编码查询都在壳中有满足的见证。该定理断言的正是这条闭合性质；它并不把壳的全部成员都刻画为成功的最小见证。
<!--ja-->
こうして、充足可能な符号化された問いはどれも、包の中に充足する証人をもちます。この定理が主張するのはこの閉包の性質であり、包のすべての要素を成功した最小の証人として特徴づけるものではありません。
<!--/-->

```agda
  closed : (k : ℕ) (ψ : Formula (⊥* {ℓ}) (suc k)) (cs : Vec Code k)
         → Sat k ψ (vals cs)
         → ∥ Σ[ a ∈ S𝒮 ]
              (⟨ toSet a ∈ˢ Hull ⟩ × ⟨ (a ∷ vals cs) ⊨₀ ψ ⟩) ∥₁
  closed k ψ cs w = ∣ a , a∈H , sat ∣₁
```

<!--en-->
The witness is not searched for again: it is the value the term algebra already assigned, namely the least satisfying element returned by the search.
<!--zh-->
见证无需另寻：它就是项代数已赋予的取值，即搜索返回的最小满足元素。
<!--ja-->
証人を改めて探す必要はありません。項代数がすでに割り当てた値、すなわち探索が返した最小の充足要素がそれです。
<!--/-->

```agda
    where
    a : S𝒮
    a = search k ψ (vals cs) w

```

<!--en-->
The selector returns `a` together with both components of `IsLeast`: a proof that `a` satisfies the query and a proof that no strictly smaller satisfying element exists; this line projects the first component.
<!--zh-->
选择器返回 `a` 以及 `IsLeast` 的两个分量：`a` 满足查询的证明，和不存在严格更小的满足元素的证明；本行投影前一分量。
<!--ja-->
選択子は `a` と `IsLeast` の二成分、すなわち `a` が問いを満たす証明と、それより真に小さい充足要素がない証明を返します。この行は前者を射影します。
<!--/-->

```agda
    pa : ⟨ (a ∷ vals cs) ⊨₀ ψ ⟩
    pa = leastOf wo {ℓ'' = ℓ-suc ℓ} lem (λ a → (a ∷ vals cs) ⊨₀ ψ) w .snd .fst

```

<!--en-->
That the witness belongs to the hull comes from the witness code built for this very query: its value is identified with the search result by `val-wit`, and every code value lies in the hull.
<!--zh-->
见证属于壳，来自专为该查询构造的见证码：其取值经 `val-wit` 被认同为搜索结果，而每个码的取值都在壳中。
<!--ja-->
証人が包に属することは、まさにこの問いのために作られた証人のコードから来ます。その値は `val-wit` によって探索の結果と同一視され、すべてのコードの値は包の中にあります。
<!--/-->

```agda
    a∈H : ⟨ toSet a ∈ˢ Hull ⟩
    a∈H = subst (λ z → ⟨ toSet z ∈ˢ Hull ⟩) (val-wit k ψ cs w)
            (inHull (wit k ψ cs))

```

<!--en-->
Satisfaction is the recorded component, and the closure clause is complete.
<!--zh-->
满足即被记录的分量，闭合子句就此完成。
<!--ja-->
充足は記録された成分であり、閉包の節はこれで完成です。
<!--/-->

```agda
    sat : ⟨ (a ∷ vals cs) ⊨₀ ψ ⟩
    sat = pa
```

<!--en-->
## Transporting satisfaction along a carrier map
<!--zh-->
## 沿载体映射搬运满足关系
<!--ja-->
## 台の写像に沿って充足関係を移す
<!--/-->

<!--en-->
With the hull built and closed, the chapter turns to its second task, transporting satisfaction between structures, and states the transfer for two predicates on the ambient carrier.
<!--zh-->
壳已建成并闭合，本章转向第二个任务，即在结构之间搬运满足关系；移送模块就外围载体上的两个谓词陈述。
<!--ja-->
包が作られ閉じたので、本章は二つ目の作業、構造の間の充足の移送に移ります。移送は、周囲の台の上の二つの述語に対して述べられます。
<!--/-->

```agda
module SatTransfer (MA MB : S → hProp (ℓ-suc ℓ)) where

```

<!--en-->
The source carrier pairs each element of the ambient carrier with the proof that it satisfies the first predicate. Its formulas are read only at such pairs.
<!--zh-->
源载体把外围载体的每个元素与「它满足第一个谓词」的证明配对；其公式只在这种对上读取。
<!--ja-->
源の台は、周囲の台の各要素と、それが第一の述語を満たすことの証明の対です。その論理式は、このような対のもとでのみ読まれます。
<!--/-->

```agda
  SA : Type (ℓ-suc ℓ)
  SA = Σ[ x ∈ S ] ⟨ MA x ⟩

```

<!--en-->
The target carrier is the same construction for the second predicate, and satisfaction there is the target reading of the same formulas.
<!--zh-->
目标载体是第二个谓词上的同一构造；那里的满足是对同一公式的目标读法。
<!--ja-->
目標の台は、第二の述語に対する同じ構成であり、そこの充足は同じ論理式の目標の読みです。
<!--/-->

```agda
  SB : Type (ℓ-suc ℓ)
  SB = Σ[ x ∈ S ] ⟨ MB x ⟩

```

<!--en-->
The source structure reads formulas at the paired carrier: its term dictionary evaluates variables to the paired elements, and its satisfaction is proposition-valued.
<!--zh-->
源结构在配对载体上读取公式：项词典把变元解释为配对中的元素，满足取值于命题。
<!--ja-->
源の構造は、対になった台のもとで論理式を読みます。項の辞書は変数を対の要素として評価し、充足は命題値です。
<!--/-->

```agda
  module SemA = FOL.Semantics (𝒮ᵥ ↾ MA)
    using ( module At )
  module SemB = FOL.Semantics (𝒮ᵥ ↾ MB)
    using ( module At )
  open SemA.At SA id renaming ( _⊨_ to _⊨ᴬ_ ; ⟦_⟧ to ⟦_⟧ᴬ )
```

<!--en-->
The target structure does the same on the other side, with its own satisfaction and its own term dictionary.
<!--zh-->
目标结构在另一侧做同样的事，拥有自己的满足与自己的项词典。
<!--ja-->
目標の構造は、反対側で同じことを行い、固有の充足と固有の項の辞書をもちます。
<!--/-->

```agda
  open SemB.At SB id renaming ( _⊨_ to _⊨ᴮ_ ; ⟦_⟧ to ⟦_⟧ᴮ )

```

<!--en-->
Two principles organize the transfer. Agreement states, for every formula and environment, an equality of propositions: satisfaction on the left equals satisfaction of the mapped formula on the mapped environment. The witness principle, stated next, supports the backward existential direction: target existential truth must yield, merely, some `q : SA` whose image satisfies the matrix.
<!--zh-->
移送由两条原理组织。一致性对每条公式与每个环境陈述命题的相等：左侧的满足等于映射环境上映射公式的满足。接下来陈述的见证原理支撑存在量词的反向：目标侧存在式为真时，只须仅仅给出某个 `q : SA`，使其像满足矩阵。
<!--ja-->
移送は二つの原理で組織されます。一致とは、すべての論理式と環境に対して、左の充足と写された環境での写された論理式の充足が等しい、という命題の等式です。次に述べる証人の原理は存在量化の逆向きを支えます。目標側の存在が成り立つとき、その像が行列を充足する `q : SA` が単に存在すればよいのです。
<!--/-->

```agda
  Agree : (SA → SB) → Type (ℓ-suc (ℓ-suc ℓ))
  Agree g = (n : ℕ) (φ : Formula SA n) (δ : SA ^ n)
          → (δ ⊨ᴬ φ) ≡ (map g δ ⊨ᴮ mapFo g φ)
  Witness : (SA → SB) → Type (ℓ-suc ℓ)
  Witness g = (n : ℕ) (φ : Formula SA (suc n)) (δ : SA ^ n)
```

<!--en-->
It need not identify `q` as the preimage of any previously chosen target witness; the principle only asserts the truncated existence of some inner point whose image satisfies the matrix, and that is exactly the form the backward existential direction consumes.
<!--zh-->
它不要求该 `q` 是某个既定目标见证的原像；该原理只主张存在某个内部点的像满足矩阵的截断陈述，而这恰是存在量词反向所消耗的形式。
<!--ja-->
この `q` が、すでに選ばれた目標側の証人の逆像である必要はありません。この原理が主張するのは、その像が行列を充足する内側の点の存在の切り詰められた主張であり、これがまさに存在量化の逆方向が消費する形です。
<!--/-->

```agda
            → ⟨ map g δ ⊨ᴮ mapFo g (∃̇ φ) ⟩
            → ∥ Σ[ q ∈ SA ] ⟨ (g q ∷ map g δ) ⊨ᴮ mapFo g φ ⟩ ∥₁

```

<!--en-->
The transfer module receives the map together with the atomic hypotheses. Atomic membership and equality are required to agree in both directions across `g`, so that membership and equality atoms become paths of propositions in the induction.
<!--zh-->
移送模块收取映射连同原子假设：原子隶属与相等必须沿 `g` 双向一致，如此归纳中的原子隶属与相等才能成为命题的路径。
<!--ja-->
移送のモジュールは、写像と原子的な仮定を受け取ります。原子的な所属と等号には、`g` を越えた双方向の一致が必要です。そうして初めて、帰納の中の所属と等号のアトムが命題のパスになります。
<!--/-->

```agda
  module Along (g : SA → SB)
    (at∈ : (n : ℕ) (t u : Term SA n) (δ : SA ^ n)
         → (δ ⊨ᴬ (t ∈̇ u)) ≡ (map g δ ⊨ᴮ mapFo g (t ∈̇ u)))
    (at≐ : (n : ℕ) (t u : Term SA n) (δ : SA ^ n)
         → (δ ⊨ᴬ (t ≐ u)) ≡ (map g δ ⊨ᴮ mapFo g (t ≐ u)))
```

<!--en-->
The witness principle is the third hypothesis, completing the data of the transfer.
<!--zh-->
见证原理是第三条假设，移送的数据就此齐备。
<!--ja-->
証人の原理が第三の仮定であり、移送のデータはこれでそろいます。
<!--/-->

```agda
    (wit : Witness g) where

```

<!--en-->
The first weakening fact is stated in the source structure. Renaming by `suc` shifts every old variable past the new head of the environment, so evaluation at `x ∷ δ` recovers evaluation at `δ`; constants are unaffected.
<!--zh-->
第一条弱化事实在源结构中陈述。沿 `suc` 改名把每个旧变元移过环境中新添的首槽，故在 `x ∷ δ` 处求值还原为在 `δ` 处求值；常元不受影响。
<!--ja-->
最初の弱化補題は源の構造で述べられます。`suc` による改名は各既存変数を環境の新しい先頭要素の後へずらすため、`x ∷ δ` での評価は `δ` での評価に戻り、定数は影響を受けません。
<!--/-->

```agda
    private
      renA : {n : ℕ} (t : Term SA n) (x : SA) (δ : SA ^ n)
           → ⟦ renameTm suc t ⟧ᴬ (x ∷ δ) ≡ ⟦ t ⟧ᴬ δ
      renA (con c) x δ = refl
      renA (var i) x δ = refl
```

<!--en-->
The same weakening is sound in the target structure, and the next statement begins the comparison of mapping with weakening.
<!--zh-->
同样的弱化在目标结构中也成立；下一条陈述开始比较映射与弱化。
<!--ja-->
同じ弱めは目標の構造でも成立します。次の主張は、写しと弱めの比較を始めます。
<!--/-->

```agda

      renB : {n : ℕ} (t : Term SB n) (x : SB) (δ : SB ^ n)
           → ⟦ renameTm suc t ⟧ᴮ (x ∷ δ) ≡ ⟦ t ⟧ᴮ δ
      renB (con c) x δ = refl
      renB (var i) x δ = refl
      mapTm-ren : {n : ℕ} (t : Term SA n)
```

<!--en-->
Mapping and weakening commute on terms, definitionally: the map of a weakened term weakens each renamed component in turn.
<!--zh-->
映射与弱化在项上交换，这是定义性的：弱化项的映射逐个弱化被改名的分量。
<!--ja-->
写しと弱めは項の上で交換します。これは定義的なことで、弱めた項の写しは、改名された各成分を順に弱めます。
<!--/-->

```agda
                → mapTm g (renameTm suc t) ≡ renameTm suc (mapTm g t)
      mapTm-ren (con c) = refl
      mapTm-ren (var i) = refl

```

<!--en-->
The mapped weakened term, evaluated at an arbitrary target point `x` followed by the mapped environment, has the same value as the mapped term at the mapped environment.
<!--zh-->
被映射的弱化项在任意目标点 `x` 接映射环境处求值，与被映射项在映射环境处的值相同。
<!--ja-->
写して弱めた項を任意の目標点 `x` と写された環境で評価した値は、写された項を写された環境で評価した値と一致します。
<!--/-->

```agda
      renG : {n : ℕ} (t : Term SA n) (x : SB) (δ : SA ^ n)
           → ⟦ mapTm g (renameTm suc t) ⟧ᴮ (x ∷ map g δ) ≡ ⟦ mapTm g t ⟧ᴮ (map g δ)
      renG t x δ = cong (λ u → ⟦ u ⟧ᴮ (x ∷ map g δ)) (mapTm-ren t)
                 ∙ renB (mapTm g t) x (map g δ)

```

<!--en-->
Membership against a term is unchanged by the weakening, in the form the bounded clauses consume; and the next lemma states the side-condition transfer itself.
<!--zh-->
对项的隶属不受弱化影响，其形式恰为有界子句所消耗者；下一条引理陈述边条件的转移本身。
<!--ja-->
項に対する所属は弱めで変わらず、その形は有界の場合が消費するものです。次の補題が、副条件の移送そのものを述べます。
<!--/-->

```agda
      memRen : {n : ℕ} (t : Term SA n) (x : SB) (δ : SA ^ n)
             → (fst x ∈ˢ fst (⟦ mapTm g (renameTm suc t) ⟧ᴮ (x ∷ map g δ)))
             ≡ (fst x ∈ˢ fst (⟦ mapTm g t ⟧ᴮ (map g δ)))
      memRen t x δ = cong (λ s → fst x ∈ˢ fst s) (renG t x δ)
      memPath : {n : ℕ} (t : Term SA n) (q : SA) (δ : SA ^ n)
```

<!--en-->
The side condition of a bounded quantifier transfers across the map. The chain starts by weakening in the source structure, then applies the atomic membership hypothesis at the shifted environment.
<!--zh-->
有界量词的边条件跨越映射转移。链条先在源结构中弱化，再在移位环境处应用原子的隶属假设。
<!--ja-->
有界量化子の副条件は、写像を越えて移ります。連鎖は、源の構造で弱めることから始まり、ずらした環境のもとで所属の原子的な仮定を適用します。
<!--/-->

```agda
              → (fst q ∈ˢ fst (⟦ t ⟧ᴬ δ))
              ≡ (fst (g q) ∈ˢ fst (⟦ mapTm g t ⟧ᴮ (map g δ)))
      memPath {n} t q δ =
        cong (λ s → fst q ∈ˢ fst s) (sym (renA t q δ))
        ∙ at∈ (suc n) (var zero) (renameTm suc t) (q ∷ δ)
```

<!--en-->
The chain ends by weakening in the target structure. With it, the side condition of any bounded clause can be read on either side of the map.
<!--zh-->
链条以目标结构中的弱化结束。有了它，任何有界子句的边条件都可在映射两侧读取。
<!--ja-->
連鎖は、目標の構造での弱めで終わります。これで、どの有界の場合の副条件も、写像の両側で読めます。
<!--/-->

```agda
        ∙ memRen t (g q) δ

```

<!--en-->
The classical step is packaged once: for a proposition, double-negation elimination follows from excluded middle. The forward universal clauses assume a target counterexample, package it as an existential witness to the negated matrix, pull that counterexample back with `Witness`, and derive a contradiction; `dne` then yields the required target truth.
<!--zh-->
经典步骤被打包一次：对命题而言，双否消去由排中律而来。全称子句的正向先假设目标侧存在反例，把它包装成否定矩阵的存在见证，再用 `Witness` 拉回内部反例并推出矛盾；最后由 `dne` 得到所需的目标侧真值。
<!--ja-->
古典的な段階は一度だけまとめられます。命題に対する二重否定の除去は排中律から従います。全称の場合の順方向では、目標側の反例を仮定し、それを否定された行列の存在証人として包み、`Witness` で内側へ引き戻して矛盾を導きます。最後に `dne` が必要な目標側の真理を与えます。
<!--/-->

```agda
      dne : (P : hProp (ℓ-suc ℓ)) → (((⟨ P ⟩) → Empty.⊥) → Empty.⊥) → ⟨ P ⟩
      dne P h = Sum.rec (λ p → p)
        (λ (np : ⟨ P ⟩ → Empty.⊥) → Empty.rec (h np)) (lem P)

```

<!--en-->
The induction now runs through the ten clauses, and it starts where the hypotheses are: the two atomic clauses are exactly `at∈` and `at≐`. The propositional connectives transport componentwise, because conjunction, disjunction, and implication on propositions are determined by their components.
<!--zh-->
归纳现在沿十条子句运行，而它恰从假设所在处开始：两条原子子句正是 `at∈` 与 `at≐`。命题联结词逐分量搬运，因为命题上的合取、析取与蕴含都由其分量决定。
<!--ja-->
帰納は十の場合を通って始まります。最初の二つは仮定そのものであり、`at∈` と `at≐` です。命題の結合子は成分ごとに運ばれます。命題の上の合取・選言・含意は成分で決まるからです。
<!--/-->

```agda
    agree : Agree g
    agree n (t ∈̇ u) δ = at∈ n t u δ
    agree n (t ≐ u) δ = at≐ n t u δ
    agree n (φ ∧̇ ψ) δ = cong₂ _⊓_ (agree n φ δ) (agree n ψ δ)
    agree n (φ ∨̇ ψ) δ = cong₂ _⊔_ (agree n φ δ) (agree n ψ δ)
```

<!--en-->
Implication transports componentwise in the same way, falsity is constant, and the existential clause opens with a biconditional. Its forward direction states that inner satisfaction of the existential maps to outer satisfaction of the mapped existential.
<!--zh-->
蕴含同样逐分量搬运，假值恒定，而存在子句以一个双条件开场。其正向陈述：内部对存在式的满足映射为「映射环境上映射存在式」的满足。
<!--ja-->
含意も同じく成分ごとに運ばれ、偽は一定です。存在の節は同値で始まります。順方向は、内側での存在の充足が、写された環境のもとで写された存在の充足へ写ることを述べます。
<!--/-->

```agda
    agree n (φ ⇒̇ ψ) δ = cong₂ _⇒_ (agree n φ δ) (agree n ψ δ)
    agree n ⊥̇ δ = refl
    agree n (∃̇ ψ) δ = ⇔toPath fwd bwd
      where
      fwd : ⟨ δ ⊨ᴬ (∃̇ ψ) ⟩ → ⟨ map g δ ⊨ᴮ mapFo g (∃̇ ψ) ⟩
```

<!--en-->
Forward eliminates the truncation of the inner witness and maps the witness; backward is where the witness principle pays: the outer satisfaction is fed to the witness principle, which returns an inner point whose image satisfies the matrix, and agreement transports that satisfaction back.
<!--zh-->
正向消去内部见证的截断并把见证映射过去；反向正是见证原理发挥作用之处：把外部满足交给见证原理，它返回一个内部点，其像满足矩阵，再由一致把该满足搬回。
<!--ja-->
順方向は内側の証人の切り詰めを消去して証人を写します。逆方向こそ、証人の原理が働く場所です。外側の充足を証人の原理に渡すと、その像が行列を充足する内側の点が返り、一致がその充足を運び戻します。
<!--/-->

```agda
      fwd = PT.rec (snd (map g δ ⊨ᴮ mapFo g (∃̇ ψ)))
        (λ { (q , hq) → ∣ g q , subst ⟨_⟩ (agree (suc n) ψ (q ∷ δ)) hq ∣₁ })
      bwd : ⟨ map g δ ⊨ᴮ mapFo g (∃̇ ψ) ⟩ → ⟨ δ ⊨ᴬ (∃̇ ψ) ⟩
      bwd h = PT.map (λ { (q , hq) →
        q , subst ⟨_⟩ (sym (agree (suc n) ψ (q ∷ δ))) hq }) (wit n ψ δ h)
```

<!--en-->
The universal clause is the classical one: its forward direction assumes every inner point satisfies the matrix, fixes an outer point `x`, and must show that `x` satisfies the matrix in the image. The proof begins by applying double-negation elimination, which is where excluded middle enters the transfer.
<!--zh-->
全称子句是经典的一支：其正向假设每个内部点都满足矩阵，固定外部点 `x`，并须证明 `x` 在像中满足矩阵。证明从双否消去开始，这正是排中律进入移送之处。
<!--ja-->
全称の節が古典的な部分です。順方向は、すべての内側の点が行列を充足すると仮定し、外側の点 `x` を固定して、`x` が像の中で行列を充足することを示します。証明は二重否定の除去から始まり、ここで排中律が移送に入ります。
<!--/-->

```agda
    agree n (∀̇ ψ) δ = ⇔toPath fwd bwd
      where
      fwd : ((q : SA) → ⟨ (q ∷ δ) ⊨ᴬ ψ ⟩)
          → (x : SB) → ⟨ (x ∷ map g δ) ⊨ᴮ mapFo g ψ ⟩
      fwd h x = dne ((x ∷ map g δ) ⊨ᴮ mapFo g ψ) λ nx →
```

<!--en-->
If `x` failed, the mapped environment would satisfy the negated matrix at `x`; the witness principle applied to that negation returns an inner point whose image satisfies the negation, and the agreement at that inner point refutes the assumption that every inner point satisfies the matrix.
<!--zh-->
若 `x` 失败，映射环境就会在 `x` 处满足否定矩阵；对该否定施加见证原理，返回一个内部点，其像满足否定，而该内部点处的一致便反驳「每个内部点都满足矩阵」的假设。
<!--ja-->
もし `x` が失敗するなら、写された環境は `x` で否定された行列を充足します。その否定に証人の原理を施すと、像が否定を充足する内側の点が返り、その点での一致が、すべての内側の点が行列を充足するという仮定と矛盾します。
<!--/-->

```agda
        PT.rec isProp⊥ (λ { (q , hq) →
          lower (hq (subst ⟨_⟩ (agree (suc n) ψ (q ∷ δ)) (h q))) })
          (wit n (¬̇ ψ) δ ∣ x , (λ yes → lift (nx yes)) ∣₁)
      bwd : ((x : SB) → ⟨ (x ∷ map g δ) ⊨ᴮ mapFo g ψ ⟩)
          → (q : SA) → ⟨ (q ∷ δ) ⊨ᴬ ψ ⟩
```

<!--en-->
Backward is direct, since every inner point maps into the outer carrier. The bounded universal then opens with an auxiliary formula that conjoins the side condition, membership in the renamed bound, with the negated matrix; satisfaction of the auxiliary is the classical reading of "in the bound but the matrix fails".
<!--zh-->
反向是直接的，因为每个内部点都映入外部载体。有界全称随之以一条辅助公式开场：它把边条件，即属于改名后的界，与矩阵的否定合取；辅助公式的满足正是「在界内但矩阵不成立」的经典读法。
<!--ja-->
逆方向は直接です。すべての内側の点は外側の台へ写るからです。有界全称は、補助の論理式で始まります。それは、名前を替えた上界への所属と、行列の否定を連言したもので、「上界には属するが行列は成立しない」という古典的な読みです。
<!--/-->

```agda
      bwd h q = subst ⟨_⟩ (sym (agree (suc n) ψ (q ∷ δ))) (h (g q))
    agree n (∀̇∈ t ψ) δ = ⇔toPath fwd bwd
      where
      mat : Formula SA (suc n)
      mat = (var zero ∈̇ renameTm suc t) ∧̇ ¬̇ ψ
```

<!--en-->
Forward states that if every inner point in the bound satisfies the matrix, then every outer point belonging to the mapped bound satisfies the mapped matrix. The proof again begins with double-negation elimination: assume the outer point fails.
<!--zh-->
正向陈述：若界内的每个内部点都满足矩阵，则每个属于映射后界的外部点都满足映射后的矩阵。证明再次从双否消去开始：假设该外部点失败。
<!--ja-->
順方向は、上界の中のすべての内側の点が行列を充足するなら、写された上界に属するすべての外側の点が写された行列を充足する、と述べます。証明は再び二重否定の除去から始まり、外側の点が失敗すると仮定します。
<!--/-->

```agda
      fwd : ((q : SA) → ⟨ fst q ∈ˢ fst (⟦ t ⟧ᴬ δ) ⟩ → ⟨ (q ∷ δ) ⊨ᴬ ψ ⟩)
          → (x : SB) → ⟨ fst x ∈ˢ fst (⟦ mapTm g t ⟧ᴮ (map g δ)) ⟩
          → ⟨ (x ∷ map g δ) ⊨ᴮ mapFo g ψ ⟩
      fwd h x hx =
        dne ((x ∷ map g δ) ⊨ᴮ mapFo g ψ) λ nx →
```

<!--en-->
The witness principle is applied to the auxiliary formula, returning an inner point `q` whose image lies in the bound but refutes the matrix. The image's membership in the bound is transported back through the weakening and `memPath`, and agreement then lifts the inner satisfaction of the matrix to its image, contradicting the failure.
<!--zh-->
见证原理被施加于辅助公式，返回内部点 `q`：其像落在界内却反驳矩阵。像在界内的隶属经弱化与 `memPath` 搬回，一致再把内部对矩阵的满足提升到其像处，与失败相矛盾。
<!--ja-->
証人の原理を補助の論理式に施すと、内側の点 `q` が返ります。その像は上界に属しますが、行列を反証します。像の上界への所属は、弱めと `memPath` を通して運び戻され、一致が行列の内側での充足を像へ持ち上げて、失敗と矛盾します。
<!--/-->

```agda
        PT.rec isProp⊥ (λ { (q , hq) →
          lower (hq .snd (subst ⟨_⟩ (agree (suc n) ψ (q ∷ δ))
            (h q (subst ⟨_⟩ (sym (memPath t q δ))
                    (subst ⟨_⟩ (memRen t (g q) δ) (hq .fst)))))) })
          (wit n mat δ ∣ x , (subst ⟨_⟩ (sym (memRen t x δ)) hx
```

<!--en-->
The auxiliary application closes with the witness record, whose second component is the failure of the matrix at the image, that is, the negated matrix. Backward states that outer satisfaction at images, together with the inner side condition, gives inner satisfaction of the matrix.
<!--zh-->
辅助应用以见证记录收尾，其第二分量是矩阵在像处的失败，即否定矩阵。反向陈述：像处的外部满足加上内部边条件，即得内部对矩阵的满足。
<!--ja-->
補助の適用は証人の記録で閉じ、その第二成分は像における行列の失敗、すなわち否定された行列です。逆方向は、像のもとの外側の充足と内側の副条件から、内側の行列の充足が出ることを述べます。
<!--/-->

```agda
            , (λ yes → lift (nx yes))) ∣₁)
      bwd : ((x : SB) → ⟨ fst x ∈ˢ fst (⟦ mapTm g t ⟧ᴮ (map g δ)) ⟩
                   → ⟨ (x ∷ map g δ) ⊨ᴮ mapFo g ψ ⟩)
          → (q : SA) → ⟨ fst q ∈ˢ fst (⟦ t ⟧ᴬ δ) ⟩ → ⟨ (q ∷ δ) ⊨ᴬ ψ ⟩
      bwd h q hq =
```

<!--en-->
Backward applies the outer satisfaction at the image of the inner point, transporting the side condition by `memPath` and the matrix by agreement. The bounded existential then opens with its auxiliary matrix conjoining the side condition and the matrix itself.
<!--zh-->
反向在内点的像处施加外部满足，边条件经 `memPath`、矩阵经一致搬运。有界存在随之以其辅助矩阵开场：它合取边条件与矩阵本身。
<!--ja-->
逆方向は、内側の点の像のもとで外側の充足を適用します。副条件は `memPath` で、行列は一致で運ばれます。有界存在は、副条件と行列自身を連言した補助の行列で始まります。
<!--/-->

```agda
        subst ⟨_⟩ (sym (agree (suc n) ψ (q ∷ δ)))
          (h (g q) (subst ⟨_⟩ (memPath t q δ) hq))
    agree n (∃̇∈ t ψ) δ = ⇔toPath fwd bwd
      where
      mat : Formula SA (suc n)
```

<!--en-->
The auxiliary matrix is the side condition conjoined with the matrix, and forward states that an inner witness pair maps to an outer witness pair. The proof is a single mapping over the truncation.
<!--zh-->
辅助矩阵即边条件与矩阵的合取；正向陈述：内部见证对映射为外部见证对。证明只是对截断的一次映射。
<!--ja-->
補助の行列は、副条件と行列の連言であり、順方向は、内側の証人の対が外側の証人の対へ写ると述べます。証明は、切り詰めの上の一回の写しです。
<!--/-->

```agda
      mat = (var zero ∈̇ renameTm suc t) ∧̇ ψ
      fwd : ∥ Σ[ q ∈ SA ] (⟨ fst q ∈ˢ fst (⟦ t ⟧ᴬ δ) ⟩ × ⟨ (q ∷ δ) ⊨ᴬ ψ ⟩) ∥₁
          → ∥ Σ[ x ∈ SB ] (⟨ fst x ∈ˢ fst (⟦ mapTm g t ⟧ᴮ (map g δ)) ⟩
                        × ⟨ (x ∷ map g δ) ⊨ᴮ mapFo g ψ ⟩) ∥₁
      fwd = PT.map (λ { (q , hq , hψ) →
```

<!--en-->
The two components are transported separately: the side condition by `memPath` and the matrix by agreement. Backward states the converse, an outer witness pair yielding an inner one.
<!--zh-->
两个分量分别搬运：边条件经 `memPath`，矩阵经一致。反向陈述其逆：外部见证对给出内部见证对。
<!--ja-->
二つの成分は別々に運ばれます。副条件は `memPath` で、行列は一致によって運ばれます。逆方向はその逆を述べ、外側の証人の対が内側の対を与えます。
<!--/-->

```agda
        g q , (subst ⟨_⟩ (memPath t q δ) hq ,
               subst ⟨_⟩ (agree (suc n) ψ (q ∷ δ)) hψ) })
      bwd : ∥ Σ[ x ∈ SB ] (⟨ fst x ∈ˢ fst (⟦ mapTm g t ⟧ᴮ (map g δ)) ⟩
                        × ⟨ (x ∷ map g δ) ⊨ᴮ mapFo g ψ ⟩) ∥₁
          → ∥ Σ[ q ∈ SA ] (⟨ fst q ∈ˢ fst (⟦ t ⟧ᴬ δ) ⟩ × ⟨ (q ∷ δ) ⊨ᴬ ψ ⟩) ∥₁
```

<!--en-->
Backward runs the witness principle on the outer pair read in the auxiliary form, returning an inner point and a pair at its image; the components are then transported back through the weakening and `memPath`, and by agreement.
<!--zh-->
反向对以辅助形式读取的外部对运行见证原理，得到内点及其像处的对；两个分量再分别经弱化与 `memPath`、经一致搬回。
<!--ja-->
逆方向は、補助の形で読んだ外側の対に証人の原理を走らせ、内側の点とその像の対を得ます。成分は、弱めと `memPath`、そして一致によって運び戻されます。
<!--/-->

```agda
      bwd h = PT.map (λ { (q , hq) →
        q , ( subst ⟨_⟩ (sym (memPath t q δ))
                (subst ⟨_⟩ (memRen t (g q) δ) (hq .fst))
            , subst ⟨_⟩ (sym (agree (suc n) ψ (q ∷ δ))) (hq .snd)) })
        (wit n mat δ (PT.map (λ { (x , hx , hψ) →
```

<!--en-->
The two components close the bounded-existential transfer, and the ten-clause induction is complete.
<!--zh-->
两个分量闭合有界存在的移送，十条子句的归纳随之完成。
<!--ja-->
二つの成分が有界存在の移送を閉じ、十場合の帰納が完了します。
<!--/-->

```agda
          x , (subst ⟨_⟩ (sym (memRen t x δ)) hx , hψ) }) h))
```

<!--en-->
## The Tarski-Vaught criterion inside a stage
<!--zh-->
## 层内部的 Tarski-Vaught 判据
<!--ja-->
## 段階内部の Tarski-Vaught 判定条件
<!--/-->

<!--en-->
For an ordinal index `α`, the stage `Lset α` supplies the ambient structure in which this transfer will prove elementarity.
<!--zh-->
对序数指数 `α`，层 `Lset α` 给出外围结构，上述移送将在其中证明初等性。
<!--ja-->
順序数の指数 `α` に対し、段階 `Lset α` を周囲の構造とすれば、上の移送からその内部での初等性が得られます。
<!--/-->

```agda
module AtStage (α : S) (ordα : IsOrd α) where

```

<!--en-->
The stage is transitive, and the reason is precise: `Lset-layer α` proves that the layer at `α` is transitive, and `layer-trans` turns that into transitivity of `Lset α`. The ordinality hypothesis is not used here; it is reserved for the well order below.
<!--zh-->
层是传递的，理由很精确：`Lset-layer α` 证明 `α` 处的层传递，`layer-trans` 由此给出 `Lset α` 的传递性。序数性假设在此并未使用，而是留给下文的良序。
<!--ja-->
段階は推移的です。その理由は正確にはこうです。`Lset-layer α` が `α` における層の推移性の証明を与え、`layer-trans` がそれを `Lset α` の推移性へ変えます。順序数性の仮定はここでは使われず、下の整列順序のために取ってあります。
<!--/-->

```agda
  Ltr : isTransV (Lset α)
  Ltr = layer-trans (Lset-layer α)

```

<!--en-->
Transitivity lets bounded formulas be interpreted absolutely between `Lset α` and the universe. Thus the restricted stage structure can be used as the outer semantics in the Tarski-Vaught argument.
<!--zh-->
传递性保证有界公式在 `Lset α` 内部与全集中绝对一致。因此，层上的受限结构可作为 Tarski-Vaught 论证的外部语义。
<!--ja-->
推移性により、有界論理式は `Lset α` の内部と宇宙全体とで絶対的になります。したがって、段階に制限した構造を Tarski-Vaught の議論の外側の意味論として使えます。
<!--/-->

```agda
  module AbsL = FOL.Absoluteness.Single 𝒮ᵥ (λ x → x ∈ˢ Lset α) Ltr
    using ( SM; 𝒮M; _⊨ᵐ_; ⟦_⟧ᵐ; abs₀ )

```

<!--en-->
The stage carrier is the type of elements that belong to `Lset α`; every hull member and every stage reading below lives in this type.
<!--zh-->
层载体是属于 `Lset α` 的元素的类型；下文的每个壳成员与每次层读取都居于该类型。
<!--ja-->
段階の台は、`Lset α` に属する要素の型です。以下のどの包の要素も、どの段階での読みも、この型の中にあります。
<!--/-->

```agda
  SL : Type (ℓ-suc ℓ)
  SL = AbsL.SM

```

<!--en-->
The stage order of the earlier chapter restricts to a well order on this carrier. Fix a carrier `M` contained in this stage; its inclusion is part of the hypotheses.
<!--zh-->
前一章的层序限制为该载体上的良序。固定一个包含于该层的载体 `M`；它到该层的包含是所取假设的一部分。
<!--ja-->
前章の段階の順序は、この台の上の整列順序に制限されます。この段階に含まれる台 `M` を固定し、段階への包含を仮定します。
<!--/-->

```agda
  wL : SWO SL
  wL = orderAt α ordα
  module AtM (M : S) (M⊆L : (x : S) → ⟨ x ∈ˢ M ⟩ → ⟨ x ∈ˢ Lset α ⟩) where

```

<!--en-->
A carrier for the substructure is an element of the ambient carrier together with the proof that it belongs to `M`; formulas are read only at such pairs.
<!--zh-->
子结构的载体是外围载体中的元素连同其属于 `M` 的证明；公式只在这种对上读取。
<!--ja-->
部分構造の台は、周囲の台の要素と、それが `M` に属することの証明の対です。論理式はこのような対のもとでのみ読まれます。
<!--/-->

```agda
    SM : Type (ℓ-suc ℓ)
    SM = Σ[ x ∈ S ] ⟨ x ∈ˢ M ⟩

```

<!--en-->
The semantics of the substructure is the ambient semantics restricted to `M`: terms evaluate inside the restriction, and satisfaction is proposition-valued.
<!--zh-->
子结构的语义是外围语义在 `M` 上的限制：项在限制内部求值，满足取值于命题。
<!--ja-->
部分構造の意味論は、周囲の意味論の `M` への制限です。項は制限の内側で評価され、充足は命題値です。
<!--/-->

```agda
    module SemM = FOL.Semantics (𝒮ᵥ ↾ (λ x → x ∈ˢ M))
      using ( module At )
    open SemM.At SM id renaming ( _⊨_ to _⊨ᵐ_ ; ⟦_⟧ to ⟦_⟧ᵐ )

```

<!--en-->
The inclusion into the stage pairs each element of the carrier with its stage membership, supplied by the containment hypothesis.
<!--zh-->
到层的包含把载体的每个元素与其层隶属配对，后者由包含假设供给。
<!--ja-->
段階への包含は、台の各要素をその段階での所属と対にします。これは包含の仮定が供給します。
<!--/-->

```agda
    inL : SM → SL
    inL c = fst c , M⊆L (fst c) (snd c)

```

<!--en-->
Elementarity states that satisfaction is unchanged by this inclusion, for every formula and every environment of the carrier. It is a path of propositions, which is the form in which the two atomic congruences and the witness principle compose with it.
<!--zh-->
初等性陈述：对该载体的每条公式与每个环境，满足在包含下不变。它是命题间的路径，两条原子同余与见证原理正是以这种形式与它复合。
<!--ja-->
初等性は、この包含のもとで充足が変わらないことを、台のすべての論理式と環境に対して述べます。これは命題の間のパスであり、二つの原子式についての合同性と証人の原理がこの形で合成されます。
<!--/-->

```agda
    Elementary : Type (ℓ-suc (ℓ-suc ℓ))
    Elementary = (n : ℕ) (φ : Formula SM n) (δ : SM ^ n)
               → (δ ⊨ᵐ φ) ≡ (map inL δ AbsL.⊨ᵐ (mapFo inL φ))

```

<!--en-->
The Tarski-Vaught criterion is the witness form of elementarity: whenever the stage satisfies an existential at the image of an environment, some element of the carrier, imaged, satisfies the matrix there. Truncated existence suffices, since satisfaction is proposition-valued.
<!--zh-->
Tarski-Vaught 判据是初等性的见证形式：每当层在某个环境的像处满足一个存在式，就有载体的某个元素，其像在该处满足矩阵。由满足的命题值性，仅仅存在即可。
<!--ja-->
Tarski-Vaught の判定条件は、初等性の証人の形です。段階がある環境の像のもとで存在の論理式を充足するなら、台のある要素の像がそこで行列を充足します。充足が命題値なので、単に存在すれば足ります。
<!--/-->

```agda
    TarskiVaught : Type (ℓ-suc ℓ)
    TarskiVaught = (n : ℕ) (φ : Formula SM (suc n)) (δ : SM ^ n)
                 → ⟨ map inL δ AbsL.⊨ᵐ (mapFo inL (∃̇ φ)) ⟩
                 → ∥ Σ[ q ∈ SM ] ⟨ (inL q ∷ map inL δ) AbsL.⊨ᵐ (mapFo inL φ) ⟩ ∥₁

```

<!--en-->
Pointwise inclusion commutes with environment lookup; this is the variable case needed for term agreement.
<!--zh-->
逐点包含与环境查找可交换；这正是项的一致性所需的变元情形。
<!--ja-->
各点での包含は環境の参照と可換です。これは項の一致に必要な変数の場合です。
<!--/-->

```agda
    private
      lookup-inL : {n : ℕ} (i : Fin n) (δ : SM ^ n)
                 → lookup i (map inL δ) ≡ inL (lookup i δ)
      lookup-inL zero (c ∷ δ) = refl
      lookup-inL (suc i) (c ∷ δ) = lookup-inL i δ
```

<!--en-->
Terms agree across the inclusion: a term of the carrier evaluates to the same underlying element whether read in the substructure or read mapped in the stage. Constants are fixed, variables follow the lookups. The transfer machinery is then instantiated at the two membership predicates.
<!--zh-->
项在包含两侧一致：载体的项无论在子结构中读取，还是映射后在层中读取，都求得同一底层元素。常元固定，变元随查找而定。移送机制随即在两个隶属谓词处实例化。
<!--ja-->
項は包含の両側で一致します。台の項は、部分構造で読んでも、写して段階で読んでも、同じ底の要素に評価されます。定数は固定的で、変数は参照に従います。そして移送の仕組みが、二つの所属の述語のもとで具体化されます。
<!--/-->

```agda

      tm-agree : (n : ℕ) (t : Term SM n) (δ : SM ^ n)
               → fst (⟦ t ⟧ᵐ δ) ≡ fst (AbsL.⟦ mapTm inL t ⟧ᵐ (map inL δ))
      tm-agree n (con c) δ = refl
      tm-agree n (var i) δ = sym (cong fst (lookup-inL i δ))
    module Tr = SatTransfer (λ x → x ∈ˢ M) (λ x → x ∈ˢ Lset α)
```

<!--en-->
Elementarity follows by instantiating the shared induction: the two atoms are the congruences just proved, the witness principle is exactly the Tarski-Vaught instance, and the shared body carries the boolean and quantifier clauses. Nothing about stages is used beyond the two congruences and the criterion.
<!--zh-->
初等性由共享归纳实例化而来：两个原子情形由刚证得的满足关系合同性给出，见证原理恰是 Tarski-Vaught 实例，而布尔与量词子句由共享主体搬运。除这两条同余与该判据外，不使用任何关于层的特殊性质。
<!--ja-->
初等性は、共有の帰納を具体化して得られます。二つの原子式の場合は、今証明した充足関係の合同性から得られ、証人の原理がちょうど Tarski-Vaught の実例で、ブールと量化子の場合は共有の本体が運びます。二つの合同性と判定条件を除けば、段階に固有のことは何も使われません。
<!--/-->

```agda

    TV→elem : TarskiVaught → Elementary
    TV→elem tv = Tr.Along.agree inL
      (λ n t u δ → cong₂ _∈ˢ_ (tm-agree n t δ) (tm-agree n u δ))
      (λ n t u δ → cong₂ _≈ˢ_ (tm-agree n t δ) (tm-agree n u δ))
      tv
```

<!--en-->
## Closing the starting set under least witnesses
<!--zh-->
## 对最小见证闭合起始集合
<!--ja-->
## 始集合を最小の証人について閉じる
<!--/-->

<!--en-->
A starting set `X` is assumed to lie in the stage, and the index `α` is assumed to contain the empty set. The empty set belongs to `Lset α` because `∅` lies in the ordinal `α` and is coded in the base layer.
<!--zh-->
假设起始集 `X` 包含于该层，并假设指数 `α` 包含空集。空集属于 `Lset α`，因为 `∅` 位于序数 `α` 中，且在基层有编码。
<!--ja-->
始集合 `X` がこの段階に含まれ、指数 `α` が空集合を含むと仮定します。空集合が `Lset α` に属するのは、`∅` が順序数 `α` の中にあり、基底の層で符号化されているからです。
<!--/-->

```agda
  module Hull (X : S) (X⊆L : (x : S) → ⟨ x ∈ˢ X ⟩ → ⟨ x ∈ˢ Lset α ⟩)
               (∅∈α : ⟨ ∅ ∈ˢ α ⟩) where
    ∅∈Lsetα : ⟨ ∅ ∈ˢ Lset α ⟩
    ∅∈Lsetα = Lset-in α ∅ ∅ ∅∈α (∅∈𝒟ₒ ∅)

```

<!--en-->
The embedding of the starting set's presentation lands in the stage carrier: each index names a member of `X`, and the containment hypothesis certifies that this member lies in the stage `Lset α`.
<!--zh-->
起始集合呈现的嵌入落入层载体：每个索引指名 `X` 的一个成员，包含假设证明该成员属于层 `Lset α`。
<!--ja-->
始集合の提示の埋め込みは、段階の台の中に着地します。各索引は `X` の要素を名指し、包含の仮定がその要素が段階 `Lset α` に属することを証明します。
<!--/-->

```agda
    inStg : ⟪ X ⟫ → SL
    inStg m = ⟪ X ⟫↪ m , X⊆L (⟪ X ⟫↪ m) (member X m)

```

<!--en-->
The term algebra is instantiated at the restricted structure of the stage: its carrier is mapped into the universe by the first projection, the witness search uses the stage's well order, the junk value is the empty set, and the base codes are indexed by the presentation of `X`. The hull now grows inside the stage.
<!--zh-->
项代数在层的受限结构处实例化：其载体经第一投影映入宇宙，见证搜索使用层的良序，垃圾值取空集，基码以 `X` 的呈现为索引。壳就此在层内生长。
<!--ja-->
項代数は、段階の制限された構造のもとで具体化されます。台は第一射影で宇宙へ写され、証人の探索は段階の整列順序を使い、既定の値は空集合、基のコードは `X` の提示で索引づけられます。包はこうして段階の中で育ちます。
<!--/-->

```agda
    module T = TermAlgebra AbsL.𝒮M fst wL (∅ , ∅∈Lsetα) {K = ⟪ X ⟫} inStg
    open T using ( Code; base; val; Hull; inHull )

```

<!--en-->
The hull lies in the stage: every member is the value of some code, and every code value is a member of the stage `Lset α` by the term algebra's own typing. The proof eliminates the truncated presentation and transports along the identification.
<!--zh-->
壳位于层内：每个成员都是某个码的取值，而码的取值依项代数自身的类型都属于层 `Lset α`。证明消去截断的呈现，并沿该同一视搬运。
<!--ja-->
包は段階の中にあります。すべての要素はあるコードの値であり、コードの値は項代数自身の型づけによって段階 `Lset α` の要素です。証明は切り詰められた提示を消去し、同一視に沿って輸送します。
<!--/-->

```agda
    Hull⊆L : (x : S) → ⟨ x ∈ˢ Hull ⟩ → ⟨ x ∈ˢ Lset α ⟩
    Hull⊆L x x∈H = PT.rec (snd (x ∈ˢ Lset α)) go x∈H
      where
      go : Σ[ c ∈ Code ] (fst (val c) ≡ x) → ⟨ x ∈ˢ Lset α ⟩
      go (c , q) = subst (λ z → ⟨ z ∈ˢ Lset α ⟩) q (snd (val c))
```

<!--en-->
Membership reads back only as truncated existence: a member of the hull is the value of some code, with no code selected. This is the honest form of the presentation, since different codes may evaluate alike.
<!--zh-->
隶属只能读回为截断的存在：壳的成员是某个码的取值，但没有选定哪个码。这是呈现的诚实形式，因为不同码可能求值相同。
<!--ja-->
所属は、切り詰められた存在としてしか読み戻せません。包の要素はあるコードの値ですが、コードは選ばれません。異なるコードが同じ値に評価しうるので、これが提示の正直な形です。
<!--/-->

```agda
    hull-member : (x : S) → ⟨ x ∈ˢ Hull ⟩
                → ∥ Σ[ c ∈ Code ] (fst (val c) ≡ x) ∥₁
    hull-member x x∈H = x∈H

```

<!--en-->
In the other direction no truncation is needed: the value of every code is a member, by the presentation's own introduction rule.
<!--zh-->
另一方向无需截断：由呈现自身的引入规则，每个码的取值都是成员。
<!--ja-->
逆方向には切り詰めは要りません。提示自身の導入規則により、どのコードの値も要素です。
<!--/-->

```agda
    val-in-Hull : (c : Code) → ⟨ fst (val c) ∈ˢ Hull ⟩
    val-in-Hull c = inHull c

```

<!--en-->
The starting set enters the hull member by member. A member `x` of `X` is presented by an index, and the fiber of the presentation at `x` returns that index.
<!--zh-->
起始集合逐成员进入壳。`X` 的成员 `x` 由一个索引呈现，呈现它在 `x` 处的纤维返回该索引。
<!--ja-->
始集合は要素ごとに包に入ります。`X` の要素 `x` は索引によって提示され、`x` における提示の繊維がその索引を返します。
<!--/-->

```agda
    module XInM (x : S) (x∈X : ⟨ x ∈ˢ X ⟩) where
      mx : ⟪ X ⟫
      mx = fiber X x∈X .fst

```

<!--en-->
The fiber carries the identification of the presented element with `x`, which is the transport used to move memberships along.
<!--zh-->
纤维携带被呈现元素与 `x` 的同一视，这正是沿之搬运隶属的通道。
<!--ja-->
繊維は、提示された要素を `x` と同一視するパスを運び、所属を運ぶときの道すじになります。
<!--/-->

```agda
      x≡val : ⟪ X ⟫↪ mx ≡ x
      x≡val = fiber X x∈X .snd

```

<!--en-->
The base code at that index evaluates to the presented element, hence to `x`; the transport lands membership of `x` in the hull.
<!--zh-->
该索引处的基码求值为被呈现元素，即 `x`；搬运把 `x` 在壳中的隶属落定。
<!--ja-->
その索引での基のコードは、提示された要素、すなわち `x` へ評価されます。輸送によって、`x` の包の中の所属が着地します。
<!--/-->

```agda
      inM : ⟨ x ∈ˢ Hull ⟩
      inM = subst (λ z → ⟨ z ∈ˢ Hull ⟩) x≡val (inHull (base mx))

```

<!--en-->
Assembled once, the containment of the starting set in the hull becomes a single lemma.
<!--zh-->
组装一次后，起始集合含于壳即成单条引理。
<!--ja-->
一度組み立てれば、始集合の包への包含は一つの補題になります。
<!--/-->

```agda
    X⊆M : (x : S) → ⟨ x ∈ˢ X ⟩ → ⟨ x ∈ˢ Hull ⟩
    X⊆M x x∈X = XInM.inM x x∈X
```

<!--en-->
## Satisfaction is invariant under the collapse isomorphism
<!--zh-->
## 满足关系在塌缩同构下不变
<!--ja-->
## 充足関係は崩壊同型で不変である
<!--/-->

<!--en-->
To compare satisfaction before and after an isomorphism, fix sets `M`, `PM`, and a carrier map `p` from members of `M` to members of `PM`.
<!--zh-->
为比较同构前后的满足关系，固定集合 `M`、`PM`，以及把 `M` 的成员映到 `PM` 的成员的载体映射 `p`。
<!--ja-->
同型の前後で充足関係を比較するため、集合 `M`、`PM` と、`M` の要素を `PM` の要素へ送る台の写像 `p` を固定します。
<!--/-->

```agda
module IsoInv (M : S) (PM : S)
  (p : S → S)
  (p∈ : (x : S) → ⟨ x ∈ˢ M ⟩ → ⟨ p x ∈ˢ PM ⟩)
```

<!--en-->
Besides the closure condition `p∈`, the map `p` satisfies four hypotheses. `iso-fwd` preserves membership, `iso-bwd` reflects it, and the last two parameters state injectivity on `M` and surjectivity onto the target `PM`.
<!--zh-->
除封闭条件 `p∈` 外，映射 `p` 还满足四条假设。`iso-fwd` 保持隶属，`iso-bwd` 反映隶属，最后两个参数陈述 `M` 上的单射性与到目标 `PM` 上的满射性。
<!--ja-->
閉性の条件 `p∈` に加えて、写像 `p` には四つの仮定を置きます。`iso-fwd` は所属を保存し、`iso-bwd` は所属を反映し、最後の二つの引数は `M` 上の単射性と終域 `PM` への全射性を述べます。
<!--/-->

```agda
  (iso-fwd : (x y : S) (x∈ : ⟨ x ∈ˢ M ⟩) (y∈ : ⟨ y ∈ˢ M ⟩)
           → ⟨ y ∈ˢ x ⟩ → ⟨ p y ∈ˢ p x ⟩)
  (iso-bwd : (x y : S) (x∈ : ⟨ x ∈ˢ M ⟩) (y∈ : ⟨ y ∈ˢ M ⟩)
           → ⟨ p y ∈ˢ p x ⟩ → ⟨ y ∈ˢ x ⟩)
  (p-inj : (x y : S) (x∈ : ⟨ x ∈ˢ M ⟩) (y∈ : ⟨ y ∈ˢ M ⟩)
```

<!--en-->
The map `p` is injective on `M` and merely surjective onto `PM`. With preservation and reflection, these are exactly the data of a membership isomorphism between the two structures.
<!--zh-->
映射 `p` 在 `M` 上单射，且仅仅地满射到 `PM`。与保持、反映合在一起，这恰是两个结构之间隶属同构的全部数据。
<!--ja-->
写像 `p` は `M` 上で単射であり、`PM` へ単に全射です。保存と反映と合わせて、これらはまさに二つの構造の間の所属の同型のデータです。
<!--/-->

```agda
          → p x ≡ p y → x ≡ y)
  (surj : (z : S) (z∈ : ⟨ z ∈ˢ PM ⟩)
        → ∥ Σ[ y ∈ S ] (⟨ y ∈ˢ M ⟩ × (p y ≡ z)) ∥₁)
  where

```

<!--en-->
The source carrier pairs each element of `M` with its membership proof, as in every restricted structure of the chapter.
<!--zh-->
源载体把 `M` 的每个元素与其隶属证明配对，与本章各受限结构相同。
<!--ja-->
源の台は、`M` の各要素とその所属の証明を対にします。本章のどの制限された構造とも同じです。
<!--/-->

```agda
  SM : Type (ℓ-suc ℓ)
  SM = Σ[ x ∈ S ] ⟨ x ∈ˢ M ⟩

```

<!--en-->
The target carrier pairs each element of `PM` with its membership proof.
<!--zh-->
目标载体把 `PM` 的每个元素与其隶属证明配对。
<!--ja-->
終域の台は、`PM` の各要素とその所属の証明を対にします。
<!--/-->

```agda
  SPM : Type (ℓ-suc ℓ)
  SPM = Σ[ x ∈ S ] ⟨ x ∈ˢ PM ⟩

```

<!--en-->
The isomorphism lifts to the paired carriers: apply `p` to the underlying element and certify membership in the image.
<!--zh-->
同构提升到配对载体：对底层元素施加 `p`，并证明其在像中的隶属。
<!--ja-->
同型は、対になった台へ持ち上がります。底の要素に `p` を施し、像の中での所属を証明するのです。
<!--/-->

```agda
  g : SM → SPM
  g m = p (fst m) , p∈ (fst m) (snd m)

```

<!--en-->
The source semantics interprets terms and formulas in the restriction to `M`.
<!--zh-->
源语义在限制于 `M` 的结构中解释项与公式。
<!--ja-->
始域の意味論は、`M` に制限した構造で項と論理式を解釈します。
<!--/-->

```agda
  module SemM = FOL.Semantics (𝒮ᵥ ↾ (λ x → x ∈ˢ M))
    using ( module At )
  module SemPM = FOL.Semantics (𝒮ᵥ ↾ (λ x → x ∈ˢ PM))
    using ( module At )
  open module Mse = SemM.At SM id public renaming ( _⊨_ to _⊨ᵐ_ ; ⟦_⟧ to ⟦_⟧ᵐ )
```

<!--en-->
The target semantics interprets the mapped terms and formulas in the restriction to `PM`.
<!--zh-->
目标语义在限制于 `PM` 的结构中解释映射后的项与公式。
<!--ja-->
終域の意味論は、`PM` に制限した構造で写された項と論理式を解釈します。
<!--/-->

```agda
  open module Pse = SemPM.At SPM id public renaming ( _⊨_ to _⊨ᵖᵐ_ ; ⟦_⟧ to ⟦_⟧ᵖᵐ )

```

<!--en-->
Surjectivity promotes to the paired carriers: every element of the target `PM` is the image of some point of `M`, and the equality of underlying elements lifts to an equality of pairs because membership in `PM` is a proposition.
<!--zh-->
满射提升到配对载体：目标 `PM` 的每个元素都是 `M` 中某点的像，而底层元素的相等因属于 `PM` 是命题而提升为对的相等。
<!--ja-->
全射は対になった台へ持ち上がります。終域 `PM` のすべての要素は `M` のある点の像であり、底の要素の等しさは、`PM` への所属が命題であるため、対の等しさへ持ち上がります。
<!--/-->

```agda
  surj' : (p' : SPM) → ∥ Σ[ q ∈ SM ] (g q ≡ p') ∥₁
  surj' (z , z∈) = PT.map (λ { (y , y∈ , e) →
    (y , y∈) , Σ≡Prop (λ w → (w ∈ˢ PM) .snd) e }) (surj z z∈)

```

<!--en-->
The general satisfaction-transfer theorem now applies to the predicates of membership in `M` and `PM`; preservation and reflection supply its membership atom.
<!--zh-->
一般的满足关系移送定理现可施用于属于 `M` 与属于 `PM` 的谓词；隶属的保持与反映给出其隶属原子情形。
<!--ja-->
一般の充足関係の移送定理を、`M` と `PM` への所属述語に適用できます。所属の保存と反映が、その所属原子式の場合を与えます。
<!--/-->

```agda
  module Tr = SatTransfer (λ x → x ∈ˢ M) (λ x → x ∈ˢ PM)

```

<!--en-->
The map `p` is applied pointwise to environments, so lookups reduce one index at a time.
<!--zh-->
映射 `p` 逐索引地作用于环境，因此查找一次一格化归。
<!--ja-->
写像 `p` は環境に各索引ごとに施されるので、参照は一度に一つずつ簡約できます。
<!--/-->

```agda
  private
    lookup-g : {n : ℕ} (i : Fin n) (δ : SM ^ n)
             → p (fst (lookup i δ)) ≡ fst (lookup i (map g δ))
    lookup-g zero (m ∷ δ) = refl
    lookup-g (suc i) (m ∷ δ) = lookup-g i δ
```

<!--en-->
Terms agree under the map `p`: applying `p` to the value of a term of `M` equals evaluating the mapped term at the mapped environment. Constants are fixed; variables follow the lookups. The membership atoms can now be stated.
<!--zh-->
项在映射 `p` 下相一致：对 `M` 的项的值施加 `p`，等于在映射环境处求值映射后的项。常元固定，变元随查找而定。隶属原子由此可陈述。
<!--ja-->
項は写像 `p` のもとで一致します。`M` の項の値に `p` を施すことは、写された項を写された環境で評価することと等しくなります。定数は固定的で、変数は参照に従います。所属の原子式がここで述べられます。
<!--/-->

```agda

    tm-agree : {n : ℕ} (t : Term SM n) (δ : SM ^ n)
             → p (fst (⟦ t ⟧ᵐ δ)) ≡ fst (⟦ mapTm g t ⟧ᵖᵐ (map g δ))
    tm-agree (con m) δ = refl
    tm-agree (var i) δ = lookup-g i δ
    at∈ : (n : ℕ) (t u : Term SM n) (δ : SM ^ n)
```

<!--en-->
Membership of atomic terms transfers in both directions: forward, the proof transports inner membership along the term equalities and then applies `iso-fwd`, the preservation of membership.
<!--zh-->
原子项的隶属双向转移：正向把内部隶属沿项等式搬运，再施加保持隶属的 `iso-fwd`。
<!--ja-->
原子項の所属は両方向に移ります。順方向は、内側の所属を項の等式に沿って運び、所属を保存する `iso-fwd` に渡します。
<!--/-->

```agda
        → (δ ⊨ᵐ (t ∈̇ u)) ≡ (map g δ ⊨ᵖᵐ mapFo g (t ∈̇ u))
    at∈ n t u δ = ⇔toPath
      (λ h → subst (λ z → ⟨ fst (⟦ mapTm g t ⟧ᵖᵐ (map g δ)) ∈ˢ z ⟩) (tm-agree u δ)
        (subst (λ z → ⟨ z ∈ˢ p (fst (⟦ u ⟧ᵐ δ)) ⟩) (tm-agree t δ)
          (iso-fwd (fst (⟦ u ⟧ᵐ δ)) (fst (⟦ t ⟧ᵐ δ)) (snd (⟦ u ⟧ᵐ δ))
```

<!--en-->
The forward transport lands at membership after applying `p`; backward reflects that membership through the isomorphism, restoring the inner membership along the term equalities.
<!--zh-->
正向搬运落在施加 `p` 后的隶属上；反向经由同构反映该隶属，沿项等式恢复内部的隶属。
<!--ja-->
順方向の輸送は、`p` を施した後の所属に着地します。逆方向は、同型を通してその所属を反映し、項の等式に沿って内側の所属を復元します。
<!--/-->

```agda
            (snd (⟦ t ⟧ᵐ δ)) h)))
      (λ h → iso-bwd (fst (⟦ u ⟧ᵐ δ)) (fst (⟦ t ⟧ᵐ δ)) (snd (⟦ u ⟧ᵐ δ))
        (snd (⟦ t ⟧ᵐ δ))
        (subst (λ z → ⟨ p (fst (⟦ t ⟧ᵐ δ)) ∈ˢ z ⟩) (sym (tm-agree u δ))
          (subst (λ z → ⟨ z ∈ˢ fst (⟦ mapTm g u ⟧ᵖᵐ (map g δ)) ⟩)
```

<!--en-->
The backward direction closes the membership clause: reflection through the isomorphism, guided by the term congruences, returns exactly the inner membership. The equality atom and the witness principle are handled by the remaining hypotheses.
<!--zh-->
反向闭合隶属子句：经同构、循项同余的反映，恰好返回内部的隶属。相等原子与见证原理由其余假设处理。
<!--ja-->
逆方向が所属の節を閉じます。項の等式に導かれた同型を通した反映が、内側の所属をちょうど返します。等号の原子式と証人の原理は、残りの仮定が扱います。
<!--/-->

```agda
            (sym (tm-agree t δ)) h)))

```

<!--en-->
Equality of atomic terms transfers by applying the collapse to both sides of the equation. The forward direction takes an equality of values in `M`, applies `p` via `cong`, and transports each side to its mapped term by the term congruences.
<!--zh-->
原子项的等式通过把塌缩施加于等式两侧而转移。正向取 `M` 中值的等式，经 `cong` 施加 `p`，再由项同约把两侧分别搬运到映射后的项。
<!--ja-->
アトムの項の等号は、等式の両辺に崩壊を施すことで移ります。順方向は、`M` における値の等式を取り、`cong` で `p` を施し、項の同約によって両辺を写された項へ運びます。
<!--/-->

```agda
    at≐ : (n : ℕ) (t u : Term SM n) (δ : SM ^ n)
        → (δ ⊨ᵐ (t ≐ u)) ≡ (map g δ ⊨ᵖᵐ mapFo g (t ≐ u))
    at≐ n t u δ = ⇔toPath
      (λ h → subst (λ z → z ≡ fst (⟦ mapTm g u ⟧ᵖᵐ (map g δ))) (tm-agree t δ)
        (subst (λ z → p (fst (⟦ t ⟧ᵐ δ)) ≡ z) (tm-agree u δ) (cong p h)))
```

<!--en-->
The backward direction is where injectivity earns its place: the collapsed sides are equal, and `p-inj` recovers the equality of the original values from it. Together the two directions turn the equality atom into a path of propositions.
<!--zh-->
反向正是单射性发挥作用之处：塌缩后的两侧相等，`p-inj` 由此恢复原值的相等。两个方向合起来，把相等原子变成命题之间的路径。
<!--ja-->
逆方向は、単射性が活きる場所です。崩壊した両辺が等しいことから、`p-inj` がもとの値の等しさを取り戻します。二つの向きで、等号のアトムが命題の間のパスになります。
<!--/-->

```agda
      (λ h → p-inj (fst (⟦ t ⟧ᵐ δ)) (fst (⟦ u ⟧ᵐ δ)) (snd (⟦ t ⟧ᵐ δ))
        (snd (⟦ u ⟧ᵐ δ))
        (subst (λ z → z ≡ p (fst (⟦ u ⟧ᵐ δ))) (sym (tm-agree t δ))
          (subst (λ z → fst (⟦ mapTm g t ⟧ᵖᵐ (map g δ)) ≡ z)
            (sym (tm-agree u δ)) h)))
```

<!--en-->
The witness principle is produced from surjectivity. An outer witness `p'` in the image is, merely, the collapse of some `q` in `M`; transporting the satisfaction along that identification returns the inner witness together with its satisfaction in the image.
<!--zh-->
见证原理由满射产出。像中的外部见证 `p'` 仅仅是 `M` 中某个 `q` 的塌缩；沿该同一视搬运满足，即得内部见证及其在像中的满足。
<!--ja-->
証人の原理は全射から作られます。像の中の外側の証人 `p'` は、単に、`M` のある `q` の崩壊です。その同一視に沿って充足を運ぶと、内側の証人と、像の中での充足が得られます。
<!--/-->

```agda
    wit : Tr.Witness g
    wit n ψ δ h = PT.rec squash₁
      (λ { (p' , hp) → PT.map
        (λ { (q , gq≡p) →
          q , subst (λ z → ⟨ (z ∷ map g δ) ⊨ᵖᵐ mapFo g ψ ⟩) (sym gq≡p) hp })
```

<!--en-->
The surjectivity lemma supplies the preimage, and the two transports compose into the witness principle of the transfer.
<!--zh-->
满射引理供给原像，两次搬运复合成移送的见证原理。
<!--ja-->
全射の補題が逆像を供給し、二つの輸送が合わさって、移送の証人の原理になります。
<!--/-->

```agda
        (surj' p') }) h

```

<!--en-->
With the atomic cases and witness principle in place, the shared induction proves that satisfaction is preserved when environments are mapped by the collapse and constants are relabelled by `g`.
<!--zh-->
原子情形与见证原理就位后，共享归纳证明：环境沿塌缩映射、常元沿 `g` 重标记时，满足关系保持不变。
<!--ja-->
原子の場合と証人原理がそろうと、共有の帰納により、環境を崩壊で写し、定数を `g` で付け替えても充足関係が保たれることが分かります。
<!--/-->

```agda
  agree : (n : ℕ) (φ : Formula SM n) (δ : SM ^ n)
        → (δ ⊨ᵐ φ) ≡ (map g δ ⊨ᵖᵐ mapFo g φ)
  agree = Tr.Along.agree g at∈ at≐ wit

```

<!--en-->
The agreement is recorded in two one-directional forms for later composition. Forward, inner satisfaction yields satisfaction of the mapped formula at the mapped environment.
<!--zh-->
一致性以两个单向形式记录备用。正向：内部的满足给出映射环境上映射公式的满足。
<!--ja-->
一致は、後で合成するために二つの片方向の形で記録されます。順方向には、内側の充足から、写された環境での写された論理式の充足が得られます。
<!--/-->

```agda
  iso-inv : (n : ℕ) (φ : Formula SM n) (δ : SM ^ n)
          → ⟨ δ ⊨ᵐ φ ⟩ → ⟨ map g δ ⊨ᵖᵐ mapFo g φ ⟩
  iso-inv n φ δ = subst ⟨_⟩ (agree n φ δ)

```

<!--en-->
Backward returns outer satisfaction to inner satisfaction. The chapter then instantiates this invariance at the collapse of a set `X` with extensionality, opening the collapse with its membership isomorphism and its injectivity.
<!--zh-->
反向把外部的满足送回内部的满足。随后本章在有外延性的集合 `X` 的塌缩处实例化这一不变性，打开塌缩及其隶属同构与单射性。
<!--ja-->
逆方向は、外側の充足を内側の充足へ戻します。本章は次に、外延性をもつ集合 `X` の崩壊のもとでこの不変性を具体化し、所属の同型と単射性を伴って崩壊を開きます。
<!--/-->

```agda
  iso-inv-bwd : (n : ℕ) (φ : Formula SM n) (δ : SM ^ n)
              → ⟨ map g δ ⊨ᵖᵐ mapFo g φ ⟩ → ⟨ δ ⊨ᵐ φ ⟩
  iso-inv-bwd n φ δ = subst ⟨_⟩ (sym (agree n φ δ))
module CollapseIso (X : S) (Xext : isExt X) where
  module C = Collapse X using ( module InjExt; π; πX; πX-intro; πX-member )
```

<!--en-->
Extensionality of `X` is exactly what the collapse needs: the restricted structure is injective, and the isomorphism between membership on `X` and membership on the collapse becomes available.
<!--zh-->
`X` 的外延性正是塌缩所需：限制后的结构单射，且 `X` 上隶属与塌缩像上隶属之间的同构随即可用。
<!--ja-->
`X` の外延性こそ、崩壊が必要とするものです。制限された構造は単射となり、`X` の上の所属と崩壊の像の上の所属の間の同型が使えるようになります。
<!--/-->

```agda
  module CI = C.InjExt Xext using ( iso; π-inj )

```

<!--en-->
The target carrier is the collapse image `πX`; its points are precisely the collapse values of members of `X`.
<!--zh-->
目标载体是塌缩像 `πX`；它的点恰是 `X` 的成员之塌缩值。
<!--ja-->
目標の台は崩壊像 `πX` であり、その点はちょうど `X` の要素の崩壊値です。
<!--/-->

```agda
  PM : S
  PM = C.πX

```

<!--en-->
The map `p` sends each set to its Mostowski collapse value.
<!--zh-->
映射 `p` 把每个集合送到其 Mostowski 塌缩值。
<!--ja-->
写像 `p` は各集合をその Mostowski 崩壊値へ送ります。
<!--/-->

```agda
  p : S → S
  p = C.π

```

<!--en-->
Members of `X` land in the image, by the collapse's own introduction rule for the image.
<!--zh-->
`X` 的成员落入像中，这由塌缩对像自身的引入规则给出。
<!--ja-->
`X` の要素は像の中に着地します。これは、像に対する崩壊自身の導入規則によるものです。
<!--/-->

```agda
  p∈ : (x : S) → ⟨ x ∈ˢ X ⟩ → ⟨ p x ∈ˢ PM ⟩
  p∈ = C.πX-intro

```

<!--en-->
Membership is preserved forward along the collapse: if `y` is a member of `x` in `X`, then the collapse of `y` is a member of the collapse of `x`. This is the first component of the membership isomorphism.
<!--zh-->
隶属沿塌缩正向保持：若在 `X` 中 `y` 属于 `x`，则 `y` 的塌缩属于 `x` 的塌缩。这是隶属同构的第一个分量。
<!--ja-->
所属は崩壊に沿って順方向に保存されます。`X` の中で `y` が `x` に属するなら、`y` の崩壊は `x` の崩壊に属します。これが所属の同型の第一成分です。
<!--/-->

```agda
  iso-fwd : (x y : S) (x∈ : ⟨ x ∈ˢ X ⟩) (y∈ : ⟨ y ∈ˢ X ⟩)
          → ⟨ y ∈ˢ x ⟩ → ⟨ p y ∈ˢ p x ⟩
  iso-fwd x y x∈ y∈ = CI.iso x y x∈ y∈ .fst

```

<!--en-->
Membership reflects backward as well: a collapsed membership can only have arisen from a genuine membership in `X`. The two directions together say the collapse is faithful on membership.
<!--zh-->
隶属也反向反映：塌缩后的隶属只能来自 `X` 中真实的隶属。两个方向合起来说明塌缩对隶属是忠实的。
<!--ja-->
所属は逆方向にも反映されます。崩壊された所属は、`X` の中の本当の所属から生じたものに限ります。二つの向き合わせて、崩壊が所属について忠実であることが言えます。
<!--/-->

```agda
  iso-bwd : (x y : S) (x∈ : ⟨ x ∈ˢ X ⟩) (y∈ : ⟨ y ∈ˢ X ⟩)
          → ⟨ p y ∈ˢ p x ⟩ → ⟨ y ∈ˢ x ⟩
  iso-bwd x y x∈ y∈ = CI.iso x y x∈ y∈ .snd

```

<!--en-->
The collapse is injective on `X`: two members with equal collapses are equal. Faithfulness on membership plus injectivity are the two halves of the isomorphism on elements.
<!--zh-->
塌缩在 `X` 上单射：塌缩相等的两个成员相等。对隶属的忠实加上单射性，构成元素层面同构的两半。
<!--ja-->
崩壊は `X` の上で単射です。崩壊が等しい二つの要素は等しい。所属への忠実さと単射性が、要素の上の同型の二つの半分です。
<!--/-->

```agda
  p-inj : (x y : S) (x∈ : ⟨ x ∈ˢ X ⟩) (y∈ : ⟨ y ∈ˢ X ⟩)
        → p x ≡ p y → x ≡ y
  p-inj = CI.π-inj

```

<!--en-->
Every point of the image comes from a member of `X`: surjectivity is truncated, so it asserts the existence of a preimage without choosing one, which is exactly the form the witness principle consumes.
<!--zh-->
像的每点都来自 `X` 的成员：满射是截断的，只主张原像存在而不选定它，这正是见证原理所消耗的形式。
<!--ja-->
像のすべての点は `X` の要素から来ます。全射は切り詰められており、証人を選ばずに逆像の存在を主張します。これがまさに、証人の原理が消費する形です。
<!--/-->

```agda
  surj : (z : S) (z∈ : ⟨ z ∈ˢ PM ⟩)
       → ∥ Σ[ y ∈ S ] (⟨ y ∈ˢ X ⟩ × (p y ≡ z)) ∥₁
  surj = C.πX-member

```

<!--en-->
For the extensional set `X`, collapse preserves and reflects membership, is injective on `X`, and covers every point of `πX`.
<!--zh-->
对外延集合 `X`，塌缩保持并反映隶属，在 `X` 上单射，且覆盖 `πX` 的每个点。
<!--ja-->
外延的な集合 `X` では、崩壊は所属を保存かつ反映し、`X` 上で単射であり、`πX` のすべての点を覆います。
<!--/-->

```agda
  module I = IsoInv X PM p p∈ iso-fwd iso-bwd p-inj surj
    using ( SM; SPM; g; surj'; iso-inv; iso-inv-bwd; _⊨ᵐ_; _⊨ᵖᵐ_; ⟦_⟧ᵐ; ⟦_⟧ᵖᵐ )
```

<!--en-->
## The Skolem hull is elementary
<!--zh-->
## Skolem 壳是初等的
<!--ja-->
## Skolem 包は初等的である
<!--/-->

<!--en-->
Hence satisfaction transfers in both directions between the structure on `X` and the structure on `πX`.
<!--zh-->
因此，满足关系可在 `X` 上的结构与 `πX` 上的结构之间双向搬运。
<!--ja-->
したがって、`X` 上の構造と `πX` 上の構造の間で充足関係を双方向に移せます。
<!--/-->

```agda
module HullElemDown (α : S) (ordα : IsOrd α)
  (X : S) (X⊆L : (x : S) → ⟨ x ∈ˢ X ⟩ → ⟨ x ∈ˢ Lset α ⟩) (∅∈α : ⟨ ∅ ∈ˢ α ⟩) where

```

<!--en-->
Applied to the Skolem hull inside `Lset α`, this reduces elementarity to the Tarski-Vaught witness condition.
<!--zh-->
把这一点用于 `Lset α` 内的 Skolem 壳，初等性便归结为 Tarski-Vaught 见证条件。
<!--ja-->
これを `Lset α` 内の Skolem 包に適用すると、初等性は Tarski-Vaught の証人条件に帰着します。
<!--/-->

```agda
  module ASt = AtStage α ordα using ( module AbsL; module AtM; module Hull; SL )
  module H = ASt.Hull X X⊆L ∅∈α
    using ( module T; Hull⊆L; hull-member )
  M : S
  M = H.T.Hull
```

<!--en-->
The substructure machinery is instantiated at the hull, and its formulas receive an ambient reading. Every element of the hull's carrier has a code: the code exists by truncated presentation, and the identification of value with inclusion is promoted by the propositionhood of stage membership.
<!--zh-->
子结构机制在壳处实例化，其公式获得一个外围读法。壳载体的每个元素都有码：码由截断的呈现给出存在，而「取值等于包含」的同一视借层隶属的命题值性提升。
<!--ja-->
部分構造の仕組みは包のもとで具体化され、その論理式には周囲の読みが与えられます。包の台のすべての要素にはコードがあります。コードは切り詰められた提示によって存在し、値と包含の同一視は、段階の所属の命題値性によって持ち上がります。
<!--/-->

```agda
  module A = ASt.AtM M H.Hull⊆L using ( Elementary; SM; module SemM; TV→elem; inL )
  module Mse = A.SemM.At A.SM id using ( _⊨_ )
  codeOf : (q : A.SM) → ∥ Σ[ c ∈ H.T.Code ] (H.T.val c ≡ A.inL q) ∥₁
  codeOf q = PT.map (λ { (c , e) → c , Σ≡Prop (λ z → (z ∈ˢ Lset α) .snd) e })
    (H.hull-member (fst q) (snd q))
```

<!--en-->
Codes lift from single elements to finite environments: the empty environment is coded by the empty vector, and the recursive case pairs one new code with the codes already built.
<!--zh-->
码从单个元素提升到有限环境：空环境由空向量编码，递归情形把一个新码与已建好的码并列。
<!--ja-->
コードは、一つの要素から有限の環境へ持ち上がります。空の環境は空のベクトルで符号化され、再帰の場合は、新しいコードを、すでに作られたコードの列に加えます。
<!--/-->

```agda

  codeEnv : {n : ℕ} (δ : Vec A.SM n)
          → ∥ Σ[ ds ∈ Vec H.T.Code n ]
               (map H.T.val ds ≡ map A.inL δ) ∥₁
  codeEnv [] = ∣ [] , refl ∣₁
  codeEnv (q ∷ δ) = PT.map2
```

<!--en-->
The cons case composes the two truncated existences into one: the extended vector of codes evaluates exactly to the included environment.
<!--zh-->
添入情形把两个截断存在复合成一个：加长后的码向量求值恰为包含后的环境。
<!--ja-->
構成の場合は、二つの切り詰められた存在を一つに合成します。延びたコードのベクトルの評価は、包含された環境にちょうど等しくなります。
<!--/-->

```agda
    (λ { (c , ec) (ds , eds) → c ∷ ds , cong₂ _∷_ ec eds })
    (codeOf q) (codeEnv δ)

```

<!--en-->
Componentwise mapping also respects concatenation of finite environments. Thus the free-variable values and the values replacing constant occurrences can be combined into one coded environment for the Tarski-Vaught argument.
<!--zh-->
逐分量映射还保持有限环境的拼接。因此，自由变元的取值与替代常元出现的取值可以合并为一个供 Tarski-Vaught 论证使用的编码环境。
<!--ja-->
成分ごとの写像は有限環境の連結も保ちます。したがって、自由変数の値と定数出現を置き換える値を、Tarski-Vaught の議論に用いる一つの符号化環境へまとめられます。
<!--/-->

```agda
  inL-++ : {n m : ℕ} (δ : Vec A.SM n) (σ : Vec A.SM m)
          → map A.inL (δ ++ σ) ≡ map A.inL δ ++ map A.inL σ
  inL-++ [] σ = refl
  inL-++ (q ∷ δ) σ = cong (A.inL q ∷_) (inL-++ δ σ)
  tv : (n : ℕ) (ψ : Formula A.SM (suc n)) (δ : Vec A.SM n)
```

<!--en-->
The statement is the Tarski-Vaught condition itself: if the stage satisfies an existential at the included environment, then, merely, some element of the hull satisfies the matrix there. The proof eliminates the coding of the environment and passes to the search closure.
<!--zh-->
该陈述即 Tarski-Vaught 条件本身：若层在包含后的环境处满足一个存在式，则仅仅地有壳中某元素在该处满足矩阵。证明先消去环境的编码，再进入搜索闭合。
<!--ja-->
この主張は Tarski-Vaught の条件そのものです。段階が包含された環境のもとで存在の論理式を充足するなら、単に、包のある要素がそこで行列を充足します。証明はまず環境の符号化を消去し、探索の閉包へ進みます。
<!--/-->

```agda
     → ⟨ map A.inL δ ASt.AbsL.⊨ᵐ (mapFo A.inL (∃̇ ψ)) ⟩
     → ∥ Σ[ q ∈ A.SM ]
          ⟨ (A.inL q ∷ map A.inL δ) ASt.AbsL.⊨ᵐ (mapFo A.inL ψ) ⟩ ∥₁
  tv n ψ δ h = PT.rec squash₁ takeEnvironment (codeEnv params)
    where
```

<!--en-->
Parameter abstraction replaces every constant occurrence by an additional free variable. The resulting formula has empty constant domain and arity increased by `countFo ψ`, while retaining the full logical structure of `ψ`.
<!--zh-->
参数抽象把每个常元出现替换为一个额外自由变元。所得公式的常元域为空，元数增加 `countFo ψ`，同时保留 `ψ` 的完整逻辑结构。
<!--ja-->
パラメータ抽象は各定数出現を追加の自由変数に置き換えます。得られる論理式は定数領域が空で、アリティが `countFo ψ` だけ増えますが、`ψ` の論理構造はすべて保たれます。
<!--/-->

```agda
    bodyFo : Formula (⊥* {ℓ}) (suc (n + countFo ψ))
    bodyFo = absFo ψ

```

<!--en-->
The environment for the abstracted body is the old environment followed by the constant occurrences: the abstraction turns constants into extra free variables, so one vector carries everything the search needs.
<!--zh-->
抽象后矩阵的环境是原环境后接诸常数出现：抽象把常数变成额外的自由变元，因此一个向量就携带搜索所需的一切。
<!--ja-->
抽象された本体のための環境は、もとの環境に定数の出現を続けたものです。抽象は定数を余分な自由変数に変えるので、一つのベクトルが探索に必要なすべてを運びます。
<!--/-->

```agda
    params : Vec A.SM (n + countFo ψ)
    params = δ ++ constantsFo ψ

```

<!--en-->
Once this combined environment has codes, least-witness closure supplies a hull witness. The semantic identification between the abstracted formula and the original parameterized formula then yields the required Tarski-Vaught witness.
<!--zh-->
一旦这个合并环境有了码，最小见证闭合便给出壳中的见证。再利用抽象公式与原带参公式之间的语义同一视，即得所需的 Tarski-Vaught 见证。
<!--ja-->
この結合環境のコードが得られると、最小証人についての閉性から包内の証人が得られます。抽象後の論理式ともとのパラメータ付き論理式との意味論的同一視により、必要な Tarski-Vaught の証人が従います。
<!--/-->

```agda
    takeEnvironment : Σ[ ds ∈ Vec H.T.Code (n + countFo ψ) ]
                        (map H.T.val ds ≡ map A.inL params)
                    → ∥ Σ[ q ∈ A.SM ]
                         ⟨ (A.inL q ∷ map A.inL δ) ASt.AbsL.⊨ᵐ
                             (mapFo A.inL ψ) ⟩ ∥₁
```

<!--en-->
The search closure runs at the coded environment. Its own evaluation record is then combined with the coding equation and the distribution of the inclusion over concatenation, producing the evaluation of the codes as the included parameters.
<!--zh-->
搜索闭合在编码环境处运行。其自身的求值记录随后与编码等式、以及包含对拼接的分配复合，得到「码的求值即包含后的参数」。
<!--ja-->
探索の閉包は、符号化された環境のもとで走ります。その評価の記録に、符号化の等式と、連結の上の包含の分配を合成すると、コードの評価が包含された引数であることが得られます。
<!--/-->

```agda
    takeEnvironment (ds , eds) = PT.map finish (H.T.closed _ bodyFo ds witness)
      where
      vals-env : H.T.vals ds
               ≡ map A.inL δ ++ map A.inL (constantsFo ψ)
      vals-env = H.T.vals≡map ds ∙ eds ∙ inL-++ δ (constantsFo ψ)
```

<!--en-->
The key identification states that the abstracted body, read in the bare search semantics at the coded environment, is the same proposition as the body read in the stage semantics at the included environment.
<!--zh-->
关键的同一视陈述：抽象矩阵在「编码环境处的裸搜索语义」下的读法，与它在「包含环境处的层语义」下的读法是同一命题。
<!--ja-->
重要な同一視はこう述べます。符号化された環境のもと、裸の探索の意味論で読んだ抽象された本体は、包含された環境のもと、段階の意味論で読んだ本体と同じ命題だと。
<!--/-->

```agda

      body-path : (b : ASt.SL)
                → ((b ∷ H.T.vals ds) H.T.⊨₀ bodyFo)
                ≡ ((b ∷ map A.inL δ) ASt.AbsL.⊨ᵐ mapFo A.inL ψ)
      body-path b =
          cong (λ ε → ε H.T.⊨₀ bodyFo) (cong (b ∷_) vals-env)
```

<!--en-->
The path combines two semantic compatibility laws: `⊨-abs` relates parameter abstraction to the extended environment, and `⊨-map` relates relabelling to the mapped environment.
<!--zh-->
这条路径复合两个语义相容律：`⊨-abs` 把参数抽象联系到扩展环境，`⊨-map` 把重标记联系到映射后的环境。
<!--ja-->
このパスは二つの意味論的な整合則を合成します。`⊨-abs` はパラメータ抽象と拡張環境を結び、`⊨-map` は付け替えと写された環境を結びます。
<!--/-->

```agda
        ∙ sym (⊨-abs ASt.AbsL.𝒮M A.inL ψ
                 (b ∷ map A.inL δ))
        ∙ sym (⊨-map ASt.AbsL.𝒮M A.inL id ψ
                 (b ∷ map A.inL δ))

```

<!--en-->
The stage's satisfaction of the existential is transported along the body path into the bare reading, producing exactly the satisfiability witness the search closure requires.
<!--zh-->
层对存在式的满足沿体路径搬运进裸读法，产出恰是搜索闭合所需的可满足性见证。
<!--ja-->
存在の論理式の段階での充足が、体のパスに沿って裸の読みへ運ばれ、探索の閉包が必要とする充足可能性の証人が、ちょうど生み出されます。
<!--/-->

```agda
      witness : H.T.Sat (n + countFo ψ) bodyFo (H.T.vals ds)
      witness = PT.map (λ { (b , hb) →
        b , subst ⟨_⟩ (sym (body-path b)) hb }) h

```

<!--en-->
The search returns a least witness inside the hull, satisfying the abstracted body at the coded environment. The conversion must turn this into the Tarski-Vaught pair for the original formula.
<!--zh-->
搜索返回壳内满足抽象矩阵的最小见证，其在编码环境处成立。转换须把它变成原公式的 Tarski-Vaught 对。
<!--ja-->
探索は、符号化された環境のもとで抽象された本体を満たす、包の中の最小の証人を返します。変換は、これをもとの論理式に対する Tarski-Vaught の対へ変える必要があります。
<!--/-->

```agda
      finish : Σ[ a ∈ ASt.SL ]
                 ( ⟨ fst a ∈ˢ M ⟩
                 × ⟨ (a ∷ H.T.vals ds) H.T.⊨₀ bodyFo ⟩ )
             → Σ[ q ∈ A.SM ]
                 ⟨ (A.inL q ∷ map A.inL δ) ASt.AbsL.⊨ᵐ (mapFo A.inL ψ) ⟩
```

<!--en-->
The witness is read back into the carrier of the substructure: the underlying set is the hull, and the membership is the one just produced.
<!--zh-->
见证被读回子结构的载体：底层集合即壳，隶属即刚产出者。
<!--ja-->
証人は、部分構造の台へ読み戻されます。底の集合は包であり、所属は今産み出されたものです。
<!--/-->

```agda
      finish (a , a∈H , ha) = q , sat
        where
        q : A.SM
        q = fst a , a∈H

```

<!--en-->
The inclusion of the witness into the stage is the witness itself: the two carriers differ only by the proposition-valued membership proof, which is identified by reflexivity.
<!--zh-->
见证到层的包含就是见证本身：两个载体只差命题值性的隶属证明，而它由自反性等同。
<!--ja-->
証人の段階への包含は、証人そのものです。二つの台は、命題値の所属の証明だけが違い、それは反射性によって同一視されます。
<!--/-->

```agda
        q≡a : A.inL q ≡ a
        q≡a = Σ≡Prop (λ z → (z ∈ˢ Lset α) .snd) refl

```

<!--en-->
The satisfaction of the body at the witness transports along the body path into the stage reading, and along the identification of the witness into the substructure's carrier; that is exactly the Tarski-Vaught conclusion for the original formula and environment.
<!--zh-->
见证处本体的满足沿体路径搬入层语义，再沿见证的同一视搬入子结构载体；这恰是原公式与原环境的 Tarski-Vaught 结论。
<!--ja-->
証人のもとの本体の充足は、体のパスに沿って段階の意味論へ、そして証人の同一視に沿って部分構造の台へ運ばれます。これが、もとの論理式と環境に対する Tarski-Vaught の結論にほかなりません。
<!--/-->

```agda
        sat : ⟨ (A.inL q ∷ map A.inL δ) ASt.AbsL.⊨ᵐ (mapFo A.inL ψ) ⟩
        sat = subst (λ b → ⟨ (b ∷ map A.inL δ) ASt.AbsL.⊨ᵐ
                                (mapFo A.inL ψ) ⟩)
                (sym q≡a) (subst ⟨_⟩ (body-path a) ha)

```

<!--en-->
The Tarski-Vaught condition therefore yields elementarity of the hull in `Lset α`.
<!--zh-->
因此，Tarski-Vaught 条件给出壳在 `Lset α` 中的初等性。
<!--ja-->
したがって、Tarski-Vaught 条件から包の `Lset α` における初等性が得られます。
<!--/-->

```agda
  elem : A.Elementary
  elem = A.TV→elem tv
```

<!--en-->
## Reading parameter-free formulas in the ambient universe
<!--zh-->
## 在外围宇宙中读取无参公式
<!--ja-->
## パラメータなし論理式を周囲の宇宙で読む
<!--/-->

<!--en-->
For formulas with empty constant domain, ambient satisfaction can then be compared without any nontrivial relabelling of constants.
<!--zh-->
对于常元域为空的公式，外围满足关系的比较不涉及任何非平凡的常元重标记。
<!--ja-->
定数領域が空の論理式では、定数の非自明な付け替えなしに周囲の充足関係を比較できます。
<!--/-->

```agda
module AtP = SemV.At (⊥* {ℓ-suc ℓ}) (λ b → Empty.rec* b) using ( _⊨_ )

```

<!--en-->
Ambient satisfaction for parameter-free formulas is named for reuse, and the key observation is stated: relabelling a parameter-free formula does not change it, since there are no constants to remap.
<!--zh-->
无参公式的外围满足被命名备用；关键观察是：改名无参公式不改变它，因为无可重映射的常数。
<!--ja-->
パラメータなしの論理式の周囲の充足は、再利用のために名付けられます。重要な観察はこうです。パラメータなしの論理式は、改名しても変わらない。写し直す定数がないからです。
<!--/-->

```agda
_⊨ₚ_ : {n : ℕ} → S ^ n → Formula (⊥* {ℓ-suc ℓ}) n → hProp (ℓ-suc ℓ)
_⊨ₚ_ = AtP._⊨_
embed-map : {ℓ₁ ℓ₂ : Level} {K : Type ℓ₁} {K' : Type ℓ₂} (f : K → K')
            {n : ℕ} (φ : Formula (⊥* {ℓ-suc ℓ}) n)
          → mapFo f (embed φ) ≡ embed φ
```

<!--en-->
The proof composes the mapping law with the fact that the empty domain's embedding is the identity on occurrences: nothing is left for the relabelling to move.
<!--zh-->
证明复合映射法则与「空域嵌入在出现上是恒等」的事实：改名无可移动之物。
<!--ja-->
証明は、写しの法則と、空の領域の埋め込みが出現の上で恒等であるという事実を合成します。改名が動かすものは何も残っていません。
<!--/-->

```agda
embed-map f φ =
    mapFo-comp Empty.rec* f φ
  ∙ cong (λ h → mapFo h φ) (funExt (λ b → Empty.rec* b))
opaque
  isOrdAt : Formula (⊥* {ℓ-suc ℓ}) 1
```

<!--en-->
Ordinality is expressed by a one-slot bounded formula saying that the parameter is transitive and that every member of it is transitive.
<!--zh-->
序数性由一个单空位有界公式表达：参数本身传递，且参数的每个成员也传递。
<!--ja-->
順序数性は、一つの枠をもつ有界論理式によって、引数自身が推移的であり、そのすべての要素も推移的であることとして表されます。
<!--/-->

```agda
  isOrdAt =
    (∀̇∈ (var zero) (∀̇∈ (var zero) (var zero ∈̇ var (suc (suc zero)))))
    ∧̇ (∀̇∈ (var zero) (∀̇∈ (var zero) (∀̇∈ (var zero) (var zero ∈̇ var (suc (suc zero))))))

```

<!--en-->
The `Δ₀` certificate follows the outer conjunction, then the two bounded quantifiers of the first clause and the three bounded quantifiers of the second, ending at membership atoms.
<!--zh-->
`Δ₀` 证书先穿过外层合取，再分别穿过第一子句的两个与第二子句的三个有界量词，最终落到隶属原子。
<!--ja-->
`Δ₀` の証拠は外側の連言を通り、第一の節の二つと第二の節の三つの有界量化子をたどって、所属の原子式に至ります。
<!--/-->

```agda
  Δ₀-isOrdAt : Δ₀ isOrdAt
  Δ₀-isOrdAt =
    δ-∧ (δ-∀∈ (δ-∀∈ δ-∈))
        (δ-∀∈ (δ-∀∈ (δ-∀∈ δ-∈)))

```

<!--en-->
The two reading lemmas identify satisfaction of `isOrdAt` exactly with the ordinal predicate, in both directions.
<!--zh-->
两个读取引理在两个方向上把 `isOrdAt` 的满足精确等同于序数谓词。
<!--ja-->
二つの読み取り補題は、`isOrdAt` の充足と順序数述語を双方向に正確に対応させます。
<!--/-->

```agda
module Amb where
  opaque
    unfolding isOrdAt

```

<!--en-->
Reading ordinality out of the formula unpacks the two bounded clauses into the two fields of the ordinal predicate: transitivity of the parameter, and transitivity of every member.
<!--zh-->
从公式读出序数性，即把两条有界子句拆成序数谓词的两个字段：参数的传递性，以及每个成员的传递性。
<!--ja-->
論理式から順序数性を読み出すとは、二つの有界の節を、順序数の述語の二つの欄へ開くことです。引数の推移性と、すべての要素の推移性です。
<!--/-->

```agda
    isOrdAt-out : (x : S) → ⟨ (x ∷ []) ⊨ₚ isOrdAt ⟩ → IsOrd x
    isOrdAt-out x h =
        ( λ {x₁} {y} y∈x₁ x₁∈x → h .fst x₁ x₁∈x y y∈x₁ )
      , ( λ a a∈x {x₁} {y} y∈x₁ x₁∈a → h .snd a a∈x x₁ x₁∈a y y∈x₁ )

```

<!--en-->
Conversely, the two fields of `IsOrd` satisfy the two bounded clauses. The three-slot companion expresses the same predicate at the middle free slot; the other two free slots do not occur in the formula.
<!--zh-->
反过来，`IsOrd` 的两个字段满足这两个有界子句。三空位伴随公式在中间的自由空位表达同一谓词；另外两个自由空位并未出现于公式中。
<!--ja-->
逆に、`IsOrd` の二つの成分から二つの有界な節が従います。三つの枠をもつ版は中央の自由な枠について同じ述語を表し、ほかの二つの自由な枠は論理式に現れません。
<!--/-->

```agda
    isOrdAt-in : (x : S) → IsOrd x → ⟨ (x ∷ []) ⊨ₚ isOrdAt ⟩
    isOrdAt-in x o =
        ( λ a a∈x b hb → o .fst {a} {b} hb a∈x )
      , ( λ a a∈x b b∈a c hc → o .snd a a∈x {b} {c} hc b∈a )
isOrd-at-p : Formula (⊥* {ℓ-suc ℓ}) 3
```

<!--en-->
The three-slot formula's first conjunct says that every member of a member of the parameter is a member of the parameter: transitivity, read at the second slot.
<!--zh-->
三空位公式的第一个合取支说：参数的成员的成员都是参数的成员，即在第二空位处读取的传递性。
<!--ja-->
三つの枠をもつ論理式の最初の連言支は、引数の要素の要素が引数の要素であること、すなわち第二の枠で読まれる推移性を言います。
<!--/-->

```agda
isOrd-at-p =
    (∀̇∈ (var (suc zero))
      (∀̇∈ (var zero) (var zero ∈̇ var (suc (suc (suc zero))))))
  ∧̇ (∀̇∈ (var (suc zero))
      (∀̇∈ (var zero)
```

<!--en-->
The second conjunct says that each member `a` of the parameter is transitive: whenever `c ∈ b ∈ a`, one has `c ∈ a`.
<!--zh-->
第二个合取支说明参数的每个成员 `a` 都传递：若 `c ∈ b ∈ a`，则 `c ∈ a`。
<!--ja-->
第二の連言支は、引数の各要素 `a` が推移的であること、すなわち `c ∈ b ∈ a` ならば `c ∈ a` であることを述べます。
<!--/-->

```agda
        (∀̇∈ (var zero) (var zero ∈̇ var (suc (suc zero))))))

```

<!--en-->
Its boundedness certificate follows the same recursion. The erasure lemma then begins: for a formula with no constant occurrences, erasing the constants preserves the Δ₀ certificate, clause by clause.
<!--zh-->
其有界性证书循同样的递归。随后消去引理开始：对无常数出现的公式，消去常数保持 Δ₀ 证书，逐子句成立。
<!--ja-->
その有界性の証拠は、同じ再帰に従います。続いて消去の補題が始まります。定数の出現をもたない論理式に対して、定数を消去しても Δ₀ の証拠は、場合ごとに保たれます。
<!--/-->

```agda
Δ₀-isOrd-at-p : Δ₀ isOrd-at-p
Δ₀-isOrd-at-p = δ-∧ (δ-∀∈ (δ-∀∈ δ-∈)) (δ-∀∈ (δ-∀∈ (δ-∀∈ δ-∈)))
erase-Δ₀ : {m : ℕ} (φ : Formula CS.S m) (p : countFo φ ≡ 0)
         → Δ₀ φ → Δ₀ (Cnt.erase φ p)
erase-Δ₀ (t ∈̇ u) p δ-∈ = δ-∈
```

<!--en-->
Atoms pass through unchanged, and the propositional connectives recurse, since erasure is applied structurally.
<!--zh-->
原子原样通过，命题联结词按结构递归，因为消去是结构性施加的。
<!--ja-->
アトムはそのまま通り、命題の結合子は構造的に消去が施されるので再帰します。
<!--/-->

```agda
erase-Δ₀ (t ≐ u) p δ-≐ = δ-≐
erase-Δ₀ (φ ∧̇ ψ) p (δ-∧ c d) = δ-∧ (erase-Δ₀ φ _ c) (erase-Δ₀ ψ _ d)
erase-Δ₀ (φ ∨̇ ψ) p (δ-∨ c d) = δ-∨ (erase-Δ₀ φ _ c) (erase-Δ₀ ψ _ d)
erase-Δ₀ (φ ⇒̇ ψ) p (δ-⇒ c d) = δ-⇒ (erase-Δ₀ φ _ c) (erase-Δ₀ ψ _ d)
erase-Δ₀ ⊥̇ p δ-⊥ = δ-⊥
```

<!--en-->
The bounded-quantifier cases recurse on their matrices.
<!--zh-->
有界量词情形递归处理其矩阵。
<!--ja-->
有界量化子の場合は本体について再帰します。
<!--/-->

```agda
erase-Δ₀ (∀̇∈ t φ) p (δ-∀∈ c) = δ-∀∈ (erase-Δ₀ φ _ c)
erase-Δ₀ (∃̇∈ t φ) p (δ-∃∈ c) = δ-∃∈ (erase-Δ₀ φ _ c)
erase-Δ₀ (∃̇ φ) p ()
erase-Δ₀ (∀̇ φ) p ()
```

<!--en-->
## The hull data required by condensation
<!--zh-->
## 凝聚所需的壳数据
<!--ja-->
## 凝縮に必要な包のデータ
<!--/-->

<!--en-->
The unbounded quantifier cases are impossible because no `Δ₀` certificate has such a constructor.
<!--zh-->
非有界量词情形不可能出现，因为 `Δ₀` 证书没有对应构造子。
<!--ja-->
非有界量化子の場合は、それに対応する `Δ₀` の構成子が存在しないため不可能です。
<!--/-->

```agda
module HullStage (lam : S) (ordλ : IsOrd lam)
```

<!--en-->
The frame receives a stage whose index admits successors of its members, a starting set contained in that stage, and the empty set's membership in the index.
<!--zh-->
框架收取：一个其指数容纳成员后继的层、包含于该层的起始集合，以及空集属于该指数。
<!--ja-->
枠組みは、指数が要素の後続を認める段階、その段階に含まれる始集合、そして空集合の指数への所属を受け取ります。
<!--/-->

```agda
  (succλ : (d : S) → ⟨ d ∈ˢ lam ⟩ → ⟨ sucV d ∈ˢ lam ⟩)
  (X : S) (X⊆L : (x : S) → ⟨ x ∈ˢ X ⟩ → ⟨ x ∈ˢ Lset lam ⟩) (∅∈λ : ⟨ ∅ ∈ˢ lam ⟩) where

```

<!--en-->
Inside `Lset lam`, the starting set generates a Skolem hull `M`. Every element of `M` remains in the stage.
<!--zh-->
在 `Lset lam` 内，起始集合生成 Skolem 壳 `M`。`M` 的每个元素仍属于该层。
<!--ja-->
`Lset lam` の内部で、始集合は Skolem 包 `M` を生成します。`M` の各要素は段階内にとどまります。
<!--/-->

```agda
  module ASt = AtStage lam ordλ
    using ( module AbsL; module AtM; module Hull; Ltr; SL; wL )

```

<!--en-->
The original set and the empty-set fallback are both represented in the hull construction.
<!--zh-->
原集合与作为回退值的空集都在壳构造中得到呈现。
<!--ja-->
もとの集合と予備値である空集合は、いずれも包の構成の中に表示されます。
<!--/-->

```agda
  module H = ASt.Hull X X⊆L ∅∈λ
    using ( module T; module XInM; Hull⊆L; X⊆M; hull-member
          ; val-in-Hull; ∅∈Lsetα; inStg )

```

<!--en-->
This set `M` is the carrier whose elementarity and Mostowski collapse enter the condensation argument.
<!--zh-->
这个集合 `M` 是凝聚论证所使用的载体，其初等性与 Mostowski 塌缩构成论证的数据。
<!--ja-->
この集合 `M` は凝縮の議論の台であり、その初等性と Mostowski 崩壊が議論のデータになります。
<!--/-->

```agda
  M : S
  M = H.T.Hull

```

<!--en-->
For the hull `M`, let `π` be its Mostowski collapse and `πX` its image. Every collapsed hull point belongs to `πX`, every member of `πX` comes from a hull point, and `πX` is transitive. Moreover, the collapse fixes any transitive point of the hull.
<!--zh-->
对壳 `M`，令 `π` 为其 Mostowski 塌缩，`πX` 为塌缩像。每个塌缩后的壳中点都属于 `πX`，`πX` 的每个成员都来自壳中的一点，并且 `πX` 是传递的。此外，塌缩固定壳中的每个传递点。
<!--ja-->
包 `M` に対し、その Mostowski 崩壊を `π`、崩壊像を `πX` とします。包の点を崩壊したものはすべて `πX` に属し、`πX` の各要素は包の点から得られ、`πX` は推移的です。さらに、包の推移的な点は崩壊によって固定されます。
<!--/-->

```agda
  module C = Collapse M
    using ( module InjExt; π; πX; πX-intro; πX-member; πX-trans; fixes )

```

<!--en-->
The condensation argument assumes two properties of the image. First, if an ordinal `δ` belongs to the image, then so does the level `Lset δ`. Second, the collapse of every hull member belongs to some level whose ordinal index lies in the image. These closure and covering properties will identify the image with a single level of `L`.
<!--zh-->
凝聚论证对塌缩像作两项假设。第一，若序数 `δ` 属于该像，则层 `Lset δ` 也属于该像。第二，每个壳成员的塌缩都属于某个层，而该层的序数指数属于塌缩像。这两项闭合与覆盖性质将把塌缩像认同为 `L` 的一个层。
<!--ja-->
凝縮の議論では、崩壊像について二つの性質を仮定します。第一に、順序数 `δ` が像に属するなら、段階 `Lset δ` も像に属します。第二に、包の各要素の崩壊は、像に属する順序数を添字とするある段階に属します。この閉性と被覆の性質により、崩壊像を `L` の一つの段階と同定できます。
<!--/-->

```agda
  module Condense
    (levelIn : (δ : S) → IsOrd δ → ⟨ δ ∈ˢ C.πX ⟩ → ⟨ Lset δ ∈ˢ C.πX ⟩)
    (cover : (y : S) → ⟨ y ∈ˢ M ⟩
           → ∥ Σ[ γ ∈ S ] (IsOrd γ × ⟨ γ ∈ˢ C.πX ⟩ × ⟨ C.π y ∈ˢ Lset γ ⟩) ∥₁)
    where
```

<!--en-->
Separation forms the set of exactly those members of `πX` that are ordinals. Thus `β` records the ordinal part of the collapse image. The separating predicate is the bounded ordinality formula, small at every environment by its Δ₀ certificate.
<!--zh-->
分离构造出恰由 `πX` 中序数组成的集合。因此 `β` 记录塌缩像的序数部分。其分离谓词正是那条陈述序数性的有界公式，凭 Δ₀ 证书在每个环境处都是小的。
<!--ja-->
分出によって、`πX` の要素のうち順序数であるものちょうどからなる集合を作ります。したがって `β` は崩壊像の順序数部分を表します。分出の述語は順序数性を述べる有界の論理式であり、Δ₀ の証拠によってどの環境でも小さいものです。
<!--/-->

```agda
    β-sep : Σ[ s ∈ S ]
              (∀ y → (y ∈ˢ s) ≡ ((y ∈ˢ C.πX) ⊓ ((y ∷ []) ⊨ₚ isOrdAt)))
    β-sep = separateFromSmall C.πX (λ y → (y ∷ []) ⊨ₚ isOrdAt)
              (λ y → D0.Δ₀-small Δ₀-isOrdAt (y ∷ []))

```

<!--en-->
We call this ordinal part `β`; the following argument proves that it is itself an ordinal and that its level is exactly the collapse image.
<!--zh-->
我们把这个序数部分记为 `β`；下面证明它本身是序数，并且它所索引的层恰为塌缩像。
<!--ja-->
この順序数部分を `β` と書きます。以下では、`β` 自身が順序数であり、`β` が添字づける階層が崩壊像と一致することを示します。
<!--/-->

```agda
    β : S
    β = β-sep .fst

```

<!--en-->
Membership in `β` is equivalent to membership in `πX` together with satisfaction of the constant-free ordinal formula when its free variable is assigned the member.
<!--zh-->
属于 `β`，等价于属于 `πX`，并且把该成员赋给自由变元后满足无常元的序数公式。
<!--ja-->
`β` に属することは、`πX` に属し、さらにその要素を自由変数に割り当てたとき無定数の順序数公式を満たすことと同値です。
<!--/-->

```agda
    β-spec : (y : S) → (y ∈ˢ β) ≡ ((y ∈ˢ C.πX) ⊓ ((y ∷ []) ⊨ₚ isOrdAt))
    β-spec = β-sep .snd

```

<!--en-->
The first projection of the equivalence shows every member of beta is a member of the collapse image.
<!--zh-->
定义等价的第一个投影表明：beta 的每个成员都是塌缩像的成员。
<!--ja-->
同値の第一の射影は、ベータのすべての要素が崩壊の像の要素であることを示します。
<!--/-->

```agda
    β∈πX : (δ : S) → ⟨ δ ∈ˢ β ⟩ → ⟨ δ ∈ˢ C.πX ⟩
    β∈πX δ δ∈β = subst ⟨_⟩ (β-spec δ) δ∈β .fst

```

<!--en-->
The second component converts satisfaction of this constant-free one-variable formula into ambient ordinality.
<!--zh-->
第二个分量把这条无常元一自由变元公式的满足转换为外围宇宙中的序数性。
<!--ja-->
第二成分は、この無定数一自由変数公式の充足を、周囲の宇宙での順序数性へ変換します。
<!--/-->

```agda
    β-ord : (δ : S) → ⟨ δ ∈ˢ β ⟩ → IsOrd δ
    β-ord δ δ∈β = Amb.isOrdAt-out δ (subst ⟨_⟩ (β-spec δ) δ∈β .snd)

```

<!--en-->
Conversely, an ordinal of the collapse image lies in beta: both defining components are supplied, membership and ordinality, and the defining equivalence transports them back inside.
<!--zh-->
反之，塌缩像的序数落入 beta：隶属与序数性两个定义分量一并提供，定义等价再把它们送回 beta 内部。
<!--ja-->
逆に、崩壊の像の順序数はベータの中にあります。所属と順序数性という定義の二つの成分が供給され、定義の同値がそれをベータの内部へ運び戻します。
<!--/-->

```agda
    ord∈β : (δ : S) → ⟨ δ ∈ˢ C.πX ⟩ → IsOrd δ → ⟨ δ ∈ˢ β ⟩
    ord∈β δ δ∈πX oδ = subst ⟨_⟩ (sym (β-spec δ)) (δ∈πX , Amb.isOrdAt-in δ oδ)

```

<!--en-->
To prove that `β` is an ordinal, we verify its two defining requirements. The first is transitivity: whenever `z ∈ x ∈ β`, we must have `z ∈ β`.
<!--zh-->
为证明 `β` 是序数，需要验证其两项定义条件。第一项是传递性：每当 `z ∈ x ∈ β`，都须有 `z ∈ β`。
<!--ja-->
`β` が順序数であることを示すため、その二つの定義条件を確かめます。第一は推移性です。`z ∈ x ∈ β` ならば `z ∈ β` でなければなりません。
<!--/-->

```agda
    β-isOrd : IsOrd β
    β-isOrd = β-trans , β-mem
      where
      β-trans : isTransV β
      β-trans {x = x} {y = z} z∈x x∈β =
```

<!--en-->
Transitivity uses the transitivity of the collapse image at the intermediate membership and reads the ordinality of the middle point from the ambient formula. The second field follows because every member of beta is an ordinal, hence transitive.
<!--zh-->
传递性在中间隶属处使用塌缩像的传递性，并从外围公式读取中间点的序数性；第二字段随之成立，因为 beta 的每个成员都是序数，故传递。
<!--ja-->
推移性は、中間の所属のもとで崩壊の像の推移性を使い、中間の点の順序数性を周囲の論理式から読みます。第二の欄は、ベータのすべての要素が順序数、したがって推移的であることから従います。
<!--/-->

```agda
        subst ⟨_⟩ (sym (β-spec z))
          ( C.πX-trans {x = x} {y = z} z∈x (β∈πX x x∈β)
          , Amb.isOrdAt-in z (mem-ord {A = x} (β-ord x x∈β) z z∈x) )
      β-mem : (x : S) → ⟨ x ∈ˢ β ⟩ → isTransV x
      β-mem x x∈β = β-ord x x∈β .fst
```

<!--en-->
The covering hypothesis lifts from hull members to collapse members. Since a collapse member is, merely, the collapse of a hull member, the cover of that hull member transports along the identification.
<!--zh-->
覆盖假设从壳成员提升到塌缩成员。由于塌缩成员仅仅是某个壳成员的塌缩，该壳成员的覆盖沿此同一视搬运。
<!--ja-->
覆いの仮定は、包の要素から崩壊の要素へ一度持ち上がります。崩壊の要素は、単に、包のある要素の崩壊なので、その要素の覆いが同一視に沿って運ばれます。
<!--/-->

```agda
    covered : (x : S) → ⟨ x ∈ˢ C.πX ⟩
            → ∥ Σ[ γ ∈ S ]
                 (IsOrd γ × ⟨ γ ∈ˢ C.πX ⟩ × ⟨ x ∈ˢ Lset γ ⟩) ∥₁
    covered x x∈πX = PT.rec squash₁ go (C.πX-member x x∈πX)
      where
```

<!--en-->
The inversion is the collapse's own member description: a member of the image is, merely, the collapse of a hull member.
<!--zh-->
该求逆正是塌缩自身的成员描述：像的成员仅仅是某个壳成员的塌缩。
<!--ja-->
逆にたどるのは、崩壊自身の要素の記述です。像の要素は、単に、包のある要素の崩壊です。
<!--/-->

```agda
      go : Σ[ y ∈ S ] (⟨ y ∈ˢ M ⟩ × (C.π y ≡ x))
         → ∥ Σ[ γ ∈ S ]
              (IsOrd γ × ⟨ γ ∈ˢ C.πX ⟩ × ⟨ x ∈ˢ Lset γ ⟩) ∥₁
      go (y , y∈M , e) = PT.map
        (λ { (γ , oγ , γ∈πX , h) →
```

<!--en-->
The cover transports along the equality of the collapse values. The lifted statement is then applied immediately: every ordinal of beta sits inside a larger ordinal of beta, the classical limit-stage step of the condensation argument.
<!--zh-->
覆盖沿塌缩值的相等搬运。提升后的命题随即被直接使用：beta 的每个序数都位于 beta 中更大的序数之内，这就是凝聚论证的经典极限层步骤。
<!--ja-->
覆いは、崩壊の値の等しさに沿って運ばれます。持ち上がった主張はすぐに使われます。ベータのすべての順序数は、ベータの中のより大きな順序数の中にあります。これが凝縮の議論の古典的な極限段階の一歩です。
<!--/-->

```agda
          γ , oγ , γ∈πX , subst (λ w → ⟨ w ∈ˢ Lset γ ⟩) e h })
        (cover y y∈M)
    β-succ : (δ : S) → ⟨ δ ∈ˢ β ⟩
           → ∥ Σ[ γ ∈ S ] (IsOrd γ × ⟨ δ ∈ˢ γ ⟩ × ⟨ γ ∈ˢ β ⟩) ∥₁
    β-succ δ δ∈β = PT.map go (covered δ (β∈πX δ δ∈β))
```

<!--en-->
The ordinality of delta is read off beta, and the conversion restates the covering conclusion in membership form: the level containing delta can be chosen to have its index inside beta.
<!--zh-->
delta 的序数性从 beta 读出；转换把覆盖结论改写为隶属形式：包含 delta 的层可取其指数落在 beta 内。
<!--ja-->
delta の順序数性はベータから読まれ、変換は覆いの結論を所属の形で言い直します。delta を含む層は、その指数をベータの中に選べるのです。
<!--/-->

```agda
      where
      oδ : IsOrd δ
      oδ = β-ord δ δ∈β
      go : Σ[ γ ∈ S ] (IsOrd γ × ⟨ γ ∈ˢ C.πX ⟩ × ⟨ δ ∈ˢ Lset γ ⟩)
         → Σ[ γ ∈ S ] (IsOrd γ × ⟨ δ ∈ˢ γ ⟩ × ⟨ γ ∈ˢ β ⟩)
```

<!--en-->
Because both `δ` and `γ` are ordinals, `δ ∈ Lset γ` implies `δ ∈ γ`; and because `γ` is an ordinal in `πX`, it belongs to `β`. The reverse inclusion is then stated: every member of the collapse lies in the level at beta.
<!--zh-->
由于 `δ` 与 `γ` 都是序数，`δ ∈ Lset γ` 推出 `δ ∈ γ`；又因 `γ` 是 `πX` 中的序数，所以 `γ ∈ β`。随后陈述反向包含：塌缩的每个成员都属于 beta 处的层。
<!--ja-->
`δ` と `γ` はともに順序数なので、`δ ∈ Lset γ` から `δ ∈ γ` が従います。また `γ` は `πX` に属する順序数なので、`γ ∈ β` です。そして逆の包含が述べられます。崩壊のすべての要素は、ベータにおける層に属します。
<!--/-->

```agda
      go (γ , oγ , γ∈πX , δ∈Lγ) =
        γ , oγ , ord∈Lset→∈ γ oγ δ oδ δ∈Lγ , ord∈β γ γ∈πX oγ
    πX⊆Lβ : (x : S) → ⟨ x ∈ˢ C.πX ⟩ → ⟨ x ∈ˢ Lset β ⟩
    πX⊆Lβ x x∈πX = PT.rec (snd (x ∈ˢ Lset β)) go (covered x x∈πX)
      where
```

<!--en-->
The reverse inclusion holds because the level at beta contains every smaller level: monotonicity of the stage construction transports the covering level inside beta.
<!--zh-->
反向包含成立，因为 beta 处的层包含所有更小的层：层构造的单调性把覆盖层搬入 beta 之内。
<!--ja-->
逆の包含が成り立つのは、ベータにおける層がすべてのより小さい層を含むからです。段階の構成の単調性が、覆いの層をベータの中へ運びます。
<!--/-->

```agda
      go : Σ[ γ ∈ S ] (IsOrd γ × ⟨ γ ∈ˢ C.πX ⟩ × ⟨ x ∈ˢ Lset γ ⟩)
         → ⟨ x ∈ˢ Lset β ⟩
      go (γ , oγ , γ∈πX , x∈Lγ) =
        Lset-mono {α = β} {β = γ} (ord∈β γ γ∈πX oγ) x∈Lγ
    Lβ⊆πX : (x : S) → ⟨ x ∈ˢ Lset β ⟩ → ⟨ x ∈ˢ C.πX ⟩
```

<!--en-->
The forward inclusion decomposes a member of the level at beta by the stage construction, and the limit step supplies a larger ordinal inside beta.
<!--zh-->
正向包含按层构造分解 beta 层的成员，而极限步供给 beta 内更大的序数。
<!--ja-->
順方向の包含は、ベータの層の要素を段階の構成で分解し、極限の一歩がベータの中のより大きな順序数を供給します。
<!--/-->

```agda
    Lβ⊆πX x x∈Lβ = PT.rec (snd (x ∈ˢ C.πX)) go (Lset-out β x x∈Lβ)
      where
      go : Σ[ δ ∈ S ] (⟨ δ ∈ˢ β ⟩ × ⟨ x ∈ˢ 𝒟ₒ (Lset δ) ⟩)
         → ⟨ x ∈ˢ C.πX ⟩
      go (δ , δ∈β , x∈𝒟ₒδ) = PT.rec (snd (x ∈ˢ C.πX)) liftStage (β-succ δ δ∈β)
```

<!--en-->
The lifting stage is stated: from an ordinal inside beta containing delta, produce the membership of `x` in the collapse.
<!--zh-->
陈述提升层：从 beta 内包含 delta 的序数，产出 `x` 在塌缩中的隶属。
<!--ja-->
持ち上げの段階が述べられます。ベータの中で delta を含む順序数から、崩壊の中での `x` の所属を産み出します。
<!--/-->

```agda
        where
        liftStage : Σ[ γ ∈ S ] (IsOrd γ × ⟨ δ ∈ˢ γ ⟩ × ⟨ γ ∈ˢ β ⟩)
             → ⟨ x ∈ˢ C.πX ⟩
        liftStage (γ , oγ , δ∈γ , γ∈β) =
          C.πX-trans {x = Lset γ} {y = x}
```

<!--en-->
The lifting composes two closures: the level at gamma contains x because x is defined at delta below gamma, and the collapse image contains the level at gamma by the first hypothesis. The two inclusions then meet in the extensionality of the universe.
<!--zh-->
提升复合两条闭合：由于 `x` 定义在 gamma 之下的 delta 处，gamma 的层包含 `x`；又由第一条假设，塌缩像包含 gamma 处的层。两条包含随即在宇宙的外延性处会合。
<!--ja-->
持ち上げは、二つの閉包を合成します。`x` は gamma より下の delta で定義されるので gamma の層に属し、さらに第一の仮定によって、崩壊の像は gamma における層を含みます。二つの包含は、宇宙の外延性のもとで出会います。
<!--/-->

```agda
            (Lset-in γ δ x δ∈γ x∈𝒟ₒδ)
            (levelIn γ oγ (β∈πX γ γ∈β))
    ext : C.πX ≡ Lset β
    ext = extensionality C.πX (Lset β) (sub , sup)
      where
```

<!--en-->
The first half of the extensionality argument moves each member through the bridge into the stage reading, applies the reverse inclusion, and returns through the bridge.
<!--zh-->
外延性论证的前一半让每个成员经桥进入层读法，应用反向包含，再经桥返回。
<!--ja-->
外延性の議論の前半は、各要素を橋を通して段階の読みへ運び、逆の包含を適用し、橋を通って戻します。
<!--/-->

```agda
      sub : (x : S) → ⟨ x ∈ₛ C.πX ⟩ → ⟨ x ∈ₛ Lset β ⟩
      sub x x∈ₛπX = ∈∈ₛ {a = x} {b = Lset β} .fst
        (πX⊆Lβ x (∈∈ₛ {a = x} {b = C.πX} .snd x∈ₛπX))
      sup : (x : S) → ⟨ x ∈ₛ Lset β ⟩ → ⟨ x ∈ₛ C.πX ⟩
      sup x x∈ₛLβ = ∈∈ₛ {a = x} {b = C.πX} .fst
```

<!--en-->
The second half does the same for the forward inclusion, and the two halves identify the collapse image with the level at beta.
<!--zh-->
后半对正向包含做同样的事，两半合起来把塌缩像等同于 beta 处的层。
<!--ja-->
後半は順方向の包含について同じことを行い、二つの半分が、崩壊の像をベータにおける層と同一視します。
<!--/-->

```agda
        (Lβ⊆πX x (∈∈ₛ {a = x} {b = Lset β} .snd x∈ₛLβ))

```

<!--en-->
The condensation statement is thus assembled: the collapse image is the level at its ordinal `β`. For the applications, take as a starting set the union of a stage `Lset α` with one extra point `x`, where `α ∈ lam`, `x ⊆ Lset α`, and `x ∈ Lset lam`.
<!--zh-->
凝聚陈述就此成立：塌缩像等于序数 `β` 所索引的层。为作应用，取层 `Lset α` 与额外一点 `x` 的并集为起始集，并假设 `α ∈ lam`、`x ⊆ Lset α` 以及 `x ∈ Lset lam`。
<!--ja-->
これで凝縮の主張が得られます。崩壊像は順序数 `β` を添字とする段階に等しくなります。応用では、段階 `Lset α` と一つの点 `x` の合併を始集合とし、`α ∈ lam`、`x ⊆ Lset α`、`x ∈ Lset lam` を仮定します。
<!--/-->

```agda
    condenses : Σ[ γ ∈ S ] (IsOrd γ × (C.πX ≡ Lset γ))
    condenses = β , β-isOrd , ext
module UnionKit (α lam x : S) (ordα : IsOrd α) (ordλ : IsOrd lam)
  (α∈λ : ⟨ α ∈ˢ lam ⟩) (x⊆Lα : (z : S) → ⟨ z ∈ˢ x ⟩ → ⟨ z ∈ˢ Lset α ⟩)
  (x∈Lλ : ⟨ x ∈ˢ Lset lam ⟩) (α∉ω : ⟨ α ∈ˢ ω ⟩ → Empty.⊥) where
```

<!--en-->
The starting set is the union of `Lset α` and the singleton `{x}`; singleton classification gives `x ∈ {x}`.
<!--zh-->
起始集合是 `Lset α` 与单点集 `{x}` 的并集；单点集的分类给出 `x ∈ {x}`。
<!--ja-->
始集合は `Lset α` と単集合 `{x}` の合併です。単集合の特徴づけから `x ∈ {x}` が得られます。
<!--/-->

```agda

  X : S
  X = Lset α ∪ ⁅ x ⁆s
  x∈sgl : ⟨ x ∈ₛ ⁅ x ⁆s ⟩
  x∈sgl = SetPackage.classification (SingletonPackage x) x .snd refl

```

<!--en-->
The extra point belongs to the starting set through the right side of the union.
<!--zh-->
额外点经并集的右侧属于起始集合。
<!--ja-->
余分な点は、和の右側を通して始集合に属します。
<!--/-->

```agda
  x∈X : ⟨ x ∈ˢ X ⟩
  x∈X = cup-inr (Lset α) ⁅ x ⁆s x (∈∈ₛ {a = x} {b = ⁅ x ⁆s} .snd x∈sgl)

```

<!--en-->
Every member of the stage belongs to the starting set through the left side.
<!--zh-->
层的每个成员经左侧属于起始集合。
<!--ja-->
段階のすべての要素は、左側を通して始集合に属します。
<!--/-->

```agda
  Lα∈X : (z : S) → ⟨ z ∈ˢ Lset α ⟩ → ⟨ z ∈ˢ X ⟩
  Lα∈X = cup-inl (Lset α) ⁅ x ⁆s

```

<!--en-->
The singleton characterization says that every member of `{x}` is equal to `x`.
<!--zh-->
单点集的特征刻画说明，`{x}` 的每个成员都等于 `x`。
<!--ja-->
単集合の特徴づけにより、`{x}` の各要素は `x` に等しくなります。
<!--/-->

```agda
  sgl≡ : (z : S) → ⟨ z ∈ˢ ⁅ x ⁆s ⟩ → z ≡ x
  sgl≡ = sgl-out x

```

<!--en-->
Consequently, membership in the starting set splits into two cases: a point belongs either to `Lset α` or to the singleton `{x}`.
<!--zh-->
因此，属于起始集分成两种情形：该点或者属于 `Lset α`，或者属于单点集 `{x}`。
<!--ja-->
したがって、始集合への所属は二つの場合に分かれます。その点は `Lset α` に属するか、単集合 `{x}` に属します。
<!--/-->

```agda
  X-mem : (z : S) → ⟨ z ∈ˢ X ⟩
        → ⟨ (z ∈ˢ Lset α) ⊔ (z ∈ˢ ⁅ x ⁆s) ⟩
  X-mem = cup-out (Lset α) ⁅ x ⁆s

```

<!--en-->
The generator is contained in the ambient stage: a member on the stage side is transported by the monotonicity of the stage construction along the index inclusion.
<!--zh-->
生成集包含于外围层：层一侧的成员沿指数包含、由层构造的单调性搬运。
<!--ja-->
生成集は周囲の段階に含まれます。段階の側の要素は、指数の包含に沿って、段階の構成の単調性によって運ばれます。
<!--/-->

```agda
  X⊆Lλ : (z : S) → ⟨ z ∈ˢ X ⟩ → ⟨ z ∈ˢ Lset lam ⟩
  X⊆Lλ z z∈X = PT.rec (snd (z ∈ˢ Lset lam)) go (X-mem z z∈X)
    where
    go : (⟨ z ∈ˢ Lset α ⟩ ⊎ ⟨ z ∈ˢ ⁅ x ⁆s ⟩) → ⟨ z ∈ˢ Lset lam ⟩
    go (inl z∈Lα) = Lset-mono {α = lam} {β = α} α∈λ z∈Lα
```

<!--en-->
A member on the singleton side reduces to the extra point, whose stage membership was a hypothesis.
<!--zh-->
单点一侧的成员化归为额外点，而额外点的层隶属本是假设。
<!--ja-->
単元の側の要素は余分な点に帰着し、その段階への所属は仮定でした。
<!--/-->

```agda
    go (inr z∈sgl) = subst (λ u → ⟨ u ∈ˢ Lset lam ⟩) (sym (sgl≡ z z∈sgl)) x∈Lλ

```

<!--en-->
The generator is transitive. A member of a member on the stage side is in the stage by the layer's transitivity, and the left inclusion then places it in the generator.
<!--zh-->
生成集是传递的。若成员的成员位于层一侧，则由层的传递性它属于层，再由左包含把它放入生成集。
<!--ja-->
生成集は推移的です。段階の側の要素の要素は、層の推移性によって段階の中にあり、左の包含がそれを生成集の中に置きます。
<!--/-->

```agda
  Xtr : isTransV X
  Xtr {x = a} {y = b} b∈a a∈X = PT.rec (snd (b ∈ˢ X)) go (X-mem a a∈X)
    where
    go : (⟨ a ∈ˢ Lset α ⟩ ⊎ ⟨ a ∈ˢ ⁅ x ⁆s ⟩) → ⟨ b ∈ˢ X ⟩
    go (inl a∈Lα) = Lα∈X b (layer-trans (Lset-layer α) b∈a a∈Lα)
```

<!--en-->
On the singleton side, the intermediate set is `x`; the hypothesis `x ⊆ Lset α` then places each of its members in the left side of the union.
<!--zh-->
在单点集一侧，中间集合就是 `x`；假设 `x ⊆ Lset α` 随即把它的每个成员放入并集的左侧。
<!--ja-->
単集合側では中間の集合は `x` です。仮定 `x ⊆ Lset α` により、その各要素は合併の左側に入ります。
<!--/-->

```agda
    go (inr a∈sgl) = Lα∈X b (x⊆Lα b
      (subst (λ u → ⟨ b ∈ˢ u ⟩) (sgl≡ a a∈sgl) b∈a))
  one∈α : ⟨ sucV ∅ ∈ˢ α ⟩
  one∈α = Sum.rec
      (λ α∈ω → Empty.rec (α∉ω α∈ω))
```

<!--en-->
Infinity means not belonging to `ω`, and the trichotomy of ordinals decides the cases: membership in `ω` contradicts the hypothesis, equality with `ω` is witnessed by the numeral one, and `ω` below `α` places the numeral one inside `α` by transitivity.
<!--zh-->
无穷即不属于 `ω`，序数三分法分拆各情形：属于 `ω` 与假设矛盾；等于 `ω` 则由数码一见证隶属；`ω` 低于 `α` 则由传递性把数码一放入 `α` 之内。
<!--ja-->
無限とは `ω` に属さないことであり、順序数の三分法が場合を分けます。`ω` に属するなら仮定と矛盾し、`ω` と等しいなら数項一が所属の証人となり、`ω` が `α` より下なら `α` の推移性によって数項一がその中に入ります。
<!--/-->

```agda
      (Sum.rec (λ α≡ω → subst (λ w → ⟨ sucV ∅ ∈ˢ w ⟩) (sym α≡ω) (#∈ω 1))
               (λ ω∈α → ordα .fst (#∈ω 1) ω∈α))
      (ord-tri α ordα ω ω-ord)

```

<!--en-->
The empty set appears at the first successor stage, by the base-layer coding transported along the description of the successor stage.
<!--zh-->
空集出现在第一个后继层，由基层编码沿后继层的描述搬运而来。
<!--ja-->
空集合は最初の後続の段階に現れます。基底の層の符号化が、後続の段階の記述に沿って運ばれるからです。
<!--/-->

```agda
  ∅∈Lset1 : ⟨ ∅ ∈ˢ Lset (sucV ∅) ⟩
  ∅∈Lset1 = subst (λ w → ⟨ ∅ ∈ˢ w ⟩) (sym (Lset-suc ∅)) (∅∈𝒟ₒ ∅)

```

<!--en-->
Monotonicity lifts the empty set first into `Lset α` and then into `Lset lam`.
<!--zh-->
单调性先把空集提升到 `Lset α`，再到 `Lset lam`。
<!--ja-->
単調性が、空集合をまず `Lset α` へ、さらに `Lset lam` へ持ち上げます。
<!--/-->

```agda
  ∅∈Lλ : ⟨ ∅ ∈ˢ Lset lam ⟩
  ∅∈Lλ = Lset-mono {α = lam} {β = α} α∈λ
    (Lset-mono {α = α} {β = sucV ∅} one∈α ∅∈Lset1)

```

<!--en-->
The rank characterization then promotes this to membership of the empty set in the index `lam` itself. It remains to prove that the hull is extensional, which is the final condition needed to make its collapse injective.
<!--zh-->
秩刻画随之把它提升为空集属于指数 `lam` 本身。余下需要证明壳的外延性，这是使其塌缩成为单射所需的最后条件。
<!--ja-->
ランクによる特徴づけにより、空集合が指数 `lam` 自身に属することが従います。残るのは包の外延性であり、これはその崩壊を単射にするために必要な最後の条件です。
<!--/-->

```agda
  ∅∈λ : ⟨ ∅ ∈ˢ lam ⟩
  ∅∈λ = subst (λ w → ⟨ w ∈ˢ lam ⟩) (rank-fix ∅ ∅-ord)
    (rank-Lset lam ordλ ∅ ∅∈Lλ)
module HullExt (α : S) (ordα : IsOrd α)
  (X : S) (X⊆L : (x : S) → ⟨ x ∈ˢ X ⟩ → ⟨ x ∈ˢ Lset α ⟩)
```

<!--en-->
The empty-set membership assumption ensures that the Skolem hull at `Lset α` has the default value required by its term algebra.
<!--zh-->
空集属于指数这一假设，保证 `Lset α` 处的 Skolem 壳具有其项代数所需的默认值。
<!--ja-->
空集合が指数に属するという仮定により、`Lset α` における Skolem 包は、その項代数に必要な既定値をもちます。
<!--/-->

```agda
  (∅∈α : ⟨ ∅ ∈ˢ α ⟩) where

```

<!--en-->
Let `M` be the Skolem hull of `X` inside `Lset α`. Its inclusion into the stage is elementary. We compare formulas in the hull with their interpretations in the stage in order to prove that membership restricted to `M` is extensional.
<!--zh-->
令 `M` 为 `Lset α` 内由 `X` 生成的 Skolem 壳。它到该层的包含是初等的。为证明限制在 `M` 上的隶属关系具有外延性，我们比较壳中公式与其在该层中的解释。
<!--ja-->
`M` を、`Lset α` の内部で `X` から生成される Skolem 包とします。段階への包含は初等的です。`M` に制限した所属関係の外延性を示すため、包の中の論理式と段階での解釈を比較します。
<!--/-->

```agda
  module ASt = AtStage α ordα using ( module AbsL; module AtM; module Hull; SL )
  module H = ASt.Hull X X⊆L ∅∈α using ( module T; Hull⊆L )
  module A = ASt.AtM H.T.Hull H.Hull⊆L using ( SM; inL; module SemM )
  module E = HullElemDown α ordα X X⊆L ∅∈α using ( elem )
  module Mse = A.SemM.At A.SM id using ( _⊨_ )
```

<!--en-->
The hull is named, and the symmetric difference of two sets is stated at the level of membership truths: a point lies in one side and provably not in the other.
<!--zh-->
壳被命名；两集合的对称差在隶属真值层面陈述：一个点在一侧之中，且可证不在另一侧之中。
<!--ja-->
包が名付けられ、二つの集合の対称差が所属の真値の水準で述べられます。ある点が一方に属し、他方には属さないと証明できる、という形です。
<!--/-->

```agda

  M : S
  M = H.T.Hull
  Different : S → S → S → Type (ℓ-suc ℓ)
  Different x y z = (z ∈ᵗ x × (z ∈ᵗ y → Empty.⊥))
                  ⊎ (z ∈ᵗ y × (z ∈ᵗ x → Empty.⊥))
```

<!--en-->
Unequal sets have a point in their symmetric difference, classically: the truncated existence is decided by excluded middle.
<!--zh-->
经典地，不等的集合必有一点位于其对称差中：这一截断存在由排中律判定。
<!--ja-->
古典的に、等しくない集合は対称差の中に点をもちます。切り詰められた存在は、排中律によって判定されます。
<!--/-->

```agda
  different : (x y : S) → (x ≡ y → Empty.⊥) → ∥ Σ[ z ∈ S ] Different x y z ∥₁
  different x y nxy = go (lem P)
    where
    P : hProp (ℓ-suc ℓ)
    P = ∥ Σ[ z ∈ S ] Different x y z ∥₁ , squash₁
```

<!--en-->
If no point separated the sets, every membership truth would agree in both directions, and the universe's extensionality would force equality, contradicting the assumption.
<!--zh-->
若没有点区分这两个集合，则每个隶属真值都双向一致，宇宙的外延性将迫使二者相等，与假设矛盾。
<!--ja-->
もし二つの集合を区別する点がなければ、すべての所属命題が両方向で一致し、宇宙の外延性によって両者は等しくなり、仮定に矛盾します。
<!--/-->

```agda
    go : ⟨ P ⟩ ⊎ (⟨ P ⟩ → Empty.⊥) → ⟨ P ⟩
    go (inl p) = p
    go (inr np) = Empty.rec (nxy (extensionalV (λ z → ⇔toPath (fwd z) (bwd z))))
      where
      fwd : (z : S) → z ∈ᵗ x → z ∈ᵗ y
```

<!--en-->
Both directions of the agreement are decided by excluded middle, and each failing direction contributes its point to the symmetric difference.
<!--zh-->
一致的两个方向各由排中律判定，每个失败的方向都把它的点贡献给对称差。
<!--ja-->
一致の両方向は排中律で判定され、失敗した方向はそれぞれの点を対称差に加えます。
<!--/-->

```agda
      fwd z zx = Sum.rec (λ zy → zy)
        (λ nzy → Empty.rec (np ∣ z , inl (zx , nzy) ∣₁)) (lem (z ∈ˢ y))
      bwd : (z : S) → z ∈ᵗ y → z ∈ᵗ x
      bwd z zy = Sum.rec (λ zx → zx)
        (λ nzx → Empty.rec (np ∣ z , inr (zy , nzx) ∣₁)) (lem (z ∈ˢ x))
```

<!--en-->
The difference formula is the disjunction `(z ∈ x ∧ z ∉ y) ∨ (z ∈ y ∧ z ∉ x)`, with the two hull members occupying its constant slots.
<!--zh-->
差公式是析取式 `(z ∈ x ∧ z ∉ y) ∨ (z ∈ y ∧ z ∉ x)`，两个常元槽分别放入这两个壳成员。
<!--ja-->
差の公式は選言 `(z ∈ x ∧ z ∉ y) ∨ (z ∈ y ∧ z ∉ x)` であり、二つの定数欄に二つの包の要素を入れます。
<!--/-->

```agda
  φ : A.SM → A.SM → Formula A.SM 1
  φ x y = ((var zero ∈̇ con x) ∧̇ (¬̇ (var zero ∈̇ con y)))
        ∨̇ ((var zero ∈̇ con y) ∧̇ (¬̇ (var zero ∈̇ con x)))
  outer : (u v : S) (u∈M : u ∈ᵗ M) (v∈M : v ∈ᵗ M)
        → (z : S) → Different u v z
```

<!--en-->
Existential satisfaction is truncated, so the distinguishing point is returned under truncation. In either branch of the symmetric difference, the same point witnesses the corresponding disjunct of the formula in the stage.
<!--zh-->
存在公式的满足是截断的，因此区分点也在截断之下返回。在对称差的任一分支中，同一点都见证该公式在层中相应的析取支。
<!--ja-->
存在論理式の充足は切り詰められているので、区別する点も切り詰めの中で返します。対称差のどちらの分岐でも、同じ点が段階における論理式の対応する選言肢を証明します。
<!--/-->

```agda
        → ∥ Σ[ a ∈ ASt.SL ]
            ⟨ (a ∷ []) ASt.AbsL.⊨ᵐ (mapFo A.inL (φ (u , u∈M) (v , v∈M))) ⟩ ∥₁
  outer u v u∈M v∈M z d = ∣ a , ∣ objectDifferent d ∣₁ ∣₁
    where
    objectDifferent = Sum.map
```

<!--en-->
In either branch, ambient membership supplies the positive conjunct, while the nonmembership proof is lifted to the negation required by formula semantics. Transitivity of the stage places the distinguishing point in its carrier.
<!--zh-->
在任一分支中，外围隶属给出肯定合取项，而不隶属证明被提升为公式语义所需的否定。层的传递性则把区分点放入该层载体。
<!--ja-->
どちらの分岐でも、周囲での所属が肯定側の連言項を与え、不所属の証明を公式意味論が要求する否定へ持ち上げます。段階の推移性により、区別する点もその台に入ります。
<!--/-->

```agda
      (λ (zu , nzv) → zu , λ zv → lift (nzv zv))
      (λ (zv , nzu) → zv , λ zu → lift (nzu zu))
    z∈L : ⟨ z ∈ˢ Lset α ⟩
    z∈L = Sum.rec
      (λ (zx , _) → layer-trans (Lset-layer α) zx (H.Hull⊆L u u∈M))
```

<!--en-->
Pairing the distinguishing point with its stage membership makes it a witness in the stage carrier. To prove hull extensionality, assume first that every hull element belonging to `x` also belongs to `y`.
<!--zh-->
把区分点与其层隶属配对，便得到层载体中的见证。为证明壳的外延性，先假设壳中每个属于 `x` 的元素也属于 `y`。
<!--ja-->
区別する点をその段階への所属と組にすると、段階の台における証人が得られます。包の外延性を示すため、まず包の各要素について、`x` に属するなら `y` にも属すると仮定します。
<!--/-->

```agda
      (λ (zv , _) → layer-trans (Lset-layer α) zv (H.Hull⊆L v v∈M)) d
    a : ASt.SL
    a = z , z∈L
  refute : (x y : S) (x∈M : x ∈ᵗ M) (y∈M : y ∈ᵗ M)
         → (ag1 : (z : S) → z ∈ᵗ M → ⟨ z ∈ˢ x ⟩ → ⟨ z ∈ˢ y ⟩)
```

<!--en-->
Assume conversely that every hull element belonging to `y` also belongs to `x`. If `x` and `y` were nevertheless unequal, a point in their symmetric difference would lead to a contradiction.
<!--zh-->
反向再假设壳中每个属于 `y` 的元素也属于 `x`。若 `x` 与 `y` 仍不相等，则其对称差中的一点将导出矛盾。
<!--ja-->
逆に、包の各要素について、`y` に属するなら `x` にも属すると仮定します。それでも `x` と `y` が等しくないなら、対称差の点から矛盾が導かれます。
<!--/-->

```agda
         → (ag2 : (z : S) → z ∈ᵗ M → ⟨ z ∈ˢ y ⟩ → ⟨ z ∈ˢ x ⟩)
         → (x ≡ y → Empty.⊥) → Empty.⊥
  refute x y x∈M y∈M ag1 ag2 nxy = PT.rec Empty.isProp⊥ diff (different x y nxy)
    where
    xS : A.SM
```

<!--en-->
The two hull members are read as elements of the substructure carrier, ready to be plugged into the difference formula.
<!--zh-->
两个壳成员被读作子结构载体的元素，准备代入差公式。
<!--ja-->
二つの包の要素は、部分構造の台の要素として読まれ、差の論理式に代入する準備ができます。
<!--/-->

```agda
    xS = x , x∈M
    yS : A.SM
    yS = y , y∈M

```

<!--en-->
The refutation eliminates the difference point. Elementarity converts the stage's satisfaction of the existential formula, with the difference point as witness, into satisfaction of the same existential inside the hull.
<!--zh-->
反驳消去差点。初等性把层对该存在公式的满足，以差点为见证，转换为壳内对同一存在公式的满足。
<!--ja-->
反証は、差の点を消去します。初等性が、差の点を証人とする存在の論理式の段階での充足を、包の中での同じ存在の充足へ変えます。
<!--/-->

```agda
    diff : Σ[ z ∈ S ] Different x y z → Empty.⊥
    diff (z , d) = PT.rec Empty.isProp⊥ inside h
      where
      h : ⟨ [] Mse.⊨ (∃̇ (φ xS yS)) ⟩
      h = subst ⟨_⟩ (sym (E.elem 0 (∃̇ (φ xS yS)) []))
```

<!--en-->
Elementarity supplies a hull witness satisfying the difference formula. Eliminating its truncated disjunction reveals which of the two asymmetric membership statements holds.
<!--zh-->
初等性给出一个满足差公式的壳中见证。消去其截断的析取后，便得到两个非对称隶属陈述中成立的那个。
<!--ja-->
初等性により、差の論理式を満たす包の中の証人が得られます。その切り詰められた選言を消去すると、二つの非対称な所属命題のどちらが成り立つかが得られます。
<!--/-->

```agda
        (outer x y x∈M y∈M z d)
      inside : Σ[ b ∈ A.SM ] ⟨ (b ∷ []) Mse.⊨ φ xS yS ⟩ → Empty.⊥
      inside (b , q) = PT.rec Empty.isProp⊥ cases q
        where
        cases : (⟨ fst b ∈ˢ x ⟩ × (⟨ fst b ∈ˢ y ⟩ → Lift Empty.⊥))
```

<!--en-->
Either disjunct identifies the witness as a member of one hull member but not the other, and the corresponding agreement hypothesis contradicts the negation. This contradiction is exactly what extensionality of the hull requires.
<!--zh-->
无论哪个析取支，都会把见证认作一个壳成员的成员而非另一个的，相应的一致性假设与该否定矛盾。这一矛盾正是壳的外延性所需要的。
<!--ja-->
どちらの選言の枝でも、証人は一方の包の要素ではあって他方ではないとされ、対応する一致の仮定がその否定と矛盾します。この矛盾こそ、包の外延性が求めるものです。
<!--/-->

```agda
              ⊎ (⟨ fst b ∈ˢ y ⟩ × (⟨ fst b ∈ˢ x ⟩ → Lift Empty.⊥))
              → Empty.⊥
        cases (inl (bx , nby)) = lower (nby (ag1 (fst b) (snd b) bx))
        cases (inr (by , nbx)) = lower (nbx (ag2 (fst b) (snd b) by))

```

<!--en-->
Extensionality of the hull is proved by classical contradiction. Since the universe of sets is an h-set, `x ≡ y` is a proposition, so excluded middle gives either an equality or a refutation of equality. In the second case, `refute` turns `x ≢ y` into a hull member belonging to exactly one of `x` and `y`, contradicting the two membership-agreement hypotheses; hence `x ≡ y`.
<!--zh-->
壳的外延性由经典反证法证明。由于集合的宇宙是 h-集合，`x ≡ y` 是命题，排中律因此给出相等或不相等。若 `x ≢ y`，`refute` 会在壳中找到一个只属于 `x`、`y` 之一的成员，这与两个隶属一致性前提矛盾；故 `x ≡ y`。
<!--ja-->
包の外延性は古典的な背理法で証明する。集合の宇宙は h-集合なので `x ≡ y` は命題であり、排中律から等しい場合と等しくない場合に分かれる。`x ≢ y` なら、`refute` は包の中に `x` と `y` の一方だけに属する要素を与え、二つの所属一致の仮定に矛盾する。したがって `x ≡ y` である。
<!--/-->

```agda
  hullExt : isExt M
  hullExt x y x∈M y∈M ag1 ag2 =
    Sum.rec (λ p → p) (λ np → Empty.rec (bad np))
      (lem ((x ≡ y) , isSetS x y))
    where
```

<!--en-->
The contradictory branch is eliminated by `bad`, completing extensionality of the hull.
<!--zh-->
`bad` 消去矛盾分支，完成壳的外延性。
<!--ja-->
`bad` が矛盾する分岐を除き、包の外延性が完成する。
<!--/-->

```agda
    bad : (x ≡ y → Empty.⊥) → Empty.⊥
    bad = refute x y x∈M y∈M ag1 ag2
```

<!--en-->
## Carrying bounded formulas across the collapse
<!--zh-->
## 沿塌缩搬运有界公式
<!--ja-->
## 崩壊を通して有界論理式を移す
<!--/-->

<!--en-->
To compare the collapse with the ambient universe, now fix a transitive set `U`. A constant-free Δ₀ formula evaluated at members of `U` has the same truth value in the restricted structure on `U` as in the ambient structure.
<!--zh-->
为比较塌缩与外围宇宙，现固定一个传递集 `U`。无常元的 Δ₀ 公式在 `U` 的成员处求值时，在 `U` 上的受限结构与外围结构中具有相同真值。
<!--ja-->
崩壊と周囲の宇宙を比較するため、ここで推移的集合 `U` を固定する。定数を含まない Δ₀ 論理式を `U` の要素で評価すると、`U` 上の制限構造と周囲の構造で同じ真理値をもつ。
<!--/-->

```agda
module Unpack (U : S) (Utr : isTrans U) where

```

<!--en-->
An element of the restricted carrier `SM` is a set together with evidence that it belongs to `U`. Projecting each such pair to its first component gives the corresponding ambient environment, and bounded absoluteness `abs₀` compares satisfaction before and after this projection.
<!--zh-->
受限载体 `SM` 的元素由一个集合及其属于 `U` 的证据组成。把这些二元组逐项投影到第一分量，便得到对应的外围环境；有界绝对性 `abs₀` 比较投影前后的满足关系。
<!--ja-->
制限された台 `SM` の要素は、集合とそれが `U` に属する証拠との組である。各組を第一成分へ射影すると対応する周囲の環境が得られ、有界絶対性 `abs₀` が射影の前後の充足を比較する。
<!--/-->

```agda
  module Ab = FOL.Absoluteness.Single 𝒮ᵥ (λ x → x ∈ˢ U) Utr using (SM; abs₀; _⊨ᵐ_)

```

<!--en-->
For a constant-free Δ₀ formula `φ`, `read` first regards `embed φ` as a formula over the restricted carrier. Bounded absoluteness compares its restricted and ambient readings; `embed-⊨` removes the induced relabelling, and uniqueness of a function from the empty constant domain identifies the remaining constant interpretations.
<!--zh-->
对无常元的 Δ₀ 公式 `φ`，`read` 先把 `embed φ` 看作受限载体上的公式。有界绝对性比较其受限读法与外围读法；`embed-⊨` 消去由嵌入引入的改名，空常元域到任意类型的函数唯一性再同一视余下的常元解释。
<!--ja-->
定数を含まない Δ₀ 論理式 `φ` について、`read` はまず `embed φ` を制限された台の上の論理式として扱う。有界絶対性が制限された読みと周囲の読みを比較し、`embed-⊨` が埋め込みに伴う改名を除き、空の定数領域からの関数の一意性が残る定数解釈を同定する。
<!--/-->

```agda
  read : {n : ℕ} {φ : Formula (⊥* {ℓ-suc ℓ}) n} → Δ₀ φ → (δ : Ab.SM ^ n)
       → (δ Ab.⊨ᵐ embed φ) ≡ (map fst δ ⊨ₚ φ)
  read {n} {φ} dφ δ =
      Ab.abs₀ (mapΔ₀ Empty.rec* dφ) δ
    ∙ embed-⊨ 𝒮ᵥ {K = Ab.SM} fst φ (map fst δ)
```

<!--en-->
The final path uses function extensionality: because the constant domain is empty, its two interpretations agree pointwise and hence are equal. We then fix the data for a hull inside `Lset lam`: an ordinal `lam` closed under successors and a starting set `X ⊆ Lset lam`.
<!--zh-->
最后一条路径使用函数外延性：常元域为空，所以两种常元解释逐点相同，因而相等。随后固定 `Lset lam` 内构造壳所需的数据：对后继封闭的序数 `lam`，以及起始集合 `X ⊆ Lset lam`。
<!--ja-->
最後のパスでは関数外延性を使う。定数領域が空なので、二つの定数解釈は各点で一致し、したがって等しい。次に `Lset lam` の内部で包を作るため、後続に閉じた順序数 `lam` と始集合 `X ⊆ Lset lam` を固定する。
<!--/-->

```agda
    ∙ cong (λ ι → SemV.At._⊨_ (⊥* {ℓ-suc ℓ}) ι (map fst δ) φ)
           (funExt (λ b → Empty.rec* b))
module Frame (lam : S) (ordλ : IsOrd lam)
  (succλ : (d : S) → ⟨ d ∈ˢ lam ⟩ → ⟨ sucV d ∈ˢ lam ⟩)
  (X : S) (X⊆Lλ : (z : S) → ⟨ z ∈ˢ X ⟩ → ⟨ z ∈ˢ Lset lam ⟩)
```

<!--en-->
We also assume `∅ ∈ lam`, the base-stage hypothesis used by the hull construction.
<!--zh-->
还假设 `∅ ∈ lam`；这是壳构造所需的基础层前提。
<!--ja-->
さらに `∅ ∈ lam` を仮定する。これは包の構成が用いる基底段階の仮定である。
<!--/-->

```agda
  (∅∈λ : ⟨ ∅ ∈ˢ lam ⟩) where

```

<!--en-->
Let `M` be the hull of `X` inside `Lset lam`. We use its inclusion into the stage, the resulting notion of elementarity, and the extensionality proved above.
<!--zh-->
令 `M` 为 `Lset lam` 内由 `X` 生成的壳。下文使用它到该层的包含、相应的初等性概念，以及上文证明的外延性。
<!--ja-->
`M` を `Lset lam` の内部で `X` から生成される包とする。以下では、段階への包含、それに対する初等性、そして上で証明した外延性を用いる。
<!--/-->

```agda
  module HS = HullStage lam ordλ succλ X X⊆Lλ ∅∈λ using (module ASt; module C; module Condense; module H; M)
  module ASt = HS.ASt using (module AbsL; module AtM; Ltr; SL)
  module A = ASt.AtM HS.M HS.H.Hull⊆L using (Elementary; SM; module SemM; inL)
  module HE = HullExt lam ordλ X X⊆Lλ ∅∈λ using (hullExt)

```

<!--en-->
Thus `M` is extensional. This is the hypothesis needed to identify `M` with its transitive Mostowski collapse.
<!--zh-->
因此 `M` 是外延的；这正是把 `M` 与其传递的 Mostowski 塌缩同一视所需的前提。
<!--ja-->
したがって `M` は外延的である。これは `M` をその推移的な Mostowski 崩壊と同一視するために必要な仮定である。
<!--/-->

```agda
  Mext : isExt HS.M
  Mext = HE.hullExt

```

<!--en-->
The carry argument takes explicitly the elementarity of the inclusion `M → Lset lam`. Together with extensionality of `M`, this supplies the two comparisons used below: from the hull to the stage and from the hull to its collapse.
<!--zh-->
搬运论证显式取得包含 `M → Lset lam` 的初等性。它与 `M` 的外延性一起给出下文的两种比较：从壳到层，以及从壳到其塌缩。
<!--ja-->
移送の議論は、包含 `M → Lset lam` の初等性を明示的に受け取る。これと `M` の外延性から、以下で使う二つの比較、すなわち包から段階への比較と、包からその崩壊への比較が得られる。
<!--/-->

```agda
  module Carry (elem : A.Elementary) where

```

<!--en-->
The comparison now involves three structures: the hull `M`, the stage `Lset lam`, and the transitive collapse image `πX`. The collapse isomorphism relates the first and third, while bounded absoluteness relates each transitive set to the ambient universe.
<!--zh-->
现在要比较三个结构：壳 `M`、层 `Lset lam` 与传递塌缩像 `πX`。塌缩同构联系第一个与第三个结构，有界绝对性则把两个传递集各自联系到外围宇宙。
<!--ja-->
ここでは三つの構造、包 `M`、段階 `Lset lam`、推移的な崩壊像 `πX` を比較する。崩壊同型が第一と第三を結び、有界絶対性が二つの推移的集合をそれぞれ周囲の宇宙に結びつける。
<!--/-->

```agda
    module CIso = CollapseIso HS.M Mext using (module I; iso-fwd; iso-bwd)
    module TL = Unpack (Lset lam) ASt.Ltr using (read)
    module Tπ = Unpack HS.C.πX HS.C.πX-trans using (module Ab; read)

```

<!--en-->
Membership is preserved by the collapse directly: the forward direction of the membership isomorphism is exactly the push needed for atomic membership.
<!--zh-->
隶属由塌缩直接保持：隶属同构的正向恰是原子隶属所需的推送。
<!--ja-->
所属は崩壊によって直接保存されます。所属の同型の順方向が、原子的な所属に必要な押し出しにちょうど当たります。
<!--/-->

```agda
    member-push : (x y : S) → ⟨ x ∈ˢ HS.M ⟩ → ⟨ y ∈ˢ HS.M ⟩
                → ⟨ y ∈ˢ x ⟩ → ⟨ HS.C.π y ∈ˢ HS.C.π x ⟩
    member-push = CIso.iso-fwd

```

<!--en-->
Because `Lset lam` is transitive, every constant-free Δ₀ formula has equal restricted and ambient readings there; `atL` is `read` specialized to this stage.
<!--zh-->
由于 `Lset lam` 是传递的，每条无常元 Δ₀ 公式在该层的受限读法与外围读法相同；`atL` 就是 `read` 在此层的实例。
<!--ja-->
`Lset lam` は推移的なので、定数を含まない各 Δ₀ 論理式はそこで制限された読みと周囲の読みが一致する。`atL` はこの段階における `read` である。
<!--/-->

```agda
    atL : {n : ℕ} {φ : Formula (⊥* {ℓ-suc ℓ}) n} → Δ₀ φ → (δ : ASt.SL ^ n)
        → (δ ASt.AbsL.⊨ᵐ embed φ) ≡ (map fst δ ⊨ₚ φ)
    atL dφ δ = TL.read dφ δ

```

<!--en-->
The collapse image `πX` is also transitive, so the same agreement holds there for constant-free Δ₀ formulas.
<!--zh-->
塌缩像 `πX` 也具有传递性，因此无常元 Δ₀ 公式在那里同样具有内外一致的读法。
<!--ja-->
崩壊像 `πX` も推移的なので、定数を含まない Δ₀ 論理式について同じ内外の一致が成り立つ。
<!--/-->

```agda
    atπ : {n : ℕ} {φ : Formula (⊥* {ℓ-suc ℓ}) n} → Δ₀ φ → (δ : Tπ.Ab.SM ^ n)
        → (δ Tπ.Ab.⊨ᵐ embed φ) ≡ (map fst δ ⊨ₚ φ)
    atπ dφ δ = Tπ.read dφ δ

```

<!--en-->
For the hull's own carrier, the reading factors through elementarity: the embedded formula is first read internally, the relabelling is fixed because the formula carries no constants, and the result is transported to the stage reading.
<!--zh-->
壳自身载体处的读法经由初等性分解：嵌入公式先在内部读取；由于该公式无常元，改名固定不动；结果再搬运到层读法。
<!--ja-->
包自身の台のもとの読みは、初等性を通って分解されます。埋め込まれた論理式はまず内部で読まれ、その論理式が定数を運ばないため改名は固定され、結果は段階の読みへ運ばれます。
<!--/-->

```agda
    atM : {n : ℕ} {φ : Formula (⊥* {ℓ-suc ℓ}) n} → Δ₀ φ → (δ : A.SM ^ n)
        → (δ CIso.I.⊨ᵐ embed φ) ≡ (map fst δ ⊨ₚ φ)
    atM {n} {φ} dφ δ =
        elem n (embed φ) δ
      ∙ cong (λ ψ → map A.inL δ ASt.AbsL.⊨ᵐ ψ) (embed-map A.inL φ)
```

<!--en-->
After stage absoluteness, only the environments must be compared. Including a hull member into `Lset lam` does not change its underlying set, so projecting the included environment gives the same vector of ambient sets as projecting the original environment.
<!--zh-->
经过层上的绝对性后，只需比较两个环境。把壳成员包含进 `Lset lam` 不改变其底层集合，因此先包含再投影所得的外围集合向量，等于直接投影原环境所得的向量。
<!--ja-->
段階での絶対性の後に残るのは環境の比較だけである。包の要素を `Lset lam` に含めても基礎にある集合は変わらないので、包含してから射影した周囲の集合のベクトルは、元の環境を直接射影したものに等しい。
<!--/-->

```agda
      ∙ atL dφ (map A.inL δ)
      ∙ cong (λ γ → γ ⊨ₚ φ) (map-inL-fst δ)
      where
      map-inL-fst : {m : ℕ} (γ : A.SM ^ m)
                  → map fst (map A.inL γ) ≡ map fst γ
```

<!--en-->
This equality is immediate for the empty environment and is preserved when one entry is prepended. Hence, for a constant-free Δ₀ formula, ambient truth at an environment of hull members implies ambient truth at the environment of their collapse values.
<!--zh-->
该等式对空环境立即成立，并在环境前添加一个分量时保持。因此，对无常元 Δ₀ 公式，壳成员环境处的外围真值蕴含其塌缩值环境处的外围真值。
<!--ja-->
この等式は空の環境では直ちに成り立ち、環境の先頭に一つの成分を加えても保たれる。したがって、定数を含まない Δ₀ 論理式について、包の要素からなる環境での周囲の真理は、それらの崩壊値からなる環境での周囲の真理を導く。
<!--/-->

```agda
      map-inL-fst [] = refl
      map-inL-fst (q ∷ γ) = cong (fst q ∷_) (map-inL-fst γ)
    push : {n : ℕ} {φ : Formula (⊥* {ℓ-suc ℓ}) n} → Δ₀ φ → (δ : A.SM ^ n)
         → ⟨ map fst δ ⊨ₚ φ ⟩
         → ⟨ map fst (map CIso.I.g δ) ⊨ₚ φ ⟩
```

<!--en-->
Starting from ambient truth at the hull environment, `atM` is used backward to obtain internal truth in the hull. `iso-inv` carries that truth to the collapse image, `embed-map` removes the vacuous relabelling of constants, and `atπ` is used forward to return to ambient truth at the collapse values.
<!--zh-->
从壳环境处的外围真值出发，先反向使用 `atM` 得到壳中的内部真值；`iso-inv` 把它搬到塌缩像，`embed-map` 消去无内容的常元改名，最后正向使用 `atπ` 得到塌缩值处的外围真值。
<!--ja-->
包の環境での周囲の真理から出発し、まず `atM` を逆向きに使って包の内部の真理を得る。`iso-inv` がそれを崩壊像へ移し、`embed-map` が空虚な定数の改名を除き、最後に `atπ` を順向きに使って崩壊値での周囲の真理へ戻す。
<!--/-->

```agda
    push {n} {φ} dφ δ h =
      subst ⟨_⟩ (atπ dφ (map CIso.I.g δ))
        (subst (λ ψ → ⟨ map CIso.I.g δ CIso.I.⊨ᵖᵐ ψ ⟩)
               (embed-map CIso.I.g φ)
               (CIso.I.iso-inv n (embed φ) δ (subst ⟨_⟩ (sym (atM dφ δ)) h)))
```

<!--en-->
For `pull`, ambient truth at the collapse values is moved backward along `atπ` into the collapse image. After `embed-map` restores the relabelled form, `iso-inv-bwd` returns to internal truth in the hull, and `atM` is used forward to recover ambient truth at the original hull environment.
<!--zh-->
在 `pull` 中，塌缩值处的外围真值先沿 `atπ` 反向进入塌缩像；`embed-map` 恢复改名后的形式，`iso-inv-bwd` 再返回壳中的内部真值，最后正向使用 `atM`，恢复原壳环境处的外围真值。
<!--ja-->
`pull` では、崩壊値での周囲の真理を `atπ` に沿って逆向きに崩壊像の内部へ移す。`embed-map` で改名された形を戻し、`iso-inv-bwd` で包の内部の真理へ戻った後、`atM` を順向きに使って元の包の環境での周囲の真理を回復する。
<!--/-->

```agda

    pull : {n : ℕ} {φ : Formula (⊥* {ℓ-suc ℓ}) n} → Δ₀ φ → (δ : A.SM ^ n)
         → ⟨ map fst (map CIso.I.g δ) ⊨ₚ φ ⟩
         → ⟨ map fst δ ⊨ₚ φ ⟩
    pull {n} {φ} dφ δ h =
      subst ⟨_⟩ (atM dφ δ)
```

<!--en-->
Together, `push` and `pull` show that for every constant-free Δ₀ formula and every finite environment of hull members, ambient satisfaction is unchanged when each entry is replaced by its collapse value. The separate lemma `member-push` gives the corresponding direct preservation statement for membership.
<!--zh-->
`push` 与 `pull` 合起来表明：对每条无常元 Δ₀ 公式及每个由壳成员组成的有限环境，把各分量换成其塌缩值不会改变外围满足。另一个引理 `member-push` 则直接给出隶属关系的相应保持性。
<!--ja-->
`push` と `pull` を合わせると、定数を含まない任意の Δ₀ 論理式と、包の要素からなる任意の有限環境について、各成分をその崩壊値に置き換えても周囲での充足は変わらない。別の補題 `member-push` は、所属について対応する保存を直接与える。
<!--/-->

```agda
        (CIso.I.iso-inv-bwd n (embed φ) δ
          (subst (λ ψ → ⟨ map CIso.I.g δ CIso.I.⊨ᵖᵐ ψ ⟩)
                 (sym (embed-map CIso.I.g φ))
                 (subst ⟨_⟩ (sym (atπ dφ (map CIso.I.g δ))) h)))
```
