```agda
{-# OPTIONS --cubical --safe --guardedness #-}
```

<!--en-->
# Soundness and completeness of the closed code domain
<!--zh-->
# 封闭码定义域的可靠性与完备性
<!--ja-->
# 閉じた符号の定義域の健全性と完全性
<!--/-->

```agda
open import Base.Prelude
open import Base.Classical using ( LEM )
```

<!--en-->
Assume `lem : LEM (ℓ-suc ℓ)`. Every construction in the chapter is relative to this hypothesis, but the hypothesis does not strengthen the decoding conclusion: witnesses to decoded formulas remain propositionally truncated.
<!--zh-->
假设 `lem : LEM (ℓ-suc ℓ)`。本章的所有构造都相对于这一假设展开，但它并不加强解码结论：解码得到的公式见证仍处于命题截断之中。
<!--ja-->
`lem : LEM (ℓ-suc ℓ)` を仮定する。本章のすべての構成はこの仮定のもとで行われるが、仮定によって復号の結論が強くなるわけではない。復号された論理式の証人は、命題的に切り詰められたままである。
<!--/-->

```agda
module L.Coding.CodeDomainAdequacy {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where
```

```agda
open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using
  ( Formula; Term; var; con; _∈̇_; _≐_; _∧̇_; _∨̇_; _⇒̇_; ⊥̇; ∃̇_; ∀̇_; ∃̇∈; ∀̇∈ )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Coding {ℓ} using ( pr; pr-inj; #-inj′; #mono )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans )
open import L.Coding.Environment {ℓ} using ( env )
open import L.Coding.EnvironmentSet {ℓ} lem using ( envSet )
open import L.Axioms.Numerals {ℓ} using ( numeralL-fst; sucʟ; sucʟ-fst )
open import L.Coding.Model {ℓ} using ( appAt; appAt-adequate )
open import L.Coding.Expressions {ℓ} using ( sucAtL )
open import L.Coding.Model {ℓ} using ( container )
import L.Coding.Expressions {ℓ} as CodingExpressions
open import L.Coding.Quantification {ℓ} using
  ( i0; i1; i2; i3; i4; i5; i6; i7; i8; sh
  ; pr-out; pr-in; down; fstS; sndS; suc-out; suc-in
  ; sndEx; sndAll; bothEx
  ; sndEx-out; sndAll-in; bothEx-out; bothAll-in
  ; fillSnd; fillBoth; useSnd; useBoth
  ; f0; f1; f2; f3; f4; f5; f6; f7; f8; f9
  ; bigOr-in; bigOr-out )
open import L.Coding.EnvironmentTower {ℓ} lem using ( module Tower; nn )
open import L.Coding.CodeDomain {ℓ} using
  ( isTm; keyUp; keyExpr; atomKeyExpr; bndKeyExpr
  ; unKey; binKey; atomKey; bndKey
  ; Tags; shN; module Shape; shapeAt; module Close; closeAt; codesAt )
open import L.Coding.CodeAlphabet {ℓ} using ( module Alphabet )
open import L.Coding.Expressions {ℓ} using ( tagAtL-adequate )
open import L.Coding.Closure {ℓ} using ( closedAt; binSameClosed-in; unSuccClosed-in; binSuccClosed-in )
open import L.Coding.CodeShape {ℓ} using
  ( shapedAt; shaped-in; ShapeWit; BinWit; bothTm; fstTm; noneB; isTmAt )
open import L.Coding.CodeSet {ℓ} lem using
  ( AllCodes; AllCodes-out; key∈AllCodes; keyS; codeS; witnessAt-out )
open import L.Ordinal {ℓ} using ( ∈#-elim )
```

<!--en-->
Internal reasoning about syntax begins with a set of formula keys inside `L`. This chapter compares such a candidate domain with the external formula grammar in two directions: every member merely decodes to a formula key, and every genuine formula key belongs to the domain. These claims concern code membership, not the truth or satisfaction of the encoded formulas.
<!--zh-->
关于语法的内部论证从 `L` 中的一组公式键开始。本章从两个方向比较候选码域与外部公式文法：域中每个成员都纯粹地可解码为某条公式的键，而每条真实公式的键都属于该域。这些结论只涉及码的隶属，不涉及被编码公式的真值或满足关系。
<!--ja-->
構文についての内部的な議論は、`L` の中の論理式キーの集合から始まる。本章は、候補となる符号領域と外部の論理式文法を二方向に比較する。領域の各要素は、ある論理式のキーへ単に復号でき、すべての真正な論理式キーは領域に属する。これらは符号の所属についての主張であり、符号化された論理式の真理や充足についての主張ではない。
<!--/-->

<!--en-->
The argument uses excluded middle together with propositional truncation. Truncation records that a decoding witness exists without choosing one, and it may be eliminated only when the target is again a proposition.
<!--zh-->
以下论证同时使用排中律与命题截断。命题截断只记录解码见证的存在，而不从中选定一个见证；只有当目标仍是命题时，才能消去这层截断。
<!--ja-->
以下の議論では、排中律と命題的切り詰めを併用する。命題的切り詰めは、復号の証人を選び出すことなく、その存在だけを記録する。この切り詰めを除去できるのは、行き先も命題である場合に限られる。
<!--/-->



<!--en-->
The chapter speaks about the full first-order language of set theory: formulas with the two bounded quantifiers as well as the unbounded ones, and terms built from variables and constants. These are the objects whose codes the domain must gather and describe.
<!--zh-->
本章谈论集合论的完整一阶语言：公式既含无界量词也含两个有界量词，词项由变元与常元建成。这些正是码域必须收集并描述的对象。
<!--ja-->
本章は集合論の完全な一階言語を扱う。論理式には非有界の量化子に加えて二つの有界量化子があり、項は変数と定数から作られる。領域が集めて記述すべき対象は、これらである。
<!--/-->

<!--en-->
Formula keys are nested ordered pairs, so injectivity of pairing recovers their arity, tag, and payload from an equality of keys. Natural-number arities are represented by von Neumann numerals, and constructible environment sets provide internal representatives for finite parameter vectors.
<!--zh-->
公式键是嵌套的有序对，因此有序对编码的单射性可从键的相等中恢复元数、标签与载荷。自然数元数由冯·诺伊曼数码表示，可构造环境集则为有限参数向量提供内部表示。
<!--ja-->
論理式キーは入れ子の順序対なので、対符号化の単射性により、キーの等しさからアリティ、タグ、ペイロードを復元できる。自然数のアリティはフォン・ノイマン数項で表され、構成可能な環境集合が有限パラメータベクトルの内部表現を与える。
<!--/-->

<!--en-->
The object language can express that a structurally assembled key belongs to a candidate domain. Ordered-pair expressions build the nested key, and their adequacy theorem identifies satisfaction of the resulting formula with membership of the corresponding host-level pair code.
<!--zh-->
对象语言能够表达按结构组装的键属于候选域。有序对表达式构造嵌套键，其充分性定理则把所得公式的满足与对应宿主层有序对码的隶属等同起来。
<!--ja-->
対象言語では、構造に従って組み立てたキーが候補領域に属することを表現できる。順序対の式が入れ子のキーを構成し、その妥当性定理が、得られた論理式の充足と、対応するホスト側の対符号への所属とを同一視する。
<!--/-->

```agda
module E = CodingExpressions.PairExpression
```

<!--en-->
Quantifier codes change arity. The body of either kind of quantifier is a key at the successor arity, while a bounded quantifier also carries a term legal at the current arity. The semantic lemmas for pairs, successors, and extended environments express precisely these changes under binders.
<!--zh-->
量词码会改变元数。无界与有界量词的主体都是后继元数处的键，而有界量词还携带一个在当前元数处合法的词项。关于配对、后继与扩展环境的语义引理恰好表达这些约束子下的变化。
<!--ja-->
量化子の符号ではアリティが変わる。どちらの量化子でも本体は後続アリティのキーであり、有界量化子はさらに現在のアリティで正当な項をもつ。対、後続、拡張環境についての意味論的補題が、束縛子の下で起こるこれらの変化を正確に表す。
<!--/-->

<!--en-->
Existential payload descriptions are propositionally truncated, sometimes through two nested witnesses. Their inward and outward readings preserve that truncation. The ten constructor tags are represented by the numerals zero through nine, and a separate environment tower records the arity at which each code is read.
<!--zh-->
存在载荷的描述采用命题截断，有时包含两层嵌套见证；其向内与向外读法都保持这一截断。十个构造子标签由零至九的数码表示，另有一座环境塔记录每个码被读取时的元数。
<!--ja-->
存在的なペイロードの記述は命題的に切り詰められ、ときには二重の証人を含む。その内向きと外向きの読みは、この切り詰めを保つ。十個の構成子タグは零から九までの数項で表され、別の環境塔が各符号を読むアリティを記録する。
<!--/-->

<!--en-->
The description `codesAt` has two complementary halves. `shapeAt` reads an existing domain member as one of the ten constructor shapes and, for composite codes, requires its immediate subkeys to remain in the domain. `closeAt` goes in the generating direction: legal terms and existing subkeys produce the corresponding new key.
<!--zh-->
描述 `codesAt` 有两个互补部分。`shapeAt` 把域中已有成员读成十种构造形状之一，并要求复合码的直接子键仍在域中。`closeAt` 沿生成方向陈述：合法词项与已有子键会产生相应的新键。
<!--ja-->
記述 `codesAt` には、相補的な二つの部分がある。`shapeAt` は領域の既存要素を十種類の構成子形のいずれかとして読み、複合符号では直下の部分キーも領域に残ることを要求する。`closeAt` は生成する向きの主張であり、正当な項と既存の部分キーから対応する新しいキーが得られる。
<!--/-->

<!--en-->
A constructor tag is an element of `Fin 10`; its natural-number value selects one of the ten payload predicates and is automatically less than ten. Environments are finite vectors, while the codes stored in the hierarchy are nested set-theoretic pairs.
<!--zh-->
构造子标签是 `Fin 10` 的元素；其自然数值选取十个载荷谓词之一，并自动小于十。环境是有限向量，而层级中存放的码则是嵌套的集合论有序对。
<!--ja-->
構成子タグは `Fin 10` の要素である。その自然数値が十個のペイロード述語の一つを選び、その値は自動的に十未満である。環境は有限ベクトルであり、階層に格納される符号は入れ子の集合論的順序対である。
<!--/-->

```agda
open import Cubical.Data.FinData.Properties using ( toℕ<n )
```

<!--en-->
Decoding branches over disjoint constructor cases and often returns only a propositionally truncated witness. Pair equalities are transported componentwise, and impossible tags lead to the empty type. None of these operations turns a merely existing formula into a globally chosen decoder.
<!--zh-->
解码按互斥的构造情形分支，并常常只返回命题截断的见证。对的等式按分量搬运，不可能的标签则导向空类型。这些操作都不会把纯粹存在的公式提升为全局选定的解码器。
<!--ja-->
復号は互いに排他的な構成子の場合に分かれ、多くの場合、命題的に切り詰められた証人だけを返す。対の等しさは成分ごとに移され、不可能なタグは空型へ至る。これらの操作から、単に存在する論理式を大域的に選ぶ復号写像は得られない。
<!--/-->

<!--en-->
The cumulative hierarchy supplies set-valued ordered-pair codes, von Neumann numerals, and the successor operation on arities. Membership has a small fibre presentation, and equality of hierarchy sets is a proposition; these facts justify the truncated decompositions and their elimination into membership or equality claims.
<!--zh-->
累积层级提供集合值的有序对码、冯·诺伊曼数码以及元数的后继运算。隶属具有小纤维表示，而层级中集合的相等是命题；这些事实使截断分解及其到隶属或相等结论的消去成立。
<!--ja-->
累積階層は、集合値の順序対符号、フォン・ノイマン数項、アリティの後続演算を与える。所属には小さなファイバー表示があり、階層の集合の等しさは命題である。これらの事実により、切り詰められた分解と、所属や等しさへのその消去が正当化される。
<!--/-->

```agda
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_; setIsSet )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫; ∈-asFiber )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet )
open InfinitySet {ℓ} using ( #_; sucV )
```

<!--en-->
The carrier of the constructible structure is fixed as `S`, so every environment and every formula reading below lives over it.
<!--zh-->
可构造结构的载体被固定为 `S`，以下每个环境与每条公式读法都居于其上。
<!--ja-->
構成可能な構造の台が `S` として固定され、以下のすべての環境と論理式の読みがその上にある。
<!--/-->

```agda
open hPropStructure 𝒮ʟ using ( S )
```

<!--en-->
All code descriptions are interpreted in the first-order structure carried by `L`. Thus“this assembled key belongs to `C`”has both an object-language formulation and a host-level membership reading; the adequacy lemmas identify these two forms of the same assertion.
<!--zh-->
所有码描述都在 `L` 所承载的一阶结构中解释。因此，「这个组装出的键属于 `C`」既可以写成对象语言公式，也可以读作宿主层的隶属陈述；充分性引理把同一断言的这两种形式等同起来。
<!--ja-->
符号の記述はすべて、`L` が担う一階構造で解釈される。したがって、「組み立てたキーが `C` に属する」という主張には、対象言語の論理式としての形と、ホスト側の所属としての読みがある。妥当性補題は、同じ主張のこの二つの形を同一視する。
<!--/-->

```agda
module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans using ( _^_; _⊨ᵐ_ )
open AbsL using ( _^_ ) renaming ( _⊨ᵐ_ to _⊨_ )
```

<!--en-->
## Reading the description
<!--zh-->
## 读取描述
<!--ja-->
## 記述の読み出し
<!--/-->

<!--en-->
Term codes are described first. A set `t` is a term code at arity `ar` when, merely, it is the pair of the tag zero with an element of the working set `Wv`, or the pair of the tag one with an element of the set `ar`. Note that `ar` is still an arbitrary set here; only when it is known to be a numeral does the second branch recover a bounded variable index.
<!--zh-->
先描述词项码。集合 `t` 是元数 `ar` 处的词项码，当它「仅仅」是：标签零与工作集 `Wv` 中一个元素组成的对，或标签一与集合 `ar` 中一个元素组成的对。注意此处 `ar` 仍是任意集合；只有当已知它是数码时，第二支才恢复出一个有界变元索引。
<!--ja-->
まず、項の符号を記述する。集合 `t` がアリティ `ar` の項の符号であるのは、それが単に、タグ零と作業集合 `Wv` の要素の対、あるいはタグ一と集合 `ar` の要素の対であるときである。ここでの `ar` はまだ任意の集合である。それが数項だと分かってはじめて、第二の分岐から有界な変数の添字が復元される。
<!--/-->

```agda
IsTmV : V ℓ → V ℓ → V ℓ → Type (ℓ-suc ℓ)
IsTmV Wv t ar = ∥ (Σ[ x ∈ V ℓ ] ((t ≡ pr (# 0) x) × ⟨ x ∈ Wv ⟩))
                ⊎ (Σ[ i ∈ V ℓ ] ((t ≡ pr (# 1) i) × ⟨ i ∈ ar ⟩)) ∥₁
```

<!--en-->
The first three payload predicates cover atomic formulas, binary connectives, and falsity. An atomic payload merely decomposes into two legal term codes; a binary payload merely decomposes into two same-arity subkeys already in the candidate domain; the falsity payload is directly the equality `r = # 0` and carries no existential witness.
<!--zh-->
前三类载荷谓词分别对应原子公式、二元联结词与假。原子载荷纯粹地分解为两个合法词项码；二元载荷纯粹地分解为候选域中两个同元数子键；假的载荷则直接是等式 `r = # 0`，不含存在见证。
<!--ja-->
最初の三種類のペイロード述語は、原子論理式、二項結合子、偽を扱う。原子のペイロードは二つの正当な項符号へ単に分解され、二項のペイロードは候補領域にすでに属する同じアリティの二つの部分キーへ単に分解される。偽のペイロードは直接の等式 `r = # 0` であり、存在証人をもたない。
<!--/-->

<details open class="submodule-fold">
<summary class="submodule-fold-heading">
```agda
module CodesSem (Wv Cv : V ℓ) where
```
</summary>
<div class="submodule-fold-content">

```agda
  AtomP BinP ConP QuP BqP : V ℓ → V ℓ → Type (ℓ-suc ℓ)
  AtomP ar r = ∥ Σ[ t ∈ V ℓ ] Σ[ u ∈ V ℓ ] ((r ≡ pr t u) × (IsTmV Wv t ar × IsTmV Wv u ar)) ∥₁
  BinP ar r = ∥ Σ[ a ∈ V ℓ ] Σ[ b ∈ V ℓ ] ((r ≡ pr a b) × (⟨ pr ar a ∈ Cv ⟩ × ⟨ pr ar b ∈ Cv ⟩)) ∥₁
  ConP ar r = r ≡ # 0
```

<!--en-->
The quantifier payloads complete the list. An unbounded-quantifier payload is a subkey at the successor arity. A bounded-quantifier payload pairs a term code legal at the current arity with such a subkey. This asymmetry comes from the grammar itself: the body has successor arity, whereas the bounding term has the arity of the quantified formula.
<!--zh-->
量词载荷补全了这份清单。无界量词的载荷是后继元数处的子键；有界量词的载荷还把一个在当前元数处合法的词项码与这样的子键配成一对。这种不对称来自文法本身：主体具有后继元数，界词项则具有被量化公式的元数。
<!--ja-->
量化子のペイロードで一覧が完成する。非有界量化子のペイロードは、後続アリティにある下位キーである。有界量化子のペイロードは、現在のアリティで正当な項符号と、そのような下位キーとの対である。この非対称性は文法そのものに由来する。本体は後続アリティをもち、境界を表す項は量化された論理式と同じアリティをもつ。
<!--/-->

```agda
  QuP ar r = ⟨ pr (sucV ar) r ∈ Cv ⟩
  BqP ar r = ∥ Σ[ t ∈ V ℓ ] Σ[ a ∈ V ℓ ] ((r ≡ pr t a) × (IsTmV Wv t ar × ⟨ pr (sucV ar) a ∈ Cv ⟩)) ∥₁
```

<!--en-->
The payload table begins: tags zero and one carry the two atom shapes, and tags two and three carry the binary shapes of conjunction and disjunction.
<!--zh-->
载荷表开始：标签零与一承载两种原子形状，标签二与三承载合取与析取的二元形状。
<!--ja-->
ペイロードの表はここからはじまる。タグ零と一が二つの原子の形を、タグ二と三が連言と選言の二項の形を担う。
<!--/-->

```agda
  PayN : ℕ → V ℓ → V ℓ → Type (ℓ-suc ℓ)
  PayN 0 = AtomP
  PayN 1 = AtomP
  PayN 2 = BinP
  PayN 3 = BinP
```

<!--en-->
The table continues: tag four carries implication, tag five the constant falsity, tags six and seven the two unbounded quantifiers, and tag eight the bounded universal.
<!--zh-->
表继续：标签四承载蕴涵，标签五承载常假，标签六与七承载两个无界量词，标签八承载有界全称。
<!--ja-->
表は続き、タグ四が含意、タグ五が定数の偽、タグ六と七が二つの非有界量化子、タグ八が有界の全称を担う。
<!--/-->

```agda
  PayN 4 = BinP
  PayN 5 = ConP
  PayN 6 = QuP
  PayN 7 = QuP
  PayN 8 = BqP
```

<!--en-->
Tag nine carries the bounded existential payload. The auxiliary family `PayN` is empty at every natural number at least ten, but a legal `Key` chooses its tag from `Fin 10`; hence only the ten cases zero through nine can occur in a key.
<!--zh-->
标签九承载有界存在量词的载荷。辅助族 `PayN` 在每个不小于十的自然数处都是空类型，但合法 `Key` 的标签取自 `Fin 10`；因此键中只可能出现零至九这十种情形。
<!--ja-->
タグ九は有界存在量化子のペイロードを担う。補助族 `PayN` は十以上の自然数では空型であるが、正当な `Key` のタグは `Fin 10` から選ばれる。したがって、キーに現れうるのは零から九までの十種類だけである。
<!--/-->

```agda
  PayN 9 = BqP
  PayN (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc _)))))))))) _ _ = ⊥*
```

<!--en-->
A key at arity `ar` is, merely, a tag from the ten together with a payload of the matching shape. Note what a key is not: it is not an inductive syntax tree, and the decomposition is not claimed to be unique data. A key is the truncated evidence that a set-coded pair splits into one of ten known shapes.
<!--zh-->
元数 `ar` 处的键「仅仅」是十个标签之一连同匹配形状的载荷。注意键不是什么：它不是归纳的语法树，其分解也不被主张为唯一数据。键只是「一个集合编码的对可拆成十种已知形状之一」的截断证据。
<!--ja-->
アリティ `ar` でのキーとは、単に、十のタグの一つと、それに合った形のペイロードのことである。キーが何でないかに注意してほしい。キーは帰納的な構文木ではなく、その分解が一意なデータだとも主張していない。キーとは、集合として符号化された対が、既知の十の形のどれかに分解されるという、切り詰められた証拠なのである。
<!--/-->

```agda
  Key : V ℓ → V ℓ → Type (ℓ-suc ℓ)
  Key ar p = ∥ Σ[ k ∈ Fin 10 ] Σ[ r ∈ V ℓ ] ((p ≡ pr (# (toℕ k)) r) × PayN (toℕ k) ar r) ∥₁
```
</div>
</details>

<!--en-->
Fix an environment containing a proposed term code `t`, an arity set `ar`, a working set `Wv`, and two entries known to be the numerals zero and one. Under these tag equations, the object-language predicate `isTm` can be compared exactly with the ambient predicate `IsTmV Wv t ar`.
<!--zh-->
固定一个环境，其中含候选词项码 `t`、元数集合 `ar`、工作集 `Wv`，以及两个已知分别为数码零和一的元素。在这些标签等式下，对象语言谓词 `isTm` 可与外围谓词 `IsTmV Wv t ar` 作精确比较。
<!--ja-->
候補となる項符号 `t`、アリティ集合 `ar`、作業集合 `Wv`、そしてそれぞれ数項零と一であることが分かっている二つの要素を含む環境を固定する。これらのタグ等式のもとで、対象言語の述語 `isTm` と外部の述語 `IsTmV Wv t ar` を正確に比較できる。
<!--/-->

<details open class="submodule-fold">
<summary class="submodule-fold-heading">
```agda
module _ {k : ℕ} (t ar w N0 N1 : Fin k) (δ : S ^ k)
  (q0 : fst (lookup N0 δ) ≡ # 0) (q1 : fst (lookup N1 δ) ≡ # 1) where
```
</summary>
<div class="submodule-fold-content">

```agda
  private
    Wv = fst (lookup w δ)
```

<!--en-->
The outward reading eliminates the truncated disjunction of the object-language formula. In the constant branch, the existential recovers the second component of the pair, the numeral equation aligns the tag, and the membership travels into `IsTmV`; the result is the left branch of the truncated definition.
<!--zh-->
向外读法消去对象语言公式的截断析取。常元支中，存在量词恢复对的第二分量，数码等式对齐标签，隶属则进入 `IsTmV`；结果即截断定义的左支。
<!--ja-->
外向きの読み出しは、対象言語の論理式の切り詰められた選言を消去する。定数の分岐では、存在量化が対の第二成分を取り出し、数項の等式がタグを揃え、所属が `IsTmV` へ入る。結果は、切り詰められた定義の左の分岐である。
<!--/-->

```agda
  isTm-out : ⟨ δ ⊨ isTm t ar w N0 N1 ⟩ → IsTmV Wv (fst (lookup t δ)) (fst (lookup ar δ))
  isTm-out = rec₁ squash₁
    (λ { (inl h) → map₁
           (λ { (v , s , (e , v∈)) → inl (fst v , (e ∙ cong (λ a → pr a (fst v)) q0 , v∈)) })
           (sndEx-out t N0 (var i0 ∈̇ var (sh 2 w)) δ h)
```

<!--en-->
The variable branch repeats the same three moves with the numeral one and the arity set, producing the right branch. Together the two branches say the object-language recognition and the set-level `IsTmV` are exactly equivalent.
<!--zh-->
变元支以数码一与元数集合重复同样三步，产出右支。两支合起来说明：对象语言的识别与集合层面的 `IsTmV` 恰好等价。
<!--ja-->
変数の分岐は、数項一とアリティの集合で同じ三歩を繰り返し、右の分岐を作る。二つの分岐合わせて、対象言語の認識と、集合レベルの `IsTmV` がまさに同値であることが言える。
<!--/-->

```agda
       ; (inr h) → map₁
           (λ { (v , s , (e , v∈)) → inr (fst v , (e ∙ cong (λ a → pr a (fst v)) q1 , v∈)) })
           (sndEx-out t N1 (var i0 ∈̇ var (sh 2 ar)) δ h) })
```

<!--en-->
The inward reading runs the conversion the other way. In the constant branch, the filling lemma places the witness `x` under the existential at slot zero, and the pair equation is transported along the reversed numeral equation so that the satisfaction matches the shape of the object-language formula.
<!--zh-->
向内读法反向执行同一转换。常元支中，填充引理把见证 `x` 置于零号槽的存在量词之下，而对等式沿反向的数码等式运输，使满足与对象语言公式的形状相合。
<!--ja-->
内向きの読み出しは、同じ変換を逆向きに行う。定数の分岐では、充填の補題が証人 `x` を枠零の存在量化子の下に置き、対の等式が逆向きの数項の等式に沿って運ばれて、充足が対象言語の論理式の形と一致するようにする。
<!--/-->

```agda
  isTm-in : IsTmV Wv (fst (lookup t δ)) (fst (lookup ar δ)) → ⟨ δ ⊨ isTm t ar w N0 N1 ⟩
  isTm-in = rec₁ (snd (δ ⊨ isTm t ar w N0 N1))
    (λ { (inl (x , (e , x∈))) →
           ∣ inl (fillSnd t δ (lookup N0 δ) (down (lookup w δ) x x∈)
                    (e ∙ cong (λ a → pr a x) (sym q0)) (var i0 ∈̇ var (sh 2 w)) x∈ N0 refl) ∣₁
```

<!--en-->
The variable branch fills the witness `i` under the existential at the numeral-one slot, transported by the corresponding reversed equation. The two branches close the equivalence in both directions.
<!--zh-->
变元支在数码一槽位的存在量词下填充见证 `i`，由相应的反向等式运输。两条支线双向闭合该等价。
<!--ja-->
変数の分岐は、数項一の枠の存在量化子の下に証人 `i` を満たし、対応する逆向きの等式に沿って運ぶ。二つの分岐が、この同値を両方向で閉じる。
<!--/-->

```agda
       ; (inr (i , (e , i∈))) →
           ∣ inr (fillSnd t δ (lookup N1 δ) (down (lookup ar δ) i i∈)
                    (e ∙ cong (λ a → pr a i) (sym q1)) (var i0 ∈̇ var (sh 2 ar)) i∈ N1 refl) ∣₁ })
```
</div>
</details>

<!--en-->
The predicate `keyUp C ar r` expresses one precise membership statement: the pair `(suc ar,r)` belongs to `C`. Its bounded existential presentation chooses an actual member of `C` and then exposes enough of that member to verify both its pair shape and the successor equation.
<!--zh-->
谓词 `keyUp C ar r` 精确表达一条隶属：有序对 `(suc ar,r)` 属于 `C`。它用有界存在量词选出 `C` 的一个实际成员，再逐层显露该成员，以验证其配对形状与后继等式。
<!--ja-->
述語 `keyUp C ar r` は、一つの正確な所属、すなわち対 `(suc ar,r)` が `C` に属することを表す。その有界存在による表現は、`C` の実際の要素を選び、その要素を順に明らかにして、対の形と後続の等式の両方を確かめる。
<!--/-->

<details open class="submodule-fold">
<summary class="submodule-fold-heading">
```agda
module _ {k : ℕ} (C ar r : Fin k) (δ : S ^ k) where
```
</summary>
<div class="submodule-fold-content">

```agda
  keyUp-out : ⟨ δ ⊨ keyUp C ar r ⟩ → ⟨ pr (sucV (fst (lookup ar δ))) (fst (lookup r δ)) ∈ fst (lookup C δ) ⟩
  keyUp-out = rec₁ (snd (pr (sucV (fst (lookup ar δ))) (fst (lookup r δ)) ∈ fst (lookup C δ)))
    (λ { (c' , (c'∈ , h)) → rec₁ (snd (pr (sucV (fst (lookup ar δ))) (fst (lookup r δ)) ∈ fst (lookup C δ)))
      (λ { (s , (s∈ , h')) → rec₁ (snd (pr (sucV (fst (lookup ar δ))) (fst (lookup r δ)) ∈ fst (lookup C δ)))
```

<!--en-->
In the outward direction, the pair formula identifies the chosen member of `C` with `(ar',r)`, while the successor formula identifies `ar'` with `suc ar`. Transporting membership along these two equalities yields `(suc ar,r) ∈ C`. All truncated witnesses are eliminated only into this membership proposition.
<!--zh-->
向外读取时，配对公式把选出的 `C` 成员认作 `(ar',r)`，后继公式再把 `ar'` 认作 `suc ar`。沿这两条等式搬运隶属，便得到 `(suc ar,r) ∈ C`。所有截断见证都只消去到这条隶属命题中。
<!--ja-->
外向きには、対の論理式が選ばれた `C` の要素を `(ar',r)` と同一視し、後続の論理式が `ar'` を `suc ar` と同一視する。この二つの等式に沿って所属を移すと、`(suc ar,r) ∈ C` が得られる。切り詰められた証人はすべて、この所属命題へのみ消去される。
<!--/-->

```agda
        (λ { (ar' , (ar'∈ , (e , hs))) →
          subst (λ u → ⟨ u ∈ fst (lookup C δ) ⟩)
            (pr-out i2 i0 (sh 3 r) (ar' ∷ s ∷ c' ∷ δ) e
             ∙ cong (λ a → pr a (fst (lookup r δ))) (suc-out (sh 3 ar) i0 (ar' ∷ s ∷ c' ∷ δ) hs))
            c'∈ })
```

<!--en-->
The three bounded witnesses therefore serve only to certify the displayed member of `C`; after their truncations are eliminated, `keyUp-out` has exactly the ambient membership statement `(suc ar,r) ∈ C`.
<!--zh-->
因此，三层有界见证只用于证明所展示的对象确为 `C` 的成员；消去其截断后，`keyUp-out` 得到的恰是外围隶属陈述 `(suc ar,r) ∈ C`。
<!--ja-->
したがって、三層の有界な証人は、表示された対象が `C` の要素であることを確かめるためだけに使われる。その切り詰めを消去した結果、`keyUp-out` は外部の所属 `(suc ar,r) ∈ C` をちょうど与える。
<!--/-->

```agda
        h' })
      h })
```

<!--en-->
For the inward direction, start with `(suc ar,r) ∈ C`. Present the successor arity as a constructible set, package the ordered pair with `r`, and use these objects as the three bounded witnesses. The pair and successor formulas then reconstruct satisfaction of `keyUp C ar r`.
<!--zh-->
向内读取时，从 `(suc ar,r) ∈ C` 出发。把后继元数呈现为可构造集合，将它与 `r` 组成的有序对打包，再以这些对象充当三层有界见证；配对公式与后继公式由此重建 `keyUp C ar r` 的满足。
<!--ja-->
内向きには、`(suc ar,r) ∈ C` から始める。後続アリティを構成可能集合として提示し、それと `r` の順序対をまとめ、これらを三つの有界な証人として使う。すると、対と後続の論理式から `keyUp C ar r` の充足が再構成される。
<!--/-->

```agda
  keyUp-in : ⟨ pr (sucV (fst (lookup ar δ))) (fst (lookup r δ)) ∈ fst (lookup C δ) ⟩ → ⟨ δ ⊨ keyUp C ar r ⟩
  keyUp-in h = ∣ c' , (h , ∣ c .fst , (c .snd .fst , ∣ ar' , (c .snd .snd .fst
    , ( pr-in i2 i0 (sh 3 r) (ar' ∷ c .fst ∷ c' ∷ δ) (sym (cong (λ a → pr a (fst (lookup r δ))) (sucʟ-fst (lookup ar δ))))
      , suc-in (sh 3 ar) i0 (ar' ∷ c .fst ∷ c' ∷ δ) (sucʟ-fst (lookup ar δ)) )) ∣₁) ∣₁) ∣₁
    where
```

<!--en-->
Concretely, `ar'` represents `suc ar`, `c'` represents the member `(suc ar,r)` of `C`, and the containing set supplied with `c'` witnesses the bounded-membership chain used by the formula. Their underlying-set equations ensure that the internal witnesses denote the intended ambient pair.
<!--zh-->
具体地，`ar'` 表示 `suc ar`，`c'` 表示 `C` 的成员 `(suc ar,r)`，而与 `c'` 一同给出的包含集则见证公式所用的有界隶属链。它们的底层集合等式保证内部见证确实表示预期的外围有序对。
<!--ja-->
具体的には、`ar'` が `suc ar` を表し、`c'` が `C` の要素 `(suc ar,r)` を表す。さらに `c'` とともに与えられる包含集合が、論理式で使う有界所属の鎖を証する。それぞれの基礎集合の等式により、内部の証人が意図した外部の対を表すことが保証される。
<!--/-->

```agda
    ar' : S
    ar' = sucʟ (lookup ar δ)
    c' : S
    c' = down (lookup C δ) (pr (sucV (fst (lookup ar δ))) (fst (lookup r δ))) h
    c = container c' ar' (lookup r δ) (cong (λ a → pr a (fst (lookup r δ))) (sym (sucʟ-fst (lookup ar δ))))
```
</div>
</details>

<!--en-->
Fix a candidate domain `C`, an arity value `A`, a tag value `N`, and a payload `a`. The unary key assembled from these data is the nested pair `(A,(N,a))`.
<!--zh-->
固定候选域 `C`、元数值 `A`、标签值 `N` 与载荷 `a`。由这些数据组装的一元键是嵌套有序对 `(A,(N,a))`。
<!--ja-->
候補領域 `C`、アリティ値 `A`、タグ値 `N`、ペイロード `a` を固定する。これらから組み立てる単項キーは、入れ子の対 `(A,(N,a))` である。
<!--/-->

<details open class="submodule-fold">
<summary class="submodule-fold-heading">
```agda
module _ {k : ℕ} (C ar N a : Fin k) (δ : S ^ k) where
```
</summary>
<div class="submodule-fold-content">

```agda
  private
    Cv = fst (lookup C δ)
    A = fst (lookup ar δ)
    Nv = fst (lookup N δ)
```

<!--en-->
The outward reading of `unKey` states precisely that the nested key `(A,(N,a))` belongs to `C`. Adequacy of the ordered-pair expression turns object-language membership into this host-level set-membership statement.
<!--zh-->
`unKey` 的向外读法精确说明嵌套键 `(A,(N,a))` 属于 `C`。有序对表达式的充分性把对象语言中的隶属转换为这条宿主层集合隶属陈述。
<!--ja-->
`unKey` の外向きの読みは、入れ子のキー `(A,(N,a))` が `C` に属することを正確に述べる。順序対の式の妥当性により、対象言語の所属は、ホスト側のこの集合所属へ変換される。
<!--/-->

```agda
  unKey-out : ⟨ δ ⊨ unKey C ar N a ⟩ → ⟨ pr A (pr Nv (fst (lookup a δ))) ∈ Cv ⟩
  unKey-out = E.member-out (keyExpr ar N (E.slot a)) (var C) δ
```

<!--en-->
Adequacy works in the reverse direction as well: membership `(A,(N,a)) ∈ C` yields satisfaction of the object-language predicate `unKey`. The key clause and its host-level reading therefore agree in both directions.
<!--zh-->
充分性也可反向使用：由 `(A,(N,a)) ∈ C` 可以得到对象语言谓词 `unKey` 的满足。因此，这条键子句与其宿主层读法双向一致。
<!--ja-->
妥当性は逆向きにも使える。所属 `(A,(N,a)) ∈ C` から、対象言語の述語 `unKey` の充足が得られる。したがって、キーの条項とホスト側での読みは、双方向に一致する。
<!--/-->

```agda
  unKey-in : ⟨ pr A (pr Nv (fst (lookup a δ))) ∈ Cv ⟩ → ⟨ δ ⊨ unKey C ar N a ⟩
  unKey-in = E.member-in (keyExpr ar N (E.slot a)) (var C) δ
```
</div>
</details>

<!--en-->
For a binary constructor, fix two payload components `a` and `b`. Their ordered pair `P=(a,b)` becomes the payload of the key `(A,(N,P))`; the arity and tag occupy the same outer positions as in the unary case.
<!--zh-->
对二元构造子，固定两个载荷分量 `a` 与 `b`。它们组成的有序对 `P=(a,b)` 成为键 `(A,(N,P))` 的载荷；元数与标签仍占据和一元情形相同的外层位置。
<!--ja-->
二項構成子について、二つのペイロード成分 `a` と `b` を固定する。その順序対 `P=(a,b)` がキー `(A,(N,P))` のペイロードとなり、アリティとタグは単項の場合と同じ外側の位置を占める。
<!--/-->

<details open class="submodule-fold">
<summary class="submodule-fold-heading">
```agda
module _ {k : ℕ} (C ar N a b : Fin k) (δ : S ^ k) where
```
</summary>
<div class="submodule-fold-content">

```agda
  private
    Cv = fst (lookup C δ)
    A = fst (lookup ar δ)
    Nv = fst (lookup N δ)
```

<!--en-->
The two argument values form the ordered pair `P = (a,b)`. This pair is the payload in the nested binary key `(A,(N,P))`.
<!--zh-->
两个实参值组成有序对 `P = (a,b)`。该有序对就是嵌套二元键 `(A,(N,P))` 的载荷。
<!--ja-->
二つの引数の値から順序対 `P = (a,b)` を作る。この対が、入れ子の二項キー `(A,(N,P))` のペイロードである。
<!--/-->

```agda
    P = pr (fst (lookup a δ)) (fst (lookup b δ))
```

<!--en-->
The outward reading of `binKey` is precisely the membership `(A,(N,(a,b))) ∈ C`. It preserves the three logical levels of the encoding: arity, constructor tag, and the paired arguments.
<!--zh-->
`binKey` 的向外读法恰为隶属 `(A,(N,(a,b))) ∈ C`。它保持编码的三个逻辑层次：元数、构造子标签与成对实参。
<!--ja-->
`binKey` の外向きの読みは、所属 `(A,(N,(a,b))) ∈ C` にほかならない。この形は、アリティ、構成子タグ、対にした引数という符号化の三つの論理的な層を保つ。
<!--/-->

```agda
  binKey-out : ⟨ δ ⊨ binKey C ar N a b ⟩ → ⟨ pr A (pr Nv P) ∈ Cv ⟩
  binKey-out = E.member-out (keyExpr ar N (E.pair (E.slot a) (E.slot b))) (var C) δ
```

<!--en-->
The inward reading is its reverse, and the two together identify the formula statement with the set membership, as with every key clause.
<!--zh-->
向内读法是其反向；与每条键子句一样，二者把公式陈述与集合隶属等同。
<!--ja-->
内向きの読み出しはその逆向きであり、他のキーの条項と同じく、二者は論理式の主張と集合の所属を同一視する。
<!--/-->

```agda
  binKey-in : ⟨ pr A (pr Nv P) ∈ Cv ⟩ → ⟨ δ ⊨ binKey C ar N a b ⟩
  binKey-in = E.member-in (keyExpr ar N (E.pair (E.slot a) (E.slot b))) (var C) δ
```
</div>
</details>

<!--en-->
An atomic key has two term codes as its payload. Each term code carries its own term tag and argument, and the pair of these two term codes is placed beneath the atomic constructor tag and the common arity.
<!--zh-->
原子键以两个词项码为载荷。每个词项码都带有自己的词项标签与实参；两个词项码组成一对，再置于原子构造子标签和共同元数之下。
<!--ja-->
原子キーのペイロードは二つの項符号である。各項符号はそれぞれの項タグと引数をもち、その二つの項符号の対が、原子構成子のタグと共通のアリティの下に置かれる。
<!--/-->

<details open class="submodule-fold">
<summary class="submodule-fold-heading">
```agda
module _ {k : ℕ} (C ar N Nx x Ny y : Fin k) (δ : S ^ k) where
```
</summary>
<div class="submodule-fold-content">

```agda
  private
    Cv = fst (lookup C δ)
    A = fst (lookup ar δ)
    Nv = fst (lookup N δ)
```

<!--en-->
Write the two term codes as `T=(Nx,x)` and `U=(Ny,y)`. At this stage `Nx` and `Ny` are arbitrary tag values from the environment; their being zero or one is imposed when the atomic closure cases are instantiated.
<!--zh-->
把两个词项码写作 `T=(Nx,x)` 与 `U=(Ny,y)`。此处 `Nx`、`Ny` 仍是环境中的任意标签值；在实例化原子封闭情形时，才要求它们为零或一。
<!--ja-->
二つの項符号を `T=(Nx,x)`、`U=(Ny,y)` と書く。この段階では `Nx` と `Ny` は環境から得た任意のタグ値であり、それらが零または一であるという条件は、原子の閉性の場合を具体化するときに課される。
<!--/-->

```agda
    T = pr (fst (lookup Nx δ)) (fst (lookup x δ))
    U = pr (fst (lookup Ny δ)) (fst (lookup y δ))
```

<!--en-->
The atomic clause reads outward as `(A,(N,(T,U))) ∈ C`, where `T` and `U` are the two term codes. Thus the outer pair records the arity, the next records the atomic tag, and the innermost pair records the two terms.
<!--zh-->
原子子句的向外读法是 `(A,(N,(T,U))) ∈ C`，其中 `T`、`U` 为两个词项码。因此，最外层有序对记录元数，下一层记录原子标签，最内层有序对记录两个词项。
<!--ja-->
原子の条件を外向きに読むと、`(A,(N,(T,U))) ∈ C` となる。ここで `T` と `U` は二つの項符号である。最も外側の対がアリティを、その次が原子タグを、最も内側の対が二つの項を記録する。
<!--/-->

```agda
  atomKey-out : ⟨ δ ⊨ atomKey C ar N Nx x Ny y ⟩ → ⟨ pr A (pr Nv (pr T U)) ∈ Cv ⟩
  atomKey-out = E.member-out (atomKeyExpr ar N Nx x Ny y) (var C) δ
```

<!--en-->
The inward reading is its reverse, closing the atomic case in both directions like every key clause before it.
<!--zh-->
向内读法是其反向；与此前每条键子句一样，原子情形双向闭合。
<!--ja-->
内向きの読み出しはその逆向きで、これまでのどのキーの条項と同じく、原子の場合を両方向で閉じる。
<!--/-->

```agda
  atomKey-in : ⟨ pr A (pr Nv (pr T U)) ∈ Cv ⟩ → ⟨ δ ⊨ atomKey C ar N Nx x Ny y ⟩
  atomKey-in = E.member-in (atomKeyExpr ar N Nx x Ny y) (var C) δ
```
</div>
</details>

<!--en-->
A bounded-quantifier key carries two different components in its payload: a term code for the bound and a subformula code for the body. The common outer data are again the current arity `A` and the bounded-quantifier tag `N`.
<!--zh-->
有界量词键的载荷含两种不同分量：表示界的词项码，以及表示主体的子公式码。共同的外层数据仍是当前元数 `A` 与有界量词标签 `N`。
<!--ja-->
有界量化子のキーのペイロードには、異なる二つの成分がある。境界を表す項符号と、本体を表す部分論理式の符号である。共通する外側のデータは、やはり現在のアリティ `A` と有界量化子タグ `N` である。
<!--/-->

<details open class="submodule-fold">
<summary class="submodule-fold-heading">
```agda
module _ {k : ℕ} (C ar N Nx x a : Fin k) (δ : S ^ k) where
```
</summary>
<div class="submodule-fold-content">

```agda
  private
    Cv = fst (lookup C δ)
    A = fst (lookup ar δ)
    Nv = fst (lookup N δ)
```

<!--en-->
Write the bound-term code as `T=(Nx,x)` and the body code as `Av`. The term is checked at the current arity, whereas the body key is checked at the successor arity; keeping them as separate payload components records this grammatical asymmetry.
<!--zh-->
把界词项码写作 `T=(Nx,x)`，把主体码写作 `Av`。词项在当前元数处检查，而主体键在后继元数处检查；把二者保留为不同载荷分量，正好记录这一文法不对称性。
<!--ja-->
境界項の符号を `T=(Nx,x)`、本体の符号を `Av` と書く。項は現在のアリティで検査され、本体のキーは後続アリティで検査される。両者を別々のペイロード成分として保つことで、この文法上の非対称が記録される。
<!--/-->

```agda
    T = pr (fst (lookup Nx δ)) (fst (lookup x δ))
    Av = fst (lookup a δ)
```

<!--en-->
The bounded-key clause reads outward as `(A,(N,(T,Av))) ∈ C`. The innermost pair contains the bound-term code and the body code in that order; it is not itself a claim that either component is already legal.
<!--zh-->
有界键子句的向外读法是 `(A,(N,(T,Av))) ∈ C`。最内层有序对依次含界词项码与主体码；这条隶属本身并不断言任一分量已经合法。
<!--ja-->
有界キーの条件を外向きに読むと、`(A,(N,(T,Av))) ∈ C` となる。最も内側の対には、境界項の符号と本体の符号がこの順で入る。この所属だけでは、どちらの成分が正当であることもまだ主張しない。
<!--/-->

```agda
  bndKey-out : ⟨ δ ⊨ bndKey C ar N Nx x a ⟩ → ⟨ pr A (pr Nv (pr T Av)) ∈ Cv ⟩
  bndKey-out = E.member-out (bndKeyExpr ar N Nx x a) (var C) δ
```

<!--en-->
Conversely, membership of `(A,(N,(T,Av)))` in `C` yields satisfaction of `bndKey`. Together the two readings establish only the structural membership equivalence; legality of `T` and successor-arity membership of `Av` are supplied by the surrounding payload predicate.
<!--zh-->
反过来，`(A,(N,(T,Av)))` 属于 `C` 可推出 `bndKey` 的满足。两条读法合起来只建立结构隶属的等价；`T` 的合法性与 `Av` 在后继元数处的隶属由外围载荷谓词另行给出。
<!--ja-->
逆に、`(A,(N,(T,Av)))` が `C` に属することから `bndKey` の充足が得られる。二方向の読みが確立するのは構造的な所属の同値だけである。`T` の正当性と、後続アリティにおける `Av` の所属は、周囲のペイロード述語が別に与える。
<!--/-->

```agda
  bndKey-in : ⟨ pr A (pr Nv (pr T Av)) ∈ Cv ⟩ → ⟨ δ ⊨ bndKey C ar N Nx x a ⟩
  bndKey-in = E.member-in (bndKeyExpr ar N Nx x a) (var C) δ
```
</div>
</details>

<!--en-->
Now fix a candidate code domain `C`, a working set `W`, and ten environment entries certified to be the numerals zero through nine. For each tag, the object-language payload description can then be compared with its ambient predicate `AtomP`, `BinP`, `ConP`, `QuP`, or `BqP`.
<!--zh-->
现固定候选码域 `C`、工作集 `W`，以及十个已被证明分别为零至九数码的环境元素。于是，对每个标签，都可把对象语言载荷描述与相应的外围谓词 `AtomP`、`BinP`、`ConP`、`QuP` 或 `BqP` 比较。
<!--ja-->
ここで、候補となる符号領域 `C`、作業集合 `W`、そして零から九までの数項であることが証明された十個の環境要素を固定する。すると各タグについて、対象言語のペイロード記述を、対応する外部の述語 `AtomP`、`BinP`、`ConP`、`QuP`、`BqP` と比較できる。
<!--/-->

<details open class="submodule-fold">
<summary class="submodule-fold-heading">
```agda
module PayRead {m : ℕ} (C w : Fin m) (N : Fin 10 → Fin m) (δ : S ^ (9 + m))
  (tg : Tags δ (shN 9 N)) where
```
</summary>
<div class="submodule-fold-content">

```agda
  private
    Cv = fst (lookup (sh 9 C) δ)
    Wv = fst (lookup (sh 9 w) δ)
```

<!--en-->
In each payload reading, `A` denotes the recorded arity and `R` the raw payload. The equations for tags zero and one are singled out because both atomic and bounded-quantifier payloads must recognize term codes, whose two legal shapes use precisely these tags.
<!--zh-->
在每条载荷读法中，`A` 表示所记录的元数，`R` 表示原始载荷。零与一的标签等式被单独取出，因为原子载荷和有界量词载荷都必须识别词项码，而词项恰有使用这两个标签的两种合法形状。
<!--ja-->
各ペイロードの読みでは、`A` が記録されたアリティを、`R` が生のペイロードを表す。タグ零と一の等式を取り出しておくのは、原子と有界量化子のペイロードがともに項符号を認識する必要があり、項の二つの正当な形がちょうどこの二タグを使うからである。
<!--/-->

```agda
    A = fst (lookup i5 δ)
    R = fst (lookup i0 δ)
    q0 = tg f0
    q1 = tg f1
    rS = lookup i0 δ
```

<!--en-->
Both sides of the comparison use the same underlying sets `Wv` and `Cv`. The syntactic payload formulas therefore describe term membership in `Wv` and subkey membership in `Cv`, exactly matching the parameters of the five ambient payload predicates.
<!--zh-->
比较的两侧使用相同的底层集合 `Wv` 与 `Cv`。因此，句法载荷公式所描述的 `Wv` 中词项隶属与 `Cv` 中子键隶属，恰好对应五个外围载荷谓词的参数。
<!--ja-->
比較の両側では、同じ基礎集合 `Wv` と `Cv` を使う。したがって、構文的なペイロード論理式が述べる `Wv` への項の所属と `Cv` への部分キーの所属は、五つの外部ペイロード述語のパラメータと正確に一致する。
<!--/-->

```agda
    module Sh = Shape C w N
  open CodesSem Wv Cv
```

<!--en-->
The atomic body requires both components of the payload to satisfy the term-code predicate at the recorded arity. The binary body instead requires both components to occur as keys of that same arity in the candidate domain. These are different conditions even though both payloads are encoded as pairs.
<!--zh-->
原子载荷体要求载荷的两个分量都在所记录元数处满足词项码谓词。二元载荷体则要求两个分量都作为该同一元数的键出现在候选域中。尽管两种载荷都编码为有序对，这两项条件并不相同。
<!--ja-->
原子の本体は、ペイロードの二成分がともに、記録されたアリティで項符号の述語を満たすことを要求する。これに対して二項の本体は、両成分が同じアリティのキーとして候補領域に現れることを要求する。どちらのペイロードも対として符号化されるが、二つの条件は異なる。
<!--/-->

```agda
  private
    tmBody : Formula S (12 + m)
    tmBody = isTm i1 i8 (sh 12 w) (sh 12 (N f0)) (sh 12 (N f1)) ∧̇ isTm i0 i8 (sh 12 w) (sh 12 (N f0)) (sh 12 (N f1))
    binBody : Formula S (12 + m)
    binBody = appAt (sh 12 C) i8 i1 ∧̇ appAt (sh 12 C) i8 i0
```

<!--en-->
The last payload shape covers the two bounded quantifiers. Its body requires a legal term at the current arity for the bound and a body key in the code set at the successor arity.
<!--zh-->
最后一种载荷形状涵盖两个有界量词。其主体要求作为界的词项在当前元数处合法，并要求主体的键在后继元数处属于码集。
<!--ja-->
最後のペイロード形は二つの有界量化子を扱う。その本体は、境界を表す項が現在のアリティで合法であることと、本体のキーが後続アリティで符号集合に属することを要求する。
<!--/-->

```agda
    bqBody : Formula S (12 + m)
    bqBody = isTm i1 i8 (sh 12 w) (sh 12 (N f0)) (sh 12 (N f1)) ∧̇ keyUp (sh 12 C) i8 i0
```

<!--en-->
Reading an atomic payload outward removes the two existential binders and produces terms `t` and `u`, an equation `R ≡ pr t u`, and proofs that both terms are legal at arity `A`. The term reader uses the tag equations for zero and one to turn the two satisfaction claims into the corresponding truncated term shapes.
<!--zh-->
向外读取原子载荷时，消去两层存在量词，得到词项 `t`、`u`、等式 `R ≡ pr t u`，以及二者在元数 `A` 处合法的证明。词项读式利用零与一的标签等式，把两份满足证明转换为相应的截断词项形状。
<!--ja-->
原子ペイロードを外向きに読むと、二つの存在束縛が除かれ、項 `t` と `u`、等式 `R ≡ pr t u`、および両方の項がアリティ `A` で合法であることの証明が得られる。項の読みは 0 と 1 のタグ等式を用いて、二つの充足証明を対応する切り詰められた項の形へ変換する。
<!--/-->

```agda
  atom-out : ⟨ δ ⊨ Sh.atomPay ⟩ → AtomP A R
  atom-out h = map₁
    (λ { (t , u , s , (e , (ht , hu))) → fst t , fst u
       , ( e , ( isTm-out i1 i8 (sh 12 w) (sh 12 (N f0)) (sh 12 (N f1)) (u ∷ t ∷ s ∷ δ) q0 q1 ht
               , isTm-out i0 i8 (sh 12 w) (sh 12 (N f0)) (sh 12 (N f1)) (u ∷ t ∷ s ∷ δ) q0 q1 hu ) ) })
```

<!--en-->
The consumption itself is one application of the two-fold existential elimination: the witnesses `t`, `u` and the container are extracted, and the remaining conjunction is discharged into the payload data.
<!--zh-->
这一消耗本身就是对双重存在消去的一次应用：抽出见证 `t`、`u` 与容器，然后把余下的合取兑现为载荷数据。
<!--ja-->
この消費は、二重の存在消去の一つの適用にすぎない。証人 `t`、`u` と容器を取り出し、残りの連言をペイロードのデータへ処理する。
<!--/-->

```agda
    (bothEx-out i0 tmBody δ h)
```

<!--en-->
Reading inward rebuilds the satisfaction from the data. The truncated legality proofs are eliminated, since the goal is again a truncated satisfaction, and each of the two terms enters its legality atom through the shifted context.
<!--zh-->
向内读取则从数据重建满足。两份截断的合法证明被消去，因为目标仍是截断的满足；两个词项各自经移位语境进入其合法原子。
<!--ja-->
内向きの読みは、データから充足を組み立て直す。切り詰められた合法性の証明は、目標もまた切り詰められた充足であるため消去でき、二つの項はそれぞれずらした文脈を通して合法性の原子に入る。
<!--/-->

```agda
  atom-in : AtomP A R → ⟨ δ ⊨ Sh.atomPay ⟩
  atom-in = rec₁ (snd (δ ⊨ Sh.atomPay))
    (λ { (t , u , (e , (ht , hu))) →
      fillBoth i0 δ (fstS rS t u e) (sndS rS t u e) e tmBody
        ( isTm-in i1 i8 (sh 12 w) (sh 12 (N f0)) (sh 12 (N f1)) (δ12 t u e) q0 q1 ht
```

<!--en-->
The second legality claim is inserted in the same way. The auxiliary environment `δ12` consists of the two components selected by `R ≡ pr t u`, a container witnessing that pairing, and the original environment; this is exactly the environment in which both term atoms are interpreted.
<!--zh-->
第二份合法性证明以同样方式填入。辅助环境 `δ12` 依次包含由 `R ≡ pr t u` 选出的两个分量、见证这次配对的容器以及原环境；两个词项原子正是在这个环境中解释的。
<!--ja-->
二つ目の合法性の証明も同じ方法で入れる。補助環境 `δ12` は、`R ≡ pr t u` によって選ばれた二つの成分、その対を証明するコンテナ、元の環境からなり、二つの項の原子式はまさにこの環境で解釈される。
<!--/-->

```agda
        , isTm-in i0 i8 (sh 12 w) (sh 12 (N f0)) (sh 12 (N f1)) (δ12 t u e) q0 q1 hu ) })
    where
    δ12 : (t u : V ℓ) (e : R ≡ pr t u) → S ^ (12 + m)
    δ12 t u e = sndS rS t u e ∷ fstS rS t u e ∷ container rS (fstS rS t u e) (sndS rS t u e) e .fst ∷ δ
```

<!--en-->
Reading a binary payload outward yields payloads `a` and `b`, an equation `R ≡ pr a b`, and membership of both `pr A a` and `pr A b` in the code set. Adequacy of the two application atoms identifies those memberships in the extended environment.
<!--zh-->
向外读取二元载荷得到载荷 `a`、`b`、等式 `R ≡ pr a b`，以及 `pr A a` 与 `pr A b` 都属于码集的证明。两个应用原子的充分性在扩展环境中识别出这两份隶属关系。
<!--ja-->
二項ペイロードを外向きに読むと、ペイロード `a` と `b`、等式 `R ≡ pr a b`、および `pr A a` と `pr A b` がともに符号集合に属することが得られる。二つの適用原子式の妥当性が、拡張環境におけるこれらの所属を同定する。
<!--/-->

```agda
  bin-out : ⟨ δ ⊨ Sh.binPay ⟩ → BinP A R
  bin-out h = map₁
    (λ { (a , b , s , (e , (ha , hb))) → fst a , fst b
       , ( e , ( subst ⟨_⟩ (appAt-adequate (sh 12 C) i8 i1 (b ∷ a ∷ s ∷ δ)) ha
               , subst ⟨_⟩ (appAt-adequate (sh 12 C) i8 i0 (b ∷ a ∷ s ∷ δ)) hb ) ) })
```

<!--en-->
As with the atoms, the two existentials of the binary condition are consumed by a single elimination.
<!--zh-->
与原子情形一样，二元条件的两层存在量词由一次消去处理。
<!--ja-->
原子の場合と同じく、二項の条件の二重の存在量化は一度の消去で処理される。
<!--/-->

```agda
    (bothEx-out i0 binBody δ h)
```

<!--en-->
Reading inward fills the two existentials with the named sub-codes. The two application atoms are satisfied by transporting along the adequacy in the reverse direction, back into the shifted context.
<!--zh-->
向内读取则以被点名的子码填入两层存在量词。两个应用原子沿充分性反方向传输，回到移位语境之中而得到满足。
<!--ja-->
内向きの読みは、名指された下位コードで二つの存在量化子を満たす。二つの適用の原子は、妥当性を逆向きに辿ってずらした文脈の中で充足される。
<!--/-->

```agda
  bin-in : BinP A R → ⟨ δ ⊨ Sh.binPay ⟩
  bin-in = rec₁ (snd (δ ⊨ Sh.binPay))
    (λ { (a , b , (e , (ha , hb))) →
      fillBoth i0 δ (fstS rS a b e) (sndS rS a b e) e binBody
        ( subst ⟨_⟩ (sym (appAt-adequate (sh 12 C) i8 i1 (δ12 a b e))) ha
```

<!--en-->
The binary helper records the same shifted-context shape, now built from the two ambient values `a` and `b`.
<!--zh-->
二元情形的辅助定义记录同样的移位语境形状，此时由两个外围值 `a` 与 `b` 构造。
<!--ja-->
二項の場合の補助定義も同じずらした文脈の形を記録する。今度は周囲の値 `a` と `b` から組み立てられる。
<!--/-->

```agda
        , subst ⟨_⟩ (sym (appAt-adequate (sh 12 C) i8 i0 (δ12 a b e))) hb ) })
    where
    δ12 : (a b : V ℓ) (e : R ≡ pr a b) → S ^ (12 + m)
    δ12 a b e = sndS rS a b e ∷ fstS rS a b e ∷ container rS (fstS rS a b e) (sndS rS a b e) e .fst ∷ δ
```

<!--en-->
The falsity payload contains no subordinate data. Its formula says that `R` is the value stored in the zero-tag slot, while `ConP A R` says `R ≡ # 0`; composing with the zero-tag equation gives the outward direction.
<!--zh-->
假的载荷不含下级数据。其公式说 `R` 等于零标签槽位中的值，而 `ConP A R` 说 `R ≡ # 0`；与零标签等式复合便得到向外方向。
<!--ja-->
偽のペイロードには下位データがない。その論理式は `R` が 0 タグのスロットに格納された値に等しいことを述べ、`ConP A R` は `R ≡ # 0` を述べる。0 タグの等式と合成することで外向きの方向が得られる。
<!--/-->

```agda
  con-out : ⟨ δ ⊨ Sh.conPay ⟩ → ConP A R
  con-out h = h ∙ q0
```

<!--en-->
Conversely, an equation `R ≡ # 0` composes with the zero-tag equation in reverse to prove that `R` equals the value of the zero-tag slot, which is precisely satisfaction of the falsity payload.
<!--zh-->
反过来，等式 `R ≡ # 0` 与零标签等式的逆向复合，证明 `R` 等于零标签槽位中的值；这正是假载荷的满足。
<!--ja-->
逆に、等式 `R ≡ # 0` を 0 タグの等式の逆向きと合成すると、`R` が 0 タグのスロットの値に等しいことが示される。これは偽のペイロードの充足そのものである。
<!--/-->

```agda
  con-in : ConP A R → ⟨ δ ⊨ Sh.conPay ⟩
  con-in h = h ∙ sym q0
```

<!--en-->
For either unbounded quantifier, the payload is a body key at the successor arity. The successor-key reader turns satisfaction of this payload formula into membership of `pr (sucV A) R` in the code set.
<!--zh-->
对任一无界量词，载荷都是后继元数处的主体键。后继键读式把这份载荷公式的满足转换为 `pr (sucV A) R` 属于码集。
<!--ja-->
どちらの非有界量化子でも、ペイロードは後続アリティにおける本体のキーである。後続キーの読みは、このペイロード論理式の充足を `pr (sucV A) R` が符号集合に属することへ変換する。
<!--/-->

```agda
  qu-out : ⟨ δ ⊨ Sh.quPay ⟩ → QuP A R
  qu-out = keyUp-out (sh 9 C) i5 i0 δ
```

<!--en-->
In the reverse direction, membership of `pr (sucV A) R` in the code set supplies the witnesses required by the successor-key formula and hence proves the quantifier payload.
<!--zh-->
反向上，`pr (sucV A) R` 属于码集为后继键公式提供所需见证，因而证明量词载荷。
<!--ja-->
逆向きには、`pr (sucV A) R` が符号集合に属することから後続キーの論理式に必要な証人が得られ、量化子ペイロードが証明される。
<!--/-->

```agda
  qu-in : QuP A R → ⟨ δ ⊨ Sh.quPay ⟩
  qu-in = keyUp-in (sh 9 C) i5 i0 δ
```

<!--en-->
Reading a bounded-quantifier payload outward yields a term `t`, a body payload `a`, and an equation `R ≡ pr t a`. It also proves that `t` is legal at arity `A` and that the body key `pr (sucV A) a` belongs to the code set.
<!--zh-->
向外读取有界量词载荷得到词项 `t`、主体载荷 `a` 与等式 `R ≡ pr t a`。同时还得到 `t` 在元数 `A` 处合法，以及主体键 `pr (sucV A) a` 属于码集。
<!--ja-->
有界量化子のペイロードを外向きに読むと、項 `t`、本体のペイロード `a`、等式 `R ≡ pr t a` が得られる。さらに、`t` がアリティ `A` で合法であることと、本体のキー `pr (sucV A) a` が符号集合に属することも得られる。
<!--/-->

```agda
  bq-out : ⟨ δ ⊨ Sh.bqPay ⟩ → BqP A R
  bq-out h = map₁
    (λ { (t , a , s , (e , (ht , ha))) → fst t , fst a
       , ( e , ( isTm-out i1 i8 (sh 12 w) (sh 12 (N f0)) (sh 12 (N f1)) (a ∷ t ∷ s ∷ δ) q0 q1 ht
               , keyUp-out (sh 12 C) i8 i0 (a ∷ t ∷ s ∷ δ) ha ) ) })
```

<!--en-->
The two existentials of the bounded body are consumed by the same two-fold elimination as everywhere else.
<!--zh-->
有界主体的两层存在量词与其他情形一样，由同一个双重消去处理。
<!--ja-->
有界の本体の二重の存在量化は、他の場所と同じく二重の消去で処理される。
<!--/-->

```agda
    (bothEx-out i0 bqBody δ h)
```

<!--en-->
Reading inward, the bounding term enters its legality atom through the shifted context.
<!--zh-->
向内读取时，界限词项经移位语境进入其合法性原子。
<!--ja-->
内向きの読みでは、境界の項がずらした文脈を通して合法性の原子に入る。
<!--/-->

```agda
  bq-in : BqP A R → ⟨ δ ⊨ Sh.bqPay ⟩
  bq-in = rec₁ (snd (δ ⊨ Sh.bqPay))
    (λ { (t , a , (e , (ht , ha))) →
      fillBoth i0 δ (fstS rS t a e) (sndS rS t a e) e bqBody
        ( isTm-in i1 i8 (sh 12 w) (sh 12 (N f0)) (sh 12 (N f1)) (δ12 t a e) q0 q1 ht
```

<!--en-->
The body key enters through the successor-key lemma, and the helper records the shifted context built from the bounding value and its container.
<!--zh-->
主体键经后继键引理进入；辅助定义记录由界限取值及其容器构造的移位语境。
<!--ja-->
本体の鍵は後続の鍵の補題を通して入り、補助定義は境界の値とその容器から作られるずらした文脈の形を記録する。
<!--/-->

```agda
        , keyUp-in (sh 12 C) i8 i0 (δ12 t a e) ha ) })
    where
    δ12 : (t a : V ℓ) (e : R ≡ pr t a) → S ^ (12 + m)
    δ12 t a e = sndS rS t a e ∷ fstS rS t a e ∷ container rS (fstS rS t a e) (sndS rS t a e) e .fst ∷ δ
```

<!--en-->
The reader for a label is selected by recursion on the label. Labels zero and one are the two atoms, and labels two, three and four are the three binary connectives.
<!--zh-->
标签的读式按标签递归选择。标签零与一是两条原子，标签二、三、四是三种二元联结词。
<!--ja-->
タグの読みはタグの上の再帰で選ばれる。タグ 0 と 1 が二つの原子式、タグ 2、3、4 が三つの二項結合子である。
<!--/-->

```agda
  payN-out : (k : ℕ) → ⟨ δ ⊨ Sh.payN k ⟩ → PayN k A R
  payN-out 0 = atom-out
  payN-out 1 = atom-out
  payN-out 2 = bin-out
  payN-out 3 = bin-out
```

<!--en-->
Labels five, six and seven cover falsity and the two unbounded quantifiers; label eight is the bounded universal.
<!--zh-->
标签五、六、七覆盖假与两个无界量词；标签八是有界全称。
<!--ja-->
タグ 5、6、7 は偽と二つの非有界の量化子を、タグ 8 は有界の全称を担う。
<!--/-->

```agda
  payN-out 4 = bin-out
  payN-out 5 = con-out
  payN-out 6 = qu-out
  payN-out 7 = qu-out
  payN-out 8 = bq-out
```

<!--en-->
Label nine is the bounded existential. Labels ten and beyond name no constructor: their payload is empty, so the reader is the identity on that empty data.
<!--zh-->
标签九是有界存在。标签十及以上不指名任何构造子：其载荷为空，读式就是这份空数据上的恒等。
<!--ja-->
タグ 9 が有界の存在である。タグ 10 以上は構成子を名指さないためペイロードは空であり、読みはその空のデータの上の恒等写像である。
<!--/-->

```agda
  payN-out 9 = bq-out
  payN-out (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc _)))))))))) h = h
```

<!--en-->
The inward reader is selected by the same recursion, one clause per label.
<!--zh-->
向内读式按同样的递归选择，每个标签一条子句。
<!--ja-->
内向きの読みも同じ再帰で選ばれ、タグごとに一つの節をもつ。
<!--/-->

```agda
  payN-in : (k : ℕ) → PayN k A R → ⟨ δ ⊨ Sh.payN k ⟩
  payN-in 0 = atom-in
  payN-in 1 = atom-in
  payN-in 2 = bin-in
  payN-in 3 = bin-in
```

<!--en-->
Labels four through seven continue the list: the last binary connective, falsity, and the two unbounded quantifiers.
<!--zh-->
标签四至七继续这份清单：最后一个二元联结词、假，以及两个无界量词。
<!--ja-->
タグ 4 から 7 までが一覧を続ける。最後の二項結合子、偽、そして二つの非有界の量化子である。
<!--/-->

```agda
  payN-in 4 = bin-in
  payN-in 5 = con-in
  payN-in 6 = qu-in
  payN-in 7 = qu-in
  payN-in 8 = bq-in
```

<!--en-->
Label nine completes the list; beyond ten there is nothing to read, since no legitimate key carries such a label.
<!--zh-->
标签九补全清单；十以上无可读取，因为没有合法的键携带这样的标签。
<!--ja-->
タグ 9 が一覧を完成させる。10 以上を読むべきものはない。そのようなタグをもつ合法な鍵はないからである。
<!--/-->

```agda
  payN-in 9 = bq-in
  payN-in (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc _)))))))))) h = h
```
</div>
</details>

<!--en-->
The ten-way reader interprets a tagged payload in a seven-entry extension of the ambient environment. It reads the code set and constant alphabet from the ambient entries, while `N` selects ten ambient positions whose values are identified with the numerals zero through nine by the tag hypothesis.
<!--zh-->
十路读式在外围环境之上的七条目扩展中解释带标签的载荷。它从外围条目读取码集与常元字母表，而 `N` 选出外围环境中的十个位置；标签假设把这些位置的值分别等同于数码零至九。
<!--ja-->
十通りの読みは、周囲の環境を七項目だけ拡張した環境でタグ付きペイロードを解釈する。符号集合と定数アルファベットは周囲の項目から読み、`N` は周囲の環境にある十個の位置を選ぶ。タグの仮定は、それらの値をそれぞれ数項 0 から 9 までと同定する。
<!--/-->

<details open class="submodule-fold">
<summary class="submodule-fold-heading">
```agda
module TenRead {m : ℕ} (C w : Fin m) (N : Fin 10 → Fin m) (δ : S ^ (7 + m))
  (tg : Tags δ (shN 7 N)) where
```
</summary>
<div class="submodule-fold-content">

```agda
  private
    Cv = fst (lookup (sh 7 C) δ)
    Wv = fst (lookup (sh 7 w) δ)
```

<!--en-->
Among the newly bound entries, `A` is the arity and `P` is the tagged payload to be recognized as a key. Retaining the set-level representative of `P` allows the equation `P ≡ pr (# (toℕ j)) r` to be realized when a tag and its payload `r` are chosen.
<!--zh-->
在新绑定的条目中，`A` 是元数，`P` 是要识别为键的带标签载荷。保留 `P` 的集合层表示后，选定标签及其载荷 `r` 时便可实现等式 `P ≡ pr (# (toℕ j)) r`。
<!--ja-->
新たに束縛された項目のうち、`A` はアリティであり、`P` はキーとして認識すべきタグ付きペイロードである。`P` の集合レベルの表示を保つことで、タグとそのペイロード `r` を選んだときに等式 `P ≡ pr (# (toℕ j)) r` を実現できる。
<!--/-->

```agda
    A = fst (lookup i3 δ)
    P = fst (lookup i0 δ)
    pS = lookup i0 δ
    module Sh = Shape C w N
  open CodesSem Wv Cv
```

<!--en-->
The tag reader converts satisfaction of the `j`-th tag atom into a key. The truncated witness pairs an index `r` with a container; the coding equation is transported along the tag equation, which says that the `j`-th tag slot names the numeral of `j`, and the payload is read by the label reader at `j`.
<!--zh-->
标签读式把第 `j` 个标签原子的满足转换为一把键。截断的见证由索引 `r` 与容器配对；编码等式沿标签等式传输。这个等式表明，第 `j` 个标签槽位点名的正是 `j` 的数码；载荷则由标签 `j` 处的读式读取。
<!--ja-->
タグの読みは、`j` 番目のタグの原子の充足を鍵へ変換する。切り詰められた証人は添字 `r` と容器の対であり、符号化の等式は、`j` 番目のタグのスロットが `j` の数項を名指すというタグの等式に沿って輸送され、ペイロードはタグ `j` での読みによって読まれる。
<!--/-->

```agda
  at-out : (j : Fin 10) → ⟨ δ ⊨ Sh.at j ⟩ → Key A P
  at-out j h = map₁
    (λ { (r , s , (e , hp)) → j , fst r
       , ( e ∙ cong (λ a → pr a (fst r)) (tg j)
         , PayRead.payN-out C w N (r ∷ s ∷ δ) tg (toℕ j) hp ) })
```

<!--en-->
The two existentials of the tag atom are consumed by its own elimination, so the reader never chooses an index: it only unpacks the one that satisfaction provides.
<!--zh-->
标签原子的两层存在量词由其自身的消去处理，因此读式从不自行选择索引：它只拆开满足所提供的那一个。
<!--ja-->
タグの原子の二重の存在量化はみずからの消去で処理されるため、読みが添字を選ぶことはない。充足が与える一つを展開するだけである。
<!--/-->

```agda
    (sndEx-out i0 (sh 7 (N j)) (Sh.pay j) δ h)
```

<!--en-->
The inward direction builds the satisfaction from a key: the witness entry is filled with the shifted value, the payload is read inward over the extended context, and the tag equation identifies the naming slot with the numeral of `j`.
<!--zh-->
向内方向由键构造满足：见证条目以移位后的取值填入，载荷在扩展语境上向内读取，而标签等式把命名槽位与 `j` 的数码等同起来。
<!--ja-->
内向きの方向は、鍵から充足を組み立てる。証人の項目はずらした値で満たされ、ペイロードは拡張された文脈の上で内向きに読まれ、タグの等式が名指しのスロットを `j` の数項と同一視する。
<!--/-->

```agda
  at-in : (j : Fin 10) (r : V ℓ) (e : P ≡ pr (# (toℕ j)) r) → PayN (toℕ j) A r → ⟨ δ ⊨ Sh.at j ⟩
  at-in j r e pay =
    fillSnd i0 δ (lookup (sh 7 (N j)) δ) rS e' (Sh.pay j)
      (PayRead.payN-in C w N (rS ∷ container pS (lookup (sh 7 (N j)) δ) rS e' .fst ∷ δ) tg (toℕ j) pay)
      (sh 7 (N j)) refl
```

<!--en-->
The renamed value pairs the numeral of `j` with the chosen entry, and the coding equation is composed with the tag equation in reverse, so the extended naming mentions the right slot.
<!--zh-->
改名后的取值把 `j` 的数码与所选条目配对；编码等式与标签等式反向复合，使扩展后的命名提到的正是那个槽位。
<!--ja-->
改名された値は `j` の数項と選ばれた項目を対にし、符号化の等式はタグの等式と逆向きに合成されて、拡張された名指しが正しいスロットに触れるようにする。
<!--/-->

```agda
    where
    rS : S
    rS = sndS pS (# (toℕ j)) r e
    e' : P ≡ pr (fst (lookup (sh 7 (N j)) δ)) (fst rS)
    e' = e ∙ cong (λ a → pr a r) (sym (tg j))
```

<!--en-->
The ten-way outward reader consumes the disjunction and quotes the tag reader at whichever tag the witness names.
<!--zh-->
十路向外读式消耗该析取，并在见证所指名的那个标签处引用标签读式。
<!--ja-->
十通りの外向きの読みは選言を消費し、証人が名指すタグのところでタグの読みを引用する。
<!--/-->

```agda
  ten-out : ⟨ δ ⊨ Sh.ten ⟩ → Key A P
  ten-out h = rec₁ squash₁ (λ { (j , hj) → at-out j hj }) (bigOr-out δ 9 Sh.at h)
```

<!--en-->
The inward reader enters the disjunction at the witnessed tag, with the payload read inward at that tag. Both directions together say: satisfaction of the ten-way disjunction is the same thing as carrying a legitimate key.
<!--zh-->
向内读式在见证到的标签处进入析取，载荷也在该标签处向内读取。两个方向合起来说：十路析取的满足，与携带一把合法键，是同一回事。
<!--ja-->
内向きの読みは、証人の現れたタグで選言に入り、ペイロードもそのタグで内向きに読まれる。二つの方向合わせて、十通りの選言の充足と、合法な鍵をもつことは同じことだと述べている。
<!--/-->

```agda
  ten-in : Key A P → ⟨ δ ⊨ Sh.ten ⟩
  ten-in = rec₁ (snd (δ ⊨ Sh.ten))
    (λ { (j , r , (e , pay)) → bigOr-in δ 9 Sh.at j (at-in j r e pay) })
```
</div>
</details>

<!--en-->
The shape reader fixes three ambient sets: the candidate code set `C`, the constant alphabet `w`, and the tower `E` of arity-family pairs. Their underlying iterative sets are used respectively for code membership, legal constant terms, and witnesses `(ar,F)` belonging to the tower.
<!--zh-->
形状读式固定三个外围集合：候选码集 `C`、常元字母表 `w`，以及由「元数与族」对组成的塔 `E`。三者的底层迭代集合分别用于码的隶属、常元词项的合法性，以及属于该塔的见证 `(ar,F)`。
<!--ja-->
形の読みは三つの周囲の集合を固定する。候補となる符号集合 `C`、定数アルファベット `w`、そしてアリティと族の対からなる塔 `E` である。それぞれの基礎にある反復集合は、符号の所属、定数項の合法性、塔に属する証人 `(ar,F)` に用いられる。
<!--/-->

<details open class="submodule-fold">
<summary class="submodule-fold-heading">
```agda
module ShapeRead {m : ℕ} (C w E : Fin m) (N : Fin 10 → Fin m) (γ : S ^ m) (tg : Tags γ N) where
```
</summary>
<div class="submodule-fold-content">

```agda
  private
    Cv = fst (lookup C γ)
    Wv = fst (lookup w γ)
    Ev = fst (lookup E γ)
```

<!--en-->
For a chosen member `c` and a tower witness `(ar,F)`, the remaining formula chooses a payload `p`, requires `c ≡ pr ar p`, and tests `p` against the ten possible tag shapes. Thus the nested witnesses expose the outer arity and the inner tagged payload separately.
<!--zh-->
对选定的成员 `c` 与塔中见证 `(ar,F)`，余下公式选择载荷 `p`，要求 `c ≡ pr ar p`，并按十种可能的标签形状检验 `p`。这样，嵌套见证分别显露外层元数与内层带标签载荷。
<!--ja-->
選ばれた要素 `c` と塔の証人 `(ar,F)` に対し、残りの論理式はペイロード `p` を選び、`c ≡ pr ar p` を要求し、十通りのタグ形に照らして `p` を検査する。このように、入れ子になった証人は外側のアリティと内側のタグ付きペイロードを別々に明らかにする。
<!--/-->

```agda
    module Sh = Shape C w N
    inner : Formula S (5 + m)
    inner = sndEx i4 i1 Sh.ten
  open CodesSem Wv Cv
```

<!--en-->
`Shaped c` records exactly the data extracted from the shape clause: there are `ar`, `F`, and `p` such that `pr ar F` belongs to `E`, `c ≡ pr ar p`, and `p` is a legitimate tagged payload at arity `ar`. All of this existence data is propositionally truncated; no unique decomposition is asserted.
<!--zh-->
`Shaped c` 恰好记录形状子句抽出的数据：存在 `ar`、`F`、`p`，使得 `pr ar F` 属于 `E`、`c ≡ pr ar p`，且 `p` 是元数 `ar` 处合法的带标签载荷。所有存在数据都经过命题截断，并不声称分解唯一。
<!--ja-->
`Shaped c` は形の節から取り出されるデータをそのまま記録する。`pr ar F` が `E` に属し、`c ≡ pr ar p` が成り立ち、`p` がアリティ `ar` における合法なタグ付きペイロードとなる `ar`、`F`、`p` が存在する。この存在データはすべて命題的に切り詰められており、分解の一意性は主張しない。
<!--/-->

```agda
  Shaped : V ℓ → Type (ℓ-suc ℓ)
  Shaped c = ∥ Σ[ ar ∈ V ℓ ] Σ[ F ∈ V ℓ ] Σ[ p ∈ V ℓ ]
               (⟨ pr ar F ∈ Ev ⟩ × ((c ≡ pr ar p) × Key ar p)) ∥₁
```

<!--en-->
For each `c` in the code set, outward reading first obtains a member `q` of `E`. Decomposing `q` gives `ar` and `F` with `q ≡ pr ar F`; the inner existential then gives `p` with `c ≡ pr ar p` and satisfaction of the ten-way payload formula.
<!--zh-->
对码集中的每个 `c`，向外读取先得到 `E` 的成员 `q`。分解 `q` 得到 `ar`、`F` 与等式 `q ≡ pr ar F`；内层存在量词再给出 `p`、等式 `c ≡ pr ar p`，以及十路载荷公式的满足。
<!--ja-->
符号集合の各 `c` について、外向きの読みはまず `E` の要素 `q` を得る。`q` を分解すると `ar` と `F` および等式 `q ≡ pr ar F` が得られ、内側の存在量化からは `p`、等式 `c ≡ pr ar p`、十通りのペイロード論理式の充足が得られる。
<!--/-->

```agda
  shape-out : ⟨ γ ⊨ shapeAt C w E N ⟩ → (c : S) → ⟨ fst c ∈ Cv ⟩ → Shaped (fst c)
  shape-out h c c∈ = rec₁ squash₁
    (λ { (q , (q∈ , hb)) → rec₁ squash₁
      (λ { (ar , F , s , (eq , hs)) → map₁
        (λ { (p , s' , (ec , ht)) →
```

<!--en-->
The equation `q ≡ pr ar F` transports the known membership of `q` in `E` to membership of `pr ar F`. The equation for `c` is retained, and the ten-way reader converts the remaining satisfaction proof into `Key ar p`.
<!--zh-->
等式 `q ≡ pr ar F` 把已知的 `q` 属于 `E` 传输为 `pr ar F` 属于 `E`。同时保留关于 `c` 的等式，并由十路读式把余下的满足证明转换为 `Key ar p`。
<!--ja-->
等式 `q ≡ pr ar F` は、既知の `q` の `E` への所属を `pr ar F` の所属へ輸送する。`c` に関する等式は保持され、十通りの読みが残りの充足証明を `Key ar p` へ変換する。
<!--/-->

```agda
          fst ar , fst F , fst p
          , ( subst (λ u → ⟨ u ∈ Ev ⟩) eq q∈
            , ( ec , TenRead.ten-out C w N (p ∷ s' ∷ F ∷ ar ∷ s ∷ q ∷ c ∷ γ) tg ht ) ) })
        (sndEx-out i4 i1 Sh.ten (F ∷ ar ∷ s ∷ q ∷ c ∷ γ) hs) })
      (bothEx-out i0 inner (q ∷ c ∷ γ) hb) })
```

<!--en-->
The original shape satisfaction is universally quantified over members of the code set. Applying it to `c` and its membership proof supplies the existential data consumed above, completing the construction of `Shaped (fst c)`.
<!--zh-->
原形状满足对码集成员作全称量化。把它应用于 `c` 及其隶属证明，就得到上面所消去的存在数据，从而构造出 `Shaped (fst c)`。
<!--ja-->
元の形の充足は符号集合の要素について全称量化されている。これを `c` とその所属証明に適用すると、上で除去した存在データが得られ、`Shaped (fst c)` の構成が完了する。
<!--/-->

```agda
    (h c c∈)
```

<!--en-->
For the inward direction, assume that every member `c` of the code set has truncated shape data. Eliminating that truncation yields `ar`, `F`, and `p`, together with membership of `pr ar F` in `E`, the equation for `c`, and `Key ar p`; the target is itself a proposition, so this elimination is valid.
<!--zh-->
在向内方向，假设码集的每个成员 `c` 都有截断的形状数据。消去这份截断便得到 `ar`、`F`、`p`，连同 `pr ar F` 属于 `E`、关于 `c` 的等式及 `Key ar p`；目标本身是命题，因此可以作此消去。
<!--ja-->
内向きの方向では、符号集合の各要素 `c` が切り詰められた形のデータをもつと仮定する。その切り詰めを除去すると、`ar`、`F`、`p` とともに、`pr ar F` の `E` への所属、`c` に関する等式、`Key ar p` が得られる。目標自体が命題なので、この除去は正当である。
<!--/-->

```agda
  shape-in : ((c : S) → ⟨ fst c ∈ Cv ⟩ → Shaped (fst c)) → ⟨ γ ⊨ shapeAt C w E N ⟩
  shape-in k c c∈ = rec₁ (snd ((c ∷ γ) ⊨ ∃̇∈ (var (sh 1 E)) (bothEx i0 inner)))
    (λ { (ar , F , p , (q∈ , (ec , key))) →
      let qS = down (lookup E γ) (pr ar F) q∈
          arS = fstS qS ar F refl
```

<!--en-->
Membership of `pr ar F` in `E` supplies a set-level representative `qS`, whose two components represent `ar` and `F`. Separately, the equation `c ≡ pr ar p` selects a representative `pS` of the payload inside `c`. The two pairing containers provide the environments required by the nested existential formulas.
<!--zh-->
`pr ar F` 属于 `E` 提供集合层表示 `qS`，其两个分量分别表示 `ar` 与 `F`。另一方面，等式 `c ≡ pr ar p` 在 `c` 内选出载荷的表示 `pS`。两个配对容器共同提供嵌套存在公式所需的环境。
<!--ja-->
`pr ar F` が `E` に属することから集合レベルの表示 `qS` が得られ、その二成分がそれぞれ `ar` と `F` を表す。これとは別に、等式 `c ≡ pr ar p` は `c` の内部でペイロードの表示 `pS` を選ぶ。二つの対コンテナが、入れ子の存在論理式に必要な環境を与える。
<!--/-->

```agda
          FS = sndS qS ar F refl
          δ2 = qS ∷ c ∷ γ
          cq = container qS arS FS refl
          δ5 = FS ∷ arS ∷ cq .fst ∷ δ2
          pS = sndS c ar p ec
```

<!--en-->
The inner formula is filled with the arity-table data, and the ten-way disjunction is filled with the key, so the full shape satisfaction is assembled from the honest data.
<!--zh-->
内层公式以「元数与表」数据填充，十路析取以键填充，于是完整的形状满足由真实数据组装而成。
<!--ja-->
内側の論理式はアリティと表のデータで満たされ、十通りの選言は鍵で満たされる。こうして形の充足の全体が、実際のデータから組み上がる。
<!--/-->

```agda
          cp = container c arS pS ec
          δ7 = pS ∷ cp .fst ∷ δ5
      in ∣ qS , ( q∈ , fillBoth i0 δ2 arS FS refl inner
            (fillSnd i4 δ5 arS pS ec Sh.ten
              (TenRead.ten-in C w N δ7 tg key) i1 refl) ) ∣₁ })
```

<!--en-->
Applying the assumed shape assignment to `c` and its membership supplies precisely the truncated witnesses used by the inward construction. Together with the outward direction, this identifies satisfaction of the shape formula with the proposition `Shaped` for every member of the code set.
<!--zh-->
把所假设的形状赋值应用于 `c` 及其隶属，就恰好得到向内构造所用的截断见证。结合向外方向，这说明对码集的每个成员，形状公式的满足与命题 `Shaped` 相符。
<!--ja-->
仮定した形の割り当てを `c` とその所属に適用すると、内向きの構成で用いる切り詰められた証人がちょうど得られる。外向きの方向と合わせると、符号集合の各要素について、形の論理式の充足が命題 `Shaped` と一致することが分かる。
<!--/-->

```agda
    (k c c∈)
```
</div>
</details>

<!--en-->
The closure clauses are interpreted after a tower member has been decomposed as `q ≡ pr ar F`. In the resulting four-entry extension, `A` is the fixed arity `ar`; the code set and constant alphabet remain available from the ambient environment, and the tag equations remain valid after the shift.
<!--zh-->
先把塔的一个成员分解为 `q ≡ pr ar F`，再解释各闭包子句。在所得的四条目扩展中，`A` 是固定元数 `ar`；码集与常元字母表仍从外围环境取得，标签等式在移位后仍然成立。
<!--ja-->
塔の要素を `q ≡ pr ar F` と分解した後で、各閉性の節を解釈する。得られる四項目の拡張では、`A` は固定されたアリティ `ar` である。符号集合と定数アルファベットは周囲の環境から引き続き参照でき、タグ等式もシフト後に保たれる。
<!--/-->

<details open class="submodule-fold">
<summary class="submodule-fold-heading">
```agda
module CloseRead {m : ℕ} (C w : Fin m) (N : Fin 10 → Fin m) (δ : S ^ (4 + m)) (tg : Tags δ (shN 4 N)) where
```
</summary>
<div class="submodule-fold-content">

```agda
  private
    Cv = fst (lookup (sh 4 C) δ)
    A = fst (lookup i1 δ)
    arS = lookup i1 δ
```

<!--en-->
At this fixed arity, the closure conditions say that applying any of the ten constructors to inputs of the required shapes produces another member of the code set. For each clause, the outward and inward readings identify its bounded formula with the corresponding closure property.
<!--zh-->
在这个固定元数处，闭包条件说：把十种构造子中的任意一种应用于具有所需形状的输入，结果仍属于码集。对每条子句，向外与向内读法都把其有界公式识别为相应的闭包性质。
<!--ja-->
この固定アリティで、閉性条件は、必要な形の入力に十個の構成子のいずれかを適用すると結果が再び符号集合に属することを述べる。各節について、外向きと内向きの読みは、その有界論理式を対応する閉性と同定する。
<!--/-->

```agda
    CS = lookup (sh 4 C) δ
    module Cl = Close C w N
```

<!--en-->
Outward reading of an atomic closure clause permits arbitrary `x` from the bound selected by `X` and arbitrary `y` from the bound selected by `Y` in the environment extended by `x`. It then yields membership in the code set of the atomic key at arity `A`, with constructor tag `k` and term-form tags `Nx` and `Ny`.
<!--zh-->
向外读取原子闭包子句时，可任取属于 `X` 所选界的 `x`，再从以 `x` 扩展后的环境里任取属于 `Y` 所选界的 `y`。由此得到相应原子键属于码集；该键的元数为 `A`，构造子标签为 `k`，两个词项形状标签为 `Nx` 与 `Ny`。
<!--ja-->
原子の閉性の節を外向きに読むと、`X` が選ぶ境界から任意の `x` を取り、さらに `x` で拡張した環境で `Y` が選ぶ境界から任意の `y` を取れる。その結果、アリティ `A`、構成子タグ `k`、項の形を示すタグ `Nx` と `Ny` をもつ原子キーが符号集合に属することが得られる。
<!--/-->

```agda
  atomClose-out : (k Nx Ny : Fin 10) (X : Fin (4 + m)) (Y : Fin (5 + m))
                → ⟨ δ ⊨ Cl.atomClose k Nx Ny X Y ⟩
                → (x y : S) → ⟨ fst x ∈ fst (lookup X δ) ⟩ → ⟨ fst y ∈ fst (lookup Y (x ∷ δ)) ⟩
                → ⟨ pr A (pr (# (toℕ k)) (pr (pr (# (toℕ Nx)) (fst x)) (pr (# (toℕ Ny)) (fst y)))) ∈ Cv ⟩
  atomClose-out k Nx Ny X Y h x y x∈ y∈ =
```

<!--en-->
The membership is transported along the tag equations, which rename the three slots to the numerals of the three tags, since the clause is stated at the tagged slots but the key is spelled with the numerals.
<!--zh-->
该隶属沿三条标签等式传输：子句在带标签的槽位上陈述，而键则以三个标签的数码写出。
<!--ja-->
この所属は、三つのタグの等式に沿って輸送される。節はタグつきのスロットで述べられる一方、鍵は三つのタグの数項で書かれるからである。
<!--/-->

```agda
    subst (λ u → ⟨ u ∈ Cv ⟩)
      (cong (pr A) (cong₂ pr (tg k) (cong₂ pr (cong (λ a → pr a (fst x)) (tg Nx)) (cong (λ a → pr a (fst y)) (tg Ny)))))
      (atomKey-out (sh 6 C) i3 (sh 6 (N k)) (sh 6 (N Nx)) i1 (sh 6 (N Ny)) i0 (y ∷ x ∷ δ) (h x x∈ y y∈))
```

<!--en-->
The inward direction rebuilds the clause: given the property for all pairs, it suffices to instantiate it at the given `x` and `y`, with the naming equations run in reverse.
<!--zh-->
向内方向重建子句：既已给出对一切对的性质，只需在给定的 `x` 与 `y` 处实例化，并把命名等式反向运行。
<!--ja-->
内向きの方向は節を組み立て直す。すべての対に対する性質が与えられていれば、与えられた `x` と `y` で具体化し、名指しの等式を逆向きに走らせれば足りる。
<!--/-->

```agda
  atomClose-in : (k Nx Ny : Fin 10) (X : Fin (4 + m)) (Y : Fin (5 + m))
               → ((x y : S) → ⟨ fst x ∈ fst (lookup X δ) ⟩ → ⟨ fst y ∈ fst (lookup Y (x ∷ δ)) ⟩
                  → ⟨ pr A (pr (# (toℕ k)) (pr (pr (# (toℕ Nx)) (fst x)) (pr (# (toℕ Ny)) (fst y)))) ∈ Cv ⟩)
               → ⟨ δ ⊨ Cl.atomClose k Nx Ny X Y ⟩
  atomClose-in k Nx Ny X Y g x x∈ y y∈ =
```

<!--en-->
The membership is transported into the tagged slots by the reversed renamings, and the introduction rule of the closure clause finishes the case.
<!--zh-->
隶属沿反向改名被传输进带标签的槽位，闭包子句的引入规则随之完成这一情形。
<!--ja-->
所属は逆向きの改名に沿ってタグつきのスロットへ輸送され、閉包の節の導入規則がこの場合を閉じる。
<!--/-->

```agda
    atomKey-in (sh 6 C) i3 (sh 6 (N k)) (sh 6 (N Nx)) i1 (sh 6 (N Ny)) i0 (y ∷ x ∷ δ)
      (subst (λ u → ⟨ u ∈ Cv ⟩)
        (sym (cong (pr A) (cong₂ pr (tg k) (cong₂ pr (cong (λ a → pr a (fst x)) (tg Nx)) (cong (λ a → pr a (fst y)) (tg Ny))))))
        (g x y x∈ y∈))
```

<!--en-->
The binary closure clause ranges over two members `c₁` and `c₂` of the code set. The equations `fst c₁ ≡ pr A (fst a)` and `fst c₂ ≡ pr A (fst b)` expose their payloads `a` and `b` at the fixed arity `A`; the clause then places the binary key with payload `pr (fst a) (fst b)` back in the code set.
<!--zh-->
二元闭包子句量化码集中的两个成员 `c₁`、`c₂`。等式 `fst c₁ ≡ pr A (fst a)` 与 `fst c₂ ≡ pr A (fst b)` 显露它们在固定元数 `A` 处的载荷 `a`、`b`；子句随后断言以 `pr (fst a) (fst b)` 为载荷的二元键仍属于码集。
<!--ja-->
二項の閉性の節は、符号集合の二つの要素 `c₁` と `c₂` を量化する。等式 `fst c₁ ≡ pr A (fst a)` と `fst c₂ ≡ pr A (fst b)` は、固定アリティ `A` におけるそれぞれのペイロード `a` と `b` を取り出す。すると、この節はペイロード `pr (fst a) (fst b)` をもつ二項キーが再び符号集合に属することを述べる。
<!--/-->

```agda
  binClose-out : (k : Fin 10) → ⟨ δ ⊨ Cl.binClose k ⟩
               → (c₁ c₂ a b : S) → ⟨ fst c₁ ∈ Cv ⟩ → ⟨ fst c₂ ∈ Cv ⟩
               → fst c₁ ≡ pr A (fst a) → fst c₂ ≡ pr A (fst b)
               → ⟨ pr A (pr (# (toℕ k)) (pr (fst a) (fst b))) ∈ Cv ⟩
  binClose-out k h c₁ c₂ a b c₁∈ c₂∈ e₁ e₂ =
```

<!--en-->
The membership is transported along the tag renaming of the label, and the two nested universal layers are discharged by the elimination lemmas of the bounded quantifiers, each entry entering the inner clause through its own pairing container.
<!--zh-->
该隶属沿标签的改名传输，两层嵌套的全称则由有界量词的消去引理兑现：每个条目都经由自己的配对容器进入内层子句。
<!--ja-->
所属はタグの改名に沿って輸送され、二重に入れ子になった全称の層は有界量化子の消去の補題によって処理される。各項目はみずからの対の容器を通して内側の節に入る。
<!--/-->

```agda
    subst (λ u → ⟨ u ∈ Cv ⟩) (cong (pr A) (cong (λ v → pr v (pr (fst a) (fst b))) (tg k)))
      (binKey-out (sh 10 C) i7 (sh 10 (N k)) i3 i0 δ10
        (useSnd i0 δ8 arS b e₂ (binKey (sh 10 C) i7 (sh 10 (N k)) i3 i0) i5 refl
          (useSnd i0 (c₁ ∷ δ) arS a e₁ inner i2 refl (h c₁ c₁∈) c₂ c₂∈)))
    where
```

<!--en-->
After `c₁` has been chosen and written as `pr A a`, the inner formula quantifies over a second code `c₂` in the code set and exposes it as `pr A b`. It then requires the binary key formed from tag `k` and the paired payload `pr a b`; the auxiliary environments record the two decompositions of `c₁` and `c₂`.
<!--zh-->
选定 `c₁` 并把它写成 `pr A a` 后，内层公式量化码集中的第二个码 `c₂`，并把它显露为 `pr A b`。随后要求由标签 `k` 与配对载荷 `pr a b` 形成的二元键属于码集；辅助环境记录 `c₁` 与 `c₂` 的两次分解。
<!--ja-->
`c₁` を選んで `pr A a` と表した後、内側の論理式は符号集合の第二の符号 `c₂` を量化し、それを `pr A b` として取り出す。次に、タグ `k` と対にしたペイロード `pr a b` からなる二項キーが符号集合に属することを要求する。補助環境は `c₁` と `c₂` の二つの分解を記録する。
<!--/-->

```agda
    inner : Formula S (7 + m)
    inner = ∀̇∈ (var (sh 7 C)) (sndAll i0 i5 (binKey (sh 10 C) i7 (sh 10 (N k)) i3 i0))
    δ7 : S ^ (7 + m)
    δ7 = a ∷ container c₁ arS a e₁ .fst ∷ c₁ ∷ δ
    δ8 : S ^ (8 + m)
```

<!--en-->
For the quantifier clauses, the environment must remember both a subkey and the data that determine its arity. The environment `δ8` contains the candidate argument `a`, a proposed successor arity `ar'`, the pair witnessing their relation, and the subkey `c₁`; `δ10` adds the term used as the bound in a bounded quantifier.
<!--zh-->
量词子句必须同时记住子键和决定其元数的数据。环境 `δ8` 包含候选实参 `a`、拟定的后继元数 `ar'`、见证二者关系的有序对以及子键 `c₁`；处理有界量词时，`δ10` 还加入充当界的词项。
<!--ja-->
量化子の条項では、下位キーと、そのアリティを定めるデータを同時に覚えておく必要がある。環境 `δ8` は、候補となる引数 `a`、後続アリティの候補 `ar'`、両者の関係を証明する順序対、下位キー `c₁` を含む。有界量化子を扱う `δ10` には、境界となる項も加わる。
<!--/-->

```agda
    δ8 = c₂ ∷ δ7
    δ10 : S ^ (10 + m)
    δ10 = b ∷ container c₂ arS b e₂ .fst ∷ δ8
```

<!--en-->
The inward direction for a binary closure clause starts from its mathematical closure rule: two subkeys of the same arity that belong to the domain determine a composite key that also belongs to it. The two universal quantifiers merely make the chosen subkeys explicit.
<!--zh-->
二元闭包子句的向内方向从相应的数学闭包规则出发：同一元数的两个子键若属于该域，由它们构成的复合键也属于该域。公式中的两层全称量化只是把所选的两个子键显式写出。
<!--ja-->
二項閉包の条項を内向きに読むときは、対応する数学的な閉包則から出発する。同じアリティをもつ二つの下位キーが領域に属するなら、それらから作られる複合キーも領域に属する。二つの全称量化は、選んだ下位キーを明示するためのものである。
<!--/-->

```agda
  binClose-in : (k : Fin 10)
              → ((c₁ c₂ a b : S) → ⟨ fst c₁ ∈ Cv ⟩ → ⟨ fst c₂ ∈ Cv ⟩
                 → fst c₁ ≡ pr A (fst a) → fst c₂ ≡ pr A (fst b)
                 → ⟨ pr A (pr (# (toℕ k)) (pr (fst a) (fst b))) ∈ Cv ⟩)
              → ⟨ δ ⊨ Cl.binClose k ⟩
```

<!--en-->
Introducing the two quantified components extends the environment in the order prescribed by the formula. At the innermost implication, the assumed closure rule gives membership of the composite key; the tag equation `tg k` identifies its displayed tag with the numeral required by `binKey`.
<!--zh-->
依公式规定的次序引入两个量化分量，便得到相应的扩展环境。在最内层的蕴涵中，所假设的闭包规则给出复合键的隶属证明；标签等式 `tg k` 再把所展示的标签与 `binKey` 所要求的数码对齐。
<!--ja-->
二つの量化された成分を論理式が定める順に導入すると、対応する拡張環境が得られる。最も内側の含意では、仮定した閉包則から複合キーの所属が得られ、タグの等式 `tg k` が、表示されたタグを `binKey` の要求する数項に揃える。
<!--/-->

```agda
  binClose-in k g c₁ c₁∈ = sndAll-in i0 i2 (∀̇∈ (var (sh 7 C)) (sndAll i0 i5 (binKey (sh 10 C) i7 (sh 10 (N k)) i3 i0))) (c₁ ∷ δ) (λ a s s∈ a∈ e₁ c₂ c₂∈ →
    sndAll-in i0 i5 (binKey (sh 10 C) i7 (sh 10 (N k)) i3 i0) (c₂ ∷ a ∷ s ∷ c₁ ∷ δ) (λ b s' s'∈ b∈ e₂ →
      binKey-in (sh 10 C) i7 (sh 10 (N k)) i3 i0 (b ∷ s' ∷ c₂ ∷ a ∷ s ∷ c₁ ∷ δ)
        (subst (λ u → ⟨ u ∈ Cv ⟩) (sym (cong (pr A) (cong (λ v → pr v (pr (fst a) (fst b))) (tg k))))
          (g c₁ c₂ a b c₁∈ c₂∈ e₁ e₂))))
```

<!--en-->
For falsity there is no subordinate code to inspect. Reading its closure clause outward therefore reduces to the equation identifying the payload with the zero numeral, followed by transport along the tag equations.
<!--zh-->
假的编码没有需要检查的子码。因此，向外读取它的闭包子句，只需利用载荷等于零数码的等式，再沿标签等式运输。
<!--ja-->
偽の符号には調べるべき下位符号がない。したがって、その閉包条項を外向きに読むには、ペイロードが零の数項に等しいことを用い、タグの等式に沿って輸送すれば十分である。
<!--/-->

```agda
  conClose-out : (k : Fin 10) → ⟨ δ ⊨ Cl.conClose k ⟩ → ⟨ pr A (pr (# (toℕ k)) (# 0)) ∈ Cv ⟩
  conClose-out k h =
    subst (λ u → ⟨ u ∈ Cv ⟩) (cong (pr A) (cong₂ pr (tg k) (tg f0)))
      (unKey-out (sh 4 C) i1 (sh 4 (N k)) (sh 4 (N f0)) δ h)
```

<!--en-->
Conversely, membership of the falsity key is transported back along the same equations to satisfy the closure clause. This case has no recursive premise: the zero payload completely determines the key.
<!--zh-->
反过来，假键的隶属证明沿同一组等式反向运输，便得到闭包子句的满足。这个情形没有递归前提，因为零载荷已经完全确定了该键。
<!--ja-->
逆に、偽のキーの所属を同じ等式に沿って反対向きに輸送すれば、閉包条項の充足が得られる。この場合には再帰的な前提がなく、零のペイロードだけでキーが完全に定まる。
<!--/-->

```agda
  conClose-in : (k : Fin 10) → ⟨ pr A (pr (# (toℕ k)) (# 0)) ∈ Cv ⟩ → ⟨ δ ⊨ Cl.conClose k ⟩
  conClose-in k h =
    unKey-in (sh 4 C) i1 (sh 4 (N k)) (sh 4 (N f0)) δ
      (subst (λ u → ⟨ u ∈ Cv ⟩) (sym (cong (pr A) (cong₂ pr (tg k) (tg f0)))) h)
```

<!--en-->
The unbounded-quantifier clause is read outward with the quantified components explicit: given a subkey `c₁` of the domain, a presentation `c₁ = pr ar' a`, and the equation `ar' = sucV A`, the quantifier key at the current arity belongs to the domain. The three hypotheses are exactly the data of a predecessor slice member.
<!--zh-->
无界量词子句的向外读法把被量化的分量显式给出：给定域的子键 `c₁`、呈现 `c₁ = pr ar' a` 与等式 `ar' = sucV A`，当前元数处的量词键便属于该域。这三条假设恰是前驱切片成员的全部数据。
<!--ja-->
非有界量化子の条項は、量化された成分を明示して外向きに読まれる。領域の下位キー `c₁`、その表示 `c₁ = pr ar' a`、そして等式 `ar' = sucV A` が与えられれば、現在のアリティでの量化子のキーが領域に属する。三つの仮定は、前者のスライスの要素のデータそのものである。
<!--/-->

```agda
  quClose-out : (k : Fin 10) → ⟨ δ ⊨ Cl.quClose k ⟩
              → (c₁ ar' a : S) → ⟨ fst c₁ ∈ Cv ⟩ → fst c₁ ≡ pr (fst ar') (fst a) → fst ar' ≡ sucV A
              → ⟨ pr A (pr (# (toℕ k)) (fst a)) ∈ Cv ⟩
  quClose-out k h c₁ ar' a c₁∈ e₁ es =
    subst (λ u → ⟨ u ∈ Cv ⟩) (cong (pr A) (cong (λ v → pr v (fst a)) (tg k)))
```

<!--en-->
The proof extends the environment by `a`, `ar'`, and the container, opens the implication with the successor equation, and reads the `unKey` membership in the eight-slot environment. Transport along the tag equation then gives membership for the numeral represented by tag `k`.
<!--zh-->
证明把 `a`、`ar'` 与容器加入环境，以后继等式进入蕴涵的结论，并在八槽环境中读取 `unKey` 的隶属。随后沿标签等式运输，得到由标签 `k` 所表示数码对应的隶属。
<!--ja-->
証明では、`a`、`ar'`、コンテナを環境に加え、後続の等式を用いて含意の結論へ進み、八つのスロットをもつ環境で `unKey` の所属を読み取る。さらにタグの等式に沿って輸送し、タグ `k` が表す数項に対応する所属を得る。
<!--/-->

```agda
      (unKey-out (sh 8 C) i5 (sh 8 (N k)) i0 δ8
        (useBoth i0 (c₁ ∷ δ) ar' a e₁ (sucAtL i5 i1 ⇒̇ unKey (sh 8 C) i5 (sh 8 (N k)) i0) (h c₁ c₁∈)
          (suc-in i5 i1 δ8 es)))
    where
    δ8 : S ^ (8 + m)
```

<!--en-->
The extended environment packages the three quantified components with the original one, in the order the implication reads them.
<!--zh-->
扩展环境按蕴涵所读取的次序，把三个被量化的分量与原有分量打包在一起。
<!--ja-->
拡張された環境は、量化された三つの成分を、含意が読む順に、もとの成分とともにまとめる。
<!--/-->

```agda
    δ8 = a ∷ ar' ∷ container c₁ ar' a e₁ .fst ∷ c₁ ∷ δ
```

<!--en-->
For the inward direction, introduce the two quantified components of the clause. The extended environment contains the proposed successor arity `ar'` and the payload `a`; the successor equation then supplies the premise of the implication.
<!--zh-->
向内读取时，先引入子句所量化的两个分量。扩展环境包含拟定的后继元数 `ar'` 与载荷 `a`，后继等式随后给出蕴涵的前提。
<!--ja-->
内向きに読むときは、条項で量化された二つの成分を導入する。拡張環境には、後続アリティの候補 `ar'` とペイロード `a` が入り、後続の等式が含意の前提を与える。
<!--/-->

```agda
  quClose-in : (k : Fin 10)
             → ((c₁ ar' a : S) → ⟨ fst c₁ ∈ Cv ⟩ → fst c₁ ≡ pr (fst ar') (fst a) → fst ar' ≡ sucV A
                → ⟨ pr A (pr (# (toℕ k)) (fst a)) ∈ Cv ⟩)
             → ⟨ δ ⊨ Cl.quClose k ⟩
  quClose-in k g c₁ c₁∈ = bothAll-in i0 (sucAtL i5 i1 ⇒̇ unKey (sh 8 C) i5 (sh 8 (N k)) i0) (c₁ ∷ δ) (λ ar' a s s∈ ar'∈ a∈ e₁ hs →
```

<!--en-->
Apply the assumed closure rule to these data, then transport the resulting membership along the tag equation to obtain the `unKey` conclusion. This completes the inward reading of the unbounded-quantifier clause.
<!--zh-->
对这些数据应用所假设的闭包规则，再沿标签等式运输所得隶属，便得到 `unKey` 的结论。无界量词子句的向内读法由此完成。
<!--ja-->
これらのデータに仮定した閉包則を適用し、得られた所属をタグの等式に沿って輸送すると、`unKey` の結論が得られる。これで、非有界量化子の条項を内向きに読む証明が完成する。
<!--/-->

```agda
    unKey-in (sh 8 C) i5 (sh 8 (N k)) i0 (a ∷ ar' ∷ s ∷ c₁ ∷ δ)
      (subst (λ u → ⟨ u ∈ Cv ⟩) (sym (cong (pr A) (cong (λ v → pr v (fst a)) (tg k))))
        (g c₁ ar' a c₁∈ e₁ (suc-out i5 i1 (a ∷ ar' ∷ s ∷ c₁ ∷ δ) hs))))
```

<!--en-->
The bounded-quantifier clause has one additional premise. Besides a body key at the successor arity, it requires a legal bounding term `x` at the current arity; the resulting payload records the quantifier tag, the term tag `Nx`, the term itself, and the body payload as nested pairs.
<!--zh-->
有界量词子句多出一项前提。除了后继元数处的主体键，还需要一个在当前元数处合法的界词项 `x`；所得载荷以嵌套有序对依次记录量词标签、词项标签 `Nx`、该词项以及主体载荷。
<!--ja-->
有界量化子の条項には前提が一つ加わる。後続アリティでの本体キーに加えて、現在のアリティで正しい境界項 `x` が必要である。得られるペイロードは、量化子のタグ、項のタグ `Nx`、その項、本体のペイロードを入れ子の順序対として記録する。
<!--/-->

```agda
  bqClose-out : (k Nx : Fin 10) (X : Fin (8 + m)) → ⟨ δ ⊨ Cl.bqClose k Nx X ⟩
              → (c₁ ar' a : S) → ⟨ fst c₁ ∈ Cv ⟩ → (e₁ : fst c₁ ≡ pr (fst ar') (fst a)) → fst ar' ≡ sucV A
              → (x : S) → ⟨ fst x ∈ fst (lookup X (a ∷ ar' ∷ container c₁ ar' a e₁ .fst ∷ c₁ ∷ δ)) ⟩
              → ⟨ pr A (pr (# (toℕ k)) (pr (pr (# (toℕ Nx)) (fst x)) (fst a))) ∈ Cv ⟩
  bqClose-out k Nx X h c₁ ar' a c₁∈ e₁ es x x∈ =
```

<!--en-->
The proof extends the environment by the bounding term and applies bounded-key elimination there. The two tag equations, one for the quantifier constructor and one for the term constructor, transport the nested pair to the shape named in the conclusion.
<!--zh-->
证明把界词项加入环境，并在该环境中应用有界键消去。两条标签等式分别对应量词构造子与词项构造子，它们把嵌套有序对运输到结论所指定的形状。
<!--ja-->
証明では、境界を表す項を環境に加え、その環境で有界キーの消去を適用する。二つのタグ等式は、それぞれ量化子の構成子と項の構成子に対応し、入れ子の対を結論で指定された形へ輸送する。
<!--/-->

```agda
    subst (λ u → ⟨ u ∈ Cv ⟩)
      (cong (pr A) (cong₂ pr (tg k) (cong (λ v → pr v (fst a)) (cong (λ v → pr v (fst x)) (tg Nx)))))
      (bndKey-out (sh 9 C) i6 (sh 9 (N k)) (sh 9 (N Nx)) i0 i1 (x ∷ δ8)
        (useBoth i0 (c₁ ∷ δ) ar' a e₁ (sucAtL i5 i1 ⇒̇ ∀̇∈ (var X) (bndKey (sh 9 C) i6 (sh 9 (N k)) (sh 9 (N Nx)) i0 i1))
          (h c₁ c₁∈) (suc-in i5 i1 δ8 es) x x∈))
```

<!--en-->
The eight-slot environment repeats the packaging used by the unbounded case, with the bound slot consumed by the elimination.
<!--zh-->
八槽环境重复无界情形的打包方式，而界槽由该消去消耗。
<!--ja-->
八つの枠の環境は、非有界の場合と同じまとめ方を繰り返し、界の枠は消去に使われる。
<!--/-->

```agda
    where
    δ8 : S ^ (8 + m)
    δ8 = a ∷ ar' ∷ container c₁ ar' a e₁ .fst ∷ c₁ ∷ δ
```

<!--en-->
For the inward direction, assume the mathematical closure rule displayed in the type. It is quantified over an arbitrary extended environment `s`, because the set from which the bounding term is chosen is evaluated in that environment.
<!--zh-->
向内读取时，假设类型中所写的数学闭包规则。该规则对任意扩展环境 `s` 量化，因为界词项所属的集合需要在这个环境中求值。
<!--ja-->
内向きに読むため、型に示された数学的閉包則を仮定する。この規則が任意の拡張環境 `s` について量化されているのは、境界を表す項を選ぶ集合が、その環境で評価されるからである。
<!--/-->

```agda
  bqClose-in : (k Nx : Fin 10) (X : Fin (8 + m))
             → ((c₁ ar' a s : S) → ⟨ fst c₁ ∈ Cv ⟩ → fst c₁ ≡ pr (fst ar') (fst a) → fst ar' ≡ sucV A
                → (x : S) → ⟨ fst x ∈ fst (lookup X (a ∷ ar' ∷ s ∷ c₁ ∷ δ)) ⟩
                → ⟨ pr A (pr (# (toℕ k)) (pr (pr (# (toℕ Nx)) (fst x)) (fst a))) ∈ Cv ⟩)
             → ⟨ δ ⊨ Cl.bqClose k Nx X ⟩
```

<!--en-->
Introduce the quantified subkey data and the bounding term, then apply the assumed closure rule in the resulting environment. Transport along the two tag equations turns its conclusion into the membership required by `bndKey`, completing the inward reading of the bounded-quantifier clause.
<!--zh-->
先引入量化的子键数据与界词项，再在所得环境中应用所假设的闭包规则。沿两条标签等式运输其结论，便得到 `bndKey` 所要求的隶属，从而完成有界量词子句的向内读法。
<!--ja-->
量化された下位キーのデータと境界を表す項を導入し、得られた環境で仮定した閉包則を適用する。その結論を二つのタグ等式に沿って輸送すると、`bndKey` が要求する所属が得られ、有界量化子の条項を内向きに読む証明が完成する。
<!--/-->

```agda
  bqClose-in k Nx X g c₁ c₁∈ = bothAll-in i0 (sucAtL i5 i1 ⇒̇ ∀̇∈ (var X) (bndKey (sh 9 C) i6 (sh 9 (N k)) (sh 9 (N Nx)) i0 i1)) (c₁ ∷ δ) (λ ar' a s s∈ ar'∈ a∈ e₁ hs x x∈ →
    bndKey-in (sh 9 C) i6 (sh 9 (N k)) (sh 9 (N Nx)) i0 i1 (x ∷ a ∷ ar' ∷ s ∷ c₁ ∷ δ)
      (subst (λ u → ⟨ u ∈ Cv ⟩)
        (sym (cong (pr A) (cong₂ pr (tg k) (cong (λ v → pr v (fst a)) (cong (λ v → pr v (fst x)) (tg Nx))))))
        (g c₁ ar' a s c₁∈ e₁ (suc-out i5 i1 (a ∷ ar' ∷ s ∷ c₁ ∷ δ) hs) x x∈)))
```
</div>
</details>

<!--en-->
## Soundness: decoding every member
<!--zh-->
## 可靠性：解码每个成员
<!--ja-->
## 健全性：各要素の復号
<!--/-->

<!--en-->
To prove soundness, we now connect three descriptions already available: numerical tags identify the ten constructors, shape and closure formulas describe their internal set codes, and `AllCodes` relates those codes back to the external formula grammar. Propositionality will allow truncated witnesses to be eliminated without choosing representatives.
<!--zh-->
为证明可靠性，现在把三类已有描述联系起来：数值标签识别十种构造，形状公式与闭包公式描述它们在集合内部的编码，而 `AllCodes` 把这些码重新联系到外部公式文法。相关性质都是命题，因此可以消去截断见证而不必选取代表。
<!--ja-->
健全性を証明するため、ここまでに得た三つの記述を結ぶ。数値タグは十種類の構成子を識別し、形と閉包の論理式は集合内部の符号を記述し、`AllCodes` はそれらの符号を外部の論理式文法へ結び戻す。関係する性質は命題なので、代表を選ばずに切り詰められた証人を除去できる。
<!--/-->

<!--en-->
The canonical code set provides both directions of this comparison: a member can be read as a formula key, and every formula has a canonical key. The remaining imports supply the witnesses for recorded arities and the fact that conjunctions of propositions are again propositions.
<!--zh-->
典范码集提供这种比较的两个方向：它的成员可以读作公式键，而每条公式也都有典范键。其余引入给出已记录元数的见证，以及两个命题的合取仍为命题这一事实。
<!--ja-->
標準的な符号集合は、この比較の両方向を与える。その要素は論理式キーとして読め、どの論理式にも標準的なキーがある。残りの導入からは、記録されたアリティの証人と、二つの命題の連言も命題であるという事実を得る。
<!--/-->

<!--en-->
Fix a working set `Wv`, whose elements may occur as constants, and a candidate code domain `Cv`. The following argument is parametric in these two sets; no assumption yet identifies `Cv` with the canonical domain `AllCodes`.
<!--zh-->
固定一个工作集 `Wv`，其元素可以作为常元出现；再固定一个候选码域 `Cv`。以下论证对这两个集合保持参数化，此时尚未假设 `Cv` 就是典范码域 `AllCodes`。
<!--ja-->
定数として現れうる要素をもつ作業集合 `Wv` と、候補となる符号領域 `Cv` を固定する。以下の議論はこの二つの集合をパラメータとし、この時点では `Cv` が標準的な領域 `AllCodes` であるとは仮定しない。
<!--/-->

<details open class="submodule-fold">
<summary class="submodule-fold-heading">
```agda
module _ (Wv Cv : V ℓ) where
```
</summary>
<div class="submodule-fold-content">

```agda
  open CodesSem Wv Cv
```

<!--en-->
Every payload condition `PayN n ar r` is a proposition. For tags zero through four this follows immediately from propositional truncation: the condition asserts only that suitable components merely exist.
<!--zh-->
每个载荷条件 `PayN n ar r` 都是命题。对标签零至四，这直接来自命题截断，因为相应条件只断言合适的分量纯粹存在。
<!--ja-->
どのペイロード条件 `PayN n ar r` も命題である。タグ 0 から 4 については命題的切り詰めから直ちに従う。対応する条件は、適切な成分が単に存在することだけを述べるからである。
<!--/-->

```agda
  isPropPayN : (n : ℕ) (ar r : V ℓ) → isProp (PayN n ar r)
  isPropPayN 0 ar r = squash₁
  isPropPayN 1 ar r = squash₁
  isPropPayN 2 ar r = squash₁
  isPropPayN 3 ar r = squash₁
```

<!--en-->
The remaining constructor tags use the same principle in the form appropriate to their payloads. Falsity has a unique zero payload; unbounded quantifiers require membership in `Cv`, which is proposition-valued; bounded quantifiers again use truncated existence.
<!--zh-->
其余构造标签也依各自的载荷使用同一原则。假的载荷唯一地等于零；无界量词要求属于 `Cv`，而隶属关系取值于命题；有界量词则再次使用截断存在。
<!--ja-->
残りの構成子タグでも、各ペイロードに応じた形で同じ原理を用いる。偽のペイロードは零に一意に等しく、非有界量化子は命題値をとる `Cv` への所属を要求し、有界量化子は再び切り詰められた存在を用いる。
<!--/-->

```agda
  isPropPayN 4 ar r = squash₁
  isPropPayN 5 ar r = setIsSet r (# 0)
  isPropPayN 6 ar r = snd (pr (sucV ar) r ∈ Cv)
  isPropPayN 7 ar r = snd (pr (sucV ar) r ∈ Cv)
  isPropPayN 8 ar r = squash₁
```

<!--en-->
Tag nine is handled by truncated existence as well. Any numeral beyond the ten constructor tags has an empty payload type, and an empty type is a proposition. Thus `PayN` is proposition-valued for every natural-number tag.
<!--zh-->
标签九同样由截断存在处理。超过十种构造标签的任何数码，其载荷类型都是空类型，而空类型是命题。因此，对每个自然数标签，`PayN` 都取值于命题。
<!--ja-->
タグ 9 も切り詰められた存在によって扱われる。十種類の構成子タグを越える数項ではペイロード型が空であり、空型は命題である。したがって `PayN` は、どの自然数タグについても命題値をとる。
<!--/-->

```agda
  isPropPayN 9 ar r = squash₁
  isPropPayN (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc _)))))))))) ar r = isProp⊥*
```

<!--en-->
The key-alignment lemma converts a `Key` at arity `ar` into a payload at any other decomposition `p = (# n, r)` of the same set. Pair injectivity and numeral injectivity align the tag and the payload separately, and because `PayN n ar r` is a proposition, the truncated key may be eliminated into it.
<!--zh-->
键对齐引理把元数 `ar` 处的一个 `Key` 转换为同一集合的任何其他分解 `p = (# n, r)` 处的载荷。配对单射性与数码单射性分别对齐标签与载荷；而 `PayN n ar r` 是命题，故截断的键可消去到它。
<!--ja-->
キーを揃える補題は、アリティ `ar` での `Key` を、同じ集合の別の分解 `p = (# n, r)` でのペイロードへ変える。対の単射性と数項の単射性が、タグとペイロードを別々に揃える。そして `PayN n ar r` は命題なので、切り詰められたキーをそこへ消去できる。
<!--/-->

```agda
  keyAt : (ar p : V ℓ) → Key ar p → (n : ℕ) (r : V ℓ) → p ≡ pr (# n) r → PayN n ar r
  keyAt ar p key n r e = rec₁ (isPropPayN n ar r)
    (λ { (k , r' , (e' , pay)) →
      let q = pr-inj (sym e ∙ e')
      in subst2 (λ j x → PayN j ar x) (sym (#-inj′ (q .fst))) (sym (q .snd)) pay })
```

<!--en-->
Applying this elimination to `key` completes the alignment: the tag and payload obtained from `Key` have already been transported to the prescribed numeral `n` and payload `r`.
<!--zh-->
把上述消去应用于 `key`，对齐便告完成：从 `Key` 取得的标签与载荷已经运输到指定的数码 `n` 和载荷 `r`。
<!--ja-->
この除去を `key` に適用すると、位置合わせが完了する。`Key` から得たタグとペイロードは、指定された数項 `n` とペイロード `r` へすでに輸送されている。
<!--/-->

```agda
    key
```
</div>
</details>

<!--en-->
The first recovery lemma converts a term-code statement into a satisfaction of the shape chapter's term predicate. It is stated for arbitrary slots and proved by eliminating the truncated `IsTmV` into the proposition-valued satisfaction.
<!--zh-->
第一条恢复引理把词项码陈述转换成形状章的词项谓词的一个满足。它对任意槽位陈述，证明方法是把这个截断的 `IsTmV` 消去到命题值的满足之中。
<!--ja-->
最初の復元の補題は、項の符号の主張を、形の章の項の述語の充足へ変換する。任意の枠に対して述べられ、切り詰められた `IsTmV` を、命題値の充足へ消去することで証明される。
<!--/-->

```agda
tmWit : ∀ {j} (ti Ni Ai : Fin j) (env : S ^ j)
      → IsTmV (fst (lookup Ai env)) (fst (lookup ti env)) (fst (lookup Ni env))
      → ⟨ env ⊨ isTmAt ti Ni Ai ⟩
tmWit ti Ni Ai env = rec₁ (snd (env ⊨ isTmAt ti Ni Ai))
  (λ { (inl (x , (e , x∈))) →
```

<!--en-->
In the constant branch, `down` presents the witness `x` as an element of the working set `Wv`. Tag adequacy transports the pair equation, while the original membership proof supplies the other conjunct. The resulting evidence enters the left disjunct of the shape predicate.
<!--zh-->
常元支中，`down` 把见证 `x` 表示为工作集 `Wv` 的元素。标签充分性运输有序对等式，原有的隶属证明则给出另一个合取项；所得证据进入形状谓词的左析取支。
<!--ja-->
定数の分岐では、`down` が証人 `x` を作業集合 `Wv` の要素として表示する。タグの妥当性が順序対の等式を輸送し、もとの所属証明がもう一方の連言肢を与える。得られた証拠は、形の述語の左の選言肢に入る。
<!--/-->

```agda
         ∣ inl ∣ down (lookup Ai env) x x∈
           , ( subst ⟨_⟩ (sym (tagAtL-adequate (suc ti) 0 zero (down (lookup Ai env) x x∈ ∷ env))) e
             , x∈ ) ∣₁ ∣₁
     ; (inr (i , (e , i∈))) →
         ∣ inr ∣ down (lookup Ni env) i i∈
```

<!--en-->
The variable branch repeats the construction with the numeral slot presenting the index. Both branches together show that term codes convert into shape satisfactions without any choice.
<!--zh-->
变元支以数码槽呈现索引，重复同一构造。两支合起来说明：词项码到形状满足的转换无须任何选择。
<!--ja-->
変数の分岐は、数項の枠で添字を提示して、同じ構成を繰り返す。二つの分岐合わせて、項の符号から形の充足への変換に選択が不要であることが分かる。
<!--/-->

```agda
           , ( subst ⟨_⟩ (sym (tagAtL-adequate (suc ti) 1 zero (down (lookup Ni env) i i∈ ∷ env))) e
             , i∈ ) ∣₁ ∣₁ })
```

<!--en-->
We can now state soundness for a candidate domain `C`. Assume that the constant alphabet is the set `W`, that the ten tag slots contain the correct numerals, that every arity recorded in the environment set is a natural-number numeral, and that `C` satisfies the shape description. From these assumptions, every member of `C` will be recovered as a formula key.
<!--zh-->
现在可以陈述候选域 `C` 的可靠性。假设常元字母表是集合 `W`，十个标签槽包含正确的数码，环境集中记录的每个元数都是自然数数码，并且 `C` 满足形状描述。由这些假设，可以把 `C` 的每个成员恢复为公式键。
<!--ja-->
これで候補領域 `C` の健全性を述べられる。定数字母表が集合 `W` であり、十個のタグ枠に正しい数項が入り、環境集合に記録された各アリティが自然数の数項であり、`C` が形の記述を満たすと仮定する。これらの仮定から、`C` の各要素を論理式キーとして復元する。
<!--/-->

<details open class="submodule-fold">
<summary class="submodule-fold-heading">
```agda
module CodesSound {m : ℕ} (C w E : Fin m) (N : Fin 10 → Fin m) (γ : S ^ m) (W : S)
  (qw : fst (lookup w γ) ≡ fst W) (tg : Tags γ N)
  (arity : (n F : S) → ⟨ pr (fst n) (fst F) ∈ fst (lookup E γ) ⟩ → ∥ Σ[ k ∈ ℕ ] (fst n ≡ # k) ∥₁)
  (hs : ⟨ γ ⊨ shapeAt C w E N ⟩) where
```
</summary>
<div class="submodule-fold-content">

```agda
  private
```

<!--en-->
Write `Cv` for the underlying set of the candidate domain and `CS` for its representative in the constructible structure, which packages that set with a proof of constructibility. Similarly, `Wv` and `Ev` denote the underlying working set and environment set. These abbreviations distinguish host-level sets used in membership statements from their packaged representatives in first-order environments.
<!--zh-->
记 `Cv` 为候选域的底层集合，记 `CS` 为它在可构造结构中的代表，其中把该集合与其可构造性证明打包在一起。类似地，`Wv` 与 `Ev` 分别表示工作集和环境集的底层集合。这些缩写区分隶属陈述所用的宿主层集合与一阶环境中所用的带证明代表。
<!--ja-->
`Cv` を候補領域の基礎となる集合、`CS` を構成可能性の証明とともにその集合をまとめた、構成可能構造内の表示と書く。同様に、`Wv` と `Ev` は作業集合と環境集合の基礎となる集合を表す。これらの略記により、所属の主張で使うホスト側の集合と、一階環境で使う証明つきの表示とを区別する。
<!--/-->

```agda
    Cv = fst (lookup C γ)
    CS = lookup C γ
    Wv = fst (lookup w γ)
    Ev = fst (lookup E γ)
    module SR = ShapeRead C w E N γ tg
```

<!--en-->
The payload conditions are henceforth interpreted relative to the fixed working set `Wv` and candidate domain `Cv`.
<!--zh-->
此后，所有载荷条件都相对于固定的工作集 `Wv` 与候选域 `Cv` 解释。
<!--ja-->
以後、すべてのペイロード条件を、固定した作業集合 `Wv` と候補領域 `Cv` に相対して解釈する。
<!--/-->

```agda
  open CodesSem Wv Cv
```

<!--en-->
The proof proceeds through auxiliary lemmas that recover the payload information hidden by the shape formula.
<!--zh-->
证明将通过若干辅助引理，逐步恢复形状公式所隐藏的载荷信息。
<!--ja-->
証明ではいくつかの補助補題を通して、形の論理式の中に隠されたペイロード情報を順に復元する。
<!--/-->

```agda
  private
```

<!--en-->
For a chosen member `c`, the environment `δ' c` places the candidate domain and `c` before the original environment. This is the context in which the shape predicate for that member is interpreted.
<!--zh-->
对一个选定的成员 `c`，环境 `δ' c` 把候选域与 `c` 放在原环境之前。该成员的形状谓词正是在这个语境中解释的。
<!--ja-->
選んだ要素 `c` に対し、環境 `δ' c` は候補領域と `c` を元の環境の前に置く。その要素についての形の述語は、この環境で解釈される。
<!--/-->

```agda
    δ' : S → S ^ (2 + m)
    δ' c = CS ∷ c ∷ γ
```

<!--en-->
The alignment lemma `at` is the core of soundness. From the shape satisfaction at a member `c`, it recovers a truncated shape witness, splits the pair equation against the target decomposition, and applies `keyAt` to move the payload to the numbered decomposition. The elimination is legitimate because payloads are propositions.
<!--zh-->
对齐引理 `at` 是可靠性的核心。由成员 `c` 处的形状满足，它恢复一个截断的形状见证，把对等式与目标分解相对齐，再应用 `keyAt` 把载荷搬到带编号的分解处。由于载荷是命题，这次消去是合法的。
<!--ja-->
揃えの補題 `at` が健全性の中心である。要素 `c` での形の充足から、切り詰められた形の証人を取り出し、対の等式を目標の分解と揃え、`keyAt` を適用してペイロードを番号つきの分解へ移す。ペイロードが命題なので、この消去は正当である。
<!--/-->

```agda
    at : (c : S) → ⟨ fst c ∈ Cv ⟩ → (n : ℕ) (ar r : V ℓ) → fst c ≡ pr ar (pr (# n) r)
       → PayN n ar r
    at c c∈ n ar r e = rec₁ (isPropPayN Wv Cv n ar r)
      (λ { (ar' , F , p , (q∈ , (ec , key))) →
        let q = pr-inj (sym ec ∙ e)
```

<!--en-->
The arity equation is transported last, since the shape witness and the target decomposition may present the arity by different sets. The source of the payload is the shape reading of the chapter's hypothesis at the member.
<!--zh-->
元数等式最后运输，因为形状见证与目标分解可能用不同的集合呈现元数。载荷的来源，是章假设在该成员处的形状读取。
<!--ja-->
アリティの等式は最後に輸送される。形の証人と目標の分解が、アリティを異なる集合で提示するかもしれないからである。ペイロードの源は、その要素での、章の仮定の形の読み出しである。
<!--/-->

```agda
        in subst (λ a → PayN n a r) (q .fst) (keyAt Wv Cv ar' p key n r (q .snd)) })
      (SR.shape-out hs c c∈)
```

<!--en-->
The binary extractor converts a binary payload into the two subkeys of the same arity inside the domain. Its statement names the tag equation explicitly, because the payload was obtained at a numbered decomposition that must be aligned with the displayed pair.
<!--zh-->
二元提取器把二元载荷转换为域中同元数的两个子键。其陈述显式名指标签等式，因为载荷是在某个带编号的分解处取得的，必须与所展示的对对齐。
<!--ja-->
二項の抽出器は、二項のペイロードを、同じアリティの領域の中の二つの下位キーへ変換する。その主張はタグの等式を明示する。ペイロードが、示された対と揃えなければならない番号つきの分解で得られたものだからである。
<!--/-->

```agda
    binAt : (k : ℕ) → PayN k ≡ BinP → (c ar a b : S) → ⟨ fst c ∈ Cv ⟩
          → fst c ≡ pr (fst ar) (pr (# k) (pr (fst a) (fst b)))
          → ⟨ pr (fst ar) (fst a) ∈ Cv ⟩ × ⟨ pr (fst ar) (fst b) ∈ Cv ⟩
    binAt k eq c ar a b c∈ e = rec₁ (isProp× (snd (pr (fst ar) (fst a) ∈ Cv)) (snd (pr (fst ar) (fst b) ∈ Cv)))
      (λ { (a' , b' , (er , (ha , hb))) →
```

<!--en-->
Pair injectivity splits the equation into the two component equations, and each subkey is transported into place. The source of the payload is the alignment lemma applied at the member with the numbered tag.
<!--zh-->
配对单射性把等式拆成两个分量等式，每个子键被运输到位。载荷的来源，是对该成员施用带编号标签的对齐引理。
<!--ja-->
対の単射性が等式を二つの成分の等式に分け、それぞれの下位キーが所定の位置へ運ばれる。ペイロードの源は、番号つきのタグでその要素に適用した揃えの補題である。
<!--/-->

```agda
        let q = pr-inj er
        in subst (λ u → ⟨ pr (fst ar) u ∈ Cv ⟩) (sym (q .fst)) ha
         , subst (λ u → ⟨ pr (fst ar) u ∈ Cv ⟩) (sym (q .snd)) hb })
      (subst (λ P → P (fst ar) (pr (fst a) (fst b))) eq (at c c∈ k (fst ar) (pr (fst a) (fst b)) e))
```

<!--en-->
The bounded-quantifier extractor turns a bounded payload into membership of its body key at the successor arity. Its proof eliminates the truncated payload and transports the inner membership along the equation for the second component of the pair.
<!--zh-->
有界量词提取器把有界载荷转换为其主体键在后继元数处的隶属。证明消去截断的载荷，再沿有序对第二分量的等式运输内层隶属。
<!--ja-->
有界量化子の抽出補題は、有界ペイロードから、その本体キーが後続アリティで属することを導く。証明では、切り詰められたペイロードを除去し、対の第二成分についての等式に沿って内側の所属を輸送する。
<!--/-->

```agda
    bqAt : (k : ℕ) → PayN k ≡ BqP → (c ar a b : S) → ⟨ fst c ∈ Cv ⟩
         → fst c ≡ pr (fst ar) (pr (# k) (pr (fst a) (fst b)))
         → ⟨ pr (sucV (fst ar)) (fst b) ∈ Cv ⟩
    bqAt k eq c ar a b c∈ e = rec₁ (snd (pr (sucV (fst ar)) (fst b) ∈ Cv))
      (λ { (t , a' , (er , (ht , ha))) →
```

<!--en-->
Once the bounded payload has been aligned with the displayed nested pair, its body component is exactly a key at the successor arity. Transporting this membership along the component equation proves the desired conclusion.
<!--zh-->
有界载荷与所展示的嵌套有序对对齐后，其中的主体分量恰好是后继元数处的键。沿相应的分量等式运输这份隶属证明，便得到所需结论。
<!--ja-->
有界ペイロードを表示された入れ子の順序対に揃えると、その本体成分は後続アリティでのキーそのものである。対応する成分の等式に沿ってこの所属を輸送すれば、求める結論が得られる。
<!--/-->

```agda
        subst (λ u → ⟨ pr (sucV (fst ar)) u ∈ Cv ⟩) (sym (pr-inj er .snd)) ha })
      (subst (λ P → P (fst ar) (pr (fst a) (fst b))) eq (at c c∈ k (fst ar) (pr (fst a) (fst b)) e))
```

<!--en-->
These extraction lemmas give the downward closure required for recursion on codes. For each of the three binary connectives, membership of a composite key implies membership of both immediate subkeys at the same arity.
<!--zh-->
这些提取引理给出对码作递归时所需的向下闭包。对三个二元联结词中的每一个，复合键属于该域都蕴含它的两个直接子键在同一元数处也属于该域。
<!--ja-->
これらの抽出補題から、符号上の再帰に必要な下向き閉包が得られる。三つの二項結合子のそれぞれについて、複合キーが領域に属すれば、その二つの直接の下位キーも同じアリティで領域に属する。
<!--/-->

```agda
    hcl : (c : S) → ⟨ δ' c ⊨ closedAt zero ⟩
    hcl c =
        binSameClosed-in zero 2 (δ' c) (binAt 2 refl)
      , ( binSameClosed-in zero 3 (δ' c) (binAt 3 refl)
      , ( binSameClosed-in zero 4 (δ' c) (binAt 4 refl)
```

<!--en-->
The same conclusion holds for quantifiers with the expected change of arity. An unbounded or bounded quantifier key at arity `n` contains a body key at successor arity; the bounded cases additionally discard the bounding-term component after verifying the payload shape.
<!--zh-->
量词也满足相应的结论，但元数按预期发生变化。元数 `n` 处的无界或有界量词键，都包含一个后继元数处的主体键；有界情形在核对载荷形状后，还需略去其中的界词项分量。
<!--ja-->
量化子についても、アリティの変化を伴う同様の結論が成り立つ。アリティ `n` の非有界または有界量化子キーは、後続アリティでの本体キーを含む。有界の場合には、ペイロードの形を確認したあと、境界項の成分を取り除く。
<!--/-->

```agda
      , ( unSuccClosed-in zero 6 (δ' c) (λ c' ar a c'∈ e → at c' c'∈ 6 (fst ar) (fst a) e)
      , ( unSuccClosed-in zero 7 (δ' c) (λ c' ar a c'∈ e → at c' c'∈ 7 (fst ar) (fst a) e)
      , ( binSuccClosed-in zero 8 (δ' c) (bqAt 8 refl)
      ,   binSuccClosed-in zero 9 (δ' c) (bqAt 9 refl) )))))
```

<!--en-->
It remains to recover the full shape of an arbitrary member `c'` of the candidate domain. The shape description gives a truncated decomposition, the environment hypothesis identifies its arity with a natural-number numeral, and `Key` identifies its tag and payload. The result remains truncated throughout.
<!--zh-->
还需恢复候选域任意成员 `c'` 的完整形状。形状描述给出一个截断分解，环境假设把其中的元数识别为自然数数码，而 `Key` 再识别其标签与载荷。整个恢复过程的结果始终保留在截断之内。
<!--ja-->
あとは、候補領域の任意の要素 `c'` の完全な形を復元する。形の記述が切り詰められた分解を与え、環境についての仮定がそのアリティを自然数の数項と同定し、`Key` がタグとペイロードを同定する。復元結果は全体を通して切り詰められたままである。
<!--/-->

```agda
    wit : (c c' : S) → ⟨ fst c' ∈ Cv ⟩ → ∥ ShapeWit (sh 2 w) (δ' c) c' ∥₁
    wit c c' c'∈ = rec₁ squash₁
      (λ { (ar , F , p , (q∈ , (ec , key))) → rec₁ squash₁
        (λ { (k , r , (e' , pay)) →
          let qS = down (lookup E γ) (pr ar F) q∈
```

<!--en-->
The recovered data are represented inside the relevant sets: `qS` presents the environment entry, `arS` presents its arity, `pS` presents the coded payload, and `rS` presents the inner payload. Their equations compose to the key equation `ek`.
<!--zh-->
恢复出的数据分别由相关集合中的代表给出：`qS` 呈现环境条目，`arS` 呈现其元数，`pS` 呈现编码后的载荷，`rS` 呈现内层载荷。这些呈现等式复合成键等式 `ek`。
<!--ja-->
復元したデータは、関係する集合の内部の表示として与えられる。`qS` は環境の要素を、`arS` はそのアリティを、`pS` は符号化されたペイロードを、`rS` は内側のペイロードを表示する。これらの表示の等式を合成したものがキーの等式 `ek` である。
<!--/-->

```agda
              arS = fstS qS ar F refl
              pS = sndS c' ar p ec
              rS = sndS pS (# (toℕ k)) r e'
              ek : fst c' ≡ pr (fst arS) (pr (# (toℕ k)) (fst rS))
              ek = ec ∙ cong (pr ar) e'
```

<!--en-->
The lemma `fill` now analyzes the recovered tag. For each of the ten possible tags, it turns the corresponding payload condition into a witness for the appropriate branch of the shape formula.
<!--zh-->
引理 `fill` 接着分析恢复出的标签。对十种可能标签中的每一种，它都把相应的载荷条件转换成形状公式对应分支的见证。
<!--ja-->
補題 `fill` は、復元されたタグを場合分けする。十種類の各タグについて、対応するペイロード条件を、形の論理式の該当する分岐の証人へ変換する。
<!--/-->

```agda
          in fill k c' arS rS pay ek })
        key })
      (SR.shape-out hs c' c'∈)
      where
      env4 : (c' arS b a : S) → S ^ (6 + m)
```

<!--en-->
The auxiliary environment records two payload components together with the successor arity. It provides precisely the variables needed to interpret the branches for binary connectives and quantified formulas.
<!--zh-->
辅助环境记录两个载荷分量以及后继元数，从而提供解释二元联结词与量化公式各分支所需的变元。
<!--ja-->
補助環境は、二つのペイロード成分と後続アリティを記録する。これにより、二項結合子と量化された論理式の各分岐を解釈するための変数が揃う。
<!--/-->

```agda
      env4 c' arS b a = b ∷ a ∷ arS ∷ c' ∷ δ' c
```

<!--en-->
A binary payload merely asserts the existence of two components whose ordered pair is the displayed payload and whose keys belong to the domain. The helper `pairWit` converts precisely these data into the witness required by the corresponding branch of the shape formula.
<!--zh-->
二元载荷只断言存在两个分量：它们组成的有序对等于所展示的载荷，并且各自对应的键都属于该域。辅助引理 `pairWit` 恰好把这些数据转换成形状公式相应分支所要求的见证。
<!--ja-->
二項ペイロードが主張するのは、二つの成分が存在し、その順序対が表示されたペイロードに等しく、それぞれに対応するキーが領域に属することだけである。補助補題 `pairWit` は、これらのデータを形の論理式の対応する分岐が要求する証人へ変換する。
<!--/-->

```agda
      pairWit : (k : ℕ) (rel : Formula S (4 + (2 + m))) (c' arS rS : S)
              → fst c' ≡ pr (fst arS) (pr (# k) (fst rS))
              → (t u : V ℓ) → fst rS ≡ pr t u
              → ((tS uS : S) → fst tS ≡ t → fst uS ≡ u → ⟨ env4 c' arS uS tS ⊨ rel ⟩)
              → BinWit k rel (δ' c) c'
```

<!--en-->
Pair injectivity separates the payload equality into equations for its two components. Together with the arity presentation and the composite key equation, these equations place the two membership proofs in the four fields required by `BinWit`.
<!--zh-->
有序对编码的单射性把载荷等式拆成两个分量等式。它们与元数呈现及复合键等式一起，把两份隶属证明放入 `BinWit` 所要求的四个字段。
<!--ja-->
順序対符号化の単射性によって、ペイロードの等式は二つの成分の等式に分かれる。これらをアリティの表示と複合キーの等式に合わせると、二つの所属証明が `BinWit` の要求する四つの欄に収まる。
<!--/-->

```agda
      pairWit k rel c' arS rS ek t u er g =
        arS , (fstS rS t u er , (sndS rS t u er
        , ( ek ∙ cong (λ v → pr (fst arS) (pr (# k) v)) er
          , g (fstS rS t u er) (sndS rS t u er) refl refl )))
```

<!--en-->
For atomic formulas, both payload components must be legal term codes at the recorded arity. Applying `tmWit` to each component turns these two semantic conditions into the two conjuncts of `bothTm`.
<!--zh-->
对原子公式，载荷的两个分量都必须是在所记录元数处合法的词项码。分别对两个分量应用 `tmWit`，便把这两项语义条件转换成 `bothTm` 的两个合取项。
<!--ja-->
原子論理式では、ペイロードの二つの成分がともに、記録されたアリティで正しい項符号でなければならない。各成分に `tmWit` を適用すると、この二つの意味的条件が `bothTm` の二つの連言肢へ変わる。
<!--/-->

```agda
      both : (c' arS : S) (t u : V ℓ) → IsTmV Wv t (fst arS) → IsTmV Wv u (fst arS)
           → (tS uS : S) → fst tS ≡ t → fst uS ≡ u → ⟨ env4 c' arS uS tS ⊨ bothTm (sh 2 w) ⟩
      both c' arS t u ht hu tS uS qt qu =
          tmWit (suc zero) (suc (suc zero)) (sh 4 (sh 2 w)) (env4 c' arS uS tS)
            (subst (λ x → IsTmV Wv x (fst arS)) (sym qt) ht)
```

<!--en-->
The second component is treated identically, so the two recovered term witnesses establish the conjunction required for an atomic payload.
<!--zh-->
第二分量以同样方式处理，于是恢复出的两个词项见证共同证明原子载荷所要求的合取。
<!--ja-->
第二成分も同じように扱われ、復元された二つの項の証人が、原子ペイロードに必要な連言を証明する。
<!--/-->

```agda
        , tmWit zero (suc (suc zero)) (sh 4 (sh 2 w)) (env4 c' arS uS tS)
            (subst (λ x → IsTmV Wv x (fst arS)) (sym qu) hu)
```

<!--en-->
A bounded quantifier needs only its bounding term to be legal at the current arity. The corresponding helper therefore applies `tmWit` to the first payload component alone.
<!--zh-->
有界量词只要求界词项在当前元数处合法，因此相应的辅助引理只对载荷的第一分量应用 `tmWit`。
<!--ja-->
有界量化子で必要なのは、境界項が現在のアリティで正しいことだけである。そのため、対応する補助補題はペイロードの第一成分だけに `tmWit` を適用する。
<!--/-->

```agda
      first : (c' arS : S) (t u : V ℓ) → IsTmV Wv t (fst arS)
            → (tS uS : S) → fst tS ≡ t → fst uS ≡ u → ⟨ env4 c' arS uS tS ⊨ fstTm (sh 2 w) ⟩
      first c' arS t u ht tS uS qt qu =
        tmWit (suc zero) (suc (suc zero)) (sh 4 (sh 2 w)) (env4 c' arS uS tS)
          (subst (λ x → IsTmV Wv x (fst arS)) (sym qt) ht)
```

<!--en-->
Tag zero denotes membership. Its payload contains two legal term codes, so the binary helper supplies the leftmost branch of the shape formula with the recovered term evidence.
<!--zh-->
标签零表示隶属。其载荷包含两个合法词项码，因此二元辅助引理利用恢复出的词项证明，给出形状公式最左侧分支的见证。
<!--ja-->
タグ 0 は所属を表す。そのペイロードには二つの正しい項符号が含まれるので、二項の補助補題が、復元した項の証拠を用いて形の論理式の最も左の分岐を証明する。
<!--/-->

```agda
      fill : (k : Fin 10) (c' arS rS : S) → PayN (toℕ k) (fst arS) (fst rS)
           → fst c' ≡ pr (fst arS) (pr (# (toℕ k)) (fst rS))
           → ∥ ShapeWit (sh 2 w) (δ' c) c' ∥₁
      fill zero c' arS rS pay ek = map₁
        (λ { (t , u , (er , (ht , hu))) → inl (pairWit 0 (bothTm (sh 2 w)) c' arS rS ek t u er (both c' arS t u ht hu)) })
```

<!--en-->
Tag one denotes equality and is handled by the same two-term argument in the next branch. Tag two begins the binary connectives; there the same ordered-pair analysis is used, but the recovered components are subformula keys rather than term codes.
<!--zh-->
标签一表示相等，在下一分支中由同样的双词项论证处理。标签二开始表示二元联结词；此时仍采用同样的有序对分析，但恢复出的两个分量是子公式键，而不是词项码。
<!--ja-->
タグ 1 は等号を表し、次の分岐で同じ二項の議論によって扱われる。タグ 2 からは二項結合子が始まる。そこでも同じ順序対の分析を用いるが、復元される二つの成分は項符号ではなく、下位論理式のキーである。
<!--/-->

```agda
        pay
      fill (suc zero) c' arS rS pay ek = map₁
        (λ { (t , u , (er , (ht , hu))) → inr (inl (pairWit 1 (bothTm (sh 2 w)) c' arS rS ek t u er (both c' arS t u ht hu))) })
        pay
      fill (suc (suc zero)) c' arS rS pay ek = map₁
```

<!--en-->
The fill cases for the three binary connectives are uniform: the payload names two sub-codes `a` and `b`, and the witness is a `pairWit` at the label, with no bounding term and a vacuous payload condition, since the binary clauses impose none. The nesting depth of the disjunction tags the label's position in the ten-way sum.
<!--zh-->
三个二元联结词的填充情形是一致的：载荷点名两个子码 `a` 与 `b`，见证是处在该标签位置上的 `pairWit`，无界限项、载荷条件空洞，因为二元子句本无额外要求。析取的嵌套深度标出该标签在十路和中的位置。
<!--ja-->
三つの二項結合子の充足の場合は一様である。ペイロードは二つの下位コード `a` と `b` を名指し、証人はそのタグの位置での `pairWit` であり、境界の項はなくペイロードの条件も空である。二項の節には余分な要求がないからである。選言の入れ子の深さが、十通りの和の中でのタグの位置を示す。
<!--/-->

```agda
        (λ { (a , b , (er , _)) → inr (inr (inl (pairWit 2 noneB c' arS rS ek a b er (λ _ _ _ _ b → b)))) })
        pay
      fill (suc (suc (suc zero))) c' arS rS pay ek = map₁
        (λ { (a , b , (er , _)) → inr (inr (inr (inl (pairWit 3 noneB c' arS rS ek a b er (λ _ _ _ _ b → b))))) })
        pay
```

<!--en-->
Implication occupies the fourth binary tag and follows the same pattern. Falsity is different: its payload is the numeral zero, so the witness consists of the arity and payload equations, with `numeralL-fst` supplying the equation for the underlying set of that numeral.
<!--zh-->
蕴涵占据第四个二元标签，仍沿用同一构造。假则有所不同：它的载荷是数码零，因此见证只需给出元数等式与载荷等式，其中 `numeralL-fst` 提供数码底层集合所需的等式。
<!--ja-->
含意は第四の二項タグを占め、同じ構成に従う。偽はこれと異なり、ペイロードが数項の零である。そのため証人に必要なのはアリティとペイロードの等式だけであり、`numeralL-fst` が数項の基底集合について必要な等式を与える。
<!--/-->

```agda
      fill (suc (suc (suc (suc zero)))) c' arS rS pay ek = map₁
        (λ { (a , b , (er , _)) → inr (inr (inr (inr (inl (pairWit 4 noneB c' arS rS ek a b er (λ _ _ _ _ b → b)))))) })
        pay
      fill (suc (suc (suc (suc (suc zero))))) c' arS rS pay ek =
        ∣ inr (inr (inr (inr (inr (inl (arS , (rS , (ek , pay ∙ sym (numeralL-fst 0))))))))) ∣₁
```

<!--en-->
The two unbounded quantifiers are again uniform: their payload is the sub-key at the successor arity, and the witness condition is the identity on that data, since the quantifier clauses add no term requirements. Only the tag position distinguishes existence from universality.
<!--zh-->
两个无界量词同样一致：其载荷是后继元数处的子键，见证条件是该数据上的恒等，因为量词子句不添加词项要求。只有标签位置区分存在与全称。
<!--ja-->
二つの非有界の量化子もやはり一様である。ペイロードは後続のアリティの下位の鍵であり、証人の条件はそのデータ上の恒等である。量化子の節が項の要求を加えることはないからである。存在と全称を区別するのはタグの位置だけである。
<!--/-->

```agda
      fill (suc (suc (suc (suc (suc (suc zero)))))) c' arS rS pay ek =
        ∣ inr (inr (inr (inr (inr (inr (inl (arS , (rS , (ek , (λ b → b)))))))))) ∣₁
      fill (suc (suc (suc (suc (suc (suc (suc zero))))))) c' arS rS pay ek =
        ∣ inr (inr (inr (inr (inr (inr (inr (inl (arS , (rS , (ek , (λ b → b))))))))))) ∣₁
      fill (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) c' arS rS pay ek = map₁
```

<!--en-->
The bounded universal adds the term layer: its payload contains a legal bounding term `t` besides the member `a`, and the witness uses the one-term reader `first` for that term, with `fstTm` naming the term slot of the bounded-key shape.
<!--zh-->
有界全称添加了词项层：其载荷除成员 `a` 外还包含合法的界限词项 `t`，见证对该词项使用单词项读式 `first`，并以 `fstTm` 指名有界键形状中的词项槽位。
<!--ja-->
有界の全称は項の層を加える。ペイロードには要素 `a` のほかに合法な境界の項 `t` が含まれ、証人はその項のために単項の読み `first` を使い、有界の鍵の形の項のスロットを `fstTm` が名指す。
<!--/-->

```agda
        (λ { (t , a , (er , (ht , _))) → inr (inr (inr (inr (inr (inr (inr (inr (inl
          (pairWit 8 (fstTm (sh 2 w)) c' arS rS ek t a er (first c' arS t a ht)))))))))) })
        pay
      fill (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))) c' arS rS pay ek = map₁
        (λ { (t , a , (er , (ht , _))) → inr (inr (inr (inr (inr (inr (inr (inr (inr
```

<!--en-->
The bounded existential has the same payload shape as the bounded universal, but occupies the final tag. The ten cases now cover exactly the constructors of formulas: four atomic forms, three binary connectives, falsity, and the bounded and unbounded quantifiers.
<!--zh-->
有界存在与有界全称具有相同的载荷形状，但占据最后一个标签。至此，十种情形恰好覆盖公式的全部构造子：四种原子公式、三个二元联结词、假，以及有界和无界量词。
<!--ja-->
有界存在は有界全称と同じペイロードの形をもつが、最後のタグを占める。これで十通りの場合が、四つの原子式、三つの二項結合子、偽、有界量化子と非有界量化子という論理式の構成子をちょうど覆う。
<!--/-->

```agda
          (pairWit 9 (fstTm (sh 2 w)) c' arS rS ek t a er (first c' arS t a ht)))))))))) })
        pay
```

<!--en-->
The shape-soundness lemma now packages the construction member by member. For each `c` in the code set, `shaped-in` turns the witness just built into satisfaction of `shapedAt`; these are precisely the local shape facts needed when a code is decoded.
<!--zh-->
形状可靠性引理把上述构造逐成员汇集起来。对于码集中的每个 `c`，`shaped-in` 将刚构造的见证转化为 `shapedAt` 的满足证明；解码某个码时，所需的正是这种局部形状事实。
<!--ja-->
形の健全性の補題は、以上の構成を要素ごとにまとめる。符号集合の各要素 `c` に対して、`shaped-in` は先ほど構成した証人を `shapedAt` の充足証明へ変換する。符号を復号するときに必要なのは、まさにこの局所的な形の事実である。
<!--/-->

```agda
    hsh : (c : S) → ⟨ δ' c ⊨ shapedAt zero (sh 2 w) ⟩
    hsh c = shaped-in zero (sh 2 w) (δ' c) (wit c)
```

<!--en-->
The closure clause is proved for all seven non-atomic constructors at once. The three binary connectives are discharged by `binAt`, which reads the label's payload and extracts the two sub-codes' memberships through the injectivity of the pair coding.
<!--zh-->
闭包子句对全部七个非原子构造子一次证得。三个二元联结词由 `binAt` 处理：它读取该标签的载荷，并经配对编码的单射性提取两个子码的隶属。
<!--ja-->
閉包の節は、非原子の七つの構成子すべてに対して一度に証明される。三つの二項結合子は `binAt` で処理される。タグのペイロードを読み、対の符号化の単射性を通して二つの下位コードの所属を取り出すのである。
<!--/-->

```agda
  closed : ⟨ γ ⊨ closedAt C ⟩
  closed =
      binSameClosed-in C 2 γ (binAt 2 refl)
    , ( binSameClosed-in C 3 γ (binAt 3 refl)
    , ( binSameClosed-in C 4 γ (binAt 4 refl)
```

<!--en-->
The two unbounded quantifiers are discharged by quoting the reader at the successor arity, and the two bounded quantifiers by `bqAt`, which additionally reads off the bounding term. Together the seven entries certify `closedAt C` in the ambient environment.
<!--zh-->
两个无界量词通过在后继元数处引用读式兑现；两个有界量词由 `bqAt` 兑现，后者还额外读出界限词项。七条合起来在环境中认证了 `closedAt C`。
<!--ja-->
二つの非有界の量化子は後続のアリティで読みを引用して処理され、二つの有界の量化子は `bqAt` が境界の項も読み取って処理する。七つの項目が合わさって、周囲の環境で `closedAt C` が認められる。
<!--/-->

```agda
    , ( unSuccClosed-in C 6 γ (λ c' ar a c'∈ e → at c' c'∈ 6 (fst ar) (fst a) e)
    , ( unSuccClosed-in C 7 γ (λ c' ar a c'∈ e → at c' c'∈ 7 (fst ar) (fst a) e)
    , ( binSuccClosed-in C 8 γ (bqAt 8 refl)
    ,   binSuccClosed-in C 9 γ (bqAt 9 refl) )))))
```

<!--en-->
The decoding theorem is the chapter's first main result. Every member `c` of a code set satisfying the description yields, under propositional truncation, a natural number `k` and a formula `ψ` of arity `k`, with `fst c ≡ fst (keyS W ψ)`. Thus the theorem asserts existence of a matching formula key, without choosing a decoder or asserting uniqueness.
<!--zh-->
解码定理是本章的第一个主要结果。对于满足描述的码集中的每个成员 `c`，都可在命题截断下得到一个自然数 `k` 和一条元数为 `k` 的公式 `ψ`，并有 `fst c ≡ fst (keyS W ψ)`。因此，定理只断言相应公式键的存在，并未选定解码函数，也未断言唯一性。
<!--ja-->
復号定理は本章の最初の主要結果である。記述を満たす符号集合の各要素 `c` から、命題的切り詰めのもとで、自然数 `k`、アリティ `k` の論理式 `ψ`、および `fst c ≡ fst (keyS W ψ)` が得られる。したがって、この定理が主張するのは対応する論理式キーの存在であり、復号関数の選択や一意性ではない。
<!--/-->

```agda
  key-out : (c : S) → ⟨ fst c ∈ Cv ⟩
          → ∥ Σ[ k ∈ ℕ ] Σ[ ψ ∈ Formula ⟪ fst W ⟫ k ] (fst c ≡ fst (keyS W ψ)) ∥₁
  key-out c c∈ = rec₁ squash₁
    (λ { (ar , F , p , (q∈ , (ec , key))) → rec₁ squash₁
      (λ { (k , qk) → map₁ (λ { (ψ , e) → k , ψ , e })
```

<!--en-->
Start with the truncated shape data of `c`: an arity entry, a table, and a payload satisfying the appropriate key condition. The arity hypothesis identifies the recorded arity with a numeral `# k`. Together with the downward closure obtained above, `witnessAt-out` then recovers, still under truncation, a formula of arity `k` whose key has underlying set `fst c`.
<!--zh-->
先从 `c` 的截断形状数据中取得元数条目、表和满足相应键条件的载荷。元数假设把所记录的元数等同于某个数码 `# k`。再结合前面得到的向下封闭性，`witnessAt-out` 便在仍受截断的意义下恢复一条元数为 `k` 的公式，其键的底层集合就是 `fst c`。
<!--ja-->
まず `c` の切り詰められた形のデータから、アリティの項目、表、そして対応するキー条件を満たすペイロードを得る。アリティについての仮定により、記録されたアリティはある数項 `# k` と同一視される。これを先に得た下向き閉性と合わせると、`witnessAt-out` は、なお切り詰めのもとで、キーの基底集合が `fst c` であるアリティ `k` の論理式を復元する。
<!--/-->

```agda
        (witnessAt-out W (suc w) zero (c ∷ γ) qw
          ∣ CS , (c∈ , (hcl c , hsh c)) ∣₁
          k (sndS c ar p ec) (ec ∙ cong (λ a → pr a p) qk)) })
      (arity (fstS (down (lookup E γ) (pr ar F) q∈) ar F refl)
             (sndS (down (lookup E γ) (pr ar F) q∈) ar F refl) q∈) })
```

<!--en-->
The required shape data is precisely the result of applying `shape-out` to the assumed shape clause and the membership proof for `c`.
<!--zh-->
所需的形状数据，正是将 `shape-out` 用于已知的形状子句和 `c` 的隶属证明所得的结果。
<!--ja-->
必要な形のデータは、仮定した形の節と `c` の所属証明に `shape-out` を適用して得られるものにほかならない。
<!--/-->

```agda
    (SR.shape-out hs c c∈)
```
</div>
</details>

<!--en-->
## Completeness: encoding every formula
<!--zh-->
## 完备性：编码每条公式
<!--ja-->
## 完全性：各論理式の符号化
<!--/-->

<!--en-->
Two arithmetic facts about finite indices enter here: converting a natural number below `n` into a valid index of `Fin n`, and round-tripping an index through its own numeral.
<!--zh-->
此处引入两条关于有穷索引的算术事实：把低于 `n` 的自然数转换为 `Fin n` 的合法索引，以及把索引经其自身数码往返。
<!--ja-->
ここで、有限の添字に関する二つの算術の事実が入る。`n` 未満の自然数を `Fin n` の正しい添字へ変換することと、添字をみずからの数項を通して往復させることである。
<!--/-->

```agda
open import Cubical.Data.FinData.Properties using ( fromℕ'; toFromId' )
```

<!--en-->
For completeness, assume a code-domain slot `C`, an alphabet slot `w`, and an arity-tower slot `E`, together with the correct tags. Assume also that every canonical tower entry belongs to `E` and that the upward closure clause holds. The aim is to prove that the key of every formula over the alphabet belongs to `C`.
<!--zh-->
为证明完备性，固定码域槽位 `C`、字母表槽位 `w` 与元数塔槽位 `E`，并假设十个标签解释正确。再假设每个典范塔条目都属于 `E`，且向上闭包子句成立；目标是证明字母表上每条公式的键都属于 `C`。
<!--ja-->
完全性を示すため、符号領域のスロット `C`、アルファベットのスロット `w`、アリティ塔のスロット `E` を固定し、十個のタグが正しく解釈されると仮定する。さらに、すべての正準な塔の要素が `E` に属し、上向きの閉包条項が成り立つと仮定する。目標は、アルファベット上のすべての論理式のキーが `C` に属することである。
<!--/-->

<details open class="submodule-fold">
<summary class="submodule-fold-heading">
```agda
module CodesComplete {m : ℕ} (C w E : Fin m) (N : Fin 10 → Fin m) (γ : S ^ m) (W : S)
  (qw : fst (lookup w γ) ≡ fst W) (tg : Tags γ N)
  (arity∈ : (n : ℕ) → ⟨ pr (# n) (fst (envSet W n)) ∈ fst (lookup E γ) ⟩)
  (hc : ⟨ γ ⊨ closeAt C w E N ⟩) where
```
</summary>
<div class="submodule-fold-content">

```agda
  open Alphabet W
```

<!--en-->
Write `Cv` for the underlying set named by the code-domain slot. Completeness will place every genuine formula key in this one set.
<!--zh-->
以 `Cv` 表示码域槽位所指的底层集合。完备性要证明每一条真实公式的键都属于这个集合。
<!--ja-->
符号領域のスロットが指す基底集合を `Cv` と書く。完全性では、すべての真正な論理式キーがこの集合に属することを示す。
<!--/-->

```agda
  private
    Cv = fst (lookup C γ)
```

<!--en-->
Every constant of the alphabet belongs to the alphabet slot: the identification of the two carriers is what transports the embedding's memberships into the environment.
<!--zh-->
字母表的每个常元都属于字母表槽位：两个载体的等同，正是把嵌入的隶属传输进环境的依据。
<!--ja-->
アルファベットのすべての定数はアルファベットのスロットに属する。二つの台の同一視こそが、埋め込みの所属を環境の中へ輸送する根拠である。
<!--/-->

```agda
    ι∈w : (q : Ab) → ⟨ ι q ∈ fst (lookup w γ) ⟩
    ι∈w q = subst (λ u → ⟨ ι q ∈ u ⟩) (sym qw) (ι∈ q)
```

<!--en-->
An alphabet entry is represented internally by an element of the slot `w`. The operation `down` packages its ambient representative together with the membership proof established above, producing the corresponding element `ιS q : S`.
<!--zh-->
每个字母表条目都由槽位 `w` 的一个内部元素表示。`down` 把它的外围表示与上面得到的隶属证明打包起来，得到相应的元素 `ιS q : S`。
<!--ja-->
各アルファベット要素は、スロット `w` の内部要素によって表される。`down` はその外部表現と上で得た所属証明を組にし、対応する要素 `ιS q : S` を作る。
<!--/-->

```agda
    ιS : Ab → S
    ιS q = down (lookup w γ) (ι q) (ι∈w q)
```

<!--en-->
The canonical tower entry at arity `n`, the pair of the numeral `n` with the environment set of length `n`, is lowered likewise, so the closure clauses can be quoted at it.
<!--zh-->
元数 `n` 处的典范塔条目是数码 `n` 与长度 `n` 环境集组成的对。它也照此下降，使闭包子句能够在它那里引用。
<!--ja-->
アリティ `n` の正準な塔の項目、すなわち数項 `n` と長さ `n` の環境の集合の対も同じように降ろされ、閉包の節をそこで引用できるようにする。
<!--/-->

```agda
    qS : ℕ → S
    qS n = down (lookup E γ) (pr (# n) (fst (envSet W n))) (arity∈ n)
```

<!--en-->
The four-slot context assembles the lowered tower entry, the numeral, their pairing container, and the lowered entry again, matching the frame the closure clauses expect.
<!--zh-->
四槽位语境装配被降下的塔条目、数码、它们的配对容器以及再次出现的被降条目，与闭包子句所期待的框架一致。
<!--ja-->
四スロットの文脈は、降ろされた塔の項目、数項、それらの対の容器、そして再び降ろされた項目を組み立て、閉包の節が期待する枠組みに一致させる。
<!--/-->

```agda
    δ4 : ℕ → S ^ (4 + m)
    δ4 n = envSet W n ∷ nn n ∷ container (qS n) (nn n) (envSet W n) refl .fst ∷ qS n ∷ γ
```

<!--en-->
The full closure clause is satisfied at that context, because the hypothesis says the closure clause holds at every canonical tower entry.
<!--zh-->
完整的闭包子句在该语境处成立，因为假设说：闭包子句在每个典范塔条目处都成立。
<!--ja-->
完全な閉包の節はこの文脈で成り立つ。仮定が、閉包の節がすべての正準な塔の項目で成り立つと言っているからである。
<!--/-->

```agda
    frame : (n : ℕ) → ⟨ δ4 n ⊨ Close.all C w N ⟩
    frame n = useBoth i0 (qS n ∷ γ) (nn n) (envSet W n) refl (Close.all C w N) (hc (qS n) (arity∈ n))
```

<!--en-->
The closure reader is reopened at each numeral's own context, so every arity gets its own copy of the eighteen clauses.
<!--zh-->
闭包读式在每个数码自己的语境处重新打开，使每个元数都拥有十八条子句的一份副本。
<!--ja-->
閉包の読みは、それぞれの数項みずからの文脈で再び開かれ、すべてのアリティが十八の節のコピーを得る。
<!--/-->

```agda
    module CR (n : ℕ) = CloseRead C w N (δ4 n) tg
```

<!--en-->
Every variable index below `n` names a numeral below the numeral of `n`: the monotonicity of the von Neumann numerals is what lets a variable's index be recognized as a member of its arity's numeral.
<!--zh-->
低于 `n` 的每个变元索引都指名低于 `n` 之数码的一个数码：冯·诺伊曼数码的单调性使变元索引能被认作其元数数码的成员。
<!--ja-->
`n` 未満のすべての変数の添字は、`n` の数項より下の数項を名指す。フォン・ノイマンの数項の単調性によって、変数の添字がそのアリティの数項の要素として認められるのである。
<!--/-->

```agda
    var∈ : (n : ℕ) (i : Fin n) → ⟨ # (toℕ i) ∈ # n ⟩
    var∈ n i = #mono (toℕ i) n (toℕ<n i)
```

<!--en-->
The structural induction begins with the four possible membership atoms. In each case, the atomic closure clause is instantiated at the fixed arity `n`. Its two term entries come independently from an alphabet constant or an arity variable, and the preceding lemmas provide the corresponding membership proofs.
<!--zh-->
结构归纳从成员关系原子的四种情形开始。每种情形都在固定元数 `n` 处实例化原子闭包子句；左右两个词项各自可以来自字母表常元或该元数下的变元，而前面的引理恰好提供相应的隶属证明。
<!--ja-->
構造帰納法は、所属原子式の四つの場合から始まる。各場合で、原子閉包条項を固定したアリティ `n` において具体化する。左右の項はそれぞれアルファベットの定数またはそのアリティの変数であり、直前の補題が対応する所属証明を与える。
<!--/-->

```agda
  key-in : ∀ {n} (ψ : Formula Ab n) → ⟨ fst (keyS W ψ) ∈ Cv ⟩
  key-in {n} (con x ∈̇ con y) = CR.atomClose-out n f0 f0 f0 (sh 4 w) (sh 5 w) (frame n .fst) (ιS x) (ιS y) (ι∈w x) (ι∈w y)
  key-in {n} (con x ∈̇ var j) = CR.atomClose-out n f0 f0 f1 (sh 4 w) i2 (frame n .snd .fst) (ιS x) (nn (toℕ j)) (ι∈w x) (var∈ n j)
  key-in {n} (var i ∈̇ con y) = CR.atomClose-out n f0 f1 f0 i1 (sh 5 w) (frame n .snd .snd .fst) (nn (toℕ i)) (ιS y) (var∈ n i) (ι∈w y)
  key-in {n} (var i ∈̇ var j) = CR.atomClose-out n f0 f1 f1 i1 i2 (frame n .snd .snd .snd .fst) (nn (toℕ i)) (nn (toℕ j)) (var∈ n i) (var∈ n j)
```

<!--en-->
The four equality atoms follow the same argument with the equality tag. For conjunction, the induction hypotheses first place both subformula keys in `C`; the binary closure clause then places the paired conjunction key in `C` as well.
<!--zh-->
四种相等原子公式以相等标签重复同一论证。对于合取，归纳假设先把两条子公式的键放入 `C`，二元闭包子句再把由它们配成的合取键放入 `C`。
<!--ja-->
四つの等号原子式についても、等号のタグを用いて同じ議論を行う。連言では、まず帰納法の仮定によって二つの部分式のキーを `C` に入れ、次に二項閉包の節によって、それらを対にした連言のキーも `C` に入れる。
<!--/-->

```agda
  key-in {n} (con x ≐ con y) = CR.atomClose-out n f1 f0 f0 (sh 4 w) (sh 5 w) (frame n .snd .snd .snd .snd .fst) (ιS x) (ιS y) (ι∈w x) (ι∈w y)
  key-in {n} (con x ≐ var j) = CR.atomClose-out n f1 f0 f1 (sh 4 w) i2 (frame n .snd .snd .snd .snd .snd .fst) (ιS x) (nn (toℕ j)) (ι∈w x) (var∈ n j)
  key-in {n} (var i ≐ con y) = CR.atomClose-out n f1 f1 f0 i1 (sh 5 w) (frame n .snd .snd .snd .snd .snd .snd .fst) (nn (toℕ i)) (ιS y) (var∈ n i) (ι∈w y)
  key-in {n} (var i ≐ var j) = CR.atomClose-out n f1 f1 f1 i1 i2 (frame n .snd .snd .snd .snd .snd .snd .snd .fst) (nn (toℕ i)) (nn (toℕ j)) (var∈ n i) (var∈ n j)
  key-in {n} (a ∧̇ b) = CR.binClose-out n f2 (frame n .snd .snd .snd .snd .snd .snd .snd .snd .fst) (keyS W a) (keyS W b) (codeS W a) (codeS W b) (key-in a) (key-in b) refl refl
```

<!--en-->
Disjunction and implication use the same binary step at their respective tags, while falsity enters through the constant closure clause with payload zero. For either unbounded quantifier, the induction hypothesis concerns its body at arity `suc n`; the quantifier closure clause turns that body key into a key at arity `n`.
<!--zh-->
析取和蕴涵分别在各自的标签处采用同一个二元步骤，假则以零为载荷，经常量闭包子句进入 `C`。对于两种无界量词，归纳假设作用于元数为 `suc n` 的量词体；量词闭包子句再由量词体的键生成元数为 `n` 的键。
<!--ja-->
選言と含意は、それぞれのタグで同じ二項の段階を用い、偽は零をペイロードとして定数閉包の節から `C` に入る。二つの非有界量化子では、帰納法の仮定をアリティ `suc n` の本体に用い、量化子閉包の節によってその本体のキーからアリティ `n` のキーを作る。
<!--/-->

```agda
  key-in {n} (a ∨̇ b) = CR.binClose-out n f3 (frame n .snd .snd .snd .snd .snd .snd .snd .snd .snd .fst) (keyS W a) (keyS W b) (codeS W a) (codeS W b) (key-in a) (key-in b) refl refl
  key-in {n} (a ⇒̇ b) = CR.binClose-out n f4 (frame n .snd .snd .snd .snd .snd .snd .snd .snd .snd .snd .fst) (keyS W a) (keyS W b) (codeS W a) (codeS W b) (key-in a) (key-in b) refl refl
  key-in {n} ⊥̇ = CR.conClose-out n f5 (frame n .snd .snd .snd .snd .snd .snd .snd .snd .snd .snd .snd .fst)
  key-in {n} (∃̇ a) = CR.quClose-out n f6 (frame n .snd .snd .snd .snd .snd .snd .snd .snd .snd .snd .snd .snd .fst) (keyS W a) (nn (suc n)) (codeS W a) (key-in a) refl refl
  key-in {n} (∀̇ a) = CR.quClose-out n f7 (frame n .snd .snd .snd .snd .snd .snd .snd .snd .snd .snd .snd .snd .snd .fst) (keyS W a) (nn (suc n)) (codeS W a) (key-in a) refl refl
```

<!--en-->
The bounded universal has two closure arguments: the sub-key at the successor arity and the legal bounding term at the current arity. When the bound is a constant, the term entry comes from the alphabet embedding; when it is a variable, from the numeral membership.
<!--zh-->
有界全称有两条闭包论证：后继元数处的子键，以及当前元数处的合法界限词项。界限为常元时，词项条目来自字母表嵌入；界限为变元时，来自数码隶属。
<!--ja-->
有界の全称には二つの閉包の引数がある。後続のアリティの下位の鍵と、現在のアリティの合法な境界の項である。境界が定数のとき項の項目はアルファベットの埋め込みから、変数のときは数項の所属から来る。
<!--/-->

```agda
  key-in {n} (∀̇∈ (con x) a) =
    CR.bqClose-out n f8 f0 (sh 8 w) (frame n .snd .snd .snd .snd .snd .snd .snd .snd .snd .snd .snd .snd .snd .snd .fst) (keyS W a) (nn (suc n)) (codeS W a) (key-in a) refl refl (ιS x) (ι∈w x)
  key-in {n} (∀̇∈ (var i) a) =
    CR.bqClose-out n f8 f1 i5 (frame n .snd .snd .snd .snd .snd .snd .snd .snd .snd .snd .snd .snd .snd .snd .snd .fst) (keyS W a) (nn (suc n)) (codeS W a) (key-in a) refl refl (nn (toℕ i)) (var∈ n i)
  key-in {n} (∃̇∈ (con x) a) =
```

<!--en-->
The bounded existential repeats the same two arguments at its own tag, completing the structural induction: every formula of every arity has its key in the closed domain.
<!--zh-->
有界存在在其自身标签处重复同样两条论证，完成结构归纳：每个元数的每条公式，其键都在封闭域中。
<!--ja-->
有界の存在量化がみずからのタグで同じ二つの引数を繰り返し、構造的帰納を完成させる。すべてのアリティのすべての論理式の鍵が、閉じた定義域の中にあるのである。
<!--/-->

```agda
    CR.bqClose-out n f9 f0 (sh 8 w) (frame n .snd .snd .snd .snd .snd .snd .snd .snd .snd .snd .snd .snd .snd .snd .snd .snd .fst) (keyS W a) (nn (suc n)) (codeS W a) (key-in a) refl refl (ιS x) (ι∈w x)
  key-in {n} (∃̇∈ (var i) a) =
    CR.bqClose-out n f9 f1 i5 (frame n .snd .snd .snd .snd .snd .snd .snd .snd .snd .snd .snd .snd .snd .snd .snd .snd .snd ) (keyS W a) (nn (suc n)) (codeS W a) (key-in a) refl refl (nn (toℕ i)) (var∈ n i)
```
</div>
</details>

<!--en-->
## The canonical closed code domain
<!--zh-->
## 典范的封闭码定义域
<!--ja-->
## 正準な閉じた符号の定義域
<!--/-->

<!--en-->
It remains to show that the canonical domain really satisfies the description. Take the code slot to denote `AllCodes W` and the arity slot to denote the environment tower over `W`; the equations `qC` and `qE` record these two identifications.
<!--zh-->
最后还要证明典范码域确实满足这份描述。令码槽位表示 `AllCodes W`，令元数槽位表示 `W` 上的环境塔；等式 `qC` 与 `qE` 分别记录这两个等同。
<!--ja-->
最後に、正準な符号領域が実際にこの記述を満たすことを示す。符号スロットには `AllCodes W` を、アリティのスロットには `W` 上の環境塔を表させ、等式 `qC` と `qE` でそれぞれの同一視を記録する。
<!--/-->

<details open class="submodule-fold">
<summary class="submodule-fold-heading">
```agda
module CodesHolds {m : ℕ} (C w E : Fin m) (N : Fin 10 → Fin m) (γ : S ^ m) (W : S)
  (qw : fst (lookup w γ) ≡ fst W) (qC : fst (lookup C γ) ≡ fst (AllCodes W))
  (qE : fst (lookup E γ) ≡ fst (Tower.tower W)) (tg : Tags γ N) where
```
</summary>
<div class="submodule-fold-content">

```agda
  open Alphabet W
  private
```

<!--en-->
Write `Cv`, `Wv`, and `Ev` for the underlying sets named by the code-domain, alphabet, and arity-tower slots. These names keep the three roles separate: formula keys are tested for membership in `Cv`, constant representatives in `Wv`, and canonical arity entries in `Ev`.
<!--zh-->
分别以 `Cv`、`Wv` 和 `Ev` 表示码域、字母表与元数塔槽位所指的底层集合。这三个名称区分了不同职责：公式键在 `Cv` 中检验，常元的表示在 `Wv` 中检验，典范元数条目则在 `Ev` 中检验。
<!--ja-->
符号領域、アルファベット、アリティ塔の各スロットが指す基底集合を、それぞれ `Cv`、`Wv`、`Ev` と書く。三つの名前は役割の違いを明確にする。論理式キーの所属は `Cv` で、定数の表現は `Wv` で、正準なアリティ要素は `Ev` で調べる。
<!--/-->

```agda
    Cv = fst (lookup C γ)
    Wv = fst (lookup w γ)
    Ev = fst (lookup E γ)
    open CodesSem Wv Cv
```

<!--en-->
Suppose a set `Wv′` contains the representative of every alphabet entry. Then every term has a legal code over `Wv′`. A constant uses the supplied membership proof for its representative; a variable uses the fact that the numeral of its index belongs to the numeral of the arity. The result is propositionally truncated because term legality is used only as a property of the code.
<!--zh-->
假设集合 `Wv′` 含有每个字母表条目的表示，那么每个词项在 `Wv′` 上都有合法编码。常元使用其表示的给定隶属证明，变元使用索引数码属于元数数码这一事实。所得见证经过命题截断，因为这里仅把词项合法性当作编码的一项性质使用。
<!--ja-->
集合 `Wv′` がすべてのアルファベット要素の表現を含むと仮定する。このとき、どの項も `Wv′` 上で正しい符号をもつ。定数ではその表現について与えられた所属証明を使い、変数では添字の数項がアリティの数項に属することを使う。ここでは項の適格性を符号の性質としてだけ用いるため、得られる証人は命題的に切り詰められている。
<!--/-->

```agda
    tmV : ∀ {n} (Wv′ : V ℓ) → ((q : Ab) → ⟨ ι q ∈ Wv′ ⟩) → (t : Term Ab n) → IsTmV Wv′ (ct t) (# n)
    tmV Wv′ into (con q) = ∣ inl (ι q , (refl , into q)) ∣₁
    tmV {n} Wv′ into (var i) = ∣ inr (# (toℕ i) , (refl , #mono (toℕ i) n (toℕ<n i))) ∣₁
```

<!--en-->
The constants of the alphabet belong to the environment's alphabet slot, transported through the equality of the two carriers.
<!--zh-->
字母表的常元属于环境的字母表槽位，经由两个载体的等同传输。
<!--ja-->
アルファベットの定数は、二つの台の同一視を通して、環境のアルファベットのスロットに属する。
<!--/-->

```agda
    ι∈w : (q : Ab) → ⟨ ι q ∈ Wv ⟩
    ι∈w q = subst (λ u → ⟨ ι q ∈ u ⟩) (sym qw) (ι∈ q)
```

<!--en-->
By definition of `AllCodes W`, the key of every formula over the alphabet belongs to it. Transporting this membership along `qC` places the same key in the set `Cv` named by the code slot.
<!--zh-->
依照 `AllCodes W` 的定义，字母表上每条公式的键都属于其中。沿 `qC` 传输这份隶属证明，便得到同一个键属于码槽位所指的集合 `Cv`。
<!--ja-->
`AllCodes W` の定義により、アルファベット上のすべての論理式キーはそこに属する。この所属証明を `qC` に沿って輸送すれば、同じキーが符号スロットの指す集合 `Cv` に属することが得られる。
<!--/-->

```agda
    mem : ∀ {n} (ψ : Formula Ab n) → ⟨ fst (keyS W ψ) ∈ Cv ⟩
    mem ψ = subst (λ u → ⟨ fst (keyS W ψ) ∈ u ⟩) (sym qC) (key∈AllCodes W ψ)
```

<!--en-->
Likewise, the tower contains the canonical entry pairing the numeral `# n` with the environment set `envSet W n`. Transport along `qE` shows that this entry belongs to the arity set `Ev`.
<!--zh-->
同样，环境塔包含由数码 `# n` 与环境集 `envSet W n` 配成的典范条目。沿 `qE` 传输其隶属证明，便知该条目属于元数集合 `Ev`。
<!--ja-->
同様に、環境塔には数項 `# n` と環境集合 `envSet W n` の対である正準な項目が含まれる。その所属証明を `qE` に沿って輸送すると、この項目がアリティ集合 `Ev` に属することが分かる。
<!--/-->

```agda
    entry∈ : (n : ℕ) → ⟨ pr (# n) (fst (envSet W n)) ∈ Ev ⟩
    entry∈ n = subst (λ u → ⟨ pr (# n) (fst (envSet W n)) ∈ u ⟩) (sym qE) (Tower.tower-in′ W n)
```

<!--en-->
The term reader is the alphabet instance of the general term legality just proved.
<!--zh-->
词项读式就是刚证明的一般词项合法性在字母表处的实例。
<!--ja-->
項の読みは、証明されたばかりの一般的な項の合法性のアルファベットにおける実例である。
<!--/-->

```agda
    tm : ∀ {n} (t : Term Ab n) → IsTmV Wv (ct t) (# n)
    tm = tmV Wv ι∈w
```

<!--en-->
Every formula determines a legitimate key at its own arity. The proof proceeds by structural recursion: atomic formulas combine the legal codes of their two terms, while conjunction and disjunction combine the already established memberships of their two subformula keys.
<!--zh-->
每条公式都在自身元数处确定一个合法键。证明按公式结构递归进行：原子公式组合两个词项的合法编码，合取和析取则组合已经得到的两条子公式键的隶属证明。
<!--ja-->
各論理式は、それ自身のアリティにおける正しいキーを定める。証明は論理式の構造に沿って再帰する。原子式では二つの項の正しい符号を組み合わせ、連言と選言では、すでに得られた二つの部分式キーの所属証明を組み合わせる。
<!--/-->

```agda
    keyOf : ∀ {n} (ψ : Formula Ab n) → Key (# n) (cd ψ)
    keyOf (t ∈̇ u) = ∣ f0 , pr (ct t) (ct u) , (refl , ∣ ct t , ct u , (refl , (tm t , tm u)) ∣₁) ∣₁
    keyOf (t ≐ u) = ∣ f1 , pr (ct t) (ct u) , (refl , ∣ ct t , ct u , (refl , (tm t , tm u)) ∣₁) ∣₁
    keyOf (a ∧̇ b) = ∣ f2 , pr (cd a) (cd b) , (refl , ∣ cd a , cd b , (refl , (mem a , mem b)) ∣₁) ∣₁
    keyOf (a ∨̇ b) = ∣ f3 , pr (cd a) (cd b) , (refl , ∣ cd a , cd b , (refl , (mem a , mem b)) ∣₁) ∣₁
```

<!--en-->
Implication repeats the pairing; falsity carries the zero payload with its definitional equation; the two unbounded quantifiers wrap the subformula key without any term requirement.
<!--zh-->
蕴涵重复这一配对；假携带零载荷及其定义性等式；两个无界量词直接包裹子公式键，无任何词项要求。
<!--ja-->
含意は同じ対を繰り返し、偽は零のペイロードとその定義的な等式を運び、二つの非有界の量化子は項の要求なしに部分式の鍵を包む。
<!--/-->

```agda
    keyOf (a ⇒̇ b) = ∣ f4 , pr (cd a) (cd b) , (refl , ∣ cd a , cd b , (refl , (mem a , mem b)) ∣₁) ∣₁
    keyOf ⊥̇ = ∣ f5 , # 0 , (refl , refl) ∣₁
    keyOf (∃̇ a) = ∣ f6 , cd a , (refl , mem a) ∣₁
    keyOf (∀̇ a) = ∣ f7 , cd a , (refl , mem a) ∣₁
    keyOf (∀̇∈ t a) = ∣ f8 , pr (ct t) (cd a) , (refl , ∣ ct t , cd a , (refl , (tm t , mem a)) ∣₁) ∣₁
```

<!--en-->
The bounded quantifiers pair the bounding term with the subformula key, completing the recursion: `keyOf ψ` is a legitimate key for every formula `ψ`, at `ψ`'s own arity.
<!--zh-->
有界量词将界限词项与子公式键配对，完成递归：对每条公式 `ψ`，`keyOf ψ` 都是在 `ψ` 自身元数处的合法键。
<!--ja-->
有界の量化子は境界の項と部分式の鍵を対にして再帰を完成させる。すべての論理式 `ψ` に対して、`keyOf ψ` は `ψ` みずからのアリティでの合法な鍵なのである。
<!--/-->

```agda
    keyOf (∃̇∈ t a) = ∣ f9 , pr (ct t) (cd a) , (refl , ∣ ct t , cd a , (refl , (tm t , mem a)) ∣₁) ∣₁
```

<!--en-->
The shape clause of the canonical instance follows: every member of `AllCodes W` decodes to a formula, whose arity-table pair belongs to the tower and whose payload is a legitimate key. The shape reader is fed this member by member.
<!--zh-->
典范实例的形状子句随之得出：`AllCodes W` 的每个成员都解码为一条公式，其「元数与表」对属于塔，其载荷是合法键。形状读式逐成员接收这些数据。
<!--ja-->
正準な実例の形の節が従う。`AllCodes W` のすべての要素は論理式へ復号され、そのアリティと表の対は塔に属し、ペイロードは合法な鍵である。形の読みはこのデータを要素ごとに受け取る。
<!--/-->

```agda
    shape : ⟨ γ ⊨ shapeAt C w E N ⟩
    shape = ShapeRead.shape-in C w E N γ tg (λ c c∈ → map₁
      (λ { (n , ψ , e) → # n , fst (envSet W n) , cd ψ , (entry∈ n , (e , keyOf ψ)) })
      (AllCodes-out W c (subst (λ u → ⟨ fst c ∈ u ⟩) qC c∈)))
```

<!--en-->
The decoding helper fixes the arity explicitly. If a code-domain member `c` has underlying set `pr (# n) z`, then, under propositional truncation, there is a formula `ψ` of arity exactly `n` such that `z ≡ cd ψ`. The conclusion recovers the payload formula only after the outer numeral has fixed its arity.
<!--zh-->
解码辅助引理显式固定元数。若码域成员 `c` 的底层集合是 `pr (# n) z`，则在命题截断下存在一条元数恰为 `n` 的公式 `ψ`，满足 `z ≡ cd ψ`。也就是说，只有外层数码固定了元数之后，结论才恢复载荷所编码的公式。
<!--ja-->
復号の補助補題はアリティを明示的に固定する。符号領域の要素 `c` の基底集合が `pr (# n) z` なら、命題的切り詰めのもとで、`z ≡ cd ψ` を満たすアリティがちょうど `n` の論理式 `ψ` が存在する。つまり、外側の数項によってアリティが固定されてから、ペイロードが符号化する論理式が復元される。
<!--/-->

```agda
    decodeAt : (c : S) → ⟨ fst c ∈ Cv ⟩ → (n : ℕ) (z : V ℓ) → fst c ≡ pr (# n) z
             → ∥ Σ[ ψ ∈ Formula Ab n ] (z ≡ cd ψ) ∥₁
    decodeAt c c∈ n z e = map₁
      (λ { (n₁ , ψ₁ , e₁) →
        let q = pr-inj (sym e₁ ∙ e)
```

<!--en-->
The proof reads the member outward and aligns the two arities by the injectivity of the pair and of the numeral, transporting the formula along the arity equation. The equation of the coding is then reversed to identify the payload.
<!--zh-->
证明向外读出该成员，并用配对与数码的单射性对齐两个元数，沿元数等式传输公式。随后反向读取编码的等式以确定载荷。
<!--ja-->
証明は要素を外向きに読み、対と数項の単射性によって二つのアリティを整え、アリティの等式に沿って論理式を輸送する。ついで符号化の等式を逆向きに読んでペイロードを確定する。
<!--/-->

```agda
            nq = #-inj′ (q .fst)
        in subst (Formula Ab) nq ψ₁ , (sym (q .snd) ∙ sym (cd-subst nq ψ₁)) })
      (AllCodes-out W c (subst (λ u → ⟨ fst c ∈ u ⟩) qC c∈))
```

<!--en-->
The term-decoding statement is parameterized by a bound set: every member of the bound decodes, up to truncation, to a term whose coding pairs the tag numeral with the member itself.
<!--zh-->
词项解码陈述由一个界集合参数化：界中的每个成员都 (至截断) 解码为一个词项，其编码把标签数码与该成员本身配对。
<!--ja-->
項の復号の主張は、界の集合によってパラメータ化される。界のすべての要素は、切り詰めの範囲で、タグの数項とみずからを対にする符号をもつ項へ復号される。
<!--/-->

```agda
    TmDec : ∀ {n} → Fin 10 → V ℓ → Type (ℓ-suc ℓ)
    TmDec {n} Nx bound = (x : V ℓ) → ⟨ x ∈ bound ⟩ → ∥ Σ[ t ∈ Term Ab n ] (ct t ≡ pr (# (toℕ Nx)) x) ∥₁
```

<!--en-->
Constants decode through the fiber of the alphabet embedding: a member of the alphabet slot is the embedded image of some alphabet entry, and that entry is the constant wanted.
<!--zh-->
常元经字母表嵌入的纤维解码：字母表槽位的成员是某个字母表条目的嵌入像，而那个条目正是所求的常元。
<!--ja-->
定数はアルファベットの埋め込みのファイバーを通して復号される。アルファベットのスロットの要素はあるアルファベットの項目の埋め込まれた像であり、その項目こそが求める定数である。
<!--/-->

```agda
    conDec : ∀ {n} → TmDec {n} f0 Wv
    conDec x x∈ = ∣ con (fib .fst) , cong (pr (# 0)) (fib .snd) ∣₁
      where
      fib : Σ[ q ∈ Ab ] (ι q ≡ x)
      fib = ∈-asFiber {a = x} {b = fst W} (subst (λ u → ⟨ x ∈ u ⟩) qw x∈)
```

<!--en-->
Variables decode through the numeral elimination: a member of the arity numeral is a natural number below `n`, which converts back into a valid index, and the coding equation is transported along the round trip.
<!--zh-->
变元经数码消去解码：元数数码的成员是低于 `n` 的自然数，可转换回合法索引，而编码等式沿该往返传输。
<!--ja-->
変数は数項の消去を通して復号される。アリティの数項の要素は `n` 未満の自然数であり、正しい添字へ変換し直せ、符号化の等式はその往復に沿って輸送される。
<!--/-->

```agda
    varDec : (n : ℕ) (A : V ℓ) → A ≡ # n → TmDec {n} f1 A
    varDec n A qa x x∈ = map₁
      (λ { (j , (p , ex)) → var (fromℕ' n j p) , cong (pr (# 1)) (cong #_ (toFromId' n j p) ∙ sym ex) })
      (∈#-elim n x (subst (λ u → ⟨ x ∈ u ⟩) qa x∈))
```

<!--en-->
Fix one entry `q` of the environment tower and an equation identifying its recorded arity with `# n`. The local context `δ4` supplies the four values expected by the closure formulas: the arity table, the numeral arity, a container relating the entry to that table, and the entry itself.
<!--zh-->
固定环境塔的一个条目 `q`，并假设其所记录的元数等同于 `# n`。局部语境 `δ4` 给出闭包公式所需的四个值：元数表、元数数码、把该条目与表联系起来的容器，以及条目本身。
<!--ja-->
環境塔の一つの項目 `q` を固定し、そこに記録されたアリティが `# n` と等しいと仮定する。局所文脈 `δ4` は、閉包論理式が要求する四つの値、すなわちアリティ表、アリティの数項、その項目と表を結ぶ容器、そして項目自身を与える。
<!--/-->

<details open class="submodule-fold">
<summary class="submodule-fold-heading">
```agda
    module At (q : S) (q∈ : ⟨ fst q ∈ Ev ⟩) (ar F s : S) (n : ℕ) (qa : fst ar ≡ # n) where
```
</summary>
<div class="submodule-fold-content">

```agda
      private
        δ4 : S ^ (4 + m)
        δ4 = F ∷ ar ∷ s ∷ q ∷ γ
        A = fst ar
```

<!--en-->
Within this fixed context, `CloseRead` turns satisfaction of each closure formula into its corresponding mathematical closure property, while `Close` supplies the formulas themselves.
<!--zh-->
在这个固定语境中，`CloseRead` 把每条闭包公式的满足转换为相应的数学闭包性质，`Close` 则给出这些公式本身。
<!--ja-->
この固定した文脈のもとで、`CloseRead` は各閉包論理式の充足を対応する数学的な閉包性へ変換し、`Close` はその論理式自体を与える。
<!--/-->

```agda
        module CR = CloseRead C w N δ4 tg
        module Cl = Close C w N
```

<!--en-->
The helper `in-key` transports canonical membership along an equality. If `x` is equal to the underlying set of the key of a formula `ψ`, then the known membership of that canonical key in `Cv` yields `x ∈ Cv`.
<!--zh-->
辅助引理 `in-key` 沿等式传输典范键的隶属证明。若 `x` 等于某条公式 `ψ` 的键的底层集合，那么由该典范键已知属于 `Cv`，即可推出 `x ∈ Cv`。
<!--ja-->
補助補題 `in-key` は、等式に沿って正準なキーの所属証明を輸送する。`x` が論理式 `ψ` のキーの基底集合に等しければ、その正準なキーが `Cv` に属するという既知の事実から `x ∈ Cv` が得られる。
<!--/-->

```agda
        in-key : ∀ {k} (ψ : Formula Ab k) (x : V ℓ) → x ≡ fst (keyS W ψ) → ⟨ x ∈ Cv ⟩
        in-key ψ x e = subst (λ u → ⟨ u ∈ Cv ⟩) (sym e) (mem ψ)
```

<!--en-->
For a tag `Nx` and an element `x`, `TmAt Nx x` is the Σ type of a term `t` together with an equation saying that `t` is coded by the pair of the numeral for `Nx` and `x`. Unlike the preceding decoding statements, this local type is not propositionally truncated.
<!--zh-->
给定标签 `Nx` 和元素 `x`，`TmAt Nx x` 是一个 Σ 类型：其第一分量是词项 `t`，第二分量是一条等式，说明 `t` 的编码正是由 `Nx` 的数码与 `x` 配成的对。与前面的解码陈述不同，这个局部类型没有经过命题截断。
<!--ja-->
タグ `Nx` と要素 `x` に対し、`TmAt Nx x` は、項 `t` と、`t` の符号が `Nx` の数項と `x` の対であることを述べる等式からなる Σ 型である。先の復号の主張とは異なり、この局所的な型は命題的に切り詰められていない。
<!--/-->

```agda
        TmAt : (Nx : Fin 10) (x : V ℓ) → Type (ℓ-suc ℓ)
        TmAt Nx x = Σ[ t ∈ Term Ab n ] (ct t ≡ pr (# (toℕ Nx)) x)
```

<!--en-->
Similarly, `FoAt k z` is the Σ type of a formula `ψ` of arity `k` together with an equation `z ≡ cd ψ`. It retains both the formula and its coding equation as usable data.
<!--zh-->
同样，`FoAt k z` 是一个 Σ 类型：其第一分量是元数为 `k` 的公式 `ψ`，第二分量是等式 `z ≡ cd ψ`。公式及其编码等式都作为可用数据保留下来。
<!--ja-->
同様に、`FoAt k z` は、アリティ `k` の論理式 `ψ` と等式 `z ≡ cd ψ` からなる Σ 型である。論理式とその符号化の等式は、どちらも利用可能なデータとして保持される。
<!--/-->

```agda
        FoAt : (k : ℕ) (z : V ℓ) → Type (ℓ-suc ℓ)
        FoAt k z = Σ[ ψ ∈ Formula Ab k ] (z ≡ cd ψ)
```

<!--en-->
The atomic closure clause is proved from the two term decodings. Given a decoding of the first coordinate's member and a decoding of the second coordinate's member, the atomic key is built from the two terms by the object-language constructor, and the coding equation identifies it with the named key.
<!--zh-->
原子闭包子句由两条词项解码证明。给定第一坐标成员的解码与第二坐标成员的解码，原子键由对象语言构造子从两个词项构造，而编码等式把它与被点名的键等同。
<!--ja-->
原子の閉包の節は、二つの項の復号から証明される。第一座標の要素の復号と第二座標の要素の復号が与えられれば、原子の鍵は対象言語の構成子によって二つの項から作られ、符号化の等式がそれを名指された鍵と同一視する。
<!--/-->

```agda
        atomIn : (k Nx Ny : Fin 10) (X : Fin (4 + m)) (Y : Fin (5 + m))
               → (op : Term Ab n → Term Ab n → Formula Ab n)
               → ((t u : Term Ab n) → cd (op t u) ≡ pr (# (toℕ k)) (pr (ct t) (ct u)))
               → TmDec Nx (fst (lookup X δ4)) → ((x : S) → TmDec Ny (fst (lookup Y (x ∷ δ4))))
               → ⟨ δ4 ⊨ Cl.atomClose k Nx Ny X Y ⟩
```

<!--en-->
Decode the two coordinates separately. The first yields a term `t` and its coding equation; after that coordinate has been added to the context, the second yields a term `u` and its coding equation.
<!--zh-->
分别解码两个坐标。第一坐标给出词项 `t` 及其编码等式；把这个坐标加入语境后，第二坐标再给出词项 `u` 及其编码等式。
<!--ja-->
二つの座標を別々に復号する。第一座標から項 `t` とその符号化の等式を得て、その座標を文脈に加えた後、第二座標から項 `u` とその符号化の等式を得る。
<!--/-->

```agda
        atomIn k Nx Ny X Y op code dx dy = CR.atomClose-in k Nx Ny X Y (λ x y x∈ y∈ →
          let d1 : ∥ TmAt Nx (fst x) ∥₁
              d1 = dx (fst x) x∈
              d2 : ∥ TmAt Ny (fst y) ∥₁
              d2 = dy x (fst y) y∈
```

<!--en-->
The set `G` is the candidate atomic key formed from the arity, the atomic tag, and the two coded coordinates. Because membership in `Cv` is a proposition, both truncated term decodings may be eliminated into this goal. Their coding equations identify `G` with the key of `op t u`, whose membership follows from `in-key`.
<!--zh-->
集合 `G` 是由元数、原子标签和两个已编码坐标组成的候选原子键。由于「属于 `Cv`」是命题，可以把两份经过截断的词项解码依次消去到这个目标中。它们的编码等式把 `G` 等同于公式 `op t u` 的键，而后者的隶属由 `in-key` 给出。
<!--ja-->
集合 `G` は、アリティ、原子式のタグ、符号化された二つの座標から作る候補の原子式キーである。`Cv` への所属は命題なので、切り詰められた二つの項の復号を順にこの目標へ消去できる。それぞれの符号化の等式により `G` は論理式 `op t u` のキーと同一視され、その所属は `in-key` から得られる。
<!--/-->

```agda
              G : V ℓ
              G = pr A (pr (# (toℕ k)) (pr (pr (# (toℕ Nx)) (fst x)) (pr (# (toℕ Ny)) (fst y))))
          in rec₁ (snd (G ∈ Cv))
            (λ { (t , et) → rec₁ (snd (G ∈ Cv))
              (λ { (u , eu) → in-key (op t u) G
```

<!--en-->
The final equality is assembled in three layers: `qa` aligns the outer arity, the two term-code equations align the paired payload, and the defining equation for `op` aligns the atomic tag. Transporting canonical membership along this equality completes the atomic closure proof.
<!--zh-->
最后的等式分三层拼合：`qa` 对齐外层元数，两条词项编码等式对齐成对载荷，而 `op` 的定义等式对齐原子标签。沿这条等式传输典范键的隶属证明，便完成原子闭包的证明。
<!--ja-->
最後の等式は三段階で組み立てる。`qa` が外側のアリティを揃え、二つの項の符号化等式が対になったペイロードを揃え、`op` の定義等式が原子タグを揃える。この等式に沿って正準なキーの所属証明を輸送すれば、原子閉包の証明が完了する。
<!--/-->

```agda
                (cong₂ pr qa (cong (pr (# (toℕ k))) (cong₂ pr (sym et) (sym eu)) ∙ sym (code t u))) })
              d2 })
            d1)
```

<!--en-->
For a binary connective, both immediate subformulas have the same arity `n` as the compound. The hypotheses present their keys with first component `# n`; after aligning that component with the recorded arity, `decodeAt` recovers each payload as the code of a formula of arity `n`.
<!--zh-->
对于二元联结词，两个直接子公式与复合公式具有相同的元数 `n`。假设已将两个子键的第一分量写成 `# n`；把这一分量与记录的元数对齐后，`decodeAt` 分别将两个载荷恢复为元数 `n` 的公式码。
<!--ja-->
二項結合子では、二つの直接の部分論理式は、複合論理式と同じアリティ `n` をもつ。仮定により二つの下位キーの第一成分は `# n` と書かれているので、この成分を記録されたアリティに揃えれば、`decodeAt` が各ペイロードをアリティ `n` の論理式の符号として復元する。
<!--/-->

```agda
        binIn : (k : Fin 10) (op : Formula Ab n → Formula Ab n → Formula Ab n)
              → ((a b : Formula Ab n) → cd (op a b) ≡ pr (# (toℕ k)) (pr (cd a) (cd b)))
              → ⟨ δ4 ⊨ Cl.binClose k ⟩
        binIn k op code = CR.binClose-in k (λ c₁ c₂ a b c₁∈ c₂∈ e₁ e₂ →
          let d1 : ∥ FoAt n (fst a) ∥₁
```

<!--en-->
The two applications of `decodeAt` yield, merely, formulas `ψ₁` and `ψ₂` whose codes are the two payload components. The set `G` is the composite key already assembled from the recorded arity, the chosen connective tag, and those components.
<!--zh-->
两次应用 `decodeAt`，分别纯粹地得到公式 `ψ₁` 与 `ψ₂`，其编码就是载荷的两个分量。集合 `G` 则是已经由记录的元数、所选联结词的标签以及这两个分量组装出的复合键。
<!--ja-->
`decodeAt` を二度適用すると、符号が二つのペイロード成分に等しい論理式 `ψ₁` と `ψ₂` が、それぞれ単に得られる。集合 `G` は、記録されたアリティ、選んだ結合子タグ、この二成分からすでに組み立てられた複合キーである。
<!--/-->

```agda
              d1 = decodeAt c₁ c₁∈ n (fst a) (e₁ ∙ cong (λ v → pr v (fst a)) qa)
              d2 : ∥ FoAt n (fst b) ∥₁
              d2 = decodeAt c₂ c₂∈ n (fst b) (e₂ ∙ cong (λ v → pr v (fst b)) qa)
              G : V ℓ
              G = pr A (pr (# (toℕ k)) (pr (fst a) (fst b)))
```

<!--en-->
Eliminating the two truncated witnesses reduces the goal to genuine formulas `ψ₁` and `ψ₂`. Their code equations identify `G` with the key of `op ψ₁ ψ₂`, so the canonical membership proof `in-key` establishes the required binary closure clause.
<!--zh-->
依次消去两份截断见证后，只需处理实际的公式 `ψ₁` 与 `ψ₂`。它们的编码等式将 `G` 与 `op ψ₁ ψ₂` 的键同一视，因此典范隶属证明 `in-key` 给出所需的二元闭包子句。
<!--ja-->
切り詰められた二つの証人を順に除去すると、実際の論理式 `ψ₁` と `ψ₂` を扱えばよくなる。それぞれの符号の等式により `G` は `op ψ₁ ψ₂` のキーと同一視されるので、正準な所属証明 `in-key` から必要な二項閉包条項が得られる。
<!--/-->

```agda
          in rec₁ (snd (G ∈ Cv))
            (λ { (ψ₁ , ea) → rec₁ (snd (G ∈ Cv))
              (λ { (ψ₂ , eb) → in-key (op ψ₁ ψ₂) G
                (cong₂ pr qa (cong (pr (# (toℕ k))) (cong₂ pr ea eb) ∙ sym (code ψ₁ ψ₂))) })
              d2 })
```

<!--en-->
The outer elimination supplies the first recovered formula and completes the proof that the domain is closed under the chosen binary connective.
<!--zh-->
外层消去代入第一个恢复出的公式，从而完成码域对所选二元联结词封闭的证明。
<!--ja-->
外側の除去が最初に復元した論理式を与え、符号領域が選んだ二項結合子について閉じていることの証明が完了する。
<!--/-->

```agda
            d1)
```

<!--en-->
Falsity has no subformula: its payload is simply the numeral zero. Once the recorded arity and the chosen tag are aligned with the canonical code of `c₀`, `in-key` places the resulting key in the domain.
<!--zh-->
假没有子公式，其载荷就是数码零。将记录的元数和所选标签与 `c₀` 的典范编码对齐后，`in-key` 便证明所得键属于码域。
<!--ja-->
偽には部分論理式がなく、そのペイロードは数項零だけである。記録されたアリティと選んだタグを `c₀` の正準な符号に揃えれば、`in-key` により得られたキーが符号領域に属することが示される。
<!--/-->

```agda
        conIn : (k : Fin 10) (c₀ : Formula Ab n) → cd c₀ ≡ pr (# (toℕ k)) (# 0) → ⟨ δ4 ⊨ Cl.conClose k ⟩
        conIn k c₀ code = CR.conClose-in k (in-key c₀ (pr A (pr (# (toℕ k)) (# 0))) (cong₂ pr qa (sym code)))
```

<!--en-->
Binding one variable changes the arity of the body from `n` to `suc n`. The quantifier closure hypothesis therefore presents its immediate subkey at the successor arity, and `decodeAt` recovers a formula body of precisely that arity.
<!--zh-->
约束一个变量会使主体的元数由 `n` 变为 `suc n`。因此，量词闭包的假设把直接子键置于后继元数处，而 `decodeAt` 恰好恢复出具有这一元数的公式主体。
<!--ja-->
変数を一つ束縛すると、本体のアリティは `n` から `suc n` に変わる。したがって量化子の閉包に関する仮定は、直接の下位キーを後続アリティに置き、`decodeAt` はちょうどそのアリティをもつ論理式の本体を復元する。
<!--/-->

```agda
        quIn : (k : Fin 10) (op : Formula Ab (suc n) → Formula Ab n)
             → ((a : Formula Ab (suc n)) → cd (op a) ≡ pr (# (toℕ k)) (cd a))
             → ⟨ δ4 ⊨ Cl.quClose k ⟩
        quIn k op code = CR.quClose-in k (λ c₁ ar' a c₁∈ e₁ es →
          let d1 : ∥ FoAt (suc n) (fst a) ∥₁
```

<!--en-->
Let `G` be the key assembled from the outer arity, the quantifier tag, and the encoded body. After the truncated body has been recovered as `ψ₁`, its code equation identifies `G` with the key of `op ψ₁`; canonical membership then proves the quantifier closure clause.
<!--zh-->
令 `G` 为由外层元数、量词标签与主体编码组装出的键。截断的主体恢复为 `ψ₁` 后，其编码等式将 `G` 与 `op ψ₁` 的键同一视；典范隶属关系随即证明量词闭包子句。
<!--ja-->
外側のアリティ、量化子タグ、本体の符号から組み立てたキーを `G` とする。切り詰められた本体を `ψ₁` として復元すると、その符号の等式により `G` は `op ψ₁` のキーと同一視され、正準な所属証明から量化子の閉包条項が従う。
<!--/-->

```agda
              d1 = decodeAt c₁ c₁∈ (suc n) (fst a) (e₁ ∙ cong (λ v → pr v (fst a)) (es ∙ cong sucV qa))
              G : V ℓ
              G = pr A (pr (# (toℕ k)) (fst a))
          in rec₁ (snd (G ∈ Cv))
            (λ { (ψ₁ , ea) → in-key (op ψ₁) G (cong₂ pr qa (cong (pr (# (toℕ k))) ea ∙ sym (code ψ₁))) })
```

<!--en-->
Eliminating the recovered body completes the proof that the domain is closed under the chosen unbounded quantifier.
<!--zh-->
消去所恢复的主体，便完成码域对所选无界量词封闭的证明。
<!--ja-->
復元した本体を除去することで、符号領域が選んだ非有界量化子について閉じていることの証明が完了する。
<!--/-->

```agda
            d1)
```

<!--en-->
A bounded quantifier carries both a body of arity `suc n` and a bounding term of arity `n`. Accordingly, `bqIn` receives a term-decoding hypothesis for the environment component in which the bound is stored, in addition to the decoder already available for the body key.
<!--zh-->
有界量词同时携带元数为 `suc n` 的主体和元数为 `n` 的界词项。因此，除了已有的主体键解码方式外，`bqIn` 还接收一项词项解码假设，用于存放界的环境分量。
<!--ja-->
有界量化子は、アリティ `suc n` の本体と、アリティ `n` の境界項をともに含む。そのため `bqIn` は、本体キーにすでに使える復号に加えて、境界を収める環境成分についての項の復号仮定を受け取る。
<!--/-->

```agda
        bqIn : (k Nx : Fin 10) (X : Fin (8 + m))
             → (op : Term Ab n → Formula Ab (suc n) → Formula Ab n)
             → ((t : Term Ab n) (a : Formula Ab (suc n)) → cd (op t a) ≡ pr (# (toℕ k)) (pr (ct t) (cd a)))
             → ((ar' a s' c₁ : S) → TmDec Nx (fst (lookup X (a ∷ ar' ∷ s' ∷ c₁ ∷ δ4))))
             → ⟨ δ4 ⊨ Cl.bqClose k Nx X ⟩
```

<!--en-->
The term-decoding hypothesis recovers the bound from its membership proof, while `decodeAt` recovers the body from the successor-arity subkey. Both results are propositionally truncated, since the closure goal requires only membership of the completed key rather than chosen decoders.
<!--zh-->
词项解码假设由界的隶属证明恢复界词项，`decodeAt` 则由后继元数处的子键恢复主体。两项结果都受命题截断，因为闭包目标只要求完整键的隶属证明，并不要求选定全局解码结果。
<!--ja-->
項の復号仮定は境界の所属証明から境界項を復元し、`decodeAt` は後続アリティの下位キーから本体を復元する。どちらの結果も命題的に切り詰められている。閉包の目標が要求するのは完成したキーの所属であって、復号結果を大域的に選ぶことではないからである。
<!--/-->

```agda
        bqIn k Nx X op code dx = CR.bqClose-in k Nx X (λ c₁ ar' a s' c₁∈ e₁ es x x∈ →
          let d1 : ∥ TmAt Nx (fst x) ∥₁
              d1 = dx ar' a s' c₁ (fst x) x∈
              d2 : ∥ FoAt (suc n) (fst a) ∥₁
              d2 = decodeAt c₁ c₁∈ (suc n) (fst a) (e₁ ∙ cong (λ v → pr v (fst a)) (es ∙ cong sucV qa))
```

<!--en-->
The key `G` now has a nested payload: first the code of the bounding term, then the code of the body. The first truncation elimination exposes a genuine term `t`; the second will expose the formula to which the body code belongs.
<!--zh-->
此时键 `G` 的载荷是嵌套的：先放界词项的编码，再放主体的编码。第一次截断消去取出实际词项 `t`，第二次则将取出主体编码所对应的公式。
<!--ja-->
ここでキー `G` のペイロードは入れ子になっており、まず境界項の符号、次に本体の符号が置かれている。一つ目の切り詰めの除去で実際の項 `t` を取り出し、二つ目で本体の符号に対応する論理式を取り出す。
<!--/-->

```agda
              G : V ℓ
              G = pr A (pr (# (toℕ k)) (pr (pr (# (toℕ Nx)) (fst x)) (fst a)))
          in rec₁ (snd (G ∈ Cv))
            (λ { (t , et) → rec₁ (snd (G ∈ Cv))
              (λ { (ψ₁ , ea) → in-key (op t ψ₁) G
```

<!--en-->
With the recovered term `t` and body `ψ₁`, their code equations identify `G` with the key of `op t ψ₁`. The canonical membership proof then supplies the bounded-quantifier clause, and the two truncation eliminations close in the reverse order in which their witnesses were introduced.
<!--zh-->
有了恢复出的词项 `t` 与主体 `ψ₁`，二者的编码等式便将 `G` 与 `op t ψ₁` 的键同一视。典范隶属证明由此给出有界量词子句，两层截断消去再按见证引入的相反次序收束。
<!--ja-->
復元した項 `t` と本体 `ψ₁` が得られると、それぞれの符号の等式により `G` は `op t ψ₁` のキーと同一視される。正準な所属証明から有界量化子の条項が得られ、二つの切り詰めの除去は、証人を導入した順序とは逆に閉じられる。
<!--/-->

```agda
                (cong₂ pr qa (cong (pr (# (toℕ k))) (cong₂ pr (sym et) ea) ∙ sym (code t ψ₁))) })
              d2 })
            d1)
```

<!--en-->
The single formula `Cl.all` packages eighteen closure clauses. Its first eight clauses concern the two atomic relations: for each relation, the left and right terms may independently be constants or variables. Constants are decoded through membership in `w`, while variables are decoded through membership of their indices in the arity numeral.
<!--zh-->
公式 `Cl.all` 将十八条闭包子句汇集在一起。开头八条处理两种原子关系：对于每种关系，左右两个词项都可以分别是常元或变元。常元通过其在 `w` 中的隶属关系解码，变元则通过其索引在元数数码中的隶属关系解码。
<!--ja-->
一つの論理式 `Cl.all` は十八の閉包条項をまとめている。最初の八条項は二つの原子関係を扱う。各関係について、左右の項はそれぞれ独立に定数または変数である。定数は `w` への所属から復号され、変数は添字がアリティの数項に属することから復号される。
<!--/-->

```agda
      all : ⟨ δ4 ⊨ Cl.all ⟩
      all =
          atomIn f0 f0 f0 (sh 4 w) (sh 5 w) _∈̇_ (λ _ _ → refl) conDec (λ _ → conDec)
        , ( atomIn f0 f0 f1 (sh 4 w) i2 _∈̇_ (λ _ _ → refl) conDec (λ _ → varDec n A qa)
        , ( atomIn f0 f1 f0 i1 (sh 5 w) _∈̇_ (λ _ _ → refl) (varDec n A qa) (λ _ → conDec)
```

<!--en-->
Four clauses cover the constant-variable combinations for membership, and four parallel clauses cover them for equality. This accounts for all eight atomic closure clauses; the remaining ten concern logical connectives and quantifiers.
<!--zh-->
其中四条覆盖成员关系原子中常元与变元的全部组合，另有四条以相同方式覆盖相等原子。这就给出了八条原子闭包子句；其余十条处理逻辑联结词与量词。
<!--ja-->
四つの条項が所属原子における定数と変数の全組合せを覆い、これと並行する四つの条項が等号原子を覆う。これで八つの原子閉包条項が揃い、残る十条項が論理結合子と量化子を扱う。
<!--/-->

```agda
        , ( atomIn f0 f1 f1 i1 i2 _∈̇_ (λ _ _ → refl) (varDec n A qa) (λ _ → varDec n A qa)
        , ( atomIn f1 f0 f0 (sh 4 w) (sh 5 w) _≐_ (λ _ _ → refl) conDec (λ _ → conDec)
        , ( atomIn f1 f0 f1 (sh 4 w) i2 _≐_ (λ _ _ → refl) conDec (λ _ → varDec n A qa)
        , ( atomIn f1 f1 f0 i1 (sh 5 w) _≐_ (λ _ _ → refl) (varDec n A qa) (λ _ → conDec)
        , ( atomIn f1 f1 f1 i1 i2 _≐_ (λ _ _ → refl) (varDec n A qa) (λ _ → varDec n A qa)
```

<!--en-->
The next six clauses cover conjunction, disjunction, implication, falsity, and the two unbounded quantifiers. Each constructor is paired with its canonical tag and its definitional coding equation, so the corresponding helper can insert the constructed key directly.
<!--zh-->
接下来的六条子句处理合取、析取、蕴涵、假以及两个无界量词。每个构造子都配以其典范标签和定义性的编码等式，因此相应的辅助引理可以直接插入所构造的键。
<!--ja-->
続く六つの条項は、連言、選言、含意、偽、二つの非有界量化子を扱う。各構成子には正準なタグと定義的な符号化の等式が添えられているので、対応する補助補題が構成されたキーを直接挿入できる。
<!--/-->

```agda
        , ( binIn f2 _∧̇_ (λ _ _ → refl)
        , ( binIn f3 _∨̇_ (λ _ _ → refl)
        , ( binIn f4 _⇒̇_ (λ _ _ → refl)
        , ( conIn f5 ⊥̇ refl
        , ( quIn f6 ∃̇_ (λ _ → refl)
```

<!--en-->
The last four clauses treat bounded universal and existential quantification. Each appears once with a constant bound and once with a variable bound; `conDec` and `varDec` verify that these are legal terms at the outer arity. The nested tuple now supplies every component of `Cl.all`.
<!--zh-->
最后四条子句处理有界全称量化与有界存在量化。每种量化各有一条以常元为界，另一条以变元为界；`conDec` 与 `varDec` 分别证明它们是外层元数处的合法词项。至此，这个嵌套元组给出了 `Cl.all` 的全部分量。
<!--ja-->
最後の四つの条項は、有界全称量化と有界存在量化を扱う。それぞれについて、境界が定数の場合と変数の場合が一つずつあり、`conDec` と `varDec` が、それらが外側のアリティで正しい項であることを示す。これで入れ子の組は `Cl.all` の全成分を与える。
<!--/-->

```agda
        , ( quIn f7 ∀̇_ (λ _ → refl)
        , ( bqIn f8 f0 (sh 8 w) ∀̇∈ (λ _ _ → refl) (λ _ _ _ _ → conDec)
        , ( bqIn f8 f1 i5 ∀̇∈ (λ _ _ → refl) (λ _ _ _ _ → varDec n A qa)
        , ( bqIn f9 f0 (sh 8 w) ∃̇∈ (λ _ _ → refl) (λ _ _ _ _ → conDec)
        ,   bqIn f9 f1 i5 ∃̇∈ (λ _ _ → refl) (λ _ _ _ _ → varDec n A qa) ))))))))))))))))
```
</div>
</details>

<!--en-->
It remains to establish the closure clauses at every entry `q` of the environment tower. The tower theorem expresses `q`, under propositional truncation, as the canonical entry `(# n, envSet W n)` for some `n`. Its first-component equation identifies the recorded arity with `# n`, so the eighteen clauses assembled in `At.all` apply at that entry.
<!--zh-->
还需在环境塔的每个条目 `q` 处证明这些闭包子句。环境塔定理在命题截断下把 `q` 表示为某个 `n` 对应的典范条目 `(# n, envSet W n)`；其中关于第一分量的等式将记录的元数与 `# n` 对齐，于是 `At.all` 汇集的十八条子句可以应用于该条目。
<!--ja-->
あとは、環境塔の各要素 `q` で閉包条項を示す。環境塔の定理により、命題的切り詰めのもとで、`q` はある `n` に対応する正準な要素 `(# n, envSet W n)` として表される。その第一成分の等式が記録されたアリティを `# n` に揃えるので、`At.all` にまとめた十八の条項をその要素に適用できる。
<!--/-->

```agda
    close : ⟨ γ ⊨ closeAt C w E N ⟩
    close q q∈ = bothAll-in i0 (Close.all C w N) (q ∷ γ) (λ ar F s s∈ ar∈ F∈ e →
      rec₁ (snd ((F ∷ ar ∷ s ∷ q ∷ γ) ⊨ Close.all C w N))
        (λ { (n , qp) → At.all q q∈ ar F s n (pr-inj (sym e ∙ qp) .fst) })
        (Tower.tower-out W q (subst (λ u → ⟨ fst q ∈ u ⟩) qE q∈)))
```

<!--en-->
The canonical domain `AllCodes W` now satisfies both halves of `codesAt`: `shape` shows that each of its members has a recorded arity and one of the ten permitted payload shapes, while `close` shows that every key assembled from legal immediate constituents belongs to the domain. This is the adequacy of the code domain itself: its syntactic description contains exactly the genuine formula keys.
<!--zh-->
典范码域 `AllCodes W` 至此满足 `codesAt` 的两个部分：`shape` 表明每个成员都具有记录的元数和十种合法载荷形状之一，`close` 则表明由合法的直接组成部分组装出的每个键都属于该域。这一结论确立了码域本身的充分性：它的语法描述恰好收录所有真实的公式键。
<!--ja-->
これで正準な符号領域 `AllCodes W` は `codesAt` の両部分を満たす。`shape` は、各要素が記録されたアリティと十種類の正しいペイロード形のいずれかをもつことを示し、`close` は、正しい直接の構成要素から組み立てたすべてのキーが領域に属することを示す。ここで確立されたのは符号領域そのものの妥当性である。その構文的記述は、真正な論理式キーをちょうどすべて収めている。
<!--/-->

```agda
  holds : ⟨ γ ⊨ codesAt C w E N ⟩
  holds = shape , close
```
</div>
</details>

<!--en-->
## Recap
<!--zh-->
## 小结
<!--ja-->
## まとめ
<!--/-->

<!--en-->
The two directions now coincide on the canonical domain. Soundness decodes each member of `AllCodes W` into a formula key at its recorded arity, while completeness places every genuine formula key back in that domain; `CodesHolds` verifies that the internal shape and closure description supports both conclusions.
<!--zh-->
两个方向在典范码域上汇合。可靠性把 `AllCodes W` 的每个成员解码为其记录元数处的公式键，完备性则把每个真实的公式键送回该码域；`CodesHolds` 证明内部的形状与封闭描述足以支撑这两个结论。
<!--ja-->
二つの方向は正準な符号領域の上で一致する。健全性は `AllCodes W` の各要素を記録されたアリティにおける論理式キーへ復号し、完全性はすべての真正な論理式キーをその領域へ戻す。`CodesHolds` は、内部の形と閉性の記述がこの二つの結論を支えることを示す。
<!--/-->
