<!--en-->
# Describing the closed domain of formula codes

Agda already provides an inductive type of formulas and an external operation that assigns sets as their codes. To reason about syntax inside set theory, however, the model needs a formula in its own language that describes a candidate set of formula keys. This chapter constructs that bounded description: its shape half reads the immediate structure of keys already in the candidate domain, and its closure half generates compound keys from legal constituents.
<!--zh-->
# 描述封闭的公式码定义域

Agda 已经给出公式的归纳类型，以及在外部把集合指定为公式码的运算。然而，要在集合论内部推理句法，模型还需要用自身语言中的公式描述一个候选公式键集合。本章构造这份有界描述：形状半边读取候选域中已有键的直接结构，闭包半边则由合法组成部分生成复合键。
<!--ja-->
# 閉じた論理式符号の定義域を記述する

Agda にはすでに論理式の帰納型と、集合をその符号として外部で割り当てる演算があります。しかし集合論の内部で構文を扱うには、論理式キーの候補集合をモデル自身の言語で記述する論理式が必要です。本章では、その有界な記述を構成します。形の半分は候補領域にすでにあるキーの直下の構造を読み、閉性の半分は正当な構成要素から複合キーを生成します。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

```

<!--en-->
The description will be constructive. It records only bounded membership, pairing, tags, and the immediate constituents of a formula key, so its definition requires no instance of excluded middle.
<!--zh-->
这份描述是构造性的。它只记录有界隶属、配对、标签与公式键的直接组成部分，因此其定义不需要排中律实例。
<!--ja-->
この記述は構成的です。記録するのは有界な所属、対、タグ、および論理式キーの直下の構成要素だけなので、排中律の仮定は必要ありません。
<!--/-->

```agda
open import Base.Prelude

```

<!--en-->
Fix a universe level. The main parameters introduced below are a candidate code domain `C`, a working set `w` that supplies constants, a set `E` intended to hold environment-tower entries, and ten named positions `N` for constructor tags. An intended entry of `E` pairs an arity with its environment set, but the formula defined here does not itself assert that `E` is the canonical tower; later adequacy hypotheses supply that fact.
<!--zh-->
固定一个宇宙层级。下文的主要参数是候选码域 `C`、提供常元的工作集 `w`、预期存放环境塔条目的集合 `E`，以及十个构造子标签的具名位置 `N`。预期的 `E` 条目把元数与相应环境集配成一对，但这里定义的公式本身并不断言 `E` 就是典范环境塔；这一事实由后续充分性证明的假设提供。
<!--ja-->
宇宙レベルを一つ固定します。以下の主なパラメータは、候補符号領域 `C`、定数を与える作業集合 `w`、環境の塔の項目を収めるものとして用いる集合 `E`、そして十個の構成子タグを指す名前付きの位置 `N` です。意図した `E` の項目はアリティと対応する環境集合の対ですが、ここで定義する論理式だけでは `E` が正準な塔であるとは主張しません。その事実は後の妥当性証明の仮定から与えられます。
<!--/-->

```agda
module L.Coding.CodeDomain {ℓ : Level} where

```

<!--en-->
The target is an object-language formula built from membership, equality, connectives, and bounded quantifiers. Its quantifiers will range only over sets already named in the description or over small containers used to unpack pairs. This is the syntactic reason the final formula can be certified as `Δ₀`.
<!--zh-->
目标是由隶属、相等、联结词与有界量词组成的对象语言公式。其中的量词只在描述中已经命名的集合，或拆解有序对所用的小容器上取值。正因这一句法限制，最终公式才能获得 `Δ₀` 认证。
<!--ja-->
目標は、所属、等号、結合子、有界量化子からなる対象言語の論理式です。量化子は、記述の中ですでに名付けられた集合か、対を分解するための小さな容器だけを動きます。この統語上の制限により、最後の論理式を `Δ₀` と認定できます。
<!--/-->

```agda
open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using
  ( Formula; var; _∈̇_; _≐_; _∧̇_; _∨̇_; _⇒̇_; ⊥̇; ∃̇∈; ∀̇∈ )
open import FOL.LevyHierarchy using
  ( checkΔ₀; Δ₀ )
```

<!--en-->
All formulas are interpreted over the constructible carrier. Ordered-pair and graph-application predicates let that internal language inspect keys of the form `(arity, tagged payload)` without assuming that set-coded pairs have primitive projections.
<!--zh-->
所有公式都在可构造载体上解释。有序对谓词与编码图应用谓词使内部语言能够检查形如「元数与带标签载荷的对」的键，而无须假定集合编码的有序对具有原始投影。
<!--ja-->
すべての論理式は構成可能な台の上で解釈されます。順序対の述語と符号化されたグラフの適用述語により、集合で符号化した対に原始的な射影を仮定せず、内部言語から「アリティとタグ付きペイロードの対」というキーを調べられます。
<!--/-->

```agda
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans )
open import L.Coding.Model {ℓ} using ( prAtL; appAt )
open import L.Coding.Expressions {ℓ} using ( sucAtL )
```

<!--en-->
Nested bounded quantifiers introduce temporary witnesses at the front of an environment. Named finite slots and their shifts keep `C`, `w`, the arity, and all ten tags referring to the same values while those witnesses are unpacked.
<!--zh-->
嵌套的有界量词会在环境前端引入临时见证。具名的有穷槽位及其移位，使 `C`、`w`、元数与全部十个标签在拆解这些见证时始终指向原来的值。
<!--ja-->
入れ子の有界量化子は、環境の先頭に一時的な証人を加えます。名前付きの有限スロットとそのずらしによって、それらの証人を分解している間も、`C`、`w`、アリティ、十個すべてのタグが同じ値を指し続けます。
<!--/-->

```agda
import L.Coding.Expressions {ℓ} as CodingExpressions
module E = CodingExpressions.PairExpression
open import L.Coding.Quantification {ℓ} using
  ( i0; i1; i2; i3; i4; i5; i6; i7; i8; sh
  ; f0; f1; f2; f3; f4; f5; f6; f7; f8; f9
```

<!--en-->
Pair readers expose both components while keeping every witness bounded. A finite disjunction will then combine the ten possible outer constructors into one shape test, and the corresponding bounded universal readers will express closure for all legal inputs.
<!--zh-->
有序对读式在保持所有见证有界的同时显露两个分量。随后，一个有穷析取把十种可能的最外层构造子合成一项形状检验；相应的有界全称读式则对所有合法输入表达封闭性。
<!--ja-->
対の読みは、すべての証人を有界に保ったまま二つの成分を取り出します。その後、有限選言が十通りの最外側の構成子を一つの形の検査にまとめ、対応する有界全称の読みがすべての正当な入力について閉性を表します。
<!--/-->

```agda
  ; sndEx; sndAll; bothEx; bothAll; bigOr )

```

<!--en-->
Finite indices and set-theoretic numerals have different roles here. The map `N` names ten positions in the surrounding environment, while `toℕ` identifies which numeral from zero through nine belongs at each tag position. Shifting preserves those references when bounded witnesses extend the environment. The arity stored in an entry of `E` is not certified as a numeral at this point; that identification comes later from the environment-tower hypotheses.
<!--zh-->
有穷索引与集合论数码在这里承担不同角色。映射 `N` 指出外围环境中的十个位置，`toℕ` 则确定每个标签位置应放置零至九中的哪个数码。当有界见证扩展环境时，移位会保持这些引用不变。此处尚未认证 `E` 的条目中记录的元数是自然数码；这一认同要由后续的环境塔假设给出。
<!--ja-->
有限添字と集合論的な数項は、ここでは異なる役割をもちます。写像 `N` は周囲の環境にある十個の位置を指し、`toℕ` は各タグ位置に 0 から 9 までのどの数項を置くかを定めます。有界な証人で環境が拡張されても、位置をずらすことでこれらの参照は保たれます。この段階では、`E` の項目に記録されたアリティが自然数の数項であるとはまだ認定されません。その同定は、後の環境の塔に関する仮定から得られます。
<!--/-->

```agda
open import Cubical.Data.Nat using ( _+_ )
open import Cubical.Data.FinData using ( toℕ )
open import Cubical.Data.Unit using ( tt )
open import Cubical.Data.Vec using ( lookup )
open import Cubical.HITs.CumulativeHierarchy.Constructions
```

<!--en-->
The ten constructor tags are represented by the von Neumann numerals from zero through nine. Their numerical separation will later distinguish the two atomic relations, three binary connectives, falsity, and four quantifiers.
<!--zh-->
十个构造子标签由零至九的冯・诺伊曼数码表示。数码之间的区分将在后文辨别两个原子关系、三个二元联结词、假与四个量词。
<!--ja-->
十個の構成子タグは、0 から 9 までのフォン・ノイマン数項で表されます。数項の違いによって、後で二つの原子関係、三つの二項結合子、偽、四つの量化子を区別します。
<!--/-->

```agda
  using ( module InfinitySet )
open InfinitySet {ℓ} using ( #_ )

```

<!--en-->
Write `S` for the carrier of constructible sets. The candidate domain, its keys, the working set, and the tower entries are all elements of this one carrier when the object-language formulas are interpreted.
<!--zh-->
以 `S` 表示可构造集合的载体。解释对象语言公式时，候选域、其中的键、工作集与环境塔条目都取自这一载体。
<!--ja-->
構成可能集合の台を `S` と書きます。対象言語の論理式を解釈するとき、候補領域、そのキー、作業集合、環境の塔の要素は、すべてこの同じ台の要素です。
<!--/-->

```agda
open hPropStructure 𝒮ʟ using ( S )

```

<!--en-->
Thus the formulas constructed below can be read in finite environments of constructible elements. We begin with the smallest local question: which tagged sets count as term codes at a fixed arity?
<!--zh-->
因此，下文构造的公式可以在可构造元素组成的有限环境中读取。先从最小的局部问题开始：在固定元数处，哪些带标签集合算作词项码？
<!--ja-->
したがって、以下で作る論理式は、構成可能な要素からなる有限環境で読めます。まず最も局所的な問いから始めます。固定したアリティで、どのタグ付き集合を項の符号として認めるのでしょうか。
<!--/-->

```agda
module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans using ( _^_; _⊨ᵐ_ )
open AbsL using ( _^_ )
```

<!--en-->
## Describing shape and closure
<!--zh-->
## 描述形状与封闭性
<!--ja-->
## 形と閉性の記述
<!--/-->

<!--en-->
The term predicate accepts either a pair tagged by slot `N0` whose payload lies in the working set `w`, or a pair tagged by slot `N1` whose payload lies in the arity set `ar`. Under the intended tag assignment these are, respectively, constants and free variables. At this stage `ar` is only a set; identifying it with a natural-number numeral requires the environment-tower facts used later.
<!--zh-->
词项谓词接受两类表示：标签取槽位 `N0` 且载荷属于工作集 `w` 的对，或标签取槽位 `N1` 且载荷属于元数集合 `ar` 的对。在预期的标签赋值下，它们分别表示常元与自由变元。此处 `ar` 仍只是一个集合；要把它认同为自然数码，还需后文使用的环境塔事实。
<!--ja-->
項の述語は二種類の表示を受け入れます。スロット `N0` のタグをもちペイロードが作業集合 `w` に属する対と、スロット `N1` のタグをもちペイロードがアリティ集合 `ar` に属する対です。意図したタグの割当てのもとで、それぞれ定数と自由変数を表します。この段階の `ar` はまだ単なる集合であり、自然数の数項と同定するには後で使う環境の塔の事実が必要です。
<!--/-->

```agda
isTm : ∀ {m} → Fin m → Fin m → Fin m → Fin m → Fin m → Formula S m
isTm t ar w N0 N1 =
    sndEx t N0 (var i0 ∈̇ var (sh 2 w))
  ∨̇ sndEx t N1 (var i0 ∈̇ var (sh 2 ar))
```

<!--en-->
For a fixed payload `r`, `keyUp C ar r` says that the full key `(ar + 1, r)` belongs to `C`, where `ar + 1` is expressed by the internal successor relation. Quantifier shape clauses use this predicate for their bodies. It asserts membership of that fixed successor-arity key, without independently checking the shape of `r` or that `ar` is a numeral.
<!--zh-->
对固定载荷 `r`，`keyUp C ar r` 断言完整键 `(ar + 1, r)` 属于 `C`，其中 `ar + 1` 由内部后继关系表达。量词的形状子句用它处理主体。该谓词只断言这个固定的加一元数键属于域，并不独立检查 `r` 的形状，也不证明 `ar` 是数码。
<!--ja-->
固定したペイロード `r` に対し、`keyUp C ar r` は完全なキー `(ar + 1, r)` が `C` に属することを述べます。ここで `ar + 1` は内部の関係で表現されます。量化子の形の節は、本体についてこの述語を使います。この述語だけでは `r` の形を検査せず、`ar` が数項であることも証明しません。
<!--/-->

```agda
keyUp : ∀ {m} → Fin m → Fin m → Fin m → Formula S m
keyUp C ar r =
  ∃̇∈ (var C) (∃̇∈ (var i0) (∃̇∈ (var i0)
    (prAtL i2 i0 (sh 3 r) ∧̇ sucAtL (sh 3 ar) i0)))
```

<!--en-->
A formula key has the uniform form `(ar, (N, p))`: `ar` is its arity, `N` is its constructor tag, and `p` is its payload. The inner tagged payload `(N, p)` is formed first and is then paired with the arity. Different constructors change the structure of `p`, while leaving this outer layout fixed.
<!--zh-->
公式键统一具有 `(ar, (N, p))` 的形状：`ar` 是元数，`N` 是构造子标签，`p` 是载荷。构造时先形成内层的带标签载荷 `(N, p)`，再把它与元数配对。不同构造子改变的是 `p` 的结构，而最外层布局保持不变。
<!--ja-->
論理式キーは一様に `(ar, (N, p))` という形をもちます。`ar` はアリティ、`N` は構成子タグ、`p` はペイロードです。まず内側のタグ付きペイロード `(N, p)` を作り、次にそれをアリティと対にします。構成子ごとに変わるのは `p` の構造であり、この外側の配置は共通です。
<!--/-->

```agda
keyExpr : ∀ {m} → Fin m → Fin m → E.Expr m → E.Expr m
keyExpr ar N p = E.pair (E.slot ar) (E.pair (E.slot N) p)

```

<!--en-->
For either atomic relation, the payload has the form `((Nx, x), (Ny, y))`. Each inner pair records both the kind of term and its payload, so the left and right terms may independently be constants or variables while the atomic formula keeps one uniform key shape.
<!--zh-->
对任一原子关系，载荷都具有 `((Nx, x), (Ny, y))` 的形状。每个内层对同时记录词项的种类与载荷，因此左右词项可以分别取常元或变元，而原子公式仍保持统一的键形状。
<!--ja-->
どちらの原子関係でも、ペイロードは `((Nx, x), (Ny, y))` という形です。各内側の対は項の種類とそのペイロードをともに記録するので、左右の項はそれぞれ独立に定数または変数となりながら、原子論理式は一様なキーの形を保てます。
<!--/-->

```agda
atomKeyExpr : ∀ {m} → Fin m → Fin m → Fin m → Fin m → Fin m → Fin m → E.Expr m
atomKeyExpr ar N Nx x Ny y = keyExpr ar N
  (E.pair (E.pair (E.slot Nx) (E.slot x))
    (E.pair (E.slot Ny) (E.slot y)))

```

<!--en-->
A bounded-quantifier payload pairs a tagged bound term `(Nx, x)` with a body payload `a`. The surrounding key records the current arity; a separate `keyUp` condition is what requires the full key `(arity + 1, a)` for the body to lie in the domain.
<!--zh-->
有界量词载荷把带标签界词项 `(Nx, x)` 与主体载荷 `a` 配成一对。外围键记录当前元数；另行给出的 `keyUp` 条件才要求主体的完整键 `(元数 + 1, a)` 属于定义域。
<!--ja-->
有界量化子のペイロードは、タグ付きの上界項 `(Nx, x)` と本体のペイロード `a` を対にします。外側のキーが現在のアリティを記録し、別の `keyUp` 条件が、本体の完全なキー `(アリティ + 1, a)` が領域に属することを要求します。
<!--/-->

```agda
bndKeyExpr : ∀ {m} → Fin m → Fin m → Fin m → Fin m → Fin m → E.Expr m
bndKeyExpr ar N Nx x a = keyExpr ar N
  (E.pair (E.pair (E.slot Nx) (E.slot x)) (E.slot a))
```

<!--en-->
The first membership template says that a nested pair `(ar, (N, a))` lies in the candidate domain. It merely records this set membership; whether `N` is the tag of an appropriate unary constructor and whether `a` is a legal constituent are conditions imposed by the surrounding clause.
<!--zh-->
第一个隶属模板断言嵌套对 `(ar, (N, a))` 属于候选域。它只记录这项集合隶属；`N` 是否是适当的一元构造子标签、`a` 是否为合法组成部分，都由外围子句另行规定。
<!--ja-->
最初の所属テンプレートは、入れ子の対 `(ar, (N, a))` が候補領域に属することを述べます。ここで記録するのは集合への所属だけです。`N` が適切な一項構成子のタグであることや、`a` が正当な構成要素であることは、外側の節が別に課します。
<!--/-->

```agda
unKey : ∀ {m} → Fin m → Fin m → Fin m → Fin m → Formula S m
unKey C ar N a = E.member (keyExpr ar N (E.slot a)) (var C)
```

<!--en-->
The binary template replaces the unary payload by the pair `(a, b)`. Later clauses use it for conjunction, disjunction, and implication after separately requiring both same-arity subkeys to belong to `C`.
<!--zh-->
二元模板把一元载荷换成对 `(a, b)`。后文先另行要求两个同元数子键属于 `C`，再用这个模板处理合取、析取与蕴涵。
<!--ja-->
二項テンプレートは、一項のペイロードを対 `(a, b)` に置き換えます。後の節では、同じアリティの二つの部分キーが `C` に属することを別に要求したうえで、このテンプレートを論理積、論理和、含意に使います。
<!--/-->

```agda
binKey : ∀ {m} → Fin m → Fin m → Fin m → Fin m → Fin m → Formula S m
binKey C ar N a b = E.member (keyExpr ar N (E.pair (E.slot a) (E.slot b))) (var C)
```

<!--en-->
The atomic template puts two tagged term payloads into the key. Membership in `C` is again the only assertion made here; the atomic shape and closure clauses supply the term bounds and select tag zero or one for the outer relation.
<!--zh-->
原子模板把两个带标签词项载荷放入键中。这里仍然只断言其属于 `C`；原子的形状与闭包子句会给出词项的界，并为最外层关系选择标签零或一。
<!--ja-->
原子テンプレートは、二つのタグ付き項ペイロードをキーに入れます。ここでも主張するのは `C` への所属だけです。原子の形と閉性の節が項の境界を与え、最外側の関係にタグ 0 または 1 を選びます。
<!--/-->

```agda
atomKey : ∀ {m} → Fin m → Fin m → Fin m → Fin m → Fin m → Fin m → Fin m → Formula S m
atomKey C ar N Nx x Ny y = E.member (atomKeyExpr ar N Nx x Ny y) (var C)
```

<!--en-->
A bounded quantifier differs from an unbounded one by carrying a bound term as well as a body. Its payload `((Nx, x), a)` records the tagged bound term and the body payload, but this membership template alone asserts no legality. The surrounding shape condition checks the term at the current arity and the full body key at the successor arity; the closure condition uses the same two constituents in the generating direction.
<!--zh-->
有界量词与无界量词的区别在于，它除主体外还携带一个界词项。载荷 `((Nx, x), a)` 记录带标签的界词项与主体载荷，但这个隶属模板本身并不断言二者合法。外围形状条件检查词项在当前元数处合法，并检查主体的完整键位于后继元数处；闭包条件则沿生成方向使用同样两个组成部分。
<!--ja-->
有界量化子は、本体に加えて境界を表す項も運ぶ点で非有界量化子と異なります。ペイロード `((Nx, x), a)` はタグ付きの境界項と本体のペイロードを記録しますが、この所属テンプレートだけでは両者の正当性を主張しません。外側の形の条件が、項を現在のアリティで、本体の完全なキーを後続アリティで検査します。閉性の条件は、同じ二つの構成要素を生成する向きに用います。
<!--/-->

```agda
bndKey : ∀ {m} → Fin m → Fin m → Fin m → Fin m → Fin m → Fin m → Formula S m
bndKey C ar N Nx x a = E.member (bndKeyExpr ar N Nx x a) (var C)
```

<!--en-->
The tag agreement says that the ten slots carry exactly the numerals zero through nine, each slot matched to its position. This is what lets every later formula refer to "the tag of the membership atom" and mean the same slot everywhere.
<!--zh-->
标签一致要求十个槽位恰取数码零至九，每个槽位对应其位置。正因如此，后文每个公式说「隶属原子的标签」时，指的都是同一个槽位。
<!--ja-->
タグの一致は、十の枠がちょうど数項の 0 から 9 を運ぶことを要求します。それぞれの枠がその位置に対応します。これにより、後のどの論理式も「所属のアトムのタグ」と言えば、常に同じ枠を指します。
<!--/-->

```agda
Tags : ∀ {m} (γ : S ^ m) (N : Fin 10 → Fin m) → Type (ℓ-suc ℓ)
Tags γ N = (k : Fin 10) → fst (lookup (N k) γ) ≡ # (toℕ k)

```

<!--en-->
When a formula is read in an environment extended by bound variables, the ten tag slots shift with the environment; the shifted naming keeps every clause aligned with the same tags.
<!--zh-->
当公式在添入受界变元后的环境中读取时，十个标签槽位随环境移位；移位后的命名使每条子句仍与相同的标签对齐。
<!--ja-->
論理式を、束縛変数が加わった環境のもとで読むときは、十のタグの枠も環境とともにずれます。ずらされた名前付けによって、すべての節が同じタグと整列し続けます。
<!--/-->

```agda
shN : ∀ {m} (j : ℕ) → (Fin 10 → Fin m) → Fin 10 → Fin (j + m)
shN j N k = sh j (N k)
```

<!--en-->
We can now ask the inward question for a member of the candidate domain: which evidence makes its payload one of the permitted constructor forms? Although there are ten constructor tags, only five kinds of payload condition are needed, because the two atomic relations, the three binary connectives, the two unbounded quantifiers, and the two bounded quantifiers share their respective component patterns.
<!--zh-->
现在可以对候选域的成员提出向内的问题：什么证据表明其载荷属于允许的构造子形状之一？虽然构造子标签共有十个，载荷条件却只需分成五类，因为两个原子关系、三个二元联结词、两个无界量词与两个有界量词分别共用各自的组成模式。
<!--ja-->
ここで、候補領域の要素を内向きに読む問いを立てられます。そのペイロードが許された構成子形の一つであることを、どのような証拠が示すのでしょうか。構成子タグは十個ありますが、必要なペイロード条件は五種類だけです。二つの原子関係、三つの二項結合子、二つの非有界量化子、二つの有界量化子が、それぞれ同じ構成要素の形を共有するからです。
<!--/-->

```agda
module Shape {m : ℕ} (C w : Fin m) (N : Fin 10 → Fin m) where
  private
    C9 w9 : Fin (9 + m)
    C9 = sh 9 C
    w9 = sh 9 w
```

<!--en-->
The five payload shapes are written out. Atomic payloads demand two legal terms; binary payloads demand two same-arity subkeys already in the domain; the falsity payload is the numeral zero; and the unbounded-quantifier payload demands a body key at the successor arity.
<!--zh-->
五种载荷形状被写出。原子载荷要求两个合法词项；二元载荷要求两个已在定义域中的同元数子键；假值的载荷是数码零；无界量词载荷要求后继元数处的主体键。
<!--ja-->
五つのペイロードの形が書き出されます。アトムのペイロードは二つの正当な項を要求し、二項のペイロードは、すでに定義域にある同じアリティの二つの部分キーを要求します。偽のペイロードは数項ゼロであり、非有界の量化子のペイロードは後続のアリティでの本体のキーを要求します。
<!--/-->

```agda

  atomPay binPay conPay quPay bqPay : Formula S (9 + m)
  atomPay = bothEx i0 (isTm i1 i8 (sh 12 w) (sh 12 (N f0)) (sh 12 (N f1)) ∧̇ isTm i0 i8 (sh 12 w) (sh 12 (N f0)) (sh 12 (N f1)))
  binPay  = bothEx i0 (appAt (sh 12 C) i8 i1 ∧̇ appAt (sh 12 C) i8 i0)
  conPay  = var i0 ≐ var (sh 9 (N f0))
  quPay   = keyUp C9 i5 i0
```

<!--en-->
For a bounded quantifier, the payload contains a legal bound term at the current arity and a body payload whose full key belongs to the domain at arity increased by one. The conjunction records both obligations; it does not choose a decoded body formula.
<!--zh-->
对有界量词，载荷包含当前元数处的合法界词项，以及一个主体载荷，而该主体在元数加一处的完整键须属于定义域。合取同时记录这两项义务，但不会选出一条解码后的主体公式。
<!--ja-->
有界量化子のペイロードには、現在のアリティで正当な上界項と、アリティを一つ増やした位置で完全なキーが領域に属する本体ペイロードが入ります。連言はこの二つの条件をともに記録しますが、復号された本体論理式を選び出すものではありません。
<!--/-->

```agda
  bqPay   = bothEx i0 (isTm i1 i8 (sh 12 w) (sh 12 (N f0)) (sh 12 (N f1)) ∧̇ keyUp (sh 12 C) i8 i0)
```

<!--en-->
The first four tags separate the two atomic relations and the first two binary connectives: tag zero is membership, tag one is equality, tag two is conjunction, and tag three is disjunction. The first pair shares the atomic payload condition, while the second pair shares the binary one; their distinct numerals still retain the outer constructor.
<!--zh-->
前四个标签区分两个原子关系与前两个二元联结词：标签零是隶属，标签一是相等，标签二是合取，标签三是析取。前一对共用原子载荷条件，后一对共用二元载荷条件；不同数码仍然保留了最外层构造子的区别。
<!--ja-->
最初の四つのタグは、二つの原子関係と最初の二つの二項結合子を区別します。タグ 0 は所属、タグ 1 は等号、タグ 2 は論理積、タグ 3 は論理和です。最初の二つは同じ原子ペイロード条件を使い、次の二つは同じ二項ペイロード条件を使いますが、数項の違いによって最外側の構成子は区別されたままです。
<!--/-->

```agda
  payN : ℕ → Formula S (9 + m)
  payN 0 = atomPay
  payN 1 = atomPay
  payN 2 = binPay
  payN 3 = binPay
```

<!--en-->
Tag four is implication, tag five is falsity, tags six and seven are the unbounded existential and universal quantifiers, and tag eight is the bounded universal quantifier. Their payload conditions are, respectively, two same-arity subkeys, the fixed numeral zero, a body key at the successor arity, and a current-arity bound term together with such a body.
<!--zh-->
标签四是蕴涵，标签五是假，标签六与七分别是无界存在量词和无界全称量词，标签八是有界全称量词。相应载荷条件依次为两个同元数子键、固定数码零、后继元数处的主体键，以及当前元数处的界词项与这种主体的组合。
<!--ja-->
タグ 4 は含意、タグ 5 は偽、タグ 6 と 7 はそれぞれ非有界存在量化子と非有界全称量化子、タグ 8 は有界全称量化子です。対応するペイロード条件は順に、同じアリティの二つの部分キー、固定された数項 0、後続アリティにある本体キー、そして現在のアリティにある境界項とそのような本体の組です。
<!--/-->

```agda
  payN 4 = binPay
  payN 5 = conPay
  payN 6 = quPay
  payN 7 = quPay
  payN 8 = bqPay
```

<!--en-->
Tag nine is the bounded existential quantifier and uses the same bounded-quantifier payload condition as tag eight. The final equation makes `payN` total on natural numbers by returning falsity above nine; since `pay` calls it only through an index in `Fin 10`, that fallback is unreachable in the ten-way shape test.
<!--zh-->
标签九是有界存在量词，与标签八共用有界量词载荷条件。末条等式在九以上返回假，使 `payN` 成为自然数上的全函数；由于 `pay` 只通过 `Fin 10` 中的索引调用它，这个后备分支不会出现在十路形状检验中。
<!--ja-->
タグ 9 は有界存在量化子で、タグ 8 と同じ有界量化子のペイロード条件を使います。最後の等式は 9 より大きい入力で偽を返し、`payN` を自然数上の全域関数にします。`pay` は `Fin 10` の添字を通してしかこれを呼ばないので、この予備の分岐は十通りの形の検査では到達しません。
<!--/-->

```agda
  payN 9 = bqPay
  payN (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc _)))))))))) = ⊥̇

```

<!--en-->
At this point every one of the ten tags has a payload test. The next step is to connect the test indexed by `k` with an actual tagged payload, and then combine all ten indexed alternatives into the shape condition.
<!--zh-->
至此，十个标签各自都有对应的载荷检验。下一步要把由 `k` 索引的检验与实际的带标签载荷联系起来，再把十个索引分支合成形状条件。
<!--ja-->
これで十個のタグのそれぞれにペイロードの検査が対応しました。次は、`k` で添字づけられた検査を実際のタグ付きペイロードと結び、その十通りの選択肢を形の条件へまとめます。
<!--/-->

```agda
  pay : Fin 10 → Formula S (9 + m)
  pay k = payN (toℕ k)
```

<!--en-->
For a chosen constructor index `k`, the outer payload is required to split as `(N k, r)`, and the remaining component `r` must satisfy the payload condition for that tag. The arity has already been exposed by the surrounding shape formula; this clause decomposes the tagged payload, rather than quantifying over a member of the arity.
<!--zh-->
对选定的构造子索引 `k`，最外层载荷必须分解为 `(N k, r)`，余下分量 `r` 则须满足该标签的载荷条件。元数已由外围形状公式显露；本子句拆解的是带标签载荷，而不是在元数的成员上作量化。
<!--ja-->
選んだ構成子添字 `k` に対し、外側のペイロードは `(N k, r)` と分解され、残りの成分 `r` はそのタグのペイロード条件を満たさなければなりません。アリティは外側の形の論理式ですでに取り出されています。この節が分解するのはタグ付きペイロードであり、アリティの要素を量化するのではありません。
<!--/-->

```agda
  at : Fin 10 → Formula S (7 + m)
  at k = sndEx i0 (sh 7 (N k)) (pay k)

```

<!--en-->
The ten shape clauses are collected into one finite disjunction. Thus a single formula states that the tagged payload matches at least one of the ten constructor shapes, without introducing an additional unbounded quantifier.
<!--zh-->
十条形状子句被收集为一个有穷析取。因此，单一公式便能陈述带标签载荷至少匹配十种构造子形状之一，而无须引入额外的无界量词。
<!--ja-->
十個の形の節は、一つの有限選言にまとめられます。したがって、一つの論理式だけで、タグ付きペイロードが十種類の構成子形の少なくとも一つに合うことを述べられ、追加の非有界量化子は導入されません。
<!--/-->

```agda
  ten : Formula S (7 + m)
  ten = bigOr 9 at
```

<!--en-->
The shape half starts from each existing member `c` of the candidate domain. It chooses an entry `(ar, F)` from `E`, decomposes `c` as `(ar, p)`, and requires `p` to match one of the ten tagged payload shapes. Composite shapes already require their immediate formula subkeys to lie in `C`. Semantically, these bounded existential witnesses are propositionally truncated, so this condition supplies no chosen decomposition and asserts no uniqueness of decoding.
<!--zh-->
形状半边从候选域中每个已有成员 `c` 出发。它从 `E` 选择条目 `(ar, F)`，把 `c` 分解为 `(ar, p)`，并要求 `p` 匹配十种带标签载荷形状之一。复合形状已经要求其直接公式子键属于 `C`。在语义解释中，这些有界存在见证经过命题截断，因此该条件既不提供选定的分解，也不声称解码唯一。
<!--ja-->
形の半分は、候補領域の既存要素 `c` ごとに出発します。`E` から要素 `(ar, F)` を取り、`c` を `(ar, p)` と分解し、`p` が十通りのタグ付きペイロード形のいずれかに合うことを要求します。複合形では、直下の論理式部分キーがすでに `C` に属することも要求されます。意味論では、これらの有界存在の証人は命題的切り詰めのもとにあるため、この条件は選ばれた分解を与えず、復号の一意性も主張しません。
<!--/-->

```agda
shapeAt : ∀ {m} → Fin m → Fin m → Fin m → (Fin 10 → Fin m) → Formula S m
shapeAt C w E N =
  ∀̇∈ (var C) (∃̇∈ (var (sh 1 E)) (bothEx i0 (sndEx i4 i1 (Shape.ten C w N))))
```

<!--en-->
The second half turns to the outward question. Fix an entry of `E` and use its first component as the common arity. The closure clauses state which compound keys must enter `C` whenever their terms are legal at that arity and their immediate formula keys already belong to `C` at the required current or successor arity.
<!--zh-->
第二个半边转向向外的问题。固定 `E` 的一个条目，并把其第一分量作为共同元数。闭包子句陈述：只要词项在该元数处合法，且直接公式键已在所需的当前元数或后继元数处属于 `C`，哪些复合键就必须进入 `C`。
<!--ja-->
後半では、外向きの問いへ移ります。`E` の項目を一つ固定し、その第一成分を共通のアリティとして使います。閉性の各節は、項がそのアリティで正当であり、直下の論理式キーが必要な現在または後続のアリティですでに `C` に属するとき、どの複合キーが `C` に入らなければならないかを述べます。
<!--/-->

```agda
module Close {m : ℕ} (C w : Fin m) (N : Fin 10 → Fin m) where
  private
    C4 w4 : Fin (4 + m)
    C4 = sh 4 C
    w4 = sh 4 w
```

<!--en-->
An atomic generation clause fixes an outer relation tag and one tag for each term. It ranges the two payloads over the corresponding bounds `X` and `Y`, then places the resulting atomic key in `C`. The eight later instances choose each term tag as constant or variable and choose `X` and `Y` as the working set or the current arity.
<!--zh-->
一条原子生成子句固定最外层关系标签，并为两个词项各固定一个标签。它让两个载荷分别在界 `X` 与 `Y` 中取值，再要求所得原子键属于 `C`。后面的八个实例让每个词项标签在常元与变元之间选择，并相应把 `X`、`Y` 取为工作集或当前元数。
<!--ja-->
原子の生成節は、最外側の関係タグと二つの項それぞれのタグを固定します。二つのペイロードを対応する境界 `X` と `Y` の中で動かし、得られる原子キーを `C` に入れます。後の八つの具体例では、各項のタグを定数または変数から選び、それに応じて `X` と `Y` を作業集合または現在のアリティにします。
<!--/-->

```agda
  atomClose : (k Nx Ny : Fin 10) (X : Fin (4 + m)) (Y : Fin (5 + m)) → Formula S (4 + m)
  atomClose k Nx Ny X Y =
    ∀̇∈ (var X) (∀̇∈ (var Y) (atomKey (sh 6 C) i3 (sh 6 (N k)) (sh 6 (N Nx)) i1 (sh 6 (N Ny)) i0))

```

<!--en-->
Binary closure demands that any two same-arity members of the domain generate the key of each binary connective applied to them.
<!--zh-->
二元闭包要求：定义域中任意两个同元数成员生成以其为子键的每个二元联结词的键。
<!--ja-->
二項の閉性は、定義域の同じアリティの任意の二つの要素が、それらを部分キーとする各二項の結合子のキーを生成することを要求します。
<!--/-->

```agda
  binClose : (k : Fin 10) → Formula S (4 + m)
  binClose k =
    ∀̇∈ (var C4) (sndAll i0 i2 (∀̇∈ (var (sh 7 C)) (sndAll i0 i5 (binKey (sh 10 C) i7 (sh 10 (N k)) i3 i0))))

```

<!--en-->
Falsity closure places the key of the falsity symbol, with its zero payload, into the domain.
<!--zh-->
假值闭包把带零载荷的假符号之键放入定义域。
<!--ja-->
偽の閉性は、ゼロのペイロードをもつ偽の記号のキーを、定義域の中に置きます。
<!--/-->

```agda
  conClose : (k : Fin 10) → Formula S (4 + m)
  conClose k = unKey C4 i1 (sh 4 (N k)) (sh 4 (N f0))
```

<!--en-->
For an unbounded quantifier, take any member of `C` that decomposes as a body key at arity `ar + 1`. The clause then requires the corresponding quantified key at arity `ar` to belong to `C`. This is the generating direction from an existing immediate constituent to the compound formula.
<!--zh-->
对无界量词，任取 `C` 中一个可分解为元数 `ar + 1` 处主体键的成员。该子句随即要求元数 `ar` 处相应的量化公式键属于 `C`。这是从已有直接组成部分到复合公式的生成方向。
<!--ja-->
非有界量化子について、`C` の任意の要素がアリティ `ar + 1` の本体キーとして分解されるとします。この節は、対応する量化されたキーがアリティ `ar` で `C` に属することを要求します。これは既存の直下の構成要素から複合論理式へ進む生成方向です。
<!--/-->

```agda
  quClose : (k : Fin 10) → Formula S (4 + m)
  quClose k = ∀̇∈ (var C4) (bothAll i0 (sucAtL i5 i1 ⇒̇ unKey (sh 8 C) i5 (sh 8 (N k)) i0))

```

<!--en-->
The bounded-quantifier clause adds a bound term at the current arity. Once a member of `C` is recognized as a body key at arity `ar + 1`, every payload in the chosen term bound `X` generates the bounded-quantifier key at arity `ar`; later instances choose the constant and variable cases separately.
<!--zh-->
有界量词子句再加入当前元数处的界词项。一旦 `C` 的某个成员被认作元数 `ar + 1` 处的主体键，所选词项界 `X` 中的每个载荷都会在元数 `ar` 处生成有界量词键；后面的实例分别选择常元与变元情形。
<!--ja-->
有界量化子の節は、現在のアリティに上界項を加えます。`C` の要素がアリティ `ar + 1` の本体キーと認められると、選んだ項の境界 `X` の各ペイロードから、アリティ `ar` の有界量化子キーが生成されます。後の具体例が定数と変数の場合を分けて選びます。
<!--/-->

```agda
  bqClose : (k Nx : Fin 10) (X : Fin (8 + m)) → Formula S (4 + m)
  bqClose k Nx X =
    ∀̇∈ (var C4) (bothAll i0 (sucAtL i5 i1 ⇒̇ ∀̇∈ (var X) (bndKey (sh 9 C) i6 (sh 9 (N k)) (sh 9 (N Nx)) i0 i1)))
```

<!--en-->
The closure conjunction opens with the eight atomic clauses: two atomic symbols with two term slots each, every slot being either a constant or a variable, give eight combinations.
<!--zh-->
闭包合取以八条原子子句开场：两个原子符号各有两个词项槽，每槽取常元或变元，共八种组合。
<!--ja-->
閉性の連言は、八つのアトムの節から始まります。二つのアトムの記号がそれぞれ二つの項の枠をもち、各枠が定数か変数のどちらかを取るので、八通りの組み合わせになります。
<!--/-->

```agda
  all : Formula S (4 + m)
  all =
      atomClose f0 f0 f0 w4 (sh 1 w4) ∧̇ (atomClose f0 f0 f1 w4 i2
    ∧̇ (atomClose f0 f1 f0 i1 (sh 1 w4) ∧̇ (atomClose f0 f1 f1 i1 i2
    ∧̇ (atomClose f1 f0 f0 w4 (sh 1 w4) ∧̇ (atomClose f1 f0 f1 w4 i2
```

<!--en-->
The conjunction continues with the last two atomic clauses, completing all four term-shape combinations for equality. It then adds three binary clauses, one falsity clause, two unbounded-quantifier clauses, and four bounded-quantifier clauses. Thus the complete count is eight atomic, three binary, one falsity, two unbounded, and four bounded clauses, for eighteen in total.
<!--zh-->
这个合取先接上最后两条原子子句，从而补全相等原子的四种词项形状组合；随后加入三条二元子句、一条假子句、两条无界量词子句与四条有界量词子句。因此总数是八条原子、三条二元、一条假、两条无界与四条有界子句，合计十八条。
<!--ja-->
この連言は最後の二つの原子節から続き、等号原子について四通りの項の形を完成させます。その後に、三つの二項節、一つの偽の節、二つの非有界量化子の節、四つの有界量化子の節を加えます。したがって内訳は、原子が八、二項が三、偽が一、非有界が二、有界が四で、合計十八節です。
<!--/-->

```agda
    ∧̇ (atomClose f1 f1 f0 i1 (sh 1 w4) ∧̇ (atomClose f1 f1 f1 i1 i2
    ∧̇ (binClose f2 ∧̇ (binClose f3 ∧̇ (binClose f4
    ∧̇ (conClose f5 ∧̇ (quClose f6 ∧̇ (quClose f7
    ∧̇ (bqClose f8 f0 (sh 8 w) ∧̇ (bqClose f8 f1 i5
    ∧̇ (bqClose f9 f0 (sh 8 w) ∧̇ bqClose f9 f1 i5))))))))))))))))
```

<!--en-->
The closure half applies all eighteen generation clauses at every entry of the set named by `E`. Once an entry is unpacked, its first component supplies the common arity for the constructors. This formula does not certify that the entries form the canonical environment tower or even that every recorded arity is a numeral; later hypotheses provide those facts. At any valid tower entry, the direction remains from legal constituents to the corresponding compound key, rather than from an arbitrary member of `C` back to its parts.
<!--zh-->
闭包半边在 `E` 所指集合的每个条目处施加全部十八条生成子句。条目拆开后，其第一分量为各构造规则提供共同元数。这个公式并不认证这些条目构成典范环境塔，甚至不认证每个记录元数都是自然数码；这些事实由后续假设提供。在任一合法塔条目处，其方向始终是由合法组成部分生成相应复合键，而不是从 `C` 的任意成员反向恢复其组成部分。
<!--ja-->
閉性の半分は、`E` が指す集合の各項目で十八の生成節すべてを課します。項目を分解すると、その第一成分が各構成規則に共通のアリティを与えます。この論理式だけでは、それらの項目が正準な環境の塔をなすことも、記録された各アリティが自然数の数項であることも認定しません。それらの事実は後の仮定から与えられます。正しい塔の項目では、向きは常に正当な構成要素から対応する複合キーへ進み、`C` の任意の要素からその部分へ戻る向きではありません。
<!--/-->

```agda

closeAt : ∀ {m} → Fin m → Fin m → Fin m → (Fin 10 → Fin m) → Formula S m
closeAt C w E N = ∀̇∈ (var E) (bothAll i0 (Close.all C w N))

```

<!--en-->
The full description conjoins the two directions. `shapeAt` reads every existing member inward and requires its immediate subkeys to remain in the candidate domain; `closeAt` starts with legal constituents and generates the corresponding compound key. Either condition alone is insufficient: shape alone may omit genuine keys, while closure alone may permit additional members. The conjunction is still only a specification relative to `w`, `E`, and `N`; it does not by itself construct the domain or prove it is the canonical one.
<!--zh-->
完整描述合取两个方向。`shapeAt` 从每个已有成员向内读取，并要求其直接子键仍在候选域中；`closeAt` 则从合法组成部分出发，生成相应的复合键。任一条件单独都不够：只有形状条件时可能漏掉真实键，只有闭包条件时可能容许额外成员。这个合取仍只是相对于 `w`、`E` 与 `N` 的规格；它自身既不构造码域，也不证明码域就是典范集合。
<!--ja-->
記述全体は二つの方向を連言します。`shapeAt` は既存の各要素を内向きに読み、その直下の部分キーが候補領域に残ることを要求します。`closeAt` は正当な構成要素から出発し、対応する複合キーを生成します。どちらか一方だけでは足りません。形だけでは真正なキーを欠くことがあり、閉性だけでは余分な要素を許すことがあります。この連言はなお `w`、`E`、`N` に相対的な仕様にすぎず、それ自体で領域を構成したり、正準な領域との一致を証明したりはしません。
<!--/-->

```agda
codesAt : ∀ {m} → Fin m → Fin m → Fin m → (Fin 10 → Fin m) → Formula S m
codesAt C w E N = shapeAt C w E N ∧̇ closeAt C w E N

```

<!--en-->
The final computation produces a certificate that every quantifier in `codesAt` is bounded, so `codesAt` lies in the class `Δ₀`. This is a classification of the object-language formula that describes the candidate domain. It neither classifies individual codes as `Δ₀` objects nor by itself proves existence, canonicity, or an absoluteness theorem for the described domain.
<!--zh-->
最后的计算给出一份证书，确认 `codesAt` 中每个量词都有界，因而 `codesAt` 属于 `Δ₀` 类。这是对描述候选域的对象语言公式所作的分类；它既不是把单个码分类为 `Δ₀` 对象，也不会单独证明所描述码域的存在性、典范性或绝对性定理。
<!--ja-->
最後の計算は、`codesAt` のすべての量化子が有界であるという証明を与えるので、`codesAt` は `Δ₀` クラスに属します。これは候補領域を記述する対象言語の論理式についての分類です。個々の符号を `Δ₀` の対象として分類するものではなく、記述された領域の存在、正準性、絶対性の定理をそれだけで証明するものでもありません。
<!--/-->

```agda
Δ₀-codesAt : ∀ {m} (C w E : Fin m) (N : Fin 10 → Fin m) → Δ₀ (codesAt C w E N)
Δ₀-codesAt C w E N = checkΔ₀ (codesAt C w E N) tt
```

<!--en-->
## Recap

The candidate-domain specification has two complementary directions. `shapeAt` reads each existing member as one of ten tagged constructor forms and requires every immediate formula subkey demanded by that form to lie in `C`; `closeAt` packages eighteen generation clauses that build the corresponding keys from legal terms and existing current- or successor-arity subkeys. Their conjunction is a bounded specification relative to `w`, `E`, and `N`.

The semantic witnesses hidden by its bounded existentials are available only under propositional truncation, so the specification selects neither a decomposition nor a decoding function. In the next chapter, the correct alphabet, tag, and environment-tower hypotheses, together with excluded middle, support two separate adequacy arguments: every candidate member merely decodes to a genuine formula key, and induction on external formulas places every genuine key in the candidate domain. External injectivity can then show that two recovered formulas of one fixed arity agree, but that separate result does not make `codesAt` a chosen or globally unique syntax decoder.
<!--zh-->
## 小结

候选码域规格包含两个互补方向。`shapeAt` 把每个已有成员读成十种带标签构造形状之一，并要求该形状所需的每个直接公式子键都属于 `C`；`closeAt` 则把十八条生成子句打包起来，由合法词项与当前元数或后继元数处已有的子键构造相应公式键。二者的合取是相对于 `w`、`E` 与 `N` 的有界规格。

有界存在量词隐藏的语义见证只能在命题截断下取得，因此这份规格既不选定分解，也不给出解码函数。下一章将在正确的字母表、标签与环境塔假设以及排中律下分别证明两项充分性结论：候选域的每个成员纯粹地可解码为真实公式键，而对外部公式作归纳则把每个真实键放入候选域。外部编码的单射性随后可以证明固定元数下恢复出的两条公式相同，但这一独立结果并不会使 `codesAt` 成为选定的或全局唯一的句法解码器。
<!--ja-->
## まとめ

候補符号領域の仕様には、相補的な二つの向きがあります。`shapeAt` は既存の各要素を十種類のタグ付き構成子形の一つとして読み、その形が必要とする直下の論理式キーがすべて `C` に属することを要求します。`closeAt` は十八の生成節をまとめ、正当な項と、現在または後続のアリティにある既存の部分キーから、対応する論理式キーを構成します。両者の連言は、`w`、`E`、`N` に相対的な有界仕様です。

有界存在量化子が隠す意味論的な証人は命題的切り詰めのもとでしか得られないため、この仕様は分解も復号関数も選びません。次章では、正しいアルファベット、タグ、環境の塔に関する仮定と排中律のもとで、二つの妥当性の議論を別々に行います。候補領域の各要素は真正な論理式キーへ単に復号でき、外部の論理式に関する帰納法はすべての真正なキーを候補領域へ入れます。その後、外部符号化の単射性から、固定した一つのアリティで復元された二つの論理式が一致することは示せますが、この別の結果によって `codesAt` が選択された、または大域的に一意な構文復号器になるわけではありません。
<!--/-->
