<!--en-->
# Pinning recursion on a subcode-closed domain

Fix an index set of hierarchy codes that is closed under the immediate formula subcodes demanded by each recognized constructor shape. Assume also that the carrier slot, tag slots, and environment tower have their canonical meanings and that the table satisfies the complete table specification. The first half of this chapter then proves a local uniqueness statement: whenever a known formula key belongs to the index set and a table entry is supplied at that key, the entry's underlying set is the recursively defined satisfaction set. Independently of closure, the second half builds the table clauses from explicit carrier, tag, tower, value-agreement, decoding, totality, and domain hypotheses. Neither direction produces a globally chosen satisfaction function.
<!--zh-->
# 在对子码封闭的定义域上钉扎递归

固定一个由层级码组成的索引集，并要求它对每个已识别构造子形状所需的直接公式子码封闭；另假设载体槽、各标签槽与环境塔具有典范含义，且表满足完整的表规格。本章前半部分由此证明一条局部唯一性结论：只要一条已知公式的键属于该索引集，且该键处给定一个表项，该表项的底层集合就等于递归定义的满足关系集合。后半部分不使用封闭性，而从显式给定的载体、标签、环境塔、取值相符性、解码、全定义性与定义域假设构造表子句。两个方向都不会产生一个全局选定的满足关系函数。
<!--ja-->
# 部分符号で閉じた領域上で再帰を固定する

階層の符号からなる添字集合を固定し、認識された各構成子の形が要求する直下の論理式部分符号について閉じていると仮定します。さらに、台のスロット、タグの各スロット、環境の塔が標準的な意味をもち、表が完全な表仕様を満たすと仮定します。すると本章の前半は局所的な一意性を示します。既知の論理式のキーがその添字集合に属し、そのキーで表項目が与えられていれば、その項目の基礎集合は再帰的に定義された充足関係集合に等しくなります。後半は閉性を用いず、台、タグ、環境の塔、値の一致、復号、全域性、領域について明示された仮定から表の各節を組み立てます。どちらの向きも、大域的に選ばれた充足関係関数を与えるものではありません。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

```

<!--en-->
The argument is carried out relative to an explicit instance of excluded middle. Classical logic supports the imported constructions of satisfaction sets, environment sets, and tables, but it does not remove propositional truncation: a decoded formula or a child table value may still be known only to exist.
<!--zh-->
论证相对于一个显式给定的排中律实例进行。经典逻辑支撑所引入的满足关系集合、环境集与表的构造，但不会消除命题截断：解码所得的公式或子公式处的表值仍可能只被知道存在。
<!--ja-->
議論は、明示的に与えた排中律の実例に相対して進みます。古典論理は、導入済みの充足関係集合、環境集合、表の構成を支えますが、命題的切り詰めを取り除くわけではありません。復号された論理式や子論理式の表の値は、存在だけが分かる場合があります。
<!--/-->

```agda
open import Base.Prelude
open import Base.Classical using ( LEM )

```

<!--en-->
The module fixes the universe level and names the classical hypothesis: every theorem below records exactly which level instance of excluded middle it consumes.
<!--zh-->
模块固定宇宙层级并命名经典假设：下文每条定理都准确记录它消耗哪个层级的排中律实例。
<!--ja-->
モジュールは宇宙レベルを固定し、古典的な仮定に名前を与えます。以下の各定理は、どのレベルの排中律の実例を消費するかを正確に記録します。
<!--/-->

```agda
module L.Coding.PinnedRecursion {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

```

<!--en-->
Structural recursion follows the ten constructors of the formula grammar: membership and equality atoms, conjunction, disjunction, implication, falsity, the two unbounded quantifiers, `∀[]-syntax`, and `∃[]-syntax`. Constant relabelling lets the same syntactic tree be read first over the member alphabet of a carrier and then over the constructible carrier, without changing its constructor structure.
<!--zh-->
结构递归沿公式文法的十个构造子进行：隶属与相等原子式、合取、析取、蕴含、假、两个无界量词、`∀[]-syntax` 与 `∃[]-syntax`。常元重标记使同一棵语法树先在某个载体的成员字母表上读取，再在可构造载体上读取，而不改变其构造结构。
<!--ja-->
構造再帰は論理式文法の十個の構成子、すなわち所属と等号の原子論理式、連言、選言、含意、偽、二つの非有界量化子、`∀[]-syntax`、`∃[]-syntax` に沿って進みます。定数の付け替えにより、同じ構文木をまず台の要素からなるアルファベット上で読み、次に構成可能な台の上で読むことができ、構成子の形は変わりません。
<!--/-->

```agda
open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using
  ( Formula; Term; var; _∈̇_; _≐_; _∧̇_; _∨̇_; _⇒̇_; ⊥̇; ∃̇∈; ∀̇∈; ∃̇_; ∀̇_ )
import FOL.Absoluteness
open import FOL.Manipulation.ConstantMapping using ( mapFo; mapFo-comp )
```

<!--en-->
A formula key combines its arity with its syntax code by set-theoretic pairing. There are two versions of this construction: one directly in the cumulative hierarchy and one internally in `L`, carrying constructibility proofs. Pair projection, numeral projection, and code projection will show that their underlying hierarchy sets agree.
<!--zh-->
公式键用集合论有序对把元数与语法码组合起来。这一构造有两个版本：一个直接位于累积层级中，另一个在 `L` 内部并携带可构造性证明。对码、数码与公式码的投影定理将说明两者的底层层级集合相等。
<!--ja-->
論理式キーは、アリティと構文符号を集合論的な順序対で組み合わせたものです。この構成には、累積階層で直接行うものと、構成可能性の証明を伴って `L` の内部で行うものがあります。対、数項、論理式符号についての射影定理により、両者の基礎にある階層集合が一致することを示します。
<!--/-->

```agda
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Coding {ℓ} using ( pr; pr-inj; #-inj′; module VCode )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans )
open import L.Axioms.Numerals {ℓ} using ( numeralL; numeralL-fst )
open import L.Coding.Model {ℓ} using ( module LCode; prʟ-fst; codeBridge )
```

<!--en-->
The closure condition follows exactly the recursive dependencies of formula satisfaction. A binary connective requires both same-arity formula children, an unbounded quantifier requires its successor-arity body, and `∀[]-syntax` or `∃[]-syntax` requires only its successor-arity formula body. The term code carried by either of the last two constructors is evaluated inside the clause and is not required to belong to the closed domain.
<!--zh-->
封闭条件恰好追随公式满足关系的递归依赖。二元联结词需要两个同元数的公式子式，无界量词需要其后继元数主体，而 `∀[]-syntax` 与 `∃[]-syntax` 只需要各自后继元数的公式主体。后两种构造子携带的词项码在子句内部求值，不要求属于封闭定义域。
<!--ja-->
閉性条件は、論理式の充足関係がもつ再帰的依存関係に正確に従います。二項結合子では同じアリティの二つの子論理式が、非有界量化子では後続アリティの本体が必要です。`∀[]-syntax` と `∃[]-syntax` では、後続アリティの論理式本体だけが必要です。後二者がもつ項の符号は節の内部で評価され、閉じた領域への所属を要求されません。
<!--/-->

```agda
open import L.Coding.Expressions {ℓ} using ( consAtL )
open import L.Coding.Closure {ℓ} using ( closedAt; binShapeAt; unShapeAt; bothSameAt; oneSuccAt; succSndAt; binSameClosed-out; unSuccClosed-out; binSuccClosed-out )
open import L.Coding.EnvironmentSet {ℓ} lem using ( envSet )
open import L.Coding.CodeConstructibility {ℓ} using ( sglʟ; cupʟ; tree; tree-inv )
open import L.Coding.CodeSet {ℓ} lem using ( AllCodes; AllCodes-out; keyS; codeS )
```

<!--en-->
For a formula `ψ`, `Sat` gives the canonical recursively defined set of satisfying environments. A satisfaction table instead stores coded key-value pairs. The theorem will compare a supplied value in such a pair with `Sat ψ`; table totality supplies child values only under propositional truncation, so the proof may use them to establish an equality but never turns them into a reusable choice function.
<!--zh-->
对公式 `ψ`，`Sat` 给出由递归定义的典范满足环境集合；满足关系表则存放编码后的键值对。定理将比较这种对中已经给出的值与 `Sat ψ`。表的全定义性只在命题截断下供给子公式的值，因此证明可以用这些值建立等式，却不能把它们变成可复用的选择函数。
<!--ja-->
論理式 `ψ` に対し、`Sat` は再帰的に定義された、充足する環境の標準的な集合を与えます。一方、充足関係の表は符号化されたキーと値の対を格納します。定理は、そこに与えられた値を `Sat ψ` と比較します。表の全域性が子論理式の値を与えるのは命題的切り詰めのもとだけなので、その値を等式の証明には使えても、再利用可能な選択関数にはできません。
<!--/-->

```agda
open import L.Coding.Satisfaction {ℓ} lem using
  ( Sat )
open import L.Coding.SatisfactionBridge {ℓ} lem using ( asConst )
open import L.Coding.SatisfactionTable {ℓ} lem using
  ( keyʟ; slot; satTable; entry-out; inSlot; ent-slot ) renaming ( total to slotTotal )
```

<!--en-->
Tags zero through nine select the ten constructor clauses. The environment tower records, for each natural arity `n`, the pair consisting of the numeral `# n` and the encoded set of length-`n` environments. These two coordinate systems let a clause recognize both the syntactic constructor and the arity at which its satisfaction set is being characterized.
<!--zh-->
零至九这十个标签选取十条构造子子句。环境塔对每个自然数元数 `n` 记录一对数据：数码 `# n` 与长度为 `n` 的编码环境集合。这两套坐标使子句既能识别语法构造子，也能识别其满足关系集合所处的元数。
<!--ja-->
零から九までのタグが十個の構成子の節を選びます。環境塔は各自然数アリティ `n` に対し、数項 `# n` と長さ `n` の符号化された環境集合との対を記録します。この二種類の座標により、節は構文上の構成子と、その充足関係集合を特徴づけるアリティの両方を認識できます。
<!--/-->

```agda
open import L.Coding.Quantification {ℓ} using
  ( f0; f1; f2; f3; f4; f5; f6; f7; f8; f9; sh; i0; i1; i2; i3; i4; i7; i8
  ; fstS; sndS; bigAnd-in; bigAnd-out )
open import L.Coding.EnvironmentTower {ℓ} lem using ( nn; towerAt; module TowerRead )
open import L.Coding.CodeDomain {ℓ} using ( Tags )
```

<!--en-->
The table specification has three mathematical parts: every domain key has some value, every table entry is a key-value pair whose key lies in the domain, and each of the ten constructors satisfies its semantic clause. The clause semantics turns the last part into extension facts. When a candidate value and the canonical recursive value have the same extension over the environment set, extensionality identifies their underlying hierarchy sets.
<!--zh-->
表规格有三个数学部分：定义域中的每个键都有某个值；每个表项都是键值对，且其键属于定义域；十个构造子各自满足相应的语义子句。子句语义把最后一部分读成外延事实。当候选值与典范递归值在环境集上具有相同外延时，外延性便将它们的底层层级集合等同起来。
<!--ja-->
表の仕様には三つの数学的な部分があります。領域の各キーには何らかの値があり、各表項目は領域に属するキーと値の対であり、十個の構成子はそれぞれの意味論的な節を満たします。節の意味論は最後の部分を外延に関する事実として読みます。候補の値と標準的な再帰値が環境集合上で同じ外延をもてば、外延性により両者の基礎となる階層集合が同一視されます。
<!--/-->

```agda
open import L.Coding.CodeAlphabet {ℓ} using ( module Alphabet )
open import L.Coding.SatisfactionClauses {ℓ} using ( tmIs; tableAt; module Clause; module Rel )
open import L.Coding.SatisfactionClauseSemantics {ℓ} lem using
  ( extB-out; extB-in; ExtFact; ext-unique; module Frame; module RelRead; module Bridge )
open import Cubical.Data.Nat using ( _+_ )
```

<!--en-->
Clause environments are finite vectors, and extending a frame shifts every older coordinate. Lookup and transport keep those coordinates aligned. Witnesses hidden by propositional truncation are eliminated only into proposition-valued targets: equality of underlying hierarchy sets in the pinning proof, and satisfaction of a fixed object-language clause in the filling proof. These eliminations do not expose reusable values, decodings, or frame data.
<!--zh-->
子句环境是有限向量，延拓框架会使每个原有坐标发生移位；查找与搬运负责保持这些坐标对齐。藏在命题截断下的见证只会被消去到命题值目标：钉扎证明中的底层层级集合等式，以及填充证明中固定对象语言子句的满足关系。这些消去都不会露出可复用的取值、解码结果或框架数据。
<!--ja-->
節の環境は有限ベクトルであり、枠を拡張すると以前の座標はすべてずれます。参照と移送によって、それらの座標を対応させ続けます。命題的切り詰めの内側に隠れた証人を消去する先は命題値の目標に限られます。固定の証明では基礎となる階層集合の等式へ、節を埋める証明では固定された対象言語の節の充足へ消去します。これらの消去から、再利用可能な値、復号結果、枠のデータが取り出されることはありません。
<!--/-->

```agda
open import Cubical.Data.Vec using ( _∷_; lookup )
open import Cubical.Data.Sigma using ( _×_ )
open import Cubical.Foundations.Prelude using ( subst2 )
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
```

<!--en-->
Propositional truncation preserves that a witness exists while forgetting which witness it was. Its eliminator therefore requires a proposition-valued target. Membership in the hierarchy is proposition-valued, and the hierarchy `V` is an h-set, so an equality between two of its sets is also a proposition and is a legitimate target for the eliminations used below.
<!--zh-->
命题截断保留见证存在这一事实，却忘去具体见证；因此，其消去目标必须取值于命题。层级中的隶属取值于命题，而层级 `V` 是 h-集合，所以其中两个集合之间的等式也是命题，可以作为下文诸次消去的合法目标。
<!--ja-->
命題的切り詰めは、証人が存在することを保ちつつ、それがどの証人であったかを忘れます。したがって、その消去先は命題値でなければなりません。階層における所属は命題値であり、階層 `V` は h-集合なので、その二つの集合の等式も命題です。このため、以下で用いる消去の正当な行き先になります。
<!--/-->

```agda
open PT using ( ∥_∥₁; squash₁ )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_; setIsSet )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫ )
open import Cubical.HITs.CumulativeHierarchy.Constructions using ( module InfinitySet )
open InfinitySet {ℓ} using ( #_; sucV )
```

<!--en-->
A constructor tag is stored as an element of `Fin 10`, while syntax codes use an ordinary natural numeral. The map `toℕ` forgets the bound proof and exposes the natural number whose numeral appears in the coded pair; the bound still guarantees that only tags zero through nine arise.
<!--zh-->
构造子标签存为 `Fin 10` 的元素，语法码中使用的则是普通自然数数码。映射 `toℕ` 忘去界限证明，露出编码有序对中数码所表示的自然数；原有界限仍保证只会出现零至九的标签。
<!--ja-->
構成子タグは `Fin 10` の要素として格納されますが、構文符号では通常の自然数の数項を使います。写像 `toℕ` は上界の証明を忘れ、符号化された対に現れる数項の自然数を取り出します。元の上界により、現れうるタグは零から九までに限られます。
<!--/-->

```agda
open import Cubical.Data.FinData using ( toℕ )

```

<!--en-->
Write `S` for the carrier of the first-order structure on `L`. An element of `S` consists of an underlying hierarchy set together with proof that it is constructible. Most conclusions in this chapter compare only the first projections, because equality of the represented sets is the mathematical content needed by satisfaction.
<!--zh-->
以 `S` 表示 `L` 上一阶结构的载体。`S` 的元素由一个底层层级集合及其可构造性证明组成。本章多数结论只比较第一投影，因为满足关系所需的数学内容正是被表示集合的相等。
<!--ja-->
`L` 上の一階構造の台を `S` と書きます。`S` の要素は、基礎となる階層集合と、その構成可能性の証明からなります。本章の結論の多くは第一射影だけを比較します。充足関係に必要な数学的内容は、表される集合の等しさだからです。
<!--/-->

```agda
open hPropStructure 𝒮ʟ using ( S )

```

<!--en-->
Object-language clauses are interpreted in the first-order structure carried by `L`. The notation `γ ⊨ φ` therefore means that the formula `φ` is satisfied by the finite environment `γ` in that structure. The bridge lemmas will compare such internal satisfaction statements with membership in the externally defined set `SatW ψ`.
<!--zh-->
对象语言子句在 `L` 所承载的一阶结构中解释。因此，记号 `γ ⊨ φ` 表示有限环境 `γ` 在该结构中满足公式 `φ`。后续桥引理将把这种内部满足断言与外部定义集合 `SatW ψ` 中的隶属相比较。
<!--ja-->
対象言語の節は、`L` が担う一階構造で解釈されます。したがって `γ ⊨ φ` は、その構造の有限環境 `γ` が論理式 `φ` を充足することを意味します。後の橋渡し補題は、この内部的な充足の主張を、外部で定義された集合 `SatW ψ` への所属と比較します。
<!--/-->

```agda
module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans using ( _^_; _⊨ᵐ_ )
open AbsL using ( _^_ ) renaming ( _⊨ᵐ_ to _⊨_ )
```

<!--en-->
## Matching keys, tags, and decoded formulas
<!--zh-->
## 匹配键、标签与解码公式
<!--ja-->
## 鍵、タグ、復号された論理式を対応させる
<!--/-->

<!--en-->
The two routes to a formula key are compared first. The external route embeds the alphabet symbols into the hierarchy and pairs the ambient numeral; the internal route relabels the constants as constructible sets, codes the formula inside `L`, and pairs the internal numeral.
<!--zh-->
先比较通往公式键的两条路线。外部路线把字母表符号嵌入层级并配以外围数码；内部路线把常元重标记为可构造集合、在 `L` 内部编码公式，并配以内部数码。
<!--ja-->
まず、論理式のキーへの二つの経路を比較します。外側の経路は、アルファベットの記号を階層へ埋め込み、周囲の数項と対にします。内側の経路は、定数を構成可能な集合として付け替え、論理式を `L` の内部で符号化し、内部の数項と対にします。
<!--/-->

```agda
module _ (A : S) where
  keyBridge : ∀ {n} (ψ : Formula ⟪ fst A ⟫ n)
            → fst (keyS A ψ) ≡ fst (keyʟ (mapFo (asConst A) ψ))
  keyBridge {n} ψ =
      cong (pr (# n))
```

<!--en-->
The proof aligns the syntax-code component first: relabelling the constants and then taking the ambient code agrees with projecting the internal code of the relabelled formula. It then aligns the arity numerals and finally projects the internal ordered pair. The resulting path relates the first projections of the two keys; it makes no claim that their accompanying constructibility proofs are definitionally the same.
<!--zh-->
证明先对齐语法码分量：重标常元后取外围公式码，等于投影重标后公式的内部码。接着对齐元数数码，最后投影内部有序对。所得路径连接两个键的第一投影；它不主张二者所附的可构造性证明在定义上相同。
<!--ja-->
証明はまず構文符号の成分をそろえます。定数を付け替えてから外部の符号を取ることは、付け替えた論理式の内部符号を射影することと一致します。次にアリティの数項をそろえ、最後に内部の順序対を射影します。得られるパスは二つのキーの第一射影を結ぶものであり、付随する構成可能性の証明が定義的に同じだとは主張しません。
<!--/-->

```agda
        ( cong (λ χ → VCode.⌜ χ ⌝) (sym (mapFo-comp (asConst A) fst ψ))
        ∙ sym (codeBridge (mapFo (asConst A) ψ)) )
    ∙ cong (λ w → pr w (fst LCode.⌜ mapFo (asConst A) ψ ⌝))
        (sym (numeralL-fst n))
    ∙ sym (prʟ-fst (numeralL n) LCode.⌜ mapFo (asConst A) ψ ⌝)
```

<!--en-->
The matching module is stated for one carrier `W`: its alphabet supplies the term and formula syntax whose shapes are matched.
<!--zh-->
匹配模块针对单一载体 `W` 陈述：其字母表供给要匹配形状的项与公式语法。
<!--ja-->
一致のモジュールは、一つの台 `W` に対して述べられます。そのアルファベットが、形を照合する項と論理式の構文を供給します。
<!--/-->

```agda
module Match (W : S) where
  open Alphabet W

```

<!--en-->
`MatchN` is a family of shape records indexed by a tag: for tags zero and one it names the two terms of an atom and their coded pair; for tags two through four it names the two immediate subformulas of a binary connective and their coded pair. The family is indexed by an already known formula, so it is not a parser of arbitrary sets.
<!--zh-->
`MatchN` 是以标签为索引的形状记录族：标签零与一时，它给出一个原子的两个项及其编码对；标签二至四时，它给出一个二元联结词的两个直接子公式及其编码对。该族以已知公式为索引，因此不是对任意集合的解析器。
<!--ja-->
`MatchN` は、タグで索引づけられた形状の記録の族です。タグ 0 と 1 では、アトムの二つの項とその符号化された対を名指し、タグ 2 から 4 では、二項結合子の直接の部分論理式とその符号化された対を名指します。この族は、すでに知られている論理式で索引づけられるので、任意の集合の解析器ではありません。
<!--/-->

```agda
  MatchN : ∀ {n} → ℕ → Formula Ab n → V ℓ → Type (ℓ-suc ℓ)
  MatchN {n} 0 ψ r = Σ[ t ∈ Term Ab n ] Σ[ u ∈ Term Ab n ] ((ψ ≡ t ∈̇ u) × (r ≡ pr (ct t) (ct u)))
  MatchN {n} 1 ψ r = Σ[ t ∈ Term Ab n ] Σ[ u ∈ Term Ab n ] ((ψ ≡ t ≐ u) × (r ≡ pr (ct t) (ct u)))
  MatchN {n} 2 ψ r = Σ[ a ∈ Formula Ab n ] Σ[ b ∈ Formula Ab n ] ((ψ ≡ a ∧̇ b) × (r ≡ pr (cd a) (cd b)))
  MatchN {n} 3 ψ r = Σ[ a ∈ Formula Ab n ] Σ[ b ∈ Formula Ab n ] ((ψ ≡ a ∨̇ b) × (r ≡ pr (cd a) (cd b)))
```

<!--en-->
Tags four through eight continue the same shape table. Tag four records implication and its two formula codes; tag five records falsity with numeral zero as payload; tags six and seven record the successor-arity bodies of the two unbounded quantifiers; tag eight records the current-arity term code and successor-arity body of `∀[]-syntax`.
<!--zh-->
标签四至八延续同一张形状表。标签四记录蕴含及其两个公式码；标签五记录假，并以零号数码为载荷；标签六与七记录两个无界量词的后继元数主体；标签八记录 `∀[]-syntax` 的当前元数词项码与后继元数主体。
<!--ja-->
タグ四から八も同じ形の表を続けます。タグ四は含意と二つの論理式符号を、タグ五は数項零をペイロードとする偽を記録します。タグ六と七は二つの非有界量化子の後続アリティの本体を記録し、タグ八は `∀[]-syntax` の現在のアリティにおける項符号と後続アリティの本体を記録します。
<!--/-->

```agda
  MatchN {n} 4 ψ r = Σ[ a ∈ Formula Ab n ] Σ[ b ∈ Formula Ab n ] ((ψ ≡ a ⇒̇ b) × (r ≡ pr (cd a) (cd b)))
  MatchN 5 ψ r = (ψ ≡ ⊥̇) × (r ≡ # 0)
  MatchN {n} 6 ψ r = Σ[ a ∈ Formula Ab (suc n) ] ((ψ ≡ ∃̇ a) × (r ≡ cd a))
  MatchN {n} 7 ψ r = Σ[ a ∈ Formula Ab (suc n) ] ((ψ ≡ ∀̇ a) × (r ≡ cd a))
  MatchN {n} 8 ψ r = Σ[ t ∈ Term Ab n ] Σ[ a ∈ Formula Ab (suc n) ] ((ψ ≡ ∀̇∈ t a) × (r ≡ pr (ct t) (cd a)))
```

<!--en-->
Tag nine has the analogous payload for `∃[]-syntax`: a term code at the current arity paired with a formula code at successor arity. The auxiliary family is empty at every natural tag at least ten. Thus `MatchN` describes exactly the ten constructor shapes, although it is defined on all natural numbers to support transport along tag equalities.
<!--zh-->
标签九为 `∃[]-syntax` 保存相应载荷：当前元数处的词项码与后继元数处的公式码组成的对。这个辅助族在每个不小于十的自然数标签处都是空类型。因此，`MatchN` 恰好描述十种构造子形状；把它定义在所有自然数上，是为了支持沿标签等式作搬运。
<!--ja-->
タグ九は `∃[]-syntax` に対応するペイロード、すなわち現在のアリティの項符号と後続アリティの論理式符号との対をもちます。この補助族は十以上の自然数タグでは空型です。したがって `MatchN` が記述するのは正確に十個の構成子形ですが、タグの等式に沿う移送を可能にするため、すべての自然数上で定義されています。
<!--/-->

```agda
  MatchN {n} 9 ψ r = Σ[ t ∈ Term Ab n ] Σ[ a ∈ Formula Ab (suc n) ] ((ψ ≡ ∃̇∈ t a) × (r ≡ pr (ct t) (cd a)))
  MatchN (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc _)))))))))) ψ r = Empty.⊥*

```

<!--en-->
The transport helper converts a matching record between tags and payloads. Pair injectivity splits an equality of coded pairs into the tag and payload components, and numeral injectivity transports the tag index; the matching record is then substituted along both.
<!--zh-->
搬运辅助在标签与载荷之间转换匹配记录。配对单射性把编码对的相等拆为标签分量与载荷分量，数码单射性搬运标签索引；匹配记录随后沿两者替换。
<!--ja-->
輸送の補助は、一致の記録をタグとペイロードの間で変換します。対の単射性が符号化された対の等式をタグとペイロードの成分に分け、数項の単射性がタグの索引を運び、一致の記録がその両方に沿って置き換えられます。
<!--/-->

```agda
  private
    at : ∀ {n} (ψ : Formula Ab n) (j k : ℕ) (r : V ℓ) → pr (# j) (cd ψ) ≡ pr (# j) (cd ψ)
       → MatchN j ψ r → (r' : V ℓ) → pr (# j) r ≡ pr (# k) r' → MatchN k ψ r'
    at ψ j k r _ mj r' e =
      subst2 (λ i x → MatchN i ψ x) (#-inj′ (pr-inj e .fst)) (pr-inj e .snd) mj
```

<!--en-->
The tag reader `matchAt` does not decode an arbitrary set. It starts from an already given formula, states the equality of that formula's code with a tagged pair, and returns the matching record: the case analysis on the formula exposes its own tag, and the transport helper relabels it to the given tag.
<!--zh-->
标签读取器 `matchAt` 并不解码任意集合。它从一条已给公式出发，陈述该公式的码与某个带标签对相等的等式，并返回匹配记录：对公式的情形分析暴露其自身的标签，而搬运辅助把它改标为给定的标签。
<!--ja-->
タグの読み手 `matchAt` は、任意の集合を復号するものではありません。すでに与えられた論理式から始まり、その論理式のコードがタグ付きの対と等しいことを述べ、一致の記録を返します。論理式についての場合分けがその固有のタグを露わにし、輸送の補助がそれを与えられたタグに付け替えます。
<!--/-->

```agda

  matchAt : ∀ {n} (ψ : Formula Ab n) (k : ℕ) (r : V ℓ) → cd ψ ≡ pr (# k) r → MatchN k ψ r
  matchAt (t ∈̇ u) k r e = at (t ∈̇ u) 0 k _ refl (t , u , (refl , refl)) r e
  matchAt (t ≐ u) k r e = at (t ≐ u) 1 k _ refl (t , u , (refl , refl)) r e
  matchAt (a ∧̇ b) k r e = at (a ∧̇ b) 2 k _ refl (a , b , (refl , refl)) r e
  matchAt (a ∨̇ b) k r e = at (a ∨̇ b) 3 k _ refl (a , b , (refl , refl)) r e
```

<!--en-->
The remaining clauses perform no search. In each structural case, the known constructor supplies its canonical tag and payload: implication supplies two child codes, falsity supplies zero, each unbounded quantifier supplies its body code, and `∀[]-syntax` supplies its term and body codes. The same transport helper then reconciles these canonical data with the tag and payload named by the input equality.
<!--zh-->
余下诸式不进行任何搜索。在每个结构情形中，已知构造子直接给出其典范标签与载荷：蕴含给出两个子公式码，假给出零，两个无界量词各给出主体码，而 `∀[]-syntax` 给出词项码与主体码。随后，同一个搬运辅助把这些典范数据与输入等式所指定的标签和载荷对齐。
<!--ja-->
残りの各式も探索は行いません。各構造の場合で、既知の構成子が標準的なタグとペイロードを直接与えます。含意は二つの子論理式符号を、偽は零を、二つの非有界量化子はそれぞれ本体の符号を、`∀[]-syntax` は項と本体の符号を与えます。その後、同じ移送補助が、これらの標準的なデータを入力の等式が指定するタグとペイロードに合わせます。
<!--/-->

```agda
  matchAt (a ⇒̇ b) k r e = at (a ⇒̇ b) 4 k _ refl (a , b , (refl , refl)) r e
  matchAt ⊥̇ k r e = at ⊥̇ 5 k _ refl (refl , refl) r e
  matchAt (∃̇ a) k r e = at (∃̇ a) 6 k _ refl (a , (refl , refl)) r e
  matchAt (∀̇ a) k r e = at (∀̇ a) 7 k _ refl (a , (refl , refl)) r e
  matchAt (∀̇∈ t a) k r e = at (∀̇∈ t a) 8 k _ refl (t , a , (refl , refl)) r e
```

<!--en-->
For `∃[]-syntax`, the canonical tag is nine and the payload is the pair of the bound term code and the successor-arity body code. This final structural branch completes `matchAt` for every formula constructor; its conclusion still describes the shape of the formula already supplied as input.
<!--zh-->
对 `∃[]-syntax`，典范标签为九，载荷是界词项码与后继元数主体码组成的对。这最后一个结构分支使 `matchAt` 覆盖全部公式构造子；其结论仍只描述作为输入已经给定的公式之形状。
<!--ja-->
`∃[]-syntax` の標準的なタグは九であり、ペイロードは境界を表す項の符号と後続アリティの本体符号との対です。この最後の構造分岐により、`matchAt` はすべての論理式構成子を扱います。その結論は依然として、入力としてすでに与えられた論理式の形を記述するだけです。
<!--/-->

```agda
  matchAt (∃̇∈ t a) k r e = at (∃̇∈ t a) 9 k _ refl (t , a , (refl , refl)) r e
```

<!--en-->
Now suppose `c` belongs to the canonical code set and is presented as the pair of the arity numeral `# n` with a payload `z`. Membership in `AllCodes W` yields, under propositional truncation, some arity `n₁`, some formula `ψ₁` of that arity, and an equality between `c` and its key. The remaining work is to reconcile `n₁` with the stated `n`.
<!--zh-->
现设 `c` 属于典范码集，并被表示为元数数码 `# n` 与载荷 `z` 的有序对。`c` 在 `AllCodes W` 中的隶属，经命题截断给出某个元数 `n₁`、该元数上的某条公式 `ψ₁`，以及 `c` 与其键之间的等式。余下任务是把 `n₁` 与题设的 `n` 对齐。
<!--ja-->
いま `c` が標準的な符号集合に属し、アリティの数項 `# n` とペイロード `z` の対として表示されているとします。`AllCodes W` への所属からは、命題的切り詰めのもとで、あるアリティ `n₁`、そのアリティの論理式 `ψ₁`、そして `c` とそのキーとの等式が得られます。残る仕事は `n₁` を指定された `n` と一致させることです。
<!--/-->

```agda
  decodeAll : (c : S) → ⟨ fst c ∈ fst (AllCodes W) ⟩ → (n : ℕ) (z : V ℓ) → fst c ≡ pr (# n) z
            → ∥ Σ[ ψ ∈ Formula Ab n ] (z ≡ cd ψ) ∥₁
  decodeAll c c∈ n z e = PT.map
    (λ { (n₁ , ψ₁ , e₁) →
      let q = pr-inj (sym e₁ ∙ e)
```

<!--en-->
Injectivity of pairing equates the two arity numerals and the two payloads; numeral injectivity then gives a path `n₁ ≡ n`. Transporting `ψ₁` along this dependent path changes its code by `cd-subst`, yielding a formula of exactly arity `n` whose code is `z`. The result remains propositionally truncated, so it provides neither a chosen decoder nor uniqueness of the decoded formula.
<!--zh-->
有序对编码的单射性分别等同两个元数数码与两个载荷；数码单射性继而给出路径 `n₁ ≡ n`。沿这条依赖路径搬运 `ψ₁`，并用 `cd-subst` 校正其码，便得到一条元数恰为 `n` 且码为 `z` 的公式。结果仍处于命题截断之下，所以既不提供选定的解码器，也不主张解码公式唯一。
<!--ja-->
対符号化の単射性により、二つのアリティ数項と二つのペイロードがそれぞれ等しくなり、数項の単射性からパス `n₁ ≡ n` が得られます。この依存パスに沿って `ψ₁` を移送し、`cd-subst` でその符号を補正すると、アリティが正確に `n` で符号が `z` である論理式を得ます。結果は命題的切り詰めされたままなので、選ばれた復号器も、復号された論理式の一意性も与えません。
<!--/-->

```agda
          nq = #-inj′ (q .fst)
      in subst (Formula Ab) nq ψ₁ , (sym (q .snd) ∙ sym (cd-subst nq ψ₁)) })
    (AllCodes-out W c c∈)
```

<!--en-->
## Uniqueness on a subcode-closed domain
<!--zh-->
## 对子码封闭定义域上的唯一性
<!--ja-->
## 部分符号で閉じた領域上の一意性
<!--/-->

<!--en-->
The soundness argument is local to an arbitrary code domain `C`. Besides a proposed table `T`, it assumes that the stored carrier is `W`, the ten tag slots contain the correct numerals, the environment slot is the correct tower, `C` is closed under the required immediate formula subcodes, and `T` satisfies the packaged table specification. These hypotheses do not assert that every formula key lies in `C`.
<!--zh-->
可靠性论证局限于任意给定的码域 `C`。除候选表 `T` 外，它还假设：所存载体为 `W`，十个标签槽含有正确数码，环境槽为正确的塔，`C` 对所需的直接公式子码封闭，并且 `T` 满足打包后的表规格。这些假设并不声称每个公式键都属于 `C`。
<!--ja-->
健全性の議論は、任意に与えた符号領域 `C` に局所化されています。候補となる表 `T` に加え、格納された台が `W` であること、十個のタグ位置が正しい数項をもつこと、環境の位置が正しい塔であること、`C` が必要な直下の論理式部分符号について閉じていること、そして `T` がまとめられた表の仕様を満たすことを仮定します。これらの仮定は、すべての論理式キーが `C` に属するとは述べません。
<!--/-->

```agda
module SatSoundC {m : ℕ} (T w C E : Fin m) (N : Fin 10 → Fin m) (γ : S ^ m) (W : S)
  (qw : fst (lookup w γ) ≡ fst W) (tg : Tags γ N)
  (hE : ⟨ γ ⊨ towerAt E w (N f0) ⟩) (hcl : ⟨ γ ⊨ closedAt C ⟩)
  (hT : ⟨ γ ⊨ tableAt T w C E N ⟩) where
  open Alphabet W
```

<!--en-->
Write `Tv`, `Cv`, and `Ev` for the underlying hierarchy sets stored in the table, code-domain, and environment-tower slots. Atomic formulas require no recursive lookup in `Cv`: their term codes are interpreted directly by the atomic bridge. Recursive calls enter only when a constructor has immediate formula children.
<!--zh-->
以 `Tv`、`Cv` 与 `Ev` 分别表示表槽、码域槽与环境塔槽中所存的底层层级集合。原子公式不需要在 `Cv` 中递归查找：其词项码由原子桥直接解释。只有构造子含有直接公式子式时，证明才会递归调用。
<!--ja-->
表、符号領域、環境塔の各位置に格納された基礎階層集合を、それぞれ `Tv`、`Cv`、`Ev` と書きます。原子論理式では `Cv` における再帰的な参照は不要です。その項符号は原子論理式の橋渡しによって直接解釈されます。再帰呼出しが生じるのは、構成子が直下の子論理式をもつ場合だけです。
<!--/-->

```agda
  open Bridge W
  private
    Tv = fst (lookup T γ)
    Cv = fst (lookup C γ)
    Ev = fst (lookup E γ)
```

<!--en-->
Let `Wv` denote the underlying hierarchy set of the carrier `W`. Quantifier bridges use this set as their range of quantification, while the atomic bridges interpret term codes over the alphabet determined by the same carrier. The proofs compare values as hierarchy sets, so the conclusion of pinning is an equality of first projections rather than an equality of proof-carrying records in `S`.
<!--zh-->
令 `Wv` 表示载体 `W` 的底层层级集合。量词桥以该集作为量化范围，原子桥则在同一载体所确定的字母表上解释词项码。证明把值作为层级集合比较，所以钉扎结论是第一投影的等式，而非 `S` 中携带证明之记录的等式。
<!--ja-->
台 `W` の基礎階層集合を `Wv` と書きます。量化子の橋渡しはこの集合を量化の範囲として用い、原子論理式の橋渡しは同じ台が定めるアルファベット上で項の符号を解釈します。証明は値を階層集合として比較するので、固定の結論は第一射影の等式であり、`S` にある証明付きレコード全体の等式ではありません。
<!--/-->

```agda
    Wv = fst W

```

<!--en-->
The environment tower supplies the row for a formula's arity, while the clause frame combines that row with the formula key, its tagged code, and a proposed table value. Reading a constructor clause at this frame exposes the semantic relation that characterizes the proposed value by its members.
<!--zh-->
环境塔给出公式元数所对应的一行；子句框架把这一行与公式键、带标签的公式码及候选表值组合起来。在该框架处读取构造子子句，便会露出按成员刻画候选值的语义关系。
<!--ja-->
環境塔は論理式のアリティに対応する行を与え、節の枠はその行を論理式キー、タグ付き符号、候補となる表の値と組み合わせます。この枠で構成子の節を読むと、候補の値をその要素によって特徴づける意味論的関係が現れます。
<!--/-->

```agda
    module TR = TowerRead E w (N f0) γ W qw (tg f0) hE
    module Fr = Frame T w C E N γ tg
    module Cl = Clause T w C E N
    module R = Rel T w N

```

<!--en-->
The packaged hypothesis `hT` contains totality, the assertion that table entries are over `C`, and the conjunction of the ten constructor clauses. The pinning proof uses totality to obtain child entries and uses the constructor clauses to characterize values. Its particular candidate entry is supplied directly, so the domain assertion `hOn` is retained from the package but is not needed by this uniqueness argument.
<!--zh-->
打包假设 `hT` 包含全定义性、表项之键位于 `C` 的断言，以及十条构造子子句的合取。钉扎证明用全定义性取得子公式表项，并用构造子子句刻画值。所讨论的候选表项由命题直接给出，因此定义域断言 `hOn` 虽从包中保留下来，却不被这段唯一性论证使用。
<!--ja-->
まとめられた仮定 `hT` は、全域性、表項目のキーが `C` 上にあるという主張、十個の構成子の節の連言からなります。固定の証明は、全域性から子論理式の表項目を得て、構成子の節から値を特徴づけます。対象となる候補の表項目は命題に直接与えられているため、領域についての主張 `hOn` は包から取り出されますが、この一意性の議論では使われません。
<!--/-->

```agda
    hTot = hT .fst
    hOn = hT .snd .fst
    hTen = hT .snd .snd

```

<!--en-->
The ten constructor clauses are stored as one finite conjunction indexed by `Fin 10`. The reader `bigAnd-out` turns this package into a family `cl k`, so a structural case can select exactly the clause named by its constructor tag without changing any of the other nine clauses.
<!--zh-->
十条构造子子句存为一个由 `Fin 10` 索引的有限合取。读取器 `bigAnd-out` 把这个包化为子句族 `cl k`，于是每个结构情形可以按其构造子标签准确选取对应子句，而无须改动其余九条。
<!--ja-->
十個の構成子の節は、`Fin 10` で添字づけられた一つの有限連言として格納されています。読み手 `bigAnd-out` はこれを族 `cl k` に変えるので、各構造の場合は、ほかの九個の節を変更せずに、その構成子タグが指定する節だけを選べます。
<!--/-->

```agda
    cl : (k : Fin 10) → ⟨ γ ⊨ Cl.clause k ⟩
    cl = bigAnd-out γ 9 Cl.clause hTen
```

<!--en-->
The case module packages the data of one induction step: a formula, its tag, its payload set, the equation between code and payload, membership of its key in the code domain, a candidate table entry, and the entry's membership. The tower reading supplies the canonical tower entry for the formula's arity.
<!--zh-->
情形模块打包一次归纳步骤的数据：一条公式、其标签、其载荷集合、码与载荷间的等式、其键在码域中的成员资格、一个候选表条目及该条目的隶属。塔读取为该公式的元数供给典范塔条目。
<!--ja-->
場合のモジュールは、一つの帰納の一歩のデータをまとめます。論理式、そのタグ、そのペイロードの集合、コードとペイロードの等式、コードの定義域の中でのキーの所属、候補の表の項目、そして項目の所属です。塔の読みが、論理式のアリティのための正準な塔の項目を供給します。
<!--/-->

```agda
    module Case {n : ℕ} (ψ : Formula Ab n) (k : Fin 10) (rS : S)
      (ep : cd ψ ≡ pr (# (toℕ k)) (fst rS)) (c∈ : ⟨ fst (keyS W ψ) ∈ Cv ⟩)
      (y : S) (mem : ⟨ pr (fst (keyS W ψ)) (fst y) ∈ Tv ⟩) where
      q∈ : ⟨ pr (# n) (fst (envSet W n)) ∈ Ev ⟩
      q∈ = TR.entry-in n
```

<!--en-->
The formula code is initially written with the canonical numeral `# k`; the tag equation rewrites that numeral as the value stored at slot `N k`. The resulting equality fits the clause interface. The frame `δ12` then prepends twelve coordinates to the ambient environment, including the arity row, formula key and code, payload, and candidate value.
<!--zh-->
公式码起初以典范数码 `# k` 表示；标签等式把这个数码改写为槽 `N k` 中存放的值，所得等式便符合子句的输入形式。随后，框架 `δ12` 在外围环境前添加十二个坐标，其中包括元数行、公式键与公式码、载荷及候选值。
<!--ja-->
論理式符号は初め標準的な数項 `# k` を用いて書かれています。タグの等式によってこの数項を位置 `N k` に格納された値へ書き換えると、得られた等式は節の入力形式に合います。その後、枠 `δ12` は周囲の環境の前に十二個の座標を加えます。そこにはアリティの行、論理式キーと符号、ペイロード、候補の値が含まれます。
<!--/-->

```agda
      ep' : fst (codeS W ψ) ≡ pr (fst (lookup (N k) γ)) (fst rS)
      ep' = ep ∙ cong (λ a → pr a (fst rS)) (sym (tg k))
      δ12 : S ^ (12 + m)
      δ12 = Fr.At.δ12 (nn n) (envSet W n) (keyS W ψ) (codeS W ψ) rS y q∈ refl k ep' mem
      rel : ⟨ δ12 ⊨ R.relN (toℕ k) ⟩
```

<!--en-->
Applying the selected clause to this concrete frame yields satisfaction of the tag-indexed relation `relN k`. The relation reader is then fixed at `δ12`; later constructor-specific readers extend this same frame and unpack `rel` into the extension fact appropriate to an atom, binary connective, or quantifier.
<!--zh-->
把所选子句施于这个具体框架，得到标签所索引关系 `relN k` 的满足关系。随后把关系读取固定在 `δ12` 上；后面的各构造专用读取会延拓同一个框架，并把 `rel` 解包为适用于原子式、二元联结词或量词的外延事实。
<!--ja-->
選んだ節をこの具体的な枠に適用すると、タグで添字づけられた関係 `relN k` の充足が得られます。次に関係の読み手を `δ12` に固定します。後の構成子別の読み手はこの同じ枠を拡張し、`rel` を原子論理式、二項結合子、量化子に適した外延の事実へ分解します。
<!--/-->

```agda
      rel = Fr.clause-out k (cl k) (nn n) (envSet W n) (keyS W ψ) (codeS W ψ) rS y q∈ c∈ refl ep mem
      module RR = RelRead T w N δ12
```

<!--en-->
If a child formula key belongs to `Cv`, table totality gives only the propositional truncation of a pair consisting of a value `ya` and an entry at that key. Thus `sub` proves mere existence, not a selected value. Each recursive case eliminates this witness directly into equality of hierarchy sets, where the h-set structure makes the target a proposition.
<!--zh-->
若子公式的键属于 `Cv`，表的全定义性只给出命题截断后的一个对，其中含有某个值 `ya` 及该键处的表项。因此，`sub` 只证明纯粹存在，而不选定一个值。每个递归情形都把这一见证直接消去到层级集合的等式；h-集合结构保证该目标是命题。
<!--ja-->
子論理式のキーが `Cv` に属するなら、表の全域性から得られるのは、値 `ya` とそのキーにおける表項目との対を命題的切り詰めしたものだけです。したがって `sub` が証明するのは単なる存在であり、値を選ぶことではありません。各再帰の場合は、この証人を階層集合の等式へ直接消去し、h-集合構造によってその行き先が命題になります。
<!--/-->

```agda
    sub : ∀ {n} (a : Formula Ab n) → ⟨ fst (keyS W a) ∈ Cv ⟩
        → ∥ Σ[ ya ∈ S ] ⟨ pr (fst (keyS W a)) (fst ya) ∈ Tv ⟩ ∥₁
    sub a a∈ = Fr.total-out hTot (keyS W a) a∈

```

<!--en-->
The central predicate is conditional. If the key of `ψ` lies in the code domain, then every table value `y` recorded at that key has the same underlying set as the recursively defined satisfaction set of `ψ`. The conditionality is the honest form: nothing is asserted for keys outside the domain.
<!--zh-->
中心谓词是条件式的。若 `ψ` 的键在码域中，则在该键处记录的每个表值 `y` 的底层集，都与 `ψ` 的递归满足集合的底层集相同。这种条件式正是诚实的形式：对域外的键不作任何断言。
<!--ja-->
中心的な述語は条件つきです。`ψ` のキーがコードの定義域にあれば、そのキーのもとで記録されたすべての表の値 `y` の底の集合は、`ψ` の再帰的な充足集合の底の集合と同じです。この条件つきの形が正直な形です。定義域の外のキーについては何も主張しません。
<!--/-->

```agda
  Pinned : ∀ {n} (ψ : Formula Ab n) → Type (ℓ-suc ℓ)
  Pinned ψ = ⟨ fst (keyS W ψ) ∈ Cv ⟩
           → (y : S) → ⟨ pr (fst (keyS W ψ)) (fst y) ∈ Tv ⟩ → fst y ≡ fst (SatW ψ)

```

<!--en-->
The proof of `Pinned` is organized by structural recursion on the given formula. Recursive calls are made only for immediate formula children supplied by the syntax constructor. There is no recursion on members of `C`, no well-founded recursion on arbitrary codes, and no attempt to define a value for a code that has not already been identified with a formula key.
<!--zh-->
`Pinned` 的证明按给定公式作结构递归。递归调用只施于语法构造子直接给出的公式子式。这里既不在 `C` 的成员上递归，也不在任意码上作良基递归，更不会试图给尚未被识别为公式键的码定义值。
<!--ja-->
`Pinned` の証明は、与えられた論理式についての構造再帰として組み立てられます。再帰呼出しは、構文の構成子が直接与える子論理式にだけ行われます。`C` の要素についての再帰でも、任意の符号についての整礎再帰でもなく、論理式キーと同定されていない符号に値を定義する試みでもありません。
<!--/-->

```agda
  private
```

<!--en-->
The payload set of a coded formula is recovered from the code equation by the pairing projection.
<!--zh-->
编码公式的载荷集合由码等式经配对投影恢复。
<!--ja-->
符号化された論理式のペイロードの集合は、コードの等式から、対の射影によって復元されます。
<!--/-->

```agda
    payS : ∀ {n} (ψ : Formula Ab n) (k : ℕ) (r : V ℓ) → cd ψ ≡ pr (# k) r → S
    payS ψ k r e = sndS (codeS W ψ) (# k) r e
```

<!--en-->
All three binary connectives share the same recursive pattern. The parameters identify the constructor, its tag and payload equation, the corresponding object-language relation, and a semantic bridge. That bridge assumes equalities identifying two coordinates of an extended environment with the canonical satisfaction sets of the two children, and from them produces an extension fact for the canonical value of the compound.
<!--zh-->
三个二元联结词共享同一种递归模式。诸参数依次确定构造子、标签与载荷等式、相应的对象语言关系，以及一条语义桥。该桥假设延拓环境中的两个坐标分别等于两个子公式的典范满足关系集合，并据此为复合公式的典范值给出外延事实。
<!--ja-->
三つの二項結合子は同じ再帰パターンを共有します。各パラメータは、構成子、タグとペイロードの等式、対応する対象言語の関係、意味論的な橋渡しを指定します。この橋渡しは、拡張された環境の二つの座標が二つの子論理式の標準的な充足関係集合に等しいという等式を仮定し、そこから複合論理式の標準値についての外延の事実を作ります。
<!--/-->

```agda
    binCase : ∀ {n} (op : ∀ {j} → Formula S j → Formula S j → Formula S j)
              (opA : Formula Ab n → Formula Ab n → Formula Ab n) (k : Fin 10)
              (a b : Formula Ab n) (code : cd (opA a b) ≡ pr (# (toℕ k)) (pr (cd a) (cd b)))
              (relIs : R.relN (toℕ k) ≡ R.binRel op)
              (bridge : ∀ {j} (env : S ^ j) (ya yb : Fin j)
```

<!--en-->
The bridge is formulated for an environment containing the two child values at named coordinates. A separate closure reader turns membership of the compound key in `Cv` into membership of both child keys, at the same arity. The recursive hypotheses can then identify whichever child entries totality provides with `SatW a` and `SatW b`.
<!--zh-->
该桥针对一个在指定坐标含有两个子值的环境陈述。另有一条封闭读取把复合键在 `Cv` 中的隶属转化为两个同元数子键的隶属。于是，无论全定义性给出哪些子表项，递归假设都能分别把它们与 `SatW a`、`SatW b` 等同。
<!--ja-->
橋渡しは、指定された座標に二つの子の値を含む環境について述べられます。別の閉性の読み手が、複合キーの `Cv` への所属から、同じアリティの二つの子キーの所属を取り出します。これにより、全域性がどの子表項目を与えても、再帰仮定によってそれぞれを `SatW a` と `SatW b` に同定できます。
<!--/-->

```agda
                      → fst (lookup ya env) ≡ fst (SatW a) → fst (lookup yb env) ≡ fst (SatW b)
                      → ExtFact (fst (SatW (opA a b))) (fst (envSet W n))
                          (λ z → ⟨ (z ∷ env) ⊨ op (var i0 ∈̇ var (suc ya)) (var i0 ∈̇ var (suc yb)) ⟩))
            → (cl2 : ⟨ fst (keyS W (opA a b)) ∈ Cv ⟩
                   → ⟨ fst (keyS W a) ∈ Cv ⟩ × ⟨ fst (keyS W b) ∈ Cv ⟩)
```

<!--en-->
To prove the compound is pinned, the proof eliminates the propositionally truncated left value, right value, and binary-relation witness. Every elimination ends in the equality `fst y ≡ fst (SatW (opA a b))`. Since `V` is an h-set, this equality is a proposition, so the eliminations reveal no permanent choice of child values or frame data.
<!--zh-->
为证明复合公式被钉扎，证明依次消去经命题截断的左子值、右子值与二元关系见证。每次消去的最终目标都是等式 `fst y ≡ fst (SatW (opA a b))`。由于 `V` 是 h-集合，该等式是命题，所以这些消去不会留下对子值或框架数据的固定选择。
<!--ja-->
複合論理式が固定されることを示すため、命題的切り詰めされた左の値、右の値、二項関係の証人を順に消去します。どの消去も、最終的には等式 `fst y ≡ fst (SatW (opA a b))` を目標とします。`V` は h-集合なのでこの等式は命題であり、消去によって子の値や枠のデータの恒久的な選択が残ることはありません。
<!--/-->

```agda
            → Pinned a → Pinned b → Pinned (opA a b)
    binCase {n} op opA k a b code relIs bridge cl2 ia ib c∈ y mem =
      PT.rec (setIsSet _ _) (λ { (ya , ma) → PT.rec (setIsSet _ _) (λ { (yb , mb) →
        PT.rec (setIsSet _ _)
          (λ { (s , s₁ , e₁ , s₂ , e₂ , ext) →
```

<!--en-->
The binary-relation reader extends the common clause frame with the two child codes, keys, and values, together with its auxiliary witnesses. In this extended environment the clause supplies an extension fact for the candidate `y`, while the bridge supplies the corresponding extension fact for `SatW (opA a b)`. The theorem `ext-unique` applies set extensionality to these two facts and equates their underlying sets.
<!--zh-->
二元关系读取器用两个子公式码、键和值以及辅助见证延拓公共子句框架。在这个延拓环境中，子句为候选值 `y` 给出外延事实，而桥为 `SatW (opA a b)` 给出相应的外延事实。定理 `ext-unique` 对这两个事实应用集合外延性，从而等同二者的底层集合。
<!--ja-->
二項関係の読み手は、二つの子論理式の符号、キー、値、および補助的な証人によって共通の節の枠を拡張します。この拡張環境では、節が候補 `y` の外延の事実を与え、橋渡しが `SatW (opA a b)` の対応する外延の事実を与えます。定理 `ext-unique` はこの二つの事実に集合の外延性を適用し、両者の基礎集合を等しくします。
<!--/-->

```agda
            let env = yb ∷ keyS W b ∷ s₂ ∷ e₂ ∷ ya ∷ keyS W a ∷ s₁ ∷ e₁ ∷ codeS W b ∷ codeS W a ∷ s ∷ K.δ12
                P : S → Type (ℓ-suc ℓ)
                P z = ⟨ (z ∷ env) ⊨ R.binBody op ⟩
            in ext-unique y (SatW (opA a b)) (envSet W n) P ext
                 (bridge env i4 i0 (ia (cl2 c∈ .fst) ya ma) (ib (cl2 c∈ .snd) yb mb)) })
```

<!--en-->
The relation reading is obtained from the clause by the tag identification, and the child values are obtained from the table's totality, in the order left child first, then right child.
<!--zh-->
关系读取由子句经标签同一视获得；两个子值由表的全域性获得，先左子值，后右子值。
<!--ja-->
関係の読みは、節からタグの同一視を通して得られ、部分の値は表の全域性から、まず左の部分、次に右の部分の順で得られます。
<!--/-->

```agda
          (K.RR.bin-out op (subst (λ φ → ⟨ K.δ12 ⊨ φ ⟩) relIs K.rel)
             (codeS W a) (codeS W b) (keyS W a) ya (keyS W b) yb refl ma refl mb refl) })
        (sub b (cl2 c∈ .snd)) })
        (sub a (cl2 c∈ .fst))
      where
```

<!--en-->
The local module `K` records the compound formula itself, its constructor tag, a constructible representative of the paired child-code payload, the compound key's domain membership, and the candidate entry. It therefore fixes one concrete clause frame for the entire binary argument; the recursive hypotheses concern only the two immediate children.
<!--zh-->
局部模块 `K` 记录复合公式本身、其构造子标签、成对子公式码载荷的一个可构造表示、复合键的定义域成员资格，以及候选表项。这样，整个二元论证只使用一个具体子句框架；递归假设则只涉及两个直接子公式。
<!--ja-->
局所モジュール `K` は、複合論理式そのもの、その構成子タグ、対になった子論理式符号のペイロードの構成可能な表現、複合キーの領域への所属、候補の表項目を記録します。これにより、二項の場合の議論全体に一つの具体的な節の枠が固定され、再帰仮定は二つの直下の子論理式だけに関わります。
<!--/-->

```agda
      module K = Case (opA a b) k (payS (opA a b) (toℕ k) (pr (cd a) (cd b)) code) code c∈ y mem

```

<!--en-->
The two unbounded quantifiers also share one recursive case. Their body has successor arity, and the payload is just that body's code. The semantic bridge receives coordinates for the fixed carrier and for a table value of the body; after that value is identified with `SatW a`, the bridge characterizes the canonical satisfaction set of the quantified formula over `envSet W n`.
<!--zh-->
两个无界量词也共享一个递归情形。其主体具有后继元数，载荷就是该主体的码。语义桥接收固定载体所在的坐标与主体表值所在的坐标；把该表值等同于 `SatW a` 后，桥便在 `envSet W n` 上刻画量化公式的典范满足关系集合。
<!--ja-->
二つの非有界量化子も一つの再帰の場合を共有します。本体は後続アリティをもち、ペイロードはその本体の符号だけです。意味論的な橋渡しは、固定された台の座標と、本体の表の値の座標を受け取ります。その値を `SatW a` と同定すると、橋渡しは `envSet W n` 上で量化された論理式の標準的な充足関係集合を特徴づけます。
<!--/-->

```agda
    quCase : ∀ {n} (q : ∀ {j} → Term S j → Formula S (suc j) → Formula S j)
             (qA : Formula Ab (suc n) → Formula Ab n) (k : Fin 10)
             (a : Formula Ab (suc n)) (code : cd (qA a) ≡ pr (# (toℕ k)) (cd a))
             (relIs : R.relN (toℕ k) ≡ R.quRel q)
             (bridge : ∀ {j} (env : S ^ j) (wi yai : Fin j)
```

<!--en-->
The carrier coordinate remains in the original ambient environment and is reached after the frame extensions by an index shift; the child value is a newly exposed coordinate of the relation witness. Closure supplies membership of the successor-arity body key, and the recursive hypothesis identifies every table entry at that key with the body's canonical satisfaction set. The bridge then matches the object-language quantifier with quantification over `Wv`.
<!--zh-->
载体坐标仍位于原来的外围环境中，框架延拓后通过索引移位访问；子公式值则是关系见证新露出的坐标。封闭性给出后继元数主体键的成员资格，递归假设把该键处每个表项都等同于主体的典范满足关系集合。于是，桥把对象语言量词与在 `Wv` 上的量化准确对应起来。
<!--ja-->
台の座標は元の周囲の環境に残り、枠を拡張した後は添字のずらしによって参照されます。子論理式の値は、関係の証人が新しく露わにする座標です。閉性から後続アリティの本体キーの所属が得られ、再帰仮定はそのキーにおけるすべての表項目を、本体の標準的な充足関係集合に同定します。これにより橋渡しは、対象言語の量化子を `Wv` 上の量化に正確に対応させます。
<!--/-->

```agda
                     → fst (lookup wi env) ≡ Wv → fst (lookup yai env) ≡ fst (SatW a)
                     → ExtFact (fst (SatW (qA a))) (fst (envSet W n))
                         (λ z → ⟨ (z ∷ env) ⊨ q (var (suc wi)) (∃̇∈ (var (suc (suc yai))) (consAtL i0 i1 i2)) ⟩))
           → (cl1 : ⟨ fst (keyS W (qA a)) ∈ Cv ⟩ → ⟨ fst (keyS W a) ∈ Cv ⟩)
           → Pinned a → Pinned (qA a)
```

<!--en-->
The proof first eliminates the propositionally truncated body value and then the propositionally truncated witness obtained by reading the quantifier relation. That witness extends the common clause frame with the successor numeral, the body key, its value, and auxiliary coordinates. Both eliminations target the equality between the candidate value and the canonical quantified satisfaction set, so no body value is selected globally.
<!--zh-->
证明先消去经命题截断的主体值，再消去读取量词关系所得的经命题截断见证。该见证以后继数码、主体键、主体值及辅助坐标延拓公共子句框架。两次消去都以候选值和典范量化满足关系集合之间的等式为目标，因此不会全局选定任何主体值。
<!--ja-->
証明はまず命題的切り詰めされた本体の値を消去し、次に量化子関係の読み取りから得た命題的切り詰めされた証人を消去します。その証人は、後続の数項、本体キー、その値、補助座標によって共通の節の枠を拡張します。どちらの消去も、候補の値と標準的な量化された充足関係集合との等式を目標とするため、本体の値が大域的に選ばれることはありません。
<!--/-->

```agda
    quCase {n} q qA k a code relIs bridge cl1 ia c∈ y mem =
      PT.rec (setIsSet _ _) (λ { (ya , ma) →
        PT.rec (setIsSet _ _)
          (λ { (s , s' , e' , ext) →
            let env = nn (suc n) ∷ s' ∷ ya ∷ keyS W a ∷ s ∷ e' ∷ K.δ12
```

<!--en-->
At the extended environment, the relation clause provides an extension fact for the candidate table value `y`. The recursive hypothesis supplies the equality needed for the bridge, and the bridge provides the matching extension fact for `SatW (qA a)`, using the carrier equation at its shifted coordinate. Set extensionality in `ext-unique` then identifies the two underlying sets.
<!--zh-->
在延拓环境中，关系子句为候选表值 `y` 给出外延事实。递归假设供给桥所需的等式，桥再利用移位后载体坐标处的等式，为 `SatW (qA a)` 给出相应的外延事实。最后，`ext-unique` 中的集合外延性等同两个底层集合。
<!--ja-->
拡張環境において、関係の節は候補の表の値 `y` に関する外延の事実を与えます。再帰仮定が橋渡しに必要な等式を与え、橋渡しは、ずらされた台の座標における等式を使って、`SatW (qA a)` に対応する外延の事実を与えます。最後に `ext-unique` の集合外延性が二つの基礎集合を同定します。
<!--/-->

```agda
                P : S → Type (ℓ-suc ℓ)
                P z = ⟨ (z ∷ env) ⊨ R.quBody q ⟩
            in ext-unique y (SatW (qA a)) (envSet W n) P ext (bridge env (sh 18 w) i2 qw (ia (cl1 c∈) ya ma)) })
          (K.RR.qu-out q (subst (λ φ → ⟨ K.δ12 ⊨ φ ⟩) relIs K.rel) (keyS W a) ya (nn (suc n)) ma refl refl) })
        (sub a (cl1 c∈))
```

<!--en-->
Here `K` is instantiated with the quantified formula `qA a`, not with its body `a`. Its payload representative is constructed from the body's code, while the domain membership and candidate entry belong to the quantified formula's key. The body appears separately as the sole recursive child, at successor arity.
<!--zh-->
这里，`K` 实例化于量化公式 `qA a`，而非其主体 `a`。它的载荷表示由主体码构造，但定义域成员资格与候选表项属于量化公式的键。主体则作为唯一递归子式单独出现，并处于后继元数。
<!--ja-->
ここで `K` が具体化されるのは、量化された論理式 `qA a` であり、その本体 `a` ではありません。ペイロードの表現は本体の符号から作られますが、領域への所属と候補の表項目は量化された論理式のキーに属します。本体は、後続アリティにある唯一の再帰的な子論理式として別に現れます。
<!--/-->

```agda
      where
      module K = Case (qA a) k (payS (qA a) (toℕ k) (cd a) code) code c∈ y mem

```

<!--en-->
For a bounded quantifier, the constructor code has two payload components: the code of the bounding term and the code of the body, whose arity is one larger. The case lemma therefore asks for the constructor tag and payload equation, the corresponding relation clause, a fixed five-slot presentation of its semantic body, an extension bridge for that presentation, and the one closure implication actually needed later: membership of the compound key in the domain implies membership of the body key. No closure condition is imposed on the term code.
<!--zh-->
有界量词的构造子码有两个载荷分量：界定词项的码，以及元数增加一的体公式之码。因此，这个情形引理需要构造子标签与载荷等式、相应的关系子句、用五个槽位固定写出的语义体、该语义体的外延桥，以及随后真正需要的唯一一条封闭蕴涵：复合公式的键属于定义域时，体公式的键也属于定义域。这里不要求定义域对词项码封闭。
<!--ja-->
有界量化子の構成子符号には二つのペイロード成分があります。境界を与える項の符号と、アリティが一つ大きい本体論理式の符号です。そこでこの場合の補題は、構成子のタグとペイロードの等式、対応する関係の節、五つのスロットで固定して表した意味論的本体、その本体に対する外延の橋、そして後で実際に必要となる唯一の閉性の含意を仮定します。その含意は、複合論理式の鍵が領域に属すれば本体の鍵も領域に属すというものです。項の符号について領域の閉性は仮定しません。
<!--/-->

```agda
    bqCase : ∀ {n} (q : ∀ {j} → Term S j → Formula S (suc j) → Formula S j)
             (c : ∀ {j} → Formula S j → Formula S j → Formula S j)
             (qA : Term Ab n → Formula Ab (suc n) → Formula Ab n) (k : Fin 10)
             (t : Term Ab n) (a : Formula Ab (suc n)) (code : cd (qA t a) ≡ pr (# (toℕ k)) (pr (ct t) (cd a)))
             (relIs : R.relN (toℕ k) ≡ R.bqRel q c)
```

<!--en-->
The body equation records how the bounded-quantifier body is spelled with five shifted slots, so that the bridge can be stated at a fixed formula shape without depending on the exact slot indices of the calling site.
<!--zh-->
体等式记录有界量词体在五个平移槽位下的拼写方式，使桥能以固定的公式形状陈述，而不依赖调用点的具体槽位索引。
<!--ja-->
本体の等式は、有界量化子の本体が五つのずらした枠でどのように綴られるかを記録します。これにより、橋を、呼び出し側の正確な枠の添字に依存しない固定された論理式の形で述べられます。
<!--/-->

```agda
             (body : ∀ {j} → Fin j → Fin j → Fin j → Fin j → Fin j → Formula S (1 + j))
             (bodyIs : ∀ {j} (wi ti yai N0i N1i : Fin j)
                     → body wi ti yai N0i N1i
                     ≡ q (var (suc wi)) (c (tmIs (suc (suc ti)) i1 i0 (suc (suc N0i)) (suc (suc N1i)))
                         (q (var (suc (suc wi))) (c (var i0 ∈̇ var i1) (∃̇∈ (var (suc (suc (suc yai)))) (consAtL i0 i1 i3))))))
```

<!--en-->
The bridge identifies the recursively defined satisfaction set of the bounded formula with the extension described by this five-slot body over encoded environments. Its quantifier and connective are still parameters here, so the statement covers both the universal and existential bounded cases; it must not be read as asserting existential membership in every instance. This extension fact is what can be compared with the extension fact extracted from the table clause.
<!--zh-->
这条桥把有界公式的递归满足集与五槽语义体在编码环境上描述的外延对应起来。这里量词与联结词仍是参数，所以同一陈述同时涵盖有界全称与有界存在两种情形，不能一概读成存在某个成员。随后，证明正是把这条外延事实与从表子句读出的外延事实相比较。
<!--ja-->
この橋は、有界論理式について再帰的に定めた充足集合を、符号化された環境上で五つのスロットをもつ意味論的本体が記述する外延と対応させます。ここでは量化子と結合子がまだパラメータなので、同じ主張が有界全称の場合と有界存在の場合の両方を扱います。したがって、すべての場合にある要素の存在を主張していると読んではいけません。証明では、この外延事実を表の節から読み取った外延事実と比較します。
<!--/-->

```agda
             (bridge : ∀ {j} (env : S ^ j) (wi ti yai N0i N1i : Fin j)
                     → fst (lookup wi env) ≡ Wv → fst (lookup ti env) ≡ ct t → fst (lookup yai env) ≡ fst (SatW a)
                     → fst (lookup N0i env) ≡ # 0 → fst (lookup N1i env) ≡ # 1
                     → ExtFact (fst (SatW (qA t a))) (fst (envSet W n)) (λ z → ⟨ (z ∷ env) ⊨ body wi ti yai N0i N1i ⟩))
           → (cl1 : ⟨ fst (keyS W (qA t a)) ∈ Cv ⟩ → ⟨ fst (keyS W a) ∈ Cv ⟩)
```

<!--en-->
Assume that membership of the compound key yields membership of the body key and that entries at the body key are already pinned. Then every supplied entry at the compound key is pinned as well. Totality gives only a merely existing body value, and the bounded-clause reader likewise hides its witnesses propositionally. Both may be eliminated here because the conclusion is an equality of underlying hierarchy sets, hence a proposition. The supplied compound entry itself is not obtained from totality and is not hidden by truncation.
<!--zh-->
假设复合公式的键属于定义域时可以推出体公式的键属于定义域，并且体公式键处的表值已经被钉扎，那么复合公式键处任何给定表值也会被钉扎。全定义性只给出经过命题截断的体公式表值，有界量词子句的读式也只在命题截断下给出其见证。这里可以消去这两层命题截断，因为结论是层级中底层集合的等式，因而是命题。复合公式的表值则由结论的前提直接给定，并非由全定义性取得，也没有藏在命题截断之下。
<!--ja-->
複合論理式の鍵が領域に属すことから本体の鍵が領域に属すことが従い、さらに本体の鍵にある表の値がすでに固定されていると仮定します。このとき、複合論理式の鍵に与えられた任意の表の値も固定されます。全域性が与える本体の値は単に存在するだけであり、有界量化子の節の読み出しもその証人を命題的切り詰めの内側に置きます。結論は階層の基礎集合どうしの等式であり命題なので、ここではその両方を消去できます。一方、複合論理式の表の値は結論の前提として直接与えられており、全域性から得るものでも、切り詰めの内側にあるものでもありません。
<!--/-->

```agda
           → Pinned a → Pinned (qA t a)
    bqCase {n} q c qA k t a code relIs body bodyIs bridge cl1 ia c∈ y mem =
      PT.rec (setIsSet _ _) (λ { (ya , ma) →
        PT.rec (setIsSet _ _)
          (λ { (s , s₁ , s' , e' , ext) →
```

<!--en-->
After the clause witnesses have been read, the proof forms the extended environment containing the successor arity, the body entry and key, the body code, and the bounding-term code. At that one environment, `ext-unique` compares the clause's extension fact for the candidate table value with the bridge's extension fact for the recursive satisfaction value. Transport along the body equation makes the predicates in those two facts identical.
<!--zh-->
读出子句见证后，证明组成一个扩展环境，其中包含后继元数、体公式的表值与键、体公式码，以及界定词项码。在这同一个环境上，`ext-unique` 比较两条外延事实：一条来自子句，刻画候选表值；另一条来自桥，刻画递归定义的满足集。沿体公式等式作运输后，两条事实中的谓词便完全一致。
<!--ja-->
節の証人を読み取った後、証明は後続アリティ、本体の表の値と鍵、本体の符号、そして境界を与える項の符号を含む拡張環境を組み立てます。その同じ環境で、`ext-unique` は二つの外延事実を比較します。一方は候補となる表の値を特徴づける節の外延事実であり、他方は再帰的な充足集合を特徴づける橋の外延事実です。本体の等式に沿って運ぶことで、両者に現れる述語が一致します。
<!--/-->

```agda
            let env = nn (suc n) ∷ s' ∷ ya ∷ keyS W a ∷ s₁ ∷ e' ∷ codeS W a ∷ tS ∷ s ∷ K.δ12
                P : S → Type (ℓ-suc ℓ)
                P z = ⟨ (z ∷ env) ⊨ R.bqBody q c ⟩
            in ext-unique y (SatW (qA t a)) (envSet W n) P ext
                 (subst (λ φ → ExtFact (fst (SatW (qA t a))) (fst (envSet W n)) (λ z → ⟨ (z ∷ env) ⊨ φ ⟩))
```

<!--en-->
The body entry obtained from totality is identified with the recursive satisfaction set by the induction hypothesis, after closure has supplied membership of the body key. Together with the carrier, term-code, and two tag equations, this identification discharges the bridge assumptions. The outward reading of the bounded clause supplies four auxiliary objects and its extension fact, all only for this local comparison.
<!--zh-->
封闭性先给出体公式键的定义域成员关系，归纳假设再把由全定义性取得的体公式表值认同为递归满足集。这个认同与载体等式、词项码等式及两条标签等式一起满足桥的全部前提。有界量词子句的向外读式则给出四个辅助对象和一条外延事实，它们只用于这里的局部比较。
<!--ja-->
まず閉性から本体の鍵が領域に属すことを得て、次に帰納仮定によって、全域性から得た本体の表の値を再帰的な充足集合と同定します。この同定と、台、項の符号、二つのタグに関する等式を合わせると、橋の仮定がすべて満たされます。有界量化子の節を外向きに読むと、四つの補助的な対象と一つの外延事実が得られますが、それらはこの局所的な比較にだけ使われます。
<!--/-->

```agda
                    (bodyIs (sh 21 w) i7 i2 (sh 21 (N f0)) (sh 21 (N f1)))
                    (bridge env (sh 21 w) i7 i2 (sh 21 (N f0)) (sh 21 (N f1)) qw refl (ia (cl1 c∈) ya ma) (tg f0) (tg f1))) })
          (K.RR.bq-out q c (subst (λ φ → ⟨ K.δ12 ⊨ φ ⟩) relIs K.rel) tS (codeS W a) (keyS W a) ya (nn (suc n)) refl ma refl refl) })
        (sub a (cl1 c∈))
      where
```

<!--en-->
Three named components support the case: the payload presented as a carrier element, its first projection carrying the term code, and the case module providing the twelve-slot frame with the table entry at the compound key.
<!--zh-->
三个被命名的分量支撑该情形：呈现为载体元素的载荷、携带词项码的第一投影，以及提供十二槽框架与复合键处表条目的情形模块。
<!--ja-->
名づけられた三つの成分がこの場合を支えます。台の要素として提示されたペイロード、項の符号を載せる第一の射影、そして、合成キーでの表の項目をもつ十二の枠のフレームを供給する場合のモジュールです。
<!--/-->

```agda
      rS : S
      rS = payS (qA t a) (toℕ k) (pr (ct t) (cd a)) code
      tS : S
      tS = fstS rS (ct t) (cd a) refl
      module K = Case (qA t a) k rS code c∈ y mem
```

<!--en-->
An atomic formula has no formula children, so its case needs no closure implication and no recursive hypothesis. Its constructor payload is the pair of two term codes. The remaining assumptions identify the appropriate atomic relation clause and provide a bridge from the carrier equation, the two term-code equations, and the two tag equations to an extension fact for the atom's recursive satisfaction set.
<!--zh-->
原子公式没有公式子式，因此这个情形不需要封闭蕴涵，也不需要递归假设。其构造子载荷是两个词项码组成的对。其余前提识别相应的原子关系子句，并提供一条桥：由载体等式、两条词项码等式和两条标签等式，得到原子公式递归满足集的外延事实。
<!--ja-->
原子論理式には論理式としての子がないので、この場合には閉性の含意も再帰仮定も要りません。構成子のペイロードは二つの項の符号の対です。残りの仮定は、対応する原子関係の節を同定し、台の等式、二つの項の符号の等式、二つのタグの等式から、原子論理式の再帰的な充足集合についての外延事実を与える橋を用意します。
<!--/-->

```agda

    atomCase : ∀ {n} (opA : ∀ {j} → Term Ab j → Term Ab j → Formula Ab j) (k : Fin 10)
               (t u : Term Ab n) (code : cd (opA t u) ≡ pr (# (toℕ k)) (pr (ct t) (ct u)))
               (rel : Formula S (18 + m))
               (relIs : R.relN (toℕ k) ≡ R.atomRel rel)
               (bridge : ∀ (env : S ^ (15 + m)) (wi ti ui N0i N1i : Fin (15 + m))
```

<!--en-->
The bridge parameter states the extension fact for the atomic formula: the satisfaction set contains exactly the environments whose term values satisfy the object-language relation. The conclusion says that this atomic formula is pinned whenever its key lies in the domain and a table entry is supplied.
<!--zh-->
桥参数陈述原子公式的外延事实：满足关系集合恰包含其词项取值满足对象语言关系的那些环境。结论说：只要该原子公式的键属于定义域且给定一个表项，该公式就被钉扎。
<!--ja-->
橋のパラメータは原子論理式の外延事実を述べます。充足関係集合には、項の値が対象言語の関係を満たす環境がちょうど含まれます。結論は、この原子論理式のキーが領域に属し、表項目が与えられていれば、その論理式が固定されることを述べます。
<!--/-->

```agda
                       → fst (lookup wi env) ≡ Wv → fst (lookup ti env) ≡ ct t → fst (lookup ui env) ≡ ct u
                       → fst (lookup N0i env) ≡ # 0 → fst (lookup N1i env) ≡ # 1
                       → ExtFact (fst (SatW (opA t u))) (fst (envSet W n)) (λ z → ⟨ (z ∷ env) ⊨ atomEx wi ti ui N0i N1i rel ⟩))
             → Pinned (opA t u)
    atomCase {n} opA k t u code rel relIs bridge c∈ y mem =
```

<!--en-->
The atomic clause yields merely an auxiliary set together with an extension fact for the candidate table value. In the environment formed from that set and the two term codes, the atomic bridge gives a second extension fact for the recursive satisfaction value. Since equality in the cumulative hierarchy is a proposition, the hidden clause witness can be eliminated and `ext-unique` identifies the two underlying sets.
<!--zh-->
原子子句只在命题截断下给出一个辅助集合，以及刻画候选表值的外延事实。在由该集合与两个词项码组成的环境中，原子桥给出另一条外延事实，刻画递归满足值。累积层级中的等式是命题，因此可以消去命题截断下的子句见证，再由 `ext-unique` 认同两个底层集合。
<!--ja-->
原子の節からは、補助的な集合と候補となる表の値についての外延事実が、単なる存在として得られます。その集合と二つの項の符号から作った環境では、原子の橋が再帰的な充足値について第二の外延事実を与えます。累積階層の等式は命題なので、節の隠された証人を消去でき、`ext-unique` によって二つの基礎集合が同定されます。
<!--/-->

```agda
      PT.rec (setIsSet _ _)
        (λ { (s , ext) →
          let env = uS ∷ tS ∷ s ∷ K.δ12
              P : S → Type (ℓ-suc ℓ)
              P z = ⟨ (z ∷ env) ⊨ R.atomBody rel ⟩
```

<!--en-->
The bridge is applied at the extended environment with the two tag equations and the carrier equation, producing the extension fact for the atomic body. The outward reading of the atomic relation supplies the intermediate set.
<!--zh-->
桥在扩展环境处以两条标签等式与载体等式被应用，产出原子体的外延事实。原子关系的向外读法供给中间集合。
<!--ja-->
橋は、拡張された環境で、二つのタグの等式と台の等式とともに適用され、原子の本体の外延の事実を作ります。原子の関係の外向きの読み出しが、中間の集合を供給します。
<!--/-->

```agda
          in ext-unique y (SatW (opA t u)) (envSet W n) P ext
               (bridge env (sh 15 w) i1 i0 (sh 15 (N f0)) (sh 15 (N f1)) qw refl refl (tg f0) (tg f1)) })
        (K.RR.atom-out rel (subst (λ φ → ⟨ K.δ12 ⊨ φ ⟩) relIs K.rel) tS uS refl)
      where
      rS : S
```

<!--en-->
Three named components support the atomic case: the payload as a carrier element, the two term codes as its first and second projections, and the case module providing the twelve-slot frame.
<!--zh-->
三个被命名的分量支撑原子情形：作为载体元素的载荷、其第一与第二投影处的两个词项码，以及提供十二槽框架的情形模块。
<!--ja-->
名づけられた三つの成分が原子の場合を支えます。台の要素としてのペイロード、その第一と第二の射影としての二つの項の符号、そして十二の枠のフレームを供給する場合のモジュールです。
<!--/-->

```agda
      rS = payS (opA t u) (toℕ k) (pr (ct t) (ct u)) code
      tS uS : S
      tS = fstS rS (ct t) (ct u) refl
      uS = sndS rS (ct t) (ct u) refl
      module K = Case (opA t u) k rS code c∈ y mem
```

<!--en-->
For the membership atom, satisfaction at the displayed environment is definitionally the same proposition as membership of the two underlying sets. The two implications in `memAgree` are therefore identities. This is the local agreement needed by the atomic bridge; it makes no statement about other relation symbols.
<!--zh-->
对这个隶属原子而言，在所示环境中的满足关系依定义就是两个底层集合之间的隶属命题。因此，`memAgree` 中的两个方向都是恒等映射。这只是原子桥在此处需要的局部相合，并未对其他关系符号作出陈述。
<!--ja-->
この所属原子では、表示された環境における充足は、二つの基礎集合の間の所属命題と定義上同じです。したがって `memAgree` の二つの向きはいずれも恒等写像です。これは原子の橋がこの箇所で必要とする局所的な一致であり、ほかの関係記号については何も主張しません。
<!--/-->

```agda

    memAgree : ∀ {j} (env : S ^ j) (z v x : S)
             → (⟨ (x ∷ v ∷ z ∷ env) ⊨ var i1 ∈̇ var i0 ⟩ → ⟨ fst v ∈ fst x ⟩) × (⟨ fst v ∈ fst x ⟩ → ⟨ (x ∷ v ∷ z ∷ env) ⊨ var i1 ∈̇ var i0 ⟩)
    memAgree env z v x = (λ h → h) , (λ h → h)

```

<!--en-->
The equality agreement says the same for the equality atom: the object-language equality is the identity of the underlying sets.
<!--zh-->
相等相合对相等原子说同样的话：对象语言的相等就是底层集合的等同。
<!--ja-->
等号の一致は、等号の原子についても同じことを言います。対象言語の等号は、基礎の集合の同一性です。
<!--/-->

```agda
    eqAgree : ∀ {j} (env : S ^ j) (z v x : S)
            → (⟨ (x ∷ v ∷ z ∷ env) ⊨ var i1 ≐ var i0 ⟩ → fst v ≡ fst x) × ((fst v ≡ fst x) → ⟨ (x ∷ v ∷ z ∷ env) ⊨ var i1 ≐ var i0 ⟩)
    eqAgree env z v x = (λ h → h) , (λ h → h)
```

<!--en-->
The closure lemma for binary connectives reads the downward closure from the shape satisfaction: if the composite key lies in the domain, then both component keys lie in the domain. The proof is one application of the binary-closure elimination.
<!--zh-->
二元联结词的闭包引理从形状满足读取向下闭包：若复合键在域中，则两个分量键都在域中。证明是二元闭包消去的一次应用。
<!--ja-->
二項の結合子のための閉じの補題は、形の充足から下向きの閉じを読み出します。合成キーが領域にあれば、両方の成分キーも領域にある、というものです。証明は、二項の閉じの消去を一度適用するだけです。
<!--/-->

```agda
    clSame : (n k : ℕ) → ⟨ γ ⊨ binShapeAt C k (bothSameAt C) ⟩
           → (ψ a b : Formula Ab n) → cd ψ ≡ pr (# k) (pr (cd a) (cd b))
           → ⟨ fst (keyS W ψ) ∈ Cv ⟩ → ⟨ fst (keyS W a) ∈ Cv ⟩ × ⟨ fst (keyS W b) ∈ Cv ⟩
    clSame n k h ψ a b e c∈ =
      binSameClosed-out C k γ h (keyS W ψ) (nn n) (codeS W a) (codeS W b) c∈ (cong (pr (# n)) e)
```

<!--en-->
The next form of the binary closure lemma fixes the two child formulas before the shape proof is supplied. Its conclusion is unchanged: domain membership of a key whose payload is the pair of those two formula codes yields domain membership of both child keys. This order lets each structural-recursion branch specialize the common closure fact to its own two children.
<!--zh-->
下面的二元封闭引理先固定两个子公式，再接收形状证明。其结论并未改变：若某个键的载荷是这两个公式码组成的对，则该键属于定义域便推出两个子公式的键都属于定义域。这样的参数次序使结构递归的每个分支都能把共同的封闭事实专门用于自己的两个子公式。
<!--ja-->
次の形の二項閉性補題では、形の証明を受け取る前に二つの子論理式を固定します。結論は変わりません。ペイロードがその二つの論理式の符号の対である鍵が領域に属すれば、両方の子の鍵も領域に属します。この引数順序により、構造再帰の各分岐は共通の閉性の事実を自分の二つの子に特殊化できます。
<!--/-->

```agda

    clBin : (n k : ℕ) (a b : Formula Ab n)
          → ⟨ γ ⊨ binShapeAt C k (bothSameAt C) ⟩
          → (ψ : Formula Ab n) → cd ψ ≡ pr (# k) (pr (cd a) (cd b))
          → ⟨ fst (keyS W ψ) ∈ Cv ⟩ → ⟨ fst (keyS W a) ∈ Cv ⟩ × ⟨ fst (keyS W b) ∈ Cv ⟩
    clBin n k a b h ψ e = clSame n k h ψ a b e
```

<!--en-->
For an unbounded quantifier, closure follows the sole formula component of the constructor payload. Thus, if the key of the quantified formula at arity `n` lies in the domain, then the key of its body at successor arity lies there as well. The statement is local to this presented constructor code; it does not decode arbitrary domain elements.
<!--zh-->
对无界量词而言，封闭性只沿构造子载荷中唯一的公式分量向下。因此，若元数为 `n` 的量化公式之键属于定义域，则其后继元数处的体公式之键也属于定义域。这个陈述只针对当前给出的构造子码，并不解码任意定义域成员。
<!--ja-->
非有界量化子では、閉性は構成子のペイロードに含まれる唯一の論理式成分だけをたどります。したがって、アリティ `n` の量化された論理式の鍵が領域に属すれば、後続アリティにある本体の鍵も領域に属します。この主張は、ここで提示された構成子符号に局所的なものであり、領域の任意の要素を復号するものではありません。
<!--/-->

```agda

    clQu : (n k : ℕ) (a : Formula Ab (suc n)) (ψ : Formula Ab n)
         → ⟨ γ ⊨ unShapeAt C k (oneSuccAt C) ⟩ → cd ψ ≡ pr (# k) (cd a)
         → ⟨ fst (keyS W ψ) ∈ Cv ⟩ → ⟨ fst (keyS W a) ∈ Cv ⟩
    clQu n k a ψ h e c∈ =
      unSuccClosed-out C k γ h (keyS W ψ) (nn n) (codeS W a) c∈ (cong (pr (# n)) e)
```

<!--en-->
For a bounded quantifier, the payload contains a term code first and a body-formula code second. The closure condition follows only the second component: membership of the compound key implies membership of the body key at successor arity. It deliberately yields no domain-membership claim for the bounding term code.
<!--zh-->
有界量词的载荷以词项码为第一分量，以体公式码为第二分量。封闭条件只沿第二分量向下：复合公式的键属于定义域，便推出后继元数处的体公式之键属于定义域。它有意不对界定词项码给出任何定义域成员关系。
<!--ja-->
有界量化子のペイロードでは、第一成分が項の符号、第二成分が本体論理式の符号です。閉性の条件がたどるのは第二成分だけであり、複合論理式の鍵が領域に属すことから、後続アリティにある本体の鍵が領域に属すことを導きます。境界を与える項の符号について、領域への所属は意図的に何も結論しません。
<!--/-->

```agda

    clBq : (n k : ℕ) (t : Term Ab n) (a : Formula Ab (suc n)) (ψ : Formula Ab n)
         → ⟨ γ ⊨ binShapeAt C k (succSndAt C) ⟩ → cd ψ ≡ pr (# k) (pr (ct t) (cd a))
         → ⟨ fst (keyS W ψ) ∈ Cv ⟩ → ⟨ fst (keyS W a) ∈ Cv ⟩
    clBq n k t a ψ h e c∈ =
      binSuccClosed-out C k γ h (keyS W ψ) (nn n) tS (codeS W a) c∈ (cong (pr (# n)) e)
```

<!--en-->
Two named components support the bounded-quantifier closure: the payload presented as a carrier element, and its first projection carrying the term code.
<!--zh-->
两个被命名的分量支撑有界量词闭包：呈现为载体元素的载荷，及其携带词项码的第一投影。
<!--ja-->
名づけられた二つの成分が、有界量化子のための閉じを支えます。台の要素として提示されたペイロードと、項の符号を載せるその第一の射影です。
<!--/-->

```agda
      where
      pS : S
      pS = sndS (codeS W ψ) (# k) (pr (ct t) (cd a)) e
      tS : S
      tS = fstS pS (ct t) (cd a) refl
```

<!--en-->
The pinned predicate is proved by structural recursion on the formula. The membership atom applies the atomic case with the identity agreement for the membership relation, consuming no subformula hypotheses.
<!--zh-->
钉扎谓词由公式的结构递归证明。隶属原子以隶属关系的恒等相合应用原子情形，不消耗任何子公式假设。
<!--ja-->
釘づけの述語は、論理式の構造についての構造再帰で証明されます。所属の原子は、所属の関係に対する恒等の一致とともに原子の場合を適用し、下位の論理式の仮定を一切消費しません。
<!--/-->

```agda

  pinned : ∀ {n} (ψ : Formula Ab n) → Pinned ψ
  pinned (t ∈̇ u) = atomCase _∈̇_ f0 t u refl (var i1 ∈̇ var i0) refl
    (λ env wi ti ui N0i N1i qw' qt qu q0 q1 →
      AtomBridge.atomBridge t u env wi ti ui N0i N1i qw' qt qu q0 q1 _∈̇_ (λ v x → ⟨ v ∈ x ⟩)
        (var i1 ∈̇ var i0) (memAgree env) (λ δ h → h) (λ δ h → h))
```

<!--en-->
The equality atom applies the atomic case with the identity agreement for equality. The conjunction case applies the binary case with the conjunction bridge and the binary closure at tag two, consuming the pinned hypotheses for both subformulas.
<!--zh-->
相等原子以相等的恒等相合应用原子情形。合取情形以合取桥与标签二处的二元闭包应用二元情形，消耗两个子公式的已钉扎假设。
<!--ja-->
等号の原子は、等号に対する恒等の一致とともに原子の場合を適用します。連言の場合は、連言の橋とタグ二での二項の閉じとともに二項の場合を適用し、二つの下位の論理式の釘づけの仮定を消費します。
<!--/-->

```agda
  pinned (t ≐ u) = atomCase _≐_ f1 t u refl (var i1 ≐ var i0) refl
    (λ env wi ti ui N0i N1i qw' qt qu q0 q1 →
      AtomBridge.atomBridge t u env wi ti ui N0i N1i qw' qt qu q0 q1 _≐_ (λ v x → v ≡ x)
        (var i1 ≐ var i0) (eqAgree env) (λ δ h → h) (λ δ h → h))
  pinned {n} (a ∧̇ b) = binCase _∧̇_ _∧̇_ f2 a b refl refl (andBridge a b) (clBin n 2 a b (hcl .fst) (a ∧̇ b) refl) (pinned a) (pinned b)
```

<!--en-->
Disjunction and implication follow the same binary pattern at their own tags. Falsity has no subformulas: its uniqueness is proved directly from the outward reading of the falsity clause and the falsity bridge, which together produce the empty extension.
<!--zh-->
析取与蕴涵在各自标签处遵循同一二元模式。假无子公式：其唯一性由假子句的向外读法与假桥直接证明，二者共同产出空外延。
<!--ja-->
選言と含意は、それぞれのタグで同じ二項のパターンに従います。偽には下位の論理式がなく、その一意性は、偽の条項の外向きの読み出しと偽の橋から直接証明されます。両方が合わせて空の外延を作るからです。
<!--/-->

```agda
  pinned {n} (a ∨̇ b) = binCase _∨̇_ _∨̇_ f3 a b refl refl (orBridge a b) (clBin n 3 a b (hcl .snd .fst) (a ∨̇ b) refl) (pinned a) (pinned b)
  pinned {n} (a ⇒̇ b) = binCase _⇒̇_ _⇒̇_ f4 a b refl refl (impBridge a b) (clBin n 4 a b (hcl .snd .snd .fst) (a ⇒̇ b) refl) (pinned a) (pinned b)
  pinned {n} ⊥̇ c∈ y mem = ext-unique y (SatW ⊥̇) (envSet W n) (λ z → ⟨ (z ∷ K.δ12) ⊨ ⊥̇ ⟩) (extB-out i0 i8 ⊥̇ K.δ12 K.rel) (botBridge n K.δ12)
    where
    module K = Case ⊥̇ f5 (nn 0) refl c∈ y mem
```

<!--en-->
The two unbounded quantifier branches use the existential and universal bridges. Closure moves from the quantified formula's key to the body key at successor arity, and the recursive hypothesis pins the body value needed by the bridge. The bounded universal branch follows the same local pattern, but its constructor code also contains a term code; it invokes the bounded case with the universal `∀[]-syntax` bridge, while closure still follows only the body.
<!--zh-->
两个无界量词分支分别使用存在桥与全称桥。封闭性把量化公式键的定义域成员关系传到后继元数处的体公式键，递归假设再钉扎桥所需的体公式值。有界全称分支遵循同样的局部模式，但它的构造子码还含有一个词项码；它以全称 `∀[]-syntax` 桥调用有界情形，而封闭性仍然只沿体公式向下。
<!--ja-->
二つの非有界量化子の分岐は、それぞれ存在の橋と全称の橋を使います。閉性によって量化された論理式の鍵から後続アリティの本体の鍵へ領域への所属を移し、再帰仮定によって橋が必要とする本体の値を固定します。有界全称の分岐も同じ局所的な形を取りますが、その構成子符号には項の符号も含まれます。この分岐は全称の `∀[]-syntax` の橋を用いて有界の場合を適用し、閉性はここでも本体だけをたどります。
<!--/-->

```agda
  pinned {n} (∃̇ a) = quCase ∃̇∈ ∃̇_ f6 a refl refl (exBridge a) (clQu n 6 a (∃̇ a) (hcl .snd .snd .snd .fst) refl) (pinned a)
  pinned {n} (∀̇ a) = quCase ∀̇∈ ∀̇_ f7 a refl refl (allBridge a) (clQu n 7 a (∀̇ a) (hcl .snd .snd .snd .snd .fst) refl) (pinned a)
  pinned {n} (∀̇∈ t a) = bqCase ∀̇∈ _⇒̇_ ∀̇∈ f8 t a refl refl bqAll (λ _ _ _ _ _ → refl)
    (λ env wi ti yai N0i N1i qw' qt qa q0 q1 → BqBridge.allInBridge t a env wi ti yai N0i N1i qw' qt qa q0 q1)
    (clBq n 8 t a (∀̇∈ t a) (hcl .snd .snd .snd .snd .snd .fst) refl) (pinned a)
```

<!--en-->
The bounded existential branch invokes the bounded case with the existential `∃[]-syntax` bridge. Its closure conjunct supplies domain membership only for the body key at successor arity, after which the recursive hypothesis pins the body entry. The bounding term is evaluated by the bridge and does not become another recursive subproblem.
<!--zh-->
有界存在分支以存在 `∃[]-syntax` 桥调用有界情形。相应的封闭合取项只给出后继元数处体公式键的定义域成员关系，递归假设随后钉扎该体公式的表值。界定词项由桥求值，不会成为另一个递归子问题。
<!--ja-->
有界存在の分岐は、存在の `∃[]-syntax` の橋を用いて有界の場合を適用します。対応する閉性の成分が与えるのは、後続アリティにある本体の鍵の領域への所属だけであり、その後で再帰仮定が本体の表の値を固定します。境界を与える項は橋の中で評価され、別の再帰部分問題にはなりません。
<!--/-->

```agda
  pinned {n} (∃̇∈ t a) = bqCase ∃̇∈ _∧̇_ ∃̇∈ f9 t a refl refl bqEx (λ _ _ _ _ _ → refl)
    (λ env wi ti yai N0i N1i qw' qt qa q0 q1 → BqBridge.exInBridge t a env wi ti yai N0i N1i qw' qt qa q0 q1)
    (clBq n 9 t a (∃̇∈ t a) (hcl .snd .snd .snd .snd .snd .snd) refl) (pinned a)
```

<!--en-->
## Filling all satisfaction clauses
<!--zh-->
## 填充全部满足关系子句
<!--ja-->
## すべての充足関係の節を満たす
<!--/-->

<!--en-->
We now prove the converse direction. Rather than extracting recursive values from clauses, we assume that represented values already agree with the recursively defined satisfaction sets and use that agreement to verify every clause. The working set `W` fixes the alphabet, the satisfaction bridges, and the constructor-code matching used throughout this argument.
<!--zh-->
下面证明反向论证。这里不是从子句推出递归值，而是假设已经表示出的表值与递归定义的满足集相合，再用这种相合验证每一条子句。工作集 `W` 固定整个论证使用的字母表、满足关系桥与构造子码匹配。
<!--ja-->
ここから逆向きの接続を証明します。節から再帰的な値を取り出すのではなく、表に表示された値がすでに再帰的に定めた充足集合と一致すると仮定し、その一致を使って各節を検証します。作業集合 `W` は、この向きで一貫して使うアルファベット、充足の橋、構成子符号の照合を定めます。
<!--/-->

```agda
module _ (W : S) where
  open Alphabet W
  open Bridge W
  open Match W

```

<!--en-->
Fix the table, carrier, code-domain, and environment-tower slots in one environment, together with the ten numeral tags and the tower specification. The decisive hypothesis `val≡` is conditional: for a known formula key and a supplied table entry at that key, it identifies the entry's underlying value with the formula's recursively defined satisfaction set. It neither asserts that every key is represented nor chooses an entry.
<!--zh-->
在同一个环境中固定表、载体、公式码定义域与环境塔的槽位，并给出十个数码标签和环境塔规格。关键假设 `val≡` 是条件性的：对一个已知公式键以及该键处给定的表条目，它把条目的底层值认同为该公式递归定义的满足集。它既不声称每个键都有表示，也不选择任何表条目。
<!--ja-->
一つの環境の中で、表、台、論理式符号の領域、環境の塔の各スロットを固定し、十個の数項タグと塔の仕様を与えます。中心となる仮定 `val≡` は条件付きです。既知の論理式の鍵と、その鍵にある与えられた表の要素に対して、その要素の基礎の値を論理式の再帰的な充足集合と同定します。すべての鍵が表されるとは主張せず、表の要素を選ぶこともしません。
<!--/-->

```agda
  module SatHoldsC {m : ℕ} (T w C E : Fin m) (N : Fin 10 → Fin m) (γ : S ^ m)
    (qw : fst (lookup w γ) ≡ fst W) (tg : Tags γ N)
    (hE : ⟨ γ ⊨ towerAt E w (N f0) ⟩)
    (val≡ : ∀ {n} (ψ : Formula Ab n) (c yc : S) → fst c ≡ fst (keyS W ψ)
          → ⟨ pr (fst c) (fst yc) ∈ fst (lookup T γ) ⟩ → fst yc ≡ fst (SatW ψ))
```

<!--en-->
Three further assumptions provide existence only under propositional truncation. A domain member presented as an arity-code pair merely decodes to a formula of that stated arity; totality merely supplies some table value at each domain key; and every table member merely decomposes into a key-value pair whose key belongs to the domain. None of these assumptions defines a reusable decoder or value-selection function.
<!--zh-->
另外三个假设只在命题截断下提供存在性。若一个定义域成员被表示为元数码与载荷之对，则仅能得到同一元数的某个公式解码；全定义性仅给出每个定义域键处某个表值的存在；每个表成员也仅能在命题截断下分解为键值对，并证明其中的键属于定义域。这些假设都没有定义可复用的解码函数或表值选择函数。
<!--ja-->
さらに三つの仮定は、命題的切り詰めの下でのみ存在を与えます。領域の要素がアリティ符号とペイロードの対として提示されると、指定されたそのアリティの論理式へ単に復号できるだけです。全域性は各領域の鍵にある何らかの表の値を単に与え、表の各要素も、鍵が領域に属す鍵と値の対へ単に分解されます。これらの仮定はいずれも、再利用できる復号関数や値の選択関数を定めません。
<!--/-->

```agda
    (decode : (c : S) → ⟨ fst c ∈ fst (lookup C γ) ⟩ → (n : ℕ) (z : V ℓ)
            → fst c ≡ pr (# n) z → ∥ Σ[ ψ ∈ Formula Ab n ] (z ≡ cd ψ) ∥₁)
    (tot : (c : S) → ⟨ fst c ∈ fst (lookup C γ) ⟩
         → ∥ Σ[ yc ∈ S ] ⟨ pr (fst c) (fst yc) ∈ fst (lookup T γ) ⟩ ∥₁)
    (onc : (e : S) → ⟨ fst e ∈ fst (lookup T γ) ⟩
```

<!--en-->
The final assumption finishes the domain condition by requiring every represented table element to be merely a pair `(c,yc)` with `c` in the stated code domain. Thus totality controls entries from keys to values, while this condition controls table members back to domain keys. The abbreviations `Tv` and `Cv` name only the underlying table and domain sets used in these local statements.
<!--zh-->
最后一个假设补全定义域条件：每个已经表示在表中的成员，都只在命题截断下被识别为某个对 `(c,yc)`，并且 `c` 属于给定的公式码定义域。因此，全定义性控制从键到表值的方向，这条条件则控制从表成员回到定义域键的方向。缩写 `Tv` 与 `Cv` 只命名这些局部陈述所用的底层表集合与定义域集合。
<!--ja-->
最後の仮定は領域条件を完成させます。表に表示された各要素は、指定された符号領域に `c` が属すような対 `(c,yc)` として、単に存在するものとして同定されます。したがって全域性は鍵から値への向きを制御し、この条件は表の要素から領域の鍵へ戻る向きを制御します。略記 `Tv` と `Cv` は、これらの局所的な主張で使う表と領域の基礎集合を名づけるだけです。
<!--/-->

```agda
         → ∥ Σ[ c ∈ S ] Σ[ yc ∈ S ] ((fst e ≡ pr (fst c) (fst yc)) × ⟨ fst c ∈ fst (lookup C γ) ⟩) ∥₁)
    where
    private
      Tv = fst (lookup T γ)
      Cv = fst (lookup C γ)
```

<!--en-->
We also name the underlying environment-tower set and the carrier. The frame, clause, and relation readers then express the same stored data at three scales: the common twelve-object frame, the top-level table conditions, and the constructor-specific relation. These are local views of the fixed environment, not new mathematical assumptions.
<!--zh-->
这里还命名环境塔的底层集合与载体。随后，框架、子句与关系的读式在三个尺度上表达同一批已存数据：十二对象组成的共同框架、表的顶层条件，以及依构造子而定的关系。它们只是对固定环境的局部读法，并没有增加新的数学假设。
<!--ja-->
さらに、環境の塔の基礎集合と台を名づけます。枠、節、関係の読み出しは、同じ格納データを三つの尺度で表します。十二個の対象からなる共通の枠、表の最上位の条件、そして構成子ごとの関係です。これらは固定された環境の局所的な見方であり、新しい数学的仮定ではありません。
<!--/-->

```agda
      Ev = fst (lookup E γ)
      Wv = fst W
      module Fr = Frame T w C E N γ tg
      module Cl = Clause T w C E N
      module R = Rel T w N
```

<!--en-->
`Arity ar F` says merely that `ar` is the numeral of some natural number `n` and that `F` is the corresponding encoded-environment set `envSet W n`. The witness `n` remains under propositional truncation, so this type records the arity information needed for a proposition-valued proof without choosing an arity for later computation.
<!--zh-->
`Arity ar F` 表示：只在命题截断下，存在自然数 `n`，使 `ar` 是 `n` 的数码，并且 `F` 是相应的编码环境集 `envSet W n`。见证 `n` 始终留在命题截断之下，因此这个类型只记录命题值证明所需的元数信息，并不为后续计算选择一个元数。
<!--ja-->
`Arity ar F` は、ある自然数 `n` が単に存在し、`ar` が `n` の数項であり、`F` が対応する符号化環境の集合 `envSet W n` であることを述べます。証人 `n` は命題的切り詰めの内側に留まるので、この型は命題値の証明に必要なアリティ情報を記録するだけで、後の計算に使うアリティを選びません。
<!--/-->

```agda
      Arity : (ar F : S) → Type (ℓ-suc ℓ)
      Arity ar F = ∥ Σ[ n ∈ ℕ ] ((fst ar ≡ # n) × (fst F ≡ fst (envSet W n))) ∥₁

```

<!--en-->
To obtain such arity evidence, present an element `q` of the environment tower as the pair `(ar,F)`. The tower specification, together with the carrier equation and the zero-tag equation, is then sufficient to read that pair as a merely existing natural arity and its canonical environment set.
<!--zh-->
要取得这样的元数证据，先把环境塔中的成员 `q` 表示为对 `(ar,F)`。于是，环境塔规格连同载体等式与零标签等式，足以把该对读成只在命题截断下存在的自然数元数及其典范环境集。
<!--ja-->
このアリティの証拠を得るには、環境の塔の要素 `q` を対 `(ar,F)` として提示します。すると塔の仕様に、台の等式と零タグの等式を合わせることで、その対から、単に存在する自然数アリティとその正準な環境集合を読み取れます。
<!--/-->

```agda
      arity : (q ar F : S) → ⟨ fst q ∈ Ev ⟩ → fst q ≡ pr (fst ar) (fst F) → Arity ar F
      module TR = TowerRead E w (N f0) γ W qw (tg f0) hE

```

<!--en-->
The pair equation transports the membership proof from `q` to the displayed pair `(ar,F)`. The tower-entry theorem then returns `Arity ar F`, still under propositional truncation. This step extracts exactly the local arity evidence and does not define a global inverse to the tower encoding.
<!--zh-->
对等式先把 `q` 的成员关系证明运输到所展示的对 `(ar,F)` 上，环境塔条目定理随后给出仍处于命题截断之下的 `Arity ar F`。这一步只抽取当前条目所需的局部元数证据，并没有定义环境塔编码的全局逆函数。
<!--ja-->
対の等式によって、`q` の所属証明を表示された対 `(ar,F)` へ運びます。続いて塔の要素に関する定理が、命題的切り詰めの内側にあるまま `Arity ar F` を返します。この段階で取り出すのは現在の要素に必要な局所的アリティ証拠だけであり、塔の符号化に対する大域的な逆関数は定めません。
<!--/-->

```agda
      arity q ar F q∈ eq = TR.entry-out ar F (subst (λ u → ⟨ u ∈ Ev ⟩) eq q∈)

```

<!--en-->
The first top-level table condition is totality on the stated code domain. The hypothesis `tot` already gives exactly its semantic content, with each value existing only propositionally, so the frame lemma converts it directly into satisfaction of the object-language totality clause.
<!--zh-->
表的第一条顶层条件是在给定公式码定义域上的全定义性。假设 `tot` 已经给出这条条件的确切语义内容，其中每个表值只在命题截断下存在；框架引理因此可直接把它化为对象语言全定义性子句的满足证明。
<!--ja-->
表に対する第一の最上位条件は、指定された論理式符号の領域上での全域性です。仮定 `tot` はすでにその意味内容を正確に与えており、各値は単に存在するだけです。そこで枠の補題は、この仮定を対象言語の全域性の節が充足されることへ直接変換します。
<!--/-->

```agda
      total : ⟨ γ ⊨ Cl.total ⟩
      total = Fr.total-in tot

```

<!--en-->
The second top-level condition says that every represented table element lies over a key in the stated domain. The hypothesis `onc` is precisely this condition at the level of underlying sets, so the frame lemma turns it into satisfaction of the corresponding object-language clause.
<!--zh-->
第二条顶层条件说，每个已经表示在表中的成员都位于给定定义域的某个键之上。假设 `onc` 正是在底层集合层面陈述这一条件，因此框架引理把它化为相应对象语言子句的满足证明。
<!--ja-->
第二の最上位条件は、表に表示された各要素が、指定された領域の鍵の上にあることを述べます。仮定 `onc` は基礎集合の水準でまさにこの条件を表すので、枠の補題によって対応する対象言語の節の充足へ変換できます。
<!--/-->

```agda
      onC : ⟨ γ ⊨ Cl.onC ⟩
      onC = Fr.onC-in onc
```

<!--en-->
Each constructor clause is tested on the same twelve-object configuration. The fields listed first record those objects: a tower entry and its arity and environment set, a code-domain element and its constructor payload, and a table entry with its value, together with the auxiliary witnesses required by the object-language formula.
<!--zh-->
每条构造子子句都在同一种十二对象配置上检验。前面的字段记录这些对象：一个环境塔条目及其元数与环境集，一个公式码定义域成员及其构造子载荷，一个表条目及其取值，以及对象语言公式所需的辅助见证。
<!--ja-->
各構成子の節は、同じ十二対象の配置について検証されます。最初のフィールド群はそれらの対象を記録します。すなわち、塔の要素とそのアリティおよび環境集合、論理式符号の領域の要素とその構成子ペイロード、表の要素とその値、そして対象言語の論理式が必要とする補助的な証人です。
<!--/-->

```agda
      record Args (k : Fin 10) : Type (ℓ-suc ℓ) where
        field
          q ar F s c p s1 r s2 e yc s3 : S
          q∈ : ⟨ fst q ∈ Ev ⟩
          eq : fst q ≡ pr (fst ar) (fst F)
```

<!--en-->
The remaining fields state the relations that make those objects one coherent frame. They say that the tower element is the arity-environment pair, the code lies in the domain and splits into arity, tag, and payload, and the table element lies in the table and splits into that code and its proposed value. These are local presentation equations, not uniqueness or global decoding claims.
<!--zh-->
其余字段陈述把这些对象连成一个一致框架的关系：环境塔成员是元数与环境集组成的对；公式码属于定义域，并分解为元数、标签与载荷；表成员属于表，并分解为该公式码与其候选值。这些只是局部表示等式，并不声称唯一性，也不声称存在全局解码。
<!--ja-->
残りのフィールドは、それらの対象を一つの整合した枠にする関係を述べます。塔の要素がアリティと環境集合の対であること、論理式の符号が領域に属してアリティ、タグ、ペイロードへ分かれること、そして表の要素が表に属してその符号と候補値へ分かれることです。これらは局所的な表示の等式であり、一意性や大域的な復号を主張しません。
<!--/-->

```agda
          c∈ : ⟨ fst c ∈ Cv ⟩
          ec : fst c ≡ pr (fst ar) (fst p)
          ep : fst p ≡ pr (# (toℕ k)) (fst r)
          e∈ : ⟨ fst e ∈ Tv ⟩
          ee : fst e ≡ pr (fst c) (fst yc)
```

<!--en-->
Fixing a tag and one coherent twelve-object frame isolates a single constructor-clause problem. All later arguments in this scope refer to the same objects and equations, so the proof can concentrate on how that tag's payload determines the required extension fact.
<!--zh-->
固定一个标签及一组一致的十二对象框架，就把问题缩小为验证单独一条构造子子句。此后这一范围内的所有论证都使用同一批对象与等式，证明因而可以专注于该标签的载荷如何决定所需的外延事实。
<!--ja-->
一つのタグと、整合した十二対象の枠を固定すると、問題は一つの構成子の節を検証することに絞られます。この範囲で後に行う議論はすべて同じ対象と等式を使うので、そのタグのペイロードが必要な外延事実をどのように定めるかに集中できます。
<!--/-->

```agda

      module Fill (k : Fin 10) (A : Args k) where
        open Args A

```

<!--en-->
The frame prepends the twelve objects in the exact coordinate order expected by the clause formula: `yc`, `s3`, `e`, `r`, `s2`, `p`, `s1`, `c`, `F`, `ar`, `s`, and `q`, followed by the original environment `γ`. Thus the proposed value, table entry, constructor payload, formula code, environment set, arity, and tower entry are interleaved with the four auxiliary witnesses at precisely the indices used by the clause.
<!--zh-->
框架依子句公式所需的精确坐标次序，把十二个对象 `yc`、`s3`、`e`、`r`、`s2`、`p`、`s1`、`c`、`F`、`ar`、`s`、`q` 添加在原环境 `γ` 之前。因此，候选取值、表项、构造子载荷、公式码、环境集、元数与环境塔条目同四个辅助见证交错排列，并且恰好落在子句所使用的索引处。
<!--ja-->
枠は、節の論理式が要求する正確な座標順に、十二個の対象 `yc`、`s3`、`e`、`r`、`s2`、`p`、`s1`、`c`、`F`、`ar`、`s`、`q` を元の環境 `γ` の前へ加えます。したがって、候補値、表項目、構成子のペイロード、論理式符号、環境集合、アリティ、塔の項目は四つの補助的な証人を間に挟みながら、節が用いる添字に正確に置かれます。
<!--/-->

```agda
        frame : S ^ (12 + m)
        frame = yc ∷ s3 ∷ e ∷ r ∷ s2 ∷ p ∷ s1 ∷ c ∷ F ∷ ar ∷ s ∷ q ∷ γ

```

<!--en-->
At this fixed frame, the relation theorem for a tag can be read or constructed in terms of its semantic extension condition. The filling proof uses the constructive direction: once the decoded payload and the prescribed child values provide the right extension fact, the tag's relation clause follows.
<!--zh-->
在这个固定框架上，标签对应的关系定理可在其语义外延条件与对象语言关系子句之间双向转换。填充证明使用构造方向：一旦解码出的载荷与给定的子公式值产生正确的外延事实，相应标签的关系子句便随之成立。
<!--ja-->
この固定された枠では、タグに対応する関係の定理を、その意味論的な外延条件と対象言語の関係の節との間で双方向に使えます。充足を組み立てる証明が使うのは構成する向きです。復号されたペイロードとあらかじめ定められた子の値から正しい外延事実が得られれば、そのタグの関係の節が従います。
<!--/-->

```agda
        module RR = RelRead T w N frame

```

<!--en-->
The goal of each filling case is the satisfaction of the relation clause for the given tag at the twelve-slot frame.
<!--zh-->
每个填充情形的目标是在十二槽框架处、对给定标签的关系子句的满足。
<!--ja-->
それぞれの充填の場合の目標は、十二の枠のフレームで、与えられたタグに対する関係の条項の充足です。
<!--/-->

```agda
        Goal : Type (ℓ-suc ℓ)
        Goal = ⟨ frame ⊨ R.relN (toℕ k) ⟩

```

<!--en-->
This goal is proposition-valued because satisfaction of any formula in the structure is an h-proposition. That fact is the exact elimination boundary used later: the merely decoded arity, formula, and constructor shape may be consumed to prove this goal, but they cannot be extracted as reusable computational data.
<!--zh-->
这个目标取值于命题，因为该结构中任意公式的满足关系都是 h-命题。这正是后面使用命题截断消去的边界：只在命题截断下得到的元数、公式与构造子形状可以被用于证明此目标，却不能被抽取成可复用的计算数据。
<!--ja-->
この目標は命題値です。この構造における任意の論理式の充足が h-命題だからです。これが後で使う命題的切り詰めの正確な消去境界になります。単に復号されたアリティ、論理式、構成子の形は、この目標を証明するためには使えますが、再利用可能な計算データとして取り出すことはできません。
<!--/-->

```agda
        isPropGoal : isProp Goal
        isPropGoal = snd (frame ⊨ R.relN (toℕ k))
```

<!--en-->
The transfer lemma is the key move: given the arity equation, the environment-set equation, the formula-code equation `fst p ≡ cd ψ`, and an extension fact for the satisfaction set of `ψ`, it produces the corresponding extension fact for the table value at the frame. The three equations align the frame's arity, environment set, and formula-code object with those of the recursive satisfaction set.
<!--zh-->
转移引理是关键步骤：给定元数等式、环境集等式、公式码等式 `fst p ≡ cd ψ`，以及 `ψ` 的满足关系集合之外延事实，它便产出框架处表取值的相应外延事实。这三条等式分别把框架中的元数、环境集与公式码对象同递归满足关系集合所用的数据对齐。
<!--ja-->
移行の補題が重要なステップです。アリティの等式、環境集合の等式、論理式符号の等式 `fst p ≡ cd ψ`、そして `ψ` の充足関係集合についての外延事実が与えられると、枠にある表の値について対応する外延事実を作ります。この三つの等式は、枠のアリティ、環境集合、論理式符号の対象を、再帰的な充足関係集合が用いるデータにそろえます。
<!--/-->

```agda
        transfer : (n : ℕ) (ψ : Formula Ab n) → fst ar ≡ # n → fst F ≡ fst (envSet W n)
                 → fst p ≡ cd ψ → {j : ℕ} (env : S ^ j) (φ : Formula S (1 + j))
                 → ExtFact (fst (SatW ψ)) (fst (envSet W n)) (λ z → ⟨ (z ∷ env) ⊨ φ ⟩)
                 → RR.Ext env φ
        transfer n ψ qa qF qp env φ ext =
```

<!--en-->
The frame equations first show that `c` is the canonical key of the decoded formula and that the supplied table member is the pair of `c` with `yc`. The value-agreement hypothesis then identifies the underlying set of `yc` with the recursive satisfaction set. Finally, transport reverses that value equality and the equation identifying `F` with the canonical environment set, converting the bridge's extension fact into the extension fact required by the frame.
<!--zh-->
框架中的等式先证明 `c` 是解码公式的典范键，并证明给定表成员是 `c` 与 `yc` 组成的对。取值相合假设随即把 `yc` 的底层集合认同为递归满足集。最后，证明沿这条取值等式的逆向以及 `F` 与典范环境集的等式作运输，把桥给出的外延事实化为框架所需的外延事实。
<!--ja-->
まず枠の等式から、`c` が復号された論理式の正準な鍵であり、与えられた表の要素が `c` と `yc` の対であることを示します。すると値の一致の仮定により、`yc` の基礎集合が再帰的な充足集合と同定されます。最後に、その値の等式を逆向きに用い、さらに `F` を正準な環境集合と同定する等式に沿って運ぶことで、橋の外延事実を枠が要求する外延事実へ変換します。
<!--/-->

```agda
          subst2 (λ Y F' → ExtFact Y F' (λ z → ⟨ (z ∷ env) ⊨ φ ⟩))
            (sym (val≡ ψ c yc (ec ∙ cong₂ pr qa qp) (subst (λ u → ⟨ u ∈ Tv ⟩) ee e∈))) (sym qF) ext
```

<!--en-->
The sub-value lemma applies the value-agreement hypothesis at a child entry of the same arity, recovering the satisfaction set from the child's table entry.
<!--zh-->
子取值引理把取值一致假设施于同元数的子条目，从子表条目恢复满足集。
<!--ja-->
下位の値の補題は、同じアリティの子の項目に、値の一致の仮定を適用します。子の表の項目から充足集合を復元するのです。
<!--/-->

```agda
        subVal : (n : ℕ) (a : Formula Ab n) (c₁ ya e₁ : S) → fst ar ≡ # n
               → ⟨ fst e₁ ∈ Tv ⟩ → fst e₁ ≡ pr (fst c₁) (fst ya) → fst c₁ ≡ pr (fst ar) (cd a)
               → fst ya ≡ fst (SatW a)
        subVal n a c₁ ya e₁ qa e₁∈ ee₁ e₁' =
          val≡ a c₁ ya (e₁' ∙ cong (λ v → pr v (cd a)) qa) (subst (λ u → ⟨ u ∈ Tv ⟩) ee₁ e₁∈)
```

<!--en-->
For a quantified body, the child key has successor arity. The additional equation identifies its arity component `ar'` with the von Neumann successor of the parent arity component; composing this with `ar = # n` yields the numeral for `suc n`. The value-agreement hypothesis can therefore identify the child entry with the recursive satisfaction set of the body. This is an arity calculation, not a claim about stages of the constructible hierarchy.
<!--zh-->
对量词体而言，子公式键位于后继元数。新增的等式把其元数分量 `ar'` 认同为父公式元数分量的冯·诺伊曼后继；再与 `ar = # n` 复合，就得到 `suc n` 的数码。因此，取值相合假设可把子公式表值认同为体公式的递归满足集。这只是元数计算，并非关于可构造层级阶段的陈述。
<!--ja-->
量化子の本体では、子の鍵は後続アリティにあります。追加の等式は、そのアリティ成分 `ar'` を親のアリティ成分のフォン・ノイマン後続と同定します。これを `ar = # n` と合成すると `suc n` の数項が得られます。したがって値の一致の仮定により、子の表の値を本体の再帰的な充足集合と同定できます。これはアリティの計算であり、構成可能階層の段階についての主張ではありません。
<!--/-->

```agda

        subValS : (n : ℕ) (a : Formula Ab (suc n)) (c₁ ya e₁ ar' : S) → fst ar ≡ # n
                → ⟨ fst e₁ ∈ Tv ⟩ → fst e₁ ≡ pr (fst c₁) (fst ya) → fst c₁ ≡ pr (fst ar') (cd a) → fst ar' ≡ sucV (fst ar)
                → fst ya ≡ fst (SatW a)
        subValS n a c₁ ya e₁ ar' qa e₁∈ ee₁ e₁' es =
          val≡ a c₁ ya (e₁' ∙ cong (λ v → pr v (cd a)) (es ∙ cong sucV qa)) (subst (λ u → ⟨ u ∈ Tv ⟩) ee₁ e₁∈)
```

<!--en-->
The data type collects the decoded arity, environment set, formula, and tag match: everything needed to dispatch on a constructor case.
<!--zh-->
数据类型收集解码出的元数、环境集、公式与标签匹配：分派构造子情形所需的一切。
<!--ja-->
データの型は、復号されたアリティ、環境の集合、論理式、そしてタグの照合を集めます。構成子の場合を振り分けるために必要なすべてです。
<!--/-->

```agda
        Data : Type (ℓ-suc ℓ)
        Data = Σ[ n ∈ ℕ ] ((fst ar ≡ # n) × ((fst F ≡ fst (envSet W n))
                 × (Σ[ ψ ∈ Formula Ab n ] ((fst p ≡ cd ψ) × MatchN (toℕ k) ψ (fst r)))))

```

<!--en-->
The evidence in `data'` remains under propositional truncation throughout. First the tower entry merely supplies an arity and its environment set. For each such witness, `decode` merely supplies a formula at that arity, and `PT.map` augments it with the constructor-shape proof obtained by `matchAt`. The outer elimination lands again in a truncated type, so no arity or formula is selected globally.
<!--zh-->
`data'` 中的证据始终留在命题截断之下。环境塔条目先只给出某个元数及其环境集；对每个这样的见证，`decode` 又只在命题截断下给出该元数处的某个公式，`PT.map` 再用 `matchAt` 得到的构造子形状证明扩充这份数据。外层消去的目标仍是命题截断后的类型，所以整个过程没有在全局选择任何元数或公式。
<!--ja-->
`data'` の証拠は、全体を通して命題的切り詰めの内側に留まります。まず塔の要素が、あるアリティとその環境集合を単に与えます。その各証人に対して、`decode` はそのアリティのある論理式を単に与え、`PT.map` が `matchAt` から得た構成子の形の証明を付け加えます。外側の消去先も再び切り詰められた型なので、アリティや論理式が大域的に選ばれることはありません。
<!--/-->

```agda
        data' : ∥ Data ∥₁
        data' = PT.rec squash₁
          (λ { (n , (qa , qF)) → PT.map
            (λ { (ψ , qp) → n , (qa , qF , ψ , (qp , matchAt ψ (toℕ k) (fst r) (sym qp ∙ ep))) })
            (decode c c∈ n (fst p) (ec ∙ cong (λ v → pr v (fst p)) qa)) })
```

<!--en-->
The final argument to the outer truncation eliminator is the local `Arity ar F` evidence read from the presented tower entry. It initiates the nested, propositionally truncated decoding above; it does not expose the hidden natural-number witness on its own.
<!--zh-->
外层命题截断消去器的最后一个实参，是从当前环境塔条目读出的局部 `Arity ar F` 证据。它启动上面的嵌套命题截断解码，却不会单独暴露其中隐藏的自然数见证。
<!--ja-->
外側の命題的切り詰めの消去に渡す最後の引数は、提示された塔の要素から読み取った局所的な `Arity ar F` の証拠です。これは上の入れ子になった切り詰め付き復号を開始しますが、隠された自然数の証人をそれだけで外へ取り出すことはありません。
<!--/-->

```agda
          (arity q ar F q∈ eq)
```

<!--en-->
For any binary constructor, the two child entries are first identified with the recursive satisfaction sets of the child formulas. The binary bridge then characterizes the recursive satisfaction set of the compound formula by applying the corresponding object-language connective to membership in those two child sets. This common argument will serve conjunction, disjunction, and implication separately.
<!--zh-->
对任意二元构造子，证明先把两个子公式的表值分别认同为其递归满足集。随后，二元桥用相应的对象语言联结词组合「属于这两个子满足集」的命题，从而刻画复合公式的递归满足集。这一共同论证将分别用于合取、析取与蕴涵。
<!--ja-->
任意の二項構成子について、まず二つの子論理式の表の値を、それぞれの再帰的な充足集合と同定します。次に二項の橋は、二つの子充足集合への所属を対応する対象言語の結合子で組み合わせることにより、複合論理式の再帰的な充足集合を特徴づけます。この共通の議論を、連言、選言、含意にそれぞれ用います。
<!--/-->

```agda
        module BinFill (op : ∀ {j} → Formula S j → Formula S j → Formula S j)
          (opA : ∀ {j} → Formula Ab j → Formula Ab j → Formula Ab j)
          (bridge : ∀ {n} (a b : Formula Ab n) {j : ℕ} (env : S ^ j) (ya yb : Fin j)
                  → fst (lookup ya env) ≡ fst (SatW a) → fst (lookup yb env) ≡ fst (SatW b)
                  → ExtFact (fst (SatW (opA a b))) (fst (envSet W n))
```

<!--en-->
The bridge's extension fact is stated at the formula that applies the binary connective to the two membership atoms over the child satisfaction sets.
<!--zh-->
桥的外延事实在「把二元联结词施于两个子满足集上的隶属原子」的公式处陈述。
<!--ja-->
橋の外延の事実は、二つの下位の充足集合の上の所属の原子に、二項の結合子を適用する論理式の上で述べられます。
<!--/-->

```agda
                      (λ z → ⟨ (z ∷ env) ⊨ op (var i0 ∈̇ var (suc ya)) (var i0 ∈̇ var (suc yb)) ⟩)) where

```

<!--en-->
The payload equation says that the frame's payload is the pair of the two child codes. Pair injectivity recovers the two component equations separately, and `subVal` uses them to identify each represented child value with the underlying set of its recursively defined value `SatW`.
<!--zh-->
载荷等式表明，框架中的载荷是两个子公式码的配对。配对的单射性分别恢复两个分量等式，`subVal` 再利用它们，把两个被表示的子公式取值分别认同为其递归定义值 `SatW` 的底层集合。
<!--ja-->
ペイロードの等式は、枠のペイロードが二つの子論理式の符号の対であることを述べます。対の単射性から二つの成分の等式を別々に取り出し、`subVal` はそれらを使って、表された各子の値の底集合を再帰的に定義された値 `SatW` の底集合と同定します。
<!--/-->

```agda
          go : (n : ℕ) (a b ψ : Formula Ab n) → fst ar ≡ # n → fst F ≡ fst (envSet W n)
             → fst p ≡ cd ψ → ψ ≡ opA a b → fst r ≡ pr (cd a) (cd b) → ⟨ frame ⊨ R.binRel op ⟩
          go n a b ψ qa qF qp qψ qr = RR.bin-in op (λ a' b' s' c₁ ya s₁ e₁ c₂ yb s₂ e₂ er e₁∈ ee₁ e₁' e₂∈ ee₂ e₂' →
            let q' = pr-inj (sym er ∙ qr)
                ya≡ = subVal n a c₁ ya e₁ qa e₁∈ ee₁ (e₁' ∙ cong (pr (fst ar)) (q' .fst))
```

<!--en-->
These two child equalities are placed in the same extended environment as the corresponding table entries. The connective bridge then characterizes `SatW (opA a b)` by the binary clause, and `transfer` replaces that canonical value and environment set by the candidate value and environment already present in the frame.
<!--zh-->
这两条子公式取值等式与相应的表条目一同放入扩展环境。联结词桥接据此用二元子句刻画 `SatW (opA a b)`，而 `transfer` 再把这个典范取值及环境集换成框架中已有的候选取值与环境集。
<!--ja-->
この二つの子の値の等式は、対応する表の項目と同じ拡張環境に置かれます。結合子の橋渡しは二項の節によって `SatW (opA a b)` を特徴づけ、`transfer` はその正準な値と環境集合を、枠にすでにある候補値と環境集合へ置き換えます。
<!--/-->

```agda
                yb≡ = subVal n b c₂ yb e₂ qa e₂∈ ee₂ (e₂' ∙ cong (pr (fst ar)) (q' .snd))
                env = yb ∷ c₂ ∷ s₂ ∷ e₂ ∷ ya ∷ c₁ ∷ s₁ ∷ e₁ ∷ b' ∷ a' ∷ s' ∷ frame
            in transfer n (opA a b) qa qF (qp ∙ cong cd qψ) env (R.binBody op)
                 (bridge a b env i4 i0 ya≡ yb≡))
```

<!--en-->
For an unbounded quantified formula, the recursive child has successor arity, while its semantic quantifier still ranges over the carrier `W`. The abstract constructor `q'` will therefore be instantiated by `∃[]-syntax` or `∀[]-syntax`; `qA` names the corresponding unbounded constructor over the alphabet, and the bridge relates its recursive satisfaction set to that carrier-bounded clause.
<!--zh-->
对于无界量化公式，递归子公式具有后继元数，而其语义量化仍在载体 `W` 上进行。因此，抽象构造子 `q'` 随后会实例化为 `∃[]-syntax` 或 `∀[]-syntax`；`qA` 表示字母表上的相应无界构造子，桥接则把它的递归满足关系集与这个由载体限定的子句联系起来。
<!--ja-->
非有界量化された論理式では、再帰的な子論理式のアリティは後続になりますが、その意味論的な量化は台 `W` 上を動きます。そこで抽象的な構成子 `q'` は後で `∃[]-syntax` または `∀[]-syntax` に具体化され、`qA` はアルファベット上の対応する非有界構成子を表し、橋渡しはその再帰的な充足集合を台で有界化した節に結び付けます。
<!--/-->

```agda
        module QuFill (q' : ∀ {j} → Term S j → Formula S (suc j) → Formula S j)
          (qA : ∀ {j} → Formula Ab (suc j) → Formula Ab j)
          (bridge : ∀ {n} (a : Formula Ab (suc n)) {j : ℕ} (env : S ^ j) (wi yai : Fin j)
                  → fst (lookup wi env) ≡ Wv → fst (lookup yai env) ≡ fst (SatW a)
                  → ExtFact (fst (SatW (qA a))) (fst (envSet W n))
```

<!--en-->
The clause tests a candidate encoded environment `z`. Its outer constructor, later instantiated as `∃[]-syntax` or `∀[]-syntax`, ranges over the carrier `W`; for each such element, the inner `∃[]-syntax` asks for a member of the child's represented satisfaction set that is the encoded environment obtained by adjoining that element to `z`. This is the object-language description of one quantifier step, not a decoder or a reusable choice of witnesses.
<!--zh-->
该子句检验一个候选编码环境 `z`。其外层构造子随后会实例化为 `∃[]-syntax` 或 `∀[]-syntax`，并在载体 `W` 上量化；对每个这样的元素，内层的 `∃[]-syntax` 要求子公式所表示的满足关系集中存在一个成员，它正是把该元素添到 `z` 所得的编码环境。这是对象语言对一步量化的描述，并不构成解码器，也不提供可复用的见证选择。
<!--ja-->
この節は、候補となる符号化環境 `z` を判定します。外側の構成子は後で `∃[]-syntax` または `∀[]-syntax` に具体化され、台 `W` 上を量化します。その各要素について、内側の `∃[]-syntax` は、その要素を `z` に付け加えて得られる符号化環境が、子論理式を表す充足集合の要素として存在することを要求します。これは一回の量化を対象言語で記述したものであり、復号器でも、再利用可能な証人の選択でもありません。
<!--/-->

```agda
                      (λ z → ⟨ (z ∷ env) ⊨ q' (var (suc wi)) (∃̇∈ (var (suc (suc yai))) (consAtL i0 i1 i2)) ⟩)) where

```

<!--en-->
The decoded formula has arity `n`, whereas its quantified body has arity `suc n`. The successor equation supplied by the relation reader lets `subValS` rewrite the body's key to that arity and identify its represented value with `SatW a`; the quantifier bridge can then use precisely the recursive child value required by the clause.
<!--zh-->
解码所得公式的元数是 `n`，而其量化主体的元数是 `suc n`。关系读式给出的后继等式使 `subValS` 能把主体的键改写到该元数，并把其被表示的取值认同为 `SatW a`；量词桥接由此取得该子句所需的递归子公式取值。
<!--ja-->
復号された論理式のアリティは `n` ですが、その量化本体のアリティは `suc n` です。関係の読み取りが与える後続の等式により、`subValS` は本体の鍵をそのアリティへ書き換え、表された値を `SatW a` と同定できます。これで量化子の橋渡しは、節が必要とする再帰的な子の値をちょうど受け取れます。
<!--/-->

```agda
          go : (n : ℕ) (a : Formula Ab (suc n)) (ψ : Formula Ab n) → fst ar ≡ # n → fst F ≡ fst (envSet W n)
             → fst p ≡ cd ψ → ψ ≡ qA a → fst r ≡ cd a → ⟨ frame ⊨ R.quRel q' ⟩
          go n a ψ qa qF qp qψ qr = RR.qu-in q' (λ c₁ ya ar' s' s'' e' e'∈ ee₁ e₁' es →
            let ya≡ = subValS n a c₁ ya e' ar' qa e'∈ ee₁ (e₁' ∙ cong (pr (fst ar')) qr) es
                env = ar' ∷ s'' ∷ ya ∷ c₁ ∷ s' ∷ e' ∷ frame
```

<!--en-->
The bridge supplies an extension fact for the canonical value `SatW (qA a)`. The arity, environment-set, and code equations then let `transfer` turn that fact into the extension statement demanded for the candidate table value in this frame, completing the unbounded-quantifier clause.
<!--zh-->
桥接先给出典范取值 `SatW (qA a)` 的外延事实。随后，元数、环境集与公式码的等式使 `transfer` 能把该事实化为当前框架中候选表取值所需的外延陈述，从而完成无界量词子句。
<!--ja-->
橋渡しはまず正準な値 `SatW (qA a)` に対する外延事実を与えます。次にアリティ、環境集合、論理式の符号の等式を使って、`transfer` がその事実を、この枠の表の候補値に必要な外延の主張へ変えます。これで非有界量化子の節が完成します。
<!--/-->

```agda
            in transfer n (qA a) qa qF (qp ∙ cong cd qψ) env (R.quBody q')
                 (bridge a env (sh 18 w) i2 qw ya≡))
```

<!--en-->
A bounded quantified formula has only one recursive formula child: its bounding term is evaluated inside the semantic bridge. The abstract data separate the bounded quantifier, the connective used to combine its conditions, the alphabet-level constructor, and the exact object-language clause body, so the same argument covers both universal and existential forms without treating the term code as a subformula.
<!--zh-->
有界量化公式只有一个递归公式子项：界限词项在语义桥接内部求值。这里的抽象数据分别给出有界量词、组合各条件的联结词、字母表层的构造子以及准确的对象语言子句主体，因而同一论证既适用于全称形式，也适用于存在形式，同时不会把词项码当作子公式。
<!--ja-->
有界量化された論理式がもつ再帰的な子論理式は一つだけであり、境界項は意味論的な橋渡しの内部で評価されます。ここでは有界量化子、条件を組み合わせる結合子、アルファベット側の構成子、そして対象言語で書かれた節の本体を分けて与えます。そのため、項の符号を子論理式として扱うことなく、同じ議論を全称形と存在形の両方に使えます。
<!--/-->

```agda
        module BqFill (q' : ∀ {j} → Term S j → Formula S (suc j) → Formula S j)
          (c' : ∀ {j} → Formula S j → Formula S j → Formula S j)
          (qA : ∀ {j} → Term Ab j → Formula Ab (suc j) → Formula Ab j)
          (body : ∀ {j} → Fin j → Fin j → Fin j → Fin j → Fin j → Formula S (1 + j))
          (bodyIs : ∀ {j} (wi ti yai N0i N1i : Fin j)
```

<!--en-->
The equation `bodyIs` identifies the generic clause body with its three bounded layers. The outer layer ranges over a proposed value of the bounding term in `W`, `tmIs` verifies that proposal, the next layer ranges over elements of that value that also lie in `W`, and the innermost `∃[]-syntax` asks for the encoded extended environment in the child's satisfaction set. This equation concerns the semantic clause body, rather than the original formula body itself.
<!--zh-->
等式 `bodyIs` 把一般子句主体认同为三层有界结构。最外层在 `W` 中量化界限词项的候选取值，`tmIs` 验证该候选；下一层量化既属于该取值又属于 `W` 的元素；最内层用 `∃[]-syntax` 要求编码后的扩展环境属于子公式的满足关系集。这个等式描述的是语义子句主体，而不是原公式主体本身。
<!--ja-->
等式 `bodyIs` は、一般の節の本体を三つの有界な層と同定します。最外層は境界項の候補値を `W` 上で量化し、`tmIs` がその候補を検証します。次の層はその値に属し、かつ `W` にも属する要素を量化し、最内層の `∃[]-syntax` は符号化された拡張環境が子論理式の充足集合に属することを要求します。この等式が記述するのは意味論的な節の本体であり、元の論理式の本体そのものではありません。
<!--/-->

```agda
                  → body wi ti yai N0i N1i
                  ≡ q' (var (suc wi)) (c' (tmIs (suc (suc ti)) i1 i0 (suc (suc N0i)) (suc (suc N1i)))
                      (q' (var (suc (suc wi))) (c' (var i0 ∈̇ var i1) (∃̇∈ (var (suc (suc (suc yai)))) (consAtL i0 i1 i3))))))
          (bridge : ∀ {n} (t : Term Ab n) (a : Formula Ab (suc n)) {j : ℕ} (env : S ^ j) (wi ti yai N0i N1i : Fin j)
                  → fst (lookup wi env) ≡ Wv → fst (lookup ti env) ≡ ct t → fst (lookup yai env) ≡ fst (SatW a)
```

<!--en-->
The bridge assumes five equalities locating, in one environment, the carrier, the bounding-term code, the recursive value of the formula child, and the numeral tags `0` and `1`. From those hypotheses it proves the extension fact for the bounded formula. Thus the extension fact is the conclusion of the bridge, while the only recursive input is the value of the formula child.
<!--zh-->
桥接假设五条等式，用以在同一环境中定位载体、界限词项码、公式子项的递归取值以及数码标签 `0` 与 `1`。它从这些前提证明有界公式的外延事实。因此，外延事实是桥接的结论，而唯一的递归输入是公式子项的取值。
<!--ja-->
橋渡しは、同じ環境の中で台、境界項の符号、子論理式の再帰的な値、そして数項タグ `0` と `1` を位置づける五つの等式を仮定します。これらから有界な論理式の外延事実を証明します。したがって外延事実は橋渡しの結論であり、再帰的に入力されるのは子論理式の値だけです。
<!--/-->

```agda
                  → fst (lookup N0i env) ≡ # 0 → fst (lookup N1i env) ≡ # 1
                  → ExtFact (fst (SatW (qA t a))) (fst (envSet W n)) (λ z → ⟨ (z ∷ env) ⊨ body wi ti yai N0i N1i ⟩)) where

```

<!--en-->
Pair injectivity separates the bounded payload into its term-code component and its formula-code component. The first equality is passed to the term part of the bridge; the second, together with the successor-arity equation, lets `subValS` identify the represented value of the sole formula child. No recursive table lookup is required for the term code.
<!--zh-->
配对的单射性把有界量词的载荷分成词项码分量与公式码分量。第一条等式交给桥接中的词项部分；第二条等式与后继元数等式一起，使 `subValS` 能认同唯一公式子项的被表示取值。词项码不需要递归查询表。
<!--ja-->
対の単射性は、有界量化子のペイロードを項の符号の成分と論理式の符号の成分に分けます。第一の等式は橋渡しの項を扱う部分へ渡され、第二の等式は後続アリティの等式とともに、唯一の子論理式の表された値を `subValS` が同定するために使われます。項の符号について再帰的に表を引く必要はありません。
<!--/-->

```agda
          go : (n : ℕ) (t : Term Ab n) (a : Formula Ab (suc n)) (ψ : Formula Ab n) → fst ar ≡ # n → fst F ≡ fst (envSet W n)
             → fst p ≡ cd ψ → ψ ≡ qA t a → fst r ≡ pr (ct t) (cd a) → ⟨ frame ⊨ R.bqRel q' c' ⟩
          go n t a ψ qa qF qp qψ qr = RR.bq-in q' c' (λ t' a' s' c₁ ya ar' s₁ s'' e' er e'∈ ee₁ e₁' es →
            let q'' = pr-inj (sym er ∙ qr)
                ya≡ = subValS n a c₁ ya e' ar' qa e'∈ ee₁ (e₁' ∙ cong (pr (fst ar')) (q'' .snd)) es
```

<!--en-->
The concrete bridge proves the extension fact in the canonical bounded-quantifier body. Rewriting by `bodyIs` places that fact in the generic relation body, after which `transfer` replaces the canonical satisfaction value by the candidate value represented in the table entry.
<!--zh-->
具体桥接先在典范的有界量词主体中证明外延事实。沿 `bodyIs` 改写后，该事实落入一般关系主体；随后 `transfer` 把典范满足关系值换成表条目所表示的候选取值。
<!--ja-->
具体的な橋渡しは、正準な有界量化子の本体について外延事実を証明します。`bodyIs` に沿って書き換えると、その事実は一般の関係の本体に置かれ、続いて `transfer` が正準な充足の値を表の項目に表された候補値へ置き換えます。
<!--/-->

```agda
                env = ar' ∷ s'' ∷ ya ∷ c₁ ∷ s₁ ∷ e' ∷ a' ∷ t' ∷ s' ∷ frame
            in transfer n (qA t a) qa qF (qp ∙ cong cd qψ) env (R.bqBody q' c')
                   (subst (λ φ → ExtFact (fst (SatW (qA t a))) (fst (envSet W n)) (λ z → ⟨ (z ∷ env) ⊨ φ ⟩))
                     (bodyIs (sh 21 w) i7 i2 (sh 21 (N f0)) (sh 21 (N f1)))
                     (bridge t a env (sh 21 w) i7 i2 (sh 21 (N f0)) (sh 21 (N f1)) qw (q'' .fst) ya≡ (tg f0) (tg f1))))
```

<!--en-->
An atomic formula has two term codes but no recursive formula child. Its generic bridge is therefore indexed by the two-place atom constructor and by a relation formula in the enlarged environment; the bridge evaluates both terms and proves the corresponding extension fact directly.
<!--zh-->
原子公式含有两个词项码，却没有递归公式子项。因此，它的一般桥接由二元原子构造子以及扩展环境中的关系公式作索引；桥接直接求值两个词项，并证明相应的外延事实。
<!--ja-->
原子論理式は二つの項の符号をもちますが、再帰的な子論理式はもちません。そこで一般の橋渡しは二項の原子構成子と、拡大された環境における関係式によって添字づけられます。橋渡しは二つの項を直接評価し、対応する外延事実を証明します。
<!--/-->

```agda
        module AtomFill (opA : ∀ {j} → Term Ab j → Term Ab j → Formula Ab j) (rel : Formula S (18 + m))
          (bridge : ∀ {n} (t u : Term Ab n) (env : S ^ (15 + m)) (wi ti ui N0i N1i : Fin (15 + m))
                  → fst (lookup wi env) ≡ Wv → fst (lookup ti env) ≡ ct t → fst (lookup ui env) ≡ ct u
                  → fst (lookup N0i env) ≡ # 0 → fst (lookup N1i env) ≡ # 1
                  → ExtFact (fst (SatW (opA t u))) (fst (envSet W n)) (λ z → ⟨ (z ∷ env) ⊨ atomEx wi ti ui N0i N1i rel ⟩)) where
```

<!--en-->
The payload equation is again a pair equation, now separating the codes of the two terms. These equations place the term codes in the environment expected by the atomic body. The actual term values are still quantified and verified by the two `tmIs` clauses inside that body; they are not obtained by recursive table lookup.
<!--zh-->
这里的载荷等式同样是配对等式，此次分离的是两个词项的码。这两条等式把词项码放入原子主体所需的环境。真正的词项取值仍由该主体内部的两条 `tmIs` 子句量化并验证，并非通过递归查询表取得。
<!--ja-->
ここでもペイロードの等式は対の等式であり、今度は二つの項の符号を分離します。得られた等式により、項の符号は原子の本体が要求する環境に置かれます。実際の項の値は、その本体の内部にある二つの `tmIs` の節によって量化され検証されるのであり、再帰的な表の参照から得られるのではありません。
<!--/-->

```agda

          go : (n : ℕ) (t u : Term Ab n) (ψ : Formula Ab n) → fst ar ≡ # n → fst F ≡ fst (envSet W n)
             → fst p ≡ cd ψ → ψ ≡ opA t u → fst r ≡ pr (ct t) (ct u) → ⟨ frame ⊨ R.atomRel rel ⟩
          go n t u ψ qa qF qp qψ qr = RR.atom-in rel (λ t' u' s' er →
            let q' = pr-inj (sym er ∙ qr)
                env = u' ∷ t' ∷ s' ∷ frame
```

<!--en-->
The three entries prepended to the frame are the two payload term codes and their pair container. With their component equations established, the atomic bridge characterizes the canonical satisfaction set by the chosen relation, and `transfer` moves that characterization to the candidate table value.
<!--zh-->
加在框架前面的三个条目是载荷中的两个词项码及其配对容纳集合。两个分量等式确立后，原子桥接便用所选关系刻画典范满足关系集，`transfer` 再把该刻画搬到候选表取值上。
<!--ja-->
枠の先頭に加えられる三つの項目は、ペイロード中の二つの項の符号と、その対のコンテナです。二つの成分の等式が確立すると、原子の橋渡しが選ばれた関係によって正準な充足集合を特徴づけ、`transfer` がその特徴づけを表の候補値へ移します。
<!--/-->

```agda
            in transfer n (opA t u) qa qF (qp ∙ cong cd qψ) env (R.atomBody rel)
                   (bridge t u env (sh 15 w) i1 i0 (sh 15 (N f0)) (sh 15 (N f1)) qw (q' .fst) (q' .snd) (tg f0) (tg f1)))
```

<!--en-->
Bottom has neither term data nor a formula child. Its bridge says directly that the recursive satisfaction set has the empty extension over `envSet W n`; `transfer` rewrites this fact to the candidate table value, and the relation constructor packages it as the bottom clause.
<!--zh-->
假命题既没有词项数据，也没有公式子项。相应桥接直接说明，其递归满足关系集在 `envSet W n` 上具有空外延；`transfer` 把这一事实改写到候选表取值，关系构造再把它封装为假命题子句。
<!--ja-->
偽は項のデータも子論理式ももちません。その橋渡しは、再帰的な充足集合が `envSet W n` 上で空の外延をもつことを直接述べます。`transfer` がこの事実を表の候補値へ書き換え、関係の構成子が偽の節としてまとめます。
<!--/-->

```agda
        botGo : (n : ℕ) (ψ : Formula Ab n) → fst ar ≡ # n → fst F ≡ fst (envSet W n)
              → fst p ≡ cd ψ → ψ ≡ ⊥̇ → ⟨ frame ⊨ R.botRel ⟩
        botGo n ψ qa qF qp qψ = extB-in i0 i8 ⊥̇ frame
          (transfer n ⊥̇ qa qF (qp ∙ cong cd qψ) frame ⊥̇ (botBridge n frame))
```

<!--en-->
Tag `0` is the membership atom. Here the relation formula already means ordinary membership in the constructible structure, so both directions of the agreement proof and both directions connecting atomic meaning to membership are identities. The atomic argument still verifies the two term codes and their values before applying that relation.
<!--zh-->
标签 `0` 对应隶属原子。这里的关系公式在可构造结构中本来就表示通常的隶属关系，因此相符证明的两个方向，以及连接原子意义与隶属关系的两个方向，都是恒等映射。原子论证仍会先验证两个词项码及其取值，再施用该关系。
<!--ja-->
タグ `0` は所属の原子論理式に対応します。ここでの関係式は構成可能な構造における通常の所属をそのまま意味するので、一致の証明の両方向と、原子の意味を所属に結び付ける両方向はいずれも恒等写像です。それでも原子の場合の議論は、関係を適用する前に二つの項の符号とその値を検証します。
<!--/-->

```agda
      fill : (k : Fin 10) (A : Args k) → Fill.Data k A → Fill.Goal k A
      fill f0 A (n , (qa , qF , ψ , (qp , (t , u , (qψ , qr))))) =
        Fill.AtomFill.go f0 A _∈̇_ (var i1 ∈̇ var i0)
          (λ t u env wi ti ui N0i N1i qw' qt qu q0 q1 →
            AtomBridge.atomBridge t u env wi ti ui N0i N1i qw' qt qu q0 q1 _∈̇_ (λ v x → ⟨ v ∈ x ⟩)
```

<!--en-->
Tag `1` is handled in the same way for equality. Object-language equality is interpreted by equality of the underlying hierarchy sets, so the agreement and semantic conversion maps again require no transport beyond the identities already displayed.
<!--zh-->
标签 `1` 对相等原子采用同一论证。对象语言的相等由层级中底层集合的相等来解释，因此相符映射与语义转换映射同样无需恒等映射以外的搬运。
<!--ja-->
タグ `1` では同じ議論を等号について行います。対象言語の等号は階層の底集合の等しさとして解釈されるので、一致の写像と意味論的な変換写像にも、表示された恒等写像以外の輸送は要りません。
<!--/-->

```agda
              (var i1 ∈̇ var i0) (λ z v x → (λ h → h) , (λ h → h)) (λ δ h → h) (λ δ h → h))
          n t u ψ qa qF qp qψ qr
      fill f1 A (n , (qa , qF , ψ , (qp , (t , u , (qψ , qr))))) =
        Fill.AtomFill.go f1 A _≐_ (var i1 ≐ var i0)
          (λ t u env wi ti ui N0i N1i qw' qt qu q0 q1 →
```

<!--en-->
Tags `2`, `3`, and `4` use the common binary argument with the bridges for conjunction, disjunction, and implication. Tag `5` is the childless bottom case. This part of the dispatch therefore follows the constructor code exactly, while all recursive information remains confined to the two child values required by a binary connective.
<!--zh-->
标签 `2`、`3`、`4` 分别以合取、析取、蕴涵的桥接使用共同的二元论证；标签 `5` 则是不含子公式的假命题情形。因此，这一段分派准确遵循构造子编码，而全部递归信息只限于二元联结词所需的两个子公式取值。
<!--ja-->
タグ `2`、`3`、`4` は、連言、選言、含意の橋渡しとともに共通の二項の議論を使います。タグ `5` は子論理式をもたない偽の場合です。この部分の振り分けは構成子の符号に正確に従い、再帰的な情報は二項結合子が必要とする二つの子の値だけに限られます。
<!--/-->

```agda
            AtomBridge.atomBridge t u env wi ti ui N0i N1i qw' qt qu q0 q1 _≐_ (λ v x → v ≡ x)
              (var i1 ≐ var i0) (λ z v x → (λ h → h) , (λ h → h)) (λ δ h → h) (λ δ h → h))
          n t u ψ qa qF qp qψ qr
      fill f2 A (n , (qa , qF , ψ , (qp , (a , b , (qψ , qr))))) = Fill.BinFill.go f2 A _∧̇_ _∧̇_ andBridge n a b ψ qa qF qp qψ qr
      fill f3 A (n , (qa , qF , ψ , (qp , (a , b , (qψ , qr))))) = Fill.BinFill.go f3 A _∨̇_ _∨̇_ orBridge n a b ψ qa qF qp qψ qr
```

<!--en-->
Tags `6` and `7` represent the unbounded existential and universal formulas. Their semantic clauses use `∃[]-syntax` and `∀[]-syntax` to range over the carrier `W`, with the recursive body value at successor arity. The remaining two tags begin the bounded cases, where the same bounded constructors are combined with conjunction or implication to express the term bound as well.
<!--zh-->
标签 `6` 与 `7` 表示无界存在公式和无界全称公式。相应语义子句用 `∃[]-syntax` 与 `∀[]-syntax` 在载体 `W` 上量化，并使用后继元数处的递归主体取值。余下两个标签开始处理有界情形；其中同样的有界构造子再与合取或蕴涵结合，以同时表达词项给出的界。
<!--ja-->
タグ `6` と `7` は、非有界の存在論理式と全称論理式を表します。それらの意味論的な節は `∃[]-syntax` と `∀[]-syntax` によって台 `W` 上を量化し、後続アリティにある再帰的な本体の値を使います。残る二つのタグから有界の場合が始まり、同じ有界構成子を連言または含意と組み合わせて、項が与える境界も表します。
<!--/-->

```agda
      fill f4 A (n , (qa , qF , ψ , (qp , (a , b , (qψ , qr))))) = Fill.BinFill.go f4 A _⇒̇_ _⇒̇_ impBridge n a b ψ qa qF qp qψ qr
      fill f5 A (n , (qa , qF , ψ , (qp , (qψ , qr)))) = Fill.botGo f5 A n ψ qa qF qp qψ
      fill f6 A (n , (qa , qF , ψ , (qp , (a , (qψ , qr))))) = Fill.QuFill.go f6 A ∃̇∈ ∃̇_ exBridge n a ψ qa qF qp qψ qr
      fill f7 A (n , (qa , qF , ψ , (qp , (a , (qψ , qr))))) = Fill.QuFill.go f7 A ∀̇∈ ∀̇_ allBridge n a ψ qa qF qp qψ qr
      fill f8 A (n , (qa , qF , ψ , (qp , (t , a , (qψ , qr))))) =
```

<!--en-->
For the bounded universal, the canonical body already has the abstract shape required by `BqFill`, so `bodyIs` is reflexivity. Its nested uses of `∀[]-syntax` express that every verified value of the bounding term, and every carrier element lying in that value, must lead to an encoded environment in the recursive child set.
<!--zh-->
对于有界全称公式，典范主体已经具有 `BqFill` 所要求的抽象形状，所以 `bodyIs` 就是自反等式。嵌套的 `∀[]-syntax` 表达：界限词项的每个经验证取值，以及属于该取值的每个载体元素，都必须导向递归子公式集合中的一个编码环境。
<!--ja-->
有界全称では、正準な本体がすでに `BqFill` の要求する抽象的な形をもつため、`bodyIs` は反射律です。入れ子になった `∀[]-syntax` は、検証された境界項の各値と、その値に属する各台要素が、再帰的な子の集合に属する符号化環境へ至らなければならないことを表します。
<!--/-->

```agda
        Fill.BqFill.go f8 A ∀̇∈ _⇒̇_ ∀̇∈ bqAll (λ _ _ _ _ _ → refl)
          (λ t a env wi ti yai N0i N1i qw' qt qa' q0 q1 → BqBridge.allInBridge t a env wi ti yai N0i N1i qw' qt qa' q0 q1)
          n t a ψ qa qF qp qψ qr
      fill f9 A (n , (qa , qF , ψ , (qp , (t , a , (qψ , qr))))) =
        Fill.BqFill.go f9 A ∃̇∈ _∧̇_ ∃̇∈ bqEx (λ _ _ _ _ _ → refl)
```

<!--en-->
The bounded existential uses the parallel three-layer body with `∃[]-syntax`, joining the term-value condition, membership in that value, and membership of the extended environment in the child set by conjunctions. Its body also matches by reflexivity, and tag `9` completes the ten constructor cases.
<!--zh-->
有界存在公式使用与之平行的三层主体，其中以 `∃[]-syntax` 量化，并用合取连接词项取值条件、元素属于该取值，以及扩展环境属于子公式集合这三项条件。它的主体同样由自反等式匹配，标签 `9` 至此完成十种构造子情形。
<!--ja-->
有界存在は、これと平行な三層の本体を `∃[]-syntax` で表し、項の値であるという条件、その値への所属、そして拡張環境の子集合への所属を連言で結びます。この本体も反射律によって一致し、タグ `9` で十個の構成子の場合がすべてそろいます。
<!--/-->

```agda
          (λ t a env wi ti yai N0i N1i qw' qt qa' q0 q1 → BqBridge.exInBridge t a env wi ti yai N0i N1i qw' qt qa' q0 q1)
          n t a ψ qa qF qp qψ qr

```

<!--en-->
To prove one constructor clause, the twelve objects and their membership and pairing equations are first collected into `Args k`. This fixes a single matching frame. The decoded arity, formula, and constructor shape remain inside propositional truncation in `Fill.data'`, because the original hypotheses do not choose any of them.
<!--zh-->
为证明一条构造子子句，先把十二个对象及其隶属与配对等式汇集为 `Args k`，从而固定一个匹配框架。解码出的元数、公式与构造子形状仍留在 `Fill.data'` 的命题截断之内，因为原有前提并未选择其中任何一项。
<!--ja-->
一つの構成子の節を証明するため、まず十二個の対象と、それらの所属および対の等式を `Args k` に集め、一つの対応する枠を固定します。復号されたアリティ、論理式、構成子の形は `Fill.data'` の命題的切り詰めの内側にとどまります。元の仮定はそのいずれも選択していないからです。
<!--/-->

```agda
      clause : (k : Fin 10) → ⟨ γ ⊨ Cl.clause k ⟩
      clause k = Fr.clause-in k (λ q ar F s c p s1 r s2 e yc s3 q∈ eq c∈ ec ep e∈ ee →
        let A : Args k
            A = record { q = q ; ar = ar ; F = F ; s = s ; c = c ; p = p ; s1 = s1 ; r = r ; s2 = s2 ; e = e ; yc = yc ; s3 = s3
                       ; q∈ = q∈ ; eq = eq ; c∈ = c∈ ; ec = ec ; ep = ep ; e∈ = e∈ ; ee = ee }
```

<!--en-->
Formula satisfaction is a proposition, so `Fill.Goal k A` is a valid target for eliminating the propositionally truncated data. For each hidden witness, `fill` proves the same clause goal; propositionality then makes the result independent of which arity, formula, or decomposition witnessed the decoding. No reusable decoder or table-value choice escapes this elimination.
<!--zh-->
公式的满足是命题，所以 `Fill.Goal k A` 可以作为消去命题截断数据的目标。对于其中每份被隐藏的见证，`fill` 都证明同一个子句目标；目标的命题性保证结果不依赖哪一个元数、公式或分解见证了解码。此次消去不会产生可重复使用的解码器，也不会给出表取值的选择。
<!--ja-->
論理式の充足は命題なので、`Fill.Goal k A` は命題的に切り詰められたデータを除去できる行き先です。隠された各証人に対して `fill` は同じ節の目標を証明し、目標の命題性により、どのアリティ、論理式、分解が復号を証言したかには結果が依存しません。この除去から再利用可能な復号器や表の値の選択が取り出されることはありません。
<!--/-->

```agda
        in PT.rec (Fill.isPropGoal k A) (fill k A) (Fill.data' k A))

```

<!--en-->
The ten constructor clauses are joined into one finite conjunction. This conjunction is the `ten` component of the full table specification; totality and the on-domain condition are added separately in the next step.
<!--zh-->
十条构造子子句被连成一个有穷合取。这个合取是完整表规格中的 `ten` 分量；全定义性与定义域约束将在下一步另行加入。
<!--ja-->
十個の構成子の節を一つの有限連言にまとめます。この連言は完全な表仕様の `ten` 成分であり、全域性と領域条件は次の段階で別に加えます。
<!--/-->

```agda
      ten : ⟨ γ ⊨ Cl.ten ⟩
      ten = bigAnd-in γ 9 Cl.clause clause

```

<!--en-->
The three parts now fit the definition of `tableAt`: `total` gives a merely existing table value for every code in `C`, `onC` says every table member has a key in `C`, and `ten` supplies all constructor clauses. Together they prove that the given relation satisfies the table specification, without asserting that it is a globally chosen function or that its values are unique.
<!--zh-->
这三部分现在恰好组成 `tableAt` 的定义：`total` 对 `C` 中每个码给出经过命题截断的表取值存在性，`onC` 说明每个表成员的键都属于 `C`，`ten` 则给出全部构造子子句。三者共同证明给定关系满足表规格，但不宣称它是全局选定的函数，也不在此证明其取值唯一。
<!--ja-->
これで三つの部分が `tableAt` の定義をちょうど満たします。`total` は `C` の各符号について表の値が命題的に切り詰められて存在することを与え、`onC` は表の各要素の鍵が `C` に属することを述べ、`ten` はすべての構成子の節を与えます。これらは与えられた関係が表の仕様を満たすことを証明しますが、それが大域的に選ばれた関数であることも、ここで値が一意であることも主張しません。
<!--/-->

```agda
    holds : ⟨ γ ⊨ tableAt T w C E N ⟩
    holds = total , (onC , ten)
```

<!--en-->
## Specializing to one formula's slot
<!--zh-->
## 专门用于单个公式的槽位
<!--ja-->
## 一つの論理式のスロットへの特殊化
<!--/-->

<!--en-->
Fixing `W` determines two linked viewpoints. `Alphabet W` supplies formulas whose constants name members of `W` and their codes, while `Bridge W` interprets those constants in the constructible carrier and compares recursive satisfaction with the object-language clauses. The specialization below uses both viewpoints for the slot generated by one formula.
<!--zh-->
固定 `W` 后便得到两个相互联系的视角。`Alphabet W` 给出常元命名 `W` 中元素的公式及其编码，`Bridge W` 则在可构造载体中解释这些常元，并比较递归满足关系与对象语言子句。下面的特化会把这两个视角同时用于一条公式生成的槽位。
<!--ja-->
`W` を固定すると、結び付いた二つの見方が定まります。`Alphabet W` は、定数が `W` の要素を名指す論理式とその符号を与え、`Bridge W` はそれらの定数を構成可能な台で解釈し、再帰的な充足と対象言語の節を比較します。以下の特殊化では、一つの論理式が生成するスロットにこの二つの見方を同時に用います。
<!--/-->

```agda
module _ (W : S) where
  open Alphabet W
  open Bridge W
```

<!--en-->
If `x` belongs to the slot generated by `ψ`, then, under propositional truncation, there are an arity `m` and a formula `χ : Formula Ab m` such that `x` is the underlying set of `keyS W χ`. The result preserves existence of such a formula key, but chooses no formula and retains no explicit proof that `χ` is a subformula of `ψ`.
<!--zh-->
若 `x` 属于 `ψ` 生成的槽位，那么在命题截断下，存在元数 `m` 与公式 `χ : Formula Ab m`，使 `x` 等于 `keyS W χ` 的底层集合。该结论保留这样一个公式键的存在性，却不选择具体公式，也不保留 `χ` 是 `ψ` 的子公式的显式证明。
<!--ja-->
`x` が `ψ` の生成するスロットに属するなら、命題的切り詰めの下で、あるアリティ `m` と論理式 `χ : Formula Ab m` が存在し、`x` は `keyS W χ` の底集合に等しくなります。この結論はそのような論理式の鍵の存在を保ちますが、論理式を選択せず、`χ` が `ψ` の部分論理式であることの明示的な証明も保持しません。
<!--/-->

```agda
  slotAb : ∀ {n} (ψ : Formula Ab n) (x : V ℓ)
         → ⟨ x ∈ fst (slot W (toS ψ)) ⟩
         → ∥ Σ[ m ∈ ℕ ] Σ[ χ ∈ Formula Ab m ] (x ≡ fst (keyS W χ)) ∥₁
  slotAb ψ x h = PT.map
    (λ { (m , χ , e , _) → m , χ , (e ∙ sym (keyBridge W χ)) })
```

<!--en-->
The local equality `mapped ψ` first rewrites the concrete slot as the generic tree that collects `keyʟ (toS χ)`. Applying `tree-inv` then yields, merely, a contributing formula `χ` and equality with that internal key. The map keeps this equality and replaces the internal key by `keyS W χ` using `keyBridge`; the accompanying subtree inclusion is deliberately discarded by the stated result.
<!--zh-->
局部等式 `mapped ψ` 先把具体槽位改写为收集 `keyʟ (toS χ)` 的一般树。随后施用 `tree-inv`，在命题截断下得到贡献该成员的公式 `χ` 及其与这个内部键的等式。映射保留该等式，再用 `keyBridge` 把内部键换成 `keyS W χ`；所得结论有意舍弃了相伴的子树包含证明。
<!--ja-->
局所的な等式 `mapped ψ` は、まず具体的なスロットを `keyʟ (toS χ)` を集める一般の木へ書き換えます。次に `tree-inv` を適用すると、寄与した論理式 `χ` と、その内部の鍵との等式が命題的に切り詰められて得られます。この写像はその等式を保ち、`keyBridge` によって内部の鍵を `keyS W χ` に置き換えます。付随する部分木の包含証明は、定理の結論から意図的に捨てられます。
<!--/-->

```agda
    (tree-inv key key ψ x (subst (λ y → ⟨ x ∈ fst y ⟩) (mapped ψ) h))
    where
    key : ∀ {n} → Formula Ab n → S
    key χ = keyʟ (toS χ)

```

<!--en-->
The equality `mapped` is proved by structural recursion because `toS` changes only constants and leaves every formula constructor in place. Membership atoms, equality atoms, and bottom agree definitionally. For a binary connective, the slot consists of the singleton containing the formula's own key together with the union of the two child trees, so the two recursive equalities are combined under the same unions.
<!--zh-->
等式 `mapped` 由结构递归证明，因为 `toS` 只改变常元，并保留每个公式构造子。隶属原子、相等原子与假命题的两种表示按定义相同。对于二元联结词，槽位由含有公式自身键的单元素集合与两棵子树的并组成，所以两条递归等式在相同的并运算下组合起来。
<!--ja-->
等式 `mapped` は構造再帰で証明されます。`toS` は定数だけを変え、論理式の各構成子をそのまま保つからです。所属の原子論理式、等号の原子論理式、偽では二つの表示が定義上等しくなります。二項結合子では、スロットは論理式自身の鍵を含む一元集合と二つの子の木の合併からなるので、二つの再帰的な等式を同じ合併の下で組み合わせます。
<!--/-->

```agda
    mapped : ∀ {n} (χ : Formula Ab n) → slot W (toS χ) ≡ tree key χ
    mapped (t ∈̇ u) = refl
    mapped (t ≐ u) = refl
    mapped ⊥̇ = refl
    mapped χ@(a ∧̇ b) = cong (cupʟ (sglʟ (key χ))) (cong₂ cupʟ (mapped a) (mapped b))
```

<!--en-->
Conjunction, disjunction, and implication all have the same binary tree shape and therefore use both recursive equalities. Each unbounded quantifier has just one formula body, so its singleton root is joined to one recursively matched child tree. The arity change under the binder affects the type of that child formula, but not this union pattern.
<!--zh-->
合取、析取与蕴涵具有相同的二叉树形状，因此都使用两条递归等式。每个无界量词只有一个公式主体，所以其根部单元素集合只与一棵经递归匹配的子树取并。约束子下的元数变化会改变该子公式的类型，却不改变这种取并模式。
<!--ja-->
連言、選言、含意はいずれも同じ二分木の形をもち、二つの再帰的な等式を使います。各非有界量化子がもつ論理式の本体は一つだけなので、根の一元集合を、再帰的に対応づけられた一つの子の木と合併します。束縛子の下でのアリティの変化は子論理式の型を変えますが、この合併の形は変えません。
<!--/-->

```agda
    mapped χ@(a ∨̇ b) = cong (cupʟ (sglʟ (key χ))) (cong₂ cupʟ (mapped a) (mapped b))
    mapped χ@(a ⇒̇ b) = cong (cupʟ (sglʟ (key χ))) (cong₂ cupʟ (mapped a) (mapped b))
    mapped χ@(∃̇ a) = cong (cupʟ (sglʟ (key χ))) (mapped a)
    mapped χ@(∀̇ a) = cong (cupʟ (sglʟ (key χ))) (mapped a)
    mapped χ@(∀̇∈ t a) = cong (cupʟ (sglʟ (key χ))) (mapped a)
```

<!--en-->
The bounded universal and existential cases also contribute only the formula body as a child tree. Their bounding terms are part of the constructor payload, not formula subtrees collected by `slot`. These last two recursive equalities complete the comparison between the concrete slot and the generic key tree.
<!--zh-->
有界全称与有界存在情形同样只把公式主体作为子树加入。它们的界限词项属于构造子的载荷，并不是 `slot` 所收集的公式子树。最后两条递归等式完成具体槽位与一般键树之间的比较。
<!--ja-->
有界全称と有界存在の場合も、子の木として加わるのは論理式の本体だけです。境界項は構成子のペイロードの一部であり、`slot` が集める子論理式の木ではありません。この最後の二つの再帰的な等式で、具体的なスロットと一般の鍵の木との比較が完成します。
<!--/-->

```agda
    mapped χ@(∃̇∈ t a) = cong (cupʟ (sglʟ (key χ))) (mapped a)

```

<!--en-->
`SlotHolds` works in an environment with positions `T`, `w`, `C`, and `E` for the table, carrier, code domain, and environment tower, together with ten tag positions `N`. It assumes the carrier, tags, and tower facts, then fixes a base formula `ψ0`; the equations `qT` and `qC` identify only the underlying sets stored at `T` and `C` with the canonical table and slot generated by `ψ0`.
<!--zh-->
`SlotHolds` 在一个环境中工作，其中 `T`、`w`、`C`、`E` 分别是表、载体、码定义域与环境塔的位置，另有十个标签位置 `N`。它假设载体、标签与环境塔的事实，再固定基公式 `ψ0`；等式 `qT` 与 `qC` 只把 `T`、`C` 处存放的底层集合分别认同为 `ψ0` 生成的典范表与槽位。
<!--ja-->
`SlotHolds` は、表、台、符号領域、環境の塔の位置をそれぞれ `T`、`w`、`C`、`E` とし、さらに十個のタグ位置 `N` をもつ環境で働きます。台、タグ、塔についての事実を仮定して基礎となる論理式 `ψ0` を固定し、等式 `qT` と `qC` は、`T` と `C` に格納された底集合だけを、`ψ0` が生成する正準な表とスロットに同定します。
<!--/-->

```agda
  module SlotHolds {m : ℕ} (T w C E : Fin m) (N : Fin 10 → Fin m) (γ : S ^ m)
    (qw : fst (lookup w γ) ≡ fst W) (tg : Tags γ N)
    (hE : ⟨ γ ⊨ towerAt E w (N f0) ⟩) {n0 : ℕ} (ψ0 : Formula Ab n0)
    (qT : fst (lookup T γ) ≡ fst (satTable W (toS ψ0)))
    (qC : fst (lookup C γ) ≡ fst (slot W (toS ψ0))) where
```

<!--en-->
Only two underlying sets are abbreviated: `Tv` is the relation stored at the table position `T`, and `Cv` is the set stored at the code-domain position `C`. The following four constructions establish exactly the value-agreement, decoding, totality, and on-domain assumptions needed for these two sets.
<!--zh-->
这里仅缩写两个底层集合：`Tv` 是表位置 `T` 所存放的关系，`Cv` 是码定义域位置 `C` 所存放的集合。随后四项构造将准确建立这两个集合所需的取值相符、解码、全定义性与定义域约束前提。
<!--ja-->
ここで略記される底集合は二つだけです。`Tv` は表の位置 `T` に格納された関係であり、`Cv` は符号領域の位置 `C` に格納された集合です。続く四つの構成は、この二つの集合について必要となる値の一致、復号、全域性、領域条件の仮定を正確に与えます。
<!--/-->

```agda

    private
      Tv = fst (lookup T γ)
      Cv = fst (lookup C γ)

```

<!--en-->
Suppose `c` has the same underlying set as the key of a formula `ψ`, and `(c,yc)` is represented in `Tv`. Rewriting by `keyBridge` and `qT` turns this into an entry of the canonical table generated by `ψ0`; `entry-out` then proves `fst yc ≡ fst (SatW ψ)`. This pins a supplied value at a genuine formula key, but does not assert that such an entry exists.
<!--zh-->
设 `c` 的底层集合等于公式 `ψ` 的键，且 `(c,yc)` 在 `Tv` 中被表示。沿 `keyBridge` 与 `qT` 改写后，它成为 `ψ0` 生成的典范表中的一个条目；`entry-out` 因而证明 `fst yc ≡ fst (SatW ψ)`。该结论固定了真实公式键处一个已经给出的取值，却不宣称这样的条目必然存在。
<!--ja-->
`c` の底集合が論理式 `ψ` の鍵に等しく、`(c,yc)` が `Tv` に表されているとします。`keyBridge` と `qT` に沿って書き換えると、これは `ψ0` の生成する正準な表の項目になり、`entry-out` によって `fst yc ≡ fst (SatW ψ)` が得られます。この結論は正しい論理式の鍵において、すでに与えられた値を固定しますが、そのような項目の存在を主張するものではありません。
<!--/-->

```agda
      val≡ : ∀ {n} (ψ : Formula Ab n) (c yc : S) → fst c ≡ fst (keyS W ψ)
           → ⟨ pr (fst c) (fst yc) ∈ Tv ⟩ → fst yc ≡ fst (SatW ψ)
      val≡ ψ c yc qc h = entry-out W (toS ψ0) (toS ψ) (fst yc)
        (subst2 (λ u v → ⟨ pr u (fst yc) ∈ v ⟩) (qc ∙ keyBridge W ψ) qT h)

```

<!--en-->
Decoding starts with both membership `c ∈ Cv` and a specified arity presentation `fst c ≡ pr (# n) z`. After transporting membership through `qC`, `slotAb` gives, under propositional truncation, some formula at some arity whose key is `c`. The remaining work must show that this hidden arity is exactly `n` and that its formula code is exactly `z`.
<!--zh-->
解码同时从成员关系 `c ∈ Cv` 与指定的元数表示 `fst c ≡ pr (# n) z` 出发。沿 `qC` 搬运成员关系后，`slotAb` 在命题截断下给出某个元数处的一条公式，其键为 `c`。余下工作必须证明这个被隐藏的元数恰为 `n`，且该公式码恰为 `z`。
<!--ja-->
復号は、所属 `c ∈ Cv` と、指定されたアリティ表示 `fst c ≡ pr (# n) z` の両方から始まります。所属を `qC` に沿って運ぶと、`slotAb` は、あるアリティの論理式でその鍵が `c` であるものを命題的切り詰めの下で与えます。残る仕事は、この隠されたアリティがちょうど `n` であり、その論理式の符号がちょうど `z` であることを示すことです。
<!--/-->

```agda
      decode : (c : S) → ⟨ fst c ∈ Cv ⟩ → (n : ℕ) (z : V ℓ)
             → fst c ≡ pr (# n) z → ∥ Σ[ ψ ∈ Formula Ab n ] (z ≡ cd ψ) ∥₁
      decode c c∈ n z e = PT.map
        (λ { (n₁ , ψ₁ , e₁) →
          let q = pr-inj (sym e₁ ∙ e)
```

<!--en-->
The two equations for `c` give an equality between pairs. Pair injectivity compares their numeral components and code components, and numeral injectivity yields equality of the two arities. Because formulas are indexed by arity, the hidden formula must be transported along that equality; `cd-subst` then accounts for how its code changes under this dependent transport and produces a formula in `Formula Ab n` with code `z`.
<!--zh-->
关于 `c` 的两条等式给出一条配对等式。配对的单射性分别比较数码分量与公式码分量，数码的单射性再推出两个元数相等。由于公式以元数为索引，必须沿这条等式搬运被隐藏的公式；`cd-subst` 随后说明其编码在这次依赖搬运下如何变化，最终得到 `Formula Ab n` 中公式码为 `z` 的公式。
<!--ja-->
`c` についての二つの等式から、対どうしの等式が得られます。対の単射性は数項の成分と論理式の符号の成分をそれぞれ比較し、数項の単射性から二つのアリティの等しさが従います。論理式はアリティで添字づけられているため、隠された論理式をその等式に沿って輸送しなければなりません。`cd-subst` はこの依存輸送に伴う符号の変化を処理し、符号が `z` である `Formula Ab n` の論理式を与えます。
<!--/-->

```agda
              nq = #-inj′ (q .fst)
          in subst (Formula Ab) nq ψ₁ , (sym (q .snd) ∙ sym (cd-subst nq ψ₁)) })
        (slotAb ψ0 (fst c) (subst (λ u → ⟨ fst c ∈ u ⟩) qC c∈))

```

<!--en-->
For each `c ∈ Cv`, transport by `qC` places `c` in the canonical slot, where `slotTotal` gives, under propositional truncation, a value `y` whose pair with `c` lies in the canonical table. Transport by `qT` moves that entry back to `Tv`. The result proves totality as mere existence and does not choose a value function on `Cv`.
<!--zh-->
对每个 `c ∈ Cv`，沿 `qC` 搬运可把 `c` 放入典范槽位；`slotTotal` 随即在命题截断下给出取值 `y`，使它与 `c` 的配对属于典范表。再沿 `qT` 搬运，便把该条目送回 `Tv`。所得结论只以存在性证明全定义性，并未在 `Cv` 上选择取值函数。
<!--ja-->
各 `c ∈ Cv` について、`qC` による輸送で `c` を正準なスロットへ移すと、`slotTotal` は、`c` と対をなして正準な表に属する値 `y` を命題的切り詰めの下で与えます。さらに `qT` に沿ってその項目を `Tv` へ戻します。得られる全域性は存在だけを述べ、`Cv` 上の値関数を選択しません。
<!--/-->

```agda
      tot : (c : S) → ⟨ fst c ∈ Cv ⟩ → ∥ Σ[ yc ∈ S ] ⟨ pr (fst c) (fst yc) ∈ Tv ⟩ ∥₁
      tot c c∈ = PT.map
        (λ { (y , h) → y , subst (λ u → ⟨ pr (fst c) (fst y) ∈ u ⟩) (sym qT) h })
        (slotTotal W (toS ψ0) (fst c) (subst (λ u → ⟨ fst c ∈ u ⟩) qC c∈))

```

<!--en-->
For a member `e` of `Tv`, the equation `qT` first transports its membership to the canonical satisfaction table. The inversion `ent-slot` then yields, under propositional truncation, an arity `m`, a formula `χ`, and an equality between `fst e` and the underlying set of the canonical entry contributed by `χ`. Composing that equality with `prʟ-fst` gives `fst e ≡ pr (fst (keyʟ χ)) (fst (Sat W χ))`.
<!--zh-->
对于 `Tv` 的成员 `e`，等式 `qT` 先把其成员关系搬到典范满足关系表。求逆引理 `ent-slot` 随后在命题截断下给出元数 `m`、公式 `χ`，以及 `fst e` 与 `χ` 所贡献典范条目的底层集合之间的等式。再把这条等式与 `prʟ-fst` 复合，便得到 `fst e ≡ pr (fst (keyʟ χ)) (fst (Sat W χ))`。
<!--ja-->
`Tv` の要素 `e` について、等式 `qT` はまずその所属を正準な充足関係表へ移します。次に `ent-slot` は、命題的切り詰めの下で、アリティ `m`、論理式 `χ`、および `fst e` と `χ` が供給した正準な項目の底集合との等式を返します。この等式を `prʟ-fst` と合成すると、`fst e ≡ pr (fst (keyʟ χ)) (fst (Sat W χ))` が得られます。
<!--/-->

```agda
      onc : (e : S) → ⟨ fst e ∈ Tv ⟩
          → ∥ Σ[ c ∈ S ] Σ[ yc ∈ S ] ((fst e ≡ pr (fst c) (fst yc)) × ⟨ fst c ∈ Cv ⟩) ∥₁
      onc e e∈ = PT.map
        (λ { (m , χ , (q , _)) →
          let ee = q ∙ prʟ-fst (keyʟ χ) (Sat W χ)
```

<!--en-->
Inside that truncated witness, take `c = keyʟ χ` and `yc = Sat W χ`. The equality just obtained supplies the required decomposition of `e`. Its transported membership in the canonical table implies, by `inSlot`, that the key lies in the canonical slot, and `qC` moves this fact to `Cv`. Thus the on-domain condition is established under the same truncation, without choosing a decomposition globally or proving single-valuedness.
<!--zh-->
在这份命题截断的见证内部，取 `c = keyʟ χ`、`yc = Sat W χ`。刚得到的等式给出 `e` 所需的分解；把 `e` 的成员关系搬入典范表后，`inSlot` 推出该键属于典范槽位，`qC` 再把这一事实送入 `Cv`。由此在同一命题截断下建立定义域约束，而没有全局选择分解，也没有证明单值性。
<!--ja-->
この切り詰められた証人の内部で `c = keyʟ χ`、`yc = Sat W χ` と取ります。先ほど得た等式が `e` の必要な分解を与えます。`e` の所属を正準な表へ運ぶと、`inSlot` によりその鍵が正準なスロットに属することが従い、`qC` がこの事実を `Cv` へ移します。こうして同じ命題的切り詰めの下で領域条件が得られますが、分解を大域的に選択することも、一価性を証明することもありません。
<!--/-->

```agda
          in keyʟ χ , Sat W χ , (ee , subst (λ u → ⟨ fst (keyʟ χ) ∈ u ⟩) (sym qC)
               (inSlot W (toS ψ0) (fst (keyʟ χ)) (fst (Sat W χ))
                 (subst2 (λ u v → ⟨ u ∈ v ⟩) ee qT e∈))) })
        (ent-slot W (toS ψ0) (fst e) (subst (λ u → ⟨ fst e ∈ u ⟩) qT e∈))

```

<!--en-->
The common carrier, tag, and tower hypotheses are now combined with the four facts just proved: value agreement, decoding, totality, and the on-domain decomposition. These are exactly the seven hypotheses of `SatHoldsC`. Closure is absent in this direction because, when a constructor clause is rebuilt, its relation presents every matching child table entry universally and `val≡` pins each supplied child value directly. The decoder handles the current domain code, while `tot` and `onc` establish the other two top-level table conditions; no step here derives child-key membership from parent-key membership.
<!--zh-->
现在把共同的载体、标签、环境塔前提与刚证明的四项事实合在一起：取值相符、解码、全定义性与定义域分解。这恰是 `SatHoldsC` 的七项前提。这个方向不需要封闭性，因为重建某条构造子子句时，关系子句以全称方式给出每个相符的子公式表条目，而 `val≡` 直接钉扎其中已经给出的子公式取值。解码器处理当前的定义域码，`tot` 与 `onc` 则建立另外两项顶层表条件；此处没有任何一步需要从父公式键的成员关系推出子公式键的成员关系。
<!--ja-->
ここで共通の台、タグ、環境の塔の仮定に、先ほど証明した値の一致、復号、全域性、領域上の分解という四つの事実を合わせます。これらが `SatHoldsC` の七つの仮定です。この向きで閉性が不要なのは、構成子の節を組み直す際に、関係の節が対応するすべての子論理式の表項目を全称的に提示し、`val≡` がその各項目にすでに与えられた子の値を直接固定するからです。復号器は現在の領域の符号を扱い、`tot` と `onc` は残る二つの最上位の表条件を確立します。ここでは、親の論理式キーの所属から子論理式キーの所属を導く段階はありません。
<!--/-->

```agda
      module SH = SatHoldsC W T w C E N γ qw tg hE val≡ decode tot onc

```

<!--en-->
Consequently, the slot and satisfaction table generated by `ψ0`, as identified by `qC` and `qT`, satisfy `tableAt T w C E N`. This conclusion is the concrete table specification only: it neither proves slot closure nor identifies every table satisfying the specification with the canonical table. Later consumers add `slotClosed` and apply `SatSoundC.pinned` when they need uniqueness at a represented key.
<!--zh-->
因此，由 `qC` 与 `qT` 认同为 `ψ0` 所生成槽位和满足关系表的对象满足 `tableAt T w C E N`。这个结论仅是具体的表规格：它既不证明槽位封闭，也不把每张满足该规格的表都认同为典范表。后续章节在需要被表示键处的唯一性时，另行加入 `slotClosed` 并施用 `SatSoundC.pinned`。
<!--ja-->
したがって、`qC` と `qT` によって `ψ0` の生成するスロットと充足関係表に同定された対象は、`tableAt T w C E N` を満たします。この結論は具体的な表の仕様だけを述べます。スロットの閉性を証明せず、この仕様を満たすすべての表を正準な表と同定するものでもありません。後の利用箇所では、表された鍵での一意性が必要なときに `slotClosed` を別に加え、`SatSoundC.pinned` を適用します。
<!--/-->

```agda
    holds : ⟨ γ ⊨ tableAt T w C E N ⟩
    holds = SH.holds
```

<!--en-->
## Recap

Pinned recursion turns an externally supplied table specification into a theorem about the canonical satisfaction table, and conversely shows that the canonical table satisfies that specification. The proof separates the mathematical obligations cleanly: decoding identifies formula codes, totality supplies values merely, the on-domain condition accounts for every table entry, and closure is invoked only in the direction where child keys must be recovered from a represented parent key.
<!--zh-->
## 回顾

钉住递归把外部给定的表规格转化为关于典范满足关系表的定理，也反过来证明典范表满足这份规格。证明中的数学职责彼此分明：解码负责认出公式码，全定义性仅给出取值的存在性，定义域约束说明表中每个条目的来源，而封闭性只在必须由已经表示的父公式键追回子公式键的方向出现。
<!--ja-->
## まとめ

固定再帰は、外から与えられた表の仕様を正準な充足関係表についての定理へ変換し、逆に正準な表がその仕様を満たすことも示します。証明の数学的な役割は明確に分かれています。復号は論理式の符号を同定し、全域性は値の存在だけを与え、領域条件は表の各項目の由来を説明します。閉性が使われるのは、表された親の論理式キーから子のキーを回収しなければならない向きに限られます。
<!--/-->
