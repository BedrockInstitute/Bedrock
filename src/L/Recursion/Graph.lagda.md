<!--en-->
# Graphs of recursive definitions

A recursion in `L` gives a unique value at every point of an internal domain. A set-theoretic function is represented by its graph, the set of ordered pairs `pr(x , y)` with input first and output second. This chapter turns the value relation of a recursion into such a set `F`, then proves that `F` is functional and has exactly the original domain.
<!--zh-->
# 递归定义的图

`L` 中的递归在内部定义域的每一点给出唯一取值。集合论函数由其图表示，即输入在前、输出在后的有序对 `pr(x , y)` 所成的集合。本章把递归的取值关系转换成这样的集合 `F`，再证明 `F` 具有函数性，并且定义域恰为原来的定义域。
<!--ja-->
# 再帰的定義のグラフ

`L` の再帰は、内部の定義域の各点で一意な値を与えます。集合論の関数は、そのグラフ、すなわち入力を先、出力を後に置く順序対 `pr(x , y)` の集合で表されます。本章は再帰の値の関係をそのような集合 `F` に変え、`F` が関数的で、もとの定義域をちょうどもつことを証明します。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Classical using ( LEM )

module L.Recursion.Graph {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
```

<!--en-->
The graph must itself be described in the object language. The available syntax forms conjunctions and existential statements, while renaming places an existing two-variable value relation beneath a new quantifier. The ambient operation `pr` supplies ordered-pair codes, and its injectivity later recovers both coordinates from an equality of codes.
<!--zh-->
图本身必须用对象语言描述。现有语法可以组成合取与存在陈述，而改名把已有的二元取值关系放到新的量词之下。外围运算 `pr` 给出有序对编码，其单射性随后可从编码相等恢复两个坐标。
<!--ja-->
グラフ自体を対象言語で記述する必要があります。利用する構文は連言と存在文を作り、改名によって既存の二変数の値関係を新しい量化子の下に置きます。周囲の演算 `pr` が順序対の符号を与え、その単射性により、後で符号の等式から両方の座標を復元できます。
<!--/-->

```agda
open import FOL.Syntax using ( Formula; _∧̇_; ∃̇_ )
open import FOL.Manipulation.Renaming using ( renameFo; module Sat )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Coding {ℓ} using ( pr; pr-inj )
```

<!--en-->
The constructible pairing operation produces an element of `L` whose underlying set is the ambient ordered-pair code. The general recursion theorem can then apply replacement to a formula describing those pairs. Equality of constructible elements is reduced to equality of their underlying sets because constructibility proofs are propositions.
<!--zh-->
可构造的有序对运算产生 `L` 中的元素，其底层集合就是外围的有序对编码。于是，一般递归定理可以把替换应用于描述这些有序对的公式。由于可构造性证明是命题，可构造元素的相等可归结为其底层集合的相等。
<!--ja-->
構成可能な順序対の演算は、その基礎集合が周囲の順序対の符号である `L` の要素を作ります。そこで一般の再帰定理を、これらの順序対を記述する論理式に適用できます。構成可能性の証明は命題なので、構成可能な要素の等式は基礎集合の等式に帰着します。
<!--/-->

```agda
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans )
open import L.Recursion {ℓ} lem using ( Recursion; module Of )
open import L.Coding.Model {ℓ}
  using ( prAtL; prAtL-adequate; prʟ; prʟ-fst; svAt; svAt-in; domAt; domAt-intro )

open import Cubical.Data.Sigma using ( Σ≡Prop )
```

<!--en-->
Several propositions below are obtained from truncated existence statements. They may be eliminated only into propositional goals. Membership and equality in the cumulative hierarchy have precisely this property, which allows witnesses to be used without making a global choice.
<!--zh-->
下文有若干命题由截断的存在陈述得到。截断只能消去到命题目标；累积层级中的成员关系与相等恰好具有这一性质。因此，可以使用存在见证，而不必作全局选择。
<!--ja-->
以下では、切り詰められた存在からいくつかの命題を得ます。切り詰めを消去できるのは命題である目標に限られます。累積階層の所属と等式はこの性質をもつため、大域的な選択を行わずに存在の証人を利用できます。
<!--/-->

```agda
open import Cubical.Foundations.HLevels using ( isPropΣ )
open import Cubical.Functions.Logic using ( ∃[∶]-syntax )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_; setIsSet )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁; squash₁ )

```

<!--en-->
The formulas are interpreted in the constructible structure. The local satisfaction notation and its renaming theorem connect syntactic substitutions with changes of environment; all later claims about the graph are statements in this semantics.
<!--zh-->
公式在可构造结构中解释。局部的满足记号及其改名定理，把句法代换与环境变化联系起来；下文关于函数图的陈述都采用这一语义。
<!--ja-->
論理式は構成可能構造で解釈されます。局所的な充足記号と改名定理が、構文的な代入と環境の変化を結びつけます。以下の関数グラフに関する主張は、すべてこの意味論で述べられます。
<!--/-->

```agda
open hPropStructure 𝒮ʟ

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL renaming ( _⊨ᵐ_ to _⊨_ )
module Ren = Sat 𝒮ʟ id using ( Agrees; ⊨-rename )
module PairFo (φ : Formula S 2) where

```

<!--en-->
## A formula for ordered pairs

Fix a two-variable formula `φ`, read as a relation between a value and an index. The module `PairFo` constructs another two-variable formula: at a candidate pair `e` and an index `p`, it asserts that some value `z` satisfies `φ(z,p)` and that `e` is the ordered pair `pr(p,z)`.
<!--zh-->
## 有序对公式

固定一条二元公式 `φ`，把它读作取值与索引之间的关系。模块 `PairFo` 构造另一条二元公式：给定候选有序对 `e` 与索引 `p`，它断言存在取值 `z` 满足 `φ(z,p)`，并且 `e` 是有序对 `pr(p,z)`。
<!--ja-->
## 順序対の論理式

値と添字の関係として読む二変数の論理式 `φ` を固定します。モジュール `PairFo` は別の二変数の論理式を作ります。順序対の候補 `e` と添字 `p` に対し、`φ(z,p)` を満たす値 `z` が存在し、`e` が順序対 `pr(p,z)` であることを述べます。
<!--/-->

```agda
  ρ : Fin 2 → Fin 3
  ρ zero       = zero
  ρ (suc zero) = suc (suc zero)

```

<!--en-->
The renaming map records how the two free variables of `φ` occur below the existential quantifier. The value variable remains in slot zero and is bound by that quantifier; the index variable moves to slot two. The formula `pairFo` is opaque, so subsequent reasoning uses its proved semantic characterization rather than unfolding it.
<!--zh-->
改名映射记录 `φ` 的两个自由变元如何出现在存在量词之下。取值变元仍位于零号槽，并由该量词约束；索引变元移到二号槽。公式 `pairFo` 被声明为不透明，因此后续推理使用已经证明的语义刻画，而不展开其定义。
<!--ja-->
改名写像は、`φ` の二つの自由変数が存在量化子の下でどこに現れるかを記録します。値の変数は位置 0 に残って量化子に束縛され、添字の変数は位置 2 へ移ります。`pairFo` は不透明なので、以後は定義を展開せず、証明された意味論的特徴づけを用います。
<!--/-->

```agda
  opaque
    pairFo : Formula S 2
```

<!--en-->
The formula conjoins two assertions under the existential quantifier. The first says that `e` codes the ordered pair of `p` and the quantified value; the second is the renamed copy of `φ`. Thus the syntax directly mirrors the mathematical description of a member of a function graph.
<!--zh-->
该公式在存在量词之下合取两个断言。第一项说明 `e` 编码 `p` 与被量化取值组成的有序对；第二项是改名后的 `φ`。因此，这段语法直接对应函数图成员的数学描述。
<!--ja-->
この論理式は、存在量化子の下で二つの主張を連言します。第一は `e` が `p` と量化された値との順序対を符号化すること、第二は改名された `φ` です。したがって、この構文は関数グラフの要素の数学的記述をそのまま表します。
<!--/-->

```agda
    pairFo = ∃̇ (prAtL (suc zero) (suc (suc zero)) zero ∧̇ renameFo ρ φ)

```

<!--en-->
The agreement proof verifies that renaming preserves the intended environment. In the longer environment `(z ∷ e ∷ p ∷ [])`, the renamed value slot reads `z` and the renamed index slot reads `p`, exactly as the original formula does in `(z ∷ p ∷ [])`.
<!--zh-->
一致性证明验证改名保持预期的环境。在较长环境 `(z ∷ e ∷ p ∷ [])` 中，改名后的取值槽读出 `z`，索引槽读出 `p`，与原公式在 `(z ∷ p ∷ [])` 中的读法完全相同。
<!--ja-->
一致の証明は、改名が意図した環境を保つことを確かめます。長い環境 `(z ∷ e ∷ p ∷ [])` では、改名後の値の位置は `z` を、添字の位置は `p` を読み、元の論理式を `(z ∷ p ∷ [])` で読む場合と正確に一致します。
<!--/-->

```agda
    private
      ag : (z e p : S) → Ren.Agrees ρ (z ∷ e ∷ p ∷ []) (z ∷ p ∷ [])
      ag z e p zero       = refl
      ag z e p (suc zero) = refl

```

<!--en-->
Two semantic equalities prepare the outward direction. Correctness of the ordered-pair formula identifies its satisfaction with the ambient equality `fst e ≡ pr (fst p) (fst z)`. The renaming theorem identifies satisfaction of the renamed formula with satisfaction of the original `φ` at value `z` and index `p`.
<!--zh-->
两条语义等式为向外方向作准备。有序对公式的正确性把其满足关系等同于外围等式 `fst e ≡ pr (fst p) (fst z)`；改名定理则把改名公式的满足关系等同于原公式 `φ` 在取值 `z`、索引 `p` 处的满足关系。
<!--ja-->
二つの意味論的等式が外向きの読みを準備します。順序対の論理式の正しさにより、その充足は周囲の等式 `fst e ≡ pr (fst p) (fst z)` と同一視されます。改名定理により、改名後の論理式の充足は、値 `z` と添字 `p` における元の `φ` の充足と同一視されます。
<!--/-->

```agda
      at : (z e p : S)
         → ⟨ (z ∷ e ∷ p ∷ []) ⊨ prAtL (suc zero) (suc (suc zero)) zero ⟩
         ≡ (fst e ≡ pr (fst p) (fst z))
      at z e p = cong ⟨_⟩ (prAtL-adequate (suc zero) (suc (suc zero)) zero (z ∷ e ∷ p ∷ []))

      gr : (z e p : S)
```

<!--en-->
Reading `pairFo` outward yields a propositionally truncated value `z`, together with the ordered-pair equation and a proof of `φ(z,p)`. Reading it inward reverses these transports: such a value, equation, and graph proof construct a satisfaction witness for `pairFo`. These are the two semantic directions used below.
<!--zh-->
向外读取 `pairFo`，得到一个经命题截断的取值 `z`，以及有序对等式和 `φ(z,p)` 的证明。向内读取则反向搬运这些数据：取值、等式与图证明共同构造 `pairFo` 的满足见证。下文使用的正是这两个语义方向。
<!--ja-->
`pairFo` を外向きに読むと、命題的に切り詰められた値 `z` と、順序対の等式および `φ(z,p)` の証明が得られます。内向きにはこれらの輸送を逆に行い、値、等式、グラフの証明から `pairFo` の充足の証人を作ります。以下ではこの二つの意味論的方向を用います。
<!--/-->

```agda
         → ⟨ (z ∷ e ∷ p ∷ []) ⊨ renameFo ρ φ ⟩ ≡ ⟨ (z ∷ p ∷ []) ⊨ φ ⟩
      gr z e p = cong ⟨_⟩ (Ren.⊨-rename ρ φ (z ∷ e ∷ p ∷ []) (z ∷ p ∷ []) (ag z e p))

    pair-out : (e p : S) → ⟨ (e ∷ p ∷ []) ⊨ pairFo ⟩
             → ∥ Σ[ z ∈ S ] ((fst e ≡ pr (fst p) (fst z)) × ⟨ (z ∷ p ∷ []) ⊨ φ ⟩) ∥₁
    pair-out e p = PT.map (λ { (z , (q , h)) →
```

<!--en-->
The inward lemma completes the semantic equivalence and the construction now turns to a fixed recursion. Its original domain and value relation are retained; only the values sent to replacement will change from bare outputs to ordered pairs of inputs and outputs.
<!--zh-->
向内引理补全了语义等价，接下来固定一项递归。原来的定义域与取值关系保持不变；改变的只是送入替换的取值，它们将由单独的输出变成输入与输出组成的有序对。
<!--ja-->
内向きの補題で意味論的同値が完成し、ここから一つの再帰を固定します。もとの定義域と値の関係は保たれます。変わるのは置換へ渡す値だけで、出力そのものから入力と出力の順序対へ変わります。
<!--/-->

```agda
      z , (transport (at z e p) q , transport (gr z e p) h) })

    pair-in : (e p z : S) → fst e ≡ pr (fst p) (fst z) → ⟨ (z ∷ p ∷ []) ⊨ φ ⟩
            → ⟨ (e ∷ p ∷ []) ⊨ pairFo ⟩
    pair-in e p z q h = ∣ z , (transport (sym (at z e p)) q , transport (sym (gr z e p)) h) ∣₁
module Graph (R₀ : Recursion) where
```

<!--en-->
## Domain and values

The recursion supplies a domain, its original graph formula, and contractibility of the graph-value fiber at each domain member. Its derived value is written `fn`. The local predicate `Mem x` is the underlying membership assertion that `fn` requires.
<!--zh-->
## 定义域与取值

递归给出定义域、原取值图公式，以及定义域每个成员处图取值纤维的可缩性。由此导出的取值记作 `fn`。局部谓词 `Mem x` 是 `fn` 所需的底层成员关系断言。
<!--ja-->
## 定義域と値

再帰は、定義域、もとの値のグラフを表す論理式、および定義域の各要素におけるグラフの値ファイバーの可縮性を与えます。そこから得られる値を `fn` と記します。局所的な述語 `Mem x` は、`fn` が必要とする基礎の所属の主張です。
<!--/-->

```agda
  open Of R₀ public using ( dom; graph; funct ) renaming ( val to fn )
  Mem : S → Type (ℓ-suc ℓ)
  Mem x = ⟨ fst x ∈ fst dom ⟩

  isPropMem : (x : S) → isProp (Mem x)
  isPropMem x = snd (fst x ∈ fst dom)

```

<!--en-->
Membership in a set is proposition-valued, so `Mem x` is a proposition. Consequently, any two proofs that `x` belongs to the domain are equal. This proof irrelevance ensures that the value `fn x m` does not depend on the chosen membership certificate.
<!--zh-->
集合的成员关系取值于命题，因此 `Mem x` 是命题。于是，`x` 属于定义域的任意两份证明都相等。这一证明无关性保证取值 `fn x m` 不依赖所选的成员证书。
<!--ja-->
集合への所属は命題値なので、`Mem x` は命題です。したがって、`x` が定義域に属することの任意の二つの証明は等しくなります。この証明無関係性により、値 `fn x m` は選んだ所属の証明に依存しません。
<!--/-->

```agda
  private
    defines : (x : S) (m : Mem x) → ⟨ (fn x m ∷ x ∷ []) ⊨ graph ⟩
    defines x m = funct x m .fst .snd

    only : (x : S) (m : Mem x) (y : S) → ⟨ (y ∷ x ∷ []) ⊨ graph ⟩ → y ≡ fn x m
    only x m y h = sym (cong fst (funct x m .snd (y , h)))

```

<!--en-->
Contractibility provides two facts about the original value relation. The selected centre proves that the formula `graph` is satisfied in the environment `(fn x m ∷ x ∷ [])`. Its contraction proves that any other `y` satisfying the formula at `x` equals `fn x m`.
<!--zh-->
可缩性给出关于原取值关系的两项事实。选定的中心证明公式 `graph` 在环境 `(fn x m ∷ x ∷ [])` 中得到满足；收缩则证明，在 `x` 处满足该公式的其他任何 `y` 都等于 `fn x m`。
<!--ja-->
可縮性から、もとの値関係について二つの事実が得られます。選ばれた中心は、環境 `(fn x m ∷ x ∷ [])` で論理式 `graph` が満たされることを証明します。収縮は、`x` でこの論理式を満たす他の任意の `y` が `fn x m` に等しいことを証明します。
<!--/-->

```agda
    module Fo = PairFo graph renaming ( pairFo to fo; pair-out to out; pair-in to into )

    fn-irr : (x : S) (m m' : Mem x) → fn x m ≡ fn x m'
    fn-irr x m m' = cong (fn x) (isPropMem x m m')
    pairOf : (x : S) → Mem x → S
    pairOf x m = prʟ x (fn x m)

```

<!--en-->
The ordered-pair formula is now specialized to the original value relation. Proof irrelevance for `Mem x` gives `fn-irr`, while `pairOf x m` is the constructible ordered pair of `x` and its value. Its underlying set is `pr (fst x) (fst (fn x m))`.
<!--zh-->
现在把有序对公式用于原取值关系。`Mem x` 的证明无关性给出 `fn-irr`；`pairOf x m` 则是 `x` 与其取值组成的可构造有序对，其底层集合为 `pr (fst x) (fst (fn x m))`。
<!--ja-->
ここで順序対の論理式をもとの値関係に適用します。`Mem x` の証明無関係性から `fn-irr` が得られ、`pairOf x m` は `x` とその値との構成可能な順序対です。その基礎集合は `pr (fst x) (fst (fn x m))` です。
<!--/-->

```agda
    uniq : (x : S) (m : Mem x) (p : S) → ⟨ (p ∷ x ∷ []) ⊨ Fo.fo ⟩ → p ≡ pairOf x m
    uniq x m p h = PT.rec (isSetS p (pairOf x m))
      (λ { (z , (e , g)) → Σ≡Prop (λ v → snd (isL v))
        (e ∙ cong (λ w → pr (fst x) (fst w)) (only x m z g) ∙ sym (prʟ-fst x (fn x m))) })
      (Fo.out p x h)

```

<!--en-->
Suppose a candidate `p` satisfies the specialized pair formula at `x`. The outward lemma merely supplies a value `z`, an equality between the underlying set of `p` and `pr(x,z)`, and a proof that `z` satisfies the original graph. Original-value uniqueness identifies `z` with `fn x m`; composing the resulting equalities proves `p ≡ pairOf x m`.
<!--zh-->
设候选元素 `p` 在 `x` 处满足专门化后的有序对公式。向外引理仅仅给出取值 `z`、`p` 的底层集合与 `pr(x,z)` 之间的等式，以及 `z` 满足原图的证明。原取值的唯一性把 `z` 等同于 `fn x m`；复合所得等式便证明 `p ≡ pairOf x m`。
<!--ja-->
候補 `p` が `x` で特殊化した順序対の論理式を満たすとします。外向きの補題は、値 `z`、`p` の基礎集合と `pr(x,z)` との等式、および `z` がもとのグラフを満たす証明を単に与えます。もとの値の一意性により `z` は `fn x m` と同一視され、得られた等式を合成すると `p ≡ pairOf x m` が従います。
<!--/-->

```agda
    R : Recursion
    R = record
      { dom   = dom
      ; graph = Fo.fo
      ; funct = λ x m →
```

<!--en-->
## Collecting the graph

A new recursion uses the same domain and the ordered-pair formula as its value relation. At `x`, its centre is `pairOf x m`; the inward semantic lemma proves that this pair satisfies the formula, and `uniq` proves that every other satisfying candidate is equal to it.
<!--zh-->
## 收集函数图

构造一项新的递归，沿用原定义域，并以有序对公式作为取值关系。在 `x` 处，其中心为 `pairOf x m`；向内语义引理证明该有序对满足公式，而 `uniq` 证明其他所有满足公式的候选元素都与它相等。
<!--ja-->
## 関数グラフを集める

もとの定義域を保ち、順序対の論理式を値関係とする新しい再帰を作ります。`x` における中心は `pairOf x m` です。内向きの意味論的補題がこの順序対による式の充足を証明し、`uniq` が他のすべての候補はそれと等しいことを証明します。
<!--/-->

```agda
          ( pairOf x m
          , Fo.into (pairOf x m) x (fn x m) (prʟ-fst x (fn x m)) (defines x m) )
        , λ { (p , h) → Σ≡Prop (λ w → snd ((w ∷ x ∷ []) ⊨ Fo.fo)) (sym (uniq x m p h)) } }

    module T = Of R using ( table; table-in; table-out )

  F : S
```

<!--en-->
The dependent-pair contraction compares a candidate value together with its satisfaction proof against the chosen centre. Equality of their first components is `uniq`; the satisfaction components are propositions, so this equality determines the whole dependent-pair path. The result is a valid `Recursion` for ordered pairs.
<!--zh-->
依值对的收缩把候选取值及其满足证明与选定中心比较。第一分量的相等由 `uniq` 给出；满足证明是命题，因此这一等式即可确定整个依值对的路径。所得记录是关于有序对的一项合法 `Recursion`。
<!--ja-->
依存対の収縮は、候補の値とその充足の証明を、選ばれた中心と比較します。第一成分の等式は `uniq` が与え、充足の証明は命題なので、この等式から依存対全体のパスが定まります。これにより、順序対についての正しい `Recursion` が得られます。
<!--/-->

```agda
  F = T.table

  F-in : (x : S) (m : Mem x) → ⟨ pr (fst x) (fst (fn x m)) ∈ fst F ⟩
  F-in x m = subst (λ w → ⟨ w ∈ fst F ⟩) (prʟ-fst x (fn x m))
    (T.table-in x (pairOf x m) m
      (Fo.into (pairOf x m) x (fn x m) (prʟ-fst x (fn x m)) (defines x m)))

```

<!--en-->
Replacement applied to this recursion forms the value range of its ordered-pair values. That range is the desired graph `F`. Thus `F` is an element of `L`, and every element placed in it is an ordered pair of a domain element with its recursively determined value.
<!--zh-->
把替换应用于这项递归，便形成其有序对取值的值域。这个值域就是所需的函数图 `F`。因此，`F` 是 `L` 的元素，其中放入的每个成员都是定义域元素与其递归确定取值组成的有序对。
<!--ja-->
この再帰に置換を適用すると、順序対としての値の値域ができます。この値域が求める関数グラフ `F` です。したがって `F` は `L` の要素であり、そこに入る各要素は、定義域の要素と再帰で定まる値との順序対です。
<!--/-->

```agda
  F-out : (p : V ℓ) → ⟨ p ∈ fst F ⟩
        → ∥ Σ[ x ∈ S ] Σ[ m ∈ Mem x ] (p ≡ pr (fst x) (fst (fn x m))) ∥₁
  F-out p h = PT.rec squash₁ step (T.table-out pS h)
    where
    pS : S
```

<!--en-->
The inward membership direction is immediate from the replacement specification. For a domain witness `m`, the constructible ordered pair `pairOf x m` satisfies the pair formula, hence belongs to the replacement range. Transport along `prʟ-fst` restates this as membership of the ambient code `pr (fst x) (fst (fn x m))` in the underlying set of `F`.
<!--zh-->
成员关系的向内方向直接来自替换规格。给定定义域见证 `m`，可构造有序对 `pairOf x m` 满足有序对公式，因此属于替换的值域。沿 `prʟ-fst` 搬运后，这被表述为外围编码 `pr (fst x) (fst (fn x m))` 属于 `F` 的底层集合。
<!--ja-->
所属の内向きは置換の仕様から直ちに得られます。定義域の証人 `m` に対し、構成可能な順序対 `pairOf x m` は順序対の論理式を満たすので、置換の値域に属します。`prʟ-fst` に沿って輸送すると、周囲の符号 `pr (fst x) (fst (fn x m))` が `F` の基礎集合に属するという形になります。
<!--/-->

```agda
    pS = p , isL-trans {x = fst F} {y = p} h (snd F)

    step : Σ[ x ∈ S ] (Mem x × ⟨ (pS ∷ x ∷ []) ⊨ Fo.fo ⟩)
         → ∥ Σ[ x ∈ S ] Σ[ m ∈ Mem x ] (p ≡ pr (fst x) (fst (fn x m))) ∥₁
    step (x , (m , g)) = PT.map
      (λ { (z , (e , gz)) →
```

<!--en-->
For the outward direction, begin with an ambient set `p ∈ fst F`. Downward closure of constructibility packages `p` as an element `pS` of `L`. The replacement specification first yields, merely, an index `x`, a domain proof `m`, and satisfaction of the ordered-pair formula by `pS`.
<!--zh-->
对向外方向，从外围集合 `p ∈ fst F` 出发。可构造性的向下封闭把 `p` 包装成 `L` 的元素 `pS`。替换规格首先仅仅给出索引 `x`、定义域证明 `m`，以及 `pS` 满足有序对公式的证明。
<!--ja-->
外向きには、周囲の集合 `p ∈ fst F` から始めます。構成可能性の下方閉性により、`p` を `L` の要素 `pS` として包みます。置換の仕様からまず、添字 `x`、定義域の証明 `m`、および `pS` が順序対の論理式を満たすことが、単に得られます。
<!--/-->

```agda
        x , m , (e ∙ cong (λ w → pr (fst x) (fst w)) (only x m z gz)) })
      (Fo.out pS x g)
  Fib : S → S → Type (ℓ-suc ℓ)
  Fib x y = Σ[ m ∈ Mem x ] (fst y ≡ fst (fn x m))

  isPropFib : (x y : S) → isProp (Fib x y)
```

<!--en-->
The semantic outward lemma then opens a second truncation and supplies a value `z`, an ordered-pair equality, and a proof of the original graph relation. Original-value uniqueness replaces `z` by `fn x m`. The result states merely that `p` is the code `pr(x,fn x m)` for some domain element `x`.
<!--zh-->
随后，语义向外引理打开第二层截断，给出取值 `z`、有序对等式以及原取值关系的证明。原取值的唯一性把 `z` 替换为 `fn x m`。所得结论仅仅说明：对某个定义域元素 `x`，`p` 是编码 `pr(x,fn x m)`。
<!--ja-->
次に意味論的な外向きの補題が第二の切り詰めを開き、値 `z`、順序対の等式、もとの値関係の証明を与えます。もとの値の一意性により `z` を `fn x m` に置き換えます。その結果、ある定義域の要素 `x` に対して `p` が符号 `pr(x,fn x m)` であることが単に示されます。
<!--/-->

```agda
  isPropFib x y = isPropΣ (isPropMem x) (λ m → setIsSet (fst y) (fst (fn x m)))

  pair-out : (x y : S) → ⟨ pr (fst x) (fst y) ∈ fst F ⟩ → Fib x y
  pair-out x y h = PT.rec (isPropFib x y) step (F-out (pr (fst x) (fst y)) h)
    where
    step : Σ[ x' ∈ S ] Σ[ m' ∈ Mem x' ] (pr (fst x) (fst y) ≡ pr (fst x') (fst (fn x' m')))
```

<!--en-->
## Recovering the coordinates

For fixed `x` and `y`, the fiber `Fib x y` consists of a domain proof `m : Mem x` and an equality between the underlying set of `y` and that of `fn x m`. Both components are propositions: domain membership is proposition-valued and equality in `V` is a proposition. Hence the whole fiber is a proposition.
<!--zh-->
## 恢复两个坐标

固定 `x` 与 `y` 后，纤维 `Fib x y` 由两部分组成：定义域证明 `m : Mem x`，以及 `y` 的底层集合与 `fn x m` 的底层集合之间的等式。两部分都是命题：定义域成员关系取值于命题，而 `V` 中的相等也是命题。因此，整个纤维是命题。
<!--ja-->
## 二つの座標を復元する

`x` と `y` を固定すると、ファイバー `Fib x y` は二つの成分からなります。定義域の証明 `m : Mem x` と、`y` の基礎集合と `fn x m` の基礎集合との等式です。定義域への所属は命題値であり、`V` の等式も命題なので、両方の成分が命題です。したがってファイバー全体も命題です。
<!--/-->

```agda
         → Fib x y
    step (x' , m' , e) = subst (λ z → Fib z y)
      (Σ≡Prop (λ v → snd (isL v)) (sym (pr-inj e .fst))) (m' , pr-inj e .snd)

  γ : S ^ 2
  γ = F ∷ dom ∷ []

```

<!--en-->
If the ordered-pair code `pr(fst x,fst y)` belongs to `F`, the outward description gives `x'`, `m'`, and an equality with `pr(fst x',fst(fn x' m'))`. Injectivity of `pr` yields equalities of both coordinates. The input equality transports `m'` to a proof that `x` lies in the domain; the output equality gives the second component of `Fib x y`.
<!--zh-->
若有序对编码 `pr(fst x,fst y)` 属于 `F`，向外刻画便给出 `x'`、`m'`，以及它与 `pr(fst x',fst(fn x' m'))` 的等式。`pr` 的单射性恢复两个坐标的等式。输入坐标的等式把 `m'` 搬运成 `x` 属于定义域的证明；输出坐标的等式给出 `Fib x y` 的第二分量。
<!--ja-->
順序対の符号 `pr(fst x,fst y)` が `F` に属するなら、外向きの特徴づけから `x'`、`m'`、および `pr(fst x',fst(fn x' m'))` との等式が得られます。`pr` の単射性が両方の座標の等式を与えます。入力座標の等式に沿って `m'` を輸送すると `x` が定義域に属する証明となり、出力座標の等式が `Fib x y` の第二成分となります。
<!--/-->

```agda
  sv : ⟨ γ ⊨ svAt zero ⟩
  sv = svAt-in zero γ (λ x y y' p q →
    let (m , e)   = pair-out x y p
        (m' , e') = pair-out x y' q
    in e ∙ cong fst (fn-irr x m m') ∙ sym e')

```

<!--en-->
The environment `γ = F ∷ dom ∷ []` assigns the two free variables used by the formulas for single-valuedness and domain. To prove single-valuedness, take two pairs in `F` with the same first coordinate `x`. Their fibers provide membership proofs `m` and `m'` and output equalities to `fn x m` and `fn x m'`. Proof irrelevance identifies the two function values, so the outputs are equal.
<!--zh-->
环境 `γ = F ∷ dom ∷ []` 为单值性公式与定义域公式的两个自由变元赋值。为证明单值性，取 `F` 中第一坐标同为 `x` 的两个有序对。相应纤维给出成员证明 `m`、`m'`，以及两个输出分别等于 `fn x m`、`fn x m'` 的等式。证明无关性使这两个函数值相等，因而两个输出相等。
<!--ja-->
環境 `γ = F ∷ dom ∷ []` は、単値性と定義域を表す論理式の二つの自由変数に値を割り当てます。単値性を示すため、第一座標が同じ `x` である二つの順序対が `F` に属するとします。それぞれのファイバーから所属の証明 `m`、`m'` と、二つの出力が `fn x m`、`fn x m'` に等しいことが得られます。証明無関係性により二つの関数値が等しくなり、したがって出力も等しくなります。
<!--/-->

```agda
  dm : ⟨ γ ⊨ domAt zero (suc zero) ⟩
  dm = domAt-intro zero (suc zero) γ (λ x → fwd x , bwd x)
    where
    fwd : (x : S) → ⟨ ∃[ y ∶ S ] (pr (fst x) (fst y) ∈ fst F) ⟩ → Mem x
    fwd x = PT.rec (isPropMem x) (λ { (y , p) → fst (pair-out x y p) })

```

<!--en-->
Finally, the domain formula is proved in both directions. If `x` occurs as the first coordinate of some ordered pair in `F`, `pair-out` returns a fiber and hence a proof `Mem x`. Conversely, from `m : Mem x`, the pair `pr(x,fn x m)` belongs to `F` by `F-in`, so `x` occurs as a first coordinate. Therefore the domain of the collected graph is exactly `dom`.
<!--zh-->
最后，从两个方向证明定义域公式。若 `x` 作为第一坐标出现在 `F` 的某个有序对中，`pair-out` 返回一个纤维，从而给出 `Mem x` 的证明。反过来，由 `m : Mem x`，`F-in` 说明有序对 `pr(x,fn x m)` 属于 `F`，所以 `x` 确实作为第一坐标出现。因此，所构造函数图的定义域恰为 `dom`。
<!--ja-->
最後に、定義域の論理式を両方向に証明します。`x` が `F` のある順序対の第一座標として現れるなら、`pair-out` がファイバーを返し、そこから `Mem x` の証明が得られます。逆に `m : Mem x` なら、`F-in` により順序対 `pr(x,fn x m)` が `F` に属するので、`x` は第一座標として現れます。したがって、構成した関数グラフの定義域はちょうど `dom` です。
<!--/-->

```agda
    bwd : (x : S) → Mem x → ⟨ ∃[ y ∶ S ] (pr (fst x) (fst y) ∈ fst F) ⟩
    bwd x m = ∣ fn x m , F-in x m ∣₁

```
