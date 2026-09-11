<!--en-->
# From ambient formulas to formulas over L

Suppose the coding chapters have handed us a bounded formula about the hierarchy, and we want to say the same thing inside `L`. Two obstacles stand in the way: the formula's constants are sets of the hierarchy, not elements of `L`, and its satisfaction was computed in the ambient structure, not in the restricted one. This chapter removes both.

The removal rests on two facts, each proved in its own chapter. First, the bounded-formula machinery can relabel the constants of a formula, provided each constant comes with evidence that it satisfies a chosen bound; here the bound is constructibility rather than membership in a stage, and the evidence is a constructibility certificate. Second, Δ₀ absoluteness says that a bounded formula means the same thing inside a transitive class as outside it, which is what makes replacing a constant by its pair with its certificate harmless.

Putting the two together gives the transfer theorem: a Δ₀ formula whose constants are all constructible can be read in the object language of `L`, and the two readings agree, witnessed by a chain of four paths with no induction of its own.
<!--zh-->
# 环境公式到 L 上公式

设编码诸章交给我们一条关于层级的有界公式，而我们要在 `L` 内部说出同样的话。这里有两重障碍：公式的常元是层级的集合，不是 `L` 的元素；而且它的满足是在环境结构中算出的，不是在限制结构中。本章就消去这两重障碍。

消去依赖两个事实，各自都在自己的章中证得。其一，有界公式的那套机制可以给公式的常元改名，只要每个常元带着满足某个界的证据；此处取的界是可构造性而非「落在某层内」，证据就是可构造性证书。其二，Δ₀ 绝对性说：有界公式在传递类之内与之外含义相同，正是这一点使「把常元换成它与证书的对」这一替换无害。

两者合起来便是搬运定理：常元全部可构造的 Δ₀ 公式可以在 `L` 的对象语言中读出，且两种读法一致，由一条四步的路径链作证，自身不含任何归纳。
<!--ja-->
# 周囲の論理式から L 上の論理式へ

符号化の諸章が階層についての有界論理式を渡してくれたとき、同じことを `L` の内部で言いたくなるでしょう。そこには二つの障害があります。論理式の定数は階層の集合であって `L` の要素ではないこと、そしてその充足が制限された構造ではなく周囲の構造で計算されていたことです。この章はその両方を取り除きます。

取り除きは二つの事実に依存します。それぞれ別の章で証明済みのものです。第一に、有界論理式を扱う機構は、各定数が選んだ界を満たす証拠を伴う限り、論理式の定数を改名できます。ここで界として取るのは「ある段階に属する」ではなく「構成可能である」であり、証拠とは構成可能性の証明書です。第二に、Δ₀ 絶対性は、有界論理式が推移的クラスの内側でも外側でも同じ意味を持つ、という主張であり、定数を「定数とその証明書の対」に置き換えることが無害なのはまさにこのためです。

この二つを合わせると移送定理が得られます。定数がすべて構成可能である Δ₀ 論理式は `L` の対象言語の中で読むことができ、二つの読み方は一致します。それを証するのは自前の帰納を一切含まない四段階のパスの連鎖です。
<!--/-->

<!--en-->
The whole chapter takes place at a single universe level `ℓ`. Both structures that will interpret the language are built over the truth algebra of propositions at level `ℓ-suc ℓ`, so a satisfaction statement is a proposition, and two such statements can be compared by a path. The ambient world is the cumulative hierarchy `V` at this level; the inner world is `L`, obtained from it by restricting to the constructible sets.
<!--zh-->
本章的全部工作都在同一个宇宙层级 `ℓ` 上进行。解释语言的两个结构都建立在层级 `ℓ-suc ℓ` 的命题真值代数之上，因此一条满足陈述是一个命题，两条这样的陈述可以由一条路径来比较。外层世界是该层级上的累积层级 `V`；内层世界则是 `L`，即在 `V` 中限制到可构造集所得。
<!--ja-->
この章の作業はすべて、単一の宇宙レベル `ℓ` の上で行われます。言語を解釈する二つの構造はどちらもレベル `ℓ-suc ℓ` の命題からなる真理値代数の上に築かれるため、充足の主張は命題であり、二つの主張はパスで比較できます。外側の世界はこのレベルの累積階層 `V` であり、内側の世界は `L`、つまり構成可能な集合への制限として得られるものです。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth

module L.Absoluteness {ℓ : Level} where

open import FOL.ZFStructure using ( module hPropStructure )
```

<!--en-->
The formula `φ` has constants in a type chosen by the surrounding interpretation, and a certificate `BoundedFo φ InL` says that each of those constants is constructible. Relabelling sends such a constant to the pair consisting of the ambient set and its constructibility proof. The theorem `⊨-map` compares satisfaction before and after this change of constant type, while Δ₀ absoluteness compares the ambient and restricted structures.
<!--zh-->
公式 `φ` 的常元来自周围解释所选的类型，证书 `BoundedFo φ InL` 说明每个常元都是可构造的。改名把这样的常元送到由环境集合及其可构造性证明组成的对。定理 `⊨-map` 比较改变常元类型前后的满足关系，而 Δ₀ 绝对性比较环境结构与限制结构。
<!--ja-->
論理式 `φ` の定数は周囲の解釈が選ぶ型に属し、証明書 `BoundedFo φ InL` は各定数が構成可能であることを述べます。改名はその定数を、周囲の集合と構成可能性の証明からなる対へ送ります。定理 `⊨-map` は定数の型を変える前後の充足を比較し、Δ₀ 絶対性は周囲の構造と制限した構造を比較します。
<!--/-->

```agda
open import FOL.Syntax using ( Formula )
open import FOL.LevyHierarchy using ( Δ₀ )
open import FOL.Manipulation.ConstantBounding using ( BoundedFo; module Relabel )
open import FOL.Manipulation.Relabelling using ( ⊨-map )
import FOL.Absoluteness
```

<!--en-->
The two worlds are now named. The ambient structure is `𝒮ᵥ`, the ZF-like structure on the hierarchy `V ℓ`: paths as equality, and the hierarchy's native membership. The inner structure is `𝒮ʟ`, the restriction of `𝒮ᵥ` to the class `isL` of constructible sets, and `isL-trans` records that this class is transitive, the one property absoluteness will require of it.
<!--zh-->
现在给两个世界命名。环境结构是 `𝒮ᵥ`，即层级 `V ℓ` 上类似 ZF 的结构：等词取路径，成员关系取层级原生的 `∈`。内层结构是 `𝒮ʟ`，即 `𝒮ᵥ` 限制到可构造集的类 `isL` 所得；`isL-trans` 记录这个类是传递的，这正是绝对性对它唯一要求的性质。
<!--ja-->
二つの世界に名前を付けます。周囲の構造は `𝒮ᵥ`、すなわち階層 `V ℓ` 上の ZF 風の構造です。等号はパスで、所属は階層本来のものです。内側の構造は `𝒮ʟ`、つまり `𝒮ᵥ` を構成可能な集合のクラス `isL` に制限したものであり、`isL-trans` はこのクラスが推移的であることを記録します。絶対性がそこに要求するのはこの性質だけです。
<!--/-->

```agda
import FOL.Semantics
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans )

open import Cubical.Data.Vec using ( map )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V )
```

<!--en-->
Both satisfaction relations take values in the same truth algebra `hPropAlgebra (ℓ-suc ℓ)`. The restricted carrier `S` consists of an ambient set paired with evidence that it is constructible. Ambient constants denote themselves through `id`, whereas an inner constant is already such a pair; projecting it with `fst` recovers the ambient set. These two interpretations are the endpoints compared by the transfer proof.
<!--zh-->
两条满足关系都取值于同一个真值代数 `hPropAlgebra (ℓ-suc ℓ)`。限制后的载体 `S` 由环境集合及其可构造性证明组成。环境常元通过 `id` 指称自身；内层常元已经是这样的对，用 `fst` 投影即可取回环境集合。这两个解释正是搬运证明所比较的两端。
<!--ja-->
二つの充足関係は同じ真理値代数 `hPropAlgebra (ℓ-suc ℓ)` に値を取ります。制限された台 `S` の元は、周囲の集合とその構成可能性の証明の対です。周囲の定数は `id` により自分自身を表し、内側の定数はすでにそのような対なので、`fst` で周囲の集合を取り出せます。この二つの解釈が移送証明の両端です。
<!--/-->

```agda

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ using ( S )

module SemV = FOL.Semantics (hPropAlgebra (ℓ-suc ℓ)) 𝒮ᵥ
open SemV using ( _^_ )
open SemV.At (V ℓ) id using () renaming ( _⊨_ to _⊨v_ )
```

<!--en-->
The absoluteness theorem is instantiated once, for the structure `𝒮ᵥ`, the class `isL`, and the proof `isL-trans` that the constructible sets form a transitive class. Its Δ₀ law `abs₀` turns a Δ₀ certificate for a formula of the inner language into a path of truth values between inner and outer satisfaction, and the inner satisfaction relation is renamed to plain `_⊨_`, since from here on it is the only one in the foreground.
<!--zh-->
绝对性定理只实例化一次：取结构 `𝒮ᵥ`、类 `isL`，以及可构造集构成传递类的证明 `isL-trans`。它的 Δ₀ 规律 `abs₀` 把内层语言公式的一条 Δ₀ 见证变成内外满足之间的一条真值路径；内层满足关系被改名为朴素的 `_⊨_`，因为此后它才是前台唯一的满足关系。
<!--ja-->
絶対性の定理は一度だけ実例化されます。構造 `𝒮ᵥ`、クラス `isL`、そして構成可能な集合が推移的クラスをなすことの証明 `isL-trans` を引数とします。その Δ₀ の法則 `abs₀` は、内側の言語の論理式に対する Δ₀ の証拠を、内側と外側の充足の間の真理値のパスへ変え、内側の充足関係には平易な `_⊨_` という名前が与えられます。これ以降、表に立つ充足関係はこれ一つだからです。
<!--/-->

```agda

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL using ( abs₀ ) renaming ( _⊨ᵐ_ to _⊨_ )
```

<!--en-->
## The bound is constructibility

Before any formula can move, the relabelling machinery must be told which constants are allowed and what they become. The whole choice of this section is that bound: a constant of the hierarchy is admissible when it is constructible, and the element of the carrier it becomes is that constant paired with its constructibility certificate. The round-trip condition, which asks that reading the image as a set give back the constant, holds by `refl`{.Agda}, since the image stores the set as its first component. Nothing else about `L` enters the instance.

A reader with no constants at all is admissible for free, which is worth naming, because most of the structural readers are of that kind: they speak entirely through variables and bounded quantifiers, so there is nothing to be constructible.
<!--zh-->
## 界是可构造性

在公式动身之前，须先告诉改名机制哪些常元合格、它们变成什么。本节的全部选择就是这个界：层级的一个常元合格，指它可构造；它变成的载体元素，就是该常元与它的可构造证书之对。往返条件要求把像当作集合读回时得到原常元，由于像把集合存在第一个分量，这由 `refl`{.Agda} 成立。实例中再没有用到关于 `L` 的别的东西。

完全不含常元的读式白白合格，这值得点名，因为大多数结构性读式正是这一类：它们全靠变元与有界量词说话，压根没有东西需要可构造。
<!--ja-->
## 境界は構成可能性

論理式を動かす前に、改名の機構にどの定数が適格で、それらが何になるかを知らせておく必要があります。この節の選択のすべてはその界にあります。階層のある定数が適格であるのは、それが構成可能なときであり、台の要素として成るのは、定数とその構成可能性の証明書の対です。像を集合として読み戻せばもとの定数が得られるという往復の条件は、像が集合を第一成分として格納するため、`refl`{.Agda} で成り立ちます。この実例で `L` について使われるのはこれだけで、それ以外のことは何も使われません。

定数をまったく含まない読み方は、証明なしに適格です。これに名を与えておく価値があります。構造に関する読み方のほとんどはまさにこの種のもので、変数と有界量化子だけによって語り、構成可能であるべきものが何もないからです。
<!--/-->

<!--en-->
The bound predicate is the whole choice of this section. A constant `c` of the hierarchy is admissible precisely when the proposition `isL c` holds, that is, when `c` lies in some ordinal stage of the constructible tower; `InL` just unpacks the underlying type of that proposition-valued class. Note where the level lives: `isL c` is a proposition at level `ℓ-suc ℓ`, so `InL` is a predicate valued in types of that level, not a decidable property of sets.
<!--zh-->
界谓词就是本节的全部选择。层级的一个常元 `c` 合格，恰指命题 `isL c` 成立，即 `c` 落在可构造塔的某个序数层中；`InL` 只是取出这个命题值类的底层类型。注意层级落在何处：`isL c` 是层 `ℓ-suc ℓ` 上的命题，因此 `InL` 是取值于该层类型的谓词，而不是集合的可判定性质。
<!--ja-->
界の述語こそ、この節の選択のすべてです。階層の定数 `c` が適格であるのは、命題 `isL c` が成り立つとき、すなわち `c` が構成可能な塔のある序数の段階に属するときに限ります。`InL` はこの命題値のクラスの基礎型を取り出すだけです。レベルがどこにあるかにも注意してください。`isL c` はレベル `ℓ-suc ℓ` の命題なので、`InL` はそのレベルの型に値を取る述語であり、集合の決定可能な性質ではありません。
<!--/-->

```agda
InL : V ℓ → Type (ℓ-suc ℓ)
InL c = ⟨ isL c ⟩
```

<!--en-->
The partial constant map is fixed point by point. A source constant is read in the common world `V ℓ` by `id`, since it already is a set there; a target constant, an element of the carrier `S`, is read by `fst`. The partial assignment sends each admissible `c` with evidence `p : InL c` to the pair `c , p`, and the triangle condition asks that `fst (c , p)` be `c`, which holds by `refl`. So the only correctness obligation is discharged by computation, and the data of `L` that entered was the certificate `p` alone.
<!--zh-->
部分常元映射被逐点固定。源常元已在共同世界 `V ℓ` 中是集合，经 `id` 读取；目标常元是载体 `S` 的元素，经 `fst` 读取。部分赋值把每个带证据 `p : InL c` 的合格常元 `c` 送到对 `c , p`，三角条件要求 `fst (c , p)` 就是 `c`，由 `refl` 成立。于是唯一正确性义务由计算消解，而 `L` 进入的全部数据只是那份证书 `p`。
<!--ja-->
部分的な定数写像は点ごとに固定されます。源の定数は、すでに共通の世界 `V ℓ` の中で集合であるため `id` で読まれ、先の定数、つまり台 `S` の要素は `fst` で読まれます。部分的な割り当ては、証拠 `p : InL c` を伴う各適格な定数 `c` を対 `c , p` へ送ります。三角条件は `fst (c , p)` が `c` であることを要求し、これは `refl` で成り立ちます。したがって唯一の正しさの義務は計算によって果たされ、`L` から入ってきたデータは証明書 `p` だけだったことになります。
<!--/-->

```agda

module ToL = Relabel {K = V ℓ} {K' = S} {W = V ℓ}
  id fst InL (λ c p → c , p) (λ c p → refl)
```

<!--en-->
At this instantiation, `liftFo` changes a bounded formula with ambient constants into one whose constants lie in the restricted carrier, and `Δ₀-liftFo` carries its Δ₀ certificate through the same relabelling. These are the syntactic inputs required before absoluteness can compare satisfaction.
<!--zh-->
在这个实例中，`liftFo` 把带环境常元的有界公式改成常元属于限制载体的公式，`Δ₀-liftFo` 则让其 Δ₀ 证书经过同一次改名。这两项正是在绝对性比较满足关系之前所需的句法输入。
<!--ja-->
この具体化では、`liftFo` が周囲の定数をもつ有界論理式を制限された台の定数をもつ論理式へ変え、`Δ₀-liftFo` が同じ改名に沿って Δ₀ の証明書を運びます。絶対性によって充足を比較する前に必要なのは、この二つの構文的な入力です。
<!--/-->

```agda

open ToL public using ( liftFo; Δ₀-liftFo )
```

<!--en-->
## The transfer

The question of this section is: when does a Δ₀ statement about the hierarchy, whose constants are constructible, hold in `L` exactly when it holds outside? The answer is `transferFo`{.Agda}, proved as one chain of four path-compositions read from the model outward. Absoluteness moves the lifted formula from satisfaction in `L` to satisfaction in the hierarchy at the projected environment. Then relabelling along the projection is undone, twice: once to recognize the lifted formula as the original with its constants replaced, and once, in the opposite direction, to see the original as itself. The middle step is where the relabelling's own correctness comes into play, and it is the only place the constants are looked at.

The identity relabelling in the last step is not idle. A formula is not definitionally its own image under the identity map on constants, since the map is applied by recursion; but its *meaning* is, and that is exactly what the relabelling theorem says at `f = id`.
<!--zh-->
## 搬运

本节的问题是：一条常元可构造的、关于层级的 Δ₀ 陈述，在 `L` 中成立与在外成立何时恰好一致？答案就是 `transferFo`{.Agda}，它被证成一条自模型向外读的四步路径串联。绝对性把抬升后的公式从「在 `L` 中满足」搬到「在层级中、于投影后的环境处满足」。随后沿投影的常元改名被撤销两次：一次是认出抬升后的公式就是原公式换掉常元的样子，一次是反方向地看出原公式就是它自己。中间那一步是常元改名自身的正确性发挥作用的地方，也是唯一需要看常元的地方。

最后一步的恒等变换不是白费。一条公式并不按定义等于它在常元恒等映射下的像，因为那个映射是递归施加的；但它的**含义**等于，而那正是常元改名定理在 `f = id` 处所说的话。
<!--ja-->
## 移送

この節の問いはこうです。定数が構成可能な、階層についての Δ₀ の主張は、`L` の内側で成り立つことと外側で成り立つこととが、いつまさに一致するのか。答えが `transferFo`{.Agda} であり、模型の側から外へ向かって読む四つのパスの連結として証明されます。絶対性が、持ち上げられた論理式の「`L` の中での充足」を、射影後の環境での階層における充足へ移します。次に射影に沿う定数の改名が二度、取り消されます。一度は、持ち上げられた論理式が定数を置き換えた元の論理式であると認めるため、もう一度は逆向きに、元の論理式がそれ自身であると見るためです。中間の段階で改名そのものの正しさが働き、定数が顧みられるのはそこだけです。

最後の段階にある恒等的な改名は無駄ではありません。定数上の恒等写像による像は、その写像が再帰的に適用されるため、論理式を定義的に等しいものにはしません。しかしその**意味**は等しく、それこそ改名の定理が `f = id` で述べていることです。
<!--/-->

<!--en-->
The statement equates two satisfaction judgments that a priori live in different worlds. On the left, the environment `γ` consists of elements of `S`, each a set with a constructibility certificate, and `γ ⊨ liftFo φ h` is satisfaction inside `L`, of the formula whose constants have been relabelled into `L`. On the right, the same environment is projected entrywise by `map fst`, and the original formula `φ` is evaluated in the ambient hierarchy. Both sides are propositions over the same truth algebra, so the claimed agreement is a single path, not an implication.
<!--zh-->
陈述等式的是两条先验地处于不同世界中的满足判断。左边，环境 `γ` 由 `S` 的元素组成，每个元素是带可构造证书的集合，`γ ⊨ liftFo φ h` 是常元已被改名进 `L` 的公式在 `L` 内的满足。右边，同一环境被 `map fst` 逐项投影，原公式 `φ` 在环境层级中求值。两边都是同一真值代数上的命题，因此所断言的一致是一条路径，而非蕴涵。
<!--ja-->
この主張が等しいと置くのは、先験的には異なる世界に住む二つの充足の判断です。左辺では環境 `γ` は `S` の要素、すなわち構成可能性の証明書を伴う集合からなり、`γ ⊨ liftFo φ h` は定数が `L` へと改名された論理式の `L` 内での充足です。右辺では同じ環境が `map fst` で項ごとに射影され、元の論理式 `φ` が周囲の階層の中で評価されます。両辺とも同じ真理値代数上の命題なので、主張される一致は単一のパスであって、含意ではありません。
<!--/-->

```agda
transferFo : ∀ {n} (φ : Formula (V ℓ) n) (h : BoundedFo InL φ) → Δ₀ φ
           → (γ : S ^ n) → (γ ⊨ liftFo φ h) ≡ ((map fst γ) ⊨v φ)
```

<!--en-->
The first two steps leave the constants alone. Absoluteness is applied with the transferred Δ₀ certificate `Δ₀-liftFo h dφ`, and it rewrites inner satisfaction in `L` into ambient satisfaction of the same formula at the projected environment. Then `⊨-map` with `f = fst` unfolds what a constant of the lifted formula denotes ambiently: the projection of the pair it names. Since the two occurrences of `fst` agree with how the inner world was built, this step only records that agreement, and `sym` presents it in the direction the chain needs.
<!--zh-->
前两步不触及常元。绝对性带着转移后的 Δ₀ 证书 `Δ₀-liftFo h dφ` 施用，把 `L` 中的内层满足改写为同一公式在投影后环境下的环境满足。随后 `⊨-map` 取 `f = fst`，展开抬升后公式的常元在环境中所指：即它所命名之对的投影。由于两处 `fst` 与内层世界的构造方式一致，这一步只是记下这份一致，再由 `sym` 把它摆成链条所需的方向。
<!--ja-->
最初の二段階は定数に触れません。絶対性は、転送された Δ₀ の証拠 `Δ₀-liftFo h dφ` とともに適用され、`L` の内側の充足を、同じ論理式の射影後の環境での周囲の充足へ書き換えます。次に `f = fst` として `⊨-map` を使うと、持ち上げられた論理式の定数が周囲で何を指すかが展開されます。それは、その定数が名指す対の射影です。二箇所の `fst` が内側の世界の作られ方と一致するため、この段階はその一致を記録するだけで、`sym` がそれを連鎖に必要な向きで提示します。
<!--/-->

```agda
transferFo φ h dφ γ =
    abs₀ (Δ₀-liftFo h dφ) γ
  ∙ sym (⊨-map (hPropAlgebra (ℓ-suc ℓ)) 𝒮ᵥ fst id (liftFo φ h) (map fst γ))
```

<!--en-->
The remaining two steps involve the constants, and together they say that relabelling changed nothing. The correctness law `liftFo-correct` gives a syntactic path `mapFo fst (liftFo φ h) ≡ mapFo id φ`: pushing the relabelled formula into the world along `fst` yields the original pushed along `id`, because the triangle condition held at each constant. Congruence then moves this path under the fixed environment and satisfaction symbol. Finally `⊨-map` with `f = id` says a formula and its identity image mean the same, closing the chain: inner satisfaction in `L` equals ambient satisfaction of `φ`.
<!--zh-->
剩下两步才涉及常元，合起来断言改名什么也没改。正确性规律 `liftFo-correct` 给出语法层面的路径 `mapFo fst (liftFo φ h) ≡ mapFo id φ`：把改名后的公式沿 `fst` 推进世界，与把原公式沿 `id` 推进去所得相同，因为三角条件在每个常元处都成立。同余再让这条路径在固定环境与满足符号下移动。最后 `⊨-map` 取 `f = id`，断言公式与其恒等像含义相同，链条就此闭合：`L` 中的内层满足等于 `φ` 的环境满足。
<!--ja-->
残りの二段階が定数に関わり、合わせて改名が何も変えていないことを述べます。正しさの法則 `liftFo-correct` は構文の水準のパス `mapFo fst (liftFo φ h) ≡ mapFo id φ` を与えます。三角条件が各定数で成り立っていたため、改名後の論理式を `fst` に沿って世界へ押し込んだものは、元の論理式を `id` に沿って押し込んだものと同じになります。続いて合同が、このパスを固定された環境と充足の記号の下へ動かします。最後に `f = id` の `⊨-map` が、論理式とその恒等像が同じ意味を持つと述べ、連鎖は閉じます。`L` の内側の充足は `φ` の周囲の充足に等しいのです。
<!--/-->

```agda
  ∙ cong (λ ψ → (map fst γ) ⊨v ψ) (ToL.liftFo-correct φ h)
  ∙ ⊨-map (hPropAlgebra (ℓ-suc ℓ)) 𝒮ᵥ id id φ (map fst γ)
```

<!--en-->
## Recap

`liftFo`{.Agda} carries a Δ₀ formula about the hierarchy into the object language of `L`, provided its constants are constructible, and `transferFo`{.Agda} says the two say the same thing. The coding chapters were written on the hierarchy side and stay there; this is how their readers are quoted from the `L` side, and it costs a chain of four steps rather than a re-statement.

One thing this does *not* do, and should not be asked to. It is Δ₀ only, because absoluteness is. That is no longer a restriction on what can be *said* in `L`, since the comprehension fields there take formulas of any complexity; it is a restriction on which conclusions can be drawn directly from the hierarchy. A predicate that is easier to write unbounded should be written unbounded, directly over the model, and not through here.
<!--zh-->
## 小结

`liftFo`{.Agda} 把关于层级的 Δ₀ 公式运进 `L` 的对象语言，只要它的常元可构造，而 `transferFo`{.Agda} 断言两者说的是同一件事。编码诸章写在层级一侧，就留在那里；这便是从 `L` 一侧引用其读式的办法，代价是一条四步的链，而非重新陈述一遍。

有一件事它**不**做，也不该被要求去做。它只管 Δ₀，因为绝对性只管 Δ₀。这已不再是对「在 `L` 中能说什么」的限制，因为那边的概括字段接受任意复杂度的公式；它限制的是「能从层级直接得到哪些结论」。一个用无界形式写起来更简便的谓词，就应当无界地、直接在模型上写出，而不必经过此处。
<!--ja-->
## まとめ

`liftFo`{.Agda} は、定数が構成可能である限り、階層についての Δ₀ 論理式を `L` の対象言語へ運び、`transferFo`{.Agda} は両者が同じことを述べていると言います。符号化の諸章は階層の側で書かれており、そこに留まります。`L` の側からそれらの読み方を引用するのがこの方法であり、その代価は書き直しではなく四段階の連鎖です。

これが**しない**ことが一つあり、そしてされてはならないことでもあります。これは Δ₀ に限られます。絶対性がそうだからです。しかし `L` の内側で何を**述べられる**かの制限ではなくなっています。そちらの内包のフィールドは任意の複雑さの論理式を受け取るからです。制限されるのは、階層から直接どの結論を引き出せるかです。無制限の形で書く方が容易な述語は、この経路を通さず、模型の上に直接、無制限に書かれるべきです。
<!--/-->
