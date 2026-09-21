<!--en-->
# From ambient formulas to formulas over L

Suppose the coding chapters have handed us a formula about the hierarchy, and we want to say the same thing inside `L`. Two adjustments stand in the way. The formula's constants currently have type `V ℓ`; to read the formula in `L`, each constant must become an element of the restricted carrier, that is, a set together with evidence that it is constructible. And the satisfaction of the original formula was computed in the ambient structure, not in the restricted one. This chapter removes both, and it does so one formula at a time: what is transferred is a particular `φ`, together with the data recording that its constants obey the chosen bound and that its shape is Δ₀.

The removal rests on two facts, each proved in its own chapter. First, the relabelling machinery can replace the constants of a formula of any complexity, provided each constant comes with evidence that it satisfies a chosen bound; here the bound is constructibility rather than membership in a stage, and the evidence is a constructibility proof. Second, Δ₀ absoluteness says that a bounded formula means the same inside a transitive class as outside it. That property is established formula by formula, by induction on the inductive witness certifying the formula is Δ₀; there is no blanket absoluteness for arbitrary formulas, and none should be expected, since unbounded quantifiers already change their truth value when the domain shrinks.

Putting the two together gives the transfer theorem: a Δ₀ formula whose constants are all constructible can be read in the object language of `L`, and the two readings agree. The agreement is a path of truth values assembled from four steps, and the proof spends no induction of its own; the inductions were already spent, once in each source chapter, on the data this chapter receives.
<!--zh-->
# 外围公式到 L 上公式

设编码诸章交给我们一条关于层级的公式，而我们要在 `L` 内部说出同样的话。这里有两处需要调整。公式的常元当前的类型是 `V ℓ`；要在 `L` 中读出这条公式，每个常元都必须换成限制载体中的元素，即一个集合连同它可构造的证据。而且原公式的满足是在外围结构中算出的，不是在限制结构中。本章消去这两处，并且逐条公式地进行：被搬运的是特定的 `φ`，连同记录其常元守界、形状为 Δ₀ 的数据。

消去依赖两个事实，各自都在自己的章中证得。其一，改名机制可以替换任意复杂度公式的常元，只要每个常元带着满足某个界的证据；此处取的界是可构造性而非「落在某层内」，证据就是可构造性的证明。其二，Δ₀ 绝对性说：有界公式在传递类之内与之外含义相同。这条性质是逐条公式证得的，归纳沿「该公式是 Δ₀」的归纳见证进行；对任意公式并不存在笼统的绝对性，也不该指望有，因为无界量词在论域缩小时本就会改值。

两者合起来便是搬运定理：常元全部可构造的 Δ₀ 公式可以在 `L` 的对象语言中读出，且两种读法一致。一致是一条真值路径，由四步组装而成，而证明自身不花费任何归纳。归纳早已在两个来源的章中各花一次，花在本章收到的数据上。
<!--ja-->
# 周囲の論理式から L 上の論理式へ

符号化の諸章が階層についての論理式を渡してくれたとき、同じことを `L` の内部で言いたくなるでしょう。ここには二つの調整が必要です。論理式の定数は現在 `V ℓ` という型に属しますが、`L` の中でこの論理式を読むには、各定数を制限された台の要素、すなわち集合と、それが構成可能であることの証拠の組に置き換えなければなりません。さらに、元の論理式の充足は制限された構造ではなく周囲の構造で計算されていました。本章はこの二つを取り除きます。しかも一度に一つの論理式ずつです。移送されるのは特定の `φ` と、その定数が選ばれた境界を守ること、そしてその形が Δ₀ であることを記録するデータです。

取り除きは二つの事実に依存します。それぞれ別の章で証明済みのものです。第一に、改名の機構は、任意の複雑さの論理式について、各定数が選んだ界を満たす証拠を伴う限り、定数を置き換えられます。ここで界として取るのは「ある段階に属する」ではなく「構成可能である」であり、証拠とは構成可能性の証明です。第二に、Δ₀ 絶対性は、有界論理式が推移的クラスの内側でも外側でも同じ意味を持つ、という主張です。この性質は一つ一つの論理式について、その式が Δ₀ であることを証明する帰納的な証拠の上の帰納法で確立されます。任意の論理式に対する包括的な絶対性はなく、またあってはなりません。非有界の量化子は、定義域が縮めば真偽を変えるからです。

この二つを合わせると移送定理が得られます。定数がすべて構成可能である Δ₀ 論理式は `L` の対象言語の中で読むことができ、二つの読み方は一致します。一致は真理値のパスであり、四段階で組み立てられ、証明自身は帰納を一切使いません。帰納はすでに、それぞれの元の章で、この章が受け取るデータのために使い果たされています。
<!--/-->

<!--en-->
The whole chapter takes place at a single universe level `ℓ`. Both structures that interpret the language have equality and membership valued in `hProp (ℓ-suc ℓ)`, so a satisfaction statement is a proposition, and two such statements can be compared by a path. The ambient world is the cumulative hierarchy `V` at this level; the inner world is `L`, obtained from it by restricting to the constructible sets.
<!--zh-->
本章的全部工作都在同一个宇宙层级 `ℓ` 上进行。解释语言的两个结构，其等词与隶属关系都取值于 `hProp (ℓ-suc ℓ)`，因此一条满足陈述是一个命题，两条这样的陈述可以由一条路径来比较。外围世界是该层级上的累积层级 `V`；内层世界则是 `L`，即在 `V` 中限制到可构造集所得。
<!--ja-->
この章の作業はすべて、単一の宇宙レベル `ℓ` の上で行われます。言語を解釈する二つの構造では、等号と所属がともに `hProp (ℓ-suc ℓ)` に値を取るため、充足の主張は命題であり、二つの主張はパスで比較できます。外側の世界はこのレベルの累積階層 `V` であり、内側の世界は `L`、つまり構成可能な集合への制限として得られるものです。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude

module L.Absoluteness {ℓ : Level} where

open import FOL.ZFStructure using ( module hPropStructure )
```

<!--en-->
The formula `φ` has constants in a type chosen by the surrounding interpretation, and a proof `h : BoundedFo InL φ` says that each of those constants is constructible. Relabelling sends such a constant to the pair consisting of the ambient set and its constructibility proof, and it does so for formulas of any complexity: unbounded quantifiers move along untouched. The theorem `⊨-map` compares satisfaction before and after this change of constant type, while Δ₀ absoluteness compares the outer and restricted structures, and it asks, in addition, that the formula carry its own Δ₀ witness.
<!--zh-->
公式 `φ` 的常元来自外围解释所选的类型，证明 `h : BoundedFo InL φ` 说明每个常元都是可构造的。改名把这样的常元送到由外围集合及其可构造性证明组成的对，而且这一替换对任意复杂度的公式都可用：无界量词原样随行。定理 `⊨-map` 比较改变常元类型前后的满足关系；Δ₀ 绝对性比较外围结构与限制结构，但额外要求公式带着自己的 Δ₀ 见证。
<!--ja-->
論理式 `φ` の定数は周囲の解釈が選ぶ型に属し、証拠 `h : BoundedFo InL φ` は各定数が構成可能であることを述べます。改名はその定数を、周囲の集合と構成可能性の証明からなる対へ送ります。しかもこの置き換えは、任意の複雑さの論理式に使えます。非有界の量化子はそのまま連れて行かれます。定理 `⊨-map` は定数の型を変える前後の充足を比較し、Δ₀ 絶対性は外側の構造と制限した構造を比較します。ただしそれは、論理式がみずからの Δ₀ の証拠を伴っていることをさらに要求します。
<!--/-->

```agda
open import FOL.Syntax using ( Formula )
open import FOL.LevyHierarchy using ( Δ₀ )
open import FOL.Manipulation.ConstantBounding using ( BoundedFo; module Relabel )
open import FOL.Manipulation.Relabelling using ( ⊨-map )
import FOL.Absoluteness
```

<!--en-->
The two worlds are now named. The ambient structure is `𝒮ᵥ`, the ZF-like structure on the hierarchy `V ℓ`: paths as equality, and the hierarchy's native membership. The inner structure is `𝒮ʟ`, the restriction of `𝒮ᵥ` to the class `isL` of constructible sets. This chapter has already chosen `isL` as the bound its constants must satisfy; the absoluteness instance then asks one more thing of the same class, namely that it be transitive, which `isL-trans` records.
<!--zh-->
现在给两个世界命名。外围结构是 `𝒮ᵥ`，即层级 `V ℓ` 上类似 ZF 的结构：等词取路径，成员关系取层级原生的 `∈`。内层结构是 `𝒮ʟ`，即 `𝒮ᵥ` 限制到可构造集的类 `isL` 所得。本章已选定 `isL` 作为常元须满足的界；绝对性实例随后对同一个类再提一项要求，即它是传递的，`isL-trans` 记录的正是这一点。
<!--ja-->
二つの世界に名前を付けます。周囲の構造は `𝒮ᵥ`、すなわち階層 `V ℓ` 上の ZF 風の構造です。等号はパスで、所属は階層本来のものです。内側の構造は `𝒮ʟ`、つまり `𝒮ᵥ` を構成可能な集合のクラス `isL` に制限したものです。本章はすでに `isL` を、定数の満たすべき境界として選んでいます。絶対性の実例は、同じクラスに対してさらに一つ、それが推移的であることを要求し、`isL-trans` が記録するのはこの点です。
<!--/-->

```agda
import FOL.Semantics
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V )
```

<!--en-->
Both satisfaction relations take values in the same type `hProp (ℓ-suc ℓ)`. The restricted carrier `S` consists of an ambient set paired with evidence that it is constructible. Ambient constants denote themselves through `id`, whereas an inner constant is already such a pair; projecting it with `fst` recovers the ambient set. These two interpretations are the endpoints compared by the transfer proof.
<!--zh-->
两条满足关系都取值于同一个类型 `hProp (ℓ-suc ℓ)`。限制后的载体 `S` 由外围集合及其可构造性证据组成。外围常元通过 `id` 指称自身；内层常元已经是这样的对，用 `fst` 投影即可取回外围集合。这两个解释正是搬运证明所比较的两端。
<!--ja-->
二つの充足関係は同じ型 `hProp (ℓ-suc ℓ)` に値を取ります。制限された台 `S` の元は、周囲の集合とその構成可能性の証拠の対です。周囲の定数は `id` により自分自身を表し、内側の定数はすでにそのような対なので、`fst` で周囲の集合を取り出せます。この二つの解釈が移送証明の両端です。
<!--/-->

```agda

open hPropStructure 𝒮ʟ using ( S )

module SemV = FOL.Semantics 𝒮ᵥ
open SemV using ( _^_ )
open SemV.At (V ℓ) id using () renaming ( _⊨_ to _⊨v_ )
```

<!--en-->
The absoluteness theorem is instantiated once, over the class `isL` that the bound already selected, with the additional input `isL-trans` saying that this class is transitive. Its Δ₀ law `abs₀` takes a formula of the inner language together with its Δ₀ witness and returns a path of truth values between inner and outer satisfaction. The witness is an argument, not a formality: the law is available exactly for those formulas whose Δ₀ witness has been written down, and the witness is what tells the induction, performed once in the absoluteness chapter, how this particular formula is built. From here on the inner satisfaction relation is renamed to plain `_⊨_`, since it is the only one in the foreground.
<!--zh-->
绝对性定理只实例化一次：在界已选定的类 `isL` 上，附加输入 `isL-trans` 说明该类是传递的。它的 Δ₀ 规律 `abs₀` 取内层语言的一条公式及其 Δ₀ 见证，返回内外满足之间的一条真值路径。见证是一个实打实的参数，而非形式：这条规律恰好对那些已写下 Δ₀ 见证的公式可用，而见证正是在绝对性一章中一次性完成的归纳的路线图，它告诉归纳这一条特定公式是如何构造的。此后内层满足关系被改名为朴素的 `_⊨_`，因为前台从此只有这一个满足关系。
<!--ja-->
絶対性の定理は一度だけ実例化されます。境界としてすでに選ばれたクラス `isL` の上で、追加の入力 `isL-trans` がこのクラスが推移的であることを述べます。その Δ₀ の法則 `abs₀` は、内側の言語の論理式とその Δ₀ の証拠を受け取り、内側と外側の充足の間の真理値のパスを返します。証拠は形式的な飾りではなく実引数です。この法則が使えるのは、Δ₀ の証拠が書き下された論理式に対して正確に限られ、その証拠が、絶対性の章で一度だけ行われた帰納に対して、この特定の論理式がどのように組み立てられているかを伝えるからです。以降、内側の充足関係には平易な `_⊨_` の名が与えられます。表に立つ充足関係はこれ一つだからです。
<!--/-->

```agda

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL using ( abs₀ ) renaming ( _⊨ᵐ_ to _⊨_ )
```

<!--en-->
## The bound is constructibility

Before any formula can move, the relabelling machinery must be told which constants are allowed and what they become. The whole choice of this section is that bound: a constant of the hierarchy is admissible when it is constructible, and the element of the carrier it becomes is that constant paired with its constructibility evidence. The round-trip condition, which asks that reading the image as a set give back the constant, holds by `refl`{.Agda}, since the image stores the set as its first component. Nothing else about `L` enters the instance.

A reader with no constants at all is admissible for free, which is worth naming, because most of the structural readers are of that kind: they speak entirely through variables and bounded quantifiers, so there is nothing to be constructible.
<!--zh-->
## 界是可构造性

在公式动身之前，须先告诉改名机制哪些常元合格、它们变成什么。本节的全部选择就是这个界：层级的一个常元合格，指它可构造；它变成的载体元素，就是该常元与它的可构造性证据之对。往返条件要求把像当作集合读回时得到原常元，由于像把集合存在第一个分量，这由 `refl`{.Agda} 成立。实例中再没有用到关于 `L` 的别的东西。

完全不含常元的读式白白合格，这值得点名，因为大多数结构性读式正是这一类：它们全靠变元与有界量词说话，压根没有东西需要可构造。
<!--ja-->
## 境界は構成可能性

論理式を動かす前に、改名の機構にどの定数が適格で、それらが何になるかを知らせておく必要があります。この節の選択のすべてはその界にあります。階層のある定数が適格であるのは、それが構成可能なときであり、台の要素として成るのは、定数とその構成可能性の証拠の対です。像を集合として読み戻せばもとの定数が得られるという往復の条件は、像が集合を第一成分として格納するため、`refl`{.Agda} で成り立ちます。この実例で `L` について使われるのはこれだけで、それ以外のことは何も使われません。

定数をまったく含まない読み方は、証明なしに適格です。これに名を与えておく価値があります。構造に関する読み方のほとんどはまさにこの種のもので、変数と有界量化子だけによって語り、構成可能であるべきものが何もないからです。
<!--/-->

<!--en-->
The bound predicate is the whole choice of this section. A constant `c` of the hierarchy is admissible precisely when the proposition `isL c` holds, that is, when `c` lies in some ordinal stage of the constructible hierarchy; `InL` just unpacks the underlying type of that proposition-valued class. Note where the level lives: `isL c` is a proposition at level `ℓ-suc ℓ`, so `InL` is a predicate valued in types of that level, not a decidable property of sets.
<!--zh-->
界谓词就是本节的全部选择。层级的一个常元 `c` 合格，恰指命题 `isL c` 成立，即 `c` 落在可构造层级的某个序数层中；`InL` 只是取出这个命题值类的底层类型。注意层级落在何处：`isL c` 是层 `ℓ-suc ℓ` 上的命题，因此 `InL` 是取值于该层类型的谓词，而不是集合的可判定性质。
<!--ja-->
界の述語こそ、この節の選択のすべてです。階層の定数 `c` が適格であるのは、命題 `isL c` が成り立つとき、すなわち `c` が構成可能階層のある序数の段階に属するときに限ります。`InL` はこの命題値のクラスの基礎型を取り出すだけです。レベルがどこにあるかにも注意してください。`isL c` はレベル `ℓ-suc ℓ` の命題なので、`InL` はそのレベルの型に値を取る述語であり、集合の決定可能な性質ではありません。
<!--/-->

```agda
InL : V ℓ → Type (ℓ-suc ℓ)
InL c = ⟨ isL c ⟩
```

<!--en-->
The partial constant map is fixed point by point. A source constant is read in the common world `V ℓ` by `id`, since it already is a set there; a target constant, an element of the carrier `S`, is read by `fst`. The partial assignment sends each admissible `c` with evidence `p : InL c` to the pair `c , p`, and the triangle condition asks that `fst (c , p)` be `c`, which holds by `refl`. So the only correctness obligation is discharged by computation, and the data of `L` that entered was the evidence `p` alone.
<!--zh-->
部分常元映射被逐点固定。源常元已在共同世界 `V ℓ` 中是集合，经 `id` 读取；目标常元是载体 `S` 的元素，经 `fst` 读取。部分赋值把每个带证据 `p : InL c` 的合格常元 `c` 送到对 `c , p`，三角条件要求 `fst (c , p)` 就是 `c`，由 `refl` 成立。于是唯一正确性义务由计算消解，而 `L` 进入的全部数据只是那份证据 `p`。
<!--ja-->
部分的な定数写像は点ごとに固定されます。源の定数は、すでに共通の世界 `V ℓ` の中で集合であるため `id` で読まれ、先の定数、つまり台 `S` の要素は `fst` で読まれます。部分的な割り当ては、証拠 `p : InL c` を伴う各適格な定数 `c` を対 `c , p` へ送ります。三角条件は `fst (c , p)` が `c` であることを要求し、これは `refl` で成り立ちます。したがって唯一の正しさの義務は計算によって果たされ、`L` から入ってきたデータは証拠 `p` だけだったことになります。
<!--/-->

```agda

module ToL = Relabel {K = V ℓ} {K' = S} {W = V ℓ}
  id fst InL (λ c p → c , p) (λ c p → refl)
```

<!--en-->
At this instantiation, `liftFo` applies to a formula of any complexity whose constants satisfy `InL`, replacing each constant by the pair of the ambient set with its constructibility evidence; and `Δ₀-liftFo h dφ` turns a Δ₀ witness `dφ` for the original formula into a Δ₀ witness for the lifted one. The two-sided law `abs₀` used by `transferFo` compares satisfaction only for Δ₀ formulas, so the witness must be carried along, and the relabelling is exactly what makes carrying it possible.
<!--zh-->
在这个实例中，`liftFo` 适用于常元满足 `InL` 的任意复杂度的公式，把每个常元换成外围集合与其可构造性证据组成的对；而 `Δ₀-liftFo h dφ` 把原公式的 Δ₀ 见证 `dφ` 变成抬升后公式的 Δ₀ 见证。`transferFo` 所用的双向规律 `abs₀` 只对 Δ₀ 公式比较满足，因此见证必须随身携带，而改名正是使携带成为可能的手段。
<!--ja-->
この具体化では、`liftFo` は、定数が `InL` を満たす任意の複雑さの論理式に使え、各定数を周囲の集合とその構成可能性の証拠の対へ置き換えます。そして `Δ₀-liftFo h dφ` は、元の論理式の Δ₀ の証拠 `dφ` を、持ち上げられた論理式の Δ₀ の証拠へ変えます。`transferFo` が用いる双方向の法則 `abs₀` が充足を比較するのは Δ₀ 論理式に限られるため、証拠は伴って運ばれねばらず、その運搬を可能にするのがまさにこの改名です。
<!--/-->

```agda

open ToL public using ( liftFo; Δ₀-liftFo )
```

<!--en-->
## The transfer

The question of this section is: when does a Δ₀ statement about the hierarchy, whose constants are constructible, hold in `L` exactly when it holds outside? The answer is `transferFo`{.Agda}, proved as one chain of four path-compositions read from the model outward. The first step is the only one that uses the absoluteness induction: performed once, over Δ₀ witnesses, in its own chapter, it is here invoked at the particular lifted formula. The remaining three steps are relabelling bookkeeping, in which the constants are finally looked at and found unchanged.

One step of that bookkeeping deserves a remark. The identity relabelling in the last step is not idle. A formula is not definitionally its own image under the identity map on constants, since the map is applied by recursion; but its *meaning* is, and that is exactly what the relabelling theorem says at `f = id`.
<!--zh-->
## 搬运

本节的问题是：一条常元可构造的、关于层级的 Δ₀ 陈述，在 `L` 中成立与在外成立何时恰好一致？答案就是 `transferFo`{.Agda}，它被证成一条自模型向外读的四步路径串联。第一步是唯一使用绝对性归纳的一步：那次归纳沿 Δ₀ 见证在其自身的章中一次性完成，此处只是在眼前这条抬升后的公式上调用它。其余三步是改名的簿记，常元至此才被检视，并被发现分毫未动。

这份簿记里有一处值得一提。最后一步的恒等改名不是白费。一条公式并不按定义等于它在常元恒等映射下的像，因为那个映射是递归施加的；但它的**含义**等于，而那正是常元改名定理在 `f = id` 处所说的话。
<!--ja-->
## 移送

この節の問いはこうです。定数が構成可能な、階層についての Δ₀ の主張は、`L` の内側で成り立つことと外側で成り立つこととが、いつまさに一致するのか。答えが `transferFo`{.Agda} であり、模型の側から外へ向かって読む四つのパスの連結として証明されます。第一段階だけが絶対性の帰納を使います。その帰納は Δ₀ の証拠の上で、みずからの章の中ですでに一度完了しており、ここでは目の前の持ち上げられた論理式において呼び出されるだけです。残りの三段階は改名の簿記であり、定数はここではじめて顧みられ、何も変わっていないことが分かります。

この簿記の一箇所には、説明を加える価値があります。最後の段階にある恒等的な改名は無駄ではありません。定数上の恒等写像による像は、その写像が再帰的に適用されるため、論理式を定義的に等しいものにはしません。しかしその**意味**は等しく、それこそ改名の定理が `f = id` で述べていることです。
<!--/-->

<!--en-->
The statement equates two satisfaction judgments that a priori live in different worlds. On the left, the environment `γ` consists of elements of `S`, each a set with a constructibility proof, and `γ ⊨ liftFo φ h` is satisfaction inside `L`, of the formula whose constants have been relabelled into `L`. On the right, the same environment is projected entrywise by `map fst`, and the original formula `φ` is evaluated in the ambient hierarchy. Both sides are propositions in the same `hProp`, so the claimed agreement is a single path, not an implication.
<!--zh-->
陈述等式的是两条先验地处于不同世界中的满足判断。左边，环境 `γ` 由 `S` 的元素组成，每个元素是带可构造性证明的集合，`γ ⊨ liftFo φ h` 是常元已被改名进 `L` 的公式在 `L` 内的满足。右边，同一环境被 `map fst` 逐项投影，原公式 `φ` 在外围层级中求值。两边都是同一个 `hProp` 中的命题，因此所断言的一致是一条路径，而非蕴涵。
<!--ja-->
この主張が等しいと置くのは、先験的には異なる世界に住む二つの充足の判断です。左辺では環境 `γ` は `S` の要素、すなわち構成可能性の証明を伴う集合からなり、`γ ⊨ liftFo φ h` は定数が `L` へと改名された論理式の `L` 内での充足です。右辺では同じ環境が `map fst` で項ごとに射影され、元の論理式 `φ` が周囲の階層の中で評価されます。両辺とも同じ `hProp` の命題なので、主張される一致は単一のパスであって、含意ではありません。
<!--/-->

```agda
transferFo : ∀ {n} (φ : Formula (V ℓ) n) (h : BoundedFo InL φ) → Δ₀ φ
           → (γ : S ^ n) → (γ ⊨ liftFo φ h) ≡ ((map fst γ) ⊨v φ)
```

<!--en-->
The first step changes the interpretation structure and leaves the syntax alone. Absoluteness is applied with the inner Δ₀ witness `Δ₀-liftFo h dφ`, and it rewrites satisfaction of the lifted formula in `L` into satisfaction of the same formula in the hierarchy, at the projected environment. The second step is the relabelling theorem `⊨-map` at `f = fst`, which handles the interpretation of the constants of the lifted formula and of the environment variables under the projection: the formula says the same thing when its constants and its environment entries are both read through `fst`. The two steps agree with how the inner world was built, and `sym` presents the second in the direction the chain needs.
<!--zh-->
第一步更换解释结构而语法不动。绝对性以内层 Δ₀ 见证 `Δ₀-liftFo h dφ` 施用，把抬升后公式在 `L` 中的满足，改写为同一公式在层级中、于投影后环境下的满足。第二步是取 `f = fst` 的改名定理 `⊨-map`，它处理抬升后公式的常元与环境变量在投影之下的解释：当常元与环境分量都经 `fst` 读取时，这条公式所说的东西不变。两步都与内层世界的构造方式一致，`sym` 再把第二步摆成链条所需的方向。
<!--ja-->
第一段階は解釈する構造を取り替えるだけで、構文はそのままです。絶対性は、内側の Δ₀ の証拠 `Δ₀-liftFo h dφ` とともに適用され、持ち上げられた論理式の `L` における充足を、同じ論理式の、射影後の環境での階層における充足へ書き換えます。第二段階は `f = fst` とした改名の定理 `⊨-map` で、持ち上げられた論理式の定数と環境の変数の、射影の下での解釈を処理します。定数と環境の各成分を `fst` を通して読んでも、この論理式の述べることは変わらないのです。二つの段階は内側の世界の作られ方と一致し、`sym` が第二を連鎖に必要な向きで提示します。
<!--/-->

```agda
transferFo φ h dφ γ =
    abs₀ (Δ₀-liftFo h dφ) γ
  ∙ sym (⊨-map 𝒮ᵥ fst id (liftFo φ h) (map fst γ))
```

<!--en-->
The remaining two steps involve the constants, and together they say that relabelling changed nothing. The correctness law `liftFo-correct` gives a syntactic path `mapFo fst (liftFo φ h) ≡ mapFo id φ`: pushing the relabelled formula into the world along `fst` yields the original pushed along `id`, because the triangle condition held at each constant. Congruence then moves this path under the fixed environment and satisfaction symbol. Finally `⊨-map` with `f = id` says a formula and its identity image mean the same, closing the chain: inner satisfaction in `L` equals ambient satisfaction of `φ`.
<!--zh-->
剩下两步才涉及常元，合起来断言改名什么也没改。正确性规律 `liftFo-correct` 给出语法层面的路径 `mapFo fst (liftFo φ h) ≡ mapFo id φ`：把改名后的公式沿 `fst` 推进世界，与把原公式沿 `id` 推进去所得相同，因为三角条件在每个常元处都成立。同余再让这条路径在固定环境与满足符号下移动。最后 `⊨-map` 取 `f = id`，断言公式与其恒等像含义相同，链条就此闭合：`L` 中的内层满足等于 `φ` 的外围满足。
<!--ja-->
残りの二段階が定数に関わり、合わせて改名が何も変えていないことを述べます。正しさの法則 `liftFo-correct` は構文の水準のパス `mapFo fst (liftFo φ h) ≡ mapFo id φ` を与えます。三角条件が各定数で成り立っていたため、改名後の論理式を `fst` に沿って世界へ押し込んだものは、元の論理式を `id` に沿って押し込んだものと同じになります。続いて合同が、このパスを固定された環境と充足の記号の下へ動かします。最後に `f = id` の `⊨-map` が、論理式とその恒等像が同じ意味を持つと述べ、連鎖は閉じます。`L` の内側の充足は `φ` の周囲の充足に等しいのです。
<!--/-->

```agda
  ∙ cong (λ ψ → (map fst γ) ⊨v ψ) (ToL.liftFo-correct φ h)
  ∙ ⊨-map 𝒮ᵥ id id φ (map fst γ)
```

<!--en-->
## Recap

`liftFo`{.Agda} carries a formula about the hierarchy, of any complexity, into the object language of `L` as soon as its constants are constructible; `transferFo`{.Agda} adds the requirement of a Δ₀ witness and says that then the two readings agree. The equivalence on this page is therefore Δ₀ only. Beyond Δ₀, the absoluteness chapter proves two one-way laws, Σ₁ truth passing upward and Π₁ truth passing downward, and they apply specifically to those two adjacent classes. Neither result is a restriction on what can be *said* in `L`: the separation and replacement schemas there accept formulas of any complexity. They mark, rather, which conclusions can be drawn directly from the hierarchy. A predicate that is easier to write unbounded should be written unbounded, directly over the model, and not through here.
<!--zh-->
## 小结

`liftFo`{.Agda} 把关于层级的、任意复杂度的公式运进 `L` 的对象语言，只要其常元可构造；`transferFo`{.Agda} 附加 Δ₀ 见证的要求，并断言此时两种读法一致。因此本页的等价仅限 Δ₀。越出 Δ₀，绝对性一章证明了两条单向规律：Σ₁ 真值向上传递，Π₁ 真值向下传递，并且它们恰好适用于这两个紧邻类别。这两条结果都不是对「在 `L` 中能说什么」的限制：那边的分离与替换模式接受任意复杂度的公式。它们标出的是「能从层级直接得到哪些结论」。一个用无界形式写起来更简便的谓词，就应当无界地、直接在模型上写出，而不必经过此处。
<!--ja-->
## まとめ

`liftFo`{.Agda} は、定数が構成可能である限り、階層についての任意の複雑さの論理式を `L` の対象言語へ運びます。`transferFo`{.Agda} は Δ₀ の証拠の存在をさらに要求し、そのとき二つの読み方が一致すると述べます。したがってこのページの同値は Δ₀ に限られます。Δ₀ の外では、絶対性の章が二つの一方向の法則、Σ₁ の真理が上向きに保存されることと Π₁ の真理が下向きに保存されることを証明しており、これら二つの隣接するクラスにそれぞれ適用されます。どちらの結果も、`L` の内側で何を**述べられる**かの制限ではありません。そちらの分出と置換の論理式のスキーマは、任意の複雑さの論理式を受け取ります。制限されるのは、階層から直接どの結論を引き出せるかです。無制限の形で書く方が容易な述語は、この経路を通さず、模型の上に直接、無制限に書かれるべきです。
<!--/-->
