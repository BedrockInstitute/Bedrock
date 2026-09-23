<!--en-->
# The constructible hierarchy inside L

A first-order graph inside `L` records the external constructible hierarchy up
to a chosen ordinal. Tables are compared with the external tower, shown
functional and exact, then collected into a constructible set whose members are
precisely the earlier stages.
<!--zh-->
# L 内部的可构造层级

`L` 内的一阶图记录外部的可构造层级，直至给定序数。表中的值与外部层级逐一对照，被证明具有函数性且精确；随后这些对被收集成一个可构造集合，其成员恰是此前各层。
<!--ja-->
# L の内部における構成可能階層

`L` 内の一階のグラフは、指定した順序数までの外部の構成可能階層を記録する。表の値を外部の塔と照らして関数的かつ正確であると示し、そののち、これらの対を、それより前の段階をちょうど要素とする構成可能集合へ集める。
<!--/-->

<!--en-->
The chapter constructs the internal hierarchy. For an ordinal `α` of the
hierarchy, `hierL`{.Agda} at `α` is an element of `L` whose members are exactly
the ordered pairs of an ordinal `β` below `α` with the tower's value `Lset β`
at it. One pattern repeats throughout. A **table** is a set of ordered pairs;
it is *correct* on a set `B` when every value it records below `B` is the meta
tower there, and *complete* when it records a value at every argument below.
Correct and complete tables are exactly what the step condition of the graph
reads and what it can be written from, so the pair of lemmas connecting the
step with the tower serves both elimination and introduction.
<!--zh-->
本章构造内部层级。对层级中的序数 `α`，`hierL`{.Agda} 在 `α` 处是 `L` 的一个元素，其成员恰是有序对「低于 `α` 的序数 `β` 与塔在该处的取值 `Lset β`」。全章重复同一个模式。**表**是有序对之集；说它在集合 `B` 上**正确**，指它在 `B` 以下记录的每个取值都是元层面的塔在那里的取值；说它**完备**，指它在以下的每个实参处都记录了取值。正确且完备的表，恰是图的步进条件所读出的内容，也恰是步进条件据以写下的内容；因此连接步进与塔的那对引理同时服务于消去与引入。
<!--ja-->
本章は内部の階層を構成する。階層の順序数 `α` に対し、`hierL`{.Agda} の `α` での値は `L` の要素であり、その要素は「`α` の下の順序数 `β` と塔の値 `Lset β`」の順序対ちょうどである。一つのパターンが章全体で繰り返される。**表**とは順序対の集合であり、集合 `B` の下で記録する値がすべてメタレベルの塔のそこでの値であるとき、`B` の上で**正しい**と言い、その下のすべての入力で値を記録しているとき**完備**と言う。正しくて完備な表こそ、グラフのステップ条件が読むものであり、そこから書き下せるものでもある。だからステップと塔を結ぶ補題の組が、消去と導入の両方に仕える。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Classical using ( LEM )

module L.Hierarchy {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where
```

<!--en-->
The chapter runs at one excluded-middle instance, taken at the successor of the
model's own level; every construction below is stated inside this module and
carries that hypothesis only where an axiom chapter passed it on.
<!--zh-->
本章在模型自身层级的后继处取一份排中律实例并在其下运行；以下每个构造都陈述于本模块之内，只在公理章传递之处携带这一假设。
<!--ja-->
本章は、モデル自身のレベルの後続で排中律の実例を一つ取り、そのもとで進む。以下の構成はすべてこのモジュールの内部で述べられ、公理の章が渡す場所でだけこの仮定を帯ぶ。
<!--/-->

```agda
open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula )
import FOL.Absoluteness
import FOL.ZFModel
```

<!--en-->
Two structures are in play. The ambient hierarchy contributes its structure
`𝒮ᵥ`{.Agda}, whose membership induction and extensionality the chapter will
use; the constructible structure `𝒮ʟ`{.Agda} contributes the carrier `S`, whose
elements are sets of the hierarchy together with a proof that they are
constructible, so every carrier element `x` has an underlying set `fst x`.
<!--zh-->
这里有两个结构。环境层级贡献其结构 `𝒮ᵥ`{.Agda}，本章将使用它的隶属归纳与外延性；可构造结构 `𝒮ʟ`{.Agda} 贡献载体 `S`，其元素是层级中的集合连同「其可构造」的证明，故每个载体元素 `x` 都有底层集合 `fst x`。
<!--ja-->
ここでは二つの構造が現れる。周囲の階層はその構造 `𝒮ᵥ`{.Agda} を与え、本章はその所属の帰納と外延性を用いる。構成可能な構造 `𝒮ʟ`{.Agda} は台 `S` を与える。その要素は、階層の集合に「それが構成可能である」証明を添えたものであり、だから各台の要素 `x` には基礎の集合 `fst x` がある。
<!--/-->

```agda
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ; ∈-induction; extensionalV )
open import V.Coding {ℓ} using ( pr; pr-inj )
```

<!--en-->
From the hierarchy come three tools used throughout: induction along
membership, extensionality of sets, and the ordered pair `pr`{.Agda} with the
injectivity that recovers its components. The pair lives at the level of the
hierarchy, which is where the recorded entries of a table live too.
<!--zh-->
层级给出全章使用的三件工具：沿隶属的归纳、集合的外延性，以及有序对 `pr`{.Agda} 连同找回其分量的单射性。这个对住在层级那一层，而表的被记录条目也住在那里。
<!--ja-->
階層は、章を通して使う三つの道具を与える。所属に沿う帰納、集合の外延性、そして順序対 `pr`{.Agda} と、その成分を取り戻す単射性である。この対は階層のレベルにあり、表の記録された項目も同じレベルにある。
<!--/-->

```agda
open import L.Constructible {ℓ}
  using ( 𝒮ʟ; isL; isL-trans; 𝒟ₒ; Lset; Lset-in; Lset-out; IsOrd )
```

<!--en-->
From the constructible side come the tower `Lset`{.Agda}, which sends an
ordinal of the hierarchy to the constructible stage at it; the definable
powerset `𝒟ₒ`{.Agda}; the two membership readings `Lset-in`{.Agda} and
`Lset-out`{.Agda}; ordinality `IsOrd`{.Agda}; and the facts that
constructibility is carried along membership. The tower is indexed by
ordinals, which are sets of the hierarchy, never by universe levels, which are
size indices of types.
<!--zh-->
可构造一侧给出塔 `Lset`{.Agda}，它把层级的一个序数送到该处的可构造层；可定义幂集 `𝒟ₒ`{.Agda}；两条隶属读式 `Lset-in`{.Agda} 与 `Lset-out`{.Agda}；序数性 `IsOrd`{.Agda}；以及「可构造性沿隶属传递」这一事实。塔由序数索引，序数是层级的集合；从不由宇宙层级索引，后者是类型的大小指标。
<!--ja-->
構成可能の側からは、塔 `Lset`{.Agda} が来る。これは階層の順序数を、そこでの構成可能段階へ送る。ほかに、定義可能冪集合 `𝒟ₒ`{.Agda}、二つの所属の読み `Lset-in`{.Agda} と `Lset-out`{.Agda}、順序数性 `IsOrd`{.Agda}、そして「構成可能性が所属に沿って伝わる」事実である。塔の添字は順序数、すなわち階層の集合であり、型の大きさの添字である宇宙レベルでは決してない。
<!--/-->

```agda
open import L.Ordinal {ℓ} using ( mem-ord )
open import L.Axioms.Basic {ℓ} using ( LsetS; isL-𝒟ₒ )
open import L.Axioms.Full {ℓ} lem using ( hasReplacementL )
open import L.Recursion {ℓ} lem using ( mereFunct )
```

<!--en-->
Three further facts carry the chapter: a member of an ordinal is an ordinal;
a stage can be presented as an element of `L`, written `LsetS`{.Agda}, and the
definable powerset of a constructible set is constructible; and replacement is
available inside `L`, in a form that accepts a value known only to exist
uniquely.
<!--zh-->
另有三件事实支撑全章：序数的成员是序数；一个层可以呈现为 `L` 的元素，记作 `LsetS`{.Agda}，且可构造集合的可定义幂集仍可构造；以及 `L` 内部可用替换，其形式接受「仅知唯一存在」的取值。
<!--ja-->
さらに三つの事実が章を支える。順序数の要素は順序数であること。段階は `L` の要素として提示でき、それを `LsetS`{.Agda} と書き、構成可能集合の定義可能冪集合はまた構成可能であること。そして `L` の内部では置換が使え、その形は「一意に存在するとだけ分かっている値」を受け入れるものである。
<!--/-->

<!--en-->
The model contributes its own ordered pair `prʟ`{.Agda}, with the reading
`prʟ-fst`{.Agda} that identifies its first projection, and the domain clause
`domAt-intro`{.Agda}.
<!--zh-->
模型贡献它自己的有序对 `prʟ`{.Agda}，连同识别其第一投影的读式 `prʟ-fst`{.Agda}，以及定义域子句 `domAt-intro`{.Agda}。
<!--ja-->
モデルは自分自身の順序対 `prʟ`{.Agda} と、その第一射影を同定する読み `prʟ-fst`{.Agda}、そして定義域の条項 `domAt-intro`{.Agda} を与える。
<!--/-->

```agda
open import L.Coding.Model {ℓ} using ( prʟ; prʟ-fst; domAt-intro )
```

<!--en-->
The preceding coding chapter contributes the vocabulary this chapter
assembles: the step condition with its witness and three readings, the
approximation with its domain, value and step clauses, the tower graph with
its two readings, and the pair graph.
<!--zh-->
前一编码章贡献本章要组装的词汇：带见证与三条读式的步进条件，带定义域、取值与步进子句的逼近，有两条读式的塔之图，以及有序对图。
<!--ja-->
一つ前の符号化の章は、本章が組み立てる語彙を供給する。証人と三つの読みをもつステップ条件、定義域・値・ステップの条項をもつ近似、二つの読みをもつ塔のグラフ、そして順序対のグラフである。
<!--/-->

```agda
open import L.Coding.HierarchySequence {ℓ} lem
  using ( StepAt; StepOf; PowOK; StepAt-in; StepAt-out; StepAt-back
        ; ApproxAt; ApproxAt-dom; ApproxAt-value; ApproxAt-step; ApproxAt-in
        ; LsetGraphAt; LsetGraph-in; LsetGraph-out; GraphOf
        ; PairGraphAt; PairOf; PairGraph-in; PairGraph-out )
```



<!--en-->
The propositional machinery is the usual one: truncated existence, its
injection and elimination, the fact that a pair with a propositional second
component is equal when its first components are, and the conversion of a
pointwise equivalence of memberships into a path of sets.
<!--zh-->
命题机制是常用的那一套：截断的存在、其注入与消去、「第二分量为命题的序对在第一分量相等时即相等」，以及把隶属的逐点等价转成集合路径的操作。
<!--ja-->
命題の機構はいつものものである。切り詰められた存在、その注入と消去、第二成分が命題である対が第一成分の等しさで等しくなること、そして所属の各点での同値を集合のパスへ変える操作である。
<!--/-->





<!--en-->
The hierarchy itself appears as a type: its elements are the sets the chapter
tabulates, its membership is the relation the three conditions speak about,
and its h-setness makes equality of two tabulated sets a proposition.
<!--zh-->
层级自身以类型的身份出现：其元素正是本章制表的对象，其隶属是三个条件所谈论的关系，而其 h-集合性使两个被制表集合的相等成为命题。
<!--ja-->
階層そのものが型として現れる。その要素は本章が表にする集合であり、その所属は三つの条件が語る関係であり、その h-集合性により、表にされた二つの集合の等しさは命題になる。
<!--/-->

```agda
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_; setIsSet )
```



<!--en-->
Inside the constructible structure, `S` is the carrier and `⊨`{.Agda} the
satisfaction judgment; `SetOf`{.Agda} pairs a candidate set with the assertion
that it realizes a class, the form in which the record's fields state their
axioms.
<!--zh-->
在可构造结构内部，`S` 是载体，`⊨`{.Agda} 是满足判断；`SetOf`{.Agda} 把候选集合与「它实现一个类」的断言配成对，record 的各字段正是以这种形式陈述其公理。
<!--ja-->
構成可能な構造の内側では、`S` が台であり、`⊨`{.Agda} が充足の判断である。`SetOf`{.Agda} は候補の集合と「それがクラスを実現する」という主張を組にする。record のフィールドが公理を述べるのはこの形である。
<!--/-->

```agda
open hPropStructure 𝒮ʟ

module ModelL = FOL.ZFModel 𝒮ʟ
open ModelL using ( SetOf )
```



<!--en-->
Satisfaction is finally read at the constructible structure: the notation
`γ ⊨ φ`{.Agda} throughout the chapter judges object-language formulas at
environments of carrier elements, with constants drawn from `L`.
<!--zh-->
满足关系最终在可构造结构处读取：全章的记号 `γ ⊨ φ`{.Agda} 都是在载体元素的环境处、以取自 `L` 的常元判断对象语言公式。
<!--ja-->
充足は最後に、構成可能な構造で読まれる。章を通しての記法 `γ ⊨ φ`{.Agda} は、`L` から取った定数をもつ論理式を、台の要素の環境で判定する。
<!--/-->

```agda
module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL renaming ( _⊨ᵐ_ to _⊨_ )
```



<!--en-->
One private helper shifts variable slots by two: when a step is read in an
environment extended by a value and then an argument, every old slot moves two
places back. It appears whenever the step of a table is judged from inside its
own entry.
<!--zh-->
一个私有辅助把变元槽后移两位：当一步要在「先加取值、再加实参」而扩展的环境中判读时，所有旧槽都后移两位。凡从表自身的条目内部判读该表的步进时，它都会出现。
<!--ja-->
一つの private な補助は、変数の枠を二つ後ろへずらす。値を一つ、次に入力を一つ追加した環境の中でステップを判定するとき、古い枠はみな二つ後ろへ移る。表自身の項目の内側からそのステップを判定する場面で、いつも現れる。
<!--/-->

```agda
private
  sh2 : ∀ {n} → Fin n → Fin (suc (suc n))
  sh2 i = suc (suc i)
```



<!--en-->
## What a table records

A **table** is a set of ordered pairs, here always pairs taken with the
hierarchy's pairing: an argument together with a value. Three conditions
describe a table over a bound set `B`, and they are complementary rather than
three readings of one statement. `Values`{.Agda} requires every value recorded
below `B` to be the tower's value there. `Entries`{.Agda} requires the
canonical entry to be recorded at every argument below `B`. `Domain`{.Agda}
requires that nothing outside `B` is recorded at all.
<!--zh-->
## 表记录什么

**表**是有序对之集，这里总是取层级配对所成的对：一个实参连同一个取值。三个条件刻画表在界集 `B` 上的样子，它们是互补的条件，而不是同一句陈述的三种读法。`Values`{.Agda} 要求：在 `B` 以下记录的每个取值都是塔在那里的取值。`Entries`{.Agda} 要求：`B` 以下的每个实参处都记录了正準条目。`Domain`{.Agda} 要求：`B` 以外的东西完全没有被记录。
<!--ja-->
## 表が記録するもの

**表**とは順序対の集合であり、ここではつねに階層の対で取った対、すなわち入力と値の組である。界集合 `B` の上での表を三つの条件が特徴づける。それらは補い合う条件であって、一つの主張の三つの読みではない。`Values`{.Agda} は、`B` の下で記録された値がすべて塔のそこでの値であることを要求する。`Entries`{.Agda} は、`B` の下のすべての入力で正準な項目が記録されていることを要求する。`Domain`{.Agda} は、`B` の外が何も記録されていないことを要求する。
<!--/-->

```agda
Values : S → V ℓ → Type (ℓ-suc ℓ)
Values h B = (c z : S) → ⟨ fst c ∈ B ⟩
           → ⟨ pr (fst c) (fst z) ∈ fst h ⟩ → fst z ≡ Lset (fst c)
```

<!--en-->
Correctness is a statement about recorded entries. If the pair of an argument
`c` below `B` with some `z` is an entry of the table, then `z` is the tower at
`c`. The membership `fst c ∈ B` is membership in the hierarchy, `B` being a set
of the hierarchy; the table `h` is a carrier element, and `fst h` is the set it
presents.
<!--zh-->
正确性是关于被记录条目的陈述。若「`B` 以下的实参 `c` 与某个 `z` 组成的对」是表的一条目，则 `z` 就是塔在 `c` 处的取值。隶属 `fst c ∈ B` 是层级中的隶属，因为 `B` 是层级的集合；表 `h` 是载体元素，`fst h` 是它呈现的那个集合。
<!--ja-->
正しさは、記録された項目についての主張である。`B` の下の入力 `c` とある `z` の対が表の項目なら、`z` は塔の `c` での値である。所属 `fst c ∈ B` は階層での所属である。`B` が階層の集合だからである。表 `h` は台の要素であり、`fst h` がそれが提示する集合である。
<!--/-->

```agda
Entries : S → V ℓ → Type (ℓ-suc ℓ)
Entries h B = (c : S) → ⟨ fst c ∈ B ⟩ → ⟨ pr (fst c) (Lset (fst c)) ∈ fst h ⟩
```

<!--en-->
Completeness is the mirror requirement on coverage: at each argument `c` below
`B`, the canonical entry, the pair of `c` with the tower's value `Lset c`, is
recorded. Between the two conditions, a correct and complete table records,
below `B`, exactly the canonical entries and nothing distorted.
<!--zh-->
完备性是关于覆盖范围的镜像要求：在 `B` 以下的每个实参 `c` 处，典范条目，即 `c` 与塔值 `Lset c` 组成的对，都被记录。两个条件合起来，正确且完备的表在 `B` 以下记录的恰是那些典范条目，没有任何走样。
<!--ja-->
完備さは、覆いについての鏡像の要求である。`B` の下の各入力 `c` で、正準な項目、すなわち `c` と塔の値 `Lset c` の対が記録される。二つの条件から、正しくて完備な表は `B` の下で正準な項目ちょうどを記録し、歪んだものを一切含まないことが分かる。
<!--/-->

```agda
Domain : S → V ℓ → Type (ℓ-suc ℓ)
Domain h B = (c z : S) → ⟨ pr (fst c) (fst z) ∈ fst h ⟩ → ⟨ fst c ∈ B ⟩
```

<!--en-->
The conditions are kept apart because the applications need different subsets
of them. The induction over an approximation uses the first two and cannot use
the third: an approximation's entries lie below its own domain, not below the
argument the induction stands at. The internal hierarchy will satisfy all
three, being built as exactly the set of the right pairs. Note also what `B`
is: the underlying bound set, a set of the hierarchy. In the semantic
applications it arrives at a slot of the environment, as the underlying part of
a carrier element that carries constructibility besides, and the ordinality of
`B` is a separate hypothesis the conditions do not supply. The stages indexed
here are sets of the hierarchy, indexed by ordinals; the universe levels of the
host never enter the tabulation.
<!--zh-->
这些条件分开保留，因为各应用所需的子集不同。对逼近的归纳只用前两条，且用不了第三条：逼近的诸条目落在它自己的定义域以下，而不落在归纳所处的那个实参以下。内部层级将三条全有，因为它就是按「恰好是那些对的集合」构造的。还要注意 `B` 是什么：它是底层界集，层级中的一个集合。在语义应用中，它经由环境的某个槽位到来，是载体元素的底层部分，而该载体元素另外携带可构造性；`B` 的序数性是一条独立的假设，不由这些条件供给。此处制表的层是层级的集合、由序数索引；宿主的宇宙层级从不进入制表。
<!--ja-->
条件を分けておくのは、応用ごとに必要な部分が異なるからである。近似についての帰納は最初の二つを使い、三つ目は使えない。近似の項目はそれ自身の定義域の下に落ちるのであって、帰納が立っている入力の下ではないからである。内部の階層は三つすべてを満たす。正しい対ちょうどの集合として作られるからである。`B` が何であるかにも注意してほしい。基礎の界集合、すなわち階層の集合である。意味論的な応用では、環境の枠を通して届き、台の要素の基礎の部分として現れる。その台の要素はさらに構成可能性を帯びており、`B` の順序数性はこれらの条件が供給しない独立の仮定である。ここで表にされる段階は階層の集合で、順序数で添字づけられる。ホストの宇宙レベルが表に現れることはない。
<!--/-->

<!--en-->
## The step, against the tower

This section connects the step condition of the previous chapter with the
tower. The step at an argument `b` collects, over the arguments `c` below `b`
and the values `w` recorded there, the members of the definable powerset of
`w`. The tower at `b` collects the same members, with `Lset c` in place of the
recorded `w`. Three private facts prepare the comparison: `ok` discharges the
side condition `PowOK`{.Agda}, `below` turns a decomposition of the tower into
a step witness, and `above` turns a step witness into a member of the tower.
<!--zh-->
## 与外部层级对照的步骤

本节把上一章的步进条件与塔连接起来。实参 `b` 处的步进，沿 `b` 以下的诸实参 `c` 与在其处记录的诸取值 `w`，收集 `w` 的可定义幂集的成员。塔在 `b` 处收集的成员与之相同，只是把被记录的 `w` 换成 `Lset c`。三个私有事实为对照做准备：`ok` 解除旁条件 `PowOK`{.Agda}，`below` 把塔的一次分解变成步进见证，`above` 把步进见证变成塔的成员。
<!--ja-->
## 外部の階層と照らすステップ

この節は、前章のステップ条件と塔を結ぶ。入力 `b` でのステップは、`b` の下の入力 `c` とそこで記録された値 `w` にわたって、`w` の定義可能冪集合の要素を集める。塔が `b` で集める要素は同じもので、記録された `w` を `Lset c` に置き換えたものである。三つの private な事実が比較の準備をする。`ok` は横条件 `PowOK`{.Agda} を清算し、`below` は塔の分解をステップの証人に変え、`above` はステップの証人を塔の要素に変える。
<!--/-->


<details open class="submodule-fold">
<summary class="submodule-fold-heading">
```agda
module _ {n : ℕ} (v b f : Fin n) (γ : S ^ n) where
```
</summary>
<div class="submodule-fold-content">

```agda
  private
```

<!--en-->
The three slots name the value, the argument, and the table, all read from one
environment `γ` of carrier elements.
<!--zh-->
三个槽位命名取值、实参与表，全部从同一环境 `γ` 的载体元素读出。
<!--ja-->
三つの枠は、値・入力・表を名指す。いずれも一つの環境 `γ` の台の要素から読まれる。
<!--/-->

```agda
    ok : IsOrd (fst (lookup b γ)) → Values (lookup f γ) (fst (lookup b γ))
       → PowOK b f γ
```

<!--en-->
The side condition is discharged once, for both directions. `PowOK`{.Agda}
asks that the definable powerset of every recorded value be an element of `L`;
a recorded value is the tower at an argument below `B`, that argument is an
ordinal because `B` is one, and the definable powerset of a stage indexed by an
ordinal is constructible. Correctness plus a single ordinality hypothesis is
all the step ever needs, and neither reading carries the condition in its
statement. The two directions are named apart because they are used apart.
Going up is the definable powerset of a recorded value sitting inside the tower
at `B`, which is `Lset-in`{.Agda}. Coming down is the tower's own decomposition,
`Lset-out`{.Agda}, followed by naming the ordinal it produces as an element of
the model, which transitivity of the class supplies.
<!--zh-->
旁条件被一次性解除，同时服务两个方向。`PowOK`{.Agda} 要求：每个被记录取值的可定义幂集是 `L` 的元素；而被记录取值是塔在 `B` 以下某个实参处的取值，该实参因 `B` 是序数而是序数，且以序数为索引的层，其可定义幂集可构造。故那一步所需的全部，就是正确性加上单独一条序数性假设，而两种读法的陈述里都不带该条件。两个方向分开命名，因为它们分开使用。向上是「被记录取值的可定义幂集落在 `B` 处的塔里面」，即 `Lset-in`{.Agda}。向下是塔自身的分解 `Lset-out`{.Agda}，随后把分解给出的序数记为模型的元素，这一步由类的传递性供给。
<!--ja-->
横条件は一度だけ清算され、両方向に働く。`PowOK`{.Agda} が要求するのは、記録されたそれぞれの値の定義可能冪集合が `L` の要素であることである。記録された値は塔の、`B` の下のある入力での値であり、その入力は `B` が順序数であるゆえに順序数であり、順序数で添字づけられた段階の定義可能冪集合は構成可能である。だからステップに必要なのは正しさと一つの順序数性の仮定だけで、二つの読み出しの主張にその条件は現れない。二つの方向が別々の名前を持つのは、別々に使われるからである。上向きは、記録された値の定義可能冪集合が `B` での塔の中に坐ることで、これが `Lset-in`{.Agda} である。下向きは塔そのものの分解 `Lset-out`{.Agda} であり、続いて、そこで現れる順序数をモデルの要素として名指す。これはクラスの推移性が与える。
<!--/-->

```agda
    ok ob vals c z rec = subst (λ u → ⟨ isL (𝒟ₒ u) ⟩)
      (sym (vals c z (rec .fst) (rec .snd)))
      (isL-𝒟ₒ (fst c) (mem-ord {A = fst (lookup b γ)} ob (fst c) (rec .fst)))
```

<!--en-->
The proof assembles the two hypotheses. The witness `rec` says `c` is below the
argument, so `c` is an ordinal by the ordinality of the argument; correctness
identifies the recorded value with the tower at `c`; and the definable
powerset of a constructible stage is constructible, which is `isL-𝒟ₒ`. The
transport lines the two facts up on the same value.
<!--zh-->
证明把两条假设拼起来。见证 `rec` 说 `c` 在实参以下，于是由实参的序数性，`c` 是序数；正确性把被记录的取值同认于塔在 `c` 处的取值；而可构造层的可定义幂集可构造，这正是 `isL-𝒟ₒ`。两行 transport 把两条事实对齐到同一个取值上。
<!--ja-->
証明は二つの仮定を組み合わせる。証人 `rec` は `c` が入力の下にあると言い、それゆえ入力の順序数性から `c` は順序数である。正しさが記録された値を `c` での塔と同一視し、構成可能な段階の定義可能冪集合は構成可能、これが `isL-𝒟ₒ` である。二つの transport が、この二つの事実を同じ値の上に並べる。
<!--/-->

```agda
    below : IsOrd (fst (lookup b γ)) → Entries (lookup f γ) (fst (lookup b γ))
          → (z : S)
          → Σ[ δ ∈ V ℓ ] (⟨ δ ∈ fst (lookup b γ) ⟩ × ⟨ fst z ∈ 𝒟ₒ (Lset δ) ⟩)
          → StepOf b f γ z
```

<!--en-->
`below` turns a decomposition of the tower into a step witness. The tower at
`b` decomposes each member: a member `z` sits in the definable powerset of the
stage at some `δ` below `b`. The witness must name an argument below the
argument and a recorded value whose powerset contains `z`.
<!--zh-->
`below` 把塔的一次分解变成步进见证。塔在 `b` 处分解它的每个成员：成员 `z` 坐在某个 `δ` (`b` 以下) 处的层的可定义幂集里。见证须指名一个低于实参的实参，以及一个其幂集含有 `z` 的被记录取值。
<!--ja-->
`below` は塔の分解をステップの証人に変える。`b` での塔は各要素を分解する。要素 `z` は、`b` の下のある `δ` での段階の定義可能冪集合に坐っている。証人が名指すべきは、入力の下の入力と、その冪集合が `z` を含むような記録された値である。
<!--/-->

```agda
    below ob ents z (δ , (δ∈ , hz)) =
      d , (LsetS δ oδ , ((δ∈ , ents d δ∈) , hz))
```

<!--en-->
The witness is given at the argument `d`, the carrier element of `δ`, where
the table records the canonical entry by completeness. The recorded value
there is the stage at `δ`, presented as an element of `L`, and `z` lies in its
definable powerset by the decomposition.
<!--zh-->
见证在实参 `d`，即 `δ` 的载体元素处给出：由完备性，表在该处记录典范条目。那里的被记录取值是 `δ` 处的层 (呈现为 `L` 的元素)，而由分解，`z` 落在其可定义幂集中。
<!--ja-->
証人は、`δ` の台の要素である入力 `d` で与えられる。完備さにより、表はそこで正準な項目を記録する。そこの記録された値は `δ` での段階 (`L` の要素として提示されたもの) であり、分解によって `z` はその定義可能冪集合に属する。
<!--/-->

```agda
      where
      oδ : IsOrd δ
      oδ = mem-ord {A = fst (lookup b γ)} ob δ δ∈
      d : S
      d = δ , isL-trans {x = fst (lookup b γ)} {y = δ} δ∈ (lookup b γ .snd)
```

<!--en-->
Two bookkeeping facts complete the construction. The ordinality of `δ`
follows from that of `b`, members of ordinals being ordinals; and `δ` is
constructible because it belongs to the constructible set underlying the
argument. The carrier element `d` packages the set with that certificate.
<!--zh-->
两个簿记事实完成构造。`δ` 的序数性由 `b` 的序数性而来，因为序数的成员是序数；`δ` 可构造，因为它属于实参底层那个可构造集合。载体元素 `d` 把集合与这份证书打包在一起。
<!--ja-->
二つの簿記の事実が構成を完成させる。`δ` の順序数性は `b` の順序数性から従う。順序数の要素は順序数だからである。そして `δ` は構成可能である。入力の基礎にある構成可能集合に属するからである。台の要素 `d` は、集合とこの証明書をひとまとめにする。
<!--/-->

```agda
    above : Values (lookup f γ) (fst (lookup b γ)) → (z : S) → StepOf b f γ z
          → ⟨ fst z ∈ Lset (fst (lookup b γ)) ⟩
```

<!--en-->
`above` is the mirror: a step witness places a member into the tower. The
witness names an argument `c` below the argument, a recorded value `w` there,
and a membership of `z` in the definable powerset of `w`.
<!--zh-->
`above` 是镜像：步进见证把一个成员放进塔里。见证指名低于实参的实参 `c`、其处被记录的取值 `w`，以及 `z` 属于 `w` 之可定义幂集的成员资格。
<!--ja-->
`above` は鏡像である。ステップの証人が要素を塔の中へ置く。証人が名指すのは、入力の下の入力 `c`、そこで記録された値 `w`、そして `z` が `w` の定義可能冪集合に属することである。
<!--/-->

```agda
    above vals z (c , (w , (rec , hz))) =
      Lset-in (fst (lookup b γ)) (fst c) (fst z) (rec .fst)
        (subst (λ u → ⟨ fst z ∈ 𝒟ₒ u ⟩) (vals c w (rec .fst) (rec .snd)) hz)
```

<!--en-->
Correctness identifies the recorded `w` with the tower at `c`, so `z` lies in
the definable powerset of that stage; the upward reading of the tower then
places `z` inside the tower at `b`, using the ordinality of `c` carried by the
witness.
<!--zh-->
正确性把被记录的 `w` 同认于塔在 `c` 处的取值，于是 `z` 落在那个层的可定义幂集中；再由塔的向上读式，借助见证所携带的 `c` 之序数性，把 `z` 放进 `b` 处的塔里。
<!--ja-->
正しさが記録された `w` を `c` での塔と同一視するので、`z` はその段階の定義可能冪集合に属する。さらに塔の上向きの読みが、証人が携える `c` の順序数性を使って、`z` を `b` での塔の中へ置く。
<!--/-->

```agda
  step-Lset : ⟨ γ ⊨ StepAt v b f ⟩ → IsOrd (fst (lookup b γ))
            → Values (lookup f γ) (fst (lookup b γ))
            → Entries (lookup f γ) (fst (lookup b γ))
            → fst (lookup v γ) ≡ Lset (fst (lookup b γ))
```

<!--en-->
The upward lemma reads: if the step condition is satisfied at the environment,
if the argument is an ordinal, and if the table is correct and complete on it,
then the value recorded at the value slot is the tower at the argument.
<!--zh-->
向上引理读作：若步进条件在该环境处成立、实参是序数、且表在其上正确而完备，则在取值槽位记录的取值就是塔在实参处的取值。
<!--ja-->
上向きの補題はこう読む。ステップ条件が環境で成立し、入力が順序数であり、表がその上で正しくて完備なら、値の枠で記録された値は入力での塔に等しい、と。
<!--/-->

```agda
  step-Lset h ob vals ents =
    extensionalV {a = fst (lookup v γ)} {b = Lset (fst (lookup b γ))} pt
    where
```

<!--en-->
Two sets of the hierarchy with the same members are equal, and this is
extensionality of the ambient hierarchy. The proof exhibits the pointwise
equivalence `pt` and lets extensionality assemble the path.
<!--zh-->
层级中成员相同的两个集合相等，这是环境层级的外延性。证明给出逐点等价 `pt`，把路径的组装交给外延性。
<!--ja-->
階層の、同じ要素をもつ二つの集合は等しく、これが周囲の階層の外延性である。証明は各点の同値 `pt` を示し、パスの組み立てを外延性に任せる。
<!--/-->

```agda
    fwd : (x : V ℓ) → ⟨ x ∈ fst (lookup v γ) ⟩
        → ⟨ x ∈ Lset (fst (lookup b γ)) ⟩
    fwd x hx = rec₁ (snd (x ∈ Lset (fst (lookup b γ)))) (above vals z)
      (StepAt-out v b f γ h (ok ob vals) z hx)
```

<!--en-->
The forward direction: a member `x` of the recorded value yields a step
witness, because the step condition is satisfied; the witness is eliminated
into the proposition that `x` belongs to the tower, and `above` proves that
proposition from the witness.
<!--zh-->
向前方向：被记录取值的成员 `x` 给出一个步进见证，因为步进条件成立；该见证被消去到「`x` 属于塔」这条命题中，而 `above` 由见证证明这条命题。
<!--ja-->
前向き：記録された値の要素 `x` は、ステップ条件が成立しているのでステップの証人を与える。証人は「`x` が塔に属する」という命題へ消去され、`above` が証人からその命題を証明する。
<!--/-->

```agda
      where
      z : S
      z = x , isL-trans {x = fst (lookup v γ)} {y = x} hx (lookup v γ .snd)
```

<!--en-->
To apply `above`, `x` is needed as a carrier element; its constructibility
follows from that of the recorded value, since `x` is a member of it.
<!--zh-->
要应用 `above`，须把 `x` 视为载体元素；其可构造性由被记录取值的可构造性而来，因为 `x` 是它的成员。
<!--ja-->
`above` を適用するには、`x` を台の要素として必要とする。その構成可能性は、記録された値の構成可能性から従う。`x` はその要素だからである。
<!--/-->

```agda
    bwd : (x : V ℓ) → ⟨ x ∈ Lset (fst (lookup b γ)) ⟩
        → ⟨ x ∈ fst (lookup v γ) ⟩
    bwd x hx = rec₁ (snd (x ∈ fst (lookup v γ))) put
      (Lset-out (fst (lookup b γ)) x hx)
```

<!--en-->
The backward direction: the tower decomposes each member `x`, exhibiting a
stage below the argument whose definable powerset contains it. The
decomposition is eliminated into the proposition that `x` belongs to the
recorded value.
<!--zh-->
向后方向：塔分解它的每个成员 `x`，给出低于实参的一个层，其可定义幂集含有 `x`。该分解被消去到「`x` 属于被记录取值」这条命题中。
<!--ja-->
後ろ向き：塔は各要素 `x` を分解し、その定義可能冪集合が `x` を含むような、入力の下の段階を示す。分解は「`x` が記録された値に属する」という命題へ消去される。
<!--/-->

```agda
      where
      z : S
      z = x , isL-trans {x = Lset (fst (lookup b γ))} {y = x} hx
                (LsetS (fst (lookup b γ)) ob .snd)
```

<!--en-->
Again `x` must be carried: its constructibility follows from belonging to the
stage at the argument, whose element-of-`L` presentation is `LsetS` at the
ordinality `ob`.
<!--zh-->
这里同样要把 `x` 载入：其可构造性由属于实参处的层而来，而该层的 `L` 元素呈现正是取序数性 `ob` 的 `LsetS`。
<!--ja-->
ここでも `x` を台に載せる必要がある。その構成可能性は、入力での段階への所属から従う。その段階の `L` 要素としての提示が、順序数性 `ob` を取った `LsetS` である。
<!--/-->

```agda
      put : Σ[ δ ∈ V ℓ ] (⟨ δ ∈ fst (lookup b γ) ⟩ × ⟨ x ∈ 𝒟ₒ (Lset δ) ⟩)
          → ⟨ x ∈ fst (lookup v γ) ⟩
      put s = StepAt-back v b f γ h (ok ob vals) z (below ob ents z s)
```

<!--en-->
The decomposition is converted into a step witness by `below`, and the
backward reading of the step condition, `StepAt-back`, turns the witness into
membership in the recorded value.
<!--zh-->
分解经 `below` 变成步进见证，而步进条件的向后读式 `StepAt-back` 把见证变成对被记录取值的隶属。
<!--ja-->
分解は `below` によってステップの証人に変えられ、ステップ条件の後ろ向きの読み `StepAt-back` が、証人を記録された値への所属に変える。
<!--/-->

```agda
    pt : (x : V ℓ) → (x ∈ fst (lookup v γ)) ≡ (x ∈ Lset (fst (lookup b γ)))
    pt x = ⇔toPath (fwd x) (bwd x)
```

<!--en-->
For each member, membership in the recorded value and membership in the tower
are the same proposition; the two directions give the equivalence, and
extensionality promotes it member by member to the equality of sets.
<!--zh-->
对每个成员而言，属于被记录取值与属于塔是同一命题；两个方向给出等价，外延性再逐成员把它提升为集合的相等。
<!--ja-->
各要素について、記録された値への所属と塔への所属は同じ命題である。二つの方向が同値を与え、外延性がそれを要素ごとに集合の等しさへ引き上げる。
<!--/-->

```agda
  step-table : IsOrd (fst (lookup b γ))
             → Values (lookup f γ) (fst (lookup b γ))
             → Entries (lookup f γ) (fst (lookup b γ))
             → fst (lookup v γ) ≡ Lset (fst (lookup b γ))
             → ⟨ γ ⊨ StepAt v b f ⟩
```

<!--en-->
The downward lemma reverses the traffic: given the ordinality of the argument,
correctness, completeness, and the fact that the recorded value is the tower,
the step condition is satisfied.
<!--zh-->
向下引理把方向反过来：给定实参的序数性、正确性、完备性，以及「被记录取值就是塔」这一事实，步进条件即告成立。
<!--ja-->
下向きの補題は流れを逆にする。入力の順序数性、正しさ、完備さ、そして記録された値が塔であるという事実が与えられれば、ステップ条件は成立する。
<!--/-->

```agda
  step-table ob vals ents q = StepAt-in v b f γ (ok ob vals) into back
    where
```

<!--en-->
The step condition is introduced from its two directions, existence of a
witness for each member and soundness of every witness, with `ok` supplying
the side condition once for both.
<!--zh-->
步进条件由它的两个方向引入：每个成员都有见证，且每个见证都可靠；旁条件由 `ok` 一并供给。
<!--ja-->
ステップ条件は、その二方向から導入される。各要素への証人の存在と、すべての証人の健全性である。横条件は `ok` が両方のために一度に供給する。
<!--/-->

```agda
    into : (z : S) → ⟨ fst z ∈ fst (lookup v γ) ⟩ → ∥ StepOf b f γ z ∥₁
    into z hz = map₁ (below ob ents z)
      (Lset-out (fst (lookup b γ)) (fst z)
        (subst (λ u → ⟨ fst z ∈ u ⟩) q hz))
```

<!--en-->
A member `z` of the recorded value is first transported into the tower along
the identification `q`, then decomposed by the tower, and `below` converts the
decomposition into a witness, which only has to exist.
<!--zh-->
被记录取值的成员 `z` 先沿同认 `q` 运入塔中，再由塔分解，而 `below` 把分解变成见证；见证只需存在即可。
<!--ja-->
記録された値の要素 `z` は、まず同定 `q` に沿って塔へ運ばれ、塔によって分解される。`below` がその分解を証人に変える。証人は存在すれば十分である。
<!--/-->

```agda
    back : (z : S) → StepOf b f γ z → ⟨ fst z ∈ fst (lookup v γ) ⟩
    back z s = subst (λ u → ⟨ fst z ∈ u ⟩) (sym q) (above vals z s)
```
</div>
</details>


<!--en-->
Conversely, a witness places `z` into the tower by `above`, and the
transportation runs the other way along `q`.
<!--zh-->
反过来，见证经 `above` 把 `z` 放进塔里，而运输沿 `q` 反向进行。
<!--ja-->
逆に、証人は `above` によって `z` を塔の中に置き、輸送は `q` に沿って逆向きに走る。
<!--/-->

<!--en-->
## Every value an approximation records

One induction, on the argument, in the meta-language, with the approximation and
its domain held fixed. The motive says: whatever value the approximation records
at this argument is the meta tower there. The motive quantifies over **all**
recorded values, and that is why single-valuedness is nowhere a hypothesis. Two
values recorded at one argument are both pinned to the same tower value, so they
are equal; the uniqueness of recorded values is read off the induction rather
than assumed.
<!--zh-->
## 逼近所记录的每个值

一次归纳，在实参上，在元语言中，逼近与它的定义域保持固定。动机说：逼近在这个实参处所记录的任何取值，都是元层面的塔在那里的取值。动机对**一切**被记录的取值作量化，而这正是单值性在任何地方都不作为假设的原因。在同一个实参处记录的两个取值都被钉在同一个塔值上，故两者相等；被记录取值的唯一性由归纳读出，而非假设。
<!--ja-->
## 近似が記録するすべての値

帰納は一回、入力の上で、メタ言語の中で行われる。近似とその定義域は固定したままである。動機はこう言う。近似がこの入力で記録するどんな値も、メタレベルの塔のそこでの値に等しい、と。動機は記録された**すべての**値を量化する。だから一価性がどこにも仮定として現れないのである。同じ入力で記録された二つの値は、どちらも同じ塔の値に釘づけになり、等しくなる。記録された値の一意性は、仮定ではなく帰納から読み出される。
<!--/-->

<!--en-->
The step of the induction is `step-Lset`{.Agda} at the recorded value.
Correctness below the argument *is* the induction hypothesis, verbatim.
Completeness below the argument is where the approximation's value clause is
spent: an argument below this one is below the approximation's domain, because
the domain is an ordinal and ordinals are transitive; the approximation
therefore has a value there; and the induction hypothesis identifies it with the
tower's. That value is produced only merely, which is enough, because what is
being proved of it is a membership.
<!--zh-->
归纳的步进就是 `step-Lset`{.Agda} 施于被记录的那个取值。实参以下的正确性**就是**归纳假设，一字不差。实参以下的完备性则是逼近的取值子句被花掉之处：比这个实参更低的实参落在逼近的定义域以下，因为定义域是序数、而序数传递；逼近于是在那里有取值；而归纳假设把它与塔的取值认同。那个取值只是「仅仅」被拿出来的，而这已经够了，因为要对它证的是一条隶属关系。
<!--ja-->
帰納のステップは、記録された値に対する `step-Lset`{.Agda} である。入力の下での正しさは、そのまま逐語的に帰納の仮定である。入力の下での完備さを使うのが、近似の値の条項を費やす場所である。この入力より下の入力は近似の定義域の下にもある。定義域は順序数であり、順序数は推移的だからである。だから近似はそこで値を持ち、帰納の仮定がそれを塔の値と同一視する。その値は「単に」取り出されるだけで十分である。それについて証明するのは一つの所属だからである。
<!--/-->


<details open class="submodule-fold">
<summary class="submodule-fold-heading">
```agda
module _ {n : ℕ} (f a : Fin n) (γ : S ^ n) where
```
</summary>
<div class="submodule-fold-content">

```agda
  private
    Value : V ℓ → Type (ℓ-suc ℓ)
    Value u = ⟨ isL u ⟩ → (z : S)
            → ⟨ pr u (fst z) ∈ fst (lookup f γ) ⟩ → fst z ≡ Lset u
```

<!--en-->
The motive `Value u` says: for a constructible `u`, every entry of the table
whose first component is `u` records the tower at `u`. The hypothesis that `u`
is constructible is carried because the table's entries are carrier elements,
whose first components are constructible sets; the induction will supply it
from membership in an ordinal.
<!--zh-->
动机 `Value u` 说：对可构造的 `u`，表中第一分量为 `u` 的每条记录都记录塔在 `u` 处的取值。「`u` 可构造」这一前提之所以被携带，是因为表的条目是载体元素，其第一分量是可构造集合；归纳将从某个序数中的隶属供给这一前提。
<!--ja-->
動機 `Value u` はこう言う。構成可能な `u` に対し、表の、第一成分が `u` である項目はすべて、塔の `u` での値を記録している、と。「`u` が構成可能」という前提が帯びられるのは、表の項目が台の要素で、その第一成分が構成可能集合だからである。帰納は、順序数への所属からこの前提を供給する。
<!--/-->

```agda
  approx-val : ⟨ γ ⊨ ApproxAt f a ⟩ → IsOrd (fst (lookup a γ))
             → (x z : S) → ⟨ pr (fst x) (fst z) ∈ fst (lookup f γ) ⟩
             → fst z ≡ Lset (fst x)
  approx-val h oa x = ∈-induction {P = Value} go (fst x) (snd x)
```

<!--en-->
The theorem runs the induction on the underlying set of `x`, the argument whose
recorded value is in question. Membership induction is available in the
hierarchy directly: to prove the motive of `u`, prove it of every member of
`u`. The ordinality hypothesis on `a` is consumed inside the induction step.
<!--zh-->
定理对 `x` 的底层集合作归纳，`x` 正是所问其被记录取值的那个实参。隶属归纳在层级中直接可用：要证 `u` 的动机，就证 `u` 的每个成员的动机。关于 `a` 的序数性假设将在归纳步内被消耗。
<!--ja-->
定理は、`x` の基礎の集合の上で帰納を実行する。`x` は、記録された値が問題になっている入力である。所属に沿う帰納は階層で直接使える。`u` の動機を証明するには、`u` のすべての要素の動機を証明する。`a` についての順序数性の仮定は、帰納のステップの内側で消費される。
<!--/-->

```agda
    where
    go : (u : V ℓ) → ((t : V ℓ) → ⟨ t ∈ u ⟩ → Value t) → Value u
    go u IH hu z p = step-Lset zero (suc zero) (sh2 f) (z ∷ d ∷ γ)
      (ApproxAt-step f a γ h d z p) ou vals ents
```

<!--en-->
The induction step is `step-Lset` applied to the approximation's own step
clause. The step is read at the environment extended by the value `z` and the
argument `u`, so the three slots of the step shift back by two, which is what
`sh2` accounts for. The conclusion is exactly the motive: the recorded `z` is
the tower at `u`.
<!--zh-->
归纳步就是把 `step-Lset` 施于逼近自己的步进子句。这一步在「加入取值 `z`、再加入实参 `u`」的扩展环境处判读，因此步进的三个槽位后移两位，这正是 `sh2` 所做的事。结论恰是动机：被记录的 `z` 就是塔在 `u` 处的取值。
<!--ja-->
帰納のステップは、近似自身のステップ条項に `step-Lset` を適用することである。ステップは、値 `z` と入力 `u` を追加した環境で判定されるので、ステップの三つの枠は二つ後ろへずれる。これが `sh2` の仕事である。結論はそのまま動機である。記録された `z` は `u` での塔である。
<!--/-->

```agda
      where
      d : S
      d = u , hu
      u∈a : ⟨ u ∈ fst (lookup a γ) ⟩
      u∈a = ApproxAt-dom f a γ h d z p
```

<!--en-->
The value and the argument travel as carrier elements: `d` packages `u` with
the constructibility `hu`. The approximation's domain clause certifies that
`u` is below the argument `a`, which is what lets the induction reach this
step at all.
<!--zh-->
取值与实参以载体元素的身份旅行：`d` 把 `u` 与可构造性 `hu` 打包。逼近的定义域子句证明 `u` 低于实参 `a`，归纳之所以能够到达这一步，全凭于此。
<!--ja-->
値と入力は、台の要素として旅をする。`d` は `u` に構成可能性 `hu` を包んでいる。近似の定義域の条項が、`u` が入力 `a` の下にあることを証明する。帰納がこのステップに届くのは、これがあればこそである。
<!--/-->

```agda
      ou : IsOrd u
      ou = mem-ord {A = fst (lookup a γ)} oa u u∈a
```

<!--en-->
Ordinality of `u` follows from ordinality of `a`, since `u` is a member of
`a`; this is what the step will need about the argument it stands at.
<!--zh-->
`u` 的序数性由 `a` 的序数性而来，因为 `u` 是 `a` 的成员；这正是该步所需要的关于其所处实参的全部。
<!--ja-->
`u` の順序数性は `a` の順序数性から従う。`u` は `a` の要素だからである。ステップがその立つ入力について必要とするのは、これである。
<!--/-->

```agda
      vals : Values (lookup f γ) u
      vals c y c∈ q = IH (fst c) c∈ (snd c) y q
```

<!--en-->
Correctness below `u` is the induction hypothesis, used exactly as stated: for
a member `c` of `u`, a recorded pair with first component `c` records the
tower at `c`. The constructibility of `c` arrives with the induction, which
supplies it from membership.
<!--zh-->
`u` 以下的正确性就是归纳假设，按原样使用：对 `u` 的成员 `c`，第一分量为 `c` 的被记录对所记录的是塔在 `c` 处的取值。`c` 的可构造性随归纳而来，归纳由隶属供给它。
<!--ja-->
`u` の下での正しさは、そのまま逐語的に帰納の仮定である。`u` の要素 `c` に対し、第一成分が `c` である記録された対は、`c` での塔を記録する。`c` の構成可能性は帰納とともに届く。帰納が所属からそれを供給するからである。
<!--/-->

```agda
      ents : Entries (lookup f γ) u
      ents c c∈ = rec₁
        (snd (pr (fst c) (Lset (fst c)) ∈ fst (lookup f γ))) named
        (ApproxAt-value f a γ h c (oa .fst {x = u} {y = fst c} c∈ u∈a))
```

<!--en-->
Completeness below `u` is where the approximation's value clause is spent. For
`c` below `u`, transitivity inside the ordinal `a` gives `c` below `a`, and the
approximation records some value there; the entry merely exists, and the
elimination targets the proposition that the canonical entry is recorded.
<!--zh-->
`u` 以下的完备性是逼近的取值子句被花掉之处。对 `u` 以下的 `c`，序数 `a` 内部的传递性给出 `c` 低于 `a`，逼近在该处记录了某个取值；该条目只是「仅仅」存在，而消去的目标是「典范条目被记录」这条命题。
<!--ja-->
`u` の下での完備さは、近似の値の条項を費やす場所である。`u` の下の `c` に対し、順序数 `a` の中の推移性が `c` が `a` の下にあることを与え、近似はそこで何らかの値を記録する。項目は単に存在するだけでよく、消去の対象は「正準な項目が記録される」という命題である。
<!--/-->

```agda
        where
        named : Σ[ y ∈ S ] ⟨ pr (fst c) (fst y) ∈ fst (lookup f γ) ⟩
              → ⟨ pr (fst c) (Lset (fst c)) ∈ fst (lookup f γ) ⟩
        named (y , q) = subst (λ t → ⟨ pr (fst c) t ∈ fst (lookup f γ) ⟩)
          (IH (fst c) c∈ (snd c) y q) q
```
</div>
</details>


<!--en-->
The merely-given recorded value is identified with the tower by the induction
hypothesis, so after the transport the canonical entry is recorded, which is
what completeness asks.
<!--zh-->
那个仅仅给出的被记录取值，由归纳假设同认于塔；运输之后，被记录的恰是典范条目，这正是完备性所要求的。
<!--ja-->
単に与えられただけの記録された値は、帰納の仮定によって塔と同定される。輸送の後には、正準な項目が記録されている。完備さが求めるのはこれである。
<!--/-->

<!--en-->
## The graph holds of nothing else

The tower graph says that the value at a slot is the tower's value at the
argument, and it says this through an approximation: there merely is an
approximation whose step at the argument is that value. Unpacked, everything is
already in hand. Correctness below the argument comes from the induction just
completed; completeness below the argument comes from the approximation's value
clause, transported by the same induction; and `step-Lset`{.Agda} applied one
last time identifies the recorded value with the tower. The graph therefore
**determines** its value: whatever satisfies it at an ordinal is the meta tower
there.
<!--zh-->
## 图只对正确值成立

塔之图说：槽位处的取值就是塔在实参处的取值，而它经由一个逼近这样说：仅存在一个逼近，其在该实参处的步进正是那个取值。展开之后，所需的材料全部就位。实参以下的正确性来自刚完成的归纳；实参以下的完备性来自逼近的取值子句，经同一场归纳运输；最后再应用一次 `step-Lset`{.Agda}，就把被记录取值同认于塔。因此图**确定**它的取值：凡在某个序数处满足它的对象，都是元层面的塔在该处的取值。
<!--ja-->
## グラフは正しい値だけを認める

塔のグラフは、枠での値が入力での塔の値であると言う。そしてそれを、近似を通して言う。入力でのステップがその値であるような近似が、単に存在する、と。ほどけば、必要な材料はすべて手もとにある。入力の下での正しさは、今完了した帰納から来る。入力の下での完備さは、近似の値の条項から来て、同じ帰納によって運ばれる。最後にもう一度 `step-Lset`{.Agda} を適用すれば、記録された値は塔と同定される。ゆえにグラフはその値を**決定**する。順序数でそれを満たすものは何であれ、メタレベルの塔のそこでの値である。
<!--/-->

<!--en-->
The reading stands at variable slots, and that is not decoration. Its
instantiations live in different concrete environments, and a statement made in
one of them would have to be transported to the other through a satisfaction
carrying the whole tower description inside it.
<!--zh-->
这条读式以变元槽形式陈述，这并非装饰。它的各处实例化住在不同的具体环境中；若在某一处陈述，就得通过一个内部装着整条塔描述的满足关系，把它运到另一处。
<!--ja-->
この読みが変数の枠の上に立つのは飾りではない。実例化はそれぞれ異なる具体的な環境に住み、一方で述べた主張を他方へ運ぶには、全体の塔の記述を内側に抱えた充足を通さねばならない。
<!--/-->


<details open class="submodule-fold">
<summary class="submodule-fold-heading">
```agda
module _ {n : ℕ} (w b : Fin n) (γ : S ^ n) where
```
</summary>
<div class="submodule-fold-content">

```agda
  Lset-only : ⟨ γ ⊨ LsetGraphAt w b ⟩ → IsOrd (fst (lookup b γ))
            → fst (lookup w γ) ≡ Lset (fst (lookup b γ))
```

<!--en-->
The statement takes the satisfaction of the tower graph at the value and
argument slots, the ordinality of the argument, and concludes that the recorded
value is the tower. Nothing about the graph is assumed beyond its holding.
<!--zh-->
陈述取塔之图在取值槽与实参槽处的满足、实参的序数性，结论是被记录取值就是塔。除了图成立之外，不假设关于图的任何东西。
<!--ja-->
主張は、塔のグラフの値と入力の枠での充足と、入力の順序数性を受け取り、記録された値が塔であると結論する。グラフについて仮定するのは、それが成立することだけである。
<!--/-->

```agda
  Lset-only h ob = rec₁
    (setIsSet (fst (lookup w γ)) (Lset (fst (lookup b γ)))) read
    (LsetGraph-out w b γ h)
    where
```

<!--en-->
The graph unfolds to a mere witness: an approximation together with its
satisfaction and its step at the value. The elimination is legitimate because
the goal is an equality of two h-sets, hence a proposition; the witness itself
is only ever needed inside that proposition.
<!--zh-->
图展开为一个单纯见证：一个逼近，连同其满足与其在取值处的步进。消去是合法的，因为目标是两个 h-集合的相等，即一条命题；而见证本身也只在这条命题内部被需要。
<!--ja-->
グラフは、単なる証人へほどける。すなわち、近似と、その充足と、値でのステップである。消去が正当なのは、目標が二つの h-集合の等しさ、つまり命題だからである。証人そのものが必要になるのは、その命題の内側だけである。
<!--/-->

```agda
    read : GraphOf w b γ → fst (lookup w γ) ≡ Lset (fst (lookup b γ))
    read (f , (ha , hs)) =
      step-Lset (suc w) (suc b) zero (f ∷ γ) hs ob vals ents
```

<!--en-->
The witness hands over an approximation `f` on the argument, its satisfaction
`ha`, and its step `hs` at the value. The step lemma is applied in the
environment extended by `f`: the approximation occupies the new slot zero,
while the value and the argument have moved up one place each.
<!--zh-->
见证交出一个在实参上的逼近 `f`、其满足 `ha`、及其在取值处的步进 `hs`。步进引理在由 `f` 扩展的环境中施用：逼近占据新增的零号槽，取值与实参各上移一位。
<!--ja-->
証人が渡すのは、入力の上の近似 `f`、その充足 `ha`、そして値でのステップ `hs` である。ステップの補題は、`f` で拡張した環境で適用される。近似が新しく増えた枠ゼロを占め、値と入力は一つずつ後ろへ移る。
<!--/-->

```agda
      where
      vals : Values f (fst (lookup b γ))
      vals c z _ p = approx-val zero (suc b) (f ∷ γ) ha ob c z p
```

<!--en-->
Correctness for the step lemma is the induction of the previous section,
applied to the approximation `ha`: every value that `f` records below the
argument is the tower there.
<!--zh-->
步进引理所需的正确性，就是把上一节的归纳施于逼近 `ha`：`f` 在实参以下记录的每个取值都是塔在该处的取值。
<!--ja-->
ステップの補題にとっての正しさは、前節の帰納を近似 `ha` に適用したものである。`f` が入力の下で記録する値はすべて、塔のそこでの値である。
<!--/-->

```agda
      ents : Entries f (fst (lookup b γ))
      ents c c∈ = rec₁ (snd (pr (fst c) (Lset (fst c)) ∈ fst f)) named
        (ApproxAt-value zero (suc b) (f ∷ γ) ha c c∈)
```

<!--en-->
Completeness comes from the approximation's value clause: at each argument
below, some entry is recorded, merely. The elimination targets the proposition
that the canonical entry is recorded, so the missing witness is never needed.
<!--zh-->
完备性来自逼近的取值子句：在以下的每个实参处，都「仅仅」记录了某条目。消去的目标是「典范条目被记录」这条命题，因此那个缺席的见证永远不会被需要。
<!--ja-->
完備さは近似の値の条項から来る。下の各入力で、ある項目が単に記録される。消去の対象は「正準な項目が記録される」という命題なので、欠けている証人は決して要らない。
<!--/-->

```agda
        where
        named : Σ[ y ∈ S ] ⟨ pr (fst c) (fst y) ∈ fst f ⟩
              → ⟨ pr (fst c) (Lset (fst c)) ∈ fst f ⟩
        named (y , q) = subst (λ t → ⟨ pr (fst c) t ∈ fst f ⟩)
          (approx-val zero (suc b) (f ∷ γ) ha ob c y q) q
```
</div>
</details>


<!--en-->
The merely-given recorded value is identified with the tower by the induction
once more, and after the transport the canonical entry is exactly what is
recorded.
<!--zh-->
那个仅仅给出的被记录取值，由同一场归纳再次同认于塔；运输之后，被记录的恰是典范条目。
<!--ja-->
単に与えられただけの記録された値は、同じ帰納によってもう一度塔と同定され、輸送の後に記録されているのは正準な項目ちょうどである。
<!--/-->

<!--en-->
## A table is an approximation

The converse direction needs a witness, and a correct, complete table is one.
`graph-table`{.Agda} turns such a table into a satisfaction of the tower graph
by filling in the previous chapter's clauses and doing nothing else.
<!--zh-->
## 表就是逼近

反方向需要一个见证，而一张正确且完备的表就是。`graph-table`{.Agda} 把这样一张表变成对塔之图的满足，办法是填上上一章的诸子句，此外什么也不做。
<!--ja-->
## 表は近似である

逆方向には証人が要るが、正しくて完備な表がまさにそれである。`graph-table`{.Agda} は、そのような表を塔のグラフの充足に変える。前章の条項を埋めるだけで、それ以上のことは何もしない。
<!--/-->

<!--en-->
The domain conjunct of the approximation is the equivalence between two ways
of saying that an argument is in the domain, and `Domain`{.Agda} and
`Entries`{.Agda} prove its two directions: an entry recorded at `c` puts `c`
below the bound, and the canonical entry at `c` is recorded whenever `c` is
below the bound. The step conjunct at a recorded pair `(c, y)` is
`step-table`{.Agda} at `c`; the ordinal's transitivity restricts correctness
and completeness of the table to the arguments below `c`, which is what the
step lemma consumes there. The value the graph asks about is the step at the
whole argument, and that again is `step-table`{.Agda}, at the identification of
the recorded value with the tower.
<!--zh-->
逼近的定义域合取项是「实参在定义域中」的两种说法之间的等价，`Domain`{.Agda} 与 `Entries`{.Agda} 分别证明其两个方向：在 `c` 处记录的条目把 `c` 放到界以下；而只要 `c` 低于界，`c` 处的正準条目就被记录。某条被记录的对 `(c, y)` 处的步进合取项，是施于 `c` 的 `step-table`{.Agda}；序数的传递性把表的正确性与完备性限制到 `c` 以下的实参，那正是步进引理在该处所消费的。图所问的取值是整个实参处的步进，这同样是 `step-table`{.Agda}，取「被记录取值同认于塔」的等式为输入。
<!--ja-->
近似の定義域の連言は、入力が定義域にあるという二つの言い方の間の同値であり、`Domain`{.Agda} と `Entries`{.Agda} がその二方向を証明する。`c` で記録された項目が `c` を界の下へ置き、`c` が界の下にあるときには `c` での正準な項目が記録される。記録された組 `(c, y)` でのステップの連言は、`c` に対する `step-table`{.Agda} である。順序数の推移性が、表の正しさと完備さを `c` の下の入力へ制限する。ステップの補題がそこで消費するのはこれである。グラフが問う値は入力全体でのステップであり、これも `step-table`{.Agda} が、記録された値と塔の同定を入力にして与える。
<!--/-->

<!--en-->
The statement takes a table `h`, the ordinality of the argument, the three
conditions of the table on the argument, and the assertion that the recorded
value is the tower.
<!--zh-->
陈述取表 `h`、实参的序数性、表在实参上的三个条件，以及「被记录取值就是塔」的断言。
<!--ja-->
主張は、表 `h`、入力の順序数性、入力の上での表の三条件、そして記録された値が塔であるという主張を受け取る。
<!--/-->


<details open class="submodule-fold">
<summary class="submodule-fold-heading">
```agda
module _ {n : ℕ} (w b : Fin n) (γ : S ^ n) where
```
</summary>
<div class="submodule-fold-content">

```agda
  graph-table : (h : S) → IsOrd (fst (lookup b γ))
              → Values h (fst (lookup b γ)) → Entries h (fst (lookup b γ))
              → Domain h (fst (lookup b γ))
              → fst (lookup w γ) ≡ Lset (fst (lookup b γ))
```

<!--en-->
It concludes that the tower graph is satisfied at the value and argument
slots.
<!--zh-->
结论是塔之图在取值槽与实参槽处成立。
<!--ja-->
塔のグラフが値と入力の枠で成立すると結論する。
<!--/-->

```agda
              → ⟨ γ ⊨ LsetGraphAt w b ⟩
  graph-table h ob vals ents dom q = LsetGraph-in w b γ h approx
    (step-table (suc w) (suc b) zero (h ∷ γ) ob vals ents q)
    where
```

<!--en-->
The tower graph is introduced from an approximation and an outer step. The
approximation is the table itself, placed in the extended environment; the
outer step is `step-table` at the argument, for which correctness, completeness
and the identification with the tower are exactly the hypotheses in hand.
<!--zh-->
塔之图由一个逼近与一个外层步进引入。逼近就是表本身，被放进扩展环境；外层步进是施于实参的 `step-table`，其正确性、完备性与对塔的同认恰是手头的假设。
<!--ja-->
塔のグラフは、一つの近似と外側のステップから導入される。近似は表そのものであり、拡張された環境に置かれる。外側のステップは入力に対する `step-table` であり、その正しさ・完備さ・塔との同定は、まさに手もとの仮定である。
<!--/-->

```agda
    onDom : (c : S)
          → (⟨ ∃[ y ∶ S ] pr (fst c) (fst y) ∈ fst h ⟩
             → ⟨ fst c ∈ fst (lookup b γ) ⟩)
          × (⟨ fst c ∈ fst (lookup b γ) ⟩
             → ⟨ ∃[ y ∶ S ] pr (fst c) (fst y) ∈ fst h ⟩)
```

<!--en-->
The approximation's domain clause is an equivalence between two ways of saying
that `c` is in the domain: that some entry with first component `c` is
recorded, and that `c` is below the argument. Both directions are needed,
since the approximation's domain condition reads them in opposite orders.
<!--zh-->
逼近的定义域子句是「`c` 在定义域中」的两种说法之间的等价：有以 `c` 为第一分量的条目被记录，与 `c` 低于实参。两个方向都需要，因为逼近的定义域条件会以相反的次序使用它们。
<!--ja-->
近似の定義域の条項は、`c` が定義域にあるという二つの言い方の間の同値である。第一成分が `c` である項目が何か記録されていることと、`c` が入力の下にあること。両方向が要る。近似の定義域の条件は、これらを逆の順で使うからである。
<!--/-->

```agda
    onDom c = (λ hy → rec₁ (snd (fst c ∈ fst (lookup b γ))) named hy)
            , (λ c∈ → ∣ LsetS (fst c) (mem-ord {A = fst (lookup b γ)} ob (fst c) c∈)
                     , ents c c∈ ∣₁)
```

<!--en-->
Reading the equivalence to the right: a recorded entry at `c`, together with
completeness of the table, exhibits the canonical entry, which is the record of
the stage at `c` presented as an element of `L`, with ordinality of `c` from
that of the argument. Reading to the left: the domain condition of the table
puts `c` below the argument.
<!--zh-->
把等价向右读：`c` 处的一条被记录条目，连同表的完备性，给出典范条目，即呈现为 `L` 元素的 `c` 处之层 (`c` 的序数性取自实参的序数性) 的记录。向左读：表的定义域条件把 `c` 放到实参以下。
<!--ja-->
同値を右へ読むと、`c` での記録された項目と表の完備さが、正準な項目を示す。それは `L` の要素として提示された `c` での段階の記録であり、`c` の順序数性は入力の順序数性から来る。左へ読むと、表の定義域の条件が `c` を入力の下へ置く。
<!--/-->

```agda
      where
      named : Σ[ y ∈ S ] ⟨ pr (fst c) (fst y) ∈ fst h ⟩
            → ⟨ fst c ∈ fst (lookup b γ) ⟩
      named (y , p) = dom c y p
```

<!--en-->
The auxiliary `named` is the domain condition read on the witness: an entry
with first component `c` exists, so `c` is below the argument. Its content is
one application of the table's third condition.
<!--zh-->
辅助事实 `named` 是对见证读取定义域条件：存在第一分量为 `c` 的条目，故 `c` 低于实参。其内容就是表的第三个条件的一次应用。
<!--ja-->
補助の `named` は、証人に定義域の条件を読んだものである。第一成分が `c` である項目が存在するので、`c` は入力の下にある。その内容は、表の第三の条件の一回の適用である。
<!--/-->

```agda
    onStep : (c y : S) → ⟨ pr (fst c) (fst y) ∈ fst h ⟩
           → ⟨ (y ∷ c ∷ h ∷ γ) ⊨ StepAt zero (suc zero) (suc (suc zero)) ⟩
    onStep c y p = step-table zero (suc zero) (suc (suc zero)) (y ∷ c ∷ h ∷ γ)
      oc vals' ents' (vals c y c∈ p)
```

<!--en-->
The step conjunct is proved at each recorded pair `(c, y)`. In the environment
extended by the value `y`, the argument `c` and the table `h`, the step
condition relates the value slot to the argument slot through the table slot;
`step-table` at `c` establishes exactly that, with the identification
`fst y ≡ Lset (fst c)` supplied by correctness at the recorded pair.
<!--zh-->
步进合取项在每条被记录的对 `(c, y)` 处证明。在加入取值 `y`、实参 `c` 与表 `h` 的扩展环境中，步进条件经由表槽把取值槽与实参槽联系起来；施于 `c` 的 `step-table` 恰好建立这一点，而所需的同认 `fst y ≡ Lset (fst c)` 由正确性在该被记录对处供给。
<!--ja-->
ステップの連言は、記録されたそれぞれの組 `(c, y)` で証明される。値 `y`、入力 `c`、表 `h` を追加した環境の中で、ステップ条件は表の枠を通して値の枠と入力の枠を結ぶ。`c` に対する `step-table` がまさにこれを確立し、同定 `fst y ≡ Lset (fst c)` は記録された組での正しさが供給する。
<!--/-->

```agda
      where
      c∈ : ⟨ fst c ∈ fst (lookup b γ) ⟩
      c∈ = dom c y p
      oc : IsOrd (fst c)
      oc = mem-ord {A = fst (lookup b γ)} ob (fst c) c∈
```

<!--en-->
Two facts about `c` are read off the recorded pair. Its underlying set is
below the argument, by the domain condition; and it is an ordinal, by the
ordinality of the argument.
<!--zh-->
关于 `c` 的两件事实从被记录对读出：其底层集合低于实参，由定义域条件；它是序数，由实参的序数性。
<!--ja-->
`c` についての二つの事実が、記録された組から読み取れる。その基礎の集合は入力の下にあり、これは定義域の条件から。そしてそれが順序数であることは、入力の順序数性からである。
<!--/-->

```agda
      vals' : Values h (fst c)
      vals' e t _ r = vals e t (dom e t r) r
      ents' : Entries h (fst c)
      ents' e e∈ = ents e (ob .fst {x = fst c} {y = fst e} e∈ c∈)
```

<!--en-->
Correctness and completeness below `c` are the table's own conditions,
restricted to arguments below `c`: correctness restricts the domain hypothesis,
and completeness uses the transitivity of the argument to see that an argument
below `c` is below the argument. This is the second and last use of that
transitivity in the chapter.
<!--zh-->
`c` 以下的正确性与完备性是表自己的条件限制到 `c` 以下：正确性限制定义域假设，完备性则用实参的传递性看出「低于 `c` 的实参低于实参」。这是本章对该传递性的第二次、也是最后一次使用。
<!--ja-->
`c` の下での正しさと完備さは、表自身の条件を `c` の下の入力に制限したものである。正しさは定義域の仮定を制限し、完備さは入力の推移性を使って、`c` の下の入力が入力の下にもあることを見る。この推移性を使うのは、本章でここが二度目で最後である。
<!--/-->

```agda
    approx : ⟨ (h ∷ γ) ⊨ ApproxAt zero (suc b) ⟩
    approx = ApproxAt-in zero (suc b) (h ∷ γ)
      (domAt-intro zero (suc b) (h ∷ γ) onDom) onStep
```
</div>
</details>


<!--en-->
Assembling the two conjuncts, the table itself is an approximation: its domain
clause is the equivalence just proved, its step clause the one before. This is
the sense in which a correct, complete table contains a recording of the
hierarchy below the argument.
<!--zh-->
把两个合取项装配起来，表本身就是逼近：其定义域子句是刚才证明的等价，其步进子句是之前的那个。所谓「正确且完备的表包含实参以下层级的记录」，其含义就在于此。
<!--ja-->
二つの連言を組み立てると、表そのものが近似になる。定義域の条項が今証明した同値であり、ステップの条項がその前のものである。正しくて完備な表が入力の下の階層の記録を含む、と言うのはこの意味である。
<!--/-->

<!--en-->
## The pair graph

The table has to be **built**, and the only builder available inside `L` is
replacement, which asks for a graph. Replacement collects the table after the
functional-graph description: an entry of the table is the ordered pair of an
argument `c` with a value `z`, and the graph holds of an entry when `z`
satisfies the tower graph at `c`, with the carrier over which the tower ranges
pinned to a constant. One existential binds the tower's value, the pair reader
equates the entry with the pair of the argument and the bound value, and the
tower graph says the bound value is the right one.
<!--zh-->
## 有序对图

表必须被**构造出来**，而 `L` 内部可用的建造者只有替换，替换需要一个图。替换在函数性图的描述之后收集这张表：表的一条目是实参 `c` 与取值 `z` 的有序对；当 `z` 满足塔在 `c` 处的图时，图对该条目成立，而塔所遍及的载体被钉在某个常元上。一个存在量词绑定塔的取值，对读式把条目与「实参和被绑定取值」组成的对等同起来，塔之图则说明被绑定的取值是正确的。
<!--ja-->
## 順序対のグラフ

表は**作られ**なければならない。`L` の内側で使える作り手は置換だけであり、置換はグラフを要求する。置換は、関数グラフの記述のあとで表を集める。表の項目は入力 `c` と値 `z` の順序対であり、`z` が `c` での塔のグラフを満たすとき、グラフはその項目について成立する。塔が渡り歩く台は定数に固定されている。一つの存在量化が塔の値を束縛し、対の読み出しが項目を「入力と束縛された値」の対と等置し、塔のグラフが、束縛された値が正しいことを言う。
<!--/-->

<!--en-->
Its two readings take the sentence as a **parameter**, with the sentence's own
equation as a hypothesis, `refl`{.Agda} at the call site of this chapter. The
frame is generic in the sentence: the readings speak of whatever formula is
passed, under the assumption that it spells the pair graph. The equation
travels with the sentence, so the readings are applied without further
argument.
<!--zh-->
它的两种读法把那个句子取作**参数**，并把该句子自己的等式取作假设，本章的调用处是 `refl`{.Agda}。该框架对句子保持通用：无论传入什么公式，读法都在「它拼出有序对图」的假设下谈论它。等式随句子同行，因此读法的施用无需更多论证。
<!--ja-->
この二つの読み出しは、文を**パラメータ**として受け取り、文自身の等式を仮定として受け取る。本章の呼び出しでは `refl`{.Agda} である。枠組みは文に対して一般的である。渡された論理式が何であれ、それが順序対のグラフを綴っているという仮定のもとで、読み出しは語る。等式は文とともに渡されるので、読み出しの適用にそれ以上の議論は要らない。
<!--/-->

<!--en-->
## The internal hierarchy

`Recorded`{.Agda} names the class of pairs that the internal hierarchy at `α`
is to collect: an argument `c` whose underlying set lies below `α`, together
with the tower's value at `c`, and nothing besides. `IsHier`{.Agda} says that a
set of the model realizes this class member for member: for every carrier
element `z`, membership in the set holds exactly when `z` presents such a pair.
Both directions of this statement are used. `HierOf`{.Agda} gathers a realizing
set together with its specification, which is the form the construction builds
and the form its two readings consume.
<!--zh-->
## 内部层级

`Recorded`{.Agda} 为内部层级在 `α` 处要收集的类命名：底层集合低于 `α` 的实参 `c`，连同塔在 `c` 处的取值组成的对，此外别无他物。`IsHier`{.Agda} 说模型的某个集合逐成员地实现这个类：对每个载体元素 `z`，属于该集合恰当 `z` 呈现为这样的对。这条陈述的两个方向都有使用。`HierOf`{.Agda} 把实现集合连同其规格收为一对；构造所建造的是这个形式，两条读式所消费的也是这个形式。
<!--ja-->
## 内部の階層

`Recorded`{.Agda} は、`α` における内部の階層が集めるべきクラスに名前を与える。基礎の集合が `α` の下にある入力 `c` と、塔の `c` での値の対であり、そのほかには何もない。`IsHier`{.Agda} は、モデルのある集合がこのクラスを要素ごとに実現することを言う。台の要素 `z` それぞれに対し、その集合への所属は、`z` がそのような対を提示するときにちょうど成立する。この主張の両方向が使われる。`HierOf`{.Agda} は、実現する集合をその仕様とともに集める。構成が作るのはこの形であり、二つの読み出しが消費するのもこの形である。
<!--/-->

<!--en-->
The two readings stand at a **variable** realizing set reached by its
specification, so that the construction to come can apply them to the set it is
building. Reading out applies the injectivity of the hierarchy's pair to a
member: an entry of the realizing set names an argument below `B` and the
tower's value there. Reading in exhibits the canonical pair as an element of
the model, which the model's own pairing supplies; it also needs ordinality of
the argument, without which the tower's value could not be named at all.

Then the construction, one membership induction on the ordinal. At `α` the pair
graph is functional at every argument below: the induction hypothesis hands over
the hierarchy up to that argument, `graph-table`{.Agda} turns it into a
satisfaction of the tower graph, and `Lset-only`{.Agda} says nothing else
satisfies it. Replacement collects the pairs into a set of the model.
Ordinality of each argument comes from `mem-ord`{.Agda}, and the functionality
requirement is met through `mereFunct`{.Agda}, because the value at an argument
is a construction.
<!--zh-->
两条读式都针对一个由其规格抵达的**变元**实现集合，这样即将到来的构造就可以把它们应用于自己正在建造的集合。向外读取时，对某个成员应用层级配对的单射性：实现集合的一条目指名低于 `B` 的实参与塔在该处的取值。向内写入时，把正準对呈现为模型的元素，这由模型自身的配对给出；它还需要实参的序数性，否则根本无法指称塔在该处的取值。

然后是构造，在序数上作一次沿成员的归纳。在 `α` 处，成对的那个图在以下的每个实参上都是函数性的：归纳假设给出直到那个实参为止的层级，`graph-table`{.Agda} 把它变成对塔之图的满足，而 `Lset-only`{.Agda} 说别的东西都不满足它。替换把这些对收集成模型的一个集合。每个实参的序数性取自 `mem-ord`{.Agda}；函数性要求由 `mereFunct`{.Agda} 满足，因为某个实参处的取值是一个构造。
<!--ja-->
二つの読み出しは、仕様を通して届く**変数**の実現集合の上に立つ。これから作る構成が、自分の作っている集合にそれを適用できるようにするためである。外向きの読みは、階層の対の単射性をある要素に適用する。実現集合の項目は、`B` の下の入力と塔のそこでの値を名指す。内向きの読みは、正準な対をモデルの要素として示す。これはモデル自身の対の構成が与えるが、入力の順序数性も要る。それがなければ、塔のそこでの値をそもそも名指せないからである。

そして構成である。順序数の上の、所属に沿う帰納が一回。`α` において、対のグラフは下のすべての入力で関数的である。帰納の仮定がその入力までの階層を渡し、`graph-table`{.Agda} がそれを塔のグラフの充足に変え、`Lset-only`{.Agda} がそれを満たすものはほかにないと言う。置換が対をモデルの集合に集める。各入力の順序数性は `mem-ord`{.Agda} から来て、関数性の要求は `mereFunct`{.Agda} で満たされる。入力での値は判定ではなく構成だからである。
<!--/-->

```agda
Recorded : V ℓ → V ℓ → hProp (ℓ-suc ℓ)
Recorded B z = ∃[ c ∶ S ] (fst c ∈ B)
  ⊓ ((z ≡ pr (fst c) (Lset (fst c))) , setIsSet z (pr (fst c) (Lset (fst c))))
```

<!--en-->
`Recorded B z` is a proposition, and it says: for some carrier element `c`
whose underlying set lies below `B`, the underlying set of `z` is the ordered
pair of `fst c` with the tower's value at `c`. The equality of two h-sets is
itself a proposition, so the join is a join of propositions.
<!--zh-->
`Recorded B z` 是一个命题，它说：存在某个载体元素 `c`，其底层集合低于 `B`，使得 `z` 的底层集合是 `fst c` 与塔在 `c` 处取值的有序对。两个 h-集合的相等本身就是命题，因此这是一个命题上的析取聚合。
<!--ja-->
`Recorded B z` は命題であり、こう言う。基礎の集合が `B` の下にある台の要素 `c` のうち何かに対して、`z` の基礎の集合は `fst c` と塔の `c` での値の順序対である、と。二つの h-集合の等しさはそれ自体命題なので、これは命題の上での選言の集まりである。
<!--/-->

```agda
IsHier : V ℓ → S → Type (ℓ-suc (ℓ-suc ℓ))
IsHier B h = (z : S) → (fst z ∈ fst h) ≡ Recorded B (fst z)
```

<!--en-->
`IsHier B h` says that the set presented by `h` realizes the recorded class
member for member: at each `z`, membership in the set and being recorded are
the same proposition. Neither direction is dropped, because each is used:
membership without recordedness would let strangers in, recordedness without
membership would leave pairs out.
<!--zh-->
`IsHier B h` 说 `h` 所呈现的集合逐成员地实现被记录的类：在每个 `z` 处，属于该集合与被记录是同一命题。两个方向都不丢弃，因为各有其用：只有隶属而无被记录，会放进陌生者；只有被记录而无隶属，会漏掉应有的对。
<!--ja-->
`IsHier B h` は、`h` が提示する集合が、記録されたクラスを要素ごとに実現することを言う。各 `z` で、集合への所属と記録されていることは同じ命題である。どちらの方向も捨てられない。それぞれに使い道があるからである。所属だけがあればよしとすると、よそ者が入る。記録だけがあればよしとすると、あるべき対が抜け落ちる。
<!--/-->

```agda
HierOf : V ℓ → Type (ℓ-suc (ℓ-suc ℓ))
HierOf B = Σ[ h ∈ S ] IsHier B h
```

<!--en-->
`HierOf B` collects a realizing set with its specification. The pair is what
the induction will build at each ordinal, and its two components answer the two
questions one asks of a construction: what is it, and why does it qualify.
<!--zh-->
`HierOf B` 把实现集合连同其规格收集为一对。这对正是归纳要在每个序数处构造的东西；它的两个分量分别回答对任何构造都要问的两个问题：它是什么，以及它为何合格。
<!--ja-->
`HierOf B` は、実現する集合をその仕様とともに集める。この対こそ、帰納がそれぞれの順序数で作るものであり、その二つの成分は、構成に対して誰もが問う二つの問いに答える。それは何か。なぜそれが資格をもつのか。
<!--/-->


<details open class="submodule-fold">
<summary class="submodule-fold-heading">
```agda
module _ (B : V ℓ) (oB : IsOrd B) (h : S) (sp : IsHier B h) where
```
</summary>
<div class="submodule-fold-content">



<!--en-->
The two readings are stated for a variable realizing set with its
specification, so that the construction to come can apply them to the set it
is building, at whatever stage the induction currently stands.
<!--zh-->
两条读式对一个带规格的变元实现集合陈述，这样即将到来的构造就可以把它们应用于自己正在建造的集合，无论归纳当前站在哪个层。
<!--ja-->
二つの読み出しは、仕様を伴う変数の実現集合に対して述べられる。これから作る構成が、帰納がいま立っている段階がどこであれ、自分の作っている集合にそれを適用できるようにするためである。
<!--/-->

```agda
  hier-out : (c z : S) → ⟨ pr (fst c) (fst z) ∈ fst h ⟩
           → ⟨ fst c ∈ B ⟩ × (fst z ≡ Lset (fst c))
```

<!--en-->
Reading out: if the pair of `c` and `z` is a member of the realizing set, then
`c` lies below `B` and `z` is the tower at `c`. Both conclusions follow from
the specification applied at the member.
<!--zh-->
向外读：若 `c` 与 `z` 组成的对是实现集合的成员，则 `c` 低于 `B`，且 `z` 是塔在 `c` 处的取值。两个结论都由规格施加于该成员而来。
<!--ja-->
外向きの読みである。`c` と `z` の対が実現集合の要素なら、`c` は `B` の下にあり、`z` は塔の `c` での値である。どちらの結論も、その要素に仕様を適用したことから従う。
<!--/-->

```agda
  hier-out c z p = rec₁
    (isProp× (snd (fst c ∈ B)) (setIsSet (fst z) (Lset (fst c)))) read
    (subst ⟨_⟩ (sp k) p)
    where
```

<!--en-->
The member's membership is transported along the specification into the
recorded proposition, which is a truncated existence; the target of the
elimination is a pair of propositions, hence a proposition, so the witness may
be consumed here.
<!--zh-->
该成员的隶属沿规格被运进被记录命题，而那是一条截断的存在；消去的目标是一对命题构成的命题，因此可以在这里消耗见证。
<!--ja-->
その要素の所属は、仕様に沿って記録の命題へ運ばれる。それは切り詰められた存在である。消去の対象は命題の対、したがって命題なので、証人をここで消費してかまわない。
<!--/-->

```agda
    k : S
    k = pr (fst c) (fst z)
      , isL-trans {x = fst h} {y = pr (fst c) (fst z)} p (h .snd)
```

<!--en-->
The member itself must be named as a carrier element: the ordered pair of the
underlying sets is constructible, because it belongs to the constructible set
presented by `h`.
<!--zh-->
成员自身也须被命名为载体元素：底层集合的有序对可构造，因为它属于 `h` 所呈现的可构造集合。
<!--ja-->
その要素自身も、台の要素として名指す必要がある。基礎の集合の順序対は構成可能である。`h` が提示する構成可能集合に属するからである。
<!--/-->

```agda
    read : Σ[ d ∈ S ] (⟨ fst d ∈ B ⟩
             × (pr (fst c) (fst z) ≡ pr (fst d) (Lset (fst d))))
         → ⟨ fst c ∈ B ⟩ × (fst z ≡ Lset (fst c))
    read (d , (d∈ , eq)) =
        subst (λ t → ⟨ t ∈ B ⟩) (sym (pr-inj eq .fst)) d∈
```

<!--en-->
The recorded proposition exhibits `d` below `B` with the member equal to the
pair of `d` and the tower at `d`. Injectivity of the hierarchy's pair splits
the equation: the first components identify `c` with `d`, which moves the
membership into `c` being below `B`, and the second components identify `z`
with the tower at `d`, which the first identification turns into the tower at
`c`.
<!--zh-->
被记录命题给出低于 `B` 的 `d`，且该成员等于 `d` 与塔在 `d` 处取值组成的对。层级配对的单射性拆开这条等式：第一分量的等同把 `c` 同认于 `d`，从而把隶属搬成「`c` 低于 `B`」；第二分量的等同把 `z` 同认于塔在 `d` 处的取值，再经第一等同变成塔在 `c` 处的取值。
<!--ja-->
記録された命題は、`B` の下の `d` と、その要素が「`d` と塔の `d` での値」の対に等しいことを示す。階層の対の単射性がこの等式を分解する。第一成分の同定は `c` を `d` と同一視し、所属を「`c` が `B` の下にある」ことへ移す。第二成分の同定は `z` を塔の `d` での値と同一視し、最初の同定がそれを塔の `c` での値へ変える。
<!--/-->

```agda
      , (pr-inj eq .snd ∙ cong Lset (sym (pr-inj eq .fst)))

  hier-in : (c : S) → ⟨ fst c ∈ B ⟩ → ⟨ pr (fst c) (Lset (fst c)) ∈ fst h ⟩
  hier-in c c∈ = subst (λ t → ⟨ t ∈ fst h ⟩) (prʟ-fst c (LsetS (fst c) oc))
    (subst ⟨_⟩ (sym (sp k)) ∣ c , (c∈ , prʟ-fst c (LsetS (fst c) oc)) ∣₁)
```

<!--en-->
Reading in: the canonical entry, the model's own pair of `c` with the tower at
`c`, is a member. The specification says the recorded class is realized, the
canonical pair is a witness of the recorded proposition with `c` itself as the
argument, and the entry equals the model's pair by its defining reading.
<!--zh-->
向内读：典范条目，即模型自身的「`c` 与塔在 `c` 处取值」之对，是成员。规格说被记录的类被实现，而典范对正是被记录命题的见证 (以 `c` 本身为实参)；条目与模型之对相等，则由该对的定义读式给出。
<!--ja-->
内向きの読みである。正準な項目、すなわちモデル自身の「`c` と塔の `c` での値」の対は、要素である。仕様は、記録されたクラスが実現されると言い、典型的な対は `c` 自身を入力とする記録の命題の証人である。そして項目がモデルの対と等しいことは、その対の定義の読みから得られる。
<!--/-->

```agda
    where
    oc : IsOrd (fst c)
    oc = mem-ord {A = B} oB (fst c) c∈
    k : S
    k = prʟ c (LsetS (fst c) oc)
```
</div>
</details>


<!--en-->
Ordinality of `c` comes from that of `B`, and with it the tower's value at `c`
can be presented as an element of `L`, which is what the model's pair needs as
its second component.
<!--zh-->
`c` 的序数性来自 `B` 的序数性；有了它，塔在 `c` 处的取值才能呈现为 `L` 的元素，而这正是模型的配对所需要的第二分量。
<!--ja-->
`c` の順序数性は `B` の順序数性から来る。それがあってはじめて、塔の `c` での値を `L` の要素として提示でき、モデルの対が第二成分として必要とするのはこれである。
<!--/-->

```agda
opaque
  hierAt : (α : V ℓ) → ⟨ isL α ⟩ → IsOrd α → HierOf α
  hierAt = ∈-induction {P = λ α → ⟨ isL α ⟩ → IsOrd α → HierOf α}
    (build (PairGraphAt zero (suc zero)) refl)
    where
```

<!--en-->
The step function keeps the pair graph as a **variable sentence carrying its
own equation**, rather than writing out the closed sentence it is instantiated
to. The equation travels with the sentence, so every reading below is applied
with `refl`{.Agda} at the call.
<!--zh-->
归纳的步进函数把成对的那个图保持为**随身携带自己等式的变元句子**，而不写出它将被实例化成的闭句子。等式随句子同行，因此下面的每条读式都在调用处以 `refl`{.Agda} 施用。
<!--ja-->
帰納のステップ関数は、対のグラフを、自分自身の等式を携えた**変数の文**として保つ。実例化先の閉じた文を書き出すのではない。等式は文とともに渡されるので、以下のどの読み出しも呼び出しで `refl`{.Agda} を仮定として受け取る。
<!--/-->

```agda
    build : (φ : Formula S 2) → φ ≡ PairGraphAt zero (suc zero)
          → (α : V ℓ)
          → ((δ : V ℓ) → ⟨ δ ∈ α ⟩ → ⟨ isL δ ⟩ → IsOrd δ → HierOf δ)
          → ⟨ isL α ⟩ → IsOrd α → HierOf α
```

<!--en-->
The step receives the sentence with its equation, the ordinal `α`, its two
certificates, and the induction hypothesis: the hierarchy is already built at
every member of `α`. It must return the hierarchy at `α` with its
specification.
<!--zh-->
步进接收句子及其等式、序数 `α`、它的两张证书，以及归纳假设：`α` 的每个成员处的层级均已建成。它须返回 `α` 处的层级及其规格。
<!--ja-->
ステップは、文とその等式、順序数 `α`、その二つの証明書、そして帰納の仮定を受け取る。`α` のすべての要素で階層はすでに作られている。ステップは、`α` での階層とその仕様を返さねばならない。
<!--/-->

```agda
    build φ qφ α IH hα oα = r .fst .fst , spec
      where
      A : S
      A = α , hα
```

<!--en-->
The hierarchy at `α` is the first component of a realizer, extracted once
replacement has produced it; `A` is `α` presented as a carrier element, the
form in which replacement consumes a domain.
<!--zh-->
`α` 处的层级是实现者的第一分量，在替换产出之后一次提取；`A` 是呈现为载体元素的 `α`，正是替换消费定义域时所用的形式。
<!--ja-->
`α` での階層は、実現者の第一成分であり、置換がそれを作ったのちに一度取り出される。`A` は台の要素として提示された `α` で、置換が定義域を消費する形である。
<!--/-->

```agda
      value : (c : S) → ⟨ fst c ∈ α ⟩ → S
      value c c∈ = LsetS (fst c) (mem-ord {A = α} oα (fst c) c∈)

      entry : (c : S) → ⟨ fst c ∈ α ⟩ → S
      entry c c∈ = prʟ c (value c c∈)
```

<!--en-->
Below `α`, two auxiliary constructions name the data. The value at an argument
`c` is the stage at `c`, an element of `L` by the stage presentation, with
ordinality of `c` from that of `α`. The entry at `c` is the model's ordered
pair of `c` with its value, the form the recorded class asks for.
<!--zh-->
在 `α` 以下，两个辅助构造为数据命名。实参 `c` 处的取值是 `c` 处的层，由层呈现而成为 `L` 的元素，`c` 的序数性取自 `α` 的序数性。`c` 处的条目是模型自身的「`c` 与其取值」的有序对，正是被记录类所要求的形式。
<!--ja-->
`α` の下では、二つの補助構成がデータに名前を与える。入力 `c` での値は `c` での段階であり、段階の提示によって `L` の要素である。`c` の順序数性は `α` の順序数性から来る。`c` での項目は、モデル自身の「`c` とその値」の順序対で、記録されたクラスが求める形である。
<!--/-->

```agda
      below : (c : S) (c∈ : ⟨ fst c ∈ α ⟩) (k : S)
            → ⟨ (value c c∈ ∷ k ∷ c ∷ []) ⊨ LsetGraphAt zero (suc (suc zero)) ⟩
      below c c∈ k = graph-table zero (suc (suc zero)) (value c c∈ ∷ k ∷ c ∷ [])
        (hc .fst) oc
```

<!--en-->
The tower graph is satisfied at the value recorded for a member `c` of `α`.
This is where the induction hypothesis is spent: it hands over the hierarchy at
`c`, a correct and complete table on the argument `c`, which is precisely what
`graph-table`{.Agda} asks for. The environment carries the value, a fresh slot
for the graph's own quantifier, and the argument.
<!--zh-->
塔之图在为 `α` 的成员 `c` 所记录的取值处成立。归纳假设正是在此被花掉：它交出 `c` 处的层级，那是实参 `c` 上一张正确且完备的表，恰是 `graph-table`{.Agda} 所要的。环境中载着取值、给图自身量词留的新槽，以及实参。
<!--ja-->
塔のグラフは、`α` の要素 `c` のために記録された値で成立する。帰納の仮定を費やすのはここである。仮定は `c` での階層、すなわち入力 `c` の上で正しくて完備な表を渡す。これは `graph-table`{.Agda} が求めるものそのものである。環境には、値と、グラフ自身の量化子のための新しい枠と、入力が載る。
<!--/-->

```agda
        (λ d z _ p → hier-out (fst c) oc (hc .fst) (hc .snd) d z p .snd)
        (hier-in (fst c) oc (hc .fst) (hc .snd))
        (λ d z p → hier-out (fst c) oc (hc .fst) (hc .snd) d z p .fst)
        refl
```

<!--en-->
The three table conditions are read off the specification of the hierarchy at
`c`: correctness says every recorded value is the tower there, completeness
says the canonical entries are recorded, and the domain condition says nothing
else is recorded. The last argument, `refl`, is the pair graph's own equation.
<!--zh-->
表的三个条件从 `c` 处层级的规格读出：正确性说每个被记录取值都是塔在那里；完备性说典范条目被记录；定义域条件说此外无他。最后一个参数 `refl` 是有序对图自己的等式。
<!--ja-->
表の三条件は、`c` での階層の仕様から読まれる。正しさは、記録されたすべての値が塔のそこでの値であると言い、完備さは正準な項目が記録されると言い、定義域の条件はほかには何も記録されないと言う。最後の引数 `refl` は、順序対のグラフ自身の等式である。
<!--/-->

```agda
        where
        oc : IsOrd (fst c)
        oc = mem-ord {A = α} oα (fst c) c∈
        hc : HierOf (fst c)
        hc = IH (fst c) c∈ (snd c) oc
```

<!--en-->
Ordinality of `c` comes from that of `α`, and with it the induction hypothesis
delivers the hierarchy at `c`, constructible set and specification together.
<!--zh-->
`c` 的序数性来自 `α` 的序数性；有了它，归纳假设交付 `c` 处的层级；可构造集合与规格一并交付。
<!--ja-->
`c` の順序数性は `α` の順序数性から来る。それがあれば、帰納の仮定は `c` での階層を、構成可能集合と仕様とともに渡す。
<!--/-->


<!--en-->
(holds) Every canonical entry satisfies the pair graph: the fiber over `c` is
exhibited, with the bound tower value, the equation identifying the entry with
the model's pair, and the satisfaction of the tower graph at the value and the
argument. The witness is a member of the fiber, that is, of the type whose
merely-existence the graph statement asserts.
<!--zh-->
（holds)每条正準条目都满足有序对图：`c` 上的纤维被给出，其中包括被绑定的塔值、把条目与模型之对等同的等式，以及塔之图在取值与实参处的满足。见证是纤维的一个元素，即图陈述所断言「仅仅存在」的那个类型的元素。
<!--ja-->
（holds)正準な項目はどれも、順序対のグラフを満たす。`c` の上のファイバーが示される。そこには、束縛された塔の値、項目をモデルの対と同定する等式、そして値と入力での塔のグラフの充足が入る。証人はファイバーの要素、すなわちグラフの主張が単なる存在を述べる型の要素である。
<!--/-->

```agda
      holds : (c : S) (c∈ : ⟨ fst c ∈ α ⟩)
            → ⟨ (entry c c∈ ∷ c ∷ []) ⊨ φ ⟩
      holds c c∈ = PairGraph-in zero (suc zero) (entry c c∈ ∷ c ∷ []) φ qφ
        (value c c∈) (prʟ-fst c (value c c∈)) (below c c∈ (entry c c∈))
```




<!--en-->
(only) Every other inhabitant of the graph at `c` equals the canonical entry.
The graph unfolds to a tower value `z` with the tower graph satisfied at `(z,
c)`; the tower graph determines its value, the pair's injectivity identifies
the two entries, and the equation is the composition of these paths.
<!--zh-->
（only)在 `c` 处满足图的其他任何居留者都等于正準条目。图展开为塔值 `z` 连同在 `(z, c)` 处成立的塔之图；塔之图确定其取值，配对的单射性等同两条目，而该等式是这些路径的复合。
<!--ja-->
（only)`c` でグラフを満たすほかのどんな inhabitant も、正準な項目と等しくなる。グラフは、塔の値 `z` と、`(z, c)` で成立する塔のグラフへほどける。塔のグラフはその値を決定し、対の単射性が二つの項目を同一視し、等式はこれらのパスの合成である。
<!--/-->

```agda
      only : (c : S) (c∈ : ⟨ fst c ∈ α ⟩) (k : S)
           → ⟨ (k ∷ c ∷ []) ⊨ φ ⟩ → k ≡ entry c c∈
      only c c∈ k h = rec₁ (isSetS k (entry c c∈)) read
        (PairGraph-out zero (suc zero) (k ∷ c ∷ []) φ qφ h)
```



<!--en-->
The pair witness splits into the tower value `z` and the equation `q`
identifying `k` with the pair of `c` and `z`. The carrier elements are equal
once their underlying sets are, which is what `Σ≡Prop` reduces the goal to.
<!--zh-->
对的见证拆成塔值 `z` 与把 `k` 同认于「`c` 与 `z` 之对」的等式 `q`。一旦底层集合相等，载体元素就相等，`Σ≡Prop` 把目标化归于此。
<!--ja-->
対の証人は、塔の値 `z` と、`k` を「`c` と `z` の対」と同定する等式 `q` に分かれる。基礎の集合が等しければ台の要素は等しい。`Σ≡Prop` が目標をこれへ帰着させる。
<!--/-->

```agda
        where
        read : PairOf zero (suc zero) (k ∷ c ∷ []) φ qφ → k ≡ entry c c∈
        read (z , (q , hg)) = Σ≡Prop (λ t → snd (isL t))
          ( q
```



<!--en-->
The tower graph at `(z, c)` determines the tower value: `z` is the tower at
`c`, by `Lset-only` applied in the environment extended by the value, the
canonical entry and the argument, with ordinality of `c` from that of `α`.
<!--zh-->
`(z, c)` 处的塔之图确定塔值：由 `Lset-only` 在「加入取值、典范条目与实参」的扩展环境中施用，得 `z` 就是塔在 `c` 处的取值；`c` 的序数性取自 `α` 的序数性。
<!--ja-->
`(z, c)` での塔のグラフは塔の値を決定する。値・正準な項目・入力を追加した環境で `Lset-only` を適用すれば、`z` は塔の `c` での値である。`c` の順序数性は `α` の順序数性から来る。
<!--/-->

```agda
          ∙ cong (pr (fst c))
              (Lset-only zero (suc (suc zero)) (z ∷ k ∷ c ∷ []) hg
                (mem-ord {A = α} oα (fst c) c∈))
          ∙ sym (prʟ-fst c (value c c∈)) )
```

<!--en-->
Composing the three paths, `k` is the pair of `c` and the tower at `c`, which
is the canonical entry read through its own defining equation.
<!--zh-->
三条路径复合起来，`k` 就是「`c` 与塔在 `c` 处取值」之对，即按其定义读式读出的典范条目。
<!--ja-->
三つのパスを合成すれば、`k` は「`c` と塔の `c` での値」の対であり、それは自分の定義の読みを通して読んだ正準な項目である。
<!--/-->


<!--en-->
(fc) Functionality at `c` is the contractible fiber that replacement asks for:
the canonical entry inhabits the graph, and every inhabitant equals it.
`mereFunct` assembles the two halves, presented merely, into exactly that
contractible fiber.
<!--zh-->
（fc)`c` 处的函数性正是替换所要的可缩纤维：正準条目在图中有一席，而每个居留者都等于它。`mereFunct` 把以「仅仅存在」形式呈现的两半，装配成恰为该可缩纤维的居留。
<!--ja-->
（fc)`c` での関数性は、置換が求める可縮なファイバーである。正準な項目がグラフの inhabitant であり、どんな inhabitant もそれと等しくなる。`mereFunct` が、単なる存在として現れるこの二つの半分を、ちょうどその可縮なファイバーへ組み立てる。
<!--/-->

```agda
      fc : (c : S) → ⟨ c ∈ˢ A ⟩
         → isContr (Σ[ k ∈ S ] ⟨ (k ∷ c ∷ []) ⊨ φ ⟩)
      fc c c∈ = mereFunct φ c ∣ entry c c∈ , (holds c c∈ , only c c∈) ∣₁
```



<!--en-->
Replacement now collects the entries: over the arguments in `α`, the pairs of
each argument with its uniquely determined value form a set of the model,
presented with the assertion that it realizes exactly the class of those
pairs. This is the moment the internal hierarchy at `α` exists as a set of
`L`.
<!--zh-->
替换随即收集诸条目：遍及 `α` 中的实参，每个实参与其唯一确定的取值组成的对构成模型的一个集合，并连同「它恰实现那个对之类」的断言一起呈现。`α` 处的内部层级作为 `L` 的集合而存在的时刻，就是此刻。
<!--ja-->
置換がすぐに項目を集める。`α` の中の入力にわたって、各入力とその一意に定まる値の対がモデルの一つの集合となり、それがその対のクラスをちょうど実現するという主張とともに提示される。`α` での内部の階層が `L` の集合として存在する瞬間は、ここである。
<!--/-->

```agda
      r : isContr (SetOf (λ z → ∃[ c ∶ S ] (c ∈ˢ A) ⊓ ((z ∷ c ∷ []) ⊨ φ)))
      r = hasReplacementL A φ fc

      spec : IsHier α (r .fst .fst)
      spec z = ⇔toPath toRec fromRec
        where
```

<!--en-->
It remains to verify that the collected set realizes the recorded class. The
specification compares, member by member, membership in the collected set with
being a recorded pair; both directions of the comparison are proved separately
and joined into the pointwise equivalence.
<!--zh-->
余下的是验证：收集所得的集合确实实现被记录的类。规格逐成员比较「属于收集集合」与「是被记录的对」；比较的两个方向分别证明，再合并为逐点等价。
<!--ja-->
残るのは、集められた集合が記録されたクラスを実現することの確認である。仕様は、要素ごとに、収集された集合への所属と、記録された対であることとを比較する。比較の両方向を別々に証明し、各点の同値へ組み合わせる。
<!--/-->

```agda
        toRec : ⟨ fst z ∈ fst (r .fst .fst) ⟩ → ⟨ Recorded α (fst z) ⟩
        toRec hz = rec₁ squash₁ conv (subst ⟨_⟩ (r .fst .snd z) hz)
          where
```

<!--en-->
Reading the collected membership out: the replacement specification turns it
into a member `c` of `α` whose value at `c` satisfies the pair graph. The
elimination is legitimate because the recorded class is a proposition.
<!--zh-->
把收集集合的隶属向外读：替换的规格把它变成 `α` 的一个成员 `c`，其取值在 `c` 处满足有序对图。消去是合法的，因为被记录的类是命题。
<!--ja-->
収集された集合への所属を外へ読み出す。置換の仕様がそれを、`α` の要素 `c` で、`c` での値が順序対のグラフを満たすという形に変える。消去が正当なのは、記録されたクラスが命題だからである。
<!--/-->

```agda
          conv : Σ[ c ∈ S ] (⟨ fst c ∈ α ⟩ × ⟨ (z ∷ c ∷ []) ⊨ φ ⟩)
               → ⟨ Recorded α (fst z) ⟩
          conv (c , (c∈ , hp)) = ∣ c , (c∈ , cong fst (only c c∈ z hp)
                                            ∙ prʟ-fst c (value c c∈)) ∣₁
```

<!--en-->
For the witness, uniqueness says the value recorded at `c` equals the canonical
entry, and the canonical entry equals the model's pair of `c` with the tower at
`c`; the underlying sets follow, which is exactly what being recorded asks.
<!--zh-->
对见证而言，唯一性说在 `c` 处记录的取值等于典范条目，而典范条目等于模型的「`c` 与塔在 `c` 处取值」之对；底层集合随之而来，这正是「被记录」所要求的。
<!--ja-->
証人に対しては、一意性が、`c` で記録された値が正準な項目に等しいと言い、正準な項目はモデルの「`c` と塔の `c` での値」の対に等しくなる。基礎の集合がそれに従い、これが「記録されている」ことの要求そのものである。
<!--/-->

```agda
        fromRec : ⟨ Recorded α (fst z) ⟩ → ⟨ fst z ∈ fst (r .fst .fst) ⟩
        fromRec hz = subst ⟨_⟩ (sym (r .fst .snd z)) (map₁ conv hz)
          where
```

<!--en-->
Reading in: a recorded pair exhibits an argument below `α` with the tower
value at it; the pair graph is satisfied at the canonical entry of that
argument, and the collected set contains it.
<!--zh-->
向内读：一条被记录的对给出低于 `α` 的实参连同塔在该处的取值；有序对图在该实参的典范条目处成立，而收集集合含有这条条目。
<!--ja-->
内側へ読む。記録された対は、`α` の下の入力と塔のそこでの値を示す。順序対のグラフはその入力の正準な項目で成立し、収集された集合はその項目を含む。
<!--/-->

```agda
          conv : Σ[ c ∈ S ] (⟨ fst c ∈ α ⟩
                   × (fst z ≡ pr (fst c) (Lset (fst c))))
               → Σ[ c ∈ S ] (⟨ fst c ∈ α ⟩ × ⟨ (z ∷ c ∷ []) ⊨ φ ⟩)
```

<!--en-->
The witness converts from the recorded presentation to the graph presentation:
the argument stays, and the equality of the underlying set with the canonical
pair becomes satisfaction of the pair graph at it.
<!--zh-->
见证从被记录的呈现转换成图的呈现：实参保持不变，而「底层集合等于典范对」的等式变成有序对图在该处的满足。
<!--ja-->
証人は、記録された提示からグラフの提示へ変換される。入力はそのままで、基礎の集合が典型的な対と等しいという等式が、そこでの順序対のグラフの充足になる。
<!--/-->

```agda
          conv (c , (c∈ , eq)) = c , (c∈
            , subst (λ t → ⟨ (t ∷ c ∷ []) ⊨ φ ⟩) (sym zeq) (holds c c∈))
            where
            zeq : z ≡ entry c c∈
            zeq = Σ≡Prop (λ t → snd (isL t))
```

<!--en-->
The equality says `z` presents the same set as the canonical entry of `c`; the
pair elements are therefore equal, and `holds` transported along that path
gives satisfaction of the pair graph at `z` and `c`.
<!--zh-->
该等式说 `z` 呈现与 `c` 的典范条目相同的集合；因此两个对元素相等，把 `holds` 沿这条路径运输，便得有序对图在 `z` 与 `c` 处的满足。
<!--ja-->
この等式は、`z` が `c` の正準な項目と同じ集合を提示すると言う。したがって対の要素たちは等しく、`holds` をこのパスに沿って運べば、`z` と `c` での順序対のグラフの充足が得られる。
<!--/-->

```agda
              (eq ∙ sym (prʟ-fst c (value c c∈)))

hierL : (α : V ℓ) → ⟨ isL α ⟩ → IsOrd α → S
hierL α hα oα = hierAt α hα oα .fst
```

<!--en-->
The internal hierarchy at an ordinal is the realizing set of the induction,
presented as an element of `L`. It exists for every constructible ordinal,
which is to say: the model now contains, for each of its ordinals, a set whose
members are exactly the pairs of an ordinal below it with the tower's value
there.
<!--zh-->
某个序数处的内部层级，就是归纳所得的实现集合，呈现为 `L` 的元素。它对每个可构造序数都存在；也就是说：模型如今为它的每个序数准备了一个集合，其成员恰是「低于该序数的序数与塔在该处取值」组成的有序对。
<!--ja-->
ある順序数での内部の階層とは、帰納が作る実現集合を `L` の要素として提示したものである。それは構成可能な順序数ごとに存在する。つまり、モデルは今や、自分の各順序数に対して、「その順序数の下の順序数と塔のそこでの値」の順序対をちょうど要素とする集合を含むのである。
<!--/-->

```agda
hierL-spec : (α : V ℓ) (hα : ⟨ isL α ⟩) (oα : IsOrd α)
           → IsHier α (hierL α hα oα)
hierL-spec α hα oα = hierAt α hα oα .snd
```

<!--en-->
The specification travels with the construction: the realizing set delivered
by the induction satisfies `IsHier`{.Agda} at its ordinal, in both directions.
This is the account against which every later use of the internal hierarchy is
checked.
<!--zh-->
规格随构造同行：归纳交付的实现集合，在其序数处于两个方向上满足 `IsHier`{.Agda}。日后对内部层级的一切使用，都对照这份说明来检验。
<!--ja-->
仕様は構成とともに渡る。帰納が渡す実現集合は、その順序数で `IsHier`{.Agda} を両方向に満たす。内部の階層のその後のすべての使用は、この説明と照らして検査される。
<!--/-->

<!--en-->
## The tower satisfies the graph

The internal hierarchy was built with `graph-table`{.Agda} and
`Lset-only`{.Agda}: at each ordinal, the induction hypothesis provided the
table below, and the two lemmas turned it into a satisfied graph with a unique
value. The last statement now runs the other way. The specification
`hierL-spec`{.Agda} hands over the table conditions on the argument, and
`Lset-defines`{.Agda} feeds them to `graph-table`{.Agda}: the tower graph is
satisfied at the recorded value, and `Lset-only`{.Agda} beside it says nothing
else is. The internal graph and the meta tower therefore agree in both
directions at every constructible ordinal.
<!--zh-->
## 外部层级满足该图

内部层级是用 `graph-table`{.Agda} 与 `Lset-only`{.Agda} 建造的：在每个序数处，归纳假设供给以下的表，两条引理把它变成成立的图与唯一的取值。最后一条陈述此刻反向而行。规格 `hierL-spec`{.Agda} 交出实参上的表条件，`Lset-defines`{.Agda} 把它们喂给 `graph-table`{.Agda}：塔之图在被记录取值处成立，与之并置的 `Lset-only`{.Agda} 说别无其他满足者。于是内部之图与元层面的塔在每个可构造序数处、在两个方向上一致。
<!--ja-->
## 外部の階層はグラフを満たす

内部の階層は、`graph-table`{.Agda} と `Lset-only`{.Agda} によって作られた。それぞれの順序数で、帰納の仮定が下の表を渡し、二つの補題がそれを成立したグラフと一意な値に変える。最後の主張は、今度は逆に走る。仕様 `hierL-spec`{.Agda} が入力の上での表の条件を渡し、`Lset-defines`{.Agda} がそれを `graph-table`{.Agda} に渡す。塔のグラフは記録された値で成立し、隣にある `Lset-only`{.Agda} は、満たすものがほかにないと言う。こうして内部のグラフとメタレベルの塔は、構成可能な順序数ごとに両方向で一致する。
<!--/-->


<details open class="submodule-fold">
<summary class="submodule-fold-heading">
```agda
module _ {n : ℕ} (w b : Fin n) (γ : S ^ n) where
```
</summary>
<div class="submodule-fold-content">

```agda
  Lset-defines : IsOrd (fst (lookup b γ))
               → fst (lookup w γ) ≡ Lset (fst (lookup b γ))
               → ⟨ γ ⊨ LsetGraphAt w b ⟩
```

<!--en-->
The statement takes the ordinality of the argument and the assertion that the
recorded value is the tower at it, and concludes that the tower graph is
satisfied. It is the reading-in direction of the previous section, available at
every constructible ordinal because the internal hierarchy exists at each of
them.
<!--zh-->
陈述取实参的序数性与「被记录取值就是塔在该处的取值」的断言，结论是塔之图成立。这是上一节的向内读式，之所以在每个可构造序数处都可用，是因为内部层级在每个可构造序数处都存在。
<!--ja-->
主張は、入力の順序数性と、記録された値が塔のそこでの値であるという主張を受け取り、塔のグラフが成立すると結論する。これは前節の内向きの読みであり、構成可能な順序数ごとに内部の階層が存在するので、それぞれの場所で使える。
<!--/-->

```agda
  Lset-defines ob q = graph-table w b γ H ob
    (λ c z _ p → hier-out (fst (lookup b γ)) ob H sp c z p .snd)
    (hier-in (fst (lookup b γ)) ob H sp)
    (λ c z p → hier-out (fst (lookup b γ)) ob H sp c z p .fst)
    q
```

<!--en-->
The set named here is the internal hierarchy at the argument, and its
specification is read as the three table conditions. Correctness and
completeness are the two directions of `hier-out`{.Agda}: an entry of the
internal table has its argument below and its value the tower there, and the
canonical entry is recorded at every argument below. The domain condition is
`hier-in`{.Agda}'s counterpart: only such pairs are recorded.
<!--zh-->
此处所指名的集合是实参处的内部层级，其规格被读作三个表条件。正确性与完备性是 `hier-out`{.Agda} 的两个方向：内部表的每条目，其实参低于实参、其取值是塔在那里；且每个低于实参的实参处的正準条目都被记录。定义域条件是 `hier-in`{.Agda} 一侧的对应物：被记录的只有那样的对。
<!--ja-->
ここで名指される集合は、入力での内部の階層であり、その仕様が三つの表の条件として読まれる。正しさと完備さは `hier-out`{.Agda} の二方向である。内部の表の項目は、入力が下にあり、値が塔のそこでの値であることを示し、下のすべての入力で正準な項目が記録される。定義域の条件は `hier-in`{.Agda} の側の対応物である。記録されるのはそのような対だけである。
<!--/-->

<!--en-->
The proof names the internal hierarchy at the argument and reads its
specification in both directions. Correctness says every value the internal
table records below the argument is the tower there; completeness says the
canonical entries are recorded; the domain condition closes the table; and the
final hypothesis `q` identifies the recorded value with the tower. The four
inputs are exactly what `graph-table`{.Agda} consumes.
<!--zh-->
证明先指名实参处的内部层级，并把其规格向两个方向读出。正确性说内部表在实参以下记录的每个取值都是塔在那里；完备性说典范条目被记录；定义域条件把表封闭；最后的假设 `q` 把被记录取值同认于塔。这四项输入恰是 `graph-table`{.Agda} 所消费的。
<!--ja-->
証明は、入力での内部の階層を名指し、その仕様を両方向に読み出す。正しさは、内部の表が入力の下で記録する値がすべて塔のそこでの値であると言い、完備さは正準な項目が記録されていると言い、定義域の条件が表を閉じる。最後の仮定 `q` が、記録された値を塔と同定する。この四つの入力は、`graph-table`{.Agda} が消費するものそのものである。
<!--/-->

```agda
    where
    H : S
    H = hierL (fst (lookup b γ)) (lookup b γ .snd) ob
    sp : IsHier (fst (lookup b γ)) H
    sp = hierL-spec (fst (lookup b γ)) (lookup b γ .snd) ob
```
</div>
</details>


<!--en-->
The internal hierarchy at the argument exists because the argument is a
constructible ordinal, and its specification is exactly the membership
equivalence proved by the induction. The two facts together say that the tower
is recorded inside the model, at every stage, with nothing besides.
<!--zh-->
实参处的内部层级之所以存在，是因为实参是可构造序数；其规格恰是归纳所证明的隶属等价。两件事合起来说：塔在每一个层处都被记录在模型内部，且此外无他。
<!--ja-->
入力での内部の階層が存在するのは、入力が構成可能な順序数だからである。そしてその仕様は、帰納が証明した所属の同値そのものである。この二つの事実を合わせれば、塔がすべての段階で、モデルの内部に、ほかには何も伴わずに記録されていると言える。
<!--/-->

<!--en-->
## Recap

`approx-val`{.Agda} proves, by one membership induction on the argument, that
every value an approximation records equals the meta tower's value at that
argument, with no single-valuedness hypothesis anywhere; equality of two values
recorded at one argument is read off it directly. `Lset-only`{.Agda} and
`Lset-defines`{.Agda} are the graph's two directions against the tower, and the
second is what `hierL`{.Agda} is built from: the internal hierarchy at an
ordinal, an element of `L` whose members are exactly the pairs of an ordinal
below it with the tower's value at it, specified by the membership equivalence
proved by the induction.

The stages tabulated here are indexed by ordinals, which are sets of the
hierarchy; the universe levels of the host are size indices of types and never
index the tower.
<!--zh-->
## 小结

`approx-val`{.Agda} 通过对实参作一次沿成员归纳，证明逼近记录的每个取值都等于元层面的塔在相应实参处的取值；这里不需要任何单值性假设。在同一个实参处记录的两个取值相等，可由它直接读出。`Lset-only`{.Agda} 与 `Lset-defines`{.Agda} 给出图与塔之间的两个方向，而后者用于构造 `hierL`{.Agda}。`hierL`{.Agda} 是某个序数处的内部层级，是 `L` 的一个元素；其成员恰是「低于该序数的序数与塔在该处取值」组成的有序对。其规格是归纳所证明的隶属等价。

此处制表的层由序数索引，序数是层级的集合；宿主的宇宙层级是类型的大小指标，从不为塔索引。
<!--ja-->
## まとめ

`approx-val`{.Agda} は、入力の上の所属に沿う帰納を一回使って、近似が記録するすべての値がメタレベルの塔のその入力での値に等しいことを証明する。一価性の仮定はどこにもない。同じ入力で記録された二つの値が等しいことは、ここから直接読み出せる。`Lset-only`{.Agda} と `Lset-defines`{.Agda} は、グラフと塔の間の二方向であり、後者が `hierL`{.Agda} を作るときに使われる。`hierL`{.Agda} はある順序数での内部の階層、`L` の要素であり、その要素は「その順序数の下の順序数と塔のそこでの値」の順序対ちょうどである。仕様は、帰納が証明した所属の同値である。

ここで表にされる段階は順序数で添字づけられ、順序数は階層の集合である。ホストの宇宙レベルは型の大きさの添字であり、塔の添字になることはない。
<!--/-->