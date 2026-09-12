<!--en-->
# Models of ZF and ZFC

A bare structure becomes a model of set theory by supplying witnesses for the ZF axioms. This chapter develops that road in stages: it says what it means for a set to realize a class, proves realizers unique from an explicit extensionality argument, introduces a description operator that reads a set back off its unique existence, and assembles the axioms into a record. It closes by extending a ZF model to ZFC with the axiom of choice.

Nothing in a bare structure yet deserves the name set theory. Its membership relation need not admit an empty set, need not pair two elements, and need not gather the subsets of anything. What a universe of sets must provide is exactly what the **axioms of ZF** say, and this chapter states them. A **model of ZF** is a structure whose fields supply the axioms, so "`𝒮` satisfies ZF" means precisely that such a witness exists at `𝒮`.

The setting is fixed once here: `𝒮` is a structure over the truth algebra `hPropAlgebra ℓ`, so every equality and membership assertion in it is a proposition, and the module runs entirely at one universe level `ℓ` with its axioms living in `Type (ℓ-suc ℓ)`.
<!--zh-->
# ZF 与 ZFC 的模型

一个裸结构通过为 ZF 公理提供见证而成为集合论模型。本章分几步走完这条路：先说明集合何时实现一个类，再由显式的外延性论证证明实现者的唯一性，引入一个从唯一存在读出集合的摹状词算子，然后把公理汇成一个 record。最后加入选择公理，把 ZF 模型扩展为 ZFC 模型。

裸结构中还没有任何东西配得上「集合论」之名。它的成员关系未必容纳空集，未必能配对两个元素，也未必能聚出子集。一个集合宇宙必须提供什么，正是 **ZF 公理**所陈述的内容，本章把它们一一写出。**ZF 模型**是其字段供给这些公理的结构，因此「`𝒮` 满足 ZF」恰是说：这样的见证在 `𝒮` 处存在。

设定在此一次确定：`𝒮` 是真值代数 `hPropAlgebra ℓ` 上的结构，其中每条等词与成员断言都是命题；整个模块在同一个宇宙层级 `ℓ` 上运行，而它的公理住在 `Type (ℓ-suc ℓ)` 中。
<!--ja-->
# ZF と ZFC のモデル

公理を持たない構造は、ZF の各公理の証拠を与えることで集合論のモデルになります。本章ではこの道を段階を追って進めます。まず集合がいつクラスを実現するかを定め、明示的な外延性の議論から実現者の一意性を証明し、一意存在から集合を読み出す確定記述の演算子を導入し、公理を record にまとめます。最後に選択公理を加えて、ZF モデルを ZFC モデルへ拡張します。

裸の構造には、集合論の名に値するものはまだ何もありません。その所属関係が空集合を許すとは限らず、二つの要素を対にできるとも、何かの部分集合を集められるとも限りません。集合の宇宙が何を提供しなければならないかは、まさに **ZF 公理**の述べる通りであり、本章はそれを書き下ろします。**ZF モデル**とは、そのフィールドが公理を供給する構造であり、「`𝒮` が ZF を満たす」とは、そのような証拠が `𝒮` で存在することを意味するにすぎません。

設定はここで一度だけ確定します。`𝒮` は真理値代数 `hPropAlgebra ℓ` の上の構造であり、その中の等号と所属の主張はすべて命題です。モジュール全体が同じ宇宙レベル `ℓ` で動作し、公理は `Type (ℓ-suc ℓ)` に住みます。
<!--/-->

<!--en-->
The module signature says what kind of thing will be studied: `𝒮` is a `ZFStructure` whose truth values are propositions, that is, a structure over `hPropAlgebra ℓ`. Two consequences follow immediately. First, the structure's equality `≈ˢ` and membership `∈ˢ` return propositions with underlying types, so membership claims in this chapter are things one can inhabit with proofs. Second, the parameter `{ℓ}` is a universe level, and it stays fixed throughout: the carrier `S` lives in `Type ℓ`, while statements quantifying over all subsets of `S`, such as the axioms themselves, will land in `Type (ℓ-suc ℓ)`.
<!--zh-->
模块签名说明了要研究的对象类型：`𝒮` 是一个 `ZFStructure`，其真值为命题，即 `hPropAlgebra ℓ` 上的结构。由此立刻得到两点。其一，结构的等词 `≈ˢ` 与成员 `∈ˢ` 返回带有底层类型的命题，因此本章的成员断言都是可以用证明占据的东西。其二，参数 `{ℓ}` 是宇宙层级，全程固定：载体 `S` 住在 `Type ℓ`，而量化 `S` 全部子集的陈述，即公理本身，则落在 `Type (ℓ-suc ℓ)`。
<!--ja-->
モジュールのシグネチャは、調べる対象の種類を示します。`𝒮` は真理値が命題である `ZFStructure`、すなわち `hPropAlgebra ℓ` の上の構造です。ここから二つのことがすぐに従います。第一に、構造の等号 `≈ˢ` と所属 `∈ˢ` は基礎型をもつ命題を返すので、本章の所属の主張は証拠で満たせるものになります。第二に、パラメータ `{ℓ}` は宇宙レベルであり、全体を通して固定されます。台 `S` は `Type ℓ` に住み、`S` のすべての部分集合を量化する命題、つまり公理そのものは `Type (ℓ-suc ℓ)` に置かれます。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import FOL.ZFStructure using ( ZFStructure; module hPropStructure )

module FOL.ZFModel {ℓ} (𝒮 : ZFStructure (hPropAlgebra ℓ)) where
```

<!--en-->
Two standing choices, both exercised here. The truth algebra is the canonical `hPropAlgebra`{.Agda}: the axioms assert facts, and the book's mathematical facts live in `hProp`{.Agda}. And the constant interpretation is the canonical one from the semantics chapter: the constant domain is the carrier itself and the interpretation is `id`{.Agda}, so a constant appearing in a formula simply *is* the set it names.
<!--zh-->
两项常设选择在此启用。真值代数取典范的 `hPropAlgebra`{.Agda}：公理断言事实，而本书数学的事实就落在 `hProp`{.Agda} 中。常元解释也取语义章的典范情形：常元域就是载体自身，解释就是 `id`{.Agda}，于是公式里出现的常元就**是**它指名的那个集合。
<!--ja-->
ここで二つの常設の選択が使われます。真理値代数は正準な `hPropAlgebra`{.Agda} です。公理は事実を主張し、本書の数学的事実は `hProp`{.Agda} に住みます。定数の解釈も意味論の章の正準なものを採ります。定数域は台そのものであり、解釈は `id`{.Agda} なので、論理式に現れる定数は、まさにその名が指す集合**そのもの**です。
<!--/-->

<!--en-->
The working vocabulary for the axioms is assembled here. The syntax chapter supplies `Formula`{.Agda}, the membership symbol `∈̇`{.Agda}, and the constructors `var`{.Agda} and `con`{.Agda}; separation and replacement will take formulas as genuine inputs. The semantics chapter contributes the module `At`, which fixes a constant interpretation and exposes satisfaction for formulas at it. From the host library come `Σ≡Prop`{.Agda}, used to reduce a path of dependent pairs whose second components are propositions, the type `WellFounded`{.Agda} of well-foundedness that regularity will record, the empty type `Empty.⊥`, and propositional truncation `∥_∥₁`{.Agda} for the axiom of choice.
<!--zh-->
这里汇集公理所需的工作词汇。语法章提供 `Formula`{.Agda}、成员符号 `∈̇`{.Agda} 与构造子 `var`{.Agda}、`con`{.Agda}；分离与替换将把公式作为真正的输入。语义章贡献模块 `At`，它固定一个常元解释，并给出该解释下公式的满足关系。宿主库则提供 `Σ≡Prop`{.Agda} (用于化归第二分量为命题的依值对的路径)、正则公理将要记录的良基类型 `WellFounded`{.Agda}、空类型 `Empty.⊥`，以及选择公理所用的命题截断 `∥_∥₁`{.Agda}。
<!--ja-->
ここで公理に必要な作業用の語彙をそろえます。構文の章は `Formula`{.Agda}、所属記号 `∈̇`{.Agda}、構成子 `var`{.Agda} と `con`{.Agda} を供給し、分出と置換は論理式を本物の入力として受け取ることになります。意味論の章はモジュール `At` を提供します。これは定数解釈を一つに固定し、その解釈での論理式の充足を公開します。ホストのライブラリからは、第二成分が命題である依存対のパスを帰着させる `Σ≡Prop`{.Agda}、正則性が記録する整礎性の型 `WellFounded`{.Agda}、空の型 `Empty.⊥`、そして選択公理で使う命題の截断 `∥_∥₁`{.Agda} が来ます。
<!--/-->

```agda
open import FOL.Syntax using ( Formula; var; con; _∈̇_ )
open import FOL.Semantics (hPropAlgebra ℓ) 𝒮 using ( module At )
open import Cubical.Data.Sigma using ( Σ≡Prop )
open import Cubical.Induction.WellFounded using ( WellFounded )
import Cubical.Data.Empty as Empty
```

<!--en-->
Three openings put the names into scope. Opening the truth algebra `hPropAlgebra ℓ` names its carrier `Ω`, which is `hProp ℓ`, and its operations `⊓`{.Agda}, `⊔`{.Agda}, `⇒`{.Agda}, `⋀`{.Agda}, `⋁`{.Agda} and the falsity `⊥`{.Agda}: these are exactly the connectives and quantifiers with which the axiom statements below are phrased. Opening `hPropStructure 𝒮` brings the structure's carrier `S`, its h-set certificate, and the two truth-valued relations `≈ˢ` and `∈ˢ`, together with the Type-valued reading `∈ᵗ`{.Agda} of membership. Finally, opening `At S id`{.Agda} instantiates the satisfaction relation `_⊨_`{.Agda} at the canonical constant interpretation, where a constant denotes itself, so a free variable slot in a formula is read as membership of a specific set.
<!--zh-->
三个 open 把名字带入作用域。打开真值代数 `hPropAlgebra ℓ` 得到其载体 `Ω` (即 `hProp ℓ`) 与运算 `⊓`{.Agda}、`⊔`{.Agda}、`⇒`{.Agda}、`⋀`{.Agda}、`⋁`{.Agda} 和假值 `⊥`{.Agda}：下面的公理陈述正是用这些联结词与量词表述的。打开 `hPropStructure 𝒮` 得到结构的载体 `S`、其 h-集合性证据，以及两个真值关系 `≈ˢ` 与 `∈ˢ`，连同成员的 Type 值读法 `∈ᵗ`{.Agda}。最后，打开 `At S id`{.Agda} 在典范常元解释下实例化满足关系 `_⊨_`{.Agda}，其中常元指自身，于是公式中的自由变元槽就被读作对某个具体集合的隶属。
<!--ja-->
三つの open が名前をスコープに入れます。真理値代数 `hPropAlgebra ℓ` を開くと、台 `Ω` (すなわち `hProp ℓ`) と、演算 `⊓`{.Agda}、`⊔`{.Agda}、`⇒`{.Agda}、`⋀`{.Agda}、`⋁`{.Agda}、偽 `⊥`{.Agda} の名前が得られます。これらはまさに、以下の公理の言明が述べられるのに使う結合子と量化子です。`hPropStructure 𝒮` を開くと、構造の台 `S`、その h-集合性の証拠、真理値を返す二つの関係 `≈ˢ` と `∈ˢ`、さらに所属の Type 値の読み `∈ᵗ`{.Agda} が得られます。最後に `At S id`{.Agda} を開くと、充足関係 `_⊨_`{.Agda} が正準な定数解釈で具体化されます。そこでは定数が自分自身を指すので、論理式の自由変数の枠は、特定の集合への所属として読まれます。
<!--/-->

```agda
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁ )

open TruthAlgebra (hPropAlgebra ℓ)
open hPropStructure 𝒮

open At S id using ( _⊨_ )
```

<!--en-->
## Realizing a class as a set

Nearly every axiom to come has the same shape: *there is a set whose members are exactly the so-and-so*. Pin down the "so-and-so" first. A **class** is a propositional predicate on the carrier, `S → Ω`: something whose membership can be stated, with no promise that any set collects it. (Classes have already appeared in disguise: the restriction `𝒮 ↾ M` of the structure chapter cuts along exactly such an `M`.) This section defines when a set realizes a class, observes that realization is itself a proposition, and packages the two together.
<!--zh-->
## 把类实现为集合

接下来的公理几乎全是同一个形状：**存在一个集合，其成员恰好是如此这般者**。先把「如此这般」说清楚。**类**是载体上的命题值谓词 `S → Ω`：可以对它谈论隶属，却不保证有集合恰好收齐它的全部成员。(类在前面已经出现过：结构章的限制 `𝒮 ↾ M` 正是沿这样一个 `M` 进行的。) 本节定义集合何时实现一个类，指出实现本身是命题，并把两者打包在一起。
<!--ja-->
## クラスを集合として実現する

これから出てくる公理はほとんどすべて同じ形をしています。**ある集合が存在して、その要素がちょうどかくかくしかじかである**。まず「かくかくしかじか」をはっきりさせましょう。**クラス**とは台の上の命題値の述語 `S → Ω` のことです。所属を語ることはできますが、それを集める集合があるとは限りません。(クラスはすでに別の姿で現れています。構造の章の制限 `𝒮 ↾ M` は、まさにこのような `M` に沿って切り取る操作でした。) 本節では、集合がいつクラスを実現するかを定義し、実現そのものが命題であることを見て、両者を一つにまとめます。
<!--/-->

<!--en-->
The definition of realization is deliberately pointwise. `IsSetOf Q b` holds when for *every* element `x` of the carrier, the proposition `x ∈ˢ b` is equal, as an element of `Ω`, to the class value `Q x`. There is no formula, no syntax, and no reduction here: the comparison is direct equality of truth values. This type lives in `Type (ℓ-suc ℓ)` because it quantifies over all of `S`, matching where the axioms themselves will live.
<!--zh-->
实现的定义刻意采取逐点形式。`IsSetOf Q b` 说：对载体的**每个**元素 `x`，命题 `x ∈ˢ b` 作为 `Ω` 的元素等于类的值 `Q x`。这里没有公式、没有语法、也没有化归：比较就是真值之间的直接相等。该类型住在 `Type (ℓ-suc ℓ)`，因为它量化了整个 `S`，与公理本身所在的位置一致。
<!--ja-->
実現の定義は意図的に各点ごとの形をしています。`IsSetOf Q b` は、台の**すべての**要素 `x` について、命題 `x ∈ˢ b` が `Ω` の要素としてクラスの値 `Q x` に等しいときに成ります。ここに公式も構文も簡約もなく、比較は真理値の直接的な等式です。この型は `S` 全体を量化するため `Type (ℓ-suc ℓ)` に住み、公理そのものの住処と一致します。
<!--/-->

```agda
IsSetOf : (S → Ω) → S → Type (ℓ-suc ℓ)
IsSetOf Q b = (x : S) → (x ∈ˢ b) ≡ Q x

isPropIsSetOf : (Q : S → Ω) (b : S) → isProp (IsSetOf Q b)
isPropIsSetOf Q b = isPropΠ (λ x → isSetHProp _ _)

SetOf : (S → Ω) → Type (ℓ-suc ℓ)
```

<!--en-->
That realization is propositional, not a heavier piece of data, is checked now. The function type `(x : S) → (x ∈ˢ b) ≡ Q x` is a proposition precisely because each fiber is: `Ω` is `hProp ℓ`, and `isSetHProp` says the type of paths between two propositions packed in `hProp` is an h-set, so its identity types are propositions; `isPropΠ`{.Agda} lifts the pointwise fact to the whole function type. Hence `SetOf Q`{.Agda}, a dependent pair of a candidate set `b` and evidence `IsSetOf Q b`, still has propositional second components, a fact used repeatedly later.
<!--zh-->
实现是命题而不是更重的数据，这一点现在检验。函数类型 `(x : S) → (x ∈ˢ b) ≡ Q x` 是命题，恰因每个纤维都是命题：`Ω` 即 `hProp ℓ`，`isSetHProp` 说明 `hProp` 中两个命题之间的路径类型是 h-集合，其恒等类型因此是命题；`isPropΠ`{.Agda} 把逐点事实提升到整个函数类型。于是 `SetOf Q`{.Agda}，即候选集合 `b` 与证据 `IsSetOf Q b` 组成的依值对，其第二分量仍是命题，这一事实后面会反复使用。
<!--ja-->
実現がより重いデータではなく命題であることを、ここで確かめます。関数型 `(x : S) → (x ∈ˢ b) ≡ Q x` が命題なのは、各繊維が命題だからです。`Ω` は `hProp ℓ` であり、`isSetHProp` は `hProp` に包まれた二つの命題の間のパス型が h-集合であることを述べるので、その恒等型は命題になります。`isPropΠ`{.Agda} がこの各点の事実を関数型全体へ持ち上げます。したがって `SetOf Q`{.Agda}、つまり候補の集合 `b` と証拠 `IsSetOf Q b` の依存対は、第二成分が命題である対のままです。この事実は後で繰り返し使われます。
<!--/-->

```agda
SetOf Q = Σ[ b ∈ S ] IsSetOf Q b
```

<!--en-->
How many realizers can one class have? Under **extensionality** (sets with the same members are equal; it will be the first field of the record) the answer is at most one, in the strong, structural sense: any single realizer makes the whole type of realizers contractible. The lemma takes extensionality as an explicit input, because the record that will provide it has not been defined yet.
<!--zh-->
一个类能有几个实现者？在**外延公理** (成员相同的集合相等；它将是 record 的第一个字段) 之下，答案是至多一个，而且是结构意义上的强「至多一」：任何一个实现者都使实现者的整个类型可缩。这条引理把外延性作为显式输入，因为提供外延性的 record 此时还没有定义。
<!--ja-->
一つのクラスに実現者はいくつあり得るでしょうか。**外延性** (同じ要素をもつ集合は等しい。これは record の最初のフィールドになります) の下では、答えは高々一つであり、しかも強い構造的な意味でそうです。どれか一つの実現者が、実現者全体の型を可縮にします。この補題が外延性を明示的な入力として受け取るのは、それを提供する record がまだ定義されていないからです。
<!--/-->

<!--en-->
Given a realizer `(b , sp)`{.Agda} of the class `Q`, the contraction sends any other realizer `(b' , sp')`{.Agda} to a path into it. The path in the first component is extensionality applied to `λ x → sp x ∙ sym (sp' x)`: at each `x`, the two specifications give paths `x ∈ˢ b ≡ Q x` and `x ∈ˢ b' ≡ Q x`, and composing the first with the reverse of the second yields `x ∈ˢ b ≡ x ∈ˢ b'`, exactly what extensionality turns into `b ≡ b'`. The second component is disposed of by `Σ≡Prop`{.Agda}, which is legitimate because `isPropIsSetOf` says the specifications of any two realizers are equal. Note the argument shape: the class `Q` and one realizer are explicit inputs, so the conclusion is literally that the type `SetOf Q`{.Agda} is contractible with the given realizer as center.
<!--zh-->
给定类 `Q` 的一个实现者 `(b , sp)`{.Agda}，收缩把任何其他实现者 `(b' , sp')`{.Agda} 映到通向它的路径。第一分量的路径是把外延性用于 `λ x → sp x ∙ sym (sp' x)`：在每个 `x` 处，两条规格分别给出 `x ∈ˢ b ≡ Q x` 与 `x ∈ˢ b' ≡ Q x`，把第一条与第二条的反向复合，得到 `x ∈ˢ b ≡ x ∈ˢ b'`，外延性正是把它变成 `b ≡ b'`。第二分量由 `Σ≡Prop`{.Agda} 处理；这是合法的，因为 `isPropIsSetOf` 说明任何两个实现者的规格相等。注意论证的形状：类 `Q` 与一个实现者是显式输入，所以结论字面上就是类型 `SetOf Q`{.Agda} 以该实现者为中心可缩。
<!--ja-->
クラス `Q` の実現者 `(b , sp)`{.Agda} が与えられると、収縮は他の任意の実現者 `(b' , sp')`{.Agda} をそれへのパスに写します。第一成分のパスは、外延性を `λ x → sp x ∙ sym (sp' x)` に適用したものです。各 `x` で二つの仕様はそれぞれ `x ∈ˢ b ≡ Q x` と `x ∈ˢ b' ≡ Q x` を与え、第一のパスと第二の逆向きを合成すれば `x ∈ˢ b ≡ x ∈ˢ b'` が得られ、外延性はまさにこれを `b ≡ b'` に変えます。第二成分は `Σ≡Prop`{.Agda} で片付けます。`isPropIsSetOf` が任意の二つの実現者の仕様の相等を示すので、これが正当です。引数の形に注意してください。クラス `Q` と一つの実現者が明示的な入力であり、結論は文字通り、型 `SetOf Q`{.Agda} がその実現者を中心として可縮であることです。
<!--/-->

```agda
setOf-unique : ({a b : S} → ((x : S) → (x ∈ˢ a) ≡ (x ∈ˢ b)) → a ≡ b)
             → (Q : S → Ω) → SetOf Q → isContr (SetOf Q)
setOf-unique ext Q (b , sp) = (b , sp) , λ { (b' , sp') →
  Σ≡Prop (isPropIsSetOf Q) (ext (λ x → sp x ∙ sym (sp' x))) }
```

<!--en-->
## The description operator

`isContr`{.Agda} is the host's **unique existence**: it packages a center together with the data contracting every element to that center. So `isContr (SetOf Q)` reads: *there is exactly one set of the `Q`s*, with the center supplying a canonical witness outright. Every existence axiom below takes this form, and the payoff is immediate: given unique existence, "the set such that" is a projection. No separate classical description axiom is needed, because the center of a contraction is already data.
<!--zh-->
## 摹状词算子

`isContr`{.Agda} 是宿主的**唯一存在**：它打包一个中心，连同把每个元素收缩到该中心的数据。因此 `isContr (SetOf Q)` 读作：**恰有一个由 `Q` 者组成的集合**，而中心直接给出一个典范见证。后面的存在性公理都采用这一形式，其好处立即可见：有了唯一存在，「那个满足条件的集合」就是一次投影。不需要另加经典的描述公理，因为收缩的中心本身就是数据。
<!--ja-->
## 確定記述の演算子

`isContr`{.Agda} はホストの**一意存在**です。中心と、すべての要素をその中心へ収縮させるデータを組にしたものです。したがって `isContr (SetOf Q)` は「`Q` なるものからなる集合がちょうど一つ存在する」と読め、中心がそのまま正準な証拠を供給します。以降の存在公理はすべてこの形を取り、その見返りはすぐに現れます。一意存在があれば、「条件を満たすあの集合」は射影になります。収縮の中心がすでにデータであるため、別の古典的な記述公理は要りません。
<!--/-->

<!--en-->
The operator `℩` takes a contraction proof of `SetOf Q` and returns its center's first component, an element of `S`: with `isContr A`{.Agda} packaged as a center together with a contraction, `c .fst`{.Agda} is the center, and one more projection reaches the set itself. This is where a classical treatment would invoke a description axiom; here the passage from unique existence to a witness is pure data extraction, and it is why every axiom below is stated with `isContr`{.Agda} rather than as a truncated existence.
<!--zh-->
算子 `℩` 接受 `SetOf Q` 的收缩证明，返回其中心的第一个分量，即 `S` 的一个元素：`isContr A`{.Agda} 打包为一个中心连同收缩，`c .fst`{.Agda} 是中心，再投影一次就到达集合本身。经典处理在这里会调用描述公理；此处从唯一存在到见证的过渡是纯粹的数据提取，这也是下面每条公理都以 `isContr`{.Agda} 而非截断存在陈述的原因。
<!--ja-->
演算子 `℩` は `SetOf Q` の収縮の証拠を受け取り、その中心の第一成分、つまり `S` の要素を返します。`isContr A`{.Agda} は中心と収縮を組にしたものなので、`c .fst`{.Agda} が中心であり、もう一度射影すれば集合そのものに届きます。古典的な扱いならここで記述公理を持ち出すところですが、ここでは一意存在から証拠への移行が純粋なデータの取り出しです。以下の公理が截断された存在ではなく `isContr`{.Agda} で述べられているのは、まさにこのためです。
<!--/-->

```agda
℩ : {Q : S → Ω} → isContr (SetOf Q) → S
℩ c = c .fst .fst
```

<!--en-->
The extracted set would be useless without a way to read back what its members are, and that reading is again a projection: `℩-spec c`{.Agda} is the specification carried by the center, that is, the second component of the first component of the contraction. Together the two say: the unique set of the `Q`s exists, and `℩` hands you that set together with the certificate `x ∈ˢ (℩ c) ≡ Q x`{.Agda}. Every derived operation in the next sections consists of applying `℩` to an axiom field and quoting `℩-spec`{.Agda} as its specification.
<!--zh-->
若无法读回该集合的成员是什么，提取出的集合便毫无用处；而这个读法同样是投影：`℩-spec c`{.Agda} 就是中心所携带的规格，即收缩的第一分量的第二分量。两者合起来说：由 `Q` 者组成的唯一集合存在，而 `℩` 把这个集合连同证书 `x ∈ˢ (℩ c) ≡ Q x`{.Agda} 一并交给你。后文每个派生运算都由「把 `℩` 用于某个公理字段」与「引用 `℩-spec`{.Agda} 作为规格」组成。
<!--ja-->
取り出した集合の要素が何であるかを読み戻す手段がなければ、その集合は役に立ちません。この読み戻しもまた射影です。`℩-spec c`{.Agda} は中心が担う仕様、すなわち収縮の第一成分の第二成分です。両者を合わせると、`Q` なるものからなる一意な集合が存在し、`℩` はその集合を証書 `x ∈ˢ (℩ c) ≡ Q x`{.Agda} とともに手渡す、となります。以降の派生演算はいずれも、公理のフィールドに `℩` を適用し、`℩-spec`{.Agda} を仕様として引用するだけで構成されます。
<!--/-->

```agda

℩-spec : {Q : S → Ω} (c : isContr (SetOf Q)) → IsSetOf Q (℩ c)
℩-spec c = c .fst .snd
```

<!--en-->
## Subsets

One derived relation completes the vocabulary: `a ⊆ˢ b` when every member of `a` is a member of `b`. This is extensionality's defining comparison, read as a truth value rather than as a hypothesis of a theorem. Unlike the axioms, which will return sets, it lives in `Ω`, and it is stated with the truth algebra's universal quantifier rather than a host function type. The power set field and the choice-set form of the axiom of choice are phrased with it.
<!--zh-->
## 子集

还需要一个派生关系来补全词汇：`a ⊆ˢ b` 谓 `a` 的每个成员都是 `b` 的成员。这正是外延公理所比较的关系，只不过作为真值而非定理前提来读。与将要返回集合的公理不同，它住在 `Ω` 中，并且用真值代数的全称量词而非宿主函数类型来陈述。幂集字段与选择公理的选择集形式都将用它表述。
<!--ja-->
## 部分集合

語彙を完成させるために、派生関係がもう一つ必要です。`a ⊆ˢ b` は、`a` の各要素が `b` にも属することを表します。これは外延性が比較する関係を、定理の仮定ではなく真理値として読んだものです。集合を返すこれからの公理と違って `Ω` に住み、ホストの関数型ではなく真理値代数の全称量化子で述べられます。冪集合のフィールドも、選択公理の選択集合の形も、これを用いて述べられます。
<!--/-->

<!--en-->
The definition uses `⋀`{.Agda}, the truth algebra's universal quantification, to conjoin the implications `x ∈ˢ a ⇒ x ∈ˢ b` over all `x` in the carrier. Staying inside `Ω` matters: the result is a truth value of the structure, comparable and combinable with the other connectives, whereas a metalevel function type would not be. The Type-valued underlying implication is available too, since each `(x ∈ˢ a) ⇒ (x ∈ˢ b)`{.Agda} in `hProp` has an underlying type, but the definition keeps everything truth-valued.
<!--zh-->
定义使用 `⋀`{.Agda}，即真值代数的全称量化，把对所有载体元素 `x` 的蕴涵 `x ∈ˢ a ⇒ x ∈ˢ b` 合取起来。留在 `Ω` 内很重要：结果是一个真值，可以与其他联结词比较与组合，而元层的函数类型做不到这一点。Type 值的蕴涵也可用，因为 `hProp` 中每个 `(x ∈ˢ a) ⇒ (x ∈ˢ b)`{.Agda} 都有底层类型，但定义把一切都保持为真值。
<!--ja-->
定義は `⋀`{.Agda}、すなわち真理値代数の全称量化を用いて、台のすべての `x` にわたる含意 `x ∈ˢ a ⇒ x ∈ˢ b` を連言します。`Ω` の中に留まることが重要です。結果は構造の真理値であり、他の結合子と比較・結合できます。メタレベルの関数型にはそれができません。Type 値の含意も使えます。`hProp` の `(x ∈ˢ a) ⇒ (x ∈ˢ b)`{.Agda} には基礎型があるからです。しかし定義はすべてを真理値のまま保ちます。
<!--/-->

```agda
_⊆ˢ_ : S → S → Ω
a ⊆ˢ b = ⋀ S (λ x → (x ∈ˢ a) ⇒ (x ∈ˢ b))
```

<!--en-->
The notation `a ⊆ˢ b` will be used inside the power-set axiom and in later arguments. Its precedence is fixed here so formulas containing membership, equality, and subset have an unambiguous reading.
<!--zh-->
记号 `a ⊆ˢ b` 将用于幂集公理及后续论证。这里固定它的优先级，使同时含成员、等词与子集的式子有明确读法。
<!--ja-->
記号 `a ⊆ˢ b` は冪集合の公理と後の議論で用います。所属、等号、部分集合を同時に含む式が一意に読めるよう、ここで優先順位を定めます。
<!--/-->

```agda

infix 20 _⊆ˢ_
```

<!--en-->
## The axioms, as a record

Here is the heart of the chapter. The fields group into three kinds. First, extensionality and the existence axioms: empty set, pairing, union, separation, replacement, power set, each in the unique-existence form just prepared, so each yields its set through `℩` (infinity joins later). Second, the two formula schemas: separation and replacement take a `Formula S 1`{.Agda} or `Formula S 2`{.Agda} and interpret it with the satisfaction relation of the semantics chapter, so the language built in the first-order logic chapters does real work here. The restriction is explicit: these fields range over encoded first-order formulas, rather than arbitrary host predicates `S → Ω`. Thus every instance used here comes with object-language syntax and is interpreted by the satisfaction relation. Third, regularity: well-foundedness of the Type-valued membership relation, recorded as `WellFounded _∈ᵗ_` from the host library. The next section explains why this axiom is stated at the meta level while the others live inside the structure.
<!--zh-->
## 公理，作为 record

这里是本章的核心。字段分三类。第一类是外延性与存在性公理：空集、配对、并、分离、替换、幂集，全部采取刚准备好的唯一存在形式，因此各自经 `℩` 得到相应的集合 (无穷稍后加入)。第二类是两条公式模式：分离与替换各收一条 `Formula S 1`{.Agda} 或 `Formula S 2`{.Agda}，并用语义章的满足关系解释它，于是一阶逻辑诸章造出的语言在此真正派上用场。这里的限制是明确的：这些字段量化编码后的一阶公式，而非任意宿主谓词 `S → Ω`。因此每个实例都带有对象语言语法，并由满足关系解释。第三类是正则公理：Type 值成员关系的良基性，以宿主库的 `WellFounded _∈ᵗ_` 记录。下一节解释为何这条公理陈述在元层面，而其余公理住在结构内部。
<!--ja-->
## record としての ZF 公理

ここが本章の中心です。フィールドは三種に分けられます。第一は外延性と存在の公理、すなわち空集合、対、和集合、分出、置換、冪集合で、いずれも直前に用意した一意存在の形を取り、それぞれ `℩` を通して集合を得ます (無限は後に加わります)。第二は二つの論理式のスキーマです。分出と置換は `Formula S 1`{.Agda} または `Formula S 2`{.Agda} を受け取り、意味論の章の充足関係で解釈するので、一階論理の諸章で作られた言語がここで実際の仕事をします。ここでの制限は明示的です。これらのフィールドが量化するのは符号化された一階論理式であり、任意のホスト述語 `S → Ω` ではありません。したがって各実例は対象言語の構文を伴い、充足関係によって解釈されます。第三は正則性です。Type 値の所属関係の整礎性として、ホストのライブラリの `WellFounded _∈ᵗ_` で記録します。次の節で、なぜこの公理だけがメタレベルで述べられ、他が構造の内部に住むのかを説明します。
<!--/-->

<!--en-->
The record is a proposition-valued structure plus the guarantees the axioms demand, and it itself lives in `Type (ℓ-suc ℓ)` because its fields quantify over all of `S`. The first two fields are not of the unique-existence form. Extensionality is the implication from pointwise agreement of membership truth values to a path `a ≡ b`, exactly the hypothesis that made `setOf-unique` work. Regularity takes `WellFounded _∈ᵗ_`, well-foundedness of the Type-valued membership: this supplies `Acc` data for every element and thereby supports recursion and induction along membership. The remaining fields each assert `isContr (SetOf Q)` for a class `Q`.
<!--zh-->
这个 record 是命题值结构加上公理所要求的保证；由于字段量化了整个 `S`，它自身住在 `Type (ℓ-suc ℓ)`。头两个字段不是唯一存在形态。外延性是从成员真值逐点相等得到路径 `a ≡ b` 的蕴涵，正是让 `setOf-unique` 得以成立的那个假设。正则性取 `WellFounded _∈ᵗ_`，即 Type 值成员关系的良基性：它为每个元素提供 `Acc` 数据，从而支持沿成员关系的递归与归纳。其余字段各自对某个类 `Q` 断言 `isContr (SetOf Q)`。
<!--ja-->
この record は、命題値の構造に公理が要求する保証を加えたものです。フィールドが `S` 全体を量化するため、record 自身は `Type (ℓ-suc ℓ)` に住みます。最初の二つのフィールドは一意存在の形ではありません。外延性は、所属の真理値が各点で一致することからパス `a ≡ b` を得る含意であり、`setOf-unique` を成立させた仮定そのものです。正則性は `WellFounded _∈ᵗ_`、つまり Type 値の所属関係の整礎性です。これは各要素に `Acc` のデータを与え、所属に沿った再帰と帰納を可能にします。残りのフィールドはそれぞれ、あるクラス `Q` に対して `isContr (SetOf Q)` を主張します。
<!--/-->

```agda
record isZFModel : Type (ℓ-suc ℓ) where
  field
    extensional    : {a b : S} → ((x : S) → (x ∈ˢ a) ≡ (x ∈ˢ b)) → a ≡ b
    regularity     : WellFounded _∈ᵗ_
    hasEmpty       : isContr (SetOf (λ _ → ⊥))
```

<!--en-->
Reading each class back into words recovers the textbook statements. Nothing realizes `⊥`, so the empty set is the unique set realizing the constantly-false class. The pair of `a` and `b` realizes the class of sets structurally equal to `a` or to `b`, joined by the truth algebra's disjunction `⊔`{.Agda}. The union of `a` realizes the class of sets `x` that are members of some member `y` of `a`, conjoined by `⊓`{.Agda} and existentially gathered by `⋁`{.Agda}. Separation, the first formula-consuming field, keeps exactly those members `x` of `a` satisfying `φ`: the class is the conjunction of membership in `a` with the satisfaction of `φ` at the one-element environment `x ∷ []`, whose single entry fills the only free-variable slot of a `Formula S 1`.
<!--zh-->
把每个类读回自然语言，教科书的陈述一一重现。没有谁实现 `⊥`，所以空集就是实现恒假类的唯一集合。`a` 与 `b` 的配对实现「与 `a` 结构相等或与 `b` 结构相等」的类，用真值代数的析取 `⊔`{.Agda} 连接。`a` 的并实现那些 `x`：存在 `a` 的成员 `y` 使 `x` 属于 `y`，用 `⊓`{.Agda} 合取、`⋁`{.Agda} 存在聚合。分离是第一个消费公式的字段，恰好留下 `a` 中满足 `φ` 的成员 `x`：该类是「属于 `a`」与「`φ` 在单元素环境 `x ∷ []` 下满足」的合取，这个环境的唯一一项填入 `Formula S 1` 唯一的自由变元槽。
<!--ja-->
それぞれのクラスを自然言語に読み戻すと、教科書の言明がそのまま現れます。`⊥` を実現するものはないので、空集合とは恒偽のクラスを実現する一意な集合です。`a` と `b` の対は、「`a` と構造的に等しいか `b` と構造的に等しい」というクラスを実現し、真理値代数の選言 `⊔`{.Agda} で結ばれます。`a` の和集合は、「`a` のある要素 `y` に属する」という形の `x` のクラスを実現し、`⊓`{.Agda} で連言し、`⋁`{.Agda} で存在的に集めます。分出は最初の論理式を受け取るフィールドで、`a` の要素のうち `φ` を満たすものをちょうど残します。クラスは「`a` への所属」と「論理式 `φ` が一要素の環境 `x ∷ []` で充足されること」の連言であり、この環境の唯一の項が `Formula S 1` の唯一の自由変数の枠を埋めます。
<!--/-->

```agda
    hasPair        : (a b : S) → isContr (SetOf (λ x → (x ≈ˢ a) ⊔ (x ≈ˢ b)))
    hasUnion       : (a : S) → isContr (SetOf (λ x → ⋁ S (λ y → (y ∈ˢ a) ⊓ (x ∈ˢ y))))
    hasSeparation  : (a : S) (φ : Formula S 1)
                   → isContr (SetOf (λ x → (x ∈ˢ a) ⊓ ((x ∷ []) ⊨ φ)))
    hasReplacement : (a : S) (φ : Formula S 2)
```

<!--en-->
Replacement is the longest field and carries a hypothesis of its own. It takes a `Formula S 2`, whose two free-variable slots are read in the order given by the environment `y ∷ x ∷ []`: first the output value, then the input. The hypothesis says `φ` is *functional on `a`*: for every member `x` of `a` there is exactly one `y` satisfying `φ`, exactly-oneness being the `isContr`{.Agda} of the type of such `y`. Under that hypothesis the field asserts unique existence of the image, the set of `y` that stand in the relation `φ` to some member of `a`. Note what it does not assert: without the functionality hypothesis the field makes no claim at all, mirroring the classical restriction of replacement to functional formulas. Finally, the power set of `a` realizes the class of subsets, using the derived relation `⊆ˢ` from the previous section.
<!--zh-->
替换是最长的字段，并自带一个前提。它取 `Formula S 2`，其两个自由变元槽按环境 `y ∷ x ∷ []` 的次序读：先是输出值，再是输入。前提说 `φ` 在 `a` 上是**函数性**的：对 `a` 的每个成员 `x`，恰有一个 `y` 满足 `φ`，这个「恰一」就是由这些 `y` 组成的类型的 `isContr`{.Agda}。在该前提之下，字段断言像集的唯一存在，即与 `a` 的某个成员处于关系 `φ` 的那些 `y` 组成的集合。注意它不断言什么：没有函数性前提时，字段不作任何断言，这与经典处理中替换公理限于函数性公式的限制一致。最后，`a` 的幂集实现子集的类，用的是上一节的派生关系 `⊆ˢ`。
<!--ja-->
置換は最も長いフィールドで、それ自身の仮定を一つ持ちます。受け取るのは `Formula S 2` であり、その二つの自由変数の枠は環境 `y ∷ x ∷ []` の順で読まれます。まず出力の値、次に入力です。仮定は、`φ` が `a` の上で**関数的**であること、つまり `a` の各要素 `x` に対して `φ` を満たす `y` がちょうど一つあることです。このちょうど一つは、そのような `y` の型の `isContr`{.Agda} として表されます。この仮定の下で、フィールドは像の一意存在、すなわち `a` のある要素と関係 `φ` に立つ `y` 全体の集合を主張します。何を主張しないかにも注意してください。関数性の仮定がなければ、このフィールドは何も主張しません。これは、古典的な扱いで置換公理が関数的な論理式に限られることと対応しています。最後に、`a` の冪集合は部分集合のクラスを実現し、前節の派生関係 `⊆ˢ` を用います。
<!--/-->

```agda
                   → ((x : S) → ⟨ x ∈ˢ a ⟩ → isContr (Σ[ y ∈ S ] ⟨ (y ∷ x ∷ []) ⊨ φ ⟩))
                   → isContr (SetOf (λ y → ⋁ S (λ x → (x ∈ˢ a) ⊓ ((y ∷ x ∷ []) ⊨ φ))))
    hasPower       : (a : S) → isContr (SetOf (λ x → x ⊆ˢ a))
```

<!--en-->
Read each `λ` back into words and the familiar statements reappear. Nothing realizes `⊥`, so `hasEmpty`{.Agda} is the empty set. The pair's members are whatever equals `a` or `b`; the union's members are the members of members. Separation keeps those members of `a` that satisfy `φ` (the environment `x ∷ []` plugs the sole free variable). Replacement first asks `φ` to be functional on `a`, one output per input in the `isContr`{.Agda} sense, then collects the outputs. The power set's members are the subsets.

## Why regularity lives at the meta level

Every other axiom speaks either the object language or plain membership; regularity alone reaches for the host's notion of well-foundedness. The classical reason is that **no first-order sentence expresses external well-foundedness**: by the **compactness theorem** of classical model theory, any sentence true in exactly the well-founded structures would also hold in a structure carrying an infinite descending ∈-chain, since every finite fragment of the extended theory (a fresh constant chain $a_{n+1} \in a_n$) has a model. The book tells this argument but does not depend on it, and compactness is not developed here. The practical reason, visible in the type `WellFounded _∈ᵗ_` itself, is what this interface buys: well-foundedness as explicit data supports recursion and induction along membership. What is surrendered is that the condition is no longer visible to first-order formulas; this chapter makes no claim about how much that matters beyond what is proved below.

## The derived operations

Now `℩` turns each unique existence into an operation, and `℩-spec`{.Agda} turns it into its specification; every specification below is literally one projection. The union of a pair gives binary union, and binary union gives the **successor** `a ⁺ = a ∪ {a}` (the pair of `a` with itself is the singleton): this is von Neumann's step from one set to the next, the step the axiom of infinity will later use.
<!--zh-->
把每个 `λ` 读回自然语言，熟悉的陈述一一归位。没有谁实现 `⊥`，所以 `hasEmpty`{.Agda} 就是空集。配对的成员是与 `a` 或 `b` 相等者；并的成员是成员的成员。分离留下 `a` 中满足 `φ` 的成员 (环境 `x ∷ []` 把唯一的自由变量填上)。替换先要求 `φ` 在 `a` 上是函数性的，即在 `isContr`{.Agda} 意义下一进一出，再收集输出。幂集的成员就是子集。

## 正则公理为何置于元层面

其余公理说的要么是对象语言，要么是单纯的成员关系；唯独正则公理要借助宿主的良基概念。经典理由是：**没有任何一阶句子能表达外部良基性**。由经典模型论的**紧致性定理**，一个恰好在良基结构中成立的句子，也会在带有无穷下降 ∈-链的结构中成立，因为扩充理论 (新常元链 $a_{n+1} \in a_n$) 的每个有限片段都有模型。本书讲述这个论证但不依赖它，紧致性也不在本书展开。实践理由直接写在类型 `WellFounded _∈ᵗ_` 里：良基性作为显式数据，支持沿成员关系的递归与归纳。付出的代价是这个条件不再被一阶公式看见；除了下文证明的内容之外，本章不对这损失有多大作任何断言。

## 派生运算

现在用 `℩` 把每个唯一存在实现为运算，并用 `℩-spec`{.Agda} 给出规格；下面每条规格都是一次投影。配对之并给出二元并，二元并又给出**后继** `a ⁺ = a ∪ {a}` (`a` 与自身的配对即单点集)：这是从一个集合到下一个集合的冯·诺伊曼后继步骤，也是无穷公理稍后所用的那一步。
<!--ja-->
それぞれの `λ` を自然言語に読み戻すと、おなじみの言明が並びます。`⊥` を実現するものはないので、`hasEmpty`{.Agda} が空集合です。対の要素は `a` または `b` と等しいものであり、和集合の要素は要素の要素です。分出は `a` の要素のうち `φ` を満たすものを残します (環境 `x ∷ []` が唯一の自由変数を埋めます)。置換はまず `φ` が `a` の上で関数的であること、つまり `isContr`{.Agda} の意味で一入力一出力であることを求め、それから出力を集めます。冪集合の要素は部分集合です。

## 正則性公理をメタレベルに置く理由

他の公理はいずれも対象言語か単純な所属で語りますが、正則性公理だけはホストの整礎性の概念に頼ります。古典的な理由は、**外部の整礎性を表現する一階の文は存在しない**ことです。古典的モデル理論の**コンパクト性定理**により、ちょうど整礎な構造で成り立つ文は、無限降下の ∈-列をもつ構造でも成り立ちます。拡張された理論 (新しい定数の列 $a_{n+1} \in a_n$) の各有限断片はモデルを持つからです。本書はこの議論を語りますが、これに依存せず、コンパクト性も展開しません。実用的な理由は型 `WellFounded _∈ᵗ_` そのものに見えます。整礎性を明示的なデータとして持てば、所属に沿った再帰と帰納が使えます。代償は、この条件が一階の論理式からは見えなくなることです。その損失がどのほど重要かについて、本章は以下で証明する範囲を超えて何も主張しません。

## 公理から得られる演算

いまや `℩` がそれぞれの一意存在を演算に変え、`℩-spec`{.Agda} がそれを仕様に変えます。以下の仕様はすべて文字通り一つの射影です。対の和集合が二項の和集合を与え、二項の和集合から**後者** `a ⁺ = a ∪ {a}` が得られます (`a` と自分自身の対が一元集合です)。これは一つの集合から次の集合へ進むフォン・ノイマンの一歩であり、無限公理が後に使う一歩です。
<!--/-->

<!--en-->
Inside the record, each field becomes an operation by applying `℩` to it. The empty set is `℩ hasEmpty`, and the pairing operation `pair a b` applies `℩` to the pairing certificate at the specific `a` and `b`. Each such application is justified because the fields provide `isContr (SetOf _)`, which is precisely the input type of `℩`. The specification `pair-spec` is not a new proof at all: it quotes `℩-spec` at the same field, and its statement is exactly the realization assertion, that `x ∈ˢ pair a b` equals the disjunction `(x ≈ˢ a) ⊔ (x ≈ˢ b)` for every `x`.
<!--zh-->
在 record 内部，每个字段通过应用 `℩` 变成运算。空集就是 `℩ hasEmpty`，配对运算 `pair a b` 把 `℩` 用于特定 `a`、`b` 处的配对证书。每个应用都是合法的，因为字段提供 `isContr (SetOf _)`，恰是 `℩` 的输入类型。规格 `pair-spec` 完全不是新证明：它在同一字段上引用 `℩-spec`，其陈述恰是实现断言，即对每个 `x`，`x ∈ˢ pair a b` 等于析取 `(x ≈ˢ a) ⊔ (x ≈ˢ b)`。
<!--ja-->
record の中では、各フィールドに `℩` を適用することで演算が得られます。空集合は `℩ hasEmpty` であり、対の演算 `pair a b` は、具体的な `a` と `b` における対の証拠に `℩` を適用します。どの適用も正当です。フィールドが `isContr (SetOf _)` を提供し、それがちょうど `℩` の入力型だからです。仕様 `pair-spec` はまったく新しい証明ではなく、同じフィールドで `℩-spec` を引用したものです。その主張は実現の主張そのまま、すなわちすべての `x` について `x ∈ˢ pair a b` が選言 `(x ≈ˢ a) ⊔ (x ≈ˢ b)` に等しいことです。
<!--/-->

```agda
  ∅ : S
  ∅ = ℩ hasEmpty

  pair : S → S → S
  pair a b = ℩ (hasPair a b)

  pair-spec : ∀ a b → IsSetOf (λ x → (x ≈ˢ a) ⊔ (x ≈ˢ b)) (pair a b)
```

<!--en-->
The union operation `⋃ a` extracts the union certificate of `a`, and binary union is defined from it: `a ∪ b` is the union of the pair `pair a b`, which is exactly the set whose members are the members of `a` together with the members of `b`. No separate axiom is spent on binary union; it is a composite of pairing and union. Note the definition's direction: `∪` is built from `⋃` applied to a pair, not the reverse.
<!--zh-->
并运算 `⋃ a` 提取 `a` 的并证书，而二元并由它定义：`a ∪ b` 是配对 `pair a b` 的并，恰是「成员为 `a` 的成员与 `b` 的成员之全体」的集合。二元并不另外花费公理，它是配对与并的复合。注意定义的方向：`∪` 是由 `⋃` 作用于配对而构造，而不是相反。
<!--ja-->
和集合の演算 `⋃ a` は `a` の和の証拠を取り出し、二項の和集合はそれから定義されます。`a ∪ b` は対 `pair a b` の和集合であり、その要素は `a` の要素と `b` の要素の全体にほかなりません。二項の和集合に別の公理は使わず、対と和の合成として得られます。定義の向きに注意してください。`∪` は対に `⋃` を適用して作られるのであり、その逆ではありません。
<!--/-->

```agda
  pair-spec a b = ℩-spec (hasPair a b)

  ⋃ : S → S
  ⋃ a = ℩ (hasUnion a)

  _∪_ : S → S → S
  a ∪ b = ⋃ (pair a b)
```

<!--en-->
Separation becomes an operation in the formula itself: `separate a φ` applies `℩` to the separation certificate at `a` and the formula `φ`, so the resulting set depends on a piece of object-language syntax. Its specification again quotes `℩-spec` verbatim, giving `x ∈ˢ separate a φ ≡ (x ∈ˢ a) ⊓ ((x ∷ []) ⊨ φ)` for every `x`: membership combines belonging to `a` with satisfying `φ`. The power set operation `𝒫 a` extracts the power set certificate, and its members will be read off, via the class it realizes, as exactly the subsets of `a`.
<!--zh-->
分离成为以公式为参数的运算：`separate a φ` 把 `℩` 用于 `a` 与公式 `φ` 处的分离证书，因此所得集合依赖一段对象语言语法。其规格同样逐字引用 `℩-spec`，给出对每个 `x` 的 `x ∈ˢ separate a φ ≡ (x ∈ˢ a) ⊓ ((x ∷ []) ⊨ φ)`：成员关系由「属于 `a`」与「满足 `φ`」合成。幂集运算 `𝒫 a` 提取幂集证书；经由它实现的类读出，其成员恰是 `a` 的子集。
<!--ja-->
分出は、論理式そのものを引数とする演算になります。`separate a φ` は `a` と論理式 `φ` における分出の証拠に `℩` を適用するので、得られる集合は対象言語の構文の一部に依存します。その仕様もやはり `℩-spec` をそのまま引用し、すべての `x` について `x ∈ˢ separate a φ ≡ (x ∈ˢ a) ⊓ ((x ∷ []) ⊨ φ)` を与えます。所属とは、`a` への属することと `φ` の充足の連言です。冪集合の演算 `𝒫 a` は冪集合の証拠を取り出します。それが実現するクラスを通して読めば、その要素は `a` の部分集合ちょうどです。
<!--/-->

```agda

  separate : (a : S) → Formula S 1 → S
  separate a φ = ℩ (hasSeparation a φ)

  separate-spec : ∀ a φ → IsSetOf (λ x → (x ∈ˢ a) ⊓ ((x ∷ []) ⊨ φ)) (separate a φ)
  separate-spec a φ = ℩-spec (hasSeparation a φ)

  𝒫 : S → S
```

<!--en-->
The trailing blank line closes this block of operations; the next sections build on them, first deriving intersection without any new axiom.
<!--zh-->
末尾的空行结束这一组运算；接下来的小节将在此基础上推进，首先不借助任何新公理地导出交。
<!--ja-->
末尾の空行はこの演算のブロックを閉じます。続く節はこれらの上に築かれ、まず新しい公理を何も使わずに共通部分を導出します。
<!--/-->

```agda
  𝒫 a = ℩ (hasPower a)

```

<!--en-->
## Intersection derived from separation

Binary intersection is deliberately **not** a field. The two-symbol formula `var zero ∈̇ con b`{.Agda} says "the variable is a member of `b`"; pass it to `separate`{.Agda} at `a` and the axioms return `a ∩ b`. Its specification is exactly the separation specification, verbatim, because satisfaction of that formula computes to `x ∈ˢ b` by the defining clauses of `⊨`. This is a worked example of the general pattern: whenever a host predicate can be named by a formula, separation turns it into a set.
<!--zh-->
## 由分离导出的交

二元交刻意**不设**为字段。两个符号的公式 `var zero ∈̇ con b`{.Agda} 表示「该变量是 `b` 的成员」；把它传给 `separate`{.Agda} 并作用于 `a`，分离公理就给出 `a ∩ b`。它的规格与分离的规格完全相同，因为按 `⊨` 的定义子句，该公式的满足直接计算为 `x ∈ˢ b`。这是一般模式的一次具体运用：凡能被公式指名的宿主谓词，分离都能把它变成集合。
<!--ja-->
## 分出から導かれる共通部分

二項の共通部分は意図的にフィールドに**しません**。二つの記号からなる論理式 `var zero ∈̇ con b`{.Agda} は「その変数が `b` の要素である」と述べます。これを `a` における `separate`{.Agda} に渡せば、公理が `a ∩ b` を返します。その仕様は分出の仕様そのままであり、`⊨` の定義節によってこの論理式の充足が `x ∈ˢ b` として計算されるからです。これは一般のパターンの実例です。論理式で名指せるホストの述語は、分出によって集合にできます。
<!--/-->

<!--en-->
The definition is one line of applied syntax: `a ∩ b` separates `a` along the formula whose only content is the atomic membership statement `var zero ∈̇ con b`. Because the constant `b` denotes itself under the interpretation `id`{.Agda}, satisfying that formula at the environment `x ∷ []` reduces, by the defining clauses of satisfaction, to the truth value `x ∈ˢ b`. The specification theorem is then the separation specification at this particular formula, unchanged: membership in the intersection is the conjunction `x ∈ˢ a ⊓ x ∈ˢ b`. No new axiom and no new existence proof are spent; a two-symbol formula already names a host predicate that separation can realize.
<!--zh-->
定义是应用语法的一行：`a ∩ b` 沿着那条内容仅为原子成员断言 `var zero ∈̇ con b` 的公式分离 `a`。由于常元 `b` 在解释 `id`{.Agda} 下指自身，在环境 `x ∷ []` 下满足该公式，按满足关系的定义子句化归为真值 `x ∈ˢ b`。于是规格定理就是分离规格在该特定公式上的原样引用：交中的成员关系是合取 `x ∈ˢ a ⊓ x ∈ˢ b`。不需要新公理，也不需要新的存在性证明；一条双符号公式已经指名了分离能够实现的一个宿主谓词。
<!--ja-->
定義は構文を適用した一行です。`a ∩ b` は、内容が原子式の所属主張 `var zero ∈̇ con b` だけである論理式に沿って `a` を分出します。定数 `b` は解釈 `id`{.Agda} の下で自分自身を指すので、環境 `x ∷ []` でこの論理式を充足することは、充足関係の定義節によって真理値 `x ∈ˢ b` へと計算されます。したがって仕様定理は、この特定の論理式での分出の仕様をそのまま引用したものであり、共通部分への所属は連言 `x ∈ˢ a ⊓ x ∈ˢ b` です。新しい公理も存在の新しい証明も要りません。二つの記号からなる論理式が、分出が実現できるホストの述語をすでに名指しているのです。
<!--/-->

```agda
  _∩_ : S → S → S
  a ∩ b = separate a (var zero ∈̇ con b)

  ∩-spec : ∀ a b x → (x ∈ˢ (a ∩ b)) ≡ ((x ∈ˢ a) ⊓ (x ∈ˢ b))
  ∩-spec a b x = separate-spec a (var zero ∈̇ con b) x
```

<!--en-->
## Infinity

One axiom remains, the one that forces a genuinely infinite set into existence. The **numerals** are the von Neumann naturals: `∅`, `∅ ⁺`, `(∅ ⁺) ⁺`, and so on. The record takes the chain itself as a field, pinned down by two propositional equations phrased in raw membership and equality: the zeroth numeral has no members, and the members of a successor numeral are exactly the previous numeral and its members. By extensionality the two equations yield precisely `numeral zero ≡ ∅` and `numeral (suc n) ≡ numeral n ⁺`, so this is exactly as strong as defining the chain outright. What is gained is latitude: the equations never mention the derived `∅`{.Agda}, so a concrete model may present the chain in whatever form is most convenient to compute with on its carrier and discharge them without ever unfolding the description operator.
<!--zh-->
## 无穷

只剩无穷公理，它要求一个真正无穷的集合存在。**数码**是冯·诺伊曼自然数：`∅`、`∅ ⁺`、`(∅ ⁺) ⁺`，如此继续。record 把数码链本身作为字段，并用两条以裸成员与裸等词表述的命题方程确定它：第零个数码没有成员，后继数码的成员恰是前一个数码及其成员。由外延公理，这两条方程分别给出 `numeral zero ≡ ∅` 与 `numeral (suc n) ≡ numeral n ⁺`，所以其强度与直接定义数码链相同。方程不提及派生的 `∅`{.Agda}，因此具体模型可以采用最便于载体计算的数码链定义，并在证明方程时避免展开摹状词算子。
<!--ja-->
## 無限

残る公理は一つ、真に無限な集合の存在を強制するものです。**数項**とはフォン・ノイマンの自然数、すなわち `∅`、`∅ ⁺`、`(∅ ⁺) ⁺`、… のことです。record はこの列そのものをフィールドとして受け取り、生の所属と等号で述べた二つの命題的等式で固定します。第零の数項は要素をひとつももたず、後者の数項の要素はちょうど直前の数項とその要素です。外延性により、この二つの等式からそれぞれ `numeral zero ≡ ∅` と `numeral (suc n) ≡ numeral n ⁺` が正確に得られるので、列を直接定義するのとちょうど同じ強さです。得られるのは自由度です。等式は派生した `∅`{.Agda} をまったく言及しないため、具体的なモデルは台の上で計算に最も都合のよい形で列を提示し、確定記述の演算子を一切展開せずに等式を満たせます。
<!--/-->

<!--en-->
The chain is a function `numeral : ℕ → S`, so indexing by the host's natural numbers is explicit data. The zero case is a negative condition: any inhabitant `z` of the Type-valued membership `z ∈ˢ numeral zero` yields a contradiction, witnessed in the empty host type `Empty.⊥`. Note the reading: `∈ˢ` returns a proposition in `Ω`, `⟨_⟩` takes its underlying type, and from an inhabitant of that type the field derives absurdity. This says the zeroth numeral has no members, without mentioning the derived empty set.
<!--zh-->
数码链是函数 `numeral : ℕ → S`，用宿主自然数作索引是显式数据。零的情形是否定条件：`z ∈ˢ numeral zero` 这个 Type 值隶属的任何居民都导出矛盾，见证落在空宿主类型 `Empty.⊥` 中。注意读法：`∈ˢ` 返回 `Ω` 中的命题，`⟨_⟩` 取其底层类型，从该类型的居民出发，字段导出荒谬。这说明第零个数码没有成员，却完全未提及派生的空集。
<!--ja-->
数項の列は関数 `numeral : ℕ → S` であり、ホストの自然数による添字付けが明示的なデータになっています。零の場合は否定の条件です。Type 値の所属 `z ∈ˢ numeral zero` の任意の inhabitant は矛盾を導き、その証拠は空のホスト型 `Empty.⊥` に落ちます。読み方に注意してください。`∈ˢ` は `Ω` の命題を返し、`⟨_⟩` がその基礎型を取り、その型の inhabitant からフィールドは荒謬を導きます。これは第零の数項が要素をもたないことを述べるものであり、派生した空集合には一言も触れません。
<!--/-->

```agda
  field
    numeral      : ℕ → S
    numeral-zero : (z : S) → ⟨ z ∈ˢ numeral zero ⟩ → Empty.⊥
    numeral-suc  : (n : ℕ) (z : S)
                 → (⟨ z ∈ˢ numeral (suc n) ⟩ → ⟨ (z ∈ˢ numeral n) ⊔ (z ≈ˢ numeral n) ⟩)
```

<!--en-->
The successor case is a pair of implications, both inside the truncated-free propositional reading. The first says a member `z` of `numeral (suc n)` is a member of `numeral n` or structurally equal to it, the disjunction being the truth-algebra `⊔`{.Agda}; the second says every such member of the previous numeral, or thing equal to it, is a member of the successor. Together the two directions say the members of a successor numeral are exactly the previous numeral together with its members, which is exactly the von Neumann step, stated only with `∈ˢ` and `≈ˢ`.
<!--zh-->
后继情形是一对蕴涵，都处于无截断的命题读法之内。第一条说 `numeral (suc n)` 的成员 `z` 属于 `numeral n` 或与之结构相等，析取用真值代数的 `⊔`{.Agda}；第二条说前一个数码的每个这样的成员、以及与之相等者，都属于后继。两个方向合起来说：后继数码的成员恰是前一个数码连同其成员，这正是冯·诺伊曼步骤，仅用 `∈ˢ` 与 `≈ˢ` 陈述。
<!--ja-->
後者の場合は二つの含意の組で、どちらも截断を含まない命題の読みの中にあります。第一は、`numeral (suc n)` の要素 `z` が `numeral n` の要素であるか、それと構造的に等しいことを述べ、選言は真理値代数の `⊔`{.Agda} です。第二は、直前の数項のそのような要素、およびそれと等しいものが、後者の要素であることを述べます。両方向を合わせると、後者の数項の要素はちょうど直前の数項とその要素であり、これがまさにフォン・ノイマンの一歩で、`∈ˢ` と `≈ˢ` だけで述べられています。
<!--/-->

```agda
                 × (⟨ (z ∈ˢ numeral n) ⊔ (z ≈ˢ numeral n) ⟩ → ⟨ z ∈ˢ numeral (suc n) ⟩)
```

<!--en-->
`isNumeral`{.Agda} determines the class of objects *equal to some numeral*. The quantification runs over `ℕ` lifted to the working level, since the indexing data lives at the bottom universe. The chosen form of the **axiom of infinity** says that this exact class is a set. Consequently `ω` is characterized in both directions: every numeral belongs to it, and every member is equal to a numeral.
<!--zh-->
`isNumeral`{.Agda} 所定出的类由**与某个数码相等**的对象组成。量化取提升到工作层级的 `ℕ`，因为索引数据位于最底层宇宙。本章采用的**无穷公理**说这个确切的类是集合。因此 `ω` 得到双向刻画：每个数码都属于它，而它的每个成员都与某个数码相等。
<!--ja-->
`isNumeral`{.Agda} が定めるクラスは、**ある数項と等しい**対象からなります。添字のデータが最下層の宇宙にあるため、量化は作業レベルへ lift された `ℕ` 上を走ります。ここで採用する**無限公理**は、この正確なクラスが集合であると述べます。したがって `ω` は双方向に特徴づけられます。すべての数項がそこに属し、そのすべての要素はある数項と等しくなります。
<!--/-->

<!--en-->
The class `isNumeral` is an existential written in the truth algebra: `⋁`{.Agda} quantifies over a carrier type and disjoins the family of propositions `x ≈ˢ numeral (lower n)`. The carrier must have type `Type ℓ` for `⋁`{.Agda} to apply, but `ℕ` lives at `Type ℓ-zero`; `Lift {ℓ-zero} {ℓ} ℕ` raises it to the working level, and `lower` recovers the plain index to feed to `numeral`. This is a level adjustment, not a mathematical change: the lifted type carries exactly the same elements. The field `hasInfinity` then asserts, in the now-familiar form, unique existence of a set realizing this class.
<!--zh-->
类 `isNumeral` 是用真值代数写出的存在式：`⋁`{.Agda} 在一个载体类型上量化，析取命题族 `x ≈ˢ numeral (lower n)`。载体必须具有类型 `Type ℓ` 才能应用 `⋁`{.Agda}，而 `ℕ` 住在 `Type ℓ-zero`；`Lift {ℓ-zero} {ℓ} ℕ` 把它提升到工作层级，`lower` 取回普通索引交给 `numeral`。这是层级的调整，不是数学内容的改变：被提升的类型恰有同样的元素。字段 `hasInfinity` 随即以熟悉的形式断言：实现该类的集合唯一存在。
<!--ja-->
クラス `isNumeral` は真理値代数で書かれた存在式です。`⋁`{.Agda} は台の型の上で量化し、命題の族 `x ≈ˢ numeral (lower n)` を選言します。`⋁`{.Agda} を適用するには台の型が `Type ℓ` である必要がありますが、`ℕ` は `Type ℓ-zero` に住みます。そこで `Lift {ℓ-zero} {ℓ} ℕ` が作業レベルへ持ち上げ、`lower` が普通の添字を取り戻して `numeral` に渡します。これは宇宙レベルの調整であって数学的な変更ではありません。lift された型はまったく同じ要素を持ちます。フィールド `hasInfinity` は、おなじみの形で、このクラスを実現する集合の一意存在を主張します。
<!--/-->

```agda
  isNumeral : S → Ω
  isNumeral x = ⋁ (Lift {ℓ-zero} {ℓ} ℕ) (λ n → x ≈ˢ numeral (lower n))

  field
    hasInfinity : isContr (SetOf isNumeral)

  ω : S
```

<!--en-->
As with every other unique existence, `ω` is the centre extracted by `℩` from `hasInfinity`. Because the class realized is `isNumeral` itself, the specification `℩-spec` says every member of `ω` is equal to some numeral; that is what makes this strong form usable as the set of naturals, not merely a set into which the numerals embed.
<!--zh-->
与其他唯一存在一样，`ω` 是 `℩` 从 `hasInfinity` 取出的中心。由于被实现的类就是 `isNumeral` 本身，规格 `℩-spec` 说 `ω` 的每个成员都与某个数码相等；正是这一点使这个强形式可以直接当作自然数集来用，而不只是数码能嵌入其中的一个集合。
<!--ja-->
他の一意存在と同様に、`ω` は `℩` が `hasInfinity` から取り出す中心です。実現されるクラスが `isNumeral` そのものであるため、仕様 `℩-spec` は `ω` のすべての要素がある数項と等しいことを述べます。この強い形を自然数の集合として直接使えるのはこのためであり、数項が埋め込まれる単なる集合ではありません。
<!--/-->

```agda
  ω = ℩ hasInfinity

```

<!--en-->
## First theorems

Extensionality upgrades the whole existence machinery once and for all: by `setOf-unique`, whenever a class has a realizer, that realizer is the unique realizer, and the realizer's type is contractible with it as center. Every derived set of this chapter therefore comes with its uniqueness.

## ZFC: choice as an extension

The **axiom of choice** is taken in choice-set form: given a set `a` whose members are nonempty and pairwise disjoint, some set meets each member of `a` in exactly one point. This form is stated with membership and the derived intersection alone; its equivalence with the other formulations is model-internal mathematics, deferred until needed. Propositional truncation `∥_∥₁`{.Agda} appears around nonemptiness, the evidence of a shared point, and the existence of a choice set. Thus the axiom asserts existence without selecting witnesses globally. Keeping it as a separate extension rather than a field of the base record preserves the distinction between what ZF proves and what choice adds.
<!--zh-->
## 最初的定理

外延公理把整套存在机制一次性升级：由 `setOf-unique`，凡是有实现者的类，该实现者就是唯一实现者，且实现者类型以它为中心可缩。因此本章的每个派生集合都带有唯一性。

## ZFC：作为扩展的选择公理

这里采用选择集形式的**选择公理**：给定集合 `a`，若其成员非空且两两不交，则存在一个集合，与 `a` 的每个成员恰交于一点。该形式只用成员关系和派生的交即可陈述；它与其他形式的等价性属于模型内部的数学，留待需要时证明。命题截断 `∥_∥₁`{.Agda} 分别包住非空性、公共点证据与选择集的存在。因此公理断言存在，却不在全局选定见证。把它保持为独立的扩展而非基础 record 的字段，正好保留了 ZF 所证与选择公理所增之间的区别。
<!--ja-->
## 最初の定理

外延性は存在の機構全体を一度に引き上げます。`setOf-unique` により、実現者をもつクラスではその実現者が一意の実現者であり、実現者の型はそれを中心として可縮です。したがって本章の派生集合は、どれも一意性を伴います。

## ZFC：選択公理による拡張

**選択公理**は選択集合の形で採ります。集合 `a` の要素が空でなく互いに素であるとき、`a` の各要素とちょうど一点で交わる集合が存在する、というものです。この形は所属と派生した共通部分だけで述べられます。他の定式化との同値性はモデル内部の数学であり、必要になるまで先送りします。命題の截断 `∥_∥₁`{.Agda} は、空でないこと、共有点の証拠、選択集合の存在をそれぞれ包みます。したがって公理は存在を主張しますが、証拠を大域的に選びません。これを基礎の record のフィールドにせず独立した拡張として保つことで、ZF が証明することと選択公理が追加することの区別が保たれます。
<!--/-->

<!--en-->
The ZFC record extends rather than repeats: its first field is an entire ZF model, and the line `open ... public` re-exports all its fields, so anything provable for a ZF model applies verbatim to a ZFC model. Only after this opening does the record declare its own new field, keeping the added axiom cleanly separated from the base theory.
<!--zh-->
ZFC record 采取扩展而非重复：它的第一个字段是一整个 ZF 模型，随后 `open ... public` 一行把其全部字段再导出，于是对 ZF 模型证明的一切都逐字适用于 ZFC 模型。record 只在这之后才声明自己的新字段，使新增公理与基础理论干净地分开。
<!--ja-->
ZFC の record は繰り返すのではなく拡張します。最初のフィールドは ZF モデル全体であり、続く `open ... public` の行がそのすべてのフィールドを再エクスポートします。したがって ZF モデルに対して証明されたことは、一字違わず ZFC モデルにも当てはまります。record が自らの新しいフィールドを宣言するのはこの開きの後だけであり、追加された公理は基礎理論からきれいに分離されます。
<!--/-->

```agda
record isZFCModel : Type (ℓ-suc ℓ) where
  field
    zf : isZFModel
  open isZFModel zf public
  field
```

<!--en-->
The two hypotheses of `hasChoice` say that `a` is a family of nonempty, pairwise disjoint sets, each in the reading available here. Nonemptiness is truncated: for each member `x` of `a` there *merely* exists a `y` in it, `∥ Σ[ y ∈ S ] ⟨ y ∈ˢ x ⟩ ∥₁`, with no chosen witness. Pairwise disjointness is also truncated: if `x` and `y` are two members of `a` that *merely* share a point `z`, then `x ≡ y` holds outright. Note the shape of the disjointness premise: its conclusion is a path in the host, so the truncation of the shared-point evidence is what feeds an untruncated equality.
<!--zh-->
`hasChoice` 的两条前提说 `a` 是由非空、两两不交的集合组成的族，各自按此处可用的读法理解。非空性是截断的：对 `a` 的每个成员 `x`，**仅仅**存在其中的 `y`，即 `∥ Σ[ y ∈ S ] ⟨ y ∈ˢ x ⟩ ∥₁`，没有被选定的见证。两两不交同样截断：若 `a` 的两个成员 `x` 与 `y` **仅仅**共享一点 `z`，则 `x ≡ y` 无截断地成立。注意不交前提的形状：其结论是宿主中的路径，正是共享点证据的截断在为无截断的相等供料。
<!--ja-->
`hasChoice` の二つの仮定は、`a` が空でなく互いに素な集合の族であることを、ここで使える読み方で述べます。空でないことは截断されています。`a` の各要素 `x` に対してその中に `y` が**単に**存在する、つまり `∥ Σ[ y ∈ S ] ⟨ y ∈ˢ x ⟩ ∥₁` であり、選ばれた証拠はありません。互いに素なことも截断されています。`a` の二つの要素 `x` と `y` が点 `z` を**単に**共有するなら、`x ≡ y` は截断なしで成ります。素であるという前提の形に注意してください。その結論はホストのパスであり、共有点の証拠の截断こそが、截断されない相等に材料を供しているのです。
<!--/-->

```agda
    hasChoice :
      (a : S)
      → ((x : S) → ⟨ x ∈ˢ a ⟩ → ∥ Σ[ y ∈ S ] ⟨ y ∈ˢ x ⟩ ∥₁)
      → ((x y : S) → ⟨ x ∈ˢ a ⟩ → ⟨ y ∈ˢ a ⟩
           → ∥ Σ[ z ∈ S ] (⟨ z ∈ˢ x ⟩ × ⟨ z ∈ˢ y ⟩) ∥₁ → x ≡ y)
```

<!--en-->
The conclusion is likewise a truncated existence: there *merely* exists a choice set `c` such that for every member `x` of `a`, the intersection `c ∩ x` has exactly one element, expressed as `isContr` of the type of its elements. The inner `isContr` is not a truncation: for each `x`, it provides an element of `c ∩ x` and proves that every other such element equals it. The outer truncation applies to the existence of a suitable `c`, so the axiom supplies no distinguished choice set.
<!--zh-->
结论同样是截断的存在：**仅仅**存在一个选择集 `c`，使得对 `a` 的每个成员 `x`，交 `c ∩ x` 恰有一个元素，即其元素类型的 `isContr`。内层 `isContr` 不是截断：对每个 `x`，它给出 `c ∩ x` 的一个元素，并证明其他此类元素都与之相等。外层截断作用于合适的 `c` 的存在性，因此公理不指定某个选择集。
<!--ja-->
結論も截断された存在です。選択集合 `c` が**単に**存在し、`a` の各要素 `x` に対して共通部分 `c ∩ x` がちょうど一つの要素をもちます。これはその要素の型の `isContr` で表されます。内側の `isContr` は截断ではありません。各 `x` について `c ∩ x` の要素を一つ与え、他のそのような要素がすべてそれに等しいことを示します。外側の截断は適切な `c` の存在にかかるため、公理は特定の選択集合を指定しません。
<!--/-->

```agda
      → ∥ Σ[ c ∈ S ] ((x : S) → ⟨ x ∈ˢ a ⟩
           → isContr (Σ[ z ∈ S ] ⟨ z ∈ˢ (c ∩ x) ⟩)) ∥₁
```

<!--en-->
## Recap

A model of ZF is a record with three kinds of fields: extensionality, which makes realizers unique; unique-existence fields for empty set, pair, union, separation, replacement and power set, with separation and replacement restricted to the book's own formulas; and regularity, stated at the meta level as host well-foundedness of membership, so that recursion and induction along membership are available. `℩` turns fields into operations whose specifications are projections; binary union and successor are composites, and intersection was obtained from separation plus a two-symbol formula whose satisfaction computes directly. Infinity enters as the numeral chain, a function `ℕ → S` fixed by raw membership equations, and the strong form makes `ω` a set all of whose members are numerals. `isZFCModel`{.Agda} adds choice on top, with truncated nonemptiness and shared-point evidence, a truncated conclusion, and an untruncated `isContr` for each chosen intersection.
<!--zh-->
## 小结

ZF 模型是一个含三类字段的 record：外延性，它使实现者唯一；空集、配对、并、分离、替换、幂集的唯一存在字段，其中分离与替换限于本书自己的公式；以及正则性，作为宿主对成员关系的良基性陈述在元层面，从而沿成员关系的递归与归纳可用。`℩` 把字段转为运算，其规格都是投影；二元并与后继是复合，交则由分离加一条满足关系直接计算的双符号公式得到。无穷以数码链进入，即由裸成员方程确定的函数 `ℕ → S`；强形式使 `ω` 成为成员全为数码的集合。`isZFCModel`{.Agda} 在此之上添加选择公理，其中非空性与公共点证据截断，结论也截断，而每个所选交集的 `isContr` 不截断。
<!--ja-->
## まとめ

ZF モデルは三種のフィールドをもつ record です。実現者を一意にする外延性。空集合、対、和集合、分出、置換、冪集合の一意存在のフィールドで、分出と置換は本書自身の論理式に限ります。そして正則性は、所属のホストの整礎性としてメタレベルで述べられ、所属に沿った再帰と帰納が使えます。`℩` はフィールドを演算に変え、その仕様は射影です。二項の和集合と後者は合成であり、共通部分は分出と、充足が直接計算される二つの記号の論理式から得られました。無限は数項の列、すなわち生の所属の等式で固定される関数 `ℕ → S` として入り、強い形は `ω` を要素がすべて数項である集合にします。`isZFCModel`{.Agda} はその上に選択公理を加えます。空でないことと共有点の証拠は截断され、結論も截断されますが、各共通部分についての `isContr` は截断されません。
<!--/-->
