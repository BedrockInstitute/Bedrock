<!--en-->
# Subcode-closed domains

A domain of formula codes is closed under immediate subformula codes when every constructor key it contains brings along the formula subcodes that its constructor demands; the atomic constructors and bottom carry no such obligations, since their term and numeral components are not demands of `closedAt`. This chapter explains why such a demand is needed and what it says. The subcode clauses of `L.Coding.Expressions` constrain a table only where the codes they consult actually carry entries, so a table satisfying all ten of them can be almost empty; what pins a value is a property of the index set itself, and the closure predicate `closedAt` states exactly that property as a single object-language formula. The chapter builds the predicate from two quantifier frames, one for binary and one for unary constructors, instantiates three payload relations to obtain its seven clauses, and proves both directions between satisfaction of those clauses and meta-level closure data: eliminations that read a satisfied clause into the subcodes it demands, and introductions that assemble satisfaction from such membership data. Once available, `closedAt` supports structural induction over codes stored inside `L`.
<!--zh-->
# 对子码封闭的定义域

若一个公式码定义域中每个构造子键都带有其构造子所要求的公式子码，就称它对直接子公式码封闭；两个原子构造子与底不承担这类义务，因为它们的词项分量与数码分量不是 `closedAt` 的义务。本章解释为什么需要这项要求、以及它说了什么。`L.Coding.Expressions` 中的诸子码子句只在它所查询的码确实带有条目之处约束一张表，因此满足全部十条子句的表可以几乎为空；真正确定取值的是索引集自身的一个性质，而封闭谓词 `closedAt` 恰把这个性质表述为一条对象语言公式。本章用两个量化框架 (二元构造子一个、一元构造子一个) 构造该谓词，实例化三条载荷关系得到其七条子句，并证明这些子句的满足与元层面封闭数据之间的两个方向：把已满足的子句读回其所要求子码的消去，以及从这类隶属数据拼装满足的引入。此后，`closedAt` 便可支持对 `L` 内存储的码作结构归纳。
<!--ja-->
# 部分符号に閉じた定義域

論理式の符号の定義域は、そこに含まれる各構成子のキーが、その構成子の要求する部分論理式符号を伴うとき、直下の部分論理式符号に閉じています。2 つの原子構成子と底はこのような義務を負いません。それらの項や数項の成分は `closedAt` の義務ではないからです。本章は、この要求がなぜ必要か、そして何を述べているかを説明します。`L.Coding.Expressions` の部分符号の節は、参照する符号が実際にエントリを持つ場所でしか表を拘束しないため、十個の節すべてを満たす表がほとんど空でありえます。値を定めるのは索引集合自身の性質であり、閉性述語 `closedAt` はまさにその性質を一つの対象言語の論理式として述べます。本章は、2 項構成子用と 1 項構成子用の 2 つの量化フレームからこの述語を組み立て、3 つのペイロード関係を具体化して七つの節を得て、それらの節の充足とメタレベルの閉性データとの両方向を証明します。充足された節をその要求する部分符号へと読み出す除去と、そのような所属データから充足を組み立てる導入です。これが揃えば、`closedAt` は `L` 内に保存された符号についての構造帰納法を支えます。
<!--/-->

<!--en-->
The chapter begins with a defect in what the coding clauses already say. In `L.Coding.Expressions`, each compound constructor came with a clause tying a table's entry at a code to entries at its immediate subcodes. Such a clause constrains a table only where the codes it consults actually carry entries, so a table can satisfy all ten clauses while being almost empty: take the index set to be a single **compound** code, put one entry there with any value at all, and every clause that looks for an entry at a subcode goes vacuous, since the subcodes carry no entry. The clauses alone do not pin a value. What pins it is a demand on the index set itself, that it contain the immediate subformula codes of each of its members. That demand, stated as a formula of the object language, is the closure predicate `closedAt` built in this chapter.
<!--zh-->
本章从一个缺陷开始，即已有编码子句的一个漏洞。在 `L.Coding.Expressions` 中，每个复合构造子都带有一条子句，把表在某个码处的条目与其直接子码处的条目联系起来。这类子句只在它所查询的码确实带有条目之处起约束作用，因此一张表可以在几乎为空的情况下满足全部十条子句：取索引集为单独一个**复合**码，在该处放一个值任取的条目，则所有查找子码条目的子句都空洞成立，因为诸子码没有条目。诸子句本身不能确定任何取值；真正起决定作用的是对索引集本身的一项要求：它须含有其每个成员的直接子公式码。这项要求以对象语言的公式表述，就是本章构造的封闭谓词 `closedAt`。
<!--ja-->
本章は、既存の符号化の節が持つ欠陥から始まります。`L.Coding.Expressions` では、各複合構成子に、ある符号での表のエントリをその直接の部分符号でのエントリと結びつける節が付いていました。この種の節は、参照する符号が実際にエントリを持つ場所でしか拘束力を持たないため、ほとんど空の表でも十個の節すべてを満たせます。索引集合をただ一つの**複合**符号とし、そこに任意の値のエントリを一つ置けば、部分符号のエントリを探す節はすべて空洞に成立します。部分符号がエントリを持たないからです。節だけでは値は定まりません。値を定めるのは索引集合自身への要求、すなわちその各メンバーの直接の部分論理式符号を含むという要求です。この要求を対象言語の論理式として述べたものが、本章で構成する閉性述語 `closedAt` です。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
```

<!--en-->
The counterexample also shows what would go wrong without repair. The entry sits at a compound code, and closure is precisely the property the empty subcodes cannot fake: if the index set contains a compound code, it must contain the subcodes that code decodes into. Compound matters here. Put the single entry at the code of the bottom formula `⊥̇` instead, and the clause for `⊥̇` pins the value outright, because that clause makes no subcode lookup at all. That small failure is the shape of the whole argument in miniature.
<!--zh-->
这个反例也显示了不修复会如何出错。条目位于一个复合码处，而封闭性恰恰是空子码无法伪装的性质：若索引集含有某个复合码，它就必须含有该码解码出的那些子码。「复合」在此要紧。若把那个条目改放在底公式 `⊥̇` 的码处，`⊥̇` 的子句便会立刻确定取值，因为该子句根本不做任何子码查找。这个小失败正是整个论证的缩影。
<!--ja-->
この反例は、修復しなければ何が誤るかも示します。エントリは複合符号に置かれており、閉性こそが空の部分符号では偽れない性質です。索引集合がある複合符号を含めば、その符号が解読される部分符号も含まねばなりません。「複合」であることがここで要になります。その一つのエントリを底の論理式 `⊥̇` の符号に置き換えると、`⊥̇` の節は部分符号の参照をまったく行わないため、値が即座に確定します。この小さな失敗が、議論全体の縮図です。
<!--/-->

```agda

module L.Coding.Closure {ℓ : Level} where
```

<!--en-->
The repair is a quantifier pattern, and it needs the same two frames as the clauses, minus the table. What remains is the shape reader and the implication: for every key of that shape in the set, such and such keys are in the set too. A key is an arity paired with a code, so a subkey is built either from the same arity, or from its successor for the four constructors that bind a variable. The bounded universal ranges over members of the set, the further universals range over the decoded parts, and the implication guards the demand behind the shape check.
<!--zh-->
修复是一个量化模式，所需的框架与诸子句相同，只是去掉了表。剩下的是形状读式与那个蕴含：对集合中每个该形状的键，某某几个键也在该集合中。一个键是元数与码之对，故一个子键或由同一个元数造出，或对绑定变元的四个构造子由其后继造出。有界全称遍历集合的成员，其余全称遍历解码出的各部分，而蕴含把要求置于形状检查之后。
<!--ja-->
修復は量化のパターンであり、それを述べるのに必要なのは、節と同じ 2 つのフレームから表を取り除いたものです。残るのは形状の読み手と含意です。その形状の鍵が集合にあるならば、かような鍵もまた集合にある、と。鍵はアリティと符号の対なので、部分鍵は同じアリティから、あるいは変数を束縛する 4 つの構成子についてはその後者から作られます。有界全称は集合のメンバーを走り、さらに全称は解読された各部分を走り、含意が要求を形状の検査の後ろに置きます。
<!--/-->

```agda

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax
  using ( Formula; var; _∧̇_; _⇒̇_; ∀̇_; ∀̇∈; ∃̇_ )
```

<!--en-->
The demands split into two shapes. The three binary connectives each contribute two formula children at the same arity; the two unbounded quantifiers contribute one child at the successor arity, and the two bounded quantifiers follow only their second, formula component at that same higher level, because their first component is a term. That gives seven constructors with an obligation. The two atoms and bottom add none: their term and numeral components are not obligations of `closedAt`, and bottom is pinned by its own clause as in the counterexample.
<!--zh-->
这些要求分为两种形状。三个二元联结词各贡献两个同元数的公式子码；两个无界量词贡献一个后继元数处的公式子码；两个有界量词只跟随其**第二个**、即公式分量，处在同一后继元数处，因为其第一个分量是词项。这给出七条义务。两个原子与底不添加任何义务：它们的词项与数码分量不是 `closedAt` 的义务，而底如反例所示由其自己的子句直接确定。
<!--ja-->
要求は 2 つの形に分かれます。3 つの二項結合子はそれぞれ同じアリティの論理式の子を 2 つ要求し、2 つの非有界量詞は後続アリティで 1 つの子を要求し、2 つの有界量詞はその同じ高いアリティで**第 2** 成分 (論理式) だけを追います。第一成分は項だからです。これで義務を持つ構成子は 7 つです。2 つの原子式と底は何も加えません。それらの項や数項の成分は `closedAt` の義務ではなく、底は反例で見たとおり自身の節が直接確定させます。
<!--/-->

```agda
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Coding {ℓ} using ( pr )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans )
open import L.Axioms.Numerals {ℓ} using ( sucʟ; sucʟ-fst )
```

<!--en-->
A relation to state in a frame is a parameter, and the seven concrete clauses arise by instantiating that parameter. Three instantiations cover the classification above: a same-arity demand for both components, a same-arity demand for one component, and a successor-arity demand in which the higher arity is supplied existentially. Each is a plain object-language formula over the extended environment that the frame itself opens.
<!--zh-->
框架中陈述的关系是一个参数，七条具体子句由实例化该参数而来。三种实例化覆盖上述分类：对两个分量的同元数要求、对一个分量的同元数要求，以及以存在量词给出更高元数的后继元数要求。每条都是框架自身打开的扩张环境上的一个朴素对象语言公式。
<!--ja-->
フレームの中で述べられる関係はパラメータであり、七つの具体的な節はそのパラメータの具体化として得られます。上の分類は 3 つの具体化で尽くされます。両成分に対する同アリティの要求、一成分に対する同アリティの要求、そしてより高いアリティを存在量化で与える後続アリティの要求です。いずれも、フレーム自身が開く拡張環境の上の素朴な対象言語の論理式です。
<!--/-->

```agda

open import Cubical.Data.Nat using ( _+_ )
```

<!--en-->
The existentially supplied successor is the one place where mere existence appears. Inside the arity-raising relations, the bound variable is witnessed to be the successor of the frame's arity, and that witness is packaged only truncated: the proposition records existence without retaining a chosen witness as data. Later the readers of these clauses discharge the truncation, which is legitimate because the membership claims they feed are propositions.
<!--zh-->
以存在量词给出的后继是唯一出现「仅仅存在」之处。在抬升元数的那些关系内部，约束变元被见证为框架元数的后继，而这个见证只以截断形式打包：这个命题记录后继的存在，却不把选定的见证保留为数据。后文这些子句的读式会消去该截断；这是合法的，因为它们所输送的隶属主张都是命题。
<!--ja-->
存在量化で与えられる後続こそ、命題的切り詰められた存在が現れる唯一の場所です。アリティを上げる関係の内部では、束縛変数がフレームのアリティの後続であることが証人され、その証人は切り詰めのかたちでだけ残ります。残るのは後続が存在することであり、選ばれた証人をデータとして保持しません。後ほど、これらの節の読み手が切り詰めを解消します。入力となる所属の主張が命題であるため、その解消は正当です。
<!--/-->

```agda
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁ )
```

<!--en-->
Everything is stated at the level of sets and membership. A code stored in `L` is read as an element of the cumulative hierarchy; the subcode demand is literally a list of membership statements, a pair `pr` pairing an arity with a payload being a member of the domain set. This is what makes the predicate transportable: satisfaction of an object-language formula about membership, nothing more.
<!--zh-->
一切都在集合与隶属的层面陈述。存于 `L` 中的码被读作累积层级的一个元素；子码要求在字面上就是一列隶属陈述：由 `pr` 把元数与载荷配成的对属于定义域集合。这正是该谓词可被传递的原因：它只是关于隶属的对象语言公式的满足，别无其他。
<!--ja-->
すべては集合と所属のレベルで述べられます。`L` に保存された符号は累積階層の要素として読まれ、部分符号の要求は文字通り所属の主張の並びです。`pr` がアリティとペイロードを組んだ対が定義域の集合に属する、という主張です。これが述語を輸送可能にする理由です。所属についての対象言語の論理式の充足、それだけです。
<!--/-->

```agda
open import Cubical.HITs.CumulativeHierarchy.Base using ( _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Constructions using ( module InfinitySet )
open InfinitySet using ( #_; sucV )
```

<!--en-->
The formulas are evaluated over the carrier `S` of `L`, in an environment `γ : S ^ n` of `n` carriers for a formula of arity `n`. Satisfaction here means satisfaction in the restricted structure over `L`; the satisfaction relation of the ambient hierarchy is kept under a separate name, so the two readings never blur. The frames extend such an environment by the slots they bind, which is why their arities are shifted sums like `4 + n`.
<!--zh-->
这些公式在 `L` 的载体 `S` 上、于环境 `γ : S ^ n` 中求值，该环境为元数 `n` 的公式提供 `n` 个载体。这里的满足指 `L` 上受限结构中的满足；外围层级的满足关系另用其名，两种读法不会混淆。各框架以自身约束的槽扩张这样的环境，因此其元数是 `4 + n` 这类移位后的和。
<!--ja-->
論理式は `L` の台 `S` の上で、アリティ `n` の論理式のための `n` 個のキャリアからなる環境 `γ : S ^ n` の中で評価されます。ここでの充足は `L` 上の制限された構造での充足を意味し、周囲の階層の充足関係は別の名前を保つため、二つの読み方が混ざることはありません。各フレームは自分が束縛するスロットで環境を延長するため、そのアリティは `4 + n` のようなずらした和になります。
<!--/-->

```agda

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ using ( S )
```

<!--en-->
Inside an extended environment, each frame names its own slots by de Bruijn indices counted from the inside out. The binary frame binds four slots, payload, payload, arity, code, so its code sits at the outermost index; the unary frame binds three. Shifting maps push the ambient variables of the original `n` past the bound slots, so a variable that named a value outside the frame still names that same value inside the quantified body.
<!--zh-->
在扩张环境中，每个框架用从内向外数的 de Bruijn 索引命名自己的槽。二元框架约束四个槽：载荷、载荷、元数、码，故码位于最外层索引；一元框架约束三个。移位映射把原 `n` 个环境变元推过被约束的槽，使框架外指称某值的变元在被量化的公式体内仍指同一个值。
<!--ja-->
拡張環境の中では、各フレームは自分のスロットを内側から外側へ数える de Bruijn のインデックスで名指します。2 項フレームはペイロード、ペイロード、アリティ、符号の 4 スロットを束縛し、符号は最も外側のインデックスにあります。1 項フレームは 3 スロットです。シフト写像は元の `n` 個の環境変数を束縛スロットの先へ押しやり、フレームの外で値を指していた変数が量化された本体の中でも同じ値を指すようにします。
<!--/-->

```agda

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL using ( _^_ ) renaming ( _⊨ᵐ_ to _⊨_ )
```

<!--en-->
Four object-language readers supply the building blocks, each with an adequacy proof equating its satisfaction with the meta-level claim it reads. One reads membership in the set stored at an environment slot; two check that a code is the tagged pair of an arity with its one or two payload components; one expresses having the successor of a stored arity as a payload. With shape, membership, and successor all readable inside the object language, the whole closure demand collapses into one formula, and the rest of the chapter unfolds what that formula says and how to satisfy it.
<!--zh-->
四个对象语言读式提供构件，每个读式都带有一条充分性证明，把它的满足等同于它所读取的元层面主张。一个读取「属于某环境槽中存储的集合」；两个检查某个码确是元数与其一个或两个载荷分量的带标记对；一个表达「以某存储元数的后继作为载荷」。形状、隶属与后继都能在对象语言内部读取后，整个封闭要求便收缩为一个公式；本章其余部分展开这个公式说了什么、以及如何满足它。
<!--ja-->
4 つの対象言語の読み手が構成要素を供給し、それぞれに、その充足を読み取り先のメタレベルの主張と同一視する妥当性証明が付きます。一つは環境スロットに保存された集合への所属を読み、二つはある符号がアリティとその 1 つまたは 2 つのペイロード成分のタグ付きの対であることを確認し、一つは保存されたアリティの後続をペイロードとして持つことを表します。形状・所属・後続がすべて対象言語の内部で読めるようになれば、閉性の要求全体が一つの論理式に収まります。本章の残りは、この論理式が何を言うか、そしてどう充足するかを展開します。
<!--/-->

```agda

open import L.Coding.Model {ℓ} using ( appAt; appAt-adequate )
open import L.Coding.Expressions {ℓ}
  using ( arityTagAtL; arityTagAtL-adequate; arityTagPairAtL; arityTagPairAtL-adequate
        ; sucAtL; sucAtL-adequate )
```

<!--en-->
## A domain that is closed under subcodes

The closure demand of the previous section is a quantified statement about decoded keys, and this section builds the two formulas that express it. The only classification needed is by shape: a decoded key of a unary constructor exhibits three witnesses, the code, the arity, and one payload component, while a decoded key of a binary constructor exhibits a fourth, the second component. A frame quantifying over a decoded key therefore quantifies over three values in the unary case and four in the binary case, and the obligations of the seven active constructors attach to these two frames.
<!--zh-->
## 对子码封闭的定义域

上一节得到的封闭要求是关于解码后键的量化陈述，本节构造表达它的两条公式。唯一需要的分类按形状划分：一元构造子的解码键给出三个见证，即码、元数与一个载荷分量；二元构造子的解码键多给一个，即第二个分量。因此量化解码键的框架在一元情形量化三个值，在二元情形量化四个值，七条有效构造子的义务就挂在这两个框架上。
<!--ja-->
## 部分符号に閉じた定義域

前節で得た閉性の要求は、解読されたキーについての量化された主張であり、本節はそれを表す 2 つの論理式を構成します。必要な分類は形によるものだけです。1 項構成子の解読されたキーは、符号・アリティ・一つのペイロード成分という 3 つの証人を示し、2 項構成子のキーは第 2 成分を加えた 4 つを示します。したがって解読されたキーを量化するフレームは、1 項では 3 つの値を、2 項では 4 つの値を量化することになり、有効な 7 つの構成子の義務はこの 2 つのフレームに掛かります。
<!--/-->

<!--en-->
The closure demand to be formalized is a quantified statement about decoded keys. Fix an index `C` and let `Cset` be the set stored there. It reads: for every code `c` in `Cset`, if `c` decodes as an arity `ar` tagged with the constructor numeral `k` and carrying payload components, then a relation `rel` holds of those data. How many payload components there are depends on the constructor's shape. A decoded key of a unary constructor exhibits three witnesses, the code, the arity, and one component; a decoded key of a binary constructor exhibits four, adding the second component. So two frames are needed, one quantifying three values and one quantifying four.
<!--zh-->
要形式化的封闭要求是关于解码后键的一个量化陈述。固定索引 `C`，记 `C` 处存储的集合为 `Cset`。它说的是：对 `Cset` 中每个码 `c`，若 `c` 解码为带构造子数码 `k` 标记的元数 `ar` 并带有载荷分量，则关系 `rel` 对这些数据成立。载荷分量的个数取决于构造子的形状。一元构造子的解码键给出三个见证：码、元数与一个分量；二元构造子的解码键给出四个，再加第二个分量。因此需要两个框架，一个量化三个值，一个量化四个值。
<!--ja-->
形式化すべき閉性の要求は、解読されたキーについての量化された主張です。インデックス `C` を固定し、そこに保存された集合を `Cset` とします。これは次のように読めます。`Cset` の各符号 `c` について、`c` が構成子の数 `k` をタグに持つアリティ `ar` として解読され、ペイロード成分を伴うならば、関係 `rel` がこれらのデータについて成り立つ、と。ペイロード成分の個数は構成子の形で決まります。1 項構成子の解読されたキーは符号・アリティ・一つの成分という 3 つの証人を示し、2 項構成子のキーは第 2 成分を加えた 4 つを示します。そこで、3 つの値を量化するフレームと 4 つの値を量化するフレームの 2 つが要ります。
<!--/-->

```agda
module _ {n : ℕ} where
```

<!--en-->
Both frames live at an ambient free-variable count `n`: they quantify inside an environment of length `n` and extend it by the slots they bind themselves, four for the binary frame and three for the unary one. An ambient variable must survive this extension unchanged, so a shift like `sh4` sends each of the `n` indices past the freshly bound slots. Inside the quantified body it then names the same value it named outside.
<!--zh-->
两个框架都处在环境自由变元个数 `n` 之下：它们在长度为 `n` 的环境内量化，并追加自身约束的槽，二元框架四个，一元框架三个。环境变元必须在这一扩张中保持不变，故 `sh4` 这样的移位把 `n` 个索引逐一推过新约束的槽；在被量化的公式体内，它所指的仍是外面指的那个值。
<!--ja-->
両方のフレームは周囲の自由変数の個数 `n` のもとで働きます。長さ `n` の環境の中で量化し、自分が束縛するスロットを追加します。2 項フレームで 4 つ、1 項フレームで 3 つです。周囲の変数はこの拡張で不変のままでなければならないため、`sh4` のようなシフトは `n` 個のインデックスをそれぞれ新しく束縛されたスロットの先へ送ります。量化された本体の中でも、それは外で指していたのと同じ値を指します。
<!--/-->

```agda
  private
    sh4 : Fin n → Fin (4 + n)
    sh4 i = suc (suc (suc (suc i)))
```

<!--en-->
Inside the extended environment the frame's own values must be addressable, and de Bruijn numbering does this with the innermost variable at `0`. For the binary frame that puts the two payload components at the two innermost slots, the arity next, and the code outermost of the four. These four names are what let the frame's body point at exactly the value playing each role, however deeply the frame is nested.
<!--zh-->
在扩张环境中，框架自身的值必须可被指称，de Bruijn 编号以最内层变元为 `0` 做到这一点。对二元框架而言，两个载荷分量占据最内层的两个槽，元数次之，码是四者最外层。正是这四个名字使框架的公式体能准确指到扮演每个角色的那个值，无论框架嵌套多深。
<!--ja-->
拡張された環境の中では、フレーム自身の値が参照可能でなければなりません。de Bruijn 番号は最内の変数を `0` とすることでこれを実現します。2 項フレームでは、2 つのペイロード成分が最内の 2 スロットを占め、次がアリティ、符号が 4 つのうち最も外側です。この 4 つの名前があるからこそ、フレームの本体は、フレームがどれほど深くネストしていても、各役割を担う値そのものを正確に指せるのです。
<!--/-->

```agda

    c4 n4 a4 b4 : Fin (4 + n)
    c4 = suc (suc (suc zero))
    n4 = suc (suc zero)
    a4 = suc zero
    b4 = zero
```

<!--en-->
The unary frame binds one slot fewer, so its shift moves ambient variables past three slots instead of four; everything else about the extension is the same.
<!--zh-->
一元框架少约束一个槽，故其移位把环境变元推过三个槽而非四个；扩张的其余方面完全相同。
<!--ja-->
1 項フレームは束縛スロットが一つ少ないため、そのシフトは周囲の変数を 4 つではなく 3 つのスロットの先へ動かします。拡張のそれ以外の部分は同じです。
<!--/-->

```agda

    sh3 : Fin n → Fin (3 + n)
    sh3 i = suc (suc (suc i))
```

<!--en-->
Its three bound slots follow the same inside-out order: the single payload component innermost, then the arity, then the code. With both frames fixed once, every clause built on the binary shape reuses the four-slot layout and every clause built on the unary shape reuses the three-slot layout, so the quantifier structure of the closure statement is written down twice in total.
<!--zh-->
其三个被约束槽遵循同样的由内向外的次序：唯一载荷分量最内，元数次之，码最外。两个框架各固定一次之后，凡建立在二元形状上的子句都复用四槽布局，凡建立在一元形状上的子句都复用三槽布局，于是封闭陈述的量化结构总共只写两遍。
<!--ja-->
その 3 つの束縛スロットも同じ内側から外側への順序に従います。唯一のペイロード成分が最内、次がアリティ、そして符号です。両方のフレームを一度ずつ固定すれば、2 項の形に基づく節はすべて 4 スロットの配置を、1 項の形に基づく節はすべて 3 スロットの配置を再利用します。閉性の主張の量化構造は合計 2 回書かれるだけで済みます。
<!--/-->

```agda

    c3 n3 a3 : Fin (3 + n)
    c3 = suc (suc zero)
    n3 = suc zero
    a3 = zero
```

<!--en-->
`binShapeAt` is the binary frame itself, the closure demand minus any table. Its quantifier structure is exact: a bounded universal first chooses `c` from the domain `C`, then three further values `ar`, `a`, and `b` are quantified; under the hypothesis that the pair reader certifies `c` to be the tagged pair of arity `ar` with tag `k` and payload `a`, `b`, the relation `rel` must hold in the extended environment `b ∷ a ∷ ar ∷ c ∷ γ`. The relation is a parameter, so each clause instantiates the same frame with its own payload demand.
<!--zh-->
`binShapeAt` 就是二元框架本身，即去掉表的封闭性要求。它的量词结构是精确的：先由一个有界全称从定义域 `C` 中选出 `c`，然后量化另外三个值 `ar`、`a`、`b`；在配对读式证明 `c` 确实是元数 `ar` 与标签 `k` 及载荷 `a`、`b` 配成的带标签的对这一假设下，关系 `rel` 必须在扩张的环境 `b ∷ a ∷ ar ∷ c ∷ γ` 中成立。关系是参数，因此每条子句以自己的载荷要求实例化同一框架。
<!--ja-->
`binShapeAt` は 2 項フレームそのものであり、表を除いた閉性の要求です。量詞の構造は正確に次のとおりです。まず有界全称が定義域 `C` から `c` を選び、続いてさらに 3 つの値 `ar`、`a`、`b` が量化されます。対の読み手が `c` が実際にアリティ `ar` をタグ `k` とペイロード `a`、`b` と組んだタグ付きの対であると証明するという仮定のもとで、関係 `rel` が拡張された環境 `b ∷ a ∷ ar ∷ c ∷ γ` の中で成り立たねばなりません。関係はパラメータなので、各節は同じフレームを自分のペイロードの要求で具体化します。
<!--/-->

```agda

  binShapeAt : Fin n → ℕ → Formula S (4 + n) → Formula S n
  binShapeAt C k rel =
    ∀̇∈ (var C) (∀̇ (∀̇ (∀̇ ( arityTagPairAtL c4 n4 k a4 b4 ⇒̇ rel))))
```

<!--en-->
`unShapeAt` is the same frame for unary constructors: one payload component instead of two, hence one fewer bound slot, and the shape reader `arityTagAtL` in place of the pair version. Everything else, the bounded universal over the domain and the implication into `rel`, is identical.
<!--zh-->
`unShapeAt` 是一元构造子的同一框架：一个载荷分量代替两个，于是少一个被约束的槽，形状读式用 `arityTagAtL` 替代配对版本。其余部分，定义域上的有界全称与指向 `rel` 的蕴含，完全相同。
<!--ja-->
`unShapeAt` は 1 項構成子のための同じフレームです。ペイロード成分が 2 つではなく 1 つであるため、束縛されるスロットが 1 つ減り、形状の読み手は対の版の代わりに `arityTagAtL` を使います。それ以外、定義域上の有界全称と `rel` への含意は同一です。
<!--/-->

```agda

  unShapeAt : Fin n → ℕ → Formula S (3 + n) → Formula S n
  unShapeAt C k rel =
    ∀̇∈ (var C) (∀̇ (∀̇ ( arityTagAtL c3 n3 k a3 ⇒̇ rel)))
```

<!--en-->
`binShape-out` is the elimination direction for the binary frame. Its type takes a proof that the environment `γ` satisfies the frame for an arbitrary relation `rel`, then the chosen code `c` with arity `ar` and components `a`, `b`, together with the membership hypothesis that `c` belongs to the domain.
<!--zh-->
`binShape-out` 是二元框架的消去方向。其类型先取「环境 `γ` 满足任意关系 `rel` 上的该框架」这一证明，然后取选定的码 `c`、元数 `ar` 与分量 `a`、`b`，以及 `c` 属于定义域的隶属假设。
<!--ja-->
`binShape-out` は 2 項フレームの除去方向です。その型は、環境 `γ` が任意の関係 `rel` についてフレームを充足するという証明を取り、続いて選ばれた符号 `c`、アリティ `ar`、成分 `a`、`b`、そして `c` が定義域に属するという所属の仮定を受け取ります。
<!--/-->

```agda

  binShape-out : (C : Fin n) (k : ℕ) (rel : Formula S (4 + n)) (γ : S ^ n)
    → ⟨ γ ⊨ binShapeAt C k rel ⟩
    → (c ar a b : S)
    → ⟨ fst c ∈ fst (lookup C γ) ⟩
```

<!--en-->
The remaining hypothesis is the shape equation saying that `c` really is the tagged pair `ar` with tag `k` and payload `a`, `b`. Under these hypotheses the conclusion is the instance of `rel` in the extended environment, where the bound slots are filled with exactly those values in the order `b ∷ a ∷ ar ∷ c ∷ γ`.
<!--zh-->
其余的假设是形状等式，说 `c` 确实是带标签 `k`、载荷 `a`、`b` 的配对 `ar`。在这些假设下，结论是 `rel` 在扩张环境中的实例，其中被约束的槽恰好按 `b ∷ a ∷ ar ∷ c ∷ γ` 的次序填上这些值。
<!--ja-->
残りの仮定は形状の等式で、`c` が実際にタグ `k` とペイロード `a`、`b` を組んだ対 `ar` であることを述べます。これらの仮定のもとで、帰結は拡張環境における `rel` の実例であり、束縛されたスロットには `b ∷ a ∷ ar ∷ c ∷ γ` の順でまさにこれらの値が満たされます。
<!--/-->

```agda
    → fst c ≡ pr (fst ar) (pr (# k) (pr (fst a) (fst b)))
    → ⟨ (b ∷ a ∷ ar ∷ c ∷ γ) ⊨ rel ⟩
```

<!--en-->
The proof is short because the frame was designed for this reading. The hypothesis `h` is a function, and applying it at `c` with membership and shape produces what is wanted, except that the shape argument must be transported along the adequacy path for `arityTagPairAtL` in the extended environment: adequacy is stated as a path between propositions, and `subst` along it moves the proof to the form the conclusion needs.
<!--zh-->
证明很短，因为框架正是为这种读法设计的。假设 `h` 是一个函数，在 `c` 处连同隶属与形状施加它就得到所要的结论，只是形状论证须沿 `arityTagPairAtL` 在扩大环境中的充分性路径作移送：充分性是命题之间的路径，沿它的 `subst` 把证明移到结论所需的形式。
<!--ja-->
証明は短いです。フレームがこの読み方のために設計されているからです。仮説 `h` は関数であり、`c` において所属と形状とともに適用すれば求めるものが得られます。ただし形状の引数は、拡張環境における `arityTagPairAtL` の妥当性のパスに沿って移送される必要があります。妥当性は命題間のパスとして述べられ、それに沿う `subst` が証明を結論の必要とする形へ移します。
<!--/-->

```agda
  binShape-out C k rel γ h c ar a b c∈ shape =
    h c c∈ ar a b
      (subst ⟨_⟩ (sym (arityTagPairAtL-adequate c4 n4 k a4 b4 (b ∷ a ∷ ar ∷ c ∷ γ)))
        shape)
```

<!--en-->
`unShape-out` is the same elimination for the unary frame. It takes satisfaction of `unShapeAt C k rel` in `γ`, a code `c` with a single payload component `a` and arity `ar`, and the membership hypothesis for `c`.
<!--zh-->
`unShape-out` 是一元框架的同一消去。它取 `γ` 对 `unShapeAt C k rel` 的满足、带唯一载荷分量 `a` 与元数 `ar` 的码 `c`，以及 `c` 的隶属假设。
<!--ja-->
`unShape-out` は 1 項フレームに対する同じ除去です。`γ` による `unShapeAt C k rel` の充足、唯一のペイロード成分 `a` とアリティ `ar` を持つ符号 `c`、そして `c` の所属の仮定を受け取ります。
<!--/-->

```agda

  unShape-out : (C : Fin n) (k : ℕ) (rel : Formula S (3 + n)) (γ : S ^ n)
    → ⟨ γ ⊨ unShapeAt C k rel ⟩
    → (c ar a : S)
```

<!--en-->
The shape equation reads `c` as the tagged pair `ar` with tag `k` and single payload `a`, checked through the unary shape reader `arityTagAtL`. The conclusion then lives in the shorter extended environment `a ∷ ar ∷ c ∷ γ`, whose bound slots are filled with exactly those values.
<!--zh-->
形状等式通过一元形状读式 `arityTagAtL` 把 `c` 读作带标签 `k`、唯一载荷 `a` 的配对 `ar`。结论于是住在较短的扩张环境 `a ∷ ar ∷ c ∷ γ` 中，其中被约束的槽恰好填上这些值。
<!--ja-->
形状の等式は、一元の形状読み手 `arityTagAtL` を通して、`c` をタグ `k` と唯一のペイロード `a` を組んだ対 `ar` として読みます。帰結はより短い拡張環境 `a ∷ ar ∷ c ∷ γ` の中で成り立ち、束縛されたスロットにはまさにこれらの値が満たされます。
<!--/-->

```agda
    → ⟨ fst c ∈ fst (lookup C γ) ⟩
    → fst c ≡ pr (fst ar) (pr (# k) (fst a))
    → ⟨ (a ∷ ar ∷ c ∷ γ) ⊨ rel ⟩
```

<!--en-->
As with the binary case, the proof applies the frame's function at the chosen components and transports the shape proof along the adequacy path for `arityTagAtL`. These two eliminations are all a consumer needs: the seven concrete closure clauses below are obtained from them by instantiating the relation.
<!--zh-->
与二元情形一样，证明在选定分量处施加框架的函数，并沿 `arityTagAtL` 的充分性路径移送形状证明。这两条消去就是使用者所需的全部：下面七条具体的封闭子句都是通过实例化关系从它们得到的。
<!--ja-->
2 項の場合と同様に、証明は選ばれた成分においてフレームの関数を適用し、`arityTagAtL` の妥当性のパスに沿って形状の証明を移送します。この 2 つの除去が利用者に必要なすべてです。以下の 7 つの具体的な閉性節は、関係を具体化することでこれらから得られます。
<!--/-->

```agda
  unShape-out C k rel γ h c ar a c∈ shape =
    h c c∈ ar a
      (subst ⟨_⟩ (sym (arityTagAtL-adequate c3 n3 k a3 (a ∷ ar ∷ c ∷ γ))) shape)
```

<!--en-->
Four generic relations cover the payload shapes. The seven active closure clauses use three of them: the three binary connectives require both components at the current arity; the two unbounded quantifiers require their single component one arity higher, with the successor supplied existentially; and the two bounded quantifiers require only their *second* component at that same higher level, because the first component is a term.
<!--zh-->
四条通用关系描述各种载荷形状，七条封闭性子句使用其中三条。三个二元联结词要求两个分量都属于当前元数处的定义域；两个无界量词要求其唯一分量属于高一个元数处的定义域，这一后继元数通过存在量词给出；两个有界量词只要求**第二个**分量属于高一个元数处的定义域，因为第一个分量是词项。
<!--ja-->
四つの一般関係が各種のペイロード形状を担当し、有効な七つの閉性節はそのうち三つを使います。三つの二項結合子は両方の成分が現在のアリティで定義域に属することを要求し、二つの非有界量詞は唯一の成分が一つ高いアリティで属することを要求しますが、その後続アリティは存在量化で与えられます。二つの有界量詞は**第二**成分だけが同じく一つ高いアリティで属することを要求します。第一成分は項だからです。
<!--/-->

<!--en-->
The two arity-preserving relations are plain conjunctions of subcode membership. Given the four fresh entries of a binary frame, `bothSameAt C` asserts that both subformula slots, named by the indices `a4` and `b4`, already belong to the set that entry `sh4 C` points to. Its unary counterpart `oneSameAt C` is a single such membership claim over the three fresh entries of a unary frame, for constructors whose sole component lives at the same arity.
<!--zh-->
两条保持元数的关系就是子码隶属的简单合取。在二元框架的四个新条目之下，`bothSameAt C` 断言由索引 `a4` 与 `b4` 指名的两个子公式槽位都已经属于条目 `sh4 C` 所指的那个集合。其一元对应物 `oneSameAt C` 则在一元框架的三个新条目之下给出单条这样的隶属断言，用于其唯一分量与自身同元数的构造子。
<!--ja-->
アリティを保つ二つの関係は、部分符号の所属の単純な連言です。二項フレームの四つの新規エントリの下で、`bothSameAt C` はインデックス `a4` と `b4` が指す二つの部分論理式スロットが、エントリ `sh4 C` の指す集合に既に属することを主張します。その一項版 `oneSameAt C` は、一項フレームの三つの新規エントリの下で単一の所属主張を与え、唯一の成分が同じアリティに置かれる構成子に対応します。
<!--/-->

```agda
  bothSameAt : Fin n → Formula S (4 + n)
  bothSameAt C = appAt (sh4 C) n4 a4 ∧̇ appAt (sh4 C) n4 b4

  oneSameAt : Fin n → Formula S (3 + n)
  oneSameAt C = appAt (sh3 C) n3 a3

  oneSuccAt : Fin n → Formula S (3 + n)
```

<!--en-->
The two arity-raising relations quantify the successor existentially. The bound variable at position `zero` is witnessed to be the successor `sucV` of the frame's arity, via `sucAtL`, and the same witness is required to pair with the component slot, now shifted to `suc a3` or `suc b4` inside the extended environment. For `succSndAt` the pair mentions only `b4`, the second slot, since for the bounded quantifiers the first slot of the binary key carries a term rather than a subformula.
<!--zh-->
两条抬升元数的关系以存在量词给出后继。位置 `zero` 处的约束变元经 `sucAtL` 被见证为框架元数的后继 `sucV`，并要求这同一见证与分量槽位配对，而该槽位在扩张后的环境中移到了 `suc a3` 或 `suc b4`。`succSndAt` 的配对只涉及第二个槽位 `b4`，因为对有界量词而言，二元键的第一个槽位放的是词项而非子公式。
<!--ja-->
アリティを上げる二つの関係は、後続を存在量化で与えます。位置 `zero` の束縛変数は `sucAtL` によってフレームのアリティの後続 `sucV` であると証人され、同じ証人が成分スロットとの対にも要求されます。スロットは拡張された環境の中で `suc a3` ないし `suc b4` へとずれます。`succSndAt` の対は第二スロット `b4` だけに言及します。有界量詞では二項キーの第一スロットは部分論理式ではなく項を載せるからです。
<!--/-->

```agda
  oneSuccAt C = ∃̇ (sucAtL (suc n3) zero ∧̇ appAt (suc (sh3 C)) zero (suc a3))

  succSndAt : Fin n → Formula S (4 + n)
  succSndAt C = ∃̇ (sucAtL (suc n4) zero ∧̇ appAt (suc (sh4 C)) zero (suc b4))
```

<!--en-->
Reading them back is what a consumer does, so each is stated at the clause, already composed with its frame: given a key of that shape in the set, the keys the constructor demands are in the set. The two that change arity discharge a truncation on the way, which the target admits because membership is a proposition.
<!--zh-->
这些关系的反向读式由使用者调用，因此每条都直接在相应子句处陈述，并已与其框架复合：若集合中含有某种形状的键，那么相应构造子所需的子键也属于该集合。两条改变元数的读式途中消去一次截断；目标是隶属命题，因此允许该消去。
<!--ja-->
これらの関係の逆方向の読み出しは利用者が行うので、各版は節の位置で、フレームと既に合成された形で述べられます。集合がその形状のキーを含むなら、構成子が要求する子キーも集合に属します。アリティを変える二つの読み出しは途中で命題的切り詰めを一つ解消します。帰結が所属命題なので、その解消が許されます。
<!--/-->

<!--en-->
Four readings unfold the clauses back into concrete membership data, one per payload shape. The first handles the binary connectives at the same arity. Its input is a satisfaction proof of the full clause `binShapeAt C k (bothSameAt C)`, together with a key of the right shape: model elements `c`, `ar`, `a`, `b`, membership of `c` in the set at `C`, and the shape equation presenting `c` as the ordered pair of the arity `ar` with the coded application to `a` and `b`.
<!--zh-->
四个读式把各子句展开回具体的隶属数据，每种载荷形状一个。第一个处理同元数的二元联结词。其输入是完整子句 `binShapeAt C k (bothSameAt C)` 的满足证明，连同形状正确的键：模型元素 `c`、`ar`、`a`、`b`，`c` 在 `C` 处集合中的隶属，以及把 `c` 呈现为「元数 `ar` 与对 `a`、`b` 的编码应用之有序对」的形状等式。
<!--ja-->
4 つの読み手が各節を具体的な所属データへ展開し直します。ペイロードの形ごとに一つです。最初のものは同アリティの 2 項結合子を扱います。入力は節全体 `binShapeAt C k (bothSameAt C)` の充足証明と、正しい形のキーです。すなわちモデルの要素 `c`、`ar`、`a`、`b`、`C` の集合への `c` の所属、そして `c` を「アリティ `ar` と `a`、`b` への符号化された適用の順序対」として呈示する形状の等式です。
<!--/-->

```agda
  binSameClosed-out : (C : Fin n) (k : ℕ) (γ : S ^ n)
    → ⟨ γ ⊨ binShapeAt C k (bothSameAt C) ⟩
    → (c ar a b : S)
    → ⟨ fst c ∈ fst (lookup C γ) ⟩
    → fst c ≡ pr (fst ar) (pr (# k) (pr (fst a) (fst b)))
```

<!--en-->
Its conclusion is the conjunction the constructor demands: both subformula keys, the pairs of the same arity `ar` with `a` and with `b`, are members of the set. The proof runs the generic frame elimination and then applies adequacy, which converts a satisfaction statement about the coded membership reader into the plain membership claim it means; this conversion is the one proof step shared by all four readings.
<!--zh-->
其结论是构造子所要求的合取：由同一元数 `ar` 分别与 `a`、`b` 配成的两个子公式键都属于该集合。证明先运行通用框架消去，再施加充分性转换，它把关于编码隶属读式的满足陈述转换为它所指的普通隶属主张；这一转换是四个读式共用的唯一证明步骤。
<!--ja-->
帰結は構成子が要求する連言です。同じアリティ `ar` を `a` および `b` と対にした 2 つの部分論理式キーが集合の要素になります。証明は一般的なフレーム除去を走らせた後、妥当性を適用します。これは符号化された所属の読み手についての充足の主張を、それが意味する通常の所属の主張へ変換するもので、4 つの読み手すべてに共通する唯一の証明の一段です。
<!--/-->

```agda
    → ⟨ pr (fst ar) (fst a) ∈ fst (lookup C γ) ⟩
    × ⟨ pr (fst ar) (fst b) ∈ fst (lookup C γ) ⟩
  binSameClosed-out C k γ h c ar a b c∈ shape =
      subst ⟨_⟩ (appAt-adequate (sh4 C) n4 a4 δ) (r .fst)
    , subst ⟨_⟩ (appAt-adequate (sh4 C) n4 b4 δ) (r .snd)
```

<!--en-->
The second reading covers the unary constructors at the same arity. Its hypotheses mirror the first with one component fewer: a satisfaction proof of the clause built from `oneSameAt`, the key's parts `c`, `ar`, `a`, membership of `c`, and the shape equation presenting `c` as the pair of the arity `ar` with the coded numeral `k` applied to `a` alone.
<!--zh-->
第二个读式覆盖同元数的一元构造子。其假设仿照第一个但少一个分量：由 `oneSameAt` 构造的子句的满足证明，键的各部分 `c`、`ar`、`a`，`c` 的隶属，以及把 `c` 呈现为「元数 `ar` 与编码数码 `k` 单独作用于 `a`」之对的形状等式。
<!--ja-->
2 番目の読み手は同アリティの 1 項構成子を扱います。仮定は最初のものを一成分分減らして写したものです。`oneSameAt` から作られる節の充足証明、キーの各部 `c`、`ar`、`a`、`c` の所属、そして `c` を「アリティ `ar` と、符号化された数 `k` の `a` への適用」の対として呈示する形状の等式です。
<!--/-->

```agda
    where
    δ : S ^ (4 + n)
    δ = b ∷ a ∷ ar ∷ c ∷ γ
    r = binShape-out C k (bothSameAt C) γ h c ar a b c∈ shape

  unSameClosed-out : (C : Fin n) (k : ℕ) (γ : S ^ n)
```

<!--en-->
The conclusion is a single membership, of the pair of `ar` with `a`. Since `oneSameAt` never raised the arity, no truncation appears, and the proof is just the unary frame elimination followed by the adequacy conversion. The third reading turns to the successor arity: `unSuccClosed-out` reads the clause built from `oneSuccAt`.
<!--zh-->
结论是一条隶属：`ar` 与 `a` 之对的隶属。由于 `oneSameAt` 从未抬升元数，其中不出现截断，证明就是一元框架消去再加充分性转换。第三个读式转向后继元数：`unSuccClosed-out` 读取由 `oneSuccAt` 构造的子句。
<!--ja-->
帰結は単一の所属、すなわち `ar` と `a` の対の所属です。`oneSameAt` はアリティを上げないため切り詰めは現れず、証明は 1 項フレームの除去に妥当性の変換が続くだけです。3 番目の読み手は後続アリティに移ります。`unSuccClosed-out` が `oneSuccAt` から作られる節を読みます。
<!--/-->

```agda
    → ⟨ γ ⊨ unShapeAt C k (oneSameAt C) ⟩
    → (c ar a : S)
    → ⟨ fst c ∈ fst (lookup C γ) ⟩
    → fst c ≡ pr (fst ar) (pr (# k) (fst a))
    → ⟨ pr (fst ar) (fst a) ∈ fst (lookup C γ) ⟩
```

<!--en-->
Its hypotheses match the previous unary reading, but the conclusion names the successor: the required subformula key pairs `a` with `sucV (fst ar)`, the successor of the key's arity, not with `ar` itself. This fits the unbounded quantifiers, which bind a variable and so store their body one arity higher. The next three paragraphs explain how the existential witness and its adequacy proofs establish this conclusion.
<!--zh-->
其假设与前一条一元读式相同，但结论提到后继：所需的子公式键把 `a` 与键元数的后继 `sucV (fst ar)` 配对，而非 `ar` 本身。这正合无界量词：它们绑定变元，故把体存放在高一个元数处。下面三段说明存在见证及其充分性证明如何建立这个结论。
<!--ja-->
仮定は前の 1 項の読み手と一致しますが、帰結は後続に言及します。要求される部分論理式キーは、`ar` 自身ではなくキーのアリティの後続 `sucV (fst ar)` と `a` を対にします。これは非有界量詞に合います。変数を束縛するため、本体は一つ高いアリティの下に保存されるからです。次の三段落で、存在証人とその妥当性証明がこの帰結をどのように導くかを説明します。
<!--/-->

```agda
  unSameClosed-out C k γ h c ar a c∈ shape =
    subst ⟨_⟩ (appAt-adequate (sh3 C) n3 a3 (a ∷ ar ∷ c ∷ γ))
      (unShape-out C k (oneSameAt C) γ h c ar a c∈ shape)

  unSuccClosed-out : (C : Fin n) (k : ℕ) (γ : S ^ n)
    → ⟨ γ ⊨ unShapeAt C k (oneSuccAt C) ⟩
```

<!--en-->
The third reading, for the unbounded quantifiers, raises the arity. Its hypotheses are the usual unary ones: satisfaction of `unShapeAt C k (oneSuccAt C)`, the key's parts `c`, `ar`, `a`, membership of `c`, and the shape equation. The conclusion replaces the arity `ar` by its successor: the required subformula key pairs `a` with `sucV (fst ar)`, the successor of the key's arity, not with `ar` itself. This is the reading appropriate to the unbounded quantifiers, which bind a variable and so store their body one arity higher.
<!--zh-->
第三种读式面向无界量词，抬升了元数。其假设是通常的一元假设：`unShapeAt C k (oneSuccAt C)` 的满足，键的各部分 `c`、`ar`、`a`，`c` 的隶属，以及形状等式。结论把元数 `ar` 换成其后继：所需的子公式键把 `a` 与键元数的后继 `sucV (fst ar)` 配对，而非与 `ar` 本身配对。这正是无界量词所需的读式：它们绑定变元，因此把体存放在高一个元数处。
<!--ja-->
3 つ目の読み出しは非有界量詞のもので、アリティを上げます。仮定は通常の 1 項のものです。`unShapeAt C k (oneSuccAt C)` の充足、キーの各部 `c`、`ar`、`a`、`c` の所属、そして形状の等式です。帰結はアリティ `ar` をその後続に置き換えます。要求される部分論理式キーは、`ar` 自身ではなくキーのアリティの後続 `sucV (fst ar)` と `a` を対にします。これは変数を束縛し、本体を一つ高いアリティの下に保存する非有界量詞に適した読み出しです。
<!--/-->

```agda
    → (c ar a : S)
    → ⟨ fst c ∈ fst (lookup C γ) ⟩
    → fst c ≡ pr (fst ar) (pr (# k) (fst a))
    → ⟨ pr (sucV (fst ar)) (fst a) ∈ fst (lookup C γ) ⟩
  unSuccClosed-out C k γ h c ar a c∈ shape =
```

<!--en-->
This is where the existential inside `oneSuccAt` matters. The successor is demanded only merely: the frame elimination hands over a propositionally truncated witness, together with certificates that it is the successor of the arity and that it pairs with `a` into the set. Such a truncation may be eliminated here because the goal is a proposition: membership in a set is an hProp, so `PT.rec` converts the mere existence into the concrete membership claim without choosing a canonical witness.
<!--zh-->
这里 `oneSuccAt` 内部的存在量词起了作用。子句对后继只是「仅仅存在」式地要求：框架消去所给出的是被命题截断的见证，连同两个证书，即它是元数的后继，且它与 `a` 配对进入该集合。这一截断在此可以消去，因为目标是命题：集合中的隶属是 hProp，故 `PT.rec` 把「仅仅存在」转换为具体的隶属主张，而无须选定某个典范见证。
<!--ja-->
ここで `oneSuccAt` 内部の存在量化が効いてきます。後続は命題的に切り詰められた形でしか要求されません。フレーム除去が渡すのは命題的に切り詰められた証人と、それがアリティの後続であること、また `a` と対になって集合に入ることの 2 つの証明書です。この切り詰めがここで除却できるのは、帰結が命題だからです。集合への所属は hProp なので、`PT.rec` は命題的切り詰められた存在を具体的な所属の主張へ変換でき、標準的な証人を選ぶ必要はありません。
<!--/-->

```agda
    PT.rec (snd target)
      (λ { (z , (sz , ap)) →
        subst (λ w → ⟨ pr w (fst a) ∈ fst (lookup C γ) ⟩)
          (subst ⟨_⟩ (sucAtL-adequate (suc n3) zero (z ∷ δ)) sz)
          (subst ⟨_⟩ (appAt-adequate (suc (sh3 C)) zero (suc a3) (z ∷ δ)) ap) })
```

<!--en-->
The adequacy lemmas of the two readers then turn those satisfactions into equations and memberships about the actual model values, and the transport along the first equation re-expresses the membership at the witness as membership at `sucV (fst ar)`. So the reading ends exactly where it should: with the membership of the successor key.
<!--zh-->
两个读式的充分性引理随后把这些满足转换为关于模型实际取值的等式与隶属，沿第一条等式的移送把见证处的隶属改写为 `sucV (fst ar)` 处的隶属。于是这条读式恰好在应在之处结束：以后继键的隶属收尾。
<!--ja-->
2 つの読み手の妥当性補題は、これらの充足をモデルの実際の値についての等式と所属へ変え、最初の等式に沿う輸送が証人での所属を `sucV (fst ar)` での所属として表し直します。こうして読み出しはあるべき場所で終わります。すなわち後続キーの所属で締めくくられるのです。
<!--/-->

```agda
      (unShape-out C k (oneSuccAt C) γ h c ar a c∈ shape)
    where
    δ : S ^ (3 + n)
    δ = a ∷ ar ∷ c ∷ γ
    target = pr (sucV (fst ar)) (fst a) ∈ fst (lookup C γ)
```

<!--en-->
The fourth reading covers the bounded quantifiers. Its hypotheses copy the binary pattern: satisfaction of `binShapeAt C k (succSndAt C)`, the four model values `c`, `ar`, `a`, `b`, membership of `c`, and the shape equation presenting `c` as the pair of `ar` with the coded application to `a`, `b`.
<!--zh-->
第四种读式覆盖有界量词。其假设照搬二元模式：`binShapeAt C k (succSndAt C)` 的满足，四个模型值 `c`、`ar`、`a`、`b`，`c` 的隶属，以及把 `c` 呈现为「`ar` 与对 `a`、`b` 的编码应用之对」的形状等式。
<!--ja-->
4 つ目の読み出しは有界量詞を担います。仮定は 2 項のパターンをそのまま写します。`binShapeAt C k (succSndAt C)` の充足、4 つのモデル値 `c`、`ar`、`a`、`b`、`c` の所属、そして `c` を「`ar` と `a`、`b` への符号化された適用の対」として呈示する形状の等式です。
<!--/-->

```agda

  binSuccClosed-out : (C : Fin n) (k : ℕ) (γ : S ^ n)
    → ⟨ γ ⊨ binShapeAt C k (succSndAt C) ⟩
    → (c ar a b : S)
    → ⟨ fst c ∈ fst (lookup C γ) ⟩
    → fst c ≡ pr (fst ar) (pr (# k) (pr (fst a) (fst b)))
```

<!--en-->
The conclusion asks only about the second component: `sucV (fst ar)` paired with `b` must be in the set, since the first slot carries the bounding term rather than a subformula. As in the unbounded case, the existential inside `succSndAt` supplies the successor merely, and the elimination of that truncation is legitimate because the membership target is a proposition.
<!--zh-->
结论只问第二个分量：`sucV (fst ar)` 与 `b` 之对须属于该集合，因为第一个槽放的是有界词项而非子公式。与无界情形一样，`succSndAt` 内部的存在量词以「仅仅存在」的方式给出后继，而该截断的消去合法，因为隶属目标是命题。
<!--ja-->
帰結は第二成分だけを問います。`sucV (fst ar)` と `b` の対が集合に属さねばなりません。第一スロットが載せるのは部分論理式ではなく有界の項だからです。非有界の場合と同様、`succSndAt` 内部の存在量化は後続を命題的に切り詰められた形で与え、所属の帰結が命題であるため、その切り詰めの除却は正当です。
<!--/-->

```agda
    → ⟨ pr (sucV (fst ar)) (fst b) ∈ fst (lookup C γ) ⟩
  binSuccClosed-out C k γ h c ar a b c∈ shape =
    PT.rec (snd target)
      (λ { (z , (sz , ap)) →
        subst (λ w → ⟨ pr w (fst b) ∈ fst (lookup C γ) ⟩)
```

<!--en-->
The proof body is the binary counterpart of the previous one: the two certificates are converted by `sucAtL-adequate` and `appAt-adequate`, and the transport along the successor equation re-expresses the pairing membership at `sucV (fst ar)`.
<!--zh-->
证明体是上一条读式的二元对应：两个证书经 `sucAtL-adequate` 与 `appAt-adequate` 转换，沿后继等式的移送把配对隶属改写到 `sucV (fst ar)` 处。
<!--ja-->
証明の本体は前の読み出しの 2 項版です。2 つの証明書は `sucAtL-adequate` と `appAt-adequate` によって変換され、後続の等式に沿う輸送が対の所属を `sucV (fst ar)` のもとで表し直します。
<!--/-->

```agda
          (subst ⟨_⟩ (sucAtL-adequate (suc n4) zero (z ∷ δ)) sz)
          (subst ⟨_⟩ (appAt-adequate (suc (sh4 C)) zero (suc b4) (z ∷ δ)) ap) })
      (binShape-out C k (succSndAt C) γ h c ar a b c∈ shape)
    where
    δ : S ^ (4 + n)
```

<!--en-->
The propositionhood of the membership conclusion is what licenses the truncation elimination in each successor-arity reading. These four readings, in two same-arity and two successor-arity forms, are all a consumer needs: every closure clause can be unfolded into concrete membership data.
<!--zh-->
隶属结论的命题性，正是每条后继元数读式中截断消去所需的许可。这四种读式，两条保持元数、两条抬升元数，就是使用者的全部所需：每条封闭性子句都能展开为具体的隶属数据。
<!--ja-->
所属の帰結の命題性こそが、各後続アリティの読み出しにおける切り詰めの除却を許すものです。同アリティの 2 つと後続アリティの 2 つ、この 4 つの読み出しが利用者に必要なすべてであり、どの閉性節も具体的な所属データへ展開できます。
<!--/-->

```agda
    δ = b ∷ a ∷ ar ∷ c ∷ γ
    target = pr (sucV (fst ar)) (fst b) ∈ fst (lookup C γ)
```

<!--en-->
The seven clauses, and their conjunction. On the elimination side, a consumer reading a satisfied `closedAt` conjunction selects the clause it wants and applies the reader that goes with it. The introduction directions appear in the next section.
<!--zh-->
七条子句，及其合取。在消去一侧，读取已满足的 `closedAt` 合取的使用者按需选取其中一条子句，并应用与之配套的读式。引入方向在下一节给出。
<!--ja-->
七つの節と、その連言です。消去の側では、充足された `closedAt` の連言を読む利用者は必要な節を選び、それに対応する読み出しを適用します。引入の方向は次の節で与えられます。
<!--/-->

<!--en-->
The seven clause names are declared first, all of the same type: at each index `C` they are formulas over the `n`-environment, at the very arity of the key stored there. No environment extension appears in their types, since each frame is applied internally with its freshly shifted indices.
<!--zh-->
首先声明七条子句的名字，类型全部相同：在每个索引 `C` 处，它们都是 `n` 环境上的公式，与该处存储的键的元数一致。其类型中不出现任何环境扩张，因为各框架都在内部以新移位的索引自行应用。
<!--ja-->
まず七つの節の名前を宣言します。型はすべて同じで、各インデックス `C` において `n` 環境上の論理式であり、そこに保存されるキーのアリティそのものです。各フレームが新しくずらしたインデックスで内部的に適用されるため、型には環境の拡張は現れません。
<!--/-->

```agda
  andClosedAt orClosedAt impClosedAt : Fin n → Formula S n
  existClosedAt forallClosedAt allInClosedAt exInClosedAt : Fin n → Formula S n

  andClosedAt    C = binShapeAt C 2 (bothSameAt C)
  orClosedAt     C = binShapeAt C 3 (bothSameAt C)
  impClosedAt    C = binShapeAt C 4 (bothSameAt C)
```

<!--en-->
Each definition pairs a constructor key with the right relation: the numerals 2, 3, 4 are the binary connectives, whose clauses use `bothSameAt`; 6 and 7 are the unbounded quantifiers, using `oneSuccAt`; and 8 and 9 are the bounded quantifiers, using `succSndAt`. The frame `binShapeAt` or `unShapeAt` is chosen according to whether the constructor's code carries two payload components or one: the binary connectives and the bounded quantifiers have two and so use `binShapeAt`, while the unbounded quantifiers have one and use `unShapeAt`. Quantifier bodies live at the successor arity, and for the bounded quantifiers only the second payload component is a formula, which is why their relation follows only that component.
<!--zh-->
每个定义把一个构造子键与恰当的关系配对：数码 2、3、4 是二元联结词，其子句使用 `bothSameAt`；6 与 7 是无界量词，使用 `oneSuccAt`；8 与 9 是有界量词，使用 `succSndAt`。框架 `binShapeAt` 或 `unShapeAt` 的选取取决于构造子码带有两个还是唯一一个载荷分量：二元联结词与有界量词有两个分量，故用 `binShapeAt`；无界量词只有一个分量，故用 `unShapeAt`。量词的体处在后继元数处，而有界量词只有第二个载荷分量是公式，因此其关系只跟随该分量。
<!--ja-->
各定義は構成子のキーと適切な関係を対にします。数 2、3、4 は二項結合子で、その節は `bothSameAt` を使い、6 と 7 は非有界量詞で `oneSuccAt` を、8 と 9 は有界量詞で `succSndAt` を使います。フレーム `binShapeAt` か `unShapeAt` かは、構成子の符号がペイロード成分を 2 つ持つか 1 つ持つかで選ばれます。二項結合子と有界量詞は 2 つ持つので `binShapeAt` を、非有界量詞は 1 つしか持たないので `unShapeAt` を使います。量詞の本体は後続アリティに置かれ、有界量詞では第 2 のペイロード成分だけが論理式なので、その関係はその成分だけを追います。
<!--/-->

```agda
  existClosedAt  C = unShapeAt  C 6 (oneSuccAt C)
  forallClosedAt C = unShapeAt  C 7 (oneSuccAt C)
  allInClosedAt  C = binShapeAt C 8 (succSndAt C)
  exInClosedAt   C = binShapeAt C 9 (succSndAt C)

  closedAt : Fin n → Formula S n
```

<!--en-->
`closedAt C` conjoins all seven clauses at the single index `C`. This is the object-language predicate later transported into `L`: a set is subcode closed at `C` when this conjunction is satisfied, and structural induction over codes then proceeds conjunct by conjunct, each with its own reader.
<!--zh-->
`closedAt C` 在单个索引 `C` 处合取全部七条子句。这就是日后被传递到 `L` 中的对象语言谓词：当该合取被满足时，集合在 `C` 处对子码封闭；对码的结构归纳随后逐个合取项推进，每个合取项各有自己的读式。
<!--ja-->
`closedAt C` は単一のインデックス `C` で七つの節すべてを連言します。これが後に `L` へ輸送される対象言語の述語です。この連言が充足されるとき集合は `C` で部分符号に対して閉じており、符号上の構造帰納法は連言項ごとに、それぞれ専用の読み出しとともに進みます。
<!--/-->

```agda
  closedAt C =
    andClosedAt C ∧̇ (orClosedAt C ∧̇ (impClosedAt C ∧̇ (existClosedAt C
      ∧̇ (forallClosedAt C ∧̇ (allInClosedAt C ∧̇ exInClosedAt C)))))
```

<!--en-->
The converse starts from actual meta-level subcode closure and turns it into satisfaction of each object-language frame. For same-arity clauses, the supplied membership facts directly establish the required payload memberships. For arity-raising clauses, the L-numeral `sucʟ ar` supplies the existential successor witness together with the equations and membership certificate that the frame demands.
<!--zh-->
反方向从元层面真实的子码封闭数据出发，把它转成每条对象语言框架的满足。对同元数子句，给定的隶属事实直接建立所需的载荷隶属；对抬升元数的子句，L 数码 `sucʟ ar` 提供存在量化的后继见证，以及框架所需的等式与隶属证书。
<!--ja-->
逆方向は、メタレベルで実際に与えられた部分符号の閉性から出発し、それを各対象言語フレームの充足へ移します。同じアリティの節では、与えられた所属事実が必要なペイロードの所属を直接示します。アリティを上げる節では、L 数項 `sucʟ ar` が存在量化された後続の証人と、フレームが要求する等式および所属の証明を与えます。
<!--/-->

<!--en-->
The introduction direction answers the converse need: given meta-level closure data, produce satisfaction of the clause. For the binary frame, `binShape-in` takes a function `g` which, from a key's parts `c`, `ar`, `a`, `b`, membership of `c`, and the shape equation, returns satisfaction of the arbitrary relation `rel` in the extended environment; it concludes satisfaction of the whole shape `binShapeAt C k rel`.
<!--zh-->
引入方向回答相反的需求：给定元层面的封闭数据，产出子句的满足。对二元框架，`binShape-in` 取函数 `g`，它从键的各部分 `c`、`ar`、`a`、`b`、`c` 的隶属以及形状等式，给出任意关系 `rel` 在扩张环境中的满足；其结论是整个形状 `binShapeAt C k rel` 的满足。
<!--ja-->
導入の方向は逆向きの需要に答えます。メタレベルの閉性データから、節の充足を作るのです。2 項フレームでは、`binShape-in` は関数 `g` を受け取ります。`g` はキーの各部 `c`、`ar`、`a`、`b`、`c` の所属、そして形状の等式から、任意の関係 `rel` の拡張環境での充足を返します。結論は形状全体 `binShapeAt C k rel` の充足です。
<!--/-->

```agda
  binShape-in : (C : Fin n) (k : ℕ) (rel : Formula S (4 + n)) (γ : S ^ n)
    → ((c ar a b : S)
       → ⟨ fst c ∈ fst (lookup C γ) ⟩
       → fst c ≡ pr (fst ar) (pr (# k) (pr (fst a) (fst b)))
       → ⟨ (b ∷ a ∷ ar ∷ c ∷ γ) ⊨ rel ⟩)
```

<!--en-->
This is the semantic content of the quantifiers read backward: satisfaction of a bounded universal is a function defined on members of the set, and satisfaction of an implication is a function on the proof of its premise. So `g` applied to the key's data is already the required satisfaction; the only conversion is along `arityTagPairAtL-adequate`, aligning the tag equation the frame reads with the shape equation `g` was handed.
<!--zh-->
这正是把量词语义反过来读：有界全称的满足是定义在集合成员上的函数，蕴涵的满足是其前提之证明上的函数。因此把 `g` 施加于键的数据就已得到所需的满足；唯一需要的转换沿 `arityTagPairAtL-adequate` 完成，把框架读取的标记等式与 `g` 收到的形状等式对齐。
<!--ja-->
これは量詞の意味論を逆向きに読んだものです。有界全称の充足は集合の要素上で定義された関数であり、含意の充足はその前提の証明上の関数です。したがって `g` をキーのデータに適用すれば求める充足が得られます。必要な変換は `arityTagPairAtL-adequate` に沿うものだけで、フレームの読むタグの等式を `g` に渡された形状の等式と整列させます。
<!--/-->

```agda
    → ⟨ γ ⊨ binShapeAt C k rel ⟩
  binShape-in C k rel γ g c c∈ ar a b sh =
    g c ar a b c∈
      (subst ⟨_⟩ (arityTagPairAtL-adequate c4 n4 k a4 b4 (b ∷ a ∷ ar ∷ c ∷ γ)) sh)

  unShape-in : (C : Fin n) (k : ℕ) (rel : Formula S (3 + n)) (γ : S ^ n)
```

<!--en-->
The unary version drops one component: `g` receives `c`, `ar`, `a` and returns satisfaction of `rel` over the unary frame's extended environment, the goal being satisfaction of `unShapeAt C k rel`. The concrete introductions below instantiate `rel` at the four relations; for the two arity-raising ones, the clause demands the successor only existentially, and the numeral chapter's L-numeral `sucʟ ar` then serves as a concrete witness, injected into the truncation together with its certificates.
<!--zh-->
一元版本少一个分量：`g` 收到 `c`、`ar`、`a`，返回 `rel` 在一元框架扩张环境上的满足，目标是 `unShapeAt C k rel` 的满足。下面的具体引入把 `rel` 实例化为四条关系；对两条抬升元数的关系，子句只以存在量词要求后继，此时数码章的 L 数码 `sucʟ ar` 便充当具体见证，与其证书一起注入截断。
<!--ja-->
1 項版は成分を一つ減らします。`g` は `c`、`ar`、`a` を受け取り、1 項フレームの拡張環境での `rel` の充足を返します。目標は `unShapeAt C k rel` の充足です。以下の具体的な導入は `rel` を 4 つの関係に具体化します。アリティを上げる 2 つの関係では、節が後続を存在量化でしか要求しないため、数項の章の L 数項 `sucŀ ar` が具体的な証人として働き、その証明書とともに切り詰めへ注入されます。
<!--/-->

```agda
    → ((c ar a : S)
       → ⟨ fst c ∈ fst (lookup C γ) ⟩
       → fst c ≡ pr (fst ar) (pr (# k) (fst a))
       → ⟨ (a ∷ ar ∷ c ∷ γ) ⊨ rel ⟩)
    → ⟨ γ ⊨ unShapeAt C k rel ⟩
```

<!--en-->
The same-arity introductions are now built by composing the generic frame introductions with the concrete relations. For the unary frame, the tag equation delivered by `arityTagAtL-adequate` aligns the shape the frame reads with the data a caller supplies. The first composed introduction `binSameClosed-in` instantiates the binary frame at `bothSameAt C`: instead of an arbitrary relation, the caller now owes meta-level membership data, and the lemma repackages that data as satisfaction of the clause.
<!--zh-->
同元数的引入通过把通用框架引入与具体关系复合而得到。对一元框架，`arityTagAtL-adequate` 给出的标记等式把框架读取的形状与使用者提供的数据对齐。第一条复合引入 `binSameClosed-in` 把二元框架实例化在 `bothSameAt C` 上：使用者不再对任意关系负责，而是交付元层面的隶属数据，这条引理把该数据重新包装为子句的满足。
<!--ja-->
同アリティの導入は、一般的なフレームの導入と具体的な関係を合成して作られます。1 項フレームでは、`arityTagAtL-adequate` が与えるタグの等式が、フレームの読む形状と利用者が渡すデータを整列させます。最初の合成導入 `binSameClosed-in` は 2 項フレームを `bothSameAt C` で具体化します。任意の関係の代わりに、利用者が負うのはメタレベルの所属データであり、この補題がそのデータを節の充足として組み直します。
<!--/-->

```agda
  unShape-in C k rel γ g c c∈ ar a sh =
    g c ar a c∈
      (subst ⟨_⟩ (arityTagAtL-adequate c3 n3 k a3 (a ∷ ar ∷ c ∷ γ)) sh)

  binSameClosed-in : (C : Fin n) (k : ℕ) (γ : S ^ n)
    → ((c ar a b : S)
```

<!--en-->
Here `g` is the closure obligation itself, stated as data: from a key of the given shape it must produce membership of both subformula keys, the pairs of the arity `ar` with `a` and with `b`. The lemma converts that data into satisfaction of the full clause, so a recursion over codes can discharge the binary-connective obligations by supplying exactly this membership data.
<!--zh-->
这里 `g` 就是以数据形式陈述的封闭义务：从给定形状的键出发，它须产出两个子公式键的隶属，即元数 `ar` 分别与 `a`、`b` 配成的两对。这条引理把该数据转换为完整子句的满足，因此对码作递归时，只需提供这样的隶属数据即可完成二元联结词的封闭义务。
<!--ja-->
ここで `g` はデータとして述べられた閉性の義務そのものです。与えられた形状のキーから、2 つの部分論理式キー、すなわちアリティ `ar` を `a` および `b` と組んだ 2 つの対の所属を生み出さねばなりません。補題がこのデータを節全体の充足へ変換するので、符号上の再帰はこの所属データを供給するだけで 2 項結合子の閉性の義務を果たせます。
<!--/-->

```agda
       → ⟨ fst c ∈ fst (lookup C γ) ⟩
       → fst c ≡ pr (fst ar) (pr (# k) (pr (fst a) (fst b)))
       → ⟨ pr (fst ar) (fst a) ∈ fst (lookup C γ) ⟩
       × ⟨ pr (fst ar) (fst b) ∈ fst (lookup C γ) ⟩)
    → ⟨ γ ⊨ binShapeAt C k (bothSameAt C) ⟩
```

<!--en-->
To build satisfaction of the conjunction, the two membership claims that `g` returns must be recast as satisfaction of the two `appAt` conjuncts. The adequacy lemma for `appAt` equates the two forms, and here it is used in the direction opposite to the elimination side, since the goal now reads from data to satisfaction.
<!--zh-->
为构造合取的满足，须把 `g` 返回的两条隶属主张改写为两个 `appAt` 合取项的满足。`appAt` 的充分性引理把两种形态等同起来，这里它的使用方向与消去一侧相反，因为目标此时是从数据读向满足。
<!--ja-->
連言の充足を作るには、`g` が返す 2 つの所属の主張を、`appAt` の 2 つの連言項の充足として言い換えねばなりません。`appAt` の妥当性補題は両者の形を同一視するもので、ここでは除却の側とは逆向きに使われます。帰結が今度はデータから充足へと読まれるからです。
<!--/-->

```agda
  binSameClosed-in C k γ g = binShape-in C k (bothSameAt C) γ
    (λ c ar a b c∈ sh →
        subst ⟨_⟩ (sym (appAt-adequate (sh4 C) n4 a4 (b ∷ a ∷ ar ∷ c ∷ γ)))
          (g c ar a b c∈ sh .fst)
      , subst ⟨_⟩ (sym (appAt-adequate (sh4 C) n4 b4 (b ∷ a ∷ ar ∷ c ∷ γ)))
```

<!--en-->
The two components are handled by the same reading, one conjunct at a time. The unary same-arity introduction `unSameClosed-in` then repeats the construction for the one-component relation, with the same data shape minus the second component.
<!--zh-->
两个分量按同一读法逐个合取项处理。随后，一元同元数引入 `unSameClosed-in` 对单分量关系重复这一构造，数据形状与二元情形相同，只是少了第二个分量。
<!--ja-->
2 つの成分は同じ読み方で、連言項ごとに扱われます。続く 1 項の同アリティ導入 `unSameClosed-in` は、単一成分の関係に対して同じ構成を繰り返すもので、データの形は第 2 成分を除いて同じです。
<!--/-->

```agda
          (g c ar a b c∈ sh .snd))

  unSameClosed-in : (C : Fin n) (k : ℕ) (γ : S ^ n)
    → ((c ar a : S)
       → ⟨ fst c ∈ fst (lookup C γ) ⟩
       → fst c ≡ pr (fst ar) (pr (# k) (fst a))
```

<!--en-->
For the unary same-arity clause a single membership claim suffices: `g` returns membership of the one subformula key, and the composition with the generic unary introduction, with `rel` fixed to `oneSameAt C`, turns it into satisfaction of the clause.
<!--zh-->
对一元同元数子句，一条隶属主张即可：`g` 给出唯一子公式键的隶属，把它与 `rel` 取为 `oneSameAt C` 的通用一元引入复合，便得到子句的满足。
<!--ja-->
1 項の同アリティの節では、単一の所属の主張で足ります。`g` が唯一の部分論理式キーの所属を返し、`rel` を `oneSameAt C` に固定した一般的な 1 項導入と合成すれば、それが節の充足になります。
<!--/-->

```agda
       → ⟨ pr (fst ar) (fst a) ∈ fst (lookup C γ) ⟩)
    → ⟨ γ ⊨ unShapeAt C k (oneSameAt C) ⟩
  unSameClosed-in C k γ g = unShape-in C k (oneSameAt C) γ
    (λ c ar a c∈ sh →
      subst ⟨_⟩ (sym (appAt-adequate (sh3 C) n3 a3 (a ∷ ar ∷ c ∷ γ)))
```

<!--en-->
The last two introductions raise the arity, starting with `unSuccClosed-in`. Its hypothesis `g` receives the usual unary key data but must conclude membership of the successor key: the pair of `sucV (fst ar)`, the successor of the key's arity, with `a`.
<!--zh-->
最后两条引入抬升元数，先看 `unSuccClosed-in`。其假设 `g` 收到通常的一元键数据，但须得出后继键的隶属：键元数的后继 `sucV (fst ar)` 与 `a` 之对。
<!--ja-->
残る 2 つの導入はアリティを上げます。まず `unSuccClosed-in` です。仮定 `g` はいつもの 1 項キーのデータを受け取りますが、後続キーの所属を結論せねばなりません。すなわちキーのアリティの後続 `sucV (fst ar)` と `a` の対の所属です。
<!--/-->

```agda
        (g c ar a c∈ sh))

  unSuccClosed-in : (C : Fin n) (k : ℕ) (γ : S ^ n)
    → ((c ar a : S)
       → ⟨ fst c ∈ fst (lookup C γ) ⟩
       → fst c ≡ pr (fst ar) (pr (# k) (fst a))
```

<!--en-->
The relation `oneSuccAt` demands its successor only existentially and merely, so any witness carrying the two certificates is acceptable, and the proof supplies a concrete one: the L-numeral `sucʟ ar`. It is a valid witness because its first-projection law `sucʟ-fst ar` identifies its first component with `sucV (fst ar)`, and the adequacy lemma for `sucAtL` converts that defining equation into the satisfaction the clause reads.
<!--zh-->
关系 `oneSuccAt` 仅以存在且「仅仅」的方式要求后继，因此任何携带两个证书的见证都可用，证明提供了一个具体见证：L 数码 `sucʟ ar`。它是合格的见证，因为其第一投影法则 `sucʟ-fst ar` 把它的第一分量等同于 `sucV (fst ar)`，而 `sucAtL` 的充分性引理把这条定义等式转换为子句所读取的满足。
<!--ja-->
関係 `oneSuccAt` は後続を命題的に切り詰められた存在の形でしか要求しないので、2 つの証明書を備えた証人ならどれでも構いません。証明は具体的な証人として L 数項 `sucʟ ar` を与えます。これが証人として適格なのは、第一射影の法則 `sucʟ-fst ar` がその第 1 成分を `sucV (fst ar)` と同一視するからで、`sucAtL` の妥当性補題がこの定義等式を節の読む充足へ変換します。
<!--/-->

```agda
       → ⟨ pr (sucV (fst ar)) (fst a) ∈ fst (lookup C γ) ⟩)
    → ⟨ γ ⊨ unShapeAt C k (oneSuccAt C) ⟩
  unSuccClosed-in C k γ g = unShape-in C k (oneSuccAt C) γ
    (λ c ar a c∈ sh → ∣ sucʟ ar
      , ( subst ⟨_⟩ (sym (sucAtL-adequate (suc n3) zero
```

<!--en-->
The second certificate is the pairing claim. `g` already yields membership of the successor key, and the numeral's projection law re-expresses that as membership of `pr (sucʟ ar) (fst a)`, which the adequacy lemma for `appAt` converts into the satisfaction of the pairing conjunct. Injecting the witness with its certificates into propositional truncation needs no propositionhood premise; that requirement belongs to elimination, not introduction.
<!--zh-->
第二个证书是配对主张。`g` 已经给出后继键的隶属，数码的投影法则把它改写为 `pr (sucʟ ar) (fst a)` 的隶属，再由 `appAt` 的充分性引理转换为配对合取项的满足。把见证与其证书注入命题截断不需要任何命题性前提；那一要求属于消去，而非引入。
<!--ja-->
第 2 の証明書は対の主張です。`g` は既に後続キーの所属を与えており、数項の射影の法則がそれを `pr (sucʟ ar) (fst a)` の所属として表し、`appAt` の妥当性補題が対の連言項の充足へ変換します。証人と証明書を命題的切り詰めへ注入するのに命題性の前提は不要です。その要件は除却に属し、導入には属しません。
<!--/-->

```agda
            (sucʟ ar ∷ a ∷ ar ∷ c ∷ γ))) (sucʟ-fst ar)
        , subst ⟨_⟩ (sym (appAt-adequate (suc (sh3 C)) zero (suc a3)
            (sucʟ ar ∷ a ∷ ar ∷ c ∷ γ)))
            (subst (λ w → ⟨ pr w (fst a) ∈ fst (lookup C γ) ⟩)
              (sym (sucʟ-fst ar)) (g c ar a c∈ sh)) ) ∣₁)
```

<!--en-->
The final introduction `binSuccClosed-in` covers the bounded quantifiers. Its hypothesis `g` receives the binary key's four values and must produce membership of the second component under the successor arity: the pair of `sucV (fst ar)` with `b`, since the first slot carries the bounding term rather than a subformula.
<!--zh-->
最后一条引入 `binSuccClosed-in` 覆盖有界量词。其假设 `g` 收到二元键的四个值，须产出第二分量在后继元数下的隶属：`sucV (fst ar)` 与 `b` 之对，因为第一个槽放的是有界词项而非子公式。
<!--ja-->
最後の導入 `binSuccClosed-in` は有界量詞を担当します。仮定 `g` は 2 項キーの 4 つの値を受け取り、後続アリティの下での第 2 成分の所属を生み出します。すなわち `sucV (fst ar)` と `b` の対です。第 1 スロットが載せるのは部分論理式ではなく有界の項だからです。
<!--/-->

```agda

  binSuccClosed-in : (C : Fin n) (k : ℕ) (γ : S ^ n)
    → ((c ar a b : S)
       → ⟨ fst c ∈ fst (lookup C γ) ⟩
       → fst c ≡ pr (fst ar) (pr (# k) (pr (fst a) (fst b)))
       → ⟨ pr (sucV (fst ar)) (fst b) ∈ fst (lookup C γ) ⟩)
```

<!--en-->
The construction is the same as the unary successor introduction, applied at the binary frame with `rel` fixed to `succSndAt C`: the witness is again the L-numeral `sucʟ ar`, its projection law again certifies the successor, and the pairing claim now concerns only the second component `b`, after which the bounded-quantifier clause is satisfied.
<!--zh-->
这一构造与一元后继引入相同，只是施加于把 `rel` 取为 `succSndAt C` 的二元框架：见证仍取 L 数码 `sucʟ ar`，其投影法则仍见证后继，而配对主张只涉及第二分量 `b`，至此有界量词子句便得到满足。
<!--ja-->
この構成は 1 項の後続の導入と同じもので、`rel` を `succSndAt C` に固定した 2 項フレームに適用されます。証人はやはり L 数項 `sucʟ ar` であり、その射影の法則が後続を証明し、対の主張は今度は第 2 成分 `b` だけに関わり、これで有界量詞の節が充足されます。
<!--/-->

```agda
    → ⟨ γ ⊨ binShapeAt C k (succSndAt C) ⟩
  binSuccClosed-in C k γ g = binShape-in C k (succSndAt C) γ
    (λ c ar a b c∈ sh → ∣ sucʟ ar
      , ( subst ⟨_⟩ (sym (sucAtL-adequate (suc n4) zero
            (sucʟ ar ∷ b ∷ a ∷ ar ∷ c ∷ γ))) (sucʟ-fst ar)
```

<!--en-->
The binary successor case uses the same witness and the same two adequacy facts, now for the formula component of a bounded quantifier. Thus every active constructor clause has both readings: satisfaction yields the required subcode memberships, and actual closure data yields satisfaction. These two directions make `closedAt C` the object-language form of meta-level closure under immediate formula subcodes.
<!--zh-->
二元后继情形使用同一个见证和同两条充分性事实，只是这次用于有界量词的公式分量。于是每条有效构造子子句都有两个读法：满足给出所需的子码隶属，而真实的封闭数据给出满足。这两个方向使 `closedAt C` 正好成为元层面直接公式子码封闭的对象语言表达。
<!--ja-->
2 項の後続の場合も同じ証人と同じ 2 つの妥当性の事実を使い、今度は有界量化子の論理式成分に適用します。したがって、有効な各構成子の節には両方向の読みがあります。充足から必要な部分符号の所属が得られ、実際の閉性データから充足が得られます。この両方向により、`closedAt C` は直下の部分論理式符号に関するメタレベルの閉性を対象言語で表したものになります。
<!--/-->

```agda
        , subst ⟨_⟩ (sym (appAt-adequate (suc (sh4 C)) zero (suc b4)
            (sucʟ ar ∷ b ∷ a ∷ ar ∷ c ∷ γ)))
            (subst (λ w → ⟨ pr w (fst b) ∈ fst (lookup C γ) ⟩)
              (sym (sucʟ-fst ar)) (g c ar a b c∈ sh)) ) ∣₁)
```

<!--en-->
## Recap

`closedAt` requires every compound code in the domain to bring along the subformula codes its clause reads. Its elimination lemmas expose those subcodes, and its introduction lemmas build the same seven obligations from meta-level membership facts.
<!--zh-->
## 小结

`closedAt` 要求定义域中的每个复合码都带上其子句将读取的子公式码。消去引理取出这些子码，引入引理则从元语言的隶属事实构造同样的七项义务。
<!--ja-->
## まとめ

`closedAt` は、定義域の各複合符号が、その節が読み取る部分論理式の符号を伴うことを要求します。消去補題はこれらの部分符号を取り出し、導入補題は同じ七つの義務をメタ言語側の所属事実から構成します。
<!--/-->
