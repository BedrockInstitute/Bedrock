<!--en-->
# Describing the satisfaction table

The object language cannot invoke the host language's recursion on formulas. It therefore needs a bounded description of the graph that recursion should produce. This chapter treats `T` as a candidate relation of formula keys and environment sets, and asks which local equations each matching entry must obey. The answer consists of ten constructor clauses and two conditions on the first projection of `T`; semantic correctness, uniqueness, closure of the code domain, and existence of canonical data require further arguments.
<!--zh-->
# 描述满足关系表

对象语言不能直接调用宿主语言中关于公式的递归，因此需要用有界方式描述该递归应产生的图。本章把 `T` 视为由公式键与环境集组成的候选关系，并追问每个匹配条目应服从哪些局部方程。答案由十条构造子子句和关于 `T` 第一投影的两项条件组成；语义正确性、唯一性、码域闭包以及典范数据的存在都还需要后续论证。
<!--ja-->
# 充足関係表を記述する

対象言語から、メタ言語にある論理式上の再帰を直接呼び出すことはできません。そこで、その再帰が作るべきグラフを有界な仕方で記述する必要があります。本章では `T` を、論理式の鍵と環境集合からなる候補関係とみなし、一致する各要素が従うべき局所方程式を調べます。その答えは十個の構成子の節と、`T` の第一射影に関する二条件です。意味論的な正しさ、一意性、符号領域の閉性、正準なデータの存在には、さらに後の議論が必要です。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

```

<!--en-->
There are two levels in this description. Agda supplies the metatheory in which the construction is checked, while the formulas constructed below belong to the first-order language of the constructible structure. The chapter assumes no excluded middle: it only assembles formulas from intuitionistically valid operations and proves a syntactic boundedness statement.
<!--zh-->
这项描述涉及两个层次。Agda 提供检查构造的元理论，而下文构造的公式属于可构造结构的一阶对象语言。本章不假设排中律：它只用直觉主义有效的运算组合公式，并证明一项句法有界性陈述。
<!--ja-->
この記述には二つの水準があります。Agda は構成を検査するメタ理論を与え、以下で組み立てる論理式は構成可能な構造の一階対象言語に属します。本章は排中律を仮定しません。直観主義的に妥当な演算から論理式を組み立て、構文上の有界性を示すだけだからです。
<!--/-->

```agda
open import Base.Prelude
module L.Coding.SatisfactionClauses {ℓ : Level} where

```

<!--en-->
A formula with `j` free slots is interpreted after those slots receive elements of the constructible carrier. Membership, equality, the propositional connectives, and bounded quantifiers are enough to state every clause below. The final Δ₀ witness will concern this object-language syntax; it will not by itself interpret the clauses or provide any of their witnesses.
<!--zh-->
带有 `j` 个自由槽的公式，要在这些槽取得可构造载体中的元素后才得到解释。隶属、相等、命题联结词与有界量词足以表述下文全部子句。末尾的 Δ₀ 见证只涉及这种对象语言构文；它本身既不解释子句，也不给出子句中的任何见证。
<!--ja-->
`j` 個の自由な枠をもつ論理式は、それらの枠に構成可能な台の元を入れてから解釈されます。所属、等号、命題結合子、有界量化子だけで、以下のすべての節を述べられます。最後の Δ₀ の証人が扱うのは、この対象言語の構文です。それだけで節を解釈したり、節に現れる証人を与えたりするものではありません。
<!--/-->

```agda
open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using
  ( Formula; Term; var; _∈̇_; _≐_; _∧̇_; _∨̇_; _⇒̇_; ⊤̇; ⊥̇; ∃̇∈; ∀̇∈ )
open import FOL.LevyHierarchy using ( checkΔ₀; Δ₀ )
open import L.Constructible {ℓ} using ( 𝒮ʟ )
```

<!--en-->
The candidate relation is expressed through coded ordered pairs. Three shapes organize the chapter: an environment-tower entry pairs an arity `ar` with an environment set `F`; a formula key pairs the same arity with a tagged payload; and a member of `T` pairs that key with a candidate value set. Bounded pair readers expose these components, while the successor and cons predicates describe the arity increase and the extension of an encoded environment.
<!--zh-->
候选关系借助编码有序对来表达。全章由三种形状组织：环境塔条目把元数 `ar` 与环境集 `F` 配对；公式键把同一元数与带标签的载荷配对；`T` 的成员再把该键与候选值集配对。有界配对读式暴露这些分量，而后继谓词与 cons 谓词分别描述元数提升和编码环境的延拓。
<!--ja-->
候補関係は符号化された順序対によって表されます。本章を組織する形は三つあります。環境の塔の要素はアリティ `ar` と環境集合 `F` を対にし、論理式の鍵は同じアリティとタグ付きペイロードを対にし、`T` の要素はその鍵と候補値集合をさらに対にします。有界な対の読みがこれらの成分を取り出し、後続と cons の述語がそれぞれアリティの増加と符号化環境の拡張を記述します。
<!--/-->

```agda
open import L.Coding.Model {ℓ} using ( prAtL )
open import L.Coding.Expressions {ℓ} using ( sucAtL; consAtL )
open import L.Coding.Quantification {ℓ} using
  ( f0; f1; i0; i1; i2; i3; i4; i5; i6; i8; i9; i11; i12; i14; i16; i17; i19; sh
  ; sndEx; sndAll; bothEx; bothAll; bigAnd )
```

<!--en-->
There are exactly ten formula-constructor positions, indexed by `Fin 10`. Converting such an index to a natural number lets one common family dispatch to the appropriate clause. The value stored in a tag slot is still an arbitrary parameter here; a later `Tags` hypothesis will identify each slot with its intended standard numeral.
<!--zh-->
公式构造子恰有十个位置，由 `Fin 10` 索引。把这样的索引转换为自然数，就能让同一个族分派到相应子句。此处标签槽中存放的值仍只是任意参数；后续的 `Tags` 假设才会把每个槽与预期的标准数码同一视。
<!--ja-->
論理式の構成子にはちょうど十個の位置があり、`Fin 10` で添字付けられます。その添字を自然数へ移すことで、一つの族から対応する節を選べます。ただし、ここでタグの枠に入る値はまだ任意のパラメータです。各枠を意図された標準数項と同定するのは、後の `Tags` 仮定です。
<!--/-->

```agda

open import Cubical.Data.Nat using ( _+_ )
open import Cubical.Data.FinData using ( toℕ )
open import Cubical.Data.Unit using ( tt )

```

<!--en-->
All object-language variables range over `S`, the carrier of the constructible structure. A slot such as `T`, `C`, or `w` names a position in an assignment; only after evaluation does that position denote a constructible set. Keeping this distinction prevents a syntactic clause from being mistaken for a metatheoretic construction of a table or a code set.
<!--zh-->
对象语言的所有变元都在可构造结构的载体 `S` 上取值。`T`、`C` 或 `w` 这样的槽只命名赋值中的位置；经过求值后，该位置才指称一个可构造集。区分这两层，可以避免把句法子句误当成在元理论中构造满足关系表或码集。
<!--ja-->
対象言語の変数はすべて、構成可能な構造の台 `S` 上を動きます。`T`、`C`、`w` のような枠は付値内の位置を名指すだけで、評価された後に初めて構成可能集合を表します。この区別により、構文上の節を、メタ理論における充足関係表や符号集合の構成と取り違えずに済みます。
<!--/-->

```agda
open hPropStructure 𝒮ʟ using ( S )
```

<!--en-->
## The table frame and its ten clauses
<!--zh-->
## 表框架及其十条子句
<!--ja-->
## 表の枠組みと十個の節
<!--/-->

<!--en-->
The first reusable idea is an exact extension condition. For a proposed set `y`, a reference set `F`, and a property `φ`, the first half of `extB` says that every member of `y` lies in `F` and satisfies `φ`; hence it gives one inclusion. The second half says that every member of `F` satisfying `φ` lies in `y`, giving the reverse inclusion. Thus `extB` characterizes `y` as the subset of `F` cut out by `φ`, but it neither constructs such a set nor asserts that one exists.
<!--zh-->
第一个可复用思想是精确的外延条件。给定候选集 `y`、参照集 `F` 与性质 `φ`，`extB` 的前半部说 `y` 的每个成员都属于 `F` 且满足 `φ`，因而给出一个包含方向；后半部说 `F` 中每个满足 `φ` 的成员都属于 `y`，给出反向包含。因此，`extB` 把 `y` 外延刻画为 `F` 中由 `φ` 截出的子集，但既不构造这个集合，也不断言它存在。
<!--ja-->
最初の再利用可能な考えは、正確な外延条件です。候補集合 `y`、基準集合 `F`、性質 `φ` に対し、`extB` の前半は `y` の各要素が `F` に属して `φ` を満たすと述べ、一方の包含を与えます。後半は、`F` のうち `φ` を満たすすべての要素が `y` に属すと述べ、逆の包含を与えます。したがって `extB` は `y` を、`F` の中で `φ` が切り出す部分集合として外延的に特徴づけますが、その集合を構成せず、存在も主張しません。
<!--/-->

```agda
extB : ∀ {j} → Fin j → Fin j → Formula S (1 + j) → Formula S j
extB y F φ = ∀̇∈ (var y) ((var i0 ∈̇ var (sh 1 F)) ∧̇ φ)
           ∧̇ ∀̇∈ (var F) (φ ⇒̇ (var i0 ∈̇ var (sh 1 y)))
```

<!--en-->
To inspect a coded pair when its second component `v` is already known, `fstAll` ranges universally through the bounded containers used by the pair coding. Whenever the pair predicate identifies a candidate first component, the body must hold with that component added to the assignment. The two bounded universals serve the set-theoretic representation of an ordered pair; mathematically this is one guarded reading of its first component, applied to every possible decomposition.
<!--zh-->
当编码对的第二分量 `v` 已知时，`fstAll` 在配对编码所用的容纳集合中作全称遍历。只要配对谓词识别出一个候选第一分量，主体就必须在把该分量加入赋值后成立。两层有界全称服务于有序对的集合论表示；数学上，这只是对第一分量的一次带守卫读取，并作用于每一种可能分解。
<!--ja-->
符号化された対の第二成分 `v` が既知のとき、`fstAll` は対の符号化に使われる容器を有界かつ全称的にたどります。対の述語が第一成分の候補を同定するたびに、その成分を付値へ加えたところで本体が成り立たなければなりません。二段の有界全称は順序対の集合論的表現のためにあり、数学的には、可能なすべての分解に対して第一成分を一度だけ条件付きで読む操作です。
<!--/-->

```agda
fstAll : ∀ {j} → Fin j → Fin j → Formula S (2 + j) → Formula S j
fstAll x v body = ∀̇∈ (var x) (∀̇∈ (var i0) (prAtL (sh 2 x) i0 (sh 2 v) ⇒̇ body))
```

<!--en-->
Formula recursion first needs a same-arity lookup. `subAt T ar a body` requires `body` for every entry of `T` whose key is the pair `(ar,a)`. It is a universal implication over matching entries, so it selects no entry and proves no value unique. If the key has no entry, the condition may hold vacuously; obtaining an entry later requires both totality and a separate proof that the child key belongs to the code domain.
<!--zh-->
公式递归首先需要同元数读取。`subAt T ar a body` 要求：对于 `T` 中键为配对 `(ar,a)` 的每个条目，`body` 都成立。它是关于全部匹配条目的全称蕴涵，因此既不选取条目，也不证明取值唯一。若该键没有条目，条件可能真空成立；后续要取得条目，还需同时使用全定义性以及子键属于码域的独立证明。
<!--ja-->
論理式上の再帰では、まず同じアリティでの読み取りが必要です。`subAt T ar a body` は、鍵が対 `(ar,a)` である `T` のすべての要素について `body` を要求します。これは一致する要素すべてに対する全称的な含意なので、要素を選ばず、値の一意性も示しません。その鍵に要素がなければ条件は空虚に成り立ちえます。後で要素を得るには、全域性に加え、子の鍵が符号領域に属するという別の証明が必要です。
<!--/-->

```agda
subAt : ∀ {j} → Fin j → Fin j → Fin j → Formula S (4 + j) → Formula S j
subAt T ar a body = ∀̇∈ (var T) (bothAll i0 (prAtL i1 (sh 4 ar) (sh 4 a) ⇒̇ body))
```

<!--en-->
A quantified formula has one more available variable in its body, so its recursive lookup must change the arity. `subSucAt T ar a body` considers every table entry whose key is `(ar',a)` and uses the additional guard `ar' = suc ar`; only then is `body` required. As with the same-arity reader, both the entry and the decomposition are universally quantified. The formula neither chooses `ar'` or a value nor guarantees that the raised child key occurs in `T`.
<!--zh-->
量化公式的主体多出一个可用变元，因此递归读取必须改变元数。`subSucAt T ar a body` 考察键为 `(ar',a)` 的每个表条目，并加入守卫 `ar' = suc ar`；只有满足该守卫时才要求 `body`。与同元数读式一样，条目及其分解都受全称量化。该公式既不选择 `ar'` 或某个取值，也不保证提升后的子键出现在 `T` 中。
<!--ja-->
量化された論理式の本体では利用できる変数が一つ増えるため、再帰的な読み取りはアリティを変えなければなりません。`subSucAt T ar a body` は、鍵が `(ar',a)` であるすべての表要素を調べ、さらに `ar' = suc ar` という条件を課してから `body` を要求します。同じアリティの読みと同様に、要素もその分解も全称的に量化されています。この論理式は `ar'` や値を選ばず、持ち上げられた子の鍵が `T` に現れることも保証しません。
<!--/-->

```agda
subSucAt : ∀ {j} → Fin j → Fin j → Fin j → Formula S (6 + j) → Formula S j
subSucAt T ar a body =
  ∀̇∈ (var T) (bothAll i0 (fstAll i1 (sh 4 a) (sucAtL (sh 6 ar) i0 ⇒̇ body)))
```

<!--en-->
Term evaluation has two code shapes. `tmIs t z v N0 N1` says that `t` is either the constant code carrying `v`, or a variable code carrying an index `i` for which the graph entry `(i,v)` belongs to the encoded environment `z`. The disjunction and the variable-index witness are interpreted under propositional truncation. Moreover, `N0` and `N1` are only tag slots until a later `Tags` hypothesis identifies them with zero and one; for an arbitrary multivalued `z`, the same variable code may validate several candidate values.
<!--zh-->
词项求值有两种码形状。`tmIs t z v N0 N1` 说：`t` 或是携带 `v` 的常元码，或是携带索引 `i` 的变元码，并且编码环境 `z` 含有图条目 `(i,v)`。析取和变元索引见证都在命题截断下解释。此外，在后续 `Tags` 假设把 `N0`、`N1` 与零号、一号数码同一视之前，它们只是标签槽；对于任意多值关系 `z`，同一个变元码可能验证多个候选值。
<!--ja-->
項の評価には二つの符号形があります。`tmIs t z v N0 N1` は、`t` が `v` を収めた定数の符号であるか、添字 `i` を収めた変数の符号であり、グラフ要素 `(i,v)` が符号化環境 `z` に属することを述べます。選言と変数添字の証人は、命題的切り詰めの下で解釈されます。また、後の `Tags` 仮定が `N0` と `N1` をゼロと一の数項に同定するまでは、これらはタグの枠にすぎません。任意の多値関係 `z` では、同じ変数符号が複数の候補値を検証しえます。
<!--/-->

```agda
tmIs : ∀ {j} → Fin j → Fin j → Fin j → Fin j → Fin j → Formula S j
tmIs t z v N0 N1 =
  prAtL t N0 v ∨̇ sndEx t N1 (∃̇∈ (var (sh 2 z)) (prAtL i0 i1 (sh 3 v)))
```

<!--en-->
The five constructor relations below share three parameters: the candidate relation `T`, the carrier bound `w`, and the family of ten tag slots `N`. Their local names `N0` and `N1` merely shift the first two tag slots past newly bound variables. This bookkeeping preserves which slots are referenced; it adds no equation identifying those slots with standard numerals.
<!--zh-->
下文五种构造子关系共享三个参数：候选关系 `T`、载体界限 `w` 与十个标签槽组成的族 `N`。局部名称 `N0`、`N1` 只把前两个标签槽移过新绑定的变元。这项簿记保持槽位指称不变，并不添加把它们识别为标准数码的等式。
<!--ja-->
以下の五つの構成子関係は、候補関係 `T`、台を与える境界 `w`、十個のタグ枠からなる族 `N` という三つのパラメータを共有します。局所名 `N0` と `N1` は、最初の二つのタグ枠を、新たに束縛された変数の先まで移すだけです。この添字の調整は参照先を保ちますが、枠を標準数項と同定する等式は加えません。
<!--/-->

```agda
module Rel {m : ℕ} (T w : Fin m) (N : Fin 10 → Fin m) where
  private
    N0 N1 : ∀ {j} → Fin (j + m)
    N0 {j} = sh j (N f0)
    N1 {j} = sh j (N f1)
```

<!--en-->
Once the two child values `ya` and `yb` have been read, a binary clause asks how one encoded environment `z` relates to them. The two propositions are simply `z ∈ ya` and `z ∈ yb`; the parameter `op` combines them. Instantiating `op` by conjunction, disjunction, or implication preserves the corresponding polarity without collapsing all three connectives into the same condition.
<!--zh-->
读出两个子公式取值 `ya`、`yb` 后，二元子句要判断同一个编码环境 `z` 与它们的关系。两个命题就是 `z ∈ ya` 与 `z ∈ yb`，参数 `op` 再把它们组合起来。把 `op` 分别实例化为合取、析取或蕴涵，就会保留相应极性，而不会把三种联结词压成同一种条件。
<!--ja-->
二つの子の値 `ya` と `yb` を読んだ後、二項の節は、一つの符号化環境 `z` がそれらとどう関わるかを調べます。二つの命題は単に `z ∈ ya` と `z ∈ yb` であり、パラメータ `op` がそれらを結びます。`op` を連言、選言、含意でそれぞれ具体化することで、三つを同じ条件へ押し込めず、対応する極性を保てます。
<!--/-->

```agda
  binBody : (∀ {j} → Formula S j → Formula S j → Formula S j) → Formula S (24 + m)
  binBody op = op (var i0 ∈̇ var i5) (var i0 ∈̇ var i1)
```

<!--en-->
For an unbounded quantifier of the encoded formula, the describing formula uses `w` as an explicit bound. With `q` instantiated by `∃[]-syntax`, it merely asserts under propositional truncation that some `x ∈ w` works; with `q` instantiated by `∀[]-syntax`, every `x ∈ w` must work. In either case the inner condition merely asks for an encoded extension `e'` in the body-value set such that `e'` is obtained by consing `x` onto `z`. This inner existence is propositionally truncated and supplies no globally chosen extension function.
<!--zh-->
对于被编码公式中的非有界量词，描述公式用 `w` 作为显式界限。当 `q` 实例化为 `∃[]-syntax` 时，它只在命题截断下断言某个 `x ∈ w` 可行；当 `q` 实例化为 `∀[]-syntax` 时，每个 `x ∈ w` 都必须可行。无论哪种情形，内层条件都只要求命题截断地存在主体取值集中的编码延拓 `e'`，使 `e'` 由把 `x` cons 到 `z` 前端得到；这里不会给出全局选定的延拓函数。
<!--ja-->
符号化された論理式の非有界量化子を記述するとき、記述側の論理式は `w` を明示的な境界として使います。`q` を `∃[]-syntax` とすれば、ある `x ∈ w` が条件を満たすことを命題的切り詰めの下で主張するだけです。`∀[]-syntax` とすれば、すべての `x ∈ w` が条件を満たさなければなりません。どちらの場合も内側の条件は、`x` を `z` の先頭へ cons して得られる符号化拡張 `e'` が本体の値集合に命題的に切り詰められて存在することだけを求めます。大域的に選ばれた拡張関数は得られません。
<!--/-->

```agda
  quBody : (∀ {j} → Term S j → Formula S (suc j) → Formula S j) → Formula S (19 + m)
  quBody q = q (var (sh 19 w)) (∃̇∈ (var i4) (consAtL i0 i1 i2))
```

<!--en-->
A bounded quantifier must also evaluate its bound term. For the universal case, `∀[]-syntax` together with implication requires every candidate `v` validated by `tmIs`, and then every `x ∈ w` belonging to `v`, to admit a merely existing encoded extension in the body-value set. For the existential case, `∃[]-syntax` together with conjunction asks merely for such a validated `v`, such an `x`, and such an extension. If the encoded environment relation is multivalued, these polarities remain significant; this clause does not repair it or prove term values unique.
<!--zh-->
有界量词还必须求出界词项的值。全称情形以 `∀[]-syntax` 配合蕴涵，要求 `tmIs` 验证的每个候选值 `v`，以及 `w` 中属于 `v` 的每个 `x`，都有一个命题截断地存在于主体取值集中的编码延拓。存在情形则以 `∃[]-syntax` 配合合取，只要求命题截断地存在这样的 `v`、`x` 与延拓。若编码环境关系是多值的，这两种极性仍有实质差别；本子句不会修复该关系，也不证明词项值唯一。
<!--ja-->
有界量化子では、境界となる項の値も求めなければなりません。全称の場合は `∀[]-syntax` と含意を組み合わせ、`tmIs` が検証するすべての候補値 `v`、さらに `v` に属するすべての `x ∈ w` について、本体の値集合に符号化拡張が命題的に切り詰められて存在することを要求します。存在の場合は `∃[]-syntax` と連言を組み合わせ、そのような `v`、`x`、拡張が命題的に切り詰められて存在すれば十分です。符号化環境の関係が多値なら、この極性の違いは実質的です。この節は関係を修復せず、項の値の一意性も示しません。
<!--/-->

```agda
  bqBody : (∀ {j} → Term S j → Formula S (suc j) → Formula S j)
         → (∀ {j} → Formula S j → Formula S j → Formula S j) → Formula S (22 + m)
  bqBody q c =
    q (var (sh 22 w)) (c (tmIs i9 i1 i0 N0 N1)
      (q (var (sh 23 w)) (c (var i0 ∈̇ var i1) (∃̇∈ (var i5) (consAtL i0 i1 i3)))))
```

<!--en-->
Atomic formulas do not recurse through formula children. Their payload consists of two term codes, so the atomic body merely asks, under propositional truncation, for two values `v,x ∈ w` validated by `tmIs`, and then tests the chosen atomic relation on them. Membership uses `v ∈ x`, while equality compares `v` and `x`; the term values come directly from the constant or variable shape rather than from entries of `T`.
<!--zh-->
原子公式不对子公式作递归。它的载荷由两个词项码组成，因此原子主体只在命题截断下要求存在两个由 `tmIs` 验证的值 `v,x ∈ w`，再在其上检验指定的原子关系。隶属情形使用 `v ∈ x`，相等情形比较 `v` 与 `x`；词项值直接来自常元或变元码形状，而不是来自 `T` 的条目。
<!--ja-->
原子論理式は子論理式を再帰的に参照しません。そのペイロードは二つの項の符号からなるので、原子の本体は、`tmIs` で検証される二つの値 `v,x ∈ w` が命題的に切り詰められて存在することを求め、その上で指定された原子関係を検査します。所属の場合は `v ∈ x` を使い、等号の場合は `v` と `x` を比較します。項の値は `T` の要素からではなく、定数または変数の符号形から直接得られます。
<!--/-->

```agda
  atomBody : Formula S (18 + m) → Formula S (16 + m)
  atomBody rel =
    ∃̇∈ (var (sh 16 w)) (∃̇∈ (var (sh 17 w))
      (tmIs i4 i2 i1 N0 N1 ∧̇ (tmIs i3 i2 i0 N0 N1 ∧̇ rel)))

```

<!--en-->
Falsity gives the simplest extension equation. Its property is impossible, so the forward inclusion says that the candidate value `yc` has no members. The reverse inclusion is immediate because no member of `F` can satisfy falsity. Thus the clause characterizes `yc` as empty without constructing an empty value or a table entry.
<!--zh-->
假命题给出最简单的外延方程。它的性质不可能成立，所以正向包含说明候选值 `yc` 没有成员；反向包含则因 `F` 中没有成员能满足假命题而立即成立。因此，这条子句把 `yc` 刻画为空，却不构造空值或表条目。
<!--ja-->
偽は最も単純な外延方程式を与えます。その性質は成り立ちえないので、順方向の包含は候補値 `yc` に要素がないことを述べます。逆方向の包含は、`F` の要素が偽を満たすことはないため直ちに成り立ちます。こうしてこの節は `yc` を空集合として特徴づけますが、空の値や表要素を構成しません。
<!--/-->

```agda
  botRel : Formula S (12 + m)
  botRel = extB i0 i8 ⊥̇

```

<!--en-->
For a binary connective, the payload is decomposed into two formula codes `a` and `b`. The two same-arity readers then range over every value of `T` matching the child keys `(ar,a)` and `(ar,b)`. For every resulting pair of child values, `extB` characterizes `yc` by the binary body. A multivalued candidate relation therefore imposes the equation for every combination; this relation constructor assumes neither existence nor uniqueness of either child value.
<!--zh-->
对于二元联结词，载荷先分解为两个公式码 `a`、`b`。随后，两次同元数读取遍历 `T` 中与子键 `(ar,a)`、`(ar,b)` 匹配的每个取值。对于所得子值的每一种组合，`extB` 都借助二元主体刻画 `yc`。因此，多值候选关系会对所有组合施加方程；这个关系构造子既不假设子值存在，也不假设它们唯一。
<!--ja-->
二項結合子では、ペイロードを二つの論理式符号 `a` と `b` に分解します。続く二回の同アリティ読み取りは、子の鍵 `(ar,a)` と `(ar,b)` に一致する `T` のすべての値をたどります。得られる子の値の組合せごとに、`extB` が二項の本体によって `yc` を特徴づけます。したがって候補関係が多値なら、すべての組合せに方程式が課されます。この関係構成子は、どちらの子の値についても存在や一意性を仮定しません。
<!--/-->

```agda
  binRel : (∀ {j} → Formula S j → Formula S j → Formula S j) → Formula S (12 + m)
  binRel op =
    bothAll i3 (subAt (sh 15 T) i12 i1 (subAt (sh 19 T) i16 i4 (extB i11 i19 (binBody op))))

```

<!--en-->
The payload of an unbounded quantified formula is its body code. The relation reads that code only at successor arity and then uses `extB` to compare the candidate value with the environments satisfying the quantifier body. Although the encoded quantifier ranges semantically over the whole intended carrier, the describing formula ranges over the explicit set `w`; this is what keeps the description bounded.
<!--zh-->
非有界量化公式的载荷就是其主体码。该关系只在后继元数处读取这个码，再用 `extB` 比较候选值与满足量词主体的环境。被编码量词在语义上遍历整个预期载体，而描述公式则以显式集合 `w` 为界遍历；正因如此，描述仍保持有界。
<!--ja-->
非有界量化論理式のペイロードは、その本体の符号です。この関係はその符号を後続アリティでだけ読み、`extB` によって、候補値と量化子本体を満たす環境とを比較します。符号化された量化子は意味論的には意図された台全体を動きますが、記述側の論理式は明示された集合 `w` の上を動きます。このため記述は有界に保たれます。
<!--/-->

```agda
  quRel : (∀ {j} → Term S j → Formula S (suc j) → Formula S j) → Formula S (12 + m)
  quRel q = subSucAt (sh 12 T) i9 i3 (extB i6 i14 (quBody q))

```

<!--en-->
The payload of a bounded quantifier is a pair `(t,a)` of a bound-term code and a body code. Only `a` is looked up recursively, again at successor arity; `t` is evaluated locally by `tmIs`. The two parameters will later give the exact polarities: the bounded universal uses `∀[]-syntax` with implication, and the bounded existential uses `∃[]-syntax` with conjunction.
<!--zh-->
有界量词的载荷是由界词项码与主体码组成的配对 `(t,a)`。只有 `a` 会在后继元数处接受递归读取；`t` 则由 `tmIs` 在局部求值。两个参数随后给出精确极性：有界全称使用 `∀[]-syntax` 配合蕴涵，有界存在使用 `∃[]-syntax` 配合合取。
<!--ja-->
有界量化子のペイロードは、境界となる項の符号と本体の符号からなる対 `(t,a)` です。再帰的に読み取られるのは `a` だけで、ここでも後続アリティが使われます。`t` は `tmIs` によって局所的に評価されます。二つのパラメータが後で正確な極性を与えます。有界全称は `∀[]-syntax` と含意を使い、有界存在は `∃[]-syntax` と連言を使います。
<!--/-->

```agda
  bqRel : (∀ {j} → Term S j → Formula S (suc j) → Formula S j)
        → (∀ {j} → Formula S j → Formula S j → Formula S j) → Formula S (12 + m)
  bqRel q c = bothAll i3 (subSucAt (sh 15 T) i12 i0 (extB i9 i17 (bqBody q c)))

```

<!--en-->
For an atomic payload, the pair reader exposes the two term codes and `extB` applies the atomic body to every candidate encoded environment in `F`. No child key is read from `T`. This separation reflects the syntax tree: formulas recurse through immediate subformulas, whereas the very small term language is interpreted directly by its two code shapes.
<!--zh-->
对于原子载荷，配对读式暴露两个词项码，`extB` 再把原子主体用于 `F` 中每个候选编码环境。这里不会从 `T` 读取任何子键。这一区分反映了语法树：公式沿直接子公式递归，而这个很小的词项语言则直接按两种码形状解释。
<!--ja-->
原子のペイロードでは、対の読みが二つの項符号を取り出し、`extB` が `F` 内の候補となる各符号化環境に原子の本体を適用します。`T` から子の鍵を読むことはありません。この区別は構文木を反映しています。論理式は直下の部分論理式を再帰的にたどりますが、この小さな項言語は二つの符号形から直接解釈されます。
<!--/-->

```agda
  atomRel : Formula S (18 + m) → Formula S (12 + m)
  atomRel rel = bothAll i3 (extB i3 i11 (atomBody rel))

```

<!--en-->
The first four tags state four exact truth conditions. Once the tag slots have been calibrated by `Tags`, tag 0 is the membership atom: if `v` and `x` are the respective values of the first and second terms, it requires `v ∈ x`. Tag 1 is the equality atom and requires `v = x`. Tags 2 and 3 combine the same-arity child assertions `z ∈ ya` and `z ∈ yb` by conjunction and disjunction, respectively. Before that calibration, these are clauses selected by the corresponding tag slots, not claims that the slots already contain the standard numerals.
<!--zh-->
前四个标签给出四种精确真值条件。在 `Tags` 校准标签槽之后，标签 0 是隶属原子：若 `v` 与 `x` 分别是第一、第二个词项的值，则要求 `v ∈ x`。标签 1 是相等原子，要求 `v = x`。标签 2、3 分别用合取与析取组合两个同元数子公式的断言 `z ∈ ya` 与 `z ∈ yb`。在校准之前，这些只是由相应标签槽选出的子句，不能据此断言槽中已经放置标准数码。
<!--ja-->
最初の四つのタグは、四つの正確な真理条件を述べます。タグの枠が `Tags` によって校正されると、タグ 0 は所属原子になります。`v` と `x` がそれぞれ第一、第二の項の値なら、必要な条件は `v ∈ x` です。タグ 1 は等号原子で、`v = x` を要求します。タグ 2 と 3 は、同じアリティの子に関する二つの主張 `z ∈ ya` と `z ∈ yb` を、それぞれ連言と選言で結びます。校正より前には、これらは対応するタグの枠によって選ばれる節にすぎず、その枠に標準の数項がすでに入っているとはいえません。
<!--/-->

```agda
  relN : ℕ → Formula S (12 + m)
  relN 0 = atomRel (var i1 ∈̇ var i0)
  relN 1 = atomRel (var i1 ≐ var i0)
  relN 2 = binRel _∧̇_
  relN 3 = binRel _∨̇_
```

<!--en-->
Tag 4 has the remaining binary polarity: `z ∈ ya` implies `z ∈ yb`, from the left child to the right child. Tag 5 gives falsity its empty extension. Tags 6 and 7 read one body at successor arity; tag 6 uses `∃[]-syntax` over `w`, while tag 7 uses `∀[]-syntax`. Tag 8 is the bounded universal. For every `v ∈ w`, `tmIs` is the antecedent that verifies `v` as a value of the bound term; for every `x ∈ w`, membership `x ∈ v` is then the antecedent to the propositionally truncated existence of an encoded extension in the body-value set.
<!--zh-->
标签 4 给出余下的二元极性：`z ∈ ya` 从左子公式向右子公式蕴涵 `z ∈ yb`。标签 5 使假命题具有空外延。标签 6、7 都在后继元数处读取一个主体；标签 6 在 `w` 上使用 `∃[]-syntax`，标签 7 使用 `∀[]-syntax`。标签 8 是有界全称。对每个 `v ∈ w`，`tmIs` 作为前件验证 `v` 是界词项的值；随后对每个 `x ∈ w`，成员关系 `x ∈ v` 又作为前件，要求命题截断地存在主体取值集中的编码延拓。
<!--ja-->
タグ 4 は、残る二項の極性を与えます。左の子から右の子へ、`z ∈ ya` が `z ∈ yb` を含意します。タグ 5 は、偽の外延を空にします。タグ 6 と 7 は一つの本体を後続アリティで読み、タグ 6 は `w` 上の `∃[]-syntax`、タグ 7 は `∀[]-syntax` を使います。タグ 8 は有界全称です。各 `v ∈ w` について、`tmIs` は `v` が境界となる項の値であることを検証する前件です。続いて各 `x ∈ w` について、所属 `x ∈ v` が前件となり、本体の値集合に符号化拡張が命題的に切り詰められて存在することを要求します。
<!--/-->

```agda
  relN 4 = binRel _⇒̇_
  relN 5 = botRel
  relN 6 = quRel ∃̇∈
  relN 7 = quRel ∀̇∈
  relN 8 = bqRel ∀̇∈ _⇒̇_
```

<!--en-->
Tag 9 has the existential polarity. Using `∃[]-syntax` with conjunction, it merely requires some `v ∈ w` validated by `tmIs`, some `x ∈ w` with `x ∈ v`, and a merely existing encoded extension in the body-value set. This completes the ten cases numbered 0 through 9. For natural numbers at least 10, `relN` returns truth, but this last equation contributes no case to the table specification: if `k : Fin 10`, then `toℕ k` is always between 0 and 9.
<!--zh-->
标签 9 具有存在极性。它用 `∃[]-syntax` 配合合取，只要求命题截断地存在由 `tmIs` 验证的某个 `v ∈ w`、满足 `x ∈ v` 的某个 `x ∈ w`，以及主体取值集中的某个编码延拓。至此得到编号 0 至 9 的十种情形。对不小于 10 的自然数，`relN` 返回真；但最后这条方程不会给表规格增加任何情形，因为当 `k : Fin 10` 时，`toℕ k` 必在 0 至 9 之间。
<!--ja-->
タグ 9 は存在の極性をもちます。`∃[]-syntax` と連言を使い、`tmIs` で検証されるある `v ∈ w`、`x ∈ v` を満たすある `x ∈ w`、および本体の値集合にある符号化拡張が、命題的に切り詰められて存在することだけを要求します。これで 0 から 9 までの十個の場合がそろいます。10 以上の自然数に対して `relN` は真を返しますが、この最後の方程式が表の仕様に場合を加えることはありません。`k : Fin 10` ならば、`toℕ k` は必ず 0 から 9 までの間にあるからです。
<!--/-->

```agda
  relN 9 = bqRel ∃̇∈ _∧̇_
  relN (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc _)))))))))) = ⊤̇
```

<!--en-->
We can now place a constructor relation into the common frame. The data to be connected are an environment-tower pair, a formula code of the same arity with a tagged payload, and a candidate entry of `T` at that code. The local relation module is reused so that every tag is judged with the same meanings of `T`, `w`, and the two term-code tags.
<!--zh-->
现在可以把构造子关系放入共同框架。需要连接的数据包括一个环境塔配对、一个具有相同元数与带标签载荷的公式码，以及 `T` 在该码处的候选条目。这里复用同一个局部关系模块，使每个标签都在相同的 `T`、`w` 与两个词项码标签解释下接受判断。
<!--ja-->
これで構成子関係を共通の枠へ置けます。結び付けるデータは、環境の塔の対、同じアリティとタグ付きペイロードをもつ論理式符号、そしてその符号における `T` の候補要素です。同じ局所関係モジュールを再利用することで、どのタグも同じ `T`、`w`、二つの項符号タグの解釈の下で判定されます。
<!--/-->

```agda
module Clause {m : ℕ} (T w C E : Fin m) (N : Fin 10 → Fin m) where
  private
    module R = Rel T w N

```

<!--en-->
For a fixed `k`, the clause follows a precise chain. It considers every `q ∈ E` and every decomposition `q=(ar,F)`; every `c ∈ C` with `c=(ar,p)`; every decomposition `p=(N k,r)`; and every `e ∈ T` with `e=(c,yc)`. At each complete matching frame, `yc` must satisfy `relN (toℕ k)`. Every decomposition is guarded by a universal implication, so the clause does not assert that any of this frame data exists. It also treats `F` and `N k` only as supplied values, without identifying them with a genuine environment set or the numeral for `k`.
<!--zh-->
固定 `k` 后，子句沿一条精确链条展开。它考察每个 `q ∈ E` 及其每种分解 `q=(ar,F)`；每个满足 `c=(ar,p)` 的 `c ∈ C`；每种分解 `p=(N k,r)`；以及每个满足 `e=(c,yc)` 的 `e ∈ T`。在每个完整匹配的框架上，`yc` 都必须满足 `relN (toℕ k)`。每次分解都由全称蕴涵守卫，因此该子句并不断言这些框架数据存在。它也只把 `F` 与 `N k` 当作给定值，并不把它们认同为真实环境集或 `k` 对应的数码。
<!--ja-->
`k` を固定すると、節は正確な連鎖をたどります。すべての `q ∈ E` と各分解 `q=(ar,F)`、`c=(ar,p)` を満たすすべての `c ∈ C`、各分解 `p=(N k,r)`、さらに `e=(c,yc)` を満たすすべての `e ∈ T` を考えます。完全に一致する各枠において、`yc` は `relN (toℕ k)` を満たさなければなりません。各分解は全称的な含意で条件付けられているため、この節はこれらの枠のデータが存在するとは主張しません。また、`F` と `N k` を与えられた値として扱うだけで、真の環境集合や `k` に対応する数項とは同定しません。
<!--/-->

```agda
  clause : Fin 10 → Formula S m
  clause k =
    ∀̇∈ (var E) (bothAll i0 (∀̇∈ (var (sh 4 C)) (sndAll i0 i2 (sndAll i0 (sh 7 (N k))
      (∀̇∈ (var (sh 9 T)) (sndAll i0 i5 (R.relN (toℕ k))))))))
```

<!--en-->
The two domain conditions supply the existence that the universal local clauses lack. `total` says that for every `c ∈ C`, there merely exists a `yc` with `(c,yc) ∈ T`; both the table member and its pair decomposition remain under propositional truncation. Conversely, `onC` says that every `e ∈ T` merely decomposes as `(c,yc)` with `c ∈ C`. Together they identify the first-projection domain of `T` with `C`, but they provide no choice function and do not make `T` single-valued.
<!--zh-->
两条定义域条件补充全称局部子句本身没有给出的存在性。`total` 说：对于每个 `c ∈ C`，命题截断地存在 `yc`，使 `(c,yc) ∈ T`；表成员及其配对分解都留在命题截断内。反过来，`onC` 说每个 `e ∈ T` 都命题截断地分解为 `(c,yc)`，且 `c ∈ C`。二者合起来把 `T` 的第一投影定义域确定为 `C`，但不给出选择函数，也不使 `T` 成为单值关系。
<!--ja-->
二つの領域条件は、全称的な局所節だけでは得られない存在を補います。`total` は、各 `c ∈ C` について、`(c,yc) ∈ T` となる `yc` が命題的に切り詰められて存在すると述べます。表要素もその対分解も切り詰めの内部に残ります。逆に `onC` は、すべての `e ∈ T` が、`c ∈ C` である `(c,yc)` として命題的に切り詰められて分解されると述べます。二条件を合わせると `T` の第一射影の領域は `C` になりますが、選択関数は得られず、`T` が単値になることもありません。
<!--/-->

```agda
  total onC : Formula S m
  total = ∀̇∈ (var C) (∃̇∈ (var (sh 1 T)) (sndEx i0 i1 ⊤̇))
  onC = ∀̇∈ (var T) (bothEx i0 (var i1 ∈̇ var (sh 4 C)))

```

<!--en-->
The ten local clauses are gathered by one finite conjunction. The argument `9` means that the indexing type is `Fin (suc 9)`, hence `Fin 10`; it does not omit a case. Ordinary conjunction and this finite conjunction introduce no new propositional truncation beyond any truncation already present inside the individual clauses.
<!--zh-->
十条局部子句由一个有限合取收集。参数 `9` 意味着索引类型是 `Fin (suc 9)`，也就是 `Fin 10`，并没有漏掉一种情形。普通合取与这个有限合取都不会在各子句已有的命题截断之外引入新的命题截断。
<!--ja-->
十個の局所節は、一つの有限連言にまとめられます。引数 `9` が意味する添字型は `Fin (suc 9)`、すなわち `Fin 10` であり、一つのケースが欠けているわけではありません。通常の連言もこの有限連言も、個々の節の内部にすでにある命題的切り詰めに加えて、新たな切り詰めを導入しません。
<!--/-->

```agda
  ten : Formula S m
  ten = bigAnd 9 clause

```

<!--en-->
The formula `tableAt` now conjoins three demands: truncated totality over `C`, the restriction of every table member to a key in `C`, and all ten constructor clauses. This is a local bounded specification for a candidate relation. It does not prove that `C` is closed under child codes, that `E` is the intended environment tower, that the tags are standard, that values are unique, or that the candidate is a canonical satisfaction table. Later chapters separately supply the tower and code descriptions, tag calibration, semantic bridges, and pinning arguments needed to relate suitable candidates to canonical data.
<!--zh-->
公式 `tableAt` 现在合取三项要求：在 `C` 上经过命题截断的全定义性、每个表成员的键都属于 `C` 的限制，以及全部十条构造子子句。这是一条关于候选关系的局部有界规格。它不证明 `C` 对子公式码封闭，不证明 `E` 是预期的环境塔，不校准标签，不证明取值唯一，也不把候选关系认同为典范满足关系表。后续章节会分别给出环境塔与码域描述、标签校准、语义桥接和钉扎论证，从而把适当候选对象与典范数据联系起来。
<!--ja-->
論理式 `tableAt` は三つの要求を連言します。`C` 上の命題的に切り詰められた全域性、各表要素の鍵が `C` に属するという制限、そして十個すべての構成子の節です。これは候補関係に対する局所的で有界な仕様です。`C` が子の符号について閉じていること、`E` が意図された環境の塔であること、タグが標準的であること、値が一意であること、候補が正準な充足関係表であることは証明しません。後の章が、環境の塔と符号領域の記述、タグの校正、意味論的な橋渡し、固定の議論をそれぞれ与え、適切な候補を正準なデータへ結び付けます。
<!--/-->

```agda
tableAt : ∀ {m} → Fin m → Fin m → Fin m → Fin m → (Fin 10 → Fin m) → Formula S m
tableAt T w C E N = Clause.total T w C E N ∧̇ (Clause.onC T w C E N ∧̇ Clause.ten T w C E N)

```

<!--en-->
Finally, the structural checker yields a witness that `tableAt` is Δ₀. Every apparent search is bounded by `T`, `C`, `E`, `w`, a pair container, or a candidate value set, so no unbounded quantifier enters the describing formula. This conclusion classifies the syntax only: it proves neither that a suitable table exists nor that any candidate satisfies the clauses, and it establishes no semantic correctness, absoluteness, or completeness theorem.
<!--zh-->
最后，结构检查器给出 `tableAt` 属于 Δ₀ 的见证。每一处看似搜索的量化都受 `T`、`C`、`E`、`w`、某个配对容纳集合或候选值集限制，因此描述公式没有引入非有界量词。这个结论只分类句法：它既不证明合适的表存在，也不证明任何候选对象满足这些子句，更不建立语义正确性、绝对性或完备性定理。
<!--ja-->
最後に、構造検査は `tableAt` が Δ₀ であることの証人を与えます。探索に見える量化はすべて、`T`、`C`、`E`、`w`、対の容器、または候補値集合のいずれかで制限されるため、記述する論理式に非有界量化子は入りません。この結論は構文を分類するだけです。適切な表の存在も、候補が各節を満たすことも示さず、意味論的な正しさ、絶対性、完全性のいずれも確立しません。
<!--/-->

```agda
Δ₀-tableAt : ∀ {m} (T w C E : Fin m) (N : Fin 10 → Fin m) → Δ₀ (tableAt T w C E N)
Δ₀-tableAt T w C E N = checkΔ₀ (tableAt T w C E N) tt
```

<!--en-->
## Recap

The formula `tableAt` is the conjunction of `total`, `onC`, and the ten local constructor clauses collected by `ten`. Here `total` gives only propositionally truncated existence of a table value for each code in `C`; `onC` restricts the first-projection domain to `C`; and the ten clauses impose universal local extension equations. The theorem `Δ₀-tableAt` certifies only that this description is syntactically bounded.

Further arguments must still identify `E` as the intended environment tower, prove that `C` contains the required child codes, calibrate the tag slots through `Tags`, and establish the two-way semantic readings, pinning, and completeness needed for the canonical graph and the global predicate `satAt`. None of those results, and no table or globally chosen value, is constructed in this chapter.
<!--zh-->
## 小结

公式 `tableAt` 是 `total`、`onC` 与由 `ten` 收集的十条局部构造子子句之合取。其中，`total` 只给出 `C` 中每个码的表取值在命题截断下的存在性；`onC` 把第一投影定义域限制为 `C`；十条子句则施加全称的局部外延方程。定理 `Δ₀-tableAt` 只证明这份描述在句法上有界。

后续论证仍需把 `E` 认同为预期环境塔，证明 `C` 含有所需的子公式码，通过 `Tags` 校准标签槽，并建立双向语义读式、钉扎与完备性，才能得到典范图与总体谓词 `satAt`。这些结论以及满足关系表或全局选定的取值都不是本章构造的对象。
<!--ja-->
## まとめ

論理式 `tableAt` は、`total`、`onC`、および `ten` が集める十個の局所的な構成子の節の連言です。ここで `total` が与えるのは、`C` の各符号に対する表の値の命題的に切り詰められた存在だけです。`onC` は第一射影の領域を `C` に制限し、十個の節は全称的な局所外延方程式を課します。定理 `Δ₀-tableAt` が保証するのは、この記述が構文上有界であることだけです。

さらに後の議論で、`E` を意図された環境の塔と同定し、`C` が必要な子の符号を含むことを証明し、`Tags` によってタグの枠を校正し、正準なグラフと全体の述語 `satAt` に必要な双方向の意味論的な読み、固定、および完全性を確立しなければなりません。それらの結果も、充足関係表や大域的に選ばれた値も、この章では構成されません。
<!--/-->
