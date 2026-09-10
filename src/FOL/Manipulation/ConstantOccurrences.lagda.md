<!--en-->
# Constants by occurrence

Parameter abstraction needs a finite list of a formula's constants without assuming decidable equality on the constant domain. This chapter therefore counts and enumerates constant occurrences, preserving repetitions, and develops the index arithmetic that places their replacement variables after the existing free variables.

A formula's constants form an ordered list of occurrences. This chapter counts and enumerates them, supplies the index arithmetic used by abstraction, and handles the boundary case in which the list is empty.
<!--zh-->
# 逐次出现地处理常元

参数抽象需要公式常元的有限列表，但不能假设常元域上的相等可判定。因此本章逐次出现地计数并枚举常元，保留重复项，再建立把替代变量放在已有自由变量之后所需的指标算术。

公式的常元组成一列有序的出现。本章计数并枚举这些出现，给出抽象所需的序号算术，并处理该列为空的边界情形。
<!--ja-->
# 出現ごとに扱う定数

パラメータ抽象には論理式の定数の有限リストが必要ですが、定数域の等号が判定可能とは仮定できません。そこで本章では重複を残したまま定数の出現を数えて列挙し、その置換変数を既存の自由変数の後ろへ配置する添字計算を整えます。

論理式の定数は、出現の順序付きリストをなします。本章はそれらを数えて列挙し、抽象で使う添字計算を与え、リストが空になる境界の場合を扱います。
<!--/-->

<!--en-->
Parameter abstraction rewrites a formula that mentions constants as a parameter-free formula of higher arity, together with the list of constants that the new variables will stand for. The construction needs that list to be finite, but it may not assume that equality on the constant domain is decidable, so it cannot merge or deduplicate entries. Two occurrences of the same constant therefore stay two separate positions, each later receiving its own replacement variable. The work divides into three steps: count the occurrences, enumerate them in order, and develop the index arithmetic that places the new variables after the existing free variables.
<!--zh-->
参数抽象把一条提及常元的公式改写为一条元数更高的无参公式，同时给出常元的列表，让新的变量逐个对应这些常元。构造需要这个列表是有限的，但不能假设常元域上的相等可判定，因此不能合并或去重条目。同一常元的两次出现因此保持为两个独立的位置，日后各自获得自己的替代变量。工作分三步：计数出现，按序枚举出现，再建立把新变量放在已有自由变量之后的序号算术。
<!--ja-->
パラメータの抽象化は、定数に言及する論理式を、より高いアリティの無パラメータ論理式へと組み替え、新しい変数が代わりを務める定数のリストを同時に与えます。このリストは有限でなければなりませんが、定数域の等号が判定可能であるとは仮定できないため、項目を統合したり重複を取り除いたりすることはできません。同じ定数の二つの出現は二つの独立した位置のままであり、後でそれぞれが専用の置換変数を受け取ります。仕事は三段階に分かれます。出現を数えること、出現を順に列挙すること、そして新しい変数を既存の自由変数の後ろへ置く添字計算を整えることです。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

module FOL.Manipulation.ConstantOccurrences where

open import Base.Prelude
open import FOL.Syntax using
  ( Term; con; var; Formula; _∈̇_; _≐_; _∧̇_; _∨̇_; _⇒̇_; ⊥̇; ∃̇_; ∀̇_; ∀̇∈; ∃̇∈ )
```

<!--en-->
Concretely, a formula's constants are read off as an ordered list of occurrences: each time a constant appears, anywhere in a term or under any quantifier, it occupies the next position of the list. Counting and enumerating then go together. The count is a natural number recording how many occurrences there are; the enumeration is a vector of exactly that length, holding the constants in the order the formula mentions them. Because repetitions are preserved rather than resolved, no comparison between constants is ever performed. The chapter closes with the boundary case of an empty occurrence list, where the formula is shown to live over the empty constant alphabet.
<!--zh-->
具体地说，公式的常元被读作一列有序的出现：常元每出现一次，无论在词项的何处或在任何量词之下，都占据列表的下一个位置。计数与枚举因此相伴而行。计数是一个自然数，记录出现了多少次；枚举是一个长度恰为该数的向量，按公式提及常元的次序存放它们。由于重复被保留而不被消解，全程不需要对常元作任何比较。本章最后处理出现列表为空的边界情形，证明这样的公式可以活在空的常元字母表上。
<!--ja-->
具体的には、論理式の定数は出現の順序付きリストとして読み出されます。定数は項のどこに現れても、またどの量化子の下に現れても、リストの次の位置を占めます。したがって数え上げと列挙は並んで進みます。数は出現がいくつあるかを記録する自然数であり、列挙はちょうどその長さのベクトルで、論理式が定数に言及した順にそれらを保持します。重複は解消されずにそのまま残るので、定数同士の比較は一切行われません。章の最後は、出現リストが空である境界の場合です。そこでは論理式が空の定数アルファベットの上で表せることが示されます。
<!--/-->

```agda
open import FOL.Manipulation.ConstantMapping using ( mapTm; mapFo )
open import Cubical.Data.Nat using ( _+_; snotz )
open import Cubical.Data.Vec using ( _++_; map )
import Cubical.Data.Empty as Empty
```

<!--en-->
## Counting by occurrence

`countTm`{.Agda} and `countFo`{.Agda} count every constant occurrence, while `constantsTm`{.Agda} and `constantsFo`{.Agda} list those constants in the same order. Repeated occurrences of one constant therefore remain distinct positions.

The design point of the chapter is decided here, before any syntax moves. A formula's constants are counted **by occurrence, not by value**: a formula with `k` constant-occurrences yields a vector of length `k`, and two occurrences of the same constant are two entries of that vector, holding the same set twice.

A reader who expects the *set* of constants a formula mentions will look for the decidable equality that would let two occurrences of one constant be recognized as one, and will not find it. There is none to find: the constant domain is an arbitrary type, nothing obliges its equality to be decidable, and no decidable equality on the intended carrier is assumed. Counting by occurrence is what frees the whole chapter from that demand. The cost is an abstraction of higher arity than strictly necessary, in the form of variables that receive a value twice over, and nothing downstream can tell the difference: a vector of parameters is a vector of parameters.

The count is a structural recursion over the ten constructors, with a term's count as its input: a constant is one occurrence, a variable is none. Where a constructor has two parts, the counts add, left part first.
<!--zh-->
## 逐次出现地计数

`countTm`{.Agda} 与 `countFo`{.Agda} 逐次计数常元的每次出现，而 `constantsTm`{.Agda} 与 `constantsFo`{.Agda} 按相同顺序列出这些常元。因此，同一常元的重复出现仍占据不同位置。

本章的设计要点在此定下，先于任何语法上的挪动。一条公式的常元**按出现计数，而非按取值**：带 `k` 次常元出现的公式给出长度为 `k` 的向量，同一常元的两次出现就是该向量的两个条目，两处写的是同一个集合。

若读者期待的是公式所提及的常元之**集**，他会寻找一个可判定的相等关系，把同一常元的两次出现认作一次，却找不到这样的相等。本来就没有可找的：常元域是任意类型，其相等未必可判定；本书也不对预期使用的集合载体假设可判定相等。逐次出现地计数，正是使整章避开这一要求的关键。代价是抽象所得的元数高于严格必要的元数，多出的部分对应于同一取值被当作两个不同变量重复处理；下游分辨不出其中差别：参数向量仍是参数向量。

计数是对十个构造子的一次结构递归，其输入是词项各部分的计数：常元算作一次出现，变量算作零次。复合构造子的计数取其两部分之和，左部在先。
<!--ja-->
## 出現ごとの数え上げ

`countTm`{.Agda} と `countFo`{.Agda} は定数が現れるたびに一つ数え、`constantsTm`{.Agda} と `constantsFo`{.Agda} は同じ順序で定数のベクトルを作ります。同じ定数の複数回の出現も別々に残します。

本章の設計上の要点は、構文を動かす前にここで決まります。論理式の定数は**値ごとではなく出現ごとに**数えます。定数が `k` 回現れる論理式は長さ `k` のベクトルを与え、同じ定数の二つの出現はそのベクトルの二つの項目であり、同じ集合を二度保持します。

論理式が言及する定数の**集合**を期待する読者は、同じ定数の二つの出現を一つと認めるための判定可能な等号を探すでしょうが、見つかりません。そもそも存在しないのです。定数域は任意の型であり、その等号が判定可能である必然性はなく、想定する集合の台にも判定可能な等号を仮定しません。出現ごとの数え上げこそが、この章全体をその要求から解放します。代償は、抽象のアリティが厳密に必要なものより高くなること、つまり同じ値を二度受ける変数が現れることですが、下流でそれを区別するものはありません。パラメータのベクトルはパラメータのベクトルです。

数え上げは十個のコンストラクタに対する構造的再帰で、入力は各部分の数です。定数は一回の出現、変数は零回。二つの部分を持つコンストラクタでは数を足し、左の部分が先です。
<!--/-->

<!--en-->
A small example fixes the convention. In `∀̇∈ (con a) ((con a) ∈̇ (var f0))`, the bounded quantifier carries the term `con a` and the left side of the atom repeats `con a`, while the right side is a variable: there are two occurrences, both of the same constant, so the count must be two, read from left to right. Terms are counted first. A constant `con c` is one occurrence, a variable `var i` is none, and these are the only two term forms; nothing inspects the free-variable index. The two atomic relations then add the counts of their two terms, the left one written first, which is what makes the example's total come out in reading order. The enumeration will return `[a, a]`, the same constant listed twice.
<!--zh-->
一个小例子定下约定。在 `∀̇∈ (con a) ((con a) ∈̇ (var f0))` 中，受限量词携带词项 `con a`，原子的左边重复 `con a`，右边是变元：共有两次出现，都是同一个常元，故计数必须是二，且按自左向右的阅读顺序。先数词项。常元 `con c` 是一次出现，变元 `var i` 是零次；词项只有这两种形式，且不检查自由变元的序号。两条原子关系再把各自两个词项的计数相加，左边的写在前面，例子的总和因此按阅读顺序得出。枚举将返回 `[a, a]`，即同一个常元被列出两次。
<!--ja-->
小さな例が規約を決めます。`∀̇∈ (con a) ((con a) ∈̇ (var f0))` では、有界量化子が項 `con a` を伴い、原子の左辺が同じ `con a` を繰り返し、右辺は変数です。出現は二つであり、どちらも同じ定数なので、数は左から右の読み順で二にならなければなりません。まず項を数えます。定数 `con c` は一回の出現、変数 `var i` は零回であり、項はこの二つの形式しかなく、自由変数の添字は調べません。二つの原子関係はさらにそれぞれの二項の数を足し、左の項を先に書くので、例の合計が読み順に現れます。列挙は `[a, a]`、つまり同じ定数を二度並べたものを返します。
<!--/-->

```agda
countTm : ∀ {ℓc} {K : Type ℓc} {n} → Term K n → ℕ
countTm (con c) = suc zero
countTm (var i) = zero

countFo : ∀ {ℓc} {K : Type ℓc} {n} → Formula K n → ℕ
countFo (t ∈̇ u)  = countTm t + countTm u
```

<!--en-->
The propositional constructors divide by role rather than being read one by one. Those that combine branches, namely conjunction, disjunction and implication, add the counts of their two subformulas, again left first; falsum carries no terms and contributes zero. So the count of a whole formula is a sum over exactly those nodes that hold terms: at a binary node the two branch counts are added, and nowhere else does the number move.
<!--zh-->
命题构造子按其作用分类，而不必逐个细读。组合分支的一类，即合取、析取与蕴涵，各把两个子公式的计数相加，仍是左边在先；假式不携带任何词项，贡献为零。于是整条公式的计数恰是对那些持有词项的节点求和：在二元节点处两个分支的计数相加，此外数字不再变动。
<!--ja-->
命題構成子は、一つ一つ読むよりも役割ごとに分けるのが分かりやすいです。枝を組み合わせるもの、すなわち連言・選言・含意はそれぞれ二つの部分論理式の数を足し、やはり左が先です。矛盾記号は項を運ばず、零を寄与します。したがって論理式全体の数は、項を保持する節点ちょうどに対する和であり、二項節点で二つの枝の数が加わるほか、この数は動きません。
<!--/-->

```agda
countFo (t ≐ u)  = countTm t + countTm u
countFo (φ ∧̇ ψ)  = countFo φ + countFo ψ
countFo (φ ∨̇ ψ)  = countFo φ + countFo ψ
countFo (φ ⇒̇ ψ)  = countFo φ + countFo ψ
countFo ⊥̇        = zero
```

<!--en-->
Quantifiers divide according to whether they carry a term. The unbounded `∃̇` and `∀̇` bind a variable and hold no constant, so they pass the body's count through unchanged; binding does not create occurrences. The bounded `∀̇∈` and `∃̇∈` do carry a term, as in the example above, so their count is `countTm t` added in front of the body's count. This keeps the left-to-right reading order that the enumeration will reproduce term for term.
<!--zh-->
量词按是否携带词项而分。无界的 `∃̇` 与 `∀̇` 约束一个变元而不含常元，因此直接沿用主体的计数；约束变元不产生出现。有界的 `∀̇∈` 与 `∃̇∈` 则携带一个词项，如上例所示，其计数是在主体计数之前加上 `countTm t`。这保持了自左向右的阅读顺序，后面的枚举将逐词项地复现这一顺序。
<!--ja-->
量化子は項を伴うかどうかで分かれます。非有界の `∃̇` と `∀̇` は変数を束縛するだけで定数を含まないため、本体の数をそのまま通します。束縛は出現を作りません。有界の `∀̇∈` と `∃̇∈` は上の例のように項を一つ伴うので、その数は本体の数の前に `countTm t` を加えたものです。これにより左から右の読み順が保たれ、後の列挙が項ごとにその順を再現します。
<!--/-->

```agda
countFo (∃̇ φ)    = countFo φ
countFo (∀̇ φ)    = countFo φ
countFo (∀̇∈ t φ) = countTm t + countFo φ
countFo (∃̇∈ t φ) = countTm t + countFo φ
```

<!--en-->
Collecting is the same recursion written a second time, and it has to be a second recursion rather than one returning both: the **length** of the vector it returns is precisely what the first computes, so the count must already exist for the collection to be typeable at all. Every clause mirrors its counterpart above, with `++` where the count had `+`, so the constants come out in the order the formula mentions them, left to right.
<!--zh-->
收集是对同一结构进行的第二次递归，而且必须与计数分成两次，不能在一次递归中同时给出两个结果：返回向量的**长度**恰是第一次递归算出的数，因此必须先算出计数，收集函数的返回类型才得以确定。每条子句都对应上面的计数子句，只把 `+` 换成 `++`；于是常元按照公式提及它们的次序，自左向右依次排列。
<!--ja-->
収集は同じ再帰をもう一度書いたものであり、両方を一度に返す一つの再帰にはできません。返すベクトルの**長さ**こそ最初の再帰が計算するものだからで、収集の返り値の型が付けられるためには、あらかじめ数が存在していなければなりません。各節は上の計数の節と対応し、`+` の代わりに `++` を使うので、定数は論理式が言及する順序、左から右へ並びます。
<!--/-->

<!--en-->
The collection is bound to the count by one invariant: the recursion is dependent, and the result type `Vec K (countTm t)` demands that the returned vector's length be definitionally the term's own occurrence count, with the entries in left-to-right order. A constant yields the single-entry vector `c ∷ []`, a variable the empty vector; the formula case concatenates the two term vectors, left one first.
<!--zh-->
收集与计数由一条不变式绑定：这里的递归是依赖的，结果类型 `Vec K (countTm t)` 要求返回向量的长度按定义就是该词项自身的出现计数，且条目按自左向右的次序排列。常元给出单条目向量 `c ∷ []`，变元给出空向量；公式情形拼接两个词项向量，左边的在先。
<!--ja-->
収集は一つの不変式によって数え上げと結び付いています。ここでの再帰は依存しており、結果の型 `Vec K (countTm t)` は、返されるベクトルの長さがその項自身の出現数に定義上等しく、項目が左から右の順に並ぶことを要求します。定数は単一項目のベクトル `c ∷ []` を、変数は空ベクトルを与え、論理式の場合は二つの項のベクトルを連結します。左の項が先です。
<!--/-->

```agda
constantsTm : ∀ {ℓc} {K : Type ℓc} {n} (t : Term K n) → Vec K (countTm t)
constantsTm (con c) = c ∷ []
constantsTm (var i) = []

constantsFo : ∀ {ℓc} {K : Type ℓc} {n} (φ : Formula K n) → Vec K (countFo φ)
constantsFo (t ∈̇ u)  = constantsTm t ++ constantsTm u
```

<!--en-->
The same invariant runs through the propositional constructors: each binary formula concatenates its two sublists at exactly the node where the count added its two summands, and falsum contributes the empty vector where the count contributed zero. Because concatenation replaces addition node for node, the length of the result computes to the count, with no separate bookkeeping.
<!--zh-->
同一条不变式贯穿命题构造子：每条二元公式恰在计数把两个加数相加的节点处拼接两个子列表，假式在计数贡献零之处贡献空向量。由于拼接逐节点地取代加法，结果的长度按定义计算就是计数，无需另行记账。
<!--ja-->
同じ不変式が命題構成子全体を貫きます。二項の論理式は、数え上げが二つの加数を足した節点で正確に二つの部分リストを連結し、矛盾記号は数が零を寄与する場所で空ベクトルを与えます。連結が節点ごとに加法を置き換えるため、結果の長さは定義により数に計算され、別途の管理は不要です。
<!--/-->

```agda
constantsFo (t ≐ u)  = constantsTm t ++ constantsTm u
constantsFo (φ ∧̇ ψ)  = constantsFo φ ++ constantsFo ψ
constantsFo (φ ∨̇ ψ)  = constantsFo φ ++ constantsFo ψ
constantsFo (φ ⇒̇ ψ)  = constantsFo φ ++ constantsFo ψ
constantsFo ⊥̇        = []
```

<!--en-->
The quantifier clauses close the recursion and settle the order: unbounded quantification passes the body's list through, while the bounded quantifiers prepend the term's list to the body's list, matching the reading order the count already used. For the example above the result is `[a, a]`, of length the formula's count, and this vector is precisely the input that parameter abstraction will consume.
<!--zh-->
量词子句结束递归并确定次序：无界量词直接传递主体的列表，受限量词把词项的列表接在主体列表之前，与计数所用的阅读顺序一致。对上面的例子，结果是 `[a, a]`，其长度就是该公式的计数，而这个向量恰是参数抽象将要消费的输入。
<!--ja-->
量化子の節が再帰を閉じ、順序を確定させます。非有界量化子は本体のリストをそのまま通し、有界量化子は項のリストを本体のリストの前に付けます。これは数え上げがすでに用いた読み順と一致します。上の例では結果は `[a, a]` で、長さは論理式の数そのものであり、このベクトルこそパラメータ抽象が入力として受け取るものです。
<!--/-->

```agda
constantsFo (∃̇ φ)    = constantsFo φ
constantsFo (∀̇ φ)    = constantsFo φ
constantsFo (∀̇∈ t φ) = constantsTm t ++ constantsFo φ
constantsFo (∃̇∈ t φ) = constantsTm t ++ constantsFo φ
```

<!--en-->
## Placing the new parameter variables

Parameter abstraction extends an environment of arity n with k positions for constant occurrences. The original variables occupy the first n positions and the parameters the following k positions. The two index embeddings and their lookup laws show that both parts keep their values in the concatenated environment.

Two placements do the index arithmetic, and each is three lines. `padRight b` reads an index of the first `a` slots of `a + b`; `padLeft a` reads an index of the last `b`. They are one another's mirror, and the asymmetry in their arguments is the asymmetry of the recursion: `padRight` recurses on the index, `padLeft` on the number of slots it steps over.
<!--zh-->
## 安置新的参数变元

参数抽象在元数为 n 的环境后增加 k 个位置，分别对应常元的出现。原有变元占据前 n 个位置，参数占据随后的 k 个位置。两个索引嵌入及其查值定律保证，环境连接后，两部分都保持原有的值。

两件安置装置承担序号算术，各占三行。`padRight b` 读 `a + b` 中头 `a` 个位的序号，`padLeft a` 读末 `b` 个位的序号。二者互为镜像，参数的不对称正是递归的不对称：`padRight` 对序号递归，`padLeft` 对它跨过的位数递归。
<!--ja-->
## 新しいパラメータ変数の配置

パラメータの抽象化では、アリティ n の環境に定数の出現に対応する k 個の位置を追加します。元の変数は先頭の n 個、パラメータは続く k 個の位置を占めます。二つの添字の埋め込みと参照の法則により、連結した環境でも両部分の値が保たれることを示します。

二つの配置関数が添字計算を担い、それぞれ三行です。`padRight b` は `a + b` の先頭 `a` 個の位置の添字を読み、`padLeft a` は末尾 `b` 個の位置の添字を読みます。両者は互いの鏡像であり、引数の非対称性は再帰の非対称性そのものです。`padRight` は添字について再帰し、`padLeft` はまたぐ位置の個数について再帰します。
<!--/-->

<!--en-->
A numeric example shows what the embeddings must do: with `a = 2` and `b = 3`, an environment of five slots splits into the first two slots, holding the original variables, and the last three, holding the parameters. `padRight` embeds `Fin a` into `Fin (a + b)` by leaving the index where it is, since the first `a` slots of the concatenation are the original `a`: an index of the first half stays at the same position among five. The bound `b` is implicit and fixed throughout, so each recursive step just wraps the index in one more `suc`: zero stays zero, and `suc i` becomes `suc (padRight b i)`.
<!--zh-->
一个数值例子说明嵌入必须做什么：取 `a = 2`、`b = 3`，五元环境分成前两元 (存放原有变元) 与后三元 (存放参数)。`padRight` 把 `Fin a` 嵌入 `Fin (a + b)`，方式是让序号保持原位，因为拼接的前 `a` 个位正是原来的 `a` 个位：前一半的序号在五个位置中位置不变。界 `b` 是隐式的且全程固定，故每个递归步骤只是给序号再包一层 `suc`：零仍是零，`suc i` 变为 `suc (padRight b i)`。
<!--ja-->
数値の例で、埋め込みが何をすべきかを示します。`a = 2`、`b = 3` のとき、五つの位置からなる環境は、元の変数を格納する先頭二つと、パラメータを格納する末尾三つに分かれます。`padRight` は `Fin a` を `Fin (a + b)` に埋め込みます。連結の先頭 `a` 個の位置が元の `a` 個であるため、添字はその場に留まります。前半の添字は五つの位置の中で同じ場所にあります。界 `b` は暗黙で全体を通じて固定されるので、各再帰段階は添字をもう一重の `suc` で包むだけです。零は零のままで、`suc i` は `suc (padRight b i)` になります。
<!--/-->

```agda
padRight : ∀ {a} b → Fin a → Fin (a + b)
padRight b zero    = zero
padRight b (suc i) = suc (padRight b i)

padLeft : ∀ a {b} → Fin b → Fin (a + b)
padLeft zero    j = j
```

<!--en-->
`padLeft` embeds `Fin b` into `Fin (a + b)` by shifting the index past the first `a` slots, so here the bound `a` is explicit and the recursion runs on it. In the example, `padLeft 2` sends the parameter index `0` to position `2`, the first slot after the original variables. When `a` is zero the concatenation is the second half and `j` already points correctly; each additional slot prepended adds one `suc`, placing the second half after the first.
<!--zh-->
`padLeft` 把 `Fin b` 嵌入 `Fin (a + b)`，方式是把序号移过前 `a` 个位，因此这里显式的界是 `a`，递归也在它上进行。在例子中，`padLeft 2` 把参数序号 `0` 送到位置 `2`，即原有变元之后的第一个位置。当 `a` 为零时，拼接就是后半段，`j` 已指向正确位置；每多前缀一个位，就多包一层 `suc`，从而把后半段放在前半段之后。
<!--ja-->
`padLeft` は `Fin b` を `Fin (a + b)` に埋め込みます。添字を先頭の `a` 個の位置の先へ移すので、ここでは界 `a` が明示的で、再帰もそれについて回ります。例では、`padLeft 2` はパラメータの添字 `0` を位置 `2`、すなわち元の変数の直後の最初の位置へ送ります。`a` が零のとき連結は後半そのものであり、`j` はすでに正しい位置を指します。前の位置が一つ増えるごとに `suc` が一つ加わり、後半が前半の後ろに置かれます。
<!--/-->

```agda
padLeft (suc a) j = suc (padLeft a j)
```

<!--en-->
Each placement comes with one law, and it is exactly the law an environment obeys: looking up a padded index in a concatenated vector is looking up the original index in the corresponding half. Alongside them stands a third law of the same shape, that lookup passes through `map`{.Agda}, and it is this law that lets the interpretation of the constants travel through the collected vector of occurrences. All three are proved by simultaneous structural recursion on the vector and the index, and each base or step case reduces to `refl`{.Agda} or to the induction hypothesis; no further equivalence machinery is involved.
<!--zh-->
每件安置装置各有一条定律，而这条定律正是环境所遵守的那一条：在拼接向量中查一个被安置过的序号，就是在对应的那一半中查原来的序号。与它们并列的还有第三条同形的定律，即查值可以穿过 `map`{.Agda}；正是这条定律使常元的解释得以穿过收集出的出现向量。三条定律都对向量与序号同时作结构递归，每个基例或步例都化归为 `refl`{.Agda} 或归纳假设，不涉及任何其他等价装置。
<!--ja-->
それぞれの配置には一つの法則が付き、それは環境が従う法則そのものです。連結されたベクトルの中で配置済みの添字を参照することは、対応する半分の中で元の添字を参照することに他なりません。これらと並ぶ第三の同型の法則は、参照が `map`{.Agda} を通り抜けるというもので、定数の解釈が出現のベクトルを通り抜けられるのはこの法則によります。三つの法則はどれもベクトルと添字への同時の構造的帰納で証明され、各基底場合と各帰納段階は `refl`{.Agda} または帰納の仮定に帰着します。
<!--/-->

<!--en-->
The picture to keep in mind is an environment written as a concatenation `p ++ q`: `p` holds the values of the original free variables, `q` the values assigned to the constant occurrences. The two embeddings answer one and the same question, whether a lookup in the joined environment still finds the value it found before the join. For an original variable with index `i : Fin a` into the first half, the first law states `lookup (padRight b i) (p ++ q) ≡ lookup i p`: `padRight b i` names the same position inside the concatenation, so the entry read is unchanged.
<!--zh-->
要记住的图景是一个写作拼接 `p ++ q` 的环境：`p` 存放原有自由变元的值，`q` 存放分配给常元出现的值。两个嵌入回答的是同一个问题：在接合后的环境中查值，是否仍读到接合前读到的值。对带有指向前一半的序号 `i : Fin a` 的原有变元，第一条定律陈述 `lookup (padRight b i) (p ++ q) ≡ lookup i p`：`padRight b i` 在拼接中指名同一个位置，因此读到的条目不变。
<!--ja-->
心に描く図は、連結 `p ++ q` と書かれた環境です。`p` は元の自由変数の値を、`q` は定数の出現に割り当てられた値を格納します。二つの埋め込みが答えるのは同じ一つの問いです。接合した環境での参照が、接合前に読んでいた値をまだ読み出せるかどうか。前半への添字 `i : Fin a` を持つ元の変数については、第一の法則は `lookup (padRight b i) (p ++ q) ≡ lookup i p` と述べます。`padRight b i` は連結の中で同じ位置を指すので、読まれる項目は変わりません。
<!--/-->

```agda
lookup-padRight : ∀ {ℓa} {A : Type ℓa} {a b} (p : Vec A a) (q : Vec A b) (i : Fin a)
                → lookup (padRight b i) (p ++ q) ≡ lookup i p
lookup-padRight []      q ()
lookup-padRight (x ∷ p) q zero    = refl
lookup-padRight (x ∷ p) q (suc i) = lookup-padRight p q i
```

<!--en-->
The second law covers a parameter with natural index `j : Fin b` into the second half: `lookup (padLeft a j) (p ++ q) ≡ lookup j q`, that is, the shifted index reads exactly the value `lookup j q` reads in `q`. Together the two laws say what an environment must say: each half of a concatenated environment keeps the value it had on its own. Both proofs descend through the vector and the index together, each step stripping one entry and one constructor until the base case is reached.
<!--zh-->
第二条定律处理带有指向后一半的自然序号 `j : Fin b` 的参数：`lookup (padLeft a j) (p ++ q) ≡ lookup j q`，即被移动后的序号读到的，恰是 `lookup j q` 在 `q` 中读到的值。两条定律合起来说的正是环境必须说的：拼接环境的每一半都保持自己单独存在时的值。两个证明都沿向量与序号一同下降，每步剥去一个条目和一层构造子，直到抵达基例。
<!--ja-->
第二の法則は、後半への自然な添字 `j : Fin b` を持つパラメータを扱います。`lookup (padLeft a j) (p ++ q) ≡ lookup j q`、すなわち移された添字が読む値は、`lookup j q` が `q` の中で読む値にちょうど一致します。二つの法則を合わせると、環境が満たすべきことが述べられます。連結された環境の各半分は、単独であったときの値を保つ、ということです。どちらの証明もベクトルと添字を共にたどり、各段階で一つの項目と一つのコンストラクタを剥がしながら基底の場合まで降ります。
<!--/-->

```agda

lookup-padLeft : ∀ {ℓa} {A : Type ℓa} a {b} (p : Vec A a) (q : Vec A b) (j : Fin b)
               → lookup (padLeft a j) (p ++ q) ≡ lookup j q
lookup-padLeft zero    []      q j = refl
lookup-padLeft (suc a) (x ∷ p) q j = lookup-padLeft a p q j

lookup-map : ∀ {ℓa ℓb} {A : Type ℓa} {B : Type ℓb} {n}
```

<!--en-->
The third law concerns a relabelled vector: `lookup j (map f v) ≡ f (lookup j v)`. Reading the mapped vector and then applying `f` is the same as applying `f` first. In parameter abstraction this is what lets the interpretation of the constants travel with the occurrences: if `f` assigns to each constant the value its replacement variable should carry, and `v` is the vector of occurrences collected from a formula, then looking up any position of `map f v` computes `f` of the constant at that position. The proof follows the same shape as the two placement laws, descending through the vector and the index together.
<!--zh-->
第三条定律关于被改名的向量：`lookup j (map f v) ≡ f (lookup j v)`。读取被映射的向量再施加 `f`，与先施加 `f` 再读取一致。在参数抽象中，正是这条定律让常元的解释随出现一同前进：若 `f` 给每个常元指派其替代变量应取的值，`v` 是从公式收集出的出现向量，则查 `map f v` 的任一位置，都计算出该位置上常元的 `f` 像。证明与两条安置定律同形，沿向量与序号一同下降。
<!--ja-->
第三の法則は、名前の付け替えられたベクトルに関するものです。`lookup j (map f v) ≡ f (lookup j v)`。写像済みのベクトルを読んでから `f` を施すことは、先に `f` を施してから読むことと同じです。パラメータ抽象では、この法則によって定数の解釈が出現と共に進みます。`f` が各定数に、その置換変数が取るべき値を割り当て、`v` が論理式から収集した出現のベクトルなら、`map f v` の任意の位置を参照することは、その位置の定数に `f` を施した値を計算します。証明は二つの配置の法則と同じ形で、ベクトルと添字を共に降りていきます。
<!--/-->

```agda
             (f : A → B) (v : Vec A n) (j : Fin n)
           → lookup j (map f v) ≡ f (lookup j v)
lookup-map f []      ()
lookup-map f (x ∷ v) zero    = refl
lookup-map f (x ∷ v) (suc j) = lookup-map f v j
```

<!--en-->
## Formulas with no constant occurrences

The counting and collecting machinery attaches a finite occurrence data to every formula. This section develops the boundary case of that interface: when the count is zero, no constant occurs anywhere in the formula, so every term it contains is a variable. Such a formula can be expressed over the empty constant alphabet `⊥*`{.Agda}, that is, as a parameter-free formula of the same arity. The module `ZeroOccurrences`{.Agda} is parameterised by the original constant domain `K` and contains, first, the arithmetic that lets a proof of `countFo φ ≡ 0` be split between the two sides of a sum, and then the two maps: `erase`{.Agda}, which removes the constant domain, and `erase-inv`{.Agda}, which shows that mapping back into `K` recovers the original formula exactly.
<!--zh-->
## 无常元出现的公式

计数与收集装置为每条公式附上一份有限的出现数据。本节发展这一接口的边界情形：当计数为零时，公式中任何地方都不出现常元，于是它所含的每个词项都是变元。这样的公式可以在空的常元字母表 `⊥*`{.Agda} 上表达，也就是写成同一元数的无参公式。模块 `ZeroOccurrences`{.Agda} 以原常元域 `K` 为参数，其中首先给出把 `countFo φ ≡ 0` 的证明按和式两侧拆开的算术，然后是两个映射：消去常元域的 `erase`{.Agda}，以及证明映回 `K` 后恰好恢复原公式的 `erase-inv`{.Agda}。
<!--ja-->
## 定数が出現しない論理式

数え上げと収集の仕組みは、すべての論理式に有限な出現のデータを添付します。この節はそのインターフェースの境界場合を扱います。個数が零なら論理式のどこにも定数が現れず、したがって含まれる項はすべて変数です。そのような論理式は空の定数アルファベット `⊥*`{.Agda} の上で、同じアリティの無パラメータ論理式として表せます。モジュール `ZeroOccurrences`{.Agda} は元の定数域 `K` をパラメータとし、まず `countFo φ ≡ 0` の証明を和の両側に分けるための算術を整え、次に二つの写像、つまり定数域を消す `erase`{.Agda} と、`K` へ写し戻すと元の論理式がちょうど復元されることを示す `erase-inv`{.Agda} を与えます。
<!--/-->

<!--en-->
The boundary question of the occurrence interface is: what does a count of zero force about the syntax? The section answers it for an arbitrary constant type `K`, given a formula `φ` and a proof that its occurrence count is zero. Since nothing in the answer may depend on which type `K` is, and in particular nothing may use a decidable equality on `K`, the argument is developed once, uniformly for every such `K` at the level `ℓ`.
<!--zh-->
出现接口的边界问题是：计数为零对语法强制了什么？本节对任意常元类型 `K` 回答这一问题，输入是一条公式 `φ` 连同其出现计数为零的证明。由于答案不得依赖 `K` 究竟是哪个类型，尤其不得使用 `K` 上的可判定相等，这一论证只发展一次，对层级 `ℓ` 上所有这样的 `K` 一致成立。
<!--ja-->
出現というインターフェースの境界の問いは、数が零であることは構文に対して何を強制するのか、というものです。この節は、任意の定数型 `K` に対してこの問いに答えます。入力は論理式 `φ` と、その出現数が零である証明です。答えが `K` がどの型であるかに依存してはならず、とりわけ `K` 上の判定可能な等号を用いてはならないので、議論は一度だけ展開され、レベル `ℓ` のすべてのそのような `K` に対して一様に成り立ちます。
<!--/-->

```agda
module ZeroOccurrences {ℓ : Level} (K : Type ℓ) where

```

<!--en-->
The section formalises the boundary case. Its input is a formula `φ` together with a proof `p : countFo φ ≡ 0`; from `p` the construction first extracts, for each subterm and subformula, a proof that its own count is zero, and on that basis rebuilds the same syntax over the empty constant alphabet. The map `eraseTm`{.Agda} and `erase`{.Agda} go from `K` to `⊥*`{.Agda}, and the maps `eraseTm-inv`{.Agda} and `erase-inv`{.Agda} show that relabelling along `Empty.rec*`{.Agda}, the eliminator that reads a constant out of the empty type, returns the original term or formula as a path. Together they say that over `K`, the formulas with no constant occurrences are exactly the images of parameter-free formulas, without any decidability assumption on `K`.
<!--zh-->
本节把边界情形形式化。输入是一条公式 `φ` 连同证明 `p : countFo φ ≡ 0`；构造先从 `p` 为每个子词项、子公式提取其自身计数为零的证明，并在此基础上在空常元字母表上重建同一语法。映射 `eraseTm`{.Agda} 与 `erase`{.Agda} 从 `K` 走向 `⊥*`{.Agda}；映射 `eraseTm-inv`{.Agda} 与 `erase-inv`{.Agda} 则证明，沿 `Empty.rec*`{.Agda}(从空类型读出一个定元的消去子) 改名后，作为路径返回原来的词项或公式。二者合起来说：在 `K` 上，无常元出现的公式恰是无参公式的像，且对 `K` 无任何可判定性假设。
<!--ja-->
この節は境界場合を形式化します。入力は論理式 `φ` と証明 `p : countFo φ ≡ 0` の対であり、構成はまず `p` から各部分項・部分論理式に対してその個数が零である証明を取り出し、その上で空の定数アルファベットの上に同じ構文を組み立て直します。写像 `eraseTm`{.Agda} と `erase`{.Agda} は `K` から `⊥*`{.Agda} へ進み、写像 `eraseTm-inv`{.Agda} と `erase-inv`{.Agda} は、空型から定数を読み出す消去子 `Empty.rec*`{.Agda} に沿って改名すると、元の項や論理式がパスとして返ることを示します。両者を合わせて、`K` の上では定数が出現しない論理式が無パラメータ論理式の像とちょうど一致し、`K` に対する判定可能性の仮定が一切不要であることが分かります。
<!--/-->

<!--en-->
The first ingredient is arithmetical: a sum is zero only when both summands are. Since the count of a composite formula is always a sum of the counts of its parts, a proof of `countFo φ ≡ 0` must split into zero-count proofs for the parts, and `plus-zero-l` and `plus-zero-r` perform exactly this split, extracting `a ≡ 0` and `b ≡ 0` from `a + b ≡ 0`. The split works because a nonzero left summand computes to a successor: `suc a + b` is `suc (a + b)`, and the lemma `snotz` turns the equation of a successor with `0` into a contradiction, from which any conclusion follows. When the left summand is `zero`, `zero + b` computes to `b`, and the claims are immediate.
<!--zh-->
第一个要素是算术的：和为零，仅当两个加数都为零。由于复合公式的计数总是各部分计数之和，`countFo φ ≡ 0` 的证明必须拆分为各部分计数为零的证明，`plus-zero-l` 与 `plus-zero-r` 执行的正是这一拆分，从 `a + b ≡ 0` 分别提取 `a ≡ 0` 与 `b ≡ 0`。拆分得以进行，是因为非零的左加数按定义计算为后继：`suc a + b` 就是 `suc (a + b)`，引理 `snotz` 把后继等于 `0` 的等式变成矛盾，从矛盾可得任意结论。当左加数为 `zero` 时，`zero + b` 计算为 `b`，两个命题都是立即的。
<!--ja-->
最初の材料は算術的なものです。和が零であるのは、両方の加数が零のときに限ります。複合論理式の数は常に部分の数の和なので、`countFo φ ≡ 0` の証明は各部分の数が零である証明に分割できなければならず、`plus-zero-l` と `plus-zero-r` がまさにこの分割を行い、`a + b ≡ 0` からそれぞれ `a ≡ 0` と `b ≡ 0` を取り出します。分割が機能するのは、非零の左加数が後続数に計算されるからです。`suc a + b` は `suc (a + b)` であり、補題 `snotz` が後続数と `0` の等式を矛盾に変え、そこから任意の結論が従います。左の加数が `zero` のときは `zero + b` が `b` に計算され、両方の主張は直ちに得られます。
<!--/-->

```agda
  plus-zero-l : {a b : ℕ} → a + b ≡ 0 → a ≡ 0
  plus-zero-l {zero} {b} p = refl
  plus-zero-l {suc a} {b} p = Empty.rec (snotz p)

  plus-zero-r : {a b : ℕ} → a + b ≡ 0 → b ≡ 0
  plus-zero-r {zero} {b} p = p
```

<!--en-->
Count zero is a theorem about syntax: no constant constructor can occur. For terms this is outright. A term has count zero precisely when it is a variable, and `eraseTm` turns this into a map: from `t` together with `p : countTm t ≡ 0` it produces a term over the empty alphabet `⊥*` at the same arity `n`. The constant case is excluded because `countTm (con a)` computes to `1`, making `p` a proof of `suc _ ≡ 0`; the contradiction supplies the required term. The variable case keeps the index, giving `var i`: free variables are untouched, the empty alphabet forbids only constants.
<!--zh-->
计数为零是关于语法的一条定理：常元构造子不可能出现。对词项而言，这已是直接的陈述。词项的计数为零恰当它是变元，`eraseTm` 把这一点变成一个映射：从 `t` 连同 `p : countTm t ≡ 0` 出发，得到空字母表 `⊥*` 上同一元数 `n` 的词项。常元情形被排除，因为 `countTm (con a)` 计算为 `1`，使 `p` 成为 `suc _ ≡ 0` 的证明；这一矛盾给出所需的词项。变元情形保留序号，给出 `var i`：自由变元原样不动，空字母表只禁绝常元。
<!--ja-->
個数が零であることは構文についての定理です。定数のコンストラクタは現れえない、という主張です。項についてはこれは直接に述べられます。項の数が零であるのは、それが変数であるときちょうどであり、`eraseTm` はこれを一つの写像にします。`t` と証明 `p : countTm t ≡ 0` から、空のアルファベット `⊥*` の上の同じアリティ `n` の項を得ます。定数の場合は排除されます。`countTm (con a)` は `1` に計算され、`p` は `suc _ ≡ 0` の証明になるからです。この矛盾が必要な項を供給します。変数の場合は添字をそのまま保ち `var i` を返します。自由変数は触られず、空のアルファベットが禁じるのは定数だけです。
<!--/-->

```agda
  plus-zero-r {suc a} {b} p = Empty.rec (snotz p)

  eraseTm : {n : ℕ} (t : Term K n) → countTm t ≡ 0 → Term (⊥* {ℓ}) n
  eraseTm (con a) p = Empty.rec {A = Term (⊥* {ℓ}) _} (snotz p)
  eraseTm (var i) _ = var i

  erase : {n : ℕ} (φ : Formula K n) → countFo φ ≡ 0 → Formula (⊥* {ℓ}) n
```

<!--en-->
The same rebuild runs through the whole of `erase`, and the atoms show the pattern in its simplest form. For `t ∈̇ u`, the count is `countTm t + countTm u`, so `plus-zero-l` and `plus-zero-r` split `p` into zero-count proofs for `t` and `u`, and `erase` recurses on each side, rebuilding the relation over `⊥*`. The equality atom `≐` behaves identically. Throughout, the arity `n` of free variables is never touched: erasing constants changes only the constant domain, not the free-variable structure.
<!--zh-->
同一重建贯穿整个 `erase`，原子关系以其最简形式展示该模式。取 `t ∈̇ u`：其计数是 `countTm t + countTm u`，于是 `plus-zero-l` 与 `plus-zero-r` 把 `p` 拆成 `t` 与 `u` 各自计数为零的证明，`erase` 对两侧各自递归，在 `⊥*` 上重建该关系。相等原子 `≐` 的处理完全相同。全程中自由变元的元数 `n` 从未被改动：消去常元只改变常元域，不改变自由变元的结构。
<!--ja-->
同じ組み立て直しが `erase` 全体を貫き、原子関係がその最も単純な形で型を示します。`t ∈̇ u` を取ると、その数は `countTm t + countTm u` なので、`plus-zero-l` と `plus-zero-r` が `p` を `t` と `u` それぞれの数が零である証明に分け、`erase` は両側で再帰して `⊥*` の上に関係を組み立て直します。等号原子 `≐` もまったく同じように扱われます。全体を通して、自由変数のアリティ `n` は決して触られません。定数を消すのは定数域だけを変え、自由変数の構造は変えないからです。
<!--/-->

```agda
  erase (t ∈̇ u) p = eraseTm t (plus-zero-l p) ∈̇ eraseTm u (plus-zero-r p)
  erase (t ≐ u) p = eraseTm t (plus-zero-l p) ≐ eraseTm u (plus-zero-r p)
  erase (φ ∧̇ ψ) p = erase φ (plus-zero-l p) ∧̇ erase ψ (plus-zero-r p)
  erase (φ ∨̇ ψ) p = erase φ (plus-zero-l p) ∨̇ erase ψ (plus-zero-r p)
  erase (φ ⇒̇ ψ) p = erase φ (plus-zero-l p) ⇒̇ erase ψ (plus-zero-r p)
```

<!--en-->
One quantifier case shows how binding interacts with the count. For an unbounded quantifier such as `∃̇ φ`, the count of the whole equals the count of the body, so the same `p` is carried into the recursive call and the result is `∃̇` applied to the erased body; falsum, with no parts and no occurrences, erases to itself. The bounded quantifiers `∀̇∈` and `∃̇∈` combine a term and a formula, and there the sum is split exactly as in the atomic cases, the term going through `eraseTm` and the body through a recursive `erase`. Every clause preserves the shape of the original formula, replacing only its constants.
<!--zh-->
一个量词情形展示了约束如何与计数互动。对无界量词如 `∃̇ φ`，整体的计数等于主体的计数，于是同一个 `p` 直接带入递归调用，结果就是把 `∃̇` 施于消去后的主体；假式没有部分也没有出现，消去后仍是自身。有界量词 `∀̇∈` 与 `∃̇∈` 组合一个词项与一个公式，这里像原子情形一样拆分和式：词项经 `eraseTm`，主体经递归的 `erase`。每条子句都保持原公式的形状，只替换其中的常元。
<!--ja-->
量化子の一つの場合が、束縛と数の相互作用を示します。`∃̇ φ` のような非有界量化子では、全体の数は本体の数に等しいので、同じ `p` をそのまま再帰呼び出しに持ち込み、結果は消去後の本体に `∃̇` を施したものです。矛盾記号は部分も出現もないので、消去しても自分自身です。有界量化子 `∀̇∈` と `∃̇∈` は項と論理式を組み合わせるので、ここでは原子の場合と同じように和を分けます。項は `eraseTm` を、本体は再帰的な `erase` を通ります。どの節も元の論理式の形を保ち、定数だけを置き換えます。
<!--/-->

```agda
  erase ⊥̇ _ = ⊥̇
  erase (∃̇ φ) p = ∃̇ erase φ p
  erase (∀̇ φ) p = ∀̇ erase φ p
  erase (∀̇∈ t φ) p = ∀̇∈ (eraseTm t (plus-zero-l p)) (erase φ (plus-zero-r p))
  erase (∃̇∈ t φ) p = ∃̇∈ (eraseTm t (plus-zero-l p)) (erase φ (plus-zero-r p))
```

<!--en-->
The round trip is what makes the construction more than a translation: mapping back into `K` must return the original formula. The term-level statement `eraseTm-inv` comes first. If `t` has count zero, then relabelling `eraseTm t p` along `Empty.rec*` gives back `t` itself, as a path between terms over `K`. The relabelling function `Empty.rec* : ⊥* → K` is the eliminator of the empty type: asked to produce a constant of `K`, it demands an element of `⊥*`, and since the erased term was built by `eraseTm` it contains no constant node, so the function is never actually applied. The induction then has only a contradictory case and a variable case, the latter closed by the computation rule of `mapTm`, which rebuilds `var i` from `var i`.
<!--zh-->
往返才是这一构造超出翻译之处：映回 `K` 必须返回原公式。词项层面的陈述 `eraseTm-inv` 先行。若 `t` 计数为零，则沿 `Empty.rec*` 改名 `eraseTm t p` 便按路径返回 `t` 本身，即 `K` 上词项之间的一条路径。改名函数 `Empty.rec* : ⊥* → K` 是空类型的消去子：要它给出一个 `K` 的常元，它就索要 `⊥*` 的一个元素；而由 `eraseTm` 建出的词项不含常元节点，该函数实际上从未被调用。于是归纳只剩一个矛盾情形和一个变元情形，后者由 `mapTm` 的计算规则关闭，它从 `var i` 重建出 `var i`。
<!--ja-->
この構成を単なる翻訳以上のものにするのは往復です。`K` へ写し戻せば元の論理式が返らなければなりません。まず項レベルの主張 `eraseTm-inv` です。`t` の数が零なら、`Empty.rec*` に沿って `eraseTm t p` の名前を替えると、`K` 上の項の間のパスとして `t` 自身が返ります。名前替えの関数 `Empty.rec* : ⊥* → K` は空の型の消去子であり、`K` の定数を一つ作るよう求められると `⊥*` の元を要求します。しかし `eraseTm` が組み立てた項には定数の節点が含まれないので、この関数が実際に適用されることはありません。したがって帰納には矛盾の場合と変数の場合しか残らず、後者は `mapTm` の計算規則、すなわち `var i` から `var i` を再構成する規則で閉じます。
<!--/-->

```agda

  eraseTm-inv : {n : ℕ} (t : Term K n) (p : countTm t ≡ 0)
              → mapTm Empty.rec* (eraseTm t p) ≡ t
  eraseTm-inv (con a) p = Empty.rec (snotz p)
  eraseTm-inv (var i) _ = refl

  erase-inv : {n : ℕ} (φ : Formula K n) (p : countFo φ ≡ 0)
```

<!--en-->
At the formula level the inverse `erase-inv` is proved by structural induction over the syntax tree, combining the term-level inverse with itself recursively. The atoms display the base pattern with two subparts: since `mapFo` distributes the relabelling into the two erased terms, the goal is a path between two applications of the same constructor, and `cong₂` lifts the pair of term-level paths `eraseTm-inv t _` and `eraseTm-inv u _` to that path. The zero-count proofs for the subterms come from `plus-zero-l` and `plus-zero-r` applied to `p`, exactly as in `erase` itself.
<!--zh-->
在公式层面，逆定律 `erase-inv` 由对语法树的结构归纳证明，把词项层面的逆与自身递归地结合起来。两条原子关系以两个子部分展示了基例模式：由于 `mapFo` 把改名分配到两个被消去的词项中，目标是同一构造子的两次应用之间的路径，`cong₂` 把词项层面的两条路径 `eraseTm-inv t _` 与 `eraseTm-inv u _` 提升为该路径。子词项的计数为零的证明由 `plus-zero-l` 与 `plus-zero-r` 作用于 `p` 得到，与 `erase` 自身完全一致。
<!--ja-->
論理式レベルでは、逆法則 `erase-inv` は構文木についての構造的帰納によって証明され、項レベルの逆を再帰的に組み合わせます。二つの原子関係が、二つの部分を持つ基底の場合を示します。`mapFo` が名前替えを消去された二つの項へ分配するので、ゴールは同じコンストラクタの二つの応用の間のパスであり、`cong₂` が項レベルの二つのパス `eraseTm-inv t _` と `eraseTm-inv u _` をそのパスへ引き上げます。部分項の数が零である証明は、`erase` 自身とまったく同様に、`p` に `plus-zero-l` と `plus-zero-r` を施して得られます。
<!--/-->

```agda
            → mapFo Empty.rec* (erase φ p) ≡ φ
  erase-inv (t ∈̇ u) p =
    cong₂ _∈̇_ (eraseTm-inv t (plus-zero-l p)) (eraseTm-inv u (plus-zero-r p))
  erase-inv (t ≐ u) p =
    cong₂ _≐_ (eraseTm-inv t (plus-zero-l p)) (eraseTm-inv u (plus-zero-r p))
```

<!--en-->
Because `erase` preserves the shape of the formula at every node, the induction hypothesis available at each node already has exactly the form the inverse needs there. The three binary connectives repeat the two-subpart pattern: for `∧̇`, `∨̇` and `⇒̇` the count of the whole splits between the two subformulas, and `cong₂` lifts the pair of induction hypotheses to a path between the reconstructed connectives. The uniformity is structural rather than coincidental: the inverse law is a property of the syntax tree, checked one node at a time.
<!--zh-->
由于 `erase` 在每个节点都保持公式的形状，每个节点可用的归纳假设已经恰是该处逆定律所需的形式。三条二元连接词重复双部分模式：对 `∧̇`、`∨̇` 与 `⇒̇`，整体的计数在两个子公式之间拆分，`cong₂` 把一对归纳假设提升为重建后的连接词之间的路径。这种一致性是结构性的而非偶然：逆定律是语法树的性质，一次核查一个节点。
<!--ja-->
`erase` がすべての節点で論理式の形を保つため、各節点で使える帰納の仮定は、そこで逆法則が必要とする形をすでにちょうど持っています。三つの二項結合子は二部分の型を繰り返します。`∧̇`、`∨̇`、`⇒̇` のいずれでも、全体の数は二つの部分論理式の間で分かれ、`cong₂` が一対の帰納の仮定を再構成された結合子の間のパスへ引き上げます。この一様さは偶然ではなく構造的なものです。逆法則は構文木の性質であり、一節点ずつ検査されるからです。
<!--/-->

```agda
  erase-inv (φ ∧̇ ψ) p =
    cong₂ _∧̇_ (erase-inv φ (plus-zero-l p)) (erase-inv ψ (plus-zero-r p))
  erase-inv (φ ∨̇ ψ) p =
    cong₂ _∨̇_ (erase-inv φ (plus-zero-l p)) (erase-inv ψ (plus-zero-r p))
  erase-inv (φ ⇒̇ ψ) p =
```

<!--en-->
Single-subpart nodes are correspondingly lighter. Falsum needs only `refl`, since both sides reduce to the constructor `⊥̇` itself. The two unbounded quantifiers use `cong` rather than `cong₂`, because they carry a single subformula: after the computation rule of `mapFo` unfolds, the goal is a path under `∃̇_`, and `cong ∃̇_ (erase-inv φ p)` supplies exactly that, with the same `p` passed through unchanged.
<!--zh-->
单子部分的情形相应地更轻。假式只需 `refl`，因为两边都化归为构造子 `⊥̇` 本身。两条无界量词使用 `cong` 而非 `cong₂`，因为它们只携带一个子公式：在 `mapFo` 的计算规则展开后，目标是 `∃̇_` 之下的一条路径，`cong ∃̇_ (erase-inv φ p)` 给出的恰是它，同一个 `p` 原样传入。
<!--ja-->
部分を一つだけ持つ節点はそれに応じて軽くなります。矛盾記号は `refl` だけで足ります。両辺ともコンストラクタ `⊥̇` 自身に簡約されるからです。二つの非有界量化子は部分論理式を一つしか持たないため、`cong₂` ではなく `cong` を用います。`mapFo` の計算規則が展開された後、ゴールは `∃̇_` の下のパスであり、`cong ∃̇_ (erase-inv φ p)` が与えるのはまさにそれです。同じ `p` がそのまま渡されます。
<!--/-->

```agda
    cong₂ _⇒̇_ (erase-inv φ (plus-zero-l p)) (erase-inv ψ (plus-zero-r p))
  erase-inv ⊥̇ _ = refl
  erase-inv (∃̇ φ) p = cong ∃̇_ (erase-inv φ p)
  erase-inv (∀̇ φ) p = cong ∀̇_ (erase-inv φ p)
  erase-inv (∀̇∈ t φ) p =
```

<!--en-->
The bounded quantifiers close the induction, mixing a term and a formula just as the atoms did: `cong₂` lifts the pair consisting of the term-level path `eraseTm-inv t (plus-zero-l p)` and the formula-level path `erase-inv φ (plus-zero-r p)`. With this clause the theorem is complete. Every formula of count zero is the exact image, up to a path, of its erased parameter-free form, so the boundary case of the occurrence interface is fully accounted for: over `K`, the constant-free formulas are precisely the parameter-free ones, with no decidability assumption anywhere.
<!--zh-->
有界量词结束了这次归纳，与原子一样混合一个词项与一个公式：`cong₂` 提升由词项层面的路径 `eraseTm-inv t (plus-zero-l p)` 与公式层面的路径 `erase-inv φ (plus-zero-r p)` 组成的对。到这一条款，定理完成。每条计数为零的公式都是其消去后的无参形式在相差一条路径意义下的精确像。于是出现接口的边界情形得到完整交代：在 `K` 上，无常元的公式恰是无参公式，且全程没有任何可判定性假设。
<!--ja-->
有界量化子がこの帰納を閉じます。原子と同じく項と論理式を混ぜます。`cong₂` が、項レベルのパス `eraseTm-inv t (plus-zero-l p)` と論理式レベルのパス `erase-inv φ (plus-zero-r p)` の対を引き上げます。この節で定理は完成です。個数が零のすべての論理式は、消去された無パラメータ形の、パスの差を除けば正確な像です。これで出現というインターフェースの境界の場合が完全に説明されました。`K` の上では、定数を含まない論理式は無パラメータ論理式とちょうど一致し、どこにも判定可能性の仮定は要りません。
<!--/-->

```agda
    cong₂ ∀̇∈ (eraseTm-inv t (plus-zero-l p)) (erase-inv φ (plus-zero-r p))
  erase-inv (∃̇∈ t φ) p =
    cong₂ ∃̇∈ (eraseTm-inv t (plus-zero-l p)) (erase-inv φ (plus-zero-r p))
```

<!--en-->
## Recap

Occurrences give a formula's constants a finite interface that never asks whether two symbols of the constant domain are equal. The count `countFo`{.Agda} indexes both the enumeration of the occurrences and, later, parameter abstraction, where each occurrence receives its own replacement variable; the placements and their lookup laws supply the resulting index arithmetic for concatenated environments. When the count is zero, `ZeroOccurrences`{.Agda} shows that the formula is the exact image of a parameter-free formula, so the empty constant domain can be adopted without losing any syntax.
<!--zh-->
## 小结

出现为公式的常元提供了一个有限接口，它从不追问常元域中两个符号是否相等。计数 `countFo`{.Agda} 既是出现之枚举的指标，也是此后参数抽象的指标：每次出现各得一个替代变量；安置装置及其查值定律为拼接环境补足所需的序号算术。当计数为零时，`ZeroOccurrences`{.Agda} 证明该公式恰是某条无参公式的精确像，于是可以采用空常元域而不损失任何语法。
<!--ja-->
## まとめ

出現は、論理式の定数に対して、定数域の二つの記号が等しいかを問わない有限のインターフェースを与えます。個数 `countFo`{.Agda} は出現の列挙の添字であると同時に、後のパラメータ抽象の添字でもあります。そこでは出現ごとに専用の置換変数が割り当てられ、配置とその参照法則が連結環境に対する添字計算を補います。個数が零のとき、`ZeroOccurrences`{.Agda} はその論理式が無パラメータ論理式の正確な像であることを示し、構文を何も失わずに空の定数域を採用できるのです。
<!--/-->
