<!--en-->
# Parameter abstraction

A formula with constants can be converted into a parameter-free formula by replacing each constant occurrence with a fresh variable and recording the constants in a vector. Supplying that vector through the environment preserves satisfaction, which makes formulas with parameters available to later coding arguments.

This chapter builds the replacement itself. The occurrence count from FOL.Manipulation.ConstantOccurrences fixes how many new variables are needed, and a placement decides which variable slot each occurrence receives. The substitution runs in a single structural pass, and the adequacy theorem at the end identifies satisfaction before and after, which is what later coding of formulas will rely on.
<!--zh-->
# 参数抽象

带常元的公式可通过将每次常元出现替换为新变量，并把这些常元记录在向量中，转成无参公式。通过环境供给该向量会保持满足关系，从而使带参数公式可用于后续符号化论证。

本章构造这个替换本身。FOL.Manipulation.ConstantOccurrences 中的出现计数决定了需要多少个新变量，而安置决定每次出现获得哪个变量位。替换只做一次结构遍历；章末的充分性定理识别替换前后的满足关系，这正是后续对公式符号化时所依赖的事实。
<!--ja-->
# パラメータ抽象

定数を含む論理式は、定数の各出現を新しい変数で置き換え、その定数をベクトルに記録することで、パラメータを持たない論理式へ変換できます。そのベクトルを環境から与えても充足関係は保存されるため、パラメータ付き論理式を後の符号化に利用できます。

本章ではこの置換そのものを構成します。FOL.Manipulation.ConstantOccurrences の出現数え上げが新しく必要な変数の個数を決め、配置が各出現にどの変数の枠を与えるかを決めます。置換は構造的な一回の走査で済み、章末の妥当性定理が置換前後の充足関係を同一視します。これが後で論理式を符号化するときに用いる事実です。
<!--/-->

<!--en-->
Chapter introductions of formulas often need constants: to say that a set $a$ is definable from parameters, one writes a formula mentioning $a$ by name. For coding arguments, however, it is convenient to work with parameter-free formulas only. Parameter abstraction is the translation that makes this possible: replace each constant occurrence by a fresh variable, and record the constants in a vector that the environment will supply.

The replacement works occurrence by occurrence, not constant by constant. If the constant $c$ appears twice, it is recorded twice and receives two variables. Recording occurrences this way means the translation never has to decide whether two names are equal, so the alphabet `K` needs no decidable equality; the positional count from the chapter on constant occurrences does all the bookkeeping.
<!--zh-->
公式的章首引言常常需要常元：要说集合 $a$ 可由参数定义，人们会写下提到 $a$ 的公式。但对编码论证而言，只使用无参公式会更方便。参数抽象正是使这成为可能的翻译：把每次常元出现换成新变量，并把诸常元记录在一个向量中，交给环境供给。

这个替换按出现逐一进行，而不是按常元本身。若常元 $c$ 出现两次，它就被记录两次、获得两个变量。按出现记录意味着翻译无须判断两个名字是否相等，因此字母表 `K` 不需要可判定相等；常元出现一章的位置计数完成了全部簿记。
<!--ja-->
論理式を使う議論では定数が要ります。集合 $a$ がパラメータ付きで定義可能だと言うには、$a$ を名前で言及する論理式を書くからです。しかし符号化の議論では、パラメータを持たない論理式だけを扱えると便利です。パラメータ抽象はそれを可能にする翻訳です。定数の各出現を新しい変数に置き換え、定数をベクトルに記録して環境から供給できるようにします。

この置き換えは定数ごとではなく、出現ごとに行われます。定数 $c$ が二度現れれば、二度記録され、二つの変数を受け取ります。出現単位で記録するため、翻訳は二つの名前が等しいかを判定する必要がなく、アルファベット `K` に可判定な等式は要りません。定数の出現を数える章の位置的な数え上げが簿記のすべてを担います。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

module FOL.Manipulation.ParameterAbstraction where

open import Base.Prelude
open import Base.Truth
open import FOL.ZFStructure using ( ZFStructure )
```

<!--en-->
Concretely, the translation consumes two pieces of data prepared in "Constants by occurrence": the number of constant occurrences, which fixes how many fresh variables are needed, and the recorded vector of constants, which fixes what those variables will stand for once interpreted. The replacement itself is described by a placement, a function deciding which variable slot each occurrence receives.

The whole construction is one structural pass over the formula. Its adequacy theorem, proved at the end of the chapter, identifies satisfaction of the original formula under a constant interpretation with satisfaction of the abstraction under the extended environment, and this identification is what later coding arguments rely on.
<!--zh-->
具体地，这个翻译消耗「逐次出现地处理常元」一章准备好的两份数据：常元出现的数目，它决定需要多少个新变量；以及记录下来的常元向量，它决定这些变量在解释之后代表什么。替换本身由一个安置描述，即一个函数，决定每次出现获得哪个变量位。

整个构造是对公式的一次结构性遍历。章末证明的充分性定理把原公式在常元解释下的满足，与抽象在扩张环境下的满足等同起来；后续编码论证所依赖的正是这一等同。
<!--ja-->
具体的には、この翻訳は前の章で用意された二つのデータを使います。定数の出現の個数は新しく必要な変数の数を決め、記録された定数のベクトルは、解釈の後でそれらの変数が何を表すかを決めます。置き換えそのものは配置と呼ばれる関数で記述され、各出現がどの変数の枠を受け取るかを決めます。

構成全体は論理式の上の一度の構造的な走査です。章の末尾で証明される妥当性の定理は、定数解釈の下での元の論理式の充足と、拡張された環境の下での抽象化の充足を同一視します。後の符号化の議論が依拠するのはまさにこの同一視です。
<!--/-->

```agda
open import FOL.Syntax using
  ( Term; con; var
  ; Formula; _∈̇_; _≐_; _∧̇_; _∨̇_; _⇒̇_; ⊥̇; ∃̇_; ∀̇_; ∀̇∈; ∃̇∈ )
import FOL.Semantics
open import FOL.Manipulation.ConstantOccurrences using
```

<!--en-->
Since every constant occurrence becomes a variable, the translated formula contains no constants at all: it lives over an alphabet with no inhabitants. The code uses the empty type `⊥*` as that alphabet. No interpretation of it is ever demanded, because there is nothing to interpret; the type only has to exist so the translated syntax has a well-formed carrier.
<!--zh-->
由于每次常元出现都成为变量，翻译后的公式完全不含常元：它定义在一个没有成员的字母表上。代码以空类型 `⊥*` 充当这个字母表。永远不会向它索要解释，因为无可解释之物；这个类型只需存在，使翻译后的语法有一个良构的载体。
<!--ja-->
定数の出現はすべて変数になるため、翻訳後の論理式には定数がまったく含まれません。つまり、元をひとつも持たないアルファベットの上にあります。コードでは空の型 `⊥*` がこのアルファベットの役を担います。解釈すべきものがないので、この解釈が実際に要求されることはなく、型が存在して翻訳後の構文に well-formed な台を与えるだけで十分です。
<!--/-->

```agda
  ( countTm; countFo; constantsTm; constantsFo; padRight; padLeft
  ; lookup-padRight; lookup-padLeft; lookup-map )
open import Cubical.Data.Nat using ( _+_ )
open import Cubical.Data.Vec using ( _++_; map )
import Cubical.Data.Empty as Empty
```

<!--en-->
## The abstraction

A placement assigns each constant occurrence a variable in a larger context. `placeFo` performs this replacement structurally, and `absFo` chooses the consecutive block after the original free variables, whose length is the occurrence count.

The traversal is stated for an arbitrary placement `θ`, and that generality is forced by the recursion: the placements used at a subformula are produced inside the traversal, so the induction hypothesis must be about all of them. Keeping `θ` abstract also keeps the proof of adequacy modular. This section builds the two traversals, over terms first and then formulas.
<!--zh-->
## 抽象

安置为每次常元出现指派较大语境中的一个变量。`placeFo` 按结构执行替换，而 `absFo` 选择原自由变量之后的连续区块，其长度正是出现次数。

遍历针对任意安置 `θ` 陈述，这种泛型是递归强加的：子公式处使用的安置就在遍历内部产生，归纳假设因此必须对所有安置成立。让 `θ` 保持抽象也使充分性证明保持模块化。本节先对词项、再对公式构造这两个遍历。
<!--ja-->
## 抽象化

配置は定数の各出現に、より大きな文脈の変数を割り当てます。`placeFo`{.Agda} はこの置換を構造的に行い、`absFo`{.Agda} は元の自由変数の直後にある、出現回数と同じ長さの連続した領域を選びます。

走査は任意の配置 `θ` に対して述べられます。この一般性は再帰から強制されます。部分論理式で用いられる配置は走査の内部で作られるため、帰納法の仮定はすべての配置について成り立つ必要があります。`θ` を抽象的なまま保つことで、妥当性の証明もモジュール的に保たれます。本節では項について、次に論理式について、この二つの走査を構成します。
<!--/-->

<!--en-->
The general form of the replacement is a traversal that takes, besides the formula, a placement `θ : Fin (countTm t) → Fin (n + k)`: it reads the occurrence slots of `t` in the order the counting chapter enumerates them, and for each one names a variable slot among the `n + k` available, of which `n` are the original free variables and `k` are the fresh parameter slots. The output is a term over the empty alphabet `⊥*`, since no constant survives.
<!--zh-->
替换的一般形式是一个遍历，除公式外还接受一个安置 `θ : Fin (countTm t) → Fin (n + k)`：它按计数章枚举的次序读取 `t` 的诸出现位，并为每一次出现指名 `n + k` 个可用位中的一个，其中 `n` 个是原自由变量，`k` 个是新的参数位。输出是空字母表 `⊥*` 上的词项，因为没有常元存活下来。
<!--ja-->
置き換えの一般形は走査で、論理式のほかに配置 `θ : Fin (countTm t) → Fin (n + k)` を受け取ります。`θ` は数え上げの章で列挙された順に `t` の出現の枠を読み、それぞれに対して利用可能な `n + k` 個の枠の一つを指名します。このうち `n` 個は元の自由変数、`k` 個は新しいパラメータの枠です。出力は空のアルファベット `⊥*` の上の項です。生き残る定数はないからです。
<!--/-->

```agda
placeTm : ∀ {ℓz ℓc} {K : Type ℓc} {n k} (t : Term K n)
        → (Fin (countTm t) → Fin (n + k)) → Term (⊥* {ℓz}) (n + k)
placeTm         (con c) θ = var (θ zero)
placeTm {k = k} (var i) θ = var (padRight k i)

placeFo : ∀ {ℓz ℓc} {K : Type ℓc} {n k} (φ : Formula K n)
```

<!--en-->
The term cases show the two moves. A constant `con c` has one occurrence, namely slot zero, and the placement says which variable replaces it: `var (θ zero)`. A variable `var i` contributes no occurrence, so the placement is unused, but the context has grown from `n` to `n + k` and the old index must be re-embedded: `padRight k` sends `i` to the same slot among the first `n`, which by the pad law keeps its value in a concatenated environment.
<!--zh-->
词项的两个情形展示了两种手法。常元 `con c` 恰有一次出现，即第零位，安置指出由哪个变量取代它：`var (θ zero)`。变量 `var i` 不贡献出现，故安置不被使用，但语境已从 `n` 增长为 `n + k`，旧序号必须重新嵌入：`padRight k` 把 `i` 送到前 `n` 个位中的同一位，由补位定律，它在拼接环境中仍取原值。
<!--ja-->
項の二つの場合が、二つの基本的な動きを示します。定数 `con c` は出現をちょうど一つ、すなわち第 0 枠に持ち、配置がどの変数で置き換えるかを決めます。それが `var (θ zero)` です。変数 `var i` は出現を持たないので配置は使われませんが、文脈は `n` から `n + k` へ伸びたため、古い添字を埋め込み直す必要があります。`padRight k` は `i` を先頭 `n` 枠の中の同じ位置へ送り、参照法則により連結された環境でも値は保たれます。
<!--/-->

```agda
        → (Fin (countFo φ) → Fin (n + k)) → Formula (⊥* {ℓz}) (n + k)
placeFo (t ∈̇ u)  θ = placeTm t (λ i → θ (padRight (countTm u) i))
                   ∈̇ placeTm u (λ j → θ (padLeft (countTm t) j))
placeFo (t ≐ u)  θ = placeTm t (λ i → θ (padRight (countTm u) i))
                   ≐ placeTm u (λ j → θ (padLeft (countTm t) j))
```

<!--en-->
At a binary node the occurrence list splits, and the placement arithmetic appears. Consider the atom `t ∈̇ u` where `t = con c` and `u = con d`: the occurrence list is `c ∷ d ∷ []`, with `c` at index 0 and `d` at index 1. The left term must therefore read the placement through `padRight`, skipping past the `countTm u` slots that belong to `u`, while the right term reads it through `padLeft`, stepping over the `countTm t` slots that belong to `t`. Each subterm then sees a placement on its own occurrence slots, and the two translated subterms recombine with the original connective.
<!--zh-->
在二元节点处出现表发生分裂，安置算术由此登场。考虑原子 `t ∈̇ u`，取 `t = con c`、`u = con d`：出现表是 `c ∷ d ∷ []`，`c` 在序号 0，`d` 在序号 1。于是左词项须经 `padRight` 读取安置，跳过属于 `u` 的 `countTm u` 个位；右词项须经 `padLeft` 读取，跨过属于 `t` 的 `countTm t` 个位。这样每个子词项看到的都是作用于自身出现位的安置，两个翻译后的子词项以原来的联结词重新组合。
<!--ja-->
二項ノードでは出現リストが分裂し、ここで配置の算術が現れます。原子 `t ∈̇ u` を、`t = con c`、`u = con d` とすると、出現リストは `c ∷ d ∷ []` で、`c` は添字 0、`d` は添字 1 にあります。そこで左の項は `padRight` を通して配置を読み、`u` に属する `countTm u` 個の枠を飛び越えます。右の項は `padLeft` を通して読み、`t` に属する `countTm t` 個の枠をまたぎます。こうして各部分項は自分の出現の枠だけに働く配置を受け取り、翻訳された二つの部分項が元の接続詞で再結合されます。
<!--/-->

```agda
placeFo (φ ∧̇ ψ)  θ = placeFo φ (λ i → θ (padRight (countFo ψ) i))
                   ∧̇ placeFo ψ (λ j → θ (padLeft (countFo φ) j))
placeFo (φ ∨̇ ψ)  θ = placeFo φ (λ i → θ (padRight (countFo ψ) i))
                   ∨̇ placeFo ψ (λ j → θ (padLeft (countFo φ) j))
placeFo (φ ⇒̇ ψ)  θ = placeFo φ (λ i → θ (padRight (countFo ψ) i))
```

<!--en-->
The formula traversal generalizes this example by structural recursion. Every two-part constructor, atom or propositional, splits its occurrence list in exactly this way: the first factor's occurrences precede the second's, so the left traversal composes `θ` with `padRight` past the right count and the right traversal with `padLeft` past the left count. Falsity `⊥̇` has no occurrences at all and translates to itself. No clause needs a second pass or a renaming lemma: composing the placements before recursing keeps the whole translation to one structural traversal.
<!--zh-->
公式遍历以结构递归推广了这个例子。每个由两部分构成的构造子，无论原子还是命题联结词，都恰以这种方式分裂其出现表：第一个因子的出现在前，第二个的在后，故左支的遍历把 `θ` 与越过右侧计数的 `padRight` 复合，右支则与越过左侧计数的 `padLeft` 复合。假值 `⊥̇` 没有任何出现，翻译为自身。没有哪条子句需要第二次遍历或改名引理：在递归之前先复合安置，使整个翻译保持为一次结构性遍历。
<!--ja-->
論理式の走査は、この例を構造的再帰で一般化したものです。二つの部分からなる構成子は、原子であれ命題的な接続詞であれ、出現リストをまさにこの方法で分割します。第一因子の出現が第二因子の出現に先立ち、左の走査は `θ` に右側の個数を越える `padRight` を、右の走査は左側の個数を越える `padLeft` を合成します。偽 `⊥̇` は出現をまったく持たず、自分自身に翻訳されます。どの節も二度目の走査や改名の補題を要しません。再帰の前に配置を合成しておくことで、翻訳全体が一度の構造的走査に保たれます。
<!--/-->

```agda
                   ⇒̇ placeFo ψ (λ j → θ (padLeft (countFo φ) j))
placeFo ⊥̇        θ = ⊥̇
placeFo (∃̇ φ)    θ = ∃̇ placeFo φ (λ j → suc (θ j))
placeFo (∀̇ φ)    θ = ∀̇ placeFo φ (λ j → suc (θ j))
placeFo (∀̇∈ t φ) θ = ∀̇∈ (placeTm t (λ i → θ (padRight (countFo φ) i)))
```

<!--en-->
Under a binder the context grows by one, and this is the second recurring move. In `∃̇∈ t φ`, the bound variable is consed onto the left of the environment when the semantics evaluates the body, so every parameter slot shifts up by one: the body is traversed under the placement `suc ∘ θ`, adjusted further by `padLeft` past the term's occurrence, while the term itself is placed at the front by `padRight` past the body's occurrences. The unbounded quantifiers `∃̇` and `∀̇` carry only the shift, and with these clauses the traversal covers all ten formula constructors.
<!--zh-->
在约束子之下语境增一，这是第二种反复出现的手法。在 `∃̇∈ t φ` 中，语义求值公式体时会把界定变量前置到环境左侧，故每个参数位都上移一：公式体在安置 `suc ∘ θ` 之下遍历，再经 `padLeft` 越过词项的出现而调整；词项本身则以越过公式体出现的 `padRight` 安置在前段。无界量词 `∃̇` 与 `∀̇` 只带移位。这些子句合起来覆盖了全部十个公式构造子。
<!--ja-->
束縛子の下では文脈が一つ伸びます。これが二つ目の繰り返し現れる動きです。`∃̇∈ t φ` では、意味論が本体を評価するときに束縛変数を環境の左に追加するため、パラメータの枠はすべて一つずれます。本体は配置 `suc ∘ θ` の下で走査され、さらに項の出現を越える `padLeft` で調整されます。項そのものは本体の出現を越える `padRight` で前の方に配置されます。非有界の量化子 `∃̇` と `∀̇` はずらしだけを持ちます。これらの節で十個の論理式の構成子がすべてカバーされます。
<!--/-->

```agda
                        (placeFo φ (λ j → suc (θ (padLeft (countTm t) j))))
placeFo (∃̇∈ t φ) θ = ∃̇∈ (placeTm t (λ i → θ (padRight (countFo φ) i)))
                        (placeFo φ (λ j → suc (θ (padLeft (countTm t) j))))
```

<!--en-->
The instance is the one the rest of the book will use: take the budget to be exactly the occurrence count and the placement to be the block that follows the variables. This is the required abstraction, and its type states the chapter's main result: a formula over `K` with `n` free variables becomes a parameter-free formula with `n + countFo φ` of them.

`padLeft n` is exactly the placement that sends occurrence `j` to slot `n + j`, so each recorded constant receives the first free slot after the original variables, in the order `constantsFo φ` lists them. Nothing else needs to be chosen.
<!--zh-->
本书余下部分使用的实例取如下参数：参数位的数目恰好等于出现次数，安置则取紧随原变量之后的那一段。这就是所需的抽象，其类型可以概括为：`K` 上带 `n` 个自由变量的公式，变为带 `n + countFo φ` 个自由变量的无参公式。

`padLeft n` 恰是把出现 `j` 送到第 `n + j` 位的那个安置，于是每个被记录的常元、按 `constantsFo φ` 列出它们的次序，分别获得原变量之后第一个空闲位。除此之外无须再做任何选择。
<!--ja-->
本の残りの部分で使うのは次のインスタンスです。予算を出現回数ちょうどにとり、配置は変数の直後に続く領域とします。これが求める抽象化であり、その型が本章の主結果を述べます。`K` 上の自由変数 `n` 個の論理式が、自由変数 `n + countFo φ` 個の無パラメータ論理式になります。

`padLeft n` は出現 `j` を枠 `n + j` へ送る配置そのものなので、記録された各定数は、`constantsFo φ` が並べる順に、元の変数の後ろの最初の空き枠を受け取ります。他に選ぶべきものはありません。
<!--/-->

<!--en-->
The definition is a single call: `absFo φ = placeFo φ (padLeft n)`. All the index arithmetic was already folded into the traversal, so the abstraction itself carries no cases of its own. Because the budget equals the count, the placement is a bijection between occurrence slots and parameter slots in effect, though the code never needs to say so.
<!--zh-->
定义只是一次调用：`absFo φ = placeFo φ (padLeft n)`。全部序号算术都已折入遍历之中，抽象本身没有任何情形需要处理。由于预算恰等于计数，安置实际上给出了出现位与参数位之间的双射，不过代码从不需要把这一点说出来。
<!--ja-->
定義は一度の呼び出しだけです。`absFo φ = placeFo φ (padLeft n)`。添字の算術はすべて走査の内側に繰り込まれているため、抽象化自身は場合分けを持ちません。予算が数え上げと一致するため、配置は事実上、出現の枠とパラメータの枠の間の全単射になりますが、コードがそのことを述べる必要はありません。
<!--/-->

```agda
absFo : ∀ {ℓz ℓc} {K : Type ℓc} {n} (φ : Formula K n) → Formula (⊥* {ℓz}) (n + countFo φ)
absFo {n = n} φ = placeFo φ (padLeft n)
```

<!--en-->
## Adequacy

Adequacy compares the original formula under a constant interpretation with its abstraction under an extended variable environment. When each placed variable contains the interpretation of its recorded constant, term denotation and formula satisfaction agree by structural induction.

The comparison is stated inside a structure `𝒮` with carrier `S`, under one interpretation `ι : K → S` of the original constants. Two semantic readings are set up side by side: `_⊨_` and `⟦_⟧` for formulas and terms over `K` under `ι`, and their renamed copies `_⊨₀_`, `⟦_⟧₀` for the abstraction's constant domain `⊥*`. The parameter-free side needs no genuine interpretation, since `⊥*` is empty, but the semantics module requires the data, and `Empty.rec*` supplies it vacuously.
<!--zh-->
## 充分性

充分性比较常元解释下的原公式与扩展变量环境下的抽象公式。只要安置后的每个变量都带有其所记录常元的解释，词项释义与公式满足关系便依结构归纳相符。

这一比较在载体为 `S` 的结构 `𝒮` 内、在原常元的一个解释 `ι : K → S` 之下陈述。两种语义读法并排建立：`_⊨_` 与 `⟦_⟧` 对应 `K` 上、`ι` 之下的公式与词项；其更名副本 `_⊨₀_`、`⟦_⟧₀` 对应抽象的常元域 `⊥*`。无参一侧不需要真正的解释，因为 `⊥*` 为空，但语义模块要求这份资料，`Empty.rec*` 空虚地供给了它。
<!--ja-->
## 妥当性

妥当性は、定数解釈の下にある元の論理式と、拡張した変数環境の下にある抽象化後の論理式を比較します。配置された各変数が記録済みの定数の解釈を持つなら、項の表示と論理式の充足関係は構造帰納法で一致します。

この比較は、台が `S` である構造 `𝒮` の中で、元の定数の一つの解釈 `ι : K → S` の下に述べられます。二つの意味論の読み方が並べて用意されます。`_⊨_` と `⟦_⟧` は `K` 上、`ι` の下の論理式と項に対応し、その改名されたコピー `_⊨₀_`・`⟦_⟧₀` は抽象化の定数域 `⊥*` に対応します。`⊥*` は空なので無パラメータの側に本物の解釈は要りませんが、意味論のモジュールはこのデータを要求するため、`Empty.rec*` が空虚にそれを供給します。
<!--/-->

<!--en-->
Adequacy is the statement that the abstraction does not change meaning. It compares two evaluations of the same formula: the original syntax over `K` with its constants interpreted by a map `ι : K → S`, against the translated syntax over the empty alphabet evaluated in the concatenated environment `γ ++ σ`, where `γ` holds the values of the original free variables and `σ` holds the interpretations of the recorded constants. Here `S` is the carrier of a structure `𝒮` over a truth algebra `𝕋`, and `S ^ n` is the type of environments of length `n`.
<!--zh-->
充分性是说抽象不改变意义。它比较同一公式的两种求值：`K` 上的原语法、其常元由映射 `ι : K → S` 解释；对空字母表上的翻译语法，在拼接环境 `γ ++ σ` 中求值，其中 `γ` 存放原自由变量的值，`σ` 存放所记录常元的解释。这里 `S` 是真值代数 `𝕋` 上结构 `𝒮` 的载体，`S ^ n` 是长度为 `n` 的环境的类型。
<!--ja-->
妥当性とは、抽象化が意味を変えないという主張です。同じ論理式の二つの評価を比較します。一方は `K` 上の元の構文で、定数は写像 `ι : K → S` によって解釈されます。他方は空のアルファベット上の翻訳後の構文で、連結された環境 `γ ++ σ` の中で評価されます。`γ` は元の自由変数の値を、`σ` は記録された定数の解釈を保持します。ここで `S` は真理値代数 `𝕋` の上の構造 `𝒮` の台であり、`S ^ n` は長さ `n` の環境の型です。
<!--/-->

```agda
module _ {ℓ ℓ'} (𝕋 : TruthAlgebra ℓ ℓ') (𝒮 : ZFStructure 𝕋) where

  open TruthAlgebra 𝕋
  open ZFStructure 𝒮

  private module Sem = FOL.Semantics 𝕋 𝒮
  open Sem using ( _^_ )
```

<!--en-->
The comparison rests on a single hypothesis connecting the two sides: for every occurrence, the variable the placement named holds the interpretation of the constant recorded there, that is, `lookup (θ j) (γ ++ σ) ≡ ι (lookup j (constantsFo φ))`. All that follows is structural induction on the syntax with this hypothesis maintained. Since the translated syntax lives over the empty alphabet, its reading `_⊨₀_` and `⟦_⟧₀` needs no genuine constant interpretation, though the semantics module requires one as data; the elimination of the empty type supplies it vacuously.
<!--zh-->
这一比较只依赖一条连接两侧的假设：对每次出现，安置所指名的变量持有该处所记录常元的解释，即 `lookup (θ j) (γ ++ σ) ≡ ι (lookup j (constantsFo φ))`。以下的一切都是在此假设之下对语法的结构归纳。由于翻译后的语法定义在空字母表上，其读法 `_⊨₀_` 与 `⟦_⟧₀` 不需要真正的常元解释，尽管语义模块要求这份资料；空类型的消去空虚地供给了它。
<!--ja-->
この比較は、両側をつなぐただ一つの仮定に依存します。各出現について、配置の指名した変数がそこに記録された定数の解釈を保持する、すなわち `lookup (θ j) (γ ++ σ) ≡ ι (lookup j (constantsFo φ))` というものです。この後のすべては、この仮定を保ちながら構文に対する構造的帰納法です。翻訳後の構文は空のアルファベットの上にあるため、その読み方 `_⊨₀_` と `⟦_⟧₀` には本物の定数解釈は要りません。ただし意味論のモジュールはこのデータを要求するため、空の型の消去が空虚にそれを供給します。
<!--/-->

```agda

  module _ {ℓz ℓc} {K : Type ℓc} (ι : K → S) where

    open Sem.At K ι using ( _⊨_; ⟦_⟧ )
    open Sem.At (⊥* {ℓz}) Empty.rec* using ()
      renaming ( _⊨_ to _⊨₀_ ; ⟦_⟧ to ⟦_⟧₀ )
```

<!--en-->
The statement is generic in the placement, and it has to be, because the recursion's placements are built at the recursive calls. It is stated at a **variable** environment `γ` and a **variable** parameter environment `σ`, constrained by one hypothesis: at every occurrence, the slot the placement names holds the interpretation of the constant the collection recorded there. That hypothesis is the whole content of "the constants are supplied in the environment", and stating it as a hypothesis rather than substituting a concrete environment is what keeps every clause from normalizing a vector.

Splitting the hypothesis is the only bookkeeping the two-part constructors need, and each half is one composition with a pad law.
<!--zh-->
这一陈述对安置是泛型的，也必须如此，因为递归中的诸安置是在递归调用处产生的。它陈述在**变元**环境 `γ` 与**变元**参数环境 `σ` 处，受一条假设约束：在每次出现处，安置所指名的那个位置存放着在该处记录的诸常元的解释。这条假设就是「常元由环境供给」的全部内容；把它取作假设、而不是代入一个具体环境，正是让每条子句都不必归一化一个向量的原因。

对由两部分构成的构造子，唯一要做的处理就是拆分这条假设，拆出的每一半各与补位定律复合一次。
<!--ja-->
この主張は配置 `θ` に関して汎用的です。しかも汎用的でなければなりません。再帰における配置は再帰呼び出しの箇所で作られるからです。主張は**変数に依存しない形で**与えた環境 `γ` とパラメータ環境 `σ` の上で述べられ、ただ一つの仮定で制約されます。すなわち、出現のたびに、配置の指す位置にはその位置に記録された定数の解釈が入っている、というものです。この仮定こそ「定数が環境から供給される」の全内容であり、具体的な環境を代入するのではなく仮定として述べることで、どの節もベクトルを正規化する必要がなくなります。

二つの部分からなる構成子に必要な準備は、この仮定を二つに分けることだけです。分かれた各半分は、それぞれ補埋の法則との一度の合成になります。
<!--/-->

<!--en-->
The induction's invariant is the hypothesis `h` about the full occurrence vector, and the only new work is splitting it when a binary constructor divides that vector into a left part `p` and a right part `q`. Suppose `h` says that in `γ ++ σ`, slot `θ j` holds the interpretation of the `j`-th entry of `p ++ q`. The left operand needs this only for indices `j` below `length p`, and reading such an index through `padRight` past `q` recovers exactly the entry of `p`: `lookup-padRight` is that law. Composing it with `h` and then applying `ι` gives the left premise of the recursive call.
<!--zh-->
归纳的不变量是关于完整出现向量的假设 `h`，唯一的新工作是在二元构造子把该向量分成左半 `p` 与右半 `q` 时拆分它。设 `h` 说在 `γ ++ σ` 中，位 `θ j` 存放 `p ++ q` 第 `j` 个条目的解释。左运算项只需要 `j` 小于 `p` 长度的那些序号，而经越过 `q` 的 `padRight` 读取这样的序号恰恢复 `p` 的对应条目：`lookup-padRight` 正是这条定律。把它与 `h` 复合、再施加 `ι`，便得到递归调用所需的左前提。
<!--ja-->
帰納法の不変条件は、出現ベクトル全体に関する仮定 `h` です。新しく必要な仕事は、二項の構成子がこのベクトルを左の部分 `p` と右の部分 `q` に分けるときに、それを分割することだけです。`h` が、`γ ++ σ` の中の枠 `θ j` に `p ++ q` の第 `j` 項の解釈が入っていると述べているとします。左の被演算子に必要なのは `p` の長さより小さい添字 `j` だけで、そのような添字を `q` を越える `padRight` を通して読めば、`p` の対応する項がちょうど回復します。それが法則 `lookup-padRight` です。これを `h` と合成し、続けて `ι` を施せば、再帰呼び出しの左の前提が得られます。
<!--/-->

```agda
    private
      leftHalf : ∀ {n k a b} (θ : Fin (a + b) → Fin (n + k))
                 (γ : S ^ n) (σ : S ^ k) (p : Vec K a) (q : Vec K b)
               → (∀ j → lookup (θ j) (γ ++ σ) ≡ ι (lookup j (p ++ q)))
               → (∀ i → lookup (θ (padRight b i)) (γ ++ σ) ≡ ι (lookup i p))
```

<!--en-->
The right half is the mirror image: indices of `q` are read through `padLeft`, which steps over exactly the `a` slots of `p`, and `lookup-padLeft` identifies the entry found in the concatenation with the entry of `q`. Note that `a` is an explicit argument of `rightHalf` while it was implicit in `leftHalf`: the placement's domain `Fin (a + b)` does not by itself determine `a`, whereas `padLeft` must be told precisely how many slots to step over.
<!--zh-->
右半是其镜像：`q` 的序号经 `padLeft` 读取，它恰跨过 `p` 的 `a` 个位，而 `lookup-padLeft` 把在拼接中读到的条目等同于 `q` 的对应条目。注意 `a` 在 `rightHalf` 中是显式参数，而在 `leftHalf` 中是隐式的：安置的定义域 `Fin (a + b)` 本身不足以确定 `a`，而 `padLeft` 必须被确切告知要跨过多少个位。
<!--ja-->
右半分はその鏡像です。`q` の添字は `padLeft` を通して読まれ、これは `p` の `a` 個の枠をちょうどまたぎます。そして `lookup-padLeft` が、連結の中で読み取った項を `q` の対応する項と同一視します。`a` が `rightHalf` では明示的な引数で `leftHalf` では暗黙だったことに注意してください。配置の定義域 `Fin (a + b)` だけでは `a` は定まりませんが、`padLeft` はいくつの枠をまたぐかを正確に知らされる必要があるからです。
<!--/-->

```agda
      leftHalf θ γ σ p q h i = h (padRight _ i) ∙ cong ι (lookup-padRight p q i)

      rightHalf : ∀ {n k} a {b} (θ : Fin (a + b) → Fin (n + k))
                  (γ : S ^ n) (σ : S ^ k) (p : Vec K a) (q : Vec K b)
                → (∀ j → lookup (θ j) (γ ++ σ) ≡ ι (lookup j (p ++ q)))
                → (∀ j → lookup (θ (padLeft a j)) (γ ++ σ) ≡ ι (lookup j q))
```

<!--en-->
With `leftHalf` and `rightHalf` in place, the splitting invariant is established once and for all. Every binary clause of the induction below restricts the joint hypothesis through one of these two lemmas, and no clause ever looks inside the concatenated environment again.
<!--zh-->
有了 `leftHalf` 与 `rightHalf`，拆分的不变量便一劳永逸地建立起来。下面归纳的每条二元子句都经这两个引理之一限制合并的假设，此后再没有子句需要查看拼接环境的内部。
<!--ja-->
`leftHalf` と `rightHalf` が揃えば、分割の不変条件は一度限り確立されます。以下の帰納法の二項の節はすべて、この二つの補題のどちらかを通して結合仮定を制限するだけで、どの節も再び連結された環境の内部を見ることはありません。
<!--/-->

```agda
      rightHalf a θ γ σ p q h j = h (padLeft a j) ∙ cong ι (lookup-padLeft a p q j)
```

<!--en-->
Terms first, two cases and both immediate. A constant's value is what the hypothesis says the slot holds; a variable's value is untouched, and the pad law finds it again in the extended environment.
<!--zh-->
先看词项，两个情形都立即成立。常元的取值正是假设所述那个位置上的解释；变量的取值不变，补位定律保证它在扩张后的环境中仍取原值。
<!--ja-->
まず項から始めます。二つの場合はいずれもすぐに示せます。定数の値は、仮定がその位置に述べている解釈そのものです。変数の値は変化せず、補埋の法則が拡張された環境の中でそれを再び見つけ出します。
<!--/-->

<!--en-->
The induction starts at terms, where the invariant already does all the work. The claim is that the value of `t` in `γ` under the interpretation `ι` equals the value of the translated term in `γ ++ σ` over the empty alphabet, whenever `h` fills the placed slots correctly. For a constant `con c` the translation is `var (θ zero)`, whose value in `γ ++ σ` is `lookup (θ zero) (γ ++ σ)`; the hypothesis `h zero` identifies it with `ι c`, which is exactly the claim, up to the direction in which the equation is stated.
<!--zh-->
归纳从词项开始，这里不变量已经完成了全部工作。命题是：只要 `h` 正确填好诸安置位，`t` 在解释 `ι` 之下于 `γ` 中的取值，就等于翻译后的词项在空字母表上于 `γ ++ σ` 中的取值。对常元 `con c`，翻译是 `var (θ zero)`，它在 `γ ++ σ` 中的取值是 `lookup (θ zero) (γ ++ σ)`；假设 `h zero` 把它等同于 `ι c`，这恰是命题，只是等式的方向相反。
<!--ja-->
帰納法は項から始まります。ここでは不変条件がすでにすべての仕事をしています。主張はこうです。`h` が配置された枠を正しく埋めているなら、解釈 `ι` の下で `t` の `γ` における値は、空のアルファベットの上で翻訳後の項の `γ ++ σ` における値に等しい。定数 `con c` の翻訳は `var (θ zero)` で、その `γ ++ σ` での値は `lookup (θ zero) (γ ++ σ)` です。仮定 `h zero` がこれを `ι c` と同一視します。これはまさに主張であり、等式の向きが逆なだけです。
<!--/-->

```agda
    ⟦⟧-place : ∀ {n k} (t : Term K n) (θ : Fin (countTm t) → Fin (n + k))
               (γ : S ^ n) (σ : S ^ k)
             → (∀ j → lookup (θ j) (γ ++ σ) ≡ ι (lookup j (constantsTm t)))
             → ⟦ t ⟧ γ ≡ ⟦ placeTm t θ ⟧₀ (γ ++ σ)
    ⟦⟧-place (con c) θ γ σ h = sym (h zero)
```

<!--en-->
For a variable `var i` nothing was replaced, only re-indexed: the translation moved it to `padRight k i`, the same slot in the wider context, and the pad law shows that looking it up in `γ ++ σ` recovers the original value. With the constant and variable cases settled, every remaining constructor is either a two-part node handled by the splitting invariant or a binder, and the formula-level induction follows the same pattern.
<!--zh-->
对变量 `var i`，没有任何东西被替换，只是重新编号：翻译把它移到 `padRight k i`，即较宽语境中的同一位，补位定律表明在 `γ ++ σ` 中查出即可恢复原值。常元与变量两个情形解决后，其余构造子要么是由拆分不变量处理的二元节点，要么是约束子，公式层面的归纳遵循同一模式。
<!--ja-->
変数 `var i` では何も置き換えられず、付け替えられただけです。翻訳はそれを `padRight k i`、すなわち広い文脈の中の同じ枠へ移し、補埋の法則により `γ ++ σ` で調べれば元の値が回復します。定数と変数の場合が済むと、残りの構成子は分割の不変条件で扱われる二項ノードか束縛子のどちらかで、論理式レベルの帰納法も同じ型に従います。
<!--/-->

```agda
    ⟦⟧-place (var i) θ γ σ h = sym (lookup-padRight γ σ i)
```

<!--en-->
Then the twelve cases of the induction, ten formula cases here and the two term cases just discharged. Every primitive propositional clause is a congruence, because the semantics assigns its constructor exactly the truth algebra's operation and there is no translation layer to cross. The four binding clauses push a value onto the environment and appeal to the induction hypothesis at the extended one, and the hypothesis about the parameter slots travels **unchanged**: consing on the left and shifting the placement by `suc` cancel each other by computation, so the binders need no lemma of their own. The two bounded clauses split, term on the left and body on the right, exactly as their constructors do.
<!--zh-->
然后是归纳的十二个情形：十个公式情形在此处理，两个词项情形刚刚证毕。命题的每条原语子句都是同余，因为语义为每个构造子指派的恰是真值代数的对应运算，中间无须任何转换。四条约束子句向环境添加一个取值，并在扩张后的环境处援引归纳假设，而关于诸参数位的那条假设**原样**适用：左侧的前置与安置的 `suc` 移位由计算相互抵消，于是约束子不需要自己的引理。两条有界子句照它们的构造子那样一分为二，词项在左，公式体在右。
<!--ja-->
続いて帰納法の十二の場合です。ここで十個の論理式の場合を扱い、二つの項の場合は先ほど証明済みです。命題の各原始節はすべて合同です。意味論が各構成子に割り当てるのは真理値代数の対応する演算そのものであり、間に変換の層がないからです。四つの束縛節は環境に値を一つ追加し、拡張後の環境で帰納法の仮定を用いますが、パラメータ位置に関する仮定は**そのまま**通用します。左側への要素の追加と配置の `suc` による移し替えは計算によって打ち消し合うので、束縛子は固有の補題を必要としません。二つの有界節は、その構成子と同じく左に項、右に本体という形で二分割されます。
<!--/-->

<!--en-->
The formula-level statement `⊨-place` has the same shape as the term lemma, with satisfaction in place of denotation: under the hypothesis `h` about the placed slots, `(γ ⊨ φ)` equals `((γ ++ σ) ⊨₀ placeFo φ θ)`. The representative atom is membership `t ∈̇ u`: satisfaction of an atom is a congruence of the two term values along the structure's membership, so the clause applies the term lemma to each operand, at the placements the traversal actually used.
<!--zh-->
公式层面的陈述 `⊨-place` 与词项引理形状相同，只是以满足关系取代取值：在关于诸安置位的假设 `h` 之下，`(γ ⊨ φ)` 等于 `((γ ++ σ) ⊨₀ placeFo φ θ)`。代表性的原子是属于关系 `t ∈̇ u`：原子的满足是两个词项取值沿结构所属关系的同余，故该子句在遍历实际使用的安置处对两个运算项各施词项引理。
<!--ja-->
論理式レベルの主張 `⊨-place` は項の補題と同じ形をしています。表示の代わりに充足が現れます。配置された枠に関する仮定 `h` の下で、`(γ ⊨ φ)` は `((γ ++ σ) ⊨₀ placeFo φ θ)` に等しい。代表的な原子は所属 `t ∈̇ u` です。原子の充足は二つの項の値の、構造の所属関係に沿った合同なので、この節は走査が実際に用いた配置で各被演算子に項の補題を適用します。
<!--/-->

```agda
    ⊨-place : ∀ {n k} (φ : Formula K n) (θ : Fin (countFo φ) → Fin (n + k))
              (γ : S ^ n) (σ : S ^ k)
            → (∀ j → lookup (θ j) (γ ++ σ) ≡ ι (lookup j (constantsFo φ)))
            → (γ ⊨ φ) ≡ ((γ ++ σ) ⊨₀ placeFo φ θ)
    ⊨-place (t ∈̇ u) θ γ σ h = cong₂ _∈ˢ_
```

<!--en-->
The per-operand hypothesis is precisely what the splitting invariant supplies: the joint hypothesis `h` for `constantsTm t ++ constantsTm u`, restricted on the left by `padRight` and on the right by `padLeft`. The equality atom `t ≐ u` is handled identically, with the structure's equality `≈ˢ` in place of membership, and the two propositional connectives that follow need only the formula-level induction in place of the term lemma.
<!--zh-->
每个运算项的假设恰由拆分不变量供给：针对 `constantsTm t ++ constantsTm u` 的合并假设 `h`，左侧经 `padRight` 限制，右侧经 `padLeft` 限制。相等原子 `t ≐ u` 的处理完全相同，只是以结构的相等 `≈ˢ` 代替属于；随后的命题联结词只需把词项引理换成公式层归纳。
<!--ja-->
各被演算子の仮定は、分割の不変条件が供給するものそのものです。`constantsTm t ++ constantsTm u` に対する結合仮定 `h` を、左では `padRight` で、右では `padLeft` で制限したものです。等号の原子 `t ≐ u` もまったく同様に扱われ、所属の代わりに構造の等号 `≈ˢ` が現れます。続く命題的な接続詞では、項の補題を論理式レベルの帰納に置き換えるだけです。
<!--/-->

```agda
      (⟦⟧-place t (λ i → θ (padRight (countTm u) i)) γ σ
        (leftHalf θ γ σ (constantsTm t) (constantsTm u) h))
      (⟦⟧-place u (λ j → θ (padLeft (countTm t) j)) γ σ
        (rightHalf (countTm t) θ γ σ (constantsTm t) (constantsTm u) h))
    ⊨-place (t ≐ u) θ γ σ h = cong₂ _≈ˢ_
```

<!--en-->
Conjunction is the first purely propositional clause. The semantics defines satisfaction of `φ ∧̇ ψ` by applying the truth algebra's conjunction operation `_⊓_` to the two satisfaction values, so the clause is `cong₂ _⊓_` under the two induction hypotheses, with `h` split between `constantsFo φ` and `constantsFo ψ`. The proof treats `(γ ⊨ φ) ⊓ (γ ⊨ ψ)` simply as a value of `Ω`: it uses congruence alone, without assuming or decomposing any pair representation.
<!--zh-->
合取是第一条纯命题子句。语义把 `φ ∧̇ ψ` 的满足定义为将真值代数的合取运算 `_⊓_` 施于两个满足值，故该子句是在两条归纳假设之下的 `cong₂ _⊓_`，其中 `h` 在 `constantsFo φ` 与 `constantsFo ψ` 之间拆分。证明只把 `(γ ⊨ φ) ⊓ (γ ⊨ ψ)` 当作 `Ω` 中的值，并且只使用同余，不假定它具有对的表示，也不将其拆解。
<!--ja-->
連言が最初の純粋に命題的な節です。意味論は `φ ∧̇ ψ` の充足を、二つの充足値に真理値代数の連言の演算 `_⊓_` を施したものとして定義するので、この節は二つの帰納法の仮定の下での `cong₂ _⊓_` になり、`h` は `constantsFo φ` と `constantsFo ψ` の間で分割されます。証明は `(γ ⊨ φ) ⊓ (γ ⊨ ψ)` を単に `Ω` の値として扱い、合同だけを用います。対による表現を仮定することも、それを分解することもありません。
<!--/-->

```agda
      (⟦⟧-place t (λ i → θ (padRight (countTm u) i)) γ σ
        (leftHalf θ γ σ (constantsTm t) (constantsTm u) h))
      (⟦⟧-place u (λ j → θ (padLeft (countTm t) j)) γ σ
        (rightHalf (countTm t) θ γ σ (constantsTm t) (constantsTm u) h))
    ⊨-place (φ ∧̇ ψ) θ γ σ h = cong₂ _⊓_
```

<!--en-->
Disjunction repeats the pattern with the truth algebra's disjunction operation `⊔`, and implication with its implication operation `⇒`. The three propositional clauses differ only in which truth algebra operation `cong₂` is applied to; everything else, including the split hypothesis, is identical.
<!--zh-->
析取以真值代数的析取运算 `⊔` 重复同一模式，蕴涵则使用其蕴涵运算 `⇒`。三条命题子句只在 `cong₂` 所施加的真值代数运算上不同；包括拆分后的假设在内，其余完全一致。
<!--ja-->
選言は真理値代数の選言の演算 `⊔` で、含意はその含意の演算 `⇒` で同じパターンを繰り返します。三つの命題的な節が違うのは、`cong₂` が施される真理値代数の演算だけです。分割された仮定を含め、その他の部分はまったく同じです。
<!--/-->

```agda
      (⊨-place φ (λ i → θ (padRight (countFo ψ) i)) γ σ
        (leftHalf θ γ σ (constantsFo φ) (constantsFo ψ) h))
      (⊨-place ψ (λ j → θ (padLeft (countFo φ) j)) γ σ
        (rightHalf (countFo φ) θ γ σ (constantsFo φ) (constantsFo ψ) h))
    ⊨-place (φ ∨̇ ψ) θ γ σ h = cong₂ _⊔_
```

<!--en-->
At this point the pattern is worth stating once: every remaining clause either applies a congruence at the truth algebra operation the semantics chose for its constructor, or pushes a value onto the environment and recurses. No clause needs a new idea.
<!--zh-->
至此值得把这个模式一次性说清：余下的每条子句，要么在其构造子所对应的真值代数运算处施加同余，要么向环境添加一个取值后递归。没有哪条子句需要新的想法。
<!--ja-->
ここでパターンを一度まとめておきます。残りの各節は、その構成子に意味論が割り当てた真理値代数の演算で合同を取るか、環境に値を一つ追加して再帰するかのどちらかであり、新しい発想を必要とする節はありません。
<!--/-->

```agda
      (⊨-place φ (λ i → θ (padRight (countFo ψ) i)) γ σ
        (leftHalf θ γ σ (constantsFo φ) (constantsFo ψ) h))
      (⊨-place ψ (λ j → θ (padLeft (countFo φ) j)) γ σ
        (rightHalf (countFo φ) θ γ σ (constantsFo φ) (constantsFo ψ) h))
    ⊨-place (φ ⇒̇ ψ) θ γ σ h = cong₂ _⇒_
```

<!--en-->
Falsity confirms this. Both sides of the equation are the truth algebra's bottom whatever the environment or placement may be, so the clause is `refl`. It is also the one constructor whose translation never mentions the parameter block.
<!--zh-->
假值印证了这一点。无论环境或安置如何，等式两边都是真值代数的底，故该子句就是 `refl`。它也是唯一一个翻译后根本不提及参数块的构造子。
<!--ja-->
偽がこれを裏付けます。環境や配置がどうであれ、等式の両辺は真理値代数の底なので、この節は `refl` で済みます。翻訳がパラメータ領域にまったく言及しない唯一の構成子でもあります。
<!--/-->

```agda
      (⊨-place φ (λ i → θ (padRight (countFo ψ) i)) γ σ
        (leftHalf θ γ σ (constantsFo φ) (constantsFo ψ) h))
      (⊨-place ψ (λ j → θ (padLeft (countFo φ) j)) γ σ
        (rightHalf (countFo φ) θ γ σ (constantsFo φ) (constantsFo ψ) h))
    ⊨-place ⊥̇       θ γ σ h = refl
```

<!--en-->
The unbounded quantifier `∃̇ φ` is the binder case, and its content is that the shift cancels. The traversal placed the body under `suc ∘ θ`, because consing the bound value onto the left moves every parameter slot up by one; the semantics quantifies over `x ∷ γ`. The recursive claim is therefore invoked at `x ∷ γ`, and there `lookup (suc (θ j)) (x ∷ γ ++ σ)` computes to `lookup (θ j) (γ ++ σ)`, which is exactly `h`. The cancellation is definitional, so no shifting lemma appears anywhere in the proof.
<!--zh-->
无界量词 `∃̇ φ` 是约束子情形，其内容是移位相互抵消。遍历把公式体置于 `suc ∘ θ` 之下，因为把界定值前置到左侧使每个参数位上移一；语义则对 `x ∷ γ` 量化。于是递归命题在 `x ∷ γ` 处被援引，在那里 `lookup (suc (θ j)) (x ∷ γ ++ σ)` 由计算化归为 `lookup (θ j) (γ ++ σ)`，恰是 `h`。这个抵消是定义性的，因此证明中不出现任何移位引理。
<!--ja-->
非有界の量化子 `∃̇ φ` が束縛子の場合で、その内容はずらしが打ち消し合うことです。走査は本体を `suc ∘ θ` の下に置きました。束縛値を左に追加するとすべてのパラメータ枠が一つずれるからです。一方、意味論は `x ∷ γ` の上で量化します。そこで再帰的主張は `x ∷ γ` で用いられ、そこでは `lookup (suc (θ j)) (x ∷ γ ++ σ)` が計算によって `lookup (θ j) (γ ++ σ)` に化け、これはちょうど `h` です。この打ち消しは定義的なので、証明のどこにもずらしのための補題は現れません。
<!--/-->

```agda
    ⊨-place (∃̇ φ)   θ γ σ h = cong (⋁ S) (funExt (λ x →
      ⊨-place φ (λ j → suc (θ j)) (x ∷ γ) σ h))
    ⊨-place (∀̇ φ)   θ γ σ h = cong (⋀ S) (funExt (λ x →
      ⊨-place φ (λ j → suc (θ j)) (x ∷ γ) σ h))
    ⊨-place (∀̇∈ t φ) θ γ σ h = cong (⋀ S) (funExt (λ x → cong₂ _⇒_
```

<!--en-->
The universal quantifier `∀̇` is the same argument with the algebra's universal-quantification operation `⋀` in place of its existential-quantification operation `⋁`; the outer `cong` is the only place the operation is named, and the induction underneath is identical.
<!--zh-->
全称量词 `∀̇` 的论证相同，只是以代数的全称量化运算 `⋀` 代替存在量化运算 `⋁`；外层的 `cong` 是唯一指名该运算之处，其下的归纳毫无二致。
<!--ja-->
全称量化子 `∀̇` の議論も同じで、代数の存在量化の演算 `⋁` の代わりに全称量化の演算 `⋀` が現れるだけです。演算が名指しされるのは外側の `cong` の一点だけで、その下の帰納は同一です。
<!--/-->

```agda
      (cong (x ∈ˢ_) (⟦⟧-place t (λ i → θ (padRight (countFo φ) i)) γ σ
        (leftHalf θ γ σ (constantsTm t) (constantsFo φ) h)))
      (⊨-place φ (λ j → suc (θ (padLeft (countTm t) j))) (x ∷ γ) σ
        (rightHalf (countTm t) θ γ σ (constantsTm t) (constantsFo φ) h))))
    ⊨-place (∃̇∈ t φ) θ γ σ h = cong (⋁ S) (funExt (λ x → cong₂ _⊓_
```

<!--en-->
The bounded quantifiers combine the two moves. For `∀̇∈ t φ` the traversal abstracted the term `t` at the front of the context, through `padRight` past the body's occurrences, and shifted the body's placement by `suc` composed with `padLeft` past the term's occurrence. The clause is accordingly a `cong₂ _⇒_` of `x`'s membership in the abstracted bound, via the term lemma, and the recursive claim at `x ∷ γ`, via the shifted induction; `leftHalf` and `rightHalf` split `h` between `constantsTm t` and `constantsFo φ`. The existential bounded quantifier `∃̇∈` mirrors it with `⊓` in place of `⇒`. Every constructor of the language is now covered by the same invariant.
<!--zh-->
有界量词把两种手法合起来。对 `∀̇∈ t φ`，遍历把词项 `t` 在语境前段抽象，经越过公式体出现的 `padRight`；并把公式体的安置经 `padLeft` 越过词项出现后再移位 `suc`。相应地，该子句是二者的 `cong₂ _⇒_`：一侧经词项引理得到 `x` 属于抽象后界定项，另一侧经移位后的归纳得到在 `x ∷ γ` 处的递归命题；`leftHalf` 与 `rightHalf` 把 `h` 在 `constantsTm t` 与 `constantsFo φ` 之间拆分。存在型有界量词 `∃̇∈` 以 `⊓` 代替 `⇒` 与之互为镜像。至此，语言的每个构造子都由同一不变量覆盖。
<!--ja-->
有界量化子は二つの動きを組み合わせます。`∀̇∈ t φ` では、走査は項 `t` を文脈の前の方で、本体の出現を越える `padRight` によって抽象化し、本体の配置は項の出現を越える `padLeft` との合成によって `suc` だけずらしました。したがってこの節は `cong₂ _⇒_` です。一方は項の補題によって `x` が抽象化された界に属することを、他方はずらした帰納によって `x ∷ γ` での再帰的主張を結びます。`leftHalf` と `rightHalf` が `h` を `constantsTm t` と `constantsFo φ` の間で分割します。存在形の有界量化子 `∃̇∈` は `⇒` の代わりに `⊓` を用いる鏡像です。これで言語のすべての構成子が同じ不変条件で扱われました。
<!--/-->

```agda
      (cong (x ∈ˢ_) (⟦⟧-place t (λ i → θ (padRight (countFo φ) i)) γ σ
        (leftHalf θ γ σ (constantsTm t) (constantsFo φ) h)))
      (⊨-place φ (λ j → suc (θ (padLeft (countTm t) j))) (x ∷ γ) σ
        (rightHalf (countTm t) θ γ σ (constantsTm t) (constantsFo φ) h))))
```

<!--en-->
The adequacy proper follows by choosing the placement the abstraction chose and the parameter environment the collection prescribes: the constants themselves, interpreted. Its hypothesis is then the two pad laws in sequence, and the theorem states exactly this. Satisfaction of the original at `γ` is satisfaction of the abstraction at `γ` extended by the collected constants.
<!--zh-->
名副其实的充分性随之而来：安置取抽象所取的那一个，参数环境取收集所规定的那一个，即诸常元自身经解释之后的样子。它的假设正是两条补位定律的延续，而定理的内容也一如所述：原公式在 `γ` 处的满足，就是抽象在「`γ` 被收集来的诸常元扩张之后」的满足。
<!--ja-->
妥当性そのものは、抽象化が選んだ配置と、収集が指定するパラメータ環境、すなわち解釈済みの定数そのものを選べば直ちに従います。仮定は二つの補埋め法則を順につなげたものになり、定理はまさにこの主張を述べます。元の論理式の `γ` での充足は、収集された定数で `γ` を拡張した後の抽象化の充足と一致します。
<!--/-->

<!--en-->
The main theorem instantiates the induction once. Since `absFo φ` was produced by the traversal at the placement `padLeft n`, that placement is the one to apply `⊨-place` at, and the parameter environment is chosen to be `map ι (constantsFo φ)`: the recorded constants, in order, each interpreted. The resulting theorem says that satisfaction of the original formula at `γ` is satisfaction of the abstraction at `γ` extended by these interpreted constants.
<!--zh-->
主定理把归纳实例化一次。由于 `absFo φ` 是在安置 `padLeft n` 处的遍历产生的，就该在那个安置处应用 `⊨-place`，而参数环境取为 `map ι (constantsFo φ)`：按次序排列的被记录常元，逐一经解释。所得定理说：原公式在 `γ` 处的满足，就是抽象在「`γ` 被这些经解释常元扩张之后」的满足。
<!--ja-->
主定理は帰納法を一度だけ具体化します。`absFo φ` は配置 `padLeft n` での走査によって作られたので、`⊨-place` はまさにその配置で用い、パラメータ環境は `map ι (constantsFo φ)`、すなわち記録された定数を順に解釈したものと取ります。得られる定理は次を述べています。元の論理式の `γ` での充足は、これらの解釈済み定数で `γ` を拡張した後の抽象化の充足と一致する。
<!--/-->

```agda
    ⊨-abs : ∀ {n} (φ : Formula K n) (γ : S ^ n)
          → (γ ⊨ φ) ≡ ((γ ++ map ι (constantsFo φ)) ⊨₀ absFo φ)
    ⊨-abs {n} φ γ = ⊨-place φ (padLeft n) γ (map ι (constantsFo φ)) hyp
      where
      hyp : ∀ j → lookup (padLeft n j) (γ ++ map ι (constantsFo φ))
```

<!--en-->
It remains to see that this choice of `σ` discharges the hypothesis. The placement `padLeft n` sends occurrence `j` to the entry `n + j`, which falls in the second half of the concatenation; `lookup-padLeft` identifies the entry with `lookup j (map ι (constantsFo φ))`, and `lookup-map` pulls the interpretation through, giving exactly `ι (lookup j (constantsFo φ))`. The two laws composed are the hypothesis, and with it `⊨-place` yields the theorem. Mathematically: a parameter-free formula together with a finite ordered vector of parameters has the same extension as the original formula with constants.
<!--zh-->
剩下的只是看到这一 `σ` 的选择如何清偿假设。安置 `padLeft n` 把出现 `j` 送到条目 `n + j`，它落在拼接的后半段；`lookup-padLeft` 把该条目等同于 `lookup j (map ι (constantsFo φ))`，`lookup-map` 再让解释穿过，恰得 `ι (lookup j (constantsFo φ))`。两条定律复合即为假设，有了它 `⊨-place` 便给出定理。数学上说：一条无参公式加上一个有限的有序参数向量，与原带常元公式具有相同的外延。
<!--ja-->
残るのは、この `σ` の選択が仮定を果たすことを見ることです。配置 `padLeft n` は出現 `j` を項 `n + j` へ送りますが、これは連結の後半に落ちます。`lookup-padLeft` がその項を `lookup j (map ι (constantsFo φ))` と同一視し、`lookup-map` が解釈を引き抜いて、ちょうど `ι (lookup j (constantsFo φ))` を与えます。二つの法則を合成したものが仮定であり、それを満たせば `⊨-place` が定理を与えます。数学的に言えば、パラメータを持たない論理式と有限で順序づけられたパラメータのベクトルの組は、定数付きの元の論理式と同じ外延を持ちます。
<!--/-->

```agda
                ≡ ι (lookup j (constantsFo φ))
      hyp j = lookup-padLeft n γ (map ι (constantsFo φ)) j
            ∙ lookup-map ι (constantsFo φ) j
```

<!--en-->
## What a definable subset is

Parameter abstraction isolates the data behind a definable subset: a parameter-free formula, its finite vector of parameters, and the variable at which membership is tested. Adequacy shows that this presentation has exactly the same extension as the original formula with constants.

One point of shape, and the reason the arity-one case is worth writing down: at arity one the extended environment is `x ∷ map ι p`, a single member followed by the parameters, which is the very shape a one-entry environment has everywhere else in the book.
<!--zh-->
## 何谓可定义子集

参数抽象把可定义子集背后的数据拆开列出：一条无参公式、一个有限参数向量，以及用于检验成员关系的变量。充分性表明，这种呈现与原带常元公式具有完全相同的外延。

还有一处形状，也是元数一的情形值得单写的理由：在元数一处，扩张后的环境是 `x ∷ map ι p`，一个成员后接诸参数，而那正是本书别处每一个单条目环境的形状。
<!--ja-->
## 定義可能な部分集合とは何か

パラメータ抽象は、定義可能な部分集合を与えるデータを分離します。すなわち、パラメータを持たない論理式、有限なパラメータベクトル、そして所属を判定する変数です。妥当性により、この提示は元の定数付き論理式とまったく同じ外延を持ちます。

ここには形状上の要点が一つあり、それがアリティ 1 の場合をわざわざ書き下す理由です。アリティ 1 では拡張後の環境は `x ∷ map ι p`、つまり一つの要素の後にパラメータが続く形になり、これは本書の他のどこでも一項環境が持つのと同じ形です。
<!--/-->

<!--en-->
For definable subsets of one variable, the corollary fixes the environment to `x ∷ []`: a formula of arity one is tested at the single member `x`, and the theorem gives the abstraction tested at `x` followed by the interpreted parameters. Because the statement is a path between propositions, the two readings of membership are interchangeable, and later chapters coding definable subsets may work with the parameter-free formula plus the parameter vector `map ι (constantsFo φ)` directly, without renaming constants or modifying the formula.
<!--zh-->
对一元可定义子集，这条推论把环境固定为 `x ∷ []`：元数为一的公式在唯一成员 `x` 处检验，定理给出抽象在 `x` 后接诸经解释参数处的检验。由于该陈述是命题之间的路径，两种对成员关系的读法可以互换；后续为可定义子集编码的章节可以直接使用无参公式加参数向量 `map ι (constantsFo φ)`，既无须重标常元，也无须改动公式。
<!--ja-->
一変数の定義可能な部分集合のために、この系は環境を `x ∷ []` と固定します。アリティ 1 の論理式はただ一つの要素 `x` で判定され、定理は `x` に解釈済みのパラメータを続けた環境での抽象化の判定を与えます。この主張は命題の間の道の等式なので、所属の二つの読み方は取り替えて使えます。定義可能な部分集合を符号化する後の章は、定数の改名も論理式の変更もせず、パラメータを持たない論理式とパラメータベクトル `map ι (constantsFo φ)` を直接扱って構いません。
<!--/-->

```agda
    ⊨-abs₁ : (φ : Formula K 1) (x : S)
           → ((x ∷ []) ⊨ φ) ≡ ((x ∷ map ι (constantsFo φ)) ⊨₀ absFo φ)
    ⊨-abs₁ φ x = ⊨-abs φ (x ∷ [])
```

<!--en-->
## Recap

`absFo` removes constants by adding one variable per occurrence, and `⊨-abs` identifies satisfaction after the recorded constants are appended to the environment. This is the finite parameter presentation used when formulas themselves must be coded.
<!--zh-->
## 小结

`absFo` 为每次常元出现增加一个变量以消去常元，`⊨-abs` 则在把记录的常元附加到环境后识别满足关系。这就是公式本身需要符号化时所用的有限参数呈现。
<!--ja-->
## まとめ

`absFo` は定数の出現ごとに変数を一つ加えて定数を除き、`⊨-abs` は記録した定数を環境へ付け加えた後の充足関係を同定します。これは論理式そのものを符号化するときに使う有限パラメータの提示です。
<!--/-->
