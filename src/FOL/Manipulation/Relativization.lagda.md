<!--en-->
# Relativization

Relativization replaces each unbounded quantifier by one bounded by a chosen constant. The transformed formula is Δ₀, and its ordinary satisfaction agrees with a semantics in which the original formula's unbounded quantifiers range only over members of the chosen set. The chapter builds three pieces in order: the rewriting operator itself, a witness that its output lies in the Δ₀ class of the Lévy hierarchy (see the chapter on that hierarchy for the definition of bounded formulas), and the correctness theorem identifying the meaning of the rewrite with bounded quantification over the chosen set. The setting is deliberately general: formulas may have constants from any type `K`, and the semantics may take values in the proposition universe `hProp ℓ` through a structure `𝒮`, so the theorem applies wherever a genuine ZF-like structure is later supplied.
<!--zh-->
# 相对化

相对化把每个无界量词替换为受选定常元约束的量词。变换后的公式是 Δ₀，并且其通常满足关系与一种语义相符；在该语义中，原公式的无界量词只在选定集合的成员上取值。本章依次构造三件东西：改写算子本身、说明其输出落在 Lévy 层级中 Δ₀ 类的见证 (有界公式的定义见该层级一章)，以及把改写结果的含义同选定集合上的有界量化相认同的正确性定理。论述保持一般性：公式可以带有任意类型 `K` 的常元，语义也可以通过结构 `𝒮` 取值于命题宇宙 `hProp ℓ`。
<!--ja-->
# 相対化

相対化は、各非有界量化子を選んだ定数で有界化します。変換後の論理式は Δ₀ であり、その通常の充足関係は、元の論理式の非有界量化子を選んだ集合の要素だけにわたらせる意味論と一致します。本章は三つの要素をこの順に構築します。すなわち、書き換え演算子そのもの、その出力が Lévy 階層の Δ₀ クラスに属することの証拠 (有界論理式の定義は階層の章を参照)、そして書き換えの意味を選んだ集合の上の有界量化と同一視する正当性定理です。議論は一般的に保たれています。論理式は任意の型 `K` の定数を持つことができ、意味論も構造 `𝒮` を通じて命題宇宙 `hProp ℓ` に値をとれます。
<!--/-->

<!--en-->
The setting: formulas may mention constants from an arbitrary type `K`, and satisfaction may take values in the proposition universe through a structure `𝒮`. Consider a formula with an unbounded quantifier, for example `∃̇ (x ∈̇ y)`, which asks for some element of the whole universe belonging to `y`. Given a constant `c`, relativization rewrites the quantifier by supplying it with the bound `con c`: the result is `∃̇∈ (con c) (x ∈̇ y)`, which asks only for a member of `y` that lies in whatever the constant `c` names. No other part of the formula changes. This rewriting is purely syntactic; whether the rewritten formula still expresses the original intention is a separate semantic question, taken up in the correctness section.
<!--zh-->
先看论域：公式可以带有来自任意类型 `K` 的常元，满足关系可以通过结构 `𝒮` 取值于命题宇宙 `hProp ℓ`。设一条公式含无界量词，例如 `∃̇ (x ∈̇ y)`，它问的是整个宇宙中是否有元素属于 `y`。给定常元 `c`，相对化改写这个量词的方式是为它补上界限 `con c`：结果为 `∃̇∈ (con c) (x ∈̇ y)`，它只问是否有属于 `y` 的元素同时落在常元 `c` 所指称者之中。公式的其余部分一概不变。这种改写纯粹是语法的；改写后的公式是否仍表达原意，是另一个语义问题，留待正确性一节处理。
<!--ja-->
舞台を整えます。論理式は任意の型 `K` の定数を含むことができ、充足関係は構造 `𝒮` を通じて命題宇宙 `hProp ℓ` に値をとれます。非有界量化子を含む論理式、たとえば `∃̇ (x ∈̇ y)` を考えてください。これは宇宙全体の中に `y` に属する要素があるかと問います。定数 `c` が与えられると、相対化はこの量化子に境界 `con c` を補って書き換えます。結果は `∃̇∈ (con c) (x ∈̇ y)` であり、`y` に属する要素のうち、定数 `c` の指すものに属するものがあるかだけを問います。論理式の他の部分はまったく変わりません。この書き換えは純粋に構文的なものです。書き換え後の論理式が依然として本来の意図を表すかどうかは別の意味論的な問題であり、正当性の節で扱います。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

module FOL.Manipulation.Relativization where

open import Base.Prelude
open import FOL.ZFStructure using ( ZFStructure )
```

<!--en-->
Rewriting one unbounded quantifier at one spot is easy; the task here is to do it uniformly at every depth of every formula, and to keep the bookkeeping afterward. The chapter's three pieces answer three questions. First, the operator `relativize c` performs the replacement itself, leaving already bounded quantifiers and their bounds untouched. Second, a witness `Δ₀-relativize` certifies that the output lies in the Δ₀ class of the Lévy hierarchy, that is, every quantifier occurring in it is bounded (the definition of bounded formulas is given in the chapter on that hierarchy). Third, the theorem `relativize-correct` connects the two readings: under any interpretation of the constants, the ordinary satisfaction of the rewritten formula agrees with a reading of the original one in which its unbounded quantifiers range only over the set named by `c`.
<!--zh-->
在单个位置把一个无界量词改写成有界量词并不难；这里的任务是在每条公式的任意深度上统一完成改写，并在事后保持记账。本章的三件东西分别回答三个问题。其一，算子 `relativize c` 执行替换本身，不触动已有的有界量词及其界限。其二，见证 `Δ₀-relativize` 证明输出落在 Lévy 层级的 Δ₀ 类中，即其中出现的每个量词都有界 (有界公式的定义见该层级一章)。其三，定理 `relativize-correct` 连接两种读法：在常元的任意解释下，改写后公式的通常满足关系，与原公式的一种读法一致，其中无界量词只在 `c` 所指称的集合上取值。
<!--ja-->
一箇所で一つの非有界量化子を書き換えるのは容易です。ここでの課題は、すべての論理式の任意の深さでこれを統一的に行い、後の管理も保つことです。本章の三つの要素は三つの問いに答えます。第一に、演算子 `relativize c` が置き換えそのものを行い、既に有界な量化子とその境界には触れません。第二に、証拠 `Δ₀-relativize` は出力が Lévy 階層の Δ₀ クラスに属すること、すなわちそこに現れる量化子がすべて有界であることを保証します (有界論理式の定義は階層の章にあります)。第三に、定理 `relativize-correct` が二つの読みを結びます。定数の任意の解釈のもとで、書き換え後の論理式の通常の充足は、元の論理式の非有界量化子を `c` の指す集合だけにわたらせる読みと一致します。
<!--/-->

```agda
open import FOL.Syntax using
  ( con; Formula; _∈̇_; _≐_; _∧̇_; _∨̇_; _⇒̇_; ⊥̇; ∃̇_; ∀̇_; ∀̇∈; ∃̇∈ )
open import FOL.LevyHierarchy using
  ( Δ₀; δ-∈; δ-≐; δ-∧; δ-∨; δ-⇒; δ-⊥; δ-∀∈; δ-∃∈ )
import FOL.Semantics
```

<!--en-->
## The operator

`relativize c` leaves atoms and already bounded quantifiers unchanged, while replacing `∃̇` and `∀̇` by quantifiers bounded by `con c`. Because the bound is a constant, it passes beneath binders without any variable shifting. The definition is a plain recursion on the ten formula constructors, and its fixed point is a syntactic invariant worth stating before reading the code: after relativization, every quantifier in the result is bounded, and the only bounds introduced are occurrences of `con c` itself.
<!--zh-->
## 算子

`relativize c` 保持原子公式与已有的有界量词不变，同时把 `∃̇` 和 `∀̇` 替换为受 `con c` 约束的量词。由于界是常元，进入约束子时无须随变量移动而调整。定义是对十个公式构造子的简单递归，读代码之前值得先陈述它的不动点这一语法不变量：相对化之后，结果中的每个量词都有界，而且引入的界限只有 `con c` 本身的出现。
<!--ja-->
## 演算子

`relativize c` は原子論理式と既に有界な量化子を変えず、`∃̇` と `∀̇` を `con c` で有界な量化子へ置き換えます。境界は定数なので、変数をずらさずに束縛子の下へ入れます。定義は 10 個の論理式構成子に対する単純な再帰であり、コードを読む前に不動点となる構文的不変量を述べておく価値があります。相対化の後は、結果のすべての量化子が有界であり、導入される境界は `con c` の出現だけだということです。
<!--/-->

<!--en-->
The signature fixes the data: a constant `c` drawn from any type `K` of constant symbols, and a formula `φ` of arity `n`, returning another formula of the same arity. The clauses for the atoms and the three binary connectives, and for falsity, do no rewriting at all; they only recurse into subformulas, preserving the connective structure. Relativization is thus depth-preserving: the only structural change it can make is at quantifier nodes.
<!--zh-->
签名固定了数据：从任意常元符号类型 `K` 取一个常元 `c`，以及一条元数为 `n` 的公式 `φ`，返回另一条同元数的公式。原子式、三个二元联结词以及伪式的子句根本不做改写，只是递归进入子公式并保持联结词结构。因此相对化保持深度：它唯一可能的结构改动只发生在量词节点。
<!--ja-->
シグニチャはデータを固定します。任意の定数記号の型 `K` から定数 `c` を一つと、アリティ `n` の論理式 `φ` を取り、同じアリティの別の論理式を返します。原子式、三つの二項結合子、そして偽に対する節はまったく書き換えを行わず、部分論理式に再帰して結合子の構造を保つだけです。したがって相対化は深さを保ち、構造的に変更しうるのは量化子の節だけです。
<!--/-->

```agda
relativize : ∀ {ℓ} {K : Type ℓ} (c : K) {n} → Formula K n → Formula K n
relativize c (t ∈̇ u)  = t ∈̇ u
relativize c (t ≐ u)  = t ≐ u
relativize c (φ ∧̇ ψ)  = relativize c φ ∧̇ relativize c ψ
relativize c (φ ∨̇ ψ)  = relativize c φ ∨̇ relativize c ψ
```

<!--en-->
The two unbounded clauses carry the whole point. `∃̇ φ` becomes `∃̇∈ (con c) φ′` and `∀̇ φ` becomes `∀̇∈ (con c) φ′`, where `φ′` is the relativization of the body: the quantifier now ranges only over elements of the constant `con c`. The two already bounded clauses keep their original bound term `t` untouched, precisely because it already restricts the quantifier; only the body is relativized. Note that the bound `con c` is a term, not a variable, so extending the environment with a freshly bound value never disturbs it: no de Bruijn style reindexing is needed anywhere in the transformation.
<!--zh-->
两条无界子句承载了整个要点。`∃̇ φ` 变为 `∃̇∈ (con c) φ′`，`∀̇ φ` 变为 `∀̇∈ (con c) φ′`，其中 `φ′` 是主体的相对化：量词现在只在常元 `con c` 的元素上取值。两条本就有界的子句保持原界限词项 `t` 不动，正因为它已经约束了量词；只有主体被相对化。注意界限 `con c` 是词项而非变量，所以用新绑定值扩展环境时它不受任何干扰：整个变换无须任何 de Bruijn 式的重编号。
<!--ja-->
非有界な二つの節が要点すべてを担います。`∃̇ φ` は `∃̇∈ (con c) φ′` へ、`∀̇ φ` は `∀̇∈ (con c) φ′` へ変わります。ここで `φ′` は本体の相対化であり、量化子は今や定数 `con c` の要素の上だけをわたります。既に有界な二つの節は、元の境界の項 `t` をそのまま保ちます。それはすでに量化子を制限しているからで、相対化されるのは本体だけです。境界の `con c` は変数ではなく項なので、新しく束縛した値で環境を拡張してもまったく乱されません。変換のどこでも de Bruijn 流の再索引付けは不要です。
<!--/-->

```agda
relativize c (φ ⇒̇ ψ)  = relativize c φ ⇒̇ relativize c ψ
relativize c ⊥̇        = ⊥̇
relativize c (∃̇ φ)    = ∃̇∈ (con c) (relativize c φ)
relativize c (∀̇ φ)    = ∀̇∈ (con c) (relativize c φ)
relativize c (∀̇∈ t φ) = ∀̇∈ t (relativize c φ)
```

<!--en-->
This completes the case analysis: all ten constructors are covered, and the recursion is structural on the input formula, so `relativize c φ` is defined for every formula. Because the two bounded clauses merely recurse, the bounded quantifiers originally present in φ survive with their own bounds, and the new bounds are exactly the relativized images of the unbounded ones.
<!--zh-->
至此分情形完毕：十个构造子全部覆盖，递归对输入公式是结构性的，所以 `relativize c φ` 对每条公式都有定义。由于两条有界子句只是递归，φ 中原有的有界量词带着自己的界限存活下来，而新界限恰好是无界量词的相对化像。
<!--ja-->
これで場合分けが完了します。10 個の構成子がすべて扱われ、再帰は入力の論理式に対して構造的であるため、`relativize c φ` はすべての論理式に対して定義されます。有界な二つの節は単に再帰するだけなので、φ に元からあった有界量化子は自分の境界を持ったまま残り、新たな境界は非有界量化子の相対化による像そのものです。
<!--/-->

```agda
relativize c (∃̇∈ t φ) = ∃̇∈ t (relativize c φ)
```

<!--en-->
Every unbounded quantifier became bounded and nothing else changed, so the result has no `∃̇` or `∀̇` constructors at all. In the terminology of the Lévy hierarchy chapter, that is exactly what it means to be Δ₀: the inductive family `Δ₀` has one constructor per permitted shape, and none for the unbounded quantifiers. The function `Δ₀-relativize` assembles such a witness by recursion on φ, one line per constructor.
<!--zh-->
每个无界量词都变为有界量词，其余部分保持不变，因此结果不含任何 `∃̇` 或 `∀̇` 构造子。用 Lévy 层级一章的术语说，这正是 Δ₀ 的含义：归纳族 `Δ₀` 对每个获准形状有一个构造子，而对无界量词没有。函数 `Δ₀-relativize` 对 φ 递归地装配这样的见证，每个构造子一行。
<!--ja-->
非有界量化子はすべて有界化され、他は何も変わらないため、結果には `∃̇` や `∀̇` の構成子がまったく現れません。Lévy 階層の章の用語で言えば、それこそが Δ₀ であることの意味です。帰納的族 `Δ₀` は許容される形ごとに一つの構成子を持ち、非有界量化子には何も持ちません。関数 `Δ₀-relativize` は φ に対する再帰でそのような証拠を組み立て、構成子ごとに一行を要します。
<!--/-->

<!--en-->
The statement quantifies over all formulas φ and produces `Δ₀ (relativize c φ)`, a witness in the inductive family, not a Boolean flag. For atoms, the witnesses `δ-∈` and `δ-≐` are given outright: an atomic formula has no quantifiers, so membership in Δ₀ is immediate. The connective clauses combine witnesses with `δ-∧`, `δ-∨` and `δ-⇒`, mirroring the closure rules of the class under its binary operations.
<!--zh-->
陈述对所有公式 φ 量化，产出的是归纳族中的见证 `Δ₀ (relativize c φ)`，而非布尔标记。对原子式，见证 `δ-∈` 与 `δ-≐` 直接给出：原子公式不含任何量词，故属于 Δ₀ 是直接的。联结词子句用 `δ-∧`、`δ-∨` 与 `δ-⇒` 组合见证，对应于该类在二元运算下的封闭规则。
<!--ja-->
この命題はすべての論理式 φ に対して量化し、ブール値のフラグではなく帰納的族の中の証拠 `Δ₀ (relativize c φ)` を作ります。原子式に対しては、証拠 `δ-∈` と `δ-≐` がそのまま与えられます。原子論理式は量化子をまったく含まないため、Δ₀ への所属は直ちに得られます。結合子の節は `δ-∧`、`δ-∨`、`δ-⇒` で証拠を組み合わせ、二項演算の下でのこのクラスの閉性の規則を写しています。
<!--/-->

```agda
Δ₀-relativize : ∀ {ℓ} {K : Type ℓ} (c : K) {n} (φ : Formula K n) → Δ₀ (relativize c φ)
Δ₀-relativize c (t ∈̇ u)  = δ-∈
Δ₀-relativize c (t ≐ u)  = δ-≐
Δ₀-relativize c (φ ∧̇ ψ)  = δ-∧ (Δ₀-relativize c φ) (Δ₀-relativize c ψ)
Δ₀-relativize c (φ ∨̇ ψ)  = δ-∨ (Δ₀-relativize c φ) (Δ₀-relativize c ψ)
```

<!--en-->
Falsity carries no quantifier, so `δ-⊥` suffices. The decisive rows are again the quantifiers: where `relativize` changed an unbounded quantifier into a bounded one, `Δ₀-relativize` applies `δ-∃∈` or `δ-∀∈`, the constructors reserved for bounded quantification, to the witness for the relativized body. A bounded quantifier of the original formula gets the same treatment on its own body. In every case the inductive hypothesis supplies the witness for the subformula, and the constructor lifts it through the surrounding connective or quantifier.
<!--zh-->
伪式不含任何量词，故 `δ-⊥` 即可。决定性的行再次是量词：凡 `relativize` 把无界量词变为有界量词之处，`Δ₀-relativize` 便对相对化主体的见证应用为有界量化保留的构造子 `δ-∃∈` 或 `δ-∀∈`。原公式中的有界量词也对自己的主体得到同样处理。每种情形里，归纳假设给出子公式的见证，构造子再把它穿过外围的联结词或量词提升上来。
<!--ja-->
偽は量化子を含まないため `δ-⊥` で足ります。決定的な行はここでも量化子です。`relativize` が非有界量化子を有界化した箇所では、`Δ₀-relativize` は相対化された本体への証拠に対し、有界量化のために用意された構成子 `δ-∃∈` か `δ-∀∈` を適用します。元の論理式の有界量化子も、自分の本体に対して同じ扱いを受けます。いずれの場合も帰納法の仮定が部分論理式の証拠を与え、構成子がそれを外側の結合子や量化子を通して持ち上げます。
<!--/-->

```agda
Δ₀-relativize c (φ ⇒̇ ψ)  = δ-⇒ (Δ₀-relativize c φ) (Δ₀-relativize c ψ)
Δ₀-relativize c ⊥̇        = δ-⊥
Δ₀-relativize c (∃̇ φ)    = δ-∃∈ (Δ₀-relativize c φ)
Δ₀-relativize c (∀̇ φ)    = δ-∀∈ (Δ₀-relativize c φ)
Δ₀-relativize c (∀̇∈ t φ) = δ-∀∈ (Δ₀-relativize c φ)
```

<!--en-->
All ten cases are now covered, and the recursion on φ guarantees the witness exists for every input. This is the syntactic half of the chapter's promise: relativized formulas are not merely intuitively bounded, they carry an explicit Δ₀ certificate that later absoluteness and definability arguments can consume directly.
<!--zh-->
十个情形至此全部覆盖，对 φ 的递归保证每条输入都有见证。这是本章承诺的语法部分：相对化后的公式不只是直观上有界，它们携带显式的 Δ₀ 证书，可供日后的绝对性与可定义性论证直接使用。
<!--ja-->
10 個のケースがすべて扱われ、φ に対する再帰によりすべての入力に証拠が存在することが保証されます。これが本章の約束の構文的な半分です。相対化された論理式は直観的に有界というだけでなく、後の絶対性や定義可能性の議論が直接消費できる明示的な Δ₀ の証拠を帯同します。
<!--/-->

```agda
Δ₀-relativize c (∃̇∈ t φ) = δ-∃∈ (Δ₀-relativize c φ)
```

<!--en-->
## Correctness

The comparison semantics interprets the original formula while restricting only its unbounded quantifiers to the value of the chosen bound. Structural induction shows that this is exactly the ordinary semantics of the relativized formula. Two semantics are therefore in play: the standard one `γ ⊨ _` from `FOL.Semantics`, and the auxiliary relation `γ ⊨ᴬ _` defined here, which agrees with the standard one at every connective, atom, and bounded quantifier, and differs only at `∃̇` and `∀̇`, where it adds the condition that the bound variable lies in the chosen set. The theorem to prove is the path `(γ ⊨ relativize c φ) ≡ (γ ⊨ᴬ φ)`, so the two relations must land in a type with an identity type; this is why the module is parameterized by a proposition-valued structure `𝒮` and a constant interpretation `ι`.
<!--zh-->
## 正确性

比较语义解释原公式，但只把其中的无界量词限制到所选界的取值。结构归纳表明，这恰好是相对化公式的通常语义。因此这里同时有两个语义：来自 `FOL.Semantics` 的标准语义 `γ ⊨ _`，以及这里定义的辅助关系 `γ ⊨ᴬ _`；后者在每个联结词、原子式和有界量词处与标准语义一致，只在 `∃̇` 与 `∀̇` 处不同，它附加了约束变元属于选定集合的条件。要证的定理是路径 `(γ ⊨ relativize c φ) ≡ (γ ⊨ᴬ φ)`，所以两个关系必须落在有同一类型的类型中；这正是模块以命题值结构 `𝒮` 与常元解释 `ι` 为参数的原因。
<!--ja-->
## 正当性

比較用の意味論は元の論理式を解釈し、非有界量化子だけを選んだ境界の値へ制限します。構造帰納法により、これは相対化した論理式の通常の意味論とちょうど一致します。ここには二つの意味論が登場します。`FOL.Semantics` からの標準的な `γ ⊨ _` と、ここで定義する補助関係 `γ ⊨ᴬ _` です。後者はすべての結合子、原子式、有界量化子で標準のものと一致し、`∃̇` と `∀̇` でのみ異なり、束縛変数が選んだ集合に属するという条件を付け加えます。証明すべき定理はパス `(γ ⊨ relativize c φ) ≡ (γ ⊨ᴬ φ)` なので、二つの関係は同一性の型をもつ型に値をとらねばなりません。これが、モジュールが命題値の構造 `𝒮` と定数の解釈 `ι` をパラメータとする理由です。
<!--/-->

<!--en-->
To compare the two readings, fix a proposition-valued ZF structure `𝒮` with domain `S`, an interpretation `ι` assigning each constant symbol a carrier element, and a distinguished constant `c`. The standard semantics `γ ⊨ _` and term evaluation `⟦_⟧` come from `FOL.Semantics`, for the given `ι`. To these data the section adds a companion relation `γ ⊨ᴬ _`, which interprets the original formula exactly as the standard semantics does, except that its unbounded quantifiers are restricted to a single carrier element `A`, the denotation `ι c` of the chosen constant. At atoms, connectives, falsity, and bounded quantifiers the companion is meant to agree with the standard semantics; it differs only where unbounded quantification is replaced by quantification inside `A`. The argument uses the proposition-valued relations of `𝒮` directly.
<!--zh-->
为了比较两种读法，固定一个论域为 `S` 的命题值 ZF 结构 `𝒮`、给每个常元符号指派载体元素的解释 `ι`，以及特选常元 `c`。标准语义 `γ ⊨ _` 与词项求值 `⟦_⟧` 来自 `FOL.Semantics`，针对给定的 `ι`。本节在这些数据之上添加一个伴随关系 `γ ⊨ᴬ _`：它按标准语义解释原公式，只是把其中的无界量词限制到单个载体元素 `A`，即所选常元的指称 `ι c`。在原子式、联结词、伪式与有界量词处，伴随关系应与标准语义一致；它只在无界量化被换成 `A` 内部量化之处不同。论证直接使用 `𝒮` 的命题值关系。
<!--ja-->
二つの読みを比較するために、台 `S` をもつ命題値の ZF 構造 `𝒮`、各定数記号に台の要素を割り当てる解釈 `ι`、そして注目の定数 `c` を固定します。標準の意味論 `γ ⊨ _` と項の評価 `⟦_⟧` は、与えられた `ι` に対して `FOL.Semantics` から得られます。この節はこれらのデータに伴う関係 `γ ⊨ᴬ _` を加えます。これは元の論理式を標準の意味論どおりに解釈しますが、非有界量化子だけを一つの台の要素 `A`、すなわち選んだ定数の表示 `ι c` に制限します。原子式、結合子、偽、有界量化子では伴う関係は標準の意味論と一致するはずであり、異なるのは無界量化が `A` の内部での量化に置き換わる箇所だけです。議論は `𝒮` の命題値関係を直接用います。
<!--/-->

```agda
module Correct {ℓ} (𝒮 : ZFStructure ℓ)
               {ℓc} {K : Type ℓc} (ι : K → ZFStructure.S 𝒮) (c : K) where

  open ZFStructure 𝒮
  open module Sem = FOL.Semantics 𝒮 using ( module At; _^_ )
```

<!--en-->
The bound is named once and for all: `A = ι c`, the carrier element denoted by the chosen constant. The relation `γ ⊨ᴬ φ` takes an environment `γ : S ^ n` and a formula `φ` of the same arity `n`, and returns a proposition in `hProp ℓ`, just as the standard satisfaction does. The superscript ᴬ records that quantifiers are relativized to `A`; the clauses follow, and only the unbounded quantifier clauses will differ from the standard ones.
<!--zh-->
界限被一次性命名：`A = ι c`，即所选常元指称的载体元素。关系 `γ ⊨ᴬ φ` 取环境 `γ : S ^ n` 与同元数 `n` 的公式 `φ`，返回命题宇宙 `hProp ℓ` 中的命题，与标准满足关系一样。上标 ᴬ 记录量词被相对化到 `A`；下面给出各子句，其中只有无界量词子句与标准者不同。
<!--ja-->
境界は一度だけ名付けられます。`A = ι c`、すなわち選んだ定数が表示する台の要素です。関係 `γ ⊨ᴬ φ` は環境 `γ : S ^ n` と同じアリティ `n` の論理式 `φ` を取り、標準の充足と同様に命題宇宙 `hProp ℓ` の命題を返します。上付きの ᴬ は量化子が `A` に相対化されていることを示します。続く節のうち、標準と異なるのは非有界量化子の節だけです。
<!--/-->

```agda
  open At K ι using ( _⊨_; ⟦_⟧ )

  A : S
  A = ι c

  infix 6 _⊨ᴬ_
  _⊨ᴬ_ : ∀ {n} → S ^ n → Formula K n → hProp ℓ
```

<!--en-->
The first five clauses copy the standard semantics verbatim: atoms become the structure's proposition-valued membership and equality applied to the denotations `⟦ t ⟧ γ` and `⟦ u ⟧ γ`, connectives become the logical operations `⊓`, `⊔`, `⇒`, and falsity becomes `⊥`. This is deliberate: at these shapes there is nothing to relativize, and making the clauses definitionally identical to the standard ones is what will let the corresponding correctness cases be proved by `refl`. The recursion is again structural, so `⊨ᴬ` is total.
<!--zh-->
前五条子句逐字复制标准语义：原子式成为结构的命题值成员关系与等词，作用于指称 `⟦ t ⟧ γ` 与 `⟦ u ⟧ γ`；联结词成为逻辑运算 `⊓`、`⊔`、`⇒`；伪式成为 `⊥`。这是有意的：在这些形状上没有可相对化之物，而让这些子句与标准子句定义性地相同，正是相应正确性情形能由 `refl` 证明的原因。递归同样是结构性的，故 `⊨ᴬ` 是全函数。
<!--ja-->
最初の五つの節は標準の意味論をそのまま写します。原子式は、指示 `⟦ t ⟧ γ` と `⟦ u ⟧ γ` に対する構造の命題値をとる所属と等号になり、結合子は論理演算 `⊓`、`⊔`、`⇒` になり、偽は `⊥` になります。これは意図的です。これらの形では相対化すべきものがなく、これらの節を標準のものと定義的に同一にしておくことが、対応する正当性のケースを `refl` で証明できる理由になります。再帰はここでも構造的であり、`⊨ᴬ` は全関数です。
<!--/-->

```agda
  γ ⊨ᴬ (t ∈̇ u)  = ⟦ t ⟧ γ ∈ˢ ⟦ u ⟧ γ
  γ ⊨ᴬ (t ≐ u)  = ⟦ t ⟧ γ ≈ˢ ⟦ u ⟧ γ
  γ ⊨ᴬ (φ ∧̇ ψ)  = (γ ⊨ᴬ φ) ⊓ (γ ⊨ᴬ ψ)
  γ ⊨ᴬ (φ ∨̇ ψ)  = (γ ⊨ᴬ φ) ⊔ (γ ⊨ᴬ ψ)
  γ ⊨ᴬ (φ ⇒̇ ψ)  = (γ ⊨ᴬ φ) ⇒ (γ ⊨ᴬ ψ)
```

<!--en-->
The quantifier clauses are where the two semantics differ. For the unbounded existential, `γ ⊨ᴬ (∃̇ φ)` is the indexed join `⋁ S (λ x → (x ∈ˢ A) ⊓ ((x ∷ γ) ⊨ᴬ φ))`: it ranges over all carrier elements x and conjoins the proposition-valued guard `x ∈ˢ A`. Dually, the unbounded universal uses `⋀` with the implication guard `x ∈ˢ A ⇒ _`. The bounded clauses already restrict their quantifier to a term, evaluated in the original environment `γ`; their guards use `⟦ t ⟧ γ` rather than `A`, and otherwise match the standard reading exactly.
<!--zh-->
量词子句是两种语义分岔之处。无界存在量词的 `γ ⊨ᴬ (∃̇ φ)` 是带下标的并 `⋁ S (λ x → (x ∈ˢ A) ⊓ ((x ∷ γ) ⊨ᴬ φ))`：它遍历所有载体元素 x，并合取命题卫式 `x ∈ˢ A`。对偶地，无界全称量词用 `⋀` 配蕴涵卫式 `x ∈ˢ A ⇒ _`。有界子句本就把量词限制到一个词项，该词项在原环境 `γ` 中求值；其卫式用的是 `⟦ t ⟧ γ` 而非 `A`，其余与标准读法完全一致。这里仅陈述定义所用的运算；抽象命题运算并未假设使卫式成为二值判定的定律。
<!--ja-->
量化子の節が二つの意味論が分かれる場所です。非有界な存在量化子に対する `γ ⊨ᴬ (∃̇ φ)` は、添字付きの結合 `⋁ S (λ x → (x ∈ˢ A) ⊓ ((x ∷ γ) ⊨ᴬ φ))` です。すべての台の要素 x をわたり、命題であるガード `x ∈ˢ A` を連言します。双対に、非有界な全称量化子は含意のガード `x ∈ˢ A ⇒ _` を伴う `⋀` を使います。有界な節はもともと量化子を項に制限しており、その項は元の環境 `γ` で評価されます。ガードは `A` ではなく `⟦ t ⟧ γ` を用い、それ以外は標準の読みと正確に一致します。ここでは定義に現れる演算だけを述べています。抽象的な命題演算は、ガードを二値判定にする法則を仮定していません。
<!--/-->

```agda
  γ ⊨ᴬ ⊥̇        = ⊥
  γ ⊨ᴬ (∃̇ φ)    = ⋁ S (λ x → (x ∈ˢ A) ⊓ ((x ∷ γ) ⊨ᴬ φ))
  γ ⊨ᴬ (∀̇ φ)    = ⋀ S (λ x → (x ∈ˢ A) ⇒ ((x ∷ γ) ⊨ᴬ φ))
  γ ⊨ᴬ (∀̇∈ t φ) = ⋀ S (λ x → (x ∈ˢ ⟦ t ⟧ γ) ⇒ ((x ∷ γ) ⊨ᴬ φ))
  γ ⊨ᴬ (∃̇∈ t φ) = ⋁ S (λ x → (x ∈ˢ ⟦ t ⟧ γ) ⊓ ((x ∷ γ) ⊨ᴬ φ))
```

<!--en-->
Correctness is then one structural induction: the standard meaning of `relativize c φ` equals the `A`-bounded meaning of `φ`. The atoms are `refl`; the two clauses the operator actually changes are exactly where the standard semantics of `∃̇∈ (con c) _` unfolds, by computation, to the companion's clause, since `⟦ con c ⟧ γ` is `A`; everything else is congruence. The conclusion is a path in the proposition universe `hProp ℓ`, not a mere iff, so the two propositions are identified outright and can be transported along in later arguments.
<!--zh-->
正确性由结构归纳证明：`relativize c φ` 的标准含义等于 `φ` 的 `A`-有界含义。原子情形是 `refl`；算子实际改动的两个量词子句，正是标准语义按计算把 `∃̇∈ (con c) _` 展开为相应子句之处，因为 `⟦ con c ⟧ γ` 就是 `A`；其余情形都是同余。结论是命题宇宙 `hProp ℓ` 中的路径，而不仅仅是当且仅当，所以两个命题被直接同一，可在日后的论证中沿其传输。
<!--ja-->
正当性は一つの構造帰納法で示されます。`relativize c φ` の標準的な意味は、`φ` の `A`-有界な意味と等しいのです。原子式のケースは `refl` であり、演算子が実際に変更する二つの量化子の節は、`⟦ con c ⟧ γ` が `A` であるため、`∃̇∈ (con c) _` の標準的な意味論が対応する節へと計算によって展開される箇所そのものです。残りはすべて合同性です。結論は単なる同値でなく命題宇宙 `hProp ℓ` の中のパスなので、二つの命題はそのまま同一視され、後の議論でそれに沿って輸送できます。
<!--/-->

<!--en-->
The statement quantifies over both the formula φ and the environment γ, and asserts a path in the proposition universe `hProp ℓ`. Because `relativize c` left atoms untouched, the left side `γ ⊨ (t ∈̇ u)` computes to exactly the proposition `⟦ t ⟧ γ ∈ˢ ⟦ u ⟧ γ`, which is what `γ ⊨ᴬ (t ∈̇ u)` is by definition; the same holds for equality and falsity, so those cases are proved by `refl`, meaning definitional equality, with no further step. The connective cases use `cong₂` applied to the corresponding logical operation: since the subresults agree, the combined propositions agree.
<!--zh-->
陈述同时对公式 φ 与环境 γ 量化，并断言命题宇宙 `hProp ℓ` 中的路径。由于 `relativize c` 未动原子式，左边 `γ ⊨ (t ∈̇ u)` 计算到恰为 `⟦ t ⟧ γ ∈ˢ ⟦ u ⟧ γ` 的命题，而这正是 `γ ⊨ᴬ (t ∈̇ u)` 的定义；等词与伪式同理，故这些情形由 `refl` 证明，即定义性等价，无须进一步步骤。联结词情形对相应的逻辑运算使用 `cong₂`：既然子结果一致，组合后的命题也一致。
<!--ja-->
この命題は論理式 φ と環境 γ の両方に対して量化し、命題宇宙 `hProp ℓ` の中のパスを主張します。`relativize c` が原子式を触っていないため、左辺 `γ ⊨ (t ∈̇ u)` はちょうど命題 `⟦ t ⟧ γ ∈ˢ ⟦ u ⟧ γ` に計算され、これは定義上 `γ ⊨ᴬ (t ∈̇ u)` そのものです。等号と偽も同様なので、これらのケースは追加の段階なしに、定義的等価を意味する `refl` で証明されます。結合子のケースは対応する論理演算に `cong₂` を適用します。部分の結果が一致するので、結合された命題も一致します。
<!--/-->

```agda
  relativize-correct : ∀ {n} (φ : Formula K n) (γ : S ^ n)
                     → (γ ⊨ relativize c φ) ≡ (γ ⊨ᴬ φ)
  relativize-correct (t ∈̇ u)  γ = refl
  relativize-correct (t ≐ u)  γ = refl
  relativize-correct (φ ∧̇ ψ)  γ = cong₂ _⊓_ (relativize-correct φ γ) (relativize-correct ψ γ)
```

<!--en-->
The existential case is the crux. On the left, `relativize c (∃̇ φ)` is `∃̇∈ (con c) φ′`, and the standard semantics of a bounded existential is `⋁ S (λ x → (x ∈ˢ ⟦ con c ⟧ γ) ⊓ ((x ∷ γ) ⊨ φ′))`. But `⟦ con c ⟧ γ` computes to `A = ι c`, so this expression is definitionally the ᴬ-clause for `∃̇ φ`, once the inner satisfaction `⊨ φ′` is replaced by `⊨ᴬ φ` using the induction hypothesis at the extended environment `x ∷ γ`. Formally, `funExt` converts the pointwise agreement over every x into agreement of the indexed families, `cong` transports it through the guard `x ∈ˢ A ⊓ _`, and the outer `cong (⋁ S)` lifts the agreement of families to agreement of their joins. The universal case is the dual with `⋀` and `⇒`.
<!--zh-->
存在情形是关键。左边 `relativize c (∃̇ φ)` 是 `∃̇∈ (con c) φ′`，有界存在的标准语义是 `⋁ S (λ x → (x ∈ˢ ⟦ con c ⟧ γ) ⊓ ((x ∷ γ) ⊨ φ′))`。但 `⟦ con c ⟧ γ` 计算到 `A = ι c`，于是一旦用扩展环境 `x ∷ γ` 处的归纳假设把内部的 `⊨ φ′` 换成 `⊨ᴬ φ`，该表达式就定义性地成为 `∃̇ φ` 的 ᴬ 子句。形式上，`funExt` 把对每个 x 的逐点一致转为两个下标族的一致，`cong` 把它穿过卫式 `x ∈ˢ A ⊓ _` 传输，外层 `cong (⋁ S)` 再把族的一致提升为并的一致。全称情形是取 `⋀` 与 `⇒` 的对偶版本。
<!--ja-->
存在量化のケースが核心です。左辺の `relativize c (∃̇ φ)` は `∃̇∈ (con c) φ′` であり、有界な存在量化の標準的意味論は `⋁ S (λ x → (x ∈ˢ ⟦ con c ⟧ γ) ⊓ ((x ∷ γ) ⊨ φ′))` です。しかし `⟦ con c ⟧ γ` は `A = ι c` に計算されるため、拡張環境 `x ∷ γ` での帰納法の仮定により内部の `⊨ φ′` を `⊨ᴬ φ` に置き換えると、この式は定義的に `∃̇ φ` の ᴬ 節になります。形式的には、`funExt` がすべての x にわたる各点ごとの一致を添字族の一致に変え、`cong` がそれをガード `x ∈ˢ A ⊓ _` を通して輸送し、外側の `cong (⋁ S)` が族の一致をその結合の一致へ持ち上げます。全称量化のケースは `⋀` と `⇒` を用いた双対です。
<!--/-->

```agda
  relativize-correct (φ ∨̇ ψ)  γ = cong₂ _⊔_ (relativize-correct φ γ) (relativize-correct ψ γ)
  relativize-correct (φ ⇒̇ ψ)  γ = cong₂ _⇒_ (relativize-correct φ γ) (relativize-correct ψ γ)
  relativize-correct ⊥̇        γ = refl
  relativize-correct (∃̇ φ)    γ = cong (⋁ S) (funExt (λ x →
    cong (λ q → (x ∈ˢ A) ⊓ q) (relativize-correct φ (x ∷ γ))))
```

<!--en-->
The two already bounded clauses mirror the previous pair. Here `relativize c` kept the original bound term `t`, and `⊨ᴬ` also guards the quantifier by `⟦ t ⟧ γ`, so the guard never changes; only the body's satisfaction must be converted via the induction hypothesis at `x ∷ γ`, and the same `funExt`, inner `cong`, and outer `cong (⋁ S)` or `cong (⋀ S)` pattern applies. Note that the bound term is still evaluated in the original environment γ, matching the standard semantics of bounded quantification exactly.
<!--zh-->
两条本就有界的子句与上一对互为镜像。这里 `relativize c` 保留了原界限词项 `t`，而 `⊨ᴬ` 也用 `⟦ t ⟧ γ` 为量词加卫，所以卫式从不改变；只需通过 `x ∷ γ` 处的归纳假设转换主体的满足关系，同样的 `funExt`、内层 `cong` 与外层 `cong (⋁ S)` 或 `cong (⋀ S)` 模式即可套用。注意界限词项仍在原环境 γ 中求值，与有界量化的标准语义完全一致。
<!--ja-->
既に有界な二つの節は、前の組と鏡像の関係にあります。ここでは `relativize c` が元の境界の項 `t` を保持し、`⊨ᴬ` も量化子を `⟦ t ⟧ γ` でガードするため、ガードは決して変わりません。`x ∷ γ` での帰納法の仮定を通して本体の充足を変換するだけで、同じ `funExt`、内側の `cong`、外側の `cong (⋁ S)` か `cong (⋀ S)` というパターンがそのまま使えます。境界の項は依然として元の環境 γ で評価され、有界量化の標準的意味論と正確に一致します。
<!--/-->

```agda
  relativize-correct (∀̇ φ)    γ = cong (⋀ S) (funExt (λ x →
    cong (λ q → (x ∈ˢ A) ⇒ q) (relativize-correct φ (x ∷ γ))))
  relativize-correct (∀̇∈ t φ) γ = cong (⋀ S) (funExt (λ x →
    cong (λ q → (x ∈ˢ ⟦ t ⟧ γ) ⇒ q) (relativize-correct φ (x ∷ γ))))
  relativize-correct (∃̇∈ t φ) γ = cong (⋁ S) (funExt (λ x →
```

<!--en-->
All ten cases are handled, and the recursion is on φ, so the proof is complete for every formula and environment. This closes the chapter's argument: relativization is a purely syntactic transformation whose output is Δ₀, and whose standard meaning in any proposition-valued ZF structure is quantification restricted to the chosen set. Later chapters can therefore relativize a definability condition to a set A, work with a Δ₀ formula, and read its satisfaction off from quantification inside A, all backed by this one induction.
<!--zh-->
十个情形全部处理完毕，递归作用于 φ，故证明对每条公式与每个环境都完成。本章论证至此闭合：相对化是纯语法的变换，其输出是 Δ₀，而它在任何取命题的 ZF 结构中的标准含义是限制到选定集合上的量化。因此，后面的章节可以把一个可定义性条件相对化到集合 A，改用 Δ₀ 公式，并直接从 A 内部的量化读出其满足关系，这一切都由这一条归纳支撑。
<!--ja-->
10 個のケースがすべて扱われ、再帰は φ に対するものなので、証明はすべての論理式と環境に対して完了します。これで本章の議論は閉じます。相対化は純粋に構文的な変換であり、その出力は Δ₀ であり、命題をとる任意の ZF 構造におけるその標準的な意味は選んだ集合に制限された量化です。したがって後の章では、定義可能性の条件を集合 A に相対化し、Δ₀ 論理式を用いて作業し、その充足を A の内部での量化から直接読み取れます。そのすべてがこの一つの帰納に支えられています。
<!--/-->

```agda
    cong (λ q → (x ∈ˢ ⟦ t ⟧ γ) ⊓ q) (relativize-correct φ (x ∷ γ))))
```

<!--en-->
## Recap

`relativize` produces a Δ₀ formula, `Δ₀-relativize` records that complexity bound, and `relativize-correct` identifies its meaning with quantification inside the chosen set. Together these give the standard set-theoretic device of restricting an arbitrary formula to a set: syntactically by bounding quantifiers with a constant naming the set, and semantically by the one induction proved here. Downstream, the Δ₀ certificate feeds absoluteness arguments, and the correctness path lets satisfaction of the relativized formula be replaced by bounded quantification over `A` wherever definability is analyzed.
<!--zh-->
## 小结

`relativize` 产生 Δ₀ 公式，`Δ₀-relativize` 记录这一复杂度界，而 `relativize-correct` 将其含义识别为在选定集合内部量化。三者合起来给出了把任意公式限制到一个集合的标准集合论手法：语法上用指称该集合的常元给量词加界，语义上则由这里证明的那一条归纳完成。往下看，Δ₀ 证书供绝对性论证使用，而正确性路径使人们在分析可定义性时，可以把相对化公式的满足关系换成对 `A` 的有界量化。
<!--ja-->
## まとめ

`relativize` は Δ₀ 論理式を作り、`Δ₀-relativize` はその複雑さの上界を記録し、`relativize-correct` はその意味を選んだ集合の内部での量化と同定します。この三つを合わせると、任意の論理式を一つの集合に制限するという標準的な集合論の手法が得られます。構文的には集合を名指す定数で量化子を有界化し、意味論的にはここで証明した一つの帰納がそれを担います。この先では、Δ₀ の証拠が絶対性の議論に供給され、正当性のパスにより、定義可能性を解析する際に相対化された論理式の充足を `A` の上の有界量化に置き換えられます。
<!--/-->
