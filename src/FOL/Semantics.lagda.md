<!--en-->
# Semantics

Syntax distinguishes constants, variables, relations, connectives, and quantifiers, but these symbols do not yet denote anything. An interpretation supplies a truth algebra `𝕋`{.Agda}, a structure `𝒮`{.Agda}, and meanings for the constant symbols. An environment supplies the values of the currently available variables. With these data fixed, structural recursion assigns a carrier element to every term and a truth value to every formula.

The central distinction is between a symbol and its denotation. A constant symbol is sent to the carrier by its interpretation; a variable position is read from the environment; object-language membership and equality are sent to the corresponding relations of the structure. Connectives and quantifiers are interpreted by the operations of the chosen truth algebra.
<!--zh-->
# 语义

语法区分常元、变量、关系、联结词与量词，但这些符号本身尚无指称。解释给出真值代数 `𝕋`{.Agda}、结构 `𝒮`{.Agda} 以及常元符号的含义；环境则给出当前可用变量的取值。确定这些数据后，结构递归为每个词项指定载体元素，并为每条公式指定真值。

关键区别在于符号与其指称。常元符号由解释送入载体，变量位置从环境读取，对象语言的成员与等词由结构中的相应关系解释，联结词与量词则由所选真值代数的运算解释。
<!--ja-->
# 意味論

構文は定数、変数、関係、結合子、量化子を区別しますが、これらの記号だけではまだ表示がありません。解釈は真理値代数 `𝕋`{.Agda}、構造 `𝒮`{.Agda}、定数記号の意味を与え、環境は現在利用できる変数の値を与えます。これらのデータを固定すると、構造的再帰によって各項に台の要素を、各論理式に真理値を割り当てられます。

中心となる区別は、記号とその表示の違いです。定数記号は解釈によって台へ送られ、変数の位置は環境から読み出されます。対象言語の所属と等号は構造の対応する関係で、結合子と量化子は選んだ真理値代数の演算で解釈されます。
<!--/-->

<!--en-->
Fix a truth algebra `𝕋 : TruthAlgebra ℓ ℓ'`{.Agda} and a structure `𝒮 : ZFStructure 𝕋`{.Agda}. Formula values then lie in the carrier `Ω` of `𝕋`, while atomic equality and membership use the truth-valued relations supplied by `𝒮`. At this stage no particular proposition-valued instance or set-theoretic axiom is needed.
<!--zh-->
固定真值代数 `𝕋 : TruthAlgebra ℓ ℓ'`{.Agda} 以及取值于它的结构 `𝒮 : ZFStructure 𝕋`{.Agda}。公式的值落在 `𝕋` 的载体 `Ω` 中，原子的等词与成员则使用 `𝒮` 提供的真值关系。此处不需要指定命题值实例，也不需要假设集合论公理。
<!--ja-->
真理値代数 `𝕋 : TruthAlgebra ℓ ℓ'`{.Agda} と、そこに値をもつ構造 `𝒮 : ZFStructure 𝕋`{.Agda} を固定します。論理式の値は `𝕋` の台 `Ω` に属し、原子的な等号と所属には `𝒮` が与える真理値関係を用います。この段階では、特定の命題値の実例も集合論の公理も必要ありません。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import FOL.ZFStructure using ( ZFStructure )

module FOL.Semantics {ℓ ℓ'} (𝕋 : TruthAlgebra ℓ ℓ') (𝒮 : ZFStructure 𝕋) where
```

<!--en-->
Each syntactic primitive then asks for exactly one semantic ingredient. A term is either a constant, answered by the interpretation, or a variable, answered by the environment. An atomic formula is answered by a relation of the structure. A connective or quantifier is answered by an operation of the truth algebra `𝕋`{.Agda}. With this division of labor the same syntax is interpretable in any structure valued in the chosen truth algebra, and the definition to come simply follows the shape of the formula.
<!--zh-->
此后每个语法原语恰好要一种语义成分来回答：词项要么是常元，由解释作答；要么是变量，由环境作答。原子公式由结构的关系作答。联结词与量词则由真值代数 `𝕋`{.Agda} 的运算作答。有了这个分工，同一套语法便可在取值于所选真值代数的任意结构中解释，接下来的定义也只是顺着公式的形状进行。
<!--ja-->
その後の各構文の primitive には、それぞれ一つの意味的成分が対応します。項は定数なら解釈が、変数なら環境が答えます。原子論理式は構造の関係が答えます。結合子と量化子は真理値代数 `𝕋`{.Agda} の演算が答えます。この分担により、同じ構文は選ばれた真理値代数に値を持つ任意の構造で解釈でき、これから定義するものは公式の形に沿って進むだけです。
<!--/-->

```agda

open import FOL.Syntax using
  ( Term; con; var
  ; Formula; _∈̇_; _≐_; _∧̇_; _∨̇_; _⇒̇_; ⊥̇; ∃̇_; ∀̇_; ∀̇∈; ∃̇∈ )

open TruthAlgebra 𝕋
open ZFStructure 𝒮
```

<!--en-->
## Environments

A term or formula of arity `n` can refer to positions indexed by `Fin n`{.Agda}, and an **environment** `γ` supplies a carrier element at each position. For example, an environment in `S ^ 2`{.Agda} has two entries, available to `var zero` and `var (suc zero)`; a particular formula may use either, both, or neither. Thus `n` bounds the available positions rather than counting the distinct variables that actually occur. Binding is handled the same way: when a quantifier introduces a value, the environment is extended with that value in front, and the body addresses it at position `zero`.
<!--zh-->
## 环境

元数为 `n` 的词项或公式可以引用由 `Fin n`{.Agda} 索引的位置，**环境** `γ` 为每个位置提供一个载体元素。例如，`S ^ 2`{.Agda} 中的环境有两个分量，可由 `var zero` 与 `var (suc zero)` 读取；某个具体公式可以只用其中一个、两个都用，或都不用。因此 `n` 限定可用位置，而不是统计实际出现的不同变量。绑定也以同样方式处理：量词引入一个值时，环境把该值加在最前面，主体在位置 `zero` 处读取它。
<!--ja-->
## 環境

アリティ `n` の項や論理式は `Fin n`{.Agda} で添字付けされた位置を参照し、**環境** `γ` は各位置に台の要素を一つ与えます。例えば `S ^ 2`{.Agda} の環境には二つの成分があり、`var zero` と `var (suc zero)` が参照できますが、個々の論理式はその一方だけ、両方、あるいはどちらも使わないこともあります。したがって `n` は利用可能な位置の範囲を定めるのであって、実際に現れる相異なる変数を数えるものではありません。束縛も同じ仕組みで扱います。量化子が値を導入するとき、環境はその値を先頭に付けた形に拡張され、本体は位置 `zero` でそれを読みます。
<!--/-->

<!--en-->
The book's notation for the type of an environment is `S ^ n`{.Agda}, matching the traditional superscript $S^n$; `_^_`{.Agda} reads "power" and is nothing but notation. It is defined to be `Vec A n`, an ordered vector whose length appears in its type, so the arity of the formula and the length of the environment are forced to agree, and `lookup` reads an entry at a position in `Fin n`.
<!--zh-->
全书把环境的类型记为 `S ^ n`{.Agda}，对应传统上标 $S^n$；`_^_`{.Agda} 读作「幂」，这只是记号。它定义为 `Vec A n`，即长度出现在类型中的有序向量，因此公式的元数与环境的长度被迫一致，`lookup` 可读取 `Fin n` 所给位置上的分量。
<!--ja-->
本書は環境の型を `S ^ n`{.Agda} と表記し、伝統的な上付きの $S^n$ に対応させます。`_^_`{.Agda} は「冪」と読みますが、単なる記法です。その定義は `Vec A n`、すなわち長さが型に現れる順序付きベクトルであり、論理式のアリティと環境の長さは型の上で一致を強制されます。`lookup` は `Fin n` の位置にある成分を読み出します。
<!--/-->

```agda
infixl 30 _^_

_^_ : ∀ {ℓ''} → Type ℓ'' → ℕ → Type ℓ''
A ^ n = Vec A n
```

<!--en-->
## Evaluation and satisfaction

Write `⟦ t ⟧ γ`{.Agda} for the carrier element denoted by a term under environment `γ`, and `γ ⊨ φ`{.Agda} for the truth value of a formula. A constant interpretation `ι : K → S` is fixed for these definitions: constants receive their values from `ι`, while variables continue to vary with `γ`. This separation lets binding change variable values without changing what the constant symbols denote.
<!--zh-->
## 求值与满足

以 `⟦ t ⟧ γ`{.Agda} 表示词项在环境 `γ` 下指称的载体元素，以 `γ ⊨ φ`{.Agda} 表示公式的真值。这些定义固定一个常元解释 `ι : K → S`：常元从 `ι` 取得值，变量则随 `γ` 改变。这样，绑定可以改变变量取值，而不改变常元符号的指称。
<!--ja-->
## 評価と充足

`⟦ t ⟧ γ`{.Agda} は環境 `γ` のもとで項が表示する台の要素を、`γ ⊨ φ`{.Agda} は論理式の真理値を表します。これらの定義では定数解釈 `ι : K → S` を固定します。定数は `ι` から値を得ますが、変数は `γ` とともに変化します。この分離により、束縛は定数記号の表示を変えずに変数の値を変えられます。
<!--/-->

<!--en-->
The interpretation `ι` and environment `γ` answer different lookup questions. A constant `con k` denotes `ι k`; a variable `var i` denotes the entry `lookup i γ`. Thus changing the environment affects variable occurrences, whereas the meanings of constant symbols remain fixed by `ι`.
<!--zh-->
解释 `ι` 与环境 `γ` 回答两种不同的查找问题。常元 `con k` 指称 `ι k`，变量 `var i` 指称分量 `lookup i γ`。因此，改变环境会影响变量的出现，而常元符号的含义仍由 `ι` 固定。
<!--ja-->
解釈 `ι` と環境 `γ` は、異なる二種類の参照に答えます。定数 `con k` は `ι k` を表示し、変数 `var i` は成分 `lookup i γ` を表示します。したがって環境の変更は変数の出現に影響しますが、定数記号の意味は `ι` によって固定されたままです。
<!--/-->

```agda
module At {ℓc} (K : Type ℓc) (ι : K → S) where
```

<!--en-->
Evaluation of a term either asks `ι` (a constant) or looks up the environment (a variable). Satisfaction is a single structural recursion over the ten constructors: each primitive clause is the truth algebra's corresponding operation applied to the meanings of the subformulas, and each quantifier extends the environment by the freshly bound value. In both bounded clauses, the bound term is evaluated in the original environment `γ`, while the body is evaluated in the extended environment `x ∷ γ`.
<!--zh-->
词项求值要么问 `ι` (常元)，要么查环境 (变量)。满足关系是对十个构造子的一次结构递归：每个原语子句都是真值代数的对应运算作用在子公式的含义上，每个量词都用新绑定的值扩展环境。两条有界子句都在原环境 `γ` 中求值界限词项，而在扩展环境 `x ∷ γ` 中求值主体。
<!--ja-->
項の評価は、定数なら `ι` に、変数なら環境を尋ねます。充足関係は十個の構成子に対する一回の構造的再帰です。各 primitive の節は部分公式の意味に対する真理値代数の対応する演算であり、各量化子は新しく束縛した値で環境を拡張します。二つの有界量化の節では、限界の項を元の環境 `γ` で評価し、本体を拡張した環境 `x ∷ γ` で評価します。
<!--/-->

<!--en-->
Satisfaction takes an environment and a formula to a truth value in `Ω`. Atomic membership and equality first evaluate their two terms and then apply the structure relations `∈ˢ` and `≈ˢ`. For compound formulas, the object-language symbols `∧̇`, `∨̇`, and `⇒̇` are interpreted by the selected operations `⊓`, `⊔`, and `⇒` of the truth algebra. These operations need not be the host-language connectives unless the chosen truth algebra makes them so.
<!--zh-->
满足关系把环境与公式送到 `Ω` 中的真值。原子的成员与等词先对两个词项求值，再应用结构关系 `∈ˢ` 与 `≈ˢ`。对于复合公式，对象语言符号 `∧̇`、`∨̇`、`⇒̇` 分别由真值代数中选定的运算 `⊓`、`⊔`、`⇒` 解释。除非所选真值代数如此规定，这些运算并不等同于宿主语言的联结词。
<!--ja-->
充足関係は、環境と論理式を `Ω` の真理値へ送ります。原子的な所属と等号では、まず二つの項を評価し、それから構造の関係 `∈ˢ` と `≈ˢ` を適用します。複合式では、対象言語の記号 `∧̇`、`∨̇`、`⇒̇` を、真理値代数で選んだ演算 `⊓`、`⊔`、`⇒` によって解釈します。選んだ真理値代数がそう定める場合を除き、これらはホスト言語の結合子そのものではありません。
<!--/-->

```agda
  ⟦_⟧ : ∀ {n} → Term K n → S ^ n → S
  ⟦ con k ⟧ γ = ι k
  ⟦ var i ⟧ γ = lookup i γ

  infix 6 _⊨_

  _⊨_ : ∀ {n} → S ^ n → Formula K n → Ω
```

<!--en-->
Falsity is sent to `⊥`. An unbounded quantifier combines the body values as `x` ranges over all of `S`; the extended environment `x ∷ γ` places the newly bound value at position `zero`, while the old entries are reached by successor positions. For example, in the body of `∀̇∈ t φ`, `var zero` denotes the candidate `x`, but any variable already free in the outer formula is read from the shifted tail `γ`.
<!--zh-->
假解释为 `⊥`。无界量词在 `x` 取遍整个 `S` 时汇集主体的真值；扩展环境 `x ∷ γ` 把新绑定的值放在位置 `zero`，原环境的分量则由后继位置读取。例如，在 `∀̇∈ t φ` 的主体中，`var zero` 指称候选元素 `x`，而外层公式中原已自由的变量从后移的尾部 `γ` 读取。
<!--ja-->
偽は `⊥` で解釈します。非有界量化は、`x` が `S` 全体を動くときの本体の値をまとめます。拡張環境 `x ∷ γ` は新しく束縛した値を位置 `zero` に置き、元の環境の成分は後続位置から読みます。例えば `∀̇∈ t φ` の本体では、`var zero` は候補 `x` を表示し、外側の論理式ですでに自由だった変数は、後ろへ移った尾部 `γ` から読み出されます。
<!--/-->

```agda
  γ ⊨ (t ∈̇ u)  = ⟦ t ⟧ γ ∈ˢ ⟦ u ⟧ γ
  γ ⊨ (t ≐ u)  = ⟦ t ⟧ γ ≈ˢ ⟦ u ⟧ γ
  γ ⊨ (φ ∧̇ ψ)  = (γ ⊨ φ) ⊓ (γ ⊨ ψ)
  γ ⊨ (φ ∨̇ ψ)  = (γ ⊨ φ) ⊔ (γ ⊨ ψ)
  γ ⊨ (φ ⇒̇ ψ)  = (γ ⊨ φ) ⇒ (γ ⊨ ψ)
```

<!--en-->
The bounded clauses combine membership in the denotation of `t` with the body. The universal formula uses `(x ∈ˢ ⟦ t ⟧ γ) ⇒ ((x ∷ γ) ⊨ φ)`; the existential formula uses the corresponding conjunction. The bound term `t` lies outside the new binder and is therefore evaluated in the original environment `γ`, while the body `φ` is evaluated in `x ∷ γ`. This is the semantic reading of *every member of `t` satisfies `φ`* and *some member of `t` satisfies `φ`*.
<!--zh-->
有界子句把属于 `t` 的指称这一条件与主体结合起来。全称公式使用 `(x ∈ˢ ⟦ t ⟧ γ) ⇒ ((x ∷ γ) ⊨ φ)`，存在公式则使用相应的合取。界限词项 `t` 位于新绑定之外，因而在原环境 `γ` 中求值；主体 `φ` 则在 `x ∷ γ` 中求值。这分别给出「`t` 的每个成员都满足 `φ`」与「`t` 的某个成员满足 `φ`」的语义读法。
<!--ja-->
有界量化の節は、`t` の表示への所属条件と本体を組み合わせます。全称論理式は `(x ∈ˢ ⟦ t ⟧ γ) ⇒ ((x ∷ γ) ⊨ φ)` を用い、存在論理式は対応する連言を用います。限界の項 `t` は新しい束縛の外側にあるため元の環境 `γ` で評価され、本体 `φ` は `x ∷ γ` で評価されます。これはそれぞれ「`t` のすべての元が `φ` を満たす」と「`t` のある元が `φ` を満たす」という意味論的な読みです。
<!--/-->

```agda
  γ ⊨ ⊥̇        = ⊥
  γ ⊨ (∃̇ φ)    = ⋁ S (λ x → (x ∷ γ) ⊨ φ)
  γ ⊨ (∀̇ φ)    = ⋀ S (λ x → (x ∷ γ) ⊨ φ)
  γ ⊨ (∀̇∈ t φ) = ⋀ S (λ x → (x ∈ˢ ⟦ t ⟧ γ) ⇒ ((x ∷ γ) ⊨ φ))
  γ ⊨ (∃̇∈ t φ) = ⋁ S (λ x → (x ∈ˢ ⟦ t ⟧ γ) ⊓ ((x ∷ γ) ⊨ φ))
```

<!--en-->
## Recap

Meaning is compositional. A term denotes a carrier element determined by its constant interpretation and environment. A formula of arity `n` determines a function `S ^ n → Ω`{.Agda}, whether or not it uses every available variable position. Atomic formulas use the structure relations; compound formulas use the truth-algebra operations. Quantifiers vary a new position at the front of the environment, and bounded quantifiers evaluate their bound outside that extension and their body inside it.
<!--zh-->
## 小结

语义按组成给出。词项的指称是由常元解释与环境确定的载体元素。元数为 `n` 的公式确定一个 `S ^ n → Ω`{.Agda} 型函数，无论它是否使用了每个可用变量位置。原子公式使用结构关系，复合公式使用真值代数运算。量词在环境前端改变一个新位置；有界量词在扩展之外求值界限，在扩展之内求值主体。
<!--ja-->
## まとめ

意味は合成的に与えられます。項は、定数解釈と環境によって定まる台の要素を表示します。アリティ `n` の論理式は、利用可能な変数位置をすべて使うかどうかにかかわらず、`S ^ n → Ω`{.Agda} 型の関数を定めます。原子式には構造の関係を、複合式には真理値代数の演算を用います。量化子は環境の先頭に新しい位置を加えてその値を動かし、有界量化子はその拡張の外で限界を、内で本体を評価します。
<!--/-->
