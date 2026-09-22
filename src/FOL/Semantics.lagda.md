<!--en-->
# Semantics

The object language consists of symbols and rules for combining them, and so far none of the symbols denotes anything. What must be supplied before `∈̇` or `_≐_` can be read? A structure decides what the variables range over and what the two atomic predicates mean there; an interpretation gives each constant symbol its carrier element; an environment gives each available variable position its current value. Once these data are fixed, structural recursion assigns to every term a carrier element and to every formula a proposition. The whole chapter turns on one distinction, that between a symbol and its denotation: the sign `∈̇` belongs to the syntax, what it comes to mean is the relation `∈ˢ`{.Agda} of the structure, and the two live on different layers.
<!--zh-->
# 语义

对象语言由符号与组合规则构成，而这些符号至今没有任何指称。要让 `∈̇` 或 `_≐_` 成为可读的东西，需要供给什么？结构决定变量在什么范围内取值、两条原子谓词在那里指什么；解释为每个常元符号指定其载体元素；环境为每个可用的变量位置指定当前取值。这些数据一经固定，结构递归便为每个词项指定一个载体元素，为每条公式指定一个命题。全章系于一个区分，即符号与指称之分：记号 `∈̇` 属于语法，它最终意味的是结构的关系 `∈ˢ`{.Agda}，二者居于不同的层。
<!--ja-->
# 意味論

対象言語は記号とその組み合わせの規則からなり、現時点で記号は何も表示しない。`∈̇` や `_≐_` を読めるようにするには、何を供給しなければならないのであろうか。構造は、変数が何の上を動くかと、二つの原始的な述語がそこで何を意味するかを決める。解釈は各定数記号に台の要素を割り当て、環境は利用できる各変数位置に現在の値を与える。これらのデータが固定されると、構造的再帰によってすべての項に台の要素が、すべての論理式に命題が割り当てられる。本章を貫くのは、記号とその表示という一つの区別である。記号 `∈̇` は構文に属し、それが意味するようになるのは構造の関係 `∈ˢ`{.Agda} であり、両者は異なる層に住んでいる。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Classical using ( LEM )
open import FOL.ZFStructure using ( ZFStructure )

module FOL.Semantics {ℓ} (𝒮 : ZFStructure ℓ) where
```

<!--en-->
Fix a structure `𝒮 : ZFStructure ℓ`{.Agda}, the model-theoretic data of the preceding chapter: a carrier `S` that is an h-set, together with an equality `≈ˢ` and a membership `∈ˢ`, each sending two carrier elements to a proposition in `hProp ℓ`{.Agda}. The interpretation of every formula will land in this same proposition universe, so a claim about sets becomes, quite literally, a proposition with proofs as its inhabitants. Nothing beyond these fields is used. The record `ZFStructure` itself contains no set-theoretic axioms, and defining the semantics requires none.
<!--zh-->
固定一个结构 `𝒮 : ZFStructure ℓ`{.Agda}，即上一章的模型论数据：一个作为 h-集合的载体 `S`，加上等词 `≈ˢ` 与隶属 `∈ˢ`，二者都把两个载体元素送到 `hProp ℓ`{.Agda} 中的一个命题。每条公式的解释都将落在这个命题宇宙之中，于是关于集合的陈述实实在在地成为一个命题，其元素就是证明。除了这些字段之外，不再使用结构的其他内容。`ZFStructure` 这个 record 本身不含集合论公理，定义语义也不需要任何集合论公理。
<!--ja-->
一つの構造 `𝒮 : ZFStructure ℓ`{.Agda} を固定する。これは前章のモデル論的データ、すなわち h-集合である台 `S` と、二つの台の要素を `hProp ℓ`{.Agda} の命題に送る等号 `≈ˢ` と所属 `∈ˢ` である。すべての論理式の解釈はこの同じ命題の宇宙に着地する。したがって集合についての主張は、文字どおり、証明を要素として持つ命題になる。これらのフィールド以外に、構造の内容は使わない。`ZFStructure` というレコード自体は集合論の公理を含まず、意味論の定義にも集合論の公理は要らない。
<!--/-->

```agda

open import FOL.Syntax using
  ( Term; con; var
  ; Formula; _∈̇_; _≐_; _∧̇_; _∨̇_; _⇒̇_; ⊥̇; ∃̇_; ∀̇_; ∀̇∈; ∃̇∈ )

open ZFStructure 𝒮
```

<!--en-->
The fields of the record are now in scope under their own names: `S` for the carrier, `∈ˢ` and `≈ˢ` for the relations, so `x ∈ˢ y` reads as the structure's membership proposition about `x` and `y`. The constructors of the object language are in scope as well, and each kind of symbol has a clear partner on the semantic side. A constant symbol needs a carrier element, fixed once by a function from the constant domain to `S`. A variable position needs a value that may change from use to use; an environment supplies it. An atomic formula needs one of the two relations. A connective or a quantifier needs no set theory at all: the logical operations on propositions from the Prelude, `⊓`, `⊔`, `⇒`, `∀[ x ] P x` and `∃[ x ] P x`, take their places. Interpretation is compositional: the meaning of a term or formula is determined from its constructor and the meanings of its immediate parts.
<!--zh-->
record 的字段如今以自己的名字进入作用域：`S` 是载体，`∈ˢ` 与 `≈ˢ` 是两个关系，于是 `x ∈ˢ y` 读作结构关于 `x`、`y` 的隶属命题。对象语言的构造子也在作用域内，每一类符号在语义一侧都有明确的对应物。常元符号需要一个载体元素，由从常元域到 `S` 的函数一次固定。变量位置需要一个可随使用变化的取值，由环境供给。原子公式需要两个关系之一。联结词与量词则完全不需要集合论：《基础词汇》中命题上的逻辑运算 `⊓`、`⊔`、`⇒`、`∀[ x ] P x`、`∃[ x ] P x` 在此就位。解释遵循组合原则：词项或公式的意义由它的构造子及其直接组成部分的意义共同确定。
<!--ja-->
レコードのフィールドは今や固有の名前でスコープに入っている。`S` が台を、`∈ˢ` と `≈ˢ` が二つの関係を表し、したがって `x ∈ˢ y` は `x` と `y` についての構造の所属命題と読む。対象言語の構成子もスコープにあり、各種の記号には意味論の側に明確な対応物がある。定数記号には台の要素が一つ必要であり、定数域から `S` への関数によって一度に固定される。変数の位置には、使用のたびに変わりうる値が必要で、それを供給するのが環境である。原子論理式には二つの関係のいずれかが必要である。結合子と量化子には集合論はまったく要らず、「基礎語彙」の命題上の論理演算 `⊓`、`⊔`、`⇒`、`∀[ x ] P x`、`∃[ x ] P x` がそこに収まる。解釈は合成的である。項や論理式の意味は、その構成子と、直接の構成部分の意味から定まる。
<!--/-->

<!--en-->
## Environments

A term of arity `n` may refer to the positions `0` through `n - 1`, and an **environment** `γ` assigns a carrier element to each of them. An environment in `S ^ 2`{.Agda} has two entries, available to `var zero` and `var (suc zero)`; a particular term or formula may use either, both, or neither. The length `n` therefore bounds the positions that are available rather than counting the variables that actually occur. Binding works on the same principle. When a quantifier considers a candidate from the carrier, the environment is extended by placing that element in front, and the body addresses it at position `zero`.
<!--zh-->
## 环境

元数为 `n` 的词项可以引用位置 `0` 到 `n - 1`，**环境** `γ` 为其中每个位置指派一个载体元素。`S ^ 2`{.Agda} 中的环境有两个分量，可供 `var zero` 与 `var (suc zero)` 读取；某个具体的词项或公式可以只用其一、两者都用，或都不用。因此长度 `n` 界定的是可用位置的范围，而不是实际出现的变量的个数。绑定遵循同一原理：量词考虑来自载体的一个候选元素时，环境把该元素加在最前面从而得到扩展，公式体在位置 `zero` 处读取它。
<!--ja-->
## 環境

アリティ `n` の項は位置 `0` から `n - 1` までを参照でき、**環境** `γ` はその各位置に台の要素を一つ割り当てる。`S ^ 2`{.Agda} の環境には二つの成分があり、`var zero` と `var (suc zero)` が参照できるが、個々の項や論理式はその一方だけ、両方、あるいはどちらも使わないこともある。したがって長さ `n` が定めるのは利用できる位置の範囲であって、実際に現れる変数の個数ではない。束縛も同じ原理で働く。量化子が台からの候補を取り上げるとき、環境はその要素を先頭に置いて拡張され、本体は位置 `zero` でそれを読む。
<!--/-->

<!--en-->
The type of an environment is written `S ^ n`{.Agda}, matching the traditional superscript $S^n$; `_^_`{.Agda} reads "power" and is pure notation. It is defined as `Vec A n`, an ordered vector whose length is part of its type. Here a dependent type does real work: the arity of a formula and the length of an environment cannot disagree, for a mismatch would not be a well-formed combination at all. The operation `lookup` returns the entry at a position in `Fin n`{.Agda}, and `x ∷ γ` prepends one entry, moving the previous ones to the successor positions.
<!--zh-->
环境的类型记作 `S ^ n`{.Agda}，对应传统的上标 $S^n$；`_^_`{.Agda} 读作「幂」，纯粹是记号。它定义为 `Vec A n`，即长度写进类型的有序向量。这里依赖类型真正发挥了作用：公式的元数与环境的长度不可能不一致，不匹配时连合法的组合都构不成。运算 `lookup` 返回 `Fin n`{.Agda} 中某位置上的分量，`x ∷ γ` 在最前面加入一个分量，原有分量顺次移到后继位置。
<!--ja-->
環境の型は `S ^ n`{.Agda} と表記し、伝統的な上付きの $S^n$ に対応させる。`_^_`{.Agda} は「冪」と読むが、単なる記法である。その定義は `Vec A n`、すなわち長さが型の一部になっている順序付きベクトルである。ここでは依存型が実際の仕事を担っている。論理式のアリティと環境の長さは食い違いようがなく、不一致ならそもそも正しい組み合わせが成立しない。演算 `lookup` は `Fin n`{.Agda} の位置にある成分を返し、`x ∷ γ` は先頭に一つ成分を付け加え、それまでの成分を後続の位置へ移す。
<!--/-->

```agda
infixl 30 _^_

_^_ : ∀ {ℓ''} → Type ℓ'' → ℕ → Type ℓ''
A ^ n = Vec A n
```

<!--en-->
## Evaluation and satisfaction

Two judgments carry the semantics. Write `⟦ t ⟧ γ`{.Agda} for the carrier element denoted by the term `t` under the environment `γ`, and `γ ⊨ φ`{.Agda} for the proposition stating that the formula `φ` holds under `γ`. Both are defined relative to a fixed constant interpretation `ι : K → S`: constants receive their values from `ι`, while variables keep varying with `γ`. The separation matters as soon as quantifiers appear: binding changes the values of the variables, and the constant symbols keep their denotations.
<!--zh-->
## 求值与满足

两个判断承载语义。以 `⟦ t ⟧ γ`{.Agda} 表示词项 `t` 在环境 `γ` 下指称的载体元素，以 `γ ⊨ φ`{.Agda} 表示陈述公式 `φ` 在 `γ` 下成立的那个命题。二者都相对于一个固定的常元解释 `ι : K → S` 而定义：常元从 `ι` 取值，变量则继续随 `γ` 变化。量词一出现，这种分离就显出作用：绑定改变变量的取值，而常元符号的指称不动。
<!--ja-->
## 評価と充足

意味論を運ぶのは二つの判断である。`⟦ t ⟧ γ`{.Agda} は項 `t` が環境 `γ` のもとで表示する台の要素を、`γ ⊨ φ`{.Agda} は論理式 `φ` が `γ` のもとで成立することを述べる命題を表す。どちらも固定された定数解釈 `ι : K → S` に対して定義される。定数は `ι` から値を得て、変数は `γ` とともに変わり続ける。量化子が現れると、この分離がただちに効いてくる。束縛は変数の値を変えるが、定数記号の表示は変わらない。
<!--/-->

<!--en-->
The interpretation and the environment answer two different questions. The constant `con k` denotes `ι k`, whichever environment is supplied; the variable `var i` denotes `lookup i γ`, whichever interpretation is fixed. Thus the environment enters term evaluation only in the variable case, while the meanings of the constant symbols remain fixed by `ι`. These two cases exhaust term evaluation.

Fix a constant domain `K` and an interpretation `ι : K → S`. At this fixed interpretation, term evaluation sends a term and an environment to an element of `S`, while satisfaction sends a formula and an environment to a proposition. Satisfaction is defined by structural recursion: atomic formulas use the two relations of the structure, connectives use the propositional operations of the Prelude, falsity uses the empty proposition, and quantifiers range over the carrier. In a bounded quantifier, the denotation of the bound determines the membership condition on the quantified element.
<!--zh-->
解释与环境回答的是两个不同的问题。常元 `con k` 指称 `ι k`，与供给哪个环境无关；变量 `var i` 指称 `lookup i γ`，与固定哪个解释无关。因此，环境只在变量这一情形参与词项求值，常元符号的含义始终由 `ι` 固定。这两个情形穷尽了词项求值。

固定常元域 `K` 与解释 `ι : K → S`。在这个固定解释下，词项求值把词项和环境送到 `S` 的元素，满足关系则把公式和环境送到命题。满足关系按公式结构递归定义：原子式使用结构的两个关系，联结词使用《基础词汇》中的命题运算，假使用空命题，量词遍及载体。在有界量词中，界限的指称决定被量化元素须满足的成员条件。
<!--ja-->
解釈と環境は、互いに異なる二つの問いに答える。定数 `con k` はどの環境を与えても `ι k` を表示し、変数 `var i` はどの解釈を固定しても `lookup i γ` を表示する。したがって環境が項の評価に関わるのは変数の場合だけで、定数記号の意味はつねに `ι` が固定する。この二つの場合で項の評価は尽くされる。

定数域 `K` と解釈 `ι : K → S` を固定する。この解釈のもとで、項の評価は項と環境を `S` の要素へ送り、充足関係は論理式と環境を命題へ送る。充足関係は論理式の構造に沿って再帰的に定まる。原子式は構造の二つの関係を、結合子は「基礎語彙」の命題演算を、偽は空命題を用い、量化子は台の上を動く。有界量化子では、限界の表示が、量化される要素の満たすべき所属条件を定める。
<!--/-->

```agda
module At {ℓc} (K : Type ℓc) (ι : K → S) where
```

<!--en-->
Two definitions carry the section, and their types say what they are. Evaluation `⟦_⟧`{.Agda} maps a term and an environment to a carrier element. Satisfaction `_⊨_`{.Agda} maps an environment and a formula to a proposition in `hProp ℓ`{.Agda}, that is, to a type any two of whose elements are equal; the inhabitants of such a type are its proofs. Satisfaction is therefore not a bare verdict but a proposition, and the definition computes, for each formula and environment, exactly which proposition is meant. The arity `n` appears in both types, so only an environment of matching length can be applied to a formula: the earlier discipline between formula and environment is now enforced by the types themselves.
<!--zh-->
两样定义承载本节，其类型说明了它们是什么。求值 `⟦_⟧`{.Agda} 把词项与环境送到一个载体元素。满足 `_⊨_`{.Agda} 把环境与公式送到 `hProp ℓ`{.Agda} 中的一个命题，即任意两个元素都相等的类型；这类类型的元素就是证明。因此满足不是单纯的判定结果，而是一个命题：定义将为每条公式与每个环境算出所指的究竟是哪个命题。元数 `n` 出现在两个类型之中，所以只有长度相符的环境才能施加于公式：先前关于公式与环境的规矩，如今由类型本身来执行。
<!--ja-->
この節を支えるのは二つの定義で、その型が何であるかを物語っている。評価 `⟦_⟧`{.Agda} は項と環境を台の要素へ写す。充足 `_⊨_`{.Agda} は環境と論理式を `hProp ℓ`{.Agda} の命題、すなわち任意の二要素が等しい型へ写す。そのような型の要素は証明である。したがって充足は単なる判定ではなく命題であり、定義は各式と各環境に対して、意味される命題がちょうどどれであるかを計算する。アリティ `n` は両方の型に現れるため、長さの合う環境だけが論理式に適用できる。論理式と環境の間の規律は、今や型そのものが強制する。
<!--/-->

```agda
  ⟦_⟧ : ∀ {n} → Term K n → S ^ n → S
  ⟦ con k ⟧ γ = ι k
  ⟦ var i ⟧ γ = lookup i γ

  infix 6 _⊨_

  _⊨_ : ∀ {n} → S ^ n → Formula K n → hProp ℓ
```

<!--en-->
An atomic membership evaluates its two terms and hands them to the structure: the claim becomes the structure's membership proposition about the two denotations. The equality atom does the same with `≈ˢ`. Here, at last, the dotted symbol means something: `∈̇` is read as `∈ˢ`, one layer down from the syntax. The propositional clauses stay entirely on the host side. Conjunction is interpreted by `⊓`, disjunction by `⊔`, implication by `⇒`, each an operation on propositions. A proof of a conjunction is a pair of proofs; a proof of an implication is a function turning a proof of the antecedent into a proof of the consequent. These three clauses use no set theory at all; they are the propositional logic of the host, applied to the propositions denoted by the subformulas.
<!--zh-->
原子的隶属先对两个词项求值，再把它们交给结构：该断言成为结构关于两个指称的隶属命题。相等原子对 `≈ˢ` 如法炮制。在此，带点的符号终于有了含义：`∈̇` 被读作 `∈ˢ`，比语法低一层。三条命题子句则完全留在宿主一侧：合取由 `⊓` 解释，析取由 `⊔` 解释，蕴涵由 `⇒` 解释，每个都是命题上的运算。合取的证明是一对证明；蕴涵的证明是一个函数，把前件的证明变成后件的证明。这三条子句完全不用集合论，它们是宿主的命题逻辑，施于子公式所指的命题。
<!--ja-->
原子的な所属は二つの項を評価し、それらを構造に渡す。主張は、二つの表示についての構造の所属命題になる。等号の原子は `≈ˢ` について同様である。ここで、点付きの記号がついに意味を持つ。`∈̇` は `∈ˢ` として読まれ、構文より一つ下の層に降りる。命題的な三つの節は完全にホストの側にとどまる。連言は `⊓` で、選言は `⊔` で、含意は `⇒` で解釈され、いずれも命題上の演算である。連言の証明は証明の対であり、含意の証明は前件の証明を後件の証明へ変える関数である。この三つの節に集合論はまったく現れず、ホストの命題論理が部分公式の表示する命題に施されるだけである。
<!--/-->

```agda
  γ ⊨ (t ∈̇ u)  = ⟦ t ⟧ γ ∈ˢ ⟦ u ⟧ γ
  γ ⊨ (t ≐ u)  = ⟦ t ⟧ γ ≈ˢ ⟦ u ⟧ γ
  γ ⊨ (φ ∧̇ ψ)  = (γ ⊨ φ) ⊓ (γ ⊨ ψ)
  γ ⊨ (φ ∨̇ ψ)  = (γ ⊨ φ) ⊔ (γ ⊨ ψ)
  γ ⊨ (φ ⇒̇ ψ)  = (γ ⊨ φ) ⇒ (γ ⊨ ψ)
```

<!--en-->
Falsity needs no environment: `⊥̇` is read as the empty proposition `⊥`. The quantifiers are where the carrier finally enters. The unbounded `∃̇ φ` expresses existential quantification over the carrier: the proposition that some element `x` of `S` makes the body hold at the extended environment `x ∷ γ`. Its twin `∀̇ φ` expresses universal quantification, and a proof of it is a function assigning to each `x : S` a proof of the body at `x ∷ γ`. Inside the body, position `zero` holds the candidate `x`, while the entries of `γ` have moved to the successor positions; a variable free in the outer formula is read from the tail. By propositional truncation, the existential records that such an element exists without carrying the element as data.

The bounded forms add one ingredient: membership in the denotation of the bound. `∀̇∈ t φ` demands that membership in `⟦ t ⟧ γ` imply the body, so every member of `⟦ t ⟧ γ` satisfies `φ`; `∃̇∈ t φ` asks for an element that is a member and satisfies the body. Note where each environment is used. The bound `t` lies outside the new binder and is evaluated in the original `γ`; only the body sees the extension `x ∷ γ`. These two clauses are precisely the semantic content of the readings "every member of `t` satisfies `φ`" and "some member of `t` satisfies `φ`".
<!--zh-->
假不需要任何环境：`⊥̇` 被读作空命题 `⊥`。量词是载体最终登场之处。无界的 `∃̇ φ` 表达对载体的存在量化：即 `S` 的某个元素 `x` 使公式体在扩展环境 `x ∷ γ` 下成立的那个命题。它的对偶 `∀̇ φ` 表达全称量化，其证明是一个函数，为每个 `x : S` 指派公式体在 `x ∷ γ` 下的证明。在公式体内部，位置 `zero` 持有候选元素 `x`，而 `γ` 的各分量已移到后继位置；外层公式中自由的变量从尾部读取。由命题截断，存在量化只记录这样的元素存在，并不把该元素作为数据携带。

有界形式增加一个成分：属于界限指称的成员资格。`∀̇∈ t φ` 要求属于 `⟦ t ⟧ γ` 蕴涵公式体，于是 `⟦ t ⟧ γ` 的每个成员都满足 `φ`；`∃̇∈ t φ` 寻求一个既是成员又满足公式体的元素。注意各环境用在哪里：界限 `t` 位于新绑定之外，在原有的 `γ` 中求值；只有公式体面对扩展 `x ∷ γ`。这两条子句正是「`t` 的每个成员都满足 `φ`」与「`t` 的某个成员满足 `φ`」这两种读法的语义内容。
<!--ja-->
偽には環境は不要である。`⊥̇` は空命題 `⊥` として読まれる。量化子は、台がついに登場する場所である。非有界の `∃̇ φ` は台の上の存在量化を表す。すなわち、`S` のある要素 `x` が拡張環境 `x ∷ γ` のもとで本体を成立させる、という命題である。対になる `∀̇ φ` は全称量化を表し、その証明は各 `x : S` に `x ∷ γ` のもとでの本体の証明を割り当てる関数である。本体の内側では位置 `zero` が候補 `x` を保持し、`γ` の成分は後続の位置へ移っている。外側の論理式で自由だった変数は末尾から読まれる。命題的切り詰めにより、存在量化はそのような要素が存在することを記録するだけで、要素そのものをデータとして運ばない。

有界の形はもう一つの成分を加える。限界の表示への所属である。`∀̇∈ t φ` は、`⟦ t ⟧ γ` への所属が本体を含意することを要求する。したがって `⟦ t ⟧ γ` のすべての元が `φ` を満たす。`∃̇∈ t φ` は、元でありかつ本体を満たす要素を求める。それぞれの環境がどこで使われるかに注意してほしい。限界 `t` は新しい束縛の外側にあり、元の `γ` で評価される。拡張 `x ∷ γ` を見るのは本体だけである。この二つの節こそ、「`t` のすべての元が `φ` を満たす」「`t` のある元が `φ` を満たす」という読みの意味論的内容である。
<!--/-->

```agda
  γ ⊨ ⊥̇        = ⊥
  γ ⊨ (∃̇ φ)    = ∃[ x ∶ S ] (x ∷ γ) ⊨ φ
  γ ⊨ (∀̇ φ)    = ∀[ x ∶ S ] (x ∷ γ) ⊨ φ
  γ ⊨ (∀̇∈ t φ) = ∀[ x ∶ S ] (x ∈ˢ ⟦ t ⟧ γ) ⇒ ((x ∷ γ) ⊨ φ)
  γ ⊨ (∃̇∈ t φ) = ∃[ x ∶ S ] (x ∈ˢ ⟦ t ⟧ γ) ⊓ ((x ∷ γ) ⊨ φ)
```

<!--en-->
## Predicates presented by formulas

A host predicate on a type of indices is not automatically a predicate that the object language can express. The following package records the missing bridge. It gives one formula, an environment for each index, the host predicate being presented, and a checked equality identifying that predicate with satisfaction. The constant interpretation is fixed outside the package, while the arity is part of the data because it determines the length of every environment.
<!--zh-->
## 由公式呈现的谓词

指标类型上的宿主谓词不会自动成为对象语言能够表达的谓词。下面的包记录了缺少的桥梁：它给出一条公式、每个指标对应的环境、所呈现的宿主谓词，以及一条经过检查的等式，把该谓词与满足关系识别起来。常元解释固定在包外，而元数属于数据的一部分，因为它决定每个环境的长度。
<!--ja-->
## 論理式によって表示される述語

添字型上のホスト述語が、自動的に対象言語で表現できる述語になるわけではない。次のパッケージは、その間に欠けている橋を記録する。一つの論理式、各添字に対応する環境、表示されるホスト述語、そしてその述語を充足と同一視する検査済みの等式を与える。定数解釈はパッケージの外で固定し、アリティは各環境の長さを決めるのでデータの一部に含める。
<!--/-->

```agda
record FormulaPredicate {ℓa ℓc} (A : Type ℓa) (K : Type ℓc)
                        (ι : K → S) (predicate : A → hProp ℓ)
    : Type (ℓ-max ℓa (ℓ-max ℓc (ℓ-suc ℓ))) where
  constructor presented
  field
    arity       : ℕ
    formula     : Formula K arity
    environment : A → S ^ arity
    reading     : (a : A) → predicate a ≡ At._⊨_ K ι (environment a) formula
```

<!--en-->
When classical logic is available, deciding a satisfaction judgment should retain the syntax that identifies the proposition being decided. `decideSatisfaction` is the small boundary for that purpose: excluded middle is applied internally, while the public arguments still display the interpretation, environment, and formula.
<!--zh-->
当经典逻辑可用时，对满足判断作判定仍应保留标识被判定命题的句法。`decideSatisfaction` 正是这道小边界：排中律在其内部应用，而公开实参仍明确展示解释、环境与公式。
<!--ja-->
古典論理が利用できるときも、充足判断の判定には、何を判定しているかを特定する構文を残すべきである。`decideSatisfaction` はそのための小さな境界であり、排中律は内部で適用される一方、公開された引数には解釈、環境、論理式が明示される。
<!--/-->

```agda
decideSatisfaction : ∀ {ℓc n} {K : Type ℓc} (ι : K → S)
                   → LEM ℓ → (γ : S ^ n) → (φ : Formula K n)
                   → Dec ⟨ At._⊨_ K ι γ φ ⟩
decideSatisfaction ι lem γ φ = lem (At._⊨_ _ ι γ φ)
```

<!--en-->
The two atomic specializations make common model-facing decisions equally explicit. Their formulas contain no constants: the two carrier arguments occupy the first and second variable slots, and satisfaction computes directly to the structure's membership or equality proposition.
<!--zh-->
两个原子特化使常见的面向模型判定同样明确。它们的公式不含常元：两个载体实参占据第一、第二变元槽，而满足关系直接计算为结构的隶属或等词命题。
<!--ja-->
二つの原子的な特殊化により、モデルに面するよく使う判定も同様に明示される。論理式は定数を含まず、二つの台の引数が第一・第二の変数枠を占め、充足は構造の所属または等号の命題へ直接計算される。
<!--/-->

```agda
decideMembership : LEM ℓ → (x y : S) → Dec ⟨ x ∈ˢ y ⟩
decideMembership lem x y =
  decideSatisfaction {K = ⊥* {ℓ}} (⊥*-rec {A = S}) lem
    (x ∷ y ∷ []) (var zero ∈̇ var (suc zero))

decideEquality : LEM ℓ → (x y : S) → Dec ⟨ x ≈ˢ y ⟩
decideEquality lem x y =
  decideSatisfaction {K = ⊥* {ℓ}} (⊥*-rec {A = S}) lem
    (x ∷ y ∷ []) (var zero ≐ var (suc zero))
```

<!--en-->
The field `reading` is deliberately an equality of proposition-valued meanings, not an informal assertion that the two sides correspond. It can therefore rewrite proofs in either direction. A consumer that performs a classical search may still use excluded middle internally, but its public model-facing input can now require this package and thereby expose the formula and environment whose satisfaction is being decided.
<!--zh-->
字段 `reading` 特意取为命题值意义之间的等式，而不是声称两边相应的一句非形式说明。因此它能在两个方向上改写证明。执行经典搜索的使用方内部仍可使用排中律，但其面向模型的公开输入如今可以要求这个包，从而显式交出被判定的满足命题所对应的公式与环境。
<!--ja-->
フィールド `reading` は、両辺が対応するという非形式的な主張ではなく、命題値の意味どうしの等式としている。そのため証明をどちらの向きにも書き換えられる。古典的探索を行う利用側は内部で排中律を使ってよいが、モデルに面する公開入力にはこのパッケージを要求でき、判定される充足命題の論理式と環境を明示できる。
<!--/-->

<!--en-->
## Recap

Meaning is compositional. A term denotes a carrier element, determined by the constant interpretation and the environment. A formula of arity `n` determines a function `S ^ n → hProp ℓ`{.Agda}, whether or not it uses every available position. The atoms consult the structure's two relations; the connectives apply the propositional operations of the host; the quantifiers let a fresh front position range over the carrier, and the bounded forms test membership in the denotation of the bound outside the extension while interpreting the body inside it. Every clause is one step of structural recursion. `FormulaPredicate` packages a host predicate together with this syntactic and semantic presentation. The construction uses the carrier `S` and the two relations `∈ˢ` and `≈ˢ`; it does not use the proof `isSetS` or any set-theoretic axiom.
<!--zh-->
## 小结

语义按组成方式给出。词项指称一个载体元素，由常元解释与环境共同确定。元数为 `n` 的公式确定一个 `S ^ n → hProp ℓ`{.Agda} 型的函数，无论它是否用尽每个可用位置。原子式查询结构的两个关系；联结词应用宿主的命题运算；量词让一个置于最前的新位置遍及载体，有界形式则在扩展之外检验属于界限指称的成员资格，在扩展之内解释公式体。每条子句都是结构递归的一步。`FormulaPredicate` 把宿主谓词连同这份句法与语义呈现一起打包。整个构造使用载体 `S` 以及关系 `∈ˢ`、`≈ˢ`，不使用证明 `isSetS`，也不使用任何集合论公理。
<!--ja-->
## まとめ

意味は合成的に与えられる。項は台の要素を表示し、それを決めるのは定数解釈と環境である。アリティ `n` の論理式は、利用できる位置を使い切るかどうかにかかわらず、`S ^ n → hProp ℓ`{.Agda} 型の関数を定める。原子式は構造の二つの関係に問い合わせ、結合子はホストの命題演算を適用する。量化子は先頭に置かれた新しい位置を台の上に動かし、有界の形は拡張の外で限界の表示への所属を確かめ、拡張の内で本体を解釈する。どの節も構造的再帰の一段である。`FormulaPredicate` はホスト述語をこの構文的・意味論的表示とともにパッケージ化する。構成が使うのは台 `S` と二つの関係 `∈ˢ`、`≈ˢ` であり、証明 `isSetS` も集合論の公理も使わない。
<!--/-->
