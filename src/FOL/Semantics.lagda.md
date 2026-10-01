```agda
{-# OPTIONS --cubical --safe --guardedness #-}
```

<!--en-->
# Semantics
<!--zh-->
# 语义
<!--ja-->
# 意味論
<!--/-->

```agda
open import FOL.ZFStructure using ( ZFStructure; ZFStructureₕ )
```

<!--en-->
Fix a proposition-valued structure `𝒮 : ZFStructureₕ ℓ`{.Agda}. Its carrier supplies the objects under discussion, and its two relations interpret equality and membership.
<!--zh-->
固定命题值结构 `𝒮 : ZFStructureₕ ℓ`{.Agda}。以它的载体元素为讨论对象，以它的两个关系解释相等和成员关系。
<!--ja-->
命題値構造 `𝒮 : ZFStructureₕ ℓ`{.Agda} を固定する。その台の要素を議論の対象とし、二つの関係で等号と所属を解釈する。
<!--/-->

```agda
module FOL.Semantics {ℓ} (𝒮 : ZFStructureₕ ℓ) where
```

```agda
open import Base.Prelude
open import Base.Classical using ( LEM )
open import FOL.Syntax using
  ( Term; con; var
  ; Formula; _∈̇_; _≐_; _∧̇_; _∨̇_; _⇒̇_; ⊥̇; ∃̇_; ∀̇_; ∀̇∈; ∃̇∈ )
```

<!--en-->
We now have both a language for writing claims and a structure in which to read them. This chapter connects the two: first we specify which objects the names and numbered positions refer to, then interpret each formula as a proposition about those objects. Giving a claim this meaning is different from deciding whether it holds; the final section explains what excluded middle adds.

Open the fixed structure to use its carrier `S`{.Agda} and relations `≈ˢ`{.Agda} and `∈ˢ`{.Agda} directly. No set-theoretic axioms are assumed.
<!--zh-->
我们已经有了写出陈述的语言，也有了解释这些陈述所需的结构。本章把二者接起来：先指定名字和带编号的位置各自指向什么对象，再把每条公式解释成关于这些对象的命题。赋予陈述含义，与判定它是否成立，是不同的两步；最后一节再说明排中律在判定中起什么作用。

打开已固定的结构，便可直接使用载体 `S`{.Agda}，以及关系 `≈ˢ`{.Agda} 和 `∈ˢ`{.Agda}。这里不假设任何集合论公理。
<!--ja-->
主張を書くための言語と、それを解釈するための構造がそろった。本章では両者を結び付ける。まず名前や番号付きの位置がどの対象を指すかを定め、次に各論理式を、それらの対象についての命題として解釈する。主張に意味を与えることと、その主張が成り立つかを判定することは別である。最後の節で、判定に排中律がどう使われるかを説明する。

固定した構造を開き、台 `S`{.Agda} と関係 `≈ˢ`{.Agda}、`∈ˢ`{.Agda} を直接使えるようにする。集合論の公理は仮定しない。
<!--/-->

```agda
open ZFStructure 𝒮
```

<!--en-->
## Environments

A variable position tells us where to look, but not what we will find there. An **[environment]{.term-intro #variable-environment}** assigns a carrier element to each available position. For a context of length `n`{.Agda}, we use a vector of length `n`{.Agda}; its entry at position `i : Fin n`{.Agda} is the value of that variable.

Environments therefore have type `Vec S n`{.Agda}.
<!--zh-->
## 环境

变元位置只说明去哪里取值，还没有说明那里放着什么。为每个可用位置指定一个载体元素，就得到一个**[环境]{.term-intro #variable-environment}**。语境长度为 `n`{.Agda} 时，我们用长度同为 `n`{.Agda} 的向量记录这些值；位置 `i : Fin n`{.Agda} 处的分量，就是相应变元的取值。

因此，环境的类型是 `Vec S n`{.Agda}。
<!--ja-->
## 環境

変数位置は値を取り出す場所を示すだけで、そこに何が入るかはまだ決めていない。利用できる各位置に台の要素を割り当てたものを**[環境]{.term-intro #variable-environment}**という。長さ `n`{.Agda} の文脈には、同じ長さのベクトルを使う。位置 `i : Fin n`{.Agda} にある成分が、その変数の値である。

したがって、環境の型は `Vec S n`{.Agda} となる。
<!--/-->

<!--en-->
For example, `a ∷ b ∷ []`{.Agda} supplies two values: position `0` holds `a`{.Agda}, and position `1` holds `b`{.Agda}. A term may use either position or neither. As in the syntax chapter, the length records the available positions, not the number of occurrences in an expression.
<!--zh-->
例如，`a ∷ b ∷ []`{.Agda} 提供两个取值：`0` 号位置存放 `a`{.Agda}，`1` 号位置存放 `b`{.Agda}。一个词项可以使用其中任意一个位置，也可以都不使用。与语法中的约定一样，长度记录的是可用位置的数量，而不是表达式中变元出现的次数。
<!--ja-->
たとえば `a ∷ b ∷ []`{.Agda} は二つの値を与える。`0` 番の位置に `a`{.Agda}、`1` 番の位置に `b`{.Agda} が入る。項はどちらかの位置を使っても、両方とも使わなくてもよい。構文の場合と同じく、長さが表すのは使える位置の数であり、式の中で変数が現れる回数ではない。
<!--/-->

<!--en-->
## Interpreting terms and formulas

Constant names need values too. A **[constant interpretation]{.term-intro #constant-interpretation}** is a function `ι : K → S`{.Agda}, assigning a carrier element to each name. Unlike variable values, these assignments remain fixed when a quantifier extends the environment. The submodule `At`{.Agda} fixes `K : Type ℓc`{.Agda} and `ι : K → S`{.Agda} for the definitions that follow.
<!--zh-->
## 解释词项与公式

常元名也需要指定取值。函数 `ι : K → S`{.Agda} 为每个名字指定一个载体元素，称为**[常元解释]{.term-intro #constant-interpretation}**。它与变元取值的区别在于：量词扩展环境时，常元的取值保持不变。子模块 `At`{.Agda} 固定 `K : Type ℓc`{.Agda} 和 `ι : K → S`{.Agda}，供下面的定义共同使用。
<!--ja-->
## 項と論理式の解釈

定数名にも値を与える必要がある。各名前に台の要素を割り当てる関数 `ι : K → S`{.Agda} を**[定数解釈]{.term-intro #constant-interpretation}**という。変数の値とは異なり、量化子によって環境が拡張されても、定数の値は変わらない。部分モジュール `At`{.Agda} で `K : Type ℓc`{.Agda} と `ι : K → S`{.Agda} を固定し、以下の定義で共通に使う。
<!--/-->

<details open class="submodule-fold">
<summary class="submodule-fold-heading">
```agda
module At {ℓc} (K : Type ℓc) (ι : K → S) where
```
</summary>
<div class="submodule-fold-content">

<!--en-->
### [Term evaluation]{.term-intro #term-evaluation}

**Definition** (`⟦_⟧`{.Agda}) Term evaluation assigns to `t : Term K n`{.Agda} and `γ : Vec S n`{.Agda} an element `⟦ t ⟧ γ : S`{.Agda}, read as the value of `t`{.Agda} under `γ`{.Agda}. A constant takes its value from `ι`{.Agda}; a variable takes its value from `γ`{.Agda}.
<!--zh-->
### [词项求值]{.term-intro #term-evaluation}

**定义** (`⟦_⟧`{.Agda}) 词项求值将词项 `t : Term K n`{.Agda} 与环境 `γ : Vec S n`{.Agda} 映到载体元素 `⟦ t ⟧ γ : S`{.Agda}，读作「`t`{.Agda} 在 `γ`{.Agda} 下的值」。常元从 `ι`{.Agda} 取值，变元从 `γ`{.Agda} 取值。
<!--ja-->
### [項の評価]{.term-intro #term-evaluation}

**定義** (`⟦_⟧`{.Agda}) 項の評価は、項 `t : Term K n`{.Agda} と環境 `γ : Vec S n`{.Agda} に台の要素 `⟦ t ⟧ γ : S`{.Agda} を対応させる。「`γ`{.Agda} のもとでの `t`{.Agda} の値」と読む。定数の値は `ι`{.Agda} から、変数の値は `γ`{.Agda} から得る。
<!--/-->

```agda
  ⟦_⟧ : ∀ {n} → Term K n → Vec S n → S
  ⟦ con k ⟧ γ = ι k
  ⟦ var i ⟧ γ = lookup i γ
```

<!--en-->
The common index `n`{.Agda} requires the environment to have exactly the length expected by the term. If `K`{.Agda} is the carrier itself, `ι = id`{.Agda} lets each element name itself. If `K`{.Agda} is empty, no constant case can arise; variable values still come from the environment. These choices are independent of the context length.

### [Satisfaction]{.term-intro #formula-satisfaction}

**Definition** (`_⊨_`{.Agda}) The satisfaction relation assigns to `γ : Vec S n`{.Agda} and `φ : Formula K n`{.Agda} a proposition `γ ⊨ φ : hProp ℓ`{.Agda}. We read it as `γ`{.Agda} satisfies `φ`{.Agda}; an element of `⟨ γ ⊨ φ ⟩`{.Agda} is a proof that the formula holds under that assignment. Define this proposition recursively on the formula as follows.
<!--zh-->
共同的下标 `n`{.Agda} 要求环境长度恰好与词项所需的语境长度一致。若常元域就是载体本身，可以取 `ι = id`{.Agda}，让每个元素以自身为名字；若常元域为空，就不可能出现常元情形，但变元仍从环境取值。这两种选择都与语境长度无关。

### [满足关系]{.term-intro #formula-satisfaction}

**定义** (`_⊨_`{.Agda}) 满足关系将环境 `γ : Vec S n`{.Agda} 与公式 `φ : Formula K n`{.Agda} 映到命题 `γ ⊨ φ : hProp ℓ`{.Agda}，读作「`γ`{.Agda} 满足 `φ`{.Agda}」。`⟨ γ ⊨ φ ⟩`{.Agda} 的元素就是该公式在此取值下成立的证明。按公式的构造方式递归定义这个命题如下。
<!--ja-->
共通の添字 `n`{.Agda} により、環境の長さは項が必要とする文脈の長さと一致する。定数域を台そのものに取れば、`ι = id`{.Agda} として各要素を自分自身の名前にできる。定数域が空なら定数の場合は生じないが、変数の値は引き続き環境から得る。どちらの選択も文脈の長さとは独立である。

### [充足関係]{.term-intro #formula-satisfaction}

**定義** (`_⊨_`{.Agda}) 充足関係は、環境 `γ : Vec S n`{.Agda} と論理式 `φ : Formula K n`{.Agda} に命題 `γ ⊨ φ : hProp ℓ`{.Agda} を対応させる。「`γ`{.Agda} は `φ`{.Agda} を満たす」と読み、`⟨ γ ⊨ φ ⟩`{.Agda} の要素は、その割当のもとで式が成り立つことの証明である。この命題を、論理式の構成に沿って次のように再帰的に定める。
<!--/-->

```agda
  infix 6 _⊨_
  _⊨_ : ∀ {n} → Vec S n → Formula K n → hProp ℓ
```

<!--en-->
For an atomic formula, evaluate the two terms and apply the corresponding relation of the structure: `∈̇`{.Agda} uses `∈ˢ`{.Agda}, and `≐`{.Agda} uses `≈ˢ`{.Agda}.
<!--zh-->
对于原子公式，先求出两个词项的值，再应用结构中的相应关系：`∈̇`{.Agda} 对应 `∈ˢ`{.Agda}，`≐`{.Agda} 对应 `≈ˢ`{.Agda}。
<!--ja-->
原子論理式では、まず二つの項を評価し、構造の対応する関係を適用する。`∈̇`{.Agda} には `∈ˢ`{.Agda}、`≐`{.Agda} には `≈ˢ`{.Agda} を使う。
<!--/-->

```agda
  γ ⊨ (t ∈̇ u)  = ⟦ t ⟧ γ ∈ˢ ⟦ u ⟧ γ
  γ ⊨ (t ≐ u)  = ⟦ t ⟧ γ ≈ˢ ⟦ u ⟧ γ
```

<!--en-->
For conjunction, disjunction and implication, interpret the two subformulas in the same environment, then combine the resulting propositions with the corresponding operation from the Prelude.
<!--zh-->
对于合取、析取和蕴涵，在同一环境下解释两个子公式，再用《基础词汇》中相应的命题运算组合所得结果。
<!--ja-->
連言・選言・含意では、二つの部分式を同じ環境で解釈し、得られた命題を「基礎語彙」の対応する演算で組み合わせる。
<!--/-->

```agda
  γ ⊨ (φ ∧̇ ψ)  = (γ ⊨ φ) ⊓ (γ ⊨ ψ)
  γ ⊨ (φ ∨̇ ψ)  = (γ ⊨ φ) ⊔ (γ ⊨ ψ)
  γ ⊨ (φ ⇒̇ ψ)  = (γ ⊨ φ) ⇒ (γ ⊨ ψ)
```

<!--en-->
Falsity always yields `⊥`{.Agda}. An unbounded quantifier ranges over `x : S`{.Agda} and interprets its body in `x ∷ γ`{.Agda}, with the new value at the front. The existential asks that such a value merely exist; the universal requires the body to hold for every value.
<!--zh-->
假始终解释为 `⊥`{.Agda}。无界量词遍历 `x : S`{.Agda}，把当前的值加到环境最前面，在 `x ∷ γ`{.Agda} 下解释公式体。存在量词断言这样的取值仅仅存在；全称量词要求每个取值都使公式体成立。
<!--ja-->
偽は常に `⊥`{.Agda} と解釈する。非有界量化子では `x : S`{.Agda} を動かし、その値を先頭に加えた `x ∷ γ`{.Agda} のもとで本体を解釈する。存在量化子はそのような値が単に存在することを述べ、全称量化子はどの値でも本体が成り立つことを求める。
<!--/-->

```agda
  γ ⊨ ⊥̇        = ⊥
  γ ⊨ (∃̇ φ)    = ∃[ x ∶ S ] (x ∷ γ) ⊨ φ
  γ ⊨ (∀̇ φ)    = ∀[ x ∶ S ] (x ∷ γ) ⊨ φ
```

<!--en-->
For bounded quantifiers, evaluate the bound `t`{.Agda} in the original environment. Universal quantification requires membership in that value to imply the body; existential quantification requires membership and the body together. Only the body uses the extended environment.
<!--zh-->
对于有界量词，先在原环境下求出界限词项 `t`{.Agda} 的值。全称情形要求：属于该值就蕴含公式体成立；存在情形要求：成员关系与公式体同时成立。只有公式体使用扩展后的环境。
<!--ja-->
有界量化子では、限界を表す項 `t`{.Agda} をもとの環境で評価する。全称の場合は、その値に属するならば本体が成り立つことを求める。存在の場合は、所属と本体がともに成り立つことを求める。拡張した環境を使うのは本体だけである。
<!--/-->

```agda
  γ ⊨ (∀̇∈ t φ) = ∀[ x ∶ S ] (x ∈ˢ ⟦ t ⟧ γ) ⇒ ((x ∷ γ) ⊨ φ)
  γ ⊨ (∃̇∈ t φ) = ∃[ x ∶ S ] (x ∈ˢ ⟦ t ⟧ γ) ⊓ ((x ∷ γ) ⊨ φ)
```
</div>
</details>

<!--en-->
These clauses give every formula a meaning without deciding its truth. The equality clause uses the supplied relation `≈ˢ`{.Agda}, not necessarily Agda path equality. Disjunction and existential quantification use propositional truncation, so their proofs do not in general provide a branch or a witness that can be extracted as data. None of these clauses requires excluded middle.

### Reading a quantified formula

The extra position in a quantifier's body now receives a value. Take the outer environment `γ = a ∷ []`{.Agda}. Prepending `x`{.Agda} produces `x ∷ a ∷ []`{.Agda}: the old value is preserved, while its index shifts. The figure shows the same position convention as in the object-language chapter, now with actual values supplied by an environment.
<!--zh-->
这些子句为每条公式赋予含义，并没有判定它的真假。相等子句采用给定的关系 `≈ˢ`{.Agda}，不一定是 Agda 的路径相等。析取与存在量化使用命题截断，因此一般不能从它们的证明中取出具体的分支或见证作为数据。以上定义都不需要排中律。

### 读懂量化公式

量词在公式体中增加的位置，现在有了取值。以外层环境 `γ = a ∷ []`{.Agda} 为例，在最前面加入 `x`{.Agda} 后，得到 `x ∷ a ∷ []`{.Agda}：原来的值保留不变，只是编号向后挪了一位。下图沿用《对象语言》的位置约定，但这次由环境实际提供各处的值。
<!--ja-->
これらの節は各論理式に意味を与えるが、その真偽を判定するわけではない。等号の節が使うのは与えられた関係 `≈ˢ`{.Agda} であり、Agda のパスによる等しさとは限らない。選言と存在量化は命題的切り詰めを使うため、その証明から分岐や証人をデータとして取り出せるとは一般にはいえない。ここまでの定義に排中律は要らない。

### 量化された論理式を読む

量化子の本体に増やした位置にも、これで値が入る。外側の環境を `γ = a ∷ []`{.Agda} とすると、先頭に `x`{.Agda} を加えた環境は `x ∷ a ∷ []`{.Agda} になる。もとの値はそのままで、番号だけが一つ後ろへずれる。次の図は「対象言語」と同じ位置の規則を、環境が与える値とともに示している。
<!--/-->

<figure class="book-diagram quantifier-context-figure" id="fig-semantics-environment" aria-describedby="fig-semantics-environment-caption">
<div class="diagram-framed">
<div class="quantifier-context-scene" aria-hidden="true">
<svg class="quantifier-context-geometry" viewBox="0 0 360 275" aria-hidden="true" focusable="false">
<rect class="diagram-space-shape quantifier-context-space" x="28" y="105" width="112" height="112"/>
<rect class="diagram-space-shape quantifier-context-space" x="205" y="74" width="126" height="174"/>
<path class="diagram-guide quantifier-context-divider" d="M218 162 H318"/>
<path class="diagram-map-line quantifier-context-old-path" d="M110 161 C159 161 167 205 247 205"/>
<path class="diagram-map-tip quantifier-context-old-tip" d="M238 199 L248 205 L238 211"/>
<path class="diagram-map-line quantifier-context-new-path" d="M187 98 C215 99 217 128 247 128"/>
<path class="diagram-map-tip quantifier-context-new-tip" d="M238 122 L248 128 L238 134"/>
<circle class="diagram-point quantifier-context-insert" cx="169" cy="98" r="18"/>
<circle class="diagram-point quantifier-context-old-node" cx="85" cy="161" r="25"/>
<circle class="diagram-point quantifier-context-new-node" cx="273" cy="128" r="25"/>
<circle class="diagram-point quantifier-context-old-node" cx="273" cy="205" r="25"/>
</svg>
<span class="quantifier-context-label quantifier-context-heading" style="left:23.33%;top:16.36%">$\gamma$</span>
<span class="quantifier-context-label quantifier-context-heading" style="left:74.17%;top:16.36%">$x\mathbin{∷}\gamma$</span>
<span class="quantifier-context-label quantifier-context-plus" style="left:46.94%;top:35.64%">$+$</span>
<span class="quantifier-context-label quantifier-context-value" style="left:23.61%;top:58.55%">$a$</span>
<span class="quantifier-context-label quantifier-context-value quantifier-context-new-value" style="left:75.83%;top:46.55%">$x$</span>
<span class="quantifier-context-label quantifier-context-value" style="left:75.83%;top:74.55%">$a$</span>
<span class="quantifier-context-label quantifier-context-index" style="left:13.05%;top:58.55%">$0$</span>
<span class="quantifier-context-label quantifier-context-index" style="left:87.5%;top:46.55%">$0$</span>
<span class="quantifier-context-label quantifier-context-index" style="left:87.5%;top:74.55%">$1$</span>
</div>
</div>
<figcaption id="fig-semantics-environment-caption">
<!--en-->
The extended environment puts the quantified value at position `0` and preserves the old value at position `1`
<!--zh-->
扩展后的环境把量化取值放在 `0` 号位置，把原有取值保留在 `1` 号位置
<!--ja-->
拡張した環境では、量化する値が `0` 番に入り、もとの値は `1` 番に残る
<!--/-->
</figcaption>
</figure>

<!--en-->
For a concrete example, let the body be `var zero ∈̇ var (suc zero)`{.Agda}. In the extended environment it means `x ∈ˢ a`{.Agda}. Prefixing `∀̇`{.Agda} therefore says that every carrier element belongs to `a`{.Agda}; prefixing `∃̇`{.Agda} says that some carrier element belongs to `a`{.Agda}. Neither is asserted to hold: the example identifies the proposition expressed by each formula.

For a bounded quantifier, the bound still refers to the old environment. In `∀̇∈ (var zero) φ`{.Agda}, the bound denotes `a`{.Agda}, but the first position inside `φ`{.Agda} denotes `x`{.Agda}. This is why the code evaluates the bound in the original environment. Finally, negation and truth need no extra clauses: their definitions in the object language already expand into implication and falsity.
<!--zh-->
取一个具体的公式体 `var zero ∈̇ var (suc zero)`{.Agda}，它在扩展环境下表达的就是 `x ∈ˢ a`{.Agda}。在前面加上 `∀̇`{.Agda}，就表示每个载体元素都属于 `a`{.Agda}；加上 `∃̇`{.Agda}，就表示存在一个属于 `a`{.Agda} 的载体元素。这里没有断言其中哪条成立，只是说明每条公式表达了什么命题。

有界量词的界限仍按原环境解释。在 `∀̇∈ (var zero) φ`{.Agda} 中，界限指的是 `a`{.Agda}，而 `φ`{.Agda} 内的首位指的是 `x`{.Agda}。这就是代码用原环境求界限值的原因。至于否定与真，无须另写子句：它们在对象语言中的定义已经展开为蕴涵与假。
<!--ja-->
具体的に、本体を `var zero ∈̇ var (suc zero)`{.Agda} とすると、拡張した環境での意味は `x ∈ˢ a`{.Agda} になる。前に `∀̇`{.Agda} を付ければ、台のどの要素も `a`{.Agda} に属するという命題になり、`∃̇`{.Agda} を付ければ、`a`{.Agda} に属する台の要素が存在するという命題になる。どちらかが成り立つと主張しているのではなく、それぞれの式が表す命題を確かめている。

有界量化子の限界は、もとの環境で解釈する。`∀̇∈ (var zero) φ`{.Agda} の限界は `a`{.Agda} を指すが、`φ`{.Agda} の内部の先頭位置は `x`{.Agda} を指す。このためコードでは、もとの環境で限界の値を求める。なお、否定と真には別の節を設けなくてよい。対象言語での定義を展開すると、含意と偽になるからである。
<!--/-->

<!--en-->
## Predicates presented by formulas

So far we have started with a formula and obtained a proposition. We can also start with a given predicate `predicate : A → hProp ℓ`{.Agda} and supply a formula presentation for it. Here `A`{.Agda} indexes the cases under consideration; it need not be the carrier. One formula is kept fixed, while an environment is supplied for each `a : A`{.Agda}.

**Definition** (`FormulaPredicate`{.Agda}) Given `A`{.Agda}, `K`{.Agda}, `ι`{.Agda} and `predicate`{.Agda}, a formula presentation consists of an arity, a formula of that arity, an environment for each index, and a proof that its meaning equals the given predicate at every index. The constructor is `presented`{.Agda}.
<!--zh-->
## 由公式呈现的谓词

到这里，我们都是从公式出发，得到它所表达的命题。反过来，也可以先给定谓词 `predicate : A → hProp ℓ`{.Agda}，再提供它的一份公式呈现。这里的 `A`{.Agda} 为要讨论的各个情形提供指标，不必就是载体。我们固定同一条公式，为每个 `a : A`{.Agda} 提供相应的环境。

**定义** (`FormulaPredicate`{.Agda}) 给定 `A`{.Agda}、`K`{.Agda}、`ι`{.Agda} 与 `predicate`{.Agda}。它的一份公式呈现由以下数据组成：元数、该元数上的公式、每个指标对应的环境，以及公式的含义逐点等于给定谓词的证明。构造子记作 `presented`{.Agda}。
<!--ja-->
## 論理式によって表示される述語

ここまでは論理式から出発し、それが表す命題を求めてきた。逆に、述語 `predicate : A → hProp ℓ`{.Agda} を先に与え、その論理式による表示を用意することもできる。`A`{.Agda} は考察する場合の添字の型であり、台と同じでなくてもよい。一つの論理式を固定し、各 `a : A`{.Agda} に環境を与える。

**定義** (`FormulaPredicate`{.Agda}) `A`{.Agda}、`K`{.Agda}、`ι`{.Agda}、`predicate`{.Agda} を与える。その論理式による表示は、アリティ、そのアリティの論理式、各添字に対応する環境、および各添字で論理式の意味が与えられた述語と等しいことの証明からなる。構成子を `presented`{.Agda} とする。
<!--/-->

```agda
record FormulaPredicate {ℓa ℓc} (A : Type ℓa) (K : Type ℓc)
                        (ι : K → S) (predicate : A → hProp ℓ)
    : Type (ℓ-max ℓa (ℓ-max ℓc (ℓ-suc ℓ))) where
  constructor presented
```

<!--en-->
The fields record these four components in order. The arity `arity`{.Agda} counts available variable positions, just as the index `n`{.Agda} did above. In `reading`{.Agda}, the local module name `I`{.Agda} selects the interpretation `At K ι`{.Agda}; thus `environment a I.⊨ formula`{.Agda} is the formula's meaning in the environment assigned to `a`{.Agda}.
<!--zh-->
下面四个字段依次记录这些数据。元数 `arity`{.Agda} 与前面的下标 `n`{.Agda} 一样，表示可用变元位置的数量。`reading`{.Agda} 中的局部模块名 `I`{.Agda} 指定解释 `At K ι`{.Agda}；因此，`environment a I.⊨ formula`{.Agda} 就是公式在 `a`{.Agda} 所对应环境下的含义。
<!--ja-->
次の四つのフィールドが、これらのデータを順に記録する。アリティ `arity`{.Agda} は、これまでの添字 `n`{.Agda} と同じく、使える変数位置の数を表す。`reading`{.Agda} 内の局所的なモジュール名 `I`{.Agda} は解釈 `At K ι`{.Agda} を指定する。したがって `environment a I.⊨ formula`{.Agda} は、`a`{.Agda} に割り当てた環境での論理式の意味である。
<!--/-->

```agda
  field
    arity       : ℕ
    formula     : Formula K arity
    environment : A → Vec S arity
    reading     : (a : A) → let module I = At K ι in predicate a ≡ (environment a I.⊨ formula)
```

<!--en-->
For example, fix `a : S`{.Agda} and consider the predicate `λ x → x ∈ˢ a`{.Agda}. It has a presentation using the formula `var zero ∈̇ var (suc zero)`{.Agda} and the environment `x ∷ a ∷ []`{.Agda} at each `x`{.Agda}. The arity is two, even though the predicate has one argument: the environment supplies both that argument and the fixed object. Evaluating the formula gives the predicate directly, so `reading`{.Agda} can use `refl`{.Agda}.

The predicate and constant interpretation are parameters, not additional fields. The field `reading`{.Agda} supplies a path between two `hProp ℓ`{.Agda} values; along it, proofs of the given predicate can be transported to proofs of satisfaction, and conversely. Neither the formula nor its environments need be unique.
<!--zh-->
例如，固定 `a : S`{.Agda}，考虑谓词 `λ x → x ∈ˢ a`{.Agda}。可以用公式 `var zero ∈̇ var (suc zero)`{.Agda} 呈现它，并为每个 `x`{.Agda} 配上环境 `x ∷ a ∷ []`{.Agda}。谓词只有一个实参，公式的元数却是二：环境同时提供变化的实参与固定的对象。公式求值后直接得到原谓词，因此 `reading`{.Agda} 可用 `refl`{.Agda} 证明。

待呈现的谓词与常元解释是参数，不是额外的字段。字段 `reading`{.Agda} 给出两个 `hProp ℓ`{.Agda} 值之间的路径；沿这条路径，可以把给定谓词的证明转换为满足关系的证明，也可以反向转换。公式与环境都不要求唯一。
<!--ja-->
たとえば `a : S`{.Agda} を固定し、述語 `λ x → x ∈ˢ a`{.Agda} を考える。論理式 `var zero ∈̇ var (suc zero)`{.Agda} を使い、各 `x`{.Agda} に環境 `x ∷ a ∷ []`{.Agda} を与えれば、この述語を表示できる。述語の引数は一つだが、論理式のアリティは二である。環境が、変化する引数と固定した対象の両方を与えるからである。論理式を解釈するとそのまま元の述語が得られるので、`reading`{.Agda} は `refl`{.Agda} で証明できる。

表示する述語と定数解釈はパラメータであり、追加のフィールドではない。`reading`{.Agda} は二つの `hProp ℓ`{.Agda} の値を結ぶパスを与える。それに沿って、与えられた述語の証明を充足の証明に移すことも、その逆もできる。論理式や環境の一意性は要求しない。
<!--/-->

<!--en-->
## Decisions under excluded middle

Interpreting a formula yields a proposition, not automatically a proof or a refutation. With `lem : LEM ℓ`{.Agda}, however, we can apply excluded middle to that proposition. The hypothesis is needed here, not in the preceding definitions.

**Lemma** (`decideSatisfaction`{.Agda}) Given a constant interpretation, an environment and a formula, `LEM ℓ`{.Agda} yields a decision of the formula's satisfaction proposition.

**Proof** Form the proposition with `At`{.Agda}, then apply `lem`{.Agda}. Keeping the formula and environment as arguments specifies exactly which proposition is being decided.
<!--zh-->
## 排中律下的判定

解释一条公式，得到的是命题，并不会自动得到它的证明或反驳。不过，若给定 `lem : LEM ℓ`{.Agda}，就能对这个命题应用排中律。这项假设用在此处，而不是前面的语义定义中。

**引理** (`decideSatisfaction`{.Agda}) 给定常元解释、环境与公式，`LEM ℓ`{.Agda} 给出相应满足命题的判定。

**证明** 用 `At`{.Agda} 得到该命题，再应用 `lem`{.Agda}。把公式与环境保留为实参，就明确记录了判定的对象。
<!--ja-->
## 排中律による判定

論理式を解釈して得られるのは命題であり、その証明や反証が自動的に得られるわけではない。ただし `lem : LEM ℓ`{.Agda} が与えられれば、その命題に排中律を適用できる。この仮定を使うのはここからであり、それまでの意味の定義には必要ない。

**補題** (`decideSatisfaction`{.Agda}) 定数解釈・環境・論理式が与えられたとき、`LEM ℓ`{.Agda} から対応する充足命題の判定が得られる。

**証明** `At`{.Agda} でその命題を定め、`lem`{.Agda} を適用する。論理式と環境を引数に残すことで、どの命題を判定しているかが明確になる。
<!--/-->

```agda
decideSatisfaction : ∀ {ℓc n} {K : Type ℓc} (ι : K → S)
                   → LEM ℓ → (γ : Vec S n) → (φ : Formula K n)
                   → let module I = At K ι in Dec ⟨ γ I.⊨ φ ⟩
decideSatisfaction ι lem γ φ = lem (γ I.⊨ φ)
  where module I = At _ ι
```

<!--en-->
The atomic cases make this correspondence concrete. Neither formula needs constant names, so take the empty constant domain `⊥* {ℓ}`{.Agda} and its eliminator as the interpretation. The environment `x ∷ y ∷ []`{.Agda} assigns the two objects to their respective positions.

**Corollary** (`decideMembership`{.Agda}) `LEM ℓ`{.Agda} decides membership between any two carrier elements.

**Proof** Apply the lemma to the atomic membership formula. Its two variables evaluate to `x`{.Agda} and `y`{.Agda}, so its meaning is precisely `x ∈ˢ y`{.Agda}.
<!--zh-->
两个原子情形让这种对应更具体。它们都不用常元名，因此取空常元域 `⊥* {ℓ}`{.Agda}，用空类型的消去函数作为解释。环境 `x ∷ y ∷ []`{.Agda} 将两个对象放在各自的位置。

**推论** (`decideMembership`{.Agda}) `LEM ℓ`{.Agda} 可判定任意两个载体元素之间的成员关系。

**证明** 将引理应用于成员关系原子公式。两个变元分别求值得到 `x`{.Agda} 和 `y`{.Agda}，所以公式的含义恰好是 `x ∈ˢ y`{.Agda}。
<!--ja-->
二つの原子的な場合で、この対応を具体的に確かめる。どちらの式にも定数名は要らないので、空の定数域 `⊥* {ℓ}`{.Agda} を取り、空型の除去関数を解釈に使う。環境 `x ∷ y ∷ []`{.Agda} が二つの対象をそれぞれの位置に割り当てる。

**系** (`decideMembership`{.Agda}) `LEM ℓ`{.Agda} により、台の任意の二要素の所属関係を判定できる。

**証明** 所属の原子論理式に補題を適用する。二つの変数の値はそれぞれ `x`{.Agda} と `y`{.Agda} なので、その意味はちょうど `x ∈ˢ y`{.Agda} である。
<!--/-->

```agda
decideMembership : LEM ℓ → (x y : S) → Dec ⟨ x ∈ˢ y ⟩
decideMembership lem x y =
  decideSatisfaction {K = ⊥* {ℓ}} (⊥*-rec {A = S}) lem
    (x ∷ y ∷ []) (var zero ∈̇ var (suc zero))
```

<!--en-->
**Corollary** (`decideEquality`{.Agda}) `LEM ℓ`{.Agda} decides the structure's equality relation between any two carrier elements.

**Proof** Use the equality atom with the same constant domain and environment. Its meaning is `x ≈ˢ y`{.Agda}, rather than a claim about Agda path equality.
<!--zh-->
**推论** (`decideEquality`{.Agda}) `LEM ℓ`{.Agda} 可判定任意两个载体元素之间由结构指定的相等关系。

**证明** 沿用相同的常元域与环境，改用相等原子公式。其含义是 `x ≈ˢ y`{.Agda}，而不是关于 Agda 路径相等的断言。
<!--ja-->
**系** (`decideEquality`{.Agda}) `LEM ℓ`{.Agda} により、台の任意の二要素について、構造が指定する等号の関係を判定できる。

**証明** 定数域と環境はそのままに、等号の原子論理式を使う。その意味は `x ≈ˢ y`{.Agda} であり、Agda のパスによる等しさについての主張ではない。
<!--/-->

```agda
decideEquality : LEM ℓ → (x y : S) → Dec ⟨ x ≈ˢ y ⟩
decideEquality lem x y =
  decideSatisfaction {K = ⊥* {ℓ}} (⊥*-rec {A = S}) lem
    (x ∷ y ∷ []) (var zero ≐ var (suc zero))
```

<!--en-->
## Recap

Constant interpretations and environments give terms their values; the structure's relations and the logical operations then give formulas their meanings. Quantifiers vary the new first entry while preserving the outer assignment. `FormulaPredicate`{.Agda} records a formula presentation of a given predicate, and excluded middle separately supplies decisions of satisfaction. Defining meaning itself requires neither excluded middle nor set-theoretic axioms. The next chapter returns to the written formulas and classifies them by the arrangement of their quantifiers.
<!--zh-->
## 小结

常元解释与环境确定词项的取值，结构中的关系与命题运算再确定公式的含义。量词改变新加入的首位取值，同时保留外层已有的取值。`FormulaPredicate`{.Agda} 记录给定谓词的一份公式呈现；排中律则进一步提供满足命题的判定。定义含义本身，既不需要排中律，也不需要集合论公理。下一章回到公式的写法，按量词的组成方式给公式分类。
<!--ja-->
## まとめ

定数解釈と環境が項の値を定め、構造の関係と命題の演算が論理式の意味を定める。量化子は新しく加えた先頭の値を動かし、外側の割当は保つ。`FormulaPredicate`{.Agda} は与えられた述語の論理式による表示を記録し、排中律はそれとは別に充足命題の判定を与える。意味を定義すること自体には、排中律も集合論の公理も要らない。次章では論理式の書き方に戻り、量化子の組み立て方に応じて分類する。
<!--/-->
