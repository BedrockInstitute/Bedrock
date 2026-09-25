```agda
{-# OPTIONS --cubical --safe --guardedness #-}
module Base.Impredicativity where
```

<!--en-->
# Impredicativity
<!--zh-->
# 非直谓性
<!--ja-->
# 非可述性
<!--/-->

```agda
open import Base.Prelude
```

<!--en-->

A predicative foundation does not allow quantification within a definition over a totality that already contains the object being defined. Cubical Agda has such a foundation, whereas the set theory formalized in this book contains impredicative constructions. This chapter therefore states the extra conditions needed for those constructions as explicit assumptions, without changing the foundation of the host.

A predicative foundation can accommodate impredicative assumptions just as intuitionistic logic can explicitly assume classical principles. The converse does not hold: once the stronger principles are built into the foundation, later results no longer reveal which of them they actually require. We therefore retain Cubical Agda's predicative foundation and name every impredicative condition at the point where it is used.
<!--zh-->

直谓主义数学基础不允许在一个定义中量化某个已经包含待定义对象的总体。Cubical Agda 建立在这样的基础之上，而本书所要形式化的集合论包含非直谓的构造。为了在直谓式的宿主中准确说明这些构造需要什么，本章专门提出一组接口：它们不改变宿主本身，而是把开展非直谓数学所需的额外条件明确列为假设。

直谓主义数学基础可以容纳这样的非直谓假设，正如直觉主义逻辑可以明确加入经典逻辑原理；反过来却不成立，因为一旦基础本身预先采用了更强的原则，就无法再分辨后续结果究竟依赖哪些额外假设。因此，本书保留 Cubical Agda 的直谓式基础，并在需要非直谓性时，通过本章的接口逐项说明所用的条件。
<!--ja-->

直謂的な基礎では、一つの定義の中で、定義される対象をすでに含む全体にわたって量化することを認めない。Cubical Agda はこのような基礎の上にあるが、本書で形式化する集合論には非可述的な構成が含まれる。そこで本章では、ホストの基礎そのものを変えずに、それらの構成に必要な追加条件を明示的な仮定として述べる。

直謂的な基礎が非可述的な仮定を受け入れられることは、直観主義論理が古典論理の原理を明示的に仮定できることに似ている。逆は成り立たない。強い原理を初めから基礎に組み込めば、後の結果がそのどれに依存するかを区別できなくなるからである。本書は Cubical Agda の直謂的な基礎を保ち、非可述性が必要な箇所で条件を一つずつ明記する。
<!--/-->

<!--en-->
The issue appears in the universe levels. All propositions whose [underlying types]{.term-ref #underlying-type} lie in `Type ℓ`{.Agda} form `hProp ℓ`{.Agda}, but this proposition universe as a whole belongs to `Type (ℓ-suc ℓ)`{.Agda}. A proposition obtained by quantifying over all of `hProp ℓ`{.Agda} need not fit at level `ℓ`{.Agda}.

For example, suppose we define a proposition `R`{.Agda} by saying that every `Q : hProp ℓ`{.Agda} implies itself, and also demand that `R`{.Agda} belong to `hProp ℓ`{.Agda}. Then the quantifier over every `Q`{.Agda} also ranges over `R`{.Agda}: the totality being quantified over already includes the proposition being defined. The claim that `Q`{.Agda} implies itself is elementary; the difficulty is the demand that this quantification produce a proposition at the same level. In Cubical Agda the quantification instead lives one universe higher. User code cannot rewrite Agda's universe-level rules, but an explicit assumption can connect the higher proposition to a lower representative with the same truth content.
<!--zh-->
困难来自宇宙层级。[底层类型]{.term-ref #underlying-type}位于 `Type ℓ`{.Agda} 的所有命题组成 `hProp ℓ`{.Agda}，而这个命题宇宙整体属于 `Type (ℓ-suc ℓ)`{.Agda}。因此，对 `hProp ℓ`{.Agda} 中所有命题量化所得的命题，不一定仍能放在层级 `ℓ`{.Agda}。

例如，试图把命题 `R`{.Agda} 定义为「每个 `Q : hProp ℓ`{.Agda} 都蕴含自身」，同时要求 `R`{.Agda} 也属于 `hProp ℓ`{.Agda}。这样，定义中的「每个 `Q`{.Agda}」也遍及 `R`{.Agda}：量化的总体已经包含正在定义的命题。「`Q`{.Agda} 蕴含自身」虽然显然成立，难点仍是要求这次量化所得的命题留在同一层级。在 Cubical Agda 中，它位于高一层的宇宙。Agda 的用户代码不能改写其宇宙层级规则，但可以通过显式假设，把这个高层命题与真值内容相同的低层代表联系起来。
<!--ja-->
問題は宇宙レベルに現れる。[基礎型]{.term-ref #underlying-type}が `Type ℓ`{.Agda} に属するすべての命題は `hProp ℓ`{.Agda} をなすが、この命題の宇宙全体は `Type (ℓ-suc ℓ)`{.Agda} に属する。したがって、`hProp ℓ`{.Agda} のすべての命題にわたる量化から得た命題が、再びレベル `ℓ`{.Agda} に収まるとは限らない。

例えば、命題 `R`{.Agda} を「すべての `Q : hProp ℓ`{.Agda} は自分自身を含意する」と定義し、同時に `R`{.Agda} も `hProp ℓ`{.Agda} に属すると要求してみる。このとき、定義中の「すべての `Q`{.Agda}」は `R`{.Agda} 自身にも及ぶ。量化する全体が、定義中の命題をすでに含んでいるのである。「`Q`{.Agda} は自分自身を含意する」という主張は明らかであるが、その量化から得た命題を同じレベルに置くという要求が問題である。Cubical Agda では、この量化は一つ上の宇宙に属する。Agda のユーザーコードから宇宙レベルの規則を書き換えることはできないが、明示的な仮定によって、上位の命題と真理内容が同じ下位の代表を結び付けられる。
<!--/-->

<!--en-->
We express this connection using the type equivalence `A ≃ B`{.Agda} introduced in the foundational vocabulary. It can relate types in different universes while preserving their elements and paths. There are two distinct size requirements: finding a representative for each proposition, and finding one type that represents an entire proposition universe.
<!--zh-->
我们用基础词汇中介绍的类型等价 `A ≃ B`{.Agda} 表达这种联系。它允许两个类型位于不同宇宙，同时保留其中的元素与路径。接下来要区分两种尺寸要求：逐个为命题寻找代表，以及用一个类型呈现整个命题宇宙。
<!--ja-->
この結び付きには、基礎語彙で導入した型同値 `A ≃ B`{.Agda} を使う。これは、異なる宇宙の型を、その要素とパスを保ちながら結び付けられる。以下では、各命題の代表を個別に求めることと、命題の宇宙全体を一つの型で提示することという、二つの大きさの要求を区別する。
<!--/-->

<!--en-->
## [Propositional resizing]{.term-intro #propositional-resizing}

Given `P : hProp ℓ₁`{.Agda}, Agda does not let us change the level at which `P`{.Agda} lives. What we can ask for is another proposition `Q : hProp ℓ₂`{.Agda} whose underlying type is connected to that of `P`{.Agda} by a [type equivalence]{.term-ref #type-equivalence}.

**Definition** (`hasSize`{.Agda}) We read `hasSize ℓ₂ P`{.Agda} as saying that `P`{.Agda} has size `ℓ₂`{.Agda}, and define it as the dependent pair below. Its first component chooses `Q`{.Agda}, and its second component gives the type equivalence showing that `Q`{.Agda} has exactly the truth content of `P`{.Agda}.
<!--zh-->
## [命题换级]{.term-intro #propositional-resizing}

给定 `P : hProp ℓ₁`{.Agda}，Agda 不允许我们直接改变 `P`{.Agda} 所在的层级；能够提出的要求，是在目标层级找到另一个命题 `Q : hProp ℓ₂`{.Agda}，使二者的底层类型[类型等价]{.term-ref #type-equivalence}。

**定义** (`hasSize`{.Agda}) 我们把「`P`{.Agda} 具有尺寸 `ℓ₂`{.Agda}」记作 `hasSize ℓ₂ P`{.Agda}，并将其定义为以下依值对：第一分量选出 `Q`{.Agda}，第二分量给出[类型等价]{.term-ref #type-equivalence}，表明 `Q`{.Agda} 与 `P`{.Agda} 具有完全相同的真值内容。
<!--ja-->
## [命題リサイズ]{.term-intro #propositional-resizing}

`P : hProp ℓ₁`{.Agda} が与えられても、Agda では `P`{.Agda} の属するレベルを直接変更できない。代わりに、目標レベルの別の命題 `Q : hProp ℓ₂`{.Agda} を見つけ、その基礎型が `P`{.Agda} の基礎型と[型同値]{.term-ref #type-equivalence}であることを要求できる。

**定義** (`hasSize`{.Agda}) ここでは「`P`{.Agda} はサイズ `ℓ₂`{.Agda} をもつ」を `hasSize ℓ₂ P`{.Agda} と表し、次の依存対として定義する。第一成分は `Q`{.Agda} を選び、第二成分は `Q`{.Agda} と `P`{.Agda} の真理内容が完全に一致することを示す[型同値]{.term-ref #type-equivalence}を与える。
<!--/-->

```agda
hasSize : ∀ {ℓ₁} (ℓ₂ : Level) → hProp ℓ₁ → Type (ℓ-max ℓ₁ (ℓ-suc ℓ₂))
hasSize ℓ₂ P = Σ[ Q ∈ hProp ℓ₂ ] (⟨ P ⟩ ≃ ⟨ Q ⟩)
```


<!--en-->
Neither level has to be larger than the other. In the applications below `ℓ₁`{.Agda} is usually the model's truth-value level and `ℓ₂`{.Agda} its indexing level, but the definition itself allows any two levels. The name "propositional resizing" refers to replacing a proposition by a type-equivalent representative at the chosen target level, rather than changing the universe annotation of the original proposition.
<!--zh-->
这里不要求两个层级有大小顺序。在后面的应用中，`ℓ₁`{.Agda} 通常是模型真值所在的层级，`ℓ₂`{.Agda} 是索引所在的层级；但定义本身允许任意两个层级。「命题换级」是指用目标层级中的[类型等价]{.term-ref #type-equivalence}代表替换原命题，而不是修改原命题的宇宙标注。
<!--ja-->
二つのレベルの大小関係は仮定しない。後の応用では通常、`ℓ₁`{.Agda} はモデルの真理値のレベル、`ℓ₂`{.Agda} は添字のレベルであるが、定義そのものは任意の二つのレベルに適用できる。「命題リサイズ」とは、元の命題の宇宙注釈を変更することではなく、目標レベルにある[型同値]{.term-ref #type-equivalence}な代表で置き換えることを指す。
<!--/-->

<!--en-->
**Definition** (`Resizing`{.Agda}) We read `Resizing ℓ₁ ℓ₂`{.Agda} as saying that propositions at level `ℓ₁`{.Agda} can be resized to level `ℓ₂`{.Agda}, and define it as the dependent function below. For each `P : hProp ℓ₁`{.Agda}, it returns a witness that `P`{.Agda} has size `ℓ₂`{.Agda}.
<!--zh-->
**定义** (`Resizing`{.Agda}) 我们把「`ℓ₁`{.Agda} 层的命题可换级到 `ℓ₂`{.Agda} 层」记作 `Resizing ℓ₁ ℓ₂`{.Agda}，并将其定义为以下[依值函数]{.term-ref #dependent-function}：对每个 `P : hProp ℓ₁`{.Agda}，它返回「`P`{.Agda} 具有尺寸 `ℓ₂`{.Agda}」的见证。
<!--ja-->
**定義** (`Resizing`{.Agda}) ここでは「レベル `ℓ₁`{.Agda} の命題をレベル `ℓ₂`{.Agda} へリサイズできる」を `Resizing ℓ₁ ℓ₂`{.Agda} と表し、次の依存関数として定義する。各 `P : hProp ℓ₁`{.Agda} に対して、「`P`{.Agda} はサイズ `ℓ₂`{.Agda} をもつ」ことの証拠を返す。
<!--/-->

```agda
Resizing : ∀ ℓ₁ ℓ₂ → Type (ℓ-max (ℓ-suc ℓ₁) (ℓ-suc ℓ₂))
Resizing ℓ₁ ℓ₂ = (P : hProp ℓ₁) → hasSize ℓ₂ P
```


<!--en-->
## [Ω-resizing]{.term-intro #proposition-universe-resizing}

**Definition** (`ΩResizing`{.Agda}) We read `ΩResizing ℓ₁ ℓ₂`{.Agda} as saying that the proposition universe `hProp ℓ₁`{.Agda} has size `ℓ₂`{.Agda}, and define it as the dependent pair below. Its first component chooses a type `Ω : Type ℓ₂`{.Agda}; its second gives a [type equivalence]{.term-ref #type-equivalence} `hProp ℓ₁ ≃ Ω`{.Agda}. Thus every proposition at `ℓ₁`{.Agda} has a code in `Ω`{.Agda}, and every element of `Ω`{.Agda} decodes to such a proposition.
<!--zh-->
## [命题宇宙换级]{.term-intro #proposition-universe-resizing}

**定义** (`ΩResizing`{.Agda}) 我们把「命题宇宙 `hProp ℓ₁`{.Agda} 具有尺寸 `ℓ₂`{.Agda}」记作 `ΩResizing ℓ₁ ℓ₂`{.Agda}，并将其定义为以下依值对：第一分量给出类型 `Ω : Type ℓ₂`{.Agda}，第二分量给出[类型等价]{.term-ref #type-equivalence} `hProp ℓ₁ ≃ Ω`{.Agda}。因此，`ℓ₁`{.Agda} 层的每个命题都在 `Ω`{.Agda} 中有编码，而 `Ω`{.Agda} 的每个元素也都解码为该层的命题。
<!--ja-->
## [命題宇宙リサイズ]{.term-intro #proposition-universe-resizing}

**定義** (`ΩResizing`{.Agda}) ここでは「命題宇宙 `hProp ℓ₁`{.Agda} はサイズ `ℓ₂`{.Agda} をもつ」を `ΩResizing ℓ₁ ℓ₂`{.Agda} と表し、次の依存対として定義する。第一成分は型 `Ω : Type ℓ₂`{.Agda} を与え、第二成分は[型同値]{.term-ref #type-equivalence} `hProp ℓ₁ ≃ Ω`{.Agda} を与える。したがって、レベル `ℓ₁`{.Agda} の各命題は `Ω`{.Agda} に符号をもち、`Ω`{.Agda} の各要素はそのレベルの命題へ復号される。
<!--/-->

```agda
ΩResizing : ∀ ℓ₁ ℓ₂ → Type (ℓ-max (ℓ-suc ℓ₁) (ℓ-suc ℓ₂))
ΩResizing ℓ₁ ℓ₂ = Σ[ Ω ∈ Type ℓ₂ ] (hProp ℓ₁ ≃ Ω)
```


<figure class="book-diagram type-comparison resizing-comparison" id="fig-resizing-comparison" aria-describedby="fig-resizing-comparison-caption">
<section class="diagram-panel resizing-case">
<!--en-->
<p class="type-comparison-title"><strong>propositional resizing</strong></p>
<!--zh-->
<p class="type-comparison-title"><strong>命题换级</strong></p>
<!--ja-->
<p class="type-comparison-title"><strong>命題リサイズ</strong></p>
<!--/-->
<!--en-->
<p class="resizing-note">Propositional resizing replaces each proposition by a type-equivalent representative at a chosen universe level.</p>
<!--zh-->
<p class="resizing-note">命题换级为每个命题在指定宇宙层级选取一个类型等价的代表。</p>
<!--ja-->
<p class="resizing-note">命題リサイズは、各命題を指定した宇宙レベルにある型同値な代表で置き換える。</p>
<!--/-->

$$r : \operatorname{Resizing}\,\ell_1\,\ell_2$$

<div class="resizing-scene">
<div class="resizing-label">

$$P_i : \operatorname{hProp}\,\ell_1$$

</div>
<div></div>
<div class="resizing-label">

$$Q_i : \operatorname{hProp}\,\ell_2$$

</div>
<div class="diagram-space resizing-type">

$$\langle P_1\rangle$$

</div>
<div class="resizing-bridge">

$$\overset{e_1}{\simeq}$$

</div>
<div class="diagram-space resizing-type">

$$\langle Q_1\rangle$$

</div>
<div class="diagram-space resizing-type">

$$\langle P_2\rangle$$

</div>
<div class="resizing-bridge">

$$\overset{e_2}{\simeq}$$

</div>
<div class="diagram-space resizing-type">

$$\langle Q_2\rangle$$

</div>
<div class="resizing-label">

$$\vdots$$

</div>
<div></div>
<div class="resizing-label">

$$\vdots$$

</div>
</div>

$$r(P_i) = (Q_i,e_i)$$

</section>
<section class="diagram-panel resizing-case">
<!--en-->
<p class="type-comparison-title"><strong>Ω-resizing</strong></p>
<!--zh-->
<p class="type-comparison-title"><strong>命题宇宙换级</strong></p>
<!--ja-->
<p class="type-comparison-title"><strong>命題宇宙リサイズ</strong></p>
<!--/-->
<!--en-->
<p class="resizing-note">Ω-resizing presents an entire proposition universe by a type in a chosen universe level.</p>
<!--zh-->
<p class="resizing-note">命题宇宙换级用指定宇宙层级中的一个类型呈现整个命题宇宙。</p>
<!--ja-->
<p class="resizing-note">命題宇宙リサイズは、命題宇宙全体を指定した宇宙レベルの型で提示する。</p>
<!--/-->

$$(\Omega,e) : \Omega\operatorname{Resizing}\,\ell_1\,\ell_2$$

<div class="resizing-scene resizing-whole">
<div class="diagram-space resizing-universe">

$$\operatorname{hProp}\,\ell_1$$

<div class="resizing-points">
<div class="resizing-point">

$$P_1$$

</div>
<div class="resizing-point">

$$P_2$$

</div>
<div class="resizing-point">

$$\cdots$$

</div>
</div>
</div>
<div class="resizing-bridge">

$$\overset{e}{\simeq}$$

</div>
<div class="diagram-space resizing-universe">

$$\Omega : \operatorname{Type}_{\ell_2}$$

<div class="resizing-points">
<div class="resizing-point">

$$c_1$$

</div>
<div class="resizing-point">

$$c_2$$

</div>
<div class="resizing-point">

$$\cdots$$

</div>
</div>
</div>
</div>

$$c_i = \operatorname{equivFun}\,e\,P_i : \Omega$$

</section>
<figcaption id="fig-resizing-comparison-caption">
<!--en-->
Resizing each proposition and resizing the whole proposition universe ask for different data.
<!--zh-->
逐个命题换级与整个命题宇宙换级，要求的是不同的数据。
<!--ja-->
個々の命題のリサイズと命題宇宙全体のリサイズは、異なるデータを要求する。
<!--/-->
</figcaption>
</figure>

<!--en-->
Next we prove that Ω-resizing implies propositional resizing. Suppose we are given `Ω : Type ℓ₂`{.Agda} and an equivalence `e : hProp ℓ₁ ≃ Ω`{.Agda}. This equivalence gives each proposition a code in `Ω`{.Agda}; we still need to turn that code into a proposition at level `ℓ₂`{.Agda} and prove it equivalent to the original.

In an ordinary mathematical proof, we might fix `Ω`{.Agda} and `e`{.Agda} for the argument and carry out several constructions under these shared assumptions. Agda expresses the same arrangement with the parameterized submodule `CodedTruth`{.Agda}: its declaration lists the common data, which its definitions can use without repeating the parameters. When the main theorem receives a particular `(Ω , e)`{.Agda}, it uses those constructions. `private`{.Agda} only makes the module an internal proof aid; it adds no mathematical assumption.
<!--zh-->
接下来证明：命题宇宙换级蕴含命题换级。假设给定 `Ω : Type ℓ₂`{.Agda} 和等价 `e : hProp ℓ₁ ≃ Ω`{.Agda}。等价使每个命题都有 `Ω`{.Agda} 中的编码；我们还需要从这个编码构造 `ℓ₂`{.Agda} 层的命题，并证明它与原命题等价。

通常的数学证明会先说「以下固定 `Ω`{.Agda} 和 `e`{.Agda}」，再在这两个共同前提下完成一系列构造。Agda 用带参数的子模块 `CodedTruth`{.Agda} 表达同样的安排：模块声明列出共同前提，里面的定义都可以直接使用它们，不必反复写出参数。证明最后收到具体的 `(Ω , e)`{.Agda} 时，再取用这一组构造。`private`{.Agda} 只表示这个模块是本章内部的辅助工具，并未增加数学假设。
<!--ja-->
次に、命題宇宙リサイズから命題リサイズが従うことを証明する。`Ω : Type ℓ₂`{.Agda} と同値 `e : hProp ℓ₁ ≃ Ω`{.Agda} が与えられたとする。この同値によって各命題は `Ω`{.Agda} に符号をもつが、その符号からレベル `ℓ₂`{.Agda} の命題を構成し、元の命題との同値を示す必要がある。

通常の数学の証明なら、「以下、`Ω`{.Agda} と `e`{.Agda} を固定する」と述べ、この共通の仮定のもとでいくつかの構成を行う。Agda では、引数を持つ部分モジュール `CodedTruth`{.Agda} が同じ役割を果たす。モジュール宣言に共通のデータを並べておけば、内部の定義は毎回引数を書き直さずにそれらを使える。最後に主定理へ具体的な `(Ω , e)`{.Agda} が与えられたとき、これらの構成を呼び出す。`private`{.Agda} はこのモジュールを本章内の補助的な道具に限るだけで、新しい数学的仮定を加えない。
<!--/-->

<details open class="submodule-fold">
<summary class="submodule-fold-heading">
```agda
private module CodedTruth {ℓ₁ ℓ₂} (Ω : Type ℓ₂) (e : hProp ℓ₁ ≃ Ω) where
```
</summary>
<div class="submodule-fold-content">

<!--en-->
Name the forward map of `e`{.Agda} by `c`{.Agda}. Then `c P`{.Agda} is the code of `P`{.Agda} in `Ω`{.Agda}.
<!--zh-->
把 `e`{.Agda} 的正向映射命名为 `c`{.Agda}。于是 `c P`{.Agda} 是 `P`{.Agda} 在 `Ω`{.Agda} 中的编码。
<!--ja-->
`e`{.Agda} の順写像を `c`{.Agda} と名付ける。すると `c P`{.Agda} が `Ω`{.Agda} における `P`{.Agda} の符号になる。
<!--/-->

```agda
  c : hProp ℓ₁ → Ω
  c = equivFun e
```

<!--en-->
**Construction** (`codedTruth`{.Agda}) The code `c P`{.Agda} is a point of `Ω`{.Agda}. To obtain a proposition, ask whether it equals the code of truth: `c ⊤ ≡ c P`{.Agda}. This path type lies at level `ℓ₂`{.Agda}. It is a proposition because `e`{.Agda} transfers the h-set structure of `hProp ℓ₁`{.Agda} to `Ω`{.Agda}. We take it as the representative of `P`{.Agda}; the isomorphism below verifies that it has the same truth content.
<!--zh-->
**构造** (`codedTruth`{.Agda}) 编码 `c P`{.Agda} 是 `Ω`{.Agda} 中的一个点。要得到命题，就问它是否等于真命题的编码：`c ⊤ ≡ c P`{.Agda}。这个路径类型位于 `ℓ₂`{.Agda} 层；`e`{.Agda} 把 `hProp ℓ₁`{.Agda} 的 h-集合结构搬运到 `Ω`{.Agda}，保证它是命题。我们取它作为 `P`{.Agda} 的代表，下面的同构将证明二者具有相同的真值内容。
<!--ja-->
**構成** (`codedTruth`{.Agda}) 符号 `c P`{.Agda} は `Ω`{.Agda} の一点である。命題を得るには、それが真の命題の符号と等しいかを問えばよい：`c ⊤ ≡ c P`{.Agda}。このパス型はレベル `ℓ₂`{.Agda} に属する。`e`{.Agda} が `hProp ℓ₁`{.Agda} の h-集合構造を `Ω`{.Agda} へ運ぶので、これは命題である。これを `P`{.Agda} の代表とし、以下の同型によって真理内容が等しいことを確かめる。
<!--/-->

```agda
  codedTruth : hProp ℓ₁ → hProp ℓ₂
  codedTruth P = (c ⊤ ≡ c P) , isOfHLevelRespectEquiv 2 e isSetHProp _ _
```


<!--en-->
The band in `Ω`{.Agda} depicts paths with endpoints `c(⊤)`{.Agda} and `c(P)`{.Agda}. Click it to unfold the path family into the second type space, with whole paths represented as points. The illustrated `q`{.Agda} and `r`{.Agda} presuppose that `P`{.Agda} has a proof; the equivalence with `⟨ P ⟩`{.Agda} holds without this assumption.
<!--zh-->
`Ω`{.Agda} 中的带状区域示意端点为 `c(⊤)`{.Agda}、`c(P)`{.Agda} 的路径族。点击它，路径族展开成第二个类型空间，整条路径改画成其中的点。图中的 `q`{.Agda}、`r`{.Agda} 以 `P`{.Agda} 有证明为前提；与 `⟨ P ⟩`{.Agda} 的类型等价本身不需要这个假设。
<!--ja-->
`Ω`{.Agda} の帯状領域は、端点を `c(⊤)`{.Agda}、`c(P)`{.Agda} とするパスの族を表す。クリックすると、この族が第二の型の空間へ広がり、パス全体がその点として描かれる。図の `q`{.Agda}、`r`{.Agda} は `P`{.Agda} の証明を前提とするが、`⟨ P ⟩`{.Agda} との型同値そのものにはこの仮定は不要である。
<!--/-->

<figure class="book-diagram type-comparison path-figure" id="fig-coded-truth" aria-describedby="fig-coded-truth-caption">
<div class="coded-truth-proof-scene">
<div class="diagram-space coded-truth-proof">

$$\langle P\rangle$$

<div class="coded-truth-universe">

$$: \operatorname{Type}_{\ell_1}$$

</div>
<div class="path-stage" style="aspect-ratio:200/140">
<svg viewBox="0 0 200 140" aria-hidden="true" focusable="false">
<circle class="diagram-point" cx="100" cy="70" r="4"/>
</svg>
<span class="path-label" style="left:50%;top:75%">$p$</span>
</div>
</div>
<div class="coded-truth-equivalence">$\simeq$</div>
<div class="diagram-space coded-truth-proof coded-truth-proof-target">

$$\langle\operatorname{codedTruth}\,P\rangle$$

<div class="coded-truth-universe">

$$: \operatorname{Type}_{\ell_2}$$

</div>
<div class="path-stage" style="aspect-ratio:200/140">
<svg viewBox="0 0 200 140" aria-hidden="true" focusable="false">
<circle class="diagram-point coded-truth-target coded-truth-target-q" cx="65" cy="70" r="4"/>
<circle class="diagram-point coded-truth-target coded-truth-target-r" cx="135" cy="70" r="4"/>
</svg>
<span class="path-label coded-truth-target" style="left:32.5%;top:75%">$q$</span>
<span class="path-label coded-truth-target" style="left:67.5%;top:75%">$r$</span>
</div>
</div>
<div class="coded-truth-detail-link">
<svg class="coded-truth-detail-horizontal" viewBox="0 0 90 30" aria-hidden="true" focusable="false">
<path class="diagram-guide" d="M0 15 L90 15"/>
</svg>
<svg class="coded-truth-detail-vertical" viewBox="0 0 30 50" aria-hidden="true" focusable="false">
<path class="diagram-guide" d="M15 0 L15 50"/>
</svg>
</div>
<div class="diagram-space coded-truth-expanded">

$$\Omega$$

<div class="coded-truth-universe">

$$: \operatorname{Type}_{\ell_2}$$

</div>
<div class="path-stage coded-truth-trigger" style="aspect-ratio:410/200">
<svg viewBox="0 0 410 200" aria-hidden="true" focusable="false">
<path class="diagram-path-space coded-truth-source-region" d="M100 95 Q205 0 310 95 Q205 190 100 95 Z"/>
<path class="diagram-path" d="M100 95 Q205 0 310 95"/>
<path class="diagram-path" d="M100 95 Q205 190 310 95"/>
<circle class="diagram-point" cx="100" cy="95" r="4"/>
<circle class="diagram-point" cx="310" cy="95" r="4"/>
<g class="coded-truth-moving-space">
<path class="diagram-path-space coded-truth-region-copy" d="M100 95 Q205 0 310 95 Q205 190 100 95 Z"/>
<g class="coded-truth-path-copy-q">
<path class="diagram-path" d="M100 95 Q205 0 310 95"/>
<circle class="diagram-point" cx="100" cy="95" r="4"/>
<circle class="diagram-point" cx="310" cy="95" r="4"/>
</g>
<g class="coded-truth-path-copy-r">
<path class="diagram-path" d="M100 95 Q205 190 310 95"/>
<circle class="diagram-point" cx="100" cy="95" r="4"/>
<circle class="diagram-point" cx="310" cy="95" r="4"/>
</g>
</g>
</svg>
<span class="path-label" style="left:50%;top:10%">$q$</span>
<span class="path-label coded-truth-region-label" style="left:50%;top:47.5%">$\langle\operatorname{codedTruth}\,P\rangle$</span>
<span class="path-label" style="left:50%;top:81%">$r$</span>
<span class="path-label" style="left:10.98%;top:47.5%">$c(\top)$</span>
<span class="path-label" style="left:89.02%;top:47.5%">$c(P)$</span>
</div>
</div>
</div>
<figcaption id="fig-coded-truth-caption">
<!--en-->
A point in `⟨ codedTruth P ⟩`{.Agda} is a whole path in `Ω`{.Agda}: `⟨ codedTruth P ⟩ = (c(⊤) ≡ c(P))`{.Agda}. The two proof types are equivalent, at levels `ℓ₁`{.Agda} and `ℓ₂`{.Agda} respectively.
<!--zh-->
`⟨ codedTruth P ⟩`{.Agda} 中的一个点，就是 `Ω`{.Agda} 中的一整条路径：`⟨ codedTruth P ⟩ = (c(⊤) ≡ c(P))`{.Agda}。两个证明类型分别位于 `ℓ₁`{.Agda} 和 `ℓ₂`{.Agda} 层，彼此类型等价。
<!--ja-->
`⟨ codedTruth P ⟩`{.Agda} の一点は、`Ω`{.Agda} の一本のパスそのものである：`⟨ codedTruth P ⟩ = (c(⊤) ≡ c(P))`{.Agda}。二つの証明の型はそれぞれレベル `ℓ₁`{.Agda} と `ℓ₂`{.Agda} に属し、互いに型同値である。
<!--/-->
</figcaption>
</figure>

<!--en-->
**Lemma** (`codedTruthIso`{.Agda}) The underlying type of `P`{.Agda} is isomorphic to the underlying type of `codedTruth P`{.Agda}. Thus the representative constructed above really has the same truth content as `P`{.Agda}.
<!--zh-->
**引理** (`codedTruthIso`{.Agda}) `P`{.Agda} 的底层类型与 `codedTruth P`{.Agda} 的底层类型同构。因此，上面构造的代表确实与 `P`{.Agda} 具有相同的真值内容。
<!--ja-->
**補題** (`codedTruthIso`{.Agda}) `P`{.Agda} の基礎型は `codedTruth P`{.Agda} の基礎型と同型である。したがって、上で構成した代表は確かに `P`{.Agda} と同じ真理内容をもつ。
<!--/-->

```agda
  codedTruthIso : (P : hProp ℓ₁) → Iso ⟨ P ⟩ ⟨ codedTruth P ⟩
```

<!--en-->
**Proof** We construct the two maps `to`{.Agda} and `from`{.Agda}, then assemble them with `iso`{.Agda}. The source `⟨ P ⟩`{.Agda} and target `⟨ codedTruth P ⟩`{.Agda} are both propositions, so their propositionhood proves the two round-trip laws once the maps have been given. Where a map must return an inhabitant of truth, we write its unique inhabitant `tt*`{.Agda} explicitly.
<!--zh-->
**证明** 我们构造两个方向的映射 `to`{.Agda} 和 `from`{.Agda}，再用 `iso`{.Agda} 把它们组装起来。源 `⟨ P ⟩`{.Agda} 和目标 `⟨ codedTruth P ⟩`{.Agda} 都是命题，因此给出两个映射之后，两端的命题性便可直接证明两条往返律。映射需要返回真命题的元素时，我们显式写出其唯一元素 `tt*`{.Agda}。
<!--ja-->
**証明** 二方向の写像 `to`{.Agda} と `from`{.Agda} を構成し、`iso`{.Agda} でまとめる。始域 `⟨ P ⟩`{.Agda} と終域 `⟨ codedTruth P ⟩`{.Agda} はどちらも命題なので、二つの写像を与えれば、両端の命題性が二つの往復則を直接証明する。写像が真の命題の要素を返す箇所では、その唯一の要素 `tt*`{.Agda} を明示する。
<!--/-->

```agda
  codedTruthIso P = iso to from (λ q → ⟨ codedTruth P ⟩isProp _ q) (λ p → ⟨ P ⟩isProp _ p)
    where
```

<!--en-->
It remains to construct the two maps.

- For `to`{.Agda}, a proof `p : ⟨ P ⟩`{.Agda} makes `⊤`{.Agda} and `P`{.Agda} logically equivalent. Propositional extensionality gives `⊤ ≡ P`{.Agda}; applying `cong c`{.Agda} yields `c ⊤ ≡ c P`{.Agda}, a proof of `codedTruth P`{.Agda}.
<!--zh-->
现在构造两个方向的映射。

- 对于 `to`{.Agda}，证明 `p : ⟨ P ⟩`{.Agda} 使 `⊤`{.Agda} 与 `P`{.Agda} 逻辑等价。命题外延性给出路径 `⊤ ≡ P`{.Agda}，再用 `cong c`{.Agda} 得到 `c ⊤ ≡ c P`{.Agda}，即 `codedTruth P`{.Agda} 的证明。
<!--ja-->
あとは二方向の写像を構成する。

- `to`{.Agda} では、証明 `p : ⟨ P ⟩`{.Agda} によって `⊤`{.Agda} と `P`{.Agda} が論理的同値になる。命題外延性からパス `⊤ ≡ P`{.Agda} を得て、`cong c`{.Agda} によって `c ⊤ ≡ c P`{.Agda}、すなわち `codedTruth P`{.Agda} の証明を得る。
<!--/-->

```agda
    to : ⟨ P ⟩ → ⟨ codedTruth P ⟩
    to p = cong c (⇔toPath (λ _ → p) (λ _ → tt*))
```

<!--en-->
- For `from`{.Agda}, start with `q : c ⊤ ≡ c P`{.Agda}. The equivalence `congEquiv e`{.Agda} identifies paths between propositions with paths between their codes. Its inverse `invEq (congEquiv e)`{.Agda} recovers `⊤ ≡ P`{.Agda}; transporting `tt*`{.Agda} along this path with `subst ⟨_⟩`{.Agda} gives a proof of `P`{.Agda}.
<!--zh-->
- 对于 `from`{.Agda}，从 `q : c ⊤ ≡ c P`{.Agda} 出发。类型等价 `congEquiv e`{.Agda} 联系命题之间的路径与编码之间的路径；其逆映射 `invEq (congEquiv e)`{.Agda} 还原出 `⊤ ≡ P`{.Agda}，再用 `subst ⟨_⟩`{.Agda} 沿该路径搬运 `tt*`{.Agda}，便得到 `P`{.Agda} 的证明。
<!--ja-->
- `from`{.Agda} では、`q : c ⊤ ≡ c P`{.Agda} から出発する。型同値 `congEquiv e`{.Agda} は命題間のパスと符号間のパスを結ぶ。その逆写像 `invEq (congEquiv e)`{.Agda} によって `⊤ ≡ P`{.Agda} を復元し、`subst ⟨_⟩`{.Agda} でこのパスに沿って `tt*`{.Agda} を輸送すれば、`P`{.Agda} の証明が得られる。
<!--/-->

```agda
    from : ⟨ codedTruth P ⟩ → ⟨ P ⟩
    from q = subst ⟨_⟩ (invEq (congEquiv e) q) tt*
```


</div>
</details>

<!--en-->
**Theorem** (`ΩResizing→Resizing`{.Agda}) Ω-resizing implies propositional resizing.

**Proof** Given `(Ω , e)`{.Agda}, the preceding module supplies `codedTruth P`{.Agda} at level `ℓ₂`{.Agda} for each `P`{.Agda}. Convert `codedTruthIso P`{.Agda} to an equivalence with `isoToEquiv`{.Agda}; the pair is precisely `hasSize ℓ₂ P`{.Agda}.
<!--zh-->
**定理** (`ΩResizing→Resizing`{.Agda}) 命题宇宙换级蕴含命题换级。

**证明** 给定 `(Ω , e)`{.Agda}，前面的模块为每个 `P`{.Agda} 提供位于 `ℓ₂`{.Agda} 层的 `codedTruth P`{.Agda}。再用 `isoToEquiv`{.Agda} 将 `codedTruthIso P`{.Agda} 转成等价，所得依值对正是 `hasSize ℓ₂ P`{.Agda}。
<!--ja-->
**定理** (`ΩResizing→Resizing`{.Agda}) 命題宇宙リサイズは命題リサイズを導く。

**証明** `(Ω , e)`{.Agda} が与えられると、先のモジュールは各 `P`{.Agda} に対してレベル `ℓ₂`{.Agda} の `codedTruth P`{.Agda} を与える。`codedTruthIso P`{.Agda} を `isoToEquiv`{.Agda} で同値に変換すれば、その対が `hasSize ℓ₂ P`{.Agda} となる。
<!--/-->

```agda
ΩResizing→Resizing : ∀ {ℓ₁ ℓ₂} → ΩResizing ℓ₁ ℓ₂ → Resizing ℓ₁ ℓ₂
ΩResizing→Resizing (Ω , e) P = codedTruth P , isoToEquiv (codedTruthIso P)
  where open CodedTruth Ω e
```


<!--en-->
## Recap

These definitions isolate the size information that predicative universe levels do not provide automatically. Equivalence gives a higher proposition a lower representative with the same truth content; propositional resizing supplies such representatives pointwise, while Ω-resizing presents a proposition universe all at once. No inhabitant has been constructed here. The classical chapter derives both principles from excluded middle.
<!--zh-->
## 小结

这些定义分离出了直谓式宇宙层级不会自动提供的尺寸信息。借助[类型等价]{.term-ref #type-equivalence}，高层命题获得具有相同真值内容的低层代表；命题换级逐点给出这类代表，命题宇宙换级则一次呈现整个命题宇宙。本章尚未构造这些原理的见证。「经典逻辑的边界」将从排中律导出二者。
<!--ja-->
## まとめ

これらの定義は、直謂的な宇宙レベルからは自動的に得られない大きさの情報を切り分ける。同値によって上位の命題は同じ真理内容をもつ低いレベルの代表を得る。命題リサイズはその代表を各命題に与え、命題宇宙リサイズは命題の宇宙全体を一度に提示する。本章では、これらの原理の証拠をまだ構成していない。「古典論理との境界」の章で排中律から両者を導く。
<!--/-->
