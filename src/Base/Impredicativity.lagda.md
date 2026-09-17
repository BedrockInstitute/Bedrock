<!--en-->
# Impredicativity

A predicative foundation does not allow quantification within a definition over a totality that already contains the object being defined. Cubical Agda has such a foundation, whereas the set theory formalized in this book contains impredicative constructions. This chapter therefore states the extra conditions needed for those constructions as explicit assumptions, without changing the foundation of the host.

A predicative foundation can accommodate impredicative assumptions just as intuitionistic logic can explicitly assume classical principles. The converse does not hold: once the stronger principles are built into the foundation, later results no longer reveal which of them they actually require. We therefore retain Cubical Agda's predicative foundation and name every impredicative condition at the point where it is used.
<!--zh-->
# 非直谓性

直谓主义数学基础不允许在一个定义中量化某个已经包含待定义对象的总体。Cubical Agda 建立在这样的基础之上，而本书所要形式化的集合论包含非直谓的构造。为了在直谓式的宿主中准确说明这些构造需要什么，本章专门提出一组接口：它们不改变宿主本身，而是把开展非直谓数学所需的额外条件明确列为假设。

直谓主义数学基础可以容纳这样的非直谓假设，正如直觉主义逻辑可以明确加入经典逻辑原理；反过来却不成立，因为一旦基础本身预先采用了更强的原则，就无法再分辨后续结果究竟依赖哪些额外假设。因此，本书保留 Cubical Agda 的直谓式基础，并在需要非直谓性时，通过本章的接口逐项说明所用的条件。
<!--ja-->
# 非可述性

直謂的な基礎では、一つの定義の中で、定義される対象をすでに含む全体にわたって量化することを認めません。Cubical Agda はこのような基礎の上にありますが、本書で形式化する集合論には非可述的な構成が含まれます。そこで本章では、ホストの基礎そのものを変えずに、それらの構成に必要な追加条件を明示的な仮定として述べます。

直謂的な基礎が非可述的な仮定を受け入れられることは、直観主義論理が古典論理の原理を明示的に仮定できることに似ています。逆は成り立ちません。強い原理を初めから基礎に組み込めば、後の結果がそのどれに依存するかを区別できなくなるからです。本書は Cubical Agda の直謂的な基礎を保ち、非可述性が必要な箇所で条件を一つずつ明記します。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

module Base.Impredicativity where

open import Base.Prelude
```

<!--en-->
The issue appears in the universe levels. All propositions whose [underlying types]{.term-ref #underlying-type} lie in `Type ℓ`{.Agda} form `hProp ℓ`{.Agda}, but this proposition universe as a whole belongs to `Type (ℓ-suc ℓ)`{.Agda}. A proposition obtained by quantifying over all of `hProp ℓ`{.Agda} need not fit at level `ℓ`.

For example, suppose we define a proposition `R` by saying that every `Q : hProp ℓ`{.Agda} implies itself, and also demand that `R` belong to `hProp ℓ`{.Agda}. Then the quantifier over every `Q` also ranges over `R`: the domain being quantified over already includes the proposition being defined. The claim that `Q` implies itself is elementary; the difficulty is the demand that this quantification produce a proposition at the same level. In Cubical Agda the quantification instead lives one universe higher. User code cannot rewrite Agda's universe-level rules, but an explicit assumption can connect the higher proposition to a lower representative with the same truth content. We must now say how to express that connection.
<!--zh-->
困难来自宇宙层级。[底层类型]{.term-ref #underlying-type}位于 `Type ℓ`{.Agda} 的所有命题组成 `hProp ℓ`{.Agda}，而这个命题宇宙整体属于 `Type (ℓ-suc ℓ)`{.Agda}。因此，对 `hProp ℓ`{.Agda} 中所有命题量化所得的命题，不一定仍能放在层级 `ℓ`。

例如，试图把命题 `R` 定义为「每个 `Q : hProp ℓ`{.Agda} 都蕴含自身」，同时要求 `R` 也属于 `hProp ℓ`{.Agda}。这样，定义中的「每个 `Q`」也遍及 `R`：量化的总体已经包含正在定义的命题。「`Q` 蕴含自身」虽然显然成立，难点仍是要求这次量化所得的命题留在同一层级。在 Cubical Agda 中，它位于高一层的宇宙。Agda 的用户代码不能改写其宇宙层级规则，但可以通过显式假设，把这个高层命题与真值内容相同的低层代表联系起来。接下来需要说明怎样表达这种联系。
<!--ja-->
問題は宇宙レベルに現れます。[基礎型]{.term-ref #underlying-type}が `Type ℓ`{.Agda} に属するすべての命題は `hProp ℓ`{.Agda} をなしますが、この命題の宇宙全体は `Type (ℓ-suc ℓ)`{.Agda} に属します。したがって、`hProp ℓ`{.Agda} のすべての命題にわたる量化から得た命題が、再びレベル `ℓ` に収まるとは限りません。

例えば、命題 `R` を「すべての `Q : hProp ℓ`{.Agda} は自分自身を含意する」と定義し、同時に `R` も `hProp ℓ`{.Agda} に属すると要求してみます。このとき、定義中の「すべての `Q`」は `R` 自身にも及びます。量化する全体が、定義中の命題をすでに含んでいるのです。「`Q` は自分自身を含意する」という主張は明らかですが、その量化から得た命題を同じレベルに置くという要求が問題です。Cubical Agda では、この量化は一つ上の宇宙に属します。Agda のユーザーコードから宇宙レベルの規則を書き換えることはできませんが、明示的な仮定によって、上位の命題と真理内容が同じ下位の代表を結び付けられます。次に、この結び付きをどう表すかを定めます。
<!--/-->

<!--en-->
A path cannot directly express this connection, because its endpoints must belong to a common ambient type, while the higher and lower propositions inhabit different universes. [Logical equivalence]{.term-intro #logical-equivalence} can express mutual implication between propositions. Sometimes, however, we must connect an entire higher proposition universe with a type in a lower universe. This is no longer a connection between two propositions. We therefore need a notion that connects arbitrary types: **[type equivalence]{.term-ref #type-equivalence}**.
<!--zh-->
路径不能直接表达这种联系，因为路径的两端必须属于同一个环境类型，而高层命题与低层命题位于不同的宇宙。[逻辑等价]{.term-intro #logical-equivalence}可以说明两个命题互相蕴含。不过，我们有时还需要把整个高层命题宇宙与低层宇宙中的一个类型联系起来；这已经不是两个命题之间的联系。因此，我们需要一种能联系任意类型的概念，这就是**[类型等价]{.term-ref #type-equivalence}**。
<!--ja-->
パスはこの結び付きを直接には表せません。パスの両端は共通の型に属する必要がありますが、上位と下位の命題は異なる宇宙に属するからです。[論理的同値]{.term-intro #logical-equivalence}は命題間の両方向の含意を表せます。しかし、命題の上位宇宙全体を下位宇宙の一つの型と結び付ける必要もあります。これはもはや二つの命題の間の結び付きではありません。そこで、任意の型を結び付けられる概念として**[型同値]{.term-ref #type-equivalence}**を用います。
<!--/-->

<!--en-->
## Type equivalence

For types `A` and `B`, `A ≃ B`{.Agda} is a [dependent pair]{.term-ref #dependent-pair}. Its [first component]{.term-ref #first-component} is a map `f : A → B`{.Agda}; its [second component]{.term-ref #second-component} is a [certificate]{.term-ref #certificate} depending on `f`, asserting that the fibre over every `b : B`{.Agda} is [contractible]{.term-ref #contractible}. To read this certificate, we first need to see what a fibre is.
<!--zh-->
## 类型等价

对类型 `A` 与 `B`，`A ≃ B`{.Agda} 是一个[依值对]{.term-ref #dependent-pair}。它的[第一分量]{.term-ref #first-component}是映射 `f : A → B`{.Agda}；[第二分量]{.term-ref #second-component}是依赖于 `f` 的[证书]{.term-ref #certificate}，证明对每个 `b : B`{.Agda}，`f` 在 `b` 上的纤维都[可缩]{.term-ref #contractible}。要读懂这份证书，先看什么是纤维。
<!--ja-->
## 型同値

型 `A` と `B` について、`A ≃ B`{.Agda} は[依存対]{.term-ref #dependent-pair}です。その[第一成分]{.term-ref #first-component}は写像 `f : A → B`{.Agda}、[第二成分]{.term-ref #second-component}は `f` に依存する[証明書]{.term-ref #certificate}で、各 `b : B`{.Agda} 上のファイバーが[可縮]{.term-ref #contractible}であることを証明します。この証明書を読むために、まずファイバーを見ます。
<!--/-->

<!--en-->
For a fixed `b : B`{.Agda}, the **[fibre]{.term-ref #fiber}** of `f` over `b` is the dependent pair type:

<div class="single-line-code"><code>Σ (a : A) (f a ≡ b)</code></div>

An element of the fibre has two components. The first is a candidate preimage `a : A`{.Agda}; the second is a path `f a ≡ b`{.Agda} witnessing that this candidate really maps to `b`. An empty fibre means that `b` has no preimage. Elements of a fibre that cannot be identified by a path represent substantively different ways to return from `b` to `A`.

The equivalence certificate gives each fibre a centre and paths from that centre to all its elements. Its centre supplies a preimage for every `b`, and the paths make that recovery unambiguous up to paths. Together with `f`, this certificate constitutes the equivalence. It also yields an inverse map `g : B → A` and two inverse laws. The first supplies a path for every `a : A`:

<div class="single-line-code"><code>g (f a) ≡ a</code></div>

The second supplies a path for every `b : B`:

<div class="single-line-code"><code>f (g b) ≡ b</code></div>
<!--zh-->
对固定的 `b : B`{.Agda}，`f` 在 `b` 上的**[纤维]{.term-ref #fiber}**是下面这个依值对类型：

<div class="single-line-code"><code>Σ (a : A) (f a ≡ b)</code></div>

纤维的一个元素由两部分组成：第一分量是一个候选原像 `a : A`{.Agda}，第二分量是一条路径 `f a ≡ b`{.Agda}，证明这个 `a` 的确映到 `b`。纤维为空，表示 `b` 没有原像；纤维中若有彼此不能通过路径等同的元素，则表示从 `b` 返回 `A` 时存在实质不同的选择。

[类型等价]{.term-ref #type-equivalence}的[证书]{.term-ref #certificate}为每条纤维给出一个中心，并给出从中心到其他元素的路径。中心为每个 `b` 给出一个原像，这些路径使恢复的结果在路径意义下没有歧义。映射 `f` 连同这份证书构成[类型等价]{.term-ref #type-equivalence}。由此还可导出逆向映射 `g : B → A` 和两条往返律。第一条对每个 `a : A` 给出一条[路径]{.term-ref #path}：

<div class="single-line-code"><code>g (f a) ≡ a</code></div>

第二条对每个 `b : B` 给出一条[路径]{.term-ref #path}：

<div class="single-line-code"><code>f (g b) ≡ b</code></div>
<!--ja-->
固定した `b : B`{.Agda} 上の `f` の**[ファイバー]{.term-ref #fiber}**は、次の依存対型です。

<div class="single-line-code"><code>Σ (a : A) (f a ≡ b)</code></div>

ファイバーの要素は二つの成分を持ちます。第一成分は原像の候補 `a : A`{.Agda}、第二成分はその候補が実際に `b` へ写ることを示すパス `f a ≡ b`{.Agda} です。ファイバーが空なら `b` に原像はありません。ファイバーにパスで同一視できない要素があれば、`b` から `A` へ戻る方法に本質的な違いが残っています。

[型同値]{.term-ref #type-equivalence}の[証明書]{.term-ref #certificate}は各ファイバーの中心と、そこから他のすべての要素へのパスを与えます。中心は各 `b` の原像を与え、それらのパスによって復元はパスの意味で曖昧さを残しません。写像 `f` とこの証明書を合わせたものが[型同値]{.term-ref #type-equivalence}です。ここから逆写像 `g : B → A` と二つの逆法則も導けます。第一の法則は各 `a : A` に[パス]{.term-ref #path}を与えます。

<div class="single-line-code"><code>g (f a) ≡ a</code></div>

第二の法則は各 `b : B` に[パス]{.term-ref #path}を与えます。

<div class="single-line-code"><code>f (g b) ≡ b</code></div>

<!--/-->

```agda
open import Cubical.Foundations.Equiv using ( _≃_ )
```

<!--en-->
This notion should be distinguished from an [isomorphism]{.term-ref #type-isomorphism}, which explicitly presents a forward map, a chosen inverse map and the two inverse laws. The definitions imported below express how the notions are related: `iso`{.Agda} packages those data as `Iso A B`{.Agda}, and `isoToEquiv`{.Agda} converts the result into `A ≃ B`{.Agda}. Explicit maps make isomorphisms convenient for constructing examples, while the cubical library uses equivalences as the common interface for transporting type structure. For propositions, `⇔toPath`{.Agda} performs a different conversion, turning two implications into a path between the corresponding `hProp`{.Agda} values.
<!--zh-->
这里的[类型等价]{.term-ref #type-equivalence}需要与[同构]{.term-ref #type-isomorphism}区分：同构显式给出正向映射、选定的逆向映射和两条逆律。下面导入的定义说明了二者的联系：`iso`{.Agda} 把这些数据打包成 `Iso A B`{.Agda}，`isoToEquiv`{.Agda} 再把所得同构转换为 `A ≃ B`{.Agda}。显式列出映射使同构便于构造具体例子，立方库则以[类型等价]{.term-ref #type-equivalence}作为搬运类型结构的统一接口。对于命题，`⇔toPath`{.Agda} 完成另一种转换，把两个方向的蕴含变成相应 `hProp`{.Agda} 值之间的路径。
<!--ja-->
この[型同値]{.term-ref #type-equivalence}は[同型]{.term-ref #type-isomorphism}と区別する必要があります。同型は順写像、選ばれた逆写像、二つの逆法則を明示的に与えます。以下で導入する定義は両者の関係を表します。`iso`{.Agda} はこれらのデータを `Iso A B`{.Agda} にまとめ、`isoToEquiv`{.Agda} は得られた同型を `A ≃ B`{.Agda} へ変換します。写像を明示する同型は具体例の構成に便利であり、Cubical ライブラリは型の構造を運ぶ共通のインターフェースとして型同値を用います。命題については、`⇔toPath`{.Agda} が別の変換を行い、両方向の含意を対応する `hProp`{.Agda} の値の間のパスへ変えます。
<!--/-->

```agda
open import Cubical.Foundations.Isomorphism using ( Iso; iso; isoToEquiv )
open import Cubical.Functions.Logic using ( ⇔toPath )
```

<!--en-->
The three notions thus serve different parts of an argument in this book. We often construct an isomorphism to prove an equivalence, use equivalences to preserve and transport structure, and finally connect objects by a path once they lie in the same ambient type.
<!--zh-->
这样便可以看清三个概念在本书论证中的分工：证明[类型等价]{.term-ref #type-equivalence}时常先构造同构，保存和搬运结构时统一使用[类型等价]{.term-ref #type-equivalence}，而当两个对象已经位于同一个环境类型中时，最终往往通过[路径]{.term-ref #path}建立联系。
<!--ja-->
以上の三つの概念は、本書の議論で異なる役割を担います。[型同値]{.term-ref #type-equivalence}を証明するときにはまず同型を構成することが多く、構造を保存して運ぶときには[型同値]{.term-ref #type-equivalence}を共通の形として用い、二つの対象が同じ型に属するところまで来れば、最後には[パス]{.term-ref #path}によって結び付けます。
<!--/-->

<!--en-->
## [Propositional resizing]{.term-intro #propositional-resizing}

We can now return to the universe-level problem that motivated type equivalence. Given `P : hProp ℓ₁`{.Agda}, Agda does not let us change the level at which `P` lives. What we can ask for is another proposition `Q : hProp ℓ₂`{.Agda} whose underlying type is connected to that of `P` by a [type equivalence]{.term-ref #type-equivalence}. We define the type `hasSize ℓ₂ P`{.Agda} to record these two pieces of data: its first component chooses `Q`, and its second component gives the type equivalence showing that `Q` has exactly the truth content of `P`.
<!--zh-->
## [命题换级]{.term-intro #propositional-resizing}

现在回到促使我们引入[类型等价]{.term-ref #type-equivalence}的宇宙层级问题。给定 `P : hProp ℓ₁`{.Agda}，Agda 不允许我们直接改变 `P` 所在的层级；能够提出的要求，是在目标层级找到另一个命题 `Q : hProp ℓ₂`{.Agda}，使二者的底层类型[类型等价]{.term-ref #type-equivalence}。我们定义类型 `hasSize ℓ₂ P`{.Agda} 来记录这两项数据：第一分量选出 `Q`，第二分量给出[类型等价]{.term-ref #type-equivalence}，表明 `Q` 与 `P` 具有完全相同的真值内容。
<!--ja-->
## [命題リサイズ]{.term-intro #propositional-resizing}

ここで、[型同値]{.term-ref #type-equivalence}を導入する動機となった宇宙レベルの問題に戻ります。`P : hProp ℓ₁`{.Agda} が与えられても、Agda では `P` の属するレベルを直接変更できません。代わりに、目標レベルの別の命題 `Q : hProp ℓ₂`{.Agda} を見つけ、その基礎型が `P` の基礎型と[型同値]{.term-ref #type-equivalence}であることを要求できます。この二つのデータを記録する型 `hasSize ℓ₂ P`{.Agda} を定義します。第一成分は `Q` を選び、第二成分は `Q` と `P` の真理内容が完全に一致することを示す[型同値]{.term-ref #type-equivalence}を与えます。
<!--/-->

```agda
hasSize : ∀ {ℓ₁} (ℓ₂ : Level) → hProp ℓ₁ → Type (ℓ-max ℓ₁ (ℓ-suc ℓ₂))
hasSize ℓ₂ P = Σ[ Q ∈ hProp ℓ₂ ] (⟨ P ⟩ ≃ ⟨ Q ⟩)
```

<!--en-->
Neither level has to be larger than the other. In the applications below `ℓ₁` is usually the model's truth-value level and `ℓ₂` its indexing level, but the definition itself allows any two levels. The name "propositional resizing" refers to replacing a proposition by a type-equivalent representative at the chosen target level, rather than changing the universe annotation of the original proposition.
<!--zh-->
这里不要求两个层级有大小顺序。在后面的应用中，`ℓ₁` 通常是模型真值所在的层级，`ℓ₂` 是索引所在的层级；但定义本身允许任意两个层级。「命题换级」是指用目标层级中的[类型等价]{.term-ref #type-equivalence}代表替换原命题，而不是修改原命题的宇宙标注。
<!--ja-->
二つのレベルの大小関係は仮定しません。後の応用では通常、`ℓ₁` はモデルの真理値のレベル、`ℓ₂` は添字のレベルですが、定義そのものは任意の二つのレベルに適用できます。「命題リサイズ」とは、元の命題の宇宙注釈を変更することではなく、目標レベルにある[型同値]{.term-ref #type-equivalence}な代表で置き換えることを指します。
<!--/-->

<!--en-->
`Resizing ℓ₁ ℓ₂`{.Agda} applies this request uniformly to every proposition at `ℓ₁`. It is a dependent function: after receiving `P : hProp ℓ₁`{.Agda}, it returns the pair specifying a representative at `ℓ₂` and its [type equivalence]{.term-ref #type-equivalence} with `P`.
<!--zh-->
`Resizing ℓ₁ ℓ₂`{.Agda} 把这项要求一致地施加于 `ℓ₁` 层的每个命题。它是一个[依值函数]{.term-ref #dependent-function}：输入 `P : hProp ℓ₁`{.Agda} 后，返回由 `ℓ₂` 层的代表及其与 `P` 的[类型等价]{.term-ref #type-equivalence}组成的依值对。
<!--ja-->
`Resizing ℓ₁ ℓ₂`{.Agda} は、この要求をレベル `ℓ₁` のすべての命題に一様に課します。これは依存関数であり、`P : hProp ℓ₁`{.Agda} を受け取ると、レベル `ℓ₂` の代表と `P` との[型同値]{.term-ref #type-equivalence}からなる対を返します。
<!--/-->

```agda
Resizing : ∀ ℓ₁ ℓ₂ → Type (ℓ-max (ℓ-suc ℓ₁) (ℓ-suc ℓ₂))
Resizing ℓ₁ ℓ₂ = (P : hProp ℓ₁) → hasSize ℓ₂ P
```

<!--en-->
## [Ω-resizing]{.term-intro #proposition-universe-resizing}

Propositional resizing chooses one representative at a time. `ΩResizing ℓ₁ ℓ₂`{.Agda} instead gives a single type `Ω : Type ℓ₂`{.Agda} together with a [type equivalence]{.term-ref #type-equivalence} `hProp ℓ₁ ≃ Ω`{.Agda}. Thus every proposition at `ℓ₁` has a code in `Ω`, and every element of `Ω` decodes to such a proposition.
<!--zh-->
## [命题宇宙换级]{.term-intro #proposition-universe-resizing}

命题换级一次选取一个代表。`ΩResizing ℓ₁ ℓ₂`{.Agda} 则给出单一类型 `Ω : Type ℓ₂`{.Agda}，以及[类型等价]{.term-ref #type-equivalence} `hProp ℓ₁ ≃ Ω`{.Agda}。因此，`ℓ₁` 层的每个命题都在 `Ω` 中有编码，而 `Ω` 的每个元素也都解码为该层的命题。
<!--ja-->
## [命題宇宙リサイズ]{.term-intro #proposition-universe-resizing}

命題リサイズは代表を一つずつ選びます。一方、`ΩResizing ℓ₁ ℓ₂`{.Agda} は一つの型 `Ω : Type ℓ₂`{.Agda} と[型同値]{.term-ref #type-equivalence} `hProp ℓ₁ ≃ Ω`{.Agda} を与えます。したがって、レベル `ℓ₁` の各命題は `Ω` に符号をもち、`Ω` の各要素はそのレベルの命題へ復号されます。
<!--/-->

```agda
ΩResizing : ∀ ℓ₁ ℓ₂ → Type (ℓ-max (ℓ-suc ℓ₁) (ℓ-suc ℓ₂))
ΩResizing ℓ₁ ℓ₂ = Σ[ Ω ∈ Type ℓ₂ ] (hProp ℓ₁ ≃ Ω)
```

<!--en-->
**Theorem** (`ΩResizing→Resizing`{.Agda}) Ω-resizing implies propositional resizing.
<!--zh-->
**定理** (`ΩResizing→Resizing`{.Agda}) 命题宇宙换级蕴含命题换级。
<!--ja-->
**定理** (`ΩResizing→Resizing`{.Agda}) 命題宇宙リサイズは命題リサイズを導きます。
<!--/-->

```agda
ΩResizing→Resizing : ∀ {ℓ₁ ℓ₂} → ΩResizing ℓ₁ ℓ₂ → Resizing ℓ₁ ℓ₂
```

<!--en-->
**Proof** For each `P`, choose `codedTruth P`{.Agda} as its representative. The isomorphism `codedTruthIso P`{.Agda}, converted by `isoToEquiv`{.Agda}, supplies the required type equivalence.
<!--zh-->
**证明** 对每个 `P`，取 `codedTruth P`{.Agda} 为代表。把同构 `codedTruthIso P`{.Agda} 经 `isoToEquiv`{.Agda} 转换，便得到所需的类型等价。
<!--ja-->
**証明** 各 `P` について `codedTruth P`{.Agda} を代表に取ります。同型 `codedTruthIso P`{.Agda} を `isoToEquiv`{.Agda} で変換すれば、必要な型同値が得られます。
<!--/-->

```agda
ΩResizing→Resizing {ℓ₁} {ℓ₂} (Ω , e) P =
  codedTruth P , isoToEquiv (codedTruthIso P)
  where
```

<details class="agda-proof-details">
<!--en-->
<summary>Construction of `codedTruth`{.Agda} and `codedTruthIso`{.Agda}</summary>
<!--zh-->
<summary>`codedTruth`{.Agda} 和 `codedTruthIso`{.Agda} 的构造</summary>
<!--ja-->
<summary>`codedTruth`{.Agda} と `codedTruthIso`{.Agda} の構成</summary>
<!--/-->

<!--en-->
It remains to construct the representative and the isomorphism used in the proof. We first import the three operations needed below. Given `e : A ≃ B`{.Agda}, `equivFun e`{.Agda} extracts the forward map `A → B`{.Agda}, while `invEq e`{.Agda} extracts the inverse map `B → A`{.Agda}. For `x y : A`{.Agda}, `congEquiv e`{.Agda} gives a type equivalence between the path `x ≡ y`{.Agda} and the path `equivFun e x ≡ equivFun e y`{.Agda} between their images. A path from `x` to `y` can therefore be sent to a path between their images, and a path between the images can be recovered as a path from `x` to `y`.
<!--zh-->
上面的证明还需要构造所用的代表和[同构]{.term-ref #type-isomorphism}。下面先导入证明所需的三项操作。给定 `e : A ≃ B`{.Agda}，`equivFun e`{.Agda} 从类型等价中取出正向映射 `A → B`{.Agda}，`invEq e`{.Agda} 则取出逆向映射 `B → A`{.Agda}。对 `x y : A`{.Agda}，`congEquiv e`{.Agda} 给出路径 `x ≡ y`{.Agda} 与其像之间的路径 `equivFun e x ≡ equivFun e y`{.Agda} 的[类型等价]{.term-ref #type-equivalence}。因此，`x` 到 `y` 的路径可以送到两者的像之间，而像之间的路径也可以还原为 `x` 到 `y` 的路径。
<!--ja-->
上の証明には、そこで使う代表と[同型]{.term-ref #type-isomorphism}の構成が残っています。まず、証明に必要な三つの操作を導入します。`e : A ≃ B`{.Agda} が与えられると、`equivFun e`{.Agda} は型同値から順写像 `A → B`{.Agda} を取り出し、`invEq e`{.Agda} は逆写像 `B → A`{.Agda} を取り出します。`x y : A`{.Agda} に対して、`congEquiv e`{.Agda} はパス `x ≡ y`{.Agda} と、それらの像の間のパス `equivFun e x ≡ equivFun e y`{.Agda} との[型同値]{.term-ref #type-equivalence}を与えます。したがって、`x` から `y` へのパスを両者の像の間のパスへ送り、像の間のパスを `x` から `y` へのパスへ戻せます。
<!--/-->

```agda
  open import Cubical.Foundations.Equiv using ( equivFun; invEq )
  open import Cubical.Foundations.Equiv.Properties using ( congEquiv )
```

<!--en-->
**Construction** (`codedTruth`{.Agda}) Use the given `Ω : Type ℓ₂`{.Agda} and `e : hProp ℓ₁ ≃ Ω`{.Agda}. For each `P : hProp ℓ₁`{.Agda}, the map `equivFun e : hProp ℓ₁ → Ω`{.Agda} encodes it as `equivFun e P : Ω`{.Agda}. This code is merely an element of `Ω`, not yet a proposition that can represent `P` at level `ℓ₂`. We therefore use the code `equivFun e ⊤`{.Agda} of truth as a reference and define `codedTruth P`{.Agda} to be the proposition that `equivFun e ⊤ ≡ equivFun e P`{.Agda}. This equality has exactly the truth content of `P`, but lies at the same level `ℓ₂` as `Ω`. The type equivalence `e`{.Agda} transfers the h-set structure of `hProp ℓ₁`{.Agda} to `Ω`, ensuring that this equality is a proposition at level `ℓ₂`.
<!--zh-->
**构造** (`codedTruth`{.Agda}) 使用给定的 `Ω : Type ℓ₂`{.Agda} 和 `e : hProp ℓ₁ ≃ Ω`{.Agda}。对每个 `P : hProp ℓ₁`{.Agda}，我们可以用 `equivFun e : hProp ℓ₁ → Ω`{.Agda} 编码命题 `P`，得到 `equivFun e P : Ω`{.Agda}。但这个编码只是 `Ω` 的一个元素，还不是能在 `ℓ₂` 层代表 `P` 的命题。所以，以真命题的编码 `equivFun e ⊤`{.Agda} 为参照，把 `codedTruth P`{.Agda} 定义为命题 `equivFun e ⊤ ≡ equivFun e P`{.Agda}。这个等式恰好具有与 `P` 相同的真值内容，但位于与 `Ω` 相同的 `ℓ₂` 层。[类型等价]{.term-ref #type-equivalence} `e`{.Agda} 把 `hProp ℓ₁`{.Agda} 的 h-集合结构搬运到 `Ω`，保证该等式是 `ℓ₂` 层的命题。
<!--ja-->
**構成** (`codedTruth`{.Agda}) 与えられた `Ω : Type ℓ₂`{.Agda} と `e : hProp ℓ₁ ≃ Ω`{.Agda} を使います。各 `P : hProp ℓ₁`{.Agda} は、`equivFun e : hProp ℓ₁ → Ω`{.Agda} によって `equivFun e P : Ω`{.Agda} と符号化できます。しかし、この符号は `Ω` の一要素にすぎず、まだレベル `ℓ₂` で `P` を代表する命題ではありません。そこで、真の命題の符号 `equivFun e ⊤`{.Agda} を基準とし、`codedTruth P`{.Agda} を命題 `equivFun e ⊤ ≡ equivFun e P`{.Agda} と定義します。この等式は `P` とちょうど同じ真理内容をもちますが、`Ω` と同じレベル `ℓ₂` に属します。[型同値]{.term-ref #type-equivalence} `e`{.Agda} が `hProp ℓ₁`{.Agda} の h-集合構造を `Ω` へ運ぶので、この等式はレベル `ℓ₂` の命題になります。
<!--/-->

```agda
  codedTruth : hProp ℓ₁ → hProp ℓ₂
  codedTruth P = (equivFun e ⊤ ≡ equivFun e P) , isOfHLevelRespectEquiv 2 e isSetHProp _ _
    where open import Cubical.Foundations.HLevels using ( isOfHLevelRespectEquiv )
```

∎

<!--en-->
**Lemma** (`codedTruthIso`{.Agda}) The underlying type of `P` is isomorphic to the underlying type of `codedTruth P`{.Agda}. Thus the representative constructed above really has the same truth content as `P`.
<!--zh-->
**引理** (`codedTruthIso`{.Agda}) `P` 的底层类型与 `codedTruth P`{.Agda} 的底层类型同构。因此，上面构造的代表确实与 `P` 具有相同的真值内容。
<!--ja-->
**補題** (`codedTruthIso`{.Agda}) `P` の基礎型は `codedTruth P`{.Agda} の基礎型と同型です。したがって、上で構成した代表は確かに `P` と同じ真理内容をもちます。
<!--/-->

```agda
  codedTruthIso : (P : hProp ℓ₁) → Iso ⟨ P ⟩ ⟨ codedTruth P ⟩
```

<!--en-->
**Proof** We construct the two maps `to`{.Agda} and `from`{.Agda}, then assemble them with `iso`{.Agda}. The source `⟨ P ⟩`{.Agda} and target `⟨ codedTruth P ⟩`{.Agda} are both propositions, so their propositionhood proves the two inverse laws once the maps have been given. Where a map must return an inhabitant of truth, the expected type lets Agda infer its unique inhabitant at `_`{.Agda}.
<!--zh-->
**证明** 我们构造两个方向的映射 `to`{.Agda} 和 `from`{.Agda}，再用 `iso`{.Agda} 把它们组装起来。源 `⟨ P ⟩`{.Agda} 和目标 `⟨ codedTruth P ⟩`{.Agda} 都是命题，因此给出两个映射之后，两端的命题性便可直接证明两条逆律。映射需要返回真命题的元素时，期望类型使 Agda 能在 `_`{.Agda} 处推断出其唯一元素。
<!--ja-->
**証明** 二方向の写像 `to`{.Agda} と `from`{.Agda} を構成し、`iso`{.Agda} でまとめます。始域 `⟨ P ⟩`{.Agda} と終域 `⟨ codedTruth P ⟩`{.Agda} はどちらも命題なので、二つの写像を与えれば、両端の命題性が二つの逆法則を直接証明します。写像が真の命題の要素を返す箇所では、期待される型から Agda が `_`{.Agda} の唯一の要素を推論できます。
<!--/-->

```agda
  codedTruthIso P = iso to from (λ q → ⟨ codedTruth P ⟩isProp _ q) (λ p → ⟨ P ⟩isProp _ p)
    where
```

<!--en-->
It remains only to construct `to`{.Agda} and `from`{.Agda}.

- For `to`{.Agda}, a proof `p : ⟨ P ⟩`{.Agda} makes truth and `P` logically equivalent: truth implies `P` by constantly returning `p`, while the reverse map returns the inferred inhabitant of truth. Propositional extensionality turns these implications into a path `⊤ ≡ P`{.Agda}. Applying `equivFun e`{.Agda} to this path gives the required equality between the two codes, hence an element of `codedTruth P`{.Agda}.
<!--zh-->
现在只需构造 `to`{.Agda} 和 `from`{.Agda}：

- 对于 `to`{.Agda}，给定证明 `p : ⟨ P ⟩`{.Agda}，真命题与 `P` 便[逻辑等价]{.term-ref #logical-equivalence}：从真命题到 `P` 的映射恒取 `p`，反向映射则返回由 Agda 推断出的真命题元素。命题外延性把这两个方向的蕴含变成路径 `⊤ ≡ P`{.Agda}。再对这条路径应用 `equivFun e`{.Agda}，便得到两个编码之间的等式，也就是 `codedTruth P`{.Agda} 的元素。
<!--ja-->
あとは `to`{.Agda} と `from`{.Agda} を構成するだけです。

- `to`{.Agda} については、証明 `p : ⟨ P ⟩`{.Agda} が与えられると、真の命題と `P` は[論理的同値]{.term-ref #logical-equivalence}になります。真の命題から `P` への写像は常に `p` を返し、逆向きの写像は Agda が推論した真の命題の要素を返します。命題外延性はこの二方向の含意をパス `⊤ ≡ P`{.Agda} に変えます。このパスに `equivFun e`{.Agda} を適用すると二つの符号の等式、すなわち `codedTruth P`{.Agda} の要素が得られます。
<!--/-->

```agda
    to : ⟨ P ⟩ → ⟨ codedTruth P ⟩
    to p = cong (equivFun e) (⇔toPath (λ _ → p) (λ _ → _))
```

<!--en-->
- For `from`{.Agda}, use the inverse map of the type equivalence given by `congEquiv e`{.Agda} between paths in the proposition universe and paths in the corresponding codes. Given `q : ⟨ codedTruth P ⟩`{.Agda}, this map recovers a path `⊤ ≡ P`{.Agda} from the equality of codes. Transporting the inferred inhabitant of truth along this path produces a proof of `P`.
<!--zh-->
- 对于 `from`{.Agda}，使用 `congEquiv e`{.Agda} 所给出的[类型等价]{.term-ref #type-equivalence}的逆向映射；这个类型等价联系命题宇宙中的路径与相应编码中的路径。给定 `q : ⟨ codedTruth P ⟩`{.Agda}，该映射把这个编码等式还原为路径 `⊤ ≡ P`{.Agda}；沿这条路径搬运由 Agda 推断出的真命题元素，便得到 `P` 的证明。
<!--ja-->
- `from`{.Agda} については、命題宇宙のパスと対応する符号におけるパスとを結ぶ、`congEquiv e`{.Agda} が与える[型同値]{.term-ref #type-equivalence}の逆写像を使います。`q : ⟨ codedTruth P ⟩`{.Agda} が与えられると、この写像によって符号の等式をパス `⊤ ≡ P`{.Agda} に戻せます。このパスに沿って Agda が推論した真の命題の要素を輸送すれば、`P` の証明が得られます。
<!--/-->

```agda
    from : ⟨ codedTruth P ⟩ → ⟨ P ⟩
    from q = subst ⟨_⟩ (invEq (congEquiv e) q) _
```

∎

</details>

<!--en-->
## Recap

These definitions isolate the size information that predicative universe levels do not provide automatically. Equivalence gives a higher proposition a lower representative with the same truth content; propositional resizing supplies such representatives pointwise, while Ω-resizing presents a proposition universe all at once. No inhabitant has been constructed here. The classical chapter derives both principles from excluded middle.
<!--zh-->
## 小结

这些定义分离出了直谓式宇宙层级不会自动提供的尺寸信息。借助[类型等价]{.term-ref #type-equivalence}，高层命题获得具有相同真值内容的低层代表；命题换级逐点给出这类代表，命题宇宙换级则一次呈现整个命题宇宙。本章尚未构造这些原理的见证。「经典逻辑的边界」将从排中律导出二者。
<!--ja-->
## まとめ

これらの定義は、直謂的な宇宙レベルからは自動的に得られない大きさの情報を切り分けます。同値によって上位の命題は同じ真理内容をもつ低いレベルの代表を得ます。命題リサイズはその代表を各命題に与え、命題宇宙リサイズは命題の宇宙全体を一度に提示します。本章では、これらの原理の証拠をまだ構成していません。「古典論理との境界」の章で排中律から両者を導きます。
<!--/-->
