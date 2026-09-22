<!--en-->
# Choice

Knowing that each type in a family has an element is different from having one function that chooses an element of every type. Propositional truncation makes the distinction precise: `∥ B x ∥₁`{.Agda} asserts existence at an individual index, while `∥ ((x : X) → B x) ∥₁`{.Agda} asserts the existence of a whole choice function. This chapter studies the principle that passes from the first kind of existence to the second, over an h-set of indices.
<!--zh-->
# 选择原理

知道一族类型中的每个类型都有元素，与拥有一个同时为它们选取元素的函数，是不同的两件事。命题截断把区别表达得很准确：`∥ B x ∥₁`{.Agda} 断言某个指标处有元素，`∥ ((x : X) → B x) ∥₁`{.Agda} 则断言整个选择函数存在。本章讨论从前一种存在过渡到后一种存在的原理，其中指标类型要求是 h-集合。
<!--ja-->
# 選択原理

型の族の各型に要素があることと、すべての型から要素を選ぶ一つの関数をもつことは異なる。命題的切り詰めはこの違いを正確に表す。`∥ B x ∥₁`{.Agda} は個々の添字における存在を述べ、`∥ ((x : X) → B x) ∥₁`{.Agda} は選択関数全体の存在を述べる。本章では、添字型を h-集合としたとき、前者から後者へ移る原理を扱う。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

module Base.Choice where
```

<!--en-->
We first state the principle and lower it by one universe level. We then prove that it implies excluded middle. The key is to encode a proposition in the equality of two quotient classes, and use choice to turn that equality into a comparison of booleans. As in the preceding chapter, every use of an additional principle remains an explicit hypothesis.
<!--zh-->
我们先陈述这条原理，再把它降低一个宇宙层级，最后证明它蕴含排中律。证明的关键是把命题编码为两个商类的相等，再借助选择，把这种相等转化为布尔值的比较。与上一章一样，所用的额外原理始终作为显式假设出现。
<!--ja-->
まず原理を定式化し、宇宙レベルを一段下げる。次に、この原理が排中律を含意することを証明する。鍵となるのは、命題を二つの商類の等しさに符号化し、選択によってそれをブール値の比較へ移すことである。前章と同じく、追加の原理は常に明示的な仮定として用いる。
<!--/-->

```agda

open import Base.Prelude
open import Cubical.Foundations.Prelude using ( Path )
open import Base.Classical using ( LEM )
```

<!--en-->
The final step compares the two Boolean representatives with decidable equality `_≟_`{.Agda}.
<!--zh-->
证明的最后一步用可判定相等 `_≟_`{.Agda} 比较两个布尔代表元。
<!--ja-->
証明の最後の段階では、判定可能な等式 `_≟_`{.Agda} によって二つのブール代表を比較する。
<!--/-->

```agda
open import Cubical.Data.Bool using ( _≟_ )
```

<!--en-->
To build the intermediate space, we use a [set quotient]{.term-intro #set-quotient}. Given a type `A`{.Agda} and a relation `R`{.Agda}, the type `A / R`{.Agda} has points `[ a ]`{.Agda}; a proof of `R a b`{.Agda} gives a path `[ a ] ≡ [ b ]`{.Agda}, and `squash/`{.Agda} ensures that the result is an h-set. For a proposition-valued equivalence relation, the library characterizes this path type by an isomorphism with `R a b`{.Agda}. We will use the resulting type equivalence to pass between paths and proofs of the relation.
<!--zh-->
中间的空间由[集合商]{.term-intro #set-quotient}构造。给定类型 `A`{.Agda} 与关系 `R`{.Agda}，类型 `A / R`{.Agda} 中有点 `[ a ]`{.Agda}；`R a b`{.Agda} 的证明给出路径 `[ a ] ≡ [ b ]`{.Agda}，`squash/`{.Agda} 则保证结果是 h-集合。对于取值于命题的等价关系，库用这个路径类型与 `R a b`{.Agda} 的同构来刻画商。我们将使用所得的类型等价，在路径与关系成立的证明之间转换。
<!--ja-->
中間の空間には[集合商]{.term-intro #set-quotient}を用いる。型 `A`{.Agda} と関係 `R`{.Agda} に対して、型 `A / R`{.Agda} は点 `[ a ]`{.Agda} をもち、`R a b`{.Agda} の証明からパス `[ a ] ≡ [ b ]`{.Agda} が得られる。さらに `squash/`{.Agda} が結果を h-集合にする。命題値の同値関係について、ライブラリはこのパス型と `R a b`{.Agda} の同型によって商を特徴付ける。得られる型同値を使い、パスと関係の証明の間を移る。
<!--/-->

```agda
open import Cubical.HITs.SetQuotients
  using ( _/_; [_]; squash/; []surjective; isEquivRel→effectiveIso )
open import Cubical.Relation.Binary.Base using ( module BinaryRelation )
```

<!--en-->
## The principle

For a family `B : X → Type ℓ`{.Agda}, there are three kinds of data worth distinguishing. If an element of every `B x`{.Agda} is already given as a function of `x`{.Agda}, that function is the choice function itself. The additional principle concerns the weaker, truncated input.

| Statement | What it supplies |
| --- | --- |
| `(x : X) → B x`{.Agda} | A choice function, which can be evaluated. |
| `(x : X) → ∥ B x ∥₁`{.Agda} | Existence separately at each index. |
| `∥ ((x : X) → B x) ∥₁`{.Agda} | Existence of one function on all indices. |

**Definition** (`SetChoice`{.Agda}) [Set-level choice]{.term-intro #set-level-choice} at level `ℓ`{.Agda} asserts that the second row implies the third for every h-set `X : Type ℓ`{.Agda} and every family `B : X → Type ℓ`{.Agda}.
<!--zh-->
## 原理

对于族 `B : X → Type ℓ`{.Agda}，值得区分三种数据。如果每个 `B x`{.Agda} 的元素已经作为 `x`{.Agda} 的函数给出，那么这个函数本身就是选择函数。额外的原理针对的是较弱的、经过截断的输入。

| 陈述 | 给出的内容 |
| --- | --- |
| `(x : X) → B x`{.Agda} | 可以求值的选择函数 |
| `(x : X) → ∥ B x ∥₁`{.Agda} | 逐个指标处的存在 |
| `∥ ((x : X) → B x) ∥₁`{.Agda} | 一个同时处理全部指标的函数的存在 |

**定义** (`SetChoice`{.Agda}) 层级 `ℓ`{.Agda} 上的[集合层选择]{.term-intro #set-level-choice}断言：对每个 h-集合 `X : Type ℓ`{.Agda} 及每个族 `B : X → Type ℓ`{.Agda}，第二行蕴含第三行。
<!--ja-->
## 原理

族 `B : X → Type ℓ`{.Agda} に対し、三種類のデータを区別する。各 `B x`{.Agda} の要素がすでに `x`{.Agda} の関数として与えられているなら、その関数自体が選択関数である。追加の原理が扱うのは、切り詰められた、より弱い入力である。

| 主張 | 得られるもの |
| --- | --- |
| `(x : X) → B x`{.Agda} | 値を計算できる選択関数 |
| `(x : X) → ∥ B x ∥₁`{.Agda} | 添字ごとの存在 |
| `∥ ((x : X) → B x) ∥₁`{.Agda} | すべての添字を扱う一つの関数の存在 |

**定義** (`SetChoice`{.Agda}) レベル `ℓ`{.Agda} の[集合レベルの選択]{.term-intro #set-level-choice}は、任意の h-集合 `X : Type ℓ`{.Agda} と族 `B : X → Type ℓ`{.Agda} に対し、第二行から第三行が従うと主張する。
<!--/-->

```agda
SetChoice : ∀ ℓ → Type (ℓ-suc ℓ)
SetChoice ℓ = (X : Type ℓ) → isSet X → (B : X → Type ℓ)
            → ((x : X) → ∥ B x ∥₁) → ∥ ((x : X) → B x) ∥₁
```

<!--en-->
The truncation moves outside the dependent function type; it does not disappear. A hypothesis `sc : SetChoice ℓ`{.Agda} therefore gives the mere existence of a choice function. To use that existence with `rec₁`{.Agda}, we must have a proposition as our goal. Quantification over `Type ℓ`{.Agda} puts the whole principle in `Type (ℓ-suc ℓ)`{.Agda}.

The definition requires <span class="prose-annotation-target">only the index type to be an h-set</span><aside class="prose-annotation-note">No `isSet (B x)`{.Agda} hypothesis is imposed. We follow the displayed definition of `SetChoice`{.Agda} throughout; the set condition here concerns the indices.</aside>.

**Lemma** (`lowerSetChoice`{.Agda}) Choice one universe level higher implies choice at the level below.

**Proof** Lift both the indices and the family before applying `sc`{.Agda}. Each part has a direct counterpart:

| At level `ℓ`{.Agda} | At level `ℓ-suc ℓ`{.Agda} |
| --- | --- |
| `X`{.Agda} | `Lift X`{.Agda} |
| `B x`{.Agda} | `Lift (B (lower x̂))`{.Agda}, for `x̂ : Lift X`{.Agda} |
| `inh x`{.Agda} | `map₁ lift (inh (lower x̂))`{.Agda} |

The proof `isOfHLevelLift 2 setX`{.Agda} preserves the required h-set condition. The lifted choice function can then be lowered pointwise.
<!--zh-->
截断移到了依值函数类型之外，但并没有消失。因此，假设 `sc : SetChoice ℓ`{.Agda} 给出的是选择函数的仅仅存在。若要用 `rec₁`{.Agda} 利用这一存在，目标就必须是命题。由于量化了 `Type ℓ`{.Agda}，整条原理位于 `Type (ℓ-suc ℓ)`{.Agda}。

定义<span class="prose-annotation-target">只要求指标类型是 h-集合</span><aside class="prose-annotation-note">这里没有 `isSet (B x)`{.Agda} 这一假设。本章始终采用所展示的 `SetChoice`{.Agda} 定义，其中「集合」限定的是指标。</aside>。

**引理** (`lowerSetChoice`{.Agda}) 高一个宇宙层级的选择蕴含原层级的选择。

**证明** 应用 `sc`{.Agda} 之前，把指标和族一起抬升。各部分有直接的对应：

| 层级 `ℓ`{.Agda} | 层级 `ℓ-suc ℓ`{.Agda} |
| --- | --- |
| `X`{.Agda} | `Lift X`{.Agda} |
| `B x`{.Agda} | `Lift (B (lower x̂))`{.Agda}，其中 `x̂ : Lift X`{.Agda} |
| `inh x`{.Agda} | `map₁ lift (inh (lower x̂))`{.Agda} |

证明 `isOfHLevelLift 2 setX`{.Agda} 保留所需的 h-集合性。得到抬升后的选择函数，再逐点降回即可。
<!--ja-->
切り詰めは依存関数型の外へ移るが、消えるわけではない。したがって仮定 `sc : SetChoice ℓ`{.Agda} が与えるのは、選択関数の単なる存在である。この存在を `rec₁`{.Agda} で使うには、目標が命題でなければならない。`Type ℓ`{.Agda} 全体を量化するので、原理自体は `Type (ℓ-suc ℓ)`{.Agda} に住む。

定義では<span class="prose-annotation-target">添字型だけに h-集合であることを要求する</span><aside class="prose-annotation-note">`isSet (B x)`{.Agda} は仮定していない。本章では表示した `SetChoice`{.Agda} の定義を用い、「集合」は添字についての条件を表す。</aside>。

**補題** (`lowerSetChoice`{.Agda}) 一つ上の宇宙レベルの選択は、一つ下のレベルの選択を含意する。

**証明** `sc`{.Agda} を適用する前に、添字と族をともに持ち上げる。各部分は次のように対応する。

| レベル `ℓ`{.Agda} | レベル `ℓ-suc ℓ`{.Agda} |
| --- | --- |
| `X`{.Agda} | `Lift X`{.Agda} |
| `B x`{.Agda} | `Lift (B (lower x̂))`{.Agda}、ただし `x̂ : Lift X`{.Agda} |
| `inh x`{.Agda} | `map₁ lift (inh (lower x̂))`{.Agda} |

`isOfHLevelLift 2 setX`{.Agda} が必要な h-集合性を保つ。得られた選択関数を各点で降ろせばよい。
<!--/-->

```agda
lowerSetChoice : ∀ {ℓ} → SetChoice (ℓ-suc ℓ) → SetChoice ℓ
```

<!--en-->
The function used in the outer `map₁`{.Agda} has the following value at `x`{.Agda}. Both the lifted function and the lowered one remain under truncation.

<div class="single-line-code" data-note="Lift the input, evaluate f, then lower the output."><code>lower (f (lift x)) : B x</code></div>
<!--zh-->
外层 `map₁`{.Agda} 所用的函数在 `x`{.Agda} 处取以下值。抬升后的函数与降回的函数始终都留在截断之内。

<div class="single-line-code" data-note="先抬升输入，求 f 的值，再降低输出。"><code>lower (f (lift x)) : B x</code></div>
<!--ja-->
外側の `map₁`{.Agda} に渡す関数は、`x`{.Agda} で次の値を取る。持ち上げた関数も降ろした関数も、切り詰めの内部に留まる。

<div class="single-line-code" data-note="入力を持ち上げ、f を適用し、出力を降ろす。"><code>lower (f (lift x)) : B x</code></div>
<!--/-->

```agda
lowerSetChoice sc X setX B inh =
  map₁ (λ f x → lower (f (lift x)))
         (sc (Lift X) (isOfHLevelLift 2 setX)
             (λ x → Lift (B (lower x)))
             (λ x → map₁ lift (inh (lower x))))
```

∎

<!--en-->
## Diaconescu's theorem

How can choosing representatives decide an arbitrary proposition? The preceding chapter encoded a proposition by a boolean after obtaining a decision. Here the order is reversed: we construct a quotient from the proposition without deciding it, and choice will supply the booleans whose comparison gives the decision.

**Theorem** (`choice→lem`{.Agda}) Set-level choice implies excluded middle at the same universe level.

**Proof** Fix `P : hProp ℓ`{.Agda}. On `Bool`{.Agda}, define a relation whose diagonal entries are always inhabited and whose off-diagonal entries are `⟨ P ⟩`{.Agda}. Thus `P`{.Agda} controls whether the two different booleans are related.
<!--zh-->
## Diaconescu 定理

选取代表元为什么能判定任意命题？上一章在取得判定之后，用布尔值编码命题。这里反过来：先由命题构造商，无须判定它，再由选择提供布尔值，最后比较这些值而得到判定。

**定理** (`choice→lem`{.Agda}) 集合层选择蕴含同一宇宙层级上的排中律。

**证明** 固定 `P : hProp ℓ`{.Agda}。在 `Bool`{.Agda} 上定义关系，对角格始终有元素，非对角格则是 `⟨ P ⟩`{.Agda}。这样，两个不同的布尔值是否相关就由 `P`{.Agda} 控制。
<!--ja-->
## ディアコネスクの定理

代表元を選ぶことから、任意の命題をどう判定できるのだろうか。前章では判定を得てから命題をブール値で符号化した。ここでは順序が逆になる。命題を判定せずに商を構成し、選択によってブール値を得て、その比較から判定を導く。

**定理** (`choice→lem`{.Agda}) 集合レベルの選択は、同じ宇宙レベルの排中律を含意する。

**証明** `P : hProp ℓ`{.Agda} を固定する。`Bool`{.Agda} 上の関係を、対角成分は常に要素をもち、非対角成分は `⟨ P ⟩`{.Agda} となるように定める。異なる二つのブール値が関係をもつかどうかを `P`{.Agda} が決める。
<!--/-->

```agda
module Diaconescu {ℓ} (P : hProp ℓ) where

  _~_ : Bool → Bool → Type ℓ
  true  ~ true  = ⊤*
  false ~ false = ⊤*
  _     ~ _     = ⟨ P ⟩
```

<!--en-->
Take the quotient by this relation. We want to characterize paths between its distinguished points `[ true ]`{.Agda} and `[ false ]`{.Agda} by proofs of `P`{.Agda}. The library's isomorphism theorem applies once we verify that `_~_`{.Agda} is a proposition-valued equivalence relation.
<!--zh-->
按这个关系取商。我们希望用 `P`{.Agda} 的证明来刻画两个特殊点 `[ true ]`{.Agda} 与 `[ false ]`{.Agda} 之间的路径。只要验证 `_~_`{.Agda} 是取值于命题的等价关系，就能应用库中的同构定理。
<!--ja-->
この関係による商を取る。二つの点 `[ true ]`{.Agda} と `[ false ]`{.Agda} の間のパスを、`P`{.Agda} の証明によって特徴付けたい。`_~_`{.Agda} が命題値の同値関係であることを確かめれば、ライブラリの同型定理を適用できる。
<!--/-->

```agda

  Glued : Type ℓ
  Glued = Bool / _~_
```

<details open class="optional-reading" aria-labelledby="choice-relation-laws-title">

<!--en-->
<summary class="optional-reading-title" id="choice-relation-laws-title">Optional: the quotient relation satisfies the required laws</summary>

For the quotient just constructed, `isEquivRel→effectiveIso`{.Agda} requires a proposition-valued equivalence relation. The checks use only the definition of `_~_`{.Agda}. Each diagonal entry is the proposition `⊤*`{.Agda}; each off-diagonal entry is the proposition packaged in `P`{.Agda}.
<!--zh-->
<summary class="optional-reading-title" id="choice-relation-laws-title">选读：验证商关系所需的性质</summary>

对于刚构造的商，`isEquivRel→effectiveIso`{.Agda} 要求关系取值于命题并满足等价律。验证只需查看 `_~_`{.Agda} 的定义：对角格是命题 `⊤*`{.Agda}，非对角格是 `P`{.Agda} 所打包的命题。
<!--ja-->
<summary class="optional-reading-title" id="choice-relation-laws-title">発展：商の関係に必要な性質の検証</summary>

いま構成した商に `isEquivRel→effectiveIso`{.Agda} を使うには、関係が命題値で同値律を満たす必要がある。検証には `_~_`{.Agda} の定義だけを使う。対角成分は命題 `⊤*`{.Agda} であり、非対角成分は `P`{.Agda} に含まれる命題である。
<!--/-->

```agda
  ~-prop : BinaryRelation.isPropValued _~_
  ~-prop true  true  = isProp⊤*
  ~-prop false false = isProp⊤*
  ~-prop true  false = ⟨ P ⟩isProp
  ~-prop false true  = ⟨ P ⟩isProp
```

<!--en-->
The diagonal entries have the inhabitant `tt*`{.Agda}, which proves reflexivity.
<!--zh-->
对角格有元素 `tt*`{.Agda}，这就证明了自反性。
<!--ja-->
対角成分の要素 `tt*`{.Agda} が反射性を証明する。
<!--/-->

```agda

  ~-refl : (a : Bool) → a ~ a
  ~-refl true  = tt*
  ~-refl false = tt*

```

<!--en-->
Swapping the inputs leaves the entry type unchanged. On the diagonal we return `tt*`{.Agda}; off the diagonal we reuse the given proof of `P`{.Agda}.
<!--zh-->
交换输入不改变格中的类型。对角格返回 `tt*`{.Agda}，非对角格复用所给的 `P`{.Agda} 的证明。
<!--ja-->
入力を交換しても成分の型は変わらない。対角では `tt*`{.Agda} を返し、非対角では与えられた `P`{.Agda} の証明を再利用する。
<!--/-->

```agda
  ~-sym : (a b : Bool) → a ~ b → b ~ a
  ~-sym true  true  _ = tt*
  ~-sym false false _ = tt*
  ~-sym true  false p = p
  ~-sym false true  p = p

```

<!--en-->
For transitivity, first compare the endpoints `a`{.Agda} and `c`{.Agda}. If they agree, `tt*`{.Agda} proves `a ~ c`{.Agda}.
<!--zh-->
传递性先看两端 `a`{.Agda} 与 `c`{.Agda}。两端相同时，`tt*`{.Agda} 证明 `a ~ c`{.Agda}。
<!--ja-->
推移性では両端 `a`{.Agda} と `c`{.Agda} を見る。一致するなら `tt*`{.Agda} が `a ~ c`{.Agda} を証明する。
<!--/-->

```agda
  ~-trans : (a b c : Bool) → a ~ b → b ~ c → a ~ c
  ~-trans true  _     true  _ _ = tt*
  ~-trans false _     false _ _ = tt*
```

<!--en-->
If the endpoints differ, the middle boolean equals one of them, so one of the two premises is already a proof of `P`{.Agda}. Return that proof.
<!--zh-->
两端不同时，中间的布尔值必等于其中一端，因而两个前提中已有一个是 `P`{.Agda} 的证明，返回它即可。
<!--ja-->
両端が異なるなら、中間のブール値はどちらか一方に等しいため、二つの前提の一方がすでに `P`{.Agda} の証明である。それを返せばよい。
<!--/-->

```agda
  ~-trans true  false false p _ = p
  ~-trans false true  true  p _ = p
  ~-trans true  true  false _ p = p
  ~-trans false false true  _ p = p
```

<!--en-->
The three laws form the equivalence-relation record required by `isEquivRel→effectiveIso`{.Agda}.
<!--zh-->
三条定律组成 `isEquivRel→effectiveIso`{.Agda} 所需的等价关系记录。
<!--ja-->
三つの法則を、`isEquivRel→effectiveIso`{.Agda} が要求する同値関係のレコードにまとめる。
<!--/-->

```agda

  ~-equivRel : BinaryRelation.isEquivRel _~_
  ~-equivRel = BinaryRelation.equivRel ~-refl ~-sym ~-trans
```

</details>

<!--en-->
The verified laws let us apply `isEquivRel→effectiveIso`{.Agda}. It identifies the path type between `[ true ]`{.Agda} and `[ false ]`{.Agda} with `true ~ false`{.Agda}, which is defined to be `⟨ P ⟩`{.Agda}. The library also supplies the two round-trip laws; `isoToEquiv`{.Agda} gives the following type equivalence. Here `Path Glued [ true ] [ false ]`{.Agda} is another notation for `[ true ] ≡ [ false ]`{.Agda} in `Glued`{.Agda}.
<!--zh-->
验证这些定律后，就能应用 `isEquivRel→effectiveIso`{.Agda}。它给出 `[ true ]`{.Agda} 与 `[ false ]`{.Agda} 之间的路径类型与 `true ~ false`{.Agda} 的同构，而后者按定义就是 `⟨ P ⟩`{.Agda}。库也提供了两条往返律，再经 `isoToEquiv`{.Agda} 得到下面的类型等价。这里 `Path Glued [ true ] [ false ]`{.Agda} 是 `Glued`{.Agda} 中的 `[ true ] ≡ [ false ]`{.Agda} 的另一种写法。
<!--ja-->
これらの法則を確認すると、`isEquivRel→effectiveIso`{.Agda} を適用できる。これは `[ true ]`{.Agda} と `[ false ]`{.Agda} の間のパス型と `true ~ false`{.Agda} の同型を与える。後者は定義上 `⟨ P ⟩`{.Agda} である。二つの往復則もライブラリが与えるので、`isoToEquiv`{.Agda} により次の型同値を得る。`Path Glued [ true ] [ false ]`{.Agda} は、`Glued`{.Agda} における `[ true ] ≡ [ false ]`{.Agda} の別表記である。
<!--/-->

```agda
  quotientPath≃P : Path Glued [ true ] [ false ] ≃ ⟨ P ⟩
  quotientPath≃P = isoToEquiv
    (isEquivRel→effectiveIso ~-prop ~-equivRel true false)
```

<!--en-->
In the diagrams, write $e$ for `quotientPath≃P`{.Agda}: its forward map sends a path to a proof of `P`{.Agda}, and its inverse sends a proof to a path. The following panels show the consequences of a proof or a refutation of `P`{.Agda}, without presuming that either has already been obtained.
<!--zh-->
图中以 $e$ 简记 `quotientPath≃P`{.Agda}：正向映射把路径变为 `P`{.Agda} 的证明，逆向映射把证明变为路径。下面分别展示有 `P`{.Agda} 的证明或反驳时的情形，并不预先断定我们已经取得了其中一种。
<!--ja-->
図では `quotientPath≃P`{.Agda} を $e$ と略記する。順方向の写像はパスを `P`{.Agda} の証明へ、逆方向の写像は証明をパスへ送る。以下は `P`{.Agda} の証明または反証があるときの帰結を示すもので、どちらかがすでに得られているとは仮定しない。
<!--/-->

<figure class="book-diagram type-comparison path-figure" id="fig-choice-gluing" aria-describedby="fig-choice-gluing-caption">
<div class="diagram-framed">

$$([\mathsf{true}] \equiv [\mathsf{false}]) \simeq \langle P\rangle$$

<div class="type-comparison-panels">
<div class="type-comparison-panel">

$$p : \langle P\rangle$$

<div class="path-stage diagram-compact-stage" style="aspect-ratio:300/190">
<svg viewBox="0 0 300 190" aria-hidden="true" focusable="false">
<rect class="diagram-space-shape" x="12" y="12" width="276" height="166"/>
<path class="diagram-path" d="M 70 115 Q 150 55 230 115"/>
<circle class="diagram-point" cx="70" cy="115" r="4"/><circle class="diagram-point" cx="230" cy="115" r="4"/>
</svg>
<span class="path-label" style="left:50%;top:20%">$\mathsf{Glued}$</span>
<span class="path-label" style="left:23.33%;top:77%">$[\mathsf{true}]$</span>
<span class="path-label" style="left:76.67%;top:77%">$[\mathsf{false}]$</span>
<span class="path-label" style="left:50%;top:35%">$e^{-1}(p)$</span>
</div>
</div>
<div class="type-comparison-panel">

$$n : \neg\langle P\rangle$$

<div class="path-stage diagram-compact-stage" style="aspect-ratio:300/190">
<svg viewBox="0 0 300 190" aria-hidden="true" focusable="false">
<rect class="diagram-space-shape" x="12" y="12" width="276" height="166"/>
<circle class="diagram-point" cx="70" cy="115" r="4"/><circle class="diagram-point" cx="230" cy="115" r="4"/>
</svg>
<span class="path-label" style="left:50%;top:20%">$\mathsf{Glued}$</span>
<span class="path-label" style="left:23.33%;top:77%">$[\mathsf{true}]$</span>
<span class="path-label" style="left:76.67%;top:77%">$[\mathsf{false}]$</span>
</div>
</div>
</div>
</div>
<figcaption id="fig-choice-gluing-caption">

<!--en-->
On the left, the inverse of $e$ supplies a path. On the right, $e$ would turn any connecting path into a proof contradicted by `n`{.Agda}.
<!--zh-->
左图通过 $e$ 的逆映射得到路径；右图中若存在连接路径，$e$ 就会把它变为与 `n`{.Agda} 矛盾的证明。
<!--ja-->
左図では $e$ の逆写像からパスを得る。右図にパスがあれば、$e$ がそれを `n`{.Agda} と矛盾する証明へ送る。
<!--/-->

</figcaption>
</figure>

<!--en-->
It remains to make equality in `Glued`{.Agda} decidable. A representative of `x : Glued`{.Agda} consists of a boolean `b`{.Agda} and a path `[ b ] ≡ x`{.Agda}. Their dependent pair type `Pick x`{.Agda} is precisely the fibre of the quotient map `[_] : Bool → Glued`{.Agda} over `x`{.Agda}. Its second component certifies that the boolean represents this particular class.

Every quotient point merely has a representative: this is `[]surjective`{.Agda}. Thus the family `Pick`{.Agda} has exactly the pointwise inhabitation needed for choice.
<!--zh-->
接下来要使 `Glued`{.Agda} 中的相等变得可判定。点 `x : Glued`{.Agda} 的代表元由布尔值 `b`{.Agda} 与路径 `[ b ] ≡ x`{.Agda} 组成。它们的依值对类型 `Pick x`{.Agda} 恰是商映射 `[_] : Bool → Glued`{.Agda} 在 `x`{.Agda} 上的一束纤维。第二分量证明这个布尔值代表的是指定的商类。

每个商点都有代表元，其存在性以命题截断表达，这由 `[]surjective`{.Agda} 保证。因此，族 `Pick`{.Agda} 恰有选择所需的逐点有元性。
<!--ja-->
次に `Glued`{.Agda} の等しさを判定できるようにする。点 `x : Glued`{.Agda} の代表元は、ブール値 `b`{.Agda} とパス `[ b ] ≡ x`{.Agda} の組である。その依存対型 `Pick x`{.Agda} は、商写像 `[_] : Bool → Glued`{.Agda} の `x`{.Agda} 上のファイバーにほかならない。第二成分は、そのブール値が指定した商類を代表することを保証する。

商の各点には代表元が単に存在する。これが `[]surjective`{.Agda} である。したがって族 `Pick`{.Agda} は、選択に必要な添字ごとの存在を満たす。
<!--/-->

```agda
  Pick : Glued → Type ℓ
  Pick x = Σ[ b ∈ Bool ] ([ b ] ≡ x)

  pickable : (x : Glued) → ∥ Pick x ∥₁
  pickable = []surjective
```

<!--en-->
Apply `sc`{.Agda} with index type `Glued`{.Agda}, its h-set certificate `squash/`{.Agda}, and the family `Pick`{.Agda}. This is the only application of choice within the argument for `P`{.Agda}. It yields the mere existence of a function that chooses a representative at every quotient point.
<!--zh-->
以 `Glued`{.Agda} 为指标类型，`squash/`{.Agda} 为其 h-集合性证书，`Pick`{.Agda} 为所选的族，应用 `sc`{.Agda}。这是针对 `P`{.Agda} 的论证中唯一一次使用选择；得到的是为每个商点选取代表元的函数的仅仅存在。
<!--ja-->
添字型を `Glued`{.Agda}、その h-集合性の証明を `squash/`{.Agda}、族を `Pick`{.Agda} として `sc`{.Agda} を適用する。`P`{.Agda} についての議論で選択を使うのはここだけである。各商点で代表元を選ぶ関数の単なる存在が得られる。
<!--/-->

```agda
  merePicker : SetChoice ℓ → ∥ ((x : Glued) → Pick x) ∥₁
  merePicker sc = sc Glued squash/ Pick pickable
```

<!--en-->
Why not simply choose `true`{.Agda} at `[ true ]`{.Agda} and `false`{.Agda} at `[ false ]`{.Agda}? These classes may be equal, and a function on the quotient must respect that equality. Choosing on the two named representatives separately does not establish a function on `Glued`{.Agda}.

Temporarily suppose such a function `g`{.Agda} is given. We will construct a decision of `P`{.Agda} from it, then justify eliminating the truncation into that decision. The booleans `b₀`{.Agda} and `b₁`{.Agda} are the first components of its values at the two distinguished classes.
<!--zh-->
为什么不直接在 `[ true ]`{.Agda} 处选 `true`{.Agda}，在 `[ false ]`{.Agda} 处选 `false`{.Agda}？这两个商类可能相等，而商上的函数必须尊重这种相等。分别在两个具名代表元处作出选取，还不能构成 `Glued`{.Agda} 上的函数。

暂设这样的函数 `g`{.Agda} 已经给出。我们先由它构造 `P`{.Agda} 的判定，随后说明为什么可以把截断消去到这一判定中。布尔值 `b₀`{.Agda} 与 `b₁`{.Agda} 是 `g`{.Agda} 在两个特殊商类处的值的第一分量。
<!--ja-->
`[ true ]`{.Agda} で `true`{.Agda} を、`[ false ]`{.Agda} で `false`{.Agda} を選ぶだけではなぜ足りないのか。この二つの商類は等しいかもしれず、商上の関数はその等しさを保たなければならない。二つの代表元で別々に選んでも、`Glued`{.Agda} 上の関数を定めたことにはならない。

いったん、そのような関数 `g`{.Agda} が与えられたとする。そこから `P`{.Agda} の判定を構成し、後でその判定へ切り詰めを消去できることを示す。`b₀`{.Agda} と `b₁`{.Agda} は、二つの商類での `g`{.Agda} の値の第一成分である。
<!--/-->

```agda
  module _ (g : (x : Glued) → Pick x) where

    b₀ : Bool
    b₀ = g [ true ] .fst

    b₁ : Bool
    b₁ = g [ false ] .fst
```

<!--en-->
If `q : b₀ ≡ b₁`{.Agda}, the certificates stored in `g`{.Agda} connect this agreement back to the quotient. Write $s_0$ and $s_1$ in the diagram for `g [ true ] .snd`{.Agda} and `g [ false ] .snd`{.Agda}. The first certificate points from `[ b₀ ]`{.Agda} to `[ true ]`{.Agda}, so the composite must use `sym`{.Agda} there.

Conversely, a proof `p : ⟨ P ⟩`{.Agda} gives the path `invEq quotientPath≃P p`{.Agda}, written $e^{-1}(p)$ in the diagram. The ordinary function `λ x → g x .fst`{.Agda} sends that path to `b₀ ≡ b₁`{.Agda}. Taking the first component makes the codomain the fixed type `Bool`{.Agda}, so `cong`{.Agda} suffices.
<!--zh-->
若有 `q : b₀ ≡ b₁`{.Agda}，`g`{.Agda} 中保存的证书就把这条相等接回商中。图中以 $s_0$、$s_1$ 分别简记 `g [ true ] .snd`{.Agda} 与 `g [ false ] .snd`{.Agda}。第一份证书从 `[ b₀ ]`{.Agda} 到 `[ true ]`{.Agda}，因此复合时要先用 `sym`{.Agda} 反向。

反过来，证明 `p : ⟨ P ⟩`{.Agda} 经逆映射给出路径 `invEq quotientPath≃P p`{.Agda}，图中写作 $e^{-1}(p)$。普通函数 `λ x → g x .fst`{.Agda} 把它送到 `b₀ ≡ b₁`{.Agda}。取第一分量后，值域是固定的 `Bool`{.Agda}，因此只需使用 `cong`{.Agda}。
<!--ja-->
`q : b₀ ≡ b₁`{.Agda} があれば、`g`{.Agda} に含まれる証明によって、この一致を商のパスへ結び付けられる。図では `g [ true ] .snd`{.Agda} と `g [ false ] .snd`{.Agda} をそれぞれ $s_0$、$s_1$ と略記する。最初の証明は `[ b₀ ]`{.Agda} から `[ true ]`{.Agda} へ向かうため、合成には `sym`{.Agda} で逆にしたものを使う。

逆に `p : ⟨ P ⟩`{.Agda} からは、逆写像によってパス `invEq quotientPath≃P p`{.Agda} が得られる。図ではこれを $e^{-1}(p)$ と書く。通常の関数 `λ x → g x .fst`{.Agda} はこのパスを `b₀ ≡ b₁`{.Agda} へ送る。第一成分を取れば終域は固定された型 `Bool`{.Agda} なので、`cong`{.Agda} で十分である。
<!--/-->

<figure class="book-diagram type-comparison path-figure" id="fig-choice-agreement" aria-describedby="fig-choice-agreement-caption">
<div class="diagram-framed">
<div class="type-comparison-panels">
<div class="type-comparison-panel">

$$q:b_0\equiv b_1$$

<div class="path-stage diagram-compact-stage" style="aspect-ratio:300/370">
<svg viewBox="0 0 300 370" aria-hidden="true" focusable="false">
<rect class="diagram-space-shape" x="12" y="10" width="276" height="350"/>
<path class="diagram-path" d="M 75 72 L 75 152"/>
<path class="diagram-path" d="M 75 152 L 75 232"/>
<path class="diagram-path" d="M 75 232 L 75 312"/>
<circle class="diagram-point" cx="75" cy="72" r="4"/>
<circle class="diagram-point" cx="75" cy="152" r="4"/>
<circle class="diagram-point" cx="75" cy="232" r="4"/>
<circle class="diagram-point" cx="75" cy="312" r="4"/>

</svg>
<span class="path-label" style="left:50%;top:9%">$\mathsf{Glued}$</span>
<span class="path-label" style="left:42%;top:19.46%">$[\mathsf{true}]$</span>
<span class="path-label" style="left:42%;top:41.08%">$[b_0]$</span>
<span class="path-label" style="left:42%;top:62.7%">$[b_1]$</span>
<span class="path-label" style="left:42%;top:84.32%">$[\mathsf{false}]$</span>
<span class="path-label" style="left:57%;top:30.27%">$\mathsf{sym}(s_0)$</span>
<span class="path-label" style="left:58%;top:51.89%">$\mathsf{cong}\,[{-}]\,q$</span>
<span class="path-label" style="left:57%;top:73.51%">$s_1$</span>
</div>
</div>
<div class="type-comparison-panel">

$$p:\langle P\rangle$$

<div class="path-stage diagram-compact-stage" style="aspect-ratio:300/370">
<svg viewBox="0 0 300 370" aria-hidden="true" focusable="false">
<rect class="diagram-space-shape" x="12" y="10" width="276" height="145"/>
<rect class="diagram-space-shape" x="12" y="215" width="276" height="145"/>
<path class="diagram-path" d="M 65 94 Q 150 48 235 94"/>
<path class="diagram-path" d="M 65 300 Q 150 254 235 300"/>
<circle class="diagram-point" cx="65" cy="94" r="4"/><circle class="diagram-point" cx="65" cy="300" r="4"/><path class="diagram-map-line" d="M 65 145 L 65 232"/><path class="diagram-map-tip" d="M 60 224 L 65 232 L 70 224"/>
<circle class="diagram-point" cx="235" cy="94" r="4"/><circle class="diagram-point" cx="235" cy="300" r="4"/><path class="diagram-map-line" d="M 235 145 L 235 232"/><path class="diagram-map-tip" d="M 230 224 L 235 232 L 240 224"/>

</svg>
<span class="path-label" style="left:50%;top:9%">$\mathsf{Glued}$</span>
<span class="path-label" style="left:50%;top:15%">$e^{-1}(p)$</span>
<span class="path-label" style="left:21.67%;top:33%">$[\mathsf{true}]$</span>
<span class="path-label" style="left:78.33%;top:33%">$[\mathsf{false}]$</span>
<span class="path-label" style="left:50%;top:50%">$x\mapsto g(x).\mathsf{fst}$</span>
<span class="path-label" style="left:50%;top:65%">$\mathsf{Bool}$</span>
<span class="path-label" style="left:21.67%;top:90%">$b_0$</span>
<span class="path-label" style="left:78.33%;top:90%">$b_1$</span>
</div>
</div>
</div>
</div>
<figcaption id="fig-choice-agreement-caption">

<!--en-->
On the left, $e$ sends the composite path to a proof of `P`{.Agda}. On the right, the selected boolean varies along $e^{-1}(p)$, giving agreement.
<!--zh-->
左图由 $e$ 把复合路径送到 `P`{.Agda} 的证明；右图沿 $e^{-1}(p)$ 读取所选布尔值，得到二者相等。
<!--ja-->
左図では $e$ が合成したパスを `P`{.Agda} の証明へ送る。右図では $e^{-1}(p)$ に沿って選んだブール値を読み、両者の等しさを得る。
<!--/-->

</figcaption>
</figure>

```agda

    agree→P : b₀ ≡ b₁ → ⟨ P ⟩
    agree→P q = equivFun quotientPath≃P
      (sym (g [ true ] .snd) ∙ cong [_] q ∙ g [ false ] .snd)

    P→agree : ⟨ P ⟩ → b₀ ≡ b₁
    P→agree p = cong (λ x → g x .fst) (invEq quotientPath≃P p)
```

<!--en-->
We now decide equality of the booleans, using `_≟_`{.Agda}. The two directions just proved convert its outcomes as follows:

| Boolean comparison | Decision of `P`{.Agda} |
| --- | --- |
| `yes q`{.Agda} | `yes (agree→P q)`{.Agda} |
| `no ne`{.Agda} | `no (λ p → ne (P→agree p))`{.Agda} |

In the second row, a proof of `P`{.Agda} would force the very equality that `ne`{.Agda} refutes. This is the negative map supplied to `mapDec`{.Agda}.
<!--zh-->
现在用 `_≟_`{.Agda} 判定两个布尔值是否相等。刚证明的两个方向把比较结果转换如下：

| 布尔值的比较 | 对 `P`{.Agda} 的判定 |
| --- | --- |
| `yes q`{.Agda} | `yes (agree→P q)`{.Agda} |
| `no ne`{.Agda} | `no (λ p → ne (P→agree p))`{.Agda} |

第二行中，`P`{.Agda} 的证明会迫使两个布尔值相等，而这正是 `ne`{.Agda} 所反驳的。因此得到传给 `mapDec`{.Agda} 的否定方向。
<!--ja-->
ここで `_≟_`{.Agda} を使って二つのブール値の等しさを判定する。証明した二方向によって、結果を次のように変換できる。

| ブール値の比較 | `P`{.Agda} の判定 |
| --- | --- |
| `yes q`{.Agda} | `yes (agree→P q)`{.Agda} |
| `no ne`{.Agda} | `no (λ p → ne (P→agree p))`{.Agda} |

第二行では、`P`{.Agda} の証明があれば、`ne`{.Agda} が否定する等しさが従ってしまう。これが `mapDec`{.Agda} に渡す否定側の写像である。
<!--/-->

```agda
    decide : Dec ⟨ P ⟩
    decide = mapDec agree→P (λ ne p → ne (P→agree p)) (b₀ ≟ b₁)
```

<!--en-->
Finally, we must use only the mere existence of `g`{.Agda}. This is possible because `Dec ⟨ P ⟩`{.Agda} is a proposition. Two positive answers agree by the propositionhood of `P`{.Agda}; two negative answers agree because negation is a proposition; a positive and a negative answer contradict each other. This is exactly `isPropDec`{.Agda}.
<!--zh-->
最后，必须把对具体 `g`{.Agda} 的使用还原为只依赖它的仅仅存在。这是可行的，因为 `Dec ⟨ P ⟩`{.Agda} 是命题：两个肯定回答由 `P`{.Agda} 的命题性而相等，两个否定回答由否定的命题性而相等，肯定与否定回答则不能同时存在。这正是 `isPropDec`{.Agda} 的内容。
<!--ja-->
最後に、具体的な `g`{.Agda} の使用を、その単なる存在だけに依存する形へ戻す。これは `Dec ⟨ P ⟩`{.Agda} が命題なので可能である。二つの肯定は `P`{.Agda} の命題性により等しく、二つの否定は否定の命題性により等しい。肯定と否定は同時には存在しない。これが `isPropDec`{.Agda} の内容である。
<!--/-->

```agda
  decideIsProp : isProp (Dec ⟨ P ⟩)
  decideIsProp = isPropDec ⟨ P ⟩isProp

```

<!--en-->
The same factorization through truncation that appeared in the Prelude now closes the proof. In the diagram, $G$ abbreviates the type `(x : Glued) → Pick x`{.Agda}. The map `decide`{.Agda} is defined on actual functions, while `rec₁ decideIsProp decide`{.Agda} accepts their mere existence.
<!--zh-->
《基础词汇》中经由截断的分解，在这里完成证明。图中 $G$ 简记类型 `(x : Glued) → Pick x`{.Agda}。`decide`{.Agda} 以实际函数为输入，`rec₁ decideIsProp decide`{.Agda} 则可以接收它们的仅仅存在。
<!--ja-->
「基礎語彙」で見た、切り詰めを経由する分解がここで証明を完成させる。図の $G$ は型 `(x : Glued) → Pick x`{.Agda} の略記である。`decide`{.Agda} は実際の関数を受け取り、`rec₁ decideIsProp decide`{.Agda} はその単なる存在を受け取る。
<!--/-->

<figure class="book-diagram type-comparison" id="fig-choice-truncation" aria-describedby="fig-choice-truncation-caption">
<div class="diagram-panel type-comparison-panel">

$$\begin{array}{ccc}
G & \xrightarrow{\;|{-}|_1\;} & \|G\|_1 \\[8pt]
\mathllap{{\scriptstyle\mathsf{decide}}\,}\Big\downarrow & & \Big\downarrow\mathrlap{\,{\scriptstyle\mathsf{rec}_1\,\cdots}} \\[8pt]
\mathsf{Dec}\,\langle P\rangle & \xrightarrow{\;\mathsf{id}\;} & \mathsf{Dec}\,\langle P\rangle
\end{array}$$

</div>
<figcaption id="fig-choice-truncation-caption">

<!--en-->
Choice supplies an element of $\|G\|_1$; the right-hand function returns a decision of `P`{.Agda}.
<!--zh-->
选择提供 $\|G\|_1$ 的元素，右侧函数由此返回 `P`{.Agda} 的判定。
<!--ja-->
選択が $\|G\|_1$ の要素を与え、右側の関数がそこから `P`{.Agda} の判定を返す。
<!--/-->

</figcaption>
</figure>

<!--en-->
Apply this function to `merePicker sc`{.Agda}. Since `P`{.Agda} was arbitrary, the result is `LEM ℓ`{.Agda}.
<!--zh-->
把这个函数应用于 `merePicker sc`{.Agda}。由于 `P`{.Agda} 任意，得到的正是 `LEM ℓ`{.Agda}。
<!--ja-->
この関数を `merePicker sc`{.Agda} に適用する。`P`{.Agda} は任意だったので、結果は `LEM ℓ`{.Agda} である。
<!--/-->

```agda
choice→lem : ∀ {ℓ} → SetChoice ℓ → LEM ℓ
choice→lem sc P = rec₁ decideIsProp decide (merePicker sc)
  where open Diaconescu P
```

∎

<!--en-->
## Recap

The content of `SetChoice`{.Agda} is the passage from pointwise mere existence to the mere existence of a whole function. `Lift`{.Agda} carries this principle down one universe level. In the proof of `choice→lem`{.Agda}, choice provides representatives uniformly on a quotient; their Boolean equality decides `P`{.Agda}, and the propositionhood of that decision lets us eliminate the truncation.

The chapter's two results have distinct uses in [the cumulative-hierarchy model](V.Model.html). From one hypothesis `SetChoice (ℓ-suc ℓ)`{.Agda}, `choice→lem`{.Agda} supplies excluded middle for the ZF construction, and `lowerSetChoice`{.Agda} supplies the lower-level choice used for the choice-set axiom. This concerns the ambient hierarchy `V`{.Agda}; the later construction of `L`{.Agda} proves its internal choice from excluded middle alone.
<!--zh-->
## 小结

`SetChoice`{.Agda} 的内容，是从逐点的仅仅存在过渡到整个函数的仅仅存在。`Lift`{.Agda} 使这条原理可以降低一个宇宙层级。`choice→lem`{.Agda} 的证明则在商上统一选取代表元，用它们的布尔相等判定 `P`{.Agda}，再借助这一判定的命题性消去截断。

本章的两个结果在[累积层级的模型](V.Model.html)中有不同用途。从一个假设 `SetChoice (ℓ-suc ℓ)`{.Agda} 出发，`choice→lem`{.Agda} 为 ZF 的构造提供排中律，`lowerSetChoice`{.Agda} 为选择集公理提供较低层级的选择。这说的是外部层级 `V`{.Agda}；后面的 `L`{.Agda} 的构造则只以排中律为前提，证明其内部选择成立。
<!--ja-->
## まとめ

`SetChoice`{.Agda} の内容は、添字ごとの単なる存在から、関数全体の単なる存在へ移ることである。`Lift`{.Agda} によって、この原理を一つ下の宇宙レベルへ移せる。`choice→lem`{.Agda} の証明では、選択によって商の上で一様に代表元を取り、そのブール値の等しさで `P`{.Agda} を判定する。最後に判定の命題性を使い、切り詰めを消去する。

二つの結果は、[累積階層のモデル](V.Model.html)で異なる役割をもつ。一つの仮定 `SetChoice (ℓ-suc ℓ)`{.Agda} から、`choice→lem`{.Agda} は ZF の構成に必要な排中律を与え、`lowerSetChoice`{.Agda} は選択集合公理に必要な低いレベルの選択を与える。これは外側の階層 `V`{.Agda} についての話である。後の `L`{.Agda} の構成では、排中律だけを仮定して内部の選択を証明する。
<!--/-->
