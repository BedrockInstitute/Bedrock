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

直謂的な基礎では、一つの定義の中で、定義される対象をすでに含む全体にわたって量化することを認めない。Cubical Agda はこのような基礎の上にあるが、本書で形式化する集合論には非可述的な構成が含まれる。そこで本章では、ホストの基礎そのものを変えずに、それらの構成に必要な追加条件を明示的な仮定として述べる。

直謂的な基礎が非可述的な仮定を受け入れられることは、直観主義論理が古典論理の原理を明示的に仮定できることに似ている。逆は成り立たない。強い原理を初めから基礎に組み込めば、後の結果がそのどれに依存するかを区別できなくなるからである。本書は Cubical Agda の直謂的な基礎を保ち、非可述性が必要な箇所で条件を一つずつ明記する。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

module Base.Impredicativity where

open import Base.Prelude
open import Cubical.Foundations.HLevels using ( isOfHLevelRespectEquiv )
```

<!--en-->
The issue appears in the universe levels. All propositions whose [underlying types]{.term-ref #underlying-type} lie in `Type ℓ`{.Agda} form `hProp ℓ`{.Agda}, but this proposition universe as a whole belongs to `Type (ℓ-suc ℓ)`{.Agda}. A proposition obtained by quantifying over all of `hProp ℓ`{.Agda} need not fit at level `ℓ`.

For example, suppose we define a proposition `R` by saying that every `Q : hProp ℓ`{.Agda} implies itself, and also demand that `R` belong to `hProp ℓ`{.Agda}. Then the quantifier over every `Q` also ranges over `R`: the totality being quantified over already includes the proposition being defined. The claim that `Q` implies itself is elementary; the difficulty is the demand that this quantification produce a proposition at the same level. In Cubical Agda the quantification instead lives one universe higher. User code cannot rewrite Agda's universe-level rules, but an explicit assumption can connect the higher proposition to a lower representative with the same truth content. We must now say how to express that connection.
<!--zh-->
困难来自宇宙层级。[底层类型]{.term-ref #underlying-type}位于 `Type ℓ`{.Agda} 的所有命题组成 `hProp ℓ`{.Agda}，而这个命题宇宙整体属于 `Type (ℓ-suc ℓ)`{.Agda}。因此，对 `hProp ℓ`{.Agda} 中所有命题量化所得的命题，不一定仍能放在层级 `ℓ`。

例如，试图把命题 `R` 定义为「每个 `Q : hProp ℓ`{.Agda} 都蕴含自身」，同时要求 `R` 也属于 `hProp ℓ`{.Agda}。这样，定义中的「每个 `Q`」也遍及 `R`：量化的总体已经包含正在定义的命题。「`Q` 蕴含自身」虽然显然成立，难点仍是要求这次量化所得的命题留在同一层级。在 Cubical Agda 中，它位于高一层的宇宙。Agda 的用户代码不能改写其宇宙层级规则，但可以通过显式假设，把这个高层命题与真值内容相同的低层代表联系起来。接下来需要说明怎样表达这种联系。
<!--ja-->
問題は宇宙レベルに現れる。[基礎型]{.term-ref #underlying-type}が `Type ℓ`{.Agda} に属するすべての命題は `hProp ℓ`{.Agda} をなすが、この命題の宇宙全体は `Type (ℓ-suc ℓ)`{.Agda} に属する。したがって、`hProp ℓ`{.Agda} のすべての命題にわたる量化から得た命題が、再びレベル `ℓ` に収まるとは限らない。

例えば、命題 `R` を「すべての `Q : hProp ℓ`{.Agda} は自分自身を含意する」と定義し、同時に `R` も `hProp ℓ`{.Agda} に属すると要求してむ。このとき、定義中の「すべての `Q`」は `R` 自身にも及ぶ。量化する全体が、定義中の命題をすでに含んでいるのである。「`Q` は自分自身を含意する」という主張は明らかであるが、その量化から得た命題を同じレベルに置くという要求が問題である。Cubical Agda では、この量化は一つ上の宇宙に属する。Agda のユーザーコードから宇宙レベルの規則を書き換えることはできないが、明示的な仮定によって、上位の命題と真理内容が同じ下位の代表を結び付けられる。次に、この結び付きをどう表すかを定める。
<!--/-->

<!--en-->
A path cannot directly express this connection, because its endpoints must belong to a common ambient type, while the higher and lower propositions inhabit different universes. [Logical equivalence]{.term-intro #logical-equivalence} can express mutual implication between propositions. Sometimes, however, we must connect an entire higher proposition universe with a type in a lower universe. This is no longer a connection between two propositions. We therefore need a notion that connects arbitrary types: **[type equivalence]{.term-intro #type-equivalence}**.
<!--zh-->
路径不能直接表达这种联系，因为路径的两端必须属于同一个环境类型，而高层命题与低层命题位于不同的宇宙。[逻辑等价]{.term-intro #logical-equivalence}可以说明两个命题互相蕴含。不过，我们有时还需要把整个高层命题宇宙与低层宇宙中的一个类型联系起来；这已经不是两个命题之间的联系。因此，我们需要一种能联系任意类型的概念，这就是**[类型等价]{.term-intro #type-equivalence}**。
<!--ja-->
パスはこの結び付きを直接には表せない。パスの両端は共通の型に属する必要があるが、上位と下位の命題は異なる宇宙に属するからである。[論理的同値]{.term-intro #logical-equivalence}は命題間の両方向の含意を表せる。しかし、命題の上位宇宙全体を下位宇宙の一つの型と結び付ける必要もある。これはもはや二つの命題の間の結び付きではない。そこで、任意の型を結び付けられる概念として**[型同値]{.term-intro #type-equivalence}**を用いる。
<!--/-->

<!--en-->
## Type equivalence

For types `A` and `B`, `A ≃ B`{.Agda} is a [dependent pair]{.term-ref #dependent-pair}. Its [first component]{.term-ref #first-component} is a map `f : A → B`{.Agda}; its [second component]{.term-ref #second-component} is a [certificate]{.term-ref #certificate} depending on `f`. To read this certificate, we first need the following definition.
<!--zh-->
## 类型等价

对类型 `A` 与 `B`，`A ≃ B`{.Agda} 是一个[依值对]{.term-ref #dependent-pair}。它的[第一分量]{.term-ref #first-component}是映射 `f : A → B`{.Agda}；[第二分量]{.term-ref #second-component}是依赖于 `f` 的[证书]{.term-ref #certificate}。要读懂这份证书，先看下面的定义。
<!--ja-->
## 型同値

型 `A` と `B` について、`A ≃ B`{.Agda} は[依存対]{.term-ref #dependent-pair}である。その[第一成分]{.term-ref #first-component}は写像 `f : A → B`{.Agda}、[第二成分]{.term-ref #second-component}は `f` に依存する[証明書]{.term-ref #certificate}である。この証明書を読むために、まず次の定義を見る。
<!--/-->

<!--en-->
For a fixed `b : B`{.Agda}, the **[fibre]{.term-intro #fiber}** of `f` over `b` is the dependent pair type:

<div class="single-line-code"><code>Σ (a : A) (f a ≡ b)</code></div>

An element of the fibre has two components. The first is a candidate preimage `a : A`{.Agda}; the second is a path `f a ≡ b`{.Agda} witnessing that this candidate really maps to `b`. An empty fibre means that `b` has no preimage. Elements of a fibre that cannot be identified by a path represent substantively different ways to return from `b` to `A`.

The animation assumes that every fibre is contractible: there is a centre and a family of paths connecting each dependent pair in the fibre to that centre.
<!--zh-->
对固定的 `b : B`{.Agda}，`f` 在 `b` 上的**[纤维]{.term-intro #fiber}**是下面这个依值对类型：

<div class="single-line-code"><code>Σ (a : A) (f a ≡ b)</code></div>

纤维的一个元素由两部分组成：第一分量是一个候选原像 `a : A`{.Agda}，第二分量是一条路径 `f a ≡ b`{.Agda}，证明这个 `a` 的确映到 `b`。纤维为空，表示 `b` 没有原像；纤维中若有彼此不能通过路径等同的元素，则表示从 `b` 返回 `A` 时存在实质不同的选择。

下面的动画假设每束纤维可缩：存在一个中心，以及一族将纤维中每个依值对连接到中心的路径。
<!--ja-->
固定した `b : B`{.Agda} 上の `f` の**[ファイバー]{.term-intro #fiber}**は、次の依存対型である。

<div class="single-line-code"><code>Σ (a : A) (f a ≡ b)</code></div>

ファイバーの要素は二つの成分を持つ。第一成分は原像の候補 `a : A`{.Agda}、第二成分はその候補が実際に `b` へ写ることを示すパス `f a ≡ b`{.Agda} である。ファイバーが空なら `b` に原像はない。ファイバーにパスで同一視できない要素があれば、`b` から `A` へ戻る方法に本質的な違いが残っている。

以下のアニメーションでは各ファイバーの可縮性を仮定する。すなわち、中心と、ファイバーの各依存対をその中心へ結ぶパスの族が存在する。
<!--/-->

<figure class="book-diagram path-figure fiber-general" id="fig-fiber-general" aria-describedby="fig-fiber-general-caption">
<div class="diagram-framed">

$$F_b=\sum_{a:A}\bigl(f(a)\equiv b\bigr)$$

<div class="path-stage fiber-fan-stage" style="aspect-ratio:680/460">
<svg viewBox="0 0 680 460" aria-hidden="true" focusable="false">
<rect class="diagram-space-shape" x="30" y="20" width="620" height="90"/>
<rect class="diagram-space-shape" x="30" y="185" width="620" height="250"/>
<g class="fiber-bundle" data-fiber="0" data-center-path="M120 390 C80 352 80 289 120 235">
<path class="diagram-map-line fiber-moving-map" d="M48 102 L48 225"/>
<path class="diagram-map-tip fiber-moving-tip" d="M44 218 L48 225 L52 218"/>
<path class="diagram-map-line fiber-moving-map" d="M96 102 L96 225"/>
<path class="diagram-map-tip fiber-moving-tip" d="M92 218 L96 225 L100 218"/>
<path class="diagram-map-line fiber-moving-map" d="M144 102 L144 225"/>
<path class="diagram-map-tip fiber-moving-tip" d="M140 218 L144 225 L148 218"/>
<path class="diagram-map-line fiber-moving-map" d="M192 102 L192 225"/>
<path class="diagram-map-tip fiber-moving-tip" d="M188 218 L192 225 L196 218"/>
<path class="diagram-path fiber-hair" d="M120 390 C33 358 33 292 48 235"/>
<path class="diagram-path fiber-hair" d="M120 390 C63 358 63 292 48 235"/>
<path class="diagram-path fiber-hair" d="M120 390 C81 358 81 292 96 235"/>
<path class="diagram-path fiber-hair" d="M120 390 C111 358 111 292 96 235"/>
<path class="diagram-path fiber-hair" d="M120 390 C129 358 129 292 144 235"/>
<path class="diagram-path fiber-hair" d="M120 390 C159 358 159 292 144 235"/>
<path class="diagram-path fiber-hair" d="M120 390 C177 358 177 292 192 235"/>
<path class="diagram-path fiber-hair" d="M120 390 C207 358 207 292 192 235"/>
<circle class="diagram-point fiber-domain-point" cx="48" cy="98" r="4"/>
<circle class="diagram-point fiber-image-point" cx="48" cy="235" r="4"/>
<circle class="diagram-point fiber-domain-point" cx="96" cy="98" r="4"/>
<circle class="diagram-point fiber-image-point" cx="96" cy="235" r="4"/>
<circle class="diagram-point fiber-domain-point" cx="144" cy="98" r="4"/>
<circle class="diagram-point fiber-image-point" cx="144" cy="235" r="4"/>
<circle class="diagram-point fiber-domain-point" cx="192" cy="98" r="4"/>
<circle class="diagram-point fiber-image-point" cx="192" cy="235" r="4"/>
<circle class="diagram-point fiber-base-point" cx="120" cy="390" r="5"/>
</g>
<g class="fiber-bundle" data-fiber="1" data-center-path="M340 390 C300 352 300 289 340 235">
<path class="diagram-map-line fiber-moving-map" d="M268 102 L268 225"/>
<path class="diagram-map-tip fiber-moving-tip" d="M264 218 L268 225 L272 218"/>
<path class="diagram-map-line fiber-moving-map" d="M316 102 L316 225"/>
<path class="diagram-map-tip fiber-moving-tip" d="M312 218 L316 225 L320 218"/>
<path class="diagram-map-line fiber-moving-map" d="M364 102 L364 225"/>
<path class="diagram-map-tip fiber-moving-tip" d="M360 218 L364 225 L368 218"/>
<path class="diagram-map-line fiber-moving-map" d="M412 102 L412 225"/>
<path class="diagram-map-tip fiber-moving-tip" d="M408 218 L412 225 L416 218"/>
<path class="diagram-path fiber-hair" d="M340 390 C253 358 253 292 268 235"/>
<path class="diagram-path fiber-hair" d="M340 390 C283 358 283 292 268 235"/>
<path class="diagram-path fiber-hair" d="M340 390 C301 358 301 292 316 235"/>
<path class="diagram-path fiber-hair" d="M340 390 C331 358 331 292 316 235"/>
<path class="diagram-path fiber-hair" d="M340 390 C349 358 349 292 364 235"/>
<path class="diagram-path fiber-hair" d="M340 390 C379 358 379 292 364 235"/>
<path class="diagram-path fiber-hair" d="M340 390 C397 358 397 292 412 235"/>
<path class="diagram-path fiber-hair" d="M340 390 C427 358 427 292 412 235"/>
<circle class="diagram-point fiber-domain-point" cx="268" cy="98" r="4"/>
<circle class="diagram-point fiber-image-point" cx="268" cy="235" r="4"/>
<circle class="diagram-point fiber-domain-point" cx="316" cy="98" r="4"/>
<circle class="diagram-point fiber-image-point" cx="316" cy="235" r="4"/>
<circle class="diagram-point fiber-domain-point" cx="364" cy="98" r="4"/>
<circle class="diagram-point fiber-image-point" cx="364" cy="235" r="4"/>
<circle class="diagram-point fiber-domain-point" cx="412" cy="98" r="4"/>
<circle class="diagram-point fiber-image-point" cx="412" cy="235" r="4"/>
<circle class="diagram-point fiber-base-point" cx="340" cy="390" r="5"/>
</g>
<g class="fiber-bundle" data-fiber="2" data-center-path="M560 390 C520 352 520 289 560 235">
<path class="diagram-map-line fiber-moving-map" d="M488 102 L488 225"/>
<path class="diagram-map-tip fiber-moving-tip" d="M484 218 L488 225 L492 218"/>
<path class="diagram-map-line fiber-moving-map" d="M536 102 L536 225"/>
<path class="diagram-map-tip fiber-moving-tip" d="M532 218 L536 225 L540 218"/>
<path class="diagram-map-line fiber-moving-map" d="M584 102 L584 225"/>
<path class="diagram-map-tip fiber-moving-tip" d="M580 218 L584 225 L588 218"/>
<path class="diagram-map-line fiber-moving-map" d="M632 102 L632 225"/>
<path class="diagram-map-tip fiber-moving-tip" d="M628 218 L632 225 L636 218"/>
<path class="diagram-path fiber-hair" d="M560 390 C473 358 473 292 488 235"/>
<path class="diagram-path fiber-hair" d="M560 390 C503 358 503 292 488 235"/>
<path class="diagram-path fiber-hair" d="M560 390 C521 358 521 292 536 235"/>
<path class="diagram-path fiber-hair" d="M560 390 C551 358 551 292 536 235"/>
<path class="diagram-path fiber-hair" d="M560 390 C569 358 569 292 584 235"/>
<path class="diagram-path fiber-hair" d="M560 390 C599 358 599 292 584 235"/>
<path class="diagram-path fiber-hair" d="M560 390 C617 358 617 292 632 235"/>
<path class="diagram-path fiber-hair" d="M560 390 C647 358 647 292 632 235"/>
<circle class="diagram-point fiber-domain-point" cx="488" cy="98" r="4"/>
<circle class="diagram-point fiber-image-point" cx="488" cy="235" r="4"/>
<circle class="diagram-point fiber-domain-point" cx="536" cy="98" r="4"/>
<circle class="diagram-point fiber-image-point" cx="536" cy="235" r="4"/>
<circle class="diagram-point fiber-domain-point" cx="584" cy="98" r="4"/>
<circle class="diagram-point fiber-image-point" cx="584" cy="235" r="4"/>
<circle class="diagram-point fiber-domain-point" cx="632" cy="98" r="4"/>
<circle class="diagram-point fiber-image-point" cx="632" cy="235" r="4"/>
<circle class="diagram-point fiber-base-point" cx="560" cy="390" r="5"/>
</g>
</svg>
<span class="path-label" style="left:7.5000%;top:8.0435%">$A$</span>
<span class="path-label" style="left:7.5000%;top:89.5652%">$B$</span>
<span class="path-label" style="left:53.9706%;top:32.3913%">$f$</span>
<span class="path-label fiber-sample-label" data-fiber="0" style="left:7.0588%;top:16.3043%">$a_{00}$</span>
<span class="path-label fiber-sample-label" data-fiber="0" style="left:14.1176%;top:16.3043%">$a_{01}$</span>
<span class="path-label fiber-sample-label" data-fiber="0" style="left:21.1765%;top:16.3043%">$a_{02}$</span>
<span class="path-label fiber-sample-label" data-fiber="0" style="left:28.2353%;top:16.3043%">$a_{03}$</span>
<span class="path-label fiber-center-label" aria-hidden="true" style="left:17.6471%;top:16.3043%">$a_0$</span>
<span class="path-label" style="left:17.6471%;top:90.2174%">$b_0$</span>
<span class="path-label fiber-sample-label" data-fiber="1" style="left:39.4118%;top:16.3043%">$a_{10}$</span>
<span class="path-label fiber-sample-label" data-fiber="1" style="left:46.4706%;top:16.3043%">$a_{11}$</span>
<span class="path-label fiber-sample-label" data-fiber="1" style="left:53.5294%;top:16.3043%">$a_{12}$</span>
<span class="path-label fiber-sample-label" data-fiber="1" style="left:60.5882%;top:16.3043%">$a_{13}$</span>
<span class="path-label fiber-center-label" aria-hidden="true" style="left:50.0000%;top:16.3043%">$a_1$</span>
<span class="path-label" style="left:50.0000%;top:90.2174%">$b_1$</span>
<span class="path-label fiber-sample-label" data-fiber="2" style="left:71.7647%;top:16.3043%">$a_{20}$</span>
<span class="path-label fiber-sample-label" data-fiber="2" style="left:78.8235%;top:16.3043%">$a_{21}$</span>
<span class="path-label fiber-sample-label" data-fiber="2" style="left:85.8824%;top:16.3043%">$a_{22}$</span>
<span class="path-label fiber-sample-label" data-fiber="2" style="left:92.9412%;top:16.3043%">$a_{23}$</span>
<span class="path-label fiber-center-label" aria-hidden="true" style="left:82.3529%;top:16.3043%">$a_2$</span>
<span class="path-label" style="left:82.3529%;top:90.2174%">$b_2$</span>
</div>
</div>
<figcaption id="fig-fiber-general-caption">
<!--en-->
Click the pulsing fibres to contract; click again to expand. The paths in each tuft merge into a single path $p_i$ from $f(a_i)$ to $b_i$, while the candidate preimages merge into $a_i$. The coincidence depicts equality by paths. The condition for $f$ to be an equivalence is that every fibre is contractible.
<!--zh-->
点击闪烁的三束纤维收拢，再次点击展开。每束路径合并为连接 $f(a_i)$ 与 $b_i$ 的一条路径 $p_i$，原像候选则合并为 $a_i$。这里的重合表示路径意义下的相等。每束纤维可缩，正是 $f$ 成为等价的条件。
<!--ja-->
点滅するファイバーをクリックすると収縮し、もう一度クリックすると広がる。各毛束のパスは $f(a_i)$ と $b_i$ を結ぶ一本のパス $p_i$ に合流し、原像の候補は $a_i$ に合流する。重なりはパスによる等しさを表す。各ファイバーが可縮であることが、$f$ が同値となる条件である。
<!--/-->
</figcaption>
</figure>



```agda
open import Cubical.Foundations.Equiv using ( _≃_ )
```

<!--en-->
This notion should be distinguished from an [isomorphism]{.term-intro #type-isomorphism}, which explicitly presents maps $f:A→B$ and $g:B→A$ and the two [round-trip laws]{.term-intro #round-trip-law}: paths $g(f(a))≡a$ for every $a:A$ and $f(g(b))≡b$ for every $b:B$. The definitions imported below express how the notions are related: `iso`{.Agda} packages those data as `Iso A B`{.Agda}, and `isoToEquiv`{.Agda} converts the result into `A ≃ B`{.Agda}. Explicit maps make isomorphisms convenient for constructing examples, while the cubical library uses equivalences as the common interface for transporting type structure.
<!--zh-->
这里的[类型等价]{.term-ref #type-equivalence}需要与[同构]{.term-intro #type-isomorphism}区分：同构显式给出映射 $f:A→B$、$g:B→A$ 和两条[往返律]{.term-intro #round-trip-law}：对每个 $a:A$ 有路径 $g(f(a))≡a$，对每个 $b:B$ 有路径 $f(g(b))≡b$。下面导入的定义说明了二者的联系：`iso`{.Agda} 把这些数据打包成 `Iso A B`{.Agda}，`isoToEquiv`{.Agda} 再把所得同构转换为 `A ≃ B`{.Agda}。显式列出映射使同构便于构造具体例子，立方库则以[类型等价]{.term-ref #type-equivalence}作为搬运类型结构的统一接口。
<!--ja-->
この[型同値]{.term-ref #type-equivalence}は[同型]{.term-intro #type-isomorphism}と区別する必要がある。同型は写像 $f:A→B$、$g:B→A$ と二つの[往復則]{.term-intro #round-trip-law}を明示的に与える。すなわち、各 $a:A$ に対するパス $g(f(a))≡a$ と、各 $b:B$ に対するパス $f(g(b))≡b$ である。以下で導入する定義は両者の関係を表す。`iso`{.Agda} はこれらのデータを `Iso A B`{.Agda} にまとめ、`isoToEquiv`{.Agda} は得られた同型を `A ≃ B`{.Agda} へ変換する。写像を明示する同型は具体例の構成に便利であり、Cubical ライブラリは型の構造を運ぶ共通のインターフェースとして型同値を用いる。
<!--/-->

```agda
open import Cubical.Foundations.Isomorphism using ( Iso; iso; isoToEquiv )
```

<!--en-->
The three notions thus serve different parts of an argument in this book. We often construct an isomorphism to prove an equivalence, use equivalences to preserve and transport structure, and finally connect objects by a path once they lie in the same ambient type.
<!--zh-->
这样便可以看清三个概念在本书论证中的分工：证明[类型等价]{.term-ref #type-equivalence}时常先构造同构，保存和搬运结构时统一使用[类型等价]{.term-ref #type-equivalence}，而当两个对象已经位于同一个环境类型中时，最终往往通过[路径]{.term-ref #path}建立联系。
<!--ja-->
以上の三つの概念は、本書の議論で異なる役割を担う。[型同値]{.term-ref #type-equivalence}を証明するときにはまず同型を構成することが多く、構造を保存して運ぶときには[型同値]{.term-ref #type-equivalence}を共通の形として用い、二つの対象が同じ型に属するところまで来れば、最後には[パス]{.term-ref #path}によって結び付ける。
<!--/-->

<!--en-->
## [Propositional resizing]{.term-intro #propositional-resizing}

We can now return to the universe-level problem that motivated type equivalence. Given `P : hProp ℓ₁`{.Agda}, Agda does not let us change the level at which `P` lives. What we can ask for is another proposition `Q : hProp ℓ₂`{.Agda} whose underlying type is connected to that of `P` by a [type equivalence]{.term-ref #type-equivalence}.

**Definition** (`hasSize`{.Agda}) We read `hasSize ℓ₂ P`{.Agda} as saying that `P`{.Agda} has size `ℓ₂`{.Agda}, and define it as the dependent pair below. Its first component chooses `Q`, and its second component gives the type equivalence showing that `Q` has exactly the truth content of `P`.
<!--zh-->
## [命题换级]{.term-intro #propositional-resizing}

现在回到促使我们引入[类型等价]{.term-ref #type-equivalence}的宇宙层级问题。给定 `P : hProp ℓ₁`{.Agda}，Agda 不允许我们直接改变 `P` 所在的层级；能够提出的要求，是在目标层级找到另一个命题 `Q : hProp ℓ₂`{.Agda}，使二者的底层类型[类型等价]{.term-ref #type-equivalence}。

**定义** (`hasSize`{.Agda}) 我们把「`P`{.Agda} 具有尺寸 `ℓ₂`{.Agda}」记作 `hasSize ℓ₂ P`{.Agda}，并将其定义为以下依值对：第一分量选出 `Q`，第二分量给出[类型等价]{.term-ref #type-equivalence}，表明 `Q` 与 `P` 具有完全相同的真值内容。
<!--ja-->
## [命題リサイズ]{.term-intro #propositional-resizing}

ここで、[型同値]{.term-ref #type-equivalence}を導入する動機となった宇宙レベルの問題に戻る。`P : hProp ℓ₁`{.Agda} が与えられても、Agda では `P` の属するレベルを直接変更できない。代わりに、目標レベルの別の命題 `Q : hProp ℓ₂`{.Agda} を見つけ、その基礎型が `P` の基礎型と[型同値]{.term-ref #type-equivalence}であることを要求できる。

**定義** (`hasSize`{.Agda}) ここでは「`P`{.Agda} はサイズ `ℓ₂`{.Agda} をもつ」を `hasSize ℓ₂ P`{.Agda} と表し、次の依存対として定義する。第一成分は `Q` を選び、第二成分は `Q` と `P` の真理内容が完全に一致することを示す[型同値]{.term-ref #type-equivalence}を与える。
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
二つのレベルの大小関係は仮定しない。後の応用では通常、`ℓ₁` はモデルの真理値のレベル、`ℓ₂` は添字のレベルであるが、定義そのものは任意の二つのレベルに適用できる。「命題リサイズ」とは、元の命題の宇宙注釈を変更することではなく、目標レベルにある[型同値]{.term-ref #type-equivalence}な代表で置き換えることを指す。
<!--/-->

<!--en-->
**Definition** (`Resizing`{.Agda}) We read `Resizing ℓ₁ ℓ₂`{.Agda} as saying that propositions at level `ℓ₁`{.Agda} can be resized to level `ℓ₂`{.Agda}, and define it as the dependent function below. For each `P : hProp ℓ₁`{.Agda}, it returns a witness that `P` has size `ℓ₂`{.Agda}.
<!--zh-->
**定义** (`Resizing`{.Agda}) 我们把「`ℓ₁`{.Agda} 层的命题可换级到 `ℓ₂`{.Agda} 层」记作 `Resizing ℓ₁ ℓ₂`{.Agda}，并将其定义为以下[依值函数]{.term-ref #dependent-function}：对每个 `P : hProp ℓ₁`{.Agda}，它返回「`P` 具有尺寸 `ℓ₂`{.Agda}」的见证。
<!--ja-->
**定義** (`Resizing`{.Agda}) ここでは「レベル `ℓ₁`{.Agda} の命題をレベル `ℓ₂`{.Agda} へリサイズできる」を `Resizing ℓ₁ ℓ₂`{.Agda} と表し、次の依存関数として定義する。各 `P : hProp ℓ₁`{.Agda} に対して、「`P` はサイズ `ℓ₂`{.Agda} をもつ」ことの証拠を返す。
<!--/-->

```agda
Resizing : ∀ ℓ₁ ℓ₂ → Type (ℓ-max (ℓ-suc ℓ₁) (ℓ-suc ℓ₂))
Resizing ℓ₁ ℓ₂ = (P : hProp ℓ₁) → hasSize ℓ₂ P
```

<!--en-->
## [Ω-resizing]{.term-intro #proposition-universe-resizing}

**Definition** (`ΩResizing`{.Agda}) We read `ΩResizing ℓ₁ ℓ₂`{.Agda} as saying that the proposition universe `hProp ℓ₁`{.Agda} has size `ℓ₂`{.Agda}, and define it as the dependent pair below. Its first component chooses a type `Ω : Type ℓ₂`{.Agda}; its second gives a [type equivalence]{.term-ref #type-equivalence} `hProp ℓ₁ ≃ Ω`{.Agda}. Thus every proposition at `ℓ₁` has a code in `Ω`, and every element of `Ω` decodes to such a proposition.
<!--zh-->
## [命题宇宙换级]{.term-intro #proposition-universe-resizing}

**定义** (`ΩResizing`{.Agda}) 我们把「命题宇宙 `hProp ℓ₁`{.Agda} 具有尺寸 `ℓ₂`{.Agda}」记作 `ΩResizing ℓ₁ ℓ₂`{.Agda}，并将其定义为以下依值对：第一分量给出类型 `Ω : Type ℓ₂`{.Agda}，第二分量给出[类型等价]{.term-ref #type-equivalence} `hProp ℓ₁ ≃ Ω`{.Agda}。因此，`ℓ₁` 层的每个命题都在 `Ω` 中有编码，而 `Ω` 的每个元素也都解码为该层的命题。
<!--ja-->
## [命題宇宙リサイズ]{.term-intro #proposition-universe-resizing}

**定義** (`ΩResizing`{.Agda}) ここでは「命題宇宙 `hProp ℓ₁`{.Agda} はサイズ `ℓ₂`{.Agda} をもつ」を `ΩResizing ℓ₁ ℓ₂`{.Agda} と表し、次の依存対として定義する。第一成分は型 `Ω : Type ℓ₂`{.Agda} を与え、第二成分は[型同値]{.term-ref #type-equivalence} `hProp ℓ₁ ≃ Ω`{.Agda} を与える。したがって、レベル `ℓ₁` の各命題は `Ω` に符号をもち、`Ω` の各要素はそのレベルの命題へ復号される。
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
**Theorem** (`ΩResizing→Resizing`{.Agda}) Ω-resizing implies propositional resizing.
<!--zh-->
**定理** (`ΩResizing→Resizing`{.Agda}) 命题宇宙换级蕴含命题换级。
<!--ja-->
**定理** (`ΩResizing→Resizing`{.Agda}) 命題宇宙リサイズは命題リサイズを導く。
<!--/-->

```agda
ΩResizing→Resizing : ∀ {ℓ₁ ℓ₂} → ΩResizing ℓ₁ ℓ₂ → Resizing ℓ₁ ℓ₂
```

<!--en-->
**Proof** For each `P`, choose `codedTruth P`{.Agda} as its representative. The isomorphism `codedTruthIso P`{.Agda}, converted by `isoToEquiv`{.Agda}, supplies the required type equivalence.
<!--zh-->
**证明** 对每个 `P`，取 `codedTruth P`{.Agda} 为代表。把同构 `codedTruthIso P`{.Agda} 经 `isoToEquiv`{.Agda} 转换，便得到所需的类型等价。
<!--ja-->
**証明** 各 `P` について `codedTruth P`{.Agda} を代表に取る。同型 `codedTruthIso P`{.Agda} を `isoToEquiv`{.Agda} で変換すれば、必要な型同値が得られる。
<!--/-->

```agda
ΩResizing→Resizing {ℓ₁} {ℓ₂} (Ω , e) P =
  codedTruth P , isoToEquiv (codedTruthIso P)
  where
```

<details open class="optional-reading" aria-labelledby="coded-truth-construction-title">
<!--en-->
<summary class="optional-reading-title" id="coded-truth-construction-title">Optional: construction of `codedTruth`{.Agda} and `codedTruthIso`{.Agda}</summary>
<!--zh-->
<summary class="optional-reading-title" id="coded-truth-construction-title">选读：`codedTruth`{.Agda} 和 `codedTruthIso`{.Agda} 的构造</summary>
<!--ja-->
<summary class="optional-reading-title" id="coded-truth-construction-title">発展：`codedTruth`{.Agda} と `codedTruthIso`{.Agda} の構成</summary>
<!--/-->

<!--en-->
To construct the representative used above, the given equivalence `e : hProp ℓ₁ ≃ Ω`{.Agda} lets us encode propositions as points of `Ω`. We name its forward map `c`{.Agda}; thus `c P`{.Agda} is the code of `P`.
<!--zh-->
为构造上面使用的代表，我们借助给定的类型等价 `e : hProp ℓ₁ ≃ Ω`{.Agda}，把命题编码为 `Ω` 中的点。将其正向映射命名为 `c`{.Agda}，于是 `c P`{.Agda} 就是命题 `P` 的编码。
<!--ja-->
上で用いた代表を構成するために、与えられた型同値 `e : hProp ℓ₁ ≃ Ω`{.Agda} によって、命題を `Ω` の点として符号化できる。その順写像を `c`{.Agda} と名付けると、`c P`{.Agda} が命題 `P` の符号となる。
<!--/-->

```agda
  open import Cubical.Foundations.Equiv using ( equivFun; invEq )
  open import Cubical.Foundations.Equiv.Properties using ( congEquiv )

  c : hProp ℓ₁ → Ω
  c = equivFun e
```

<!--en-->
**Construction** (`codedTruth`{.Agda}) The code `c P`{.Agda} is a point of `Ω`. To obtain a proposition, ask whether it equals the code of truth: `c ⊤ ≡ c P`{.Agda}. This path type lies at level `ℓ₂`. It is a proposition because `e`{.Agda} transfers the h-set structure of `hProp ℓ₁`{.Agda} to `Ω`. We take it as the representative of `P`; the isomorphism below verifies that it has the same truth content.
<!--zh-->
**构造** (`codedTruth`{.Agda}) 编码 `c P`{.Agda} 是 `Ω` 中的一个点。要得到命题，就问它是否等于真命题的编码：`c ⊤ ≡ c P`{.Agda}。这个路径类型位于 `ℓ₂` 层；`e`{.Agda} 把 `hProp ℓ₁`{.Agda} 的 h-集合结构搬运到 `Ω`，保证它是命题。我们取它作为 `P` 的代表，下面的同构将证明二者具有相同的真值内容。
<!--ja-->
**構成** (`codedTruth`{.Agda}) 符号 `c P`{.Agda} は `Ω` の一点である。命題を得るには、それが真の命題の符号と等しいかを問えばよい：`c ⊤ ≡ c P`{.Agda}。このパス型はレベル `ℓ₂` に属する。`e`{.Agda} が `hProp ℓ₁`{.Agda} の h-集合構造を `Ω` へ運ぶので、これは命題である。これを `P` の代表とし、以下の同型によって真理内容が等しいことを確かめる。
<!--/-->

```agda
  codedTruth : hProp ℓ₁ → hProp ℓ₂
  codedTruth P = (c ⊤ ≡ c P) , isOfHLevelRespectEquiv 2 e isSetHProp _ _
```

<!--en-->
The band in `Ω` depicts paths with endpoints `c(⊤)` and `c(P)`. Click it to unfold the path family into the second type space, with whole paths represented as points. The illustrated `q` and `r` presuppose that `P` has a proof; the equivalence with `⟨ P ⟩` holds without this assumption.
<!--zh-->
`Ω` 中的带状区域示意端点为 `c(⊤)`、`c(P)` 的路径族。点击它，路径族展开成第二个类型空间，整条路径改画成其中的点。图中的 `q`、`r` 以 `P` 有证明为前提；与 `⟨ P ⟩` 的类型等价本身不需要这个假设。
<!--ja-->
`Ω` の帯状領域は、端点を `c(⊤)`、`c(P)` とするパスの族を表す。クリックすると、この族が第二の型の空間へ広がり、パス全体がその点として描かれる。図の `q`、`r` は `P` の証明を前提とするが、`⟨ P ⟩` との型同値そのものにはこの仮定は不要である。
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
A point in `⟨ codedTruth P ⟩` is a whole path in `Ω`: `⟨ codedTruth P ⟩ = (c(⊤) ≡ c(P))`. The two proof types are equivalent, at levels `ℓ₁` and `ℓ₂` respectively.
<!--zh-->
`⟨ codedTruth P ⟩` 中的一个点，就是 `Ω` 中的一整条路径：`⟨ codedTruth P ⟩ = (c(⊤) ≡ c(P))`。两个证明类型分别位于 `ℓ₁` 和 `ℓ₂` 层，彼此类型等价。
<!--ja-->
`⟨ codedTruth P ⟩` の一点は、`Ω` の一本のパスそのものである：`⟨ codedTruth P ⟩ = (c(⊤) ≡ c(P))`。二つの証明の型はそれぞれレベル `ℓ₁` と `ℓ₂` に属し、互いに型同値である。
<!--/-->
</figcaption>
</figure>

<!--en-->
**Lemma** (`codedTruthIso`{.Agda}) The underlying type of `P` is isomorphic to the underlying type of `codedTruth P`{.Agda}. Thus the representative constructed above really has the same truth content as `P`.
<!--zh-->
**引理** (`codedTruthIso`{.Agda}) `P` 的底层类型与 `codedTruth P`{.Agda} 的底层类型同构。因此，上面构造的代表确实与 `P` 具有相同的真值内容。
<!--ja-->
**補題** (`codedTruthIso`{.Agda}) `P` の基礎型は `codedTruth P`{.Agda} の基礎型と同型である。したがって、上で構成した代表は確かに `P` と同じ真理内容をもつ。
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

- For `to`{.Agda}, a proof `p : ⟨ P ⟩`{.Agda} makes `⊤` and `P` logically equivalent. Propositional extensionality gives `⊤ ≡ P`{.Agda}; applying `cong c`{.Agda} yields `c ⊤ ≡ c P`{.Agda}, a proof of `codedTruth P`{.Agda}.
<!--zh-->
现在构造两个方向的映射。

- 对于 `to`{.Agda}，证明 `p : ⟨ P ⟩`{.Agda} 使 `⊤` 与 `P` 逻辑等价。命题外延性给出路径 `⊤ ≡ P`{.Agda}，再用 `cong c`{.Agda} 得到 `c ⊤ ≡ c P`{.Agda}，即 `codedTruth P`{.Agda} 的证明。
<!--ja-->
あとは二方向の写像を構成する。

- `to`{.Agda} では、証明 `p : ⟨ P ⟩`{.Agda} によって `⊤` と `P` が論理的同値になる。命題外延性からパス `⊤ ≡ P`{.Agda} を得て、`cong c`{.Agda} によって `c ⊤ ≡ c P`{.Agda}、すなわち `codedTruth P`{.Agda} の証明を得る。
<!--/-->

```agda
    to : ⟨ P ⟩ → ⟨ codedTruth P ⟩
    to p = cong c (⇔toPath (λ _ → p) (λ _ → tt*))
```

<!--en-->
- For `from`{.Agda}, start with `q : c ⊤ ≡ c P`{.Agda}. The equivalence `congEquiv e`{.Agda} identifies paths between propositions with paths between their codes. Its inverse `invEq (congEquiv e)`{.Agda} recovers `⊤ ≡ P`{.Agda}; transporting `tt*`{.Agda} along this path with `subst ⟨_⟩`{.Agda} gives a proof of `P`.
<!--zh-->
- 对于 `from`{.Agda}，从 `q : c ⊤ ≡ c P`{.Agda} 出发。类型等价 `congEquiv e`{.Agda} 联系命题之间的路径与编码之间的路径；其逆映射 `invEq (congEquiv e)`{.Agda} 还原出 `⊤ ≡ P`{.Agda}，再用 `subst ⟨_⟩`{.Agda} 沿该路径搬运 `tt*`{.Agda}，便得到 `P` 的证明。
<!--ja-->
- `from`{.Agda} では、`q : c ⊤ ≡ c P`{.Agda} から出発する。型同値 `congEquiv e`{.Agda} は命題間のパスと符号間のパスを結ぶ。その逆写像 `invEq (congEquiv e)`{.Agda} によって `⊤ ≡ P`{.Agda} を復元し、`subst ⟨_⟩`{.Agda} でこのパスに沿って `tt*`{.Agda} を輸送すれば、`P` の証明が得られる。
<!--/-->

```agda
    from : ⟨ codedTruth P ⟩ → ⟨ P ⟩
    from q = subst ⟨_⟩ (invEq (congEquiv e) q) tt*
```

</details>

∎

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
